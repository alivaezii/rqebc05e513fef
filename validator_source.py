"""Sprint 15A opaque-attestation custody-protocol validation tooling
(``sprints/sprint-15a.md`` §2.10, §5.1, §6.4, §8.3-§8.5, §11, Appendix A --
the merged custody-architecture amendment, its merged attestation-schema
amendment, and its merged key-registry-schema amendment, ``origin/main`` @
``e63dfdbc0d746466b32354da6f4c31b55ed9f388``).

**Synthetic-only, local, offline tooling.** This module never creates the
public attestation repository, never accesses the dedicated evidence
server, never generates or holds a real Sprint 15A cohort key or key
registry, and never performs discovery, screening, repository selection,
annotation, or detector execution. Every key this module generates
(:func:`generate_disposable_test_keypair`) is explicitly disposable and
test-only, created fresh inside a caller-supplied temporary directory --
never a cohort key, never persisted, never reused (§8.4 "Dedicated,
cohort-only signing keys").

**Module placement note**, mirroring ``truvis/sprint15a_screen.py``'s own
placement rationale: this lives at the ``truvis/`` top level, a sibling of
``truvis/sprint15a_screen.py``/``sprint15a_discovery.py``/
``sprint15a_warning_mapping.py``, rather than inside any ``*_engine``
package -- it implements a Sprint-15A-specific preregistration contract
with no natural home in ``audit_engine``/``artifact_engine``/
``dataset_engine``.

**Literal schema, now frozen by the merged document itself.** An earlier
version of this module chose its own field names as an implementation
detail, since the original merged text described fields by role, not by
literal JSON key. A subsequent amendment (``sprints/sprint-15a.md`` §8.4
"Attestation-record and signing-payload literal schema, frozen") froze the
literal key strings normatively. This module now uses exactly those
frozen names: the eleven-key attestation record
(``schema_version``, ``artifact_id``, ``artifact_sha256``, ``byte_length``,
``sequence_number``, ``previous_attestation_sha256``,
``role_key_fingerprint``, ``detached_signature_sha256``,
``signing_payload_sha256``, ``key_registry_version``,
``key_registry_sha256``) and the eight-key signing payload
(``signing_schema_version``, ``artifact_id``, ``artifact_sha256``,
``byte_length``, ``role_identity``, ``role_key_fingerprint``,
``created_at``, ``custody_sequence_reference``). No implementation choice
remains for these names; only ``truvis/sprint15a_screen.py``-style
placement and the specifics below (receipt-binding fields, Actions-record
URL shapes, etc., none of which the frozen document specifies) are this
module's own design.

**What this tooling can and cannot prove.** It can mechanically enforce
every closed allowlist, type, format, canonicalization, chain-linkage,
Actions-conclusion, key-registry-membership, and registry-verification-
topology rule §8.4 freezes (including, since the 2026-09-02 key-registry-
schema amendment, the registry document's own ten-entry representation and
the Record A/Record B two-record pre-genesis verification topology -- see
:func:`validate_registry_document` and
:func:`validate_registry_verification_topology`). Every registry-membership
check requires the caller to independently supply
``expected_role_identities`` -- an exact, out-of-band ten-identity roster,
never defaulted and never inferred from the registry document or
verification records under test (§8.4 item 7's "a fresh derivation...
never merely trusting the registry file's own contents"). With that
roster supplied, this tooling **does** now detect a duplicated,
substituted, missing, or additional identity among all ten registered
entries -- including the eight the merged document never names literally
(discovery operator, screening operator, the §8.1 custodian role, four
ground-truth reviewers, and the separate §5.1 identity-extraction
custodian); an earlier version of this module checked only the count and
the two topology-critical identities' literal presence for those eight,
silently trusting the registry's own self-reported membership -- an
implementation completeness gap (not a genuine specification boundary,
since §8.4 item 7 already obligates exactly this caller-supplied check),
closed by this correction. What remains a genuine, irreducible boundary:
this tooling **cannot** discover the expected roster on its own, or prove
that ``expected_role_identities`` itself is authentic rather than a set
the caller mistakenly (or maliciously) re-derived from the very artifact
under test -- sourcing that roster from the real, confidential cohort role
assignment is a caller obligation no runtime check can discharge (see
:func:`validate_registry_document`'s docstring). It also **cannot** prove
that an opaque identifier does not, by coincidence or construction,
semantically encode a real identity (a separate custodian obligation, see
:func:`require_custodian_non_derivation_receipt`); and, as a pure function
library with no persistent store, it **cannot** independently detect a
caller who fabricates a false publication or receipt-usage history from
scratch -- every history-dependent check here (poisoned-chain evidence,
receipt-reuse tracking) is only as trustworthy as the history the caller
supplies, which must be sourced from the actual, tamper-evident custody
log. Each such boundary is documented at the function that has it, not
silently assumed away.
"""
from __future__ import annotations

import base64
import binascii
import hashlib
import json
import os
import re
import shutil
import subprocess
import unicodedata
import uuid
from dataclasses import dataclass
from datetime import datetime
from pathlib import Path
from typing import Dict, FrozenSet, Iterable, List, Mapping, Optional, Sequence, Tuple

# =========================================================================
# Exceptions
# =========================================================================


class CustodyProtocolError(Exception):
    """Base class for every fail-closed rejection this module raises. Every
    public entry point in this module raises only subclasses of this (or
    lets a genuine environment/I-O error propagate unwrapped, e.g. a
    missing directory) -- never a raw ``json.JSONDecodeError``,
    ``UnicodeDecodeError``, ``binascii.Error``, or ``subprocess`` failure."""


class NoncanonicalSerializationError(CustodyProtocolError):
    """A value or a committed byte string is not RFC 8785 (JCS) canonical,
    per ``sprints/sprint-15a.md`` §8.4's per-artifact role-signing protocol
    item 2 and "Signing-field formats -- frozen types"."""


class AttestationSchemaError(CustodyProtocolError):
    """An attestation record or signing payload violates §8.4's closed
    field allowlist, a frozen field format, or (via
    :func:`verify_composed_artifact_binding`) the cross-binding between the
    two."""


class ForbiddenSemanticMaterialError(CustodyProtocolError):
    """A defense-in-depth syntactic scan found a forbidden semantic term in
    a string value that will be (or was) published. See
    :func:`scan_for_forbidden_semantic_material` for what this can and
    cannot prove."""


class MissingCustodianVerificationError(CustodyProtocolError):
    """No, or an invalid, or an already-used, custodian non-derivation
    verification receipt was supplied for a record about to be treated as
    publication-ready. See :func:`require_custodian_non_derivation_receipt`."""


class AttestationChainError(CustodyProtocolError):
    """A proposed attestation history (or a single new record proposed
    against the current head) violates §8.4's "Attestation chain
    integrity" rules. ``code`` is one of: ``MISSING_GENESIS``,
    ``MULTIPLE_GENESIS``, ``DUPLICATE_SEQUENCE``, ``SKIPPED_SEQUENCE``,
    ``REORDERED``, ``DUPLICATE_PREDECESSOR``, ``FORK``, ``REPLAY``,
    ``REPLACED``, ``STALE_HEAD``, ``HASH_MISMATCH``,
    ``SCHEMA_VERSION_MISMATCH``, ``KEY_REGISTRY_MISMATCH``."""

    def __init__(self, code: str, message: str):
        super().__init__(f"[{code}] {message}")
        self.code = code


class StageManifestError(CustodyProtocolError):
    """A stage manifest violates §8.4's "Stage manifest -- frozen exact
    representation"."""


class SigningVerificationError(CustodyProtocolError):
    """A synthetic OpenSSH signing/verification/fingerprint operation
    failed, or the tooling required to perform one is unavailable (or is
    unavailable while ``TRUVIS_REQUIRE_OPENSSH=1`` mandates it)."""


class RegistryVerificationError(CustodyProtocolError):
    """A key-registry document or registry-verification-record check
    failed (§8.4 "Role public-key registry" and "Registry verification
    record -- frozen exact representation"). ``code`` is one of:
    ``REGISTRY_HASH_MISMATCH``, ``FINGERPRINT_NOT_REGISTERED``,
    ``VERIFICATION_RECORD_SNAPSHOT_MISMATCH``,
    ``VERIFICATION_SCHEMA_VERSION_MISMATCH``, ``WRONG_VERIFIER``,
    ``UNREGISTERED_VERIFIER``, ``VERIFIER_FINGERPRINT_MISMATCH``,
    ``VERIFIED_ENTRY_MISMATCH``, ``SELF_VERIFICATION``,
    ``RECORD_A_COVERAGE_MISMATCH``, ``RECORD_B_COVERAGE_MISMATCH``,
    ``VERIFIED_ENTRY_OVERLAP``, ``NON_EXHAUSTIVE_UNION``,
    ``TOO_FEW_VERIFICATION_RECORDS``, ``THIRD_RECORD_REJECTED``,
    ``NONCANONICAL_VERIFICATION_RECORD``,
    ``SIGNING_PAYLOAD_SIGNER_MISMATCH``, ``GENESIS_ANCHOR_MISMATCH``,
    ``EXPECTED_ROLE_IDENTITIES_MISSING``,
    ``EXPECTED_ROLE_IDENTITIES_MALFORMED``,
    ``EXPECTED_ROLE_IDENTITIES_COUNT_MISMATCH``,
    ``EXPECTED_ROLE_IDENTITIES_DUPLICATE``,
    ``REGISTRY_IDENTITY_SET_MISMATCH``. The last five guard the
    caller-supplied *expected role-identity set* (see
    :func:`validate_registry_document`) that every registry-membership
    check now mandatorily requires; ``NON_EXHAUSTIVE_UNION`` additionally
    serves as the frozen "verification-record union mismatch" check once
    that expected set is enforced (see
    :func:`validate_registry_verification_topology`'s docstring for why
    this is a deliberate reuse, not an omission)."""

    def __init__(self, code: str, message: str):
        super().__init__(f"[{code}] {message}")
        self.code = code


class ActionsGateError(CustodyProtocolError):
    """A proposed custody transition is not authorized by §8.4's
    "Mandatory successful Actions completion" rule. ``code`` is one of:
    ``MISSING_RECORDED_FIELD``, ``MALFORMED_COMMIT_SHA``,
    ``MALFORMED_COMMIT_URL``, ``COMMIT_URL_SHA_MISMATCH``,
    ``MALFORMED_WORKFLOW_RUN_URL``, ``INVALID_TIMESTAMP``,
    ``MALFORMED_CONCLUSION``, ``NO_COMPLETED_RUN``, ``SHA_MISMATCH``,
    ``BRANCH_MISMATCH``, ``NON_AUTHORIZING_CONCLUSION``,
    ``MISSING_PUBLICATION_HISTORY``, ``INCOMPLETE_PUBLICATION_HISTORY``,
    ``HISTORY_RUN_MISMATCH``."""

    def __init__(self, code: str, message: str):
        super().__init__(f"[{code}] {message}")
        self.code = code


class PoisonedChainError(CustodyProtocolError):
    """The canonical chain, per validated publication-run evidence, is
    poisoned (§8.4 "Failed-run and poisoned-chain policy"). See
    :func:`compute_chain_poison_status` and
    :func:`raise_if_chain_poisoned`."""


# =========================================================================
# Canonical serialization: RFC 8785 (JCS), NFC-before-JCS
# (sprints/sprint-15a.md §8.4 "Per-artifact role-signing protocol" item 2,
# "Signing-field formats -- frozen types")
# =========================================================================

# JCS's ECMAScript-compatible number rule guarantees a round-trippable
# decimal representation only within the IEEE-754 double's safe-integer
# range. This protocol's frozen numeric fields (byte_length,
# sequence_number) are integers well inside that range in any realistic
# use; values at or beyond it are rejected rather than silently
# mis-serialized.
_JCS_SAFE_INTEGER_BOUND = 2**53


def _nfc(value: str) -> str:
    return unicodedata.normalize("NFC", value)


def _utf16_code_units(value: str) -> Tuple[int, ...]:
    """The sort key JCS requires for object keys: comparison by UTF-16
    code-unit value, which differs from plain Python code-point comparison
    only for non-BMP (surrogate-pair) characters -- implemented exactly,
    not approximated by ``str`` comparison. **This governs JSON *object
    key* ordering only** -- it is unrelated to, and never used for,
    ``members``-array element ordering (:func:`validate_stage_manifest`
    uses plain code-point order for that, per the frozen exact-ordering
    rule)."""
    encoded = value.encode("utf-16-be")
    return tuple(int.from_bytes(encoded[i : i + 2], "big") for i in range(0, len(encoded), 2))


def _jcs_number(value: int) -> str:
    if isinstance(value, bool) or not isinstance(value, int):
        raise NoncanonicalSerializationError(f"JCS numbers in this protocol must be Python int, got {type(value).__name__}")
    if value < 0:
        raise NoncanonicalSerializationError("this protocol's frozen formats never permit a negative integer")
    if value >= _JCS_SAFE_INTEGER_BOUND:
        raise NoncanonicalSerializationError("integer exceeds the ECMAScript safe-integer range JCS numbers require")
    return str(value)


def _jcs_encode(value: object) -> str:
    if isinstance(value, bool):
        raise NoncanonicalSerializationError("boolean values are not part of this protocol's frozen schema")
    if isinstance(value, str):
        return json.dumps(_nfc(value), ensure_ascii=False)
    if isinstance(value, int):
        return _jcs_number(value)
    if isinstance(value, float):
        # Covers NaN, Infinity, -Infinity, and -0.0 alike -- Python floats
        # are rejected outright, never selectively.
        raise NoncanonicalSerializationError("floating-point numbers (including NaN/Infinity/-0.0) are not part of this protocol's frozen schema")
    if isinstance(value, dict):
        for key in value.keys():
            if not isinstance(key, str):
                raise NoncanonicalSerializationError(f"object keys must be strings, got {type(key).__name__}")
        normalized_keys = {key: _nfc(key) for key in value.keys()}
        if len(set(normalized_keys.values())) != len(normalized_keys):
            colliding = sorted({k for k, nk in normalized_keys.items() if list(normalized_keys.values()).count(nk) > 1})
            raise NoncanonicalSerializationError(f"object keys collide after NFC normalization: {colliding}")
        ordered_keys = sorted(value.keys(), key=lambda k: _utf16_code_units(normalized_keys[k]))
        parts = [f"{json.dumps(normalized_keys[key], ensure_ascii=False)}:{_jcs_encode(value[key])}" for key in ordered_keys]
        return "{" + ",".join(parts) + "}"
    if isinstance(value, (list, tuple)):
        return "[" + ",".join(_jcs_encode(item) for item in value) + "]"
    if value is None:
        raise NoncanonicalSerializationError("null is not part of this protocol's frozen schema")
    raise NoncanonicalSerializationError(f"unsupported value type for canonical serialization: {type(value).__name__}")


def jcs_canonicalize(value: object) -> bytes:
    """RFC 8785 (JCS) canonical serialization, restricted to the value
    shapes this protocol's frozen schema actually uses (objects, arrays,
    NFC-normalized strings, and non-negative integers within the
    ECMAScript safe-integer range) -- with every Unicode string value (and
    every object key) normalized to NFC *before* serialization, per
    §8.4's frozen rule. UTF-8 encoded, no insignificant whitespace, no
    trailing newline. A string containing a lone (unpaired) UTF-16
    surrogate code point cannot be encoded as valid UTF-8 at all; this is
    surfaced as :class:`NoncanonicalSerializationError`, never a raw
    ``UnicodeEncodeError``."""
    encoded = _jcs_encode(value)
    try:
        return encoded.encode("utf-8")
    except UnicodeEncodeError as exc:
        raise NoncanonicalSerializationError(f"value contains a lone surrogate code point, not representable as valid UTF-8: {exc}") from exc


def canonical_sha256(value: object) -> str:
    """SHA-256 of ``value``'s RFC 8785/JCS canonical serialization, as
    lowercase hex -- the exact preimage §8.4's "Predecessor-hash preimage,
    stated completely" paragraph defines for ``previous_attestation_sha256``."""
    return hashlib.sha256(jcs_canonicalize(value)).hexdigest()


def _reject_json_constant(constant_text: str) -> None:
    raise NoncanonicalSerializationError(f"JSON constant {constant_text!r} (NaN/Infinity/-Infinity) is never part of this protocol's frozen schema")


def _strict_object_pairs_hook(pairs: List[Tuple[str, object]]) -> Dict[str, object]:
    """Rejects duplicate raw JSON object keys *before* they could silently
    overwrite one another the way the stdlib ``dict`` constructor (and
    therefore ``json.loads``'s default behavior) otherwise would."""
    seen: Dict[str, object] = {}
    for key, value in pairs:
        if key in seen:
            raise NoncanonicalSerializationError(f"duplicate JSON object key {key!r} in committed bytes")
        seen[key] = value
    return seen


_UTF8_BOM = b"\xef\xbb\xbf"


def assert_canonical_bytes(raw_bytes: bytes) -> Dict[str, object]:
    """Decodes ``raw_bytes`` as strict UTF-8 JSON -- rejecting a leading
    byte-order mark, duplicate object keys, and the non-standard
    ``NaN``/``Infinity``/``-Infinity`` constant tokens Python's ``json``
    module otherwise accepts by default -- and re-serializes the resulting
    value with :func:`jcs_canonicalize`; raises
    :class:`NoncanonicalSerializationError` unless the two are
    byte-identical. This single byte-identity comparison is also what
    fails closed on trailing garbage/whitespace after the JSON value: the
    canonical form never has any, so any input that does cannot match.
    This is the direct test of §8.4's "any byte-level deviation from RFC
    8785 in the committed JSON" rejection rule -- it operates on the
    literal bytes as committed, not on an already-parsed-and-therefore-
    reformatted Python object."""
    if raw_bytes.startswith(_UTF8_BOM):
        raise NoncanonicalSerializationError("committed bytes begin with a UTF-8 byte-order mark, which RFC 8785/JCS never produces")
    try:
        text = raw_bytes.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise NoncanonicalSerializationError(f"committed bytes are not valid UTF-8: {exc}") from exc
    try:
        decoded = json.loads(text, object_pairs_hook=_strict_object_pairs_hook, parse_constant=_reject_json_constant)
    except json.JSONDecodeError as exc:
        raise NoncanonicalSerializationError(f"committed bytes are not valid JSON: {exc}") from exc
    recanonicalized = jcs_canonicalize(decoded)
    if recanonicalized != raw_bytes:
        raise NoncanonicalSerializationError(
            "committed bytes are not the RFC 8785/JCS canonical serialization of their own decoded JSON value"
        )
    if not isinstance(decoded, dict):
        raise NoncanonicalSerializationError("a committed attestation/signing-payload/manifest document must be a JSON object")
    return decoded


# =========================================================================
# Frozen field formats (sprints/sprint-15a.md §8.4
# "Signing-field formats -- frozen types")
# =========================================================================

GENESIS_SENTINEL = "0" * 64

_ASCII_ID_RE = re.compile(r"^[A-Za-z0-9][A-Za-z0-9._-]{0,127}$")
_SHA256_RE = re.compile(r"^[0-9a-f]{64}$")
_TIMESTAMP_RE = re.compile(r"^\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}Z$")
_TIMESTAMP_STRPTIME_FORMAT = "%Y-%m-%dT%H:%M:%SZ"
# 32-byte SHA-256 digest, unpadded standard base64: ceil(256/6) = 43 chars.
_FINGERPRINT_RE = re.compile(r"^SHA256:[A-Za-z0-9+/]{43}$")


def _validate_ascii_id(name: str, value: object) -> None:
    if not isinstance(value, str) or not _ASCII_ID_RE.match(value):
        raise AttestationSchemaError(f"{name!r} must match the frozen ASCII grammar ^[A-Za-z0-9][A-Za-z0-9._-]{{0,127}}$, got {value!r}")


def _validate_sha256(name: str, value: object) -> None:
    if not isinstance(value, str) or not _SHA256_RE.match(value):
        raise AttestationSchemaError(f"{name!r} must be exactly 64 lowercase hexadecimal characters, got {value!r}")


def _validate_nonneg_int(name: str, value: object) -> None:
    if isinstance(value, bool) or not isinstance(value, int) or value < 0:
        raise AttestationSchemaError(f"{name!r} must be a non-negative integer, got {value!r}")


def _validate_timestamp(name: str, value: object) -> None:
    """Lexical form (per :data:`_TIMESTAMP_RE`) **and** real calendar/time
    validity (via ``strptime``, which rejects e.g. month 13, day 32 for a
    30-day month, or a non-leap-year February 29th) -- a string can match
    the regex and still name a date that never existed."""
    if not isinstance(value, str) or not _TIMESTAMP_RE.match(value):
        raise AttestationSchemaError(f"{name!r} must be an RFC 3339 UTC whole-second timestamp ending in 'Z', got {value!r}")
    try:
        datetime.strptime(value, _TIMESTAMP_STRPTIME_FORMAT)
    except ValueError as exc:
        raise AttestationSchemaError(f"{name!r} is not a valid calendar timestamp: {value!r} ({exc})") from exc


def _validate_fingerprint(name: str, value: object) -> None:
    """Lexical form, decodability, exact 32-byte length, **and** canonical
    base64 encoding (no non-zero discarded bits in the final partial
    character group -- detected by re-encoding the decoded bytes and
    requiring an exact match against the original, rather than trusting a
    lenient decoder to silently accept a noncanonical variant)."""
    if not isinstance(value, str) or not _FINGERPRINT_RE.match(value):
        raise AttestationSchemaError(f"{name!r} must be an OpenSSH 'SHA256:<base64-without-padding>' fingerprint, got {value!r}")
    encoded = value[len("SHA256:") :]
    try:
        decoded = base64.b64decode(encoded + "=", validate=True)
    except (binascii.Error, ValueError) as exc:
        raise AttestationSchemaError(f"{name!r} does not decode as valid base64: {value!r} ({exc})") from exc
    if len(decoded) != 32:
        raise AttestationSchemaError(f"{name!r} must decode to exactly 32 bytes (a SHA-256 digest), got {len(decoded)}: {value!r}")
    recanonicalized = base64.b64encode(decoded).decode("ascii").rstrip("=")
    if recanonicalized != encoded:
        raise AttestationSchemaError(f"{name!r} is not canonically encoded (non-zero discarded bits in the final base64 group): {value!r}")


# =========================================================================
# Attestation record and signing payload: closed, literal-key allowlists
# (sprints/sprint-15a.md §8.4 "Attestation-record and signing-payload
# literal schema, frozen" -- the eleven and eight literal keys are
# normative, not this module's own choice)
# =========================================================================

ATTESTATION_RECORD_FIELDS = frozenset(
    {
        "schema_version",
        "artifact_id",
        "artifact_sha256",
        "byte_length",
        "sequence_number",
        "previous_attestation_sha256",
        "role_key_fingerprint",
        "detached_signature_sha256",
        "signing_payload_sha256",
        "key_registry_version",
        "key_registry_sha256",
    }
)
assert len(ATTESTATION_RECORD_FIELDS) == 11, "the frozen attestation record must carry exactly eleven fields (sprints/sprint-15a.md §8.4)"

_ATTESTATION_FIELD_VALIDATORS = {
    "schema_version": _validate_ascii_id,
    "artifact_id": _validate_ascii_id,
    "artifact_sha256": _validate_sha256,
    "byte_length": _validate_nonneg_int,
    "sequence_number": _validate_nonneg_int,
    "previous_attestation_sha256": _validate_sha256,
    "role_key_fingerprint": _validate_fingerprint,
    "detached_signature_sha256": _validate_sha256,
    "signing_payload_sha256": _validate_sha256,
    "key_registry_version": _validate_ascii_id,
    "key_registry_sha256": _validate_sha256,
}
assert set(_ATTESTATION_FIELD_VALIDATORS) == ATTESTATION_RECORD_FIELDS

SIGNING_PAYLOAD_FIELDS = frozenset(
    {
        "signing_schema_version",
        "artifact_id",
        "artifact_sha256",
        "byte_length",
        "role_identity",
        "role_key_fingerprint",
        "created_at",
        "custody_sequence_reference",
    }
)
assert len(SIGNING_PAYLOAD_FIELDS) == 8, "the frozen signing payload must carry exactly eight fields (sprints/sprint-15a.md §8.4)"

_SIGNING_PAYLOAD_FIELD_VALIDATORS = {
    "signing_schema_version": _validate_ascii_id,
    "artifact_id": _validate_ascii_id,
    "artifact_sha256": _validate_sha256,
    "byte_length": _validate_nonneg_int,
    "role_identity": _validate_ascii_id,
    "role_key_fingerprint": _validate_fingerprint,
    "created_at": _validate_timestamp,
    "custody_sequence_reference": _validate_nonneg_int,
}
assert set(_SIGNING_PAYLOAD_FIELD_VALIDATORS) == SIGNING_PAYLOAD_FIELDS


def validate_attestation_record(record: object) -> None:
    """Validates ``record`` against §8.4's closed, literal eleven-key
    attestation-record allowlist: rejects any unknown/extra/differently-
    named field, any missing field, and any field whose type or lexical
    format deviates from "Signing-field formats -- frozen types". This is
    a schema check only -- chain position (genesis/sequence/predecessor
    linkage, genesis-anchor consistency) is
    :func:`validate_attestation_chain`'s responsibility."""
    if not isinstance(record, dict):
        raise AttestationSchemaError(f"attestation record must be a JSON object, got {type(record).__name__}")
    present = set(record.keys())
    unknown = present - ATTESTATION_RECORD_FIELDS
    if unknown:
        raise AttestationSchemaError(f"attestation record carries field(s) outside the closed eleven-key allowlist: {sorted(unknown)}")
    missing = ATTESTATION_RECORD_FIELDS - present
    if missing:
        raise AttestationSchemaError(f"attestation record is missing required field(s): {sorted(missing)}")
    for field, validator in _ATTESTATION_FIELD_VALIDATORS.items():
        validator(field, record[field])


def validate_signing_payload(payload: object) -> None:
    """Validates ``payload`` against the frozen, literal eight-key
    signing-payload schema (§8.4 "Attestation-record and signing-payload
    literal schema, frozen")."""
    if not isinstance(payload, dict):
        raise AttestationSchemaError(f"signing payload must be a JSON object, got {type(payload).__name__}")
    present = set(payload.keys())
    unknown = present - SIGNING_PAYLOAD_FIELDS
    if unknown:
        raise AttestationSchemaError(f"signing payload carries field(s) outside the frozen eight-key allowlist: {sorted(unknown)}")
    missing = SIGNING_PAYLOAD_FIELDS - present
    if missing:
        raise AttestationSchemaError(f"signing payload is missing required field(s): {sorted(missing)}")
    for field, validator in _SIGNING_PAYLOAD_FIELD_VALIDATORS.items():
        validator(field, payload[field])


def verify_composed_artifact_binding(signing_payload: Mapping[str, object], attestation_record: Mapping[str, object]) -> None:
    """Cross-checks a signing payload and the attestation record produced
    from it agree on every field the two share, at the **composed
    artifact/attestation verification boundary**: ``artifact_id``,
    ``artifact_sha256``, ``byte_length``, and ``role_key_fingerprint`` must
    match exactly, ``custody_sequence_reference`` (payload) must equal
    ``sequence_number`` (record), and the record's ``signing_payload_sha256``
    must equal the recomputed canonical SHA-256 of the payload itself.
    Raises :class:`AttestationSchemaError` on the first mismatch found."""
    validate_signing_payload(dict(signing_payload))
    validate_attestation_record(dict(attestation_record))
    for payload_field, record_field in (
        ("artifact_id", "artifact_id"),
        ("artifact_sha256", "artifact_sha256"),
        ("byte_length", "byte_length"),
        ("role_key_fingerprint", "role_key_fingerprint"),
    ):
        if signing_payload[payload_field] != attestation_record[record_field]:
            raise AttestationSchemaError(
                f"composed binding mismatch: signing payload {payload_field!r}={signing_payload[payload_field]!r} != "
                f"attestation record {record_field!r}={attestation_record[record_field]!r}"
            )
    if signing_payload["custody_sequence_reference"] != attestation_record["sequence_number"]:
        raise AttestationSchemaError(
            "composed binding mismatch: signing payload custody_sequence_reference "
            f"{signing_payload['custody_sequence_reference']!r} != attestation record sequence_number "
            f"{attestation_record['sequence_number']!r}"
        )
    expected_signing_payload_sha256 = canonical_sha256(signing_payload)
    if attestation_record["signing_payload_sha256"] != expected_signing_payload_sha256:
        raise AttestationSchemaError(
            "composed binding mismatch: attestation record signing_payload_sha256 does not match the recomputed "
            "canonical SHA-256 of the supplied signing payload"
        )


# =========================================================================
# Forbidden semantic material (sprints/sprint-15a.md §8.4: "and never
# candidate identity, repository identity, detector name, result, label,
# rationale text, source, ground truth, role name, or
# role-name-to-fingerprint mapping of any kind")
# =========================================================================

# A defense-in-depth denylist scan over literal string values -- NOT a
# proof of semantic opacity. §8.4 states plainly that whether an opaque
# identifier semantically encodes a forbidden identity is a custodian
# obligation no automated tool can discharge on its own; this scan only
# catches the narrower case of an accidentally-literal forbidden term
# appearing in a field that is otherwise schema-valid.
FORBIDDEN_SEMANTIC_SUBSTRINGS = frozenset(
    {
        "candidate",
        "repository",
        "repo_",
        "detector",
        "ground_truth",
        "ground truth",
        "label",
        "rationale",
        "verdict",
        "comparison",
        "test_set_misuse",
        "preprocessing_fit_before_split",
        "github.com",
        "role_name",
        "sprint15",
        "sprint_15",
        "truvis",
    }
)


def scan_for_forbidden_semantic_material(record: Mapping[str, object]) -> List[str]:
    """Returns a list of human-readable violation descriptions (empty if
    none found) for every string value in ``record`` that contains a
    literal :data:`FORBIDDEN_SEMANTIC_SUBSTRINGS` term, case-insensitively.
    See the module- and section-level notes: this is a syntactic net, not
    a semantic-opacity proof."""
    hits: List[str] = []
    for key, value in record.items():
        if isinstance(value, str):
            lowered = value.lower()
            for term in FORBIDDEN_SEMANTIC_SUBSTRINGS:
                if term in lowered:
                    hits.append(f"field {key!r} contains forbidden term {term!r} (value {value!r})")
    return hits


def assert_no_forbidden_semantic_material(record: Mapping[str, object]) -> None:
    hits = scan_for_forbidden_semantic_material(record)
    if hits:
        raise ForbiddenSemanticMaterialError("; ".join(hits))


@dataclass(frozen=True)
class CustodianNonDerivationReceipt:
    """A synthetic stand-in, for this tooling's purposes, for the
    custodian's real-world recorded confirmation that a given opaque
    identifier was generated by a non-derivation, cryptographically random
    process and independently checked against the real identity it stands
    in for (§8.4, "GitHub Actions cannot itself determine ..."). This is a
    required *input* to :func:`validate_publication_ready`, never a value
    this module computes on its own.

    **Content-bound, not merely ID-bound.** ``artifact_sha256``,
    ``byte_length``, and ``signing_payload_sha256`` bind this receipt to
    one exact artifact *version* -- a receipt is never valid for a
    different hash/length/payload published under a reused ``artifact_id``.

    **Reuse tracking is the caller's responsibility.** This dataclass
    carries ``receipt_id`` so a caller *can* track consumption, but this
    module has no persistent store of its own -- see
    :func:`require_custodian_non_derivation_receipt`'s
    ``previously_used_receipt_ids`` parameter, which is mandatory (not
    merely optional-and-defaulted) at every call site that checks reuse."""

    receipt_id: str
    artifact_id: str
    artifact_sha256: str
    byte_length: int
    signing_payload_sha256: str
    reviewed_by_role_identity: str
    reviewed_at: str  # RFC 3339 UTC, whole seconds, trailing 'Z'
    confirmed_non_derived: bool
    confirmed_not_previously_published: bool
    notes: str = ""


def require_custodian_non_derivation_receipt(
    record: Mapping[str, object],
    receipt: Optional[CustodianNonDerivationReceipt],
    *,
    previously_used_receipt_ids: Optional[FrozenSet[str]],
) -> None:
    """Fail-closed gate: raises :class:`MissingCustodianVerificationError`
    unless ``receipt`` is present, its ``receipt_id`` is well-formed and
    absent from ``previously_used_receipt_ids``, its ``reviewed_at`` is a
    valid timestamp, it binds exactly (``artifact_id``, ``artifact_sha256``,
    ``byte_length``, ``signing_payload_sha256``) to ``record``, and it
    affirmatively confirms both non-derivation and non-prior-publication.

    ``previously_used_receipt_ids`` is a **required keyword argument with
    no default** -- pass ``None`` explicitly only if the caller has
    verified, out of band, that this is the very first publication ever
    (e.g. the genesis attestation) and no reuse history can exist yet; any
    other omission is refused rather than silently treated as "no reuse
    has ever occurred". This module has no persistent store of consumed
    receipts and cannot detect reuse on its own -- the publication caller
    must source this set from the actual custody log."""
    if receipt is None:
        raise MissingCustodianVerificationError(
            "no custodian non-derivation verification receipt supplied -- this tooling cannot itself "
            "prove semantic opacity of an opaque identifier (sprints/sprint-15a.md §8.4); publication "
            "readiness requires an explicit custodian receipt, never an automated inference"
        )
    if previously_used_receipt_ids is None:
        raise MissingCustodianVerificationError(
            "previously_used_receipt_ids was not supplied -- this pure validator has no persistent store of "
            "which receipts have already been consumed; the publication caller must supply that history "
            "explicitly (sourced from the actual custody log) so reuse can be detected -- fail closed rather "
            "than silently assume no prior use"
        )
    _validate_ascii_id("receipt_id", receipt.receipt_id)
    if receipt.receipt_id in previously_used_receipt_ids:
        raise MissingCustodianVerificationError(f"custodian receipt {receipt.receipt_id!r} has already been used and may not authorize a second publication")
    try:
        _validate_timestamp("reviewed_at", receipt.reviewed_at)
    except AttestationSchemaError as exc:
        raise MissingCustodianVerificationError(f"custodian receipt reviewed_at is invalid: {exc}") from exc

    mismatches = []
    if receipt.artifact_id != record.get("artifact_id"):
        mismatches.append("artifact_id")
    if receipt.artifact_sha256 != record.get("artifact_sha256"):
        mismatches.append("artifact_sha256")
    if receipt.byte_length != record.get("byte_length"):
        mismatches.append("byte_length")
    if receipt.signing_payload_sha256 != record.get("signing_payload_sha256"):
        mismatches.append("signing_payload_sha256")
    if mismatches:
        raise MissingCustodianVerificationError(
            f"custodian receipt does not exactly match the attestation record under review on: {mismatches} "
            "-- a receipt is bound to one exact artifact version, never merely a reused opaque artifact_id"
        )
    if not receipt.confirmed_non_derived or not receipt.confirmed_not_previously_published:
        raise MissingCustodianVerificationError(
            "custodian receipt does not affirmatively confirm both non-derivation and non-prior-publication"
        )


def validate_publication_ready(
    record: Mapping[str, object],
    non_derivation_receipt: Optional[CustodianNonDerivationReceipt],
    *,
    previously_used_receipt_ids: Optional[FrozenSet[str]],
) -> None:
    """The combined publication-readiness gate: schema-valid, free of
    forbidden semantic material by the syntactic scan, and backed by an
    explicit, content-bound, not-yet-used custodian non-derivation
    receipt."""
    validate_attestation_record(dict(record))
    assert_no_forbidden_semantic_material(record)
    require_custodian_non_derivation_receipt(record, non_derivation_receipt, previously_used_receipt_ids=previously_used_receipt_ids)


# =========================================================================
# Attestation chain integrity (sprints/sprint-15a.md §8.4 "Attestation
# chain integrity -- single, non-forkable, linear history"; genesis-anchor
# consistency per "Attestation-record and signing-payload literal schema,
# frozen" and "Role public-key registry -- genesis-anchored")
# =========================================================================


def _check_genesis_anchor_consistency(record: Mapping[str, object], genesis: Mapping[str, object], position: int) -> None:
    if record["schema_version"] != genesis["schema_version"]:
        raise AttestationChainError(
            "SCHEMA_VERSION_MISMATCH",
            f"record at position {position} has schema_version {record['schema_version']!r}, but the genesis "
            f"attestation anchors {genesis['schema_version']!r} for the complete cohort chain",
        )
    if record["key_registry_version"] != genesis["key_registry_version"] or record["key_registry_sha256"] != genesis["key_registry_sha256"]:
        raise AttestationChainError(
            "KEY_REGISTRY_MISMATCH",
            f"record at position {position} references key registry "
            f"{record['key_registry_version']!r}/{record['key_registry_sha256']!r}, but the genesis attestation "
            f"anchors {genesis['key_registry_version']!r}/{genesis['key_registry_sha256']!r}",
        )


def validate_attestation_chain(
    records: Sequence[Mapping[str, object]],
    previously_validated_hashes: Optional[Mapping[int, str]] = None,
) -> None:
    """Validates a **complete proposed canonical history**, supplied in
    commit order (``records[0]`` must be the genesis; ``records[i]`` must
    be the unique immediate successor of ``records[i-1]``) -- mirroring
    §8.4's own requirement that every Actions run "validates the entire
    reachable canonical first-parent attestation history from genesis to
    that commit". Every individual record is first schema-validated, and
    every record's ``schema_version``/``key_registry_version``/
    ``key_registry_sha256`` must equal the genesis record's (a mixed
    registry/schema history is ``STOP``).

    ``previously_validated_hashes``, if supplied, maps a ``sequence_number``
    already validated in a prior pass to the canonical SHA-256 recorded for
    it then; a record now recomputing to a different hash at that same
    ``sequence_number`` is rejected as ``REPLACED`` ("the content at a
    given sequence_number differs from what was previously validated at
    that position")."""
    if not records:
        raise AttestationChainError("MISSING_GENESIS", "empty history has no genesis record")

    for record in records:
        validate_attestation_record(record)

    genesis_positions = [i for i, r in enumerate(records) if r["sequence_number"] == 0]
    if not genesis_positions:
        raise AttestationChainError("MISSING_GENESIS", "no record with sequence_number == 0 found")
    if len(genesis_positions) > 1:
        raise AttestationChainError("MULTIPLE_GENESIS", f"{len(genesis_positions)} records claim sequence_number == 0")
    if genesis_positions[0] != 0:
        raise AttestationChainError("REORDERED", "the genesis record (sequence_number == 0) is not first in the supplied history order")
    if records[0]["previous_attestation_sha256"] != GENESIS_SENTINEL:
        raise AttestationChainError(
            "MISSING_GENESIS", "the genesis record's previous_attestation_sha256 is not the frozen 64-zero sentinel"
        )

    genesis = records[0]
    seen_sequences: Dict[int, str] = {}
    seen_predecessors: Dict[str, int] = {}
    seen_canonical_hashes: Dict[str, int] = {}
    prior_hash: Optional[str] = None

    for i, record in enumerate(records):
        _check_genesis_anchor_consistency(record, genesis, i)

        seq = record["sequence_number"]
        assert isinstance(seq, int)

        if seq in seen_sequences:
            raise AttestationChainError("DUPLICATE_SEQUENCE", f"sequence_number {seq} appears more than once in this history")

        if i > 0:
            expected_seq = records[i - 1]["sequence_number"] + 1  # type: ignore[operator]
            if seq != expected_seq:
                code = "SKIPPED_SEQUENCE" if seq > expected_seq else "REORDERED"
                raise AttestationChainError(code, f"expected sequence_number {expected_seq} at position {i}, found {seq}")

        pred = record["previous_attestation_sha256"]
        assert isinstance(pred, str)
        if pred in seen_predecessors:
            code = "MULTIPLE_GENESIS" if pred == GENESIS_SENTINEL else "FORK"
            raise AttestationChainError(
                code, f"previous_attestation_sha256 {pred!r} is claimed by more than one record (positions {seen_predecessors[pred]} and {i})"
            )

        own_hash = canonical_sha256(record)
        if own_hash in seen_canonical_hashes:
            raise AttestationChainError(
                "REPLAY",
                f"record at position {i} (sequence_number {seq}) is byte-identical, after canonicalization, to the "
                f"record at position {seen_canonical_hashes[own_hash]} -- a previously seen attestation committed again",
            )

        if i > 0:
            if pred != prior_hash:
                raise AttestationChainError(
                    "HASH_MISMATCH",
                    f"record at position {i} (sequence_number {seq}) claims predecessor {pred!r}, but the immediately "
                    f"preceding record's canonical SHA-256 is {prior_hash!r}",
                )

        if previously_validated_hashes is not None and seq in previously_validated_hashes:
            expected_hash = previously_validated_hashes[seq]
            if own_hash != expected_hash:
                raise AttestationChainError(
                    "REPLACED",
                    f"record at sequence_number {seq} now canonicalizes to {own_hash!r}, but a prior validation pass "
                    f"recorded {expected_hash!r} at that same position -- its content was replaced after the fact",
                )

        seen_sequences[seq] = own_hash
        seen_predecessors[pred] = i
        seen_canonical_hashes[own_hash] = i
        prior_hash = own_hash


def validate_new_attestation_against_head(new_record: Mapping[str, object], current_head_record: Optional[Mapping[str, object]]) -> None:
    """Models the moment of publication described in §8.4 "Publication
    mechanics": "Each attestation starts from the current canonical
    `HEAD`". Detects a stale-head, forked, duplicate-sequence, replayed,
    or genesis-anchor-drifted publication attempt **at that boundary** -- a
    single proposed new record checked against the actual current head --
    independent of, and complementary to,
    :func:`validate_attestation_chain`'s full-history check.
    ``current_head_record`` is ``None`` only when no attestation has ever
    been published yet (the proposed record must then be the genesis, and
    defines its own anchor -- there is nothing yet to compare it against)."""
    validate_attestation_record(new_record)

    if current_head_record is None:
        if new_record["sequence_number"] != 0:
            raise AttestationChainError(
                "MISSING_GENESIS", "no attestation has been published yet, but the proposed record is not the genesis"
            )
        if new_record["previous_attestation_sha256"] != GENESIS_SENTINEL:
            raise AttestationChainError("MISSING_GENESIS", "the genesis record's predecessor must be the frozen 64-zero sentinel")
        return

    validate_attestation_record(current_head_record)
    _check_genesis_anchor_consistency(new_record, current_head_record, position=-1)
    head_hash = canonical_sha256(current_head_record)
    if canonical_sha256(new_record) == head_hash:
        raise AttestationChainError("REPLAY", "the proposed record is byte-identical to the current head -- it is already published")

    expected_seq = current_head_record["sequence_number"] + 1  # type: ignore[operator]
    if new_record["sequence_number"] != expected_seq:
        code = "SKIPPED_SEQUENCE" if new_record["sequence_number"] > expected_seq else "DUPLICATE_SEQUENCE"  # type: ignore[operator]
        raise AttestationChainError(
            code, f"expected sequence_number {expected_seq} as the current head's successor, found {new_record['sequence_number']}"
        )

    if new_record["previous_attestation_sha256"] != head_hash:
        raise AttestationChainError(
            "STALE_HEAD",
            "the proposed record's previous_attestation_sha256 does not match the actual current canonical HEAD's "
            "hash -- its branch was cut from a stale or different head (concurrent publication / fork)",
        )


# =========================================================================
# Key-registry document: frozen exact representation (sprints/sprint-15a.md
# §8.4 "Role public-key registry -- genesis-anchored, frozen for the
# cohort", merged by the 2026-09-02 key-registry-schema amendment,
# origin/main @ e63dfdbc0d746466b32354da6f4c31b55ed9f388). Previously this
# section could only enforce the registry's hashing/genesis-anchoring
# discipline, since the document's internal field layout was unfrozen; the
# merged amendment now freezes that layout completely, closing the gap
# :class:`RegistryFingerprintMembershipUnspecifiedError` used to document.
# =========================================================================

REGISTRY_DOCUMENT_FIELDS = frozenset({"registry_schema_version", "key_registry_version", "entries"})
assert len(REGISTRY_DOCUMENT_FIELDS) == 3, "the frozen registry document must carry exactly three top-level fields (sprints/sprint-15a.md §8.4)"

REGISTRY_ENTRY_FIELDS = frozenset({"role_identity", "role_key_fingerprint", "public_key"})
assert len(REGISTRY_ENTRY_FIELDS) == 3, "the frozen registry entry must carry exactly three fields (sprints/sprint-15a.md §8.4)"

EXPECTED_REGISTRY_ENTRY_COUNT = 10

# item 8's two-record verification topology names these two identities as
# literals (backtick-quoted in the frozen text: "Record A -- `audit_operator`
# verification record", "the `audit_operator` identity for Record A, the
# `comparison_role` identity for Record B") -- the only two of the ten
# registered identities whose literal `role_identity` string the merged
# document actually freezes. The other eight (discovery operator, screening
# operator, the §8.1 custodian role, four ground-truth reviewers, and the
# separate §5.1 identity-extraction custodian) are frozen only by *category*
# and *count*, never by literal string -- this module does not invent names
# for them, exactly as it already refuses to invent an unfrozen registry
# schema elsewhere (see the former RegistryFingerprintMembershipUnspecifiedError,
# now obsolete for the fields this amendment did freeze).
AUDIT_OPERATOR_IDENTITY = "audit_operator"
COMPARISON_ROLE_IDENTITY = "comparison_role"

# OpenSSH wire-format `ssh-ed25519` public-key blob: a 4-byte big-endian
# length prefix, the 11-byte ASCII string "ssh-ed25519", a 4-byte big-endian
# length prefix, and the raw 32-byte ED25519 public key -- always exactly
# 4 + 11 + 4 + 32 = 51 bytes.
_SSH_ED25519_WIRE_TYPE = b"ssh-ed25519"
_SSH_ED25519_WIRE_FORMAT_LENGTH = 4 + len(_SSH_ED25519_WIRE_TYPE) + 4 + 32
_REGISTRY_PUBLIC_KEY_LINE_RE = re.compile(r"^ssh-ed25519 ([A-Za-z0-9+/]+=*)$")


def _validate_registry_public_key(name: str, value: object) -> None:
    """§8.4 "Role public-key registry" item 4: exactly one OpenSSH
    public-key line of the exact literal form ``ssh-ed25519
    <canonical-base64>`` and **nothing else** -- no comment, no leading or
    trailing whitespace, no embedded tab/newline/carriage return, no
    additional token. The base64 portion uses the RFC 4648 §4 standard
    alphabet with canonical padding, verified by an exact decode/re-encode
    round trip (never a lenient decoder silently accepting a noncanonical
    variant). The decoded bytes must be a structurally valid OpenSSH
    ``ssh-ed25519`` wire-format blob containing exactly one 32-byte ED25519
    public key -- never a different key type, never a truncated or
    padded-out length."""
    if not isinstance(value, str):
        raise AttestationSchemaError(f"{name!r} must be a string, got {type(value).__name__}")
    if "\t" in value or "\n" in value or "\r" in value:
        raise AttestationSchemaError(f"{name!r} contains an embedded tab/newline/carriage return, never valid in a registry public_key: {value!r}")
    if value != value.strip():
        raise AttestationSchemaError(f"{name!r} has leading or trailing whitespace, never valid in a registry public_key: {value!r}")
    match = _REGISTRY_PUBLIC_KEY_LINE_RE.match(value)
    if not match:
        raise AttestationSchemaError(
            f"{name!r} must be exactly 'ssh-ed25519 <canonical-base64>' -- no comment, no additional token: {value!r}"
        )
    encoded = match.group(1)
    try:
        decoded = base64.b64decode(encoded, validate=True)
    except (binascii.Error, ValueError) as exc:
        raise AttestationSchemaError(f"{name!r} base64 portion does not decode as valid base64: {value!r} ({exc})") from exc
    recanonicalized = base64.b64encode(decoded).decode("ascii")
    if recanonicalized != encoded:
        raise AttestationSchemaError(
            f"{name!r} base64 portion is not canonically encoded (RFC 4648 §4 standard alphabet, canonical padding, "
            f"exact round trip required): {value!r}"
        )
    if len(decoded) != _SSH_ED25519_WIRE_FORMAT_LENGTH:
        raise AttestationSchemaError(
            f"{name!r} does not decode to a structurally valid OpenSSH ssh-ed25519 wire-format blob (expected "
            f"exactly {_SSH_ED25519_WIRE_FORMAT_LENGTH} bytes for one 32-byte ED25519 key, got {len(decoded)}): {value!r}"
        )
    type_len = int.from_bytes(decoded[0:4], "big")
    if type_len != len(_SSH_ED25519_WIRE_TYPE) or decoded[4 : 4 + type_len] != _SSH_ED25519_WIRE_TYPE:
        raise AttestationSchemaError(f"{name!r} wire-format key-type field is not the literal 'ssh-ed25519': {value!r}")
    offset = 4 + type_len
    key_len = int.from_bytes(decoded[offset : offset + 4], "big")
    if key_len != 32 or len(decoded) != offset + 4 + key_len:
        raise AttestationSchemaError(f"{name!r} wire-format key-blob length is not exactly one 32-byte ED25519 key: {value!r}")


_REGISTRY_ENTRY_FIELD_VALIDATORS = {
    "role_identity": _validate_ascii_id,
    "role_key_fingerprint": _validate_fingerprint,
    "public_key": _validate_registry_public_key,
}
assert set(_REGISTRY_ENTRY_FIELD_VALIDATORS) == REGISTRY_ENTRY_FIELDS


def _validate_registry_entry(entry: object, index: int) -> None:
    if not isinstance(entry, dict):
        raise AttestationSchemaError(f"registry entry at index {index} must be a JSON object, got {type(entry).__name__}")
    present = set(entry.keys())
    unknown = present - REGISTRY_ENTRY_FIELDS
    if unknown:
        raise AttestationSchemaError(f"registry entry at index {index} carries field(s) outside the closed three-key allowlist: {sorted(unknown)}")
    missing = REGISTRY_ENTRY_FIELDS - present
    if missing:
        raise AttestationSchemaError(f"registry entry at index {index} is missing required field(s): {sorted(missing)}")
    for field, validator in _REGISTRY_ENTRY_FIELD_VALIDATORS.items():
        validator(field, entry[field])


def _validate_expected_role_identities(expected_role_identities: object) -> FrozenSet[str]:
    """Validates and normalizes a caller-supplied **expected role-identity
    set**: an independently sourced, exact roster of the ten role
    identities that ought to populate the registry under test (§8.4 item
    7's "a fresh derivation... never merely trusting the registry file's
    own contents" obligation, applied to *every* one of the ten
    identities, not merely the two topology-critical ones).

    This is a **mandatory** input everywhere registry membership is
    checked -- there is no default, and ``None`` is rejected exactly like
    any other malformed value, never silently treated as "no check
    requested". The caller must source this set from the real,
    out-of-band cohort role assignment -- never from the registry
    document, a registry verification record, or any other artifact this
    module is simultaneously validating; deriving it from the artifact
    under test would let a substituted registry validate itself against
    its own, equally substituted, self-reported membership, which defeats
    the entire point of this check (this function has no way to detect
    that specific misuse -- see the module docstring's "What this tooling
    can and cannot prove").

    Raises :class:`RegistryVerificationError` with a stable code:
    ``EXPECTED_ROLE_IDENTITIES_MISSING`` (``None``),
    ``EXPECTED_ROLE_IDENTITIES_MALFORMED`` (not an iterable of ASCII-id
    strings, or missing one of the two topology-critical identities),
    ``EXPECTED_ROLE_IDENTITIES_DUPLICATE`` (a repeated identity),
    ``EXPECTED_ROLE_IDENTITIES_COUNT_MISMATCH`` (not exactly
    :data:`EXPECTED_REGISTRY_ENTRY_COUNT` unique identities, checked only
    after de-duplication is confirmed absent, so a count-mismatch report
    is never masking an unreported duplicate). Returns the validated set
    as a ``frozenset``."""
    if expected_role_identities is None:
        raise RegistryVerificationError(
            "EXPECTED_ROLE_IDENTITIES_MISSING",
            "expected_role_identities was not supplied -- registry-membership validation refuses to run without "
            "an independently sourced expected identity set (never inferred from the registry document or "
            "verification records under test, and never defaulted); the caller must supply the real, fresh "
            "ten-identity roster explicitly",
        )
    if isinstance(expected_role_identities, (str, bytes)):
        raise RegistryVerificationError(
            "EXPECTED_ROLE_IDENTITIES_MALFORMED",
            f"expected_role_identities must be an iterable of role-identity strings, not a single "
            f"{type(expected_role_identities).__name__}",
        )
    try:
        items = list(expected_role_identities)  # type: ignore[call-overload]
    except TypeError as exc:
        raise RegistryVerificationError("EXPECTED_ROLE_IDENTITIES_MALFORMED", f"expected_role_identities is not iterable: {exc}") from exc

    for item in items:
        try:
            _validate_ascii_id("expected_role_identities element", item)
        except AttestationSchemaError as exc:
            raise RegistryVerificationError("EXPECTED_ROLE_IDENTITIES_MALFORMED", str(exc)) from exc

    seen: Dict[str, int] = {}
    for i, item in enumerate(items):
        assert isinstance(item, str)
        if item in seen:
            raise RegistryVerificationError(
                "EXPECTED_ROLE_IDENTITIES_DUPLICATE", f"expected_role_identities contains duplicate identity {item!r}"
            )
        seen[item] = i

    if len(items) != EXPECTED_REGISTRY_ENTRY_COUNT:
        raise RegistryVerificationError(
            "EXPECTED_ROLE_IDENTITIES_COUNT_MISMATCH",
            f"expected_role_identities must contain exactly {EXPECTED_REGISTRY_ENTRY_COUNT} identities, got {len(items)}",
        )

    for required in (AUDIT_OPERATOR_IDENTITY, COMPARISON_ROLE_IDENTITY):
        if required not in seen:
            raise RegistryVerificationError(
                "EXPECTED_ROLE_IDENTITIES_MALFORMED",
                f"expected_role_identities does not contain the topology-critical identity {required!r}, which "
                "item 8's Record A/Record B verification topology requires",
            )

    return frozenset(items)


def validate_registry_document(document: object, *, expected_role_identities: object) -> Dict[str, object]:
    """Validates ``document`` against §8.4 "Role public-key registry"'s
    frozen exact representation: the closed three-key top-level schema
    (``registry_schema_version``/``key_registry_version``/``entries``),
    the closed three-key entry schema
    (``role_identity``/``role_key_fingerprint``/``public_key``), a casing
    variant of any key rejected exactly as an unknown field, exactly
    :data:`EXPECTED_REGISTRY_ENTRY_COUNT` (ten) entries, no duplicate
    ``role_identity``/``role_key_fingerprint``/``public_key``, strict
    ascending code-point order by ``role_identity`` (item 6 -- the
    identical ordinal ordering rule the stage manifest freezes for
    ``members``, never RFC 8785/JCS's UTF-16 object-key ordering), that
    both topology-critical identities (:data:`AUDIT_OPERATOR_IDENTITY`,
    :data:`COMPARISON_ROLE_IDENTITY`) are present exactly once, and --
    mandatorily, via ``expected_role_identities`` -- that the registry's
    complete ten-identity membership is *exactly* the caller's
    independently sourced roster (:func:`_validate_expected_role_identities`;
    ``REGISTRY_IDENTITY_SET_MISMATCH`` on any deviation).

    ``expected_role_identities`` is a **required keyword argument with no
    default** -- there is no way to call this function without supplying
    it, and supplying ``None`` is refused exactly like any other malformed
    value (see :func:`_validate_expected_role_identities`). This closes an
    implementation completeness gap an earlier version of this function
    left open: that version checked only *count* and the two
    topology-critical identities' literal presence, silently trusting the
    registry's own self-reported membership for the other eight entries
    (discovery operator, screening operator, the §8.1 custodian role, four
    ground-truth reviewers, and the separate §5.1 identity-extraction
    custodian) -- even though §8.4 item 7 already requires the custodian
    to "independently check `entries` against this expected identity set
    -- a fresh derivation... never merely trusting the registry file's own
    contents", and explicitly lists a substituted identity as `STOP`. That
    was not a legitimate specification-boundary refusal (the merged
    document genuinely never freezes those eight identities' literal
    strings, but it does require the *caller* to supply and check them);
    it was a gap in what this function actually enforced. This function
    still does not, and cannot, invent those eight literal strings itself
    -- ``expected_role_identities`` must come from the caller, sourced
    from the real, confidential cohort role assignment, never inferred,
    defaulted, or derived from the registry document under test (a
    self-referential expected set -- one the caller mistakenly builds from
    the very artifact being validated -- is indistinguishable from a
    trustworthy one at this function's boundary; guarding against that
    misuse is the caller's obligation, not a runtime-enforceable one).

    Does **not** independently recompute any ``role_key_fingerprint`` from
    its ``public_key`` -- see
    :func:`recompute_fingerprint_from_registry_public_key` for that (it
    needs ``ssh-keygen`` and a working directory, so it is a separate,
    opt-in call, never folded into this pure schema/structure validator).

    Returns ``document`` unchanged on success."""
    validated_expected_role_identities = _validate_expected_role_identities(expected_role_identities)
    if not isinstance(document, dict):
        raise AttestationSchemaError(f"registry document must be a JSON object, got {type(document).__name__}")
    present = set(document.keys())
    unknown = present - REGISTRY_DOCUMENT_FIELDS
    if unknown:
        raise AttestationSchemaError(f"registry document carries field(s) outside the closed three-key allowlist: {sorted(unknown)}")
    missing = REGISTRY_DOCUMENT_FIELDS - present
    if missing:
        raise AttestationSchemaError(f"registry document is missing required field(s): {sorted(missing)}")

    _validate_ascii_id("registry_schema_version", document["registry_schema_version"])
    _validate_ascii_id("key_registry_version", document["key_registry_version"])

    entries = document["entries"]
    if not isinstance(entries, list):
        raise AttestationSchemaError("registry document 'entries' must be a JSON array")
    if len(entries) != EXPECTED_REGISTRY_ENTRY_COUNT:
        raise AttestationSchemaError(
            f"registry document must contain exactly {EXPECTED_REGISTRY_ENTRY_COUNT} entries, got {len(entries)} -- "
            "fewer or more than ten is STOP, unconditionally, regardless of which identities are present or absent"
        )

    seen_identities: Dict[str, int] = {}
    seen_fingerprints: Dict[str, int] = {}
    seen_public_keys: Dict[str, int] = {}
    previous_sort_key: Optional[Tuple[int, ...]] = None
    for i, entry in enumerate(entries):
        _validate_registry_entry(entry, i)
        identity = entry["role_identity"]
        fingerprint = entry["role_key_fingerprint"]
        public_key = entry["public_key"]
        assert isinstance(identity, str) and isinstance(fingerprint, str) and isinstance(public_key, str)

        if identity in seen_identities:
            raise AttestationSchemaError(f"duplicate role_identity {identity!r} at entries[{i}] and entries[{seen_identities[identity]}]")
        if fingerprint in seen_fingerprints:
            raise AttestationSchemaError(
                f"duplicate role_key_fingerprint {fingerprint!r} at entries[{i}] and entries[{seen_fingerprints[fingerprint]}]"
            )
        if public_key in seen_public_keys:
            raise AttestationSchemaError(f"duplicate public_key at entries[{i}] and entries[{seen_public_keys[public_key]}]")

        sort_key = _codepoint_sort_key(identity)
        if previous_sort_key is not None and sort_key <= previous_sort_key:
            raise AttestationSchemaError(
                f"registry entries are not sorted in strict ascending code-point order by role_identity at index {i}: {identity!r}"
            )
        previous_sort_key = sort_key

        seen_identities[identity] = i
        seen_fingerprints[fingerprint] = i
        seen_public_keys[public_key] = i

    for expected_identity in (AUDIT_OPERATOR_IDENTITY, COMPARISON_ROLE_IDENTITY):
        if expected_identity not in seen_identities:
            raise AttestationSchemaError(
                f"registry document does not contain the topology-critical {expected_identity!r} identity item 8's "
                "Record A/Record B verification topology requires"
            )

    registry_identity_set = frozenset(seen_identities)
    if registry_identity_set != validated_expected_role_identities:
        missing_from_registry = sorted(validated_expected_role_identities - registry_identity_set)
        unexpected_in_registry = sorted(registry_identity_set - validated_expected_role_identities)
        raise RegistryVerificationError(
            "REGISTRY_IDENTITY_SET_MISMATCH",
            "registry document's role_identity set does not exactly equal the independently supplied "
            f"expected_role_identities (missing from registry: {missing_from_registry}; unexpected/substituted in "
            f"registry: {unexpected_in_registry}) -- a missing, additional, or substituted identity relative to "
            "the caller's trusted roster is STOP, regardless of whether the registry is otherwise internally "
            "well-formed",
        )

    return document


def parse_canonical_registry_document(raw_bytes: bytes, *, expected_role_identities: object) -> Tuple[Dict[str, object], str]:
    """Parses and validates ``raw_bytes`` as the frozen exact registry
    document representation: strict RFC 8785/JCS canonical bytes
    (:func:`assert_canonical_bytes`) and the closed ten-entry schema,
    including exact expected-identity-set membership
    (:func:`validate_registry_document`; ``expected_role_identities`` is
    forwarded unchanged and is just as mandatory here). Returns
    ``(document, canonical_sha256_hex)`` -- the recomputed lowercase-hex
    SHA-256 of the exact bytes as given, per item 9's "the lowercase-hex
    SHA-256 of those exact canonical registry bytes" rule.

    This performs **no** comparison against any genesis anchor -- it is
    the pre-genesis parse a registry verifier (item 8) uses before genesis
    exists to compare against. See :func:`verify_registry_document_hash`
    for the post-genesis-anchor comparison."""
    document = assert_canonical_bytes(raw_bytes)
    validate_registry_document(document, expected_role_identities=expected_role_identities)
    return document, hashlib.sha256(raw_bytes).hexdigest()


def verify_registry_document_hash(raw_bytes: bytes, genesis_key_registry_sha256: str, *, expected_role_identities: object) -> Dict[str, object]:
    """Parses and schema-validates ``raw_bytes``
    (:func:`parse_canonical_registry_document`, including the mandatory
    ``expected_role_identities`` membership check) and requires its
    recomputed canonical SHA-256 to equal ``genesis_key_registry_sha256``
    (the value the genesis attestation anchors). Raises
    :class:`RegistryVerificationError` (code ``REGISTRY_HASH_MISMATCH``) on
    mismatch; returns the parsed registry document on success."""
    document, recomputed = parse_canonical_registry_document(raw_bytes, expected_role_identities=expected_role_identities)
    if recomputed != genesis_key_registry_sha256:
        raise RegistryVerificationError(
            "REGISTRY_HASH_MISMATCH",
            f"registry document's recomputed SHA-256 {recomputed!r} does not match the genesis-anchored "
            f"key_registry_sha256 {genesis_key_registry_sha256!r}",
        )
    return document


def recompute_fingerprint_from_registry_public_key(public_key_line: str, work_dir: Path) -> str:
    """Independently recomputes the OpenSSH fingerprint of a registry
    entry's ``public_key`` line (``ssh-keygen -lf``) -- never trusting the
    entry's own ``role_key_fingerprint`` field as ground truth. This is
    item 5's "recomputed from the exact accompanying public_key value ...
    never a separately supplied or cached value" requirement, and item 8's
    identical requirement for the two independent registry verifiers."""
    _validate_registry_public_key("public_key", public_key_line)
    require_ssh_keygen_if_mandatory()
    if not ssh_keygen_available():
        raise SigningVerificationError("ssh-keygen is not available on PATH -- cannot recompute a registry entry's fingerprint")
    key_path = work_dir / f"registry-pubkey-{uuid.uuid4().hex}.pub"
    key_path.write_bytes((public_key_line + "\n").encode("utf-8"))
    return compute_fingerprint(key_path)


def verify_role_key_registered(registry_document: Mapping[str, object], fingerprint: str, *, expected_role_identities: object) -> Dict[str, object]:
    """Returns the single registry entry whose ``role_key_fingerprint``
    equals ``fingerprint``. Raises :class:`RegistryVerificationError`
    (code ``FINGERPRINT_NOT_REGISTERED``) if no entry matches.

    The 2026-09-02 key-registry-schema amendment froze the registry
    document's exact internal representation, closing the contract gap
    this function previously refused to bridge (see the former
    ``RegistryFingerprintMembershipUnspecifiedError``, now removed --
    fingerprint-membership lookup no longer requires inventing an
    unfrozen schema). ``expected_role_identities`` is mandatory and
    forwarded unchanged to :func:`validate_registry_document` -- a lookup
    against a registry whose membership does not match the caller's
    trusted roster is refused before the fingerprint search ever runs."""
    validate_registry_document(dict(registry_document), expected_role_identities=expected_role_identities)
    _validate_fingerprint("fingerprint", fingerprint)
    entries = registry_document["entries"]
    assert isinstance(entries, list)
    matches = [entry for entry in entries if entry["role_key_fingerprint"] == fingerprint]
    if not matches:
        raise RegistryVerificationError(
            "FINGERPRINT_NOT_REGISTERED", f"fingerprint {fingerprint!r} is not a registered member of the supplied registry document"
        )
    assert len(matches) == 1, "validate_registry_document already rejects duplicate role_key_fingerprint values"
    return matches[0]


# =========================================================================
# Registry verification record: frozen exact representation
# (sprints/sprint-15a.md §8.4 "Registry verification record -- frozen
# exact representation" and item 8's Record A/Record B two-record
# pre-genesis verification topology, merged by the 2026-09-02
# key-registry-schema amendment).
# =========================================================================

REGISTRY_VERIFICATION_RECORD_FIELDS = frozenset(
    {
        "verification_schema_version",
        "registry_schema_version",
        "key_registry_version",
        "key_registry_sha256",
        "verifier_role_identity",
        "verifier_role_key_fingerprint",
        "verified_at",
        "verification_result",
        "verified_entries",
    }
)
assert len(REGISTRY_VERIFICATION_RECORD_FIELDS) == 9, "the frozen registry verification record must carry exactly nine fields (sprints/sprint-15a.md §8.4)"

VERIFIED_ENTRY_FIELDS = frozenset({"role_identity", "role_key_fingerprint"})
assert len(VERIFIED_ENTRY_FIELDS) == 2, "a frozen verified_entries element must carry exactly two fields (sprints/sprint-15a.md §8.4)"

VERIFICATION_RESULT_SUCCESS = "success"

_REGISTRY_VERIFICATION_RECORD_SCALAR_FIELD_VALIDATORS = {
    "verification_schema_version": _validate_ascii_id,
    "registry_schema_version": _validate_ascii_id,
    "key_registry_version": _validate_ascii_id,
    "key_registry_sha256": _validate_sha256,
    "verifier_role_identity": _validate_ascii_id,
    "verifier_role_key_fingerprint": _validate_fingerprint,
    "verified_at": _validate_timestamp,
}


def _validate_verification_result(name: str, value: object) -> None:
    if value != VERIFICATION_RESULT_SUCCESS:
        raise AttestationSchemaError(
            f"{name!r} must be exactly the literal {VERIFICATION_RESULT_SUCCESS!r} -- no other value is ever valid "
            f"in a record treated as authorizing (a failed or incomplete verification produces no authorizing "
            f"record at all): got {value!r}"
        )


def _validate_verified_entry(entry: object, index: int) -> None:
    if not isinstance(entry, dict):
        raise AttestationSchemaError(f"verified_entries[{index}] must be a JSON object, got {type(entry).__name__}")
    present = set(entry.keys())
    unknown = present - VERIFIED_ENTRY_FIELDS
    if unknown:
        raise AttestationSchemaError(f"verified_entries[{index}] carries field(s) outside the closed two-key allowlist: {sorted(unknown)}")
    missing = VERIFIED_ENTRY_FIELDS - present
    if missing:
        raise AttestationSchemaError(f"verified_entries[{index}] is missing required field(s): {sorted(missing)}")
    _validate_ascii_id("role_identity", entry["role_identity"])
    _validate_fingerprint("role_key_fingerprint", entry["role_key_fingerprint"])


def validate_registry_verification_record(record: object) -> None:
    """Schema-only validation of one registry verification record (Record
    A or Record B) against the frozen nine-key top-level schema and the
    two-key ``verified_entries`` element schema: closed allowlists
    (a casing variant, alias, or any other/missing/duplicate key is
    ``STOP``), frozen field formats, ``verification_result`` restricted to
    exactly the literal ``"success"``, ``verified_entries`` non-empty,
    duplicate-free, and sorted in strict ascending code-point order by
    ``role_identity`` (the identical ordering rule the registry document's
    own ``entries`` freezes).

    This is schema/structure only -- it does **not** check the two-record
    topology (which record this is, whether it covers the right entries,
    whether its verifier matches a real registry entry): see
    :func:`validate_registry_verification_topology` for that, and
    :func:`verify_registry_verification_record_signature` for the
    signature/sibling binding."""
    if not isinstance(record, dict):
        raise AttestationSchemaError(f"registry verification record must be a JSON object, got {type(record).__name__}")
    present = set(record.keys())
    unknown = present - REGISTRY_VERIFICATION_RECORD_FIELDS
    if unknown:
        raise AttestationSchemaError(f"registry verification record carries field(s) outside the closed nine-key allowlist: {sorted(unknown)}")
    missing = REGISTRY_VERIFICATION_RECORD_FIELDS - present
    if missing:
        raise AttestationSchemaError(f"registry verification record is missing required field(s): {sorted(missing)}")
    for field, validator in _REGISTRY_VERIFICATION_RECORD_SCALAR_FIELD_VALIDATORS.items():
        validator(field, record[field])
    _validate_verification_result("verification_result", record["verification_result"])

    verified_entries = record["verified_entries"]
    if not isinstance(verified_entries, list):
        raise AttestationSchemaError("registry verification record 'verified_entries' must be a JSON array")
    if not verified_entries:
        raise AttestationSchemaError("registry verification record 'verified_entries' must not be empty")

    seen_identities: Dict[str, int] = {}
    seen_fingerprints: Dict[str, int] = {}
    previous_sort_key: Optional[Tuple[int, ...]] = None
    for i, entry in enumerate(verified_entries):
        _validate_verified_entry(entry, i)
        identity = entry["role_identity"]
        fingerprint = entry["role_key_fingerprint"]
        assert isinstance(identity, str) and isinstance(fingerprint, str)
        if identity in seen_identities:
            raise AttestationSchemaError(
                f"duplicate role_identity {identity!r} in verified_entries at index {i} and {seen_identities[identity]}"
            )
        if fingerprint in seen_fingerprints:
            raise AttestationSchemaError(
                f"duplicate role_key_fingerprint {fingerprint!r} in verified_entries at index {i} and {seen_fingerprints[fingerprint]}"
            )
        sort_key = _codepoint_sort_key(identity)
        if previous_sort_key is not None and sort_key <= previous_sort_key:
            raise AttestationSchemaError(
                f"verified_entries is not sorted in strict ascending code-point order by role_identity at index {i}: {identity!r}"
            )
        previous_sort_key = sort_key
        seen_identities[identity] = i
        seen_fingerprints[fingerprint] = i


def validate_registry_verification_topology(
    record_a: Mapping[str, object],
    record_b: Mapping[str, object],
    registry_document: Mapping[str, object],
    registry_canonical_sha256: str,
    *,
    expected_role_identities: object,
) -> None:
    """Validates the complete Record A / Record B two-record verification
    topology against one specific registry snapshot (§8.4 item 8 and
    "Registry verification record -- frozen exact representation").
    Schema-validates both records (:func:`validate_registry_verification_record`)
    and the registry document, **including its mandatory
    expected-identity-set membership check**
    (:func:`validate_registry_document`; ``expected_role_identities`` is
    forwarded unchanged and just as mandatory here -- there is no way to
    validate this topology against a registry whose membership silently
    goes unchecked), first, then checks every substantive cross-binding
    rule:

    - both records' registry-snapshot fields (``registry_schema_version``/
      ``key_registry_version``/``key_registry_sha256``) are identical to
      each other and to the supplied ``registry_document``/
      ``registry_canonical_sha256``;
    - both records carry an identical ``verification_schema_version``;
    - Record A's verifier is the registered :data:`AUDIT_OPERATOR_IDENTITY`;
      Record B's verifier is the registered :data:`COMPARISON_ROLE_IDENTITY`;
      each record's ``verifier_role_key_fingerprint`` matches that
      identity's actual registered ``role_key_fingerprint``;
    - Record A's ``verified_entries`` is exactly the other nine registry
      entries (excluding ``audit_operator``); Record B's is exactly one
      entry (``audit_operator``);
    - every ``verified_entries`` pair in both records matches exactly one
      real registry entry;
    - the union of the two records' verified identities is exactly the
      registry's own ten identities, and their intersection is empty;
    - neither record's verifier appears in its own ``verified_entries``
      (no self-verification).

    **Why there is no separate "union vs. expected_role_identities" check.**
    Because the registry document is validated against
    ``expected_role_identities`` first (raising
    ``REGISTRY_IDENTITY_SET_MISMATCH`` on any deviation, unconditionally,
    before any union is ever computed), the registry's own identity set is
    already provably equal to ``expected_role_identities`` by the time the
    union check below runs -- so the existing ``NON_EXHAUSTIVE_UNION``
    check (union of Record A/B's verified identities vs. the registry's
    own identities) *is* the "verification-record union mismatch" check:
    adding a second, separately-coded check against
    ``expected_role_identities`` directly at that point would be
    unreachable dead code, since the two conditions are mathematically
    identical once the registry-vs-expected equality above holds. This
    mirrors the reasoning already applied elsewhere in this function (see
    the overlap/union-before-shape comment below).

    Raises :class:`RegistryVerificationError` with a stable code on the
    first violation found (see that class's docstring for the complete
    code list). Does **not** verify either record's detached signature --
    see :func:`verify_registry_verification_record_signature` for that,
    since it needs the raw signed bytes/signature/public key, not merely
    the parsed record.

    **Call this, and require it to succeed, before constructing or
    publishing the genesis attestation** -- per item 8, "Genesis must not
    be created unless both records exist, are individually signed, and
    their union covers exactly the ten frozen entries with an empty
    intersection." Once genesis is actually published, also call
    :func:`verify_registry_verification_records_match_genesis`."""
    validate_registry_verification_record(dict(record_a))
    validate_registry_verification_record(dict(record_b))
    validate_registry_document(dict(registry_document), expected_role_identities=expected_role_identities)
    _validate_sha256("registry_canonical_sha256", registry_canonical_sha256)

    registry_entries = registry_document["entries"]
    assert isinstance(registry_entries, list)
    registry_by_identity: Dict[str, Mapping[str, object]] = {entry["role_identity"]: entry for entry in registry_entries}
    all_identities = frozenset(registry_by_identity)

    for label, record in (("Record A", record_a), ("Record B", record_b)):
        for field, expected in (
            ("registry_schema_version", registry_document["registry_schema_version"]),
            ("key_registry_version", registry_document["key_registry_version"]),
            ("key_registry_sha256", registry_canonical_sha256),
        ):
            if record[field] != expected:
                raise RegistryVerificationError(
                    "VERIFICATION_RECORD_SNAPSHOT_MISMATCH",
                    f"{label}'s {field}={record[field]!r} does not match the registry snapshot being verified ({expected!r})",
                )
    if (
        record_a["registry_schema_version"] != record_b["registry_schema_version"]
        or record_a["key_registry_version"] != record_b["key_registry_version"]
        or record_a["key_registry_sha256"] != record_b["key_registry_sha256"]
    ):
        raise RegistryVerificationError(
            "VERIFICATION_RECORD_SNAPSHOT_MISMATCH", "Record A and Record B do not bind to the identical registry snapshot"
        )

    if record_a["verification_schema_version"] != record_b["verification_schema_version"]:
        raise RegistryVerificationError(
            "VERIFICATION_SCHEMA_VERSION_MISMATCH",
            f"Record A verification_schema_version {record_a['verification_schema_version']!r} != Record B "
            f"verification_schema_version {record_b['verification_schema_version']!r}",
        )

    for label, record, expected_identity in (
        ("Record A", record_a, AUDIT_OPERATOR_IDENTITY),
        ("Record B", record_b, COMPARISON_ROLE_IDENTITY),
    ):
        verifier_identity = record["verifier_role_identity"]
        assert isinstance(verifier_identity, str)
        registry_entry = registry_by_identity.get(verifier_identity)
        if registry_entry is None:
            raise RegistryVerificationError(
                "UNREGISTERED_VERIFIER", f"{label}'s verifier_role_identity {verifier_identity!r} is not a registered entry in the supplied registry"
            )
        if record["verifier_role_key_fingerprint"] != registry_entry["role_key_fingerprint"]:
            raise RegistryVerificationError(
                "VERIFIER_FINGERPRINT_MISMATCH", f"{label}'s verifier_role_key_fingerprint does not match {verifier_identity!r}'s registered fingerprint"
            )
        if verifier_identity != expected_identity:
            raise RegistryVerificationError(
                "WRONG_VERIFIER", f"{label}'s verifier_role_identity must be {expected_identity!r}, got {verifier_identity!r}"
            )

    def _covered_identities(record: Mapping[str, object], label: str) -> FrozenSet[str]:
        covered = set()
        entries_list = record["verified_entries"]
        assert isinstance(entries_list, list)
        for entry in entries_list:
            identity = entry["role_identity"]
            fingerprint = entry["role_key_fingerprint"]
            registry_entry = registry_by_identity.get(identity)
            if registry_entry is None or registry_entry["role_key_fingerprint"] != fingerprint:
                raise RegistryVerificationError(
                    "VERIFIED_ENTRY_MISMATCH",
                    f"{label} verifies (role_identity={identity!r}, role_key_fingerprint={fingerprint!r}), which does "
                    "not match exactly one entry in the supplied registry",
                )
            covered.add(identity)
        return frozenset(covered)

    record_a_covered = _covered_identities(record_a, "Record A")
    record_b_covered = _covered_identities(record_b, "Record B")

    if AUDIT_OPERATOR_IDENTITY in record_a_covered:
        raise RegistryVerificationError("SELF_VERIFICATION", "Record A's verifier (audit_operator) verifies its own entry")
    if COMPARISON_ROLE_IDENTITY in record_b_covered:
        raise RegistryVerificationError("SELF_VERIFICATION", "Record B's verifier (comparison_role) verifies its own entry")

    # Overlap and union are checked *before* each record's own exact
    # expected shape, below -- not merely as an equivalent restatement of
    # it. A split that is disjoint and exhaustive but not exactly 9-vs-1
    # (e.g. 8-vs-2) is caught by the shape checks that follow; an overlap
    # or a gap, which the shape checks alone would report only as a less
    # specific "wrong content" mismatch, is caught here first, with the
    # exact offending identity set named.
    overlap = record_a_covered & record_b_covered
    if overlap:
        raise RegistryVerificationError("VERIFIED_ENTRY_OVERLAP", f"Record A and Record B both verify: {sorted(overlap)}")

    union = record_a_covered | record_b_covered
    if union != all_identities:
        missing = all_identities - union
        raise RegistryVerificationError(
            "NON_EXHAUSTIVE_UNION",
            f"the union of Record A's and Record B's verified entries is not exactly the registry's ten identities (missing: {sorted(missing)})",
        )

    expected_record_a_covered = all_identities - {AUDIT_OPERATOR_IDENTITY}
    if record_a_covered != expected_record_a_covered:
        raise RegistryVerificationError(
            "RECORD_A_COVERAGE_MISMATCH", "Record A must verify exactly the other nine registry entries (every entry except audit_operator)"
        )
    expected_record_b_covered = frozenset({AUDIT_OPERATOR_IDENTITY})
    if record_b_covered != expected_record_b_covered:
        raise RegistryVerificationError("RECORD_B_COVERAGE_MISMATCH", "Record B must verify exactly one entry: audit_operator")


def validate_registry_verification_records(
    records: Sequence[Mapping[str, object]],
    registry_document: Mapping[str, object],
    registry_canonical_sha256: str,
    *,
    expected_role_identities: object,
) -> None:
    """Convenience entry point mechanically enforcing item 8's "a wrong
    number of records (not exactly two)" `STOP` condition before
    delegating to :func:`validate_registry_verification_topology` --
    ``expected_role_identities`` is forwarded unchanged and is just as
    mandatory here, so this combined entry point can never validate
    registry membership while silently omitting the expected-identity-set
    check: requires ``records`` to contain **exactly two** registry
    verification records.

    Which supplied record is Record A vs Record B is determined from each
    record's own ``verifier_role_identity`` (never from list position) --
    a caller need not know in advance which physical file is which.

    Raises :class:`RegistryVerificationError` (code
    ``TOO_FEW_VERIFICATION_RECORDS`` or ``THIRD_RECORD_REJECTED``) if
    ``records`` does not contain exactly two. **A third record is never
    valid here, and neither is a routine ``X.verification_receipt.json``
    sibling mistaken for a substantive registry verification record** --
    see "Registry verification record -- frozen exact representation"'s
    explicit "not a third registry verification record" clarification."""
    if len(records) < 2:
        raise RegistryVerificationError(
            "TOO_FEW_VERIFICATION_RECORDS",
            f"exactly two registry verification records (Record A and Record B) are required, got {len(records)}",
        )
    if len(records) > 2:
        raise RegistryVerificationError(
            "THIRD_RECORD_REJECTED",
            f"exactly two registry verification records are ever permitted, got {len(records)} -- a third record "
            "('Record C') is never valid, and neither is a routine X.verification_receipt.json sibling mistaken "
            "for a substantive registry verification record",
        )
    first, second = records
    first_identity = first.get("verifier_role_identity") if isinstance(first, Mapping) else None
    if first_identity == COMPARISON_ROLE_IDENTITY:
        record_a, record_b = second, first
    else:
        record_a, record_b = first, second
    validate_registry_verification_topology(
        record_a, record_b, registry_document, registry_canonical_sha256, expected_role_identities=expected_role_identities
    )


def verify_registry_verification_record_signature(
    record: Mapping[str, object],
    canonical_record_bytes: bytes,
    signing_payload: Mapping[str, object],
    signature: bytes,
    allowed_signers_path: Path,
    work_dir: Path,
) -> None:
    """Verifies the complete signature/sibling binding for one registry
    verification record (§8.4 "Registry verification record", "Canonicalization
    and signing"):

    - ``canonical_record_bytes`` is the exact RFC 8785/JCS canonicalization
      of ``record`` itself (never a stale or separately supplied byte
      string) -- the *artifact* the signing payload describes;
    - the signing payload's ``artifact_sha256``/``byte_length`` bind those
      exact bytes (:func:`verify_artifact_binding`);
    - the signing payload's own ``role_identity``/``role_key_fingerprint``
      equal the record's own ``verifier_role_identity``/
      ``verifier_role_key_fingerprint`` -- never merely a different,
      unrelated signer;
    - the detached signature verifies, under the exact allowed-signers
      file, against the signing payload's own canonical bytes -- the
      "Per-artifact role-signing protocol" signs the payload, never the
      raw artifact bytes directly (:func:`verify_production_signature`,
      the frozen namespace/principal, never a caller-overridable one).

    Raises :class:`RegistryVerificationError` on a record/payload/bytes
    mismatch, :class:`SigningVerificationError` if the signature itself
    fails OpenSSH verification. This function checks *this one record's*
    own signature only -- see :func:`validate_registry_verification_topology`
    for the cross-record/cross-registry topology checks, and
    :func:`validate_registry_verification_records` for the combined,
    exactly-two-records entry point."""
    validate_registry_verification_record(dict(record))
    validate_signing_payload(dict(signing_payload))

    if jcs_canonicalize(dict(record)) != canonical_record_bytes:
        raise RegistryVerificationError(
            "NONCANONICAL_VERIFICATION_RECORD", "the supplied canonical_record_bytes are not the exact RFC 8785/JCS canonicalization of record"
        )
    verify_artifact_binding(signing_payload, canonical_record_bytes)

    if signing_payload["role_identity"] != record["verifier_role_identity"]:
        raise RegistryVerificationError(
            "SIGNING_PAYLOAD_SIGNER_MISMATCH",
            f"signing payload role_identity {signing_payload['role_identity']!r} != record verifier_role_identity "
            f"{record['verifier_role_identity']!r}",
        )
    if signing_payload["role_key_fingerprint"] != record["verifier_role_key_fingerprint"]:
        raise RegistryVerificationError(
            "SIGNING_PAYLOAD_SIGNER_MISMATCH",
            f"signing payload role_key_fingerprint {signing_payload['role_key_fingerprint']!r} != record "
            f"verifier_role_key_fingerprint {record['verifier_role_key_fingerprint']!r}",
        )

    canonical_payload_bytes = jcs_canonicalize(dict(signing_payload))
    if not verify_production_signature(allowed_signers_path, canonical_payload_bytes, signature, work_dir):
        raise SigningVerificationError(
            "registry verification record's detached signature does not verify against the registered public key "
            "under the frozen namespace/principal"
        )


def verify_registry_verification_records_match_genesis(
    record_a: Mapping[str, object],
    record_b: Mapping[str, object],
    genesis_record: Mapping[str, object],
) -> None:
    """Post-genesis check (§8.4 "Registry verification record" rule 2,
    final sentence): once the genesis attestation actually exists, its own
    ``key_registry_version``/``key_registry_sha256`` must match, field-for-
    field and byte-for-byte, the identical registry snapshot both records
    verified pre-genesis -- never a different, later, or re-derived
    registry snapshot. Raises :class:`RegistryVerificationError` (code
    ``GENESIS_ANCHOR_MISMATCH``) on any mismatch.

    Call this once ``genesis_record`` actually exists; before that,
    :func:`validate_registry_verification_topology`'s own snapshot-binding
    check is all that can be checked (there is no genesis yet to compare
    against).

    **Does not take ``expected_role_identities``.** This function never
    receives the registry document or either record's ``verified_entries``
    -- it compares only ``key_registry_version``/``key_registry_sha256``
    scalars between the two records and the genesis record. It performs
    no registry-membership check of its own to omit; that check is
    already mandatory wherever the registry document itself is validated
    (:func:`validate_registry_document`,
    :func:`validate_registry_verification_topology`), which must always
    happen before this function is ever called."""
    validate_attestation_record(dict(genesis_record))
    if genesis_record["sequence_number"] != 0:
        raise AttestationChainError("MISSING_GENESIS", "genesis_record must be the sequence_number == 0 record")
    for label, record in (("Record A", record_a), ("Record B", record_b)):
        if record["key_registry_version"] != genesis_record["key_registry_version"]:
            raise RegistryVerificationError(
                "GENESIS_ANCHOR_MISMATCH",
                f"{label}'s key_registry_version {record['key_registry_version']!r} does not match the "
                f"genesis-anchored value {genesis_record['key_registry_version']!r}",
            )
        if record["key_registry_sha256"] != genesis_record["key_registry_sha256"]:
            raise RegistryVerificationError(
                "GENESIS_ANCHOR_MISMATCH",
                f"{label}'s key_registry_sha256 {record['key_registry_sha256']!r} does not match the "
                f"genesis-anchored value {genesis_record['key_registry_sha256']!r}",
            )


# =========================================================================
# Stage manifest: frozen exact representation (sprints/sprint-15a.md §8.4
# "Stage manifest -- frozen exact representation": printable single-byte
# ASCII paths, ordinal/code-point member ordering -- explicitly distinct
# from, and never altering, RFC 8785's UTF-16 object-key ordering above)
# =========================================================================

_MANIFEST_MEMBER_FIELDS = frozenset({"path", "byte_length", "sha256"})

# Printable US-ASCII, excluding control characters: 0x20-0x7E inclusive.
_MANIFEST_PATH_CHAR_MIN = 0x20
_MANIFEST_PATH_CHAR_MAX = 0x7E


def _validate_manifest_path(path: object) -> None:
    if not isinstance(path, str) or path == "":
        raise StageManifestError(f"member path must be a non-empty string, got {path!r}")
    for ch in path:
        code_point = ord(ch)
        if not (_MANIFEST_PATH_CHAR_MIN <= code_point <= _MANIFEST_PATH_CHAR_MAX):
            raise StageManifestError(
                f"member path {path!r} contains a character (U+{code_point:04X}) outside the frozen printable "
                "single-byte-ASCII set (U+0020-U+007E) -- non-ASCII paths, including non-BMP characters, are "
                "never valid, regardless of NFC normalization"
            )
    # Every valid path is ASCII-only by the check above, so NFC
    # normalization is a no-op here; retained only for continuity with
    # every other string field's frozen format.
    if _nfc(path) != path:
        raise StageManifestError(f"member path {path!r} is not NFC-normalized")
    if "\\" in path:
        raise StageManifestError(f"member path {path!r} contains a backslash, which is never a valid separator")
    if "\x00" in path:
        raise StageManifestError(f"member path {path!r} contains a NUL byte")
    if path.startswith("/"):
        raise StageManifestError(f"member path {path!r} must not begin with '/'")
    if path.startswith("./"):
        raise StageManifestError(f"member path {path!r} must not begin with './'")
    for segment in path.split("/"):
        if segment == "":
            raise StageManifestError(f"member path {path!r} contains an empty segment")
        if segment == ".":
            raise StageManifestError(f"member path {path!r} contains a '.' segment")
        if segment == "..":
            raise StageManifestError(f"member path {path!r} contains a '..' segment")


def _codepoint_sort_key(path: str) -> Tuple[int, ...]:
    """The frozen ``members``-array ordering rule: plain Unicode
    code-point/ordinal comparison -- **not** :func:`_utf16_code_units`.
    For a manifest path (ASCII-only by construction, per
    :func:`_validate_manifest_path`), the two coincide, but this function
    intentionally never calls the UTF-16 helper, to keep the two ordering
    rules structurally independent in code as they are in the frozen
    text."""
    return tuple(ord(ch) for ch in path)


def validate_stage_manifest(
    manifest: object,
    expected_members: Optional[Iterable[Tuple[str, int, str]]] = None,
) -> None:
    """Validates ``manifest`` against §8.4's frozen exact ``members``-array
    representation: exactly one top-level ``members`` key; each member
    exactly ``path``/``byte_length``/``sha256``; ``path`` restricted to
    printable single-byte ASCII (U+0020-U+007E) plus the POSIX-relative
    segment restrictions; strict ascending **code-point** ordering by
    ``path`` (equivalent to ascending unsigned UTF-8 byte order for every
    valid path, and never the UTF-16 ordering RFC 8785 uses for JSON
    object keys); no duplicate normalized path.

    If ``expected_members`` (an iterable of ``(path, byte_length, sha256)``
    triples standing in for "the stage's actual members on the server") is
    supplied, also enforces exact membership -- no member missing from the
    manifest, none present in the manifest but absent from the server, and
    no ``byte_length``/``sha256`` mismatch against the expected value."""
    if not isinstance(manifest, dict) or set(manifest.keys()) != {"members"}:
        raise StageManifestError("a stage manifest must be a JSON object with exactly one top-level key, 'members'")
    members = manifest["members"]
    if not isinstance(members, list):
        raise StageManifestError("'members' must be a JSON array")

    seen_paths: Dict[str, Dict[str, object]] = {}
    previous_sort_key: Optional[Tuple[int, ...]] = None
    for i, member in enumerate(members):
        if not isinstance(member, dict) or set(member.keys()) != _MANIFEST_MEMBER_FIELDS:
            raise StageManifestError(f"member at index {i} must contain exactly the keys path/byte_length/sha256, got {member!r}")
        path, byte_length, sha256 = member["path"], member["byte_length"], member["sha256"]
        _validate_manifest_path(path)
        _validate_nonneg_int("byte_length", byte_length)
        _validate_sha256("sha256", sha256)

        if path in seen_paths:
            raise StageManifestError(f"duplicate normalized member path: {path!r}")

        sort_key = _codepoint_sort_key(path)
        if previous_sort_key is not None and sort_key <= previous_sort_key:
            raise StageManifestError(f"members are not sorted in strict ascending code-point order by path at index {i}: {path!r}")
        previous_sort_key = sort_key
        seen_paths[path] = member

    if expected_members is not None:
        expected_by_path = {path: (byte_length, sha256) for path, byte_length, sha256 in expected_members}
        expected_paths = set(expected_by_path)
        actual_paths = set(seen_paths)
        missing = expected_paths - actual_paths
        extra = actual_paths - expected_paths
        if missing:
            raise StageManifestError(f"manifest is missing expected member(s) present on the server: {sorted(missing)}")
        if extra:
            raise StageManifestError(f"manifest contains member(s) not present on the server: {sorted(extra)}")
        for path, member in seen_paths.items():
            expected_byte_length, expected_sha256 = expected_by_path[path]
            if member["byte_length"] != expected_byte_length or member["sha256"] != expected_sha256:
                raise StageManifestError(f"member {path!r} byte_length/sha256 does not match the actual server-side file")


# =========================================================================
# Mandatory-OpenSSH-environment gate (M4): TRUVIS_REQUIRE_OPENSSH=1 makes
# a missing ssh-keygen a hard failure rather than a silent skip -- CI and
# the future Trust Gate set this; only a developer-only local environment
# may fall back to an explicit, reasoned skip.
# =========================================================================

MANDATORY_OPENSSH_ENV_VAR = "TRUVIS_REQUIRE_OPENSSH"


def openssh_mandatory() -> bool:
    """``True`` iff ``TRUVIS_REQUIRE_OPENSSH=1`` is set in the environment.
    CI and the future Trust Gate are required to set this; a developer-only
    environment without it may still skip OpenSSH-dependent tests with an
    explicit reason when ``ssh-keygen`` is genuinely unavailable."""
    return os.environ.get(MANDATORY_OPENSSH_ENV_VAR) == "1"


def require_ssh_keygen_if_mandatory() -> None:
    """Raises :class:`SigningVerificationError` immediately if mandatory
    mode is set and ``ssh-keygen`` is not on ``PATH`` -- call this at the
    start of any code path (test ``setUpClass``, a real tooling entry
    point) that would otherwise silently no-op or be skipped when
    ``ssh-keygen`` is unavailable, so the absence is a hard failure in
    mandatory mode rather than ever being silently green."""
    if openssh_mandatory() and not ssh_keygen_available():
        raise SigningVerificationError(
            f"{MANDATORY_OPENSSH_ENV_VAR}=1 is set but ssh-keygen is not available on PATH -- mandatory-mode "
            "OpenSSH signing verification cannot be silently skipped"
        )


# =========================================================================
# Synthetic signing: disposable ED25519 keys, OpenSSH `-Y sign`/`-Y verify`
# (sprints/sprint-15a.md §8.4 "Per-artifact role-signing protocol")
#
# Uses the system `ssh-keygen` binary via subprocess rather than adding a
# cryptography dependency: the frozen protocol *is* OpenSSH's own `-Y
# sign`/`-Y verify` signature format under a fixed namespace, not merely
# "an ED25519 signature" in the abstract, so shelling out to the real
# ssh-keygen is the higher-fidelity choice, not a workaround. ssh-keygen
# ships by default on both GitHub-hosted ubuntu-latest and windows-latest
# runners; ssh_keygen_available() lets a caller (or a test) skip cleanly
# where it does not and TRUVIS_REQUIRE_OPENSSH is unset.
#
# Every subprocess call below uses a list-form argv (never shell=True /
# a shell-interpolated string) -- shell-free by construction.
# =========================================================================

SIGNATURE_NAMESPACE = "sprint15a-artifact"
ALLOWED_SIGNERS_PRINCIPAL = "sprint15a-artifact"

_SSH_ED25519_PUBKEY_LINE_RE = re.compile(r"^ssh-ed25519 [A-Za-z0-9+/]+=* ?[^\r\n]*$")
_ALLOWED_SIGNERS_PRINCIPAL_RE = re.compile(r"^[A-Za-z0-9][A-Za-z0-9._-]{0,127}$")


def ssh_keygen_available() -> bool:
    return shutil.which("ssh-keygen") is not None


def generate_disposable_test_keypair(directory: Path, key_name: str, comment: str) -> Tuple[Path, Path]:
    """Generates a brand-new, disposable, **synthetic, test-only** ED25519
    keypair inside ``directory`` (intended to be a pytest ``tmp_path``).
    This is never a Sprint 15A cohort key -- it exists solely to exercise
    this module's OpenSSH signing/verification code paths in isolation.
    The caller owns ``directory``'s lifetime and disposal."""
    require_ssh_keygen_if_mandatory()
    if not ssh_keygen_available():
        raise SigningVerificationError("ssh-keygen is not available on PATH -- cannot generate a synthetic test keypair")
    private_key_path = directory / key_name
    result = subprocess.run(
        ["ssh-keygen", "-t", "ed25519", "-N", "", "-C", comment, "-f", str(private_key_path)],
        capture_output=True,
        text=True,
    )
    if result.returncode != 0:
        raise SigningVerificationError(f"ssh-keygen key generation failed: {result.stderr.strip()}")
    return private_key_path, Path(f"{private_key_path}.pub")


def compute_fingerprint(public_key_path: Path) -> str:
    """The exact OpenSSH ``SHA256:<base64-without-padding>`` fingerprint
    form §8.4's frozen fingerprint format requires, as emitted by
    ``ssh-keygen -lf``."""
    result = subprocess.run(["ssh-keygen", "-lf", str(public_key_path)], capture_output=True, text=True)
    if result.returncode != 0:
        raise SigningVerificationError(f"ssh-keygen fingerprint computation failed: {result.stderr.strip()}")
    for token in result.stdout.split():
        if token.startswith("SHA256:"):
            return token
    raise SigningVerificationError(f"could not locate a SHA256: fingerprint token in ssh-keygen output: {result.stdout!r}")


def build_signing_payload(
    *,
    signing_schema_version: str,
    artifact_id: str,
    artifact_sha256: str,
    byte_length: int,
    role_identity: str,
    role_key_fingerprint: str,
    created_at: str,
    custody_sequence_reference: int,
) -> Dict[str, object]:
    """Assembles and schema-validates the exact, literal eight-key signing
    payload (§8.4 "Attestation-record and signing-payload literal schema,
    frozen")."""
    payload: Dict[str, object] = {
        "signing_schema_version": signing_schema_version,
        "artifact_id": artifact_id,
        "artifact_sha256": artifact_sha256,
        "byte_length": byte_length,
        "role_identity": role_identity,
        "role_key_fingerprint": role_key_fingerprint,
        "created_at": created_at,
        "custody_sequence_reference": custody_sequence_reference,
    }
    validate_signing_payload(payload)
    return payload


def sign_canonical_payload(private_key_path: Path, payload: Mapping[str, object], work_dir: Path) -> bytes:
    """Canonicalizes ``payload`` (RFC 8785/JCS) and signs the exact
    resulting bytes via ``ssh-keygen -Y sign`` under the frozen namespace
    :data:`SIGNATURE_NAMESPACE`. Returns the raw detached-signature bytes.
    Uses a fresh, uniquely-named subdirectory of ``work_dir`` per call, so
    concurrent or repeated calls sharing the same ``work_dir`` never
    collide on a fixed filename."""
    require_ssh_keygen_if_mandatory()
    validate_signing_payload(dict(payload))
    canonical_bytes = jcs_canonicalize(payload)
    call_dir = work_dir / f"sign-{uuid.uuid4().hex}"
    call_dir.mkdir(parents=True, exist_ok=False)
    data_path = call_dir / "signing_payload.jcs.json"
    data_path.write_bytes(canonical_bytes)
    result = subprocess.run(
        ["ssh-keygen", "-Y", "sign", "-f", str(private_key_path), "-n", SIGNATURE_NAMESPACE, str(data_path)],
        capture_output=True,
        text=True,
    )
    if result.returncode != 0:
        raise SigningVerificationError(f"ssh-keygen -Y sign failed: {result.stderr.strip()}")
    return Path(f"{data_path}.sig").read_bytes()


def write_allowed_signers_file(work_dir: Path, public_key_path: Path, principal: str = ALLOWED_SIGNERS_PRINCIPAL) -> Path:
    """Writes an ``allowed_signers`` file suitable for ``ssh-keygen -Y
    verify``, whose sole principal is ``principal`` (the frozen literal
    :data:`ALLOWED_SIGNERS_PRINCIPAL` in real use) mapped to the given
    public key -- never an ad-hoc identity, never one derived from a role
    or candidate name (§8.4 item 3).

    ``principal`` and the public-key line are both validated before
    writing: ``principal`` must match the frozen ASCII-grammar (no
    embedded whitespace or newline), and the public key file's content
    must be a single, well-formed ``ssh-ed25519 <base64> [comment]`` line
    with no embedded newline -- both checks exist specifically to prevent
    allowed-signers injection (a crafted principal or "public key" file
    smuggling in an extra line that grants an unintended, additional
    signer). The file is written as raw bytes with a deterministic ``\\n``
    line ending on every platform, never platform-dependent newline
    translation (``Path.write_text`` would silently emit ``\\r\\n`` on
    Windows)."""
    if not _ALLOWED_SIGNERS_PRINCIPAL_RE.match(principal):
        raise SigningVerificationError(f"principal {principal!r} does not match the frozen ASCII-grammar -- refusing to risk allowed-signers injection")
    raw_pubkey_text = public_key_path.read_text()
    if "\n" in raw_pubkey_text.strip("\n") or "\r" in raw_pubkey_text:
        raise SigningVerificationError("public key file contains more than one line -- refusing to risk allowed-signers injection")
    pubkey_line = raw_pubkey_text.strip()
    if not _SSH_ED25519_PUBKEY_LINE_RE.match(pubkey_line):
        raise SigningVerificationError(f"public key file does not contain a single well-formed 'ssh-ed25519 <base64> [comment]' line: {pubkey_line!r}")
    allowed_signers_path = work_dir / f"allowed_signers-{uuid.uuid4().hex}"
    allowed_signers_path.write_bytes(f"{principal} {pubkey_line}\n".encode("utf-8"))
    return allowed_signers_path


def verify_signature(
    allowed_signers_path: Path,
    principal: str,
    namespace: str,
    canonical_bytes: bytes,
    signature: bytes,
    work_dir: Path,
) -> bool:
    """Runs ``ssh-keygen -Y verify`` for ``canonical_bytes``/``signature``
    against ``allowed_signers_path`` under the given ``principal``/
    ``namespace``. Returns ``True`` only on a genuine successful
    verification (exit code 0) -- never raises for a verification
    *failure*, since a caller legitimately probes wrong-key/
    wrong-principal/wrong-namespace cases and expects a boolean, not an
    exception, for those. Raises :class:`SigningVerificationError` only if
    ``ssh-keygen`` itself cannot be invoked at all. This is the general,
    flexible entry point (arbitrary ``principal``/``namespace``, useful for
    negative testing); production code should prefer
    :func:`verify_production_signature`, which hard-codes the frozen
    values so they can never be accidentally parameterized away."""
    require_ssh_keygen_if_mandatory()
    if not ssh_keygen_available():
        raise SigningVerificationError("ssh-keygen is not available on PATH -- cannot verify a signature")
    sig_path = work_dir / f"verify-{uuid.uuid4().hex}.sig"
    sig_path.write_bytes(signature)
    result = subprocess.run(
        ["ssh-keygen", "-Y", "verify", "-f", str(allowed_signers_path), "-I", principal, "-n", namespace, "-s", str(sig_path)],
        input=canonical_bytes,
        capture_output=True,
    )
    return result.returncode == 0


def verify_production_signature(allowed_signers_path: Path, canonical_bytes: bytes, signature: bytes, work_dir: Path) -> bool:
    """The strict production verifier: identical to :func:`verify_signature`
    except ``principal``/``namespace`` are **hard-coded** to
    :data:`ALLOWED_SIGNERS_PRINCIPAL`/:data:`SIGNATURE_NAMESPACE` and
    cannot be overridden by any caller argument -- eliminating an entire
    class of bug where production code accidentally passes through a
    caller- or config-supplied namespace/principal instead of the one
    §8.4 freezes."""
    return verify_signature(allowed_signers_path, ALLOWED_SIGNERS_PRINCIPAL, SIGNATURE_NAMESPACE, canonical_bytes, signature, work_dir)


def verify_artifact_binding(payload: Mapping[str, object], artifact_bytes: bytes) -> None:
    """Recomputes the artifact's SHA-256 and byte length from
    ``artifact_bytes`` and confirms both match ``payload`` -- the
    custodian's own recompute-and-compare step (§8.4 item 7). Raises
    :class:`SigningVerificationError` on any mismatch."""
    validate_signing_payload(dict(payload))
    actual_sha256 = hashlib.sha256(artifact_bytes).hexdigest()
    actual_length = len(artifact_bytes)
    if payload["artifact_sha256"] != actual_sha256:
        raise SigningVerificationError(
            f"signing payload artifact_sha256 {payload['artifact_sha256']!r} does not match the recomputed hash {actual_sha256!r}"
        )
    if payload["byte_length"] != actual_length:
        raise SigningVerificationError(
            f"signing payload byte_length {payload['byte_length']!r} does not match the recomputed length {actual_length!r}"
        )


def verify_fingerprint_binding(payload: Mapping[str, object], public_key_path: Path) -> None:
    """Recomputes the fingerprint of the actual public key file and
    confirms it matches ``payload["role_key_fingerprint"]`` -- the
    signature-verification counterpart to :func:`verify_artifact_binding`:
    a signature can verify successfully against *some* key while the
    payload's own recorded fingerprint silently names a *different* one,
    if this cross-check is skipped."""
    validate_signing_payload(dict(payload))
    actual_fingerprint = compute_fingerprint(public_key_path)
    if payload["role_key_fingerprint"] != actual_fingerprint:
        raise SigningVerificationError(
            f"signing payload role_key_fingerprint {payload['role_key_fingerprint']!r} does not match the "
            f"recomputed fingerprint {actual_fingerprint!r} of the supplied public key"
        )


@dataclass(frozen=True)
class SyntheticSigningResult:
    payload: Dict[str, object]
    canonical_bytes: bytes
    signature: bytes
    fingerprint: str
    verified: bool


def synthetic_sign_and_verify_artifact(
    *,
    private_key_path: Path,
    public_key_path: Path,
    artifact_bytes: bytes,
    artifact_id: str,
    role_identity: str,
    created_at: str,
    custody_sequence_reference: int,
    work_dir: Path,
    signing_schema_version: str = "v1",
) -> SyntheticSigningResult:
    """End-to-end orchestration, over a **synthetic** artifact and a
    **synthetic, disposable** keypair: build the eight-field payload, sign
    it, verify signature + frozen principal + frozen namespace (via
    :func:`verify_production_signature`), verify the fingerprint binding,
    and separately confirm the artifact-hash/byte-length binding
    (:func:`verify_artifact_binding`)."""
    artifact_sha256 = hashlib.sha256(artifact_bytes).hexdigest()
    fingerprint = compute_fingerprint(public_key_path)
    payload = build_signing_payload(
        signing_schema_version=signing_schema_version,
        artifact_id=artifact_id,
        artifact_sha256=artifact_sha256,
        byte_length=len(artifact_bytes),
        role_identity=role_identity,
        role_key_fingerprint=fingerprint,
        created_at=created_at,
        custody_sequence_reference=custody_sequence_reference,
    )
    verify_artifact_binding(payload, artifact_bytes)
    verify_fingerprint_binding(payload, public_key_path)
    canonical_bytes = jcs_canonicalize(payload)
    signature = sign_canonical_payload(private_key_path, payload, work_dir)
    allowed_signers_path = write_allowed_signers_file(work_dir, public_key_path, ALLOWED_SIGNERS_PRINCIPAL)
    verified = verify_production_signature(allowed_signers_path, canonical_bytes, signature, work_dir)
    return SyntheticSigningResult(
        payload=payload, canonical_bytes=canonical_bytes, signature=signature, fingerprint=fingerprint, verified=verified
    )


# =========================================================================
# GitHub Actions conclusion gate (sprints/sprint-15a.md §8.4 "Mandatory
# successful Actions completion before any custody transition")
# =========================================================================

AUTHORIZING_CONCLUSION = "success"

# Re-runnable *only* for these documented infrastructure outcomes
# ("Failed-run and poisoned-chain policy").
RERUNNABLE_INFRASTRUCTURE_CONCLUSIONS = frozenset({"startup_failure", "timed_out", "cancelled"})

# Semantic, authoritative, and final -- may never be re-run to green.
SEMANTIC_TERMINAL_CONCLUSIONS = frozenset({"failure", "failed", "neutral", "action_required", "stale"})

# Not yet completed -- never authorizing, never poisoning.
NON_TERMINAL_CONCLUSIONS = frozenset({"queued", "in_progress"})

_CONCLUSION_FORMAT_RE = re.compile(r"^[a-z][a-z_]*$")
_GIT_SHA_RE = re.compile(r"^[0-9a-f]{40}$")
_COMMIT_URL_RE = re.compile(r"^https://github\.com/[^/\s]+/[^/\s]+/commit/([0-9a-f]{40})$")
_RUN_URL_RE = re.compile(r"^https://github\.com/[^/\s]+/[^/\s]+/actions/runs/\d+$")


def is_rerun_eligible(conclusion: str) -> bool:
    """``True`` only for the three documented infrastructure outcomes.
    Every semantic terminal conclusion (and every conclusion this module
    has never heard of) is *not* rerun-eligible -- §8.4 treats "any other
    non-`success` conclusion" as semantic and final, so eligibility is an
    allowlist, never a denylist."""
    return conclusion in RERUNNABLE_INFRASTRUCTURE_CONCLUSIONS


@dataclass(frozen=True)
class ActionsRunRecord:
    """The custodian's recorded evidence for one post-merge, push-triggered
    validation run, per §8.4's required-fields list, bound to the specific
    attestation ``sequence_number`` it validates."""

    sequence_number: int
    commit_url: str
    commit_sha: str
    workflow_run_url: str
    github_server_timestamp: str
    branch: str
    conclusion: Optional[str]  # None means "no completed run recorded yet"


@dataclass(frozen=True)
class PublicationRunEvidence:
    """Immutable, per-attestation record of pre-merge and post-merge
    validation-run conclusions, used to derive whether the canonical chain
    is poisoned (§8.4 "Failed-run and poisoned-chain policy"). **No default
    values** on either conclusion field -- a caller must state
    ``post_merge_conclusion=None`` explicitly for "not yet run" rather than
    have that meaning fall out of an omitted argument, so a missing field
    is a ``TypeError`` at construction time, never a silent default."""

    sequence_number: int
    pre_merge_conclusion: str
    post_merge_conclusion: Optional[str]


def _evidence_is_poisoning(evidence: PublicationRunEvidence) -> bool:
    return evidence.pre_merge_conclusion == AUTHORIZING_CONCLUSION and evidence.post_merge_conclusion in SEMANTIC_TERMINAL_CONCLUSIONS


def compute_chain_poison_status(history: Sequence[PublicationRunEvidence]) -> Optional[PublicationRunEvidence]:
    """Returns the first poisoning evidence record found (ordered by
    ``sequence_number``), or ``None`` if the supplied ``history`` contains
    no poisoning event. This function trusts ``history`` as given -- it
    is recomputed fresh from the supplied, immutable evidence tuples every
    call, never cached, and there is no "clear" operation anywhere in this
    module: constructing a new, different-looking ``history`` (omitting
    the poisoning entry, "replacing" it with a fabricated success, or
    appending a revert/correction/follow-up entry) does not un-poison a
    *real* chain -- it only produces a different, and in that case
    dishonest, input to this pure function. Detecting such fabrication
    requires the caller to source ``history`` from an authoritative,
    tamper-evident custody log; this module cannot do that on its own,
    and does not claim to."""
    ordered = sorted(history, key=lambda e: e.sequence_number)
    for evidence in ordered:
        if _evidence_is_poisoning(evidence):
            return evidence
    return None


def raise_if_chain_poisoned(history: Sequence[PublicationRunEvidence]) -> None:
    """Raises :class:`PoisonedChainError` if
    :func:`compute_chain_poison_status` finds a poisoning event anywhere
    in ``history``. Standalone entry point for callers that want the
    poison check in isolation; :func:`authorize_custody_transition` also
    calls this internally (mandatorily, not as a separately-rememberable
    step) as part of its own history validation."""
    poisoning_evidence = compute_chain_poison_status(history)
    if poisoning_evidence is not None:
        raise PoisonedChainError(
            f"the canonical attestation chain is poisoned at sequence_number {poisoning_evidence.sequence_number} "
            "(a successful pre-merge validation was followed by a semantic post-merge validation failure) -- "
            "cohort-wide STOP; no revert commit, follow-up attestation, replacement, force-push, deletion, "
            "rerun-to-green, or other continuation can authorize further use of this chain"
        )


def authorize_custody_transition(
    run: ActionsRunRecord,
    *,
    expected_commit_sha: str,
    expected_branch: str,
    publication_history: Sequence[PublicationRunEvidence],
) -> None:
    """The sole authorization path for any custody transition. Requires
    and validates the **complete** publication history for every
    attestation from genesis up to and including ``run.sequence_number``
    (missing or incomplete history is ``STOP``, never interpreted as
    "unpoisoned"), refuses authorization if
    :func:`compute_chain_poison_status` finds *any* canonical post-merge
    poisoning event anywhere in that history (not merely at
    ``run.sequence_number`` itself), cross-checks ``run`` against its own
    entry in ``publication_history`` for internal consistency, structurally
    validates ``run``'s URLs/timestamp/conclusion format, and only then
    requires a completed run for the exact commit SHA on the exact
    canonical branch with conclusion exactly ``"success"``. This is
    allowlist-based on conclusion -- only ``"success"`` authorizes -- so
    any conclusion this module has never seen (a future GitHub addition
    included) fails closed automatically, exactly as §8.4 requires ("this
    list is a non-exhaustive enumeration... not a closed set to be matched
    against")."""
    for field_name, value in (
        ("commit_url", run.commit_url),
        ("commit_sha", run.commit_sha),
        ("workflow_run_url", run.workflow_run_url),
        ("github_server_timestamp", run.github_server_timestamp),
        ("branch", run.branch),
    ):
        if not value:
            raise ActionsGateError("MISSING_RECORDED_FIELD", f"required field {field_name!r} was not recorded")

    if not _GIT_SHA_RE.match(run.commit_sha):
        raise ActionsGateError("MALFORMED_COMMIT_SHA", f"run.commit_sha {run.commit_sha!r} is not a 40-character lowercase hex git SHA")
    if not _GIT_SHA_RE.match(expected_commit_sha):
        raise ActionsGateError("MALFORMED_COMMIT_SHA", f"expected_commit_sha {expected_commit_sha!r} is not a 40-character lowercase hex git SHA")
    commit_url_match = _COMMIT_URL_RE.match(run.commit_url)
    if not commit_url_match:
        raise ActionsGateError("MALFORMED_COMMIT_URL", f"run.commit_url {run.commit_url!r} is not a well-formed GitHub commit URL")
    if commit_url_match.group(1) != run.commit_sha:
        raise ActionsGateError(
            "COMMIT_URL_SHA_MISMATCH", f"run.commit_url embeds SHA {commit_url_match.group(1)!r}, but run.commit_sha is {run.commit_sha!r}"
        )
    if not _RUN_URL_RE.match(run.workflow_run_url):
        raise ActionsGateError("MALFORMED_WORKFLOW_RUN_URL", f"run.workflow_run_url {run.workflow_run_url!r} is not a well-formed GitHub Actions run URL")
    try:
        _validate_timestamp("github_server_timestamp", run.github_server_timestamp)
    except AttestationSchemaError as exc:
        raise ActionsGateError("INVALID_TIMESTAMP", str(exc)) from exc
    if run.conclusion is not None and not _CONCLUSION_FORMAT_RE.match(run.conclusion):
        raise ActionsGateError("MALFORMED_CONCLUSION", f"run.conclusion {run.conclusion!r} is not a lowercase snake_case conclusion string")

    if not publication_history:
        raise ActionsGateError(
            "MISSING_PUBLICATION_HISTORY",
            "no publication history supplied -- cannot verify the chain has never been poisoned; missing history "
            "is STOP, never interpreted as unpoisoned",
        )
    history_by_sequence = {e.sequence_number: e for e in publication_history}
    if len(history_by_sequence) != len(publication_history):
        raise ActionsGateError("INCOMPLETE_PUBLICATION_HISTORY", "publication_history contains more than one entry for the same sequence_number")
    required_sequences = set(range(0, run.sequence_number + 1))
    missing_sequences = required_sequences - set(history_by_sequence)
    if missing_sequences:
        raise ActionsGateError(
            "INCOMPLETE_PUBLICATION_HISTORY", f"publication history is missing evidence for sequence_number(s) {sorted(missing_sequences)}"
        )
    own_evidence = history_by_sequence[run.sequence_number]
    if own_evidence.post_merge_conclusion != run.conclusion:
        raise ActionsGateError(
            "HISTORY_RUN_MISMATCH",
            f"run.conclusion {run.conclusion!r} does not match publication_history's recorded "
            f"post_merge_conclusion {own_evidence.post_merge_conclusion!r} for sequence_number {run.sequence_number}",
        )

    raise_if_chain_poisoned(publication_history)

    if run.conclusion is None:
        raise ActionsGateError("NO_COMPLETED_RUN", "no completed run exists for the exact commit SHA under review")
    if run.commit_sha != expected_commit_sha:
        raise ActionsGateError(
            "SHA_MISMATCH", f"run's commit SHA {run.commit_sha!r} does not match the attestation commit under review {expected_commit_sha!r}"
        )
    if run.branch != expected_branch:
        raise ActionsGateError("BRANCH_MISMATCH", f"run's branch {run.branch!r} does not match the canonical branch {expected_branch!r}")
    if run.conclusion != AUTHORIZING_CONCLUSION:
        raise ActionsGateError(
            "NON_AUTHORIZING_CONCLUSION", f"conclusion {run.conclusion!r} is not 'success' -- it never authorizes a custody transition"
        )


# =========================================================================
# Composed raw-history validator: the single publication-facing entry
# point (§8.4, synthesizing "Attestation chain integrity", "Attestation-
# record and signing-payload literal schema, frozen", and the custodian
# non-derivation obligation into one call over raw committed bytes).
# =========================================================================


def validate_published_attestation_history(
    raw_records: Sequence[bytes],
    *,
    non_derivation_receipts: Optional[Mapping[str, CustodianNonDerivationReceipt]] = None,
    previously_used_receipt_ids: Optional[FrozenSet[str]] = None,
) -> Tuple[Dict[str, object], ...]:
    """The single publication-facing entry point: takes the **ordered raw
    committed attestation bytes** (genesis first) and:

    1. rejects duplicate JSON keys, an invalid/BOM-prefixed encoding, and
       the non-standard NaN/Infinity constants (:func:`assert_canonical_bytes`);
    2. verifies each record's bytes are exact RFC 8785/JCS canonical form
       (also :func:`assert_canonical_bytes`);
    3. validates each record against the closed, literal eleven-key schema
       (:func:`validate_attestation_chain`, which calls
       :func:`validate_attestation_record` per record);
    4. validates the complete chain -- genesis/sequence/predecessor
       linkage and genesis-anchor (``schema_version``/``key_registry_*``)
       consistency (also :func:`validate_attestation_chain`);
    5. if ``non_derivation_receipts`` is supplied, applies the custodian
       receipt/reuse-history check to every record whose ``artifact_id``
       has a matching receipt (:func:`validate_publication_ready`) --
       ``previously_used_receipt_ids`` is then mandatory, per
       :func:`require_custodian_non_derivation_receipt`.

    Callers never need to remember a separate byte-level validation call
    -- everything above is reachable through this one function.

    **What this function cannot prove, because it has no Git/GitHub
    repository context at all** (it never clones, fetches, or inspects a
    repository -- it only sees the byte strings it was handed):

    - that each attestation truly corresponds to exactly one file in
      exactly one commit;
    - that each attestation PR added exactly one new attestation file and
      touched nothing else;
    - that no workflow/configuration/setup file was ever changed by an
      attestation PR;
    - that publication actually used squash merge, producing genuinely
      linear history;
    - that the canonical branch is actually protected, with no
      administrator bypass, in the live repository (§8.4 "Public-
      repository creation gate" is an empirical, on-the-live-repository
      check this pure function cannot perform);
    - that each attestation truly started from a fresh, ephemeral branch
      cut from the current canonical `HEAD`;
    - the exact real GitHub PR/commit topology (PR numbers, branch names,
      merge commit parentage) behind the supplied bytes.

    Establishing those requires actual Git/GitHub API inspection of the
    live repository (the Trust Gate's job, §11 item 5/6) -- this function
    validates only the *content* it was given, honestly and completely,
    never the surrounding repository topology it was never shown."""
    decoded_records = tuple(assert_canonical_bytes(raw) for raw in raw_records)
    validate_attestation_chain(decoded_records)

    if non_derivation_receipts is not None:
        for record in decoded_records:
            artifact_id = record["artifact_id"]
            assert isinstance(artifact_id, str)
            receipt = non_derivation_receipts.get(artifact_id)
            if receipt is not None:
                validate_publication_ready(record, receipt, previously_used_receipt_ids=previously_used_receipt_ids)

    return decoded_records
