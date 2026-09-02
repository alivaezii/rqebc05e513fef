"""Trusted, read-only validation runner. Frozen after setup -- any change
to this file after freeze is itself a semantic failure for any PR that
proposes it (enforced by the frozen-path check below and by branch
protection requiring this exact check to pass).

Two modes:
  pre-merge  <repo_root> <changed_files_json> <candidate_data_dir>
  post-merge <repo_root>

pre-merge validates a *proposed* history (existing canonical entries plus
exactly one new candidate file, fetched as inert data -- never executed,
imported, or sourced). post-merge validates the *actual* canonical history
already on the canonical branch after a merge.
"""
from __future__ import annotations

import json
import re
import sys
from pathlib import Path
from typing import Dict, List

import validator_source as v

RECORD_PATH_RE = re.compile(r"^entries/([A-Za-z0-9][A-Za-z0-9._-]{0,127})\.json$")

FROZEN_SETUP_PATHS = {
    "validator_source.py",
    "check.py",
}
FROZEN_SETUP_PREFIXES = (".github/",)


def fail(reason: str) -> None:
    print(f"SEMANTIC_FAILURE: {reason}")
    sys.exit(1)


def is_frozen_path(path: str) -> bool:
    if path in FROZEN_SETUP_PATHS:
        return True
    return any(path.startswith(prefix) for prefix in FROZEN_SETUP_PREFIXES)


def load_existing_entries(entries_dir: Path) -> List[Dict[str, object]]:
    records: List[Dict[str, object]] = []
    if not entries_dir.is_dir():
        return records
    for p in sorted(entries_dir.glob("*.json")):
        raw = p.read_bytes()
        try:
            record = v.assert_canonical_bytes(raw)
        except v.NoncanonicalSerializationError as exc:
            fail(f"existing canonical entry {p.name} is not canonical: {exc}")
            raise AssertionError("unreachable")
        try:
            v.validate_attestation_record(record)
        except v.AttestationSchemaError as exc:
            fail(f"existing canonical entry {p.name} fails schema: {exc}")
            raise AssertionError("unreachable")
        records.append(record)
    return records


def run_pre_merge(repo_root: Path, changed_files_path: Path, candidate_data_dir: Path) -> None:
    entries_dir = repo_root / "entries"
    changed_files = json.loads(changed_files_path.read_text(encoding="utf-8"))

    if len(changed_files) != 1:
        fail(f"proposed change touches {len(changed_files)} file(s); exactly one is required")

    entry = changed_files[0]
    path = entry["filename"]
    status = entry["status"]

    if is_frozen_path(path):
        fail(f"path {path!r} is a frozen setup/workflow/config path; it may never change after freeze")

    if status != "added":
        fail(f"path {path!r} has status {status!r}; only a pure addition is permitted")

    match = RECORD_PATH_RE.match(path)
    if not match:
        fail(f"path {path!r} does not match the frozen opaque grammar entries/<id>.json")
    path_artifact_id = match.group(1)

    candidate_file = candidate_data_dir / Path(path).name
    if not candidate_file.is_file():
        fail(f"candidate content for {path!r} was not fetched as data")

    raw = candidate_file.read_bytes()
    try:
        new_record = v.assert_canonical_bytes(raw)
    except v.NoncanonicalSerializationError as exc:
        fail(f"candidate file is not canonical UTF-8 RFC 8785/JCS JSON: {exc}")
        raise AssertionError("unreachable")

    try:
        v.validate_attestation_record(new_record)
    except v.AttestationSchemaError as exc:
        fail(f"candidate record fails the frozen eleven-field schema: {exc}")

    if new_record.get("artifact_id") != path_artifact_id:
        fail(f"path artifact id {path_artifact_id!r} does not match record artifact_id {new_record.get('artifact_id')!r}")

    try:
        v.assert_no_forbidden_semantic_material(new_record)
    except v.ForbiddenSemanticMaterialError as exc:
        fail(f"candidate record contains forbidden semantic material: {exc}")

    existing = load_existing_entries(entries_dir)
    existing_ids = {r["artifact_id"] for r in existing}
    if new_record["artifact_id"] in existing_ids:
        fail(f"artifact_id {new_record['artifact_id']!r} already exists in the canonical history")

    proposed_history = sorted(existing + [new_record], key=lambda r: r["sequence_number"])
    try:
        v.validate_attestation_chain(proposed_history)
    except v.AttestationChainError as exc:
        fail(f"proposed canonical history is invalid: {exc}")

    print(f"SEMANTIC_SUCCESS: proposed history of {len(proposed_history)} record(s) is valid")


def run_post_merge(repo_root: Path) -> None:
    entries_dir = repo_root / "entries"
    existing = load_existing_entries(entries_dir)
    if not existing:
        fail("no canonical entries present after merge")

    existing_sorted = sorted(existing, key=lambda r: r["sequence_number"])
    try:
        v.validate_attestation_chain(existing_sorted)
    except v.AttestationChainError as exc:
        fail(f"canonical history is invalid: {exc}")

    print(f"SEMANTIC_SUCCESS: canonical history of {len(existing_sorted)} record(s) is valid")


def main() -> None:
    mode = sys.argv[1]
    repo_root = Path(sys.argv[2])
    if mode == "pre-merge":
        run_pre_merge(repo_root, Path(sys.argv[3]), Path(sys.argv[4]))
    elif mode == "post-merge":
        run_post_merge(repo_root)
    else:
        fail(f"unknown mode {mode!r}")
    sys.exit(0)


if __name__ == "__main__":
    main()
