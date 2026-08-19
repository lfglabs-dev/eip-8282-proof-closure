#!/usr/bin/env python3
"""Fail-closed metadata and pin checks. Lean proofs remain authoritative."""
from __future__ import annotations

import hashlib
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CANONICAL = ["P-SUBMIT-1", "P-DRAIN-1", "P-CONTROL-1"]
STATUSES = {"OPEN", "PARTIAL", "CHECKED"}


def die(msg: str) -> None:
    raise SystemExit(f"audit metadata error: {msg}")


def load_json(path: Path):
    return json.loads(path.read_text(encoding="utf-8"))


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    g = load_json(ROOT / "audit/guarantees.yaml")
    lock = load_json(ROOT / "audit/artifacts.lock.json")
    assumptions = load_json(ROOT / "audit/assumptions.yaml")
    if g.get("schema") != "eip-8282-assurance-contract-v1":
        die("guarantees schema")
    if lock.get("schema") != "eip-8282-artifacts-lock-v1":
        die("lock schema")
    ids = [row["id"] for row in g["guarantees"]]
    if ids != CANONICAL:
        die(f"canonical ids {ids}")
    for row in g["guarantees"]:
        if row["abstract"]["status"] not in STATUSES:
            die(f"{row['id']} abstract status")
        if row["verity"]["status"] not in STATUSES:
            die(f"{row['id']} verity status")
        if row["verity"]["status"] == "CHECKED":
            die(f"{row['id']} verity must not be CHECKED until a theorem exists")
        if row["abstract"]["status"] != "CHECKED":
            die(f"{row['id']} abstract should be CHECKED for this campaign")
    for rel, expected in lock["files"].items():
        got = sha256(ROOT / rel)
        if got != expected:
            die(f"pin mismatch {rel}: {got} != {expected}")
    assumed = {a["id"] for a in assumptions["assumptions"]}
    for row in g["guarantees"]:
        for a in row["assumptions"]:
            if a not in assumed:
                die(f"{row['id']} unknown assumption {a}")
    print("audit-check ok")


if __name__ == "__main__":
    main()
