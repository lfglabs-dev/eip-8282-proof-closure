#!/usr/bin/env python3
"""Fail-closed metadata and pin checks. Lean proofs remain authoritative."""
from __future__ import annotations

import hashlib
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CANONICAL = ["P-SUBMIT-1", "P-DRAIN-1", "P-CONTROL-1"]
STATUSES = {"OPEN", "PARTIAL", "CHECKED"}

# Lean hex literal -> the pinned artifact it must reproduce exactly.
BYTECODE_LITERALS = {
    "depositRuntimeHex": "pinned/bytecode/builder_deposits/main.hex",
    "depositInitHex": "pinned/bytecode/builder_deposits/ctor.hex",
    "exitRuntimeHex": "pinned/bytecode/builder_exits/main.hex",
    "exitInitHex": "pinned/bytecode/builder_exits/ctor.hex",
}


def die(msg: str) -> None:
    raise SystemExit(f"audit metadata error: {msg}")


def load_json(path: Path):
    return json.loads(path.read_text(encoding="utf-8"))


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def lean_hex_literals(source: str) -> dict[str, str]:
    """Extract `def <name>Hex : String := "..." ++ "..."` bodies from Bytecode.lean."""
    out: dict[str, str] = {}
    for name in BYTECODE_LITERALS:
        m = re.search(rf"^def {name} : String :=\n((?:.*\n)*?)\n", source, re.MULTILINE)
        if not m:
            die(f"Bytecode.lean has no literal {name}")
        out[name] = "".join(re.findall(r'"([0-9a-fA-F]*)"', m.group(1)))
    return out


def check_bytecode_literals() -> None:
    """The bytes Lean executes must be the pinned bytes, not a paraphrase."""
    source = (ROOT / "Eip8282/Audit/Bytecode.lean").read_text(encoding="utf-8")
    literals = lean_hex_literals(source)
    for name, rel in BYTECODE_LITERALS.items():
        pinned = (ROOT / rel).read_text(encoding="utf-8").strip()
        if pinned.startswith("0x"):
            pinned = pinned[2:]
        got = literals[name]
        if got.lower() != pinned.lower():
            die(
                f"{name} does not match {rel} "
                f"(lean {len(got)//2} bytes, pinned {len(pinned)//2} bytes)"
            )


def check_theorems_exist(g) -> None:
    """Every theorem named in the metadata must exist in a Lean source file."""
    sources = "\n".join(
        p.read_text(encoding="utf-8") for p in (ROOT / "Eip8282").rglob("*.lean")
    )
    for row in g["guarantees"]:
        named = [(row["id"], row.get("parent"))]
        for layer in ("abstract", "evm", "verity"):
            block = row.get(layer)
            if not block:
                continue
            named.append((layer, block.get("theorem")))
            kill = block.get("kill_line")
            if kill:
                named.append((f"{layer}.kill_line", kill.get("theorem")))
        for where, full in named:
            if not full:
                continue
            short = full.rsplit(".", 1)[-1]
            if not re.search(rf"^theorem {re.escape(short)}\b", sources, re.MULTILINE):
                die(f"{row['id']} {where} names missing theorem {full}")


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
        evm = row.get("evm")
        if evm is not None:
            if evm["status"] not in STATUSES:
                die(f"{row['id']} evm status")
            if evm["status"] == "CHECKED":
                if not evm.get("theorem"):
                    die(f"{row['id']} evm CHECKED without a theorem")
                if not evm.get("kill_line", {}).get("theorem"):
                    die(f"{row['id']} evm CHECKED without a kill-line theorem")
                if evm.get("scope") != "CONCRETE_TRACES":
                    die(f"{row['id']} evm scope must be declared CONCRETE_TRACES")
                if row.get("parent") != evm["theorem"]:
                    die(f"{row['id']} evm is CHECKED so parent must be the evm theorem")
    check_bytecode_literals()
    check_theorems_exist(g)
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
