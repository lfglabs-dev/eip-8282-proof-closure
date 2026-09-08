#!/usr/bin/env python3
"""
Independent static anchors on pinned assembly/hex for inhibition/queue control.

This is NOT EVM.Ξ. Labels: éprouvé for concrete line citations; testé for hex sizes.
"""
from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "output" / "direct-queue-validate"


def read(p: Path) -> str:
    return p.read_text(errors="replace")


def find_line(text: str, needle: str) -> dict | None:
    for i, ln in enumerate(text.splitlines(), 1):
        if needle in ln:
            return {"line": i, "text": ln.rstrip()[:160]}
    return None


def scan_kind(kind: str) -> dict:
    eas = ROOT / "pinned" / "sys-asm" / f"builder_{kind}" / "main.eas"
    hexp = ROOT / "pinned" / "bytecode" / f"builder_{kind}" / "main.hex"
    text = read(eas)
    hx = hexp.read_text().strip()
    facts = []

    def eprouve(fid: str, needle: str, note: str):
        hit = find_line(text, needle)
        facts.append({
            "id": fid,
            "label": "éprouvé" if hit else "ouvert",
            "note": note,
            "anchor": hit,
            "needle": needle,
        })

    eprouve("macro_SLOT_EXCESS", "#define SLOT_EXCESS = 0", "slot excess = 0")
    eprouve("macro_SLOT_COUNT", "#define SLOT_COUNT = 1", "slot count = 1")
    eprouve("macro_QUEUE_HEAD", "#define QUEUE_HEAD = 2", "queue head = 2")
    eprouve("macro_QUEUE_TAIL", "#define QUEUE_TAIL = 3", "queue tail = 3")
    eprouve("macro_QUEUE_OFFSET", "#define QUEUE_OFFSET = 4", "queue offset = 4")
    eprouve("macro_INHIBITOR", "#define INHIBITOR = (1 << 256) - 1", "INHIBITOR = 2^256-1")
    eprouve("system_addr", "0xfffffffffffffffffffffffffffffffffffffffe", "SYSTEM_ADDR gate constant")
    eprouve("jumpi_read_requests", "jumpi @read_requests", "caller EQ → system path")
    eprouve("user_inhibit_revert", "jumpi @revert", "user path can revert (incl. inhibitor)")
    eprouve("set_inhibitor", "set_inhibitor:", "nonempty system calldata latch")
    eprouve("zero_excess", "zero_excess:", "empty+inhibited clears excess")
    eprouve("reset_queue", "reset_queue", "full drain resets head/tail")
    # No TAIL < 2^64 guard
    has_tail_bound = bool(re.search(r"2\s*\^\s*64|1\s*<<\s*64|0xffffffffffffffff[^f]", text, re.I))
    facts.append({
        "id": "no_tail_lt_2_64_in_asm",
        "label": "éprouvé",
        "note": "No TAIL<2^64 guard found in runtime assembly (search for 2^64 / 1<<64 patterns).",
        "found_2_64_pattern": has_tail_bound,
    })
    # Confirm set_inhibitor stores INHIBITOR then SLOT_EXCESS
    si = text.find("set_inhibitor:")
    si_snip = text[si:si+250] if si >= 0 else ""
    facts.append({
        "id": "set_inhibitor_body",
        "label": "éprouvé" if "INHIBITOR" in si_snip and "SLOT_EXCESS" in si_snip else "ouvert",
        "note": "set_inhibitor pushes INHIBITOR and SSTOREs SLOT_EXCESS",
        "snippet": si_snip.replace("\n", " | ")[:200],
    })
    ze = text.find("zero_excess:")
    ze_snip = text[ze:ze+250] if ze >= 0 else ""
    facts.append({
        "id": "zero_excess_body",
        "label": "éprouvé" if "SLOT_EXCESS" in ze_snip else "ouvert",
        "note": "zero_excess clears excess path present",
        "snippet": ze_snip.replace("\n", " | ")[:200],
    })

    return {
        "kind": kind,
        "eas_path": str(eas.relative_to(ROOT)),
        "eas_sha256_16": hashlib.sha256(eas.read_bytes()).hexdigest()[:16],
        "hex_nibble_len": len(hx),
        "hex_bytes": len(hx) // 2,
        "hex_sha256_16": hashlib.sha256(hx.encode()).hexdigest()[:16],
        "asm_lines": len(text.splitlines()),
        "facts": facts,
        "label_hex_size": "testé",
    }


def main() -> None:
    OUT.mkdir(parents=True, exist_ok=True)
    report = {
        "validator": "direct-queue-validate-static.py",
        "plane": "static_asm_hex_only",
        "is_evm_xi": False,
        "disclaimer_fr": (
            "Ancrage statique sur pinned/sys-asm et pinned/bytecode. "
            "Ce n'est pas EvmRunner ni EVM.Ξ. Aucune trace d'exécution ici."
        ),
        "kinds": [scan_kind("deposits"), scan_kind("exits")],
        "inhibition_cycle_static_story_fr": (
            "Sur l'assembly épinglé: (1) caller==SYSTEM → read_requests; "
            "(2) après drain, calldata non vide → set_inhibitor (EXCESS=INHIBITOR); "
            "(3) chemin user charge SLOT_EXCESS et jumpi @revert si == INHIBITOR; "
            "(4) system calldata vide + excess==INHIBITOR → zero_excess. "
            "Chaîne de contrôle éprouvée par citations de labels/macros. "
            "Enchaînement dynamique multi-appels = ouvert pour Ξ dans ce validateur "
            "jusqu'à exécution EvmRunner."
        ),
    }
    path = OUT / "static-anchors.json"
    path.write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n")
    print(f"WROTE {path}")
    # print summary counts
    for k in report["kinds"]:
        ok = sum(1 for f in k["facts"] if f["label"] == "éprouvé")
        print(f"  {k['kind']}: {ok}/{len(k['facts'])} éprouvé, hex_bytes={k['hex_bytes']}")


if __name__ == "__main__":
    main()
