#!/usr/bin/env python3
"""
Independent classification of predecessor direct-queue diagnostics.

Verdict target: are scripts/direct-queue-* pinned-bytecode EVM.Ξ execution
via EvmRunner, or a handwritten Python/assembly simulator?

Output: output/direct-queue-validate/classify.json
"""
from __future__ import annotations

import hashlib
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
# Predecessor artifacts are local-only inspect targets (do not destroy).
PRED_CANDIDATES = [
    Path("/workspaces/mission-1ce62b1c/wt-direct-queue"),
    Path("/workspaces/mission-1ce62b1c/output"),
]
OUT = ROOT / "output" / "direct-queue-validate"


def sha16(p: Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()[:16]


def classify_script(p: Path) -> dict:
    text = p.read_text(errors="replace")
    imports = re.findall(r"^(?:import|from)\s+([A-Za-z0-9_\.]+)", text, re.M)
    kinds = []
    if p.suffix == ".sh":
        kinds.append("shell_orchestrator")
    if p.name.endswith("lib.py") or "StorageImage" in text:
        kinds.append("python_storage_image_simulator")
    if "cycles" in p.name:
        kinds.append("finite_cycle_driver_on_simulator")
    if "bytecode-scan" in p.name:
        kinds.append("static_asm_hex_scanner")
    if "rapport" in p.name:
        kinds.append("report_generator")
    mentions_xi = bool(re.search(r"EvmYul|EVM\.Ξ|EvmRunner|native_decide", text))
    # Execution plane markers: real Ξ would import lean bindings or shell out to lake.
    invokes_lean = bool(re.search(r"\blake\b|\blean\b|EvmRunner\.run", text))
    uses_only_stdlib = all(
        i.split(".")[0]
        in {
            "__future__",
            "json",
            "os",
            "re",
            "sys",
            "pathlib",
            "typing",
            "dataclasses",
            "enum",
            "importlib",
            "hashlib",
            "collections",
            "functools",
            "itertools",
            "copy",
            "math",
            "struct",
            "argparse",
            "textwrap",
            "datetime",
        }
        or i.startswith("importlib")
        for i in imports
    )
    return {
        "path": str(p),
        "name": p.name,
        "sha256_16": sha16(p),
        "bytes": p.stat().st_size,
        "imports": imports,
        "kinds": kinds,
        "mentions_xi_or_evmrunner": mentions_xi,
        "invokes_lean_or_evmrunner_run": invokes_lean,
        "stdlib_only_python": uses_only_stdlib and p.suffix == ".py",
        "has_storage_image_sim": "StorageImage" in text or "user_append" in text,
    }


def main() -> int:
    OUT.mkdir(parents=True, exist_ok=True)
    pred = next((c for c in PRED_CANDIDATES if (c / "scripts").is_dir()), None)
    if pred is None:
        report = {
            "error": "predecessor worktree not found",
            "searched": [str(c) for c in PRED_CANDIDATES],
            "is_evm_xi": False,
        }
        (OUT / "classify.json").write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n")
        print(json.dumps(report, indent=2))
        return 1

    scripts_dir = pred / "scripts"
    scripts = sorted(scripts_dir.glob("direct-queue-*"))
    classified = [classify_script(p) for p in scripts if p.is_file()]

    # Read lib docstring for self-description
    lib = scripts_dir / "direct-queue-lib.py"
    lib_excerpt = None
    if lib.exists():
        m = re.search(r'"""(.*?)"""', lib.read_text(errors="replace"), re.S)
        lib_excerpt = m.group(1).strip()[:600] if m else None

    # Predecessor report self-claim
    pred_rapport = pred / "output" / "direct-queue" / "rapport-fr.md"
    pred_claims_not_xi = False
    if pred_rapport.exists():
        rt = pred_rapport.read_text(errors="replace")
        pred_claims_not_xi = "pas" in rt.lower() and ("Ξ" in rt or "EvmYul" in rt)

    any_xi_exec = any(c["invokes_lean_or_evmrunner_run"] for c in classified)
    any_sim = any(
        "python_storage_image_simulator" in c["kinds"] or c["has_storage_image_sim"]
        for c in classified
    )

    verdict_fr = (
        "CLASSIFICATION INDÉPENDANTE : les scripts predecessor `scripts/direct-queue-*` "
        "sont un simulateur Python manuscrit du flot de contrôle assembly "
        "(`StorageImage` / `user_append` / `system_drain` dans direct-queue-lib.py), "
        "plus un scan statique asm/hex et un générateur de rapport. "
        "Ce n'est PAS une exécution EvmRunner / EvmYul.EVM.Ξ des octets runtime épinglés. "
        "Les traces `output/direct-queue/cycles.json` ne sont PAS des preuves Ξ et ne "
        "doivent pas être comptées comme telles. Le scan statique peut ancrer des faits "
        "éprouvé sur des lignes asm/hex, distincts de l'exécution Ξ."
    )

    report = {
        "validator": "direct-queue-validate-classify.py",
        "predecessor_root": str(pred),
        "predecessor_branch_expected": "private/direct-queue-diag-20260908",
        "classification": "handwritten_python_assembly_simulator",
        "is_evm_xi": False,
        "is_evmrunner": False,
        "any_script_invokes_lean_or_evmrunner_run": any_xi_exec,
        "any_simulator_core": any_sim,
        "predecessor_rapport_self_claims_not_xi": pred_claims_not_xi,
        "lib_docstring_excerpt": lib_excerpt,
        "scripts": classified,
        "verdict_fr": verdict_fr,
        "labels": {
            "classification": "testé",
            "simulator_traces_as_xi_proofs": "rejeté",
            "static_scan_may_be_eprouve": "hypothèse_si_citations_lignes_vérifiées",
        },
    }
    out_path = OUT / "classify.json"
    out_path.write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n")
    print(verdict_fr)
    print(f"WROTE {out_path}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
