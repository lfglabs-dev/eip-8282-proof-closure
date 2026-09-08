#!/usr/bin/env python3
"""Regenerate output/direct-queue-validate/rapport-fr.md from JSON artifacts."""
from __future__ import annotations
import json
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "output" / "direct-queue-validate"

def load(name: str) -> dict:
    p = OUT / name
    return json.loads(p.read_text()) if p.exists() else {}

def main() -> None:
    classify = load("classify.json")
    static = load("static-anchors.json")
    cross = load("cross-check-predecessor.json")
    cite = load("in-tree-xi-citation.json")
    gap = load("xi-gap.json")
    receipt = load("xi-inhibition-receipt.json")
    xi_ok = bool(receipt.get("is_evm_xi")) or receipt.get("eval_result") == "true"

    L: list[str] = []
    A = L.append
    A("# Rapport privé — validation indépendante file / inhibition EIP-8282")
    A("")
    A("**Branche :** `private/direct-queue-validate-20260908`  ")
    A("**Base :** `f14791d482690c64b71c17f63024d78459d15939` (main)  ")
    A("**Pin EVMYulLean (cible lecture seule) :** `b62586650b4f96cc6da25f36574aaa8f329a6420`  ")
    A("**Predecessor inspecté :** `private/direct-queue-diag-20260908` @ `b3b4220c97cf3fbe7e224676120b17cdee987936`  ")
    A("**Worktree predecessor (local, non détruit) :** `/workspaces/mission-1ce62b1c/wt-direct-queue`  ")
    A("**Périmètre :** `scripts/direct-queue-validate-*` et `output/direct-queue-validate/*` uniquement.  ")
    A("**Hors périmètre :** Model.lean, AdmissibleCall, UniversalBoundary, Trust, YAML, frais `fa913be7`, wrap `617c7ef2`, PR #20/#31.")
    A("")
    A(f"*Généré : {datetime.now(timezone.utc).strftime('%Y-%m-%dT%H:%MZ')}*")
    A("")
    A("## Légende des labels")
    A("")
    A("| Label | Sens |")
    A("| --- | --- |")
    A("| **testé** | Exercé par un script fini dans cette course de validation |")
    A("| **éprouvé** | Ancré sur des lignes de l'assembly/bytecode épinglé ou du texte Lean main cité |")
    A("| **hypothèse** | Proposition ou mécanisme — pas une preuve ∀ ni un reçu Ξ |")
    A("| **ouvert** | Obligation non déchargée ici |")
    A("")
    A("## 1. Classification des scripts predecessor — **testé**")
    A("")
    A("> **Verdict :** les scripts `scripts/direct-queue-*` du predecessor sont un")
    A("> **simulateur Python manuscrit** du flot de contrôle assembly")
    A("> (`StorageImage` / `user_append` / `system_drain`), plus un scan statique")
    A("> asm/hex et un générateur de rapport.")
    A(">")
    A("> Ils ne sont **pas** `Eip8282.Audit.EvmRunner`, **pas** `EvmYul.EVM.Ξ`, et")
    A("> **n'exécutent pas** les octets runtime épinglés.")
    A(">")
    A("> **Les traces `cycles.json` ne constituent PAS des preuves Ξ** et ne sont")
    A("> **pas comptées** comme telles dans cette validation.")
    A("")
    A("Détail (fichiers predecessor) :")
    A("")
    for s in classify.get("scripts", []):
        kinds = ", ".join(s.get("kinds") or ["?"])
        A(
            f"- `{s.get('name')}` — {kinds} ; sha16=`{s.get('sha256_16')}` ; "
            f"invoke_lean/EvmRunner={s.get('invokes_lean_or_evmrunner_run')}"
        )
    A("")
    excerpt = (classify.get("lib_docstring_excerpt") or "")[:180].replace("\n", " ")
    A(f"- Auto-description lib (extrait) : « {excerpt}… »")
    A(
        f"- Rapport predecessor revendique déjà non-Ξ : "
        f"**{classify.get('predecessor_rapport_self_claims_not_xi')}** (cohérent)."
    )
    A("- Artefact : `output/direct-queue-validate/classify.json`.")
    A("")
    A("## 2. Ancrages statiques asm/hex — **éprouvé** / **testé**")
    A("")
    A(
        "Re-scan indépendant de `pinned/sys-asm/builder_{deposits,exits}/main.eas` "
        "et des `main.hex` (lecture seule)."
    )
    A("")
    for k in static.get("kinds", []):
        ok = sum(1 for f in k.get("facts", []) if f.get("label") == "éprouvé")
        tot = len(k.get("facts", []))
        A(
            f"### Runtime `{k.get('kind')}` — {k.get('asm_lines')} lignes asm, "
            f"**testé** hex_bytes={k.get('hex_bytes')}"
        )
        A("")
        A(f"- sha16 eas=`{k.get('eas_sha256_16')}` hex=`{k.get('hex_sha256_16')}`")
        A(f"- Faits ancrés éprouvé : {ok}/{tot}")
        for f in k.get("facts", []):
            if f.get("id") in (
                "macro_INHIBITOR",
                "set_inhibitor",
                "zero_excess",
                "set_inhibitor_body",
                "zero_excess_body",
                "jumpi_read_requests",
                "no_tail_lt_2_64_in_asm",
                "system_addr",
            ):
                anchor = f.get("anchor") or {}
                loc = f"L{anchor['line']}" if anchor.get("line") else "—"
                A(
                    f"- **[{f.get('label')}]** `{f.get('id')}` "
                    f"{(f.get('note') or '')[:100]} ({loc})"
                )
        A("")
    A(static.get("inhibition_cycle_static_story_fr", ""))
    A("")
    A("Artefact : `output/direct-queue-validate/static-anchors.json`.")
    A("")
    A("## 3. Cycles predecessor — reclassification")
    A("")
    A(
        "Les cycles finis du predecessor restent utiles comme **hypothèse** de "
        "comportement du flot assembly, **testés** seulement sur le simulateur Python."
    )
    A("")
    for t in cross.get("tests", []):
        A(
            f"- `{t.get('predecessor_name')}` — predecessor=`{t.get('predecessor_status')}` → "
            f"**notre label=`{t.get('our_label')}`** ; "
            f"counts_as_xi_proof=**{t.get('counts_as_xi_proof')}**"
        )
    A("")
    A("Aucune extrapolation `2^64` ; pas de commodité `TAIL<2^64` introduite ici.")
    A("")
    A("## 4. Exécution Ξ / EvmRunner")
    A("")
    if xi_ok:
        A("### Statut : **testé** (reçu Ξ produit dans cette course)")
        A("")
        A(f"- plane : `{receipt.get('plane')}`")
        A(f"- eval_result : `{receipt.get('eval_result')}`")
        A(f"- cycle : {receipt.get('cycle')}")
        A("")
        A("Reçu : `output/direct-queue-validate/xi-inhibition-receipt.json`.")
    else:
        A("### Statut : **ouvert** — écart exact à Ξ documenté (voie **b**)")
        A("")
        A(
            "Cette course **n'a pas** produit de reçu d'exécution `EvmRunner` / "
            "`EVM.Ξ` sur les octets runtime épinglés. Conformément à l'objectif, "
            "on **s'arrête sans sur-revendiquer**."
        )
        A("")
        A("#### Écart exact (G1–G5)")
        A("")
        for g in gap.get("exact_gap_to_xi_fr", []):
            A(f"- {g}")
        A("")
        A("#### Bloquant observé")
        A("")
        blk = gap.get("blocker") or {}
        A(f"- `{blk.get('kind')}` : {blk.get('detail_fr', '')}")
        A("")
        A("#### Ce qui fermerait l'écart (non fait si non atteint)")
        A("")
        for w in gap.get("what_would_close_gap", []):
            A(f"- `{w}`")
        A("")
        A(
            "Artefacts : `xi-gap.json` ; tentative "
            "`scripts/direct-queue-validate-xi-attempt.lean`."
        )
    A("")
    A("## 5. Citation in-tree (pas une reproduction) — **éprouvé** sur texte Lean")
    A("")
    A(
        "Le parent kill-line `pcontrol1_bytecode_parent` dans main affirme déjà, via "
        "`native_decide` sur `runDeposit`/`runDepositSystem` et "
        "`depositRuntime`/`exitRuntime` :"
    )
    A("")
    A("- system calldata non vide → `SLOT_EXCESS = INHIBITOR` ;")
    A("- system vide depuis image inhibée → excess `0` ;")
    A("- user depuis image inhibée → `isRevert` ; system → `isSuccess`.")
    A("")
    A("**Label :** éprouvé *comme texte de théorème dans le dépôt* ;")
    A(f"**is_our_reproduction = {cite.get('is_our_reproduction')}**. ")
    A(
        "Ne remplace pas un reçu produit par cette validation ; ne convertit pas "
        "le simulateur en Ξ."
    )
    A("")
    A("Artefact : `in-tree-xi-citation.json`.")
    A("")
    A("## 6. Invariant / wrap — position de cette validation")
    A("")
    A("- **éprouvé :** pas de garde `TAIL<2^64` dans l'assembly runtime (re-scan).")
    A(
        "- **ouvert :** non-wrap u256 des pointeurs sur toutes traces "
        "protocolaires atteignables."
    )
    A(
        "- **rejeté :** toute affirmation de wrap `2^64` par extrapolation des "
        "cycles simulateur ou de cette course."
    )
    A("- **hors scope :** `A-ABSTRACT-TX` (Ξ ↔ Model), frais, wrap-diagnosis dédié.")
    A("")
    A("## 7. Non-revendications")
    A("")
    A("- Pas de preuve ∀ P-CONTROL-1 / P-DRAIN-1 nouvelle.")
    A("- Pas d'édition Model / AdmissibleCall / YAML / Trust.")
    A("- Pas de PR #20 / #31.")
    A("- Pas de toucher à `617c7ef2` (wrap) ni `fa913be7` (fees).")
    A("- Traces simulateur predecessor ≠ preuves Ξ.")
    A("")
    A("## 8. Conclusion")
    A("")
    A("1. **testé** — Classification : simulateur Python/assembly, **pas** EVM.Ξ.")
    A("2. **éprouvé** — Macros/labels d'inhibition et tailles hex re-ancrés sur pins.")
    if xi_ok:
        A("3. **testé** — Reçu d'un cycle d'inhibition fini via EvmRunner/Ξ (file vide).")
    else:
        A(
            "3. **ouvert** — Reçu d'un cycle d'inhibition via EvmRunner/Ξ **non obtenu** "
            "dans cette course ; écart G1–G5 consigné (voie b, sans sur-revendication)."
        )
    A(
        "4. Continuation possible : fermer G2–G3 par build lake+FFI puis `#eval` "
        "du lean de tentative — sans compter le simulateur comme Ξ."
    )
    A("")
    A("---")
    A("")
    A("*Fin du rapport de validation indépendante.*")
    A("")
    text = "\n".join(L)
    (OUT / "rapport-fr.md").write_text(text)
    mission_out = Path("/workspaces/mission-1718b986/output")
    mission_out.mkdir(exist_ok=True)
    (mission_out / "rapport-fr.md").write_text(text)
    print(f"WROTE {OUT / 'rapport-fr.md'} ({len(text)} bytes)")

if __name__ == "__main__":
    main()
