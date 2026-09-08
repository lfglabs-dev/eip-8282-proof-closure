# Rapport privé — validation indépendante + exécution Ξ file/inhibition EIP-8282

**Branche :** `private/direct-queue-validate-20260908`  
**Base :** `f14791d482690c64b71c17f63024d78459d15939` (main)  
**Pin EVMYulLean :** `b62586650b4f96cc6da25f36574aaa8f329a6420` (exécuté via EvmRunner)  
**Predecessor inspecté :** `private/direct-queue-diag-20260908` @ `b3b4220c97cf3fbe7e224676120b17cdee987936`  
**Worktree predecessor (intact) :** `/workspaces/mission-1ce62b1c/wt-direct-queue`  
**Périmètre :** `scripts/direct-queue-validate-*`, `output/direct-queue-validate/*`.  
**Hors périmètre :** Model/AdmissibleCall/Trust/YAML, wrap `617c7ef2`, fees `fa913be7`, PR #20/#31.

*Généré : 2026-09-08T14:21Z*

## Légende

| Label | Sens |
| --- | --- |
| **testé** | Exercé par un script/évaluation fini dans cette course |
| **prouvé** | Observé sous `EvmRunner` → `EvmYul.EVM.Ξ` sur octets épinglés (reçu) |
| **éprouvé** | Ancré sur lignes asm/hex ou texte Lean cité (sans exécution ici) |
| **hypothèse** | Mécanisme ou lecture — pas ∀ |
| **ouvert** | Non déchargé ici |

## 1. Classification predecessor — **testé**

> Les scripts `scripts/direct-queue-*` sont un **simulateur Python manuscrit**
> du flot assembly. **Pas** EvmRunner, **pas** EVM.Ξ.
> **`cycles.json` n'est PAS une preuve Ξ** et n'est pas compté comme tel.

- `direct-queue-bytecode-scan.py` — static_asm_hex_scanner ; invoke_lean=True
- `direct-queue-cycles.py` — finite_cycle_driver_on_simulator ; invoke_lean=False
- `direct-queue-lib.py` — python_storage_image_simulator ; invoke_lean=True
- `direct-queue-rapport.py` — report_generator ; invoke_lean=True
- `direct-queue-run.sh` — shell_orchestrator ; invoke_lean=False

Artefact : `classify.json`.

## 2. Ancrages statiques asm/hex — **éprouvé** / **testé**

- `deposits` : 14 faits éprouvé, hex_bytes=**testé** 628
- `exits` : 14 faits éprouvé, hex_bytes=**testé** 458

## 3. Cycles predecessor — non-Ξ

- `deposit_inhibit_reactivate_pointer_cycles` → **testé_simulateur_seulement** (counts_as_xi=**false**)
- `exit_ctor_inhibited_then_reactivate` → **testé_simulateur_seulement** (counts_as_xi=**false**)
- `system_impersonation_flags` → **testé_simulateur_seulement** (counts_as_xi=**false**)
- `non_protocol_inverted_pointers` → **testé_simulateur_seulement** (counts_as_xi=**false**)
- `count_vs_queue_length` → **testé_simulateur_seulement** (counts_as_xi=**false**)
- `reduced_word_mod16_collision_sandbox` → **hypothèse_mécanisme_mod_réduit** (counts_as_xi=**false**)
- `stale_slots_after_full_drain` → **testé_simulateur_seulement** (counts_as_xi=**false**)

## 4. Exécution EvmRunner / EVM.Ξ — **prouvé** / **testé**

### Statut : **prouvé** sur cycle fini (voie **a**)

- **plane :** `Eip8282.Audit.EvmRunner → EvmYul.EVM.Ξ`
- **is_evm_xi :** `True`
- **lean_exit_code :** `0`
- **not_python_simulator :** `True`
- **claims_2_64_wrap :** `False`
- **nowrap_as_premise :** `False`

### Constructeurs (init → runtime) — **prouvé**

- deposit ctor : payload = `depositRuntime`, slots 0–3 = 0 → `true`
- exit ctor : payload = `exitRuntime`, slot0 = INHIBITOR → `true`

### File non vide — inhibition / réactivation — **prouvé**

- `deposit_system_nonempty_calldata_drains_2_and_sets_INHIBITOR` → **true**
- `deposit_user_reverts_while_inhibited` → **true**
- `deposit_system_empty_clears_inhibitor` → **true**
- `deposit_nonempty_inhibited_queue_drains_and_clears` → **true**
- `exit_system_nonempty_drains_2_and_sets_INHIBITOR` → **true**
- `exit_nonempty_inhibited_queue_drains_and_clears` → **true**

### Flags SYSTEM / payload / storage / gas / balances — **prouvé**

- gate user vs SYSTEM (même image file non vide) → `true`
- SYSTEM_ADDR = `0xfffffffffffffffffffffffffffffffffffffffe` ; submitter = `0x1234`
- final gas (après inhibit deposit nonempty) : **29956672** (gas initial runner 30_000_000)
- balance predeploy deposit après appel : **0**
- payload size return inhibit deposit : **368** (= 2×184)
- slot0 == INHIBITOR après inhibit : flag **1**

### Faits #eval (tous true)

- `nonemptyInhibitionCycleReceipt` = **true**
- `depositCtorOk` = **true**
- `exitCtorOk` = **true**
- `depositNonemptyInhibitOk` = **true**
- `depositInhibitedUserRevertsOk` = **true**
- `depositUninhibitOk` = **true**
- `depositNonemptyUninhibitOk` = **true**
- `exitNonemptyInhibitOk` = **true**
- `exitNonemptyUninhibitOk` = **true**
- `depositSystemFlagOk` = **true**

### Pins hex

- `builder_deposits/main.hex` : 628 B, sha16=`1b643450f340305c`
- `builder_exits/main.hex` : 458 B, sha16=`801baf70a2efb3ee`
- `builder_deposits/ctor.hex` : 638 B, sha16=`20d76f572f22c4f7`
- `builder_exits/ctor.hex` : 503 B, sha16=`678d5945780f4c3e`

Reçu machine : `output/direct-queue-validate/xi-inhibition-receipt.json`  
Log : `output/direct-queue-validate/xi-run.log`  
Source : `scripts/direct-queue-validate-xi-attempt.lean`

## 5. Ce qui reste **ouvert** / **hypothèse**

- **ouvert :** correspondance universelle Ξ ↔ Model (`A-ABSTRACT-TX`).
- **ouvert :** non-wrap des pointeurs u256 sur *toutes* traces protocolaires (aucun claim `2^64`).
- **hypothèse :** lectures assembly-fidèles du simulateur predecessor (non Ξ).
- **prouvé (fini seulement) :** le cycle d'inhibition/réactivation ci-dessus sur images finies ; pas un ∀.

## 6. Non-revendications

- Pas de wrap `2^64` ; `noWrap` n'est **pas** une prémisse des évaluations.
- Pas d'édition Model / AdmissibleCall / YAML / Trust.
- Pas PR #20/#31 ; pas touché wrap-diagnosis ni fees.
- Simulateur predecessor ≠ preuves Ξ.

## 7. Conclusion

1. **testé** — predecessor = simulateur Python, pas Ξ.
2. **éprouvé** — macros/labels inhibition re-ancrés sur pins asm.
3. **prouvé** — constructeurs + cycles inhibition/réactivation **file non vide** via `EvmRunner`/`EVM.Ξ` sur runtime+init épinglés, avec reçus (payload, storage slots 0–3, gas final, balance, flag SYSTEM).
4. **ouvert** — ∀ / A-ABSTRACT-TX / non-wrap global.

---
*Fin du rapport.*
