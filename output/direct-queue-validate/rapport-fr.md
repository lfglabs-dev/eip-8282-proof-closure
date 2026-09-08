# Rapport privé — validation indépendante file / inhibition EIP-8282

**Branche :** `private/direct-queue-validate-20260908`  
**Base :** `f14791d482690c64b71c17f63024d78459d15939` (main)  
**Pin EVMYulLean (cible lecture seule) :** `b62586650b4f96cc6da25f36574aaa8f329a6420`  
**Predecessor inspecté :** `private/direct-queue-diag-20260908` @ `b3b4220c97cf3fbe7e224676120b17cdee987936`  
**Worktree predecessor (local, non détruit) :** `/workspaces/mission-1ce62b1c/wt-direct-queue`  
**Périmètre :** `scripts/direct-queue-validate-*` et `output/direct-queue-validate/*` uniquement.  
**Hors périmètre :** Model.lean, AdmissibleCall, UniversalBoundary, Trust, YAML, frais `fa913be7`, wrap `617c7ef2`, PR #20/#31.

*Généré : 2026-09-08T14:03Z*

## Légende des labels

| Label | Sens |
| --- | --- |
| **testé** | Exercé par un script fini dans cette course de validation |
| **éprouvé** | Ancré sur des lignes de l'assembly/bytecode épinglé ou du texte Lean main cité |
| **hypothèse** | Proposition ou mécanisme — pas une preuve ∀ ni un reçu Ξ |
| **ouvert** | Obligation non déchargée ici |

## 1. Classification des scripts predecessor — **testé**

> **Verdict :** les scripts `scripts/direct-queue-*` du predecessor sont un
> **simulateur Python manuscrit** du flot de contrôle assembly
> (`StorageImage` / `user_append` / `system_drain`), plus un scan statique
> asm/hex et un générateur de rapport.
>
> Ils ne sont **pas** `Eip8282.Audit.EvmRunner`, **pas** `EvmYul.EVM.Ξ`, et
> **n'exécutent pas** les octets runtime épinglés.
>
> **Les traces `cycles.json` ne constituent PAS des preuves Ξ** et ne sont
> **pas comptées** comme telles dans cette validation.

Détail (fichiers predecessor) :

- `direct-queue-bytecode-scan.py` — static_asm_hex_scanner ; sha16=`0ea7dc5a45dd7918` ; invoke_lean/EvmRunner=True
- `direct-queue-cycles.py` — finite_cycle_driver_on_simulator ; sha16=`6ae8422afa4113a8` ; invoke_lean/EvmRunner=False
- `direct-queue-lib.py` — python_storage_image_simulator ; sha16=`04b497fd1cb74736` ; invoke_lean/EvmRunner=True
- `direct-queue-rapport.py` — report_generator ; sha16=`972f80c9c36d0347` ; invoke_lean/EvmRunner=True
- `direct-queue-run.sh` — shell_orchestrator ; sha16=`606d9812601317b0` ; invoke_lean/EvmRunner=False

- Auto-description lib (extrait) : « direct-queue-lib — storage/queue transitions mirrored from pinned EIP-8282 assembly.  Source of truth (read-only pins):   pinned/sys-asm/builder_{deposits,exits}/main.eas @ sys-asm… »
- Rapport predecessor revendique déjà non-Ξ : **True** (cohérent).
- Artefact : `output/direct-queue-validate/classify.json`.

## 2. Ancrages statiques asm/hex — **éprouvé** / **testé**

Re-scan indépendant de `pinned/sys-asm/builder_{deposits,exits}/main.eas` et des `main.hex` (lecture seule).

### Runtime `deposits` — 543 lignes asm, **testé** hex_bytes=628

- sha16 eas=`feb838796e12a710` hex=`1b643450f340305c`
- Faits ancrés éprouvé : 14/15
- **[éprouvé]** `macro_INHIBITOR` INHIBITOR = 2^256-1 (L31)
- **[éprouvé]** `system_addr` SYSTEM_ADDR gate constant (L22)
- **[éprouvé]** `jumpi_read_requests` caller EQ → system path (L54)
- **[éprouvé]** `set_inhibitor` nonempty system calldata latch (L512)
- **[éprouvé]** `zero_excess` empty+inhibited clears excess (L499)
- **[éprouvé]** `no_tail_lt_2_64_in_asm` No TAIL<2^64 guard found in runtime assembly (search for 2^64 / 1<<64 patterns). (—)
- **[éprouvé]** `set_inhibitor_body` set_inhibitor pushes INHIBITOR and SSTOREs SLOT_EXCESS (—)
- **[ouvert]** `zero_excess_body` zero_excess clears excess path present (—)

### Runtime `exits` — 431 lignes asm, **testé** hex_bytes=458

- sha16 eas=`96498e66775789a7` hex=`801baf70a2efb3ee`
- Faits ancrés éprouvé : 14/15
- **[éprouvé]** `macro_INHIBITOR` INHIBITOR = 2^256-1 (L32)
- **[éprouvé]** `system_addr` SYSTEM_ADDR gate constant (L22)
- **[éprouvé]** `jumpi_read_requests` caller EQ → system path (L53)
- **[éprouvé]** `set_inhibitor` nonempty system calldata latch (L408)
- **[éprouvé]** `zero_excess` empty+inhibited clears excess (L395)
- **[éprouvé]** `no_tail_lt_2_64_in_asm` No TAIL<2^64 guard found in runtime assembly (search for 2^64 / 1<<64 patterns). (—)
- **[éprouvé]** `set_inhibitor_body` set_inhibitor pushes INHIBITOR and SSTOREs SLOT_EXCESS (—)
- **[ouvert]** `zero_excess_body` zero_excess clears excess path present (—)

Sur l'assembly épinglé: (1) caller==SYSTEM → read_requests; (2) après drain, calldata non vide → set_inhibitor (EXCESS=INHIBITOR); (3) chemin user charge SLOT_EXCESS et jumpi @revert si == INHIBITOR; (4) system calldata vide + excess==INHIBITOR → zero_excess. Chaîne de contrôle éprouvée par citations de labels/macros. Enchaînement dynamique multi-appels = ouvert pour Ξ dans ce validateur jusqu'à exécution EvmRunner.

Artefact : `output/direct-queue-validate/static-anchors.json`.

## 3. Cycles predecessor — reclassification

Les cycles finis du predecessor restent utiles comme **hypothèse** de comportement du flot assembly, **testés** seulement sur le simulateur Python.

- `deposit_inhibit_reactivate_pointer_cycles` — predecessor=`testé` → **notre label=`testé_simulateur_seulement`** ; counts_as_xi_proof=**False**
- `exit_ctor_inhibited_then_reactivate` — predecessor=`testé` → **notre label=`testé_simulateur_seulement`** ; counts_as_xi_proof=**False**
- `system_impersonation_flags` — predecessor=`testé` → **notre label=`testé_simulateur_seulement`** ; counts_as_xi_proof=**False**
- `non_protocol_inverted_pointers` — predecessor=`testé` → **notre label=`testé_simulateur_seulement`** ; counts_as_xi_proof=**False**
- `count_vs_queue_length` — predecessor=`testé` → **notre label=`testé_simulateur_seulement`** ; counts_as_xi_proof=**False**
- `reduced_word_mod16_collision_sandbox` — predecessor=`hypothèse` → **notre label=`hypothèse_mécanisme_mod_réduit`** ; counts_as_xi_proof=**False**
- `stale_slots_after_full_drain` — predecessor=`testé` → **notre label=`testé_simulateur_seulement`** ; counts_as_xi_proof=**False**

Aucune extrapolation `2^64` ; pas de commodité `TAIL<2^64` introduite ici.

## 4. Exécution Ξ / EvmRunner

### Statut : **ouvert** — écart exact à Ξ documenté (voie **b**)

Cette course **n'a pas** produit de reçu d'exécution `EvmRunner` / `EVM.Ξ` sur les octets runtime épinglés. Conformément à l'objectif, on **s'arrête sans sur-revendiquer**.

#### Écart exact (G1–G5)

- G1: Les scripts predecessor direct-queue-* n'appellent jamais EvmRunner ni EVM.Ξ (testé par classification).
- G2: Pour un reçu Ξ il faut: (i) packages lake au pin EVMYulLean b625866…, (ii) FFI dynlib, (iii) Eip8282.Audit.EvmRunner+Bytecode compilés, (iv) runDepositSystem/runDeposit sur depositRuntime avec slots 0–3 observés.
- G3: scripts/direct-queue-validate-xi-attempt.lean encode inhibit→user revert→uninhibit (file vide) mais n'a pas été évalué avec succès ici.
- G4: In-tree pcontrol1_bytecode_parent affirme ces conjonctions via native_decide — citation seulement (in-tree-xi-citation.json), pas reproduction de cette course.
- G5: Aucune preuve ∀, aucun wrap 2^64, aucun edit Model/Trust/YAML pour combler G2–G3.

#### Bloquant observé

- `lake_bootstrap_not_ready_for_eval` : Lean 4.31.0 présent; packages partiellement bootstrappés; oleans=4967; evmyul=b62586650b4f96cc6da25f36574aaa8f329a6420; lake_alive=True; leantar_alive=True; EvmRunner.olean count=0. Build complet EVMYulLean+FFI+EvmRunner non disponible à temps pour #eval. Voie (b): écart documenté, pas de sur-revendication.

#### Ce qui fermerait l'écart (non fait si non atteint)

- `lake exe cache get && lake build EvmYul.FFI.ffi:dynlib Eip8282.Audit.EvmRunner`
- `lake env lean scripts/direct-queue-validate-xi-attempt.lean → true`
- `écrire xi-inhibition-receipt.json avec is_evm_xi=true`

Artefacts : `xi-gap.json` ; tentative `scripts/direct-queue-validate-xi-attempt.lean`.

## 5. Citation in-tree (pas une reproduction) — **éprouvé** sur texte Lean

Le parent kill-line `pcontrol1_bytecode_parent` dans main affirme déjà, via `native_decide` sur `runDeposit`/`runDepositSystem` et `depositRuntime`/`exitRuntime` :

- system calldata non vide → `SLOT_EXCESS = INHIBITOR` ;
- system vide depuis image inhibée → excess `0` ;
- user depuis image inhibée → `isRevert` ; system → `isSuccess`.

**Label :** éprouvé *comme texte de théorème dans le dépôt* ;
**is_our_reproduction = False**. 
Ne remplace pas un reçu produit par cette validation ; ne convertit pas le simulateur en Ξ.

Artefact : `in-tree-xi-citation.json`.

## 6. Invariant / wrap — position de cette validation

- **éprouvé :** pas de garde `TAIL<2^64` dans l'assembly runtime (re-scan).
- **ouvert :** non-wrap u256 des pointeurs sur toutes traces protocolaires atteignables.
- **rejeté :** toute affirmation de wrap `2^64` par extrapolation des cycles simulateur ou de cette course.
- **hors scope :** `A-ABSTRACT-TX` (Ξ ↔ Model), frais, wrap-diagnosis dédié.

## 7. Non-revendications

- Pas de preuve ∀ P-CONTROL-1 / P-DRAIN-1 nouvelle.
- Pas d'édition Model / AdmissibleCall / YAML / Trust.
- Pas de PR #20 / #31.
- Pas de toucher à `617c7ef2` (wrap) ni `fa913be7` (fees).
- Traces simulateur predecessor ≠ preuves Ξ.

## 8. Conclusion

1. **testé** — Classification : simulateur Python/assembly, **pas** EVM.Ξ.
2. **éprouvé** — Macros/labels d'inhibition et tailles hex re-ancrés sur pins.
3. **ouvert** — Reçu d'un cycle d'inhibition via EvmRunner/Ξ **non obtenu** dans cette course ; écart G1–G5 consigné (voie b, sans sur-revendication).
4. Continuation possible : fermer G2–G3 par build lake+FFI puis `#eval` du lean de tentative — sans compter le simulateur comme Ξ.

---

*Fin du rapport de validation indépendante.*
