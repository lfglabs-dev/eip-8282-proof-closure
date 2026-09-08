# Rapport privé — validation file/inhibition EIP-8282 (Ξ finies = **testé**)

**Branche :** `private/direct-queue-validate-20260908`  
**Base :** `f14791d`  
**Pin EVMYulLean :** `b62586650b4f96cc6da25f36574aaa8f329a6420`  
**Périmètre :** `scripts/direct-queue-validate-*`, `output/direct-queue-validate/*`  
**Hors scope :** Model/AdmissibleCall/Trust/YAML, wrap `617c7ef2`, fees, PR20/31.

*Généré : 2026-09-08T15:21Z*

## Légende

| Label | Sens |
| --- | --- |
| **testé** | Trace finie `#eval` / script exercé ici (y compris sous EvmRunner/Ξ) |
| **éprouvé** | Ancrage asm/hex ou texte Lean cité, sans exécution nouvelle |
| **hypothèse** | Lecture de mécanisme — pas ∀ |
| **ouvert** | Non déchargé (∀, A-ABSTRACT-TX, non-wrap global) |

> **Important :** les faits `#eval` sous `EvmRunner`/`EVM.Ξ` sont **testé**
> (traces finies). Ils ne sont **pas** `prouvé ∀`. Aucune prémisse `noWrap` ;
> aucun claim de wrap `2^64` ; pas de commodité `TAIL<2^64`.

## 1. Predecessor — **testé** (simulateur, pas Ξ)

Scripts `direct-queue-*` = simulateur Python assembly-fidèle. `cycles.json` ≠ preuve Ξ.

## 2. Ancrages statiques — **éprouvé**

- `deposits` hex_bytes=628
- `exits` hex_bytes=458

## 3. Ancien reçu two-item — **testé** (pas cycle persistant)

Fichier `xi-inhibition-receipt.json` : file de **2** éléments + system nonempty
→ drain complet + INHIBITOR + **(HEAD,TAIL)=(0,0)**.

- **testé** sous Ξ (ctors, inhibit/uninhibit, SYSTEM gate).
- **N'est pas** un cycle de pointeurs persistants après drain partiel.
- Relabel explicite : `is_forall_proof=false`, `not_persistent_pointer_cycle=true`.

## 4. Nouveau reçu — nonempty-after-drain persistent inhibition — **testé**

- plane : `Eip8282.Audit.EvmRunner → EvmYul.EVM.Ξ`
- is_evm_xi : **True**
- is_forall_proof : **False**
- lean_exit_code : `0`
- cycle_kind : `nonempty_after_partial_drain_persistent_inhibition`

Drain à 2 éléments + inhibit remet (HEAD,TAIL)=(0,0) — reset complet, pas un cycle de pointeurs persistants. Ici file deposit 70 > cap 64: après system calldata non vide, HEAD=64 TAIL=70 COUNT=0 EXCESS=INHIBITOR (file encore non vide sous inhibition).

### Étapes deposit (queue initiale tail=70, excess=100, count=5)

| Step | Succ | Rev | payload | slot0 | count | head | tail | gas | ok |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| D1 | True | False | 11776 | INHIBITOR | 0 | 64 | 70 | 29134686 | true |
| D2 | False | True | — | — | — | — | — | 29997850 | true |
| D3 | True | False | 1104 | excess=0 | 0 | 0 | 0 | 29904712 | true |
| D4 | True | False | 0 | excess=0 | 0 | 0 | 0 | 29990963 | true |

- **D1 testé :** partial drain 64×184=11776 ; **head=64 tail=70 count=0 slot0=INHIBITOR** (file encore non vide).
- **D2 testé :** user revert sous inhibition + file non vide.
- **D3 testé :** drain reste 6×184=1104 ; clear excess ; reset 0,0.
- **D4 testé :** idle system empty.

### Étapes exit (queue tail=20)

| Step | Succ | Rev | payload | slot0 | count | head | tail | gas | ok |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| E1 | True | False | 1088 | INHIBITOR | 0 | 16 | 20 | 29862623 | true |
| E2 | False | True | — | — | — | — | — | 29997850 | true |
| E3 | True | False | 272 | excess=0 | 0 | 0 | 0 | 29956840 | true |

- **E1 testé :** head=16 tail=20 count=0 slot0=INHIBITOR ; payload 16×68=1088.
- **E2 testé :** user revert.
- **E3 testé :** drain reste 4×68=272 ; clear ; 0,0.

### Contraste two-item — **testé**

- full reset head=0 tail=0 payload=368 — **≠** persistent.

Artefacts : `xi-persistent-inhibition-receipt.json`, `scripts/direct-queue-validate-xi-persistent.lean`.

## 5. Ouvert / hypothèse

- **ouvert :** ∀ P-CONTROL-1 / `A-ABSTRACT-TX` / non-wrap u256 global.
- **hypothèse :** lectures simulateur predecessor.
- **rejeté :** wrap 2^64 ; prouvé ∀ à partir de #eval.

## 6. Conclusion

1. Simulateur predecessor ≠ Ξ (**testé**).
2. Two-item Ξ = **testé** full-reset, pas pointeurs persistants.
3. **Nouveau** cycle Ξ nonempty-after-drain (70→64/70 sous INHIBITOR ; exit 20→16/20) = **testé** avec reçus head/tail/count/slot0/payload/gas.
4. Rien n'est **prouvé ∀** ici.

