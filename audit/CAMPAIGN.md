# Universal bytecode campaign

Replace finite `EvmYul.EVM.Ξ` traces with `∀` parents under well-formed
storage and enough gas. The abstract `Model` stays as the spec;
correspondence (`A-ABSTRACT-TX`) is how those `∀` lemmas become bytecode
facts. More `native_decide` images are **not** this campaign.

Orchestrator prompt: `audit/CLOUD_ORCHESTRATOR.md`.

## Status (main @ `ccdca6b`)

Waves A–D are **done**: #11 (P-SUBMIT-1), #12 (P-CONTROL-1), #13
(P-DRAIN-1) landed the CFG `∀` parents with the Wave-1/5/6 Ξ traces kept
as kill-line witnesses. `A-ABSTRACT-TX` (Ξ ↔ Model/CFG) remains open and
is honestly classified PARTIAL in `audit/guarantees.yaml`; closing it needs
a non-`partial` `D_J_aux` upstream in EVMYulLean, not more traces here.

In flight (branch `cursor/psubmit1-parent-honesty-5c89`, draft PR, not
merged): P-SUBMIT-1 parent strength — the fee-getter conjunct now observes
post-storage from the CFG machine (the completing run's `SSTORE` overlay
is proved empty) instead of copying pre-state slots into the observation,
and the exit append conjunct exports the LOG0 payload
`msg.sender ‖ pubkey` from `Append.exit_handle_input_append` (YAML already
claimed both). No new IDs, no new traces, kill-line unchanged.

## Baseline (do not redo)

`origin/main` at **`85dab78`** already has:

| Landed | What it is | Still not |
| --- | --- | --- |
| P-CONTROL-1 Wave 5 (#8) | Nonempty-queue excess fold on `Ξ`; parent `pcontrol1_nonempty_bytecode_parent` | `∀` excess/count; exit ctor |
| P-SUBMIT-1 Wave 6 (#9) | Underpay revert + second storage image (`50/3/2/6`) | `∀` calldata/value/storage; `revertFreezesSlots` is runner-API (`storageSlotAfter = none` on any revert), load-bearing part is the revert itself |
| P-DRAIN-1 Wave 6 (#10) | More leftover words (deposit 0/1/32/63/64, exit 0/7/15) | `∀` drained indices; SSTORE-footprint lemma |

Closed as superseded: PR **#7** (same Wave 5 as #8, conflicted).

Do **not** spend workers on extra trace depths, extra stale indices, or a
third submit image. Jump to CFG / correspondence / `∀`.

## Method

`native_decide` only closes ground terms. A `∀` parent cannot be discharged
that way. Two further constraints:

1. `D_J_aux` is `partial`. Prove JUMPDEST sets of the two **pinned** hexes
   once (F1). Later lemmas use those tables.
2. `∀` over raw EVM storage is the wrong theorem. Use `WellFormed` (packed
   records, `head ≤ tail`, slots 0–3). The model already uses a list queue.

Preferred path: prove `Ξ` agrees with `Model.userCall` / `systemCall` on
well-formed states (F4). Claim workers then transport model `∀` and add
what the model omitted (`LOG0`, stale slots, ctors).

Fallback if F4 slips: CFG-direct `∀` for revert/append/gate/excess/footprint;
leave `A-ABSTRACT-TX` open; do not block ctors or drain footprint on a
complete simulation.

Hypotheses allowed on every `∀`: `WellFormed`, gas ≥ 30M, interpreter fuel
bound, caller class (`SYSTEM_ADDR` vs not). Not “whatever is in storage.”

## Counts

| Role | IDs | How many |
| --- | --- | --- |
| Foundation workers | F1–F4 | **4** |
| Claim workers | S1–S4, C1–C4, D1–D3 | **11** |
| Integrators | IS, IC, ID | **3** |
| Public PRs | stacked on `main` | **3** |
| **Total agents** | orchestrator + above | **1 + 18** if fully fan-out; orchestrator may do integrate itself |

Best-of-n (run 2–3, keep the one that builds): **F1**, **F4**, **S4**, **D2**.

## Waves

```
F1 Jumpdests  F2 WellFormed
        \         /
         F3 Stepper
              |
         F4 Model ↔ Ξ
         /    |    \
     S1–S4  C1–C4  D1–D3
         |    |    |
        IS   IC   ID
         |    |    |
      PR1 → PR2, PR3   (PR3 rebases onto PR2 after PR2 merges)
```

- **Wave A** — F1 and F2 in parallel from `main`. F3 after F1. F4 after F2+F3.
  Merge onto `forall/foundation`. Do not open a PR to `main` yet.
- **Wave B** — 11 claim workers from `forall/foundation`, parallel, each on
  its own `cursor/…` branch. Start only after `lake build` of foundation.
- **Wave C** — integrators write the three parent theorems + YAML.
- **Wave D** — humans review and merge **PR1 then PR2 then PR3**. Agents
  do **not** merge to `main`.

## Git

| Branch | Base | Touches |
| --- | --- | --- |
| `forall/foundation` | `main` @ `85dab78` | `Jumpdests.lean`, `WellFormed.lean`, `Step.lean`, `Correspondence.lean` |
| `forall/psubmit1` | `forall/foundation` | `PSubmit1/*` + parent/YAML/Trust for submit |
| `forall/pcontrol1` | `forall/psubmit1` | `PControl1/*` + control YAML |
| `forall/pdrain1` | `forall/psubmit1` | `PDrain1/*` + drain YAML; rebase onto `pcontrol1` after PR2 merges |

Each cloud worker uses a **new** `cursor/…` branch (`workOnCurrentBranch: false`).
Do not have two workers push the same branch.

## Shared modules (Wave A only)

| File | Owner | Done when |
| --- | --- | --- |
| `Eip8282/Audit/Jumpdests.lean` | F1 | `D_J` of `depositRuntime` and `exitRuntime` is a concrete finite set |
| `Eip8282/Audit/WellFormed.lean` | F2 | Packed queue, `head ≤ tail`, slot 0–3 meaning, both predeploys |
| `Eip8282/Audit/Step.lean` | F3 | Opcode-at-PC; `CALLER == SYSTEM_ADDR` iff `read_requests`; enough-gas explicit |
| `Eip8282/Audit/Correspondence.lean` | F4 | Well-formed storage: `EvmRunner`/`Ξ` matches `userCall`/`systemCall` |

Claim workers treat these as **read-only**.

## Claim workers

User path = caller ≠ `SYSTEM_ADDR`. System path = `SYSTEM_ADDR`.

### P-SUBMIT-1 (PR1, merge first; carries foundation)

| ID | Module | Done when |
| --- | --- | --- |
| S1 | `PSubmit1/Revert.lean` | Every `jumpi @revert` is before first `SSTORE`/`LOG0`. Inhibitor, **bad `calldatasize`** (not just empty vs 184/48 — Wave 6 did not cover this), value-on-getter, underpay (Wave 6 sampled; now `∀` fee), min-amount, stake |
| S2 | `PSubmit1/Append.lean` | `∀` 184-byte paying deposit: six words at `tail*6`, `LOG0` = calldata. `∀` 48-byte paying exit: slot0 = `CALLER`, `LOG0` = sender‖pubkey |
| S3 | `PSubmit1/Fee.lean` | Empty calldata, value 0: 32-byte return, slots 0–3 unchanged, `∀` excess/count. **Not** `fake_expo` equality |
| S4 | `PSubmit1/FakeExpo.lean` | Pinned `fake_expo` equals `Model.fakeExponential` for all excess. Hardest submit lemma. Shared with control quotes |

Wave 6 already samples underpay at two quotes (357/427 and 18/19). S1 must
generalise, not add a third image.

### P-CONTROL-1 (PR2, merge second)

Excess **does not use queue length**. C2 ignores FIFO. Ctor is init bytecode.

| ID | Module | Done when |
| --- | --- | --- |
| C1 | `PControl1/Gate.lean` | `∀` callers: `CALLER = SYSTEM_ADDR` iff system subroutine |
| C2 | `PControl1/Excess.lean` | `∀` excess, count, calldata length: nonempty → `INHIBITOR`; inhibited+empty → 0; else `max(0, excess+count−TARGET)` for targets 8 and 2 |
| C3 | `PControl1/Count.lean` | Paid user: `SLOT_COUNT += 1`, excess unchanged. System: `SLOT_COUNT := 0`. `∀` prior count (mod 2^256) |
| C4 | `PControl1/Ctor.lean` | `exitInit` / `depositInit` under `Ξ`. Exit stores `INHIBITOR` at slot 0 then returns runtime. Deposit leaves storage zero. Closes `initial_gating` on bytes |

Wave 5 already samples nonempty drain+fold. C2 is the `∀` recurrence, not
more `TAIL ∈ {2,17,65}` traces.

### P-DRAIN-1 (PR3, merge last)

| ID | Module | Done when |
| --- | --- | --- |
| D1 | `PDrain1/Footprint.lean` | System `SSTORE` targets ⊆ `{SLOT_EXCESS, SLOT_COUNT, QUEUE_HEAD, QUEUE_TAIL}` → `∀` stale-slot non-erasure (Wave 6 only sampled indices) |
| D2 | `PDrain1/Fifo.lean` | `accum_loop`: oldest `min(length, cap)` records; HEAD advances or both pointers zero on full drain; caps 64 and 16. Hardest drain lemma |
| D3 | `PDrain1/Encode.lean` | Deposit amount BE storage → LE return, `∀` queued items. User fee quote does not move HEAD/TAIL |

## Integrators

Only IS/IC/ID edit `PSubmit1.lean` / `PControl1.lean` / `PDrain1.lean`
parents, `Eip8282.lean` imports, `Trust.lean`, `audit/guarantees.yaml`,
README.

Re-register the public parent as the `∀` conjunction. **Keep**
`submitFacts` / `drainFacts` / `controlFacts` traces as kill-line
witnesses. The existing one-byte mutants must still make the **new** parent
false. Sibling independence must still hold.

YAML: `evm.scope` moves off `CONCRETE_TRACES` toward the stated hypotheses.
Close or shrink `A-EVM-WORLD` and `A-ABSTRACT-TX` only when Lean actually
does. `python3 scripts/audit_metadata.py` must pass.

## Three PRs (Wave D — humans merge)

1. **P-SUBMIT-1 `∀` on pinned user path** — foundation + S*. First time
   reviewers see the stepper. Largest diff.
2. **P-CONTROL-1 `∀` control plane** — stacks on 1. Gate, excess, count, ctors.
3. **P-DRAIN-1 `∀` FIFO** — stacks on 1, rebase onto 2 after it merges.

`autoCreatePR: true` only for these three. Foundation/claim workers push
branches only.

## Worker rules

1. One module, named above. Do not edit sibling guarantee files.
2. No `sorry`. No new `axiom`. `native_decide` only for F1 finite tables.
3. Do not delete `Model.lean`. Correspondence uses it. Do not re-register
   `unfold userCall` as the parent.
4. Do not weaken existing concrete traces until the `∀` parent implies them.
5. Do not merge to `main`.

## PR allow-list (integrator)

A guarantee PR is allowed only when:

- `lake build` of the guarantee + its mutant module succeeds
- Kill-line still falsifies the **new** parent
- Sibling facts stay true on that mutant
- YAML `parent` matches the Lean name
- `Trust.lean` `#print axioms` for the new parent has no undisclosed axiom

## Fallback

If F4 correspondence slips: ship PR1 with CFG-direct `∀` for revert and
append only, keep fee numeric traces, leave `A-ABSTRACT-TX` open. C4 and D1
must not wait on a complete Model simulation.
