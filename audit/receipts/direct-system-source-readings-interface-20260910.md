# Constructive SYSTEM storage readings

Read-only proposal, 2026-09-10. Existing pins remain unadopted as a protocol baseline. No implementation or compiler run in this task.

The smallest adapter can keep the existing `SystemMeterResources.Inputs = EVM.State -> Reading` API, but instantiate it with a closed function of the fixed source parent/created set and actual pinned state. A separate source access-set relation then proves that this function returns exactly the readings computed by the evolving source view. There is no need for an arbitrary oracle or a global interpreter/gas equivalence.

## Source behavior that the adapter must retain

Amsterdam SLOAD pops the key, queries `(current_target,key32)` in `accessed_storage_keys`, inserts on cold access, charges 100 or 2100, then `get_storage` records a BAL read and reads transaction writes, block-parent writes, then prestate. SSTORE first rejects static context, pops key then new value, computes pre-access warmth and checks max(access,2301) before any original/current lookup. It then inserts a cold key, reads original (created account overrides to zero; otherwise parent/prestate) and current (tx/parent/prestate, recording a BAL read). Refunds/state credits are computed before execution charge; execution charge precedes state charge and the final write. Source access/update chronology on failing operations is not interchangeable with successful effects.

The existing `ReferenceStorageView.Tx.reads` models BAL reads. **It is not the warm-access set.** BAL reads and created accounts are shared by snapshots and survive rollback, while child frame access sets are copied and merged into their parent only on success. A failed child can therefore leave a BAL read for a slot that is cold in its parent. Using `key in tx.reads` as `warm` is a concrete wrong adapter. An access-list entry can also make a key warm without a prior BAL storage read.

## Proposed exclusive module: ReferenceSourceReadings.lean

Do not change common View, StorageView or frozen meter modules. Add these definitions and focused lemmas in a new module:

```lean
abbrev Warm := Set (AccountAddress × ByteArray)
def WarmRelated (w : Warm) (pre : EVM.State) : Prop :=
  ∀ a k, ((a, k.toByteArray) ∈ w ↔
    pre.substate.accessedStorageKeys.contains (a,k) = true)
```

Use `UInt256.toByteArray` key injectivity already proved by ReferenceStorageView. Quantifying all typed keys suffices; arbitrary non-32-byte members are outside the source Bytes32 domain and never consulted.

Define `sourceReading parent v w` by key=`v.stack[0]!`, new=`v.stack[1]!`, address=`v.env.codeOwner`, warm=decide membership in w, original=`ReferenceStorageView.original parent v.storage address key.toByteArray`, current=`ReferenceStorageView.current parent v.storage address key.toByteArray`. The actual Action.load/store witnesses discharge list default cases; original/new are irrelevant to SLOAD and all four fields except warm are irrelevant to ordinary nonstorage price. The function is total for convenience, not an admissibility rule.

Define closed `inputs parent created pre` using:
- address/key/new from actual pre.env.codeOwner / pre.stack[0]! / pre.stack[1]!;
- warm=`pre.substate.accessedStorageKeys.contains (address,key)`;
- original=`if address ∈ created then 0 else parentRead parent address key.toByteArray`;
- current=`SystemSpec.slotW pre.toState key`.

`created` is the fixed **source** initial Tx.created set, not pinned createdAccounts. This yields an actual Inputs function, so existing `Paid` and `pay_completed` can be reused literally.

Export `reading_eq`: input `Related parent v pre`, `WarmRelated w pre`, and `v.storage.created = created` imply `inputs parent created pre = sourceReading parent v w`. This is fieldwise extensionality: Related supplies stack/env/current values; WarmRelated supplies pre-access warmth; created equality supplies source-original value. No premise equates desired charges, refunds or poststate.

Export `action_metadata`: each actual `ReferenceSystemAction.Action kind parent instr v next` preserves env and `storage.created`; load and store record the key in BAL reads; store writes the selected input value. This is a finite analysis of the literal input-computed actions, not a new source interpreter.

Define `warmAfter instr v w` = insert(owner,headKey32) w for SLOAD/SSTORE, otherwise w. Export `accepted_warm`: actual runtime At + accepted Z/StepOk + existing-owner + input Related/WarmRelated imply `WarmRelated (warmAfter instr v w) post`. Inspect actual step: SLOAD always inserts; SSTORE inserts only in its owner-present branch, discharged by Related.owner. Pure/memory/RETURN operations leave this set untouched. Z/stepPre adjustments do not insert storage keys. The proof may use a generic actual set-frame fact for nonstorage operations and the two concrete storage equations. It must not take post-access-set equality as a premise.

A trace consumer should carry `(v,w)` along the **same Viewed/actual XRuns list**, derive source-reading equality at each position, and retain canonical warmAfter evolution. `created` constancy follows by induction; current changes follow existing Action.store/Related, and original stays fixed because only writes/reads change. Define an indexed `ReadingsCoupled` relation containing each actual edge, its actual source Action, sourceReading equality and computed next warm set. Derive it from the same Viewed witness plus initial Related/WarmRelated; propagate actual Related by a same-run induction or consume the actual step action producer, since bare Viewed alone does not store every intermediate Related proof.

Finally use `SystemMeterResources.pay_completed (inputs parent tx.created) h ...` on the same Completed h and attach ReadingsCoupled to its PricedTrace. Now every SSTORE event is `.store` with actual source warmth/original/current/new, and each SLOAD ordinaryCost uses that source warmth. No per-edge payment condition is needed: the existing conservative aggregate payment theorem proves every sentry and debit. Meter.refund:Int/state spill/reservoir continue in the **source meter** only.

## Can pinned warmth be used?

Yes, locally for this successful nonrecursive SYSTEM path, **after** proving initial WarmRelated and the actual step lemma above. The local insertion rule matches source SLOAD/SSTORE under owner existence. It is false to infer equality from the current-slot relation alone, from BAL reads, or from arbitrary outer history. Root SYSTEM dispatch must supply the initial source access set; a default empty pinned substate is not by itself proof the source dispatcher starts with the same set. Ordinary transactions derive source warmth from access lists and frame setup, and recursive calls require rollback-aware access-set transport separately.

Do not copy the pinned original state or refunds as part of this shortcut. Pinned `Csstore`/`State.sstore` obtain original from sigma0 with missing-account zero; source original explicitly zeros accounts in Tx.created even if parent/prestate contains storage. Existing Related constrains current owner slots only, so it cannot establish original equality. Using source parent/created in closed Inputs avoids this unnecessary obligation. Pinned SSTORE costs use the older single-pool schedule (warm surcharge behavior and set/reset costs), while Amsterdam has always-charged warm access, 10000 first-write cost and 97920 state charge. Pinned refundBalance is a UInt256 with modular arithmetic; source refund is signed and uses different constants/order plus spill/refill. No refund or gas equality is required or justified.

## Next implementation scope and remaining boundary

The proposed new module can close: constructive reading constructor; fieldwise exact source-view readings; successful local warm-set preservation; created-set constancy. A following same-Completed trace composition then removes arbitrary Inputs from concrete SYSTEM wrappers without changing existing universal payment theorems.

Still explicit: initial Parent/Tx correspondence to source state dictionaries and current pinned world; source address/key representations; initial access-set correspondence; actual original-created set and account existence; permitted context; source checked numeric/state mutation implementation; operational integration of source metering/effects and failure cleanup. This local successful trace cannot assert global failed-child warmth/BAL parity or adoption of Amsterdam. Original-read computation in a pure Lean function is not a pre-sentry state access; when binding source execution, retain sentry-before-get_storage ordering already modeled by storageCharge.

## Exact inspected source bodies

- `/tmp/eip-adequacy-sources/vm__instructions__storage.py` lines 37-170; SHA256 `d355855a1c50212a4e4753abb533c338919103635755da13bc1e154fcb3ed11b`.

- `/tmp/eip-adequacy-sources/state_tracker.py` lines 244-302, 718-775; SHA256 `ce420ad5682df9051178d298220d1552448e26c37f67be3b604b9f493541cf4a`.

- `/tmp/eip-adequacy-sources/vm____init__.py` lines 228-249; SHA256 `664702bc483736fca3c4ac4bb9e459a24c83f5365b495485c4674d5c41fbe993`.

- `/tmp/eip-adequacy-sources/vm__interpreter.py` lines 145-162; SHA256 `8281535f92be8cfe663033716baf9418ffc37b6c8861f70ac357e41fb6cf4c82`.

- `/tmp/eip-reference-memory-control/vm__instructions__system.py` lines 172, 441; SHA256 `37c888c4f1dfed62f1947ceb457db349be6978da5519234a5b6604f2e6036890`.

- `/Users/thomas/work/eip-8282/direct-closure-implementation/.lake/packages/evmyul/EvmYul/StateOps.lean` lines 124-163; SHA256 `ed24f52c490c1f9a56f4df5a3883533dad884ca2276f58d05cbf9ed3cd386e21`.

- `/Users/thomas/work/eip-8282/direct-closure-implementation/.lake/packages/evmyul/EvmYul/EVM/Gas.lean` lines 97-117, 151-155; SHA256 `9f06caccf5cc8f27f7822392cd1963c8353eb816052f4596321a12c2da707436`.

- `/Users/thomas/work/eip-8282/direct-closure-implementation/.lake/packages/evmyul/EvmYul/State/SubstateOps.lean` lines 10-11; SHA256 `ac84b31b185f12b9f0e57b8845aa88c4c227a87b50880ce5eb86777fecb53b31`.
