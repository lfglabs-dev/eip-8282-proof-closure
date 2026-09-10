# Reference storage transport interface

Faraday, 2026-09-10. Read-only investigation of exact cached proposed EL `0cc100eb190b64b23baba72dac0165652eaec252` and pinned EVMYulLean `b62586650b4f96cc6da25f36574aaa8f329a6420`. No builds, source edits, downloads or interpreter-equivalence claim.

The useful local bridge is equality of **current protected storage reads after successful SLOAD/SSTORE**, with an existing owner and exact operand representation. It must not require equality of reference/pinned refund counters, original-state objects or all rollback metadata. ReferenceStorageGas provides a checked Lean model of the source gas branch arithmetic; connecting actual source execution to that model is still a source-to-formalization obligation.

## Bodies inspected

| Source | SHA256 |
|---|---|
| `/tmp/eip-adequacy-sources/state_tracker.py` | `ce420ad5682df9051178d298220d1552448e26c37f67be3b604b9f493541cf4a` |
| `/tmp/eip-adequacy-sources/vm__instructions__storage.py` | `d355855a1c50212a4e4753abb533c338919103635755da13bc1e154fcb3ed11b` |
| `/tmp/eip-adequacy-sources/vm__interpreter.py` | `8281535f92be8cfe663033716baf9418ffc37b6c8861f70ac357e41fb6cf4c82` |
| `/tmp/eip-adequacy-sources/vm____init__.py` | `664702bc483736fca3c4ac4bb9e459a24c83f5365b495485c4674d5c41fbe993` |
| `/Users/thomas/work/eip-8282/direct-closure-implementation/.lake/packages/evmyul/EvmYul/StateOps.lean` | `ed24f52c490c1f9a56f4df5a3883533dad884ca2276f58d05cbf9ed3cd386e21` |
| `/Users/thomas/work/eip-8282/direct-closure-implementation/.lake/packages/evmyul/EvmYul/Semantics.lean` | `e6bd5acd768d93f50a93f789a301d2f9218b210bdcd3739f95088fd4e5279d7b` |
| `/Users/thomas/work/eip-8282/direct-closure-implementation/.lake/packages/evmyul/EvmYul/EVM/Gas.lean` | `9f06caccf5cc8f27f7822392cd1963c8353eb816052f4596321a12c2da707436` |
| `/Users/thomas/work/eip-8282/direct-closure-implementation/Eip8282/Audit/Integrator/ReferenceStorageGas.lean` | `232a212971a1be7376f1032ea9f6d23b9fa200485a7bbf91e505548bd746877e` |

## Exact reads, writes and order

Reference `storage.py:39-67` SLOAD pops the last stack word as key and encodes it with `to_be_bytes32`. If `(current_target,key)` is warm, charge100; otherwise add it to `accessed_storage_keys` and charge2100. Then `get_storage`, push value and increment PC. Cold warmth insertion thus precedes a possibly failing charge. `get_storage` also inserts the key into a distinct BAL read set.

Reference `storage.py:80-170` SSTORE rejects static first, then pops key, then new value. It checks execution gas >=max(accessCost,2301) before touching state. Cold access is marked warm after that check, then original/current are read. Refund changes and state refund precede execution charge; execution charge precedes state charge; only then `set_storage` mutates storage and PC increments. Exact classification and resource bounds are in the separately reviewed ReferenceStorageGas module. A resource bridge must bind classify arguments to these actual original/current/new/warm values; it cannot pass arbitrary predicted values.

Pinned `Semantics.lean:369-372` routes SLOAD/SSTORE to corresponding operations; `StateOps.lean:124-167` loads through `executionEnv.codeOwner`, returns default0 if owner is absent, and adds accessed key. SSTORE reads current map, fixed σ₀ original slot, computes modular UInt256 refund balance, then updates an existing account only. If owner is absent, the final `lookupAccount ... option self` leaves state unchanged. This differs from reference `set_storage`'s assertion that the account exists. Therefore owner existence is a necessary local relation premise, to be produced from installed code and preserved along the runtime. It is not justified by assigning the same numeric address alone.

Both successful writes assign exactly the supplied256-bit word to the key; reference `state_tracker.py:433-458` writes `storage_writes[address][key]=value` even when zero. A finite-map representation may remove zero or retain zero; use extensional default-zero reads, not dictionary/tree structural equality. Pinned `SystemSpec.slot_sstore` under HasOwner gives the exact if-key-equal update equation; `AppendSpec.other_account_sstore` frames every other account.

## Reference state is layered

`state_tracker.py:44-92` defines BlockState and TransactionState, with separate account, storage and code dictionaries. Storage is not embedded in Account as in the pinned world.

`get_storage`, lines244-273: add `(address,key)` to transaction `storage_reads`; look first in transaction storage writes, then parent block writes, then `parent.pre_state.get_storage`. Presence tests matter: a stored zero overrides an earlier nonzero. PreState default-zero behavior is an interface obligation at the bottom layer, not implemented by this function itself.

`get_storage_original`, lines276-302: if address belongs to `created_accounts`, return0; otherwise parent block writes then prestate. It deliberately ignores transaction writes. Thus original is transaction-entry state including earlier block transactions, not block-entry/genesis state, and new-account original values have an additional created-account override.

`set_storage` asserts `get_account_optional(...) is not None`. That account lookup and the PreState protocol must be represented consistently, including any account deletion overlays. Merely defining a slot function from storage dictionaries without account validity is insufficient for a whole-state adapter, though a protected installed owner avoids deletion locally.

`incorporate_tx_into_block`, lines775-825: calls BAL builder before merge; merges account/storage/code writes into parent, then clears transaction writes/created/transient sets and resets reads. For successful committed storage observables, prove merge lookup equals pre-merge transaction overlay lookup. Do not claim equality of their data structures or transaction-original views across the boundary.

## Rollback metadata and concrete divergences

`copy_tx_state`, lines718-749, deep-copies account/storage/code/transient writes but **shares** parent, created_accounts, storage_reads and account_reads. `restore_tx_state`, lines752-769, restores only those four write/transient objects. BAL reads and created_accounts are not restored. This is explicit source behavior, not a guess about generic Ethereum rollback.

`process_call`, interpreter lines419,455-473, snapshots before value transfer. Exceptional halt restores state gas then forfeits execution gas; REVERT restores state gas while retaining unspent execution gas; both restore transaction write overlays on error. Child logs/warm access sets are incorporated only on success (`vm/__init__.py:193-249`), whereas shared BAL read sets survive failure. These are separate sets: never identify `storage_reads` with `accessed_storage_keys`.

The shared created_accounts means failed creation history can affect later reference original-storage lookup. Pinned State.sstore uses σ₀ lookup with no created-set override. For a no-child exact runtime call, membership can be fixed along that local path, but may already be true at entry. Avoid asserting original equality generically. A stronger original relation needs a proved adapter that selects a shadow σ₀ matching reference original slot semantics for this frame; actual transaction-history composition must explain compatibility. The generic conservative ReferenceStorageGas upper bounds hold for every original/current triple, so resource liveness does not need original equality across evaluators.

Refund/gas equality is false as a general transport objective: source refunds are signed integers with storage-write refund10000/clear11616 and separate state credit97920; pinned refunds are modular UInt256 with legacy pricing and no state reservoir. Access cost timing also differs. Successful value updates can still agree under independently payable charges. A source OOG need not match a shadow-gas pinned outcome; failure transport must use direct source rollback rather than successful replay.

## Minimal relation

For a protected owner a and current source transaction S / pinned machine p:

1. `p.executionEnv.codeOwner` corresponds to actual reference current_target a; exact installed runtime and existing account on both sides. Caller/static/other runtime inputs belong to broader entry relation.
2. Stack relation identifies reference end-pop order with pinned head-first order; at SSTORE reference top is key, next is new value. Word relation is exact bounded natural value, key bytes are canonical32-byte big-endian encoding and injective.
3. For every256-bit key k, `ref_get_storage_view S a (encode32 k) = worldSlot p.accountMap a k`. Use a pure read view plus a separate lemma explaining read-tracking side effects.
4. PC/memory relation is carried by Russell's decoder/control/memory lane. Gas/refund meters are related by sufficient-resource predicates, not equal values. A separate optional warmth relation equates actual warm pairs if exact gas accounting needs it; a cold upper bound avoids needing it for resource sufficiency.
5. For framing across multiple protected owners, extend3 to all relevant addresses; do not demand account balance/nonce/code-hash/trie identity merely to prove a storage step.

## Concrete next local lemmas, non-circular

A. `overlay_write_read`: purely defined source storage overlay, owner-present, canonical encoded key -> reading after literal set equals if queriedkey=key then value else prior read. Also `read_tracking_preserves_view`. This is a source-shaped data lemma, not yet execution correspondence.
B. `successful_sload_values`: actual reference SLOAD step plus entry relation yields equal loaded word, related post stack/storage; update warmth relation separately. It may assume actual reference step success for safety transport, but must not assume desired loaded word.
C. `successful_sstore_values`: actual reference successful SSTORE step + entry relation/owner -> relate post storage to actual pinned sstore endpoint using A and SystemSpec.slot_sstore. No supplied post-storage equality, original/refund equality or queue invariant. Need actual accepted pinned step produced by independent shadow-resource lemma.
D. `funded_reference_sstore`: actual pre-op environment and source-read values, static=false, sufficient sentry/execution/reservoir -> source charge sequence succeeds by a **proved evaluation equation** to ReferenceStorageGas.storageCharge; then actual set_storage and stack/PC update. This equation remains OPEN because the Python evaluator is not a Lean constant in the current source. Merely wrapping the transcription's theorem is not that adapter.
E. `rollback_storage_view`: actual restore_tx_state following snapshot returns pre-call current storage view (parent unchanged), even though BAL/created metadata differ. Pair separately with success-only warm/log incorporation. For current slots this is straightforward overlay equality; original view requires additional created-set reasoning and is not automatically restored.
F. `commit_storage_view`: actual transaction-to-block dictionary merge preserves selected current storage reads, under lower-layer PreState/account interpretation.

## Checked boundaries

UInt256 and reference U256 share256-bit range, but encoding32 injectivity and endianness need proved byte lemmas. Reference set/get use Bytes32, so no natural-to-key truncation should be hidden. Stack arity and static checks must come from actual decoded accepted execution. Small memory offsets are not relevant to SLOAD/SSTORE directly; gas numeric types and refund conversions require their own bounded/signed treatment. ReferenceStorageGas uses Nat execution/reservoir/spill and Int refund; checked Python numeric wrapper construction correspondence is still external, including every addition in refund credit. Its conservative_success proves lower bounds without refund reliance, not all upper bounds needed for checked wrapper representability.

No new concrete counterexample to successful protected storage-value transport was found. The missing-owner behavior, original-created override, shared rollback metadata and refund arithmetic above are concrete definition-level divergences that rule out stronger indiscriminate full-state equality. No Lean source or proof was changed in this investigation.
