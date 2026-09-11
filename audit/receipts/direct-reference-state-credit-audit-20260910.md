# Pinned Amsterdam state-credit audit

Pin: `0cc100eb190b64b23baba72dac0165652eaec252`. Read-only source audit, not a Lean theorem, Python execution, canonical counterexample, or fee-exploit claim.

## Classification

No valid fresh-transaction negative-net-state example was established. The source docstring allowing a negative signed counter is not evidence of one. All four direct state-refund call sites are identifiable: one SSTORE refill and three refunds of a prior NEW_ACCOUNT charge on denied/failed creation or CALL. AUTH7702 and SELFDESTRUCT do not directly credit state gas. Source inspection supports a charge/refund pairing invariant for fresh transactions, but a universal nonnegative theorem remains OPEN until actual source storage/account lifecycle, frame snapshots and meter histories are linked. Do not promote protected-runtime Coupled nonnegativity to all source execution.

A nested frame may legitimately clear a zero-original slot set by its caller and thereby have negative local state charge-minus-credit. Its caller paid the earlier charge. Successful incorporation and spill repayment reunite the credit and charge; failure discards the credit through baseline restoration. This is a local accounting possibility, not a demonstrated negative whole-transaction counter.

## Complete scope and evidence

The untruncated pinned GitHub tree lists49 Python files under `src/ethereum/forks/amsterdam/`. Every body was scanned, including all opcode and precompile modules; existing cache bodies were reused only after Git blob SHA1 equality. Missing bodies were fetched from official pinned raw GitHub, without execution or new dependencies. All49 Git blob hashes and SHA256s, full bodies and acquisition sources are in `/tmp/eip-state-credit-scan-faraday/sources.json`; tree evidence is `/tmp/eip-state-credit-source-tree-faraday.json`; AST results in `scan.json`. Python3.12 parsed all49 files; the installed default3.9 parser could not parse match syntax and was not used for the completed scan. External prior-fork imports are Header type bindings, not inherited gas-mutating opcode implementations.

AST scan found28 calls to named state-accounting helpers and20 direct attribute writes across gas.py and vm/__init__.py. Full direct-write list below includes baseline and committed spill, not just reservoir. Constructor initializations and returned TransactionOutput fields are separate value copies, not hidden credits.

## Direct credits and required pairing

| Source | Credit | Exact pairing / outstanding producer |
|---|---|---|
| vm/instructions/storage.py150 | STORAGE_SET=97920 | current differs from new, original=new=0. Prior successful zero-to-nonzero SSTORE must be in same transaction live slot history, possibly another frame. Actual failure baseline restoration must be paired to same storage snapshot. |
| vm/instructions/system.py187 | NEW_ACCOUNT=183600 | CREATE/CREATE2 internal_create charged at116 iff target not alive. Reached only after dispatched child returns error. Early depth/balance/nonce failure at101-107 precedes charge; collision after withholding has no refund and requires account-deployable/alive implication. |
| vm/instructions/system.py398 | NEW_ACCOUNT=183600 | generic_call preflight depth/balance denied: returns exact withheld grant and drained state reservoir, then refills only params.new_account_charged. Actual CALL constructor must link this flag to earlier552 charge. |
| vm/instructions/system.py457 | NEW_ACCOUNT=183600 | generic_call entered child errors: incorporate settled child, then conditional refund of same earlier caller charge. No success refund. |

## Other charge classes

- AUTH7702 (`vm/eoa_delegation.py296,314`): NEW_ACCOUNT if authority does not exist; AUTH_BASE=23*1530=35190 for first net-new delegation indicator relative to transaction prestate/delegation_set_for. No credit_state_gas_refund calls. Setting then clearing a delegation retains AUTH_BASE charge. Top create_evm commits these charges at interpreter.py168; ordinary code failure preserves them. Predispatch failure uses restore-to-entry and undoes them with the preparation snapshot.
- CREATE account charge described above; deployed-code state charge interpreter.py381-384 is len(code)*1530 after execution hash cost. No direct code-state credit. Deployment errors restore creation snapshot/state baseline and then forfeit execution; require matching source frame and parent charged-account flag.
- Top dispatch account creation: interpreter.py135 (value recipient nonalive),186 (top creation prestate EMPTY_ACCOUNT). No direct credit; ordinary/predispatch rollback handles its state fate. Top authorizations commit before later dispatch charges, so baseline/committed spill must stay distinct.
- SELFDESTRUCT system.py751-764: beneficiary nonalive plus nonzero source balance triggers NEW_ACCOUNT and execution ACCOUNT_WRITE; execution charge precedes state charge. No direct state refill or destruction credit; only enclosing rollback refills. Deferred account deletion is not credited here.
- CALLCODE/DELEGATECALL/STATICCALL variants use common generic_call with their actual flags/grants; scan found no extra direct state credits outside the common paths. Field/flag source extraction remains required.

## Meter transitions and source settlement

- gas.py423-444: state charge consumes reservoir then execution spill; checked failure branches are real.
- gas.py604-626: state credit returns min(amount,spill) to execution, reduces spill, credits remainder to reservoir. This alone permits arbitrary overcredit; actual provenance is essential.
- gas.py469-500 commit: reservoir<=baseline assert; baseline lowers, spill becomes committed spill. No net-state credit.
- gas.py503-527 restore: outstanding spill returns to execution, reservoir resets baseline, refund counter0; committed spill preserved.
- gas.py530-566 restore-to-entry: baseline<=entryGrant and refund0 asserted; outstanding AND committed spill restored, reservoir/baseline=grant.
- gas.py629-656 repay: min(reservoir,spill) transferred to execution after successful child merge; signed state usage and pool sum unchanged. Failure does not run repayment.
- gas.py699-744: parent reservoir drained into exact child grant and returned intact on denied call. Returning an arbitrary supplied grant is not conservation; actual split identity must be extracted. CALL execution stipend is separately covered by prior CALL_VALUE.
- vm/__init__.py226-249: child committed spill0 asserted; failed child must have spill0/refund0/reservoir=baseline. Core fields absorbed for all outcomes; success-only repay/log/SD/warm merge.
- interpreter.py455-474: exceptional error restore THEN execution forfeit; REVERT restore only; both restore same transaction writes snapshot. state_tracker.py756-772 restores account/storage/code/transient writes, not shared created/read metadata.
- gas.py568-601 tx_state_gas_used = entryGrant - finalReservoir + outstandingSpill + committedSpill, signed. settle_transaction_gas uses max(0,net_state_gas_used); that clipping is not a proof of nonnegative raw usage or permission to drop negative corrections in another bound.

## Account lifecycle seam that must not be assumed away

interpreter.py346-365 explicitly allows historical pre-Spurious-Dragon empty-code/nonce-zero accounts with preexisting storage to be creation targets: process_create destroys that storage, marks created, and increments nonce. state_tracker.py276-301 treats original storage as zero for created accounts. Its created marker intentionally survives rollback (529-545), while old storage may be restored. The comment says this is harmless because the restored account had no code and cannot execute storage reads. This is a semantic reachability obligation, not a storage-arithmetic identity. Do not assume all nonce-zero/code-empty canonical accounts had empty storage, or apply a fixed-original all-key potential unchanged through CREATE/rollback. An account-lifecycle adapter must show either every executable storage frame has the matching charged live-slot history, or account resets/created-marker changes are covered by explicit potential correction.

## Minimal next proof interfaces

1. Actual source snapshot-linked frame relation carrying transaction-current/original/created/account/code projections, full meter baseline/committed spill and actual grants. No global foreign-source/pinned trace equivalence.
2. Per-class charge receipts: storage same-slot live history; account NEW_ACCOUNT paid-token keyed to exact dispatch and returned-failure branch; AUTH/code/SD nonnegative charges and their source rollback/commit boundaries. Never an arbitrary new_account_charged flag detached from its actual charge.
3. Recursive source frame composition: successful child merges charges/credits and repay; failed child resets to exact entry storage and meter baseline, with predispatch reset distinguished. Derive parent-child pooling from actual grants, including CALL stipend cost.
4. Fresh source TransactionState starts empty write/created overlays and full meter spill/committed0; exact source validator/block adapter constructs it. Then prove transaction-wide signed counter nonnegative (if confirmed), or retain a rigorously bounded negative correction. Current analysis supplies no valid counterexample and no universal theorem.

## Direct field writes (complete AST scan)

- `vm/__init__.py:239`: `gas_meter.state_gas_left += child_meter.state_gas_left`
- `vm/__init__.py:240`: `gas_meter.state_gas_spilled += child_meter.state_gas_spilled`
- `vm/gas.py:439`: `gas_meter.state_gas_left -= amount`
- `vm/gas.py:442`: `gas_meter.state_gas_left = StateGas(Uint(0))`
- `vm/gas.py:444`: `gas_meter.state_gas_spilled += remainder`
- `vm/gas.py:498`: `gas_meter.state_gas_committed_spill += gas_meter.state_gas_spilled`
- `vm/gas.py:499`: `gas_meter.state_gas_baseline = gas_meter.state_gas_left`
- `vm/gas.py:500`: `gas_meter.state_gas_spilled = StateGas(Uint(0))`
- `vm/gas.py:525`: `gas_meter.state_gas_spilled = StateGas(Uint(0))`
- `vm/gas.py:526`: `gas_meter.state_gas_left = gas_meter.state_gas_baseline`
- `vm/gas.py:562`: `gas_meter.state_gas_spilled = StateGas(Uint(0))`
- `vm/gas.py:563`: `gas_meter.state_gas_committed_spill = StateGas(Uint(0))`
- `vm/gas.py:564`: `gas_meter.state_gas_left = state_gas_reservoir`
- `vm/gas.py:565`: `gas_meter.state_gas_baseline = state_gas_reservoir`
- `vm/gas.py:625`: `gas_meter.state_gas_spilled -= from_gas_left`
- `vm/gas.py:626`: `gas_meter.state_gas_left += amount - from_gas_left`
- `vm/gas.py:652`: `gas_meter.state_gas_left -= repayment`
- `vm/gas.py:653`: `gas_meter.state_gas_spilled -= repayment`
- `vm/gas.py:719`: `gas_meter.state_gas_left = StateGas(Uint(0))`
- `vm/gas.py:744`: `gas_meter.state_gas_left += state_gas_reservoir`

## Body hashes

- `src/ethereum/forks/amsterdam/__init__.py`: `96bb8285ee383d6759c90fef8f43e79eb004e252c95423a93a13cc71f16324aa`
- `src/ethereum/forks/amsterdam/block_access_lists.py`: `fc17da88c2dc89065f6f6c87cb1c5ecf2b16c9d23b8010516f4d47c43d013800`
- `src/ethereum/forks/amsterdam/blocks.py`: `ec2cdd7fae64861b76c225573aac20be18ddb39e1fb2c2e0015a5cd0c4d2852c`
- `src/ethereum/forks/amsterdam/bloom.py`: `c594a4d3252e9f0126e9952e09a3575309780c8e086296c0b74682033ebe9a76`
- `src/ethereum/forks/amsterdam/exceptions.py`: `e13c789de279056f78ed35ed89e15ae600dd20fca5b6dfab0e1068bcba37053d`
- `src/ethereum/forks/amsterdam/fork.py`: `dd0d069cbd0ba3e60e3f927c0e2d41be40958c6415be039ee29d6074eb2950da`
- `src/ethereum/forks/amsterdam/fork_types.py`: `3e0013e251867df02aca7b746b77403b36b41d73f7c4158bed09964838c935ca`
- `src/ethereum/forks/amsterdam/requests.py`: `1950f374f27fb3999534f3b11fdfcc2e5a8fa5a2ef14fa5dff6803849fe04ccf`
- `src/ethereum/forks/amsterdam/state_tracker.py`: `ce420ad5682df9051178d298220d1552448e26c37f67be3b604b9f493541cf4a`
- `src/ethereum/forks/amsterdam/transactions.py`: `1fb6202062805d892a2a0100f46220d7a762e88a049ab9871b53f5159f6e0b25`
- `src/ethereum/forks/amsterdam/utils/__init__.py`: `bb6131a66d7f7c253a52ed45dbc36f88be31a6a74232afe50784df33796c4983`
- `src/ethereum/forks/amsterdam/utils/address.py`: `08e1f1d687c61293d52aed5b1d97807c5db8b3e130df54d727cc3c9ebd3009cb`
- `src/ethereum/forks/amsterdam/utils/hexadecimal.py`: `73292a79a9ce8a3f6b5c82c81de11a16f105667267f00fcdc6f801a2877b36b6`
- `src/ethereum/forks/amsterdam/vm/__init__.py`: `664702bc483736fca3c4ac4bb9e459a24c83f5365b495485c4674d5c41fbe993`
- `src/ethereum/forks/amsterdam/vm/eoa_delegation.py`: `260a8938958e309011b1c6f49c011ca0505784a580d2dd19929bb5ea18624e24`
- `src/ethereum/forks/amsterdam/vm/exceptions.py`: `e3e4b0b24c5b5702a64851d2ac675d1d2fc526aa3f1a439b17d5c2d22c569a01`
- `src/ethereum/forks/amsterdam/vm/gas.py`: `41d97e32f68585f99276f164b828b9091c112a05df31002594276d8e1feacc0c`
- `src/ethereum/forks/amsterdam/vm/instructions/__init__.py`: `2bef9321753167d80f62eb1f861120412de5b9561cba38b6832f96a5535f617f`
- `src/ethereum/forks/amsterdam/vm/instructions/arithmetic.py`: `7bd39760ffa9c27334129a89974d863362579dc1d221d09983532dec4be81d9f`
- `src/ethereum/forks/amsterdam/vm/instructions/bitwise.py`: `e48944ae09c914f44e348e68de107f3af52233504772a8d6077e6d9bd1449f22`
- `src/ethereum/forks/amsterdam/vm/instructions/block.py`: `6092b4679b0b4f85021e0a62745b75fa4a2bae732dea6982d67de19e0aec52ab`
- `src/ethereum/forks/amsterdam/vm/instructions/comparison.py`: `45a320c05063bb8d1d281a5383f73a936961552e3b29c08f0e9ac7ccc8916700`
- `src/ethereum/forks/amsterdam/vm/instructions/control_flow.py`: `b6b481918211a8e86ded3acd9ec13e940ba05860786e584913478aec13abc0c3`
- `src/ethereum/forks/amsterdam/vm/instructions/environment.py`: `8c57bd699b99ff8b4d8e41e6a9c89cd1a03dda8160bf1d6dffe091932ec03657`
- `src/ethereum/forks/amsterdam/vm/instructions/keccak.py`: `21cc2e1b86a87f22bf5ea969aeca89f66bcf2acb6b49e6233310fab82e7666d1`
- `src/ethereum/forks/amsterdam/vm/instructions/log.py`: `f62f6cb589811e3a58c3a4644fcf7b979a506df1f09213e2a96e7988a4574874`
- `src/ethereum/forks/amsterdam/vm/instructions/memory.py`: `77fec2a002eb27f34af82bd4ce5db98d593033f220a91eb65f56ff9496135278`
- `src/ethereum/forks/amsterdam/vm/instructions/stack.py`: `1065b389a6d8e4a0ed72945b0be5e67b18484836695041aae83bbc08484caace`
- `src/ethereum/forks/amsterdam/vm/instructions/storage.py`: `d355855a1c50212a4e4753abb533c338919103635755da13bc1e154fcb3ed11b`
- `src/ethereum/forks/amsterdam/vm/instructions/system.py`: `37c888c4f1dfed62f1947ceb457db349be6978da5519234a5b6604f2e6036890`
- `src/ethereum/forks/amsterdam/vm/interpreter.py`: `8281535f92be8cfe663033716baf9418ffc37b6c8861f70ac357e41fb6cf4c82`
- `src/ethereum/forks/amsterdam/vm/memory.py`: `50b962d2477ddcaeeb87d2ea56073b3691d93ea8d41ab29eb8b77605c6efef95`
- `src/ethereum/forks/amsterdam/vm/precompiled_contracts/__init__.py`: `dec628e3d240b0912c9fb338c54704dc4d5018af7062bb4b79a909732453b188`
- `src/ethereum/forks/amsterdam/vm/precompiled_contracts/alt_bn128.py`: `53b9931a8dbe8a33e64e6251bf4b42565ac518189d9aff0fd825c29f41f40ec2`
- `src/ethereum/forks/amsterdam/vm/precompiled_contracts/blake2f.py`: `41c694322942be234ca55165b870d0b2889b21160fc2254f7c10e7cea3710952`
- `src/ethereum/forks/amsterdam/vm/precompiled_contracts/bls12_381/__init__.py`: `f0f1b6ee4b350c97e0cb723db8e283cdb335bedbe0d777782ab3b8049e123ea3`
- `src/ethereum/forks/amsterdam/vm/precompiled_contracts/bls12_381/bls12_381_g1.py`: `cc55a0ca524b677d8bf6e0a2fc5aa27f233c1b4ae47305ffe13d233ebea785c9`
- `src/ethereum/forks/amsterdam/vm/precompiled_contracts/bls12_381/bls12_381_g2.py`: `a4236833dd793d53cb5eb10a7298c6aa7ffe6d0a8ce85e8279e4d55cf47f5e5f`
- `src/ethereum/forks/amsterdam/vm/precompiled_contracts/bls12_381/bls12_381_pairing.py`: `4de13019e4771f6c283e603434c5b6f759a9528934d7630c7d4e0cda1c984942`
- `src/ethereum/forks/amsterdam/vm/precompiled_contracts/ecrecover.py`: `4eee29a682d9dbadb943a18adbfbe2e4d3f980c1dd93677288d457dbb373d7bc`
- `src/ethereum/forks/amsterdam/vm/precompiled_contracts/identity.py`: `a09e791bda2962a6f49bd3b7d4018931eef38b17908a8fd0c756d0122bbbc733`
- `src/ethereum/forks/amsterdam/vm/precompiled_contracts/mapping.py`: `5a9a33067eb1998ced0d5973d039c850efd55cbbd61a3defdc20f8682643983c`
- `src/ethereum/forks/amsterdam/vm/precompiled_contracts/modexp.py`: `40cbb94cb2eeab3de3a0c7b063713279b3f2d190c4aea09dd6d2a5c473e593c2`
- `src/ethereum/forks/amsterdam/vm/precompiled_contracts/p256verify.py`: `16cfeb2e172fb225b99999ea894d7ec1e0e641c767f6c693ac725a7e4eaebd98`
- `src/ethereum/forks/amsterdam/vm/precompiled_contracts/point_evaluation.py`: `3c5dc9d6b6e1d1b2c3c7c8400c3b7b6d567463351aa07a111db5a3e54d8246f9`
- `src/ethereum/forks/amsterdam/vm/precompiled_contracts/ripemd160.py`: `179a86485e19da118998345387ac329d6322377a33c0a29dfcdff965e696b1fe`
- `src/ethereum/forks/amsterdam/vm/precompiled_contracts/sha256.py`: `3913d21b41fefd2d980052273121ad431c3ea434722ac1552290b11493d350a8`
- `src/ethereum/forks/amsterdam/vm/runtime.py`: `628c98137eddaec3a4902bd1ce5f42c2fc27f9c79cb9eba36d4d3a5d990fa7af`
- `src/ethereum/forks/amsterdam/vm/stack.py`: `20cdb907098ae500c47abc6a1437cb9e4cdb5809f6c40b7d8935038aedd57b2a`
