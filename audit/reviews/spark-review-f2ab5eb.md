# Independent review — SYSTEM success (a612bbb) + checked SYSTEM (5cd0fe5) + SYSTEM block pair (cb65536) + ordinary block incorporation (f2ab5eb)

Reviewer: independent (Claude sub-agent, fresh context, not the author)
Source commits: a612bbb, 5cd0fe5, cb65536, f2ab5eb
Head: 681d186 (branch codex/source-ordinary-block-candidate-20260911)
Started at: 2026-09-11T10:22:02Z

## Scope items reviewed (per receipt)

### a612bbb — SYSTEM success (`direct-system-success-review-status-20260911.json`)
- "All transitive output stack/PC/context/owner/payment premises are produced, not added to the public domain." — OK. `ReferenceCheckedSystemDrainTotal.verified` and `ReferenceCheckedSystemSuccess.{erased,owner,execution}` only take `history`, `emptyHash`, `accountsParent`, `codeParent` and `loaded` as inputs. Stack bound, PC fit, memory alignment, owner presence and paid-event acceptance are derived inside `ReferenceSystemStackBound.handler`, `ReferenceCheckedSystemForward.handler`, `ReferenceCheckedSystemTraceForward.{selected,coupled}`, `ReferenceCheckedSystemReturn.evaluated`, `ReferenceCheckedSystemSuccess.owner` and consumed internally — no such premise appears in the public consumer.
- "Source Whole -> exact prefix continuation -> paid RETURN, arbitrary finite computation; actual gas distinct from replay." — OK. `ReferenceCheckedSystemWhole.evaluated` composes `coupled` prefix with `Return.evaluated`, computes fuel as `potential meter + 1` (arbitrary finite), and `DrainTotal.verified` records `receipt.meter = ended.meter`. Replay budget (`depExtra`, `extExtra`) is separate from evaluator meter.
- "Source frame/view/meter equality after fresh zero-value entry; computed account evaluator identified through projection/determinism." — OK. `ReferenceCheckedSystemSuccess.erased` proves `sameView` and `sameMeter` from `ProtocolSystemDispatchExtraction`, and `.execution` uses `ReferenceCheckedAccountEvaluator.evaluated` (projection) plus `owner` to identify `same.symm.trans paidRun` — the same computed evaluator.
- "SystemDrainTotal has same actual result/receipt/journal as old safety; no unproved canonical SYSTEM pair/block incorporation or History applicability." — OK. `DrainTotal.verified` reuses the exact fields of `SystemTotal.verified` and strengthens the result-tag to `.terminal ended` with `ended.halt = .returned`; no block-pair or History-canonicalization claim appears.
- "Injected sentry/terminal/decoded-cost mutants and original bytecode kill-lines." — OK. `Eip8282/Tests/ReferenceSystemSuccess.lean` exposes `sentry_not_nominal_payment`, `return_payment_required`, `decoded_payment_required`, all decidable/finite; comments describe them as "injected local opcode/resource mutations … not canonical histories".

### 5cd0fe5 — checked SYSTEM (`direct-checked-system-review-status-20260911.json`)
- "Same actual computed outcome, prefix and final dispatch; no supplied endpoint or success." — OK. `ReferenceCheckedSystemTotal.verified` binds `events`, `result`, `finalAccounts` via `ReferenceCheckedSystemExecution.computed` and `.extracted`; the theorem parametrizes on ALL outcome types (returned/reverted/eof/failed) via `ReferenceCheckedSystemOutcome.Claims`. There is no `.terminal`/`.returned` premise supplied to `verified`.
- "Fresh mandatory empty-data SYSTEM entry and code presence; zero-value transfer, no ordinary fee admission." — OK. `entered` is `enter … (call kind c).value true`, and `call kind c` uses `ProtocolSystemCalls.call kind ... 8503 ByteArray.empty` (empty calldata). No `RefundAccounting.Context`, prepayment or sender-fee debit occurs in the SYSTEM entry pipeline. Mutation `entry_has_no_fee_debit` codifies this.
- "Same receipt/storage/account journal and checked output gas/refund conversions, including failure." — OK. `ReferenceSystemOutputReceipt.settled` covers success/EOF/failure; failure branches into `.returned` via `ReferenceCheckedFrameOutcome.settle` with revert or exceptional metadata. `Facts` from `ReferenceSystemOutputMeter` gives U256 refund conversion.
- "History and source semantics remain meaningful external domain; no source payment-to-success or canonical pair claim." — OK. `SystemTotal.verified` explicitly does not assert successful drain (documented in its module header, and no `ended.halt = .returned` in its statement); the successful-drain claim is factored into the separate `SystemDrainTotal.verified` from a612bbb.

### cb65536 — SYSTEM block pair (`direct-system-block-review-status-20260911.json`)
- "Unmerged parent used for BAL comparisons; key-length check before big-endian conversion; U32 index preservation." — OK. `ReferenceSystemBlockAccess.update` filters via `parentRead parent owner key = value` on the unmerged parent, then `decodeKey` (length check first via `if 32 < bytes.size then none else …`), before any `add` (which does not change `builder.index`). `update_index` proves the index is preserved.
- "Every write present exactly once, no repeated key; account/code write journals empty; account/storage reads merged; transaction journals cleared." — OK. `entries_unique` (Nodup), `entries_complete`+`entries_sound`, `Certificate.journal` produces `settled.accounts.writes = (before Hash).accounts.writes` (empty), `settled.codeWrites = (before Hash).codeWrites` (empty). `incorporate` returns `(_, before Hash)` — fresh tx journal.
- "Intermediate parent/world relation, Exit invariant, finite write support, key-conversion success, empty account/code writes and warmth are conclusions, not inputs." — OK. `ReferenceCheckedSystemBlock.verified`'s domain hypotheses are only `history`, `emptyHash`, `accountsParent`, `codeParent`, `builder`, `accountReads`, `storageReads`, and per-kind `loaded`. Middle world/reads (`middleInv`, `depReads`), Exit invariant, finite support (`support`), key-conversion (`entries_typed`), empty writes (`journal.1`/`journal.2.2.1`), warm continuity (`coherent`) all appear on the RHS.
- "No independent intermediate equality, successful endpoint, final meter, final journal or new funded History at Exit is assumed." — OK. Verified: no `runOn .exit … some ...` hypothesis; instead constructed via `ReferenceSystemBlockWorld.rebase` from `middleInv`. `Certificate` fields (`halt = .returned`, `receipt`, `journal`) are conclusions in `ReferenceSystemBlockPair.one`.
- "No claim of canonical funded histories, complete call-tree occurrence accounting, global gas, deployment, SYSTEM authorization, inhibition, or upgrade applicability." — OK. Module headers and DIRECT-CLOSURE.md sec. "Preserved SYSTEM candidate" explicitly enumerate these as OPEN. Nothing in `verified` produces a `ReleaseCandidate.History` on `extPost.accountMap`.

### f2ab5eb — ordinary block incorporation (`direct-ordinary-block-review-status-20260911.json`)
- "Same fee-finalized ordinary source journal incorporated into source block." — OK. `ReferenceFullFeeBlockTotal.verified` consumes `ReferenceFullFeeBlockReceipt.verified`, which composes `ReferenceFullFeeTotal.verified` (unchanged fee-finalized journal) via `ReferenceFullFeeBlockNonce.verified`; `settled cert = journal … cert.receipt` uses the same `ReferenceSourceFeeFinalization.finish` pipeline.
- "One actual computation supplies the three conditional claims, exact frame receipt, full logs/rollback/meter, ordered fee credits, checked sender nonce." — OK. `Certificate` has ONE `events, core, finalAccounts, finish, finalWarm, final, receipt` bundle plus `actual`, `claims`, `full`, `trace`, `last`, `settled`, `fees`, `nonces`, `senderNonce`, all bound to the same tuple.
- "Final journal has finite, duplicate-free account writes over sender/contract/beneficiary and finite storage writes over the contract; code hashes unchanged; code write overlay empty." — OK. `accountSupport` restricts writes to `addresses kind tx`; `writes : Writes … keys` bounds storage writes to `ReachableCalls.address kind`; `hashes` proves hashes unchanged, `code` proves `codeWrites = fun _ => none` (composed with `freshCode`). `entries_unique`/`entries_sound`/`entries_complete` (BlockAccess and BlockSettlement variants) codify Nodup and completeness.
- "Account BAL updates precede storage BAL updates; both compare against unmerged block parent. U32 index preserved. Sender nonce converts through checked U64 path; other nonces unchanged. Cumulative reads merged; returned transaction journal is fresh." — OK. `ReferenceOrdinaryBlockSettlement.incorporate` bind-order is `ReferenceOrdinaryBlockAccess.update` (accounts, against `block.accounts`) THEN `ReferenceSystemBlockAccess.update` (storage, against `block.storage`); both use unmerged parents. `builder.storage.index` is preserved via `update_index` composition. `checkedNonce` in `ReferenceOrdinaryBlockNonce.admitted_nonce`; other nonces stated as `+ (if a = tx.sender then 1 else 0)` (0 for others). `merged` unions reads; second component of `incorporate` is `ReferenceCheckedSystemEntry.before Hash` (fresh).
- "Two initial conditions are explicit additions: source sender nonce read equals admitted old sender nonce; initial account/code write overlays are fresh. Final support, conversions, merge and reset are conclusions, not premises." — OK. `sourceNonce` and derivations of `freshAccounts`/`freshCode` (via `beforeAccounts` in Certificate and initial `before` shape) appear as HYPOTHESES; final support (accountSupport, writes), U64 conversions (senderNonce, nonceExact), merge success (`incorporate = some (final, before Hash)`) and fresh reset all appear on the RHS.
- "No canonical Ethereum production of initialized funded History or next-transaction History, complete admission, deployment, SYSTEM authorization, inhibition or upgrade applicability claimed." — OK. `ReleaseCandidate.History deposit exit tx.world` is a HYPOTHESIS; no `ReleaseCandidate.History _ _ commitAccounts …` conclusion. DIRECT-CLOSURE.md explicitly lists these as OPEN.

## Findings

None (no BLOCKING or ADVISORY findings).

Details of individual checks:
1. `sorry`/`admit`/stub — none found in any of the 35 module files across the four commits (grep across all Integrator files for `\bsorry\b|\badmit\b` returns empty; also no `sorryAx` mentions).
2. Axiom drift — no `axiom` declarations introduced in changed source files (grep `^axiom ` returns none; existing hits in `Eip8282/Audit/Guarantees/PDrain1.lean:416` and `PControl1.lean:551` are inside comments/documentation only). All 79 tracked exports across the four axioms JSONs list only `propext`, `Classical.choice`, `Quot.sound`.
3. Renamed premises restating the conclusion — none: hypotheses (`history`, `loaded`, `checks`, `found`, `nonblob`, `costs`, `balances`, `slots`, `fresh`, `sourceNonce`, `freshAccounts`, `freshCode`, `builder`, `accountReads`, `storageReads`) are all input-domain conditions. Consumers derive the three predicates and settlement fields; the theorems do NOT restate `.returned`, `.terminal`, empty writes, U64 conversion or successful `incorporate` as inputs.
4. Trivial/vacuous conclusion — checked: `ReferenceCheckedSystemDrainTotal.verified`, `ReferenceCheckedSystemTotal.verified`, `ReferenceCheckedSystemBlock.verified`, `ReferenceFullFeeBlockTotal.verified` produce substantial equations (frame equality, execution equalities, journal projection identities, incorporation existence, read/write enumeration soundness/completeness). None are `True`/self-implying.
5. Scope drift — module docstrings and DIRECT-CLOSURE.md sec. "Current local candidate" and "Preserved SYSTEM candidate" explicitly disclaim canonical funded History, canonical block admission, SYSTEM authorization, inhibition applicability, deployment reachability, and full source-payment-to-success identity. No theorem body observed to widen beyond that boundary.
6. Bundle-hash mismatch — all 34 files whose SHA appears in the four bundles compute to exactly the recorded SHA (see verification table below). The two files listed under `comment_only_updates` in `direct-system-success-bundle-20260911.json` (`ReferenceCheckedSystemOutcome`, `ReferenceCheckedSystemTotal`) intentionally have no SHA in the a612bbb bundle; their SHAs in the 5cd0fe5 bundle match the file contents at commit 5cd0fe5 exactly, and the a612bbb-time contents diff only comment strings ("stronger ReferenceCheckedSystemDrainTotal now connects …") — confirmed via `git diff 5cd0fe5..a612bbb -- Eip8282/Audit/Integrator/ReferenceCheckedSystem{Outcome,Total}.lean`.
7. DIRECT-CLOSURE.md conclusions not established — spot-checked the four sections. Each stated conclusion (finite account/storage enumeration, U32-index preservation, unmerged-parent BAL, empty code-writes, fresh tx-journal reset, per-kind checked evaluator run, DrainTotal derivation from Whole) is visible on the RHS of the corresponding `verified` theorem.
8. Nonce-fixture mutants — `Eip8282/Tests/ReferenceOrdinaryBlock.lean` module docstring reads "Injected functional journals/builders, not canonical histories or a counterexample to the existing FullFeeTotal theorem. These witnesses expose why balance-only observations do not supply nonce admission". DIRECT-CLOSURE.md L52-54 reads "Nonce fixtures in the mutation module are injected projection witnesses, not canonical counterexamples". Ordinary-block bundle receipt line 182 also says "Nonce fixtures are injected projection witnesses, not full theorem/canonical counterexamples". No file/comment presents them as canonical.

## Axiom audit (production modules)

Cross-referenced against `direct-{system-success,checked-system,system-block,ordinary-block}-axioms-20260911.json`:

- All 22 production exports of a612bbb list axioms drawn only from {`propext`, `Classical.choice`, `Quot.sound`}.
- All 13 production exports of 5cd0fe5 list axioms drawn only from {`propext`, `Classical.choice`, `Quot.sound`}.
- All 35 production exports of cb65536 list axioms drawn only from {`propext`, `Classical.choice`, `Quot.sound`}.
- All 28 production exports of f2ab5eb list axioms drawn only from {`propext`, `Classical.choice`, `Quot.sound`}.
- All 20 mutation exports (across the four commits) list axioms drawn only from {`propext`, `Classical.choice`, `Quot.sound`} — some (e.g., `Eip8282.Tests.ReferenceOrdinaryBlock.nonce_keeps_maximum`, `nonce_updates_first`) even list `[]` (pure `rfl`).
- No `native_decide` axiom is introduced in these commits' new modules. Existing `A-NATIVE-DECIDE` disclosures in Trust.lean remain restricted to the earlier bytecode/Guarantees layer.

## Bundle hash verification

For every module whose SHA-256 is recorded in the four `direct-*-bundle-20260911.json` files, the disk SHA-256 was recomputed with `sha256sum`. Every recorded hash matched the current file byte-for-byte.

a612bbb (SYSTEM success bundle):
- ReferenceCheckedPureForward: `b3c5338b31b6e2516e51c251c91258c50b0387a55d44a082a95449e5c4ebbcce` = disk. OK.
- ReferenceCheckedStorageForward: `43c75a079d1375924553ed195130a135d20bb69a77d6525bcf3e01447512ce25` = disk. OK.
- ReferenceCheckedMemoryForward: `ea92512440b838d53b6379ecea84c431ced57851bd269fb1188ea438373a23e2` = disk. OK.
- ReferenceCheckedSourceSelection: `ca7a4411987d3afb94522e1888e61909751c60f16e838b19952bc15055f719d3` = disk. OK.
- ReferenceCheckedSystemForward: `626d8e346d965d45d140147342155ed6991e0083badcbc4ab1d8242e61816688` = disk. OK.
- ReferenceSystemStackBound: `d9566d5bb5f44f7856eab1cc1bd1382d8b09ecf909f819d135eceb68798f875f` = disk. OK.
- ReferenceCheckedSystemTraceForward: `0c3bac32b5deba7732e92244e2771378e2d0f38fedfec8328f7dabe78acc7eef` = disk. OK.
- ReferenceCheckedSystemReturn: `03495e193ef773f481fc5b742a2743ef2a6541f65167276ab068d62c621ec1ac` = disk. OK.
- ReferenceCheckedSystemWhole: `5b7286f49cca63d77300a463f4e8158dcec84ece6b1c0db8cf0ec98af85a1e89` = disk. OK.
- ReferenceCheckedSystemSuccess: `2e4d0e94279387777626e190dcbfc4d28415f3eba3ea618ed8dc9bbb0bde914a` = disk. OK.
- ReferenceCheckedSystemDrainTotal: `c102a85c00e3bc41d51146ad5fd80c3b42e5ecae337fd13e42e623b168915021` = disk. OK.
- (`comment_only_updates` `ReferenceCheckedSystemOutcome`, `ReferenceCheckedSystemTotal`: no SHA recorded in this bundle. Their disk SHAs `76b1a873…` and `3030767a…` differ from the 5cd0fe5 bundle values `651135b7…` and `589baf75…`, but `git diff 5cd0fe5..a612bbb` on both files shows comment-only changes.) Documented, OK.

5cd0fe5 (checked SYSTEM bundle):
- ReferenceOutcomeGas: `556ab4fe2e4c5ce035f99fd793c2fd26643f199b5a7f42680f76b235e5b8c20c` = disk. OK.
- ReferenceCheckedSystemEntry: `7f05a2159e691c7cb492860129b90b7cb67a59ebd9046c894c47f94e50fcab3a` = disk. OK.
- ReferenceCheckedSystemExecution: `03b7e3e5271af5a41f70c5aa05fbe74a18fcacea196f87ec4e0a74a15fcd9c88` = disk. OK.
- ReferenceCheckedSystemOutcome (at 5cd0fe5): `651135b774b9971859a1d5a69be8ec9823eb1e923223431529f7e0d4b937c4d3` = `git show 5cd0fe5:…`. OK (later superseded by comment-only diff at a612bbb).
- ReferenceSystemOutputMeter: `164b950390e91a5e2b029af8bb6836a56f6ba61db7415a8a888132df6d07b8e3` = disk. OK.
- ReferenceSystemOutputReceipt: `4d6a73c57ccf58e4e83d9a8224d0be19fc17172b18e664e90b81145f1b77d03b` = disk. OK.
- ReferenceCheckedSystemJournal: `9d12eafe8dccba8691f41acd01081fba303aea328d6847c5a0eca4a1f38f05af` = disk. OK.
- ReferenceCheckedSystemTotal (at 5cd0fe5): `589baf7597f36d637661537273cd28e388e04c50ebd1707082ff88fb92073729` = `git show 5cd0fe5:…`. OK (later superseded by comment-only diff at a612bbb).

cb65536 (SYSTEM block bundle):
- ReferenceSystemBlockFootprint: `70c90565860928d4951a32a24a4ee13be7c3accd645d72f82f8ca5ec50b1ac54` = disk. OK.
- ReferenceSystemBlockParent: `30f557eadc158caeeea1fefbf65308a0112c40c133e364e87eb572544270fb6c` = disk. OK.
- ReferenceSystemBlockReceipt: `e8657a64fe97c633260f054b3d757e6b4c1fc6d3b516b07b84121efc03fa2228` = disk. OK.
- ReferenceSystemBlockAccess: `56b5d10df28b14820aeb3330a214b18c1a0b373107cbb32ae88afd52a14d7c76` = disk. OK.
- ReferenceCheckedSystemPair: `fabefc7736d7ff3606334701ef54a398f59e768ea6f44dc451afb0ea25187df6` = disk. OK.
- ReferenceSystemBlockSettlement: `d9c0671ade987eafe5cc9d37aa7471a9f4ef16ab6c064adab516b71216cdcfd9` = disk. OK.
- ReferenceSystemBlockWorld: `e501361b09a85d212d911401ca3dd4c8a18667294262766a0dca887c941fa4a7` = disk. OK.
- ReferenceCheckedSystemBlock: `21e0dc7c7fd47b51ba9c6a836725cd1332eeff4afbbae2871e7642b2a130604b` = disk. OK.

f2ab5eb (ordinary block bundle):
- ReferenceOrdinaryBlockNonce: `0f520baa76aa57e9a475a869abb7d2956586f38082f60f661341857c96e9510b` = disk. OK.
- ReferenceFullFeeBlockNonce: `118eef1c5cc04133290f21037ed916247c0ace74b265fe718e2486a592dcedb8` = disk. OK.
- ReferenceOrdinaryBlockAccounts: `8fcfe36667cba6bd50ec77ca753ada2c958e6965793793891b7a65aa237759b3` = disk. OK.
- ReferenceOrdinaryBlockStorage: `3d8bb98b4594372666d25636ed50f8f949ac9fe9ddbc72a1795cde00c1ee5188` = disk. OK.
- ReferenceOrdinaryBlockAccess: `270dfa5bbdf06481f6b9caebfe35b2f52e23192aa0f6452d2969ba7b03130fa7` = disk. OK.
- ReferenceFullFeeBlockReceipt: `098bb6a4f056786eb09b9195c7c6012d26b53100265618c83cecceaf3a6d353a` = disk. OK.
- ReferenceOrdinaryBlockSettlement: `ec4160a0aecdd1ee217136a9c97acb22ebed827101a49e63d3b69fff5ea9a788` = disk. OK.
- ReferenceFullFeeBlockTotal: `98500b59d1f693e4b2312ffbc19ea971ce5255e7625560dc80fd59c15b4fa979` = disk. OK.

## Conclusion

The four composed candidates a612bbb, 5cd0fe5, cb65536 and f2ab5eb pass all eight blocking checks. No `sorry`, `admit` or project axiom is present in any of the 35 modules; the axiom sets recorded in the four axiom receipts are entirely within {`propext`, `Classical.choice`, `Quot.sound`}; the added Trust.lean lines are `#print axioms` disclosures only. Every SHA-256 in each of the four bundle receipts matches the current file on disk (or, for the two `comment_only_updates` files, matches at the corresponding earlier commit with only comment-string edits between). Theorem statements do not restate the conclusions as premises: the successful drain, three-predicate composition, checked U64 nonce conversion, unmerged-parent BAL, empty account/code-write journals, complete-and-unique dictionary enumerations and successful `incorporate` all appear on the RHS. Module headers and DIRECT-CLOSURE.md consistently label canonical funded-History production, canonical block admission, complete admission, deployment, SYSTEM authorization, inhibition/upgrade applicability, whole-block BAL capacity, and full source-payment-to-success identity as OPEN. The `ReferenceOrdinaryBlock` nonce fixtures are correctly described as injected projection witnesses, never as canonical counterexamples.

VERDICT: CLEAN
