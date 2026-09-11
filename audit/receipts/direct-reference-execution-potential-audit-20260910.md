# Execution-potential route: independent source audit

Pinned EL0cc100eb190b64b23baba72dac0165652eaec252; complete49-file body/hash evidence is `/tmp/eip-state-credit-scan-faraday/sources.json`. This is source inspection and arithmetic, not a new Lean theorem or canonical source execution witness.

The proposed route is sound for selected completed protected append work once actual source frame/grant and occurrence producers are supplied. It does not need a theorem that total source net state usage is nonnegative. Two distinctions are necessary: gross execution charges must deduct CALL/CALLCODE stipend creation at the parent edge, and the five/eight-store lower bounds apply to completed append paths, not blindly to all executed LOG0 events.

## Potential identities

Let P(m)=execution+spill+committedSpill, with Nat fields and exact full-meter mappings.

- State charge: reservoir payment leaves P unchanged; execution remainder decreases execution and increases spill equally.
- State credit: min(credit,spill) increases execution/decreases spill equally; excess credit enters reservoir only, so P stays fixed even for arbitrary signed net-state balance.
- Repayment after successful merge: execution increases by min(reservoir,spill), spill decreases equally; P fixed.
- Commit: spill moves into committedSpill; P fixed.
- Ordinary restore: execution gains spill and spill becomes0; committedSpill retained; P fixed.
- Restore-to-entry: execution gains both spills and both become0; P fixed.
- Execution charge: P decreases by exact charged amount, provided actual successful checked subtraction.
- Exceptional halt: restore precedes forfeiture. Forfeit sets execution0 after spill0; P cannot increase. Nonrefillable top committedSpill remains in P and does not invalidate the bound.
- Child incorporation: child committedSpill0 source assertion; absorption adds parent and child P; success repayment preserves it, failure already settled. Parent baseline/committedSpill remain fixed.
- CREATE withhold and reservoir drain preserve parent+child P. Collision consumes withheld execution, hence decreases it. Denied CREATE occurs before withholding/NEW_ACCOUNT; no extra credit.
- CALL/CALLCODE: child grant includes2300 on nonzero value, so the grant-only sum increases by stipend. Prior CALL_VALUE=9000+2300 covers that increase. Define counted foreign overhead as execution charge minus stipend (still nonnegative), then retain all protected leaf SSTORE/LOG execution costs. Do not claim the sum of all gross parent and child execution charges is bounded by initial P: it equals initial-minus-final P plus issued stipends, absent other decreases.
- DELEGATECALL/STATICCALL pass literal U256(0) to gas calculation and therefore add no stipend, even when DELEGATECALL inherits a nonzero env.value. This distinction is visible at system.py854-861 and957-964.
- AUTH7702 charges state NEW_ACCOUNT/AUTH_BASE (P invariant), execution ACCOUNT_WRITE (P decreases), then top commit (P invariant). No AUTH state credits occur.
- CREATE code-deposit state charge and SELFDESTRUCT beneficiary creation preserve P; their execution costs decrease it. Final transaction refund counter is used for sender settlement, not injected into live execution P.

The complete AST scan found all direct gas_left mutations only in gas.py403,443,522,557,624,651,673,695,743 and vm/__init__.py238. These are precisely execution charging, state spill/credit, restores, repayment, forfeiture, CREATE withholding, denied child-return, and child absorption. No other Amsterdam opcode/precompile directly increases live execution gas.

## Exact completed append paths

Exit actual successful suffix in `Eip8282/Audit/Integrator/AppendGasPath.lean:471` inverts SSTORE sites173,186,193,201,223 and LOG0 site217 with length68. EntryReach/Exit.lean463-490 names countStore, three item words, log, tailStore. Deposit suffix at AppendGasPath.lean742 inverts SSTORE213,227,235,243,251,259,267,282 and LOG0 site276 length184; EntryReach/Deposit.lean574-604 names countStore, six item words, log, tailStore.

Source storage.py execution access component is always at least100, independently of original/current/new aliases and whether the store changes a value. LOG0 source charge is375+8*len, excluding nonnegative memory expansion. Thus completed Exit append lower bound=5*100+375+8*68=1419; Deposit=8*100+375+8*184=2647. Other execution costs only strengthen these bounds. This instruction count does not require noWrap or distinct storage keys.

The tail SSTORE occurs AFTER LOG0 in both images. An internal failure after LOG0 can omit that accepted store. Therefore the five/eight-store argument needs an actual successful completed append frame (which may later be undone by an ancestor). It cannot be substituted directly into the current generic logCount theorem over all executed logs. This does not establish an actual below1399 failed LOG path; it identifies why the proposed structural count alone is insufficient for that broader statement.

## Floor comparison

16777216//1419=11823 <12000; even weaker1399 gives11992 <12000. Source transaction allocation caps initial execution grant by16777216 minus intrinsic execution. Fresh top meter starts spill=committedSpill=0. Therefore a source-tree P accounting theorem and disjoint selection of completed append leaves give per-transaction append count<=11823.

The literal source calldata floor is ((4*dataLen)+accessTokens)*16+(12000+recipientCost)>=12000. Source settlement sets block execution use=max(beforeRefund-max(0,netState),calldataFloor), so block execution use>=12000 independently of whether signed netState was negative. Hence per-transaction selected append count<=charged block execution. This deliberately avoids claiming block execution directly equals all gross instruction work when netState is negative. Literal settlement checked-subtraction validity and actual transaction/block field extraction remain separate producers.

## Remaining precise interfaces

1. Full source meter P-preservation/charge-debit lemmas, including source CALL/CALLCODE net-of-stipend splitting, with actual grants and settled child incorporation. No foreign-bytecode equality to pinned evaluator.
2. A source frame tree that extracts protected runtime boundaries, threads actual source grants/journals, and supplies an injective/disjoint selection of completed user append frames. Retained append count is a subset; later ancestor rollback cannot erase their execution charge.
3. Annotate the existing actual successful append suffixes with exact SSTORE count and LOG data length (five/eight and68/184). Lift through protected source-view correspondence on the same actual completed witness, not a supplied desired count.
4. Actual source top initialization/allocate bounds and per-transaction calldata-floor/settlement projection, then block admission and chronological finite slot/header bounds. SYSTEM calls are a separate schedule/context; this per-transaction argument does not grant them an arbitrary transaction budget.

No new compiler invocation, proof source edit, remote write, provider, or fee-exploit claim was made in this audit.
