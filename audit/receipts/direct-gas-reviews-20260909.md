# Independent reviews: append gas paths and transaction refunds

# AppendGasPath independent source review — CLEAN

Exact frozen SHA256 `4ae4dfb5b97ede8a12f108dc79ba45c4e041936b554772cbefb8c5539074c366`, confirmed locally twice. Read the complete898-line source in sections, complete ActualAppendGas (SHA `79a04a7b1a092026b24e3dfc3b0adc9bffaaa17a473e76a3f8a5447e75a7ea0d`), actual XStepAt/XRuns definitions and decomposition/concatenation, success_continue, supported-opcode enumeration, and pinned LOG0 gas semantics. Parent `/tmp/eip-AppendGasPath-final.log` is clean; all printed exports use only propext, Classical.choice, Quot.sound. No edits or build.

## Actual labels and segments

Segment is exactly existential XRuns plus Supported, with no independent synthetic transition semantics. Segment.single labels its real XStepAt by `(fuel,cost,decodeAt pre)` as XRuns.cons requires. Supported therefore constrains the opcode actually decoded, not a separately supplied label. Concatenation uses XRuns.trans at exactly matching intermediate state and fuel, and Supported splits actual append membership.

traced_symStep/block, jumps and effect adapters recover accepted Z and executed StepOk from the actual successful evaluation. withGE changes reflect the actual gas debit and step counter, while memory/storage/log effects match the checked semantic shape. Their Segment and remaining-success equations refer to the same intermediate state; no sufficiently funded substitute execution is introduced. allOps includes the proven pure/effectful runtime instructions and excludes child-frame CALL/CREATE/related opcodes that could replenish caller gas.

## Complete fee and append paths

Both entry branches retain all gate/excess/count-dependent instructions. Nonzero fee cycles execute24 actual instructions and preserve a Segment with strictly reduced actual evaluator fuel. Strong induction follows that fuel and produces the same fee output/counter and exit continuation, for any successful finite run; no supplied quote completion, bound256, mathematical domain or liveness assumption occurs. Dispatch uses the real calldata size (48 exit,184 deposit); rejection guards are forced untaken by actual success.

Exit suffix retains count+three record stores, address MSTORE, pubkey copy, the actual LOG0 at217 with stack length68, tail store and final STOP224. Deposit retains count+six record stores, calldata copy, LOG0 at276 with length184, tail store and STOP283. ThroughLog prefixes finish at fLog+1, its actual LOG step consumes that one fuel unit, and the suffix starts at exactly fLog and ends before supported STOP. Length operands are derived by checked block shapes and rfl on the actual stack, not assumed gas estimates.

## Same final gas and natural debit

ThroughLog does not itself store the final successful tuple, but this is sound: ActualAppendGas.xi_log_debit obtains the original successful final state and rewrites that same X result using prefix XRuns.X_eq, LOG XStepAt.X_succ and suffix XRuns.X_eq. The residual execution is the actual STOP state with the same final/out. success_final_step_debit includes its actual accepted halting step and bounds the same returned final gas. There is no gap between pre-STOP gas and published gas.

accepted_gas derives memory and opcode no-underflow conditions directly from Z acceptance. accepted_step_debit uses actual supported StepOk to prove exact natural debit; xruns_debit telescopes nonnegative actual opcode charges and safely drops additional memory costs. C' LOG0 costs375+8*length:919 for68 bytes,1847 for184 bytes. These are lower bounds, not exact total append costs. CallSuccess/Θ preserve the same remaining gas even if the world/substate empty fallback is selected, so no owner/nonempty/fit premise is needed.

The final exit_theta_debit/deposit_theta_debit require only actual Θ success, explicit runtime equality, non-SYSTEM caller and exact submission size. They conclude actual returned gas plus919/1847≤input gas. No external LogPath, gas/fuel lower bound, permission, fee completion/domain, owner or storage-fit condition remains.

Scope: per-call evaluator gas consumed before transaction refunds, not billed transaction gas, total block accounting, supply/funding or nested-frame extraction. RefundBalance bookkeeping does not replenish gasAvailable inside these supported opcodes. The source explicitly leaves transaction/nested/refund accounting separate. Interpreter OutOfFuel cannot satisfy actual-success premises. No concrete correctness/circularity/overclaim findings.

---

# Independent root review: RefundAccounting.lean

CLEAN for the actual Υ gas observation and conditional event-to-net-gas bound.
Frozen SHA256 4c67ebc4ccb77819248e0c6030cc5f63a0274ce0752d8ad17784a136096750fb.

Read the complete module and compared its provisional checkpoint, prices, access sets, intrinsic entry gas, Θ/Lambda dispatch, exact arguments, and refund expression to pinned EVM/Semantics.lean Υ (lines832–954). result_observation unfolds the actual function and projects only gas/substate/status; it does not replace or erase its final world cleanup semantically. Precompiles remain selected by actual toExecute; provisional failure status and errors are retained.

Given the explicit actual remaining≤gasLimit bound, the min refund cap gives refund≤gross/5, hence remaining+refund≤limit<2^256. The returned-gas addition and final subtraction cannot wrap. The natural net formula follows, and 919*count≤gross gives count≤net after the capped refund. No desired net-gas equality or individual fit premise is supplied.

Actual Υ result inversion retains the SAME provisional gas/substate/status. count_le_transaction_gas joins its independently supplied provisional execution witness by deterministic equality, then applies the arithmetic bound to the actual reported used gas. It works for either transaction success status. entryGas_toNat and entryGas_le_limit follow from natural subtraction before the word cast and do not claim intrinsic-gas validation.

Limits remain material: remaining≤limit (or entryGas) and aggregate919*count≤gross must be derived from real, nonduplicated execution accounting. This file does not count nested append events, validate transactions, relate block gas or prove storage preservation through final cleanup. The auto-generated Υ.match_1 unfolding warning is a pinned-source maintenance dependency, not a logical axiom or correctness defect.

Inspected /tmp/eip-RefundAccounting-local-compile.log: compile exit0 with that one disclosed warning; all nine printed results use standard axioms. No proof edits by reviewer. Exact-commit validation follows separately.

---
