# Independent review: funded LOG0 mutation and direct kill-line collection

Verdict: CLEAN at the final exact sources below. The funded LOG0 witness refutes the same parameter-code PSubmit predicate through an actual successful Θ result; no semantic blocker remains.

Worktree: `/Users/thomas/work/eip-8282/direct-closure-implementation`.

- `Eip8282/Tests/DirectThetaSubmitMutation.lean`: `e5315502d98aa18cce68d1063e4f95677b57a2de9357c7112c2647f77dc726bc`
- `Eip8282/Tests/DirectThetaSubmitCounterexample.lean`: `901132e757a609f1ac540029db1ffb4c175a28bef9210aed023096e2388952bf`
- `Eip8282/Tests/DirectThetaKills.lean`: `df9633ea5ba2fe5892a14f5689ce474cdede276f12317e4e777094d1c965459a`

Read the complete mutation certificate, all 159 states / 158 decode-charge-step certificates, the complete final wrapper, test conjunctions and relevant executable/proof dependencies. No proof edit or build by reviewer. Read-only structural checks confirmed contiguous state0..158, decode/charge/step0..157, edge0..156, and every edge's fuel decrement from 511. Inspected the supplied final logs:

- `/tmp/eip-DirectThetaSubmitMutation-local-compile.log`
- `/tmp/eip-DirectThetaSubmitCounterexample-root-2.log`
- `/tmp/eip-DirectThetaKills-1.log`

All are clean. The earlier wrapper root-1 had two elaboration errors (rewritten existential equality and unreduced match); root fixed them without changing theorem statements, and root-2 is the reviewed final receipt.

## Actual financing and initial state

The fixture has precisely two accounts: target balance zero and caller 0x1234 balance 2*10^18 wei. It sends 10^18+1 wei as both actual and apparent value, with the inherited 184-byte depositInput, gas 30M, permission true and Context.fuel 512. The caller is distinct from the predeploy and SYSTEM. `funded` proves the real pre-transfer sender can cover the value. `funds` uses two exact TransferFunding.funds_insert identities to prove the natural finite AccountMap total is exactly 2 ETH; no wrapped credit or invented post-balance is used.

The initial EVM state uses fixture.entryWorld, the actual Θ credit-then-debit world, and fixture.originalWorld as σ₀. The latter is intentionally the pre-transfer map. Target and caller balances after the distinct-address transfer are respectively 10^18+1 and 10^18-1 wei; all are below the word modulus. The initial environment, created set, substate, gas, blocks and genesis match the actual fresh state in Ξ. The proof never identifies this world with the old untransferred finite Ξ fixture.

`domain code` is universal in the supplied code and establishes the same DirectGuarantees.Domain at budget 0: target owner, ordinary value, input-size fit, zero controls/ordered empty queue, bounded budget and enabled-safe zero numerator. It has no pin to the original runtime, no execution/postcondition premise and no funded-ceiling trick. Financing is additional demonstrated fixture evidence, not a hidden premise that makes mutant success impossible.

## Real bytecode and certificates

The inherited mutation is definitionally depositRuntime.set! 274 0x00. Independent read of the pinned bytes confirms runtime length 628 and the original byte274=0xb8; byte273=PUSH1, byte269 remains the calldata-copy size 184, byte276=LOG0, and byte283=STOP. The original mutated-byte sanity theorems use native_decide, but the new certificate only needs the concrete mutation definition. Its printed transitive axioms contain no native receipt axiom.

validJumps_eq checks D_J of the actual mutant image, so the array is not assumed jump metadata. Every instruction separately proves actual decode, actual Z acceptance and actual StepOk on its stated state. SLOAD/SSTORE shared-state effects remain the executable operations rather than stipulated expected maps. Candidate numeric stack/memory snapshots are validated by these equalities, not trusted because an offline evaluator generated them.

The path performs the actual zero-numerator fee loop and obtains price 1, checks 184-byte input, actual CALLVALUE 10^18+1, the actual amount 10^9 gwei, and stake coverage. It increments count, writes the six record words, copies all 184 bytes to memory, then reaches the mutated PUSH1 zero followed by LOG0. The actual LOG0 has offset=length=0 and no topics, charges 375 gas, and appends exactly an empty-data receipt. Tail becomes 1 and the actual STOP succeeds at gas 29,820,096.

All 157 continuation equations use X_succ_of_continue with matching decode/Z/Step/H evidence. The final halt uses X_succ_of_halt on STOP, including non-REVERT evidence. Their equality chain establishes X 511 from the true fresh initial state; Ξ 512 follows by its exact definition. Local irreducibility attributes only prevent redundant elaboration and do not alter semantics or add premises.

## Memory and platform bounds

The padding helper proves the actual USize/BitVec subtraction equals natural 32-n for n<=32 by splitting System.Platform.numBits into its supported 32/64-bit cases. It does not silently fix the platform at 64 bits. CALLDATALOAD proofs reduce the real readBytes and use that helper, including the final load at offset160 with 24 bytes available and eight zero bytes. All offsets and lengths are small, so no large-array panic or truncation boundary is used. CALLDATACOPY's materialized memory is checked by the real step. Empty LOG0 data uses the actual zero-length readWithPadding theorem.

## Θ settlement and exact predicate negation

execution_result carries the actual full Ξ success tuple. actual_empty_log rewrites MessageCall.result_eq_settle and that tuple, then reduces the actual settlement including the world==empty branch. The produced map remains nonempty; the concrete reduction publishes its accrued log. It does not bypass the empty-world fallback with an assumed equality or LawfulBEq for Account.

The wrapper splits the real Θ result using actual_empty_log, ruling out errors and status false. Assuming SubmitObserved on that very successful tuple forces, through the non-SYSTEM/nonempty branch and DirectAppend's authentic-log clause, the exact singleton receipt containing depositInput. Its size is kernel checked as 184, contradicting the actual singleton empty-data log. `log_refutes_psubmit` then instantiates PSubmit with this same fixture, code equality rfl and independently proved Domain. This is actual `¬ DirectGuarantees.PSubmit .deposit logSizeMutatedDeposit`, not only a failed Boolean observation or an impossible original-code-pin premise.

The result is one finite counterexample to mutant correctness. It is not a universal correctness proof, transaction-validity/supply theorem or universal sibling-independence statement.

## Test-only conjunctions and trust

DirectThetaKills.submit_kill is the exact new PSubmit negation. drain_kills collects the two deposit / one exit exact PDrain negations. control_kills collects gate and target exact PControl negations for any initializer. The strengthened control predicate's initializer and SYSTEM progress clauses are retained: refuting its runtime conjunct suffices. None of these tests is conjoined into a correctness parent.

The funded LOG0 kernel_run, execution_result, actual_empty_log, theta_counterexample, log_refutes_psubmit and submit_kill report only propext, Classical.choice and Quot.sound. The test-only drain conjunction retains exactly the three historical native axioms for exit cap, deposit cap and stale-slot receipts; control retains exactly the two for gate and target. No new native evaluation, sorry or custom axiom occurs in these new sources. Full import of the historical mutant module does not make every imported theorem an axiom dependency of the LOG0 proof.

Relevant bindings:

- PSubmit1Mutant.lean: `53a8ec20aab3dadc83c3309fb15987f105783be50e46f7d73db2d14d21bf5bba`
- DirectGuarantees.lean: `9b39dc88aac5acb38b4ef7bac387739e9e0e1ab52f5c0e6994b9e1d0a792850d`
- MessageCall.lean: `3f16088bd13b6f6fdf13de417e4843f08e9dcd61fa6dfdddfc6342c250ccf342`

These six same-predicate Θ refutations satisfy the mutation gate proposed in `/tmp/eip-direct-registration-next.md`. Conditional registration still requires the parent's frozen integration/full checks and must retain the separately OPEN protocol-domain obligations. No universal sibling survival is claimed.
