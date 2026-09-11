# Initializer success and canonical deployment interface — 9 September 2026

Read-only source review. No proof edits or builds. Proposed signatures below are implementation interfaces, not compiled declarations. Keep existing public parents and shared `Initialization.lean` unchanged while implementing an auxiliary `InitializerProgress.lean`.

## Feasibility and exact gap

A universal successful **actual Lambda** theorem is feasible with small additional gas lemmas. Existing `Initialization.deposit_execution` and `exit_execution` prove actual Ξ success but return an existential gas without a lower bound. `CreationSettlement.installs_of_execution` already turns that execution into actual successful Lambda when `depositFailure=false`. The missing bridge is retained gas sufficient to install the returned code.

The public `DirectInitialization.Initializes` assumes actual Lambda success. Its resource assumptions (deposit gas≥1000 and steps≥8; exit permission, sender existence, gas≥25000 and steps≥11) cover initializer execution only. Runtime code-deposit costs alone are **125600** gas for deposit (628×200) and **91600** for exit (458×200). Consequently deleting the success premise while retaining those public resource minima would be false. This is an applicability/liveness gap, not a flaw in the current conditional theorem.

Use conservative input bounds **126600** (deposit) and **116600** (exit). These equal existing execution envelopes plus code-deposit cost. They are sufficient bounds to prove, not exact minimum gas estimates and not total factory-transaction gas limits. The new theorem need not calculate the minimum.

## Exclusive-file consumer interface

Suggested public declarations in `Eip8282.Audit.Integrator.InitializerProgress`:

```lean
def executionEnvelope : Kind → Nat
  | .deposit => 1000
  | .exit => 25000

def creationGas : Kind → Nat
  | .deposit => 126600
  | .exit => 116600

-- All context and domain names are the existing public ones.
theorem initializes_success (kind : Kind)
    (c : CreationSettlement.Context) (preimage : ByteArray) (steps : Nat)
    (hi : c.init = Initialization.initCode kind)
    (hd : DirectInitialization.Domain kind c preimage steps)
    (hg : creationGas kind ≤ c.gas.toNat) :
    ∃ created world gas substate,
      c.result = .ok (CreationSettlement.address preimage,
        created, world, gas, substate, true, ByteArray.empty) ∧
      DirectInitialization.Observed kind c preimage
        (CreationSettlement.address preimage) world substate
```

This interface is sufficient to discharge the existing initializer success hypothesis and produce `Bounded 0`, `EnabledSafe`, empty queue and installed runtime. It does not add any desired storage or creation-success premise. `hd` retains independent preimage, absent target, no collision, fuel and exit owner/permission conditions. Some fields become redundant under stronger gas/absence; retain them initially to minimize integration risk. Deposit does not need sender presence for the local pinned Lambda theorem; protocol deployment should additionally derive a valid present/funded factory independently.

The higher-level canonical consumer can take `haddress : CreationSettlement.address preimage = ReachableCalls.address contract` to rewrite the result; that equality remains an explicit external binding until certified against the actual CREATE2 inputs. Do not include `haddress` in the local theorem and label it canonical deployment proof.

## Minimal auxiliary lemmas

1. **Remaining-gas lower bound from the exact init path.** Export a result that retains both the literal Ξ execution and `c.gas.toNat - executionEnvelope kind ≤ remaining.toNat`. For example, deposit:

```lean
theorem deposit_execution_budget (c : Initialization.InitCall)
    (hg : 1000 ≤ c.gas.toNat) (hf : 8 ≤ c.fuel) :
    ∃ gas,
      c.result .deposit = .ok (.success
        (c.createdAccounts, c.world, gas, c.substate) Bytecode.depositRuntime) ∧
      c.gas.toNat - 1000 ≤ gas.toNat
```

Exit should retain the exact existing `(Initialization.exitStored c)` created/world/substate result and the lower bound `c.gas.toNat-25000 ≤ gas.toNat`, with existing permission and steps≥11 conditions. This gas lemma itself need not assume an owner; `exit_initializes` requires owner for its storage observation, supplied later by `hd.resources`.

2. **Pinned runtime passes non-gas code-deposit guards.** For both kinds derive `(runtime kind).size = runtimeLen kind`, size≤24576 and first byte≠0xef from concrete bytes. An absent pre-target proves the occupied guard false. With `200*runtimeLen kind ≤ remaining.toNat`, prove `c.depositFailure a remaining (runtime kind)=false`. This is finite byte metadata plus symbolic gas arithmetic, not a finite execution substitute.

3. **Compose existing exact settlement and observation.** `execution_eq_initialization` transports the Ξ equation using `hd.fuel_eq`, `hd.no_collision`, `hi`; `installs_of_execution` produces the literal Lambda tuple and exact remaining gas subtraction. Then apply `DirectInitialization.pinned kind` to that same receipt to obtain Observed. Avoid re-proving initial scalar/queue facts already in `InitializedInvariant`.

4. **Optional simplifications.** Prove `no_collision_of_absent`; prove successful CREATE2 `preimage` directly from `c.salt=some saltBytes`. Neither requires a hashing assumption merely to form the preimage.

## How to implement without modifying shared Initialization

The needed inequalities exist **inside private proofs**, but their public statements erase them. `copy_return_path` has `hg1`, `hg2`, `hg3`; `result_of_return_path` explicitly chooses final gas but exposes it existentially. These private helpers are not a stable public API. The existing public execution theorem plus `ReturnedGas` cannot recover a lower bound: ReturnedGas gives an upper bound only.

A separate file therefore needs a small universal symbolic init path or a generic gas-reserve simulation. Prefer copying only the relevant local path construction into its own namespace and strengthening the gas outputs; do not rely on mangled `_private` names. Reuse public `block_step`, `reach_sstore`, `Reaches`, `Halt`, `runUntil_of_xRuns`, opcode/decode lemmas, memory bounds and actual Ξ settlement. CODECOPY's local helper may need its own short proof because existing initialization copy helpers are private. Keep parameterized arbitrary gas/world/originalWorld proofs; no `native_decide` execution.

The conservative arithmetic can be even smaller than the public envelope: copy-opening block≤11, CODECOPY≤123, closing PUSH0≤2, RETURN≤60, total≤196. Exit adds opening≤5 and SSTORE≤22100, hence total≤22301. `EntryReach.reach_sstore` already exports the 22100 lower-bound debit. Those sums fit under1000/25000. `RETURN` actually copies an already allocated range; a coarse≤60 suffices, so no tight memory-cost identity is needed. For natural subtraction lower bounds, retain the proven charge affordability to exclude modular wrap.

## Fuel indexing

`CreationSettlement.Context.result = Lambda (c.fuel+1) ...`; Lambda selects `Ξ c.fuel ...`; `execution_eq_initialization` assumes `c.fuel=steps+1`, while `InitCall.result` uses `Ξ (steps+1)` and its inner X budget is `steps`. Therefore current minima mean outer Lambda fuel≥10 for deposit and≥13 for exit. They do **not** mean Lambda fuel8 or11. Gas accounting and evaluator fuel are separate. The CREATE2 dispatcher `CreationGas.child ... fuel ...` invokes `Lambda fuel`; adapting to Context.result requires the corresponding positive-fuel equality, not reusing the same bare variable off by one.

## Concrete canonical deployment candidate — not normative adoption

Protocol agent evidence `/tmp/eip-protocol-current-20260909.json` independently retrieved execution-specs commit `0cc100eb190b64b23baba72dac0165652eaec252` fixtures and recomputed CREATE2 addresses. Factory is `0x4e59b44847b379578588920cA78FbF26c0B4956C`.

| Kind | Salt | Derived address |
| --- | --- | --- |
| Deposit | `0x1f4f2c41c28e816e259b621c58b94b37309c8dec42c8f6e400001a46c9d96bf7` | `0x0000bff46984e3725691fa540a8c7589300d8282` |
| Exit | `0x89abb1878437213f971f849327423ed1d9c5cdb03970cd8f0000318b3ff10119` | `0x000064d678505ad48f8ccb093bc65613800e8282` |

Fixture text SHA256: deposit `aae4bd49b90e96874ea3f49a256c0d0e208ba2eef85963c12f4281f1d16e3a13`; exit `ed76ac573281d1f894444c11a9a4675ef7211e67fef3312ea4f6a8e94cdd0587`. Deployment test SHA256 `3e5866517ba209b2c5592cf7d1a7be7fde93751989342dbf056ae6b4e4860668`. Decoded init SHA256 deposit `166510c29d9ea96c80b854e86743377de1cadccaef62a620c684641fb9267f61` (638 bytes), exit `37d89175964e696bfed69ad5309c0147bdb7af8b11a25ea1ba557d7adb9d50b8` (503 bytes). Both equal pinned init bytes according to that evidence. These fix a usable candidate preimage; they do not prove an on-chain deployment or select normative Amsterdam semantics.

For CREATE2, pinned Lambda.L_A produces `BE 255 ++ sender.toByteArray ++ salt ++ ffi.KEC init`; `some salt` makes encoding success immediate, independently of the nonce. Actual CREATE2 extracts a full UInt256 salt via `salt.toByteArray`, so bind exactly32 salt bytes and20 sender bytes. The canonical equality requires a justified KEC computation/certificate or named cryptographic implementation boundary; the Python recomputation does not become a kernel theorem automatically. The core constructor proof can remain symbolic over KEC.

## Extraction still required after local Lambda success

An actual deployment theorem must extract the literal factory CREATE2 child: factory installed code, actual sender/owner, calldata→salt/init memory, accepted Z and step, nonceAllowed, funds/depth/init-size gate, forwarded allowance, evaluator fuel, permission, and pre-target absence. Existing `CreationGas.child` and `CreationOutcome.admitted_equation` bind the real child and settlement; they do not prove that a real factory program reaches this CREATE2 or that the surrounding transaction commits. After child success, prove the parent continuation and every ancestor returns successfully, so installed state survives, then connect the Υ result and canonical deployment history. A successful child followed by factory/ancestor REVERT does not establish persistent installation.

The pinned EIP says deployment is **before activation** and deposit accepts pre-fork submissions. Therefore activation state cannot simply be assumed to be the constructor's empty queue: the entire interval from deployment through activation must be included in state/history preservation. Exit begins inhibited but deployment alone does not justify subsequent scheduling.

## Semantic boundaries / mismatches to retain

- Raw Lambda omits sender-funding validation; if sender is absent, entryWorld remains unchanged. Deposit can still return/install code through the later installer, which defaults a missing account. This is accepted by the local universal theorem but does not model a valid factory deployment without admission/owner binding.
- Lambda's collision check includes nonempty storage (EIP7610); its later occupied guard checks old nonce/code. Absence is stronger than either, and avoids their distinction. Do not infer deposit clears arbitrary old storage: it preserves storage.
- CREATE/CREATE2 catch every Lambda error, including evaluator OutOfFuel, into an empty account map, as represented literally by `CreationOutcome.select`. The final parent gas guard uses **word addition** of charged gas and child returned gas. Local init success removes the child-error case but does not automatically discharge the parent guard or establish external EVM conformance. A justified bounded protocol gas domain can establish no-wrap and the guard.
- The selected Amsterdam reference adds state-gas accounting absent from the simple pinned gas model, according to the protocol-agent source review. The126600/116600 bounds are for pinned EVMYulLean; do not advertise them as complete Amsterdam transaction limits without correspondence.
- Success settlement/code hashing and address equality are distinct proof obligations. Standard Lean axioms for current conditional parents do not certify `ffi.KEC` matches real Keccak or that the candidate deployment happened.

## Acceptance for the separate file

Both kinds must produce an actual successful Lambda equation and Observed under independent stronger input resources, no success/post-world premise. Exact returned tuple must come from existing settlement, code-deposit cost must be accounted, and `#print axioms` must remain standard Lean only. This completes local initialization liveness under sufficient resources; canonical deployment and its transaction/history extraction remain separately named obligations.

Exact local source entry points:

- `Eip8282/Audit/Integrator/DirectInitialization.lean:46` — `def Initializes`
- `Eip8282/Audit/Integrator/CreationSettlement.lean:146` — `theorem installs_of_execution`
- `Eip8282/Audit/Integrator/CreationSettlement.lean:267` — `theorem execution_eq_initialization`
- `Eip8282/Audit/Integrator/Initialization.lean:219` — `private theorem copy_return_path`
- `Eip8282/Audit/Integrator/Initialization.lean:272` — `private theorem result_of_return_path`
- `Eip8282/Audit/Integrator/Initialization.lean:305` — `theorem deposit_execution`
- `Eip8282/Audit/Integrator/Initialization.lean:329` — `theorem exit_execution`
- `Eip8282/Audit/EntryReach/Steps.lean:191` — `theorem reach_sstore`
- `Eip8282/Audit/EntryReach/Steps.lean:432` — `theorem halt_RETURN`
- `Eip8282/Audit/Integrator/CreationGas.lean:47` — `def child`
- `Eip8282/Audit/Integrator/CreationOutcome.lean:35` — `def finish`
- `.lake/packages/evmyul/EvmYul/EVM/Semantics.lean:571` — `def Lambda`
