# Actual nested event certificate: interface decision proposal

Read-only architecture audit of implementation HEAD 41bcff3 / frozen proof source 68c083a, 9 September 2026. Inspected AGENTS, superseded CAMPAIGN, current DIRECT-CLOSURE, the design receipt, EventTree, FrameEvents, AppendEvents, CallOutcome, CreationOutcome, RecursiveEventDebit, WrapperEventDebit, ReturnedGas, message/creation contexts and literal pinned Semantics. No proof files changed, no builds, no compiler probes. The signatures below are proposed interfaces, not compiled declarations.

## Decision

Use **one indexed inductive certificate over five request kinds**, rather than five mutually inductive relations or a frame certificate parameterized by an arbitrary child relation. This is just the usual tagged encoding of mutual inductives. It makes the recursive IH and fixed file ownership easier: one datatype file, pure argument/branch adapters in another file, independent extraction and charging proofs above them. The certificate has the actual complete Except outcome as an index. Its step component carries only the selected child's tree; X owns the local marker and continuation edge.

Do not use FrameEvents.Trace directly as the nested certificate: its stepError constructor intentionally forgets children. Reuse its local projection and append injection after proving that projection from the new certificate.

Do not put a gas inequality into a certificate constructor or request record. No generic `error -> done`, `StepOk -> noChild`, or `same returned result -> interchangeable child` rule is permitted.

## 1. Request arguments and exact indices

Create records without fuel. Use field names/types below; these are precisely existing evaluator inputs, not additional machine state:

```lean
abbrev Created := Std.TreeSet AccountAddress compare
abbrev World := AccountMap .EVM
abbrev XResult := Except ExecutionException (ExecutionResult EVM.State)
abbrev XiResult := WrapperEventDebit.XiResult
abbrev ThetaResult := Except ExecutionException
  (Created × World × UInt256 × Substate × Bool × ByteArray)
abbrev LambdaResult := CreationOutcome.ChildResult
abbrev StepResult := Except ExecutionException EVM.State

structure XiArgs where
  created : Created
  genesis : BlockHeader
  blocks : ProcessedBlocks
  world original : World
  gas : UInt256
  substate : Substate
  env : ExecutionEnv .EVM

structure ThetaArgs where
  hashes : List ByteArray
  created : Created
  genesis : BlockHeader
  blocks : ProcessedBlocks
  world original : World
  substate : Substate
  source origin target : AccountAddress
  code : ToExecute .EVM
  gas price value apparent : UInt256
  data : ByteArray
  depth : Nat
  header : BlockHeader
  permission : Bool

structure LambdaArgs where
  hashes : List ByteArray
  created : Created
  genesis : BlockHeader
  blocks : ProcessedBlocks
  world original : World
  substate : Substate
  source origin : AccountAddress
  gas price value : UInt256
  init : ByteArray
  depth : UInt256
  salt : Option ByteArray
  header : BlockHeader
  permission : Bool

structure StepArgs where
  vj : Array UInt256
  pre mid : EVM.State
  cost : Nat
  op : Operation .EVM
  arg : Option (UInt256 × Nat)
  guard : Z vj op pre = .ok (mid, cost)

inductive Request where
  | x (fuel : Nat) (vj : Array UInt256) (pre : EVM.State)
  | xi (fuel : Nat) (a : XiArgs)
  | theta (fuel : Nat) (a : ThetaArgs)
  | lambda (fuel : Nat) (a : LambdaArgs)
  | step (fuel : Nat) (a : StepArgs)

def Outcome : Request → Type
-- x/XResult, xi/XiResult, theta/ThetaResult, lambda/LambdaResult,
-- step/StepResult
def eval (q : Request) : Outcome q
-- one direct call to X, Ξ, Θ, Lambda, or EVM.step; NO recursion
def fuel : Request → Nat
def gas : Request → Nat
-- gas(step a) = a.pre.gasAvailable.toNat, x similarly;
-- wrappers use their original input gas.toNat
def residual (q : Request) : Outcome q → Nat
-- reuse FrameEvents.residual, WrapperEventDebit.xiResidual,
-- RecursiveEventDebit.thetaResidual/lambdaResidual/stepResidual
```

Accepted steps are the correct gas boundary. A raw unguarded step has no universal nonincrease guarantee because raw word subtraction may wrap. If an API for arbitrary `step ... none` is wanted later, it needs a decode adapter and an explicit accepted-Z hypothesis for charging. It is unnecessary for extracting every actual X/Ξ/Θ/Λ run. Our step interface covers *every outcome*, including errors, of every accepted explicit instruction dispatched by X.

Use adapters `ThetaArgs.message (a) (n) (bytes)` only after `a.code = .Code bytes`, yielding MessageCall.Context with fuel n. Similarly `LambdaArgs.context a n` yields CreationSettlement.Context. These contexts count the inner Ξ fuel; the request records count original outer fuel. Keep that distinction explicit. XiArgs.entry is exactly WrapperEventDebit.entry; XiArgs.jumps is `D_J a.env.code ⟨0⟩`.

The request evaluator is a nonrecursive abbreviation of the pinned evaluator, not another interpreter. Constructors may index their own result by `eval q`; this directly ties the result even when no settlement equation is convenient. The recursive child still must be forced by a branch-specific selection proof, never by equality of returned results alone.

## 2. Forced selected-child boundary

Before the certificate, define an inductive nonrecursive relation:

```lean
inductive StepChild : (n : Nat) → StepArgs → Option Request → Prop
```

Exactly these constructors are allowed:

* `zero`: n=0, child none.
* `ordinary`: n>0, OrdinaryGas.Ordinary a.op, child none.
* `callLow`: n=1, a.op=.CALL, child none.
* `familyLow`: n=1, a.op=CallFamilyGas.opcode k, child none.
* `callDenied`: n=m+2, actual seven-stack equation on a.mid, ¬CallOutcome.Gate a.mid value, child none.
* `familyDenied`: n=m+2, actual k-stack equation, ¬CallFamilyGas.gate k a.mid value, child none.
* `callAdmitted`: n=m+2, same actual stack equation, Gate, child `some (.theta m (callArgs ... (CallDispatchGas.entered a.mid)))`.
* `familyAdmitted`: n=m+2, same actual stack equation, gate, child `some (.theta m (familyArgs k a.mid ...))`.
* `creationDenied`: n=m+1, actual CreationGas.stack equation on a.mid, `¬nonceAllowed a.mid ∨ ¬gate a.mid value off len`, child none.
* `creationAdmitted`: n=m+1, actual stack equation, nonceAllowed and gate, child `some (.lambda m (creationArgs k a.cost a.mid value off len salt))`.

No constructor tests the final step result to decide whether to attach a child. In particular creationAdmitted attaches the child even if its settlement fails the word-addition guard. Denied creation keeps no child even if its final guard fails. Stack shape follows from ReturnedGas.accepted_stack and Z_ok_stack; malformed-stack alternatives cannot arise after accepted Z.

`callArgs` must have exactly the fields of CallGasAccounting.child (all converted source/recipient/code-target addresses preserved): hashes, created, genesis, blocks, world=pre.accountMap, original=pre.σ₀, substate=(pre.addAccessedAccount target).substate, source=ofUInt256 source, origin=pre.executionEnv.sender, target=ofUInt256 recipient, code=toExecute .EVM pre.accountMap (ofUInt256 target), gas=ofNat Ccallgas, price=ofNat pre.executionEnv.gasPrice, value/apparent, data=readWithPadding inOff inLen, depth=pre.depth+1, header, permission. CALL receives `entered a.mid`; family uses existing source/recipient/transfer/apparent/permission functions with `entered a.mid`, exactly like childResult.

`creationArgs` must expand CreationGas.child literally: charged=stepPre cost mid (which includes execLength increment), nonce-incremented world, charged.σ₀, charged.substate, owner/source, origin=sender, gas=ofNat (L charged.gasAvailable.toNat), word depth=ofNat(depth+1), exact init bytes and saltBytes. Do not use the unincremented world, original pre-Z state, raw target for CALLCODE recipient, or apparent value for stipend.

Required lower-layer signatures:

```lean
theorem stepChild_total (n : Nat) (a : StepArgs) : ∃ child, StepChild n a child
theorem stepChild_unique (h₁ : StepChild n a c₁) (h₂ : StepChild n a c₂) : c₁ = c₂
theorem stepChild_fuel (h : StepChild n a (some q)) : q.fuel < n
theorem callArgs_eval (...) :
  eval (.theta n (callArgs ...)) = CallGasAccounting.child n ...
theorem familyArgs_eval (...) :
  eval (.theta n (familyArgs ...)) = CallFamilyGas.childResult k n ...
theorem creationArgs_eval (...) :
  eval (.lambda n (creationArgs ...)) = CreationGas.child k n cost mid ...
```

The three eval equations should be rfl after unfolding adapters. Child selection is a syntactic branch relation, not a new execution function. The ignored value operand in DELEGATECALL/STATICCALL and salt in CREATE must either be set to zero in selection constructors or proved irrelevant to args, to make uniqueness painless.

## 3. Certificate constructors

```lean
inductive Cert : (q : Request) → Outcome q → EventTree → Prop
```

Use aliases XCert/XiCert/ThetaCert/LambdaCert/StepCert if readable. The only constructors are:

* X zero and Z-error: `.done`, exact .error outcome.
* X step-error: accepted Z, `Cert (.step n a) (.error err) child`; conclusion `Cert (.x (n+1) vj pre) (.error err) (.step false child .done)`.
* X continue: accepted Z, `Cert (.step n a) (.ok post) child`, H=none, `Cert (.x n vj post) result next`; conclusion `.step (decide (FrameEvents.Marked pre)) child next` and same result.
* X halt / revert: same successful step premise and exact H/REVERT tests as FrameEvents.Trace; conclusion `.step (decide (FrameEvents.Marked pre)) child .done` and exact success/revert result.
* Ξ zero: done. Ξ successor: certificate of `.x n a.jumps a.entry` with *actual* X result and tree t; conclusion `.xi (n+1) a`, actual eval result, same t.
* Θ zero: done. Θ precompile successor: actual precompile code index, actual eval result, done. Θ code successor: a.code=.Code bytes and certificate of `.xi n` with the exact MessageCall.Context execution args; actual eval outcome, same t.
* Λ zero: done. Λ successor with context.preimage=none: actual eval result, done. Λ successor with preimage=some b: certificate of `.xi n` on context.execution(address b)'s exact args; actual eval result, same t.
* Step no-child: StepChild n a none, actual eval result, done.
* Step child: StepChild n a (some q), `Cert q (eval q) t`; actual step eval result, same t.

For the X constructors, a is not an unconstrained parameter: `a = { vj, pre, mid, cost, op := (decodeAt pre).1, arg := (decodeAt pre).2, guard := hz }`. Make it a let expression in the constructor type to avoid a transport premise.

The error-step tree has a false root, retains the entire child, and has no continuation. Keeping this structural node is necessary to retain the child prefix and to distinguish the preceding local instruction positions. Successful recursive steps cannot be marked because all six recursive opcodes differ from LOG0. Wrapper constructors never add a node.

Using actual eval indices in wrapper/step constructors means their outcome soundness is immediate. Their trace completeness and branch accuracy remain substantive and come exclusively from forced selection and recursive certificates. It does NOT license a constructor taking an arbitrary child with an equal output.

## 4. Exact extraction, uniqueness, and charging boundaries

```lean
theorem sound {q : Request} {r : Outcome q} {t : EventTree}
  (h : Cert q r t) : eval q = r

theorem extract (q : Request) : ∃ t, Cert q (eval q) t

theorem deterministic {q : Request} {r₁ r₂ : Outcome q} {t₁ t₂ : EventTree}
  (h₁ : Cert q r₁ t₁) (h₂ : Cert q r₂ t₂) : t₁ = t₂
```

No `r = ok` premise on any of these. Prove extract by strong induction on q.fuel, decomposing X using existing X_succ_of_* equations; choose StepChild using totality; invoke IH for its strictly smaller selected child. Ξ/Θ/Λ positive-fuel wrapper children have fuel one less. All outcomes, including default unknown precompile result, need no case exclusion.

Charging needs one special case because StepCert carries only descendants, not its local instruction marker:

```lean
def localCharge (a : StepArgs) (r : StepResult) : Nat :=
  match r with
  | .error _ => 0
  | .ok _ => if a.op = .LOG0 ∧ 68 ≤ (a.pre.stack.getD 1 ⟨0⟩).toNat
             then 919 else 0

def extra (q : Request) (r : Outcome q) : Nat :=
  -- localCharge a r for .step; 0 for all other requests

theorem gas_bound {q : Request} {r : Outcome q} {t : EventTree}
  (h : Cert q r t) : residual q r + extra q r + 919*t.count ≤ q.gas

theorem extracted_bound (q : Request) :
  ∃ t, Cert q (eval q) t ∧ t.occurrences.Nodup ∧
    residual q (eval q) + extra q (eval q) + 919*t.count ≤ q.gas
```

Prove gas_bound by strong induction on request fuel (using child sound to rewrite actual eval), not by assuming an aggregate bound. This is the same five-way product induction as ReturnedGas.all_bounds; a dependent Request packages that product. Structural Cert induction is also logically sufficient, but the fuel proof makes the actual requested termination argument explicit.

Ordinary StepChild uses no descendant charge. When unmarked, use uncharged_step. For marked successful LOG0, generalize the short proof in FrameEvents.step_debit from decodeAt to explicit a.op using OrdinaryGas.accepted_step_debit and ActualAppendGas.accepted_log_cost. Error ordinary steps have zero residual and marker. No-child recursive branches also use uncharged_step with marker zero.

Admitted recursive StepChild gets IH residual(child)+919*child.count ≤ inputChildGas.toNat. Rewrite exact child eval adapter; turn ofNat allowance into the natural allowance using existing accepted_forwarded_fit (or accepted_allowance_le plus UInt256 bound for CREATE). Apply call_charge/family_charge/creation_charge with `charge := 919*t.count`. These lemmas already cover parent errors, child false status, caught Λ errors, and CREATE postguard rejection. Never add full CALL cost in addition to this child charge.

X continuation combines the step bound and continuation IH by arithmetic; child and next are disjoint by EventTree construction. X step-error consumes only its child bound. Halt/revert residual equals post gas. Ξ uses xi_residual; code Θ uses theta_charge; selected Λ uses lambda_charge. Zero wrappers and failed preimage have done and zero residual. Precompile wrappers have done; successful result uses ReturnedGas.precompile_theta/theta_remaining, error result has zero residual. No recursive charge premise is assumed there.

Fuel table: X(n+1)→Step(n),X(n); Ξ(n+1)→X(n); Θ/Lambda(n+1)→Ξ(n); CALL-family Step(n+2)→Θ(n); CREATE-family Step(n+1)→Lambda(n). Crucially Step(1) CREATE really attempts Lambda(0), catches its error, and can continue; Step(1) CALL reaches helper(0) and never attempts Θ.

## 5. Successful append injection and ownership

Deliver this local projection before global call-frame counting:

```lean
def localEvents : Nat → EventTree → List Nat
  | _, .done => []
  | n, .step marked _ next =>
      (if marked then [n-1] else []) ++ localEvents (n-1) next

theorem local_projection
  (h : Cert (.x fuel vj pre) result t) :
  FrameEvents.Trace vj fuel pre result (localEvents fuel t)

theorem local_address
  (h : Cert (.x fuel vj pre) result t)
  (he : event ∈ localEvents fuel t) :
  List.replicate (fuel-(event+1)) true ∈ t.occurrences
```

Use AppendEvents.exit_occurrence/deposit_occurrence or path_occurrence on local_projection. Therefore no new bytecode proof is needed. This locates an event in the exact same-fuel X subtree, including continuation failure for generic paths. XiCall.result uses Ξ(q.fuel+1); do not mistakenly use Ξ(q.fuel).

Frame identity is the path to a selected **Ξ invocation**, not each transparent Θ/Λ/Ξ wrapper and not each X continuation. Define a proof relation `XiAt top result tree path fuel args xiResult` following Cert constructors. It inserts a frame only at an actual Ξ request; its traversal through that Ξ to X enters a separate `XWithin` relation, whose continuation traversal does not insert a frame. At a child-bearing X step, follow false into the selected Θ/Λ and then its selected Ξ. Through continuation prepend true. Θ/Λ wrappers are transparent. Its result must include the actual selected XiResult, not top-level transaction success. Top X runs can expose an explicitly designated root X frame if needed; they should not invent a second Ξ invocation.

Expected theorem-facing APIs:

```lean
-- aliases abstract the internal mutually inductive traversal relations
theorem xiAt_unique (h₁ : XiAt q r t p n₁ a₁ s₁)
  (h₂ : XiAt q r t p n₂ a₂ s₂) : n₁ = n₂ ∧ a₁ = a₂ ∧ s₁ = s₂
-- use dependent equality if xiResult is stored in a packed request instead

theorem append_at_has_event
  (top : Cert root result tree)
  (at : XiAt root result tree framePath (q.fuel+1) (XiArgs.ofXiCall q) q.result)
  (user : q.env.source ≠ EvmRunner.sysAddr)
  (size : q.env.calldata.size = match kind with | .deposit => 184 | .exit => 48)
  (success : q.result = .ok (.success (created,world,gas,substate) out)) :
  ∃ k, framePath ++ List.replicate k true ∈ tree.occurrences

theorem owned_events_distinct
  (h₁ : XiAt root result tree p₁ n₁ a₁ s₁)
  (h₂ : XiAt root result tree p₂ n₂ a₂ s₂)
  (different : p₁ ≠ p₂)
  (e₁ : p₁ ++ List.replicate k₁ true ∈ tree.occurrences)
  (e₂ : p₂ ++ List.replicate k₂ true ∈ tree.occurrences) :
  p₁ ++ List.replicate k₁ true ≠ p₂ ++ List.replicate k₂ true
```

The last lemma needs the frame-path grammar from XiAt. EventTree.path_prefix_injective alone is NOT sufficient for different prefixes. Prove that two Xi roots either diverge into disjoint subtrees or the descendant root extends the ancestor by some continuation trues and then a false. Every event owned locally by a frame is its root path followed only by trues. It therefore cannot equal an event owned locally by a proper descendant. This is valid even if a hypothetical audited parent called another audited frame; no special no-child runtime theorem is necessary.

For a finite collection of successful append calls require Nodup **frame paths**, or model them as a finite subtype/set of XiAt occurrence paths. Selecting one successful proof twice is not two actual calls. Then append_at_has_event plus owned_events_distinct and EventTree.occurrences_length yields `calls.length ≤ tree.count`. Do not use equality of code address, PC, gas, payload, or proof object as occurrence identity. XiAt must survive top-level errors and rollback, exactly as Cert does.

Prop certificates cannot generally be eliminated to compute data in Type. Keep XiAt and existential membership lemmas in Prop; do not promise a computable annotated-frame enumeration by recursion over Cert proofs. If an executable frame listing becomes necessary, add it as a separate data index or construct it alongside extraction. It is not required for the counting theorem or finite-set injection.

## 6. Fixed ownership split and order

1. `NestedEventArgs.lean`: request records, eval/residual/gas wrappers, exact call/family/create child args, StepChild, totality/uniqueness/fuel and adapter equations. One owner. No imports from the certificate layer.
2. `NestedEventCert.lean`: Cert datatype, all constructors, wrapper selected-Xi args, soundness. One owner; freeze after root review. Imports Args, EventTree, existing wrappers only.
3. `NestedEventExtract.lean`: extract and deterministic; imports Cert. May progress independently of charge proof after interfaces freeze.
4. `NestedEventDebit.lean`: localCharge/extra and fuel-inductive gas_bound/extracted_bound; imports Cert, existing charge edges and Extract only for extracted_bound. No modifying cert constructors to make algebra easier.
5. `NestedAppendEvents.lean`: local projection, XiAt/XWithin traversal, ownership separation, append injection/count. Imports Extract plus AppendEvents. Root can own this along with global transaction/history composition.

Root must confirm Hermes has no overlapping ownership before authorizing any of these edits. Do not split datatype constructors across workers. For smallest initial implementation combine 1+2 under one owner; the rest consume a frozen interface. No proof implementation is authorized by this memo.

## 7. Obstructions and limits

No gas-aggregation counterexample was found in inspected semantics. Important semantic traps remain:

* Λ collision does NOT skip execution: it selects invalid bytecode 0xfe and still invokes Ξ. Only fuel zero or missing address preimage skips it. Trace the selected invalid-code frame.
* Unknown `.Precompiled p` uses the evaluator's default branch. It still has no EVM instruction subtree; preserve its exact result without asserting an exception or successful status.
* CREATE catches *all* Λ exceptions, including OutOfFuel, and substitutes empty world with zero child gas. CALL propagates Θ error. In both cases children remain selected.
* CREATE's final `(chargedGas + returnedGas).toNat` guard uses modular WORD addition. A denied creation can also reach that guard. Keep it literal; no natural-affordability liveness premise is valid.
* Step gas claims require actual accepted Z. Exposing an unconditional bound over arbitrary raw steps would be false because of underflow; extraction can be more general than gas, but that is unnecessary scope.
* A generic nested-event gas theorem alone does not provide valid transaction histories, external funding provenance, constructor initialization, block scheduling, or the normative version choice. Root's global composition must still connect actual Υ selected execution and refund/block accounting, with an independently justified collection of actual successful append frame paths.

The proposed construction closes the specific current gap: every actual nested instruction run has a forced, unique event tree; descendants survive every caught/propagated error and rollback; and actual-fuel IH pays their charge without assuming the desired aggregate inequality.
