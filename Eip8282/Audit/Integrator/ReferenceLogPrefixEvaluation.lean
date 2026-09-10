import Eip8282.Audit.Integrator.ReferenceLogPrefixHandlers

/-! Full log-prefix transport of the same source-shaped account evaluator.
Every finite fuel is covered, including exhaustion and partial failures.
Account reads, writes, source gas events, outputs and outcome tags are identical.
Consumer: the allocated full-frame log and rollback theorem. -/
namespace Eip8282.Audit.Integrator.ReferenceLogPrefixEvaluation
open EvmYul EvmYul.EVM
open ReferenceRuntimeView ReferenceSourceReadings ReferenceMeterRollback ReferenceCheckedDispatch
open ReferenceLogPrefixHandlers
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

theorem handler (incoming : List LogEntry) (h : Handler) (d : List Nat) (owner : Bool)
    (p : ReferenceStorageView.Parent) (v : View) (w : Warm) (m : Meter) (o : ByteArray) :
    runHandler h d owner p (view incoming v) w m o = outcome incoming (runHandler h d owner p v w m o) := by
  cases h with
  | binary h =>
    simp only [runHandler]
    rw [ReferenceLogPrefixHandlers.binary]
    cases hx : ReferenceCheckedBinaryStep.run h v m with
    | error e => rcases e with ⟨e0,e1,e2⟩; rfl
    | ok r => rcases r with ⟨r0,r1⟩; rfl
  | environment h =>
    simp only [runHandler]
    rw [ReferenceLogPrefixHandlers.environment]
    cases hx : ReferenceCheckedEnvironmentStep.run h v m with
    | error e => rcases e with ⟨e0,e1,e2⟩; rfl
    | ok r => rcases r with ⟨r0,r1⟩; rfl
  | stackControl h =>
    simp only [runHandler]
    rw [ReferenceLogPrefixHandlers.stackControl]
    cases hx : ReferenceCheckedStackControlStep.run h d v m with
    | error e => rcases e with ⟨e0,e1,e2⟩; rfl
    | ok r => rcases r with ⟨r0,r1⟩; rfl
  | memoryStore h =>
    simp only [runHandler]
    rw [ReferenceLogPrefixHandlers.memoryStore]
    cases hx : ReferenceCheckedMemoryStore.run h v m with
    | error e => rcases e with ⟨e0,e1,e2⟩; rfl
    | ok r => rcases r with ⟨r0,r1⟩; rfl
  | copyLog h =>
    simp only [runHandler]
    rw [ReferenceLogPrefixHandlers.copyLog]
    cases hx : ReferenceCheckedCopyLogStep.run h v m with
    | error e => rcases e with ⟨e0,e1,e2⟩; rfl
    | ok r => rcases r with ⟨r0,r1⟩; rfl
  | load =>
    simp only [runHandler]
    rw [ReferenceLogPrefixHandlers.load]
    cases hx : ReferenceCheckedStorageStep.load p v w m with
    | error e => rcases e with ⟨e0,e1,e2,e3⟩; rfl
    | ok r => rcases r with ⟨r0,r1,r2⟩; rfl
  | store =>
    simp only [runHandler]
    rw [ReferenceLogPrefixHandlers.store]
    cases hx : ReferenceCheckedStorageStep.store owner p v w m with
    | error e => rcases e with ⟨e0,e1,e2,e3⟩; rfl
    | ok r => rcases r with ⟨r0,r1,r2⟩; rfl
  | terminal h =>
    simp only [runHandler]
    rw [ReferenceLogPrefixHandlers.terminal]
    cases hx : ReferenceCheckedTerminalStep.run h v m o with
    | error e => rcases e with ⟨e0,e1,e2,e3⟩; rfl
    | ok r => rfl

theorem dispatch (incoming : List LogEntry) (d : List Nat) (owner : Bool)
    (p : ReferenceStorageView.Parent) (v : View) (w : Warm) (m : Meter) (o : ByteArray) :
    ReferenceCheckedDispatch.run d owner p (view incoming v) w m o = outcome incoming (ReferenceCheckedDispatch.run d owner p v w m o) := by
  unfold ReferenceCheckedDispatch.run
  change (match read v.env.code v.pc with
    | .eof => .eof (view incoming v) w m o
    | .invalid t => .failed (.invalidOpcode t) (view incoming v) w m o
    | .unsupported t => .unsupported t (view incoming v) w m o
    | .handler h => runHandler h d owner p (view incoming v) w m o : Outcome) = _
  cases read v.env.code v.pc <;> try rfl
  exact handler ..

theorem assertion (incoming : List LogEntry) (selected : Dispatch) (r : Outcome) :
    ReferenceCheckedAccountDispatch.assertionReached selected (outcome incoming r) =
      ReferenceCheckedAccountDispatch.assertionReached selected r := by
  cases selected with
  | eof => cases r <;> rfl
  | invalid t => cases r <;> rfl
  | unsupported t => cases r <;> rfl
  | handler h =>
    cases h <;> cases r <;> try rfl
    rename_i fault v w m o
    cases fault <;> try rfl
    rename_i e
    cases e <;> rfl

theorem account {A : Type} (incoming : List LogEntry) (ap : ReferenceAccountLookup.Parent A)
    (a : ReferenceAccountLookup.Tx A) (d : List Nat) (p : ReferenceStorageView.Parent)
    (v : View) (w : Warm) (m : Meter) (o : ByteArray) :
    ReferenceCheckedAccountDispatch.run ap a d p (view incoming v) w m o =
      let r := ReferenceCheckedAccountDispatch.run ap a d p v w m o
      (outcome incoming r.1,r.2) := by
  unfold ReferenceCheckedAccountDispatch.run
  simp only [show (view incoming v).env = v.env from rfl,show (view incoming v).pc = v.pc from rfl,dispatch,assertion]

def evaluated {A : Type} (incoming : List LogEntry) (r : (List ReferenceMeterPath.Event × Outcome) × ReferenceAccountLookup.Tx A) :=
  ((r.1.1,outcome incoming r.1.2),r.2)

theorem eval {A : Type} (incoming : List LogEntry) (ap : ReferenceAccountLookup.Parent A)
    (d : List Nat) (p : ReferenceStorageView.Parent) (o : ByteArray)
    (fuel : Nat) (a : ReferenceAccountLookup.Tx A) (v : View) (w : Warm) (m : Meter) :
    ReferenceCheckedAccountEvaluator.eval ap d p o fuel a (view incoming v) w m =
      (ReferenceCheckedAccountEvaluator.eval ap d p o fuel a v w m).map (evaluated incoming) := by
  induction fuel generalizing a v w m with
  | zero => rfl
  | succ fuel ih =>
    simp only [ReferenceCheckedAccountEvaluator.eval,account]
    cases hx : ReferenceCheckedAccountDispatch.run ap a d p v w m o with
    | mk r nextA =>
      cases r with
      | continued next nw nm event =>
        simp only [outcome]
        rw [ih]
        simp only [Option.map_map]
        rfl
      | terminal last => rfl
      | eof last lw lm lo => rfl
      | failed e last lw lm lo => rfl
      | unsupported t last lw lm lo => rfl

#print axioms handler
#print axioms dispatch
#print axioms assertion
#print axioms account
#print axioms eval
end Eip8282.Audit.Integrator.ReferenceLogPrefixEvaluation
