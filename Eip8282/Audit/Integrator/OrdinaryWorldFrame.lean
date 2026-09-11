import Eip8282.Audit.Integrator.OrdinaryFunding
import Eip8282.Audit.Integrator.TransferFrame

/-!
# Protected account shape across actual ordinary steps at another owner

Only the balance is erased from the account projection: nonce, code, persistent
and transient storage are retained. Existing protected accounts survive.
Absence need not survive: SELFDESTRUCT can create an absent beneficiary with
default shape. No supply, framing postcondition or Amsterdam equivalence is
assumed. Transaction-end deletion and recursive calls are separate obligations.
-/
namespace Eip8282.Audit.Integrator.OrdinaryWorldFrame

open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.SymExec Eip8282.Audit.EntryReach
open SuccessInversion

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2400000

/-- All account fields except balance. -/
def shape (a : Account .EVM) : Account .EVM := { a with balance := ⟨0⟩ }

def observed (w : AccountMap .EVM) (a : AccountAddress) : Account .EVM :=
  shape ((w.get? a).getD default)

/-- Defaulted shape is invariant, and a previously existing account survives.
A previously absent account may be created with default shape. -/
def Preserved (before after : AccountMap .EVM) (a : AccountAddress) : Prop :=
  observed after a = observed before a ∧
  ∀ old, before.get? a = some old → ∃ current, after.get? a = some current

theorem refl (w : AccountMap .EVM) (a : AccountAddress) : Preserved w w a :=
  ⟨rfl, fun old h => ⟨old, h⟩⟩

theorem trans {u v w : AccountMap .EVM} {a : AccountAddress}
    (huv : Preserved u v a) (hvw : Preserved v w a) : Preserved u w a := by
  refine ⟨hvw.1.trans huv.1, ?_⟩
  intro old h
  obtain ⟨middle, hm⟩ := huv.2 old h
  exact hvw.2 middle hm

private theorem lookup_insert (w : AccountMap .EVM) (key a : AccountAddress)
    (acc : Account .EVM) :
    (w.insert key acc).get? a = if key = a then some acc else w.get? a := by
  exact (Std.TreeMap.getElem?_insert (t := w) (k := key) (a := a) (v := acc)).trans
    (by simp only [Std.LawfulEqOrd.compare_eq_iff_eq]; rfl)

private theorem lookup_preserved {u v : AccountMap .EVM} {a : AccountAddress}
    (h : v.get? a = u.get? a) : Preserved u v a := by
  refine ⟨?_, ?_⟩
  · simp only [observed, h]
  · intro old ho
    exact ⟨old, h.trans ho⟩

private theorem insert_away (w : AccountMap .EVM) (key a : AccountAddress)
    (acc : Account .EVM) (hne : key ≠ a) : Preserved w (w.insert key acc) a := by
  apply lookup_preserved
  rw [lookup_insert, if_neg hne]

private theorem insert_shape (w : AccountMap .EVM) (key a : AccountAddress)
    (acc : Account .EVM) (hshape : shape acc = observed w key) :
    Preserved w (w.insert key acc) a := by
  by_cases he : key = a
  · subst a
    refine ⟨?_, ?_⟩
    · simpa only [observed, lookup_insert, if_pos rfl, ite_true, Option.getD_some] using hshape
    · intro old ho
      exact ⟨acc, Std.TreeMap.getElem?_insert_self⟩
  · exact insert_away w key a acc he

private theorem balance_insert (w : AccountMap .EVM) (key a : AccountAddress)
    (acc : Account .EVM) (balance : UInt256) (ha : w.get? key = some acc) :
    Preserved w (w.insert key {acc with balance := balance}) a := by
  apply insert_shape
  simp only [observed, ha, Option.getD_some, shape]

private theorem default_insert (w : AccountMap .EVM) (key a : AccountAddress)
    (balance : UInt256) (ha : w.get? key = none) :
    Preserved w (w.insert key {(default : Account .EVM) with balance := balance}) a := by
  apply insert_shape
  simp only [observed, ha, Option.getD_none, shape]

/-- The actual SELFDESTRUCT map update changes only balances at other owners,
including when its beneficiary is the protected address. -/
theorem selfdestruct_updated (burn : Bool) (w : AccountMap .EVM)
    (source target a : AccountAddress) (hne : source ≠ a) :
    Preserved w (SelfdestructFunding.updated burn w source target) a := by
  unfold SelfdestructFunding.updated
  cases hs : w.get? source with
  | none => exact refl w a
  | some fromAcc =>
    simp only
    cases ht : w.get? target with
    | none =>
      simp only
      split
      · exact refl w a
      · exact trans (default_insert w target a fromAcc.balance ht)
          (insert_away _ source a _ hne)
    | some toAcc =>
      simp only
      split
      · exact trans (balance_insert w target a toAcc _ ht)
          (insert_away _ source a _ hne)
      · split
        · exact trans (balance_insert w target a toAcc _ ht)
            (insert_away _ source a _ hne)
        · exact refl w a

private theorem sstore_frame (st : EvmYul.State .EVM) (key value : UInt256)
    (a : AccountAddress) (hne : st.executionEnv.codeOwner ≠ a) :
    Preserved st.accountMap (st.sstore key value).accountMap a := by
  cases ha : st.accountMap.get? st.executionEnv.codeOwner with
  | none =>
    unfold EvmYul.State.sstore
    dsimp only
    rcases hg : Std.TreeMap.get! st.accountMap st.executionEnv.codeOwner with
      ⟨⟨nonce, bal, storage, code⟩, transient⟩
    have hl : st.lookupAccount st.executionEnv.codeOwner = none := ha
    rw [hl]
    exact refl _ a
  | some acc =>
    rw [SystemSpec.accountMap_sstore ha]
    exact insert_away _ _ a _ hne

private theorem tstore_frame (st : EvmYul.State .EVM) (key value : UInt256)
    (a : AccountAddress) (hne : st.executionEnv.codeOwner ≠ a) :
    Preserved st.accountMap (st.tstore key value).accountMap a := by
  unfold EvmYul.State.tstore
  dsimp only
  cases ha : st.lookupAccount st.executionEnv.codeOwner with
  | none => exact refl _ a
  | some acc => exact insert_away _ _ a _ hne

private theorem raw_sstore {arg : Option (UInt256 × Nat)} {pre post : EVM.State}
    {a : AccountAddress} (hne : pre.executionEnv.codeOwner ≠ a)
    (h : EvmYul.step (τ := .EVM) .SSTORE arg pre = .ok post) :
    Preserved pre.accountMap post.accountMap a ∧ post.executionEnv = pre.executionEnv := by
  obtain ⟨sh, pc, stk, ex⟩ := pre
  rcases stk with _ | ⟨key, _ | ⟨value, tail⟩⟩
  · cases h
  · cases h
  · cases h
    exact ⟨sstore_frame sh.toState key value a hne, executionEnv_sstore _ _ _⟩

private theorem raw_tstore {arg : Option (UInt256 × Nat)} {pre post : EVM.State}
    {a : AccountAddress} (hne : pre.executionEnv.codeOwner ≠ a)
    (h : EvmYul.step (τ := .EVM) .TSTORE arg pre = .ok post) :
    Preserved pre.accountMap post.accountMap a ∧ post.executionEnv = pre.executionEnv := by
  obtain ⟨sh, pc, stk, ex⟩ := pre
  rcases stk with _ | ⟨key, _ | ⟨value, tail⟩⟩
  · cases h
  · cases h
  · cases h
    refine ⟨tstore_frame sh.toState key value a hne, ?_⟩
    change (sh.toState.tstore key value).executionEnv = sh.executionEnv
    unfold EvmYul.State.tstore
    dsimp only
    cases sh.toState.lookupAccount sh.executionEnv.codeOwner <;> rfl

private theorem raw_selfdestruct {arg : Option (UInt256 × Nat)} {pre post : EVM.State}
    {a : AccountAddress} (hne : pre.executionEnv.codeOwner ≠ a)
    (h : EvmYul.step (τ := .EVM) .SELFDESTRUCT arg pre = .ok post) :
    Preserved pre.accountMap post.accountMap a ∧ post.executionEnv = pre.executionEnv := by
  obtain ⟨sh, pc, stk, ex⟩ := pre
  cases stk with
  | nil => cases h
  | cons dest stk =>
    change (if sh.createdAccounts.contains sh.executionEnv.codeOwner then
      Except.ok _ else Except.ok _) = Except.ok post at h
    split at h
    · cases h
      exact ⟨selfdestruct_updated true _ _ (AccountAddress.ofUInt256 dest) a hne, rfl⟩
    · cases h
      exact ⟨selfdestruct_updated false _ _ (AccountAddress.ofUInt256 dest) a hne, rfl⟩

private theorem raw_extcodehash {arg : Option (UInt256 × Nat)} {pre post : EVM.State}
    (a : AccountAddress)
    (h : EvmYul.step (τ := .EVM) .EXTCODEHASH arg pre = .ok post) :
    Preserved pre.accountMap post.accountMap a ∧ post.executionEnv = pre.executionEnv := by
  obtain ⟨sh, pc, stk, ex⟩ := pre
  cases stk with
  | nil => cases h
  | cons value stk =>
    have hm (st : EvmYul.State .EVM) (v : UInt256) :
        (st.extCodeHash v).1.accountMap = st.accountMap ∧
        (st.extCodeHash v).1.executionEnv = st.executionEnv := by
      unfold EvmYul.State.extCodeHash
      dsimp only
      split <;> exact ⟨rfl, rfl⟩
    cases h
    change Preserved sh.accountMap (sh.toState.extCodeHash value).1.accountMap a ∧
      (sh.toState.extCodeHash value).1.executionEnv = sh.executionEnv
    rw [(hm _ _).1, (hm _ _).2]
    exact ⟨refl _ a, rfl⟩

private theorem raw_dup (n : Nat) {pre post : EVM.State} (a : AccountAddress)
    (h : EvmYul.dup n pre = .ok post) :
    Preserved pre.accountMap post.accountMap a ∧ post.executionEnv = pre.executionEnv := by
  unfold EvmYul.dup at h
  dsimp only at h
  split at h
  · cases h; exact ⟨refl _ a, rfl⟩
  · cases h

private theorem raw_swap (n : Nat) {pre post : EVM.State} (a : AccountAddress)
    (h : EvmYul.swap n pre = .ok post) :
    Preserved pre.accountMap post.accountMap a ∧ post.executionEnv = pre.executionEnv := by
  unfold EvmYul.swap at h
  dsimp only at h
  split at h
  · cases h; exact ⟨refl _ a, rfl⟩
  · cases h

/-- Actual valid nonrecursive opcode semantics at a distinct code owner. -/
theorem raw_preserved {op : Operation .EVM} (hop : OrdinaryGas.Ordinary op)
    (hv : op ≠ .INVALID) {arg : Option (UInt256 × Nat)} {pre post : EVM.State}
    {a : AccountAddress} (hne : pre.executionEnv.codeOwner ≠ a)
    (h : EvmYul.step op arg pre = .ok post) :
    Preserved pre.accountMap post.accountMap a ∧ post.executionEnv = pre.executionEnv := by
  cases op <;> rename_i op <;> cases op
  all_goals first
    | exact False.elim (hv rfl)
    | (simp only [OrdinaryGas.Ordinary, Operation.isCall, Operation.isCreate,
        Bool.true_eq_false, false_and, and_false] at hop; done)
    | exact raw_selfdestruct hne h
    | exact raw_sstore hne h
    | exact raw_tstore hne h
    | exact raw_extcodehash a h
    | exact raw_dup _ a h
    | exact raw_swap _ a h
    | skip
  all_goals
    obtain ⟨sh, pc, stk, ex⟩ := pre
    rcases arg with _ | ⟨v,n⟩
    all_goals rcases stk with _ | ⟨x, _ | ⟨y, _ | ⟨z, _ | ⟨d, _ | ⟨e, _ | ⟨f, tail⟩⟩⟩⟩⟩⟩
    all_goals first
      | (cases h <;> exact ⟨refl _ a, rfl⟩)

/-- The actual dispatcher changes gas/counters, not these account projections. -/
theorem step_preserved {op : Operation .EVM} (hop : OrdinaryGas.Ordinary op)
    (hv : op ≠ .INVALID) {arg : Option (UInt256 × Nat)} {pre post : EVM.State}
    {a : AccountAddress} (hne : pre.executionEnv.codeOwner ≠ a)
    {fuel cost : Nat} (hs : StepOk fuel cost (op,arg) pre post) :
    Preserved pre.accountMap post.accountMap a ∧ post.executionEnv = pre.executionEnv := by
  cases fuel with
  | zero => change Except.error ExecutionException.OutOfFuel = Except.ok post at hs; cases hs
  | succ fuel =>
    change EVM.step (fuel+1) cost (some (op,arg)) pre = .ok post at hs
    rw [OrdinaryGas.dispatch hop] at hs
    exact raw_preserved (pre := stepPre cost pre) hop hv hne hs

/-- Accepted Z supplies validity and preserves account map/environment. -/
theorem accepted_step_preserved {vj : Array UInt256} {op : Operation .EVM}
    (hop : OrdinaryGas.Ordinary op) {arg : Option (UInt256 × Nat)}
    {pre mid post : EVM.State} {a : AccountAddress}
    (hne : pre.executionEnv.codeOwner ≠ a) {fuel cost : Nat}
    (hz : Z vj op pre = .ok (mid,cost)) (hs : StepOk fuel cost (op,arg) mid post) :
    Preserved pre.accountMap post.accountMap a ∧ post.executionEnv = pre.executionEnv := by
  have hm := Z_ok_state hz
  subst mid
  exact step_preserved (pre := zMid pre op) hop (OrdinaryGas.accepted_valid hz) hne hs

/-- Strong lookup form: all nonbalance fields of an existing account survive. -/
theorem existing_shape {before after : AccountMap .EVM} {a : AccountAddress}
    (h : Preserved before after a) {old : Account .EVM} (ho : before.get? a = some old) :
    ∃ current, after.get? a = some current ∧ shape current = shape old := by
  obtain ⟨current, hc⟩ := h.2 old ho
  refine ⟨current, hc, ?_⟩
  simpa only [observed, ho, hc, Option.getD_some] using h.1

/-- Convenient code and persistent-storage projection for installed checkpoints. -/
theorem existing_code_storage {before after : AccountMap .EVM} {a : AccountAddress}
    (h : Preserved before after a) {old : Account .EVM} (ho : before.get? a = some old) :
    ∃ current, after.get? a = some current ∧ current.code = old.code ∧
      ∀ q, current.lookupStorage q = old.lookupStorage q := by
  obtain ⟨current, hc, he⟩ := existing_shape h ho
  refine ⟨current, hc, ?_, ?_⟩
  · have hp := congrArg (fun acc : Account .EVM => acc.code) he
    simpa only [shape] using hp
  · intro q
    have hp := congrArg (fun acc : Account .EVM => acc.lookupStorage q) he
    simpa only [shape, Account.lookupStorage] using hp

#print axioms selfdestruct_updated
#print axioms raw_preserved
#print axioms accepted_step_preserved
#print axioms existing_shape
#print axioms existing_code_storage

end Eip8282.Audit.Integrator.OrdinaryWorldFrame
