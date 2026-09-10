import Eip8282.Audit.Integrator.CodeStorageFrame
import Eip8282.Audit.Integrator.CreationWorld

/-! Creation entry preserves existing code and persistent storage, including
sender/target aliasing. Installation is framed only away from its target.
Occupied-target rejection concerns completed Lambda results, not caught errors. -/
namespace Eip8282.Audit.Integrator.CreationStorageFrame
open EvmYul EvmYul.EVM
open CreationSettlement CodeStorageFrame
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

private theorem lookup_insert (world : AccountMap .EVM) (key addr : AccountAddress)
    (account : Account .EVM) :
    (world.insert key account).get? addr = if key = addr then some account else world.get? addr := by
  exact (Std.TreeMap.getElem?_insert (t := world) (k := key) (a := addr) (v := account)).trans
    (by simp only [Std.LawfulEqOrd.compare_eq_iff_eq]; rfl)

/-- Literal debit and fresh-account insertion preserve code, including aliases. -/
theorem entry_frame (c : Context) (target protectedAddr : AccountAddress) :
    Frame c.world (c.entryWorld target) protectedAddr := by
  constructor
  · intro old hold
    unfold Context.entryWorld
    cases hs : c.world.get? c.sender with
    | none => exact ⟨old,hold,rfl⟩
    | some sender =>
      dsimp only
      by_cases ht : target = protectedAddr
      · subst target
        refine ⟨{ (c.existing protectedAddr) with nonce := (c.existing protectedAddr).nonce + ⟨1⟩, balance := c.value + (c.existing protectedAddr).balance }, ?_, ?_⟩
        · exact Std.TreeMap.getElem?_insert_self
        · change (c.existing protectedAddr).code = old.code
          unfold Context.existing
          rw [Std.TreeMap.getD_eq_getD_getElem?]
          change ((c.world.get? protectedAddr).getD default).code = old.code
          rw [hold]
          rfl
      · rw [lookup_insert, if_neg ht]
        by_cases ha : c.sender = protectedAddr
        · rw [lookup_insert, if_pos ha]
          refine ⟨_,rfl,?_⟩
          have he : sender = old := Option.some.inj ((ha ▸ hs).symm.trans hold)
          change sender.code = old.code
          exact congrArg (fun a : Account .EVM => a.code) he
        · rw [lookup_insert, if_neg ha]
          exact ⟨old,hold,rfl⟩
  · exact CreationSettlement.entry_storage c target protectedAddr

theorem install_away_frame (world : AccountMap .EVM) (target protectedAddr : AccountAddress)
    (code : ByteArray) (hne : target ≠ protectedAddr) :
    Frame world (install world target code) protectedAddr := by
  constructor
  · intro old hold
    refine ⟨old,?_,rfl⟩
    unfold install
    rw [lookup_insert, if_neg hne]
    exact hold
  · exact CreationSettlement.install_storage world target protectedAddr code

/-- The occupied guard rejects even a hypothetical successful initializer;
ordinary init errors and reverts also return the exact input world. -/
theorem occupied_creation_fails (c : Context) {bytes : ByteArray}
    {old : Account .EVM} {target : AccountAddress}
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {ss : Substate} {status : Bool} {out : ByteArray}
    (hp : c.preimage = some bytes)
    (hold : c.world.get? (address bytes) = some old) (hcode : old.code ≠ .empty)
    (hr : c.result = .ok (target,created,world,gas,ss,status,out)) :
    status = false ∧ world = c.world := by
  have hf (gas : UInt256) (code : ByteArray) : c.depositFailure (address bytes) gas code = true := by
    unfold Context.depositFailure
    simp only [hold]
    simp [hcode]
  rw [result_eq_settle c hp] at hr
  cases he : c.execution (address bytes) with
  | error err =>
    simp only [Context.settle, he] at hr
    split at hr
    · cases hr
    · cases hr; exact ⟨rfl,rfl⟩
  | ok result =>
    cases result with
    | revert remaining output =>
      simp only [Context.settle, he] at hr
      cases hr; exact ⟨rfl,rfl⟩
    | success state code =>
      obtain ⟨cr,w,g,sub⟩ := state
      simp only [Context.settle, he, hf, ↓reduceIte, Bool.not_true] at hr
      cases hr; exact ⟨rfl,rfl⟩

#print axioms entry_frame
#print axioms install_away_frame
#print axioms occupied_creation_fails
end Eip8282.Audit.Integrator.CreationStorageFrame
