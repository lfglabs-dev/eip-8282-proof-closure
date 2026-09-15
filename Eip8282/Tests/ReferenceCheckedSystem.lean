import Eip8282.Audit.Integrator.Topics.ReferenceCheckedSystem

/-! Entry-domain and resource mutations, complementing the retained bytecode
P-DRAIN/P-CONTROL kill-lines. Missing-code examples are injected source inputs;
no protocol reachability is inferred. SYSTEM has no ordinary gas allocation or
sender-fee admission, and the fresh before-state cannot be silently replaced. -/
namespace Eip8282.Tests.ReferenceCheckedSystem
open EvmYul EvmYul.EVM Eip8282.Audit.Integrator
open ReferenceCheckedSystemEntry ReferenceSourceValueTransfer
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

private def absent : Parent Bool := ⟨fun _ => none,fun _ => none⟩

theorem missing_code_excluded (kind : ReachableCalls.Contract)
    (codeParent : ReferenceCodeAccountPresence.CodeParent Bool Unit) :
    (ReferenceCodeAccountPresence.load ReferenceSourceValueTransfer.Account.codeHash false absent
      (before Bool).accounts codeParent (before Bool).codeWrites (ReachableCalls.address kind)).1 ≠ .ok (ReachableCalls.runtime kind) := by
  simp only [ReferenceCodeAccountPresence.load,ReferenceAccountLookup.peek,ReferenceAccountLookup.parentRead,
    before,absent,ReferenceCodeAccountPresence.getCode,Option.map_none,Option.getD_none,if_true]
  cases kind <;> decide +kernel

theorem rejects_ordinary_allocation (kind : ReachableCalls.Contract) (c : Context) :
    (meter kind c).execution ≠ (ReferenceTransactionGas.allocate 30000000 0).execution ∧
    (meter kind c).reservoir = 97920*16 := by
  change (30000000 : Nat) ≠ 16777216 ∧ (97920*16 : Nat) = 97920*16
  decide +kernel

/-- Source entry writes no sender debit even when all account write/read
overlays are initially empty. A fee-paying user admission is not substituted. -/
theorem entry_has_no_fee_debit {Hash Error : Type} [DecidableEq Hash]
    (kind : ReachableCalls.Contract) (c : Context) (emptyHash : Hash)
    (accountsParent : Parent Hash) (codeParent : ReferenceCodeAccountPresence.CodeParent Hash Error)
    (loaded : (ReferenceCodeAccountPresence.load ReferenceSourceValueTransfer.Account.codeHash emptyHash accountsParent
      (before Hash).accounts codeParent (before Hash).codeWrites (ReachableCalls.address kind)).1 = .ok (ReachableCalls.runtime kind)) :
    (entered kind c emptyHash accountsParent codeParent).1 = .ok () ∧
    (entered kind c emptyHash accountsParent codeParent).2.accounts.writes = (before Hash).accounts.writes ∧
    (entered kind c emptyHash accountsParent codeParent).2.accounts.reads = {ReachableCalls.address kind} := by
  rw [(ready kind c emptyHash accountsParent codeParent loaded).2]
  refine ⟨rfl,rfl,?_⟩
  simp [ReferenceTransferredFailure.fetched,ReferenceCodeAccountPresence.load,ReferenceAccountLookup.tracked,before]

#print axioms missing_code_excluded
#print axioms rejects_ordinary_allocation
#print axioms entry_has_no_fee_debit
end Eip8282.Tests.ReferenceCheckedSystem
