import Eip8282.Audit.Integrator.Topics.Factory
import Eip8282.Audit.Integrator.FactoryRuntimeReturn
import Eip8282.Audit.Integrator.CreationSettlementProgress
import Eip8282.Audit.Integrator.Topics.Journal
import Eip8282.Audit.Integrator.InitializerJournalFields
import Eip8282.Audit.Integrator.InitializerWorldFrame

/-! Initializer success is produced for the selected CREATE2 child, then
composed through the actual factory continuation. Canonical hash identity,
collision freedom, installed factory and transaction admission remain explicit
bindings; no raw initializer output is silently treated as a committed world. -/
namespace Eip8282.Audit.Integrator.FactoryInitializedExecution
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.SymExec Eip8282.Audit.EntryReach
open NestedEvents FactoryRuntimeEntry FactoryChildResources
open ReachableCalls (Contract address)
open JournalInvariant (modelKind Invariant)
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

private theorem post_shape (kind : Eip8282.Audit.Model.Kind) (a : XiArgs)
    (gas : UInt256) (e : Nat) (addr : AccountAddress) (cr : Created) (w : World)
    (ret : UInt256) (ss : Substate) :
    let p := CreationSettlementProgress.successfulPost (createCost kind) (atCreate kind a gas e)
      ⟨0⟩ (UInt256.ofNat (initSize kind)) [⟨0⟩,UInt256.ofNat (initSize kind)] addr cr w ret ss
    p = FactoryRuntimeReturn.start kind {a with created := cr,world := w,substate := ss}
      (UInt256.ofNat addr) p.gasAvailable (e+1) := by
  cases kind <;> rfl

/-- Actual complete factory Xi success with the initializer-derived invariant.
The gas range is an explicit deployment-call resource envelope, not an assumed
arithmetic no-wrap property. The upper bound is used at the literal CREATE2
WORD guard and still requires the canonical transaction admission adapter. -/
theorem initializes (kind : Contract) (a : XiArgs) (steps : Nat)
    (hcode : a.env.code = FactoryRuntimeEntry.runtime)
    (hdata : a.env.calldata = calldata (modelKind kind))
    (ha : a.env.codeOwner = factoryAddress) (hp : a.env.perm = true)
    (hgas : 1000000 ≤ a.gas.toNat) (hupper : a.gas.toNat ≤ 2^64) (hf : 13 ≤ steps)
    (hn : (a.world.get? a.env.codeOwner |>.getD default).nonce.toNat < 2^64-1)
    (hv : a.env.weiValue ≤ (a.world.get? a.env.codeOwner |>.option ⟨0⟩ (·.balance)))
    (hd : a.env.depth < 1024)
    (hcollision : ((childArgs (modelKind kind) a a.gas 0).context (steps+1)).collision
      (CreationSettlement.address (preimage (modelKind kind))) = false)
    (haddress : CreationSettlement.address (preimage (modelKind kind)) = address kind) :
    ∃ cr w gas ss,
      (Request.xi (steps+18) a).eval = .ok (.success (cr,w,gas,ss)
        (FactoryRuntimeReturn.output (modelKind kind) (UInt256.ofNat (address kind)))) ∧
      Invariant kind 0 w ∧ ss.logSeries = a.substate.logSeries ∧
      ss.selfDestructSet = a.substate.selfDestructSet ∧
      ∀ protectedAddr, factoryAddress ≠ protectedAddr → address kind ≠ protectedAddr →
        CodeStorageFrame.Frame a.world w protectedAddr := by
  let k := modelKind kind
  obtain ⟨gas,e,hg,hr,hselected,heval,hdom,hresources⟩ := entry_resources k a steps
    hcode hdata ha hp hgas (by omega) hn hv hd hcollision
  obtain ⟨cr,w,ret,ss,hchild,hinv⟩ := JournalGuarantees.initializes kind
    ((childArgs k a gas e).context (steps+1)) (preimage k) steps
    (child_init k a gas e) hdom hresources haddress
  have hfields := InitializerJournalFields.completed k
    ((childArgs k a gas e).context (steps+1)) (preimage k) steps
    (child_init k a gas e) hdom hchild
  have hframes : ∀ protectedAddr, factoryAddress ≠ protectedAddr → address kind ≠ protectedAddr →
      CodeStorageFrame.Frame a.world w protectedAddr := by
    intro protectedAddr hfactory htarget
    have hentry := (JournalChildEntry.selected_lambda_input hselected protectedAddr
      (by change a.env.codeOwner ≠ protectedAddr; rw [ha]; exact hfactory)).1
    have hinit := InitializerWorldFrame.preserves k
      ((childArgs k a gas e).context (steps+1)) (preimage k) steps protectedAddr
      (child_init k a gas e) hdom (by rw [haddress]; exact htarget) hchild
    exact CodeStorageFrame.trans hentry hinit
  rw [← heval] at hchild
  have hchild' : CreationGas.child .create2 (steps+2) (createCost k) (atCreate k a gas e)
      a.env.weiValue ⟨0⟩ (UInt256.ofNat (initSize k)) (salt k) =
      .ok (address kind,cr,w,ret,ss,true,.empty) := by
    rw [haddress] at hchild
    exact hchild
  have hgate : CreationGas.gate (atCreate k a gas e) a.env.weiValue ⟨0⟩
      (UInt256.ofNat (initSize k)) := by
    refine ⟨hv,hd,?_⟩
    change (childArgs k a gas e).init.size ≤ 49152
    rw [child_init,init_size]
    cases kind <;> decide
  have hcharged : (stepPre (createCost k) (atCreate k a gas e)).gasAvailable.toNat =
      gas.toNat-createCost k := toNat_sub_ofNat hg
  have hgasupper := FactoryPrefixGas.atCreate_gas_le hr
  obtain ⟨hstep,hremain⟩ := CreationSettlementProgress.step_success .create2 (steps+2)
    (createCost k) (atCreate k a gas e) none a.env.weiValue ⟨0⟩
    (UInt256.ofNat (initSize k)) (salt k) [⟨0⟩,UInt256.ofNat (initSize k)]
    (address kind) cr w ret ss .empty rfl hn hgate hchild'
    (by rw [hcharged]; omega)
  let post := CreationSettlementProgress.successfulPost (createCost k) (atCreate k a gas e)
    ⟨0⟩ (UInt256.ofNat (initSize k)) [⟨0⟩,UInt256.ofNat (initSize k)] (address kind) cr w ret ss
  have hpostgas : 200 ≤ post.gasAvailable.toNat := by
    have hb : 116600 ≤ InitializerProgress.creationGas k := by cases kind <;> decide
    rw [child_gas_exact k a gas e hg] at hresources
    rw [hcharged] at hremain
    unfold L at hresources
    change _ ≤ post.gasAvailable.toNat at hremain
    omega
  have hxstep : XStepAt a.jumps (steps+3) (createCost k) (atCreate k a gas e) post := by
    refine ⟨atCreate k a gas e,?_,?_,?_⟩
    all_goals
      have hdcode : decodeAt (atCreate k a gas e) = (.CREATE2,none) :=
        decodeAt_of_code_pc (by exact hcode) rfl (create_site)
      rw [hdcode]
    · exact create_guard k a gas e hp hg
    · exact hstep
    · rfl
  have hnonzero : UInt256.ofNat (address kind) ≠ (⟨0⟩ : UInt256) := by cases kind <;> decide
  let after : XiArgs := {a with created := cr,world := w,substate := ss}
  obtain ⟨final,htail,hw,hcr,hss,_⟩ := FactoryRuntimeReturn.execution k after
    (UInt256.ofNat (address kind)) post.gasAvailable (e+1) (steps+3)
    hcode hnonzero hpostgas (by omega)
  have hshape : post = FactoryRuntimeReturn.start k after (UInt256.ofNat (address kind))
      post.gasAvailable (e+1) := post_shape k a gas e (address kind) cr w ret ss
  rw [← hshape] at htail
  have hprefix := XReaches.X_eq (hr (steps+3))
  have hx : X (steps+17) a.jumps a.entry = .ok (.success final
      (FactoryRuntimeReturn.output k (UInt256.ofNat (address kind)))) := by
    calc
      _ = X (steps+4) a.jumps (atCreate k a gas e) := hprefix
      _ = X (steps+3) a.jumps post := hxstep.X_succ
      _ = _ := htail
  refine ⟨cr,w,final.gasAvailable,ss,?_,hinv,hfields.1,hfields.2,hframes⟩
  change (do
    let r ← X (steps+17) a.jumps a.entry
    match r with
    | .success st out => Except.ok (ExecutionResult.success (st.createdAccounts,st.accountMap,st.gasAvailable,st.substate) out)
    | .revert g out => Except.ok (ExecutionResult.revert g out)) = _
  rw [hx]
  simp only [Bind.bind,Except.bind,hw,hcr,hss]
  rfl

#print axioms initializes
end Eip8282.Audit.Integrator.FactoryInitializedExecution
