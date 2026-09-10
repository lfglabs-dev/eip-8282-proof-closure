import Eip8282.Audit.Integrator.SystemTraceAnnotations
import Eip8282.Audit.Integrator.RuntimeOpcodeScope

/-! SYSTEM-specific budgets over exact operation lists of actual XRuns.
Static list checks feed the symbolic-block soundness companion; no desired
execution annotation or final storage result is assumed. Terminal halt is separate. -/
namespace Eip8282.Audit.Integrator.SystemPathBudget
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.SymExec Eip8282.Audit.EntryReach
open Eip8282.Audit.Model (Kind)
open Eip8282.Audit.XiTransport (XiCall)
open SystemTraceAnnotations
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

def Allowed (op : Op) : Prop :=
  op ∈ RuntimeOpcodeScope.allowedOps ∧ op ≠ .LOG0 ∧ op ≠ .CALLDATACOPY

instance (op : Op) : Decidable (Allowed op) := by unfold Allowed; infer_instance

def storeWeight (op : Op) : Nat := if op = .SSTORE then 1 else 0

def Reach (vj : Array UInt256) (K stores : Nat) (s t : EVM.State) : Prop :=
  ∃ ops, ops.length ≤ K ∧ weight storeWeight ops ≤ stores ∧
    (∀ op ∈ ops, Allowed op) ∧ ReachesOps vj ops s t

theorem Reach.refl (vj : Array UInt256) (s : EVM.State) : Reach vj 0 0 s s :=
  ⟨[],by simp,by simp [weight],by simp,SystemTraceAnnotations.refl vj s⟩

theorem Reach.trans {vj : Array UInt256} {K L stores more : Nat} {s t u : EVM.State}
    (h : Reach vj K stores s t) (h' : Reach vj L more t u) :
    Reach vj (K+L) (stores+more) s u := by
  obtain ⟨ops,hl,hw,ha,hr⟩ := h
  obtain ⟨ops',hl',hw',ha',hr'⟩ := h'
  refine ⟨ops++ops',by simp; omega,?_,?_,SystemTraceAnnotations.trans hr hr'⟩
  · rw [weight_append]; omega
  · intro op hop
    rcases List.mem_append.mp hop with h | h
    · exact ha op h
    · exact ha' op h

theorem Reach.mono {vj : Array UInt256} {K L stores more : Nat} {s t : EVM.State}
    (h : Reach vj K stores s t) (hk : K ≤ L) (hs : stores ≤ more) : Reach vj L more s t := by
  obtain ⟨ops,hl,hw,ha,hr⟩ := h
  exact ⟨ops,hl.trans hk,hw.trans hs,ha,hr⟩

theorem Reach.erase {vj : Array UInt256} {K stores : Nat} {s t : EVM.State}
    (h : Reach vj K stores s t) : ReachesLe vj K s t := by
  obtain ⟨ops,hl,_,_,hr⟩ := h
  exact ⟨ops.length,hl,SystemTraceAnnotations.erase hr⟩

theorem singleton {vj : Array UInt256} {s t : EVM.State} {op : Op}
    (h : Reaches vj 1 s t) (hdecode : (decodeAt s).1 = op) (allowed : Allowed op) :
    Reach vj 1 (storeWeight op) s t := by
  refine ⟨[op],by simp,by simp [weight],?_,?_⟩
  · intro o ho
    obtain rfl := List.mem_singleton.mp ho
    exact allowed
  · simpa only [hdecode] using SystemTraceAnnotations.singleton h

/-- Lift an existing actual one-step leaf without changing its selected gas or counter. -/
theorem singleton_result {vj : Array UInt256} {pre : EVM.State} {op : Op}
    {F : UInt256 → Nat → EVM.State} {K : Nat} {g₀ : UInt256}
    (h : ∃ g e, g₀.toNat-K ≤ g.toNat ∧ Reaches vj 1 pre (F g e))
    (hdecode : (decodeAt pre).1 = op) (allowed : Allowed op) :
    ∃ g e, g₀.toNat-K ≤ g.toNat ∧ Reach vj 1 (storeWeight op) pre (F g e) := by
  obtain ⟨g,e,hg,hr⟩ := h
  exact ⟨g,e,hg,singleton hr hdecode allowed⟩

/-- Bounded gas chaining, retaining both actual instruction and SSTORE budgets. -/
theorem chain {vj : Array UInt256} {k k' stores more : Nat} {s : EVM.State}
    {F G : UInt256 → Nat → EVM.State} {K K' : Nat} {g₀ : UInt256}
    (h₁ : ∃ g e, g₀.toNat-K ≤ g.toNat ∧ Reach vj k stores s (F g e))
    (h₂ : ∀ g e, g₀.toNat-K ≤ g.toNat →
      ∃ g' e', g.toNat-K' ≤ g'.toNat ∧ Reach vj k' more (F g e) (G g' e')) :
    ∃ g' e', g₀.toNat-(K+K') ≤ g'.toNat ∧ Reach vj (k+k') (stores+more) s (G g' e') := by
  obtain ⟨g,e,hg,hr⟩ := h₁
  obtain ⟨g',e',hg',hr'⟩ := h₂ g e hg
  exact ⟨g',e',by omega,hr.trans hr'⟩

theorem chainAt {kind : Kind} {c : XiCall kind} {vj : Array UInt256} {k k' K K' B stores more : Nat}
    {s : EVM.State} {st st' : EvmYul.State .EVM} {mem mem' : ByteArray} {pc pc' : Nat}
    {stk stk' : Stack UInt256} {g₀ : UInt256}
    (h₁ : ∃ (aw g : UInt256) (e : Nat), aw.toNat ≤ B ∧ g₀.toNat - K ≤ g.toNat ∧
      Reach vj k stores s (at_ c st mem aw g pc stk e))
    (h₂ : ∀ (aw g : UInt256) (e : Nat), aw.toNat ≤ B → g₀.toNat - K ≤ g.toNat →
      ∃ (aw' g' : UInt256) (e' : Nat), aw'.toNat ≤ B ∧ g.toNat - K' ≤ g'.toNat ∧
        Reach vj k' more (at_ c st mem aw g pc stk e) (at_ c st' mem' aw' g' pc' stk' e')) :
    ∃ (aw' g' : UInt256) (e' : Nat), aw'.toNat ≤ B ∧ g₀.toNat - (K + K') ≤ g'.toNat ∧
      Reach vj (k + k') (stores+more) s (at_ c st' mem' aw' g' pc' stk' e') := by
  obtain ⟨aw, g, e, haw, hg, hr⟩ := h₁
  obtain ⟨aw', g', e', haw', hg', hr'⟩ := h₂ aw g e haw hg
  exact ⟨aw', g', e', haw', by omega, hr.trans hr'⟩

/-- Lift an exact step into the threaded form: `haw` bounds the active-word
count of the machine the step lands on. Stated on `at_` so that its implicit
arguments are fixed by the expected type before the step's side goals run. -/
theorem liftAt {kind : Kind} {c : XiCall kind} {vj : Array UInt256} {k K B stores : Nat} {s : EVM.State}
    {st' : EvmYul.State .EVM} {mem' : ByteArray} {pc' : Nat} {stk' : Stack UInt256}
    {g₀ aw' : UInt256}
    (h : ∃ (g' : UInt256) (e' : Nat), g₀.toNat - K ≤ g'.toNat ∧
      Reach vj k stores s (at_ c st' mem' aw' g' pc' stk' e'))
    (haw : aw'.toNat ≤ B) :
    ∃ (aw'' g' : UInt256) (e' : Nat), aw''.toNat ≤ B ∧ g₀.toNat - K ≤ g'.toNat ∧
      Reach vj k stores s (at_ c st' mem' aw'' g' pc' stk' e') := by
  obtain ⟨g', e', hg, hr⟩ := h
  exact ⟨aw', g', e', haw, hg, hr⟩

/-- Same literal block-step interface as EntryReach, followed by finite static
opcode checks. The actual annotated trace and gas/end counter are produced. -/
theorem block_step {kind : Kind} {vj : Array UInt256} {vjNats : List Nat}
    (hvj : ∀ n ∈ vjNats, vj.contains (UInt256.ofNat n) = true)
    {code : ByteArray} (sites : List Site) (hsites : sitesOk code sites = true)
    {K n stores : Nat} (hK : blockBound sites = K) (hn : sites.length = n)
    {c : XiCall kind} {st st' : EvmYul.State .EVM} {mem : ByteArray} {aw g : UInt256}
    {pc pc' : Nat} {stk stk' : Stack UInt256} {e : Nat}
    (hshape : symBlock vjNats (sites.map Prod.snd) (at_ c st mem aw g pc stk e)
      = some (at_ c st' mem aw g pc' stk' e))
    (hcode : st.executionEnv.code = code) (hpc : pc = headPc sites)
    (hgas : K ≤ g.toNat) (hlen : stk.length+n ≤ 1024)
    (hallowed : ∀ site ∈ sites, Allowed site.2.1)
    (hstores : weight storeWeight (sites.map (fun site => site.2.1)) ≤ stores) :
    ∃ g' e', g.toNat-K ≤ g'.toNat ∧
      Reach vj n stores (at_ c st mem aw g pc stk e) (at_ c st' mem aw g' pc' stk' e') := by
  obtain ⟨g',e',hg,hr⟩ := xRuns_symBlock_ops hvj sites hsites
    (s := at_ c st mem aw g pc stk e) hcode
    (by change UInt256.ofNat pc = UInt256.ofNat (headPc sites); rw [hpc])
    (by simpa only [hK,gas_at] using hgas) (by simpa only [hn,stack_at] using hlen) hshape
  refine ⟨g',e',?_,sites.map (fun site => site.2.1),?_,hstores,?_,?_⟩
  · simpa only [hK,gas_at] using hg
  · simp [hn]
  · intro op hop
    obtain ⟨site,hs,he⟩ := List.mem_map.mp hop
    subst op
    exact hallowed site hs
  · intro f
    obtain ⟨tr,ht,ho⟩ := hr f
    exact ⟨tr,by simpa only [List.length_map,withGE_at] using ht,ho⟩

#print axioms Reach.trans
#print axioms Reach.erase
#print axioms singleton
#print axioms singleton_result
#print axioms chain
#print axioms block_step
end Eip8282.Audit.Integrator.SystemPathBudget
