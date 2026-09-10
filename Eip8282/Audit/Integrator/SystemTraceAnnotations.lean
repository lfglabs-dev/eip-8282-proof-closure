import Eip8282.Audit.EntryReach.Path

/-! Exact operation lists of actual pinned XRuns. These companions retain
operational witnesses; no SYSTEM store-count or reference replay is assumed.
The symbolic-block companion follows SymExec.xRuns_symBlock's actual steps. -/
namespace Eip8282.Audit.Integrator.SystemTraceAnnotations
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.SymExec Eip8282.Audit.EntryReach
open Eip8282.Audit.Bytecode Eip8282.Audit.Jumpdests
open Eip8282.Audit.XiTransport (XiCall jumpdestsOf)
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

abbrev Op := Operation .EVM

def operations (tr : List Labelled) : List Op := tr.map (fun label => label.2.2.1)

def ReachesOps (vj : Array UInt256) (ops : List Op) (s t : EVM.State) : Prop :=
  ∀ f, ∃ tr, XRuns vj (f+1+ops.length) s tr (f+1) t ∧ operations tr = ops

theorem erase {vj : Array UInt256} {ops : List Op} {s t : EVM.State}
    (h : ReachesOps vj ops s t) : Reaches vj ops.length s t := by
  intro f
  obtain ⟨tr,hr,_⟩ := h f
  exact ⟨tr,hr⟩

theorem refl (vj : Array UInt256) (s : EVM.State) : ReachesOps vj [] s s :=
  fun f => ⟨[],XRuns.refl (f+1) s,rfl⟩

theorem trans {vj : Array UInt256} {left right : List Op} {s t u : EVM.State}
    (hl : ReachesOps vj left s t) (hr : ReachesOps vj right t u) :
    ReachesOps vj (left++right) s u := by
  intro f
  obtain ⟨lt,hl,he⟩ := hl (f+right.length)
  obtain ⟨rt,hr,hf⟩ := hr f
  rw [show f+right.length+1+left.length = f+1+(left++right).length by simp; omega,
    show f+right.length+1 = f+1+right.length by omega] at hl
  refine ⟨lt++rt,hl.trans hr,?_⟩
  unfold operations
  rw [List.map_append]
  change operations lt ++ operations rt = left++right
  rw [he,hf]

theorem singleton {vj : Array UInt256} {s t : EVM.State} (h : Reaches vj 1 s t) :
    ReachesOps vj [(decodeAt s).1] s t := by
  intro f
  obtain ⟨tr,hr⟩ := h f
  refine ⟨tr,hr,?_⟩
  have hn : tr.length = 1 := by have := hr.length; omega
  cases hr with
  | cons step tail =>
    simp_all [operations]

theorem bounded_trace {vj : Array UInt256} {K fuel : Nat} {s t : EVM.State}
    (h : ReachesLe vj K s t) (hf : K+1 ≤ fuel) :
    ∃ tr rem, XRuns vj fuel s tr (rem+1) t ∧ tr.length ≤ K := by
  obtain ⟨k,hk,hr⟩ := h
  obtain ⟨tr,ht⟩ := hr (fuel-k-1)
  rw [show fuel-k-1+1+k = fuel by omega] at ht
  exact ⟨tr,fuel-k-1,ht,by have := ht.length; omega⟩

theorem ends_trace {kind : Eip8282.Audit.Model.Kind} {c : XiCall kind}
    {K fuel : Nat} {s : EVM.State} {op : Op} {out : ByteArray}
    (h : Ends c K s op out) (hf : K+1 ≤ fuel) :
    ∃ tr rem, XRuns (jumpdestsOf kind) fuel c.entry tr (rem+1) s ∧
      tr.length ≤ K ∧ Halt (jumpdestsOf kind) s op out := by
  obtain ⟨tr,rem,hr,hl⟩ := bounded_trace h.1 hf
  exact ⟨tr,rem,hr,hl,h.2⟩

def weight (w : Op → Nat) (ops : List Op) : Nat := (ops.map w).sum

theorem weight_append (w : Op → Nat) (left right : List Op) :
    weight w (left++right) = weight w left + weight w right := by simp [weight]

theorem xRuns_symBlock_ops {vj : Array UInt256} {vjNats : List Nat}
    (hvj : ∀ n ∈ vjNats, vj.contains (UInt256.ofNat n) = true)
    {code : ByteArray} (sites : List Site) (hsites : sitesOk code sites = true)
    {s s' : EVM.State}
    (hcode : s.executionEnv.code = code) (hpc : s.pc = UInt256.ofNat (headPc sites))
    (hgas : blockBound sites ≤ s.gasAvailable.toNat)
    (hlen : s.stack.length + sites.length ≤ 1024)
    (hsym : symBlock vjNats (sites.map Prod.snd) s = some s') :
    ∃ g' e', s.gasAvailable.toNat - blockBound sites ≤ g'.toNat ∧
      ∀ f, ∃ tr, XRuns vj (f + 1 + sites.length) s tr (f + 1) (withGE s' g' e') ∧ operations tr = (sites.map (fun site => site.2.1)) := by
  induction sites generalizing s s' with
  | nil =>
    simp only [List.map_nil, symBlock, Option.some.injEq] at hsym
    subst hsym
    exact ⟨s.gasAvailable, s.execLength, by omega, fun f => ⟨[], XRuns.refl (f + 1) s,rfl⟩⟩
  | cons site rest ih =>
    obtain ⟨pc, i⟩ := site
    obtain ⟨hop, hrest⟩ := sitesOk_cons hsites
    rw [List.map_cons, symBlock_cons] at hsym
    cases hs₁ : symStep vjNats i s with
    | none => rw [hs₁] at hsym; exact absurd hsym (by simp)
    | some s₁ =>
    rw [hs₁] at hsym
    change symBlock vjNats (rest.map Prod.snd) s₁ = some s' at hsym
    obtain ⟨hguard, hstep₁⟩ := guardOk_of_symStep hs₁
    have hmem := mem_blockOps_of_guardOk hguard
    have hps : pureStep i s = some s₁ := by
      unfold symStep at hs₁; rw [if_pos hguard] at hs₁; exact hs₁
    have hgrow := (pureStep_stack_ok hmem (arg := i.2) hps).2
    have hlen' : s.stack.length + (rest.length + 1) ≤ 1024 := hlen
    have hover : s.stack.length < 1024 := by omega
    have hdec : decodeAt s = i := decodeAt_of_code_pc hcode hpc hop
    rw [blockBound_cons] at hgas
    have hgas' : costBound i.1 + blockBound rest ≤ s.gasAvailable.toNat := hgas
    have hcost : costBound i.1 ≤ s.gasAvailable.toNat := by omega
    have hC := C'_le_costBound hmem s
    have hg₁ : (s.gasAvailable - UInt256.ofNat (C' s i.1)).toNat
        = s.gasAvailable.toNat - C' s i.1 := toNat_sub_ofNat (by omega)
    rcases hrest with rfl | ⟨hhead, hne, hrest⟩
    · change some s₁ = some s' at hsym
      obtain rfl := Option.some.inj hsym
      refine ⟨_, _, ?_, fun f => ⟨_,
        XRuns.cons (xStepAt_symStep hvj (f := f) hdec hs₁ hcost hover) (XRuns.refl (f + 1) _),by simp [operations,hdec]⟩⟩
      change s.gasAvailable.toNat - (costBound i.1 + blockBound []) ≤
        (s.gasAvailable - UInt256.ofNat (C' s i.1)).toNat
      rw [hg₁]
      simp only [blockBound, List.map_nil, List.sum_nil]
      omega
    · have hcode₁ : (bump (C' s i.1) s s₁).executionEnv.code = code := by
        show s₁.executionEnv.code = code
        rw [executionEnv_step (List.mem_append_left _ hmem) hstep₁, hcode]
      have hpc₁ : (bump (C' s i.1) s s₁).pc = UInt256.ofNat (headPc rest) := by
        show s₁.pc = _
        rw [pc_step hmem hne (arg_width_of_opcodeAt hop) hstep₁, hpc, ofNat_add_ofNat, hhead]
        show UInt256.ofNat (pc + (argOnNBytesOfInstr i.1 + 1))
          = UInt256.ofNat (pc + 1 + argOnNBytesOfInstr i.1)
        congr 1
        omega
      have hgas₁ : blockBound rest ≤ (bump (C' s i.1) s s₁).gasAvailable.toNat := by
        change blockBound rest ≤ (s.gasAvailable - UInt256.ofNat (C' s i.1)).toNat
        rw [hg₁]; omega
      have hsym₁ : symBlock vjNats (rest.map Prod.snd) (bump (C' s i.1) s s₁)
          = some (withGE s' (s.gasAvailable - UInt256.ofNat (C' s i.1)) (s.execLength + 1)) := by
        show symBlock vjNats (rest.map Prod.snd) (withGE s₁ _ _) = _
        rw [symBlock_withGE, hsym]
        rfl
      have hlen₁ : (bump (C' s i.1) s s₁).stack.length + rest.length ≤ 1024 := by
        show s₁.stack.length + rest.length ≤ 1024
        omega
      obtain ⟨g', e', hbound, hrun⟩ := ih hrest hcode₁ hpc₁ hgas₁ hlen₁ hsym₁
      refine ⟨g', e', ?_, fun f => ?_⟩
      · change (s.gasAvailable - UInt256.ofNat (C' s i.1)).toNat - blockBound rest ≤ g'.toNat
          at hbound
        rw [hg₁] at hbound
        rw [blockBound_cons]
        change s.gasAvailable.toNat - (costBound i.1 + blockBound rest) ≤ g'.toNat
        omega
      · obtain ⟨tr, hrun,hops⟩ := hrun f
        rw [withGE_withGE] at hrun
        have hx := xStepAt_symStep hvj (f := f + rest.length) hdec hs₁ hcost hover
        rw [show f + rest.length + 1 = f + 1 + rest.length by omega] at hx
        exact ⟨_, XRuns.cons hx hrun,by simpa [operations,hdec] using congrArg (List.cons i.1) hops⟩

#print axioms erase
#print axioms trans
#print axioms singleton
#print axioms bounded_trace
#print axioms ends_trace
#print axioms weight_append
#print axioms xRuns_symBlock_ops
end Eip8282.Audit.Integrator.SystemTraceAnnotations
