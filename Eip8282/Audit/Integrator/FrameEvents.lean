import Eip8282.Audit.Integrator.ReturnedGas

/-!
# Actual frame events for every evaluator outcome

These certificates enrich the actual X execution with instruction occurrences.
They retain local events before REVERT, exceptional halt and OutOfFuel. They
count only this frame's executed LOG0 instructions of length at least 68; child
frames are still opaque steps and must be attached separately for a tree bound.
-/
namespace Eip8282.Audit.Integrator.FrameEvents
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.EntryReach
open SuccessInversion
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1400000

/-- A conservative local superset of the two audited append log sites. The
actual stack operand is inspected; no stipulated gas charge is used. -/
def Marked (pre : EVM.State) : Prop :=
  (decodeAt pre).1 = .LOG0 ∧ 68 ≤ (pre.stack.getD 1 ⟨0⟩).toNat

instance (pre : EVM.State) : Decidable (Marked pre) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Fuel is an occurrence index within a frame, not a gas estimate. -/
def emit (pre : EVM.State) (fuel : Nat) : List Nat := if Marked pre then [fuel] else []

/-- Errors have no returned gas. Zero is solely the residual used in this
accounting inequality; no actual error endpoint is invented. -/
def residual : Except ExecutionException (ExecutionResult EVM.State) → Nat
  | .error _ => 0
  | .ok result => (ReturnedGas.xGas result).toNat

/-- All outcomes of literal X. Failed child steps retain their actual error;
only local events are indexed here, so those children's events are not counted. -/
inductive Trace (vj : Array UInt256) : Nat → EVM.State →
    Except ExecutionException (ExecutionResult EVM.State) → List Nat → Prop where
  | zero (pre : EVM.State) : Trace vj 0 pre (.error .OutOfFuel) []
  | guardError {fuel : Nat} {pre : EVM.State} {err : ExecutionException}
      (guard : Z vj (decodeAt pre).1 pre = .error err) :
      Trace vj (fuel+1) pre (.error err) []
  | stepError {fuel cost : Nat} {pre mid : EVM.State} {err : ExecutionException}
      (guard : Z vj (decodeAt pre).1 pre = .ok (mid,cost))
      (step : Step fuel cost (decodeAt pre) mid (.error err)) :
      Trace vj (fuel+1) pre (.error err) []
  | next {fuel cost : Nat} {pre mid post : EVM.State}
      {result : Except ExecutionException (ExecutionResult EVM.State)} {events : List Nat}
      (guard : Z vj (decodeAt pre).1 pre = .ok (mid,cost))
      (step : StepOk fuel cost (decodeAt pre) mid post)
      (cont : H post.toMachineState (decodeAt pre).1 = none)
      (tail : Trace vj fuel post result events) :
      Trace vj (fuel+1) pre result (emit pre fuel ++ events)
  | halt {fuel cost : Nat} {pre mid post : EVM.State} {out : ByteArray}
      (guard : Z vj (decodeAt pre).1 pre = .ok (mid,cost))
      (step : StepOk fuel cost (decodeAt pre) mid post)
      (halt : H post.toMachineState (decodeAt pre).1 = some out)
      (normal : (decodeAt pre).1 ≠ .REVERT) :
      Trace vj (fuel+1) pre (.ok (.success post out)) (emit pre fuel)
  | revert {fuel cost : Nat} {pre mid post : EVM.State} {out : ByteArray}
      (guard : Z vj (decodeAt pre).1 pre = .ok (mid,cost))
      (step : StepOk fuel cost (decodeAt pre) mid post)
      (halt : H post.toMachineState (decodeAt pre).1 = some out)
      (reverting : (decodeAt pre).1 = .REVERT) :
      Trace vj (fuel+1) pre (.ok (.revert post.gasAvailable out)) (emit pre fuel)

/-- A certificate cannot describe an alternate result or a larger-fuel run. -/
theorem sound {vj : Array UInt256} {fuel : Nat} {pre : EVM.State}
    {result : Except ExecutionException (ExecutionResult EVM.State)} {events : List Nat}
    (h : Trace vj fuel pre result events) : X fuel vj pre = result := by
  induction h with
  | zero => rfl
  | guardError hz => exact X_succ_of_Z_error rfl hz
  | stepError hz hs => exact X_succ_of_step_error rfl hz hs
  | next hz hs hh _ ih => exact (X_succ_of_continue rfl hz hs hh).trans ih
  | halt hz hs hh hn => exact X_succ_of_halt rfl hz hs hh hn
  | revert hz hs hh hr => exact X_succ_of_revert rfl hz hs hh hr

/-- Every literal X execution has such a certificate, including errors. This
is extraction from the evaluator, not a supplied trace or success-only premise. -/
theorem extract (vj : Array UInt256) (fuel : Nat) (pre : EVM.State) :
    ∃ events, Trace vj fuel pre (X fuel vj pre) events := by
  induction fuel generalizing pre with
  | zero => exact ⟨[], .zero pre⟩
  | succ fuel ih =>
      cases hz : Z vj (decodeAt pre).1 pre with
      | error err =>
          rw [X_succ_of_Z_error rfl hz]
          exact ⟨[], .guardError hz⟩
      | ok charged =>
          obtain ⟨mid,cost⟩ := charged
          cases hs : EVM.step fuel cost (some (decodeAt pre)) mid with
          | error err =>
              rw [X_succ_of_step_error rfl hz hs]
              exact ⟨[], .stepError hz hs⟩
          | ok post =>
              cases hh : H post.toMachineState (decodeAt pre).1 with
              | none =>
                  obtain ⟨events,ht⟩ := ih post
                  rw [X_succ_of_continue rfl hz hs hh]
                  exact ⟨_, .next hz hs hh ht⟩
              | some out =>
                  by_cases hr : (decodeAt pre).1 = .REVERT
                  · rw [X_succ_of_revert rfl hz hs hh hr]
                    exact ⟨_, .revert hz hs hh hr⟩
                  · rw [X_succ_of_halt rfl hz hs hh hr]
                    exact ⟨_, .halt hz hs hh hr⟩

/-- Every emitted occurrence is paid by the real accepted opcode. Other
instructions, including recursive calls/creation, have nonincreasing gas. -/
theorem step_debit {vj : Array UInt256} {fuel cost : Nat} {pre mid post : EVM.State}
    (hz : Z vj (decodeAt pre).1 pre = .ok (mid,cost))
    (hs : StepOk fuel cost (decodeAt pre) mid post) :
    post.gasAvailable.toNat + 919*(emit pre fuel).length ≤ pre.gasAvailable.toNat := by
  by_cases hm : Marked pre
  · obtain ⟨hop,hlen⟩ := hm
    have hz' : Z vj .LOG0 pre = .ok (mid,cost) := hop ▸ hz
    have hsize := ReturnedGas.accepted_stack hz'
    have htwo : 2 ≤ pre.stack.length := by simpa only [δ, Option.getD_some] using hsize
    obtain ⟨off,len,rest,hstack⟩ : ∃ off len rest, pre.stack = off::len::rest := by
      rcases he : pre.stack with _ | ⟨off, _ | ⟨len,rest⟩⟩
      all_goals simp_all
    have hd := OrdinaryGas.accepted_step_debit
      (show OrdinaryGas.Ordinary (decodeAt pre).1 from hop ▸ (by decide)) hz hs
    have hc := ActualAppendGas.accepted_log_cost hstack hz'
    have hl : 68 ≤ len.toNat := by simpa only [hstack, List.getD_cons_succ, List.getD_cons_zero] using hlen
    have hmark : Marked pre := ⟨hop,hlen⟩
    simp only [emit, if_pos hmark, List.length_singleton]
    omega
  · have hd := ReturnedGas.step_remaining fuel hz hs
    simpa only [emit, if_neg hm, List.length_nil, Nat.mul_zero, Nat.add_zero] using hd

/-- All local events remain counted irrespective of final outcome or journal
rollback. The aggregate inequality is derived from actual steps. -/
theorem gas_bound {vj : Array UInt256} {fuel : Nat} {pre : EVM.State}
    {result : Except ExecutionException (ExecutionResult EVM.State)} {events : List Nat}
    (h : Trace vj fuel pre result events) :
    residual result + 919*events.length ≤ pre.gasAvailable.toNat := by
  induction h with
  | zero => exact Nat.zero_le _
  | guardError => exact Nat.zero_le _
  | stepError => exact Nat.zero_le _
  | next hz hs _ _ ih =>
      have hd := step_debit hz hs
      rw [List.length_append, Nat.mul_add]
      omega
  | halt hz hs _ _ => exact step_debit hz hs
  | revert hz hs _ _ => exact step_debit hz hs

private theorem mem_emit {pre : EVM.State} {fuel event : Nat} (h : event ∈ emit pre fuel) : event = fuel := by
  unfold emit at h
  split at h
  · exact List.mem_singleton.mp h
  · cases h

/-- Decreasing evaluator fuel uniquely labels local instruction occurrences,
even if the PC loops back to the same byte offset. -/
theorem occurrence_lt {vj : Array UInt256} {fuel : Nat} {pre : EVM.State}
    {result : Except ExecutionException (ExecutionResult EVM.State)} {events : List Nat}
    (h : Trace vj fuel pre result events) : ∀ event ∈ events, event < fuel := by
  induction h with
  | zero => simp
  | guardError => simp
  | stepError => simp
  | next _ _ _ _ ih =>
      intro event he
      rcases List.mem_append.mp he with he | he
      · have hh := mem_emit he; omega
      · have hh := ih event he; omega
  | halt => intro event he; have hh := mem_emit he; omega
  | revert => intro event he; have hh := mem_emit he; omega

theorem distinct {vj : Array UInt256} {fuel : Nat} {pre : EVM.State}
    {result : Except ExecutionException (ExecutionResult EVM.State)} {events : List Nat}
    (h : Trace vj fuel pre result events) : events.Nodup := by
  induction h with
  | zero => exact List.nodup_nil
  | guardError => exact List.nodup_nil
  | stepError => exact List.nodup_nil
  | @next fuel cost pre mid post result events hz hs hh ht ih =>
      unfold emit
      split
      · simp only [List.singleton_append, List.nodup_cons]
        exact ⟨fun he => (Nat.lt_irrefl fuel) (occurrence_lt ht fuel he), ih⟩
      · exact ih
  | halt => unfold emit; split <;> simp
  | revert => unfold emit; split <;> simp

/-- The actual evaluator fixes the entire local occurrence list, not only its
result. Certificates cannot omit an executed local event or duplicate one. -/
theorem deterministic {vj : Array UInt256} {fuel : Nat} {pre : EVM.State}
    {result₁ result₂ : Except ExecutionException (ExecutionResult EVM.State)}
    {events₁ events₂ : List Nat}
    (h₁ : Trace vj fuel pre result₁ events₁) (h₂ : Trace vj fuel pre result₂ events₂) :
    events₁ = events₂ := by
  induction h₁ generalizing result₂ events₂ with
  | zero => cases h₂; rfl
  | guardError hz => cases h₂ <;> simp_all
  | stepError hz hs => cases h₂ <;> simp_all [StepOk, Step]
  | next hz hs hh ht ih =>
      cases h₂ <;> simp_all [StepOk, Step]
      exact ih (by assumption)
  | halt hz hs hh hn => cases h₂ <;> simp_all [StepOk, Step]
  | revert hz hs hh hr => cases h₂ <;> simp_all [StepOk, Step]

/-- Embed an existing actual nonhalting prefix in the all-outcome certificate.
The prefix's events are recovered from its real steps. -/
theorem prepend {vj : Array UInt256} {fuel rest : Nat} {pre post : EVM.State}
    {labels : List Labelled} {result : Except ExecutionException (ExecutionResult EVM.State)}
    {events : List Nat} (hp : XRuns vj fuel pre labels rest post)
    (ht : Trace vj rest post result events) :
    ∃ earlier, Trace vj fuel pre result (earlier ++ events) := by
  induction hp with
  | refl => exact ⟨[],ht⟩
  | @cons fuel cost rest pre mid post labels hs hp ih =>
      obtain ⟨earlier,hprefix⟩ := ih ht
      obtain ⟨charged,hz,hs,hh⟩ := hs
      refine ⟨emit pre fuel ++ earlier, ?_⟩
      simpa only [List.append_assoc] using Trace.next hz hs hh hprefix

/-- A real qualifying LOG site in any actual prefix belongs to the SAME
uniquely extracted occurrence list, even if its continuation later fails. -/
theorem contains_site {vj : Array UInt256} {fuel site cost : Nat}
    {pre atLog post : EVM.State} {labels : List Labelled}
    {result : Except ExecutionException (ExecutionResult EVM.State)} {events : List Nat}
    (ht : Trace vj fuel pre result events)
    (hp : XRuns vj fuel pre labels (site+1) atLog)
    (hs : XStepAt vj site cost atLog post) (marked : Marked atLog) : site ∈ events := by
  obtain ⟨tailEvents,tail⟩ := extract vj site post
  obtain ⟨mid,hz,hs,hh⟩ := hs
  have atSite := Trace.next hz hs hh tail
  obtain ⟨earlier,hprefix⟩ := prepend hp atSite
  rw [← deterministic hprefix ht]
  simp only [emit, if_pos marked, List.singleton_append, List.mem_append, List.mem_cons,
    true_or, or_true]

/-- Universal all-outcome extraction and accounting for one actual frame.
This does not yet count the events inside opaque child steps. -/
theorem extracted_bound (vj : Array UInt256) (fuel : Nat) (pre : EVM.State) :
    ∃ events, Trace vj fuel pre (X fuel vj pre) events ∧ events.Nodup ∧
      residual (X fuel vj pre) + 919*events.length ≤ pre.gasAvailable.toNat := by
  obtain ⟨events,ht⟩ := extract vj fuel pre
  exact ⟨events,ht,distinct ht,gas_bound ht⟩

#print axioms sound
#print axioms extract
#print axioms step_debit
#print axioms gas_bound
#print axioms distinct
#print axioms deterministic
#print axioms prepend
#print axioms contains_site
#print axioms extracted_bound
end Eip8282.Audit.Integrator.FrameEvents
