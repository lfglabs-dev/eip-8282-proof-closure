import Eip8282.Audit.Integrator.ReferenceMeterMetadata

/-! Derived gas-settlement validity for each real full-frame outcome. The
finite checked trace, terminal charge and partial-fault metadata are the same
computation. Freshness constrains the initial transaction journal; returned
pools, net state usage and refund conversion are conclusions. Consumer: the
exhaustive full-gas allocated transaction theorem. -/
namespace Eip8282.Audit.Integrator.ReferenceOutcomeGas
open EvmYul EvmYul.EVM
open ReferenceRuntimeView ReferenceSourceReadings ReferenceMeterRollback ReferenceMeterBoundary ReferenceCheckedDispatch
open ReferenceMeterPath
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

structure Valid (txGas grant : Nat) (m : Meter) : Prop where
  baseline : m.baseline ≤ grant
  returned : m.execution+m.reservoir ≤ txGas
  state : ReferenceTransactionGas.settledState (netUsed grant m) ≤ txGas-m.execution-m.reservoir
  refund_nonnegative : 0 ≤ m.refund
  refund_fits : m.refund < UInt256.size

theorem paid_valid {kind : Eip8282.Audit.Model.Kind} {p : ReferenceStorageView.Parent}
    {v finish : View} {w fw : Warm} {middle final : Meter} {events : List Event} {amount txGas intrinsic : Nat}
    (actual : ReferenceCheckedRuntimeTrace.Run kind p v w (ReferenceTransactionWork.initial txGas intrinsic) finish fw middle events)
    (stack : v.stack.length ≤ 1024) (aligned : ReferenceActionMemoryBounds.Aligned v)
    (fresh : v.storage = ReferenceRuntimeStateBalance.emptyTx)
    (terminal : runFull [.ordinary amount] middle = some final)
    (affords : intrinsic ≤ txGas) (maximum : intrinsic ≤ 16777216) :
    Valid txGas (ReferenceTransactionGas.allocate txGas intrinsic).reservoir final ∧
    Valid txGas (ReferenceTransactionGas.allocate txGas intrinsic).reservoir (restore final) := by
  have guards := ReferenceCheckedStateGas.fresh_guards actual stack aligned fresh terminal affords maximum
  have refund := ReferenceRefundCounter.fresh_terminal actual stack aligned fresh terminal
  constructor
  · exact ⟨by omega,guards.1,guards.2.2.1,refund.1,refund.2.1⟩
  · have prefixPaid := (actual.extract stack aligned).2.1
    have whole : runFull (events++[.ordinary amount]) (ReferenceTransactionWork.initial txGas intrinsic) = some final := by
      rw [ReferenceCheckedRuntimeTrace.runFull_append,prefixPaid,Option.bind_some,terminal]
    have rollback := ReferenceMeterBoundary.rollback_accounting whole (ReferenceTransactionGas.allocate txGas intrinsic).reservoir rfl rfl
    have allocation := ReferenceTransactionGas.allocation txGas intrinsic affords maximum
    have used := ReferenceExecutionLedger.work_cast (events++[.ordinary amount])
    have metadata := (ReferenceMeterBoundary.accounting whole (ReferenceTransactionGas.allocate txGas intrinsic).reservoir).2.2
    have netZero : netUsed (ReferenceTransactionGas.allocate txGas intrinsic).reservoir (restore final) = 0 := by
      simpa [ReferenceTransactionWork.initial,ReferenceChildMeter.init,netUsed] using rollback.1
    refine ⟨by change final.baseline ≤ _; omega,?_,?_,by simp [restore],?_⟩
    · simp only [pools,ReferenceTransactionWork.initial,ReferenceChildMeter.init,restore] at rollback
      simp only [restore]
      omega
    · simp [netZero,ReferenceTransactionGas.settledState]
    · change (0 : Int) < UInt256.size
      decide +kernel

private theorem execution_payment {m : Meter} {charged : ReferenceStorageGas.Meter} {amount : Nat}
    (paid : ReferenceStorageGas.chargeExecution (core m) amount = some charged) :
    runFull [.ordinary amount] m = some (update m charged) := by
  simp only [runFull,ReferenceMeterPath.run,pay,paid,Option.bind_some,Option.map_some]

private theorem terminal_payment {h : ReferenceCheckedTerminalStep.Halt} {v : View} {m : Meter} {o : ByteArray} {result : ReferenceCheckedTerminalStep.End}
    (actual : ReferenceCheckedTerminalStep.run h v m o = .ok result) :
    ∃ amount, runFull [.ordinary amount] m = some result.meter := by
  unfold ReferenceCheckedTerminalStep.run at actual
  split at actual
  · cases actual
    exact ⟨0,by simp [runFull,ReferenceMeterPath.run,pay,ReferenceStorageGas.chargeExecution,core,update]⟩
  · split at actual
    · contradiction
    · split at actual
      · contradiction
      · split at actual
        · contradiction
        · rename_i charged paid
          cases actual
          exact ⟨_,execution_payment paid⟩

/-- The existing exact terminal-payment producer is also consumed by the
SYSTEM output conversion proof; SYSTEM does not use transaction allocation. -/
theorem terminal_paid {h : ReferenceCheckedTerminalStep.Halt} {v : View} {m : Meter} {o : ByteArray} {result : ReferenceCheckedTerminalStep.End}
    (actual : ReferenceCheckedTerminalStep.run h v m o = .ok result) :
    ∃ amount, runFull [.ordinary amount] m = some result.meter := terminal_payment actual

theorem terminal {kind : Eip8282.Audit.Model.Kind} {p : ReferenceStorageView.Parent}
    {v finish : View} {w fw : Warm} {middle : Meter} {events : List Event} {txGas intrinsic : Nat}
    (actual : ReferenceCheckedRuntimeTrace.Run kind p v w (ReferenceTransactionWork.initial txGas intrinsic) finish fw middle events)
    (stack : v.stack.length ≤ 1024) (aligned : ReferenceActionMemoryBounds.Aligned v)
    (fresh : v.storage = ReferenceRuntimeStateBalance.emptyTx)
    {d : List Nat} {owner : Bool} {o : ByteArray} {result : ReferenceCheckedTerminalStep.End}
    (last : ReferenceCheckedDispatch.run d owner p finish fw middle o = .terminal result)
    (snapshot : ReferenceStorageView.Tx) (affords : intrinsic ≤ txGas) (maximum : intrinsic ≤ 16777216) :
    ∃ receipt, ReferenceCheckedFrameOutcome.settle snapshot [] fw (.terminal result) = .returned receipt ∧
      Valid txGas (ReferenceTransactionGas.allocate txGas intrinsic).reservoir receipt.meter := by
  obtain ⟨_,handler,_⟩ := ReferenceCheckedDispatchTerminal.terminal last
  obtain ⟨amount,paid⟩ := terminal_payment handler
  have valid := paid_valid actual stack aligned fresh paid affords maximum
  by_cases reverted : result.halt = .reverted
  · refine ⟨ReferenceCheckedFrameOutcome.failure snapshot result.view fw (restore result.meter) result.output .reverted,?_,valid.2⟩
    simp only [ReferenceCheckedFrameOutcome.settle,reverted,if_true,ReferenceChildMeter.settle]
  · refine ⟨ReferenceCheckedFrameOutcome.success [] result.view fw result.meter result.output,?_,valid.1⟩
    simp only [ReferenceCheckedFrameOutcome.settle,if_neg reverted]

theorem eof {kind : Eip8282.Audit.Model.Kind} {p : ReferenceStorageView.Parent}
    {v finish : View} {w fw : Warm} {middle : Meter} {events : List Event} {txGas intrinsic : Nat}
    (actual : ReferenceCheckedRuntimeTrace.Run kind p v w (ReferenceTransactionWork.initial txGas intrinsic) finish fw middle events)
    (stack : v.stack.length ≤ 1024) (aligned : ReferenceActionMemoryBounds.Aligned v)
    (fresh : v.storage = ReferenceRuntimeStateBalance.emptyTx)
    {d : List Nat} {owner : Bool} {o output : ByteArray} {post : View} {postWarm : Warm} {postMeter : Meter}
    (last : ReferenceCheckedDispatch.run d owner p finish fw middle o = .eof post postWarm postMeter output)
    (snapshot : ReferenceStorageView.Tx) (affords : intrinsic ≤ txGas) (maximum : intrinsic ≤ 16777216) :
    ∃ receipt, ReferenceCheckedFrameOutcome.settle snapshot [] fw (.eof post postWarm postMeter output) = .returned receipt ∧
      Valid txGas (ReferenceTransactionGas.allocate txGas intrinsic).reservoir receipt.meter := by
  have same := ReferenceCheckedEOF.fields last
  have paid : runFull [.ordinary 0] middle = some middle := by simp [runFull,ReferenceMeterPath.run,pay,ReferenceStorageGas.chargeExecution,core,update]
  refine ⟨ReferenceCheckedFrameOutcome.success [] post postWarm postMeter output,rfl,?_⟩
  change Valid _ _ postMeter
  rw [←same.2.2.1]
  exact (paid_valid actual stack aligned fresh paid affords maximum).1

theorem failed {kind : Eip8282.Audit.Model.Kind} {p : ReferenceStorageView.Parent}
    {v finish : View} {w fw : Warm} {middle : Meter} {events : List Event} {txGas intrinsic : Nat}
    (actual : ReferenceCheckedRuntimeTrace.Run kind p v w (ReferenceTransactionWork.initial txGas intrinsic) finish fw middle events)
    (stack : v.stack.length ≤ 1024) (aligned : ReferenceActionMemoryBounds.Aligned v)
    {d : List Nat} {owner : Bool} {o output : ByteArray} {post : View} {postWarm : Warm} {postMeter : Meter} {fault : Fault}
    (last : ReferenceCheckedDispatch.run d owner p finish fw middle o = .failed fault post postWarm postMeter output)
    (caught : ReferenceCheckedFaultClass.caught fault = true)
    (snapshot : ReferenceStorageView.Tx) (affords : intrinsic ≤ txGas) (maximum : intrinsic ≤ 16777216) :
    ∃ receipt, ReferenceCheckedFrameOutcome.settle snapshot [] fw (.failed fault post postWarm postMeter output) = .returned receipt ∧
      Valid txGas (ReferenceTransactionGas.allocate txGas intrinsic).reservoir receipt.meter := by
  have paid := (actual.extract stack aligned).2.1
  have prefixFields := (ReferenceMeterBoundary.accounting paid (ReferenceTransactionGas.allocate txGas intrinsic).reservoir).2.2
  have lastFields := ReferenceMeterMetadata.dispatch d owner p finish fw middle o
  rw [last] at lastFields
  have baseline : postMeter.baseline = (ReferenceTransactionGas.allocate txGas intrinsic).reservoir := lastFields.1.trans prefixFields.1
  have committed : postMeter.committedSpill = 0 := lastFields.2.trans prefixFields.2
  have allocation := ReferenceTransactionGas.allocation txGas intrinsic affords maximum
  refine ⟨ReferenceCheckedFrameOutcome.failure snapshot post postWarm (ReferenceChildMeter.settle .exceptional postMeter) ByteArray.empty (.exceptional fault),by simp only [ReferenceCheckedFrameOutcome.settle,caught,if_true],?_⟩
  refine ⟨by simp [ReferenceCheckedFrameOutcome.failure,ReferenceChildMeter.settle,restore,baseline],?_,?_,?_,?_⟩
  · simp only [ReferenceCheckedFrameOutcome.failure,ReferenceChildMeter.settle,restore,baseline,Nat.zero_add]
    omega
  · simp [ReferenceCheckedFrameOutcome.failure,ReferenceChildMeter.settle,restore,netUsed,baseline,committed,ReferenceTransactionGas.settledState]
  · simp [ReferenceCheckedFrameOutcome.failure,ReferenceChildMeter.settle,restore]
  · change (0 : Int) < UInt256.size
    decide +kernel

#print axioms paid_valid
#print axioms terminal
#print axioms eof
#print axioms failed
end Eip8282.Audit.Integrator.ReferenceOutcomeGas
