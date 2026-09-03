import Eip8282.Audit.EntryReach.Operands
import Eip8282.Audit.XiTransport

/-!
# ENDPOINT — concrete return bytes at reached endpoints

This slice turns the named bytes at an ENTRY-REACH `RETURN` into the model's
byte encoding where the endpoint is a fee getter.  It is observation-only:
the committed state and the drain-record encoding remain separate endpoint
obligations.
-/

namespace Eip8282.Audit.EntryReach.Endpoint

open EvmYul EvmYul.EVM
open Eip8282.Audit.XiTransport
open Eip8282.Audit.Model
open Eip8282.Audit.EntryReach.Deposit

/-- A getter's real `MSTORE 0 fee; RETURN 0 32` publishes the model's
32-byte big-endian fee word. -/
theorem getter_mstore_bytes (mem : ByteArray) (fee : UInt256) :
    bytes ((mstoreMem mem (UInt256.ofNat 0) fee).readWithPadding 0 32) =
      toBeBytes fee.toNat 32 := by
  unfold mstoreMem
  change bytes ((ByteArray.write fee.toByteArray 0 mem 0 32).readWithPadding 0 32) = _
  rw [ByteArray.readWithPadding_write_self_of_pad _ _ _ _ (by norm_num) (by norm_num)
    (EvmYul.UInt256.size_toByteArray fee) (by simp)]
  exact bytes_toByteArray fee

/-- An inhibited deposit call reaches the same empty-data revert observation as
the model.  Unlike the fee endpoints, this branch needs no fee-loop premise. -/
theorem deposit_inhibited_observes_model (c : XiCall .deposit) {s : Model.State}
    {caller : Address} {calldata : List Byte} {value : Wei}
    (hw : Eip8282.Audit.EntryReach.Deposit.UserWords c s calldata value)
    (hinh : excessWord c = INH) (hg : 2200 ≤ c.gas.toNat) (hf : 17 ≤ c.fuel) :
    observe c.result = some (observeModel (Model.step s (.user caller calldata value))) := by
  have hmodel : inhibited s = true :=
    (Eip8282.Audit.EntryReach.Deposit.inhibited_iff_word c hw).mp hinh
  obtain ⟨_, _, hend⟩ := Eip8282.Audit.EntryReach.Deposit.user_inhibited c hw.user hinh hg
  rw [Eip8282.Audit.EntryReach.observe_of_ends hend
    Eip8282.Audit.EntryReach.halting_REVERT (by omega)]
  simp [exitObservation, observeModel, Model.step, Model.userCall, hmodel,
    bytes_readWithPadding_zero]

/-- An inhibited exit call reaches the same empty-data revert observation as
the model. -/
theorem exit_inhibited_observes_model (c : XiCall .exit) {s : Model.State}
    {caller : Address} {calldata : List Byte} {value : Wei}
    (hw : Eip8282.Audit.EntryReach.Exit.UserWords c s caller calldata value)
    (hinh : Eip8282.Audit.EntryReach.Exit.excessWord c = INH)
    (hg : 2200 ≤ c.gas.toNat) (hf : 17 ≤ c.fuel) :
    observe c.result = some (observeModel (Model.step s (.user caller calldata value))) := by
  have hmodel : inhibited s = true :=
    (Eip8282.Audit.EntryReach.Exit.inhibited_iff_word c hw).mp hinh
  obtain ⟨_, _, hend⟩ := Eip8282.Audit.EntryReach.Exit.user_inhibited c hw.user hinh hg
  rw [Eip8282.Audit.EntryReach.observe_of_ends hend
    Eip8282.Audit.EntryReach.halting_REVERT (by omega)]
  simp [exitObservation, observeModel, Model.step, Model.userCall, hmodel,
    bytes_readWithPadding_zero]

/-- An enabled deposit getter carrying wei reverts with the model's empty-data
revert observation. -/
theorem deposit_paidGetter_observes_model (c : XiCall .deposit) {s : Model.State}
    {caller : Address} {calldata : List Byte} {value : Wei}
    (hw : Eip8282.Audit.EntryReach.Deposit.UserWords c s calldata value)
    (hen : excessWord c ≠ INH) {n : Nat} {o' i' : UInt256}
    (hfee : FeeLoopEnds c n o' i') (hsize : cdsizeWord c = ⟨0⟩)
    (hval : valueWord c ≠ ⟨0⟩) (hg : 87 * n + 4500 ≤ c.gas.toNat)
    (hf : 24 * n + 72 ≤ c.fuel) :
    observe c.result = some (observeModel (Model.step s (.user caller calldata value))) := by
  have hlen : calldata.length = 0 := by
    rw [eq_zero_iff_toNat] at hsize
    rw [hw.size] at hsize
    exact hsize
  have hnil : calldata = [] := List.eq_nil_of_length_eq_zero hlen
  have hnonzero : value ≠ 0 := by
    intro hzero
    apply hval
    rw [eq_zero_iff_toNat, hw.value, hzero]
  have hinh : inhibited s = false := by
    apply Bool.eq_false_of_not_eq_true
    intro h
    exact hen ((Eip8282.Audit.EntryReach.Deposit.inhibited_iff_word c hw).mpr h)
  obtain ⟨_, _, hend⟩ := Eip8282.Audit.EntryReach.Deposit.user_paidGetter_reverts c
    hw.user hen hfee hsize hval hg
  rw [Eip8282.Audit.EntryReach.observe_of_ends hend
    Eip8282.Audit.EntryReach.halting_REVERT (by omega)]
  simp [exitObservation, observeModel, Model.step, Model.userCall, hinh, hnil, hnonzero,
    bytes_readWithPadding_zero]

/-- An enabled EIP-7002 getter carrying wei reverts with the model's empty-data
revert observation. -/
theorem exit_paidGetter_observes_model (c : XiCall .exit) {s : Model.State}
    {caller : Address} {calldata : List Byte} {value : Wei}
    (hw : Eip8282.Audit.EntryReach.Exit.UserWords c s caller calldata value)
    (hen : Eip8282.Audit.EntryReach.Exit.excessWord c ≠ INH) {n : Nat} {o' i' : UInt256}
    (hfee : Eip8282.Audit.EntryReach.Exit.FeeLoopEnds c n o' i')
    (hsize : Eip8282.Audit.EntryReach.Exit.cdsizeWord c = ⟨0⟩)
    (hval : Eip8282.Audit.EntryReach.Exit.valueWord c ≠ ⟨0⟩)
    (hg : 87 * n + 4500 ≤ c.gas.toNat) (hf : 24 * n + 72 ≤ c.fuel) :
    observe c.result = some (observeModel (Model.step s (.user caller calldata value))) := by
  have hlen : calldata.length = 0 := by
    rw [Eip8282.Audit.EntryReach.eq_zero_iff_toNat] at hsize
    rw [hw.size] at hsize
    exact hsize
  have hnil : calldata = [] := List.eq_nil_of_length_eq_zero hlen
  have hnonzero : value ≠ 0 := by
    intro hzero
    apply hval
    rw [Eip8282.Audit.EntryReach.eq_zero_iff_toNat, hw.value, hzero]
  have hinh : inhibited s = false := by
    apply Bool.eq_false_of_not_eq_true
    intro h
    exact hen ((Eip8282.Audit.EntryReach.Exit.inhibited_iff_word c hw).mpr h)
  obtain ⟨_, _, hend⟩ := Eip8282.Audit.EntryReach.Exit.user_paidGetter_reverts c
    hw.user hen hfee hsize hval hg
  rw [Eip8282.Audit.EntryReach.observe_of_ends hend
    Eip8282.Audit.EntryReach.halting_REVERT (by omega)]
  simp [exitObservation, observeModel, Model.step, Model.userCall, hinh, hnil, hnonzero,
    bytes_readWithPadding_zero]

/-- A nonempty deposit call whose calldata length is neither the submit width
nor zero reaches the model's empty-data rejection observation. -/
theorem deposit_badsize_observes_model (c : XiCall .deposit) {s : Model.State}
    {caller : Address} {calldata : List Byte} {value : Wei}
    (hw : Eip8282.Audit.EntryReach.Deposit.UserWords c s calldata value)
    (hen : excessWord c ≠ INH) {n : Nat} {o' i' : UInt256}
    (hfee : FeeLoopEnds c n o' i') (hsize : cdsizeWord c ≠ UInt256.ofNat 184)
    (hzero : cdsizeWord c ≠ ⟨0⟩) (hg : 87 * n + 4500 ≤ c.gas.toNat)
    (hf : 24 * n + 72 ≤ c.fuel) :
    observe c.result = some (observeModel (Model.step s (.user caller calldata value))) := by
  have hlen : calldata.length ≠ 184 := by
    intro h
    apply hsize
    rw [eq_ofNat_iff_toNat _ _ (by rw [size_eq]; decide), hw.size]
    exact h
  have hnonempty : calldata ≠ [] := by
    intro hnil
    apply hzero
    rw [eq_zero_iff_toNat, hw.size, hnil]
    simp
  have hinh : inhibited s = false := by
    apply Bool.eq_false_of_not_eq_true
    intro h
    exact hen ((Eip8282.Audit.EntryReach.Deposit.inhibited_iff_word c hw).mpr h)
  have hadm : admissible s calldata value = false := by
    apply Bool.eq_false_of_not_eq_true
    intro h
    exact hlen ((Eip8282.Audit.EntryReach.Deposit.admissible_iff c hw hinh).mp h).1
  obtain ⟨_, _, hend⟩ := Eip8282.Audit.EntryReach.Deposit.user_badsize_reverts c
    hw.user hen hfee hsize hzero hg
  rw [Eip8282.Audit.EntryReach.observe_of_ends hend
    Eip8282.Audit.EntryReach.halting_REVERT (by omega)]
  simp [exitObservation, observeModel, Model.step, Model.userCall, hinh, hnonempty, hadm,
    bytes_readWithPadding_zero]

/-- A nonempty EIP-7002 call whose calldata length is neither the request width
nor zero reaches the model's empty-data rejection observation. -/
theorem exit_badsize_observes_model (c : XiCall .exit) {s : Model.State}
    {caller : Address} {calldata : List Byte} {value : Wei}
    (hw : Eip8282.Audit.EntryReach.Exit.UserWords c s caller calldata value)
    (hen : Eip8282.Audit.EntryReach.Exit.excessWord c ≠ INH) {n : Nat} {o' i' : UInt256}
    (hfee : Eip8282.Audit.EntryReach.Exit.FeeLoopEnds c n o' i')
    (hsize : Eip8282.Audit.EntryReach.Exit.cdsizeWord c ≠ UInt256.ofNat 48)
    (hzero : Eip8282.Audit.EntryReach.Exit.cdsizeWord c ≠ ⟨0⟩)
    (hg : 87 * n + 4500 ≤ c.gas.toNat) (hf : 24 * n + 72 ≤ c.fuel) :
    observe c.result = some (observeModel (Model.step s (.user caller calldata value))) := by
  have hlen : calldata.length ≠ 48 := by
    intro h
    apply hsize
    rw [Eip8282.Audit.EntryReach.eq_ofNat_iff_toNat _ _ (by rw [size_eq]; decide), hw.size]
    exact h
  have hnonempty : calldata ≠ [] := by
    intro hnil
    apply hzero
    rw [Eip8282.Audit.EntryReach.eq_zero_iff_toNat, hw.size, hnil]
    simp
  have hinh : inhibited s = false := by
    apply Bool.eq_false_of_not_eq_true
    intro h
    exact hen ((Eip8282.Audit.EntryReach.Exit.inhibited_iff_word c hw).mpr h)
  have hadm : admissible s calldata value = false := by
    apply Bool.eq_false_of_not_eq_true
    intro h
    exact hlen ((Eip8282.Audit.EntryReach.Exit.admissible_iff c hw hinh).mp h).1
  obtain ⟨_, _, hend⟩ := Eip8282.Audit.EntryReach.Exit.user_badsize_reverts c
    hw.user hen hfee hsize hzero hg
  rw [Eip8282.Audit.EntryReach.observe_of_ends hend
    Eip8282.Audit.EntryReach.halting_REVERT (by omega)]
  simp [exitObservation, observeModel, Model.step, Model.userCall, hinh, hnonempty, hadm,
    bytes_readWithPadding_zero]

/-- An underpaid deposit submission reaches the model's empty-data rejection
observation. -/
theorem deposit_underpay_observes_model (c : XiCall .deposit) {s : Model.State}
    {caller : Address} {calldata : List Byte} {value : Wei}
    (hw : Eip8282.Audit.EntryReach.Deposit.UserWords c s calldata value)
    (hen : excessWord c ≠ INH) {n : Nat} {o' i' : UInt256}
    (hfee : FeeLoopEnds c n o' i') (hquote : (feeWord o').toNat = currentFee s)
    (hsize : cdsizeWord c = UInt256.ofNat 184) (hlt : valueWord c < feeWord o')
    (hg : 87 * n + 4500 ≤ c.gas.toNat) (hf : 24 * n + 82 ≤ c.fuel) :
    observe c.result = some (observeModel (Model.step s (.user caller calldata value))) := by
  have hlen : calldata.length = 184 := by
    rw [eq_ofNat_iff_toNat _ _ (by rw [size_eq]; decide), hw.size] at hsize
    exact hsize
  have hunder : value < currentFee s := by
    rw [← hw.value, ← hquote]
    exact (Eip8282.Audit.EntryReach.lt_iff_toNat _ _).mp hlt
  have hnonempty : calldata ≠ [] := by
    intro hnil
    rw [hnil] at hlen
    norm_num at hlen
  have hinh : inhibited s = false := by
    apply Bool.eq_false_of_not_eq_true
    intro h
    exact hen ((Eip8282.Audit.EntryReach.Deposit.inhibited_iff_word c hw).mpr h)
  have hadm : admissible s calldata value = false := by
    apply Bool.eq_false_of_not_eq_true
    intro h
    obtain ⟨_, _, hpaid⟩ := (Eip8282.Audit.EntryReach.Deposit.admissible_iff c hw hinh).mp h
    exact (not_le_of_gt hunder)
      (Nat.le_trans (Nat.le_add_left _ _) hpaid)
  obtain ⟨_, _, hend⟩ := Eip8282.Audit.EntryReach.Deposit.user_underpay_reverts c
    hw.user hen hfee hsize hlt hg
  rw [Eip8282.Audit.EntryReach.observe_of_ends hend
    Eip8282.Audit.EntryReach.halting_REVERT (by omega)]
  simp [exitObservation, observeModel, Model.step, Model.userCall, hinh, hnonempty, hadm,
    bytes_readWithPadding_zero]

/-- An underpaid EIP-7002 request reaches the model's empty-data rejection
observation. -/
theorem exit_underpay_observes_model (c : XiCall .exit) {s : Model.State}
    {caller : Address} {calldata : List Byte} {value : Wei}
    (hw : Eip8282.Audit.EntryReach.Exit.UserWords c s caller calldata value)
    (hen : Eip8282.Audit.EntryReach.Exit.excessWord c ≠ INH) {n : Nat} {o' i' : UInt256}
    (hfee : Eip8282.Audit.EntryReach.Exit.FeeLoopEnds c n o' i')
    (hquote : (Eip8282.Audit.EntryReach.Exit.feeWord o').toNat = currentFee s)
    (hsize : Eip8282.Audit.EntryReach.Exit.cdsizeWord c = UInt256.ofNat 48)
    (hlt : Eip8282.Audit.EntryReach.Exit.valueWord c < Eip8282.Audit.EntryReach.Exit.feeWord o')
    (hg : 87 * n + 4500 ≤ c.gas.toNat) (hf : 24 * n + 82 ≤ c.fuel) :
    observe c.result = some (observeModel (Model.step s (.user caller calldata value))) := by
  have hlen : calldata.length = 48 := by
    rw [Eip8282.Audit.EntryReach.eq_ofNat_iff_toNat _ _ (by rw [size_eq]; decide), hw.size] at hsize
    exact hsize
  have hunder : value < currentFee s := by
    rw [← hw.value, ← hquote]
    exact (Eip8282.Audit.EntryReach.lt_iff_toNat _ _).mp hlt
  have hnonempty : calldata ≠ [] := by
    intro hnil
    rw [hnil] at hlen
    norm_num at hlen
  have hinh : inhibited s = false := by
    apply Bool.eq_false_of_not_eq_true
    intro h
    exact hen ((Eip8282.Audit.EntryReach.Exit.inhibited_iff_word c hw).mpr h)
  have hadm : admissible s calldata value = false := by
    apply Bool.eq_false_of_not_eq_true
    intro h
    exact (not_le_of_gt hunder)
      ((Eip8282.Audit.EntryReach.Exit.admissible_iff c hw hinh).mp h).2
  obtain ⟨_, _, hend⟩ := Eip8282.Audit.EntryReach.Exit.user_underpay_reverts c
    hw.user hen hfee hsize hlt hg
  rw [Eip8282.Audit.EntryReach.observe_of_ends hend
    Eip8282.Audit.EntryReach.halting_REVERT (by omega)]
  simp [exitObservation, observeModel, Model.step, Model.userCall, hinh, hnonempty, hadm,
    bytes_readWithPadding_zero]

/-- A deposit submission below the amount floor reaches the model's empty-data
rejection observation. -/
theorem deposit_amountFloor_observes_model (c : XiCall .deposit) {s : Model.State}
    {caller : Address} {calldata : List Byte} {value : Wei}
    (hw : Eip8282.Audit.EntryReach.Deposit.UserWords c s calldata value)
    (hen : excessWord c ≠ INH) {n : Nat} {o' i' : UInt256}
    (hfee : FeeLoopEnds c n o' i') (hsize : cdsizeWord c = UInt256.ofNat 184)
    (hpaid : ¬ valueWord c < feeWord o')
    (hfloor : amountWord c < UInt256.ofNat 1000000000)
    (hg : 87 * n + 4600 ≤ c.gas.toNat) (hf : 24 * n + 92 ≤ c.fuel) :
    observe c.result = some (observeModel (Model.step s (.user caller calldata value))) := by
  have hlen : calldata.length = 184 := by
    rw [eq_ofNat_iff_toNat _ _ (by rw [size_eq]; decide), hw.size] at hsize
    exact hsize
  have hamount : (amountWord c).toNat = depositAmount calldata := hw.amount hlen
  have hfloorNat : depositAmount calldata < 1000000000 := by
    rw [← hamount]
    exact (Eip8282.Audit.EntryReach.lt_iff_toNat _ _).mp hfloor
  have hnonempty : calldata ≠ [] := by
    intro hnil
    rw [hnil] at hlen
    norm_num at hlen
  have hinh : inhibited s = false := by
    apply Bool.eq_false_of_not_eq_true
    intro h
    exact hen ((Eip8282.Audit.EntryReach.Deposit.inhibited_iff_word c hw).mpr h)
  have hadm : admissible s calldata value = false := by
    apply Bool.eq_false_of_not_eq_true
    intro h
    obtain ⟨_, hmin, _⟩ := (Eip8282.Audit.EntryReach.Deposit.admissible_iff c hw hinh).mp h
    exact (not_le_of_gt hfloorNat) hmin
  obtain ⟨_, _, hend⟩ := Eip8282.Audit.EntryReach.Deposit.user_amountFloor_reverts c
    hw.user hen hfee hsize hpaid hfloor hg
  rw [Eip8282.Audit.EntryReach.observe_of_ends hend
    Eip8282.Audit.EntryReach.halting_REVERT (by omega)]
  simp [exitObservation, observeModel, Model.step, Model.userCall, hinh, hnonempty, hadm,
    bytes_readWithPadding_zero]

/-- The reached, enabled, zero-value getter endpoint has the model's exact
observation.  This is the `ExitAgrees` observation half for this endpoint;
the common post-state relation is deliberately not asserted here. -/
theorem deposit_getter_observes_model (c : XiCall .deposit) {s : Model.State}
    {caller : Address} {calldata : List Byte} {value : Wei}
    (hw : Eip8282.Audit.EntryReach.Deposit.UserWords c s calldata value)
    (hen : excessWord c ≠ INH) {n : Nat} {o' i' : UInt256}
    (hfee : FeeLoopEnds c n o' i') (hquote : (feeWord o').toNat = currentFee s)
    (hsize : cdsizeWord c = ⟨0⟩) (hval : valueWord c = ⟨0⟩)
    (hg : 87 * n + 4500 ≤ c.gas.toNat) (hf : 24 * n + 82 ≤ c.fuel) :
    observe c.result = some (observeModel (Model.step s (.user caller calldata value))) := by
  have hlen : calldata.length = 0 := by
    rw [eq_zero_iff_toNat] at hsize
    rw [hw.size] at hsize
    exact hsize
  have hnil : calldata = [] := List.eq_nil_of_length_eq_zero hlen
  have hzero : value = 0 := by
    rw [eq_zero_iff_toNat] at hval
    rw [hw.value] at hval
    exact hval
  have hinh : inhibited s = false := by
    apply Bool.eq_false_of_not_eq_true
    intro h
    exact hen ((Eip8282.Audit.EntryReach.Deposit.inhibited_iff_word c hw).mpr h)
  rw [Eip8282.Audit.EntryReach.Deposit.observe_getter c hw.user hen hfee hsize hval hg hf]
  rw [show exitObservation (.RETURN : Operation .EVM)
      ((mstoreMem (mem₀ c) (UInt256.ofNat 0) (feeWord o')).readWithPadding 0 32) =
        { reverted := false
          returnData := bytes ((mstoreMem (mem₀ c) (UInt256.ofNat 0) (feeWord o')).readWithPadding 0 32) } by
    simp [exitObservation]]
  simp only [Option.some.injEq]
  rw [getter_mstore_bytes, hquote]
  simp [observeModel, Model.step, Model.userCall, hinh, hnil, hzero]

/-- The analogous EIP-7002 getter endpoint has the model's exact observation. -/
theorem exit_getter_observes_model (c : XiCall .exit) {s : Model.State}
    {caller : Address} {calldata : List Byte} {value : Wei}
    (hw : Eip8282.Audit.EntryReach.Exit.UserWords c s caller calldata value)
    (hen : Eip8282.Audit.EntryReach.Exit.excessWord c ≠ INH) {n : Nat} {o' i' : UInt256}
    (hfee : Eip8282.Audit.EntryReach.Exit.FeeLoopEnds c n o' i')
    (hquote : (Eip8282.Audit.EntryReach.Exit.feeWord o').toNat = currentFee s)
    (hsize : Eip8282.Audit.EntryReach.Exit.cdsizeWord c = ⟨0⟩)
    (hval : Eip8282.Audit.EntryReach.Exit.valueWord c = ⟨0⟩)
    (hg : 87 * n + 4500 ≤ c.gas.toNat) (hf : 24 * n + 82 ≤ c.fuel) :
    observe c.result = some (observeModel (Model.step s (.user caller calldata value))) := by
  have hlen : calldata.length = 0 := by
    rw [Eip8282.Audit.EntryReach.eq_zero_iff_toNat] at hsize
    rw [hw.size] at hsize
    exact hsize
  have hnil : calldata = [] := List.eq_nil_of_length_eq_zero hlen
  have hzero : value = 0 := by
    rw [Eip8282.Audit.EntryReach.eq_zero_iff_toNat] at hval
    rw [hw.value] at hval
    exact hval
  have hinh : inhibited s = false := by
    apply Bool.eq_false_of_not_eq_true
    intro h
    exact hen ((Eip8282.Audit.EntryReach.Exit.inhibited_iff_word c hw).mpr h)
  rw [Eip8282.Audit.EntryReach.Exit.observe_getter c hw.user hen hfee hsize hval hg hf]
  rw [show exitObservation (.RETURN : Operation .EVM)
      ((mstoreMem (Eip8282.Audit.EntryReach.Exit.mem₀ c) (UInt256.ofNat 0)
        (Eip8282.Audit.EntryReach.Exit.feeWord o')).readWithPadding 0 32) =
        { reverted := false
          returnData := bytes ((mstoreMem (Eip8282.Audit.EntryReach.Exit.mem₀ c) (UInt256.ofNat 0)
            (Eip8282.Audit.EntryReach.Exit.feeWord o')).readWithPadding 0 32) } by
    simp [exitObservation]]
  simp only [Option.some.injEq]
  rw [getter_mstore_bytes, hquote]
  simp [observeModel, Model.step, Model.userCall, hinh, hnil, hzero]

end Eip8282.Audit.EntryReach.Endpoint
