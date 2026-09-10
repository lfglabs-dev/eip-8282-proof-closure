import Eip8282.Audit.Integrator.InitializerProgress
import Eip8282.Audit.Integrator.NestedEventArgs

/-! Actual entry prefix of the archived deterministic factory runtime.
Reference EL 0cc100eb190b64b23baba72dac0165652eaec252, EIP7997 mixin
and generator fixture salt||initcode. Exact code is an input binding, not a
consequence of the familiar address. No child success or canonical installation
is assumed or concluded by the prefix theorem. -/
namespace Eip8282.Audit.Integrator.FactoryRuntimeEntry
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.SymExec Eip8282.Audit.EntryReach
open Eip8282.Audit.XiTransport (XiCall)
open Eip8282.Audit.Model (Kind)
open Eip8282.Audit.Bytecode Eip8282.Audit.Jumpdests
open NestedEvents
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

def factoryAddress : AccountAddress := AccountAddress.ofNat 0x4e59b44847b379578588920ca78fbf26c0b4956c

def runtime : ByteArray := ⟨#[0x7f,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xe0,0x36,0x01,0x60,0x00,0x81,0x60,0x20,0x82,0x37,0x80,0x35,0x82,0x82,0x34,0xf5,0x80,0x15,0x15,0x60,0x39,0x57,0x81,0x82,0xfd,0x5b,0x80,0x82,0x52,0x50,0x50,0x50,0x60,0x14,0x60,0x0c,0xf3]⟩
def salt : Kind → UInt256
  | .deposit => UInt256.ofNat 0x1f4f2c41c28e816e259b621c58b94b37309c8dec42c8f6e400001a46c9d96bf7
  | .exit => UInt256.ofNat 0x89abb1878437213f971f849327423ed1d9c5cdb03970cd8f0000318b3ff10119

def saltData : Kind → ByteArray
  | .deposit => ⟨#[0x1f,0x4f,0x2c,0x41,0xc2,0x8e,0x81,0x6e,0x25,0x9b,0x62,0x1c,0x58,0xb9,0x4b,0x37,0x30,0x9c,0x8d,0xec,0x42,0xc8,0xf6,0xe4,0x00,0x00,0x1a,0x46,0xc9,0xd9,0x6b,0xf7]⟩
  | .exit => ⟨#[0x89,0xab,0xb1,0x87,0x84,0x37,0x21,0x3f,0x97,0x1f,0x84,0x93,0x27,0x42,0x3e,0xd1,0xd9,0xc5,0xcd,0xb0,0x39,0x70,0xcd,0x8f,0x00,0x00,0x31,0x8b,0x3f,0xf1,0x01,0x19]⟩

def calldata (kind : Kind) : ByteArray := saltData kind ++ Initialization.initCode kind

def initSize : Kind → Nat | .deposit => 638 | .exit => 503

theorem salt_encoding (kind : Kind) : (salt kind).toByteArray = saltData kind := by
  have h : Eip8282.Audit.XiTransport.bytes ((salt kind).toByteArray) =
      Eip8282.Audit.XiTransport.bytes (saltData kind) := by
    rw [Eip8282.Audit.XiTransport.bytes_toByteArray]
    cases kind <;> decide +kernel
  rw [Eip8282.Audit.XiTransport.bytes_eq_map_data,Eip8282.Audit.XiTransport.bytes_eq_map_data] at h
  apply ByteArray.ext
  apply Array.ext'
  exact (List.map_injective_iff.mpr (fun _ _ he => UInt8.toNat_inj.mp he)) h

theorem init_size (kind : Kind) : (Initialization.initCode kind).size = initSize kind := by
  cases kind <;> rfl

theorem data_size (kind : Kind) : (calldata kind).size = 32+initSize kind := by
  cases kind <;> rfl

private def template (a : XiArgs) : XiCall .deposit :=
  { fuel := 0, createdAccounts := a.created, genesisBlockHeader := a.genesis,
    blocks := a.blocks, σ := a.world, σ₀ := a.original, gas := a.gas,
    substate := a.substate, env := {a.env with code := depositRuntime}, code_pinned := rfl }

def machine (a : XiArgs) (mem : ByteArray) (aw gas : UInt256) (pc : Nat)
    (stack : Stack UInt256) (executed : Nat) : EVM.State :=
  at_ (template a) a.entry.toState mem aw gas pc stack executed

theorem entry_machine (a : XiArgs) : a.entry = machine a .empty ⟨0⟩ a.gas 0 [] 0 := rfl

def atCreate (kind : Kind) (a : XiArgs) (gas : UInt256) (executed : Nat) : EVM.State :=
  machine a (Initialization.initCode kind) (mAfter ⟨0⟩ 0 (initSize kind)) gas 47
    [a.env.weiValue,⟨0⟩,UInt256.ofNat (initSize kind),salt kind,⟨0⟩,UInt256.ofNat (initSize kind)] executed

private def negative32 : UInt256 := UInt256.ofNat (UInt256.size-32)
private def lengthWord (st : EvmYul.State .EVM) : UInt256 := cdsizeW st + negative32

private def beforeCopy : List Site :=
  [(0,(.PUSH32,some (negative32,32))), (33,(.CALLDATASIZE,none)), (34,(.ADD,none)),
   (35,(.PUSH1,some (⟨0⟩,1))), (37,(.DUP2,none)),
   (38,(.PUSH1,some (UInt256.ofNat 32,1))), (40,(.DUP3,none))]
private def afterCopy : List Site :=
  [(42,(.DUP1,none)),(43,(.CALLDATALOAD,none)),(44,(.DUP3,none)),(45,(.DUP3,none)),(46,(.CALLVALUE,none))]

private theorem before_sites : sitesOk runtime beforeCopy = true := by decide +kernel
private theorem after_sites : sitesOk runtime afterCopy = true := by decide +kernel
private theorem copy_site : opcodeAt runtime 41 = some (.CALLDATACOPY,none) := by decide +kernel
theorem create_site : opcodeAt runtime 47 = some (.CREATE2,none) := by decide +kernel

private theorem before_shape (a : XiArgs) (st : EvmYul.State .EVM) (gas : UInt256) (e : Nat) :
    symBlock [] (beforeCopy.map Prod.snd) (at_ (template a) st .empty ⟨0⟩ gas 0 [] e) =
      some (at_ (template a) st .empty ⟨0⟩ gas 41
        [⟨0⟩,UInt256.ofNat 32,lengthWord st,⟨0⟩,lengthWord st] e) := by rfl

private theorem after_shape (a : XiArgs) (st : EvmYul.State .EVM)
    (mem : ByteArray) (aw gas len : UInt256) (e : Nat) :
    symBlock [] (afterCopy.map Prod.snd) (at_ (template a) st mem aw gas 42 [⟨0⟩,len] e) =
      some (at_ (template a) st mem aw gas 47 [valueW st,⟨0⟩,len,cdW st ⟨0⟩,⟨0⟩,len] e) := by rfl

private theorem length_word (kind : Kind) (st : EvmYul.State .EVM)
    (hdata : st.executionEnv.calldata = calldata kind) :
    lengthWord st = UInt256.ofNat (initSize kind) := by
  simp only [lengthWord,cdsizeW,hdata]
  cases kind <;> decide +kernel

private theorem salt_load (kind : Kind) (st : EvmYul.State .EVM)
    (hdata : st.executionEnv.calldata = calldata kind) : cdW st ⟨0⟩ = salt kind := by
  unfold cdW EvmYul.State.calldataload
  rw [hdata]
  have he : (uInt256OfByteArray ((calldata kind).readBytes 0 32)).toNat = (salt kind).toNat := by
    rw [toNat_calldataload _ _ (by decide)]
    cases kind <;> decide +kernel
  change uInt256OfByteArray ((calldata kind).readBytes 0 32) = salt kind
  rw [← ofNat_toNat' (uInt256OfByteArray ((calldata kind).readBytes 0 32)), he, ofNat_toNat']

private theorem write_empty_slice (src : ByteArray) (off len : Nat)
    (hl : 0 < len) (hb : off+len ≤ src.size) :
    src.write off .empty 0 len = src.extract off (off+len) := by
  unfold ByteArray.write
  rw [if_neg (by omega),if_neg (by omega)]
  have hm : min len (src.size-off) = len := by omega
  simp only [hm,ByteArray.size_empty,Nat.zero_add,Nat.zero_min,Nat.zero_sub]
  have hz : ffi.ByteArray.zeroes (⟨((0 : Nat) : BitVec System.Platform.numBits)⟩ : USize) = .empty := rfl
  rw [hz]
  simp only [ByteArray.append_empty]
  unfold ByteArray.extract
  rw [Nat.add_sub_cancel_left]
  rfl

private theorem copied_init (kind : Kind) :
    (calldata kind).write 32 .empty 0 (initSize kind) = Initialization.initCode kind := by
  rw [write_empty_slice _ _ _ (by cases kind <;> decide) (by rw [data_size])]
  unfold calldata
  exact ByteArray.extract_append_eq_right (by cases kind <;> rfl)
    (by rw [init_size]; cases kind <;> rfl)

private def copyBudget (kind : Kind) : Nat :=
  memBound 20 + GasConstants.Gverylow + GasConstants.Gcopy*((initSize kind+31)/32)

/-- Thirteen accepted actual X instructions reach CREATE2 with the fixture's
full salt and initializer. The bound includes memory expansion and copying. -/
theorem reaches_create2 (kind : Kind) (a : XiArgs) (hcode : a.env.code = runtime)
    (hdata : a.env.calldata = calldata kind) (hgas : 200 ≤ a.gas.toNat) :
    ∃ gas executed, a.gas.toNat-157 ≤ gas.toNat ∧
      Reaches a.jumps 13 a.entry (atCreate kind a gas executed) := by
  have hc : a.entry.toState.executionEnv.code = runtime := hcode
  have hd : a.entry.toState.executionEnv.calldata = calldata kind := hdata
  obtain ⟨g₁,e₁,hg₁,first⟩ := reach_block (vj := a.jumps) (vjNats := []) (by simp)
    beforeCopy before_sites (c := template a) (st := a.entry.toState) hc rfl
    (by change 20 ≤ a.gas.toNat; omega) (by decide) (before_shape a a.entry.toState a.gas 0)
  rw [length_word kind _ hd] at first
  have hcopy : copyBudget kind ≤ g₁.toNat := by
    have hb : copyBudget kind ≤ 123 := by cases kind <;> decide
    change a.gas.toNat-20 ≤ g₁.toNat at hg₁
    omega
  obtain ⟨g₂,e₂,hg₂,middle⟩ := reach_calldatacopy (vj := a.jumps) (c := template a)
    (st := a.entry.toState) (mem := .empty) (aw := ⟨0⟩) (g := g₁)
    (dst := ⟨0⟩) (src := UInt256.ofNat 32) (len := UInt256.ofNat (initSize kind))
    (r := [⟨0⟩,UInt256.ofNat (initSize kind)]) (e := e₁) (B := 20)
    copy_site hc (by decide) (by cases kind <;> decide) (by decide)
    (M := copyBudget kind) (by cases kind <;> rfl) hcopy (by simp)
  have hm : cdcopyMem a.entry.toState .empty ⟨0⟩ (UInt256.ofNat 32)
      (UInt256.ofNat (initSize kind)) = Initialization.initCode kind := by
    unfold cdcopyMem
    change a.env.calldata.write 32 .empty 0 (UInt256.ofNat (initSize kind)).toNat = _
    rw [hdata]
    have hl : (UInt256.ofNat (initSize kind)).toNat = initSize kind := by cases kind <;> rfl
    rw [hl]
    exact copied_init kind
  have hl : (UInt256.ofNat (initSize kind)).toNat = initSize kind := by cases kind <;> rfl
  rw [hm,hl] at middle
  have hg₂' : 14 ≤ g₂.toNat := by
    have hb : copyBudget kind ≤ 123 := by cases kind <;> decide
    change a.gas.toNat-20 ≤ g₁.toNat at hg₁
    omega
  obtain ⟨g₃,e₃,hg₃,last⟩ := reach_block (vj := a.jumps) (vjNats := []) (by simp)
    afterCopy after_sites (c := template a) (st := a.entry.toState) hc rfl hg₂'
    (by simp [afterCopy]) (after_shape a a.entry.toState (Initialization.initCode kind)
      (mAfter ⟨0⟩ 0 (initSize kind)) g₂ (UInt256.ofNat (initSize kind)) e₂)
  rw [salt_load kind _ hd] at last
  refine ⟨g₃,e₃,?_,?_⟩
  · have hb : copyBudget kind ≤ 123 := by cases kind <;> decide
    change a.gas.toNat-20 ≤ g₁.toNat at hg₁
    change g₂.toNat-14 ≤ g₃.toNat at hg₃
    omega
  · rw [entry_machine]
    exact (first.trans middle).trans last


def createCost (kind : Kind) : Nat :=
  GasConstants.Gcreate + GasConstants.Gkeccak256word*((initSize kind+31)/32) + R (initSize kind)

private theorem create_memory (kind : Kind) (a : XiArgs) (gas : UInt256) (e : Nat) :
    memoryExpansionCost (atCreate kind a gas e) .CREATE2 = 0 := by
  cases kind <;> simp [memoryExpansionCost,memoryExpansionCost.μᵢ',atCreate,machine,at_,mAfter,MachineState.M,Cₘ,initSize] <;> decide +kernel

private theorem create_cost (kind : Kind) (a : XiArgs) (gas : UInt256) (e : Nat) :
    C' (atCreate kind a gas e) .CREATE2 = createCost kind := by
  cases kind <;> rfl

/-- CREATE2 itself is accepted, including the static-mode and init-size gates. -/
theorem create_guard (kind : Kind) (a : XiArgs) (gas : UInt256) (e : Nat)
    (hp : a.env.perm = true) (hg : createCost kind ≤ gas.toNat) :
    Z a.jumps .CREATE2 (atCreate kind a gas e) =
      .ok (atCreate kind a gas e,createCost kind) := by
  have hm := create_memory kind a gas e
  have hc := charged_eq_self hm
  have hg' : ¬ (atCreate kind a gas e).gasAvailable.toNat <
      memoryExpansionCost (atCreate kind a gas e) .CREATE2 := by rw [hm]; omega
  simp only [Z,Bind.bind,Except.bind,pure,Except.pure]
  rw [if_neg hg']
  unfold charged at hc
  have hsub := congrArg (fun (s : EVM.State) => s.gasAvailable) hc
  dsimp only at hsub
  rw [hc,create_cost,hsub]
  have hgg : ¬ (atCreate kind a gas e).gasAvailable.toNat < createCost kind := Nat.not_lt.mpr hg
  rw [if_neg hgg]
  have hs : ¬ (UInt256.ofNat (initSize kind) > (⟨49152⟩ : UInt256)) := by
    cases kind <;> decide
  simp [δ,α,atCreate,machine,at_,W,Operation.isCreate,hs]
  exact hp

def createStep (kind : Kind) (a : XiArgs) (gas : UInt256) (e : Nat)
    (hp : a.env.perm = true) (hg : createCost kind ≤ gas.toNat) : StepArgs :=
  { vj := a.jumps, pre := atCreate kind a gas e, mid := atCreate kind a gas e,
    cost := createCost kind, op := .CREATE2, arg := none,
    guard := create_guard kind a gas e hp hg }

def childArgs (kind : Kind) (a : XiArgs) (gas : UInt256) (e : Nat) : LambdaArgs :=
  creationArgs .create2 (createCost kind) (atCreate kind a gas e)
    a.env.weiValue ⟨0⟩ (UInt256.ofNat (initSize kind)) (salt kind)

private theorem read_init (kind : Kind) :
    (Initialization.initCode kind).readWithPadding 0 (initSize kind) = Initialization.initCode kind := by
  rw [ByteArray.readWithPadding_eq_extract _ 0 _ (by cases kind <;> decide)
    (by cases kind <;> decide) (by rw [init_size]; omega)]
  apply ByteArray.ext
  simp only [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by rw [ByteArray.size_data,init_size]; omega)

theorem child_init (kind : Kind) (a : XiArgs) (gas : UInt256) (e : Nat) :
    (childArgs kind a gas e).init = Initialization.initCode kind := by
  change (Initialization.initCode kind).readWithPadding 0
    (UInt256.ofNat (initSize kind)).toNat = _
  have hl : (UInt256.ofNat (initSize kind)).toNat = initSize kind := by cases kind <;> rfl
  rw [hl,read_init]

theorem child_source (kind : Kind) (a : XiArgs) (gas : UInt256) (e : Nat)
    (ha : a.env.codeOwner = factoryAddress) : (childArgs kind a gas e).source = factoryAddress := ha

theorem child_value (kind : Kind) (a : XiArgs) (gas : UInt256) (e : Nat) :
    (childArgs kind a gas e).value = a.env.weiValue := rfl

theorem child_salt (kind : Kind) (a : XiArgs) (gas : UInt256) (e : Nat) :
    (childArgs kind a gas e).salt = some (saltData kind) := by
  change some (salt kind).toByteArray = _
  rw [salt_encoding]

/-- Literal child selection, before any claim about the child's outcome. -/
theorem selected_create2 (kind : Kind) (a : XiArgs) (gas : UInt256) (e n : Nat)
    (hp : a.env.perm = true) (hg : createCost kind ≤ gas.toNat)
    (hn : (a.world.get? a.env.codeOwner |>.getD default).nonce.toNat < 2^64-1)
    (hv : a.env.weiValue ≤ (a.world.get? a.env.codeOwner |>.option ⟨0⟩ (·.balance)))
    (hd : a.env.depth < 1024) :
    StepChild (n+1) (createStep kind a gas e hp hg)
      (some (.lambda n (childArgs kind a gas e))) := by
  classical
  have hi : CreationGas.init (atCreate kind a gas e) ⟨0⟩
      (UInt256.ofNat (initSize kind)) = Initialization.initCode kind := child_init kind a gas e
  have hgates : CreationGas.nonceAllowed (atCreate kind a gas e) ∧
      CreationGas.gate (atCreate kind a gas e) a.env.weiValue ⟨0⟩
        (UInt256.ofNat (initSize kind)) := by
    refine ⟨hn,hv,hd,?_⟩
    rw [hi,init_size]
    cases kind <;> decide
  simp only [StepChild,selectedChild,createStep,operand,atCreate,machine,at_,List.getD_cons_zero,List.getD_cons_succ]
  change (if CreationGas.nonceAllowed (atCreate kind a gas e) ∧
      CreationGas.gate (atCreate kind a gas e) a.env.weiValue ⟨0⟩
        (UInt256.ofNat (initSize kind)) then _ else _) = _
  rw [if_pos hgates]
  rfl

/-- Actual factory entry reaches and selects precisely the initializer invocation.
The execution result of CREATE2 and the factory tail remain separate obligations. -/
theorem entry_selects (kind : Kind) (a : XiArgs) (n : Nat)
    (hcode : a.env.code = runtime) (hdata : a.env.calldata = calldata kind)
    (ha : a.env.codeOwner = factoryAddress) (hp : a.env.perm = true)
    (hgas : 40000 ≤ a.gas.toNat)
    (hn : (a.world.get? a.env.codeOwner |>.getD default).nonce.toNat < 2^64-1)
    (hv : a.env.weiValue ≤ (a.world.get? a.env.codeOwner |>.option ⟨0⟩ (·.balance)))
    (hd : a.env.depth < 1024) :
    ∃ (gas : UInt256) (e : Nat), ∃ hg : createCost kind ≤ gas.toNat,
      a.gas.toNat-157 ≤ gas.toNat ∧
      Reaches a.jumps 13 a.entry (atCreate kind a gas e) ∧
      StepChild (n+1) (createStep kind a gas e hp hg)
        (some (.lambda n (childArgs kind a gas e))) ∧
      (childArgs kind a gas e).source = factoryAddress ∧
      (childArgs kind a gas e).init = Initialization.initCode kind ∧
      (childArgs kind a gas e).value = a.env.weiValue ∧
      (childArgs kind a gas e).salt = some (saltData kind) := by
  obtain ⟨gas,e,hg,hr⟩ := reaches_create2 kind a hcode hdata (by omega)
  have hc : createCost kind ≤ 32160 := by cases kind <;> decide
  have hgc : createCost kind ≤ gas.toNat := by omega
  exact ⟨gas,e,hgc,hg,hr,selected_create2 kind a gas e n hp hgc hn hv hd,
    child_source kind a gas e ha,child_init kind a gas e,child_value kind a gas e,
    child_salt kind a gas e⟩

#print axioms entry_selects

#print axioms create_guard
#print axioms selected_create2

#print axioms salt_encoding
#print axioms reaches_create2
end Eip8282.Audit.Integrator.FactoryRuntimeEntry
