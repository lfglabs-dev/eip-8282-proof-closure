import Eip8282.Audit.Integrator.FactoryRuntimeEntry

/-! The actual successful factory tail, including its conditional jump,
memory write and RETURN. This preserves the complete world and substate
produced by CREATE2; it does not assume or establish creation success. -/
namespace Eip8282.Audit.Integrator.FactoryRuntimeReturn
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.SymExec Eip8282.Audit.EntryReach
open Eip8282.Audit.XiTransport (XiCall)
open Eip8282.Audit.Model (Kind)
open Eip8282.Audit.Bytecode Eip8282.Audit.Jumpdests
open NestedEvents FactoryRuntimeEntry
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

private def template (a : XiArgs) : XiCall .deposit :=
  { fuel := 0, createdAccounts := a.created, genesisBlockHeader := a.genesis,
    blocks := a.blocks, σ := a.world, σ₀ := a.original, gas := a.gas,
    substate := a.substate, env := {a.env with code := depositRuntime}, code_pinned := rfl }

private def checkBlock : List Site :=
  [(48,(.DUP1,none)),(49,(.ISZERO,none)),(50,(.ISZERO,none)),
   (51,(.PUSH1,some (UInt256.ofNat 57,1)))]
private def storeBlock : List Site :=
  [(57,(.JUMPDEST,none)),(58,(.DUP1,none)),(59,(.DUP3,none))]
private def returnBlock : List Site :=
  [(61,(.POP,none)),(62,(.POP,none)),(63,(.POP,none)),
   (64,(.PUSH1,some (UInt256.ofNat 20,1))),
   (66,(.PUSH1,some (UInt256.ofNat 12,1)))]

private theorem check_sites : sitesOk runtime checkBlock = true := by decide +kernel
private theorem store_sites : sitesOk runtime storeBlock = true := by decide +kernel
private theorem return_sites : sitesOk runtime returnBlock = true := by decide +kernel

def start (kind : Kind) (a : XiArgs) (address gas : UInt256) (e : Nat) : EVM.State :=
  machine a (Initialization.initCode kind) (mAfter ⟨0⟩ 0 (initSize kind)) gas 48
    [address,⟨0⟩,UInt256.ofNat (initSize kind)] e

def returnedMemory (kind : Kind) (address : UInt256) : ByteArray :=
  mstoreMem (Initialization.initCode kind) ⟨0⟩ address

def output (kind : Kind) (address : UInt256) : ByteArray :=
  (returnedMemory kind address).readWithPadding 12 20

def finish (kind : Kind) (a : XiArgs) (address gas : UInt256) (e : Nat) : EVM.State :=
  machine a (returnedMemory kind address)
    (mAfter (mAfter ⟨0⟩ 0 (initSize kind)) 0 32) gas 68 [⟨12⟩,⟨20⟩] e

/-- Fourteen actual instructions reach RETURN with the created address.
The resource margin is conservative and independent of stored account data. -/
theorem reaches_return (kind : Kind) (a : XiArgs) (address gas : UInt256) (e : Nat)
    (hc : a.env.code = runtime) (ha : address ≠ ⟨0⟩) (hg : 200 ≤ gas.toNat) :
    ∃ gas' e', gas.toNat-104 ≤ gas'.toNat ∧
      Reaches a.jumps 14 (start kind a address gas e) (finish kind a address gas' e') ∧
      Halt a.jumps (finish kind a address gas' e') .RETURN (output kind address) := by
  have hcode : a.entry.toState.executionEnv.code = runtime := hc
  have hj : a.jumps.contains (UInt256.ofNat 57) = true := by
    change (D_J a.env.code ⟨0⟩).contains (UInt256.ofNat 57) = true
    rw [hc]
    decide +kernel
  have hvj : ∀ n ∈ ([57] : List Nat), a.jumps.contains (UInt256.ofNat n) = true := by
    intro n hn
    have he : n = 57 := List.mem_singleton.mp hn
    exact he ▸ hj
  obtain ⟨g₁,e₁,hg₁,h₁⟩ := reach_block (vj := a.jumps) (vjNats := [57]) hvj
    checkBlock check_sites (c := template a) (st := a.entry.toState)
    (mem := Initialization.initCode kind) (aw := mAfter ⟨0⟩ 0 (initSize kind))
    (g := gas) (pc := 48) (stk := [address,⟨0⟩,UInt256.ofNat (initSize kind)]) (e := e)
    hcode rfl (by change 12 ≤ gas.toNat; omega) (by simp [checkBlock])
    (show symBlock [57] (checkBlock.map Prod.snd) _ = some
      (at_ (template a) a.entry.toState (Initialization.initCode kind)
       (mAfter ⟨0⟩ 0 (initSize kind)) gas 53
       [⟨57⟩,UInt256.isZero (UInt256.isZero address),address,⟨0⟩,UInt256.ofNat (initSize kind)] e) from rfl)
  obtain ⟨g₂,e₂,hg₂,h₂⟩ := reach_jumpi_taken (vj := a.jumps) (c := template a)
    (st := a.entry.toState) (mem := Initialization.initCode kind)
    (aw := mAfter ⟨0⟩ 0 (initSize kind)) (g := g₁) (pc := 53) (d := 57)
    (cond := UInt256.isZero (UInt256.isZero address))
    (r := [address,⟨0⟩,UInt256.ofNat (initSize kind)]) (e := e₁)
    (by decide +kernel : opcodeAt runtime 53 = some (.JUMPI,none)) hcode
    ((isZero_ne_zero_iff _).mpr ((isZero_eq_zero_iff _).mpr ha)) hj
    (by change gas.toNat-12 ≤ g₁.toNat at hg₁; omega) (by simp)
  obtain ⟨g₃,e₃,hg₃,h₃⟩ := reach_block (vj := a.jumps) (vjNats := [57]) hvj
    storeBlock store_sites (c := template a) (st := a.entry.toState)
    (mem := Initialization.initCode kind) (aw := mAfter ⟨0⟩ 0 (initSize kind))
    (g := g₂) (pc := 57) (stk := [address,⟨0⟩,UInt256.ofNat (initSize kind)]) (e := e₂)
    hcode rfl (by change 7 ≤ g₂.toNat; change gas.toNat-12 ≤ g₁.toNat at hg₁; omega)
    (by simp [storeBlock])
    (show symBlock [57] (storeBlock.map Prod.snd) _ = some
      (at_ (template a) a.entry.toState (Initialization.initCode kind)
       (mAfter ⟨0⟩ 0 (initSize kind)) g₂ 60
       [⟨0⟩,address,address,⟨0⟩,UInt256.ofNat (initSize kind)] e₂) from rfl)
  obtain ⟨g₄,e₄,hg₄,h₄⟩ := reach_mstore (vj := a.jumps) (c := template a)
    (st := a.entry.toState) (mem := Initialization.initCode kind)
    (aw := mAfter ⟨0⟩ 0 (initSize kind)) (g := g₃) (pc := 60)
    (off := ⟨0⟩) (v := address) (r := [address,⟨0⟩,UInt256.ofNat (initSize kind)]) (e := e₃)
    (B := 20) (by decide +kernel) hcode (by cases kind <;> decide)
    (by decide) (by decide) (M := 63) rfl
    (by change gas.toNat-12 ≤ g₁.toNat at hg₁; change g₂.toNat-7 ≤ g₃.toNat at hg₃; omega)
    (by simp)
  obtain ⟨g₅,e₅,hg₅,h₅⟩ := reach_block (vj := a.jumps) (vjNats := [57]) hvj
    returnBlock return_sites (c := template a) (st := a.entry.toState)
    (mem := returnedMemory kind address) (aw := mAfter (mAfter ⟨0⟩ 0 (initSize kind)) 0 32)
    (g := g₄) (pc := 61) (stk := [address,⟨0⟩,UInt256.ofNat (initSize kind)]) (e := e₄)
    hcode rfl
    (by change 12 ≤ g₄.toNat; change gas.toNat-12 ≤ g₁.toNat at hg₁; change g₂.toNat-7 ≤ g₃.toNat at hg₃; omega)
    (by simp [returnBlock])
    (show symBlock [57] (returnBlock.map Prod.snd) _ = some
      (at_ (template a) a.entry.toState (returnedMemory kind address)
       (mAfter (mAfter ⟨0⟩ 0 (initSize kind)) 0 32) g₄ 68 [⟨12⟩,⟨20⟩] e₄) from rfl)
  have hb : gas.toNat-104 ≤ g₅.toNat := by
    change gas.toNat-12 ≤ g₁.toNat at hg₁
    change g₂.toNat-7 ≤ g₃.toNat at hg₃
    change g₄.toNat-12 ≤ g₅.toNat at hg₅
    omega
  refine ⟨g₅,e₅,hb,(h₁.trans h₂ |>.trans h₃ |>.trans h₄ |>.trans h₅),?_⟩
  exact halt_RETURN (vj := a.jumps) (c := template a) (st := a.entry.toState)
    (mem := returnedMemory kind address) (aw := mAfter (mAfter ⟨0⟩ 0 (initSize kind)) 0 32)
    (g := g₅) (pc := 68) (off := ⟨12⟩) (len := ⟨20⟩) (r := []) (e := e₅)
    (B := 20) (by decide +kernel) hcode (by cases kind <;> decide)
    (by decide) (by decide) (M := 60) rfl (by omega) (by decide)

/-- Complete actual X execution of the successful tail. The returned world,
created-account set and full substate are the original tail inputs. -/
theorem execution (kind : Kind) (a : XiArgs) (address gas : UInt256) (e fuel : Nat)
    (hc : a.env.code = runtime) (ha : address ≠ ⟨0⟩) (hg : 200 ≤ gas.toNat)
    (hf : 16 ≤ fuel) :
    ∃ post, X fuel a.jumps (start kind a address gas e) =
        .ok (.success post (output kind address)) ∧
      post.accountMap = a.world ∧ post.createdAccounts = a.created ∧
      post.substate = a.substate ∧ post.executionEnv = a.env := by
  obtain ⟨g',e',_,hp,hh⟩ := reaches_return kind a address gas e hc ha hg
  obtain ⟨tr,hr⟩ := hp (fuel-15)
  rw [show fuel-15+1+14 = fuel by omega] at hr
  have hr' := Eip8282.Audit.XiTransport.runUntil_of_xRuns hr
    (RunUntil.stop (by rw [hh.decode]; exact stopOrHalting_of_halting EntryReach.halting_RETURN))
  obtain ⟨post,hs,hH⟩ := hh.step (fuel-16)
  have hc' := stepOk_halt (f := fuel-16) (by decide : .RETURN ∈ allOps)
    (Eip8282.Audit.SymExec.step_RETURN
      (s := finish kind a address g' e')
      (rfl : (finish kind a address g' e').stack = [⟨12⟩,⟨20⟩]))
  have heq := Step.deterministic_ok hs hc'
  subst post
  rw [show fuel-16+1 = fuel-15 by omega] at hs
  have hx := hr'.X_success hh.decode hh.charge hs hH
    (by decide : (Operation.RETURN : Operation .EVM) ≠ .REVERT)
  exact ⟨_,hx,rfl,rfl,rfl,rfl⟩

#print axioms reaches_return
#print axioms execution
end Eip8282.Audit.Integrator.FactoryRuntimeReturn
