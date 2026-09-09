import Eip8282.Audit.Integrator.StorageFunding
import Eip8282.Audit.Integrator.CreationGas
import Eip8282.Audit.Integrator.CallFunding

/-!
# Funding of the literal creation entry and settlement

Lambda debits before inserting a fresh account built from the old target.
Consequently its entry need not conserve funds when sender and target alias.
A nonzero sender nonce makes that alias an occupied-target failure, restoring
its input world on every completed settlement. CREATE derives that nonce from
its actual admitted increment. No property of address hashing is assumed.
-/
namespace Eip8282.Audit.Integrator.CreationFunding
open EvmYul EvmYul.EVM
open Eip8282.Audit.EntryReach
open TransferFunding CreationSettlement
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

theorem lookup_insert (world : AccountMap .EVM) (key addr : AccountAddress)
    (account : Account .EVM) :
    (world.insert key account).get? addr = if key = addr then some account else world.get? addr := by
  exact (Std.TreeMap.getElem?_insert (t := world) (k := key) (a := addr) (v := account)).trans
    (by simp only [Std.LawfulEqOrd.compare_eq_iff_eq]; rfl)

theorem getD_balance (world : AccountMap .EVM) (a : AccountAddress) :
    (world.getD a default).balance.toNat = worldBalance world a := by
  rw [Std.TreeMap.getD_eq_getD_getElem?]
  change ((world.get? a).getD default).balance.toNat = _
  unfold worldBalance
  cases h : world.get? a <;> rfl

/-- Installation only changes code, including the absent-account case. -/
theorem install_preserves (world : AccountMap .EVM) (a : AccountAddress) (code : ByteArray) :
    worldFunds (install world a code) = worldFunds world := by
  have h := funds_insert world a { world.getD a default with code := code }
  change worldFunds (install world a code) + worldBalance world a =
    worldFunds world + (world.getD a default).balance.toNat at h
  rw [getD_balance] at h
  omega

/-- The exact nonce-updated world passed by CREATE/CREATE2. -/
def nonceWorld (pre : EVM.State) : AccountMap .EVM :=
  let owner := pre.executionEnv.codeOwner
  let account := (pre.accountMap.get? owner).getD default
  pre.accountMap.insert owner { account with nonce := account.nonce + ⟨1⟩ }

theorem nonce_preserves (pre : EVM.State) :
    worldFunds (nonceWorld pre) = worldFunds pre.accountMap := by
  unfold nonceWorld
  have h := funds_insert pre.accountMap pre.executionEnv.codeOwner
    { (pre.accountMap.get? pre.executionEnv.codeOwner).getD default with
      nonce := ((pre.accountMap.get? pre.executionEnv.codeOwner).getD default).nonce + ⟨1⟩ }
  cases he : pre.accountMap.get? pre.executionEnv.codeOwner <;>
    simp only [he, worldBalance, Option.getD_none, Option.getD_some, Option.map_none,
      Option.map_some] at h ⊢
  · change worldFunds _ + 0 = worldFunds _ + 0 at h
    exact h
  · omega

theorem nonce_balance (pre : EVM.State) :
    worldBalance (nonceWorld pre) pre.executionEnv.codeOwner =
      worldBalance pre.accountMap pre.executionEnv.codeOwner := by
  unfold nonceWorld worldBalance
  rw [lookup_insert, if_pos rfl]
  cases he : pre.accountMap.get? pre.executionEnv.codeOwner <;> rfl

theorem nonce_positive (pre : EVM.State) (hn : CreationGas.nonceAllowed pre) :
    ∃ account, (nonceWorld pre).get? pre.executionEnv.codeOwner = some account ∧ account.nonce ≠ ⟨0⟩ := by
  refine ⟨_, Std.TreeMap.getElem?_insert_self, ?_⟩
  have hb : ((pre.accountMap.get? pre.executionEnv.codeOwner).getD default).nonce.toNat + 1 < UInt256.size := by
    change _ < 2^64-1 at hn
    unfold UInt256.size
    omega
  intro he
  have he := congrArg UInt256.toNat he
  change (((pre.accountMap.get? pre.executionEnv.codeOwner).getD default).nonce.toNat + 1) % UInt256.size = 0 at he
  rw [Nat.mod_eq_of_lt hb] at he
  omega

/-- Distinct sender and target: the real debit and fresh-account credit cannot
increase the finite natural total, even if the recipient addition wraps. -/
theorem entry_distinct (c : Context) (a : AccountAddress) (hne : c.sender ≠ a)
    (hf : c.value.toNat ≤ worldBalance c.world c.sender) :
    worldFunds (c.entryWorld a) ≤ worldFunds c.world := by
  unfold Context.entryWorld
  cases hs : c.world.get? c.sender with
  | none => exact Nat.le_refl _
  | some account =>
    dsimp only
    have hd := funds_insert c.world c.sender { account with balance := account.balance - c.value }
    have hc := funds_insert (c.world.insert c.sender { account with balance := account.balance-c.value }) a
      { c.existing a with nonce := (c.existing a).nonce+⟨1⟩, balance := c.value+(c.existing a).balance }
    have hl : worldBalance (c.world.insert c.sender { account with balance := account.balance-c.value }) a =
        worldBalance c.world a := by
      unfold worldBalance
      rw [lookup_insert, if_neg hne]
    rw [hl] at hc
    simp only [worldBalance, hs, Option.map_some, Option.getD_some] at hf hd
    have hsub := toNat_sub_of_le account.balance c.value hf
    have hadd : (c.value+(c.existing a).balance).toNat ≤ c.value.toNat+(c.existing a).balance.toNat := Nat.mod_le _ _
    have hbal : (c.existing a).balance.toNat = worldBalance c.world a := getD_balance _ _
    dsimp only at hd hc
    rw [hsub] at hd
    omega

/-- The final occupied-target guard handles the alias case, without applying
an execution induction hypothesis to its potentially inflated entry world. -/
theorem alias_deposit_failure (c : Context) (account : Account .EVM)
    (hs : c.world.get? c.sender = some account) (hn : account.nonce ≠ ⟨0⟩)
    (gas : UInt256) (code : ByteArray) :
    c.depositFailure c.sender gas code = true := by
  unfold Context.depositFailure
  simp only [hs]
  simp [hn]

/-- Aliasing with this nonce also selects the literal one-byte INVALID init.
It does not run user-provided init code before the rollback. -/
theorem alias_selected_invalid (c : Context) (account : Account .EVM)
    (hs : c.world.get? c.sender = some account) (hn : account.nonce ≠ ⟨0⟩) :
    c.selectedCode c.sender = ⟨#[0xfe]⟩ := by
  unfold Context.selectedCode Context.collision Context.existing
  rw [Std.TreeMap.getD_eq_getD_getElem?]
  change (if decide (((c.world.get? c.sender).getD default).nonce ≠ ⟨0⟩) || _ || _ then _ else _) = _
  have hs' : c.world[c.sender]? = some account := hs
  simp [hs', hn]

/-- Any actual completed settlement of the alias case restores the input world,
regardless of which actual init outcome produced it. -/
theorem alias_settle_world (c : Context) (account : Account .EVM)
    (hs : c.world.get? c.sender = some account) (hn : account.nonce ≠ ⟨0⟩)
    (r : Eip8282.Audit.EvmRunner.RunResult)
    {a : AccountAddress} {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {success : Bool} {out : ByteArray}
    (h : c.settle c.sender r = .ok (a,created,world,gas,substate,success,out)) :
    world = c.world := by
  cases r with
  | error e =>
    simp only [Context.settle] at h
    split at h
    · cases h
    · exact (congrArg (fun t => t.2.2.1) (Except.ok.inj h)).symm
  | ok result =>
    cases result with
    | revert remaining output => exact (congrArg (fun t => t.2.2.1) (Except.ok.inj h)).symm
    | success state code =>
      rcases state with ⟨ic,iw,ig,ia⟩
      simp only [Context.settle, alias_deposit_failure c account hs hn, ↓reduceIte] at h
      exact (congrArg (fun t => t.2.2.1) (Except.ok.inj h)).symm

#print axioms install_preserves
#print axioms nonce_preserves
#print axioms nonce_positive
#print axioms entry_distinct
#print axioms alias_selected_invalid
#print axioms alias_settle_world
end Eip8282.Audit.Integrator.CreationFunding
