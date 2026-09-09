import Eip8282.Audit.Integrator.Initialization

/-!
# Actual Lambda creation settlement

Creation addresses are those computed by the pinned Lambda semantics. No
canonical-predeploy identity or genesis allocation is assumed. Address hashing
and optional RLP failure remain semantic inputs; this module does not evaluate
or replace them. Collision handling and all code-deposit failure guards remain
visible in the exact settlement equation.

The constructor specializations describe actual successful creation and retain
explicit resource, code-pin and no-collision hypotheses. They do not claim that
init success alone pays the code-deposit cost. Deposit preserves prior storage;
its enabled/zero-control corollary requires those prior slots to be zero. Exit
sets INHIBITOR independently of the old slot-zero value. Establishing a canonical
predeploy address or a deployment transaction's validity remains outside scope.
-/

namespace Eip8282.Audit.Integrator.CreationSettlement

open EvmYul EvmYul.EVM
open Eip8282.Audit.Model (Kind)
open SystemSpec (worldSlot HasOwner)

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

structure Context where
  fuel : Nat
  blobHashes : List ByteArray
  created : Std.TreeSet AccountAddress compare
  genesis : BlockHeader
  blocks : ProcessedBlocks
  world : AccountMap .EVM
  originalWorld : AccountMap .EVM
  substate : Substate
  sender : AccountAddress
  origin : AccountAddress
  gas : UInt256
  gasPrice : UInt256
  value : UInt256
  init : ByteArray
  depth : UInt256
  salt : Option ByteArray
  header : BlockHeader
  permission : Bool

def Context.result (c : Context) :=
  Lambda (c.fuel + 1) c.blobHashes c.created c.genesis c.blocks c.world c.originalWorld
    c.substate c.sender c.origin c.gas c.gasPrice c.value c.init c.depth c.salt c.header c.permission

def Context.preimage (c : Context) : Option ByteArray :=
  Lambda.L_A c.sender ((c.world.get? c.sender |>.option ⟨0⟩ (·.nonce)) - ⟨1⟩) c.salt c.init

/-- Exact upstream address derivation, kept symbolic. -/
def address (preimage : ByteArray) : AccountAddress :=
  (ffi.KEC preimage).extract 12 32 |> fromByteArrayBigEndian |> Fin.ofNat _

def Context.existing (c : Context) (a : AccountAddress) : Account .EVM := c.world.getD a default

def Context.collision (c : Context) (a : AccountAddress) : Bool :=
  (c.existing a).nonce ≠ ⟨0⟩ || (c.existing a).code.size ≠ 0 || (c.existing a).storage != default

def Context.selectedCode (c : Context) (a : AccountAddress) : ByteArray :=
  if c.collision a then ⟨#[0xfe]⟩ else c.init

def Context.selectedCreated (c : Context) (a : AccountAddress) : Std.TreeSet AccountAddress compare :=
  if c.collision a then c.created else c.created.insert a

def Context.accessed (c : Context) (a : AccountAddress) : Substate := c.substate.addAccessedAccount a

/-- Debit sender before inserting the new account, exactly in Lambda's order.
If the sender is missing, Lambda leaves the world alone. -/
def Context.entryWorld (c : Context) (a : AccountAddress) : AccountMap .EVM :=
  let old := c.existing a
  let fresh : Account .EVM := { old with nonce := old.nonce + ⟨1⟩, balance := c.value + old.balance }
  match c.world.get? c.sender with
  | none => c.world
  | some acc => (c.world.insert c.sender { acc with balance := acc.balance - c.value }).insert a fresh

def Context.environment (c : Context) (a : AccountAddress) : ExecutionEnv .EVM :=
  { codeOwner := a, sender := c.origin, source := c.sender, weiValue := c.value,
    calldata := default, code := c.selectedCode a, gasPrice := c.gasPrice.toNat,
    header := c.header, depth := c.depth.toNat, perm := c.permission,
    blobVersionedHashes := c.blobHashes }

def Context.execution (c : Context) (a : AccountAddress) :=
  Ξ c.fuel (c.selectedCreated a) c.genesis c.blocks (c.entryWorld a) c.originalWorld
    c.gas (c.accessed a) (c.environment a)

/-- All four actual code-deposit rejection checks, after init success. -/
def Context.depositFailure (c : Context) (a : AccountAddress)
    (remaining : UInt256) (code : ByteArray) : Bool :=
  let occupied : Bool := match c.world.get? a with
    | some acc => acc.code ≠ .empty ∨ acc.nonce ≠ ⟨0⟩
    | none => false
  let insufficient : Bool := remaining.toNat < GasConstants.Gcodedeposit * code.size
  let oversized : Bool := code.size > 24576
  let forbiddenPrefix : Bool := ¬oversized && code[0]? = some 0xef
  occupied ∨ insufficient ∨ oversized ∨ forbiddenPrefix

/-- Exact code installation: only the target account's code field changes. -/
def install (world : AccountMap .EVM) (a : AccountAddress) (code : ByteArray) : AccountMap .EVM :=
  world.insert a { world.getD a default with code := code }

def Context.settle (c : Context) (a : AccountAddress) (r : Eip8282.Audit.EvmRunner.RunResult) :
    Except ExecutionException (AccountAddress × Std.TreeSet AccountAddress compare ×
      AccountMap .EVM × UInt256 × Substate × Bool × ByteArray) :=
  match r with
  | .error e => if e == ExecutionException.OutOfFuel then .error ExecutionException.OutOfFuel
      else .ok (a, c.selectedCreated a, c.world, (⟨0⟩ : UInt256), c.accessed a, false, ByteArray.empty)
  | .ok (.revert gas out) => .ok (a, c.selectedCreated a, c.world, gas, c.accessed a, false, out)
  | .ok (.success (created, world, gas, substate) code) =>
      let failed := c.depositFailure a gas code
      .ok (a, created, if failed then c.world else install world a code,
        UInt256.ofNat (if failed then 0 else gas.toNat - GasConstants.Gcodedeposit * code.size),
        if failed then c.accessed a else substate, !failed, ByteArray.empty)

private theorem pair_choice {α β : Type} (b : Bool) (x z : α) (y w : β) :
    (if b then (x, y) else (z, w)) = (if b then x else z, if b then y else w) := by
  cases b <;> rfl

/-- This is Lambda itself unfolded, not an alternative creation interpreter.
The optional address preimage is required to have been successfully encoded. -/
theorem result_eq_settle (c : Context) {preimage : ByteArray}
    (hp : c.preimage = some preimage) :
    c.result = c.settle (address preimage) (c.execution (address preimage)) := by
  unfold Context.result Lambda
  change Lambda.L_A c.sender ((c.world.get? c.sender |>.option ⟨0⟩ (·.nonce)) - ⟨1⟩) c.salt c.init =
    some preimage at hp
  dsimp only
  rw [hp]
  dsimp only [liftM, MonadLift.monadLift, MonadLiftT.monadLift, Option.elim, Option.option, Except.bind, Bind.bind]
  unfold Context.settle Context.execution Context.environment Context.selectedCode
    Context.selectedCreated Context.collision Context.existing Context.entryWorld
    Context.accessed Context.depositFailure install address
  simp only [pair_choice]
  dsimp only [Context.existing]
  congr 1


/-- Forward installation retains the actual remaining-gas check; init success
alone does not imply successful creation. -/
theorem installs_of_execution (c : Context) {preimage : ByteArray}
    (hp : c.preimage = some preimage)
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {code : ByteArray}
    (hr : c.execution (address preimage) = .ok (.success (created, world, gas, substate) code))
    (hf : c.depositFailure (address preimage) gas code = false) :
    c.result = .ok (address preimage, created, install world (address preimage) code,
      UInt256.ofNat (gas.toNat - GasConstants.Gcodedeposit * code.size),
      substate, true, ByteArray.empty) := by
  rw [result_eq_settle c hp, hr]
  simp only [Context.settle, hf, Bool.false_eq_true, ↓reduceIte, Bool.not_false]

/-- Rejected code deposit restores the original world and accessed substate,
uses zero remaining gas, and returns failure. The actual returned created-account
set is retained exactly as upstream Lambda specifies. -/
theorem failed_deposit_result (c : Context) {preimage : ByteArray}
    (hp : c.preimage = some preimage)
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {code : ByteArray}
    (hr : c.execution (address preimage) = .ok (.success (created, world, gas, substate) code))
    (hf : c.depositFailure (address preimage) gas code = true) :
    c.result = .ok (address preimage, created, c.world, UInt256.ofNat 0,
      c.accessed (address preimage), false, ByteArray.empty) := by
  rw [result_eq_settle c hp, hr]
  simp only [Context.settle, hf, ↓reduceIte, Bool.not_true]

/-- Successful Lambda output entails successful init execution and passing all
code-deposit guards. No hypothesis about the resulting world is used. -/
theorem success_inversion (c : Context) {preimage : ByteArray}
    (hp : c.preimage = some preimage)
    {a : AccountAddress} {created : Std.TreeSet AccountAddress compare}
    {world : AccountMap .EVM} {gas : UInt256} {substate : Substate} {out : ByteArray}
    (hr : c.result = .ok (a, created, world, gas, substate, true, out)) :
    ∃ initWorld initGas code,
      c.execution (address preimage) = .ok (.success (created, initWorld, initGas, substate) code) ∧
      c.depositFailure (address preimage) initGas code = false ∧
      a = address preimage ∧ world = install initWorld a code ∧
      gas = UInt256.ofNat (initGas.toNat - GasConstants.Gcodedeposit * code.size) ∧
      out = ByteArray.empty := by
  rw [result_eq_settle c hp] at hr
  cases he : c.execution (address preimage) with
  | error e =>
      simp only [he, Context.settle] at hr
      split at hr <;> simp_all
  | ok result =>
      cases result with
      | revert remaining returned => simp [he, Context.settle] at hr
      | success state code =>
          rcases state with ⟨ic, iw, ig, ia⟩
          cases hf : c.depositFailure (address preimage) ig code <;>
            simp only [he, Context.settle, hf, Bool.false_eq_true, Bool.not_false,
              Bool.not_true, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at hr
          · rcases hr with ⟨rfl, rfl, rfl, rfl, rfl, _, rfl⟩
            exact ⟨iw, ig, code, rfl, hf, rfl, rfl, rfl, rfl⟩
          · simp at hr

private theorem lookup_insert (world : AccountMap .EVM) (key addr : AccountAddress)
    (account : Account .EVM) :
    (world.insert key account).get? addr = if key = addr then some account else world.get? addr := by
  exact (Std.TreeMap.getElem?_insert (t := world) (k := key) (a := addr) (v := account)).trans
    (by simp only [Std.LawfulEqOrd.compare_eq_iff_eq]; rfl)

/-- Code installation supplies an existing owner and exactly the returned bytes. -/
theorem installed_code (world : AccountMap .EVM) (a : AccountAddress) (code : ByteArray) :
    ∃ acc, (install world a code).get? a = some acc ∧ acc.code = code := by
  exact ⟨_, Std.TreeMap.getElem?_insert_self, rfl⟩

/-- Code deposit does not change a storage lookup, including absent accounts. -/
theorem install_storage (world : AccountMap .EVM) (a addr : AccountAddress)
    (code : ByteArray) (q : UInt256) :
    worldSlot (install world a code) addr q = worldSlot world addr q := by
  unfold install worldSlot
  rw [lookup_insert]
  by_cases h : a = addr
  · subst addr
    rw [if_pos rfl, Std.TreeMap.getD_eq_getD_getElem?]
    cases he : world.get? a with
    | none =>
        change (({ (world.get? a).getD default with code := code } : Account .EVM).lookupStorage q) = _
        rw [he]
        rfl
    | some acc =>
        change (({ (world.get? a).getD default with code := code } : Account .EVM).lookupStorage q) = _
        rw [he]
        rfl
  · rw [if_neg h]

private theorem getD_storage (world : AccountMap .EVM) (addr : AccountAddress) (q : UInt256) :
    (world.getD addr default).lookupStorage q = worldSlot world addr q := by
  rw [Std.TreeMap.getD_eq_getD_getElem?]
  change ((world.get? addr).getD default).lookupStorage q = _
  unfold worldSlot
  cases he : world.get? addr <;> rfl

/-- Lambda's value transfer and new-account nonce update preserve every storage
observation, also when sender = target or either original account is missing. -/
theorem entry_storage (c : Context) (a addr : AccountAddress) (q : UInt256) :
    worldSlot (c.entryWorld a) addr q = worldSlot c.world addr q := by
  unfold Context.entryWorld
  cases hs : c.world.get? c.sender with
  | none => rfl
  | some acc =>
      unfold worldSlot
      rw [lookup_insert]
      by_cases ha : a = addr
      · subst addr
        rw [if_pos rfl]
        exact getD_storage c.world a q
      · rw [if_neg ha, lookup_insert]
        by_cases hsender : c.sender = addr
        · subst addr
          rw [if_pos rfl, hs]
          rfl
        · rw [if_neg hsender]

/-- The initialization call uses Lambda's actual entry world and environment. -/
def Context.initCall (c : Context) (a : AccountAddress) (steps : Nat) : Initialization.InitCall :=
  { fuel := steps, createdAccounts := c.selectedCreated a, genesisBlockHeader := c.genesis,
    blocks := c.blocks, world := c.entryWorld a, originalWorld := c.originalWorld,
    gas := c.gas, substate := c.accessed a, env := c.environment a }

theorem execution_eq_initialization (c : Context) (a : AccountAddress) (steps : Nat)
    (kind : Kind) (hf : c.fuel = steps + 1) (hc : c.collision a = false)
    (hi : c.init = Initialization.initCode kind) :
    c.execution a = (c.initCall a steps).result kind := by
  unfold Context.execution Initialization.InitCall.result Context.initCall
    Initialization.InitCall.environment Context.environment Context.selectedCode
  rw [hf, hc, hi]
  rfl

/-- A known actual init result identifies the runtime and storage in any
successful creation result; remaining gas and every deposit guard are retained. -/
theorem installed_of_known_execution (c : Context) {preimage : ByteArray}
    (hp : c.preimage = some preimage)
    {ic : Std.TreeSet AccountAddress compare} {iw : AccountMap .EVM}
    {ig : UInt256} {ia : Substate} {code : ByteArray}
    (he : c.execution (address preimage) = .ok (.success (ic, iw, ig, ia) code))
    {a : AccountAddress} {created : Std.TreeSet AccountAddress compare}
    {world : AccountMap .EVM} {gas : UInt256} {substate : Substate} {out : ByteArray}
    (hr : c.result = .ok (a, created, world, gas, substate, true, out)) :
    a = address preimage ∧
      (∃ acc, world.get? a = some acc ∧ acc.code = code) ∧
      (∀ addr q, worldSlot world addr q = worldSlot iw addr q) ∧
      c.depositFailure a ig code = false ∧
      gas = UInt256.ofNat (ig.toNat - GasConstants.Gcodedeposit * code.size) ∧
      substate = ia ∧ created = ic ∧ out = ByteArray.empty := by
  rw [result_eq_settle c hp, he] at hr
  cases hf : c.depositFailure (address preimage) ig code <;>
    simp only [Context.settle, hf, Bool.false_eq_true, Bool.not_false,
      Bool.not_true, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at hr
  · rcases hr with ⟨rfl, rfl, rfl, rfl, rfl, _, rfl⟩
    exact ⟨rfl, installed_code _ _ _, fun addr q => install_storage _ _ addr _ q,
      hf, rfl, rfl, rfl, rfl⟩
  · simp at hr

/-- A present sender makes Lambda's actual newly inserted owner exist, including
sender = creation address. No balance or sufficient-funds assertion is made. -/
theorem entry_hasOwner (c : Context) (a : AccountAddress) (steps : Nat) (kind : Kind)
    (hs : ∃ acc, c.world.get? c.sender = some acc) :
    HasOwner ((c.initCall a steps).entry kind).toState := by
  obtain ⟨acc, hs⟩ := hs
  change ∃ owner, (c.entryWorld a).get? a = some owner
  unfold Context.entryWorld
  rw [hs]
  exact ⟨_, Std.TreeMap.getElem?_insert_self⟩

/-- Successful creation with the pinned deposit init installs the exact pinned
runtime. Deposit init and code installation preserve every control/storage slot.
Resource hypotheses belong to the universal constructor execution proof. -/
theorem deposit_creation (c : Context) {preimage : ByteArray}
    (hp : c.preimage = some preimage) (steps : Nat)
    (hf : c.fuel = steps + 1) (hc : c.collision (address preimage) = false)
    (hi : c.init = Initialization.initCode .deposit)
    (hg : 1000 ≤ c.gas.toNat) (hs : 8 ≤ steps)
    {a : AccountAddress} {created : Std.TreeSet AccountAddress compare}
    {world : AccountMap .EVM} {gas : UInt256} {substate : Substate} {out : ByteArray}
    (hr : c.result = .ok (a, created, world, gas, substate, true, out)) :
    a = address preimage ∧
      (∃ acc, world.get? a = some acc ∧ acc.code = Initialization.runtime .deposit) ∧
      (∀ q, worldSlot world a q = worldSlot c.world a q) ∧
      substate.logSeries = c.substate.logSeries := by
  let init := c.initCall (address preimage) steps
  obtain ⟨ic, iw, ig, ia, hex, hslots, hlogs⟩ :=
    Initialization.deposit_initializes init hg hs
  rw [← execution_eq_initialization c (address preimage) steps .deposit hf hc hi] at hex
  obtain ⟨ha, hcode, hstorage, _, _, hsub, _, _⟩ :=
    installed_of_known_execution c hp hex hr
  subst a
  refine ⟨rfl, hcode, ?_, ?_⟩
  · intro q
    rw [hstorage]
    exact (hslots q).trans (entry_storage c (address preimage) (address preimage) q)
  · rw [hsub, hlogs]
    rfl

/-- Successful creation with the pinned exit init installs the exact runtime,
latches slot zero to INHIBITOR, and preserves every other owner storage slot. -/
theorem exit_creation (c : Context) {preimage : ByteArray}
    (hp : c.preimage = some preimage) (steps : Nat)
    (hf : c.fuel = steps + 1) (hc : c.collision (address preimage) = false)
    (hi : c.init = Initialization.initCode .exit) (hperm : c.permission = true)
    (hg : 25000 ≤ c.gas.toNat) (hs : 11 ≤ steps)
    (howner : ∃ acc, c.world.get? c.sender = some acc)
    {a : AccountAddress} {created : Std.TreeSet AccountAddress compare}
    {world : AccountMap .EVM} {gas : UInt256} {substate : Substate} {out : ByteArray}
    (hr : c.result = .ok (a, created, world, gas, substate, true, out)) :
    a = address preimage ∧
      (∃ acc, world.get? a = some acc ∧ acc.code = Initialization.runtime .exit) ∧
      (∀ q, worldSlot world a q =
        if q = ⟨0⟩ then Eip8282.Audit.EntryReach.INH else worldSlot c.world a q) ∧
      substate.logSeries = c.substate.logSeries := by
  let init := c.initCall (address preimage) steps
  obtain ⟨ic, iw, ig, ia, hex, _, hslots, hlogs, _⟩ :=
    Initialization.exit_initializes init hperm hg hs
      (entry_hasOwner c (address preimage) steps .exit howner)
  rw [← execution_eq_initialization c (address preimage) steps .exit hf hc hi] at hex
  obtain ⟨ha, hcode, hstorage, _, _, hsub, _, _⟩ :=
    installed_of_known_execution c hp hex hr
  subst a
  refine ⟨rfl, hcode, ?_, ?_⟩
  · intro q
    rw [hstorage]
    have h := hslots q
    change worldSlot iw (address preimage) q =
      (if Kind.exit = Kind.exit ∧ q = ⟨0⟩ then _ else
        worldSlot (c.entryWorld (address preimage)) (address preimage) q) at h
    simpa only [eq_self, true_and, entry_storage] using h
  · rw [hsub, hlogs]
    rfl

#print axioms result_eq_settle
#print axioms failed_deposit_result
#print axioms success_inversion
#print axioms install_storage
#print axioms entry_storage
#print axioms deposit_creation
#print axioms exit_creation

end Eip8282.Audit.Integrator.CreationSettlement
