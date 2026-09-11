import Eip8282.Audit.Integrator.ReferenceOrdinaryBlockStorage

/-! Account branches of the pinned update_builder_from_tx617-660. Balance
changes replace the first equal index; nonce changes retain its maximum, unlike
balance/storage changes. Code changes resolve the post hash through get_code.
This is a successful functional projection: None does not assert rollback of
partially mutated Python builders. The final consumer derives conversion and
unchanged-code conditions from actual execution and fresh initial writes. -/
namespace Eip8282.Audit.Integrator.ReferenceOrdinaryBlockAccess
open EvmYul EvmYul.EVM ReferenceSourceValueTransfer
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

structure Change (Value : Type) where
  index : UInt32
  value : Value

def replace {Value : Type} (index : UInt32) (value : Value) : List (Change Value) → List (Change Value)
  | [] => [⟨index,value⟩]
  | c::rest => if c.index = index then ⟨index,value⟩::rest else c::replace index value rest

/-- add_nonce_change440-456 preserves the highest same-index nonce. -/
def highest (index : UInt32) (value : UInt64) : List (Change UInt64) → List (Change UInt64)
  | [] => [⟨index,value⟩]
  | c::rest => if c.index = index then
      (if c.value < value then ⟨index,value⟩ else c)::rest
    else c::highest index value rest

structure Builder where
  storage : ReferenceSystemBlockAccess.Builder
  balances : AccountAddress → List (Change UInt256)
  nonces : AccountAddress → List (Change UInt64)
  codes : AccountAddress → List (Change ByteArray)

noncomputable def addBalance (b : Builder) (a : AccountAddress) (value : UInt256) : Builder := by
  classical
  exact {b with
    storage := {b.storage with accounts := insert a b.storage.accounts}
    balances := fun x => if x = a then replace b.storage.index value (b.balances x) else b.balances x}

noncomputable def addNonce (b : Builder) (a : AccountAddress) (value : UInt64) : Builder := by
  classical
  exact {b with
    storage := {b.storage with accounts := insert a b.storage.accounts}
    nonces := fun x => if x = a then highest b.storage.index value (b.nonces x) else b.nonces x}

noncomputable def addCode (b : Builder) (a : AccountAddress) (value : ByteArray) : Builder := by
  classical
  exact {b with
    storage := {b.storage with accounts := insert a b.storage.accounts}
    codes := fun x => if x = a then replace b.storage.index value (b.codes x) else b.codes x}

noncomputable def one {Hash Error : Type} [DecidableEq Hash] (emptyHash : Hash)
    (parent : Parent Hash) (codeParent : ReferenceCodeAccountPresence.CodeParent Hash Error)
    (codeWrites : Hash → Option ByteArray) (a : AccountAddress) (value : Option (ReferenceSourceValueTransfer.Account Hash))
    (builder : Builder) : Option Builder :=
  let pre := (ReferenceAccountLookup.parentRead parent a).getD (empty emptyHash)
  let post := value.getD (empty emptyHash)
  let balance := if pre.balance = post.balance then builder else addBalance builder a post.balance
  let nonce := if pre.nonce = post.nonce then some balance else
    (ReferenceOrdinaryBlockNonce.checkedNonce post.nonce).map (addNonce balance a)
  nonce.bind fun b => if pre.codeHash = post.codeHash then some b else
    match ReferenceCodeAccountPresence.getCode emptyHash codeParent codeWrites post.codeHash with
    | .error _ => none
    | .ok code => some (addCode b a code)

noncomputable def update {Hash Error : Type} [DecidableEq Hash] (emptyHash : Hash)
    (parent : Parent Hash) (codeParent : ReferenceCodeAccountPresence.CodeParent Hash Error)
    (codeWrites : Hash → Option ByteArray) :
    List (AccountAddress × Option (ReferenceSourceValueTransfer.Account Hash)) → Builder → Option Builder
  | [],b => some b
  | (a,value)::rest,b => (one emptyHash parent codeParent codeWrites a value b).bind
      (update emptyHash parent codeParent codeWrites rest)

noncomputable def entries {Hash : Type} (tx : ReferenceAccountLookup.Tx (ReferenceSourceValueTransfer.Account Hash))
    (addresses : List AccountAddress) : List (AccountAddress × Option (ReferenceSourceValueTransfer.Account Hash)) :=
  addresses.dedup.filterMap (fun a => (tx.writes a).map (fun value => (a,value)))

def Valid {Hash : Type} (emptyHash : Hash) (parent : Parent Hash)
    (pair : AccountAddress × Option (ReferenceSourceValueTransfer.Account Hash)) : Prop :=
  let pre := (ReferenceAccountLookup.parentRead parent pair.1).getD (empty emptyHash)
  let post := pair.2.getD (empty emptyHash)
  (pre.nonce = post.nonce ∨ ∃ value, ReferenceOrdinaryBlockNonce.checkedNonce post.nonce = some value) ∧
  pre.codeHash = post.codeHash

theorem one_total {Hash Error : Type} [DecidableEq Hash] (emptyHash : Hash)
    (parent : Parent Hash) (codeParent : ReferenceCodeAccountPresence.CodeParent Hash Error)
    (codeWrites : Hash → Option ByteArray) (a : AccountAddress) (value : Option (ReferenceSourceValueTransfer.Account Hash))
    (builder : Builder) (valid : Valid emptyHash parent (a,value)) :
    ∃ final, one emptyHash parent codeParent codeWrites a value builder = some final := by
  unfold one
  dsimp only
  by_cases same : ((ReferenceAccountLookup.parentRead parent a).getD (empty emptyHash)).nonce =
      (value.getD (empty emptyHash)).nonce
  · simp only [if_pos same,Option.bind_some,if_pos valid.2]
    exact ⟨_,rfl⟩
  · obtain ⟨next,hn⟩ := valid.1.resolve_left same
    simp only [if_neg same,hn,Option.map_some,Option.bind_some,if_pos valid.2]
    exact ⟨_,rfl⟩

theorem one_index {Hash Error : Type} [DecidableEq Hash] {emptyHash : Hash}
    {parent : Parent Hash} {codeParent : ReferenceCodeAccountPresence.CodeParent Hash Error}
    {codeWrites : Hash → Option ByteArray} {a : AccountAddress} {value : Option (ReferenceSourceValueTransfer.Account Hash)}
    {builder final : Builder} (actual : one emptyHash parent codeParent codeWrites a value builder = some final) :
    final.storage.index = builder.storage.index := by
  unfold one at actual
  obtain ⟨middle,nonce,finished⟩ := Option.bind_eq_some_iff.mp actual
  have middleIndex : middle.storage.index = builder.storage.index := by
    split at nonce
    · cases nonce
      split <;> rfl
    · obtain ⟨n,_,hn⟩ := Option.map_eq_some_iff.mp nonce
      subst middle
      change (if _ then _ else _ : Builder).storage.index = _
      split <;> rfl
  split at finished
  · cases finished
    exact middleIndex
  · split at finished
    · contradiction
    · cases finished
      exact middleIndex

theorem update_total {Hash Error : Type} [DecidableEq Hash] (emptyHash : Hash)
    (parent : Parent Hash) (codeParent : ReferenceCodeAccountPresence.CodeParent Hash Error)
    (codeWrites : Hash → Option ByteArray) {items : List (AccountAddress × Option (ReferenceSourceValueTransfer.Account Hash))}
    (valid : ∀ pair ∈ items, Valid emptyHash parent pair) (builder : Builder) :
    ∃ final, update emptyHash parent codeParent codeWrites items builder = some final := by
  induction items generalizing builder with
  | nil => exact ⟨builder,rfl⟩
  | cons pair rest ih =>
    obtain ⟨middle,first⟩ := one_total emptyHash parent codeParent codeWrites pair.1 pair.2 builder (valid pair (by simp))
    obtain ⟨final,last⟩ := ih (fun pair member => valid pair (List.mem_cons_of_mem _ member)) middle
    exact ⟨final,by simp only [update,first,Option.bind_some,last]⟩

theorem update_index {Hash Error : Type} [DecidableEq Hash] {emptyHash : Hash}
    {parent : Parent Hash} {codeParent : ReferenceCodeAccountPresence.CodeParent Hash Error}
    {codeWrites : Hash → Option ByteArray} {items : List (AccountAddress × Option (ReferenceSourceValueTransfer.Account Hash))}
    {builder final : Builder} (actual : update emptyHash parent codeParent codeWrites items builder = some final) :
    final.storage.index = builder.storage.index := by
  induction items generalizing builder with
  | nil => cases actual; rfl
  | cons pair rest ih =>
    obtain ⟨middle,first,last⟩ := Option.bind_eq_some_iff.mp actual
    exact (ih last).trans (one_index first)

theorem entries_sound {Hash : Type} (tx : ReferenceAccountLookup.Tx (ReferenceSourceValueTransfer.Account Hash))
    (addresses : List AccountAddress) (pair : AccountAddress × Option (ReferenceSourceValueTransfer.Account Hash))
    (member : pair ∈ entries tx addresses) : tx.writes pair.1 = some pair.2 := by
  obtain ⟨a,_,mapped⟩ := List.mem_filterMap.mp member
  obtain ⟨value,write,rfl⟩ := Option.map_eq_some_iff.mp mapped
  exact write

theorem entries_unique {Hash : Type} (tx : ReferenceAccountLookup.Tx (ReferenceSourceValueTransfer.Account Hash))
    (addresses : List AccountAddress) : ((entries tx addresses).map Prod.fst).Nodup := by
  classical
  unfold entries
  rw [List.map_filterMap]
  apply List.Nodup.filterMap ?_ (List.nodup_dedup addresses)
  intro a a' address ha ha'
  simp only [Option.map_map,Function.comp_def] at ha ha'
  cases hw : tx.writes a with
  | none => simp [hw] at ha
  | some value =>
    cases hw' : tx.writes a' with
    | none => simp [hw'] at ha'
    | some value' =>
      simp only [hw,hw',Option.map_some,Option.mem_some_iff] at ha ha'
      exact ha.trans ha'.symm

#print axioms one_total
#print axioms one_index
#print axioms update_total
#print axioms update_index
#print axioms entries_sound
#print axioms entries_unique
end Eip8282.Audit.Integrator.ReferenceOrdinaryBlockAccess
