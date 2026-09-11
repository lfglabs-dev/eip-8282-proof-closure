import Eip8282.Audit.Integrator.SystemSpec

/-!
# Discharge the message-call empty-world fallback

The pinned Θ uses boolean map equality to test its successful result against
the empty map. An account lookup suffices to refute that test: the map equality
implementation rejects unequal sizes before comparing any account values.
No lawful boolean equality instance for accounts is needed or assumed.
-/

namespace Eip8282.Audit.Integrator.WorldNonempty

open EvmYul

/-- A successful lookup makes the map's structural size nonzero. -/
theorem size_ne_zero_of_get_some {world : AccountMap .EVM}
    {address : AccountAddress} {account : Account .EVM}
    (h : world.get? address = some account) : world.size ≠ 0 := by
  have hc : world.contains address = true := by
    rw [Std.TreeMap.contains_eq_isSome_getElem?]
    change (world.get? address).isSome = true
    rw [h]
    rfl
  have he := Std.TreeMap.isEmpty_eq_false_of_contains hc
  rw [Std.TreeMap.isEmpty_eq_size_eq_zero] at he
  simpa using he

/-- The boolean test used by Θ is false whenever an account exists. This
proof depends only on its first, size-based branch, not on account equality. -/
theorem beq_empty_false_of_get_some {world : AccountMap .EVM}
    {address : AccountAddress} {account : Account .EVM}
    (h : world.get? address = some account) : (world == ∅) = false := by
  have hs := size_ne_zero_of_get_some h
  change (if world.size ≠ 0 then false else _) = false
  rw [if_pos hs]

/-- Owner preservation supplies exactly the nonempty-world premise required
by `MessageCall.success_commits_world` and `CallBridge.commits_endpoint`. -/
theorem beq_empty_false_of_hasOwner {st : EvmYul.State .EVM}
    (h : SystemSpec.HasOwner st) : (st.accountMap == ∅) = false := by
  obtain ⟨account, haccount⟩ := h
  exact beq_empty_false_of_get_some haccount

#print axioms beq_empty_false_of_get_some
#print axioms beq_empty_false_of_hasOwner

end Eip8282.Audit.Integrator.WorldNonempty
