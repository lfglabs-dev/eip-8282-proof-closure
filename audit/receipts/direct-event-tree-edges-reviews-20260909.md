# Structural event trees and execution-wrapper edge reviews

These are structural and wrapper foundations, not a complete actual call-tree
extraction or universal nested-event debit theorem.

## Frozen source bindings

- `Eip8282/Audit/Integrator/EventTree.lean`: `a6393ed6adb27caa2e1e282b3692e6ba40fcd1715021aa2ea196ec67569d36c4`
- `Eip8282/Audit/Integrator/WrapperEventDebit.lean`: `500678f48cd7259159ab6ba448e267df89dbd4f5c3c7230e3a335b48251683ee`

---

# Independent review: EventTree

CLEAN. Root integrator review, independent of the author.
Source SHA256: a6393ed6adb27caa2e1e282b3692e6ba40fcd1715021aa2ea196ec67569d36c4.
Read the entire structural module. /tmp/eip-EventTree-3.log completed with exit0;
all ten printed projections use no axioms or only propext/Quot.sound. The unused
Nat.add_left_comm simp warning is cosmetic and retained in the frozen source.

The tree has one possible marked local root, exactly one child subtree and
one continuation subtree. Address generation is fixed: [] for a marked root,
false::address for child occurrences and true::address for continuation.
Root/child/continuation disjointness and cons-prefix injection therefore need
no assumptions on event payloads, PC, local fuel or uniqueness of subtrees.
Length=count and recursive Nodup agree with that exact occurrence list;
repeated structurally equal subtrees still have different prefixed addresses.
Membership lemmas recover the correct branch and fixed-path prefix injection
preserves uniqueness under that SAME prefix.

The module intentionally provides no execution certificate, event-to-bytecode
binding, call-frame extraction or gas bound. Arbitrary unequal frame prefixes
are not asserted to make arbitrary suffixed paths disjoint. A future actual
trace and audited-call injection must establish the relevant ownership and
structural positions; the tree alone cannot discharge those semantics.

---

# Independent review: WrapperEventDebit

Verdict: CLEAN as all-outcome residual/charge transport edges.

Complete frozen source reviewed at SHA256 `500678f48cd7259159ab6ba448e267df89dbd4f5c3c7230e3a335b48251683ee`. `/tmp/eip-WrapperEventDebit-2.log` reports only propext, Classical.choice, Quot.sound for all six theorems. Two unused `he` simp-argument warnings are cosmetic. No edits or builds were performed.

xiResidual projects the actual gas from both success and REVERT and uses0 only as the accounting residual of an error. entry matches the literal fresh Ξ machine, retaining the separate original-world snapshot, code/environment, current account map, substate, created set, block context, gas, and default remaining machine fields. xi_residual proves equality for Ξ(fuel+1) and its actual X(fuel) at D_J env.code0; splitting actual X covers both execution results and every error without any successful-outcome premise or alternate entry state.

theta_residual rewrites the exact MessageCall.result_eq_settle identity. Propagated OutOfFuel has residual0; caught other execution errors return false with actual gas0; REVERT returns its actual gas; success retains the same gas, even when the world/substate empty-map fallback selects the original journal. Thus no rollback branch creates residual gas. In fact the code Θ projection is equal in these cases, but the weaker <= statement is valid and sufficient. The Context binds Θ(c.fuel+1) to the SAME Ξ(c.fuel) execution after actual entry transfer; it is not an arbitrary supplied execution result.

lambda_residual is attached to the SAME actual selected init execution at the address derived from the actual successful preimage. It uses the frozen exact Lambda settlement identity. Propagated/caught errors have residual0; REVERT keeps its gas. Successful init either fails the real code-deposit checks and returns0 or returns UInt256.ofNat(initGasNat - depositCost). Nat subtraction and modulo cannot increase init gas, so the bound does not require assuming successful code installation, a code-length fit, fee sufficiency or desired poststate. Collision-selected INVALID init and other selected code are part of c.execution itself; no user init is substituted for the actual selected code.

lambda_no_preimage unfolds the literal Lambda address-encoding step. A none preimage prevents actual init execution and results in accounting residual0. It does not pretend to transport a nonzero descendant count through that branch: the theorem only gives a residual equation. A future event certificate must assign it an empty subtree.

theta_charge and lambda_charge preserve an EXPLICIT independently established child residual+charge<=input bound by adding the same charge to the wrapper residual inequality. They neither assume a parent postcondition nor derive the child count/global charge. No child trace is duplicated, erased by a rollback, or reconstructed by these scalar theorems; actual trace attachment remains separate. Arbitrary finite child fuel is retained in the Context, including child fuel0, while raw wrapper fuel0 is not packaged by these positive-wrapper Context statements.

Scope accurately excludes raw precompile Θ adapters, raw fuel0 wrapper cases, full call-tree extraction, event-marker semantics/global distinctness and universal nested aggregate charging. Those still need to instantiate this induction-edge API. The error residual0 convention is not a claim of an actual gas-returning OutOfFuel endpoint. No no-wrap, successful-parent/child, supply, funding, queue or gas-liveness assumption is hidden in these theorems. No blocking finding.

Compared with literal pinned Ξ and the previously independently reviewed literal Θ/Lambda semantics through their unchanged exact settlement identities. Checked current residual definitions and relevant complete helpers. All dependency hashes below retain reviewed values.

## Source bindings

- `Eip8282/Audit/Integrator/WrapperEventDebit.lean`: `500678f48cd7259159ab6ba448e267df89dbd4f5c3c7230e3a335b48251683ee`
- `Eip8282/Audit/Integrator/RecursiveEventDebit.lean`: `5f2e5192fa26543e30eb470773417ebba0c57ed3a5947ec5a90a454ffd39a9b3`
- `Eip8282/Audit/Integrator/FrameEvents.lean`: `d5f2ff9126b3a054f5f63b71d4dbaf9a2d79070ec6a7ac80ddd2a54963c32f66`
- `Eip8282/Audit/Integrator/MessageCall.lean`: `3f16088bd13b6f6fdf13de417e4843f08e9dcd61fa6dfdddfc6342c250ccf342`
- `Eip8282/Audit/Integrator/CreationSettlement.lean`: `d95b28f2a46daf588a2aaf15e8a8f77fc28b075116e5f2395360e73152383820`
- `.lake/packages/evmyul/EvmYul/EVM/Semantics.lean`: `8b49f1aee609ce888041ba9e7253bbe55d06fda136252bc46d4e006755110f4b`
