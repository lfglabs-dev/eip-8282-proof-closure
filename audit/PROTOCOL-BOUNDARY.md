# Protocol resources: reference facts and remaining formal bindings

The bytecode/EIP/EVMYulLean pins in `audit/artifacts.lock.json` remain unchanged.
The sources below are immutable references retrieved on 9 September 2026 for
checking the proposed protocol-domain argument. They do not silently select a
new normative fork, prove correspondence with the pinned evaluator, or resolve
the inhibition/upgrade ambiguity.

The consensus reference uses a 64-bit Slot, requires increasing block slots,
and gives payload block number, gas limit and gas used 64-bit types. Those are
potential inputs to a finite canonical-history bound. [Phase0 reference](https://github.com/ethereum/consensus-specs/blob/ad0058fd0d34c5dcf504fa51ea2f4f11077b9996/specs/phase0/beacon-chain.md),
[Gloas payload reference](https://github.com/ethereum/consensus-specs/blob/ad0058fd0d34c5dcf504fa51ea2f4f11077b9996/specs/gloas/beacon-chain.md).

The execution reference processes transactions before general-purpose requests.
Its request handler invokes each builder contract once with empty calldata;
checked system calls reject absent code or execution failure. Its configured
system gas allowance is 30 million. These observations concern this reference
version; upgrade orchestration and target-bytecode identity need separate
binding. [Amsterdam execution reference](https://github.com/ethereum/execution-specs/blob/0cc100eb190b64b23baba72dac0165652eaec252/src/ethereum/forks/amsterdam/fork.py).

File hashes and repository commits are recorded in
`receipts/protocol-reference-sources-20260909.json`.

## What the arithmetic theorem proves

`Integrator/ResourceBounds` represents a history as distinct 64-bit slots, each
with 64-bit accounted gas. Given `appends ≤ accounted gas` in each block, it
proves total appends are below 2^128. If actual tail/count/excess are bounded by
that total, storage windows and control sums fit 256-bit arithmetic. This bound
does not imply fee-recurrence products fit: the fee-domain obligation is much
stronger and remains separate.

The resource bound is conditional on real accounting inputs, not desired
post-state equations. It is not yet a `ReachableProtocol` theorem.

## Bindings still needed

* Establish that the selected consensus/execution version supplies the typed,
  distinct canonical slots and that its payload gas bounds cover the call
  histories being audited, including any supported activation or upgrade path.
* Connect locally successful append events to nonduplicated transaction gas accounting.
  Account for nested calls, failed enclosing frames, and refund limits. A
  Include append events later reverted by an ancestor: their gas is spent and
  their temporary states also need bounds. A positive opcode cost alone is not
  a complete block-accounting proof.
* Prove actual-state induction: HEAD≤TAIL≤budget, count≤budget and, when
  enabled, excess+count≤budget, starting from installed initialization. The
  budget counts locally successful appends monotonically across ancestor rollback.
  An assumed `AppendFits` in a history constructor would not discharge this.
* Bind caller authorization and system scheduling. An arbitrary raw Θ input
  can select SYSTEM; the evaluator alone is not consensus admission.
* Establish the economic domain needed by the natural tariff, or obtain an
  explicit report decision for the remaining arithmetic divergence. Do not
  replace the agreed mathematical clauses with word arithmetic alone.

The current evaluator's `BlockHeader` stores several fields as unrestricted
Nat. Its type alone therefore does not supply the 64-bit protocol bound above.

## Next implementation steps identified by source review

`receipts/direct-protocol-next-review-20260909.md` inspects the pinned evaluator
and identifies the missing accounting chain: accepted Z/step gas equations,
actual LOG0 cost, distinct append occurrences in the call tree, stipend and
returned gas, transaction refund limits, and the actual block gas total. A sum
of independent Θ input budgets is not a block-accounting bridge.

`AccountedState` implements the structural scalar invariant and its preservation
by the already proved append/SYSTEM storage maps. It derives AppendFits before
applying the append postcondition. This is a local preservation result, not yet
an extraction of every relevant event from a valid initialized execution history.
