# Next concrete CALL gas bridge

Read-only analysis of pinned EVMYulLean b62586650b4f96cc6da25f36574aaa8f329a6420. No source changes or builds.

Sources read: EvmYul/EVM/Gas.lean Caccess/Cnew/Cxfer/Cextra/Cgascap/Ccallgas/Ccall/C'; EvmYul/EVM/Semantics.lean call, CALL/CALLCODE/DELEGATECALL/STATICCALL dispatch, X/Z, Xi, Theta and CREATE/CREATE2 gas settlement; MachineStateOps.writeBytes; GasConstants. Existing ActualAppendGas and AppendGasPath provide the audited leaf debit.

## Exact accounting identity

Let P be the parent state before Z, M its actual memory-expansion cost, and Q the state after Z's memory subtraction. For the actual call arguments evaluated on Q, define:

- G = Q.gasAvailable.toNat.
- K = Cgascap(target, recipient, value, requestedGas, Q.accountMap, Q.toMachineState, Q.substate).
- E = Cextra(target, recipient, value, Q.accountMap, Q.substate).
- S = 0 when actual transferred value is zero, otherwise Gcallstipend = 2300.
- B = Ccallgas(...) = K + S, the child's actual input gas.
- R = the actual gas returned by Theta, irrespective of its returned success flag.
- P' = the actual parent state after this CALL instruction.

Actual accepted Z supplies K+E <= G. The call helper computes B BEFORE subtracting K+E. It then runs Theta with UInt256.ofNat B and restores exactly the returned R by word addition:

    P'.gasAvailable = Q.gasAvailable - UInt256.ofNat (K+E) + returnedGas.

The writeBytes and return-data/active-word updates preserve this gas field. CALL's final stack/PC update also preserves it. The step's execLength increment does not affect any callgas argument.

For nonzero value, E includes the 9000 value charge, so S <= E. For zero value S=0. Consequently B <= K+E <= G < UInt256.size: the child's UInt256.ofNat B conversion is exact, derived from accepted Z without a protocol gas-limit bound.

Once the child's actual return theorem gives R <= B, the parent addition also cannot wrap: G-(K+E)+R <= G. Therefore the exact natural identity is:

    P'.gasAvailable.toNat + (B-R) + (E-S) + M
      = P.gasAvailable.toNat.

The stipend must be subtracted from parent overhead. Charging both child consumption B-R and all of E would count 2300 twice for value-carrying calls. The nonnegative residual overhead E-S is still at least the access cost (and at least 6700 plus access/new-account cost for nonzero value).

This identity also covers child REVERT: Theta restores the child's pre-transfer journal but forwards its actual remaining gas R. An exceptional child halt returns R=0; interpreter OutOfFuel is propagated as an error, not converted to a completed call. A later parent REVERT restores storage, not the gas previously spent by its descendants.

## First directly tractable semantic lemma

Implement one generic inversion at EVM.call, before specializing CALL. For arbitrary arguments and states, the following is an exact proposed signature (all names here are already existing semantic types/functions):

    theorem call_child_result_gas
      (fuel cost : Nat) (hashes : List ByteArray)
      (requested source recipient target value apparent inOff inLen outOff outLen : UInt256)
      (permission : Bool) (pre post : EVM.State) (x : UInt256)
      (hgate : value <= (pre.accountMap.get? pre.executionEnv.codeOwner |>.option ⟨0⟩ (·.balance))
        ∧ pre.executionEnv.depth < 1024)
      (hcall : EVM.call (fuel+1) cost hashes requested source recipient target
        value apparent inOff inLen outOff outLen permission pre = .ok (x,post)) :
      ∃ created world returnedGas substate success out,
        Θ fuel hashes pre.createdAccounts pre.genesisBlockHeader pre.blocks
          pre.accountMap pre.σ₀
          (pre.addAccessedAccount (AccountAddress.ofUInt256 target)).substate
          (AccountAddress.ofUInt256 source) pre.executionEnv.sender
          (AccountAddress.ofUInt256 recipient)
          (toExecute .EVM pre.accountMap (AccountAddress.ofUInt256 target))
          (UInt256.ofNat (Ccallgas (AccountAddress.ofUInt256 target)
            (AccountAddress.ofUInt256 recipient) value requested
            pre.accountMap pre.toMachineState pre.substate))
          (UInt256.ofNat pre.executionEnv.gasPrice) value apparent
          (pre.memory.readWithPadding inOff.toNat inLen.toNat)
          (pre.executionEnv.depth+1) pre.executionEnv.header permission
          = .ok (created,world,returnedGas,substate,success,out)
        ∧ post.gasAvailable = pre.gasAvailable - UInt256.ofNat cost + returnedGas

This theorem has no child-gas bound or desired post-state premise. It derives the actual child invocation/result and word gas equation by unfolding the real call helper once, selecting its funded/depth branch, and eliminating its actual Except result. It should be straightforward compared with the opcode-path inversions: writeBytes changes only memory, and the remaining assignments are explicit field updates.

Follow with its denied-entry counterpart: when the real funds/depth gate is false, no Theta execution occurs, the helper refunds exactly UInt256.ofNat B, returns a false call outcome, and has zero descendant append events. Do not insert a synthetic child execution for this branch. Separate OutOfFuel at helper fuel zero.

Then a CALL-specific StepOk inversion supplies the helper input after execLength increment, seven actual operands, and exact helper fuel. EVM.step (k+2) dispatches call (k+1), which dispatches Theta k. From actual XStepAt, accepted_gas supplies cost=C' Q CALL=Ccall(...) and cost<=G. The gate may be split or derived from an observed actual child invocation; it is not an arbitrary proof of successful append.

The small prerequisite arithmetic lemmas are: Ccallgas=cap+stipend, stipend<=Cextra, Ccallgas<=Ccall, and the natural settlement identity under the LOCAL child returned-gas bound. Use toNat_sub_ofNat and toNat_add_of_lt from the existing word arithmetic. No new execution model is needed.

## Summation without double counting

At a recursive CALL, apply the child's inductive theorem to its actual Theta result:

    returnedGas.toNat + childAuditCharge <= childInputGas.toNat.

Here childAuditCharge is derived from the child's actual semantic execution witnesses. It is not supplied as 'sum childgas <= gross'. Substituting it in the identity above yields:

    parentPostGas + childAuditCharge + (E-S) + M <= parentPreGas.

For sequential parent instructions telescope this inequality exactly as XRuns currently telescopes supported local steps. Do NOT charge the full forwarded child input B as irrecoverable gas, and do NOT add both the full parent inclusive debit and child inclusive debits. Charge each actual audited append LOG0 once; its enclosing CALL contributes only residual overhead plus that already-proved child charge.

The audit contracts contain no CALL/CREATE, so successful audited append frames are leaves for this purpose. Their charge can be 919 (uniform lower bound) or their specific919/1847 bound from AppendGasPath. Arbitrary intermediate frames contribute zero local audit events and transmit all descendant audit charges through their actual CALL edges.

A rigorous whole-tree proof must retain actual execution witnesses even when the final world rolls them back. Counts must include successful local audited appends later cancelled by any ancestor REVERT/exception. The accumulator is not reconstructed from committed storage or surviving logs. An observational witness tree extracted from the EXISTING mutual evaluator calls is acceptable; independently defined abstract transitions, or assumed gas domination of that tree, are not.

For generic arbitrary intermediate bytecode this requires a mutual induction that also handles successful, reverting and exceptional execution. A completed REVERT keeps its remaining gas. A non-OutOfFuel exceptional halt returns zero, but the proof must retain the successfully executed prefix and its child audit events. Existing success_trace covers only successful X; an error/revert-prefix extraction is a real additional obligation. Merely proving the CALL success equation does not solve it.

## Other boundary cases to preserve

- CALLCODE shares the same value/stipend accounting but uses the parent's owner as recipient; target for code/access and recipient for new-account cost must not be confused.
- DELEGATECALL and STATICCALL pass actual transfer value0, so no stipend. DELEGATECALL's apparent value may be nonzero: stipend and Cxfer use the actual value parameter, not apparent CALLVALUE.
- Precompile Theta results need their own returnedGas<=inputGas proof for the generic induction; audit-code pinning excludes them only at audited leaves.
- CREATE/CREATE2 can enclose later audit calls. Their real budget/return formula is different and must be separately inverted. They forward L(remaining gas), then settle parent gas using remaining-L(remaining)+returned, while Lambda code deposit may spend additional gas. They cannot be silently folded into CALL accounting or excluded from a claimed all-transactions result.
- Refunds affect later Upsilon settlement, not the gasAvailable restored by REVERT. Use the separate refund theorem only after gross execution accounting is established.
- No protocol funding, supply or global budget bound has been derived by this read-only analysis.
