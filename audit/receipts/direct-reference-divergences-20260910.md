# Reference transport divergences and impact

These findings compare EVMYulLean b62586650b4f96cc6da25f36574aaa8f329a6420 with the proposed execution-specs Amsterdam source 0cc100eb190b64b23baba72dac0165652eaec252. They do not adopt that fork or change any public guarantee. Source bodies and component reviews are retained in the reference-operations bundle. Source transcription and actual Python/numeric-library interpretation remain distinct obligations.

## Truncated PUSH

For bytes `61 01` at PC0, the pinned decoder produces PUSH2 value1; the reference right-pads the missing immediate byte and produces256. The new kernel counterexample refutes arbitrary-bytecode decoder equality. The five fixed images are checked separately for complete PUSH spans and compatible jump scanning.

Functional impact: a foreign contract using a truncated immediate can branch, compute calldata or choose a call value differently in the two evaluators. Therefore an arbitrary foreign call tree cannot be transported by asserting identical whole-world execution. Fixed protected-runtime decoder checks do not close this foreign-code obligation.

Economic impact: a foreign computation may change amounts or resource consumption, so funding histories must be extracted from actual reference transfers/admission or a separately proved adequate relation. The counterexample itself transfers no funds and establishes no loss.

Security impact: this is a limitation of the current proof model's general applicability, not evidence of an exploit in the two fixed EIP bytecodes. Reference protected-call occurrence, foreign-state framing and ledger producers remain open. No author-intent statement can discharge them.

## Sparse versus rounded memory and terminal PC

A pinned memory write can retain a shorter physical byte array than the reference's eager zero extension. MSTORE8 at0 may have physical length1 versus32. RETURN/STOP/EOF also differ in internal PC or fuel conventions. These refute raw-machine equality, including raw memory arrays and terminal PC.

The new memory composition compares every zero-extended byte, derives actual MSTORE/MSTORE8 post-coherence and reference rounded size, and proves RETURN output equality with explicit host-length bounds. It does not assume a desired post-memory relation. Functional return bytes can agree despite representation differences; raw equality was unnecessarily strong. Economic memory cost must use allocated capacity, not physical sparse length. Security still requires actual trace producers for access bounds and source instruction dispatch; representation lemmas alone do not prove runtime success or absence of OOG.

The initial resource investigation incorrectly treated RETURN length as the maximum touched byte. Deposit's last full MSTORE touches11784 bytes although output length is11776; Exit touches1104 although output length is1088. The corrected capacities are369 and35 words. Kernel arithmetic gives C(369)=1372 and C(35)=107. A subsequent handwritten1373 was also rejected. Relative to the original1368/104 estimates, the increases are4/3 gas. Conditional envelopes18,941,372/1,930,107 remain below30M, but actual trace shape and all reference charge/error guards must still be proved; these numbers alone are not a liveness result.

## Value transfer and logs

Pinned call entry credits before debiting; reference move_ether debits before reading/crediting the recipient. Zero transfers are skipped by the source. The new account-map proofs derive full pointwise lookup equality, including aliases, account absence and zero value, with checked addition from the same literal funding ledger. Apparent CALLVALUE is distinct from the transfer amount when should_transfer_value is false.

Reference synthetic Transfer logs are emitted at SYSTEM, with three topics, under enabled/nonzero/nonalias guards. Full raw log equality for paid calls is not asserted. The existing all-topics projection at each protected address is preserved; no LOG0-only filter or spec weakening is introduced. Actual log placement and error settlement remain source trace obligations. Economically, missing call-kind or checked-arithmetic bindings could invalidate accounting; the local equations do not replace their producers.

## Storage, original state and gas refunds

Reference current storage reads layer transaction writes over block writes over prestate; an explicit written zero overrides a lower nonzero value. Original storage additionally checks created_accounts. Snapshot restore restores current writes but retains shared created-account/BAL-read metadata. The pinned SSTORE original-state view and modular refund word do not generally equal the reference original view and signed dual-pool refund accounting. A missing owner also differs: reference set_storage asserts existence, while pinned SSTORE leaves the state unchanged.

The new storage view proves canonical key injectivity, current write/read transport under an existing owner, and current-slot rollback/commit equations. It deliberately does not equate original/refund/full-state objects. Installed-owner and actual state-layer producers remain required. Source-shaped SSTORE charging includes sentry-before-refunds and execution-before-state charging, with conservative sufficient local margins independent of refunds.

Functional storage values can be related on successful protected execution, but failures cannot be matched by simply giving the pinned evaluator a larger gas budget. Economic refund, spill and final transaction/block accounting require direct reference proofs. Security claims about admitted histories and mandatory SYSTEM success remain conditional until those producers and the selected protocol context are closed.

No external message, publication, dependency-pin change or normative adoption accompanies this record. Existing fee1608/1620/2893 and inhibition findings retain their separate domains and receipts.
