# Withdrawal count producer — conditional archived-source binding

The new ProtocolWithdrawalCount module proves finite list/slot arithmetic and literal existing Lean credit dispatch. It does not adopt a reference fork or establish Python/SSZ-to-Lean correspondence.

Archived CL: ad0058fd0d34c5dcf504fa51ea2f4f11077b9996. Archived EL: 0cc100eb190b64b23baba72dac0165652eaec252. No download or external request was made.

## Exact source observations

- Capella beacon-chain.md lines 105–115: Withdrawals extends List[Withdrawal] with LIMIT=MAX_WITHDRAWALS_PER_PAYLOAD; line 138 sets that limit to 16. Lines 154–157 retain address and Gwei amount.
- Gloas lines 1807–1833: builder-pending appends only while combined prior/current length is below 15. Lines 1839–1873: builder sweep uses the same combined length limit. Lines 1879–1916 concatenate builder-pending, validator-partial, builder-sweep, validator-sweep in that order. No builder class may be omitted.
- Gloas line 1940 constructs Withdrawals(data=withdrawals), and lines 1992–2017 stage the expected withdrawals. A deferred/empty payload cannot be counted merely because that staging function ran: the credited execution payload must be linked exactly once.
- Capella lines 430–473 show the validator sweep guarding combined length below 16. The cached local corpus does not contain the inherited pending-partial helper implementation; its guarded trace is an explicit hypothesis in the optional four-stage constructor.
- Phase0 lines 473–478 define Slot as Uint64; process_slots lines 1788–1796 requires strict advancement. This is evidence for typed slots, not a complete proof that an accepted canonical EL payload occurs only once per slot.
- Amsterdam fork.py lines 1101–1120 enumerates every withdrawal and calls create_ether(address,U256(amount)*GWEI_TO_WEI). Amsterdam blocks.py Withdrawal.amount is U64. The Lean Item includes all classes without a validator filter. Identical recipients/amounts remain distinct list positions.

## Proven consumer shape

Payload carries a Fin(2^64) beacon slot and an accepted list length <=16. `total_count` derives sum of all payload lengths <=16*2^64 from Nodup slot enumeration. `Dispatch` traverses every item and uses the existing actual AccountMap.increaseBalance credit update. `dispatch_ledger` derives exactly one Ledger.withdrawal increment per item and the actual credit sum. `dispatched_counts` combines this literal dispatch with the complete payload enumeration and independent PoW/migration facts to construct Counts. No aggregate withdrawal-count premise is supplied.

The optional gloasPayload constructor consumes all four actual lists and per-append guard traces. It proves their concatenation bounded, not the reference loop simulation. The generic Payload constructor can instead consume accepted SSZ list validity directly.

## Still-required adapters

1. Decode/transport accepted SSZ Uint64 slot and Gwei fields to the typed Lean fields, and transport accepted Withdrawals validity to the local per-payload length bound.
2. Bind every selected canonical execution payload to its beacon slot, with no duplicate credited payloads; handle Gloas deferred payloads/empty parents and all adopted forks. Strict process_slots alone does not prove this.
3. Bind the exact complete accepted CL list to the EL withdrawal sequence, retaining builders and validator classes without omissions or repetitions.
4. Prove reference create_ether/transaction-state incorporation corresponds to the literal Lean increaseBalance updates, including absent accounts and arithmetic. Dispatch is a concrete Lean operation relation, not an asserted cross-interpreter adapter.
5. Supply PoW count independently; EL block number is Uint, so no EL uint64 width inference is used. Supply complete fork-migration conservation and genesis world binding separately.
6. Histories with other interleaved credits/transactions consume dispatch_ledger per payload inside the root's ledger chronology; the flattened dispatched_counts theorem is a specialized consecutive-dispatch corollary.

## Inspected source SHA256
- `/tmp/eip-funding-sources/consensus-specs-specs-capella-beacon-chain.md` `e68a7653e3bab44d4eae2a5b2e7b962605c166f8e9527c21e7a46a3ef8d63042`
- `/tmp/eip-protocol-sources/consensus-specs-gloas-beacon-chain.md` `10b7decc3dd86a1e4921f8cf49081c87dc528d61631bc83646cb5d6a062c65ce`
- `/tmp/eip-protocol-sources/consensus-specs-phase0-beacon-chain.md` `95bbeca116dfc60ee75c1713d32409e29854de2340a71ee325ff7257f4412483`
- `/tmp/eip-protocol-sources/execution-specs-amsterdam-fork.py` `dd0d069cbd0ba3e60e3f927c0e2d41be40958c6415be039ee29d6074eb2950da`
- `/tmp/eip-funding-sources/execution-specs-src-ethereum-forks-amsterdam-blocks.py` `ec2cdd7fae64861b76c225573aac20be18ddb39e1fb2c2e0015a5cd0c4d2852c`
