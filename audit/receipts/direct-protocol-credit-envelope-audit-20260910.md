# Protocol credit envelope audit — proposed reference, not adopted

No unconditional lifetime funding theorem follows from the cached references alone. A sufficient arithmetic envelope is readily available, but protocol admission/transition adapters and complete intermediate-fork migration coverage remain open. This audit made no external requests, builds, source changes or adoption decisions.

## Sources and scope

Reference EL commit `0cc100eb190b64b23baba72dac0165652eaec252`; CL commit `ad0058fd0d34c5dcf504fa51ea2f4f11077b9996`. Exact local files/hashes appear below. Line references below use filenames from that manifest. The cached corpus contains selected fork files, not the whole fork lineage: an exhaustive assertion that no other fork introduces balance credits is therefore NOT justified.

## Credit classes and exact rules

1. **Genesis allocation**: mainnet asset `execution-specs-src-ethereum-assets-mainnet.json`; exact receipt/data under `audit/receipts/direct-genesis-funding-input-20260910.json`, `GenesisFundingInput.lean`, `GenesisFundingWorld.lean`. Complete 8,893-address sum G=72009990499480000000000000 wei <2^96. This is proposed mainnet input, not an adopted initial world. Genesis loader correspondence and selection remain explicit adapters; current finite arithmetic is not a universal genesis bound.
2. **PoW canonical miner reward, inclusion bonus, and ommer beneficiary reward**: Frontier `fork.py:58,60,516,545-547,581-589`: R=5e18 wei, at most two ommers, each age d in [1,6]; canonical reward R+n*(R//32); each ommer ((8-d)*R)//8. Thus total ≤45R/16 = 14062500000000000000 wei per canonical block, including all ommers and bonus. Byzantium `fork.py:62,597-604` lowers R to3e18; Constantinople same locations lowers to2e18. Aliased beneficiaries do not increase this sum. Paris `fork.py:172,328` rejects ommers; its block processing has no PoW reward producer. Missing: all intervening versions' inherited reward correctness and exact adopted terminal-PoW boundary/count adapter. **Do not derive Npow<2^64 from EL block-number width**: Amsterdam blocks.py:157 says `number: Uint`, not U64. An actual mainnet terminal height or admitted difficulty/terminal-difficulty argument would supply Npow; neither is silently assumed here.
3. **All consensus-to-EL withdrawals**, including full validator, partial/sweep, requested withdrawals and proposed Gloas builder withdrawals/payments: Amsterdam blocks.py:37-62 `Withdrawal.amount: U64`; Amsterdam fork.py:1101-1120 credits `U256(wd.amount)*GWEI_TO_WEI`. Every credit ≤(2^64-1)*10^9 wei, without proving CL issuance conservation. Capella lines98-115,138,154-157 define Uint64 index, Withdrawals list cap16, Gwei amount; phase0 lines376,473 define Gwei/Slot as Uint64. Capella lines429-473,480-543 computes expected withdrawals, debits validator balance and advances index. Gloas lines1807-1873 adds builder queue/sweep with cap-minus-one budgets; lines1879-1916 concatenates builder, partial, builder sweep, validator sweep; lines1992-2017 applies/debits and records expected payload withdrawals. These builder classes MUST be included, not treated as ordinary validator issuance only. Missing: inherited Electra helpers/full Gloas payload validation linkage and cardinality proof for the final concatenated list, one accepted execution payload per increasing canonical slot, SSZ uint64/no-wrap semantics. Phase0 process_slots:1788-1796 provides strict advancing input slot, but alone is not the full payload uniqueness theorem. EL process_withdrawals itself does not impose the CL list cap.
4. **Fork irregular transitions**: DAO fork.py:79-108 invokes `apply_dao`; cached file does not contain its implementation. Its transfer/conservation must be established from that helper, including complete target list and alias behavior, not assumed from a prose description. Amsterdam fork.py:172-192 `apply_fork` is identity, so it introduces no direct upgrade credit at this pin. Missing: every intermediate fork apply_fork/state override (including system-contract installation and any balance-preservation behavior), and any proposed Amsterdam special-credit change outside this exact source. No such additional credit is found in the cached Amsterdam fork body, but absent files prevent a complete lineage exclusion.
5. **Balance increments that are NOT independent issuance**: transaction refund and priority fee use create_ether (Amsterdam fork.py:1005-1006), paired with actual gas debit (964-967), and must be represented as a conserving transaction step. Blob/base fees burn; value/CALL/CREATE/SELFDESTRUCT redistribution is not fresh external credit. Deposits into consensus leave EL balances in the deposit contract; nevertheless each later withdrawal is safely counted as fresh EL credit in this coarse envelope. CL rewards/penalties, builder bids and consolidation affect EL only when included in withdrawals; do not double-count them separately. Amsterdam system transaction uses value0 (fork.py:759-761); this alone does not prove arbitrary runtime conservation—use actual execution semantics. Proposed system builder-deposit/exit calls (904,916) are request-producing calls, not another explicit create_ether in this file.

## Honest arithmetic proposal

For admitted finite prefix H, let Npow be its canonical premerge blocks and W be the number of all accepted withdrawal items (including builders). Let S be the SUM OF ACTUAL positive balance credits from any independently audited fork irregular transition, not a maximum-world-wealth premise. Then

`worldFunds(H) ≤ G + 14062500000000000000 * Npow + (2^64-1)*10^9 * W + S`.

A producer can derive `W ≤ 16*2^64` from the complete CL cardinality and strictly increasing uint64 slot/payload correspondence. This deliberately ignores index monotonicity, avoiding an unjustified lifetime index wrap argument. If an adopted premerge-boundary producer derives `Npow ≤ 2^64`, and all fork migrations are conserving (S=0), the explicit envelope is

`5444517870994422753655458393319438037440000000000` wei `< 2^163 < fundingCeiling`.

Checked with Python integers: `True`. fundingCeiling is `76059800903738432429721259523001950250726052916847211303159755524395288041` wei. This arithmetic is a reproducible calculation, not a new kernel proof. More generally retain symbolic Npow and S and prove their operation-derived sum below the displayed ceiling. No finite universal lifetime bound follows if Npow or unclassified S is left unbounded. The existing receipt's coarse/flexible supply arithmetic must not be promoted to protocol theorem until these count/credit facts are linked.

## Exact consumers and missing adapters

- `FundingHistory.lean:36-38` credit constructor counts actual `amount.toNat`; `trace_funds:58` and `message_value_lt:72` consume linked actual history and `worldFunds initial+credits<fundingCeiling`. Map each withdrawal/reward to these concrete credits, retaining order/world and proving actual external create_ether matches the pinned Lean credit update (including overflow/absence behavior).
- `TransactionFunding.result_equation`, transaction conservation and refund settlement must account for refund/tip increments once, paired to debit. Proposed Amsterdam gas/state-gas settlement differs from the pinned Lean evaluator; require a version-specific correspondence, not import by name.
- Add protocol-derived reward-list and withdrawal-list sum lemmas, a canonical prefix credit ledger, and fork-migration conservation/explicit-credit lemmas. Root owns composition; protocol owner supplies admission/fork/payload facts; funding owner proves arithmetic and actual-step adapters. Preserve genesis/fork adoption as user decisions.
- Public queue provenance and SYSTEM scheduling are separate; this memo does not discharge them.

## Exact cached source manifest

- `/tmp/eip-funding-sources/sources.json` SHA256 `f2bdf48b022d3ae7800a7726053290af1a55a03eeefe1fc2f193e7df185cbced`
- `/tmp/eip-funding-sources/consensus-specs-specs-capella-beacon-chain.md` SHA256 `e68a7653e3bab44d4eae2a5b2e7b962605c166f8e9527c21e7a46a3ef8d63042`
- `/tmp/eip-funding-sources/execution-specs-src-ethereum-assets-mainnet.json` SHA256 `48bb73806f4ed8f0e4f869cb0bc7ba2e1e5724ceb08c9ec079170dfd63042d65`
- `/tmp/eip-funding-sources/consensus-specs-specs-fulu-beacon-chain.md` SHA256 `0e72312417d1df6f7aac14f731bb6bd71a3ef2715ced68e0b039d7622abc4490`
- `/tmp/eip-funding-sources/execution-specs-src-ethereum-forks-amsterdam-blocks.py` SHA256 `ec2cdd7fae64861b76c225573aac20be18ddb39e1fb2c2e0015a5cd0c4d2852c`
- `/tmp/eip-funding-sources/execution-specs-src-ethereum-forks-constantinople-fork.py` SHA256 `139b60c76f18068145d6d548b8e1f9228385fb145b4f6df942758ed0fa772efc`
- `/tmp/eip-funding-sources/execution-specs-src-ethereum-genesis.py` SHA256 `e22eccebf3404e832245633ff88da4dc304ada33198fbf05d8bab50445af0e3c`
- `/tmp/eip-funding-sources/execution-specs-src-ethereum-forks-dao_fork-fork.py` SHA256 `83d0dff4f9802f72791d206426cd29504b2a841eed9bd168e96b7c68c7addfa8`
- `/tmp/eip-funding-sources/execution-specs-src-ethereum-forks-byzantium-fork.py` SHA256 `6b593d3bb31b5ee8f2bf9f9745b2a90af24e28ccd716fd3bd012de8f407ce90b`
- `/tmp/eip-funding-sources/execution-specs-src-ethereum-forks-frontier-fork.py` SHA256 `636a8111fa4a60bf793faaadc620715a75ec39ca4c9434db42bedf4236f6d138`
- `/tmp/eip-funding-sources/execution-specs-src-ethereum-forks-paris-fork.py` SHA256 `2d87c6527d6e5e8d0ec5cfbe51da4e2ea39d7e6c6194ad5316b96d0b8789dacd`
- `/tmp/eip-funding-sources/arithmetic.json` SHA256 `4a925028908c914f90829177f155b45a6e14640e035ac6c3a4c26cef68383131`
- `/tmp/eip-protocol-sources/execution-specs-amsterdam-fork.py` SHA256 `dd0d069cbd0ba3e60e3f927c0e2d41be40958c6415be039ee29d6074eb2950da`
- `/tmp/eip-protocol-sources/metadata.json` SHA256 `fd1162720e236067c95a9d2c0e68298f810cde1498b200671129261f965242d6`
- `/tmp/eip-protocol-sources/consensus-specs-phase0-beacon-chain.md` SHA256 `95bbeca116dfc60ee75c1713d32409e29854de2340a71ee325ff7257f4412483`
- `/tmp/eip-protocol-sources/consensus-specs-gloas-beacon-chain.md` SHA256 `10b7decc3dd86a1e4921f8cf49081c87dc528d61631bc83646cb5d6a062c65ce`
