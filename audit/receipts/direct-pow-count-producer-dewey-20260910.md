# Proposed mainnet PoW count producer — independent read-only audit

The TTD route works conditionally and removes any reliance on EL block-number width. With verified T=58750000000000000000000 and minimum difficulty m=131072, a canonical chain ending at its first terminal crossing has at most **448226928710937500** non-genesis PoW reward blocks, strictly below 2^64=18446744073709551616. This is a proposed arithmetic/ancestry interface, not a new Lean theorem or adopted protocol baseline. No builds or repository modifications were performed.

The exact proposed EL pin is `0cc100eb190b64b23baba72dac0165652eaec252`; CL pin `ad0058fd0d34c5dcf504fa51ea2f4f11077b9996`. Fresh immutable primary-source bytes and a SHA256/URL manifest are in `/tmp/eip-pow-count-sources/manifest.json`. Existing cached references were not silently treated as freshly verified pins.

## Verified transition rule and override

[Pinned mainnet config](https://raw.githubusercontent.com/ethereum/consensus-specs/ad0058fd0d34c5dcf504fa51ea2f4f11077b9996/configs/mainnet.yaml), lines 17–20 (one-based), sets TTD=58750000000000000000000, terminal block hash zero and activation epoch 2^64−1. Mainnet selection remains Thomas's decision.

[Pinned Bellatrix fork choice](https://raw.githubusercontent.com/ethereum/consensus-specs/ad0058fd0d34c5dcf504fa51ea2f4f11077b9996/specs/bellatrix/fork-choice.md), lines 141–171, requires terminal TD≥T and parent TD<T. The payload parent identifies the terminal block; its parent hash identifies the predecessor. Lines 158–162 instead permit a nonzero configured hash override, bypassing TTD after its activation epoch. That branch needs a separate ancestry/height bound. Lines 120–137 model externally obtained PowBlock records, including Uint256 total_difficulty; they do not prove cumulative difficulty correspondence. The on_block handler invokes validation at line 220. [Bellatrix beacon transition](https://raw.githubusercontent.com/ethereum/consensus-specs/ad0058fd0d34c5dcf504fa51ea2f4f11077b9996/specs/bellatrix/beacon-chain.md), lines 443–454, checks subsequent payload-parent linkage and execution-engine validity. These checks still require an adapter to the same validated EL ancestry and reward ledger; a self-reported TD field is insufficient.

## Minimum difficulty across pinned premerge fork modules

Every listed validate_header rejects a difficulty differing from calculate_block_difficulty; every calculation clamps to 131072. Exact one-based lines below are constant / validation equality / final clamp. The immutable repository tree was inspected: it contains these 13 premerge fork modules, no separate Petersburg or constantinople_fix directory. Two attempted legacy directory fetches returned 404; neither was treated as evidence. Mainnet asset lists Constantinople and Petersburg at the same height 7280000. Mapping that config to this pin's consolidated Constantinople implementation remains an explicit fork-selection adapter.

| Module | Lines | SHA256 |
|---|---|---|
| [arrow_glacier](https://raw.githubusercontent.com/ethereum/execution-specs/0cc100eb190b64b23baba72dac0165652eaec252/src/ethereum/forks/arrow_glacier/fork.py) | 74 / 352 / 963 | `3111d8555b18d97215c974a78a459b95a1dd97a827ee012ea2db38f0ffce8d15` |
| [berlin](https://raw.githubusercontent.com/ethereum/execution-specs/0cc100eb190b64b23baba72dac0165652eaec252/src/ethereum/forks/berlin/fork.py) | 68 / 275 / 855 | `534966457f5708df0e2a9f577f754be6108d3289bc89ed92524eeca568360eac` |
| [byzantium](https://raw.githubusercontent.com/ethereum/execution-specs/0cc100eb190b64b23baba72dac0165652eaec252/src/ethereum/forks/byzantium/fork.py) | 63 / 270 / 832 | `6b593d3bb31b5ee8f2bf9f9745b2a90af24e28ccd716fd3bd012de8f407ce90b` |
| [constantinople](https://raw.githubusercontent.com/ethereum/execution-specs/0cc100eb190b64b23baba72dac0165652eaec252/src/ethereum/forks/constantinople/fork.py) | 63 / 270 / 832 | `139b60c76f18068145d6d548b8e1f9228385fb145b4f6df942758ed0fa772efc` |
| [dao_fork](https://raw.githubusercontent.com/ethereum/execution-specs/0cc100eb190b64b23baba72dac0165652eaec252/src/ethereum/forks/dao_fork/fork.py) | 63 / 274 / 827 | `83d0dff4f9802f72791d206426cd29504b2a841eed9bd168e96b7c68c7addfa8` |
| [frontier](https://raw.githubusercontent.com/ethereum/execution-specs/0cc100eb190b64b23baba72dac0165652eaec252/src/ethereum/forks/frontier/fork.py) | 59 / 262 / 797 | `636a8111fa4a60bf793faaadc620715a75ec39ca4c9434db42bedf4236f6d138` |
| [gray_glacier](https://raw.githubusercontent.com/ethereum/execution-specs/0cc100eb190b64b23baba72dac0165652eaec252/src/ethereum/forks/gray_glacier/fork.py) | 74 / 352 / 963 | `7ae1dbd606a57711ef8e1fd67e5c2b452a16ceaa743ae07d041c18140a6f30ab` |
| [homestead](https://raw.githubusercontent.com/ethereum/execution-specs/0cc100eb190b64b23baba72dac0165652eaec252/src/ethereum/forks/homestead/fork.py) | 59 / 262 / 806 | `01634375751d85c719bb3570fb9f7713d737f6c8bb4fd31cbf12c5d8c696c4c9` |
| [istanbul](https://raw.githubusercontent.com/ethereum/execution-specs/0cc100eb190b64b23baba72dac0165652eaec252/src/ethereum/forks/istanbul/fork.py) | 63 / 270 / 832 | `33bf2c41311d8c3e137c5fdc94015abed73dfc5d2d7d09fb79a263443d674545` |
| [london](https://raw.githubusercontent.com/ethereum/execution-specs/0cc100eb190b64b23baba72dac0165652eaec252/src/ethereum/forks/london/fork.py) | 75 / 361 / 972 | `1daebd84f89a2b8dcb8ff60ae1c496ad35cd4a5526ed7ad700a459674bb21923` |
| [muir_glacier](https://raw.githubusercontent.com/ethereum/execution-specs/0cc100eb190b64b23baba72dac0165652eaec252/src/ethereum/forks/muir_glacier/fork.py) | 63 / 270 / 834 | `5a569fb5ff0201d88f02ae52a4f16577082f9c151c6472ecc4c8966e550f824f` |
| [spurious_dragon](https://raw.githubusercontent.com/ethereum/execution-specs/0cc100eb190b64b23baba72dac0165652eaec252/src/ethereum/forks/spurious_dragon/fork.py) | 63 / 266 / 829 | `916185a1862cf4b696a1c63c6a2d6a06d03682ae9fba3b42b5e195cb6c018cfe` |
| [tangerine_whistle](https://raw.githubusercontent.com/ethereum/execution-specs/0cc100eb190b64b23baba72dac0165652eaec252/src/ethereum/forks/tangerine_whistle/fork.py) | 59 / 262 / 806 | `01634375751d85c719bb3570fb9f7713d737f6c8bb4fd31cbf12c5d8c696c4c9` |

Paris rejects nonzero difficulty at fork.py:324 and ommers at 328; state transition has no PoW reward producer. The exact Paris bytes are included in the manifest. Later-fork no-resumption and adopted mainnet fork-dispatch linkage remain proof obligations, not consequences of this table alone.

## Precise proposed arithmetic interface

Let `ds : List Nat` contain the difficulties of all rewarded, non-genesis canonical PoW blocks strictly before the terminal crossing, in ancestry order; let `g : Nat` be genesis difficulty. Require:

- every d in ds satisfies m≤d, derived from actual fork header validation;
- `g + ds.sum < T`, derived from the actual terminal parent's cumulative difficulty;
- reward-batch count p for any selected canonical history prefix satisfies `p ≤ ds.length + 1` (the +1 is the terminal crossing block).

Then `m * ds.length ≤ ds.sum < T`; hence `p ≤ (T−1)/m + 1 = 448226928710937500 < 2^64`. This formulation only needs nonnegative genesis difficulty; no genesis minimum or genesis reward is assumed. Genesis allocation remains separately counted by GenesisFundingInput. A prefix before merge can instead use its own below-T cumulative TD and omit the +1, or embed into the validated terminal ancestry. The latter option is conditional on that ancestry being available, not on arbitrary future liveness.

The terminal block itself can overshoot T by an unbounded amount relative to T: **do not assume terminal TD≤T**. Only its parent's TD<T is needed. No block.number arithmetic, UInt256 wrap assumption or bound on per-block maximum difficulty is used. Natural-sum correspondence must be proved before turning the CL Uint256 field into this inequality.

Proposed Lean stages (not implemented): `difficulty_sum_lower` over a list; `pow_count_of_terminal_parent` with the three independent premises above; closed kernel arithmetic `mainnet_ttd_count_lt_u64`; then populate only `ProtocolCreditEnvelope.Counts.pow_count` using the derived p bound. Withdrawal count and migration conservation fields remain independent open producers.

## Exact remaining adapters and consumer impact

1. Bind each PoW reward batch in ProtocolCreditEnvelope.Ledger to exactly one non-genesis canonical header position in the same linked EL world history. Count ommer rewards inside its batch, not as additional canonical blocks. Do not aggregate competing forks or repeatedly credit a reorg replay; rollback/reorg history must select the canonical ancestry.
2. Formalize fork dispatch and actual validate_header→difficulty≥m across the consolidated modules above, plus accepted PoW validation and hash-parent identity. Source inspection is not a kernel proof of Python semantics.
3. Prove totalDifficulty equals genesis difficulty plus the natural sum on that validated ancestry, with exact hash lookup correspondence and no wrapping or fabricated external TD. CL/BLS trust does not discharge this EL data obligation.
4. Use default zero terminal override and actual terminal-parent check, or name a separate override-specific ancestry bound. Prove no additional canonical PoW reward batches after transition through later forks.
5. Bind adopted initial genesis world and credit operations separately. A kernel numeric bound alone does not prove genesis loading, reward-value bound, migrations or the complete funding history.

This substantially narrows the former open PoW count problem to an ancestry/sum adapter and a small list-arithmetic lemma. It does not close protocol funding by itself. For the default mainnet config, no observed terminal-height oracle is needed; a nonzero-hash override is a clearly separate conditional alternative.

## Config and consensus source hashes
- [consensus-specs-configs-mainnet.yaml](https://raw.githubusercontent.com/ethereum/consensus-specs/ad0058fd0d34c5dcf504fa51ea2f4f11077b9996/configs/mainnet.yaml): `1c954ef11d38db5c0728f0487da0c29cc2c18869809bff765ab8a4788b269731`.
- [consensus-specs-specs-bellatrix-beacon-chain.md](https://raw.githubusercontent.com/ethereum/consensus-specs/ad0058fd0d34c5dcf504fa51ea2f4f11077b9996/specs/bellatrix/beacon-chain.md): `66b0d3f7b9db744b40f6caa8531e0b5feed5fa6a8e340debd574a57678544338`.
- [consensus-specs-specs-bellatrix-fork-choice.md](https://raw.githubusercontent.com/ethereum/consensus-specs/ad0058fd0d34c5dcf504fa51ea2f4f11077b9996/specs/bellatrix/fork-choice.md): `657cd44f4e287e4cc9e0ef69369137bd0859882e683abb02d762fa36f6a0141b`.


Implementation update: the earlier proposal is now implemented in ProtocolPowCount.lean in this source bundle. Canonical ancestry, reward-batch linkage and configuration adoption remain open.
