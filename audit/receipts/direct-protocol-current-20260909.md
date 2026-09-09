# Current protocol and report review — 9 September 2026

Read-only evidence and proposed decisions; **no normative pin adopted**. JSON companion contains retrieval timestamp, primary-source bodies and hashes, API responses, deployment calculations and local evidence hashes. Requested review target was HEAD `41bcff3`, proof source `68c083a`; actual HEAD observed is recorded in JSON. No repository edits, builds, repeated EVM tests, remote jobs, publication or author messages. Read AGENTS, superseded CAMPAIGN, lock, PROTOCOL-BOUNDARY, relevant direct reviews/receipts and all 968 lines of the GPT Pro report at `/Users/thomas/work/eip-8282/eip8282.txt`. The Desktop copy and report-linked sandbox reproduction files were not available. An existing authors draft was not located; root was asked for its path.

## Findings that affect the decision

1. **The pinned bytes remain the current sys-asm bytes.** All four source and four hex files match their lock hashes. EVMYulLean default HEAD remains the exact pinned `b62586650b4f96cc6da25f36574aaa8f329a6420`. No dependency migration is justified by this check.
2. **The published EIP and current code still disagree about inhibition.** The published EIP says permanent disablement. Both runtimes clear INHIBITOR on the next empty SYSTEM call, and Amsterdam tests explicitly describe reversible inhibition. This cannot be resolved by proving the existing bytes more strongly.
3. **The report’s arithmetic findings are substantiated, but its reachability classifications must remain separated.** Lean proves the 2893 word/natural disagreement and local fee drop. Anvil receipts reproduce threshold getters and intermediate-sum wrap on injected states. Neither is a canonical-history theorem. The report’s 3,307-submit constructor history is reported evidence whose original executable artifact is unavailable here.
4. **SYSTEM admission needs a named EL trust boundary.** The inspected EL transaction admission recovers a signed sender and checks funding and code restrictions; it does not explicitly reject `sender == SYSTEM_ADDRESS`. Unforgeability cannot be inferred from an arbitrary Θ input or from the BLS boundary. Specify cryptographic/address assumptions and bind internal-call semantics and code-installation invariants.

## Version comparison

| Component | Exact observation | Drift meaning |
|---|---|---|
| sys-asm | HEAD `83f9801245ff56878a450b5625801101b9a225a1` | Exactly pinned; common fake_expo source SHA256 `14b0cf7fee7c3e506327c9c7e7e7878add7e8cd69a415374481fd8b83a41d318` |
| EVMYulLean fork | HEAD `b62586650b4f96cc6da25f36574aaa8f329a6420` | Exactly pinned; does not establish Amsterdam evaluator correspondence |
| Pinned EIP fork branch | Now `4b5f3f42f6df8c9100f9954d2fc121d67e951449`; lock `b759aae809235802e23df47adeea50a1e6a7befb` | EIP file remains byte-identical, SHA256 `cc31a27ed39eceabed88140fa463e1ab430dacb5138b3bc5fccae95b7ed6786b` |
| Published/upstream EIP | Repo HEAD `d2a64c2d4cc44f2f507577d0ebfb110dcc21d358`; EIP last change `2d3c5e59e47103df15e51aafc815ba0b234e3388`; EIP SHA256 `d518461e4c1eb96254727155a3f8b60e92be29d43512551c4952345ab077a359` | Still Review; substantive text differs from pinned fork |
| Amsterdam EL reference | `0cc100eb190b64b23baba72dac0165652eaec252` | Still current default HEAD; fork.py SHA256 identical to archived reference |
| CL reference | Archived `ad0058fd0d34c5dcf504fa51ea2f4f11077b9996`; current `11f44343a8a282e7a9c2dee46590e273a8a0348a` | Three commits ahead; Phase0 and Gloas beacon-chain files identical. Presets, p2p docs and tests did change: do not generalize file equality to entire fork equality. |

Primary sources: [sys-asm](https://github.com/ethereum/sys-asm/tree/83f9801245ff56878a450b5625801101b9a225a1), [EVMYulLean](https://github.com/lfglabs-dev/EVMYulLean/tree/b62586650b4f96cc6da25f36574aaa8f329a6420), [upstream EIP revision](https://github.com/ethereum/EIPs/blob/2d3c5e59e47103df15e51aafc815ba0b234e3388/EIPS/eip-8282.md), [CL comparison](https://github.com/ethereum/consensus-specs/compare/ad0058fd0d34c5dcf504fa51ea2f4f11077b9996...11f44343a8a282e7a9c2dee46590e273a8a0348a).

Both [upstream PR12120](https://github.com/ethereum/EIPs/pull/12120) and [fork PR1](https://github.com/lfglabs-dev/EIPs/pull/1) are open and unmerged at branch head `4b5f3f42…`. API reports upstream mergeable/clean, fork PR unmergeable/dirty. These are transient merge metadata, not editorial approval. Local AGENTS requires humans to review/merge the guarantee PRs in P-SUBMIT → P-CONTROL → P-DRAIN order; superseded campaign machinery does not authorize merging or silently adopting upstream changes.

## Byte identities and constructor addresses

Hashes below are **decoded binary SHA256**, distinct from the hex-text file SHA256 in artifacts.lock. All hex-text lock hashes also match upstream.

| Image | Bytes | Binary SHA256 |
|---|---:|---|
| Deposit runtime | 628 | `2c49dcf745b1304f3dac0ea7487eae6d8fd07812ada980d542f79e8e5e53eb8d` |
| Deposit init | 638 | `166510c29d9ea96c80b854e86743377de1cadccaef62a620c684641fb9267f61` |
| Exit runtime | 458 | `c889ed88730d157d192aae28c2dee61324d0df3bd01ff0078386808b4adb27aa` |
| Exit init | 503 | `37d89175964e696bfed69ad5309c0147bdb7af8b11a25ea1ba557d7adb9d50b8` |

The reference deployment fixtures use factory `0x4e59b44847b379578588920cA78FbF26c0B4956C`, with deposit salt `0x1f4f2c41c28e816e259b621c58b94b37309c8dec42c8f6e400001a46c9d96bf7` and exit salt `0x89abb1878437213f971f849327423ed1d9c5cdb03970cd8f0000318b3ff10119`. Their initcode equals the pinned initcode. Read-only CREATE2 Keccak calculation yields exactly deposit `0x0000bff46984e3725691fa540a8c7589300d8282` and exit `0x000064d678505ad48f8ccb093bc65613800e8282`. This verifies preimages, not an actual chain installation. [Fixtures and deployment tests](https://github.com/ethereum/execution-specs/tree/0cc100eb190b64b23baba72dac0165652eaec252/tests/amsterdam/eip8282_builder_execution_requests).

Deposit init returns runtime without clearing existing storage; “zero initial controls” requires the fresh installation world. Exit init stores INHIBITOR. Actual Lambda constructor results in the current direct proof remain conditional on creation context and installation hypotheses. A permanent-inhibition redesign must distinguish initial Exit activation from permanent retirement, or the first empty SYSTEM call would no longer unlock Exit.

## EL/CL rules and unresolved bindings

[Amsterdam fork.py](https://github.com/ethereum/execution-specs/blob/0cc100eb190b64b23baba72dac0165652eaec252/src/ethereum/forks/amsterdam/fork.py) processes transactions, then withdrawals, then requests. Each builder target gets one empty SYSTEM call with zero value; request types 03 then 04 follow earlier request types, and empty outputs are omitted. Checked system transactions reject absent code and execution errors. They use 30 million execution gas and a separate state-gas reservoir for at most 16 new writes. The latter is relevant fork behavior absent from a simplistic Prague-gas extrapolation. The code-present check is not an exact-codehash check.

Phase0 `Slot` and Gloas payload block number/gas fields are 64-bit at the archived and current checked versions. Increasing canonical slots plus accounted gas can support the existing ResourceBounds argument. They do not themselves extract nonduplicated nested successful appends, handle ancestors that later revert, apply refunds, or connect the pinned evaluator to Amsterdam state-gas accounting. The current direct proof and receipts explicitly keep these protocol obligations open.

[Transaction admission](https://github.com/ethereum/execution-specs/blob/0cc100eb190b64b23baba72dac0165652eaec252/src/ethereum/forks/amsterdam/transactions.py) derives sender through signature recovery and Keccak. [Internal-call rules](https://github.com/ethereum/execution-specs/blob/0cc100eb190b64b23baba72dac0165652eaec252/src/ethereum/forks/amsterdam/vm/instructions/system.py) use current target as CALL caller and preserve caller for DELEGATECALL. Therefore prove genuine calls into the installed target, bind owner/storage context, and rule out ordinary execution under SYSTEM identity through explicit address assumptions. BLS correctness can remain a CL assumption, but that does not discharge EL sender authorization, SYSTEM scheduling, funding, call-value versus apparent-value, installation, request ordering or rollback obligations.

Current [disable tests](https://github.com/ethereum/execution-specs/blob/0cc100eb190b64b23baba72dac0165652eaec252/tests/amsterdam/eip8282_builder_execution_requests/test_builder_exit_disable.py) seed inhibitor state directly; the normal protocol does not send the nonempty calldata that sets it. With pinned reversible code, retiring an old queue while draining requires nonempty calldata on **each** drain until retirement; an empty drain reopens it. Handling old and new request sources, order within one type, and final retirement must be specified. A normal single-target schedule is not an upgrade specification.

## GPT Pro conclusions, checked against exact evidence

| Claim | Evidence and classification | Remaining limitation |
|---|---|---|
| 1608: 257 versus 256 iterations, same quote | UniversalBoundary.fakeExpoFitsWord_fuel_boundary proves old fuel-domain failure; direct-semantics Anvil receipts corroborate both exact runtimes | Injected state, not protocol history; new MathFee already removes the old semantic truncation |
| 1620: quote one wei above old model | Both runtime receipts return `243056981773394081136356734028591621772929`; helper old partial quote ends `2928` | Report-specific underpayment transaction is not among local receipts; source comparison supports rejection, but do not claim that exact reported transaction/gas was independently replayed |
| 2893: word quote drops below 2892 and differs from Nat | FeeBoundary.natural_quote, word_quote, word_price_not_mathematical, local_fee_drop; reviewed hashes and Anvil getters agree | Theorems are recurrence/counterexample certificates, not valid-history existence; earliest product-overflow counter167 is independently noted in prior review, not a separate Lean earliest-overflow theorem |
| Every numerator ≤2892 safe | FeeSafeDomain.domain_certificate and safe_quote derive universal agreement/completion by monotonicity from a checked upper trajectory | Arithmetic domain must still be derived from actual protocol funding; this is no longer merely the report's exhaustive Python scan |
| A1/A2 intermediate ADD wrap | UniversalBoundary wrapExcessImage/wrapWindowImage results; direct-semantics SYSTEM overflow cases | Injected states. Bounding only final Nat result is insufficient; close actual history/accounting induction to exclude them |
| Inhibition clears on next empty SYSTEM | Source, direct controls and injected Anvil unlock receipt agree | Not permanent; normal schedule has no disable instruction; upgrade remains unspecified |
| 3,307 submissions, 207 groups from constructor to2893 | Full report gives exact state and funding; sequence arithmetic is plausible | Original sandbox files unavailable, no matching chain receipt found. Classify as reported artificially funded constructor history, not independently verified canonical history |
| Collision at huge Exit TAIL | Slot arithmetic follows pinned code; report claims exact injected execution and mathematical constructor sequence | No corresponding local collision receipt or Lean constructor-history witness located. Not a demonstrated protocol exploit |
| OOG at very large numerators | Report's minimal-interpreter results | No matching local receipt; engine-specific gas/totality claims remain unverified here |

Existing `audit/receipts/direct-semantics-20260909.json` is explicitly `finite_injected_state_regressions`, Anvil1.5.0 / Prague, protocol_reachability=false. Getter transaction gas is 47,781 at1608; 47,868 at1620; 65,616 at2892; 65,181 at2893. Subtracting 21,000 intrinsic gas gives the report's getter execution-gas numbers exactly. No new finite tests were needed. The receipt also confirms rollback after an outer revert, without proving universal transaction accounting.

Structural protocol bounds do not settle tariff reachability: 2893 is far below2^128. Conversely “artificial ETH required” is not an eternal unreachability proof. Existing funding-reference work identifies a generous lifetime credit bound under a chosen genesis/fork sequence; conservation and actual admission bindings still need composition. No current-supply estimate or arbitrary msg.value cap substitutes for it.

## Concrete proposal for Thomas, with conditional alternatives

**Proposed baseline: PINNED-REVERSIBLE / AMSTERDAM-GLOAS-REFERENCE.** Keep lock EIP fork `b759…`, sys-asm `83f980…`, EVMYulLean `b625…`, Lean4.31.0 and exact CREATE2 preimages. Use EL `0cc100e` and archived CL `ad0058f` as expressly selected reference versions only after approval. Normal history permits one empty zero-value SYSTEM call per target at end of each valid block, fixed target code identity, and Exit initial unlock. No unspecified upgrade path. Keep all three direct mathematical/functional guarantees, explicit applicability hypotheses and OPEN protocol binding. Treat word-exact semantics as supporting evidence, not replacement of agreed mathematical clauses.

**Alternative PERMANENT-RETIREMENT:** normative published-EIP intent. Requires a concrete source/code change, separate initialization activation, new init/runtime hashes and likely new CREATE2 salts/addresses; update source, EIP, tests and proofs together. No adoption can occur by changing prose alone.

**Alternative REVERSIBLE-UPGRADE:** keep current bytes but explicitly define old/new target schedule, repeated nonempty old-target drains, request merge/order, inhibition duration and retirement. Prove those histories separately; the current normal reference schedule does not implement this.

**Alternative AUTHENTICATED-CHECKPOINT:** replace full genesis/history correspondence with a named authenticated activation state and explicit resource/funding certificates. This can reduce proof scope but must remain a disclosed conditional theorem. It cannot be advertised as proof from genesis.

**Alternative HARDENED-FEE:** if arbitrary funded EVM histories or future forks are in scope, choose overflow-safe recurrence or explicit rejection/saturation semantics, then repin and reprove. Rejection changes availability; saturation changes economic growth; both need author agreement. Merely adopting uint256 semantics abandons the original tariff intent.

Exact decisions/questions to take to Thomas and authors:

1. Which EIP text is normative: pinned reversible PR text or published permanent wording? Does retirement require persistent disablement while old records drain?
2. Which EL/CL fork commits, activation horizon and installation/checkpoint are covered? May the reference commits above become normative pins, or stay applicability evidence?
3. What named cryptographic/address assumptions authorize exclusion of ordinary SYSTEM callers, including deployed-code and delegated-call routes? Is there an intended explicit protocol admission rule missing from the reference?
4. During an upgrade, which address receives which calldata each block, how are old/new queues combined in request type order, and when is the old address abandoned?
5. Is the economic guarantee required only on a funding-bounded selected protocol history, or also on arbitrary funded EVM histories? If the latter, which hardening behavior is intended at arithmetic overflow?
6. Are finite injected regressions and conditional direct parents acceptable as the current evidence package while full protocol binding remains open? They must not be relabeled unconditional closure.

No question above requests generic permission for already authorized proof work. These are normative choices whose alternatives change behavior or theorem scope. Work toward existing authorized closure can continue while they remain explicitly unresolved.

## SYSTEM resource comparison

The reviewed direct SystemProgress theorem exposes gas≥2,500,000 and evaluator Context.fuel≥8503, with owner and write permission conditions. The reference's 30,000,000 execution-gas grant numerically exceeds that threshold. This is a useful margin, not a completed transport: the interpreter fuel is a proof resource, Amsterdam has separate execution/state-gas accounting, and admission must bind the concrete environment, installed code, initial storage domain and permissions. Do not describe 2.5M versus30M as a configuration mismatch, or describe numerical dominance alone as an Amsterdam execution theorem.

## Unsent draft to EIP authors

We are checking the current builder deposit/exit predeploys at sys-asm83f9801245ff56878a450b5625801101b9a225a1. The runtime and constructor bytes still match the reference deployment fixtures and proposed addresses.

We found a specification choice that needs clarification before calling the audit protocol-complete. Published EIP8282 describes nonempty SYSTEM calldata as permanent inhibition. Both current runtimes instead drain first, set INHIBITOR on nonempty input, and clear INHIBITOR on the next empty SYSTEM call. Amsterdam's normal request processing sends empty input once per target per block; its disable tests explicitly describe the switch as reversible.

Our suggested resolution for these exact bytes is to make reversibility explicit. If the intended upgrade retires an old queue while draining it, the old target must receive nonempty input on every drain until retirement; an empty drain re-enables user submissions. Could you specify the old/new address schedule, request ordering when both return records, and the retirement condition? If permanent inhibition is intended instead, initialization must distinguish the Exit constructor's temporary gate from permanent retirement, and source, bytecode, deployment data and tests need to change together.

We also verified a fee-domain boundary. At effective numerator1620 the historical proof model's256-iteration truncation underquotes by one wei; the complete contract recurrence agrees with the natural formula. The new proof definitions remove that truncation. At2893, however, the actual256-bit recurrence differs from the natural formula and the fee falls below its2892 value. The existing bytes therefore support the mathematical tariff only on a justified arithmetic domain. We have a checked safe interval through2892; tying it to valid funded protocol histories remains a separate obligation. This is not a demonstrated affordable protocol exploit.

For the audit scope, please confirm the normative EIP revision, EL/CL reference versions and activation/deployment state. We also need an explicit SYSTEM-address assumption: transaction admission recovers an ECDSA address but does not expressly reject SYSTEM, while internal CALL and DELEGATECALL have different caller/storage contexts. We intend to keep the cryptographic/address assumption separate from BLS consensus validation and to prove the remaining EL scheduling, funding, rollback and request obligations under the selected scope.

This draft has not been sent or posted.
