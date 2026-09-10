# Checked types and exceptions for the complete local SYSTEM source step

Read-only audit, 2026-09-10. Uses cached EL 0cc100eb source bodies; narrow exact-source downloads authorized after the initial audit; no builds or Lean edits. Statements below distinguish proved natural/word bounds from still-unbound source class behavior.

## Exact type binding resolved from the lock

After the initial cached-source audit, root authorized fetching the narrowly missing exact files. EL commit0cc100eb's uv.lock selects ethereum-types **0.4.1**, although pyproject alone permits >=0.4.1,<0.5. The locked pure-Python wheel URL and SHA256 were verified before inspecting its contents; no package was installed or executed. Use the lock-selected artifact, not an arbitrary compatible version. Every fetched EL body also matches its exact Git tree blob. Full bodies, URLs, hashes and binding metadata are in `/tmp/eip-reference-checked-types/sources.json`; the verified wheel is retained beside it.

Concrete domains from numeric.py:

- `Uint` is an Unsigned wrapper around a Python int, accepts precisely nonnegative integers and has no upper width (517-540). `Unsigned.__init__` calls int(value) and throws **OverflowError** on range failure (44-48). `__index__` returns the same integer (78-79).
- `U256` is FixedUnsigned with MAX_VALUE=2^256-1 (690-712), range checked at611-612. Ordinary +,*,shifts reconstruct the same class and may overflow; wrapping_add/sub/mul explicitly mask. FixedUnsigned.from_be_bytes first throws **ValueError** if longer than32 bytes, then constructs U256 (566-579).
- Amsterdam fork_types.py37-39 defines `ExecutionGas = NewType("ExecutionGas", Uint)` and similarly StateGas. NewType is runtime identity, not a U64 constructor. Valid typed gas objects are therefore Uint with no upper bound. **There is no bounded-gas overflow obligation for memory cost, aggregate gas or source refunds converted into gas.**
- Same-class arithmetic is required; operands of a different unsigned class return NotImplemented and can produce TypeError. Uint subtraction explicitly rejects negative results with OverflowError (103-129). Existing payment and monotonic-cost facts supply precisely these nonnegative bounds. Division/modulo require nonzero divisor; local memory divisors32/512 are literal positive Uint values.
- Bytes is built-in bytes; Bytes32 validates exact length32 (bytes.py31-38,114-123,171). to_be_bytes32 calls Python int.to_bytes(32,big), then Bytes32 (numeric.py424-429). Typed U256 range guarantees fit. MSTORE8's mask produces a value0..255 whose __index__ supports Bytes([value]).
- `ceil32` uses Uint(32), remainder, and value+32-remainder for a nonzero remainder; no width cap (EL utils/numeric.py43-65). Padding is built-in bytes.ljust(int(size), zero) (utils/byte.py40-65).

No variants are necessary for the lock-selected pure Python artifact. A different dependency resolution or optimized replacement is a distinct explicit runtime context and must be compared separately; no such change is adopted here.

## Memory calculations actually consumed

`calculate_gas_extend_memory` gas.py 774-819 skips a zero-size request before offset addition. Otherwise it computes ceil32(current memory length) and ceil32(Uint(offset)+Uint(length)), extends only when the latter is larger, and charges the difference of memory costs. Source memory cost (747-771) computes words*3 + words^2//512 and explicitly catches ValueError from ExecutionGas(total_cost), rethrowing OutOfGasError. For the locked fork_types binding this NewType call is identity: the ValueError catch supplies no additional range guard. The upstream Uint formula stays nonnegative, so payment is the remaining semantic OOG condition here.

Existing input memory Related supplies exact eager length 32*activeWords, not merely zero-byte agreement. RuntimeMemoryCharges.accepted_expansion identifies actual post words with natural M; RuntimeMemoryMonotone.accepted derives positive operand span and nondecreasing capacity. SystemExecutionResources.Completed gives exit cap400/40, and SystemMemoryResources.attach derives **post-RETURN** cap400/40 on the same witness. Consequently all actual SYSTEM memory lengths and positive spans are at most12800/1280; costs at most1512/123. Actual MSTORE/MSTORE8 local producers derive span and cap-word-fit, not supplied postmemory. Source extension subtraction and cost subtraction are nonnegative by the actual monotonic relation.

These constants also fit host memory bounds. Uint/ExecutionGas have no upper bound in the resolved lock-selected source, so no numeric overflow bound is needed for these costs. Ordinary memory charge is base3 plus nonnegative delta (at most1515/126 with these conservative caps); terminal RETURN has base0. Payment is already derived for all actual events by SystemMeterResources.pay_completed, with source Reading coupling now supplied by the new constructive-readings work. Source resource-class operations and comparisons are now source-identified as Uint/Int arithmetic; their Lean operational correspondence still needs composition with the payment proof.

## Operation-specific checks

| Operation | Exact source effect/check | Existing discharge and remaining binding |
|---|---|---|
| MSTORE | Pop offset then value; value.to_be_bytes32(); checked U256(len(value)); extend; write; Uint PC+1 | Actual Z pop2 and full view action; typed UInt256 value and 32-byte encoding; literal constant32 fits; positive span and memory splice already proved. Exact numeric source identifies int.to_bytes(32,big), Bytes32 length check, and U256(32); their range preconditions are discharged by typed word/length32. |
| MSTORE8 | Pop offset/value; U256(1), mask with U256(0xff), Bytes([masked]); extend/write | Actual low-byte action uses UInt8.ofNat value.toNat; mask range0..255 follows word bit semantics; locked Bytes is built-in bytes and U256 mask uses same-class AND; the result range discharges element conversion. No arbitrary postbyte premise. |
| RETURN | Pop offset/length; extension; unpadded memory_read_bytes; running=False, no PC increment | Actual ReturnView.halted plus ReturnSlice.output_eq_extract gives exact eager unpadded slice. Positive length derives end<=new capacity; zero length allows arbitrary offset and requires no expansion. No terminal PC equality should be added. |
| CALLDATALOAD | Pop arbitrary source offset; U256(32); padded buffer_read; U256.from_be_bytes | EnvironmentOps proves fixed32 padding at arbitrary word offsets, and typed word conversion; buffer_size gives32-byte result. No source-offset cutoff. Locked from_be_bytes rejects only lengths above32 before range checking; fixed32 padding discharges both mathematical conditions. |
| CALLDATASIZE | U256(len(call_data)) then push | Existing PureEnvironment uses explicit calldata.size<2^256 gate only in this family; empty canonical SYSTEM call discharges it. General arbitrary calldata wrappers retain admission fit. |
| CALLDATACOPY | Pop destination, source offset, length; ceil32(Uint(size))//32; ExecutionGas(3*words); extend; padded read then write | **Not present on the proved actual SYSTEM trace:** SystemPathBudget.Allowed excludes CALLDATACOPY and Completed.allowed is derived from actual path. Hence not an unresolved exception in this SYSTEM induction. General user/runtime copy transport remains separate and must account for copy-cost cast, three operands, destination span, zero-length behavior and arbitrary source offset. Do not silently claim this dispatch case is handled by SystemAction. |

For general CALLDATACOPY, source buffer indexing is natural (Uint(start)+Uint(size)), not wrapped U256 addition. Size0 skips memory growth and copies empty bytes even at huge destination/source offsets. A positive destination span bound is needed for memory write, not a small source offset. Existing typed UInt256 proves each operand <2^256 but alone does not prove the *sum* fits U256; no such fit is appropriate when the source intentionally promotes to Uint. For SYSTEM this entire case is excluded by actual path evidence, not by an artificial protocol restriction.

## Other exception points for source SYSTEM induction

- Stack pop/push: source vm/stack.py pops only nonempty and raises overflow at length1024. ReferenceAcceptedStack.bounds/pop1/pop2 and initial empty stack with exact action evolution discharge operand and postarity bounds. Source end-oriented stack reversal is explicit. Per-step actual Z also covers the supported DUP/SWAP depths.
- Decode and jumps: actual runtime sites and complete immediate span already discharge truncated PUSH hazards; PureControl action checks the exact source jump set. Source instruction table/numeric enum dispatch binding remains distinct from the finite matching theorem. New instruction-family parameter exceptions cannot occur at the proved fixed sites.
- CALLER/address and CALLVALUE: the source address byte representation and apparent value must be initially bound to view.env.source and view.env.weiValue; field typing alone does not identify source message context. No ADDRESS/SLOTNUM/CLZ operation is inserted into SYSTEM proof obligations unless reached by its actual opcode scope.
- Storage: SSTORE static rejection is excluded by retained permission; source existing-account assertion is not established solely by pinned HasOwner without the account-map adapter. Constructive SourceReadings and StorageWarmth concern pre-access data; sentry-before-read and refund-before-execution/state charges retain source ordering. Signed refund is not a UInt256; do not reuse pinned refundBalance. Source parent/created/current/access-set initial bindings remain explicit.
- Meter arithmetic: natural decrements are justified by the sequential payment proof; state refunds use min(spill,refund) and nonnegative restoration. Resolved Uint has no upper-bound failure, so an additional gas/refund upper-bound invariant is unnecessary. Same-class arithmetic and each nonnegative subtraction are the actual typed preconditions. Do not infer source readings are correct merely because arbitrary Reading values are accepted by the payment model.
- Host memory: the generic premise32*cap<2^System.Platform.numBits is a Lean USize normalization bound, **not** by itself Python's signed Py_ssize_t allocation bound. Concrete cap400/40 is enough for both signed32/64 maxima. Formal source execution still needs the chosen list/bytearray model or an explicit standard-runtime resource interpretation. No theorem can promise absence of external host OOM merely from protocol gas; that is not an EVM validity exception.

## Minimal next interface

A focused `SourceTypeSafeStep` record can contain typed stack values, source eager-size equality, bound on computed memory cost and charge, nonnegative source subtractions, decoded-site/successful jump evidence, and exact output bytes. Derive its mathematical fields from the same Completed/Viewed/paid trace. The exact imported constructor domains are now resolved; bind their source operations to these ranges and equations; then operational source opcode dispatch can consume the calculated action and payment. Avoid replacing this with a single assumed 'source step succeeds' postcondition. Initial source world/context/typing plus actual operation definitions remain the trusted/adapted boundary until their concrete correspondence is proved.

## Inspected cached bodies

- `/tmp/eip-reference-memory-control/vm__instructions__memory.py` lines 29-90; SHA256 `77fec2a002eb27f34af82bd4ce5db98d593033f220a91eb65f56ff9496135278`.

- `/tmp/eip-reference-memory-control/vm__instructions__environment.py` lines 159-243; SHA256 `8c57bd699b99ff8b4d8e41e6a9c89cd1a03dda8160bf1d6dffe091932ec03657`.

- `/tmp/eip-reference-memory-control/vm__instructions__system.py` lines 314-344; SHA256 `37c888c4f1dfed62f1947ceb457db349be6978da5519234a5b6604f2e6036890`.

- `/tmp/eip-reference-memory-control/vm__memory.py` lines 20-83; SHA256 `50b962d2477ddcaeeb87d2ea56073b3691d93ea8d41ab29eb8b77605c6efef95`.

- `/tmp/eip-reference-memory-control/vm__gas.py` lines 372-425, 747-819; SHA256 `41d97e32f68585f99276f164b828b9091c112a05df31002594276d8e1feacc0c`.

- `/tmp/eip-reference-memory-control/vm__stack.py` lines 116-157; SHA256 `20cdb907098ae500c47abc6a1437cb9e4cdb5809f6c40b7d8935038aedd57b2a`.

## Newly resolved exact artifacts

- `src/ethereum/forks/amsterdam/fork_types.py`: SHA256 `3e0013e251867df02aca7b746b77403b36b41d73f7c4158bed09964838c935ca`; source `https://raw.githubusercontent.com/ethereum/execution-specs/0cc100eb190b64b23baba72dac0165652eaec252/src/ethereum/forks/amsterdam/fork_types.py`.

- `pyproject.toml`: SHA256 `06b23dc8c145eb4cf208676686eba7c5a7ee78059cc66ce7d5e84b64921fe46a`; source `https://raw.githubusercontent.com/ethereum/execution-specs/0cc100eb190b64b23baba72dac0165652eaec252/pyproject.toml`.

- `uv.lock`: SHA256 `ba73e32170aba3709a1edcc64e9ef7fe9af27222bafd352926a6cd18abd86dc5`; source `https://raw.githubusercontent.com/ethereum/execution-specs/0cc100eb190b64b23baba72dac0165652eaec252/uv.lock`.

- `src/ethereum/utils/numeric.py`: SHA256 `cb1db3b70f2e4b2998c3e05d3dc0e308a8414f1794c0f54fa31c4698a80fdfd5`; source `https://raw.githubusercontent.com/ethereum/execution-specs/0cc100eb190b64b23baba72dac0165652eaec252/src/ethereum/utils/numeric.py`.

- `src/ethereum/utils/byte.py`: SHA256 `895e0c6b80bdd63ba7712dad3ce2cd1891cc618d4be8d31decb706462ae24f43`; source `https://raw.githubusercontent.com/ethereum/execution-specs/0cc100eb190b64b23baba72dac0165652eaec252/src/ethereum/utils/byte.py`.

- `ethereum_types/__init__.py`: SHA256 `152464f2558f6bbd378d25056cf1dea66b63fde0e6fecb468b8c32f81caef0cc`; source `https://files.pythonhosted.org/packages/78/f6/466c684cee5eacd6413f33284a8bd45686564e7c5974d5cda331c9577c4e/ethereum_types-0.4.1-py3-none-any.whl#ethereum_types/__init__.py`.

- `ethereum_types/bytes.py`: SHA256 `e76b5ad74228e0d5dbf3e44e4fb3200203eef918c996584a64abcbc27fed9e82`; source `https://files.pythonhosted.org/packages/78/f6/466c684cee5eacd6413f33284a8bd45686564e7c5974d5cda331c9577c4e/ethereum_types-0.4.1-py3-none-any.whl#ethereum_types/bytes.py`.

- `ethereum_types/enum.py`: SHA256 `e2f73f979ec23fac1af93a370c41eb50467c18bcfa14850d9e043b258807a944`; source `https://files.pythonhosted.org/packages/78/f6/466c684cee5eacd6413f33284a8bd45686564e7c5974d5cda331c9577c4e/ethereum_types-0.4.1-py3-none-any.whl#ethereum_types/enum.py`.

- `ethereum_types/frozen.py`: SHA256 `50998345b38977de4c5d92b136f00dc30180add2215c59485a513daeef3b3418`; source `https://files.pythonhosted.org/packages/78/f6/466c684cee5eacd6413f33284a8bd45686564e7c5974d5cda331c9577c4e/ethereum_types-0.4.1-py3-none-any.whl#ethereum_types/frozen.py`.

- `ethereum_types/numeric.py`: SHA256 `47d040d4de043e46d19c2fd9f74b318396b6c83ab01fe346f98a3c477e58db46`; source `https://files.pythonhosted.org/packages/78/f6/466c684cee5eacd6413f33284a8bd45686564e7c5974d5cda331c9577c4e/ethereum_types-0.4.1-py3-none-any.whl#ethereum_types/numeric.py`.

- `ethereum_types-0.4.1.dist-info/METADATA`: SHA256 `970c0b08c3b10b4cafcec69b8270ba99b2337700a578d77ccdbdba79089b5964`; source `https://files.pythonhosted.org/packages/78/f6/466c684cee5eacd6413f33284a8bd45686564e7c5974d5cda331c9577c4e/ethereum_types-0.4.1-py3-none-any.whl#ethereum_types-0.4.1.dist-info/METADATA`.

Wheel locked/observed SHA256: `33de3e2a0c0e57ea1b67802485de556b92d557aae7c8c640070800f2b4f639e3`. No dynamic library tests or code execution were used as evidence.

## Exact LOG0 source added for the separate user-path adapter

The same archive now includes full pinned instructions/log.py, gas.py and blocks.py, all verified against the EL commit tree (reusing cached bytes rather than downloading unchanged sources). log.py32-83 defines log_n; line86 specializes log0 with topic count0. Source fields are current_target as emitter, empty tuple topics, and the unpadded slice of the newly extended memory. This is the authentic contract LOG0, not the synthetic transfer LOG3 emitted at SYSTEM.

Precise order: pop offset/size; no topic conversions; compute extension; charge375 + 8*Uint(size) + memory delta; extend eager memory; reject static context; construct/append exactly one Log; increment pc with Uint(1). The late static guard at72-73 must not be transcribed as SSTORE's early static guard when modeling exceptional intermediate state. Under the successful permitted-call premise, it cannot throw. Size0 still emits exactly one empty-data log with base375 and does not expand memory; arbitrary offset then remains valid. Positive-size bounds are needed only for memory effects/host size, not for Uint gas arithmetic.

`Log` is the dataclass in blocks.py329-355 with address/topics/data fields; the module's fixed-size topic encoding path is unused by LOG0 because num_topics=0. For other LOGn, typed U256.to_be_bytes32 discharges topic byte length; LOG0 adapter need not introduce arbitrary topic constraints. Current-target/view-owner initial binding and projected append order remain explicit. Literal bytes/tuple append are source operations whose representation correspondence must be proved, not inferred solely from a type annotation.

Proposed adapter should reuse the ReturnSlice zero-extension argument for data, derive memory capacity from actual LOG0 expansion, and prove the full view's all-topics owner projection appends that one exact record. It may use source375+8*size+delta payment on an actual user trace, but the existing SYSTEM payment theorem excludes LOG0 and does not supply this user-path gas proof.

- Added source `src/ethereum/forks/amsterdam/vm/instructions/log.py` SHA256 `f62f6cb589811e3a58c3a4644fcf7b979a506df1f09213e2a96e7988a4574874`, URL `https://raw.githubusercontent.com/ethereum/execution-specs/0cc100eb190b64b23baba72dac0165652eaec252/src/ethereum/forks/amsterdam/vm/instructions/log.py`.

- Added source `src/ethereum/forks/amsterdam/vm/gas.py` SHA256 `41d97e32f68585f99276f164b828b9091c112a05df31002594276d8e1feacc0c`, URL `https://raw.githubusercontent.com/ethereum/execution-specs/0cc100eb190b64b23baba72dac0165652eaec252/src/ethereum/forks/amsterdam/vm/gas.py`.

- Added source `src/ethereum/forks/amsterdam/blocks.py` SHA256 `ec2cdd7fae64861b76c225573aac20be18ddb39e1fb2c2e0015a5cd0c4d2852c`, URL `https://raw.githubusercontent.com/ethereum/execution-specs/0cc100eb190b64b23baba72dac0165652eaec252/src/ethereum/forks/amsterdam/blocks.py`.
