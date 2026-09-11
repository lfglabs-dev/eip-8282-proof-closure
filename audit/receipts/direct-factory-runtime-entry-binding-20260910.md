# Factory entry binding

`FactoryRuntimeEntry.lean` binds the exact 69-byte runtime from the cached EIP-7997 testing mixin at reference commit `0cc100eb190b64b23baba72dac0165652eaec252`. The deployment generator constructs transaction data as the fixture salt followed by initcode. This producer requires actual XiArgs code and calldata equal those bytes; the factory address alone does not establish code behavior.

Archived sources:
- `/tmp/eip-reference-migration-deployment/packages__testing__src__execution_testing__forks__forks__eips__amsterdam__eip_7997.py`, SHA256 `5c6d05875c4e650df3f1254c5a81008c39e8bdee8e00a6d40fc3568d510818cd`.
- `/tmp/eip-reference-migration-deployment/packages__testing__src__execution_testing__tools__utility__generators.py`, SHA256 `f1d922a839ec593bc5f03762b41f059792fcca22d62446bd47f01329289fec2a`.
- Deposit JSON `/tmp/eip-adequacy-sources/tests__amsterdam__eip8282_builder_execution_requests__builder_deposit_factory_deploy.json`, SHA256 `aae4bd49b90e96874ea3f49a256c0d0e208ba2eef85963c12f4281f1d16e3a13`.
- Exit fixture SHA256 `ed76ac573281d1f894444c11a9a4675ef7211e67fef3312ea4f6a8e94cdd0587`.

Runtime binary SHA256 `e0af82ad2e5188285db8ba0b2ae054d13f0fd4fe325c48c7f2dace48454404b9`. Deposit initcode 638 bytes, SHA256 `166510c29d9ea96c80b854e86743377de1cadccaef62a620c684641fb9267f61`. Exit initcode 503 bytes, SHA256 `37d89175964e696bfed69ad5309c0147bdb7af8b11a25ea1ba557d7adb9d50b8`. Full salts are literal 32-byte arrays and their UInt256 big-endian encoding is proved.

Actual prefix: PC0 PUSH32(-32),33 CALLDATASIZE,34 ADD,35 PUSH1(0),37 DUP2,38 PUSH1(32),40 DUP3,41 CALLDATACOPY,42 DUP1,43 CALLDATALOAD,44 DUP3,45 DUP3,46 CALLVALUE. These 13 accepted instructions reach PC47 CREATE2 with memory exactly the initializer, stack [value,0,len,salt,0,len], and gas at least initial gas minus157.

The selection boundary checks actual Z permission, memory, gas, stack and init-size rules, then the actual selectedChild nonce/depth/balance gate. Child creator, value, init bytes and salt are explicit. Fuel n+1 at the step selects Lambda n, including n=0; no child execution success is implied.

Remaining integration obligations: actual parent calldata/code/owner binding and protocol execution environment, resource adequacy for initialization, actual CREATE2 address/hash binding, child success and code deposit, factory tail success and parent Theta/Upsilon checkpoint survival, and canonical installation in the admitted history. Cached generator preallocation is source evidence, not a proved mainnet bootstrap or reference adapter.
