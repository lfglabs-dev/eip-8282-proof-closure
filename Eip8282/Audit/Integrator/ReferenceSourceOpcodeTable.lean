import Eip8282.Audit.Integrator.ReferenceCheckedDecode

/-! Complete source Ops table at EL0cc100eb190b64b23baba72dac0165652eaec252,
vm/instructions/__init__.py, SHA2562bef9321753167d80f62eb1f861120412de5b9561cba38b6832f96a5535f617f.
Full body archived in audit/receipts/direct-reference-amsterdam-gas-sources-20260910.json.
Names and values below retain source declaration order, including CLZ, SLOTNUM,
DUPN, SWAPN and EXCHANGE. This is audited table transcription, not Python extraction.
validTag means membership in Ops, NOT support by the checked protected handlers,
NOT successful execution, and NOT old parseInstr compatibility. Source INVALID
0xfe is absent from Ops; EOF is determined by code lookup, not by this table.
The finite tests concern the byte universe, never an execution iteration bound. -/
namespace Eip8282.Audit.Integrator.ReferenceSourceOpcodeTable
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

def sourceTags : List (String × UInt8) := [
    ("ADD",0x01),
    ("MUL",0x02),
    ("SUB",0x03),
    ("DIV",0x04),
    ("SDIV",0x05),
    ("MOD",0x06),
    ("SMOD",0x07),
    ("ADDMOD",0x08),
    ("MULMOD",0x09),
    ("EXP",0x0a),
    ("SIGNEXTEND",0x0b),
    ("LT",0x10),
    ("GT",0x11),
    ("SLT",0x12),
    ("SGT",0x13),
    ("EQ",0x14),
    ("ISZERO",0x15),
    ("AND",0x16),
    ("OR",0x17),
    ("XOR",0x18),
    ("NOT",0x19),
    ("BYTE",0x1a),
    ("SHL",0x1b),
    ("SHR",0x1c),
    ("SAR",0x1d),
    ("CLZ",0x1e),
    ("KECCAK",0x20),
    ("ADDRESS",0x30),
    ("BALANCE",0x31),
    ("ORIGIN",0x32),
    ("CALLER",0x33),
    ("CALLVALUE",0x34),
    ("CALLDATALOAD",0x35),
    ("CALLDATASIZE",0x36),
    ("CALLDATACOPY",0x37),
    ("CODESIZE",0x38),
    ("CODECOPY",0x39),
    ("GASPRICE",0x3a),
    ("EXTCODESIZE",0x3b),
    ("EXTCODECOPY",0x3c),
    ("RETURNDATASIZE",0x3d),
    ("RETURNDATACOPY",0x3e),
    ("EXTCODEHASH",0x3f),
    ("BLOCKHASH",0x40),
    ("COINBASE",0x41),
    ("TIMESTAMP",0x42),
    ("NUMBER",0x43),
    ("PREVRANDAO",0x44),
    ("GASLIMIT",0x45),
    ("CHAINID",0x46),
    ("SELFBALANCE",0x47),
    ("BASEFEE",0x48),
    ("BLOBHASH",0x49),
    ("BLOBBASEFEE",0x4a),
    ("SLOTNUM",0x4b),
    ("STOP",0x00),
    ("JUMP",0x56),
    ("JUMPI",0x57),
    ("PC",0x58),
    ("GAS",0x5a),
    ("JUMPDEST",0x5b),
    ("SLOAD",0x54),
    ("SSTORE",0x55),
    ("TLOAD",0x5c),
    ("TSTORE",0x5d),
    ("POP",0x50),
    ("PUSH0",0x5f),
    ("PUSH1",0x60),
    ("PUSH2",0x61),
    ("PUSH3",0x62),
    ("PUSH4",0x63),
    ("PUSH5",0x64),
    ("PUSH6",0x65),
    ("PUSH7",0x66),
    ("PUSH8",0x67),
    ("PUSH9",0x68),
    ("PUSH10",0x69),
    ("PUSH11",0x6a),
    ("PUSH12",0x6b),
    ("PUSH13",0x6c),
    ("PUSH14",0x6d),
    ("PUSH15",0x6e),
    ("PUSH16",0x6f),
    ("PUSH17",0x70),
    ("PUSH18",0x71),
    ("PUSH19",0x72),
    ("PUSH20",0x73),
    ("PUSH21",0x74),
    ("PUSH22",0x75),
    ("PUSH23",0x76),
    ("PUSH24",0x77),
    ("PUSH25",0x78),
    ("PUSH26",0x79),
    ("PUSH27",0x7a),
    ("PUSH28",0x7b),
    ("PUSH29",0x7c),
    ("PUSH30",0x7d),
    ("PUSH31",0x7e),
    ("PUSH32",0x7f),
    ("DUP1",0x80),
    ("DUP2",0x81),
    ("DUP3",0x82),
    ("DUP4",0x83),
    ("DUP5",0x84),
    ("DUP6",0x85),
    ("DUP7",0x86),
    ("DUP8",0x87),
    ("DUP9",0x88),
    ("DUP10",0x89),
    ("DUP11",0x8a),
    ("DUP12",0x8b),
    ("DUP13",0x8c),
    ("DUP14",0x8d),
    ("DUP15",0x8e),
    ("DUP16",0x8f),
    ("SWAP1",0x90),
    ("SWAP2",0x91),
    ("SWAP3",0x92),
    ("SWAP4",0x93),
    ("SWAP5",0x94),
    ("SWAP6",0x95),
    ("SWAP7",0x96),
    ("SWAP8",0x97),
    ("SWAP9",0x98),
    ("SWAP10",0x99),
    ("SWAP11",0x9a),
    ("SWAP12",0x9b),
    ("SWAP13",0x9c),
    ("SWAP14",0x9d),
    ("SWAP15",0x9e),
    ("SWAP16",0x9f),
    ("DUPN",0xe6),
    ("SWAPN",0xe7),
    ("EXCHANGE",0xe8),
    ("MLOAD",0x51),
    ("MSTORE",0x52),
    ("MSTORE8",0x53),
    ("MSIZE",0x59),
    ("MCOPY",0x5e),
    ("LOG0",0xa0),
    ("LOG1",0xa1),
    ("LOG2",0xa2),
    ("LOG3",0xa3),
    ("LOG4",0xa4),
    ("CREATE",0xf0),
    ("CALL",0xf1),
    ("CALLCODE",0xf2),
    ("RETURN",0xf3),
    ("DELEGATECALL",0xf4),
    ("CREATE2",0xf5),
    ("STATICCALL",0xfa),
    ("REVERT",0xfd),
    ("SELFDESTRUCT",0xff)]

def tags : List UInt8 := sourceTags.map Prod.snd

def validTag (tag : UInt8) : Bool := tags.contains tag

theorem tags_nodup : tags.Nodup := by decide +kernel

theorem source_count : sourceTags.length = 153 := by decide +kernel

theorem invalid_examples : validTag 0x0c = false ∧ validTag 0x1f = false ∧
    validTag 0xa5 = false ∧ validTag 0xfe = false := by decide +kernel

theorem extended_valid : validTag 0x1e = true ∧ validTag 0xe6 = true ∧
    validTag 0xe7 = true ∧ validTag 0xe8 = true := by decide +kernel

/-- The 41 checked running variants plus three terminal opcodes. This explicit
subset is not the full source-valid table; unsupported valid tags stay valid. -/
def protectedTags : List UInt8 := [0x01,0x02,0x03,0x04,0x10,0x11,0x14,0x16,0x1b,0x1c,0x15,0x33,0x34,0x36,0x35,0x5b,0x50,0x5f,0x60,0x61,0x63,0x67,0x73,0x7f,0x80,0x81,0x82,0x83,0x84,0x90,0x91,0x92,0x93,0x56,0x57,0x54,0x55,0x52,0x53,0x37,0xa0,0x00,0xf3,0xfd]

theorem known_valid : ∀ tag ∈ protectedTags, validTag tag = true := by decide +kernel

theorem protected_count : protectedTags.length = 44 ∧ protectedTags.Nodup := by decide +kernel

#print axioms tags_nodup
#print axioms source_count
#print axioms invalid_examples
#print axioms extended_valid
#print axioms known_valid
#print axioms protected_count
end Eip8282.Audit.Integrator.ReferenceSourceOpcodeTable
