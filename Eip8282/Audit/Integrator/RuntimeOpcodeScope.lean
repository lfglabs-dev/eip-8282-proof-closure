import Eip8282.Audit.Jumpdests

/-!
# Finite opcode scope of the two pinned runtimes

Kernel-checked tables use the actual `decode`, `N` and existing `D_J` tables.
A boundary starts at PC zero and advances by the pinned instruction width;
PUSH immediate bytes are not decoded as instructions. Checked fall-through and
jump-target membership support a later execution-PC invariant. No execution
invariant, gas independence, sufficient-fuel or interpreter equivalence theorem
is asserted here. The intended consumer is the focused shadow-gas adapter.
-/
namespace Eip8282.Audit.Integrator.RuntimeOpcodeScope

open EvmYul EvmYul.EVM
open Eip8282.Audit.Bytecode Eip8282.Audit.Jumpdests

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- Exact union of opcode names at the two images' instruction sites. -/
def allowedOps : List (Operation .EVM) :=
  [.STOP, .ADD, .MUL, .SUB, .DIV, .LT, .GT, .EQ, .ISZERO, .AND,
   .SHL, .SHR, .CALLER, .CALLVALUE, .CALLDATALOAD, .CALLDATASIZE,
   .CALLDATACOPY, .POP, .MSTORE, .MSTORE8, .SLOAD, .SSTORE,
   .JUMP, .JUMPI, .JUMPDEST, .PUSH0, .PUSH1, .PUSH2, .PUSH4,
   .PUSH8, .PUSH20, .PUSH32, .DUP1, .DUP2, .DUP3, .DUP4, .DUP5,
   .SWAP1, .SWAP2, .SWAP3, .SWAP4, .LOG0, .RETURN, .REVERT]

/-- Real pinned fall-through PC, including UInt256 arithmetic. -/
def nextPC (pc : Nat) (op : Operation .EVM) : Nat :=
  (N (UInt256.ofNat pc) op).toNat

/-- Linear instruction boundaries, independent of any proposed site table.
This includes sites following a halt, as an ordinary bytecode disassembly does. -/
inductive Boundary (code : ByteArray) : Nat → Prop
  | start (h : 0 < code.size) : Boundary code 0
  | next {pc : Nat} {op : Operation .EVM} {arg : Option (UInt256 × Nat)}
      (before : Boundary code pc)
      (decoded : opcodeAt code pc = some (op, arg))
      (inside : nextPC pc op < code.size) : Boundary code (nextPC pc op)

/-- Finite fact at a site: in bounds, decodable, in the explicit opcode subset,
and its actual successor is another listed site or exactly EOF. -/
def SiteOK (code : ByteArray) (sites : List Nat) (pc : Nat) : Prop :=
  pc < code.size ∧
  match opcodeAt code pc with
  | none => False
  | some (op, _) => op ∈ allowedOps ∧
      (nextPC pc op ∈ sites ∨ nextPC pc op = code.size)

instance (code : ByteArray) (sites : List Nat) (pc : Nat) :
    Decidable (SiteOK code sites pc) := by
  unfold SiteOK
  cases opcodeAt code pc with
  | none => infer_instance
  | some pair =>
    rcases pair with ⟨op, arg⟩
    infer_instance

def depositSites : List Nat :=
  [0, 1, 22, 23, 26, 27, 28, 29, 30, 63, 64, 67, 68, 70, 71, 73, 74, 75,
   77, 78, 79, 81, 82, 83, 85, 86, 87, 88, 89, 91, 92, 94, 95, 96, 98, 99,
   100, 101, 102, 103, 104, 105, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118,
   119, 121, 122, 123, 124, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 139,
   140, 142, 143, 144, 147, 148, 149, 152, 153, 154, 155, 157, 158, 159, 160, 161, 162, 163,
   166, 167, 169, 170, 179, 180, 181, 186, 187, 190, 191, 196, 197, 198, 199, 200, 201, 204,
   205, 207, 208, 210, 211, 213, 214, 216, 217, 218, 220, 221, 223, 224, 225, 226, 227, 228,
   230, 231, 233, 234, 235, 236, 238, 239, 241, 242, 243, 244, 246, 247, 249, 250, 251, 252,
   254, 255, 257, 258, 259, 260, 262, 263, 265, 266, 267, 268, 270, 271, 272, 273, 275, 276,
   277, 279, 280, 282, 283, 284, 285, 287, 288, 290, 291, 292, 293, 294, 295, 297, 298, 301,
   302, 303, 305, 306, 307, 308, 309, 310, 311, 314, 315, 316, 317, 318, 320, 321, 323, 324,
   325, 327, 328, 329, 330, 331, 332, 334, 335, 336, 338, 339, 340, 341, 342, 344, 345, 346,
   348, 349, 350, 351, 352, 353, 355, 356, 365, 366, 367, 369, 370, 371, 373, 374, 375, 377,
   378, 379, 380, 382, 383, 384, 386, 387, 388, 389, 391, 392, 393, 395, 396, 397, 398, 400,
   401, 402, 404, 405, 406, 407, 409, 410, 411, 413, 414, 415, 416, 418, 419, 420, 422, 423,
   424, 425, 427, 428, 429, 431, 432, 433, 434, 436, 437, 438, 440, 441, 442, 443, 444, 446,
   447, 448, 450, 451, 452, 453, 454, 456, 457, 458, 460, 461, 462, 463, 464, 466, 467, 470,
   471, 472, 473, 474, 475, 476, 477, 480, 481, 482, 484, 485, 488, 489, 490, 491, 492, 493,
   495, 496, 497, 499, 500, 501, 502, 505, 506, 507, 508, 510, 511, 512, 545, 546, 549, 550,
   552, 553, 554, 555, 556, 559, 560, 561, 562, 563, 564, 567, 568, 569, 570, 572, 573, 574,
   577, 578, 579, 612, 613, 614, 615, 616, 618, 619, 621, 622, 623, 624, 625, 626, 627]

def exitSites : List Nat :=
  [0, 1, 22, 23, 25, 26, 27, 28, 29, 62, 63, 66, 67, 69, 70, 72, 73, 74,
   76, 77, 78, 80, 81, 82, 84, 85, 86, 87, 88, 90, 91, 93, 94, 95, 97, 98,
   99, 100, 101, 102, 103, 104, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117,
   118, 120, 121, 122, 123, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 138,
   139, 141, 142, 143, 146, 147, 148, 151, 152, 153, 154, 156, 157, 158, 159, 160, 161, 164,
   165, 167, 168, 170, 171, 173, 174, 176, 177, 178, 180, 181, 183, 184, 185, 186, 187, 189,
   190, 191, 192, 193, 194, 196, 197, 199, 200, 201, 202, 203, 205, 206, 207, 208, 210, 211,
   213, 214, 216, 217, 218, 220, 221, 223, 224, 225, 226, 228, 229, 231, 232, 233, 234, 235,
   236, 238, 239, 241, 242, 243, 245, 246, 247, 248, 249, 250, 251, 254, 255, 256, 257, 258,
   260, 261, 263, 264, 265, 267, 268, 269, 270, 272, 273, 274, 275, 277, 278, 279, 281, 282,
   283, 284, 285, 287, 288, 289, 291, 292, 293, 294, 295, 297, 298, 300, 301, 302, 303, 304,
   305, 306, 307, 310, 311, 312, 314, 315, 318, 319, 320, 321, 322, 323, 325, 326, 327, 329,
   330, 331, 332, 335, 336, 337, 338, 340, 341, 342, 375, 376, 379, 380, 382, 383, 384, 385,
   386, 389, 390, 391, 392, 393, 394, 397, 398, 399, 400, 402, 403, 404, 407, 408, 409, 442,
   443, 444, 445, 446, 448, 449, 451, 452, 453, 454, 455, 456, 457]

theorem deposit_checked : ∀ pc ∈ depositSites,
    SiteOK depositRuntime depositSites pc := by
  decide +kernel

theorem exit_checked : ∀ pc ∈ exitSites,
    SiteOK exitRuntime exitSites pc := by
  decide +kernel

private theorem boundary_mem {code : ByteArray} {sites : List Nat}
    (zero : 0 ∈ sites) (checked : ∀ pc ∈ sites, SiteOK code sites pc)
    {pc : Nat} (h : Boundary code pc) : pc ∈ sites := by
  induction h with
  | start => exact zero
  | @next pc op arg before decoded inside ih =>
    have hs := checked pc ih
    simp only [SiteOK, decoded] at hs
    rcases hs.2.2 with hm | he
    · exact hm
    · omega

theorem deposit_boundary_mem {pc : Nat} (h : Boundary depositRuntime pc) :
    pc ∈ depositSites :=
  boundary_mem (by decide +kernel) deposit_checked h

theorem exit_boundary_mem {pc : Nat} (h : Boundary exitRuntime pc) :
    pc ∈ exitSites :=
  boundary_mem (by decide +kernel) exit_checked h

/-- The explicit subset excludes gas observation and every recursive child
opcode, as well as SELFDESTRUCT. -/
theorem allowed_excludes : ∀ op ∈ allowedOps,
    op ≠ .GAS ∧ op.isCall = false ∧ op.isCreate = false ∧
      op ≠ .SELFDESTRUCT := by
  decide +kernel

private theorem scoped_decode {code : ByteArray} {sites : List Nat} {pc : Nat}
    (h : SiteOK code sites pc) {op : Operation .EVM}
    {arg : Option (UInt256 × Nat)}
    (hd : opcodeAt code pc = some (op, arg)) : op ∈ allowedOps := by
  simp only [SiteOK, hd] at h
  exact h.2.1

theorem deposit_decode_scope {pc : Nat} (h : Boundary depositRuntime pc)
    {op : Operation .EVM} {arg : Option (UInt256 × Nat)}
    (hd : opcodeAt depositRuntime pc = some (op, arg)) : op ∈ allowedOps :=
  scoped_decode (deposit_checked pc (deposit_boundary_mem h)) hd

theorem exit_decode_scope {pc : Nat} (h : Boundary exitRuntime pc)
    {op : Operation .EVM} {arg : Option (UInt256 × Nat)}
    (hd : opcodeAt exitRuntime pc = some (op, arg)) : op ∈ allowedOps :=
  scoped_decode (exit_checked pc (exit_boundary_mem h)) hd

/-- Existing D_J tables land on listed decoded JUMPDESTs, not PUSH data. -/
private theorem deposit_jump_checked : ∀ n ∈ depositJumpdestNats,
    (UInt256.ofNat n).toNat ∈ depositSites ∧
    opcodeAt depositRuntime (UInt256.ofNat n).toNat = some (.JUMPDEST, none) := by
  decide +kernel

private theorem exit_jump_checked : ∀ n ∈ exitJumpdestNats,
    (UInt256.ofNat n).toNat ∈ exitSites ∧
    opcodeAt exitRuntime (UInt256.ofNat n).toNat = some (.JUMPDEST, none) := by
  decide +kernel

theorem deposit_jump_scope {pc : UInt256} (h : pc ∈ D_J depositRuntime ⟨0⟩) :
    pc.toNat ∈ depositSites ∧
    opcodeAt depositRuntime pc.toNat = some (.JUMPDEST, none) := by
  rw [deposit_D_J] at h
  obtain ⟨n, hn, rfl⟩ : ∃ n ∈ depositJumpdestNats, UInt256.ofNat n = pc := by
    simpa only [depositJumpdests, List.mem_toArray, List.mem_map] using h
  exact deposit_jump_checked n hn

theorem exit_jump_scope {pc : UInt256} (h : pc ∈ D_J exitRuntime ⟨0⟩) :
    pc.toNat ∈ exitSites ∧
    opcodeAt exitRuntime pc.toNat = some (.JUMPDEST, none) := by
  rw [exit_D_J] at h
  obtain ⟨n, hn, rfl⟩ : ∃ n ∈ exitJumpdestNats, UInt256.ofNat n = pc := by
    simpa only [exitJumpdests, List.mem_toArray, List.mem_map] using h
  exact exit_jump_checked n hn

#print axioms deposit_checked
#print axioms exit_checked
#print axioms deposit_decode_scope
#print axioms exit_decode_scope
#print axioms allowed_excludes
#print axioms deposit_jump_scope
#print axioms exit_jump_scope

end Eip8282.Audit.Integrator.RuntimeOpcodeScope
