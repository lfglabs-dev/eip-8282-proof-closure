import Eip8282.Audit.Integrator.FactoryRuntimeEntry

/-! Finite decoder facts for five fixed images, using an audited transcription
of EL0cc100eb190b64b23baba72dac0165652eaec252 Amsterdam runtime.py's scanner.
Source-to-formalization is an explicit boundary; no executable-Python theorem
or arbitrary-bytecode decoder equivalence is asserted. Opcode tags use the
existing pinned parse table as a translation; the complete fixed-image checks
exclude Amsterdam's unsupported extended-immediate instructions. -/
namespace Eip8282.Audit.Integrator.ReferenceDecodeSites
open EvmYul EvmYul.EVM
open Eip8282.Audit.Bytecode
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

inductive Image where
  | deposit | exit | depositInit | exitInit | factory
  deriving DecidableEq

def code : Image → ByteArray
  | .deposit => depositRuntime | .exit => exitRuntime
  | .depositInit => Bytecode.depositInit | .exitInit => Bytecode.exitInit
  | .factory => FactoryRuntimeEntry.runtime

def pushWidth (op : UInt8) : Nat :=
  if 0x60 ≤ op.toNat ∧ op.toNat ≤ 0x7f then op.toNat-0x5f else 0

/-- Amsterdam skips one immediate for DUPN/SWAPN/EXCHANGE except their
explicit invalid ranges. An absent immediate is skipped too. -/
def scanWidth (bytes : ByteArray) (pc : Nat) (op : UInt8) : Nat :=
  if 0x60 ≤ op.toNat ∧ op.toNat ≤ 0x7f then op.toNat-0x5f
  else if op=0xe6 ∨ op=0xe7 then
    if (bytes[pc+1]?).any (fun b => 0x5b ≤ b.toNat && b.toNat ≤ 0x7f) then 0 else 1
  else if op=0xe8 then
    if (bytes[pc+1]?).any (fun b => 0x52 ≤ b.toNat && b.toNat ≤ 0x7f) then 0 else 1
  else 0

def scan (bytes : ByteArray) : Nat → Nat → List Nat
  | 0,_ => []
  | fuel+1,pc => match bytes[pc]? with
    | none => []
    | some op => pc :: scan bytes fuel (pc+1+scanWidth bytes pc op)

/-- Explicit finite tables are checked against the source-shaped scanner below. -/
def sites : Image → List Nat
  | .deposit => [0,1,22,23,26,27,28,29,30,63,64,67,68,70,71,73,74,75,77,78,79,81,82,83,85,86,87,88,89,91,92,94,95,96,98,99,100,101,102,103,104,105,107,108,109,110,111,112,113,114,115,116,117,118,119,121,122,123,124,126,127,128,129,130,131,132,133,134,135,136,137,139,140,142,143,144,147,148,149,152,153,154,155,157,158,159,160,161,162,163,166,167,169,170,179,180,181,186,187,190,191,196,197,198,199,200,201,204,205,207,208,210,211,213,214,216,217,218,220,221,223,224,225,226,227,228,230,231,233,234,235,236,238,239,241,242,243,244,246,247,249,250,251,252,254,255,257,258,259,260,262,263,265,266,267,268,270,271,272,273,275,276,277,279,280,282,283,284,285,287,288,290,291,292,293,294,295,297,298,301,302,303,305,306,307,308,309,310,311,314,315,316,317,318,320,321,323,324,325,327,328,329,330,331,332,334,335,336,338,339,340,341,342,344,345,346,348,349,350,351,352,353,355,356,365,366,367,369,370,371,373,374,375,377,378,379,380,382,383,384,386,387,388,389,391,392,393,395,396,397,398,400,401,402,404,405,406,407,409,410,411,413,414,415,416,418,419,420,422,423,424,425,427,428,429,431,432,433,434,436,437,438,440,441,442,443,444,446,447,448,450,451,452,453,454,456,457,458,460,461,462,463,464,466,467,470,471,472,473,474,475,476,477,480,481,482,484,485,488,489,490,491,492,493,495,496,497,499,500,501,502,505,506,507,508,510,511,512,545,546,549,550,552,553,554,555,556,559,560,561,562,563,564,567,568,569,570,572,573,574,577,578,579,612,613,614,615,616,618,619,621,622,623,624,625,626,627]
  | .exit => [0,1,22,23,25,26,27,28,29,62,63,66,67,69,70,72,73,74,76,77,78,80,81,82,84,85,86,87,88,90,91,93,94,95,97,98,99,100,101,102,103,104,106,107,108,109,110,111,112,113,114,115,116,117,118,120,121,122,123,125,126,127,128,129,130,131,132,133,134,135,136,138,139,141,142,143,146,147,148,151,152,153,154,156,157,158,159,160,161,164,165,167,168,170,171,173,174,176,177,178,180,181,183,184,185,186,187,189,190,191,192,193,194,196,197,199,200,201,202,203,205,206,207,208,210,211,213,214,216,217,218,220,221,223,224,225,226,228,229,231,232,233,234,235,236,238,239,241,242,243,245,246,247,248,249,250,251,254,255,256,257,258,260,261,263,264,265,267,268,269,270,272,273,274,275,277,278,279,281,282,283,284,285,287,288,289,291,292,293,294,295,297,298,300,301,302,303,304,305,306,307,310,311,312,314,315,318,319,320,321,322,323,325,326,327,329,330,331,332,335,336,337,338,340,341,342,375,376,379,380,382,383,384,385,386,389,390,391,392,393,394,397,398,399,400,402,403,404,407,408,409,442,443,444,445,446,448,449,451,452,453,454,455,456,457]
  | .depositInit => [0,3,4,6,7,8,9,10,11,32,33,36,37,38,39,40,73,74,77,78,80,81,83,84,85,87,88,89,91,92,93,95,96,97,98,99,101,102,104,105,106,108,109,110,111,112,113,114,115,117,118,119,120,121,122,123,124,125,126,127,128,129,131,132,133,134,136,137,138,139,140,141,142,143,144,145,146,147,149,150,152,153,154,157,158,159,162,163,164,165,167,168,169,170,171,172,173,176,177,179,180,189,190,191,196,197,200,201,206,207,208,209,210,211,214,215,217,218,220,221,223,224,226,227,228,230,231,233,234,235,236,237,238,240,241,243,244,245,246,248,249,251,252,253,254,256,257,259,260,261,262,264,265,267,268,269,270,272,273,275,276,277,278,280,281,282,283,285,286,287,289,290,292,293,294,295,297,298,300,301,302,303,304,305,307,308,311,312,313,315,316,317,318,319,320,321,324,325,326,327,328,330,331,333,334,335,337,338,339,340,341,342,344,345,346,348,349,350,351,352,354,355,356,358,359,360,361,362,363,365,366,375,376,377,379,380,381,383,384,385,387,388,389,390,392,393,394,396,397,398,399,401,402,403,405,406,407,408,410,411,412,414,415,416,417,419,420,421,423,424,425,426,428,429,430,432,433,434,435,437,438,439,441,442,443,444,446,447,448,450,451,452,453,454,456,457,458,460,461,462,463,464,466,467,468,470,471,472,473,474,476,477,480,481,482,483,484,485,486,487,490,491,492,494,495,498,499,500,501,502,503,505,506,507,509,510,511,512,515,516,517,518,520,521,522,555,556,559,560,562,563,564,565,566,569,570,571,572,573,574,577,578,579,580,582,583,584,587,588,589,622,623,624,625,626,628,629,631,632,633,634,635,636,637]
  | .exitInit => [0,33,34,35,38,39,41,42,43,44,45,46,67,68,70,71,72,73,74,107,108,111,112,114,115,117,118,119,121,122,123,125,126,127,129,130,131,132,133,135,136,138,139,140,142,143,144,145,146,147,148,149,151,152,153,154,155,156,157,158,159,160,161,162,163,165,166,167,168,170,171,172,173,174,175,176,177,178,179,180,181,183,184,186,187,188,191,192,193,196,197,198,199,201,202,203,204,205,206,209,210,212,213,215,216,218,219,221,222,223,225,226,228,229,230,231,232,234,235,236,237,238,239,241,242,244,245,246,247,248,250,251,252,253,255,256,258,259,261,262,263,265,266,268,269,270,271,273,274,276,277,278,279,280,281,283,284,286,287,288,290,291,292,293,294,295,296,299,300,301,302,303,305,306,308,309,310,312,313,314,315,317,318,319,320,322,323,324,326,327,328,329,330,332,333,334,336,337,338,339,340,342,343,345,346,347,348,349,350,351,352,355,356,357,359,360,363,364,365,366,367,368,370,371,372,374,375,376,377,380,381,382,383,385,386,387,420,421,424,425,427,428,429,430,431,434,435,436,437,438,439,442,443,444,445,447,448,449,452,453,454,487,488,489,490,491,493,494,496,497,498,499,500,501,502]
  | .factory => [0,33,34,35,37,38,40,41,42,43,44,45,46,47,48,49,50,51,53,54,55,56,57,58,59,60,61,62,63,64,66,68]

theorem scan_eq_sites (image : Image) : scan (code image) (code image).size 0 = sites image := by
  cases image <;> decide +kernel

#print axioms scan_eq_sites

def referenceJumps (image : Image) : List Nat :=
  (sites image).filter (fun pc => (code image)[pc]? == some 0x5b)

/-- Source buffer_read's right-zero-padding, expressed without host casts. -/
def paddedImmediate (bytes : ByteArray) (pc width : Nat) : ByteArray :=
  bytes.extract' (pc+1) (pc+1+width) ++
    ⟨(List.replicate (width-(bytes.size-(pc+1))) (0 : UInt8)).toArray⟩

/-- Local PUSH decode transcript. This does not interpret extended instructions;
fixed-image sites below exclude them and certify matching widths. -/
def referenceDecode (bytes : ByteArray) (pc : Nat) :
    Option (Operation .EVM × Option (UInt256 × Nat)) := do
  let tag ← bytes[pc]?
  let op ← parseInstr tag
  let width := pushWidth tag
  pure (op, if width=0 then none else some (uInt256OfByteArray (paddedImmediate bytes pc width),width))

def siteOK (image : Image) (pc : Nat) : Bool :=
  decide (pc < (code image).size) &&
  decide (pc+1+pushWidth ((code image)[pc]?.getD 0) ≤ (code image).size) &&
  !([0xe6,0xe7,0xe8] : List UInt8).contains ((code image)[pc]?.getD 0) &&
  decide (((parseInstr ((code image)[pc]?.getD 0)).map argOnNBytesOfInstr) =
    some (pushWidth ((code image)[pc]?.getD 0)))

theorem checked (image : Image) : (sites image).all (siteOK image) = true := by
  cases image <;> decide +kernel

#print axioms checked

theorem jumps_eq (image : Image) :
    D_J (code image) ⟨0⟩ = ((referenceJumps image).map UInt256.ofNat).toArray := by
  cases image <;> decide +kernel

#print axioms jumps_eq

theorem site_facts {image : Image} {pc : Nat} (hp : pc ∈ sites image) :
    pc < (code image).size ∧
    pc+1+pushWidth ((code image)[pc]?.getD 0) ≤ (code image).size ∧
    ¬ ((code image)[pc]?.getD 0) ∈ ([0xe6,0xe7,0xe8] : List UInt8) ∧
    ((parseInstr ((code image)[pc]?.getD 0)).map argOnNBytesOfInstr) =
      some (pushWidth ((code image)[pc]?.getD 0)) := by
  have h := List.all_eq_true.mp (checked image) pc hp
  simp only [siteOK,Bool.and_eq_true,decide_eq_true_eq,and_assoc] at h
  obtain ⟨hpc,hspan,hn,hw⟩ := h
  refine ⟨hpc,hspan,?_,hw⟩
  intro hm
  rw [List.contains_iff_mem.mpr hm] at hn
  cases hn

private theorem decode_eq_of_facts (bytes : ByteArray) (pc : Nat) (tag : UInt8)
    (op : Operation .EVM) (hpc : pc < UInt256.size)
    (htag : bytes[pc]? = some tag) (hop : parseInstr tag = some op)
    (hw : argOnNBytesOfInstr op = pushWidth tag)
    (hspan : pc+1+pushWidth tag ≤ bytes.size) :
    decode bytes (UInt256.ofNat pc) = referenceDecode bytes pc := by
  have hn : (UInt256.ofNat pc).toNat = pc := Eip8282.Audit.EntryReach.toNat_ofNat_lit _ hpc
  have hz : pushWidth tag - (bytes.size-(pc+1)) = 0 := by omega
  unfold decode referenceDecode
  rw [hn]
  change (bytes[pc]? >>= parseInstr >>= fun op => some (op,
      if argOnNBytesOfInstr op == 0 then none else
        some (uInt256OfByteArray (bytes.extract' (pc+1) (pc+1+argOnNBytesOfInstr op)),argOnNBytesOfInstr op))) = _
  rw [htag]
  have hempty (b : ByteArray) : b ++ (⟨#[]⟩ : ByteArray) = b := by
    ext1
    simp
  simp [hop,hw,paddedImmediate,hz,hempty]

theorem decode_eq {image : Image} {pc : Nat} (hp : pc ∈ sites image) :
    decode (code image) (UInt256.ofNat pc) = referenceDecode (code image) pc := by
  obtain ⟨hpc,hspan,_,hw⟩ := site_facts hp
  have hsize : (code image).size < UInt256.size := by cases image <;> decide
  have htag : (code image)[pc]? = some ((code image)[pc]?.getD 0) := by
    change (code image).data[pc]? = some ((code image).data[pc]?.getD 0)
    rw [Array.getElem?_eq_getElem (xs := (code image).data) hpc]
    rfl
  obtain ⟨op,hop,he⟩ := Option.map_eq_some_iff.mp hw
  exact decode_eq_of_facts (code image) pc _ op (hpc.trans hsize) htag hop he hspan

/-- A generic malformed PUSH is deliberately outside the finite-image scope. -/
def truncatedPush : ByteArray := ⟨#[0x61,0x01]⟩

theorem truncated_push_actual :
    decode truncatedPush ⟨0⟩ = some (.PUSH2,some (UInt256.ofNat 1,2)) := by decide +kernel

theorem truncated_push_reference :
    referenceDecode truncatedPush 0 = some (.PUSH2,some (UInt256.ofNat 256,2)) := by decide +kernel

theorem truncated_push_differs : decode truncatedPush ⟨0⟩ ≠ referenceDecode truncatedPush 0 := by
  rw [truncated_push_actual,truncated_push_reference]
  decide +kernel

#print axioms site_facts
#print axioms decode_eq
#print axioms truncated_push_differs
end Eip8282.Audit.Integrator.ReferenceDecodeSites
