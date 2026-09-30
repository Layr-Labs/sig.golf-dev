import SigGolfCandidate.Packed.ExpandRun
import SigGolfCandidate.Rv.Api
import SigGolfCandidate.Packed.Radix27Codec
import SigGolfCandidate.Packed.Images
import SigGolfCandidate.Packed.ByteCodec
import SigGolfCandidate.Expand.Loop
import SigGolfCandidate.Submission
import SigGolfCandidate.Packed.ExpandMain
import SigGolfCandidate.Expand.Mem
import SigGolfCandidate.Ref
import SigGolfCandidate.Rv
import SigGolfCandidate.Verify.Swar
import SigGolfCandidate.Packed.Submission
/-! Auto-collected 13-byte codec certificate. Each section preserves a checked scratch module. -/


section -- Radix27Quotient

namespace Radix27Quotient
open RiscvZkvm.Rv64

abbrev q1 (t : Word) : Word := rv64_divu t (27#64)
abbrev q2 (t : Word) : Word := rv64_divu (q1 t) (27#64)
abbrev q3 (t : Word) : Word := rv64_divu (q2 t) (27#64)
abbrev q4 (t : Word) : Word := rv64_divu (q3 t) (27#64)

theorem div27_nat (t : Word) : (rv64_divu t (27#64)).toNat = t.toNat / 27 := by
  simp [rv64_divu, BitVec.toNat_udiv]

theorem rem27_nat (t : Word) : (rv64_remu t (27#64)).toNat = t.toNat % 27 := by
  simp [rv64_remu, BitVec.toNat_umod]

theorem q1_nat (t : Word) : (q1 t).toNat = t.toNat / 27 := div27_nat t

theorem q2_nat (t : Word) : (q2 t).toNat = t.toNat / 729 := by
  simp only [q2, div27_nat, Nat.div_div_eq_div_mul]

theorem q3_nat (t : Word) : (q3 t).toNat = t.toNat / 19683 := by
  simp only [q3, div27_nat, Nat.div_div_eq_div_mul]

theorem q4_nat (t : Word) : (q4 t).toNat = t.toNat / 531441 := by
  simp only [q4, div27_nat, Nat.div_div_eq_div_mul]

theorem digit0_nat (t : Word) : (rv64_remu t (27#64)).toNat = t.toNat % 27 := rem27_nat t

theorem digit1_nat (t : Word) : (rv64_remu (q1 t) (27#64)).toNat = t.toNat / 27 % 27 := by
  rw [rem27_nat, q1_nat]

theorem digit2_nat (t : Word) : (rv64_remu (q2 t) (27#64)).toNat = t.toNat / 729 % 27 := by
  rw [rem27_nat, q2_nat]

theorem digit3_nat (t : Word) : (rv64_remu (q3 t) (27#64)).toNat = t.toNat / 19683 % 27 := by
  rw [rem27_nat, q3_nat]

theorem digit4_nat (t : Word) : (rv64_remu (q4 t) (27#64)).toNat = t.toNat / 531441 % 27 := by
  rw [rem27_nat, q4_nat]

theorem combine_low0 (d : Word) (w : BitVec 32) :
    (((d <<< 16) ||| (((w.zeroExtend 64) <<< 48) >>> 48)).truncate 32) =
      d.truncate 16 ++ w.extractLsb' 0 16 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_append,
    BitVec.getLsbD_extractLsb', BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth]
  interval_cases i <;> simp [BitVec.getLsbD_ofNat, Nat.testBit]

theorem combine_low1 (d : Word) (w : BitVec 32) :
    (((d <<< 16) ||| ((w.zeroExtend 64) >>> 16)).truncate 32) =
      d.truncate 16 ++ w.extractLsb' 16 16 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_append,
    BitVec.getLsbD_extractLsb', BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth]
  interval_cases i <;> simp [BitVec.getLsbD_ofNat, Nat.testBit]

theorem digit_to_high16 (d : Word) : d.truncate 16 = BitVec.ofNat 16 d.toNat := by
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]

#print axioms digit4_nat
#print axioms combine_low0
#print axioms combine_low1
end Radix27Quotient


end


section -- Radix27ValidWord

namespace SigGolfCandidate.Radix27Sym
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open RiscvZkvm.Rv64
set_option maxRecDepth 100000
def signTail : List (BitVec 32) := [
  0x00036483, 0x00436503, 0x00836583, 0x00c36603, 0x01036683, 0x00400937, 0x006519b7, 0xd9598993,
  0x00dafab7, 0x26ba8a93, 0x01b00813, 0x0124e463, 0x0734e463, 0x0106d713, 0x07077e63, 0x03070733,
  0x01065a13, 0x070a7863, 0x01470733, 0x03070733, 0x0105da13, 0x070a7063, 0x01470733, 0x03070733,
  0x01055a13, 0x050a7863, 0x01470733, 0x03070733, 0x0104da13, 0x050a7063, 0x01470733, 0x00939023,
  0x00a39123, 0x00b39223, 0x00c39323, 0x03069893, 0x0308d893, 0x02c0006f, 0x41248733, 0x01570733,
  0x00a3a023, 0x00b3a223, 0x03061893, 0x0308d893, 0x0100006f, 0x0003b023, 0x00000893, 0x000a8713,
  0x01071793, 0x0117e7b3, 0x00f3a423, 0x01075793, 0x00f38623, 0x00100293, 0x00000513, 0x00000073
]

def expandTail : List (BitVec 32) := [
  0x00036483, 0x00436503, 0x00836583, 0x00c34603, 0x0105d693, 0x01061613, 0x00c6e6b3, 0x00daf737,
  0x26b70713, 0x01b00813, 0x08e6f463, 0x0306f7b3, 0x0306d6b3, 0x01079793, 0x03049893, 0x0308d893,
  0x0117e7b3, 0x00f3a023, 0x0306f7b3, 0x0306d6b3, 0x01079793, 0x0104d893, 0x0117e7b3, 0x00f3a223,
  0x0306f7b3, 0x0306d6b3, 0x01079793, 0x03051893, 0x0308d893, 0x0117e7b3, 0x00f3a423, 0x0306f7b3,
  0x0306d6b3, 0x01079793, 0x01055893, 0x0117e7b3, 0x00f3a623, 0x0306f7b3, 0x01079793, 0x03059893,
  0x0308d893, 0x0117e7b3, 0x00f3a823, 0x02c0006f, 0x40e687b3, 0x004008b7, 0x011787b3, 0x00f3a023,
  0x0093a223, 0x00a3a423, 0x03059793, 0x0307d793, 0x00f3a623, 0x0003a823, 0x00100293, 0x00000513,
  0x00000073
]


sym_block signFirst := symRun {} (signTail.take 12) (BitVec.ofNat 64 (0x1000 + 4*2935)) 20
sym_block expandFirst := symRun {} (expandTail.take 11) (BitVec.ofNat 64 (0x1000 + 4*15)) 20
sym_block signSecond := symRun {} ((signTail.drop 12).take 1) (BitVec.ofNat 64 (0x1000 + 4*2947)) 100
sym_block signValid0 := symRun {} ((signTail.drop 13).take 2) (BitVec.ofNat 64 (0x1000 + 4*2948)) 100
sym_block signValid1 := symRun {} ((signTail.drop 15).take 3) (BitVec.ofNat 64 (0x1000 + 4*2950)) 100
sym_block signValid2 := symRun {} ((signTail.drop 18).take 4) (BitVec.ofNat 64 (0x1000 + 4*2953)) 100
sym_block signValid3 := symRun {} ((signTail.drop 22).take 4) (BitVec.ofNat 64 (0x1000 + 4*2957)) 100
sym_block signValid4 := symRun {} ((signTail.drop 26).take 4) (BitVec.ofNat 64 (0x1000 + 4*2961)) 100
sym_block signValidEnd := symRun {} ((signTail.drop 30).take 8) (BitVec.ofNat 64 (0x1000 + 4*2965)) 100
sym_block signReserved := symRun {} ((signTail.drop 38).take 7) (BitVec.ofNat 64 (0x1000 + 4*2973)) 100
sym_block signFallback := symRun {} ((signTail.drop 45).take 3) (BitVec.ofNat 64 (0x1000 + 4*2980)) 100
sym_block signTrailer := symRun {} ((signTail.drop 48).take 8) (BitVec.ofNat 64 (0x1000 + 4*2983)) 100
sym_block expandValid := symRun {} ((expandTail.drop 11).take 33) (BitVec.ofNat 64 (0x1000 + 4*26)) 100
sym_block expandReserved := symRun {} ((expandTail.drop 44).take 10) (BitVec.ofNat 64 (0x1000 + 4*59)) 100
sym_block expandDone := symRun {} ((expandTail.drop 54).take 3) (BitVec.ofNat 64 (0x1000 + 4*69)) 100


def vlow0 (s : MachineState) : BitVec 32 :=
  (((rv64_remu (s.getReg .x13) (27#64)) <<< 16) |||
    (((s.getReg .x9) <<< 48) >>> 48)).truncate 32

def vlow1 (s : MachineState) : BitVec 32 :=
  (((rv64_remu (rv64_divu (s.getReg .x13) (27#64)) (27#64)) <<< 16) |||
    ((s.getReg .x9) >>> 16)).truncate 32

def q1 (s : MachineState) : Word := rv64_divu (s.getReg .x13) (27#64)
def q2 (s : MachineState) : Word := rv64_divu (q1 s) (27#64)
def q3 (s : MachineState) : Word := rv64_divu (q2 s) (27#64)
def q4 (s : MachineState) : Word := rv64_divu (q3 s) (27#64)

def vlow2 (s : MachineState) : BitVec 32 :=
  (((rv64_remu (q2 s) (27#64)) <<< 16) |||
    (((s.getReg .x10) <<< 48) >>> 48)).truncate 32

def vlow3 (s : MachineState) : BitVec 32 :=
  (((rv64_remu (q3 s) (27#64)) <<< 16) |||
    ((s.getReg .x10) >>> 16)).truncate 32

def vlow4 (s : MachineState) : BitVec 32 :=
  (((rv64_remu (q4 s) (27#64)) <<< 16) |||
    (((s.getReg .x11) <<< 48) >>> 48)).truncate 32

theorem valid_word0 (s : MachineState)
    (h7 : s.getReg .x7 = 0x20F0)
    (h16 : s.getReg .x16 = 27) :
    (expandValid.res.toState s).getMem (0x20F0) = vlow1 s ++ vlow0 s := by
  simp only [Result.toState_getMem, expandValid.res, memEval, Addr.eval,
    E.eval, BinOp.eval, StoreKind.merge, replaceWord32, vlow0, vlow1]
  simp only [h7, h16]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_or,
    BitVec.getLsbD_not, BitVec.getLsbD_append,
    BitVec.getLsbD_extractLsb', BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth]
  interval_cases i <;> simp [← BitVec.getLsbD_eq_getElem,
    BitVec.getLsbD_ofNat, Nat.testBit]

theorem valid_word1 (s : MachineState)
    (h7 : s.getReg .x7 = 0x20F0)
    (h16 : s.getReg .x16 = 27) :
    (expandValid.res.toState s).getMem (0x20F8) = vlow3 s ++ vlow2 s := by
  simp only [Result.toState_getMem, expandValid.res, memEval, Addr.eval,
    E.eval, BinOp.eval, StoreKind.merge, replaceWord32, vlow2, vlow3,
    q1, q2, q3]
  simp only [h7, h16]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_or,
    BitVec.getLsbD_not, BitVec.getLsbD_append,
    BitVec.getLsbD_extractLsb', BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth]
  interval_cases i <;> simp [← BitVec.getLsbD_eq_getElem,
    BitVec.getLsbD_ofNat, Nat.testBit]

theorem valid_word2 (s : MachineState)
    (h7 : s.getReg .x7 = 0x20F0)
    (h16 : s.getReg .x16 = 27) :
    ((expandValid.res.toState s).getMem (0x2100)).extractLsb' 0 32 = vlow4 s := by
  simp only [Result.toState_getMem, expandValid.res, memEval, Addr.eval,
    E.eval, BinOp.eval, StoreKind.merge, replaceWord32, vlow4,
    q1, q2, q3, q4]
  simp only [h7, h16]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_or,
    BitVec.getLsbD_not, BitVec.getLsbD_append,
    BitVec.getLsbD_extractLsb', BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth]
  interval_cases i <;> simp [← BitVec.getLsbD_eq_getElem,
    BitVec.getLsbD_ofNat, Nat.testBit]

#print axioms valid_word0
#print axioms valid_word1
#print axioms valid_word2
end SigGolfCandidate.Radix27Sym


end


section -- Radix27ExpandPureBridge

namespace Radix27ExpandPureBridge
open RiscvZkvm.Rv64 SigGolfCandidate.Radix27Sym Radix27Quotient Radix27

theorem validBlock_word1 (l : BitVec 80) (t : Nat) :
    word (validBlock l t) 1 = BitVec.ofNat 16 (t / 27 % 27) ++ lo16 l 1 := by
  unfold word validBlock lo16
  bv_normalize

theorem validBlock_word2 (l : BitVec 80) (t : Nat) :
    word (validBlock l t) 2 = BitVec.ofNat 16 (t / 729 % 27) ++ lo16 l 2 := by
  unfold word validBlock lo16
  bv_normalize

theorem validBlock_word3 (l : BitVec 80) (t : Nat) :
    word (validBlock l t) 3 = BitVec.ofNat 16 (t / 19683 % 27) ++ lo16 l 3 := by
  unfold word validBlock lo16
  bv_normalize

theorem validBlock_word4 (l : BitVec 80) (t : Nat) :
    word (validBlock l t) 4 = BitVec.ofNat 16 (t / 531441 % 27) ++ lo16 l 4 := by
  unfold word validBlock lo16
  bv_normalize

theorem vlow0_eq (s : MachineState) (l : BitVec 80) (t : Word)
    (h9 : s.getReg .x9 = (l.extractLsb' 0 32).zeroExtend 64)
    (h13 : s.getReg .x13 = t) :
    vlow0 s = word (validBlock l t.toNat) 0 := by
  unfold vlow0
  rw [h9, h13, combine_low0, Radix27.validBlock_word0]
  rw [digit_to_high16, digit0_nat]
  congr 1
  unfold lo16
  exact BitVec.extractLsb'_extractLsb'_of_le (by decide)

theorem vlow1_eq (s : MachineState) (l : BitVec 80) (t : Word)
    (h9 : s.getReg .x9 = (l.extractLsb' 0 32).zeroExtend 64)
    (h13 : s.getReg .x13 = t) :
    vlow1 s = word (validBlock l t.toNat) 1 := by
  unfold vlow1
  rw [h9, h13, combine_low1, validBlock_word1]
  rw [digit_to_high16, Radix27Quotient.digit1_nat]
  congr 1
  unfold lo16
  simpa only [show 16 * 1 = 16 by decide] using
    (BitVec.extractLsb'_extractLsb'_of_le (x := l) (start := 16)
      (len := 16) (len' := 32) (by decide))

theorem vlow2_eq (s : MachineState) (l : BitVec 80) (t : Word)
    (h10 : s.getReg .x10 = (l.extractLsb' 32 32).zeroExtend 64)
    (h13 : s.getReg .x13 = t) :
    vlow2 s = word (validBlock l t.toNat) 2 := by
  unfold vlow2 SigGolfCandidate.Radix27Sym.q2 SigGolfCandidate.Radix27Sym.q1
  rw [h10, h13, combine_low0, validBlock_word2]
  rw [digit_to_high16, Radix27Quotient.digit2_nat]
  congr 1
  unfold lo16
  simpa only [show 16 * 2 = 32 by decide] using
    (Radix27.extract_nested l 32 0 16 32 (by decide))

theorem vlow3_eq (s : MachineState) (l : BitVec 80) (t : Word)
    (h10 : s.getReg .x10 = (l.extractLsb' 32 32).zeroExtend 64)
    (h13 : s.getReg .x13 = t) :
    vlow3 s = word (validBlock l t.toNat) 3 := by
  unfold vlow3 SigGolfCandidate.Radix27Sym.q3 SigGolfCandidate.Radix27Sym.q2 SigGolfCandidate.Radix27Sym.q1
  rw [h10, h13, combine_low1, validBlock_word3]
  rw [digit_to_high16, Radix27Quotient.digit3_nat]
  congr 1
  unfold lo16
  simpa only [show 16 * 3 = 48 by decide] using
    (Radix27.extract_nested l 32 16 16 32 (by decide))

theorem vlow4_eq (s : MachineState) (l : BitVec 80) (t : Word)
    (h11 : s.getReg .x11 = ((s.getReg .x11).truncate 32).zeroExtend 64)
    (h11low : ((s.getReg .x11).truncate 32).extractLsb' 0 16 = lo16 l 4)
    (h13 : s.getReg .x13 = t) :
    vlow4 s = word (validBlock l t.toNat) 4 := by
  unfold vlow4 SigGolfCandidate.Radix27Sym.q4 SigGolfCandidate.Radix27Sym.q3
    SigGolfCandidate.Radix27Sym.q2 SigGolfCandidate.Radix27Sym.q1
  conv_lhs => rw [h11]
  rw [h13, combine_low0, validBlock_word4]
  rw [digit_to_high16, Radix27Quotient.digit4_nat, h11low]

#print axioms vlow0_eq
#print axioms vlow4_eq

end Radix27ExpandPureBridge


end


section -- Radix27MachineScratch

set_option maxRecDepth 100000

namespace SigGolfCandidate.Radix27Images
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv

abbrev sizes13 : Sizes := ⟨6397, 6404, CACHE_BYTES⟩

def signTail : List (BitVec 32) := [
  0x00036483, 0x00436503, 0x00836583, 0x00c36603, 0x01036683, 0x00400937, 0x006519b7, 0xd9598993,
  0x00dafab7, 0x26ba8a93, 0x01b00813, 0x0124e463, 0x0734e463, 0x0106d713, 0x07077e63, 0x03070733,
  0x01065a13, 0x070a7863, 0x01470733, 0x03070733, 0x0105da13, 0x070a7063, 0x01470733, 0x03070733,
  0x01055a13, 0x050a7863, 0x01470733, 0x03070733, 0x0104da13, 0x050a7063, 0x01470733, 0x00939023,
  0x00a39123, 0x00b39223, 0x00c39323, 0x03069893, 0x0308d893, 0x02c0006f, 0x41248733, 0x01570733,
  0x00a3a023, 0x00b3a223, 0x03061893, 0x0308d893, 0x0100006f, 0x0003b023, 0x00000893, 0x000a8713,
  0x01071793, 0x0117e7b3, 0x00f3a423, 0x01075793, 0x00f38623, 0x00100293, 0x00000513, 0x00000073
]

def expandTail : List (BitVec 32) := [
  0x00036483, 0x00436503, 0x00836583, 0x00c34603, 0x0105d693, 0x01061613, 0x00c6e6b3, 0x00daf737,
  0x26b70713, 0x01b00813, 0x08e6f463, 0x0306f7b3, 0x0306d6b3, 0x01079793, 0x03049893, 0x0308d893,
  0x0117e7b3, 0x00f3a023, 0x0306f7b3, 0x0306d6b3, 0x01079793, 0x0104d893, 0x0117e7b3, 0x00f3a223,
  0x0306f7b3, 0x0306d6b3, 0x01079793, 0x03051893, 0x0308d893, 0x0117e7b3, 0x00f3a423, 0x0306f7b3,
  0x0306d6b3, 0x01079793, 0x01055893, 0x0117e7b3, 0x00f3a623, 0x0306f7b3, 0x01079793, 0x03059893,
  0x0308d893, 0x0117e7b3, 0x00f3a823, 0x02c0006f, 0x40e687b3, 0x004008b7, 0x011787b3, 0x00f3a023,
  0x0093a223, 0x00a3a423, 0x03059793, 0x0307d793, 0x00f3a623, 0x0003a823, 0x00100293, 0x00000513,
  0x00000073
]

def signCode : List (BitVec 32) :=
  SigGolfCandidate.Images.signCode.take 2800 ++
  SigGolfCandidate.Images.expandCode.take 120 ++
  SigGolfCandidate.Packed.Images.signBodyPrelude ++ SigGolfCandidate.Expand.loopCode ++
  SigGolfCandidate.Packed.Images.signCounterPrelude ++ signTail

def expandCode : List (BitVec 32) :=
  SigGolfCandidate.Packed.Images.expandBodyPrelude ++ SigGolfCandidate.Expand.loopCode ++
  SigGolfCandidate.Packed.Images.expandCounterPrelude ++ expandTail

def signImage : Riscv.Image := ⟨signCode, SigGolfCandidate.Images.signData⟩
def expandImage : Riscv.Image := ⟨expandCode, []⟩

example : signCode.length = 2991 := by decide
example : expandCode.length = 72 := by decide

theorem sign_valid : signImage.Valid sizes13 SigGolfCandidate.Images.layout := by decide +kernel
theorem expand_valid : expandImage.Valid sizes13 SigGolfCandidate.Images.layout := by decide +kernel


def signL : Rv.Layout :=
  [(0, signCode.take 2935),
   (2935, signTail.take 12),
   (2947, (signTail.drop 12).take 1),
   (2948, (signTail.drop 13).take 2),
   (2950, (signTail.drop 15).take 3),
   (2953, (signTail.drop 18).take 4),
   (2957, (signTail.drop 22).take 4),
   (2961, (signTail.drop 26).take 4),
   (2965, (signTail.drop 30).take 8),
   (2973, (signTail.drop 38).take 7),
   (2980, (signTail.drop 45).take 3),
   (2983, (signTail.drop 48).take 8)]

def expandL : Rv.Layout :=
  [(0, expandCode.take 15), (15, expandTail.take 11),
   (26, (expandTail.drop 11).take 33),
   (59, (expandTail.drop 44).take 10),
   (69, (expandTail.drop 54).take 3)]

theorem signL_ok : layoutOk 0 signL = true := by decide +kernel
theorem expandL_ok : layoutOk 0 expandL = true := by decide +kernel
theorem signL_eq : signImage.code = layoutCode signL := by decide +kernel
theorem expandL_eq : expandImage.code = layoutCode expandL := by decide +kernel

theorem codeAt_signFirst : CodeAt signImage (BitVec.ofNat 64 (0x1000 + 4*2935)) (signTail.take 12) :=
  codeAt_layout signL_eq signL_ok (i := 1) (by kernel_rfl) (by decide)
theorem codeAt_expandFirst : CodeAt expandImage (BitVec.ofNat 64 (0x1000 + 4*15)) (expandTail.take 11) :=
  codeAt_layout expandL_eq expandL_ok (i := 1) (by kernel_rfl) (by decide)

theorem codeAt_signSecond : CodeAt signImage (BitVec.ofNat 64 (0x1000 + 4*2947)) ((signTail.drop 12).take 1) :=
  codeAt_layout signL_eq signL_ok (i := 2) (by kernel_rfl) (by decide)
theorem codeAt_signValid0 : CodeAt signImage (BitVec.ofNat 64 (0x1000 + 4*2948)) ((signTail.drop 13).take 2) :=
  codeAt_layout signL_eq signL_ok (i := 3) (by kernel_rfl) (by decide)
theorem codeAt_signValid1 : CodeAt signImage (BitVec.ofNat 64 (0x1000 + 4*2950)) ((signTail.drop 15).take 3) :=
  codeAt_layout signL_eq signL_ok (i := 4) (by kernel_rfl) (by decide)
theorem codeAt_signValid2 : CodeAt signImage (BitVec.ofNat 64 (0x1000 + 4*2953)) ((signTail.drop 18).take 4) :=
  codeAt_layout signL_eq signL_ok (i := 5) (by kernel_rfl) (by decide)
theorem codeAt_signValid3 : CodeAt signImage (BitVec.ofNat 64 (0x1000 + 4*2957)) ((signTail.drop 22).take 4) :=
  codeAt_layout signL_eq signL_ok (i := 6) (by kernel_rfl) (by decide)
theorem codeAt_signValid4 : CodeAt signImage (BitVec.ofNat 64 (0x1000 + 4*2961)) ((signTail.drop 26).take 4) :=
  codeAt_layout signL_eq signL_ok (i := 7) (by kernel_rfl) (by decide)
theorem codeAt_signValidEnd : CodeAt signImage (BitVec.ofNat 64 (0x1000 + 4*2965)) ((signTail.drop 30).take 8) :=
  codeAt_layout signL_eq signL_ok (i := 8) (by kernel_rfl) (by decide)
theorem codeAt_signReserved : CodeAt signImage (BitVec.ofNat 64 (0x1000 + 4*2973)) ((signTail.drop 38).take 7) :=
  codeAt_layout signL_eq signL_ok (i := 9) (by kernel_rfl) (by decide)
theorem codeAt_signFallback : CodeAt signImage (BitVec.ofNat 64 (0x1000 + 4*2980)) ((signTail.drop 45).take 3) :=
  codeAt_layout signL_eq signL_ok (i := 10) (by kernel_rfl) (by decide)
theorem codeAt_signTrailer : CodeAt signImage (BitVec.ofNat 64 (0x1000 + 4*2983)) ((signTail.drop 48).take 8) :=
  codeAt_layout signL_eq signL_ok (i := 11) (by kernel_rfl) (by decide)
theorem codeAt_expandValid : CodeAt expandImage (BitVec.ofNat 64 (0x1000 + 4*26)) ((expandTail.drop 11).take 33) :=
  codeAt_layout expandL_eq expandL_ok (i := 2) (by kernel_rfl) (by decide)
theorem codeAt_expandReserved : CodeAt expandImage (BitVec.ofNat 64 (0x1000 + 4*59)) ((expandTail.drop 44).take 10) :=
  codeAt_layout expandL_eq expandL_ok (i := 3) (by kernel_rfl) (by decide)
theorem codeAt_expandDone : CodeAt expandImage (BitVec.ofNat 64 (0x1000 + 4*69)) ((expandTail.drop 54).take 3) :=
  codeAt_layout expandL_eq expandL_ok (i := 4) (by kernel_rfl) (by decide)

sym_block signFirst := symRun {} (signTail.take 12) (BitVec.ofNat 64 (0x1000 + 4*2935)) 20
sym_block expandFirst := symRun {} (expandTail.take 11) (BitVec.ofNat 64 (0x1000 + 4*15)) 20
sym_block signSecond := symRun {} ((signTail.drop 12).take 1) (BitVec.ofNat 64 (0x1000 + 4*2947)) 100
sym_block signValid0 := symRun {} ((signTail.drop 13).take 2) (BitVec.ofNat 64 (0x1000 + 4*2948)) 100
sym_block signValid1 := symRun {} ((signTail.drop 15).take 3) (BitVec.ofNat 64 (0x1000 + 4*2950)) 100
sym_block signValid2 := symRun {} ((signTail.drop 18).take 4) (BitVec.ofNat 64 (0x1000 + 4*2953)) 100
sym_block signValid3 := symRun {} ((signTail.drop 22).take 4) (BitVec.ofNat 64 (0x1000 + 4*2957)) 100
sym_block signValid4 := symRun {} ((signTail.drop 26).take 4) (BitVec.ofNat 64 (0x1000 + 4*2961)) 100
sym_block signValidEnd := symRun {} ((signTail.drop 30).take 8) (BitVec.ofNat 64 (0x1000 + 4*2965)) 100
sym_block signReserved := symRun {} ((signTail.drop 38).take 7) (BitVec.ofNat 64 (0x1000 + 4*2973)) 100
sym_block signFallback := symRun {} ((signTail.drop 45).take 3) (BitVec.ofNat 64 (0x1000 + 4*2980)) 100
sym_block signTrailer := symRun {} ((signTail.drop 48).take 8) (BitVec.ofNat 64 (0x1000 + 4*2983)) 100
sym_block expandValid := symRun {} ((expandTail.drop 11).take 33) (BitVec.ofNat 64 (0x1000 + 4*26)) 100
sym_block expandReserved := symRun {} ((expandTail.drop 44).take 10) (BitVec.ofNat 64 (0x1000 + 4*59)) 100
sym_block expandDone := symRun {} ((expandTail.drop 54).take 3) (BitVec.ofNat 64 (0x1000 + 4*69)) 100


theorem signFirst_steps (s : RiscvZkvm.Rv64.MachineState)
    (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4*2935))
    (h6 : s.getReg .x6 = BitVec.ofNat 64 0x20F0) :
    Steps signImage s 12 12 (signFirst.res.toState s) := by
  have ho : signFirst.res.obligs s := by
    simp only [signFirst.res, rv_simp]
    rw [h6]
    decide
  exact symRun_sound signFirst codeAt_signFirst s hpc ho

theorem signValidEnd_obligs (s : RiscvZkvm.Rv64.MachineState)
    (h7 : s.getReg .x7 = BitVec.ofNat 64 0x3F40) :
    signValidEnd.res.obligs s := by
  simp only [signValidEnd.res, rv_simp]
  rw [h7]
  decide

theorem expandValid_obligs (s : RiscvZkvm.Rv64.MachineState)
    (h7 : s.getReg .x7 = BitVec.ofNat 64 0x20F0) :
    expandValid.res.obligs s := by
  simp only [expandValid.res, rv_simp]
  rw [h7]
  decide

theorem signFirst_pc (s : RiscvZkvm.Rv64.MachineState)
    (h6 : s.getReg .x6 = BitVec.ofNat 64 0x20F0) :
    (signFirst.res.toState s).pc =
      if (s.getWord32 (BitVec.ofNat 64 0x20F0)).toNat < 4194304 then
        BitVec.ofNat 64 (0x1000 + 4*2948)
      else BitVec.ofNat 64 (0x1000 + 4*2947) := by
  simp only [Result.toState_pc, signFirst.res, rv_simp]
  simp only [h6]
  simp only [RiscvZkvm.Rv64.MachineState.getWord32, BitVec.ult_eq_decide,
    decide_eq_true_eq]
  have hv : (RiscvZkvm.Rv64.extractWord32 (s.getMem (8432#64)) 0).toNat < 2 ^ 64 := by
    have := BitVec.isLt (RiscvZkvm.Rv64.extractWord32 (s.getMem (8432#64)) 0)
    omega
  simp only [show RiscvZkvm.Rv64.alignToDword (8432#64) = 8432#64 by decide,
    show RiscvZkvm.Rv64.byteOffset (8432#64) = 0 by decide]
  change (RiscvZkvm.Rv64.extractWord32 (s.getMem (8432#64)) 0).toNat <
    18446744073709551616 at hv
  have hmod : (RiscvZkvm.Rv64.extractWord32 (s.getMem (8432#64)) 0).toNat %
      18446744073709551616 =
      (RiscvZkvm.Rv64.extractWord32 (s.getMem (8432#64)) 0).toNat :=
    Nat.mod_eq_of_lt hv
  simp [BitVec.zeroExtend, BitVec.toNat_setWidth, hmod]

theorem expandFirst_steps (s : RiscvZkvm.Rv64.MachineState)
    (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4*15))
    (h6 : s.getReg .x6 = BitVec.ofNat 64 0x3F40) :
    Steps expandImage s 11 11 (expandFirst.res.toState s) := by
  have ho : expandFirst.res.obligs s := by
    simp only [expandFirst.res, rv_simp]
    rw [h6]
    decide
  exact symRun_sound expandFirst codeAt_expandFirst s hpc ho

theorem expandFirst_pc (s : RiscvZkvm.Rv64.MachineState) :
    (expandFirst.res.toState s).pc =
      if 14348907 ≤ ((expandFirst.res.toState s).getReg .x13).toNat then
        BitVec.ofNat 64 (0x1000 + 4*59)
      else BitVec.ofNat 64 (0x1000 + 4*26) := by
  simp only [Result.toState_pc, Result.toState_getReg, expandFirst.res, rv_simp]
  simp [BitVec.ult_eq_decide, not_lt]

theorem expandTail_path (s : RiscvZkvm.Rv64.MachineState)
    (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4*15))
    (h6 : s.getReg .x6 = BitVec.ofNat 64 0x3F40)
    (h7 : s.getReg .x7 = BitVec.ofNat 64 0x20F0) :
    ∃ u k c, Steps expandImage s k c u ∧
      ((k = 46 ∧ c = 73) ∨ (k = 23 ∧ c = 23)) ∧
      fetch expandImage u = some (.base .ECALL) ∧
      u.getReg .x5 = 1 ∧ u.getReg .x10 = 0 := by
  let t := expandFirst.res.toState s
  have hs1 : Steps expandImage s 11 11 t := expandFirst_steps s hpc h6
  have ht7 : t.getReg .x7 = BitVec.ofNat 64 0x20F0 := by
    simpa only [t, Result.toState_getReg, expandFirst.res, rv_simp] using h7
  by_cases hr : 14348907 ≤ (t.getReg .x13).toNat
  · have htp : t.pc = BitVec.ofNat 64 (0x1000 + 4*59) := by
      simpa only [t, if_pos hr] using expandFirst_pc s
    have ho : expandReserved.res.obligs t := by
      simp only [expandReserved.res, rv_simp]
      rw [ht7]
      decide
    let v := expandReserved.res.toState t
    have hs2 : Steps expandImage t 10 10 v :=
      symRun_sound expandReserved codeAt_expandReserved t htp ho
    have hvp : v.pc = BitVec.ofNat 64 (0x1000 + 4*69) := by
      simp only [v, Result.toState_pc, expandReserved.res, rv_simp]
    have ho3 : expandDone.res.obligs v := by simp only [expandDone.res, rv_simp]
    let u := expandDone.res.toState v
    have hs3 : Steps expandImage v 2 2 u :=
      symRun_sound expandDone codeAt_expandDone v hvp ho3
    refine ⟨u, 23, 23, ?_, Or.inr ⟨rfl, rfl⟩, ?_, ?_, ?_⟩
    · simpa only [show 11 + (10 + 2) = 23 by decide] using hs1.trans (hs2.trans hs3)
    · exact symRun_ecall expandDone codeAt_expandDone v ho3 rfl
    · simp only [u, Result.toState_getReg, expandDone.res, rv_simp]
    · simp only [u, Result.toState_getReg, expandDone.res, rv_simp]
  · have htp : t.pc = BitVec.ofNat 64 (0x1000 + 4*26) := by
      simpa only [t, if_neg hr] using expandFirst_pc s
    have ho : expandValid.res.obligs t := expandValid_obligs t ht7
    let v := expandValid.res.toState t
    have hs2 : Steps expandImage t 33 60 v :=
      symRun_sound expandValid codeAt_expandValid t htp ho
    have hvp : v.pc = BitVec.ofNat 64 (0x1000 + 4*69) := by
      simp only [v, Result.toState_pc, expandValid.res, rv_simp]
    have ho3 : expandDone.res.obligs v := by simp only [expandDone.res, rv_simp]
    let u := expandDone.res.toState v
    have hs3 : Steps expandImage v 2 2 u :=
      symRun_sound expandDone codeAt_expandDone v hvp ho3
    refine ⟨u, 46, 73, ?_, Or.inl ⟨rfl, rfl⟩, ?_, ?_, ?_⟩
    · simpa only [show 11 + (33 + 2) = 46 by decide,
        show 11 + (60 + 2) = 73 by decide] using hs1.trans (hs2.trans hs3)
    · exact symRun_ecall expandDone codeAt_expandDone v ho3 rfl
    · simp only [u, Result.toState_getReg, expandDone.res, rv_simp]
    · simp only [u, Result.toState_getReg, expandDone.res, rv_simp]

#print axioms signFirst_steps
#print axioms expandTail_path

#print axioms sign_valid
#print axioms expand_valid
end SigGolfCandidate.Radix27Images


end


section -- Radix27Loaded

namespace Radix27Loaded
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Radix27Images
  SigGolfCandidate.Rv SigGolfCandidate.Packed SigGolfCandidate.Mem Radix27

def packedLoaded (s : MachineState) : BitVec 104 :=
  (s.getMem (BitVec.ofNat 64 0x3F48)).extractLsb' 0 40 ++
    s.getMem (BitVec.ofNat 64 0x3F40)

def lowLoaded (s : MachineState) : BitVec 80 :=
  (packedLoaded s).extractLsb' 0 80

def rankLoaded (s : MachineState) : BitVec 24 :=
  (packedLoaded s).extractLsb' 80 24

private theorem byteExtract (x : BitVec 64) (i : Nat) :
    extractByte x i = x.extractLsb' (8 * i) 8 := by
  simp only [extractByte, BitVec.truncate_eq_setWidth,
    BitVec.setWidth_ushiftRight_eq_extractLsb, Nat.mul_comm]

theorem packedLoaded_byte (s : MachineState) (j : Nat) (hj : j < 13) :
    s.getByte (BitVec.ofNat 64 (0x3F40 + j)) =
      (packedLoaded s).extractLsb' (8 * j) 8 := by
  have ha : alignToDword (BitVec.ofNat 64 (0x3F40 + j)) =
      BitVec.ofNat 64 (0x3F40 + 8 * (j / 8)) := by
    apply BitVec.eq_of_toNat_eq
    rw [alignToDword_toNat]
    simp only [BitVec.toNat_ofNat]
    omega
  have hb : byteOffset (BitVec.ofNat 64 (0x3F40 + j)) = j % 8 := by
    rw [byteOffset_ofNat (by omega)]
    omega
  simp only [MachineState.getByte]
  rw [ha, hb]
  by_cases hj0 : j < 8
  · have hd : j / 8 = 0 := by omega
    have hm : j % 8 = j := by omega
    simp only [hd, hm, Nat.mul_zero, Nat.add_zero]
    rw [byteExtract]
    unfold packedLoaded
    rw [BitVec.extractLsb'_append_eq_of_add_le (by omega : 8 * j + 8 ≤ 64)]
  · have hd : j / 8 = 1 := by omega
    have hm : j % 8 = j - 8 := by omega
    simp only [hd, hm, Nat.mul_one, Nat.reduceAdd]
    rw [byteExtract]
    unfold packedLoaded
    rw [BitVec.extractLsb'_append_eq_of_le (by omega : 64 ≤ 8 * j)]
    rw [Radix27.extract_nested (s.getMem (BitVec.ofNat 64 0x3F48)) 0
      (8 * j - 64) 8 40 (by omega)]
    congr 1
    omega

theorem packedLoaded_readBuffer (s : MachineState) :
    packedLoaded s = trailer13 (readBuffer s 0x2650 6397) := by
  calc
    packedLoaded s = readBuffer s 0x3F40 13 := by
      symm
      apply readBuffer_eq_of_bytes
      intro i hi
      rw [packedLoaded_byte s i hi]
      exact (getD_bytes (packedLoaded s) i hi).symm
    _ = trailer13 (readBuffer s 0x2650 6397) :=
      Radix27ByteCodec.readBuffer_trailer13 s

theorem first_x9 (s : MachineState)
    (h6 : s.getReg .x6 = BitVec.ofNat 64 0x3F40) :
    (expandFirst.res.toState s).getReg .x9 =
      ((lowLoaded s).extractLsb' 0 32).zeroExtend 64 := by
  have hlow : (lowLoaded s).extractLsb' 0 32 =
      extractWord32 (s.getMem (BitVec.ofNat 64 0x3F40)) 0 := by
    unfold lowLoaded packedLoaded
    rw [Radix27.extract_nested _ 0 0 32 80 (by decide)]
    rw [BitVec.extractLsb'_append_eq_of_add_le (by decide : 0 + 32 ≤ 64)]
    simp only [extractWord32, Nat.mul_zero, BitVec.ushiftRight_zero,
      BitVec.truncate_eq_setWidth, BitVec.setWidth_ushiftRight_eq_extractLsb]
  calc
    (expandFirst.res.toState s).getReg .x9 =
        (extractWord32 (s.getMem (BitVec.ofNat 64 0x3F40)) 0).zeroExtend 64 := by
      simp only [Result.toState_getReg, expandFirst.res, rv_simp, h6]
    _ = ((lowLoaded s).extractLsb' 0 32).zeroExtend 64 := by rw [hlow]

theorem first_x10 (s : MachineState)
    (h6 : s.getReg .x6 = BitVec.ofNat 64 0x3F40) :
    (expandFirst.res.toState s).getReg .x10 =
      ((lowLoaded s).extractLsb' 32 32).zeroExtend 64 := by
  have hlow : (lowLoaded s).extractLsb' 32 32 =
      extractWord32 (s.getMem (BitVec.ofNat 64 0x3F40)) 1 := by
    unfold lowLoaded packedLoaded
    rw [Radix27.extract_nested _ 0 32 32 80 (by decide)]
    rw [BitVec.extractLsb'_append_eq_of_add_le (by decide : 32 + 32 ≤ 64)]
    simp only [extractWord32, BitVec.truncate_eq_setWidth,
      BitVec.setWidth_ushiftRight_eq_extractLsb]
  calc
    (expandFirst.res.toState s).getReg .x10 =
        (extractWord32 (s.getMem (BitVec.ofNat 64 0x3F40)) 1).zeroExtend 64 := by
      simp only [Result.toState_getReg, expandFirst.res, rv_simp, h6]
    _ = ((lowLoaded s).extractLsb' 32 32).zeroExtend 64 := by rw [hlow]

theorem first_x11 (s : MachineState)
    (h6 : s.getReg .x6 = BitVec.ofNat 64 0x3F40) :
    (expandFirst.res.toState s).getReg .x11 =
      (extractWord32 (s.getMem (BitVec.ofNat 64 0x3F48)) 0).zeroExtend 64 := by
  simp only [Result.toState_getReg, expandFirst.res, rv_simp, h6]
  rw [show (16192#64) + (8#64) = (16200#64) by decide]

theorem first_x11low (s : MachineState)
    (h6 : s.getReg .x6 = BitVec.ofNat 64 0x3F40) :
    (((expandFirst.res.toState s).getReg .x11).truncate 32).extractLsb' 0 16 =
      lo16 (lowLoaded s) 4 := by
  rw [first_x11 s h6]
  have hlow : (lowLoaded s).extractLsb' 64 16 =
      (s.getMem (BitVec.ofNat 64 0x3F48)).extractLsb' 0 16 := by
    unfold lowLoaded packedLoaded
    rw [Radix27.extract_nested _ 0 64 16 80 (by decide)]
    rw [BitVec.extractLsb'_append_eq_of_le (by decide : 64 ≤ 64)]
    rw [Radix27.extract_nested _ 0 0 16 40 (by decide)]
  unfold lo16
  simp only [show 16 * 4 = 64 by decide, hlow]
  simp only [extractWord32, BitVec.truncate_eq_setWidth,
    BitVec.setWidth_ushiftRight_eq_extractLsb]
  simpa using (BitVec.extractLsb'_extractLsb'_of_le
    (x := s.getMem (BitVec.ofNat 64 0x3F48)) (start := 0) (len := 16)
    (len' := 32) (by decide))

theorem rankLoaded_eq (s : MachineState) :
    rankLoaded s = (s.getMem (BitVec.ofNat 64 0x3F48)).extractLsb' 16 24 := by
  unfold rankLoaded packedLoaded
  rw [BitVec.extractLsb'_append_eq_of_le (by decide : 64 ≤ 80)]
  rw [Radix27.extract_nested _ 0 16 24 40 (by decide)]

theorem first_x13 (s : MachineState)
    (h6 : s.getReg .x6 = BitVec.ofNat 64 0x3F40) :
    (expandFirst.res.toState s).getReg .x13 =
      (rankLoaded s).zeroExtend 64 := by
  rw [rankLoaded_eq]
  simp only [Result.toState_getReg, expandFirst.res, rv_simp, h6]
  simp only [extractWord32, extractByte, BitVec.truncate_eq_setWidth,
    BitVec.setWidth_ushiftRight_eq_extractLsb]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_not, BitVec.getLsbD_and,
    BitVec.getLsbD_append, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_setWidth]
  interval_cases i <;> simp [BitVec.getLsbD_ofNat, Nat.testBit]

theorem first_rank_toNat (s : MachineState)
    (h6 : s.getReg .x6 = BitVec.ofNat 64 0x3F40) :
    ((expandFirst.res.toState s).getReg .x13).toNat =
      (rankLoaded s).toNat := by
  rw [first_x13 s h6]
  have hr : (rankLoaded s).toNat < 2 ^ 64 := by
    have := BitVec.isLt (rankLoaded s)
    omega
  simp [BitVec.toNat_setWidth]
  norm_num at hr ⊢
  exact hr

theorem first_valid_words (s : MachineState)
    (h6 : s.getReg .x6 = BitVec.ofNat 64 0x3F40) :
    let f := expandFirst.res.toState s
    let l := lowLoaded s
    let t := (rankLoaded s).toNat
    SigGolfCandidate.Radix27Sym.vlow0 f = word (validBlock l t) 0 ∧
    SigGolfCandidate.Radix27Sym.vlow1 f = word (validBlock l t) 1 ∧
    SigGolfCandidate.Radix27Sym.vlow2 f = word (validBlock l t) 2 ∧
    SigGolfCandidate.Radix27Sym.vlow3 f = word (validBlock l t) 3 ∧
    SigGolfCandidate.Radix27Sym.vlow4 f = word (validBlock l t) 4 := by
  let f := expandFirst.res.toState s
  let l := lowLoaded s
  let t : Word := (rankLoaded s).zeroExtend 64
  have h9 : f.getReg .x9 = (l.extractLsb' 0 32).zeroExtend 64 := first_x9 s h6
  have h10 : f.getReg .x10 = (l.extractLsb' 32 32).zeroExtend 64 := first_x10 s h6
  have h11 : f.getReg .x11 = ((f.getReg .x11).truncate 32).zeroExtend 64 := by
    rw [first_x11 s h6]
    simp
  have h11low : ((f.getReg .x11).truncate 32).extractLsb' 0 16 = lo16 l 4 :=
    first_x11low s h6
  have h13 : f.getReg .x13 = t := first_x13 s h6
  have ht : t.toNat = (rankLoaded s).toNat := by
    have hr : (rankLoaded s).toNat < 2 ^ 64 := by
      have := BitVec.isLt (rankLoaded s)
      omega
    simp [t, BitVec.toNat_setWidth]
    norm_num at hr ⊢
    exact hr
  simp only [ht]
  exact ⟨Radix27ExpandPureBridge.vlow0_eq f l t h9 h13,
    Radix27ExpandPureBridge.vlow1_eq f l t h9 h13,
    Radix27ExpandPureBridge.vlow2_eq f l t h10 h13,
    Radix27ExpandPureBridge.vlow3_eq f l t h10 h13,
    Radix27ExpandPureBridge.vlow4_eq f l t h11 h11low h13⟩

#print axioms first_valid_words

#print axioms first_x9
end Radix27Loaded


end


section -- Radix27CounterMem

namespace Radix27CounterMem
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Packed
  SigGolfCandidate.Rv SigGolfCandidate.Mem

private theorem nestedExtract {w : Nat} (x : BitVec w) (a l b n : Nat)
    (h : b + n ≤ l) :
    (x.extractLsb' a l).extractLsb' b n = x.extractLsb' (a + b) n := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb']
  have hib : b + i < l := by omega
  simp [hi, hib, Nat.add_assoc]

private theorem byteExtract (x : BitVec 64) (i : Nat) :
    extractByte x i = x.extractLsb' (8 * i) 8 := by
  simp only [extractByte, BitVec.truncate_eq_setWidth,
    BitVec.setWidth_ushiftRight_eq_extractLsb, Nat.mul_comm]

theorem counter_byte_eq (u : MachineState) (q : BitVec 160)
    (h0 : u.getMem (BitVec.ofNat 64 0x20F0) = q.extractLsb' 0 64)
    (h1 : u.getMem (BitVec.ofNat 64 0x20F8) = q.extractLsb' 64 64)
    (h2 : (u.getMem (BitVec.ofNat 64 0x2100)).extractLsb' 0 32 =
      q.extractLsb' 128 32)
    (j : Nat) (hj : j < 20) :
    u.getByte (BitVec.ofNat 64 (0x20F0 + j)) = q.extractLsb' (8 * j) 8 := by
  have ha : alignToDword (BitVec.ofNat 64 (0x20F0 + j)) =
      BitVec.ofNat 64 (0x20F0 + 8 * (j / 8)) := by
    apply BitVec.eq_of_toNat_eq
    rw [alignToDword_toNat]
    simp only [BitVec.toNat_ofNat]
    omega
  have hb : byteOffset (BitVec.ofNat 64 (0x20F0 + j)) = j % 8 := by
    rw [byteOffset_ofNat (by omega)]
    omega
  simp only [MachineState.getByte]
  rw [ha, hb]
  by_cases hj0 : j < 8
  · have hd : j / 8 = 0 := by omega
    have hm : j % 8 = j := by omega
    simp only [hd, hm, Nat.mul_zero, Nat.add_zero]
    rw [h0, byteExtract]
    simpa only [Nat.zero_add] using
      nestedExtract q 0 64 (8 * j) 8 (by omega)
  · by_cases hj1 : j < 16
    · have hd : j / 8 = 1 := by omega
      have hm : j % 8 = j - 8 := by omega
      simp only [hd, hm, Nat.mul_one, Nat.reduceAdd]
      rw [h1, byteExtract]
      rw [nestedExtract q 64 64 (8 * (j - 8)) 8 (by omega)]
      congr 1
      omega
    · have hd : j / 8 = 2 := by omega
      have hm : j % 8 = j - 16 := by omega
      simp only [hd, hm, Nat.reduceMul, Nat.reduceAdd]
      let x := u.getMem (BitVec.ofNat 64 0x2100)
      calc
        extractByte x (j - 16) =
            (x.extractLsb' 0 32).extractLsb' (8 * (j - 16)) 8 := by
          rw [byteExtract]
          simpa only [Nat.zero_add] using
            (nestedExtract x 0 32 (8 * (j - 16)) 8 (by omega)).symm
        _ = (q.extractLsb' 128 32).extractLsb' (8 * (j - 16)) 8 := by
          exact congrArg (fun v : BitVec 32 => v.extractLsb' (8 * (j - 16)) 8) h2
        _ = q.extractLsb' (8 * j) 8 := by
          rw [nestedExtract q 128 32 (8 * (j - 16)) 8 (by omega)]
          congr 1
          omega

theorem counter_readBuffer_eq (u : MachineState) (q : BitVec 160)
    (h0 : u.getMem (BitVec.ofNat 64 0x20F0) = q.extractLsb' 0 64)
    (h1 : u.getMem (BitVec.ofNat 64 0x20F8) = q.extractLsb' 64 64)
    (h2 : (u.getMem (BitVec.ofNat 64 0x2100)).extractLsb' 0 32 =
      q.extractLsb' 128 32) :
    readBuffer u 0x20F0 20 = q := by
  apply readBuffer_eq_of_bytes
  intro j hj
  rw [counter_byte_eq u q h0 h1 h2 j hj]
  exact (getD_bytes q j hj).symm

#print axioms counter_readBuffer_eq
end Radix27CounterMem


end


section -- Radix27ExpandValidMem

namespace Radix27ExpandValidMem
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Radix27Images
  SigGolfCandidate.Rv Radix27
open SigGolfCandidate.Radix27Sym (vlow0 vlow1 vlow2 vlow3 vlow4)

theorem block_pair0 (q : BitVec 160) :
    word q 1 ++ word q 0 = q.extractLsb' 0 64 := by
  unfold word
  bv_normalize

theorem block_pair1 (q : BitVec 160) :
    word q 3 ++ word q 2 = q.extractLsb' 64 64 := by
  unfold word
  bv_normalize

theorem block_pair2 (q : BitVec 160) :
    word q 4 = q.extractLsb' 128 32 := by
  unfold word
  bv_normalize

theorem valid_counter_readBuffer (s : MachineState)
    (h6 : s.getReg .x6 = BitVec.ofNat 64 0x3F40)
    (h7 : s.getReg .x7 = BitVec.ofNat 64 0x20F0) :
    let f := expandFirst.res.toState s
    let v := expandValid.res.toState f
    readBuffer v 0x20F0 20 =
      validBlock (Radix27Loaded.lowLoaded s)
        (Radix27Loaded.rankLoaded s).toNat := by
  let f := expandFirst.res.toState s
  let v := expandValid.res.toState f
  let q := validBlock (Radix27Loaded.lowLoaded s)
    (Radix27Loaded.rankLoaded s).toNat
  have hf7 : f.getReg .x7 = BitVec.ofNat 64 0x20F0 := by
    simpa only [f, Result.toState_getReg, expandFirst.res, rv_simp] using h7
  have hf16 : f.getReg .x16 = 27 := by
    simp only [f, Result.toState_getReg, expandFirst.res, rv_simp]
  obtain ⟨h0, h1, h2, h3, h4⟩ := Radix27Loaded.first_valid_words s h6
  have hv0 : v.getMem (BitVec.ofNat 64 0x20F0) = q.extractLsb' 0 64 := by
    calc
      v.getMem (BitVec.ofNat 64 0x20F0) = vlow1 f ++ vlow0 f :=
        SigGolfCandidate.Radix27Sym.valid_word0 f hf7 hf16
      _ = word q 1 ++ word q 0 := by rw [h0, h1]
      _ = q.extractLsb' 0 64 := block_pair0 q
  have hv1 : v.getMem (BitVec.ofNat 64 0x20F8) = q.extractLsb' 64 64 := by
    calc
      v.getMem (BitVec.ofNat 64 0x20F8) = vlow3 f ++ vlow2 f :=
        SigGolfCandidate.Radix27Sym.valid_word1 f hf7 hf16
      _ = word q 3 ++ word q 2 := by rw [h2, h3]
      _ = q.extractLsb' 64 64 := block_pair1 q
  have hv2 : (v.getMem (BitVec.ofNat 64 0x2100)).extractLsb' 0 32 =
      q.extractLsb' 128 32 := by
    calc
      (v.getMem (BitVec.ofNat 64 0x2100)).extractLsb' 0 32 = vlow4 f :=
        SigGolfCandidate.Radix27Sym.valid_word2 f hf7 hf16
      _ = word q 4 := h4
      _ = q.extractLsb' 128 32 := block_pair2 q
  exact Radix27CounterMem.counter_readBuffer_eq v q hv0 hv1 hv2

#print axioms valid_counter_readBuffer
end Radix27ExpandValidMem


end


section -- Radix27ReservedOnly

namespace SigGolfCandidate.Radix27Sym
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv RiscvZkvm.Rv64

theorem reserved_word0 (s : RiscvZkvm.Rv64.MachineState)
    (h7 : s.getReg .x7 = 0x20F0)
    (h14 : s.getReg .x14 = 14348907) :
    (expandReserved.res.toState s).getMem (0x20F0) =
      (s.getReg .x9).truncate 32 ++
        (s.getReg .x13 - 14348907#64 + 4194304#64).truncate 32 := by
  simp only [Result.toState_getMem, expandReserved.res, memEval, Addr.eval,
    E.eval, BinOp.eval, StoreKind.merge, replaceWord32]
  simp only [h7, h14]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_or,
    BitVec.getLsbD_not, BitVec.getLsbD_append,
    BitVec.getLsbD_extractLsb', BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_setWidth]
  interval_cases i <;> simp [← BitVec.getLsbD_eq_getElem,
    BitVec.getLsbD_ofNat, Nat.testBit]

theorem reserved_word1 (s : RiscvZkvm.Rv64.MachineState)
    (h7 : s.getReg .x7 = 0x20F0) :
    (expandReserved.res.toState s).getMem (0x20F8) =
      ((0#16) ++ (s.getReg .x11).truncate 16) ++ (s.getReg .x10).truncate 32 := by
  simp only [Result.toState_getMem, expandReserved.res, memEval, Addr.eval,
    E.eval, BinOp.eval, StoreKind.merge, replaceWord32]
  simp only [h7]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_or,
    BitVec.getLsbD_not, BitVec.getLsbD_append,
    BitVec.getLsbD_extractLsb', BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_setWidth]
  interval_cases i <;> simp [← BitVec.getLsbD_eq_getElem,
    BitVec.getLsbD_ofNat, Nat.testBit]

theorem reserved_word2 (s : RiscvZkvm.Rv64.MachineState)
    (h7 : s.getReg .x7 = 0x20F0) :
    ((expandReserved.res.toState s).getMem (0x2100)).extractLsb' 0 32 = 0 := by
  simp only [Result.toState_getMem, expandReserved.res, memEval, Addr.eval,
    E.eval, BinOp.eval, StoreKind.merge, replaceWord32]
  simp only [h7]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_or,
    BitVec.getLsbD_not, BitVec.getLsbD_append,
    BitVec.getLsbD_extractLsb', BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_setWidth]
  interval_cases i <;> simp [← BitVec.getLsbD_eq_getElem,
    BitVec.getLsbD_ofNat, Nat.testBit]

#print axioms reserved_word0
#print axioms reserved_word1
#print axioms reserved_word2
end SigGolfCandidate.Radix27Sym


end


section -- Radix27ReservedBridge

namespace Radix27ReservedBridge
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Radix27Images
  SigGolfCandidate.Rv Radix27

theorem reserved_pair0 (l : BitVec 80) (t : Nat) :
    (reservedBlock l t).extractLsb' 0 64 =
      l.extractLsb' 0 32 ++ BitVec.ofNat 32 (4194304 + (t - 14348907)) := by
  unfold reservedBlock
  rw [BitVec.extractLsb'_append_eq_ite]
  simp only [show 0 < 32 by decide, show ¬ 0 + 64 ≤ 32 by decide,
    dite_true, dite_false]
  rw [BitVec.extractLsb'_append_eq_right]
  unfold lo16
  bv_normalize

theorem reserved_pair1 (l : BitVec 80) (t : Nat) :
    (reservedBlock l t).extractLsb' 64 64 =
      ((0#16) ++ lo16 l 4) ++ l.extractLsb' 32 32 := by
  unfold reservedBlock
  rw [BitVec.extractLsb'_append_eq_of_le (by decide : 32 ≤ 64)]
  rw [BitVec.extractLsb'_append_eq_of_le (by decide : 32 ≤ 32)]
  rw [BitVec.extractLsb'_append_eq_ite]
  simp only [show 0 < 32 by decide, show ¬ 0 + 64 ≤ 32 by decide,
    dite_true, dite_false]
  rw [BitVec.extractLsb'_append_eq_right]
  unfold lo16
  bv_normalize

theorem reserved_pair2 (l : BitVec 80) (t : Nat) :
    (reservedBlock l t).extractLsb' 128 32 = 0 := by
  unfold reservedBlock lo16
  bv_normalize

theorem marker_arithmetic (t : BitVec 24) (ht : 14348907 ≤ t.toNat) :
    ((t.zeroExtend 64 - (14348907#64) + (4194304#64)).truncate 32) =
      BitVec.ofNat 32 (4194304 + (t.toNat - 14348907)) := by
  bv_omega

theorem reserved_counter_readBuffer (s : MachineState)
    (h6 : s.getReg .x6 = BitVec.ofNat 64 0x3F40)
    (h7 : s.getReg .x7 = BitVec.ofNat 64 0x20F0)
    (ht : 14348907 ≤ (Radix27Loaded.rankLoaded s).toNat) :
    let f := expandFirst.res.toState s
    let v := expandReserved.res.toState f
    readBuffer v 0x20F0 20 =
      reservedBlock (Radix27Loaded.lowLoaded s)
        (Radix27Loaded.rankLoaded s).toNat := by
  let f := expandFirst.res.toState s
  let v := expandReserved.res.toState f
  let l := Radix27Loaded.lowLoaded s
  let t := Radix27Loaded.rankLoaded s
  let q := reservedBlock l t.toNat
  have hf7 : f.getReg .x7 = BitVec.ofNat 64 0x20F0 := by
    simpa only [f, Result.toState_getReg, expandFirst.res, rv_simp] using h7
  have hf14 : f.getReg .x14 = 14348907 := by
    simp only [f, Result.toState_getReg, expandFirst.res, rv_simp]
  have hf9 : f.getReg .x9 = (l.extractLsb' 0 32).zeroExtend 64 :=
    Radix27Loaded.first_x9 s h6
  have hf10 : f.getReg .x10 = (l.extractLsb' 32 32).zeroExtend 64 :=
    Radix27Loaded.first_x10 s h6
  have hf11 : (f.getReg .x11).truncate 16 = lo16 l 4 := by
    have hh := Radix27Loaded.first_x11low s h6
    have hh' : (f.getReg .x11).extractLsb' 0 16 = lo16 l 4 := by
      simpa only [f, l, BitVec.truncate_eq_setWidth,
        BitVec.extractLsb'_setWidth_of_le (by decide : 0 + 16 ≤ 32)] using hh
    simpa only [BitVec.truncate_eq_setWidth,
      ← BitVec.setWidth_ushiftRight_eq_extractLsb,
      BitVec.ushiftRight_zero] using hh'
  have hf13 : f.getReg .x13 = t.zeroExtend 64 :=
    Radix27Loaded.first_x13 s h6
  have hv0 : v.getMem (BitVec.ofNat 64 0x20F0) = q.extractLsb' 0 64 := by
    calc
      v.getMem (BitVec.ofNat 64 0x20F0) =
          (f.getReg .x9).truncate 32 ++
            (f.getReg .x13 - 14348907#64 + 4194304#64).truncate 32 :=
        SigGolfCandidate.Radix27Sym.reserved_word0 f hf7 hf14
      _ = l.extractLsb' 0 32 ++ BitVec.ofNat 32 (4194304 + (t.toNat - 14348907)) := by
        rw [hf9, hf13, marker_arithmetic t ht]
        simp
      _ = q.extractLsb' 0 64 := (reserved_pair0 l t.toNat).symm
  have hv1 : v.getMem (BitVec.ofNat 64 0x20F8) = q.extractLsb' 64 64 := by
    calc
      v.getMem (BitVec.ofNat 64 0x20F8) =
          ((0#16) ++ (f.getReg .x11).truncate 16) ++
            (f.getReg .x10).truncate 32 :=
        SigGolfCandidate.Radix27Sym.reserved_word1 f hf7
      _ = ((0#16) ++ lo16 l 4) ++ l.extractLsb' 32 32 := by
        rw [hf11, hf10]
        simp
      _ = q.extractLsb' 64 64 := (reserved_pair1 l t.toNat).symm
  have hv2 : (v.getMem (BitVec.ofNat 64 0x2100)).extractLsb' 0 32 =
      q.extractLsb' 128 32 := by
    calc
      _ = 0 := SigGolfCandidate.Radix27Sym.reserved_word2 f hf7
      _ = q.extractLsb' 128 32 := (reserved_pair2 l t.toNat).symm
  exact Radix27CounterMem.counter_readBuffer_eq v q hv0 hv1 hv2

#print axioms marker_arithmetic
#print axioms reserved_counter_readBuffer
end Radix27ReservedBridge


end


section -- Radix27ExpandTailOutput

namespace Radix27ExpandTailOutput
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Radix27Images
  SigGolfCandidate.Rv SigGolfCandidate.Packed Radix27

theorem done_mem (v : MachineState) (a : Word) :
    (expandDone.res.toState v).getMem a = v.getMem a := by
  simp only [Result.toState_getMem, expandDone.res, rv_simp]

theorem first_mem (s : MachineState) (a : Word) :
    (expandFirst.res.toState s).getMem a = s.getMem a := by
  simp only [Result.toState_getMem, expandFirst.res, rv_simp]

theorem valid_mem_frame (s : MachineState) (a : Word)
    (h7 : s.getReg .x7 = BitVec.ofNat 64 0x20F0)
    (h0 : a ≠ BitVec.ofNat 64 0x20F0)
    (h1 : a ≠ BitVec.ofNat 64 0x20F8)
    (h2 : a ≠ BitVec.ofNat 64 0x2100) :
    (expandValid.res.toState s).getMem a = s.getMem a := by
  simp only [Result.toState_getMem, expandValid.res, memEval, Addr.eval]
  simp only [show E.eval s (.reg .x7) = s.getReg .x7 by rfl, h7,
    show (8432#64) + (16#64) = 8448#64 by decide,
    show (8432#64) + (8#64) = 8440#64 by decide,
    show (8432#64) + (0#64) = 8432#64 by decide,
    h0, h1, h2, if_false]

theorem reserved_mem_frame (s : MachineState) (a : Word)
    (h7 : s.getReg .x7 = BitVec.ofNat 64 0x20F0)
    (h0 : a ≠ BitVec.ofNat 64 0x20F0)
    (h1 : a ≠ BitVec.ofNat 64 0x20F8)
    (h2 : a ≠ BitVec.ofNat 64 0x2100) :
    (expandReserved.res.toState s).getMem a = s.getMem a := by
  simp only [Result.toState_getMem, expandReserved.res, memEval, Addr.eval]
  simp only [show E.eval s (.reg .x7) = s.getReg .x7 by rfl, h7,
    show (8432#64) + (16#64) = 8448#64 by decide,
    show (8432#64) + (8#64) = 8440#64 by decide,
    show (8432#64) + (0#64) = 8432#64 by decide,
    h0, h1, h2, if_false]

theorem done_readBuffer (v : MachineState) :
    readBuffer (expandDone.res.toState v) 0x20F0 20 =
      readBuffer v 0x20F0 20 := by
  apply readBuffer_eq_of_bytes
  intro i hi
  simp only [MachineState.getByte, done_mem]
  exact (readBuffer_byte v 0x20F0 20 i hi).symm

theorem loaded_expand13 (s : MachineState) :
    expand13 (trailer13 (readBuffer s 0x2650 6397)) =
      if (Radix27Loaded.rankLoaded s).toNat < 14348907 then
        validBlock (Radix27Loaded.lowLoaded s)
          (Radix27Loaded.rankLoaded s).toNat
      else reservedBlock (Radix27Loaded.lowLoaded s)
          (Radix27Loaded.rankLoaded s).toNat := by
  rw [← Radix27Loaded.packedLoaded_readBuffer]
  rfl

theorem reserved_tail_readBuffer (s : MachineState)
    (h6 : s.getReg .x6 = BitVec.ofNat 64 0x3F40)
    (h7 : s.getReg .x7 = BitVec.ofNat 64 0x20F0)
    (hr : 14348907 ≤ (Radix27Loaded.rankLoaded s).toNat) :
    let f := expandFirst.res.toState s
    let v := expandReserved.res.toState f
    let u := expandDone.res.toState v
    readBuffer u 0x20F0 20 =
      expand13 (trailer13 (readBuffer s 0x2650 6397)) := by
  dsimp only
  rw [done_readBuffer,
    Radix27ReservedBridge.reserved_counter_readBuffer s h6 h7 hr,
    loaded_expand13]
  simp only [if_neg (by omega : ¬(Radix27Loaded.rankLoaded s).toNat < 14348907)]

theorem valid_tail_readBuffer (s : MachineState)
    (h6 : s.getReg .x6 = BitVec.ofNat 64 0x3F40)
    (h7 : s.getReg .x7 = BitVec.ofNat 64 0x20F0)
    (hr : (Radix27Loaded.rankLoaded s).toNat < 14348907) :
    let f := expandFirst.res.toState s
    let v := expandValid.res.toState f
    let u := expandDone.res.toState v
    readBuffer u 0x20F0 20 =
      expand13 (trailer13 (readBuffer s 0x2650 6397)) := by
  dsimp only
  rw [done_readBuffer,
    Radix27ExpandValidMem.valid_counter_readBuffer s h6 h7,
    loaded_expand13]
  simp only [if_pos hr]

def tailState (s : MachineState) : MachineState :=
  let f := expandFirst.res.toState s
  if 14348907 ≤ (Radix27Loaded.rankLoaded s).toNat then
    expandDone.res.toState (expandReserved.res.toState f)
  else expandDone.res.toState (expandValid.res.toState f)

theorem tail_counter_readBuffer (s : MachineState)
    (h6 : s.getReg .x6 = BitVec.ofNat 64 0x3F40)
    (h7 : s.getReg .x7 = BitVec.ofNat 64 0x20F0) :
    readBuffer (tailState s) 0x20F0 20 =
      expand13 (trailer13 (readBuffer s 0x2650 6397)) := by
  by_cases hr : 14348907 ≤ (Radix27Loaded.rankLoaded s).toNat
  · simpa only [tailState, if_pos hr] using reserved_tail_readBuffer s h6 h7 hr
  · have hr' : (Radix27Loaded.rankLoaded s).toNat < 14348907 := by omega
    simpa only [tailState, if_neg hr] using valid_tail_readBuffer s h6 h7 hr'

theorem tail_mem_frame (s : MachineState)
    (h7 : s.getReg .x7 = BitVec.ofNat 64 0x20F0)
    (a : Word) (ha : a.toNat < 0x20F0) :
    (tailState s).getMem a = s.getMem a := by
  let f := expandFirst.res.toState s
  have hf7 : f.getReg .x7 = BitVec.ofNat 64 0x20F0 := by
    simpa only [f, Result.toState_getReg, expandFirst.res, rv_simp] using h7
  have hne (x : Nat) (hx : 0x20F0 ≤ x) (hxb : x < 2 ^ 64) :
      a ≠ BitVec.ofNat 64 x := by
    intro h
    rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hxb] at ha
    omega
  by_cases hr : 14348907 ≤ (Radix27Loaded.rankLoaded s).toNat
  · simp only [tailState, if_pos hr, done_mem]
    rw [reserved_mem_frame f a hf7 (hne _ (by omega) (by decide))
      (hne _ (by omega) (by decide)) (hne _ (by omega) (by decide)), first_mem]
  · simp only [tailState, if_neg hr, done_mem]
    rw [valid_mem_frame f a hf7 (hne _ (by omega) (by decide))
      (hne _ (by omega) (by decide)) (hne _ (by omega) (by decide)), first_mem]

theorem tail_body_byte (s : MachineState)
    (h7 : s.getReg .x7 = BitVec.ofNat 64 0x20F0)
    (j : Nat) (hj : j < 6384) :
    (tailState s).getByte (BitVec.ofNat 64 (0x800 + j)) =
      s.getByte (BitVec.ofNat 64 (0x800 + j)) := by
  have ha : (alignToDword (BitVec.ofNat 64 (0x800 + j))).toNat < 0x20F0 := by
    rw [alignToDword_toNat, BitVec.toNat_ofNat]
    omega
  simp only [MachineState.getByte]
  rw [tail_mem_frame s h7 _ ha]

#print axioms tail_counter_readBuffer
#print axioms tail_body_byte

#print axioms reserved_tail_readBuffer
#print axioms valid_tail_readBuffer
end Radix27ExpandTailOutput


end


section -- Radix27ExpandTailSteps

namespace Radix27ExpandTailSteps
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv
  SigGolfCandidate.Radix27Images SigGolfCandidate.Rv

theorem tail_steps (s : MachineState)
    (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4*15))
    (h6 : s.getReg .x6 = BitVec.ofNat 64 0x3F40)
    (h7 : s.getReg .x7 = BitVec.ofNat 64 0x20F0) :
    ∃ k c, Steps expandImage s k c (Radix27ExpandTailOutput.tailState s) ∧
      ((k = 46 ∧ c = 73) ∨ (k = 23 ∧ c = 23)) ∧
      fetch expandImage (Radix27ExpandTailOutput.tailState s) =
        some (.base .ECALL) ∧
      (Radix27ExpandTailOutput.tailState s).getReg .x5 = 1 ∧
      (Radix27ExpandTailOutput.tailState s).getReg .x10 = 0 := by
  let f := expandFirst.res.toState s
  have hs1 : Steps expandImage s 11 11 f := expandFirst_steps s hpc h6
  have hf7 : f.getReg .x7 = BitVec.ofNat 64 0x20F0 := by
    simpa only [f, Result.toState_getReg, expandFirst.res, rv_simp] using h7
  by_cases hr : 14348907 ≤ (Radix27Loaded.rankLoaded s).toNat
  · have hfp : f.pc = BitVec.ofNat 64 (0x1000 + 4*59) := by
      have hp := expandFirst_pc s
      rw [Radix27Loaded.first_rank_toNat s h6, if_pos hr] at hp
      exact hp
    have ho : expandReserved.res.obligs f := by
      simp only [expandReserved.res, rv_simp]
      rw [hf7]
      decide
    let v := expandReserved.res.toState f
    have hs2 : Steps expandImage f 10 10 v :=
      symRun_sound expandReserved codeAt_expandReserved f hfp ho
    have hvp : v.pc = BitVec.ofNat 64 (0x1000 + 4*69) := by
      simp only [v, Result.toState_pc, expandReserved.res, rv_simp]
    have ho3 : expandDone.res.obligs v := by simp only [expandDone.res, rv_simp]
    have hs3 : Steps expandImage v 2 2 (expandDone.res.toState v) :=
      symRun_sound expandDone codeAt_expandDone v hvp ho3
    refine ⟨23, 23, ?_, Or.inr ⟨rfl, rfl⟩, ?_, ?_, ?_⟩
    · simpa only [Radix27ExpandTailOutput.tailState, if_pos hr,
        show 11 + (10 + 2) = 23 by decide] using hs1.trans (hs2.trans hs3)
    · simpa only [Radix27ExpandTailOutput.tailState, if_pos hr] using
        symRun_ecall expandDone codeAt_expandDone v ho3 rfl
    · simp only [Radix27ExpandTailOutput.tailState, if_pos hr,
        Result.toState_getReg, expandDone.res, rv_simp]
    · simp only [Radix27ExpandTailOutput.tailState, if_pos hr,
        Result.toState_getReg, expandDone.res, rv_simp]
  · have hfp : f.pc = BitVec.ofNat 64 (0x1000 + 4*26) := by
      have hp := expandFirst_pc s
      rw [Radix27Loaded.first_rank_toNat s h6, if_neg hr] at hp
      exact hp
    have ho : expandValid.res.obligs f := expandValid_obligs f hf7
    let v := expandValid.res.toState f
    have hs2 : Steps expandImage f 33 60 v :=
      symRun_sound expandValid codeAt_expandValid f hfp ho
    have hvp : v.pc = BitVec.ofNat 64 (0x1000 + 4*69) := by
      simp only [v, Result.toState_pc, expandValid.res, rv_simp]
    have ho3 : expandDone.res.obligs v := by simp only [expandDone.res, rv_simp]
    have hs3 : Steps expandImage v 2 2 (expandDone.res.toState v) :=
      symRun_sound expandDone codeAt_expandDone v hvp ho3
    refine ⟨46, 73, ?_, Or.inl ⟨rfl, rfl⟩, ?_, ?_, ?_⟩
    · simpa only [Radix27ExpandTailOutput.tailState, if_neg hr,
        show 11 + (33 + 2) = 46 by decide,
        show 11 + (60 + 2) = 73 by decide] using hs1.trans (hs2.trans hs3)
    · simpa only [Radix27ExpandTailOutput.tailState, if_neg hr] using
        symRun_ecall expandDone codeAt_expandDone v ho3 rfl
    · simp only [Radix27ExpandTailOutput.tailState, if_neg hr,
        Result.toState_getReg, expandDone.res, rv_simp]
    · simp only [Radix27ExpandTailOutput.tailState, if_neg hr,
        Result.toState_getReg, expandDone.res, rv_simp]

#print axioms tail_steps
end Radix27ExpandTailSteps


end


section -- Radix27ExpandBodyStage

namespace Radix27ExpandBodyStage
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv
  SigGolfCandidate.Radix27Images SigGolfCandidate.Rv SigGolfCandidate.Mem

def L : SigGolfCandidate.Rv.Layout :=
  [(0, SigGolfCandidate.Packed.Images.expandBodyPrelude),
   (5, SigGolfCandidate.Expand.loopCode),
   (11, SigGolfCandidate.Packed.Images.expandCounterPrelude),
   (15, expandTail)]

theorem layout_ok : layoutOk 0 L = true := by decide +kernel
theorem code_eq : expandImage.code = layoutCode L := by decide +kernel

theorem codeAt_pre : CodeAt expandImage (BitVec.ofNat 64 (0x1000 + 4*0))
    SigGolfCandidate.Packed.Images.expandBodyPrelude :=
  codeAt_layout code_eq layout_ok (i := 0) (by kernel_rfl) (by decide)

theorem codeAt_loop : CodeAt expandImage (BitVec.ofNat 64 (0x1000 + 4*5))
    SigGolfCandidate.Expand.loopCode :=
  codeAt_layout code_eq layout_ok (i := 1) (by kernel_rfl) (by decide)

theorem codeAt_counter : CodeAt expandImage (BitVec.ofNat 64 (0x1000 + 4*11))
    SigGolfCandidate.Packed.Images.expandCounterPrelude :=
  codeAt_layout code_eq layout_ok (i := 2) (by kernel_rfl) (by decide)

sym_block runPre := symRun {} SigGolfCandidate.Packed.Images.expandBodyPrelude
  (BitVec.ofNat 64 0x1000) 10
sym_block runCounter := symRun {} SigGolfCandidate.Packed.Images.expandCounterPrelude
  (BitVec.ofNat 64 (0x1000 + 4*11)) 10

theorem body_stage (t : MachineState) (htpc : t.pc = 0x1000)
    (f : Nat → Byte) (hf : SigGolfCandidate.Expand.BytesEq t f) :
    ∃ u, Steps expandImage t (runPre.res.steps + 1596 * 6)
        (runPre.res.cycles + 1596 * 6) u ∧
      u.pc = BitVec.ofNat 64 (0x1000 + 4*11) ∧
      SigGolfCandidate.Expand.BytesEq u
        (SigGolfCandidate.Expand.applyCopy (0x2650, 0x800, 1596) f) := by
  obtain ⟨u, hsteps, hpc, hmem⟩ :=
    SigGolfCandidate.Expand.stage runPre codeAt_pre rfl rfl rfl rfl rfl rfl
      codeAt_loop (by decide) t htpc f hf
  exact ⟨u, hsteps, by simpa using hpc, hmem⟩

theorem counter_stage (u : MachineState)
    (hpc : u.pc = BitVec.ofNat 64 (0x1000 + 4*11)) :
    Steps expandImage u 4 4 (runCounter.res.toState u) ∧
      (runCounter.res.toState u).pc = BitVec.ofNat 64 (0x1000 + 4*15) ∧
      (runCounter.res.toState u).getReg .x6 = BitVec.ofNat 64 0x3F40 ∧
      (runCounter.res.toState u).getReg .x7 = BitVec.ofNat 64 0x20F0 ∧
      (∀ a : Word, (runCounter.res.toState u).getMem a = u.getMem a) := by
  have ho : runCounter.res.obligs u := by simp only [runCounter.res, rv_simp]
  refine ⟨symRun_sound runCounter codeAt_counter u hpc ho, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, runCounter.res, rv_simp]
  · simp only [Result.toState_getReg, runCounter.res, rv_simp]
  · simp only [Result.toState_getReg, runCounter.res, rv_simp]
  · intro a
    simp only [Result.toState_getMem, runCounter.res, rv_simp]

#print axioms body_stage
#print axioms counter_stage
end Radix27ExpandBodyStage


end


section -- Radix27ExpandFull

namespace Radix27ExpandFull
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv
  SigGolfCandidate.Radix27Images SigGolfCandidate.Rv SigGolfCandidate.Mem
  SigGolfCandidate.Packed Radix27
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem body_sig_unchanged (s u : MachineState)
    (hb : SigGolfCandidate.Expand.BytesEq u
      (SigGolfCandidate.Expand.applyCopy (0x2650, 0x800, 1596)
        (fun a => s.getByte (BitVec.ofNat 64 a)))) :
    readBuffer u 0x2650 6397 = readBuffer s 0x2650 6397 := by
  apply readBuffer_eq_of_bytes
  intro i hi
  rw [hb _ (by omega)]
  have hne : ¬ (0x800 ≤ 0x2650 + i ∧ 0x2650 + i < 0x800 + 4 * 1596) := by omega
  simp only [SigGolfCandidate.Expand.applyCopy, if_neg hne]
  exact (readBuffer_byte s 0x2650 6397 i hi).symm

theorem final_readBuffer (s u : MachineState)
    (hb : SigGolfCandidate.Expand.BytesEq u
      (SigGolfCandidate.Expand.applyCopy (0x2650, 0x800, 1596)
        (fun a => s.getByte (BitVec.ofNat 64 a))))
    (h6 : u.getReg .x6 = BitVec.ofNat 64 0x3F40)
    (h7 : u.getReg .x7 = BitVec.ofNat 64 0x20F0) :
    readBuffer (Radix27ExpandTailOutput.tailState u) 0x800 6404 =
      expandWitness13 (readBuffer s 0x2650 6397) := by
  let sig : Bytes 6397 := readBuffer s 0x2650 6397
  have hc : readBuffer (Radix27ExpandTailOutput.tailState u) 0x20F0 20 =
      expand13 (trailer13 sig) := by
    rw [Radix27ExpandTailOutput.tail_counter_readBuffer u h6 h7,
      body_sig_unchanged s u hb]
  change readBuffer (Radix27ExpandTailOutput.tailState u) 0x800 6404 =
    expandWitness13 sig
  apply readBuffer_eq_of_bytes
  intro i hi
  by_cases hbody : i < 6384
  · rw [Radix27ExpandTailOutput.tail_body_byte u h7 i hbody,
      hb _ (by omega)]
    have hhit : 0x800 ≤ 0x800 + i ∧ 0x800 + i < 0x800 + 4 * 1596 := by omega
    simp only [SigGolfCandidate.Expand.applyCopy, if_pos hhit]
    have heq : 0x800 + i - 0x800 + 0x2650 = 0x2650 + i := by omega
    rw [heq, ← readBuffer_byte s 0x2650 6397 i (by omega)]
    rw [Radix27ByteCodec.expandWitness13_body_byte sig i hbody,
      Radix27ByteCodec.body13_byte sig i hbody]
  · have hj : i - 6384 < 20 := by omega
    have heq : 0x800 + i = 0x20F0 + (i - 6384) := by omega
    rw [heq, ← readBuffer_byte (Radix27ExpandTailOutput.tailState u)
      0x20F0 20 (i - 6384) hj, hc]
    have hi' : 6384 + (i - 6384) = i := by omega
    rw [← hi', Radix27ByteCodec.expandWitness13_counter_byte sig (i - 6384) hj]
    have hidx : 6384 + (i - 6384) - 6384 = i - 6384 := by omega
    rw [hidx]

#print axioms final_readBuffer

theorem expand_steps (s : MachineState) (hpc : s.pc = 0x1000) :
    ∃ u k c, Steps expandImage s k c u ∧
      ((k = 9631 ∧ c = 9658) ∨ (k = 9608 ∧ c = 9608)) ∧
      fetch expandImage u = some (.base .ECALL) ∧
      u.getReg .x5 = 1 ∧ u.getReg .x10 = 0 ∧
      readBuffer u 0x800 6404 =
        expandWitness13 (readBuffer s 0x2650 6397) := by
  obtain ⟨u0, st0, pc0, hb0⟩ :=
    Radix27ExpandBodyStage.body_stage s hpc _ (fun a _ => rfl)
  obtain ⟨st1, pc1, h6, h7, hm⟩ := Radix27ExpandBodyStage.counter_stage u0 pc0
  let u1 := Radix27ExpandBodyStage.runCounter.res.toState u0
  have hb1 : SigGolfCandidate.Expand.BytesEq u1
      (SigGolfCandidate.Expand.applyCopy (0x2650, 0x800, 1596)
        (fun a => s.getByte (BitVec.ofNat 64 a))) := by
    intro a ha
    simp only [MachineState.getByte, hm]
    exact hb0 a ha
  obtain ⟨k2, c2, st2, hcost, hf, h5, h10⟩ :=
    Radix27ExpandTailSteps.tail_steps u1 pc1 h6 h7
  let z := Radix27ExpandTailOutput.tailState u1
  have hout : readBuffer z 0x800 6404 =
      expandWitness13 (readBuffer s 0x2650 6397) :=
    final_readBuffer s u1 hb1 h6 h7
  refine ⟨z, Radix27ExpandBodyStage.runPre.res.steps + 1596 * 6 + 4 + k2,
    Radix27ExpandBodyStage.runPre.res.cycles + 1596 * 6 + 4 + c2,
    ?_, ?_, hf, h5, h10, hout⟩
  · simpa only [Nat.add_assoc] using st0.trans (st1.trans st2)
  · rcases hcost with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨by decide, by decide⟩
    · exact Or.inr ⟨by decide, by decide⟩

#print axioms expand_steps
end Radix27ExpandFull


end


section -- Radix27Submission

namespace Radix27Submission
open SigGolfCandidate.Legacy

def concrete : Submission where
  sizes := SigGolfCandidate.Radix27Images.sizes13
  layout := SigGolfCandidate.submission.layout
  image
    | .keygen => SigGolfCandidate.submission.image .keygen
    | .sign => SigGolfCandidate.Radix27Images.signImage
    | .expand => SigGolfCandidate.Radix27Images.expandImage
    | .verify => SigGolfCandidate.submission.image .verify

end Radix27Submission


end


section -- Radix27ExpandWrapper

namespace Radix27ExpandWrapper
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv
  SigGolfCandidate.Rv SigGolfCandidate.Mem SigGolfCandidate.Packed OracleComp
set_option maxRecDepth 100000

abbrev concrete := Radix27Submission.concrete

def initState (m : Message) (pk : PublicKey) (σ : Bytes 6397) : MachineState :=
  let blank : MachineState := { regs := fun _ => 0, mem := fun _ => 0, pc := 0x1000 }
  ((((blank.writeBytesAsWords (BitVec.ofNat 64
      (dataBase SigGolfCandidate.Radix27Images.expandImage))
      SigGolfCandidate.Radix27Images.expandImage.data).writeBytesAsWords
      (BitVec.ofNat 64 0x40) (bytes m)).writeBytesAsWords
      (BitVec.ofNat 64 0xA0) (bytes pk)).writeBytesAsWords
      (BitVec.ofNat 64 0x2650) (bytes σ)).setReg .x2
      (BitVec.ofNat 64 (dataBase SigGolfCandidate.Radix27Images.expandImage))

theorem initialState_eq (m : Message) (pk : PublicKey) (σ : Bytes 6397) :
    initialState concrete .expand (m, pk, σ) = some (initState m pk σ) := by
  unfold initialState
  rw [if_pos (by exact SigGolfCandidate.Radix27Images.expand_valid)]
  rfl

theorem initState_sig (m : Message) (pk : PublicKey) (σ : Bytes 6397)
    (j : Nat) (hj : j < 6397) :
    (initState m pk σ).getByte (BitVec.ofNat 64 (0x2650 + j)) =
      (bytes σ).getD j 0 := by
  unfold initState
  simp only [getByte_setReg]
  rw [getByte_writeBytesAsWords _ _ _ _ (by decide)
    (by simp [SigGolfCandidate.Legacy.bytes]) (by omega),
    if_pos (by simp [SigGolfCandidate.Legacy.bytes]; omega)]
  congr 1
  omega

theorem initState_readSig (m : Message) (pk : PublicKey) (σ : Bytes 6397) :
    readBuffer (initState m pk σ) 0x2650 6397 = σ := by
  apply readBuffer_eq_of_bytes
  intro i hi
  exact initState_sig m pk σ i hi

theorem expand_run (m : Message) (pk : PublicKey) (σ : Bytes 6397) :
    ∃ cyc, cyc < CYCLE_LIMIT ∧
      concrete.run .expand (m, pk, σ) =
        pure ⟨some (Radix27.expandWitness13 σ), true, cyc, 0, 0⟩ := by
  obtain ⟨u, k, c, hst, hcost, hf, h5, h10, hb⟩ :=
    Radix27ExpandFull.expand_steps (initState m pk σ)
      (initialState_pc _ _ _ _ (initialState_eq m pk σ))
  have hk : k + 1 < CYCLE_LIMIT := by rcases hcost with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide
  refine ⟨c + 1, ?_, ?_⟩
  · rcases hcost with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide
  rw [run_eq concrete .expand _ _ (initialState_eq m pk σ)]
  change toRunResult concrete .expand <$>
    execute CYCLE_LIMIT SigGolfCandidate.Radix27Images.expandImage (initState m pk σ) = _
  rw [hst.execute_le (by omega : k ≤ CYCLE_LIMIT),
    show CYCLE_LIMIT - k = (CYCLE_LIMIT - (k + 1)) + 1 by omega,
    execute_halt _ hf h5, map_pure]
  have hr : readOutput concrete.sizes concrete.layout .expand u =
      Radix27.expandWitness13 σ := by
    rw [initState_readSig m pk σ] at hb
    exact hb
  rw [h10, if_pos rfl, map_pure]
  unfold toRunResult
  simp only [Execution.charge_exit, Execution.charge_state, if_pos, hr]
  rfl

theorem expand_runWith (hash : Hash) (m : Message) (pk : PublicKey)
    (σ : Bytes 6397) :
    ∃ cyc, cyc < CYCLE_LIMIT ∧
      concrete.runWith hash .expand (m, pk, σ) =
        ⟨some (Radix27.expandWitness13 σ), true, cyc, 0, 0⟩ := by
  obtain ⟨cyc, hcyc, hrun⟩ := expand_run m pk σ
  refine ⟨cyc, hcyc, ?_⟩
  unfold Submission.runWith
  rw [hrun]
  rfl

#print axioms expand_run
#print axioms expand_runWith
end Radix27ExpandWrapper


end


section -- SignClone13.Sim

/-! ### cloned Sim -/

/-!
# Refinement of oracle computations by machine runs (`Sim`)

`Sim image s W oa Q` : running the organizer machine from `s` performs *exactly* the oracle
queries of the spec `oa` (query for query), and after them reaches a state `t` with `Q a t`,
where `a` is the value returned by `oa`; the machine part costs at most `W` cycles (and at most
`W` steps / fuel). Formally there is a computation `oc` over the outcomes
(`Out`: value, #calls, #blocks, steps, cycles, final state) such that

* projecting `oc` to `(value, calls, blocks)` gives `countBoth oa` (joint counter), and
* for every `fuel ≥ W`, `execute fuel image s` is `oc` followed by the rest of the execution
  from the outcome's state, charged with the outcome's costs.

Combinators: `Sim.pure`, `Sim.steps` (prefix a block of ordinary steps), `Sim.query` / `Sim.hash`
(one HASH `ECALL`), `Sim.bind`, `Sim.mono`, `Sim.foldlM_range` (loops), and
`Sim.run_eq` / `Sim.runWith` (a whole phase: refinement and termination).
-/

namespace SigGolfCandidate.Radix27Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec SigGolfCandidate.Rv
  SigGolfCandidate.Ref

/-! ## Joint call / compression counter -/

/-- Forward a query, counting one call and its blocks. -/
def countImpl2 : QueryImpl HashSpec (StateT (Nat × Nat) (OracleComp HashSpec)) :=
  fun q => do
    modify (fun p => (p.1 + 1, p.2 + Query.blocks q))
    liftM (HashSpec.query q)

/-- The result, the number of oracle calls and the number of compressions. -/
def countBoth {α : Type} (oa : OracleComp HashSpec α) : OracleComp HashSpec (α × Nat × Nat) :=
  (simulateQ countImpl2 oa).run (0, 0)

section count
variable {α β : Type}

theorem countImpl2_run (oa : OracleComp HashSpec α) (c b : Nat) :
    (simulateQ countImpl2 oa).run (c, b) =
      (fun p => (p.1, c + p.2.1, b + p.2.2)) <$> countBoth oa := by
  unfold countBoth
  induction oa using OracleComp.inductionOn generalizing c b with
  | pure a => simp
  | query_bind q oa ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, countImpl2]
    simp only [StateT.run_modify, pure_bind, map_bind]
    have hl : ∀ s, (liftM (OracleSpec.query q) : StateT (Nat × Nat) (OracleComp HashSpec) _).run s =
        (fun a => (a, s)) <$> (liftM (OracleSpec.query q) : OracleComp HashSpec _) := fun s => rfl
    simp only [hl, bind_map_left]
    congr 1; funext a
    rw [ih a (c + 1) (b + Query.blocks q), ih a (0 + 1) (0 + Query.blocks q), Functor.map_map]
    congr 1; funext p
    simp only [Prod.mk.injEq, true_and]; omega

@[simp] theorem countBoth_pure (a : α) :
    countBoth (pure a : OracleComp HashSpec α) = pure (a, 0, 0) := rfl

theorem countBoth_bind (oa : OracleComp HashSpec α) (f : α → OracleComp HashSpec β) :
    countBoth (oa >>= f) =
      countBoth oa >>= fun p => (fun r => (r.1, p.2.1 + r.2.1, p.2.2 + r.2.2)) <$> countBoth (f p.1) := by
  conv_lhs => unfold countBoth
  rw [simulateQ_bind, StateT.run_bind]
  exact congrArg _ (funext fun p => countImpl2_run (f p.1) p.2.1 p.2.2)

@[simp] theorem countBoth_query (q : Query) :
    countBoth (liftM (HashSpec.query q) : OracleComp HashSpec _) =
      (fun a => (a, 1, q.blocks)) <$> (liftM (HashSpec.query q) : OracleComp HashSpec _) := by
  unfold countBoth
  rw [simulateQ_spec_query]
  simp only [countImpl2, StateT.run_bind, StateT.run_modify, pure_bind, Nat.zero_add]
  rfl

@[simp] theorem countBoth_H (x : List Byte) :
    countBoth (H x) = (fun a => (a, 1, (fmt x).blocks)) <$> H x :=
  countBoth_query (fmt x)

/-- The joint counter projects to `countCalls`. -/
theorem countBoth_calls (oa : OracleComp HashSpec α) :
    (fun p => (p.1, p.2.1)) <$> countBoth oa = countCalls oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind q oa ih =>
    rw [countBoth_bind, countCalls_bind, countBoth_query, countCalls_query]
    simp only [map_bind, bind_map_left, Functor.map_map]
    congr 1; funext a
    rw [← ih a, Functor.map_map]

/-- The joint counter projects to `countBlocks`. -/
theorem countBoth_blocks (oa : OracleComp HashSpec α) :
    (fun p => (p.1, p.2.2)) <$> countBoth oa = countBlocks oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind q oa ih =>
    rw [countBoth_bind, countBlocks, countWith_bind, countBoth_query, countWith_query]
    simp only [map_bind, bind_map_left, Functor.map_map]
    congr 1; funext a
    rw [show countWith Query.blocks (oa a) = countBlocks (oa a) from rfl, ← ih a, Functor.map_map]

@[simp] theorem fst_countBoth (oa : OracleComp HashSpec α) : Prod.fst <$> countBoth oa = oa := by
  have := congrArg (fun x => Prod.fst <$> x) (countBoth_calls oa)
  simp only [Functor.map_map] at this
  rw [this, fst_countCalls]

end count

/-! ## `Sim` -/

/-- An outcome of a machine segment: spec value, calls, blocks, steps (fuel), cycles, state. -/
structure Out (α : Type) where
  val : α
  calls : Nat
  blocks : Nat
  steps : Nat
  cycles : Nat
  st : MachineState

/-- Admissible outcomes: steps ≤ cycles ≤ W and the postcondition. -/
def Out.Good {α : Type} (W : Nat) (Q : α → MachineState → Prop) (o : Out α) : Prop :=
  o.steps ≤ o.cycles ∧ o.cycles ≤ W ∧ Q o.val o.st

/-- `Sim image s W oa Q`: see the module docstring. -/
def Sim {α : Type} (image : Image) (s : MachineState) (W : Nat) (oa : OracleComp HashSpec α)
    (Q : α → MachineState → Prop) : Prop :=
  ∃ oc : OracleComp HashSpec {o : Out α // o.Good W Q},
    (fun o => (o.1.val, o.1.calls, o.1.blocks)) <$> oc = countBoth oa ∧
    ∀ fuel, W ≤ fuel → Riscv.execute fuel image s =
      oc >>= fun o => (fun r => r.charge o.1.cycles o.1.calls o.1.blocks) <$>
        Riscv.execute (fuel - o.1.steps) image o.1.st

theorem steps_le_cycles {image : Image} {s t : MachineState} {k c : Nat}
    (h : Steps image s k c t) : k ≤ c := by
  induction h with
  | refl => exact le_refl _
  | @step s t u i k c _ _ _ ih =>
    have : 1 ≤ instructionCycles i := by
      unfold instructionCycles; split <;> omega
    omega

section sim
variable {α β : Type} {image : Image}

/-- A block of ordinary steps returning a pure value. -/
theorem Sim.pure_steps {s t : MachineState} {k c : Nat} {a : α} {Q : α → MachineState → Prop}
    (h : Steps image s k c t) (hQ : Q a t) : Sim image s c (pure a) Q := by
  refine ⟨pure ⟨⟨a, 0, 0, k, c, t⟩, steps_le_cycles h, le_refl _, hQ⟩, rfl, ?_⟩
  intro fuel hf
  rw [pure_bind, h.execute_le (le_trans (steps_le_cycles h) hf)]

theorem Sim.pure {s : MachineState} {a : α} {Q : α → MachineState → Prop} (hQ : Q a s) :
    Sim image s 0 (pure a) Q :=
  Sim.pure_steps (Steps.refl s) hQ

theorem Sim.mono {s : MachineState} {W W' : Nat} {oa : OracleComp HashSpec α}
    {Q Q' : α → MachineState → Prop} (h : Sim image s W oa Q) (hW : W ≤ W')
    (hQ : ∀ a t, Q a t → Q' a t) : Sim image s W' oa Q' := by
  obtain ⟨oc, hp, hf⟩ := h
  refine ⟨(fun o => ⟨o.1, o.2.1, le_trans o.2.2.1 hW, hQ _ _ o.2.2.2⟩) <$> oc, ?_, ?_⟩
  · rw [Functor.map_map]; exact hp
  · intro fuel hfuel
    rw [hf fuel (le_trans hW hfuel), bind_map_left]

theorem Sim.of_eq {s : MachineState} {W : Nat} {oa ob : OracleComp HashSpec α}
    {Q : α → MachineState → Prop} (h : Sim image s W oa Q) (he : oa = ob) : Sim image s W ob Q :=
  he ▸ h

theorem Sim.bind {s : MachineState} {W₁ W₂ : Nat} {oa : OracleComp HashSpec α}
    {f : α → OracleComp HashSpec β} {Q₁ : α → MachineState → Prop}
    {Q₂ : β → MachineState → Prop} (h₁ : Sim image s W₁ oa Q₁)
    (h₂ : ∀ a t, Q₁ a t → Sim image t W₂ (f a) Q₂) : Sim image s (W₁ + W₂) (oa >>= f) Q₂ := by
  classical
  obtain ⟨oc₁, hp₁, hf₁⟩ := h₁
  have h₂' : ∀ o : {o : Out α // o.Good W₁ Q₁}, Sim image o.1.st W₂ (f o.1.val) Q₂ :=
    fun o => h₂ _ _ o.2.2.2
  let oc₂ := fun o => Classical.choose (h₂' o)
  have hp₂ := fun o => (Classical.choose_spec (h₂' o)).1
  have hf₂ := fun o => (Classical.choose_spec (h₂' o)).2
  let comb : (o₁ : {o : Out α // o.Good W₁ Q₁}) → {o : Out β // o.Good W₂ Q₂} →
      {o : Out β // o.Good (W₁ + W₂) Q₂} := fun o₁ o₂ =>
    ⟨⟨o₂.1.val, o₁.1.calls + o₂.1.calls, o₁.1.blocks + o₂.1.blocks, o₁.1.steps + o₂.1.steps,
      o₁.1.cycles + o₂.1.cycles, o₂.1.st⟩,
      by have := o₁.2; have := o₂.2; simp only [Out.Good] at *; omega,
      by have := o₁.2; have := o₂.2; simp only [Out.Good] at *; omega, o₂.2.2.2⟩
  refine ⟨oc₁ >>= fun o₁ => comb o₁ <$> oc₂ o₁, ?_, ?_⟩
  · rw [countBoth_bind, ← hp₁, map_bind, bind_map_left]
    congr 1; funext o₁
    rw [← hp₂ o₁, Functor.map_map, Functor.map_map]
  · intro fuel hfuel
    rw [hf₁ fuel (le_trans (Nat.le_add_right _ _) hfuel), bind_assoc]
    congr 1; funext o₁
    have hs : o₁.1.steps ≤ W₁ := le_trans o₁.2.1 o₁.2.2.1
    rw [hf₂ o₁ (fuel - o₁.1.steps) (by omega), map_bind, bind_map_left]
    congr 1; funext o₂
    simp only [Functor.map_map, Execution.charge_charge, comb]
    rw [Nat.sub_sub]

/-- Prefix a block of ordinary steps. -/
theorem Sim.steps {s t : MachineState} {k c W : Nat} {oa : OracleComp HashSpec α}
    {Q : α → MachineState → Prop} (h : Steps image s k c t) (h₂ : Sim image t W oa Q) :
    Sim image s (c + W) oa Q := by
  have := Sim.bind (Sim.pure_steps (Q := fun _ t' => t' = t) (a := ()) h rfl)
    (f := fun _ => oa) (fun _ t' ht => ht ▸ h₂)
  simpa using this

/-- One HASH `ECALL`. -/
theorem Sim.query {s : MachineState} {q : Query}
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hq : hashInput s = q) :
    Sim image s (8 * q.blocks) (liftM (HashSpec.query q) : OracleComp HashSpec _)
      (fun a t => t = writeHash s a) := by
  subst hq
  have hb : 1 ≤ (hashInput s).blocks := by unfold Query.blocks; omega
  refine ⟨(fun a => ⟨⟨a, 1, (hashInput s).blocks, 1, 8 * (hashInput s).blocks, writeHash s a⟩,
      by show 1 ≤ 8 * _; omega, le_refl _, rfl⟩) <$> (liftM (HashSpec.query (hashInput s)) : OracleComp HashSpec _),
      ?_, ?_⟩
  · rw [Functor.map_map, countBoth_query]
  · intro fuel hfuel
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    rw [execute_hash f hf ht0 hv, bind_map_left]
    rfl

/-- One HASH `ECALL` followed by a continuation. -/
theorem Sim.query_bind {s : MachineState} {q : Query} {W : Nat}
    {f : BitVec 256 → OracleComp HashSpec β} {Q : β → MachineState → Prop}
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hq : hashInput s = q)
    (h : ∀ a, Sim image (writeHash s a) W (f a) Q) :
    Sim image s (8 * q.blocks + W) ((liftM (HashSpec.query q) : OracleComp HashSpec _) >>= f) Q :=
  Sim.bind (Sim.query hf ht0 hv hq) (fun a _ ht => ht ▸ h a)

/-- `hash16 x` (one HASH `ECALL` on `fmt x`) followed by a continuation. -/
theorem Sim.hash16_bindF {s : MachineState} {x : List Byte} {W : Nat}
    {f : Val → OracleComp HashSpec β} {Q : β → MachineState → Prop}
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hq : hashInput s = fmt x)
    (h : ∀ a, Sim image (writeHash s a) W (f (answerBytes 16 a)) Q) :
    Sim image s (8 * (fmt x).blocks + W) (hash16 x >>= f) Q := by
  have : hash16 x >>= f = (liftM (HashSpec.query (fmt x)) : OracleComp HashSpec _) >>=
      fun a => f (answerBytes 16 a) := by
    simp only [hash16, H, bind_assoc, pure_bind]
  rw [this]
  exact Sim.query_bind hf ht0 hv hq h

/-- `hash16 x` for a zero-padded input (`fmt x = pad64 x`) followed by a continuation. -/
theorem Sim.hash16_bind {s : MachineState} {x : List Byte} {W : Nat}
    {f : Val → OracleComp HashSpec β} {Q : β → MachineState → Prop}
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hq : hashInput s = pad64 x) (hx : fmt x = pad64 x)
    (h : ∀ a, Sim image (writeHash s a) W (f (answerBytes 16 a)) Q) :
    Sim image s (8 * (pad64 x).blocks + W) (hash16 x >>= f) Q := by
  have := Sim.hash16_bindF hf ht0 hv (hq.trans hx.symm) h
  rwa [hx] at this

/-- `hash16 x` at the end. -/
theorem Sim.hash16 {s : MachineState} {x : List Byte} {W : Nat} {Q : Val → MachineState → Prop}
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hq : hashInput s = pad64 x) (hx : fmt x = pad64 x)
    (h : ∀ a, Sim image (writeHash s a) W (Pure.pure (answerBytes 16 a)) Q) :
    Sim image s (8 * (pad64 x).blocks + W) (Ref.hash16 x) Q := by
  have := Sim.hash16_bind (f := Pure.pure) hf ht0 hv hq hx h
  rwa [bind_pure] at this

/-- Loop over `List.range n` with an invariant indexed by the number of processed elements. -/
theorem Sim.foldlM_range {γ : Type} (n : Nat) (f : γ → Nat → OracleComp HashSpec γ) (init : γ)
    (Inv : Nat → γ → MachineState → Prop) (W : Nat)
    (hbody : ∀ j < n, ∀ acc t, Inv j acc t → Sim image t W (f acc j) (Inv (j + 1)))
    {s : MachineState} (h0 : Inv 0 init s) :
    Sim image s (n * W) ((List.range n).foldlM f init) (Inv n) := by
  induction n with
  | zero => simpa using Sim.pure (image := image) h0
  | succ n ih =>
    rw [List.range_succ, List.foldlM_append]
    have := Sim.bind (ih (fun j hj => hbody j (by omega))) (f := fun acc => [n].foldlM f acc)
      (W₂ := W) (Q₂ := Inv (n + 1)) (fun acc t ht => by
        simpa using hbody n (by omega) acc t ht)
    refine this.mono ?_ (fun _ _ h => h)
    rw [Nat.succ_mul]

/-- Loop over `List.range' a n` (`a, …, a+n-1`); the invariant is indexed by the number `j` of
processed elements. -/
theorem Sim.foldlM_range' {γ : Type} (a n : Nat) (f : γ → Nat → OracleComp HashSpec γ) (init : γ)
    (Inv : Nat → γ → MachineState → Prop) (W : Nat)
    (hbody : ∀ j < n, ∀ acc t, Inv j acc t → Sim image t W (f acc (a + j)) (Inv (j + 1)))
    {s : MachineState} (h0 : Inv 0 init s) :
    Sim image s (n * W) ((List.range' a n).foldlM f init) (Inv n) := by
  induction n with
  | zero => simpa using Sim.pure (image := image) h0
  | succ n ih =>
    rw [List.range'_concat, Nat.one_mul, List.foldlM_append]
    have := Sim.bind (ih (fun j hj => hbody j (by omega))) (f := fun acc => [a + n].foldlM f acc)
      (W₂ := W) (Q₂ := Inv (n + 1)) (fun acc t ht => by
        simpa using hbody n (by omega) acc t ht)
    refine this.mono ?_ (fun _ _ h => h)
    rw [Nat.succ_mul]

end sim

/-! ## Whole phases -/

section run
variable {α : Type}

/-- **Refinement of a whole phase.** If the machine refines `oa` from the initial state and every
final state is at a HALT `ECALL` whose output (`a0 = 0`: success with `readOutput`) is `F a`, then
`submission.run` has the value / call / compression distribution of `F <$> countBoth oa`. -/
theorem Sim.run_eq (submission : Submission) (phase : Phase) (input : Input submission.sizes phase)
    {s : MachineState} (hinit : initialState submission phase input = some s) {W : Nat}
    {oa : OracleComp HashSpec α} {Q : α → MachineState → Prop}
    (hsim : Sim (submission.image phase) s W oa Q) (hW : W < CYCLE_LIMIT)
    (F : α → Option (Output submission.sizes phase))
    (hQ : ∀ a t, Q a t → fetch (submission.image phase) t = some (.base .ECALL) ∧
      t.getReg .x5 = 1 ∧
      F a = if t.getReg .x10 = 0 then some (readOutput submission.sizes submission.layout phase t)
        else none) :
    (fun r => (r.value, r.hashCalls, r.hashCompressions)) <$> submission.run phase input =
      (fun p => (F p.1, p.2.1, p.2.2)) <$> countBoth oa := by
  obtain ⟨oc, hp, hf⟩ := hsim
  rw [Rv.run_eq submission phase input s hinit, hf CYCLE_LIMIT (le_of_lt hW), ← hp,
    Functor.map_map]
  simp only [map_bind, Functor.map_map]
  rw [map_eq_bind_pure_comp (x := oc)]
  congr 1; funext o
  obtain ⟨h1, h2, h3⟩ := hQ _ _ o.2.2.2
  have hs : o.1.steps < CYCLE_LIMIT := lt_of_le_of_lt (le_trans o.2.1 o.2.2.1) hW
  obtain ⟨f, hf'⟩ : ∃ f, CYCLE_LIMIT - o.1.steps = f + 1 := ⟨CYCLE_LIMIT - o.1.steps - 1, by omega⟩
  rw [hf', execute_halt f h1 h2]
  simp only [map_pure, Function.comp, toRunResult, Execution.charge, h3]
  congr 2
  split <;> simp_all

/-- `Sim.run_eq` including the `finished` flag (always `true`). -/
theorem Sim.run_eq_fin (submission : Submission) (phase : Phase) (input : Input submission.sizes phase)
    {s : MachineState} (hinit : initialState submission phase input = some s) {W : Nat}
    {oa : OracleComp HashSpec α} {Q : α → MachineState → Prop}
    (hsim : Sim (submission.image phase) s W oa Q) (hW : W < CYCLE_LIMIT)
    (F : α → Option (Output submission.sizes phase))
    (hQ : ∀ a t, Q a t → fetch (submission.image phase) t = some (.base .ECALL) ∧
      t.getReg .x5 = 1 ∧
      F a = if t.getReg .x10 = 0 then some (readOutput submission.sizes submission.layout phase t)
        else none) :
    (fun r => (r.value, r.finished, r.hashCalls, r.hashCompressions)) <$> submission.run phase input =
      (fun p => (F p.1, true, p.2.1, p.2.2)) <$> countBoth oa := by
  obtain ⟨oc, hp, hf⟩ := hsim
  rw [Rv.run_eq submission phase input s hinit, hf CYCLE_LIMIT (le_of_lt hW), ← hp,
    Functor.map_map]
  simp only [map_bind, Functor.map_map]
  rw [map_eq_bind_pure_comp (x := oc)]
  congr 1; funext o
  obtain ⟨h1, h2, h3⟩ := hQ _ _ o.2.2.2
  have hs : o.1.steps < CYCLE_LIMIT := lt_of_le_of_lt (le_trans o.2.1 o.2.2.1) hW
  obtain ⟨f, hf'⟩ : ∃ f, CYCLE_LIMIT - o.1.steps = f + 1 := ⟨CYCLE_LIMIT - o.1.steps - 1, by omega⟩
  rw [hf', execute_halt f h1 h2]
  simp only [map_pure, Function.comp, toRunResult, Execution.charge, h3]
  congr 2
  · split <;> simp_all
  · split <;> rfl

/-- **Termination of a whole phase** under every fixed oracle: finished, and at most `W + 1`
cycles (`W + 1 < CYCLE_LIMIT`). -/
theorem Sim.runWith (submission : Submission) (phase : Phase) (input : Input submission.sizes phase)
    {s : MachineState} (hinit : initialState submission phase input = some s) {W : Nat}
    {oa : OracleComp HashSpec α} {Q : α → MachineState → Prop}
    (hsim : Sim (submission.image phase) s W oa Q) (hW : W + 1 < CYCLE_LIMIT)
    (hQ : ∀ a t, Q a t → fetch (submission.image phase) t = some (.base .ECALL) ∧ t.getReg .x5 = 1)
    (hash : Hash) :
    (submission.runWith hash phase input).finished = true ∧
      (submission.runWith hash phase input).cycles ≤ W + 1 := by
  obtain ⟨oc, _, hf⟩ := hsim
  rw [runWith_eq submission hash phase input s hinit, hf CYCLE_LIMIT (by omega),
    evalWithAnswerFn_bind, evalWithAnswerFn_map]
  generalize evalWithAnswerFn hash oc = o
  obtain ⟨h1, h2⟩ := hQ _ _ o.2.2.2
  have hs : o.1.steps < CYCLE_LIMIT := by have := o.2.1; have := o.2.2.1; omega
  obtain ⟨f, hf'⟩ : ∃ f, CYCLE_LIMIT - o.1.steps = f + 1 := ⟨CYCLE_LIMIT - o.1.steps - 1, by omega⟩
  rw [hf', evalWith_halt hash f h1 h2]
  have := o.2.2.1
  simp only [toRunResult, Execution.charge]
  constructor
  · split <;> rfl
  · omega

end run

end SigGolfCandidate.Radix27Sign



end


section -- SignClone13.Words

/-! ### cloned Words -/

/-!
# Byte lists as doublewords; HASH inputs of the reference formats

* `wordsOf l` : the little-endian doublewords of a byte list (last chunk zero-padded);
  `wordsToNat (wordsOf l) = leNat l`, `wordsOf_append` (first part 8-divisible).
* `bytesOfWord`, `valOfWords` (16-byte values from two dwords), `answerBytes_16`.
* `pad64_eq_query` : `pad64 x = queryOfWords (padBlocks |x|) (wordsOf (padTo64 x))`, and
  `hashInput_eq_pad64` : the HASH input of a machine state is `pad64 x` once its buffer
  `readWords` equals `wordsOf (padTo64 x)`.
* `twWords` : the two dwords of a tweak (`wordsOf_tweak`), and the dword lists of every input
  format (`words_prfInput`, `words_chainInput`, …).
* `readWords` helpers on `BitVec.ofNat` addresses, `writeHash` memory.
-/

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace SigGolfCandidate.Radix27Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

/-! ## `leNat` -/

theorem leNat_append (a b : List Byte) : leNat (a ++ b) = leNat a + 256 ^ a.length * leNat b := by
  induction a with
  | nil => simp [leNat]
  | cons x xs ih => simp only [List.cons_append, leNat, ih, List.length_cons, Nat.pow_succ]; ring

theorem leNat_leBytes (k v : Nat) : leNat (leBytes k v) = v % 256 ^ k := leNat_map_range k v

theorem leNat_le32 (v : Nat) : leNat (le32 v) = v % 2 ^ 32 := by
  rw [le32, leNat_leBytes]; norm_num

theorem leNat_zeros (k : Nat) : leNat (zeros k) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [zeros, List.replicate_succ, leNat] at ih ⊢; exact ih

/-! ## `wordsOf` -/

/-- Little-endian doublewords of a byte list (the last chunk zero-padded). -/
def wordsOf : List Byte → List Word
  | [] => []
  | b :: l => BitVec.ofNat 64 (leNat ((b :: l).take 8)) :: wordsOf ((b :: l).drop 8)
termination_by l => l.length
decreasing_by all_goals (simp; try omega)

theorem wordsOf_nil : wordsOf [] = [] := wordsOf.eq_1

theorem wordsOf_cons (b : Byte) (l : List Byte) :
    wordsOf (b :: l) = BitVec.ofNat 64 (leNat ((b :: l).take 8)) :: wordsOf ((b :: l).drop 8) :=
  wordsOf.eq_2 b l

theorem wordsOf_eq (l : List Byte) (h : l ≠ []) :
    wordsOf l = BitVec.ofNat 64 (leNat (l.take 8)) :: wordsOf (l.drop 8) := by
  cases l with
  | nil => exact absurd rfl h
  | cons b l => exact wordsOf_cons b l

theorem wordsToNat_wordsOf (l : List Byte) : wordsToNat (wordsOf l) = leNat l := by
  induction h : l.length using Nat.strong_induction_on generalizing l with
  | _ n ih =>
    cases l with
    | nil => rw [wordsOf_nil]; rfl
    | cons b l' =>
      rw [wordsOf_cons, wordsToNat, ih _ (by simp at h ⊢; omega) _ rfl]
      have hlt := leNat_lt ((b :: l').take 8)
      have hl8 : ((b :: l').take 8).length ≤ 8 := by simp
      have : (256 : Nat) ^ ((b :: l').take 8).length ≤ 2 ^ 64 := by
        calc (256 : Nat) ^ ((b :: l').take 8).length ≤ 256 ^ 8 := Nat.pow_le_pow_right (by norm_num) hl8
          _ = 2 ^ 64 := by norm_num
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      conv_rhs => rw [← List.take_append_drop 8 (b :: l'), leNat_append]
      by_cases h8 : 8 ≤ (b :: l').length
      · rw [List.length_take, Nat.min_eq_left h8]; norm_num
      · have : (b :: l').drop 8 = [] := List.drop_eq_nil_of_le (by omega)
        rw [this]; simp [leNat]

theorem wordsOf_append (a b : List Byte) (h : a.length % 8 = 0) :
    wordsOf (a ++ b) = wordsOf a ++ wordsOf b := by
  induction hn : a.length using Nat.strong_induction_on generalizing a with
  | _ n ih =>
    cases a with
    | nil => simp [wordsOf_nil]
    | cons x xs =>
      have h8 : 8 ≤ (x :: xs).length := by simp at h ⊢; omega
      rw [List.cons_append, wordsOf_cons, wordsOf_cons, ← List.cons_append,
        List.take_append_of_le_length h8, List.drop_append_of_le_length h8,
        ih _ (by simp at hn ⊢; omega) _ (by simp at h ⊢; omega) rfl]
      rfl

theorem wordsOf_eight (l : List Byte) (h : l.length = 8) : wordsOf l = [BitVec.ofNat 64 (leNat l)] := by
  have hne : l ≠ [] := by rintro rfl; simp at h
  rw [wordsOf_eq l hne, List.take_of_length_le (by omega),
    List.drop_eq_nil_of_le (by omega), wordsOf_nil]

theorem wordsOf_zeros (k : Nat) : wordsOf (zeros (8 * k)) = List.replicate k 0 := by
  induction k with
  | zero => simp [zeros, wordsOf_nil]
  | succ k ih =>
    rw [show 8 * (k + 1) = 8 + 8 * k by ring,
      show zeros (8 + 8 * k) = zeros 8 ++ zeros (8 * k) from List.replicate_add _ _ _,
      wordsOf_append _ _ (by simp), wordsOf_eight _ (by simp), ih, leNat_zeros, List.replicate_succ]
    rfl

@[simp] theorem length_wordsOf_16 (l : List Byte) (h : l.length = 16) : (wordsOf l).length = 2 := by
  rw [← List.take_append_drop 8 l, wordsOf_append _ _ (by simp; omega),
    wordsOf_eight _ (by simp; omega), wordsOf_eight _ (by simp; omega)]
  rfl

/-! ## Words and values -/

/-- The 8 little-endian bytes of a dword. -/
def bytesOfWord (w : Word) : List Byte := (List.range 8).map fun i => w.extractLsb' (8 * i) 8

@[simp] theorem length_bytesOfWord (w : Word) : (bytesOfWord w).length = 8 := by simp [bytesOfWord]

theorem leNat_bytesOfWord (w : Word) : leNat (bytesOfWord w) = w.toNat := by
  have h := leNat_map_range 8 w.toNat
  have he : bytesOfWord w = (List.range 8).map fun i => byte (w.toNat / 256 ^ i) := by
    unfold bytesOfWord
    apply List.map_congr_left
    intro i hi
    have hi' : i < 8 := List.mem_range.mp hi
    have := extractByte_ofNat 64 w.toNat i (by omega)
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq] at this
    exact this
  rw [he, h]
  exact Nat.mod_eq_of_lt (by have := w.isLt; norm_num at this ⊢; omega)

@[simp] theorem wordsOf_bytesOfWord (w : Word) : wordsOf (bytesOfWord w) = [w] := by
  rw [wordsOf_eight _ (by simp), leNat_bytesOfWord, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- The 16-byte value of two dwords. -/
def valOfWords (w0 w1 : Word) : Val := bytesOfWord w0 ++ bytesOfWord w1

@[simp] theorem length_valOfWords (w0 w1 : Word) : (valOfWords w0 w1).length = 16 := by
  simp [valOfWords]

@[simp] theorem wordsOf_valOfWords (w0 w1 : Word) : wordsOf (valOfWords w0 w1) = [w0, w1] := by
  rw [valOfWords, wordsOf_append _ _ (by simp)]; simp

theorem extractLsb'_extractLsb' (a : BitVec 256) (o i : Nat) (hi : i < 8) :
    (a.extractLsb' o 64).extractLsb' (8 * i) 8 = a.extractLsb' (o + 8 * i) 8 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  rw [Nat.pow_add, ← Nat.div_div_eq_div_mul]
  rw [show (64 : Nat) = 8 * i + (64 - 8 * i) by omega, Nat.pow_add, Nat.mod_mul_right_div_self,
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))]

/-- A 16-byte hash answer as two dwords. -/
theorem answerBytes_16 (a : BitVec 256) :
    answerBytes 16 a = valOfWords (a.extractLsb' 0 64) (a.extractLsb' 64 64) := by
  unfold answerBytes valOfWords bytesOfWord
  simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append]
  simp only [extractLsb'_extractLsb' _ _ _ (by norm_num : (0 : Nat) < 8),
    extractLsb'_extractLsb' _ _ _ (by norm_num : (1 : Nat) < 8),
    extractLsb'_extractLsb' _ _ _ (by norm_num : (2 : Nat) < 8),
    extractLsb'_extractLsb' _ _ _ (by norm_num : (3 : Nat) < 8),
    extractLsb'_extractLsb' _ _ _ (by norm_num : (4 : Nat) < 8),
    extractLsb'_extractLsb' _ _ _ (by norm_num : (5 : Nat) < 8),
    extractLsb'_extractLsb' _ _ _ (by norm_num : (6 : Nat) < 8),
    extractLsb'_extractLsb' _ _ _ (by norm_num : (7 : Nat) < 8)]

theorem wordsOf_answerBytes_16 (a : BitVec 256) :
    wordsOf (answerBytes 16 a) = [a.extractLsb' 0 64, a.extractLsb' 64 64] := by
  rw [answerBytes_16, wordsOf_valOfWords]

/-- A 16-byte value is determined by its dwords. -/
theorem val_eq_valOfWords (v : Val) (h : v.length = 16) (w0 w1 : Word) (hw : wordsOf v = [w0, w1]) :
    v = valOfWords w0 w1 := by
  have h1 : v = v.take 8 ++ v.drop 8 := (List.take_append_drop 8 v).symm
  rw [h1, wordsOf_append _ _ (by simp; omega), wordsOf_eight _ (by simp; omega),
    wordsOf_eight _ (by simp; omega)] at hw
  simp only [List.cons_append, List.nil_append, List.cons.injEq, and_true] at hw
  have key : ∀ (l : List Byte), l.length = 8 → l = bytesOfWord (BitVec.ofNat 64 (leNat l)) := by
    intro l hl
    apply List.ext_getElem (by simp [hl])
    intro i h1 h2
    simp only [bytesOfWord, List.getElem_map, List.getElem_range]
    rw [extractByte_ofNat _ _ _ (by simp at h2; omega)]
    apply BitVec.eq_of_toNat_eq
    rw [byte_toNat, leNat_div_mod, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]; rfl
  rw [h1, valOfWords, key (v.take 8) (by simp; omega), key (v.drop 8) (by simp; omega), hw.1, hw.2]

/-! ## Queries -/

theorem pad64_eq_query (x : List Byte) :
    pad64 x = queryOfWords (padBlocks x.length) (wordsOf (padTo64 x)) := by
  unfold pad64 queryOfWords ofList
  rw [wordsToNat_wordsOf]

/-- The HASH input of a state whose buffer holds the padded words of `x`. -/
theorem hashInput_eq_pad64 (t : MachineState) (x : List Byte) (n : Nat) (hn : padBlocks x.length = n)
    (h11 : t.getReg .x11 = BitVec.ofNat 64 (64 * (n + 1))) (hn' : 64 * (n + 1) < 2 ^ 64)
    (h10 : (t.getReg .x10).toNat % 8 = 0)
    (hw : t.readWords (t.getReg .x10) (8 * (n + 1)) = wordsOf (padTo64 x)) :
    hashInput t = pad64 x := by
  rw [hashInput_eq_words t n h11 hn' h10, hw, pad64_eq_query, hn]

/-- HASH argument validity for numeric registers. -/
theorem hashArgs_of {t : MachineState} {a n d : Nat} (h10 : t.getReg .x10 = BitVec.ofNat 64 a)
    (h11 : t.getReg .x11 = BitVec.ofNat 64 n) (h12 : t.getReg .x12 = BitVec.ofNat 64 d)
    (ha : a % 8 = 0) (hn : 0 < n ∧ n % 64 = 0) (han : a + n ≤ 2 ^ 24) (hd : d % 8 = 0)
    (hd' : d + 32 ≤ 2 ^ 24) (hn' : n < 2 ^ 64) : hashArgumentsValid t = true := by
  have ha' : a < 2 ^ 64 := by omega
  have hd'' : d < 2 ^ 64 := by omega
  simp only [hashArgumentsValid, h10, h11, h12, accessValid, rangeValid, MEMORY_BYTES,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha', Nat.mod_eq_of_lt hd'', Nat.mod_eq_of_lt hn',
    Bool.and_eq_true, decide_eq_true_eq]
  omega

/-! ## Tweaks -/

/-- The two dwords of `tweak t lay tau p j` (fields reduced mod their widths). -/
def twWords (t lay tau p j : Nat) : List Word :=
  [BitVec.ofNat 64 (1 + 256 * (t % 256) + 65536 * (lay % 256) + 2 ^ 24 * (tau / 2 ^ 32 % 256) +
      2 ^ 32 * (p % 2 ^ 32)),
   BitVec.ofNat 64 (tau % 2 ^ 32 + 2 ^ 32 * (j % 2 ^ 32))]

theorem wordsOf_tweak (t lay tau p j : Nat) : wordsOf (tweak t lay tau p j) = twWords t lay tau p j := by
  unfold tweak
  rw [List.append_assoc, wordsOf_append _ _ (by simp), wordsOf_eight _ (by simp),
    wordsOf_eight _ (by simp)]
  simp only [twWords, leNat_append, leNat, leNat_le32, byte_toNat, List.length_cons,
    List.length_nil, length_le32]
  simp only [List.cons_append, List.nil_append, Nat.mod_mod, List.cons.injEq, and_true]
  constructor <;> congr 1 <;> ring

/-- `thInput tw payload` followed by zero padding, as dwords. -/
theorem wordsOf_thInput_pad (t lay tau p j : Nat) (payload : List Byte) (z : Nat) :
    wordsOf (thInput (tweak t lay tau p j) payload ++ zeros z) =
      twWords t lay tau p j ++ [0, 0] ++ wordsOf (payload ++ zeros z) := by
  unfold thInput P
  rw [List.append_assoc, List.append_assoc, wordsOf_append _ _ (by simp), wordsOf_tweak,
    wordsOf_append _ _ (by simp), show (16 : Nat) = 8 * 2 from rfl, wordsOf_zeros]
  simp

theorem padTo64_eq (x : List Byte) (n : Nat) (h1 : x.length ≤ 64 * (n + 1)) (h2 : 64 * n < x.length) :
    padBlocks x.length = n ∧ padTo64 x = x ++ zeros (64 * (n + 1) - x.length) := by
  have := padBlocks_eq _ _ h1 h2
  exact ⟨this, by unfold padTo64; rw [this]⟩

/-- A 16-byte value followed by zero padding. -/
theorem wordsOf_val_append (v : Val) (hv : v.length = 16) (rest : List Byte) :
    wordsOf (v ++ rest) = wordsOf v ++ wordsOf rest := wordsOf_append _ _ (by omega)

/-- A list of 16-byte values. -/
theorem wordsOf_flatten (vs : List Val) (hv : ∀ v ∈ vs, v.length = 16) :
    wordsOf vs.flatten = (vs.map wordsOf).flatten := by
  induction vs with
  | nil => simp [wordsOf_nil]
  | cons v vs ih =>
    rw [List.flatten_cons, wordsOf_append _ _ (by rw [hv v (by simp)]),
      ih (fun w hw => hv w (by simp [hw]))]
    simp

theorem length_flatten_vals (vs : List Val) (hv : ∀ v ∈ vs, v.length = 16) :
    vs.flatten.length = 16 * vs.length := by
  induction vs with
  | nil => simp
  | cons v vs ih =>
    simp only [List.flatten_cons, List.length_append, List.length_cons,
      hv v (by simp), ih (fun w hw => hv w (by simp [hw]))]
    ring

/-! ## Input formats as dwords (`wordsOf (padTo64 x)` and `padBlocks`) -/

theorem words_prfInput (S : List Byte) (hS : S.length = 32) (lay tau e i : Nat) :
    padBlocks (prfInput S lay tau e i).length = 0 ∧
    wordsOf (padTo64 (prfInput S lay tau e i)) = twWords 0 lay tau i e ++ [0, 0] ++ wordsOf S := by
  obtain ⟨h1, h2⟩ := padTo64_eq (prfInput S lay tau e i) 0 (by simp [prfInput, hS])
    (by simp [prfInput, hS])
  refine ⟨h1, ?_⟩
  rw [h2, prfInput, wordsOf_thInput_pad]
  simp [hS, zeros]

theorem words_ftsPrfInput (S : List Byte) (hS : S.length = 32) (k idx j : Nat) :
    padBlocks (ftsPrfInput S k idx j).length = 0 ∧
    wordsOf (padTo64 (ftsPrfInput S k idx j)) = twWords 8 k idx 0 j ++ [0, 0] ++ wordsOf S := by
  obtain ⟨h1, h2⟩ := padTo64_eq (ftsPrfInput S k idx j) 0 (by simp [ftsPrfInput, hS])
    (by simp [ftsPrfInput, hS])
  refine ⟨h1, ?_⟩
  rw [h2, ftsPrfInput, wordsOf_thInput_pad]
  simp [hS, zeros]

/-- A 48-byte input `tw | P | v` (chain step, FORS leaf). -/
theorem words_th16 (t lay tau p j : Nat) (v : Val) (hv : v.length = 16) :
    padBlocks (thInput (tweak t lay tau p j) v).length = 0 ∧
    wordsOf (padTo64 (thInput (tweak t lay tau p j) v)) =
      twWords t lay tau p j ++ [0, 0] ++ wordsOf v ++ [0, 0] := by
  obtain ⟨h1, h2⟩ := padTo64_eq (thInput (tweak t lay tau p j) v) 0 (by simp [hv]) (by simp [hv])
  refine ⟨h1, ?_⟩
  rw [h2, wordsOf_thInput_pad, wordsOf_val_append _ hv]
  simp only [length_thInput, length_tweak, hv]
  rw [show 64 * (0 + 1) - (16 + 16 + 16) = 8 * 2 from rfl, wordsOf_zeros]
  simp

/-- The HASH input of a chain step (value-last format `tw || 0^32 || v`, `fmt_chainInput`). -/
theorem hashInput_eq_chain (t : MachineState) (lay tau e i mu : Nat) (v : Val) (hv : v.length = 16)
    (hmu : 1 ≤ mu) (hmu' : mu ≤ 8) (hi : i < 2 ^ 24)
    (h11 : t.getReg .x11 = BitVec.ofNat 64 64) (h10 : (t.getReg .x10).toNat % 8 = 0)
    (hw : t.readWords (t.getReg .x10) 8 =
      twWords 1 lay tau (mu - 1 + 256 * i) e ++ [0, 0, 0, 0] ++ wordsOf v) :
    hashInput t = fmt (chainInput lay tau e i mu v) := by
  rw [hashInput_eq_words t 0 h11 (by norm_num) h10, hw, fmt_chainInput _ _ _ _ _ _ hv hmu hmu' hi]
  unfold queryOfWords ofList
  rw [← wordsToNat_wordsOf (tweak 1 lay tau (mu - 1 + 256 * i) e ++ zeros 32 ++ v),
    wordsOf_append _ _ (by simp [zeros]), wordsOf_append _ _ (by simp), wordsOf_tweak,
    show (32 : Nat) = 8 * 4 from rfl, wordsOf_zeros]
  rfl

/-- The HASH input of the one-block digest (`tw | rho | m`, `fmt_digestInput`). -/
theorem hashInput_eq_digest (t : MachineState) (rho m : List Byte) (hr : rho.length = 16)
    (hm : m.length = 32)
    (h11 : t.getReg .x11 = BitVec.ofNat 64 64) (h10 : (t.getReg .x10).toNat % 8 = 0)
    (hw : t.readWords (t.getReg .x10) 8 = twWords 12 0 0 0 0 ++ wordsOf rho ++ wordsOf m) :
    hashInput t = fmt (digestInput rho m) := by
  rw [hashInput_eq_words t 0 h11 (by norm_num) h10, hw, fmt_digestInput _ _ hr hm]
  unfold queryOfWords ofList
  rw [← wordsToNat_wordsOf (tweak 12 0 0 0 0 ++ rho ++ m),
    wordsOf_append _ _ (by simp [hr]), wordsOf_append _ _ (by simp), wordsOf_tweak]

theorem blocks_fmt_th (t lay tau p j : Nat) (payload : List Byte)
    (ht : byte t ∉ [byte 1, byte 3, byte 10, byte 12]) :
    (fmt (thInput (tweak t lay tau p j) payload)).blocks = (pad64 (thInput (tweak t lay tau p j) payload)).blocks := by
  rw [fmt_thInput _ _ _ _ _ _ ht]

/-- A 64-byte input `tw | P | l | r` (tree node, FORS node). -/
theorem words_th32 (t lay tau p j : Nat) (l r : Val) (hl : l.length = 16) (hr : r.length = 16) :
    padBlocks (thInput (tweak t lay tau p j) (l ++ r)).length = 0 ∧
    wordsOf (padTo64 (thInput (tweak t lay tau p j) (l ++ r))) =
      twWords t lay tau p j ++ [0, 0] ++ wordsOf l ++ wordsOf r := by
  obtain ⟨h1, h2⟩ := padTo64_eq (thInput (tweak t lay tau p j) (l ++ r)) 0 (by simp [hl, hr])
    (by simp [hl, hr])
  refine ⟨h1, ?_⟩
  rw [h2, wordsOf_thInput_pad]
  simp only [length_thInput, length_tweak, List.length_append, hl, hr]
  rw [show 64 * (0 + 1) - (16 + 16 + (16 + 16)) = 0 from rfl, show zeros 0 = [] from rfl,
    List.append_nil, wordsOf_val_append _ hl]
  simp

/-- Inputs `tw | P | v_0 .. v_{m-1}` with `m` 16-byte values filling whole blocks
(`32 + 16 m = 64 (n+1)`): OTS leaf (`m = 42`), FORS roots (`m = 14`). -/
theorem words_thVals (t lay tau p j : Nat) (vs : List Val) (hv : ∀ v ∈ vs, v.length = 16) (n : Nat)
    (hn : 32 + 16 * vs.length = 64 * (n + 1)) :
    padBlocks (thInput (tweak t lay tau p j) vs.flatten).length = n ∧
    wordsOf (padTo64 (thInput (tweak t lay tau p j) vs.flatten)) =
      twWords t lay tau p j ++ [0, 0] ++ (vs.map wordsOf).flatten := by
  have hl := length_flatten_vals vs hv
  obtain ⟨h1, h2⟩ := padTo64_eq (thInput (tweak t lay tau p j) vs.flatten) n
    (by simp [hl]; omega) (by simp [hl]; omega)
  refine ⟨h1, ?_⟩
  rw [h2, wordsOf_thInput_pad]
  simp only [length_thInput, length_tweak, hl]
  rw [show 64 * (n + 1) - (16 + 16 + 16 * vs.length) = 0 by omega, show zeros 0 = [] from rfl,
    List.append_nil, wordsOf_flatten _ hv]

theorem wordsOf_le32_pad (c : Nat) : wordsOf (le32 c ++ zeros 12) = [BitVec.ofNat 64 (c % 2 ^ 32), 0] := by
  rw [show zeros 12 = zeros 4 ++ zeros (8 * 1) from List.replicate_add 4 8 (0 : Byte), ← List.append_assoc,
    wordsOf_append _ _ (by simp), wordsOf_eight _ (by simp), wordsOf_zeros]
  simp [leNat_append, leNat_le32, leNat_zeros]

theorem words_encInput (lay tau e : Nat) (M : Val) (hM : M.length = 16) (c : Nat) :
    padBlocks (encInput lay tau e M c).length = 0 ∧
    wordsOf (padTo64 (encInput lay tau e M c)) =
      twWords 4 lay tau 0 e ++ [0, 0] ++ wordsOf M ++ [BitVec.ofNat 64 (c % 2 ^ 32), 0] := by
  obtain ⟨h1, h2⟩ := padTo64_eq (encInput lay tau e M c) 0 (by simp [encInput, hM])
    (by simp [encInput, hM])
  refine ⟨h1, ?_⟩
  rw [h2, encInput, wordsOf_thInput_pad]
  simp only [length_thInput, length_tweak, List.length_append, hM, length_le32]
  rw [show 64 * (0 + 1) - (16 + 16 + (16 + 4)) = 12 from rfl, List.append_assoc M,
    wordsOf_val_append _ hM, wordsOf_le32_pad]
  simp

theorem words_rndInput (S m : List Byte) (hS : S.length = 32) (hm : m.length = 32) (a : Nat) :
    padBlocks (rndInput S m a).length = 1 ∧
    wordsOf (padTo64 (rndInput S m a)) =
      twWords 7 0 0 a 0 ++ [0, 0] ++ wordsOf S ++ wordsOf m ++ [0, 0, 0, 0] := by
  obtain ⟨h1, h2⟩ := padTo64_eq (rndInput S m a) 1 (by simp [rndInput, hS, hm])
    (by simp [rndInput, hS, hm])
  refine ⟨h1, ?_⟩
  rw [h2, rndInput, wordsOf_thInput_pad]
  simp only [length_thInput, length_tweak, List.length_append, hS, hm]
  rw [show 64 * (1 + 1) - (16 + 16 + (32 + 32)) = 8 * 4 from rfl,
    wordsOf_append _ _ (by simp [hS, hm]), wordsOf_append _ _ (by omega), wordsOf_zeros]
  simp

theorem words_digestInput (rho m : List Byte) (hr : rho.length = 16) (hm : m.length = 32) :
    padBlocks (digestInput rho m).length = 1 ∧
    wordsOf (padTo64 (digestInput rho m)) =
      twWords 12 0 0 0 0 ++ [0, 0] ++ wordsOf rho ++ [0, 0] ++ wordsOf m ++ [0, 0, 0, 0] := by
  obtain ⟨h1, h2⟩ := padTo64_eq (digestInput rho m) 1 (by simp [digestInput, hr, hm])
    (by simp [digestInput, hr, hm])
  refine ⟨h1, ?_⟩
  rw [h2, digestInput, wordsOf_thInput_pad]
  simp only [length_thInput, length_tweak, List.length_append, hr, hm, length_zeros]
  rw [show 64 * (1 + 1) - (16 + 16 + (16 + 16 + 32)) = 8 * 4 from rfl,
    wordsOf_append _ _ (by simp [hr, hm]), wordsOf_append _ _ (by simp [hr]),
    wordsOf_append _ _ (by omega), wordsOf_zeros, show (16 : Nat) = 8 * 2 from rfl, wordsOf_zeros]
  simp

/-! ## `readWords` on numeric addresses -/

theorem readWords_add (t : MachineState) (a : Word) (m n : Nat) :
    t.readWords a (m + n) = t.readWords a m ++ t.readWords (a + BitVec.ofNat 64 (8 * m)) n := by
  induction m generalizing a with
  | zero => simp [MachineState.readWords]
  | succ m ih =>
    rw [Nat.add_right_comm, MachineState.readWords_succ, ih, MachineState.readWords_succ]
    simp only [List.cons_append, BitVec.add_assoc]
    congr 3
    apply BitVec.eq_of_toNat_eq; simp <;> omega

theorem readWords_ofNat_add (t : MachineState) (a m n : Nat) :
    t.readWords (BitVec.ofNat 64 a) (m + n) =
      t.readWords (BitVec.ofNat 64 a) m ++ t.readWords (BitVec.ofNat 64 (a + 8 * m)) n := by
  rw [readWords_add, BitVec.ofNat_add]

theorem readWords_ofNat_succ (t : MachineState) (a n : Nat) :
    t.readWords (BitVec.ofNat 64 a) (n + 1) =
      t.getMem (BitVec.ofNat 64 a) :: t.readWords (BitVec.ofNat 64 (a + 8)) n := by
  rw [MachineState.readWords_succ]
  congr 2
  apply BitVec.eq_of_toNat_eq; simp <;> omega

theorem readWords_ofNat_one (t : MachineState) (a : Nat) :
    t.readWords (BitVec.ofNat 64 a) 1 = [t.getMem (BitVec.ofNat 64 a)] := rfl

theorem readWords_ofNat_two (t : MachineState) (a : Nat) :
    t.readWords (BitVec.ofNat 64 a) 2 = [t.getMem (BitVec.ofNat 64 a), t.getMem (BitVec.ofNat 64 (a + 8))] := by
  rw [readWords_ofNat_succ, readWords_ofNat_succ]; rfl

/-- `readWords` depends only on the memory at the read addresses. -/
theorem readWords_congr (t t' : MachineState) (a : Nat) (n : Nat)
    (h : ∀ i < n, t'.getMem (BitVec.ofNat 64 (a + 8 * i)) = t.getMem (BitVec.ofNat 64 (a + 8 * i))) :
    t'.readWords (BitVec.ofNat 64 a) n = t.readWords (BitVec.ofNat 64 a) n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    rw [readWords_ofNat_succ, readWords_ofNat_succ, ih (a + 8)]
    · congr 1; simpa using h 0 (by omega)
    · intro i hi; have := h (i + 1) (by omega); rw [show a + 8 + 8 * i = a + 8 * (i + 1) by ring]; exact this

/-- An element of a `readWords` list. -/
theorem getMem_of_readWords (t : MachineState) : ∀ (n a i : Nat) (L : List Word),
    t.readWords (BitVec.ofNat 64 a) n = L → i < n → t.getMem (BitVec.ofNat 64 (a + 8 * i)) = L.getD i 0 := by
  intro n
  induction n with
  | zero => intro a i L _ hi; omega
  | succ n ih =>
    intro a i L h hi
    rw [readWords_ofNat_succ] at h
    subst h
    cases i with
    | zero => simp
    | succ i =>
      rw [show a + 8 * (i + 1) = a + 8 + 8 * i by ring, ih (a + 8) i _ rfl (by omega)]
      simp

/-- `readWords` of 16-byte slots `base + 16 i`, `i < m`. -/
theorem readWords_slots (t : MachineState) (base : Nat) (vs : List Val)
    (h : ∀ i (hi : i < vs.length), t.readWords (BitVec.ofNat 64 (base + 16 * i)) 2 = wordsOf vs[i]) :
    t.readWords (BitVec.ofNat 64 base) (2 * vs.length) = (vs.map wordsOf).flatten := by
  induction vs generalizing base with
  | nil => rfl
  | cons v vs ih =>
    rw [List.length_cons, show 2 * (vs.length + 1) = 2 + 2 * vs.length by ring,
      readWords_ofNat_add, ih (base + 16)]
    · have := h 0 (by simp); simp at this; simp [this]
    · intro i hi; have := h (i + 1) (by simp; omega)
      rw [show base + 16 + 16 * i = base + 16 * (i + 1) by ring]; simpa using this

/-! ## `writeHash` -/

theorem writeHash_getMem (s : MachineState) (a : BitVec 256) (x : Word) :
    (writeHash s a).getMem x =
      if x = s.getReg .x12 + 8 + 8 + 8 then a.extractLsb' 192 64
      else if x = s.getReg .x12 + 8 + 8 then a.extractLsb' 128 64
      else if x = s.getReg .x12 + 8 then a.extractLsb' 64 64
      else if x = s.getReg .x12 then a.extractLsb' 0 64
      else s.getMem x := by
  simp only [writeHash, MachineState.writeWords, MachineState.getMem, MachineState.setMem,
    MachineState.setPC, beq_iff_eq]

@[simp] theorem writeHash_getReg (s : MachineState) (a : BitVec 256) (r : Reg) :
    (writeHash s a).getReg r = s.getReg r := by
  cases r <;> simp [writeHash, MachineState.writeWords, MachineState.getReg, MachineState.setMem,
    MachineState.setPC]

@[simp] theorem writeHash_pc (s : MachineState) (a : BitVec 256) : (writeHash s a).pc = s.pc + 4 := by
  simp [writeHash, MachineState.writeWords, MachineState.setMem, MachineState.setPC]

/-- Memory after `writeHash` at `x12 = ofNat d` for a numeric address `x`. -/
theorem writeHash_getMem_ofNat (s : MachineState) (a : BitVec 256) (d x : Nat)
    (hd : s.getReg .x12 = BitVec.ofNat 64 d) (hd' : d + 32 < 2 ^ 64) (hx : x < 2 ^ 64) :
    (writeHash s a).getMem (BitVec.ofNat 64 x) =
      if x = d + 24 then a.extractLsb' 192 64
      else if x = d + 16 then a.extractLsb' 128 64
      else if x = d + 8 then a.extractLsb' 64 64
      else if x = d then a.extractLsb' 0 64
      else s.getMem (BitVec.ofNat 64 x) := by
  rw [writeHash_getMem, hd]
  have e : ∀ k, k < 2 ^ 64 → (BitVec.ofNat 64 x = BitVec.ofNat 64 k ↔ x = k) := by
    intro k hk
    constructor
    · intro h; have := congrArg BitVec.toNat h; simp at this; omega
    · rintro rfl; rfl
  have h3 : BitVec.ofNat 64 d + 8 + 8 + 8 = BitVec.ofNat 64 (d + 24) := by
    apply BitVec.eq_of_toNat_eq; simp <;> omega
  have h2 : BitVec.ofNat 64 d + 8 + 8 = BitVec.ofNat 64 (d + 16) := by
    apply BitVec.eq_of_toNat_eq; simp <;> omega
  have h1 : BitVec.ofNat 64 d + 8 = BitVec.ofNat 64 (d + 8) := by
    apply BitVec.eq_of_toNat_eq; simp <;> omega
  rw [h3, h2, h1]
  simp only [e _ (by omega : d + 24 < 2 ^ 64), e _ (by omega : d + 16 < 2 ^ 64),
    e _ (by omega : d + 8 < 2 ^ 64), e _ (by omega : d < 2 ^ 64)]

/-- The value written by `writeHash` at `x12 = ofNat d` (a 16-byte slot). -/
theorem writeHash_readWords_val (s : MachineState) (a : BitVec 256) (d : Nat)
    (hd : s.getReg .x12 = BitVec.ofNat 64 d) (hd' : d + 32 < 2 ^ 64) :
    (writeHash s a).readWords (BitVec.ofNat 64 d) 2 = wordsOf (answerBytes 16 a) := by
  rw [readWords_ofNat_two, writeHash_getMem_ofNat _ _ _ _ hd hd' (by omega),
    writeHash_getMem_ofNat _ _ _ _ hd hd' (by omega), wordsOf_answerBytes_16]
  simp

/-- `writeHash` does not touch dwords outside `[d, d + 32)` (numeric addresses). -/
theorem writeHash_getMem_frame (s : MachineState) (a : BitVec 256) (d x : Nat)
    (hd : s.getReg .x12 = BitVec.ofNat 64 d) (hd' : d + 32 < 2 ^ 64) (hx : x < 2 ^ 64)
    (hout : x < d ∨ d + 32 ≤ x ∨ x % 8 ≠ d % 8) :
    (writeHash s a).getMem (BitVec.ofNat 64 x) = s.getMem (BitVec.ofNat 64 x) := by
  rw [writeHash_getMem_ofNat _ _ _ _ hd hd' hx]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

end SigGolfCandidate.Radix27Sign



end


section -- SignClone13.Base

/-! ### cloned Base -/

/-!
# Relocatable blocks and `Nat`-level normalization

* `kernel_theorem name : ∀ xs, lhs = rhs` : adds the theorem with proof `fun xs => Eq.refl lhs`,
  checked by the **kernel only** (no elaborator defeq). Used to run the symbolic executor at a
  *variable* pc: `symRun cfg seg pc n = some (relocated result)` holds for every `pc` when the
  block only uses pc for its final pc (no `AUIPC`/`JAL rd≠x0`), so block lemmas can be stated
  for any placement `CodeAt image (pcOf P) seg` (shared code in several images).
* `addN pc n = pc + 4 + … + 4` (the executor's pc after `n` instructions), `addN_ofNat`.
* `bvn` simp set: `BitVec.ofNat 64` arithmetic → `Nat` arithmetic (`ofNat a + ofNat b = ofNat (a+b)`,
  shifts, masks), `ofNat_eq_iff`, `accessValid_ofNat`.
-/

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace SigGolfCandidate.Radix27Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv

open Lean Elab Command Meta in
/-- `kernel_theorem name : ∀ xs, lhs = rhs` — proof `fun xs => Eq.refl lhs`, checked by the
kernel only. -/
elab "kernel_theorem " id:ident " : " t:term : command => do
  liftTermElabM do
    let ty ← Term.elabType t
    Term.synthesizeSyntheticMVarsNoPostponing
    let ty ← instantiateMVars ty
    if ty.hasMVar then throwError "kernel_theorem: statement has metavariables"
    let pf ← forallTelescope ty fun xs body => do
      let some (_, lhs, _) := body.eq? | throwError "kernel_theorem: not an equation"
      mkLambdaFVars xs (← mkEqRefl lhs)
    let base := (← getCurrNamespace) ++ id.getId
    addDecl <| Declaration.thmDecl { name := base, levelParams := [], type := ty, value := pf }

/-- The executor's pc after `n` instructions from `pc`. -/
def addN (pc : Word) : Nat → Word
  | 0 => pc
  | n + 1 => addN (pc + 4) n

/-- `pc` of instruction index `i` (image code starts at `0x1000`). -/
abbrev pcOf (i : Nat) : Word := BitVec.ofNat 64 (0x1000 + 4 * i)

theorem addN_ofNat (a n : Nat) : addN (BitVec.ofNat 64 a) n = BitVec.ofNat 64 (a + 4 * n) := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    rw [addN, show BitVec.ofNat 64 a + 4 = BitVec.ofNat 64 (a + 4) from by
      apply BitVec.eq_of_toNat_eq; simp <;> omega, ih]
    congr 1; ring

theorem addN_pcOf (i n : Nat) : addN (pcOf i) n = pcOf (i + n) := by
  rw [addN_ofNat]; congr 1; ring

/-- Replace the two constant targets of a branch pc. -/
def retarget : E → Word → Word → E
  | .ite op x y _ _, a, b => .ite op x y (.c a) (.c b)
  | e, _, _ => e

/-! ## `BitVec.ofNat 64` arithmetic as `Nat` arithmetic -/

theorem ofNat_add_ofNat (a b : Nat) :
    BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) := by
  apply BitVec.eq_of_toNat_eq; simp

theorem ofNat_sub_ofNat (a b : Nat) (hb : b ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub]; omega

theorem ofNat_shiftLeft (a k : Nat) :
    BitVec.ofNat 64 a <<< k = BitVec.ofNat 64 (a * 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_mod]

theorem ofNat_ushiftRight (a k : Nat) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a >>> k = BitVec.ofNat 64 (a / 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt ha]
  rw [Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_le_self _ _) ha)]

theorem ofNat_and_ofNat (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    BitVec.ofNat 64 a &&& BitVec.ofNat 64 b = BitVec.ofNat 64 (a &&& b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  rw [Nat.mod_eq_of_lt (lt_of_le_of_lt Nat.and_le_left ha)]

theorem ofNat_or_ofNat (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    BitVec.ofNat 64 a ||| BitVec.ofNat 64 b = BitVec.ofNat 64 (a ||| b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_or, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  rw [Nat.mod_eq_of_lt (Nat.or_lt_two_pow ha hb)]

theorem ofNat_xor_ofNat (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    BitVec.ofNat 64 a ^^^ BitVec.ofNat 64 b = BitVec.ofNat 64 (a ^^^ b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_xor, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  rw [Nat.mod_eq_of_lt (Nat.xor_lt_two_pow ha hb)]

theorem ofNat_eq_iff (a b : Nat) :
    BitVec.ofNat 64 a = BitVec.ofNat 64 b ↔ a % 2 ^ 64 = b % 2 ^ 64 := by
  constructor
  · intro h; have := congrArg BitVec.toNat h; simpa using this
  · intro h; apply BitVec.eq_of_toNat_eq; simpa using h

theorem accessValid_ofNat (a w : Nat) :
    accessValid (BitVec.ofNat 64 a) w = true ↔ a % 2 ^ 64 + w ≤ 2 ^ 24 ∧ a % 2 ^ 64 % w = 0 := by
  simp [accessValid, rangeValid, MEMORY_BYTES]

theorem toNat_ofNat_64 (a : Nat) : (BitVec.ofNat 64 a).toNat = a % 2 ^ 64 := by simp

theorem ofNat_beq_ofNat (a b : Nat) :
    (BitVec.ofNat 64 a == BitVec.ofNat 64 b) = decide (a % 2 ^ 64 = b % 2 ^ 64) :=
  Bool.eq_iff_iff.mpr (by simp only [beq_iff_eq, ofNat_eq_iff, decide_eq_true_eq])

theorem ofNat_bne_ofNat (a b : Nat) :
    (BitVec.ofNat 64 a != BitVec.ofNat 64 b) = !decide (a % 2 ^ 64 = b % 2 ^ 64) := by
  rw [bne, ofNat_beq_ofNat]

/-- Signed comparison of small numbers. -/
theorem ofNat_slt_ofNat (a b : Nat) (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) :
    BitVec.slt (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = decide (a < b) := by
  rw [BitVec.slt_eq_ult_of_msb_eq]
  · simp [BitVec.ult]; omega
  · simp [BitVec.msb_eq_decide, Nat.mod_eq_of_lt (by omega : a < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : b < 2 ^ 64)]; omega

/-- First tweak dword (independent of `j`). -/
def twWord0 (t lay tau p : Nat) : Word :=
  BitVec.ofNat 64 (1 + 256 * (t % 256) + 65536 * (lay % 256) + 2 ^ 24 * (tau / 2 ^ 32 % 256) +
    2 ^ 32 * (p % 2 ^ 32))

theorem twWords_eq (t lay tau p j : Nat) :
    twWords t lay tau p j = [twWord0 t lay tau p, BitVec.ofNat 64 (tau % 2 ^ 32 + 2 ^ 32 * (j % 2 ^ 32))] :=
  rfl

/-! ## 32-bit halves of dwords (`SW` merges) -/

/-- Low / high 32-bit half of a dword. -/
abbrev lo32 (w : Word) : BitVec 32 := w.extractLsb' 0 32
abbrev hi32 (w : Word) : BitVec 32 := w.extractLsb' 32 32

@[simp] theorem lo32_replace0 (w : Word) (v : BitVec 32) : lo32 (replaceWord32 w 0 v) = v := by
  ext i hi; simp only [replaceWord32]; interval_cases i <;> simp
@[simp] theorem hi32_replace0 (w : Word) (v : BitVec 32) : hi32 (replaceWord32 w 0 v) = hi32 w := by
  ext i hi; simp only [replaceWord32]; interval_cases i <;> simp
@[simp] theorem lo32_replace1 (w : Word) (v : BitVec 32) : lo32 (replaceWord32 w 1 v) = lo32 w := by
  ext i hi; simp only [replaceWord32]; interval_cases i <;> simp
@[simp] theorem hi32_replace1 (w : Word) (v : BitVec 32) : hi32 (replaceWord32 w 1 v) = v := by
  ext i hi; simp only [replaceWord32]; interval_cases i <;> simp

/-- A dword from its halves. -/
theorem word_of_halves (w : Word) (a b : Nat) (hlo : lo32 w = BitVec.ofNat 32 a)
    (hhi : hi32 w = BitVec.ofNat 32 b) : w = BitVec.ofNat 64 (a % 2 ^ 32 + 2 ^ 32 * (b % 2 ^ 32)) := by
  have h1 := congrArg BitVec.toNat hlo
  have h2 := congrArg BitVec.toNat hhi
  simp only [lo32, hi32, BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow] at h1 h2
  apply BitVec.eq_of_toNat_eq
  have := w.isLt
  simp only [BitVec.toNat_ofNat]
  omega

@[simp] theorem lo32_ofNat (n : Nat) : lo32 (BitVec.ofNat 64 n) = BitVec.ofNat 32 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [lo32, BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_zero]
  omega

@[simp] theorem hi32_ofNat (n : Nat) : hi32 (BitVec.ofNat 64 n) = BitVec.ofNat 32 (n / 2 ^ 32) := by
  apply BitVec.eq_of_toNat_eq
  simp only [hi32, BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega

@[simp] theorem truncate32_ofNat (n : Nat) : (BitVec.ofNat 64 n).truncate 32 = BitVec.ofNat 32 n := by
  apply BitVec.eq_of_toNat_eq; simp <;> omega

end SigGolfCandidate.Radix27Sign

namespace SigGolfCandidate.Radix27Sign
/-- `rvs [hs]` : `rv_simp` plus constant folding, `ite` on `True/False`, and the `ofNat`
normalizations. -/
macro "rvs" " [" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => do
  let ts' : Lean.Syntax.TSepArray [`Lean.Parser.Tactic.simpStar, `Lean.Parser.Tactic.simpErase,
    `Lean.Parser.Tactic.simpLemma] "," := ⟨ts.elemsAndSeps⟩
  `(tactic| simp only [rv_simp, ite_true, ite_false, if_true, if_false, Nat.reduceDiv, Nat.reduceMod,
      Nat.reduceAdd, Nat.reduceMul, Nat.reducePow, truncate32_ofNat, BitVec.toNat_ofNat,
      ofNat_add_ofNat, ofNat_shiftLeft, $ts',*])
end SigGolfCandidate.Radix27Sign

namespace SigGolfCandidate.Radix27Sign
/-- `omega` after removing `% 2^64` of in-range terms (omega is incomplete with the huge
coefficients those produce). -/
macro "bvomega" : tactic =>
  `(tactic| ((try simp (disch := omega) only [Nat.reducePow, Nat.mod_eq_of_lt]); omega))
end SigGolfCandidate.Radix27Sign

namespace SigGolfCandidate.Radix27Sign
open RiscvZkvm.Rv64

/-- OR of values with disjoint bit ranges is addition. -/
theorem ofNat_or_disjoint (x b i : Nat) (hx : x % 2 ^ i = 0) (hb : b < 2 ^ i) (h : x + b < 2 ^ 64) :
    BitVec.ofNat 64 x ||| BitVec.ofNat 64 b = BitVec.ofNat 64 (x + b) := by
  rw [ofNat_or_ofNat _ _ (by omega) (by omega)]
  congr 1
  obtain ⟨q, rfl⟩ : ∃ q, x = 2 ^ i * q := ⟨x / 2 ^ i, by rw [Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hx)]⟩
  rw [Nat.two_pow_add_eq_or_of_lt hb]

theorem ofNat_or_disjoint' (x b i : Nat) (hx : x % 2 ^ i = 0) (hb : b < 2 ^ i) (h : x + b < 2 ^ 64) :
    BitVec.ofNat 64 b ||| BitVec.ofNat 64 x = BitVec.ofNat 64 (x + b) := by
  rw [BitVec.or_comm, ofNat_or_disjoint x b i hx hb h]
end SigGolfCandidate.Radix27Sign

namespace SigGolfCandidate.Radix27Sign
/-- `BitVec.ofNat 64` arithmetic → `Nat` arithmetic, side conditions by `omega`. Run after
`simp only [blk.res, rv_simp]` (whose `addNegLit` turns `x + (-c)` into `x - c`). -/
macro "bvsimp" " [" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => do
  let ts' : Lean.Syntax.TSepArray [`Lean.Parser.Tactic.simpStar, `Lean.Parser.Tactic.simpErase,
    `Lean.Parser.Tactic.simpLemma] "," := ⟨ts.elemsAndSeps⟩
  `(tactic| simp (disch := omega) only [ofNat_add_ofNat, ofNat_sub_ofNat, ofNat_shiftLeft,
      ofNat_ushiftRight, ofNat_and_ofNat, ofNat_xor_ofNat, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.reducePow, Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceSub, truncate32_ofNat,
      ite_true, ite_false, if_true, if_false, BitVec.ofNat_eq_ofNat, Nat.add_sub_cancel,
      Nat.mod_eq_of_lt, Nat.reduceEqDiff, reduceIte, and_true, true_and, or_false, false_or, not_false_eq_true, $ts',*])
end SigGolfCandidate.Radix27Sign

namespace SigGolfCandidate.Radix27Sign
theorem bne_cond (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    ((!decide (a % 2 ^ 64 = b % 2 ^ 64)) = true) ↔ a ≠ b := by
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]; simp
end SigGolfCandidate.Radix27Sign

namespace SigGolfCandidate.Radix27Sign
theorem ofNat_congr {a b : Nat} (h : a = b) : BitVec.ofNat 64 a = BitVec.ofNat 64 b := h ▸ rfl
end SigGolfCandidate.Radix27Sign



end


section -- SignClone13.Code

/-! ### cloned Code -/
-- Generated by SigGolfCandidate/Sign/gen_code.py from work/py/out/sign.lst. Do not edit.

namespace SigGolfCandidate.Radix27Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv

set_option maxRecDepth 16384

/-- instructions 0 .. 54 (start): ld ra, 128(x0); sd ra, 1728(x0); sd ra, 1600(x0); ld ra, 64(x0); sd ra, 1632(x0); ld ra, 136(x0) ... -/
def seg0 : List (BitVec 32) := [0x08003083#32, 0x6c103023#32, 0x64103023#32, 0x04003083#32, 0x66103023#32, 0x08803083#32, 0x6c103423#32, 0x64103423#32, 0x04803083#32, 0x66103423#32, 0x09003083#32, 0x6c103823#32, 0x64103823#32, 0x05003083#32, 0x66103823#32, 0x09803083#32, 0x6c103c23#32, 0x64103c23#32, 0x05803083#32, 0x66103c23#32, 0x70100193#32, 0x62302023#32, 0x000011b7#32, 0xc0118193#32, 0x02303023#32, 0x00004eb7#32, 0x4a0e8e93#32, 0x000eb683#32, 0x008eb703#32, 0x010eb783#32, 0x018eb803#32, 0x00004eb7#32, 0x4a0e8e93#32, 0x000011b7#32, 0xe0118193#32, 0xfe3eb023#32, 0x08003083#32, 0x001eb023#32, 0x08803083#32, 0x001eb423#32, 0x09003083#32, 0x001eb823#32, 0x09803083#32, 0x001ebc23#32, 0x000141b7#32, 0x4a018193#32, 0x0001b023#32, 0x0001b423#32, 0x0001b823#32, 0x0001bc23#32, 0xfe0e8513#32, 0x000105b7#32, 0x04058593#32, 0x16000613#32, 0x00000073#32]
/-- instructions 55 .. 56: ld ra, 352(x0); bne ra, a3, +124 -/
def seg55 : List (BitVec 32) := [0x16003083#32, 0x06d09e63#32]
/-- instructions 57 .. 58: ld ra, 360(x0); bne ra, a4, +116 -/
def seg57 : List (BitVec 32) := [0x16803083#32, 0x06e09a63#32]
/-- instructions 59 .. 60: ld ra, 368(x0); bne ra, a5, +108 -/
def seg59 : List (BitVec 32) := [0x17003083#32, 0x06f09663#32]
/-- instructions 61 .. 62: ld ra, 376(x0); bne ra, a6, +100 -/
def seg61 : List (BitVec 32) := [0x17803083#32, 0x07009263#32]
/-- instructions 63 .. 64: lui t2, 0x100; addi t1, x0, 0 -/
def seg63 : List (BitVec 32) := [0x001003b7#32, 0x00000313#32]
/-- instructions 65 .. 69 (dig_loop): sw t1, 1572(x0); addi a0, x0, 1568; addi a1, x0, 128; addi a2, x0, 320; ecall  -/
def seg65 : List (BitVec 32) := [0x62602223#32, 0x62000513#32, 0x08000593#32, 0x14000613#32, 0x00000073#32]
/-- instructions 70 .. 77: ld ra, 320(x0); ld sp, 328(x0); sd ra, 48(x0); sd sp, 56(x0); addi a0, x0, 32; addi a1, x0, 64 ... -/
def seg70 : List (BitVec 32) := [0x14003083#32, 0x14803103#32, 0x02103823#32, 0x02203c23#32, 0x02000513#32, 0x04000593#32, 0x16000613#32, 0x00000073#32]
/-- instructions 78 .. 81: ld gp, 368(x0); slli gp, gp, 8; srli gp, gp, 54; beq gp, x0, +36 -/
def seg78 : List (BitVec 32) := [0x17003183#32, 0x00819193#32, 0x0361d193#32, 0x02018263#32]
/-- instructions 82 .. 83: addi t1, t1, 1; bne t1, t2, -72 -/
def seg82 : List (BitVec 32) := [0x00130313#32, 0xfa731ce3#32]
/-- instructions 84 .. 86 (fail_digest): addi t0, x0, 1; addi a0, x0, 1; ecall  -/
def seg84 : List (BitVec 32) := [0x00100293#32, 0x00100513#32, 0x00000073#32]
/-- instructions 87 .. 89 (fail_mac): addi t0, x0, 1; addi a0, x0, 1; ecall  -/
def seg87 : List (BitVec 32) := [0x00100293#32, 0x00100513#32, 0x00000073#32]
/-- instructions 90 .. 155 (dig_ok): lui s2, 0x2; addi s2, s2, 1616; ld ra, 48(x0); ld sp, 56(x0); sd ra, 0(s2); sd sp, 8(s2) ... -/
def seg90 : List (BitVec 32) := [0x00002937#32, 0x65090913#32, 0x03003083#32, 0x03803103#32, 0x00193023#32, 0x00293423#32, 0x16003083#32, 0x16803103#32, 0x17003e03#32, 0x01e09b13#32, 0x01eb5b13#32, 0x0220d193#32, 0x3ff1f193#32, 0x70303823#32, 0x02c0d193#32, 0x3ff1f193#32, 0x70303c23#32, 0x0360d193#32, 0x72303023#32, 0x3ff17193#32, 0x72303423#32, 0x00a15193#32, 0x3ff1f193#32, 0x72303823#32, 0x01415193#32, 0x3ff1f193#32, 0x72303c23#32, 0x01e15193#32, 0x3ff1f193#32, 0x74303023#32, 0x02815193#32, 0x3ff1f193#32, 0x74303423#32, 0x03215193#32, 0x3ff1f193#32, 0x74303823#32, 0x03c15213#32, 0x03fe7193#32, 0x00419193#32, 0x004181b3#32, 0x74303c23#32, 0x006e5193#32, 0x3ff1f193#32, 0x76303023#32, 0x010e5193#32, 0x3ff1f193#32, 0x76303423#32, 0x01ae5193#32, 0x3ff1f193#32, 0x76303823#32, 0x024e5193#32, 0x3ff1f193#32, 0x76303c23#32, 0x6b602423#32, 0x0d602423#32, 0x1d602423#32, 0x23602423#32, 0x6a002223#32, 0x0c002223#32, 0x020b5193#32, 0x01819193#32, 0x00001eb7#32, 0x801e8e93#32, 0x01d18733#32, 0x000309b7#32, 0x00000413#32]
/-- instructions 156 .. 163 (fors_loop): slli gp, s0, 3; ld a3, 1808(gp); slli gp, s0, 16; add t4, a4, gp; sw t4, 1696(x0); addi t4, t4, 256 ... -/
def seg156 : List (BitVec 32) := [0x00341193#32, 0x7101b683#32, 0x01041193#32, 0x00370eb3#32, 0x6bd02023#32, 0x100e8e93#32, 0x0dd02023#32, 0x00000493#32]
/-- instructions 164 .. 165 (fors_leaf_loop): andi gp, s1, 1; bne gp, x0, +28 -/
def seg164 : List (BitVec 32) := [0x0014f193#32, 0x00019e63#32]
/-- instructions 166 .. 171: srli gp, s1, 1; sw gp, 1708(x0); addi a0, x0, 1696; addi a1, x0, 64; addi a2, x0, 320; ecall  -/
def seg166 : List (BitVec 32) := [0x0014d193#32, 0x6a302623#32, 0x6a000513#32, 0x04000593#32, 0x14000613#32, 0x00000073#32]
/-- instructions 172 .. 178 (prf_have_1): andi gp, s1, 1; slli gp, gp, 4; ld ra, 320(gp); ld sp, 328(gp); sd ra, 224(x0); sd sp, 232(x0) ... -/
def seg172 : List (BitVec 32) := [0x0014f193#32, 0x00419193#32, 0x1401b083#32, 0x1481b103#32, 0x0e103023#32, 0x0e203423#32, 0x00d49a63#32]
/-- instructions 179 .. 182: ld ra, 224(x0); ld sp, 232(x0); sd ra, 16(s2); sd sp, 24(s2) -/
def seg179 : List (BitVec 32) := [0x0e003083#32, 0x0e803103#32, 0x00193823#32, 0x00293c23#32]
/-- instructions 183 .. 187 (fors_nocap): sw s1, 204(x0); addi a0, x0, 192; slli gp, s1, 4; add a2, s3, gp; ecall  -/
def seg183 : List (BitVec 32) := [0x0c902623#32, 0x0c000513#32, 0x00449193#32, 0x00398633#32, 0x00000073#32]
/-- instructions 188 .. 190: addi s1, s1, 1; addi gp, x0, 1024; bne s1, gp, -104 -/
def seg188 : List (BitVec 32) := [0x00148493#32, 0x40000193#32, 0xf8349ce3#32]
/-- instructions 191 .. 192: addi a5, x0, 1; addi a7, x0, 1024 -/
def seg191 : List (BitVec 32) := [0x00100793#32, 0x40000893#32]
/-- instructions 193 .. 209 (fors_level_loop): addi gp, a5, -1; srl gp, a3, gp; xori gp, gp, 1; slli gp, gp, 4; add gp, gp, s3; ld ra, 0(gp) ... -/
def seg193 : List (BitVec 32) := [0xfff78193#32, 0x0036d1b3#32, 0x0011c193#32, 0x00419193#32, 0x013181b3#32, 0x0001b083#32, 0x0081b103#32, 0x00479e93#32, 0x012e8eb3#32, 0x001eb823#32, 0x002ebc23#32, 0x01041193#32, 0x00e181b3#32, 0x20018193#32, 0x1c303023#32, 0x0018d893#32, 0x00000813#32]
/-- instructions 210 .. 226 (fors_node_loop): add sp, a6, a7; sw sp, 460(x0); slli gp, a6, 5; add gp, gp, s3; ld ra, 0(gp); sd ra, 480(x0) ... -/
def seg210 : List (BitVec 32) := [0x01180133#32, 0x1c202623#32, 0x00581193#32, 0x013181b3#32, 0x0001b083#32, 0x1e103023#32, 0x0081b083#32, 0x1e103423#32, 0x0101b083#32, 0x1e103823#32, 0x0181b083#32, 0x1e103c23#32, 0x1c000513#32, 0x04000593#32, 0x00481193#32, 0x00398633#32, 0x00000073#32]
/-- instructions 227 .. 228: addi a6, a6, 1; bne a6, a7, -72 -/
def seg227 : List (BitVec 32) := [0x00180813#32, 0xfb181ce3#32]
/-- instructions 229 .. 231: addi a5, a5, 1; addi gp, x0, 10; bge gp, a5, -152 -/
def seg229 : List (BitVec 32) := [0x00178793#32, 0x00a00193#32, 0xf6f1d4e3#32]
/-- instructions 232 .. 240: ld ra, 0(s3); ld sp, 8(s3); slli gp, s0, 4; sd ra, 576(gp); sd sp, 584(gp); addi s2, s2, 176 ... -/
def seg232 : List (BitVec 32) := [0x0009b083#32, 0x0089b103#32, 0x00441193#32, 0x2411b023#32, 0x2421b423#32, 0x0b090913#32, 0x00140413#32, 0x00e00193#32, 0xea3418e3#32]
/-- instructions 241 .. 251: srli gp, s6, 32; slli gp, gp, 24; lui t4, 0x1; addi t4, t4, -1279; add gp, gp, t4; sw gp, 544(x0) ... -/
def seg241 : List (BitVec 32) := [0x020b5193#32, 0x01819193#32, 0x00001eb7#32, 0xb01e8e93#32, 0x01d181b3#32, 0x22302023#32, 0x22002223#32, 0x22000513#32, 0x10000593#32, 0x12000613#32, 0x00000073#32]
/-- instructions 252 .. 271: lui t2, 0x400; lui s10, 0x71c7; addi s10, s10, 455; slli s10, s10, 12; addi s10, s10, 455; slli s10, s10, 12 ... -/
def seg252 : List (BitVec 32) := [0x004003b7#32, 0x071c7d37#32, 0x1c7d0d13#32, 0x00cd1d13#32, 0x1c7d0d13#32, 0x00cd1d13#32, 0x1c7d0d13#32, 0x00cd1d13#32, 0x1c7d0d13#32, 0xff03fdb7#32, 0x03fd8d93#32, 0x00cd9d93#32, 0x03fd8d93#32, 0x00cd9d93#32, 0x03fd8d93#32, 0x00cd9d93#32, 0x03fd8d93#32, 0x00400413#32, 0x00001937#32, 0x66090913#32]
/-- instructions 272 .. 273 (layer_loop): addi gp, x0, 4; blt s0, gp, +16 -/
def seg272 : List (BitVec 32) := [0x00400193#32, 0x00344863#32]
/-- instructions 274 .. 276: addi t3, x0, 0; addi s1, x0, 5; jal x0, +44 -/
def seg274 : List (BitVec 32) := [0x00000e13#32, 0x00500493#32, 0x02c0006f#32]
/-- instructions 277 .. 277 (layer_h6): beq s0, x0, +32 -/
def seg277 : List (BitVec 32) := [0x02040063#32]
/-- instructions 278 .. 284: slli gp, s0, 1; add gp, gp, s0; slli gp, gp, 1; addi t3, x0, 23; sub t3, t3, gp; addi s1, x0, 6 ... -/
def seg278 : List (BitVec 32) := [0x00141193#32, 0x008181b3#32, 0x00119193#32, 0x01700e13#32, 0x403e0e33#32, 0x00600493#32, 0x00c0006f#32]
/-- instructions 285 .. 286 (layer_h11): addi t3, x0, 23; addi s1, x0, 11 -/
def seg285 : List (BitVec 32) := [0x01700e13#32, 0x00b00493#32]
/-- instructions 287 .. 301 (layer_route): srl a3, s6, t3; addi gp, x0, 1; sll gp, gp, s1; addi gp, gp, -1; and a3, a3, gp; add t4, t3, s1 ... -/
def seg287 : List (BitVec 32) := [0x01cb56b3#32, 0x00100193#32, 0x009191b3#32, 0xfff18193#32, 0x0036f6b3#32, 0x009e0eb3#32, 0x01db5f33#32, 0x02069193#32, 0x003f0fb3#32, 0x01041193#32, 0x40118193#32, 0x10303023#32, 0x11f03423#32, 0x12003c23#32, 0x00000313#32]
/-- instructions 302 .. 306 (enc_loop): sd t1, 304(x0); addi a0, x0, 256; addi a1, x0, 64; addi a2, x0, 320; ecall  -/
def seg302 : List (BitVec 32) := [0x12603823#32, 0x10000513#32, 0x04000593#32, 0x14000613#32, 0x00000073#32]
/-- instructions 307 .. 310: ld ra, 320(x0); ld sp, 328(x0); or gp, ra, sp; blt gp, x0, +92 -/
def seg307 : List (BitVec 32) := [0x14003083#32, 0x14803103#32, 0x0020e1b3#32, 0x0401ce63#32]
/-- instructions 311 .. 331: srli t3, ra, 3; and t3, t3, s10; and t4, ra, s10; add t3, t3, t4; srli t4, sp, 3; and t4, t4, s10 ... -/
def seg311 : List (BitVec 32) := [0x0030de13#32, 0x01ae7e33#32, 0x01a0feb3#32, 0x01de0e33#32, 0x00315e93#32, 0x01aefeb3#32, 0x01de0e33#32, 0x01a17eb3#32, 0x01de0e33#32, 0x006e5e93#32, 0x01de0e33#32, 0x01be7e33#32, 0x00ce5e93#32, 0x01de0e33#32, 0x018e5e93#32, 0x01de0e33#32, 0x030e5e93#32, 0x01de0e33#32, 0x7ffe7e13#32, 0xf48e0e13#32, 0x000e1463#32]
/-- instructions 332 .. 332: jal x0, +24 -/
def seg332 : List (BitVec 32) := [0x0180006f#32]
/-- instructions 333 .. 334 (enc_next): addi t1, t1, 1; bne t1, t2, -128 -/
def seg333 : List (BitVec 32) := [0x00130313#32, 0xf87310e3#32]
/-- instructions 335 .. 337 (fail_enc): addi t0, x0, 1; addi a0, x0, 1; ecall  -/
def seg335 : List (BitVec 32) := [0x00100293#32, 0x00100513#32, 0x00000073#32]
/-- instructions 338 .. 464 (enc_ok): sd t1, 0(s2); addi a4, x0, 1920; andi gp, ra, 7; sd gp, 0(a4); srli gp, ra, 3; andi gp, gp, 7 ... -/
def seg338 : List (BitVec 32) := [0x00693023#32, 0x78000713#32, 0x0070f193#32, 0x00373023#32, 0x0030d193#32, 0x0071f193#32, 0x00373423#32, 0x0060d193#32, 0x0071f193#32, 0x00373823#32, 0x0090d193#32, 0x0071f193#32, 0x00373c23#32, 0x00c0d193#32, 0x0071f193#32, 0x02373023#32, 0x00f0d193#32, 0x0071f193#32, 0x02373423#32, 0x0120d193#32, 0x0071f193#32, 0x02373823#32, 0x0150d193#32, 0x0071f193#32, 0x02373c23#32, 0x0180d193#32, 0x0071f193#32, 0x04373023#32, 0x01b0d193#32, 0x0071f193#32, 0x04373423#32, 0x01e0d193#32, 0x0071f193#32, 0x04373823#32, 0x0210d193#32, 0x0071f193#32, 0x04373c23#32, 0x0240d193#32, 0x0071f193#32, 0x06373023#32, 0x0270d193#32, 0x0071f193#32, 0x06373423#32, 0x02a0d193#32, 0x0071f193#32, 0x06373823#32, 0x02d0d193#32, 0x0071f193#32, 0x06373c23#32, 0x0300d193#32, 0x0071f193#32, 0x08373023#32, 0x0330d193#32, 0x0071f193#32, 0x08373423#32, 0x0360d193#32, 0x0071f193#32, 0x08373823#32, 0x0390d193#32, 0x0071f193#32, 0x08373c23#32, 0x03c0d193#32, 0x0071f193#32, 0x0a373023#32, 0x00717193#32, 0x0a373423#32, 0x00315193#32, 0x0071f193#32, 0x0a373823#32, 0x00615193#32, 0x0071f193#32, 0x0a373c23#32, 0x00915193#32, 0x0071f193#32, 0x0c373023#32, 0x00c15193#32, 0x0071f193#32, 0x0c373423#32, 0x00f15193#32, 0x0071f193#32, 0x0c373823#32, 0x01215193#32, 0x0071f193#32, 0x0c373c23#32, 0x01515193#32, 0x0071f193#32, 0x0e373023#32, 0x01815193#32, 0x0071f193#32, 0x0e373423#32, 0x01b15193#32, 0x0071f193#32, 0x0e373823#32, 0x01e15193#32, 0x0071f193#32, 0x0e373c23#32, 0x02115193#32, 0x0071f193#32, 0x10373023#32, 0x02415193#32, 0x0071f193#32, 0x10373423#32, 0x02715193#32, 0x0071f193#32, 0x10373823#32, 0x02a15193#32, 0x0071f193#32, 0x10373c23#32, 0x02d15193#32, 0x0071f193#32, 0x12373023#32, 0x03015193#32, 0x0071f193#32, 0x12373423#32, 0x03315193#32, 0x0071f193#32, 0x12373823#32, 0x03615193#32, 0x0071f193#32, 0x12373c23#32, 0x03915193#32, 0x0071f193#32, 0x14373023#32, 0x03c15193#32, 0x0071f193#32, 0x14373423#32, 0x20040463#32]
/-- instructions 465 .. 478: lui s3, 0x34; addi s3, s3, 256; slli gp, s0, 16; ori t4, gp, 1; sw t4, 1696(x0); ori t4, gp, 257 ... -/
def seg465 : List (BitVec 32) := [0x000349b7#32, 0x10098993#32, 0x01041193#32, 0x0011ee93#32, 0x6bd02023#32, 0x1011ee93#32, 0x0dd02023#32, 0x2011ee93#32, 0x35d03023#32, 0x00100193#32, 0x009198b3#32, 0x00000a13#32, 0x0e003023#32, 0x0e003423#32]
/-- instructions 479 .. 485 (tb_leaf_loop): slli gp, s4, 32; or gp, gp, t5; sd gp, 1704(x0); sd gp, 200(x0); sd gp, 840(x0); addi s5, x0, 0 ... -/
def seg479 : List (BitVec 32) := [0x020a1193#32, 0x01e1e1b3#32, 0x6a303423#32, 0x0c303423#32, 0x34303423#32, 0x00000a93#32, 0x00000c13#32]
/-- instructions 486 .. 487 (tb_chain_loop): andi gp, s5, 1; bne gp, x0, +28 -/
def seg486 : List (BitVec 32) := [0x001af193#32, 0x00019e63#32]
/-- instructions 488 .. 493: srli gp, s5, 1; sw gp, 1700(x0); addi a0, x0, 1696; addi a1, x0, 64; addi a2, x0, 320; ecall  -/
def seg488 : List (BitVec 32) := [0x001ad193#32, 0x6a302223#32, 0x6a000513#32, 0x04000593#32, 0x14000613#32, 0x00000073#32]
/-- instructions 494 .. 505 (prf_have_2): andi gp, s5, 1; slli gp, gp, 4; ld ra, 320(gp); ld sp, 328(gp); sd ra, 240(x0); sd sp, 248(x0) ... -/
def seg494 : List (BitVec 32) := [0x001af193#32, 0x00419193#32, 0x1401b083#32, 0x1481b103#32, 0x0e103823#32, 0x0e203c23#32, 0x0c000513#32, 0x0f000613#32, 0x00000b93#32, 0x003a9193#32, 0x7801bc83#32, 0x02da1063#32]
/-- instructions 506 .. 506: bne s7, s9, +28 -/
def seg506 : List (BitVec 32) := [0x019b9e63#32]
/-- instructions 507 .. 512: slli gp, s5, 4; add gp, gp, s2; ld ra, 240(x0); ld sp, 248(x0); sd ra, 8(gp); sd sp, 16(gp) -/
def seg507 : List (BitVec 32) := [0x004a9193#32, 0x012181b3#32, 0x0f003083#32, 0x0f803103#32, 0x0011b423#32, 0x0021b823#32]
/-- instructions 513 .. 520 (tb_cap0_3,tb_step_loop): addi s7, s7, 1; srli gp, s8, 3; slli gp, gp, 8; andi t4, s8, 7; or gp, gp, t4; sw gp, 196(x0) ... -/
def seg513 : List (BitVec 32) := [0x001b8b93#32, 0x003c5193#32, 0x00819193#32, 0x007c7e93#32, 0x01d1e1b3#32, 0x0c302223#32, 0x0c000513#32, 0x00000073#32]
/-- instructions 521 .. 522: addi s8, s8, 1; bne s4, a3, +32 -/
def seg521 : List (BitVec 32) := [0x001c0c13#32, 0x02da1063#32]
/-- instructions 523 .. 523: bne s7, s9, +28 -/
def seg523 : List (BitVec 32) := [0x019b9e63#32]
/-- instructions 524 .. 529: slli gp, s5, 4; add gp, gp, s2; ld ra, 240(x0); ld sp, 248(x0); sd ra, 8(gp); sd sp, 16(gp) -/
def seg524 : List (BitVec 32) := [0x004a9193#32, 0x012181b3#32, 0x0f003083#32, 0x0f803103#32, 0x0011b423#32, 0x0021b823#32]
/-- instructions 530 .. 531 (tb_cap1_4): addi gp, x0, 7; bne s7, gp, -72 -/
def seg530 : List (BitVec 32) := [0x00700193#32, 0xfa3b9ce3#32]
/-- instructions 532 .. 540: addi s8, s8, 1; slli gp, s5, 4; ld ra, 240(x0); ld sp, 248(x0); sd ra, 864(gp); sd sp, 872(gp) ... -/
def seg532 : List (BitVec 32) := [0x001c0c13#32, 0x004a9193#32, 0x0f003083#32, 0x0f803103#32, 0x3611b023#32, 0x3621b423#32, 0x001a8a93#32, 0x02a00193#32, 0xf23a94e3#32]
/-- instructions 541 .. 545: addi a0, x0, 832; addi a1, x0, 704; slli gp, s4, 4; add a2, s3, gp; ecall  -/
def seg541 : List (BitVec 32) := [0x34000513#32, 0x2c000593#32, 0x004a1193#32, 0x00398633#32, 0x00000073#32]
/-- instructions 546 .. 547: addi s4, s4, 1; bne s4, a7, -272 -/
def seg546 : List (BitVec 32) := [0x001a0a13#32, 0xef1a18e3#32]
/-- instructions 548 .. 548: addi a5, x0, 1 -/
def seg548 : List (BitVec 32) := [0x00100793#32]
/-- instructions 549 .. 565 (tb_level_loop): addi gp, a5, -1; srl gp, a3, gp; xori gp, gp, 1; slli gp, gp, 4; add gp, gp, s3; ld ra, 0(gp) ... -/
def seg549 : List (BitVec 32) := [0xfff78193#32, 0x0036d1b3#32, 0x0011c193#32, 0x00419193#32, 0x013181b3#32, 0x0001b083#32, 0x0081b103#32, 0x00479e93#32, 0x012e8eb3#32, 0x281ebc23#32, 0x2a2eb023#32, 0x01041193#32, 0x3011e193#32, 0x1c303023#32, 0x1de02423#32, 0x0018d893#32, 0x00000813#32]
/-- instructions 566 .. 582 (tb_node_loop): add sp, a6, a7; sw sp, 460(x0); slli gp, a6, 5; add gp, gp, s3; ld ra, 0(gp); sd ra, 480(x0) ... -/
def seg566 : List (BitVec 32) := [0x01180133#32, 0x1c202623#32, 0x00581193#32, 0x013181b3#32, 0x0001b083#32, 0x1e103023#32, 0x0081b083#32, 0x1e103423#32, 0x0101b083#32, 0x1e103823#32, 0x0181b083#32, 0x1e103c23#32, 0x1c000513#32, 0x04000593#32, 0x00481193#32, 0x00398633#32, 0x00000073#32]
/-- instructions 583 .. 584: addi a6, a6, 1; bne a6, a7, -72 -/
def seg583 : List (BitVec 32) := [0x00180813#32, 0xfb181ce3#32]
/-- instructions 585 .. 586: addi a5, a5, 1; bge s1, a5, -148 -/
def seg585 : List (BitVec 32) := [0x00178793#32, 0xf6f4d6e3#32]
/-- instructions 587 .. 593: ld ra, 0(s3); ld sp, 8(s3); sd ra, 288(x0); sd sp, 296(x0); addi s2, s2, -856; addi s0, s0, -1 ... -/
def seg587 : List (BitVec 32) := [0x0009b083#32, 0x0089b103#32, 0x12103023#32, 0x12203423#32, 0xca890913#32, 0xfff40413#32, 0xafdff06f#32]
/-- instructions 594 .. 602 (top_layer): addi gp, x0, 1; sd gp, 1696(x0); sd t6, 1704(x0); addi gp, x0, 257; sw gp, 192(x0); sd t6, 200(x0) ... -/
def seg594 : List (BitVec 32) := [0x00100193#32, 0x6a303023#32, 0x6bf03423#32, 0x10100193#32, 0x0c302023#32, 0x0df03423#32, 0x0e003023#32, 0x0e003423#32, 0x00000a93#32]
/-- instructions 603 .. 604 (top_chain_loop): andi gp, s5, 1; bne gp, x0, +28 -/
def seg603 : List (BitVec 32) := [0x001af193#32, 0x00019e63#32]
/-- instructions 605 .. 610: srli gp, s5, 1; sw gp, 1700(x0); addi a0, x0, 1696; addi a1, x0, 64; addi a2, x0, 320; ecall  -/
def seg605 : List (BitVec 32) := [0x001ad193#32, 0x6a302223#32, 0x6a000513#32, 0x04000593#32, 0x14000613#32, 0x00000073#32]
/-- instructions 611 .. 621 (prf_have_5): andi gp, s5, 1; slli gp, gp, 4; ld ra, 320(gp); ld sp, 328(gp); sd ra, 240(x0); sd sp, 248(x0) ... -/
def seg611 : List (BitVec 32) := [0x001af193#32, 0x00419193#32, 0x1401b083#32, 0x1481b103#32, 0x0e103823#32, 0x0e203c23#32, 0x0f000613#32, 0x003a9193#32, 0x7801bc83#32, 0x003a9c13#32, 0x00000b93#32]
/-- instructions 622 .. 622 (top_step_loop): beq s7, s9, +44 -/
def seg622 : List (BitVec 32) := [0x039b8663#32]
/-- instructions 623 .. 629: srli gp, s8, 3; slli gp, gp, 8; andi t4, s8, 7; or gp, gp, t4; sw gp, 196(x0); addi a0, x0, 192 ... -/
def seg623 : List (BitVec 32) := [0x003c5193#32, 0x00819193#32, 0x007c7e93#32, 0x01d1e1b3#32, 0x0c302223#32, 0x0c000513#32, 0x00000073#32]
/-- instructions 630 .. 632: addi s8, s8, 1; addi s7, s7, 1; jal x0, -40 -/
def seg630 : List (BitVec 32) := [0x001c0c13#32, 0x001b8b93#32, 0xfd9ff06f#32]
/-- instructions 633 .. 641 (top_step_done): slli gp, s5, 4; add gp, gp, s2; ld ra, 240(x0); ld sp, 248(x0); sd ra, 8(gp); sd sp, 16(gp) ... -/
def seg633 : List (BitVec 32) := [0x004a9193#32, 0x012181b3#32, 0x0f003083#32, 0x0f803103#32, 0x0011b423#32, 0x0021b823#32, 0x001a8a93#32, 0x02a00193#32, 0xf63a94e3#32]
/-- instructions 642 .. 645: lui s3, 0x4; addi s3, s3, 1216; lui a7, 0x8; addi a5, x0, 0 -/
def seg642 : List (BitVec 32) := [0x000049b7#32, 0x4c098993#32, 0x000088b7#32, 0x00000793#32]
/-- instructions 646 .. 657 (top_path_loop): srl a6, a3, a5; xori a6, a6, 1; slli gp, a5, 32; addi gp, gp, 1665; addi gp, gp, 1664; sd gp, 1696(x0) ... -/
def seg646 : List (BitVec 32) := [0x00f6d833#32, 0x00184813#32, 0x02079193#32, 0x68118193#32, 0x68018193#32, 0x6a303023#32, 0x02081193#32, 0x6a303423#32, 0x6a000513#32, 0x04000593#32, 0x14000613#32, 0x00000073#32]
/-- instructions 658 .. 674: slli gp, a6, 4; add gp, gp, s3; slli t4, a5, 4; add t4, t4, s2; ld ra, 0(gp); ld sp, 320(x0) ... -/
def seg658 : List (BitVec 32) := [0x00481193#32, 0x013181b3#32, 0x00479e93#32, 0x012e8eb3#32, 0x0001b083#32, 0x14003103#32, 0x0020c0b3#32, 0x2a1eb423#32, 0x0081b083#32, 0x14803103#32, 0x0020c0b3#32, 0x2a1eb823#32, 0x011989b3#32, 0x0018d893#32, 0x00178793#32, 0x00b00193#32, 0xf83798e3#32]
/-- instructions 675 .. 1113 (pack_0,pack_1,pack_2,pack_3,pack_4,pack_5,pack_6,pack_7,pack_8,pack_9): lui t3, 0x1; addi t3, t3, -1792; lui t4, 0x3; lwu ra, 0(t3); lwu sp, 8(t3); slli sp, sp, 32 ... -/
def seg675 : List (BitVec 32) := [0x00001e37#32, 0x900e0e13#32, 0x00003eb7#32, 0x000e6083#32, 0x008e6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb023#32, 0x00ce6083#32, 0x010e6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb423#32, 0x014e6083#32, 0x018e6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb823#32, 0x01ce6083#32, 0x020e6103#32, 0x02011113#32, 0x002080b3#32, 0x001ebc23#32, 0x024e6083#32, 0x028e6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb023#32, 0x02ce6083#32, 0x030e6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb423#32, 0x034e6083#32, 0x038e6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb823#32, 0x03ce6083#32, 0x040e6103#32, 0x02011113#32, 0x002080b3#32, 0x021ebc23#32, 0x00001e37#32, 0x944e0e13#32, 0x00003eb7#32, 0x040e8e93#32, 0x000e6083#32, 0x004e6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb023#32, 0x008e6083#32, 0x00ce6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb423#32, 0x010e6083#32, 0x014e6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb823#32, 0x018e6083#32, 0x01ce6103#32, 0x02011113#32, 0x002080b3#32, 0x001ebc23#32, 0x020e6083#32, 0x024e6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb023#32, 0x028e6083#32, 0x02ce6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb423#32, 0x030e6083#32, 0x034e6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb823#32, 0x038e6083#32, 0x03ce6103#32, 0x02011113#32, 0x002080b3#32, 0x021ebc23#32, 0x00001e37#32, 0x984e0e13#32, 0x00003eb7#32, 0x080e8e93#32, 0x000e6083#32, 0x004e6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb023#32, 0x008e6083#32, 0x00ce6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb423#32, 0x010e6083#32, 0x014e6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb823#32, 0x018e6083#32, 0x01ce6103#32, 0x02011113#32, 0x002080b3#32, 0x001ebc23#32, 0x020e6083#32, 0x024e6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb023#32, 0x028e6083#32, 0x02ce6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb423#32, 0x030e6083#32, 0x034e6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb823#32, 0x038e6083#32, 0x03ce6103#32, 0x02011113#32, 0x002080b3#32, 0x021ebc23#32, 0x00001e37#32, 0x9c4e0e13#32, 0x00003eb7#32, 0x0c0e8e93#32, 0x000e6083#32, 0x004e6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb023#32, 0x008e6083#32, 0x00ce6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb423#32, 0x010e6083#32, 0x014e6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb823#32, 0x018e6083#32, 0x01ce6103#32, 0x02011113#32, 0x002080b3#32, 0x001ebc23#32, 0x020e6083#32, 0x024e6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb023#32, 0x028e6083#32, 0x02ce6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb423#32, 0x030e6083#32, 0x034e6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb823#32, 0x038e6083#32, 0x03ce6103#32, 0x02011113#32, 0x002080b3#32, 0x021ebc23#32, 0x00001e37#32, 0xa04e0e13#32, 0x00003eb7#32, 0x100e8e93#32, 0x000e6083#32, 0x004e6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb023#32, 0x008e6083#32, 0x00ce6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb423#32, 0x010e6083#32, 0x014e6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb823#32, 0x018e6083#32, 0x01ce6103#32, 0x02011113#32, 0x002080b3#32, 0x001ebc23#32, 0x020e6083#32, 0x024e6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb023#32, 0x028e6083#32, 0x02ce6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb423#32, 0x030e6083#32, 0x034e6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb823#32, 0x038e6083#32, 0x03ce6103#32, 0x02011113#32, 0x002080b3#32, 0x021ebc23#32, 0x00001e37#32, 0xa44e0e13#32, 0x00003eb7#32, 0x140e8e93#32, 0x000e6083#32, 0x004e6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb023#32, 0x008e6083#32, 0x00ce6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb423#32, 0x010e6083#32, 0x014e6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb823#32, 0x018e6083#32, 0x01ce6103#32, 0x02011113#32, 0x002080b3#32, 0x001ebc23#32, 0x020e6083#32, 0x024e6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb023#32, 0x028e6083#32, 0x02ce6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb423#32, 0x030e6083#32, 0x034e6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb823#32, 0x038e6083#32, 0x03ce6103#32, 0x02011113#32, 0x002080b3#32, 0x021ebc23#32, 0x00001e37#32, 0xa84e0e13#32, 0x00003eb7#32, 0x180e8e93#32, 0x000e6083#32, 0x004e6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb023#32, 0x008e6083#32, 0x00ce6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb423#32, 0x010e6083#32, 0x014e6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb823#32, 0x018e6083#32, 0x01ce6103#32, 0x02011113#32, 0x002080b3#32, 0x001ebc23#32, 0x020e6083#32, 0x024e6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb023#32, 0x028e6083#32, 0x02ce6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb423#32, 0x030e6083#32, 0x034e6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb823#32, 0x038e6083#32, 0x03ce6103#32, 0x02011113#32, 0x002080b3#32, 0x021ebc23#32, 0x00001e37#32, 0xac4e0e13#32, 0x00003eb7#32, 0x1c0e8e93#32, 0x000e6083#32, 0x004e6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb023#32, 0x008e6083#32, 0x00ce6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb423#32, 0x010e6083#32, 0x014e6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb823#32, 0x018e6083#32, 0x01ce6103#32, 0x02011113#32, 0x002080b3#32, 0x001ebc23#32, 0x020e6083#32, 0x024e6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb023#32, 0x028e6083#32, 0x02ce6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb423#32, 0x030e6083#32, 0x034e6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb823#32, 0x038e6083#32, 0x03ce6103#32, 0x02011113#32, 0x002080b3#32, 0x021ebc23#32, 0x00001e37#32, 0xb04e0e13#32, 0x00003eb7#32, 0x200e8e93#32, 0x000e6083#32, 0x004e6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb023#32, 0x008e6083#32, 0x00ce6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb423#32, 0x010e6083#32, 0x014e6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb823#32, 0x018e6083#32, 0x01ce6103#32, 0x02011113#32, 0x002080b3#32, 0x001ebc23#32, 0x020e6083#32, 0x024e6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb023#32, 0x028e6083#32, 0x02ce6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb423#32, 0x030e6083#32, 0x034e6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb823#32, 0x038e6083#32, 0x03ce6103#32, 0x02011113#32, 0x002080b3#32, 0x021ebc23#32, 0x00001e37#32, 0xb44e0e13#32, 0x00003eb7#32, 0x240e8e93#32, 0x000e6083#32, 0x004e6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb023#32, 0x008e6083#32, 0x00ce6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb423#32, 0x010e6083#32, 0x014e6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb823#32, 0x018e6083#32, 0x01ce6103#32, 0x02011113#32, 0x002080b3#32, 0x001ebc23#32, 0x020e6083#32, 0x024e6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb023#32, 0x028e6083#32, 0x02ce6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb423#32, 0x030e6083#32, 0x034e6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb823#32, 0x038e6083#32, 0x03ce6103#32, 0x02011113#32, 0x002080b3#32, 0x021ebc23#32]
/-- instructions 1114 .. 1394 (pack_10,pack_11,pack_12,pack_13,pack_14,pack_15,pack_16,pack_17,pack_18,pack_19): lui t3, 0x1; addi t3, t3, -1148; lui t4, 0x3; addi t4, t4, 640; lwu ra, 0(t3); lwu sp, 4(t3) ... -/
def seg1114 : List (BitVec 32) := [0x00001e37#32, 0xb84e0e13#32, 0x00003eb7#32, 0x280e8e93#32, 0x000e6083#32, 0x004e6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb023#32, 0x008e6083#32, 0x00ce6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb423#32, 0x010e6083#32, 0x014e6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb823#32, 0x018e6083#32, 0x01ce6103#32, 0x02011113#32, 0x002080b3#32, 0x001ebc23#32, 0x020e6083#32, 0x024e6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb023#32, 0x028e6083#32, 0x02ce6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb423#32, 0x030e6083#32, 0x034e6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb823#32, 0x038e6083#32, 0x03ce6103#32, 0x02011113#32, 0x002080b3#32, 0x021ebc23#32, 0x00001e37#32, 0xbc4e0e13#32, 0x00003eb7#32, 0x2c0e8e93#32, 0x000e6083#32, 0x004e6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb023#32, 0x008e6083#32, 0x00ce6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb423#32, 0x010e6083#32, 0x014e6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb823#32, 0x018e6083#32, 0x01ce6103#32, 0x02011113#32, 0x002080b3#32, 0x001ebc23#32, 0x020e6083#32, 0x024e6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb023#32, 0x028e6083#32, 0x02ce6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb423#32, 0x030e6083#32, 0x034e6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb823#32, 0x038e6083#32, 0x03ce6103#32, 0x02011113#32, 0x002080b3#32, 0x021ebc23#32, 0x00001e37#32, 0xc04e0e13#32, 0x00003eb7#32, 0x300e8e93#32, 0x000e6083#32, 0x004e6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb023#32, 0x008e6083#32, 0x00ce6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb423#32, 0x010e6083#32, 0x014e6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb823#32, 0x018e6083#32, 0x01ce6103#32, 0x02011113#32, 0x002080b3#32, 0x001ebc23#32, 0x020e6083#32, 0x024e6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb023#32, 0x028e6083#32, 0x02ce6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb423#32, 0x030e6083#32, 0x034e6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb823#32, 0x038e6083#32, 0x03ce6103#32, 0x02011113#32, 0x002080b3#32, 0x021ebc23#32, 0x00001e37#32, 0xc44e0e13#32, 0x00003eb7#32, 0x340e8e93#32, 0x000e6083#32, 0x004e6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb023#32, 0x008e6083#32, 0x00ce6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb423#32, 0x010e6083#32, 0x014e6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb823#32, 0x01ce3083#32, 0x001ebc23#32, 0x024e3083#32, 0x021eb023#32, 0x02ce3083#32, 0x021eb423#32, 0x034e3083#32, 0x021eb823#32, 0x03ce3083#32, 0x021ebc23#32, 0x00001e37#32, 0xc88e0e13#32, 0x00003eb7#32, 0x380e8e93#32, 0x000e3083#32, 0x001eb023#32, 0x008e3083#32, 0x001eb423#32, 0x010e3083#32, 0x001eb823#32, 0x018e3083#32, 0x001ebc23#32, 0x020e3083#32, 0x021eb023#32, 0x028e3083#32, 0x021eb423#32, 0x030e3083#32, 0x021eb823#32, 0x038e3083#32, 0x021ebc23#32, 0x00001e37#32, 0xcc8e0e13#32, 0x00003eb7#32, 0x3c0e8e93#32, 0x000e3083#32, 0x001eb023#32, 0x008e3083#32, 0x001eb423#32, 0x010e3083#32, 0x001eb823#32, 0x018e3083#32, 0x001ebc23#32, 0x020e3083#32, 0x021eb023#32, 0x028e3083#32, 0x021eb423#32, 0x030e3083#32, 0x021eb823#32, 0x038e3083#32, 0x021ebc23#32, 0x00001e37#32, 0xd08e0e13#32, 0x00003eb7#32, 0x400e8e93#32, 0x000e3083#32, 0x001eb023#32, 0x008e3083#32, 0x001eb423#32, 0x010e3083#32, 0x001eb823#32, 0x018e3083#32, 0x001ebc23#32, 0x020e3083#32, 0x021eb023#32, 0x028e3083#32, 0x021eb423#32, 0x030e3083#32, 0x021eb823#32, 0x038e3083#32, 0x021ebc23#32, 0x00001e37#32, 0xd48e0e13#32, 0x00003eb7#32, 0x440e8e93#32, 0x000e3083#32, 0x001eb023#32, 0x008e3083#32, 0x001eb423#32, 0x010e3083#32, 0x001eb823#32, 0x018e3083#32, 0x001ebc23#32, 0x020e3083#32, 0x021eb023#32, 0x028e3083#32, 0x021eb423#32, 0x030e3083#32, 0x021eb823#32, 0x038e3083#32, 0x021ebc23#32, 0x00001e37#32, 0xd88e0e13#32, 0x00003eb7#32, 0x480e8e93#32, 0x000e3083#32, 0x001eb023#32, 0x008e3083#32, 0x001eb423#32, 0x010e3083#32, 0x001eb823#32, 0x018e3083#32, 0x001ebc23#32, 0x020e3083#32, 0x021eb023#32, 0x028e3083#32, 0x021eb423#32, 0x030e3083#32, 0x021eb823#32, 0x038e3083#32, 0x021ebc23#32, 0x00001e37#32, 0xdc8e0e13#32, 0x00003eb7#32, 0x4c0e8e93#32, 0x000e3083#32, 0x001eb023#32, 0x008e3083#32, 0x001eb423#32, 0x010e3083#32, 0x001eb823#32, 0x018e3083#32, 0x001ebc23#32, 0x020e3083#32, 0x021eb023#32, 0x028e3083#32, 0x021eb423#32, 0x030e3083#32, 0x021eb823#32, 0x038e3083#32, 0x021ebc23#32]
/-- instructions 1395 .. 1705 (pack_20,pack_21,pack_22,pack_23,pack_24,pack_25,pack_26,pack_27,pack_28,pack_29): lui t3, 0x1; addi t3, t3, -504; lui t4, 0x3; addi t4, t4, 1280; ld ra, 0(t3); sd ra, 0(t4) ... -/
def seg1395 : List (BitVec 32) := [0x00001e37#32, 0xe08e0e13#32, 0x00003eb7#32, 0x500e8e93#32, 0x000e3083#32, 0x001eb023#32, 0x008e3083#32, 0x001eb423#32, 0x010e3083#32, 0x001eb823#32, 0x018e3083#32, 0x001ebc23#32, 0x020e3083#32, 0x021eb023#32, 0x028e3083#32, 0x021eb423#32, 0x030e3083#32, 0x021eb823#32, 0x038e3083#32, 0x021ebc23#32, 0x00001e37#32, 0xe48e0e13#32, 0x00003eb7#32, 0x540e8e93#32, 0x000e3083#32, 0x001eb023#32, 0x008e3083#32, 0x001eb423#32, 0x010e3083#32, 0x001eb823#32, 0x018e3083#32, 0x001ebc23#32, 0x020e3083#32, 0x021eb023#32, 0x028e3083#32, 0x021eb423#32, 0x030e3083#32, 0x021eb823#32, 0x038e3083#32, 0x021ebc23#32, 0x00001e37#32, 0xe88e0e13#32, 0x00003eb7#32, 0x580e8e93#32, 0x000e3083#32, 0x001eb023#32, 0x008e3083#32, 0x001eb423#32, 0x010e3083#32, 0x001eb823#32, 0x018e3083#32, 0x001ebc23#32, 0x020e3083#32, 0x021eb023#32, 0x028e3083#32, 0x021eb423#32, 0x030e3083#32, 0x021eb823#32, 0x038e3083#32, 0x021ebc23#32, 0x00001e37#32, 0xec8e0e13#32, 0x00003eb7#32, 0x5c0e8e93#32, 0x000e3083#32, 0x001eb023#32, 0x008e3083#32, 0x001eb423#32, 0x010e3083#32, 0x001eb823#32, 0x018e3083#32, 0x001ebc23#32, 0x020e3083#32, 0x021eb023#32, 0x028e3083#32, 0x021eb423#32, 0x030e3083#32, 0x021eb823#32, 0x038e3083#32, 0x021ebc23#32, 0x00001e37#32, 0xf08e0e13#32, 0x00003eb7#32, 0x600e8e93#32, 0x000e3083#32, 0x001eb023#32, 0x008e3083#32, 0x001eb423#32, 0x010e3083#32, 0x001eb823#32, 0x018e3083#32, 0x001ebc23#32, 0x020e3083#32, 0x021eb023#32, 0x028e3083#32, 0x021eb423#32, 0x030e3083#32, 0x021eb823#32, 0x038e3083#32, 0x021ebc23#32, 0x00001e37#32, 0xf48e0e13#32, 0x00003eb7#32, 0x640e8e93#32, 0x000e3083#32, 0x001eb023#32, 0x008e3083#32, 0x001eb423#32, 0x010e3083#32, 0x001eb823#32, 0x068e6083#32, 0x070e6103#32, 0x02011113#32, 0x002080b3#32, 0x001ebc23#32, 0x074e6083#32, 0x078e6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb023#32, 0x07ce6083#32, 0x080e6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb423#32, 0x084e6083#32, 0x088e6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb823#32, 0x08ce6083#32, 0x090e6103#32, 0x02011113#32, 0x002080b3#32, 0x021ebc23#32, 0x00001e37#32, 0xfdce0e13#32, 0x00003eb7#32, 0x680e8e93#32, 0x000e6083#32, 0x004e6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb023#32, 0x008e6083#32, 0x00ce6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb423#32, 0x010e6083#32, 0x014e6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb823#32, 0x018e6083#32, 0x01ce6103#32, 0x02011113#32, 0x002080b3#32, 0x001ebc23#32, 0x020e6083#32, 0x024e6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb023#32, 0x028e6083#32, 0x02ce6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb423#32, 0x030e6083#32, 0x034e6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb823#32, 0x038e6083#32, 0x03ce6103#32, 0x02011113#32, 0x002080b3#32, 0x021ebc23#32, 0x00001e37#32, 0x01ce0e13#32, 0x00003eb7#32, 0x6c0e8e93#32, 0x000e6083#32, 0x004e6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb023#32, 0x008e6083#32, 0x00ce6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb423#32, 0x010e6083#32, 0x014e6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb823#32, 0x018e6083#32, 0x01ce6103#32, 0x02011113#32, 0x002080b3#32, 0x001ebc23#32, 0x020e6083#32, 0x024e6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb023#32, 0x028e6083#32, 0x02ce6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb423#32, 0x030e6083#32, 0x034e6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb823#32, 0x038e6083#32, 0x03ce6103#32, 0x02011113#32, 0x002080b3#32, 0x021ebc23#32, 0x00001e37#32, 0x05ce0e13#32, 0x00003eb7#32, 0x700e8e93#32, 0x000e6083#32, 0x004e6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb023#32, 0x008e6083#32, 0x00ce6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb423#32, 0x010e6083#32, 0x014e6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb823#32, 0x018e6083#32, 0x01ce6103#32, 0x02011113#32, 0x002080b3#32, 0x001ebc23#32, 0x020e6083#32, 0x024e6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb023#32, 0x028e6083#32, 0x02ce6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb423#32, 0x030e6083#32, 0x034e6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb823#32, 0x038e6083#32, 0x03ce6103#32, 0x02011113#32, 0x002080b3#32, 0x021ebc23#32, 0x00001e37#32, 0x09ce0e13#32, 0x00003eb7#32, 0x740e8e93#32, 0x000e6083#32, 0x004e6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb023#32, 0x008e6083#32, 0x00ce6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb423#32, 0x010e6083#32, 0x014e6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb823#32, 0x018e6083#32, 0x01ce6103#32, 0x02011113#32, 0x002080b3#32, 0x001ebc23#32, 0x020e6083#32, 0x024e6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb023#32, 0x028e6083#32, 0x02ce6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb423#32, 0x030e6083#32, 0x034e6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb823#32, 0x038e6083#32, 0x03ce6103#32, 0x02011113#32, 0x002080b3#32, 0x021ebc23#32]
/-- instructions 1706 .. 2085 (pack_30,pack_31,pack_32,pack_33,pack_34,pack_35,pack_36,pack_37,pack_38,pack_39): lui t3, 0x1; addi t3, t3, 220; lui t4, 0x3; addi t4, t4, 1920; lwu ra, 0(t3); lwu sp, 4(t3) ... -/
def seg1706 : List (BitVec 32) := [0x00001e37#32, 0x0dce0e13#32, 0x00003eb7#32, 0x780e8e93#32, 0x000e6083#32, 0x004e6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb023#32, 0x008e6083#32, 0x00ce6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb423#32, 0x010e6083#32, 0x014e6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb823#32, 0x018e6083#32, 0x01ce6103#32, 0x02011113#32, 0x002080b3#32, 0x001ebc23#32, 0x020e6083#32, 0x024e6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb023#32, 0x028e6083#32, 0x02ce6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb423#32, 0x030e6083#32, 0x034e6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb823#32, 0x038e6083#32, 0x03ce6103#32, 0x02011113#32, 0x002080b3#32, 0x021ebc23#32, 0x00001e37#32, 0x11ce0e13#32, 0x00003eb7#32, 0x7c0e8e93#32, 0x000e6083#32, 0x004e6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb023#32, 0x008e6083#32, 0x00ce6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb423#32, 0x010e6083#32, 0x014e6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb823#32, 0x018e6083#32, 0x01ce6103#32, 0x02011113#32, 0x002080b3#32, 0x001ebc23#32, 0x020e6083#32, 0x024e6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb023#32, 0x028e6083#32, 0x02ce6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb423#32, 0x030e6083#32, 0x034e6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb823#32, 0x038e6083#32, 0x03ce6103#32, 0x02011113#32, 0x002080b3#32, 0x021ebc23#32, 0x00001e37#32, 0x15ce0e13#32, 0x00004eb7#32, 0x800e8e93#32, 0x000e6083#32, 0x004e6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb023#32, 0x008e6083#32, 0x00ce6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb423#32, 0x010e6083#32, 0x014e6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb823#32, 0x018e6083#32, 0x01ce6103#32, 0x02011113#32, 0x002080b3#32, 0x001ebc23#32, 0x020e6083#32, 0x024e6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb023#32, 0x028e6083#32, 0x02ce6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb423#32, 0x030e6083#32, 0x034e6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb823#32, 0x038e6083#32, 0x03ce6103#32, 0x02011113#32, 0x002080b3#32, 0x021ebc23#32, 0x00001e37#32, 0x19ce0e13#32, 0x00004eb7#32, 0x840e8e93#32, 0x000e6083#32, 0x004e6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb023#32, 0x008e6083#32, 0x00ce6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb423#32, 0x010e6083#32, 0x014e6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb823#32, 0x018e6083#32, 0x01ce6103#32, 0x02011113#32, 0x002080b3#32, 0x001ebc23#32, 0x020e6083#32, 0x024e6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb023#32, 0x028e6083#32, 0x02ce6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb423#32, 0x030e6083#32, 0x034e6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb823#32, 0x038e6083#32, 0x03ce6103#32, 0x02011113#32, 0x002080b3#32, 0x021ebc23#32, 0x00001e37#32, 0x1dce0e13#32, 0x00004eb7#32, 0x880e8e93#32, 0x000e6083#32, 0x004e6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb023#32, 0x008e6083#32, 0x00ce6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb423#32, 0x010e6083#32, 0x014e6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb823#32, 0x018e6083#32, 0x01ce6103#32, 0x02011113#32, 0x002080b3#32, 0x001ebc23#32, 0x020e6083#32, 0x024e6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb023#32, 0x028e6083#32, 0x02ce6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb423#32, 0x030e6083#32, 0x034e6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb823#32, 0x038e6083#32, 0x03ce6103#32, 0x02011113#32, 0x002080b3#32, 0x021ebc23#32, 0x00001e37#32, 0x21ce0e13#32, 0x00004eb7#32, 0x8c0e8e93#32, 0x000e6083#32, 0x004e6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb023#32, 0x008e6083#32, 0x00ce6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb423#32, 0x010e6083#32, 0x014e6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb823#32, 0x018e6083#32, 0x01ce6103#32, 0x02011113#32, 0x002080b3#32, 0x001ebc23#32, 0x020e6083#32, 0x024e6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb023#32, 0x028e6083#32, 0x02ce6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb423#32, 0x030e6083#32, 0x034e6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb823#32, 0x038e6083#32, 0x03ce6103#32, 0x02011113#32, 0x002080b3#32, 0x021ebc23#32, 0x00001e37#32, 0x25ce0e13#32, 0x00004eb7#32, 0x900e8e93#32, 0x000e6083#32, 0x004e6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb023#32, 0x008e6083#32, 0x00ce6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb423#32, 0x010e6083#32, 0x014e6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb823#32, 0x018e6083#32, 0x01ce6103#32, 0x02011113#32, 0x002080b3#32, 0x001ebc23#32, 0x020e6083#32, 0x024e6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb023#32, 0x028e6083#32, 0x02ce6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb423#32, 0x030e6083#32, 0x034e6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb823#32, 0x038e6083#32, 0x03ce6103#32, 0x02011113#32, 0x002080b3#32, 0x021ebc23#32, 0x00001e37#32, 0x29ce0e13#32, 0x00004eb7#32, 0x940e8e93#32, 0x000e6083#32, 0x004e6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb023#32, 0x008e6083#32, 0x00ce6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb423#32, 0x010e6083#32, 0x014e6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb823#32, 0x018e6083#32, 0x06ce6103#32, 0x02011113#32, 0x002080b3#32, 0x001ebc23#32, 0x074e3083#32, 0x021eb023#32, 0x07ce3083#32, 0x021eb423#32, 0x084e3083#32, 0x021eb823#32, 0x08ce3083#32, 0x021ebc23#32, 0x00001e37#32, 0x330e0e13#32, 0x00004eb7#32, 0x980e8e93#32, 0x000e3083#32, 0x001eb023#32, 0x008e3083#32, 0x001eb423#32, 0x010e3083#32, 0x001eb823#32, 0x018e3083#32, 0x001ebc23#32, 0x020e3083#32, 0x021eb023#32, 0x028e3083#32, 0x021eb423#32, 0x030e3083#32, 0x021eb823#32, 0x038e3083#32, 0x021ebc23#32, 0x00001e37#32, 0x370e0e13#32, 0x00004eb7#32, 0x9c0e8e93#32, 0x000e3083#32, 0x001eb023#32, 0x008e3083#32, 0x001eb423#32, 0x010e3083#32, 0x001eb823#32, 0x018e3083#32, 0x001ebc23#32, 0x020e3083#32, 0x021eb023#32, 0x028e3083#32, 0x021eb423#32, 0x030e3083#32, 0x021eb823#32, 0x038e3083#32, 0x021ebc23#32]
/-- instructions 2086 .. 2297 (pack_40,pack_41,pack_42,pack_43,pack_44,pack_45,pack_46,pack_47,pack_48,pack_49): lui t3, 0x1; addi t3, t3, 944; lui t4, 0x4; addi t4, t4, -1536; ld ra, 0(t3); sd ra, 0(t4) ... -/
def seg2086 : List (BitVec 32) := [0x00001e37#32, 0x3b0e0e13#32, 0x00004eb7#32, 0xa00e8e93#32, 0x000e3083#32, 0x001eb023#32, 0x008e3083#32, 0x001eb423#32, 0x010e3083#32, 0x001eb823#32, 0x018e3083#32, 0x001ebc23#32, 0x020e3083#32, 0x021eb023#32, 0x028e3083#32, 0x021eb423#32, 0x030e3083#32, 0x021eb823#32, 0x038e3083#32, 0x021ebc23#32, 0x00001e37#32, 0x3f0e0e13#32, 0x00004eb7#32, 0xa40e8e93#32, 0x000e3083#32, 0x001eb023#32, 0x008e3083#32, 0x001eb423#32, 0x010e3083#32, 0x001eb823#32, 0x018e3083#32, 0x001ebc23#32, 0x020e3083#32, 0x021eb023#32, 0x028e3083#32, 0x021eb423#32, 0x030e3083#32, 0x021eb823#32, 0x038e3083#32, 0x021ebc23#32, 0x00001e37#32, 0x430e0e13#32, 0x00004eb7#32, 0xa80e8e93#32, 0x000e3083#32, 0x001eb023#32, 0x008e3083#32, 0x001eb423#32, 0x010e3083#32, 0x001eb823#32, 0x018e3083#32, 0x001ebc23#32, 0x020e3083#32, 0x021eb023#32, 0x028e3083#32, 0x021eb423#32, 0x030e3083#32, 0x021eb823#32, 0x038e3083#32, 0x021ebc23#32, 0x00001e37#32, 0x470e0e13#32, 0x00004eb7#32, 0xac0e8e93#32, 0x000e3083#32, 0x001eb023#32, 0x008e3083#32, 0x001eb423#32, 0x010e3083#32, 0x001eb823#32, 0x018e3083#32, 0x001ebc23#32, 0x020e3083#32, 0x021eb023#32, 0x028e3083#32, 0x021eb423#32, 0x030e3083#32, 0x021eb823#32, 0x038e3083#32, 0x021ebc23#32, 0x00001e37#32, 0x4b0e0e13#32, 0x00004eb7#32, 0xb00e8e93#32, 0x000e3083#32, 0x001eb023#32, 0x008e3083#32, 0x001eb423#32, 0x010e3083#32, 0x001eb823#32, 0x018e3083#32, 0x001ebc23#32, 0x020e3083#32, 0x021eb023#32, 0x028e3083#32, 0x021eb423#32, 0x030e3083#32, 0x021eb823#32, 0x038e3083#32, 0x021ebc23#32, 0x00001e37#32, 0x4f0e0e13#32, 0x00004eb7#32, 0xb40e8e93#32, 0x000e3083#32, 0x001eb023#32, 0x008e3083#32, 0x001eb423#32, 0x010e3083#32, 0x001eb823#32, 0x018e3083#32, 0x001ebc23#32, 0x020e3083#32, 0x021eb023#32, 0x028e3083#32, 0x021eb423#32, 0x030e3083#32, 0x021eb823#32, 0x038e3083#32, 0x021ebc23#32, 0x00001e37#32, 0x530e0e13#32, 0x00004eb7#32, 0xb80e8e93#32, 0x000e3083#32, 0x001eb023#32, 0x008e3083#32, 0x001eb423#32, 0x010e3083#32, 0x001eb823#32, 0x018e3083#32, 0x001ebc23#32, 0x020e3083#32, 0x021eb023#32, 0x028e3083#32, 0x021eb423#32, 0x030e3083#32, 0x021eb823#32, 0x038e3083#32, 0x021ebc23#32, 0x00001e37#32, 0x570e0e13#32, 0x00004eb7#32, 0xbc0e8e93#32, 0x000e3083#32, 0x001eb023#32, 0x008e3083#32, 0x001eb423#32, 0x010e3083#32, 0x001eb823#32, 0x018e3083#32, 0x001ebc23#32, 0x020e3083#32, 0x021eb023#32, 0x028e3083#32, 0x021eb423#32, 0x030e3083#32, 0x021eb823#32, 0x038e3083#32, 0x021ebc23#32, 0x00001e37#32, 0x5b0e0e13#32, 0x00004eb7#32, 0xc00e8e93#32, 0x000e3083#32, 0x001eb023#32, 0x008e3083#32, 0x001eb423#32, 0x010e3083#32, 0x001eb823#32, 0x018e3083#32, 0x001ebc23#32, 0x020e3083#32, 0x021eb023#32, 0x028e3083#32, 0x021eb423#32, 0x030e3083#32, 0x021eb823#32, 0x038e3083#32, 0x021ebc23#32, 0x00001e37#32, 0x5f0e0e13#32, 0x00004eb7#32, 0xc40e8e93#32, 0x000e3083#32, 0x001eb023#32, 0x008e3083#32, 0x001eb423#32, 0x010e3083#32, 0x001eb823#32, 0x018e3083#32, 0x001ebc23#32, 0x070e6083#32, 0x078e6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb023#32, 0x07ce6083#32, 0x080e6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb423#32, 0x084e6083#32, 0x088e6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb823#32, 0x08ce6083#32, 0x090e6103#32, 0x02011113#32, 0x002080b3#32, 0x021ebc23#32]
/-- instructions 2298 .. 2737 (pack_50,pack_51,pack_52,pack_53,pack_54,pack_55,pack_56,pack_57,pack_58,pack_59): lui t3, 0x1; addi t3, t3, 1668; lui t4, 0x4; addi t4, t4, -896; lwu ra, 0(t3); lwu sp, 4(t3) ... -/
def seg2298 : List (BitVec 32) := [0x00001e37#32, 0x684e0e13#32, 0x00004eb7#32, 0xc80e8e93#32, 0x000e6083#32, 0x004e6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb023#32, 0x008e6083#32, 0x00ce6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb423#32, 0x010e6083#32, 0x014e6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb823#32, 0x018e6083#32, 0x01ce6103#32, 0x02011113#32, 0x002080b3#32, 0x001ebc23#32, 0x020e6083#32, 0x024e6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb023#32, 0x028e6083#32, 0x02ce6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb423#32, 0x030e6083#32, 0x034e6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb823#32, 0x038e6083#32, 0x03ce6103#32, 0x02011113#32, 0x002080b3#32, 0x021ebc23#32, 0x00001e37#32, 0x6c4e0e13#32, 0x00004eb7#32, 0xcc0e8e93#32, 0x000e6083#32, 0x004e6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb023#32, 0x008e6083#32, 0x00ce6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb423#32, 0x010e6083#32, 0x014e6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb823#32, 0x018e6083#32, 0x01ce6103#32, 0x02011113#32, 0x002080b3#32, 0x001ebc23#32, 0x020e6083#32, 0x024e6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb023#32, 0x028e6083#32, 0x02ce6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb423#32, 0x030e6083#32, 0x034e6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb823#32, 0x038e6083#32, 0x03ce6103#32, 0x02011113#32, 0x002080b3#32, 0x021ebc23#32, 0x00001e37#32, 0x704e0e13#32, 0x00004eb7#32, 0xd00e8e93#32, 0x000e6083#32, 0x004e6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb023#32, 0x008e6083#32, 0x00ce6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb423#32, 0x010e6083#32, 0x014e6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb823#32, 0x018e6083#32, 0x01ce6103#32, 0x02011113#32, 0x002080b3#32, 0x001ebc23#32, 0x020e6083#32, 0x024e6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb023#32, 0x028e6083#32, 0x02ce6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb423#32, 0x030e6083#32, 0x034e6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb823#32, 0x038e6083#32, 0x03ce6103#32, 0x02011113#32, 0x002080b3#32, 0x021ebc23#32, 0x00001e37#32, 0x744e0e13#32, 0x00004eb7#32, 0xd40e8e93#32, 0x000e6083#32, 0x004e6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb023#32, 0x008e6083#32, 0x00ce6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb423#32, 0x010e6083#32, 0x014e6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb823#32, 0x018e6083#32, 0x01ce6103#32, 0x02011113#32, 0x002080b3#32, 0x001ebc23#32, 0x020e6083#32, 0x024e6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb023#32, 0x028e6083#32, 0x02ce6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb423#32, 0x030e6083#32, 0x034e6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb823#32, 0x038e6083#32, 0x03ce6103#32, 0x02011113#32, 0x002080b3#32, 0x021ebc23#32, 0x00001e37#32, 0x784e0e13#32, 0x00004eb7#32, 0xd80e8e93#32, 0x000e6083#32, 0x004e6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb023#32, 0x008e6083#32, 0x00ce6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb423#32, 0x010e6083#32, 0x014e6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb823#32, 0x018e6083#32, 0x01ce6103#32, 0x02011113#32, 0x002080b3#32, 0x001ebc23#32, 0x020e6083#32, 0x024e6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb023#32, 0x028e6083#32, 0x02ce6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb423#32, 0x030e6083#32, 0x034e6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb823#32, 0x038e6083#32, 0x03ce6103#32, 0x02011113#32, 0x002080b3#32, 0x021ebc23#32, 0x00001e37#32, 0x7c4e0e13#32, 0x00004eb7#32, 0xdc0e8e93#32, 0x000e6083#32, 0x004e6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb023#32, 0x008e6083#32, 0x00ce6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb423#32, 0x010e6083#32, 0x014e6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb823#32, 0x018e6083#32, 0x01ce6103#32, 0x02011113#32, 0x002080b3#32, 0x001ebc23#32, 0x020e6083#32, 0x024e6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb023#32, 0x028e6083#32, 0x02ce6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb423#32, 0x030e6083#32, 0x034e6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb823#32, 0x038e6083#32, 0x03ce6103#32, 0x02011113#32, 0x002080b3#32, 0x021ebc23#32, 0x00002e37#32, 0x804e0e13#32, 0x00004eb7#32, 0xe00e8e93#32, 0x000e6083#32, 0x004e6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb023#32, 0x008e6083#32, 0x00ce6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb423#32, 0x010e6083#32, 0x014e6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb823#32, 0x018e6083#32, 0x01ce6103#32, 0x02011113#32, 0x002080b3#32, 0x001ebc23#32, 0x020e6083#32, 0x024e6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb023#32, 0x028e6083#32, 0x02ce6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb423#32, 0x030e6083#32, 0x034e6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb823#32, 0x038e6083#32, 0x03ce6103#32, 0x02011113#32, 0x002080b3#32, 0x021ebc23#32, 0x00002e37#32, 0x844e0e13#32, 0x00004eb7#32, 0xe40e8e93#32, 0x000e6083#32, 0x004e6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb023#32, 0x008e6083#32, 0x00ce6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb423#32, 0x010e6083#32, 0x014e6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb823#32, 0x018e6083#32, 0x01ce6103#32, 0x02011113#32, 0x002080b3#32, 0x001ebc23#32, 0x020e6083#32, 0x024e6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb023#32, 0x028e6083#32, 0x02ce6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb423#32, 0x030e6083#32, 0x034e6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb823#32, 0x038e6083#32, 0x03ce6103#32, 0x02011113#32, 0x002080b3#32, 0x021ebc23#32, 0x00002e37#32, 0x884e0e13#32, 0x00004eb7#32, 0xe80e8e93#32, 0x000e6083#32, 0x004e6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb023#32, 0x008e6083#32, 0x00ce6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb423#32, 0x010e6083#32, 0x014e6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb823#32, 0x018e6083#32, 0x01ce6103#32, 0x02011113#32, 0x002080b3#32, 0x001ebc23#32, 0x020e6083#32, 0x024e6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb023#32, 0x028e6083#32, 0x02ce6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb423#32, 0x030e6083#32, 0x034e6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb823#32, 0x038e6083#32, 0x03ce6103#32, 0x02011113#32, 0x002080b3#32, 0x021ebc23#32, 0x00002e37#32, 0x8c4e0e13#32, 0x00004eb7#32, 0xec0e8e93#32, 0x000e6083#32, 0x004e6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb023#32, 0x008e6083#32, 0x00ce6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb423#32, 0x010e6083#32, 0x014e6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb823#32, 0x018e6083#32, 0x01ce6103#32, 0x02011113#32, 0x002080b3#32, 0x001ebc23#32, 0x020e6083#32, 0x024e6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb023#32, 0x028e6083#32, 0x02ce6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb423#32, 0x030e6083#32, 0x034e6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb823#32, 0x038e6083#32, 0x03ce6103#32, 0x02011113#32, 0x002080b3#32, 0x021ebc23#32]
/-- instructions 2738 .. 2797 (pack_60,pack_61): lui t3, 0x2; addi t3, t3, -1788; lui t4, 0x4; addi t4, t4, -256; lwu ra, 0(t3); lwu sp, 4(t3) ... -/
def seg2738 : List (BitVec 32) := [0x00002e37#32, 0x904e0e13#32, 0x00004eb7#32, 0xf00e8e93#32, 0x000e6083#32, 0x004e6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb023#32, 0x008e6083#32, 0x00ce6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb423#32, 0x010e6083#32, 0x014e6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb823#32, 0x018e6083#32, 0x01ce6103#32, 0x02011113#32, 0x002080b3#32, 0x001ebc23#32, 0x020e6083#32, 0x024e6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb023#32, 0x028e6083#32, 0x02ce6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb423#32, 0x030e6083#32, 0x034e6103#32, 0x02011113#32, 0x002080b3#32, 0x021eb823#32, 0x038e6083#32, 0x03ce6103#32, 0x02011113#32, 0x002080b3#32, 0x021ebc23#32, 0x00002e37#32, 0x944e0e13#32, 0x00004eb7#32, 0xf40e8e93#32, 0x000e6083#32, 0x004e6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb023#32, 0x008e6083#32, 0x00ce6103#32, 0x02011113#32, 0x002080b3#32, 0x001eb423#32, 0x010e6083#32, 0x001eb823#32]
/-- instructions 2798 .. 2800 (success): addi t0, x0, 1; addi a0, x0, 0; ecall  -/
def seg2798 : List (BitVec 32) := [0x00100293#32, 0x00000513#32, 0x00002337#32]

/-- Segment table of the sign image. -/
def L : Rv.Layout := [(0, seg0), (55, seg55), (57, seg57), (59, seg59), (61, seg61), (63, seg63), (65, seg65), (70, seg70), (78, seg78), (82, seg82), (84, seg84), (87, seg87), (90, seg90), (156, seg156), (164, seg164), (166, seg166), (172, seg172), (179, seg179), (183, seg183), (188, seg188), (191, seg191), (193, seg193), (210, seg210), (227, seg227), (229, seg229), (232, seg232), (241, seg241), (252, seg252), (272, seg272), (274, seg274), (277, seg277), (278, seg278), (285, seg285), (287, seg287), (302, seg302), (307, seg307), (311, seg311), (332, seg332), (333, seg333), (335, seg335), (338, seg338), (465, seg465), (479, seg479), (486, seg486), (488, seg488), (494, seg494), (506, seg506), (507, seg507), (513, seg513), (521, seg521), (523, seg523), (524, seg524), (530, seg530), (532, seg532), (541, seg541), (546, seg546), (548, seg548), (549, seg549), (566, seg566), (583, seg583), (585, seg585), (587, seg587), (594, seg594), (603, seg603), (605, seg605), (611, seg611), (622, seg622), (623, seg623), (630, seg630), (633, seg633), (642, seg642), (646, seg646), (658, seg658), (675, seg675), (1114, seg1114), (1395, seg1395), (1706, seg1706), (2086, seg2086), (2298, seg2298), (2738, seg2738), (2798, seg2798), (2801, SigGolfCandidate.Radix27Images.signCode.drop 2801)]

theorem layout_ok : layoutOk 0 L = true := by decide +kernel

/-- The sign image. -/
abbrev image : Image := SigGolfCandidate.Radix27Images.signImage


set_option maxHeartbeats 4000000 in
theorem code_eq : image.code = layoutCode L := by decide +kernel

theorem codeAt_0 : CodeAt image (pcOf 0) seg0 :=
  codeAt_layout code_eq layout_ok (i := 0) (by kernel_rfl) (by decide)
theorem codeAt_55 : CodeAt image (pcOf 55) seg55 :=
  codeAt_layout code_eq layout_ok (i := 1) (by kernel_rfl) (by decide)
theorem codeAt_57 : CodeAt image (pcOf 57) seg57 :=
  codeAt_layout code_eq layout_ok (i := 2) (by kernel_rfl) (by decide)
theorem codeAt_59 : CodeAt image (pcOf 59) seg59 :=
  codeAt_layout code_eq layout_ok (i := 3) (by kernel_rfl) (by decide)
theorem codeAt_61 : CodeAt image (pcOf 61) seg61 :=
  codeAt_layout code_eq layout_ok (i := 4) (by kernel_rfl) (by decide)
theorem codeAt_63 : CodeAt image (pcOf 63) seg63 :=
  codeAt_layout code_eq layout_ok (i := 5) (by kernel_rfl) (by decide)
theorem codeAt_65 : CodeAt image (pcOf 65) seg65 :=
  codeAt_layout code_eq layout_ok (i := 6) (by kernel_rfl) (by decide)
theorem codeAt_70 : CodeAt image (pcOf 70) seg70 :=
  codeAt_layout code_eq layout_ok (i := 7) (by kernel_rfl) (by decide)
theorem codeAt_78 : CodeAt image (pcOf 78) seg78 :=
  codeAt_layout code_eq layout_ok (i := 8) (by kernel_rfl) (by decide)
theorem codeAt_82 : CodeAt image (pcOf 82) seg82 :=
  codeAt_layout code_eq layout_ok (i := 9) (by kernel_rfl) (by decide)
theorem codeAt_84 : CodeAt image (pcOf 84) seg84 :=
  codeAt_layout code_eq layout_ok (i := 10) (by kernel_rfl) (by decide)
theorem codeAt_87 : CodeAt image (pcOf 87) seg87 :=
  codeAt_layout code_eq layout_ok (i := 11) (by kernel_rfl) (by decide)
theorem codeAt_90 : CodeAt image (pcOf 90) seg90 :=
  codeAt_layout code_eq layout_ok (i := 12) (by kernel_rfl) (by decide)
theorem codeAt_156 : CodeAt image (pcOf 156) seg156 :=
  codeAt_layout code_eq layout_ok (i := 13) (by kernel_rfl) (by decide)
theorem codeAt_164 : CodeAt image (pcOf 164) seg164 :=
  codeAt_layout code_eq layout_ok (i := 14) (by kernel_rfl) (by decide)
theorem codeAt_166 : CodeAt image (pcOf 166) seg166 :=
  codeAt_layout code_eq layout_ok (i := 15) (by kernel_rfl) (by decide)
theorem codeAt_172 : CodeAt image (pcOf 172) seg172 :=
  codeAt_layout code_eq layout_ok (i := 16) (by kernel_rfl) (by decide)
theorem codeAt_179 : CodeAt image (pcOf 179) seg179 :=
  codeAt_layout code_eq layout_ok (i := 17) (by kernel_rfl) (by decide)
theorem codeAt_183 : CodeAt image (pcOf 183) seg183 :=
  codeAt_layout code_eq layout_ok (i := 18) (by kernel_rfl) (by decide)
theorem codeAt_188 : CodeAt image (pcOf 188) seg188 :=
  codeAt_layout code_eq layout_ok (i := 19) (by kernel_rfl) (by decide)
theorem codeAt_191 : CodeAt image (pcOf 191) seg191 :=
  codeAt_layout code_eq layout_ok (i := 20) (by kernel_rfl) (by decide)
theorem codeAt_193 : CodeAt image (pcOf 193) seg193 :=
  codeAt_layout code_eq layout_ok (i := 21) (by kernel_rfl) (by decide)
theorem codeAt_210 : CodeAt image (pcOf 210) seg210 :=
  codeAt_layout code_eq layout_ok (i := 22) (by kernel_rfl) (by decide)
theorem codeAt_227 : CodeAt image (pcOf 227) seg227 :=
  codeAt_layout code_eq layout_ok (i := 23) (by kernel_rfl) (by decide)
theorem codeAt_229 : CodeAt image (pcOf 229) seg229 :=
  codeAt_layout code_eq layout_ok (i := 24) (by kernel_rfl) (by decide)
theorem codeAt_232 : CodeAt image (pcOf 232) seg232 :=
  codeAt_layout code_eq layout_ok (i := 25) (by kernel_rfl) (by decide)
theorem codeAt_241 : CodeAt image (pcOf 241) seg241 :=
  codeAt_layout code_eq layout_ok (i := 26) (by kernel_rfl) (by decide)
theorem codeAt_252 : CodeAt image (pcOf 252) seg252 :=
  codeAt_layout code_eq layout_ok (i := 27) (by kernel_rfl) (by decide)
theorem codeAt_272 : CodeAt image (pcOf 272) seg272 :=
  codeAt_layout code_eq layout_ok (i := 28) (by kernel_rfl) (by decide)
theorem codeAt_274 : CodeAt image (pcOf 274) seg274 :=
  codeAt_layout code_eq layout_ok (i := 29) (by kernel_rfl) (by decide)
theorem codeAt_277 : CodeAt image (pcOf 277) seg277 :=
  codeAt_layout code_eq layout_ok (i := 30) (by kernel_rfl) (by decide)
theorem codeAt_278 : CodeAt image (pcOf 278) seg278 :=
  codeAt_layout code_eq layout_ok (i := 31) (by kernel_rfl) (by decide)
theorem codeAt_285 : CodeAt image (pcOf 285) seg285 :=
  codeAt_layout code_eq layout_ok (i := 32) (by kernel_rfl) (by decide)
theorem codeAt_287 : CodeAt image (pcOf 287) seg287 :=
  codeAt_layout code_eq layout_ok (i := 33) (by kernel_rfl) (by decide)
theorem codeAt_302 : CodeAt image (pcOf 302) seg302 :=
  codeAt_layout code_eq layout_ok (i := 34) (by kernel_rfl) (by decide)
theorem codeAt_307 : CodeAt image (pcOf 307) seg307 :=
  codeAt_layout code_eq layout_ok (i := 35) (by kernel_rfl) (by decide)
theorem codeAt_311 : CodeAt image (pcOf 311) seg311 :=
  codeAt_layout code_eq layout_ok (i := 36) (by kernel_rfl) (by decide)
theorem codeAt_332 : CodeAt image (pcOf 332) seg332 :=
  codeAt_layout code_eq layout_ok (i := 37) (by kernel_rfl) (by decide)
theorem codeAt_333 : CodeAt image (pcOf 333) seg333 :=
  codeAt_layout code_eq layout_ok (i := 38) (by kernel_rfl) (by decide)
theorem codeAt_335 : CodeAt image (pcOf 335) seg335 :=
  codeAt_layout code_eq layout_ok (i := 39) (by kernel_rfl) (by decide)
theorem codeAt_338 : CodeAt image (pcOf 338) seg338 :=
  codeAt_layout code_eq layout_ok (i := 40) (by kernel_rfl) (by decide)
theorem codeAt_465 : CodeAt image (pcOf 465) seg465 :=
  codeAt_layout code_eq layout_ok (i := 41) (by kernel_rfl) (by decide)
theorem codeAt_479 : CodeAt image (pcOf 479) seg479 :=
  codeAt_layout code_eq layout_ok (i := 42) (by kernel_rfl) (by decide)
theorem codeAt_486 : CodeAt image (pcOf 486) seg486 :=
  codeAt_layout code_eq layout_ok (i := 43) (by kernel_rfl) (by decide)
theorem codeAt_488 : CodeAt image (pcOf 488) seg488 :=
  codeAt_layout code_eq layout_ok (i := 44) (by kernel_rfl) (by decide)
theorem codeAt_494 : CodeAt image (pcOf 494) seg494 :=
  codeAt_layout code_eq layout_ok (i := 45) (by kernel_rfl) (by decide)
theorem codeAt_506 : CodeAt image (pcOf 506) seg506 :=
  codeAt_layout code_eq layout_ok (i := 46) (by kernel_rfl) (by decide)
theorem codeAt_507 : CodeAt image (pcOf 507) seg507 :=
  codeAt_layout code_eq layout_ok (i := 47) (by kernel_rfl) (by decide)
theorem codeAt_513 : CodeAt image (pcOf 513) seg513 :=
  codeAt_layout code_eq layout_ok (i := 48) (by kernel_rfl) (by decide)
theorem codeAt_521 : CodeAt image (pcOf 521) seg521 :=
  codeAt_layout code_eq layout_ok (i := 49) (by kernel_rfl) (by decide)
theorem codeAt_523 : CodeAt image (pcOf 523) seg523 :=
  codeAt_layout code_eq layout_ok (i := 50) (by kernel_rfl) (by decide)
theorem codeAt_524 : CodeAt image (pcOf 524) seg524 :=
  codeAt_layout code_eq layout_ok (i := 51) (by kernel_rfl) (by decide)
theorem codeAt_530 : CodeAt image (pcOf 530) seg530 :=
  codeAt_layout code_eq layout_ok (i := 52) (by kernel_rfl) (by decide)
theorem codeAt_532 : CodeAt image (pcOf 532) seg532 :=
  codeAt_layout code_eq layout_ok (i := 53) (by kernel_rfl) (by decide)
theorem codeAt_541 : CodeAt image (pcOf 541) seg541 :=
  codeAt_layout code_eq layout_ok (i := 54) (by kernel_rfl) (by decide)
theorem codeAt_546 : CodeAt image (pcOf 546) seg546 :=
  codeAt_layout code_eq layout_ok (i := 55) (by kernel_rfl) (by decide)
theorem codeAt_548 : CodeAt image (pcOf 548) seg548 :=
  codeAt_layout code_eq layout_ok (i := 56) (by kernel_rfl) (by decide)
theorem codeAt_549 : CodeAt image (pcOf 549) seg549 :=
  codeAt_layout code_eq layout_ok (i := 57) (by kernel_rfl) (by decide)
theorem codeAt_566 : CodeAt image (pcOf 566) seg566 :=
  codeAt_layout code_eq layout_ok (i := 58) (by kernel_rfl) (by decide)
theorem codeAt_583 : CodeAt image (pcOf 583) seg583 :=
  codeAt_layout code_eq layout_ok (i := 59) (by kernel_rfl) (by decide)
theorem codeAt_585 : CodeAt image (pcOf 585) seg585 :=
  codeAt_layout code_eq layout_ok (i := 60) (by kernel_rfl) (by decide)
theorem codeAt_587 : CodeAt image (pcOf 587) seg587 :=
  codeAt_layout code_eq layout_ok (i := 61) (by kernel_rfl) (by decide)
theorem codeAt_594 : CodeAt image (pcOf 594) seg594 :=
  codeAt_layout code_eq layout_ok (i := 62) (by kernel_rfl) (by decide)
theorem codeAt_603 : CodeAt image (pcOf 603) seg603 :=
  codeAt_layout code_eq layout_ok (i := 63) (by kernel_rfl) (by decide)
theorem codeAt_605 : CodeAt image (pcOf 605) seg605 :=
  codeAt_layout code_eq layout_ok (i := 64) (by kernel_rfl) (by decide)
theorem codeAt_611 : CodeAt image (pcOf 611) seg611 :=
  codeAt_layout code_eq layout_ok (i := 65) (by kernel_rfl) (by decide)
theorem codeAt_622 : CodeAt image (pcOf 622) seg622 :=
  codeAt_layout code_eq layout_ok (i := 66) (by kernel_rfl) (by decide)
theorem codeAt_623 : CodeAt image (pcOf 623) seg623 :=
  codeAt_layout code_eq layout_ok (i := 67) (by kernel_rfl) (by decide)
theorem codeAt_630 : CodeAt image (pcOf 630) seg630 :=
  codeAt_layout code_eq layout_ok (i := 68) (by kernel_rfl) (by decide)
theorem codeAt_633 : CodeAt image (pcOf 633) seg633 :=
  codeAt_layout code_eq layout_ok (i := 69) (by kernel_rfl) (by decide)
theorem codeAt_642 : CodeAt image (pcOf 642) seg642 :=
  codeAt_layout code_eq layout_ok (i := 70) (by kernel_rfl) (by decide)
theorem codeAt_646 : CodeAt image (pcOf 646) seg646 :=
  codeAt_layout code_eq layout_ok (i := 71) (by kernel_rfl) (by decide)
theorem codeAt_658 : CodeAt image (pcOf 658) seg658 :=
  codeAt_layout code_eq layout_ok (i := 72) (by kernel_rfl) (by decide)
theorem codeAt_675 : CodeAt image (pcOf 675) seg675 :=
  codeAt_layout code_eq layout_ok (i := 73) (by kernel_rfl) (by decide)
theorem codeAt_1114 : CodeAt image (pcOf 1114) seg1114 :=
  codeAt_layout code_eq layout_ok (i := 74) (by kernel_rfl) (by decide)
theorem codeAt_1395 : CodeAt image (pcOf 1395) seg1395 :=
  codeAt_layout code_eq layout_ok (i := 75) (by kernel_rfl) (by decide)
theorem codeAt_1706 : CodeAt image (pcOf 1706) seg1706 :=
  codeAt_layout code_eq layout_ok (i := 76) (by kernel_rfl) (by decide)
theorem codeAt_2086 : CodeAt image (pcOf 2086) seg2086 :=
  codeAt_layout code_eq layout_ok (i := 77) (by kernel_rfl) (by decide)
theorem codeAt_2298 : CodeAt image (pcOf 2298) seg2298 :=
  codeAt_layout code_eq layout_ok (i := 78) (by kernel_rfl) (by decide)
theorem codeAt_2738 : CodeAt image (pcOf 2738) seg2738 :=
  codeAt_layout code_eq layout_ok (i := 79) (by kernel_rfl) (by decide)
theorem codeAt_2798 : CodeAt image (pcOf 2798) seg2798 :=
  codeAt_layout code_eq layout_ok (i := 80) (by kernel_rfl) (by decide)

end SigGolfCandidate.Radix27Sign



end


section -- SignClone13.Blocks

/-! ### cloned Blocks -/
-- Generated by SigGolfCandidate/Sign/gen_code.py. Do not edit.

namespace SigGolfCandidate.Radix27Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv

/-! Symbolic blocks of the sign program (before the pack). -/

sym_block blk0 := symRun { noAlias := true } seg0 (pcOf 0) 56
sym_block blk55 := symRun { noAlias := true } seg55 (pcOf 55) 3
sym_block blk57 := symRun { noAlias := true } seg57 (pcOf 57) 3
sym_block blk59 := symRun { noAlias := true } seg59 (pcOf 59) 3
sym_block blk61 := symRun { noAlias := true } seg61 (pcOf 61) 3
sym_block blk63 := symRun { noAlias := true } seg63 (pcOf 63) 3
sym_block blk65 := symRun { noAlias := true } seg65 (pcOf 65) 6
sym_block blk70 := symRun { noAlias := true } seg70 (pcOf 70) 9
sym_block blk78 := symRun { noAlias := true } seg78 (pcOf 78) 5
sym_block blk82 := symRun { noAlias := true } seg82 (pcOf 82) 3
sym_block blk84 := symRun { noAlias := true } seg84 (pcOf 84) 4
sym_block blk87 := symRun { noAlias := true } seg87 (pcOf 87) 4
sym_block blk90 := symRun { noAlias := true } seg90 (pcOf 90) 67
sym_block blk156 := symRun { noAlias := true } seg156 (pcOf 156) 9
sym_block blk164 := symRun { noAlias := true } seg164 (pcOf 164) 3
sym_block blk166 := symRun { noAlias := true } seg166 (pcOf 166) 7
sym_block blk172 := symRun { noAlias := true } seg172 (pcOf 172) 8
sym_block blk179 := symRun { noAlias := true } seg179 (pcOf 179) 5
sym_block blk183 := symRun { noAlias := true } seg183 (pcOf 183) 6
sym_block blk188 := symRun { noAlias := true } seg188 (pcOf 188) 4
sym_block blk191 := symRun { noAlias := true } seg191 (pcOf 191) 3
sym_block blk193 := symRun { noAlias := true } seg193 (pcOf 193) 18
sym_block blk210 := symRun { noAlias := true } seg210 (pcOf 210) 18
sym_block blk227 := symRun { noAlias := true } seg227 (pcOf 227) 3
sym_block blk229 := symRun { noAlias := true } seg229 (pcOf 229) 4
sym_block blk232 := symRun { noAlias := true } seg232 (pcOf 232) 10
sym_block blk241 := symRun { noAlias := true } seg241 (pcOf 241) 12
sym_block blk252 := symRun { noAlias := true } seg252 (pcOf 252) 21
sym_block blk272 := symRun { noAlias := true } seg272 (pcOf 272) 3
sym_block blk274 := symRun { noAlias := true } seg274 (pcOf 274) 4
sym_block blk277 := symRun { noAlias := true } seg277 (pcOf 277) 2
sym_block blk278 := symRun { noAlias := true } seg278 (pcOf 278) 8
sym_block blk285 := symRun { noAlias := true } seg285 (pcOf 285) 3
sym_block blk287 := symRun { noAlias := true } seg287 (pcOf 287) 16
sym_block blk302 := symRun { noAlias := true } seg302 (pcOf 302) 6
sym_block blk307 := symRun { noAlias := true } seg307 (pcOf 307) 5
sym_block blk311 := symRun { noAlias := true } seg311 (pcOf 311) 22
sym_block blk332 := symRun { noAlias := true } seg332 (pcOf 332) 2
sym_block blk333 := symRun { noAlias := true } seg333 (pcOf 333) 3
sym_block blk335 := symRun { noAlias := true } seg335 (pcOf 335) 4
sym_block blk338 := symRun { noAlias := true } seg338 (pcOf 338) 128
sym_block blk465 := symRun { noAlias := true } seg465 (pcOf 465) 15
sym_block blk479 := symRun { noAlias := true } seg479 (pcOf 479) 8
sym_block blk486 := symRun { noAlias := true } seg486 (pcOf 486) 3
sym_block blk488 := symRun { noAlias := true } seg488 (pcOf 488) 7
sym_block blk494 := symRun { noAlias := true } seg494 (pcOf 494) 13
sym_block blk506 := symRun { noAlias := true } seg506 (pcOf 506) 2
sym_block blk507 := symRun { noAlias := true } seg507 (pcOf 507) 7
sym_block blk513 := symRun { noAlias := true } seg513 (pcOf 513) 9
sym_block blk521 := symRun { noAlias := true } seg521 (pcOf 521) 3
sym_block blk523 := symRun { noAlias := true } seg523 (pcOf 523) 2
sym_block blk524 := symRun { noAlias := true } seg524 (pcOf 524) 7
sym_block blk530 := symRun { noAlias := true } seg530 (pcOf 530) 3
sym_block blk532 := symRun { noAlias := true } seg532 (pcOf 532) 10
sym_block blk541 := symRun { noAlias := true } seg541 (pcOf 541) 6
sym_block blk546 := symRun { noAlias := true } seg546 (pcOf 546) 3
sym_block blk548 := symRun { noAlias := true } seg548 (pcOf 548) 2
sym_block blk549 := symRun { noAlias := true } seg549 (pcOf 549) 18
sym_block blk566 := symRun { noAlias := true } seg566 (pcOf 566) 18
sym_block blk583 := symRun { noAlias := true } seg583 (pcOf 583) 3
sym_block blk585 := symRun { noAlias := true } seg585 (pcOf 585) 3
sym_block blk587 := symRun { noAlias := true } seg587 (pcOf 587) 8
sym_block blk594 := symRun { noAlias := true } seg594 (pcOf 594) 10
sym_block blk603 := symRun { noAlias := true } seg603 (pcOf 603) 3
sym_block blk605 := symRun { noAlias := true } seg605 (pcOf 605) 7
sym_block blk611 := symRun { noAlias := true } seg611 (pcOf 611) 12
sym_block blk622 := symRun { noAlias := true } seg622 (pcOf 622) 2
sym_block blk623 := symRun { noAlias := true } seg623 (pcOf 623) 8
sym_block blk630 := symRun { noAlias := true } seg630 (pcOf 630) 4
sym_block blk633 := symRun { noAlias := true } seg633 (pcOf 633) 10
sym_block blk642 := symRun { noAlias := true } seg642 (pcOf 642) 5
sym_block blk646 := symRun { noAlias := true } seg646 (pcOf 646) 13
sym_block blk658 := symRun { noAlias := true } seg658 (pcOf 658) 18

end SigGolfCandidate.Radix27Sign



end


section -- SignClone13.Inv

/-! ### cloned Inv -/

/-!
# Frames: memory and registers that a segment leaves unchanged

* `Frame s t W` : every numeric address outside the write set `W` has the same dword in `t` as
  in `s` (`Frame.refl/.trans/.mono`, `Frame.readWords`, `frame_writeHash`, `frame_toState`).
* `RegsEq s t l` : registers outside `l` are unchanged.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace SigGolfCandidate.Radix27Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

def Frame (s t : MachineState) (W : Nat → Prop) : Prop :=
  ∀ a, a < 2 ^ 64 → ¬ W a → t.getMem (BitVec.ofNat 64 a) = s.getMem (BitVec.ofNat 64 a)

theorem Frame.refl (s : MachineState) (W : Nat → Prop) : Frame s s W := fun _ _ _ => rfl

theorem Frame.trans {s t u : MachineState} {W₁ W₂ : Nat → Prop} (h₁ : Frame s t W₁)
    (h₂ : Frame t u W₂) : Frame s u (fun a => W₁ a ∨ W₂ a) := by
  intro a ha hW
  rw [h₂ a ha (fun h => hW (Or.inr h)), h₁ a ha (fun h => hW (Or.inl h))]

theorem Frame.mono {s t : MachineState} {W W' : Nat → Prop} (h : Frame s t W)
    (hW : ∀ a, W a → W' a) : Frame s t W' :=
  fun a ha hna => h a ha (fun h' => hna (hW a h'))

theorem Frame.trans' {s t u : MachineState} {W₁ W₂ W : Nat → Prop} (h₁ : Frame s t W₁)
    (h₂ : Frame t u W₂) (hW : ∀ a, W₁ a ∨ W₂ a → W a) : Frame s u W :=
  (h₁.trans h₂).mono hW

theorem Frame.getMem {s t : MachineState} {W : Nat → Prop} (h : Frame s t W) {a : Nat}
    (ha : a < 2 ^ 64) (hW : ¬ W a) : t.getMem (BitVec.ofNat 64 a) = s.getMem (BitVec.ofNat 64 a) :=
  h a ha hW

theorem Frame.readWords {s t : MachineState} {W : Nat → Prop} (h : Frame s t W) (a n : Nat)
    (ha : a + 8 * n < 2 ^ 64) (hW : ∀ i < n, ¬ W (a + 8 * i)) :
    t.readWords (BitVec.ofNat 64 a) n = s.readWords (BitVec.ofNat 64 a) n :=
  readWords_congr s t a n (fun i hi => h _ (by omega) (hW i hi))

theorem frame_writeHash (s : MachineState) (ans : BitVec 256) (d : Nat)
    (hd : s.getReg .x12 = BitVec.ofNat 64 d) (hd' : d + 32 < 2 ^ 64) :
    Frame s (writeHash s ans) (fun a => d ≤ a ∧ a < d + 32) := by
  intro a ha hW
  exact writeHash_getMem_frame s ans d a hd hd' ha (by omega)

/-- Frame of a block result from a proof that no written key equals an address outside `W`. -/
theorem frame_toState (r : Result) (s : MachineState) (W : Nat → Prop)
    (h : ∀ a, a < 2 ^ 64 → ¬ W a → ∀ p ∈ r.st.mem, BitVec.ofNat 64 a ≠ p.1.eval s) :
    Frame s (r.toState s) W := by
  intro a ha hW
  rw [Result.toState_getMem]
  exact memEval_frame s r.st.mem _ (h a ha hW)

def RegsEq (s t : MachineState) (l : List Reg) : Prop := ∀ r, r ∉ l → t.getReg r = s.getReg r

theorem RegsEq.refl (s : MachineState) (l : List Reg) : RegsEq s s l := fun _ _ => rfl

theorem RegsEq.trans {s t u : MachineState} {l₁ l₂ : List Reg} (h₁ : RegsEq s t l₁)
    (h₂ : RegsEq t u l₂) : RegsEq s u (l₁ ++ l₂) := by
  intro r hr
  rw [h₂ r (fun h => hr (List.mem_append_right _ h)), h₁ r (fun h => hr (List.mem_append_left _ h))]

theorem RegsEq.mono {s t : MachineState} {l l' : List Reg} (h : RegsEq s t l) (hl : ∀ r ∈ l, r ∈ l') :
    RegsEq s t l' := fun r hr => h r (fun h' => hr (hl r h'))

theorem RegsEq.trans' {s t u : MachineState} {l₁ l₂ l : List Reg} (h₁ : RegsEq s t l₁)
    (h₂ : RegsEq t u l₂) (hl : ∀ r, r ∈ l₁ ∨ r ∈ l₂ → r ∈ l) : RegsEq s u l :=
  (h₁.trans h₂).mono (fun r hr => hl r (List.mem_append.mp hr))

theorem RegsEq.get {s t : MachineState} {l : List Reg} (h : RegsEq s t l) (r : Reg)
    (hr : r ∉ l := by decide) : t.getReg r = s.getReg r := h r hr

theorem regsEq_writeHash (s : MachineState) (ans : BitVec 256) (l : List Reg) :
    RegsEq s (writeHash s ans) l := fun r _ => writeHash_getReg s ans r

/-- Registers of a block result: all registers whose symbolic value is `.reg r` are unchanged. -/
theorem regsEq_toState (r : Result) (s : MachineState) (l : List Reg)
    (h : ∀ x : Reg, x ∉ l → (r.st.regs.get x).eval s = s.getReg x) : RegsEq s (r.toState s) l := by
  intro x hx
  rw [Result.toState_getReg]
  exact h x hx

theorem getReg_x0 (s : MachineState) : s.getReg .x0 = 0 := rfl

/-! ## Arrays of 16-byte values -/

/-- `vs[i]` is stored at `B + 16 i`. -/
def Slots (t : MachineState) (B : Nat) (vs : List Val) : Prop :=
  ∀ i (hi : i < vs.length), t.readWords (BitVec.ofNat 64 (B + 16 * i)) 2 = wordsOf vs[i]

theorem Slots.nil (t : MachineState) (B : Nat) : Slots t B [] := fun i hi => by simp at hi

theorem Slots.snoc {t : MachineState} {B : Nat} {vs : List Val} {v : Val} (h : Slots t B vs)
    (hv : t.readWords (BitVec.ofNat 64 (B + 16 * vs.length)) 2 = wordsOf v) : Slots t B (vs ++ [v]) := by
  intro i hi
  simp only [List.length_append, List.length_singleton] at hi
  by_cases h' : i < vs.length
  · rw [List.getElem_append_left h']; exact h i h'
  · have : i = vs.length := by omega
    subst this
    rw [List.getElem_append_right (le_refl _)]; simpa using hv

theorem Slots.frame {s t : MachineState} {W : Nat → Prop} {B : Nat} {vs : List Val}
    (h : Slots s B vs) (hf : Frame s t W) (hB : B + 16 * vs.length + 16 < 2 ^ 64)
    (hW : ∀ i < vs.length, ¬ W (B + 16 * i) ∧ ¬ W (B + 16 * i + 8)) : Slots t B vs := by
  intro i hi
  rw [hf.readWords _ _ (by omega) (by
    intro j hj
    have := hW i hi
    interval_cases j
    · simpa using this.1
    · simpa using this.2)]
  exact h i hi

theorem Slots.getD {t : MachineState} {B : Nat} {vs : List Val} (h : Slots t B vs) (i : Nat)
    (hi : i < vs.length) :
    t.readWords (BitVec.ofNat 64 (B + 16 * i)) 2 = wordsOf (vs.getD i []) := by
  rw [h i hi]; simp [List.getD, List.getElem?_eq_getElem hi]

theorem Slots.append {t : MachineState} {B : Nat} {l1 l2 : List Val} (h1 : Slots t B l1)
    (h2 : Slots t (B + 16 * l1.length) l2) : Slots t B (l1 ++ l2) := by
  intro i hi
  by_cases h : i < l1.length
  · rw [List.getElem_append_left h]; exact h1 i h
  · rw [List.getElem_append_right (by omega)]
    have := h2 (i - l1.length) (by simp at hi; omega)
    rw [show B + 16 * l1.length + 16 * (i - l1.length) = B + 16 * i by omega] at this
    exact this

theorem Slots.cons {t : MachineState} {B : Nat} {v : Val} {vs : List Val}
    (h1 : t.readWords (BitVec.ofNat 64 B) 2 = wordsOf v) (h2 : Slots t (B + 16) vs) :
    Slots t B (v :: vs) := by
  intro i hi
  cases i with
  | zero => simpa using h1
  | succ i =>
    have := h2 i (by simpa using hi)
    rw [show B + 16 * (i + 1) = B + 16 + 16 * i by ring]; simpa using this

end SigGolfCandidate.Radix27Sign



end


section -- SignClone13.Digest

/-! ### cloned Digest -/

/-!
# `sign`, phase 1: the digest search (`dig_loop`, instructions 27 .. 45)

`digLoop_sim` : from `dig_loop` with counter `a`, the machine refines `searchDigest S m a (2^20 - a)`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace SigGolfCandidate.Radix27Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

/-- Facts about the buffers used by the digest search (at the start of the loop). -/
structure DigMem (S mm : List Byte) (u : MachineState) : Prop where
  rbS : u.readWords (BitVec.ofNat 64 0x640) 4 = wordsOf S
  rbM : u.readWords (BitVec.ofNat 64 0x660) 4 = wordsOf mm
  rbZ : u.readWords (BitVec.ofNat 64 0x680) 4 = [0, 0, 0, 0]
  rbP : u.readWords (BitVec.ofNat 64 0x628) 3 = [0, 0, 0]
  rb0 : lo32 (u.getMem (BitVec.ofNat 64 0x620)) = BitVec.ofNat 32 0x701
  db0 : u.readWords (BitVec.ofNat 64 0x20) 2 = [twWord0 12 0 0 0, 0]
  dbM : u.readWords (BitVec.ofNat 64 0x40) 4 = wordsOf mm

/-- Addresses written by the digest search. -/
def digW (a : Nat) : Prop := a = 0x620 ∨ (0x30 ≤ a ∧ a < 0x40) ∨ (0x140 ≤ a ∧ a < 0x180)

def digRegs : List Reg := [.x1, .x2, .x3, .x6, .x10, .x11, .x12]

/-- Loop invariant at `dig_loop` with counter `a`. -/
def DigInv (u : MachineState) (a : Nat) (t : MachineState) : Prop :=
  t.pc = pcOf 65 ∧ t.getReg .x6 = BitVec.ofNat 64 a ∧ a < 2 ^ 20 ∧ RegsEq u t digRegs ∧
    Frame u t digW ∧ lo32 (t.getMem (BitVec.ofNat 64 0x620)) = lo32 (u.getMem (BitVec.ofNat 64 0x620))

/-- Result of the digest search. -/
def DigPost (u : MachineState) : Option (Val × Nat) → MachineState → Prop
  | none, t => t.pc = pcOf 86 ∧ t.getReg .x5 = 1 ∧ t.getReg .x10 = 1
  | some (rho, N), t => t.pc = pcOf 90 ∧ RegsEq u t digRegs ∧ Frame u t digW ∧
      rho.length = 16 ∧ t.readWords (BitVec.ofNat 64 0x30) 2 = wordsOf rho ∧
      (∃ ans : BitVec 256, N = ans.toNat % 2 ^ 184 ∧
        t.readWords (BitVec.ofNat 64 0x160) 3 =
          [ans.extractLsb' 0 64, ans.extractLsb' 64 64, ans.extractLsb' 128 64]) ∧
      uOf N 14 = 0

theorem admissible_iff (ans : BitVec 256) :
    (ans.extractLsb' 128 64 <<< 8 >>> 54 = BitVec.ofNat 64 0) ↔ uOf (ans.toNat % 2 ^ 184) 14 = 0 := by
  rw [← BitVec.toNat_inj]
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.extractLsb'_toNat,
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, BitVec.toNat_ofNat, uOf, totalH, ftsA,
    BitVec.toNat_zero, Nat.reducePow, Nat.reduceAdd, Nat.reduceMul, Nat.reduceMod]
  have := ans.isLt
  constructor <;> intro h <;> omega

theorem pcOf_eq (i : Nat) (h : 0x1000 + 4 * i < 2 ^ 64) (w : Word) (hw : w.toNat = 0x1000 + 4 * i) :
    w = pcOf i := by
  apply BitVec.eq_of_toNat_eq; rw [hw]; simp; omega

theorem pcOf_add4 (i : Nat) : pcOf i + 4 = pcOf (i + 1) := by
  apply BitVec.eq_of_toNat_eq; simp; omega

/-- One trial: from `dig_loop` (counter `a`) the rnd hash, the digest hash, and the test;
`rest` is what follows a non-admissible trial (from instruction 41). -/
theorem digTrial (sk : SecretKey) (m : Message) (u : MachineState)
    (hmem : DigMem (toList sk) (toList m) u) (hx5 : u.getReg .x5 = 0) (a : Nat) (t : MachineState)
    (hinv : DigInv u a t) (rest : OracleComp HashSpec (Option (Val × Nat))) (Wr : Nat)
    (hrest : ∀ t', t'.pc = pcOf 82 → t'.getReg .x6 = BitVec.ofNat 64 a → RegsEq u t' digRegs →
      Frame u t' digW → lo32 (t'.getMem (BitVec.ofNat 64 0x620)) = lo32 (u.getMem (BitVec.ofNat 64 0x620)) →
      Sim image t' Wr rest (DigPost u)) :
    Sim image t (44 + Wr) (hash16 (rndInput (toList sk) (toList m) a) >>= fun rho =>
      (liftM (HashSpec.query (fmt (digestInput rho (toList m)))) : OracleComp HashSpec _) >>= fun ans =>
        if admissible (ans.toNat % 2 ^ 184) then pure (some (rho, ans.toNat % 2 ^ 184)) else rest)
      (DigPost u) := by
  have hS : (toList sk).length = 32 := length_toList sk
  have hm : (toList m).length = 32 := length_toList m
  obtain ⟨tpc, t6, ha, tregs, tframe, tlo⟩ := hinv
  -- block 27
  have hs1 := symRun_sound blk65 codeAt_65 t tpc (by simp only [blk65.res, rv_simp])
  set t1 := blk65.res.toState t with ht1
  have f1 : Frame t t1 (fun x => x = 0x620) := by
    apply frame_toState; intro x hx hW
    simp only [blk65.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq, ofNat_eq_iff]
    omega
  have r1 : RegsEq t t1 [.x10, .x11, .x12] := by
    intro r hr; simp only [ht1, Result.toState_getReg]
    cases r <;> simp_all [blk65.res, rv_simp] <;> rfl
  have e1 : fetch image t1 = some (.base .ECALL) := symRun_ecall blk65 codeAt_65 t (by simp only [blk65.res, rv_simp]) rfl
  have x10 : t1.getReg .x10 = BitVec.ofNat 64 0x620 := by simp only [ht1, blk65.res, rv_simp]
  have x11 : t1.getReg .x11 = BitVec.ofNat 64 128 := by simp only [ht1, blk65.res, rv_simp]
  have x12 : t1.getReg .x12 = BitVec.ofNat 64 0x140 := by simp only [ht1, blk65.res, rv_simp]
  have x5 : t1.getReg .x5 = 0 := by rw [r1.get .x5, tregs.get .x5, hx5]
  have pc1 : t1.pc = pcOf 69 := by simp only [ht1, blk65.res, rv_simp]
  have m620 : t1.getMem (BitVec.ofNat 64 0x620) = twWord0 7 0 0 a := by
    rvs [ht1, blk65.res, t6]
    refine (word_of_halves _ 0x701 a (by rw [lo32_replace1, tlo, hmem.rb0]) (by rw [hi32_replace1])).trans ?_
    unfold twWord0; congr 1
  have hq1 : hashInput t1 = pad64 (rndInput (toList sk) (toList m) a) := by
    obtain ⟨hn, hw⟩ := words_rndInput _ _ hS hm a
    refine hashInput_eq_pad64 t1 _ 1 hn (by rw [x11]) (by norm_num) (by rw [x10]; decide) ?_
    rw [hw, x10, show 8 * (1 + 1) = 1 + 3 + 4 + 4 + 4 from rfl]
    rw [readWords_ofNat_add, readWords_ofNat_add, readWords_ofNat_add, readWords_ofNat_add]
    simp only [Nat.reduceMul, Nat.reduceAdd]
    rw [readWords_ofNat_one, m620]
    rw [f1.readWords _ _ (by norm_num) (by intro i hi; omega),
      f1.readWords _ _ (by norm_num) (by intro i hi; omega),
      f1.readWords _ _ (by norm_num) (by intro i hi; omega),
      f1.readWords _ _ (by norm_num) (by intro i hi; omega),
      tframe.readWords _ _ (by norm_num) (by intro i hi; simp only [digW]; omega),
      tframe.readWords _ _ (by norm_num) (by intro i hi; simp only [digW]; omega),
      tframe.readWords _ _ (by norm_num) (by intro i hi; simp only [digW]; omega),
      tframe.readWords _ _ (by norm_num) (by intro i hi; simp only [digW]; omega),
      hmem.rbP, hmem.rbS, hmem.rbM, hmem.rbZ]
    simp [twWords_eq]
  have hc1 : blk65.res.cycles = 4 := rfl
  rw [hc1] at hs1
  have hb1 : (pad64 (rndInput (toList sk) (toList m) a)).blocks = 2 := by
    simp [pad64, Query.blocks, (words_rndInput _ _ hS hm a).1]
  refine (Sim.steps hs1 (Sim.hash16_bind (W := 4 + (16 + (4 + Wr))) e1 x5
    (hashArgs_of x10 x11 x12 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)) hq1 (fmt_thInput _ _ _ _ _ _ (by decide)) (fun ans1 => ?_))).mono (by rw [hb1]; omega) (fun _ _ h => h)
  -- after the rnd hash
  set rho := answerBytes 16 ans1 with hrho
  set t2 := writeHash t1 ans1 with ht2
  have f2 : Frame t1 t2 (fun x => 0x140 ≤ x ∧ x < 0x140 + 32) := frame_writeHash t1 ans1 0x140 x12 (by norm_num)
  have v2 : t2.readWords (BitVec.ofNat 64 0x140) 2 = wordsOf rho := writeHash_readWords_val t1 ans1 0x140 x12 (by norm_num)
  have pc2 : t2.pc = pcOf 70 := by rw [ht2, writeHash_pc, pc1, pcOf_add4]
  have hs2 := symRun_sound blk70 codeAt_70 t2 pc2 (by simp only [blk70.res, rv_simp])
  set t3 := blk70.res.toState t2 with ht3
  have f3 : Frame t2 t3 (fun x => x = 0x30 ∨ x = 0x38) := by
    apply frame_toState; intro x hx hW
    simp only [blk70.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq, ofNat_eq_iff]
    omega
  have r3 : RegsEq t2 t3 [.x1, .x2, .x10, .x11, .x12] := by
    intro r hr; simp only [ht3, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have e3 : fetch image t3 = some (.base .ECALL) := symRun_ecall blk70 codeAt_70 t2 (by simp only [blk70.res, rv_simp]) rfl
  have y10 : t3.getReg .x10 = BitVec.ofNat 64 0x20 := by simp only [ht3, blk70.res, rv_simp]
  have y11 : t3.getReg .x11 = BitVec.ofNat 64 64 := by simp only [ht3, blk70.res, rv_simp]
  have y12 : t3.getReg .x12 = BitVec.ofNat 64 0x160 := by simp only [ht3, blk70.res, rv_simp]
  have y5 : t3.getReg .x5 = 0 := by rw [r3.get .x5, ht2, writeHash_getReg, x5]
  have pc3 : t3.pc = pcOf 77 := by simp only [ht3, blk70.res, rv_simp]
  have v3 : t3.readWords (BitVec.ofNat 64 0x30) 2 = wordsOf rho := by
    rw [← v2, readWords_ofNat_two, readWords_ofNat_two]; simp only [ht3, blk70.res, rv_simp]; rfl
  -- frame from u to t3 outside digW
  have fu3 : Frame u t3 digW := (((tframe.trans f1).trans f2).trans f3).mono (by
    intro x hx; simp only [digW, false_or, or_false] at hx ⊢; omega)
  have hlen : rho.length = 16 := by simp [hrho]
  have hq2 : hashInput t3 = fmt (digestInput rho (toList m)) := by
    refine hashInput_eq_digest t3 _ _ hlen hm y11 (by rw [y10]; decide) ?_
    rw [y10, show (8 : Nat) = 2 + 2 + 4 from rfl]
    rw [readWords_ofNat_add, readWords_ofNat_add]
    simp only [Nat.reduceMul, Nat.reduceAdd]
    rw [fu3.readWords _ _ (by norm_num) (by intro i hi; simp only [digW]; omega), hmem.db0, v3,
      fu3.readWords _ _ (by norm_num) (by intro i hi; simp only [digW]; omega), hmem.dbM]
    simp [twWords_eq, twWord0]
  have hc2 : blk70.res.cycles = 7 := rfl
  rw [hc2] at hs2
  have hb2 : (fmt (digestInput rho (toList m))).blocks = 1 := by
    rw [fmt_digestInput _ _ hlen hm]; rfl
  refine (Sim.steps hs2 (Sim.query_bind (W := 4 + Wr) e3 y5
    (hashArgs_of y10 y11 y12 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)) hq2 (fun ans2 => ?_))).mono (by rw [hb2]; omega) (fun _ _ h => h)
  -- after the digest hash
  set t4 := writeHash t3 ans2 with ht4
  have f4 : Frame t3 t4 (fun x => 0x160 ≤ x ∧ x < 0x160 + 32) :=
    frame_writeHash t3 ans2 0x160 y12 (by norm_num)
  have pc4 : t4.pc = pcOf 78 := by rw [ht4, writeHash_pc, pc3, pcOf_add4]
  have w4 : ∀ k, k < 3 → t4.getMem (BitVec.ofNat 64 (0x160 + 8 * k)) = ans2.extractLsb' (64 * k) 64 := by
    intro k hk
    rw [ht4, writeHash_getMem_ofNat t3 ans2 0x160 _ y12 (by norm_num) (by omega)]
    interval_cases k <;> simp
  have hs3 := symRun_sound blk78 codeAt_78 t4 pc4 (by simp only [blk78.res, rv_simp])
  have hc3 : blk78.res.cycles = 4 := rfl
  rw [hc3] at hs3
  set t5 := blk78.res.toState t4 with ht5
  have f5 : Frame t4 t5 (fun _ => False) := by
    apply frame_toState; intro x hx hW; simp [blk78.res]
  have r5 : RegsEq t4 t5 [.x3] := by
    intro r hr; simp only [ht5, Result.toState_getReg]
    cases r <;> simp_all [blk78.res, rv_simp]
  have fu5 : Frame u t5 digW := ((fu3.trans f4).trans f5).mono (by
    intro x hx; simp only [digW, false_or, or_false] at hx ⊢; omega)
  have ru5 : RegsEq u t5 digRegs := (((((tregs.trans r1).trans (regsEq_writeHash _ _ [])).trans r3).trans
    (regsEq_writeHash _ _ [])).trans r5).mono (by decide)
  have pc5 : t5.pc = if admissible (ans2.toNat % 2 ^ 184) then pcOf 90 else pcOf 82 := by
    have h368 := w4 2 (by norm_num)
    simp only [Nat.reduceMul, Nat.reduceAdd] at h368
    simp only [ht5, blk78.res, rv_simp, h368]
    simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, admissible, beq_iff_eq]
    by_cases h : uOf (ans2.toNat % 2 ^ 184) 14 = 0
    · rw [if_pos ((admissible_iff ans2).mpr h), if_pos (by simpa using h)]
    · rw [if_neg (mt (admissible_iff ans2).mp h), if_neg (by simpa using h)]
  by_cases hadm : admissible (ans2.toNat % 2 ^ 184) = true
  · rw [if_pos hadm]
    refine (Sim.pure_steps hs3 ?_).mono (by omega) (fun _ _ h => h)
    refine ⟨by rw [pc5, if_pos hadm], ru5, fu5, hlen, ?_, ⟨ans2, rfl, ?_⟩, ?_⟩
    · rw [f5.readWords _ _ (by norm_num) (by simp), f4.readWords _ _ (by norm_num) (by intro i hi; omega), v3]
    · rw [f5.readWords _ _ (by norm_num) (by simp)]
      simp only [readWords_ofNat_succ, MachineState.readWords]
      have := w4 0 (by norm_num); have := w4 1 (by norm_num); have := w4 2 (by norm_num)
      simp_all
    · simpa [admissible] using hadm
  · rw [if_neg hadm]
    refine Sim.steps hs3 (hrest t5 (by rw [pc5, if_neg hadm]) ?_ ru5 fu5 ?_)
    · rw [r5.get .x6, ht4, writeHash_getReg, r3.get .x6, ht2, writeHash_getReg, r1.get .x6, t6]
    · rw [f5.getMem (by norm_num) (by simp), f4.getMem (by norm_num) (by omega),
        f3.getMem (by norm_num) (by omega), f2.getMem (by norm_num) (by omega)]
      simp only [ht1, blk65.res, rv_simp, ite_true, lo32_replace1, Nat.reduceDiv]
      exact tlo

theorem searchDigest_succ (S mm : List Byte) (a f : Nat) :
    searchDigest S mm a (f + 1) = (hash16 (rndInput S mm a) >>= fun rho =>
      (liftM (HashSpec.query (fmt (digestInput rho mm))) : OracleComp HashSpec _) >>= fun ans =>
        if admissible (ans.toNat % 2 ^ 184) then pure (some (rho, ans.toNat % 2 ^ 184))
        else searchDigest S mm (a + 1) f) := by
  simp only [searchDigest, digest, H, bind_assoc, pure_bind]

/-- After a non-admissible trial (instruction 41): `a += 1`, back to the loop or fail. -/
theorem digNext (u : MachineState) (hx7 : u.getReg .x7 = BitVec.ofNat 64 (2 ^ 20)) (a : Nat)
    (ha : a < 2 ^ 20) (t : MachineState) (tpc : t.pc = pcOf 82) (t6 : t.getReg .x6 = BitVec.ofNat 64 a)
    (tregs : RegsEq u t digRegs) (tframe : Frame u t digW)
    (tlo : lo32 (t.getMem (BitVec.ofNat 64 0x620)) = lo32 (u.getMem (BitVec.ofNat 64 0x620))) :
    ∃ t', Steps image t 2 2 t' ∧
      (a + 1 < 2 ^ 20 → DigInv u (a + 1) t') ∧ (a + 1 = 2 ^ 20 → t'.pc = pcOf 84) ∧
      RegsEq t t' [.x6] := by
  have hs := symRun_sound blk82 codeAt_82 t tpc (by simp only [blk82.res, rv_simp])
  have r41 : RegsEq t (blk82.res.toState t) [.x6] := by
    intro r hr
    rw [Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  refine ⟨_, hs, ?_, ?_, r41⟩
  · intro h
    refine ⟨?_, ?_, h, ?_, ?_, ?_⟩
    · simp only [blk82.res, rv_simp, t6, tregs.get .x7 (by simp [digRegs]), hx7, ofNat_add_ofNat,
        ofNat_bne_ofNat]
      rw [if_pos (by simp; omega)]
    · simp only [blk82.res, rv_simp, t6, ofNat_add_ofNat]
    · exact (tregs.trans r41).mono (by intro r hr; simp [digRegs] at hr ⊢; tauto)
    · intro x hx hW
      rw [Result.toState_getMem, show blk82.res.st.mem = [] from rfl, memEval_nil]; exact tframe x hx hW
    · rw [Result.toState_getMem, show blk82.res.st.mem = [] from rfl, memEval_nil]; exact tlo
  · intro h
    simp only [blk82.res, rv_simp, t6, tregs.get .x7 (by simp [digRegs]), hx7, ofNat_add_ofNat,
      ofNat_bne_ofNat]
    rw [if_neg (by simp; omega)]

/-- The digest search. -/
theorem digLoop_sim (sk : SecretKey) (m : Message) (u : MachineState)
    (hmem : DigMem (toList sk) (toList m) u) (hx5 : u.getReg .x5 = 0)
    (hx7 : u.getReg .x7 = BitVec.ofNat 64 (2 ^ 20)) :
    ∀ fuel a t, a + (fuel + 1) = 2 ^ 20 → DigInv u a t →
      Sim image t ((fuel + 1) * 46 + 2) (searchDigest (toList sk) (toList m) a (fuel + 1))
        (DigPost u) := by
  have hS : (toList sk).length = 32 := length_toList sk
  have hm : (toList m).length = 32 := length_toList m
  intro fuel
  induction fuel with
  | zero =>
    intro a t ha hinv
    rw [searchDigest_succ]
    refine (digTrial sk m u hmem hx5 a t hinv _ 4 ?_).mono (by omega) (fun _ _ h => h)
    intro t' tpc t6 tregs tframe tlo
    obtain ⟨t'', hs, -, hfail, -⟩ := digNext u hx7 a (by omega) t' tpc t6 tregs tframe tlo
    have hs43 := symRun_sound blk84 codeAt_84 t'' (hfail (by omega)) (by simp only [blk84.res, rv_simp])
    have hc : blk84.res.cycles = 2 := rfl
    rw [hc] at hs43
    have := Sim.steps hs (Sim.pure_steps (a := (none : Option (Val × Nat))) (Q := DigPost u) hs43
      ⟨by simp only [blk84.res, rv_simp], by simp only [blk84.res, rv_simp],
       by simp only [blk84.res, rv_simp]⟩)
    simpa [searchDigest] using this
  | succ f ih =>
    intro a t ha hinv
    rw [searchDigest_succ]
    refine (digTrial sk m u hmem hx5 a t hinv _ (2 + ((f + 1) * 46 + 2)) ?_).mono (by ring_nf; omega)
      (fun _ _ h => h)
    intro t' tpc t6 tregs tframe tlo
    obtain ⟨t'', hs, hinv', -, -⟩ := digNext u hx7 a (by omega) t' tpc t6 tregs tframe tlo
    exact Sim.steps hs (ih (a + 1) t'' (by omega) (hinv' (by omega)))

end SigGolfCandidate.Radix27Sign



end


section -- SignClone13.Enc

/-! ### cloned Enc -/

/-!
# `sign`, the counter search of a layer (`enc_loop`, instructions 294 .. 329)

`encLoop_sim` : from `enc_loop` with counter `c`, the machine refines
`searchCounter lay tau e M c (2^22 - c)`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace SigGolfCandidate.Radix27Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

theorem slice_valOfWords_0 (w0 w1 : Word) : slice (valOfWords w0 w1) 0 8 = bytesOfWord w0 := by
  simp [slice, valOfWords]

theorem slice_valOfWords_8 (w0 w1 : Word) : slice (valOfWords w0 w1) 8 8 = bytesOfWord w1 := by
  simp [slice, valOfWords, List.drop_append_of_le_length]

/-- `decodeDigits` of a hash answer, in terms of its first two dwords. -/
theorem decodeDigits_answer (a : BitVec 256) :
    decodeDigits (answerBytes 16 a) =
      if (a.extractLsb' 0 64).toNat < 2 ^ 63 ∧ (a.extractLsb' 64 64).toNat < 2 ^ 63 then
        (if (digitsOfWord (a.extractLsb' 0 64).toNat ++ digitsOfWord (a.extractLsb' 64 64).toNat).sum
            = 184 then
          some (digitsOfWord (a.extractLsb' 0 64).toNat ++ digitsOfWord (a.extractLsb' 64 64).toNat)
        else none)
      else none := by
  rw [answerBytes_16]
  unfold decodeDigits
  rw [slice_valOfWords_0, slice_valOfWords_8, leNat_bytesOfWord, leNat_bytesOfWord]
  rfl

theorem slt_zero_ofNat (d : Nat) (hd : d < 2 ^ 64) :
    BitVec.slt (BitVec.ofNat 64 d) (BitVec.ofNat 64 0) = decide (2 ^ 63 ≤ d) := by
  rw [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.slt_zero_eq_msb, BitVec.msb_eq_decide]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd]

theorem land7 (n : Nat) : n &&& 7 = n % 8 := Nat.and_two_pow_sub_one_eq_mod n 3

/-! ## The SWAR digit sum (shared with verify: `Verify.swar_nat`) -/

/-- The digit-sum masks `M1 = 0x71C7..` (3-bit digits, even positions of 6-bit lanes) and
`M2 = 0xF03F..` (6-bit lanes, even positions of 12-bit lanes). -/
abbrev swM1 : Word := BitVec.ofNat 64 8198552921648689607
abbrev swM2 : Word := BitVec.ofNat 64 17311559823019733055

/-- The four masked digit lanes. -/
def swS1 (a b m1 : Word) : Word := ((a >>> 3) &&& m1) + (a &&& m1) + ((b >>> 3) &&& m1) + (b &&& m1)

/-- One folding step `x + (x >> k)`. -/
def swF (x : Word) (k : Nat) : Word := x + (x >>> k)

/-- The machine's SWAR digit sum of `(d0, d1)` (instructions 309 .. 327). -/
def swarW (a b m1 m2 : Word) : Word :=
  swF (swF (swF (swF (swS1 a b m1) 6 &&& m2) 12) 24) 48 &&& 2047

-- The final pc of the SWAR block (`bne t3, x0` after `addi t3, t3, -184`).
kernel_theorem blk311_pc_raw : ∀ t : MachineState, (blk311.res.toState t).pc =
    if (swarW (t.getReg .x1) (t.getReg .x2) (t.getReg .x26) (t.getReg .x27) +
        BitVec.ofNat 64 (2 ^ 64 - 184) != 0#64) = true then pcOf 333 else pcOf 332

theorem swF_toNat (x : Word) (k : Nat) : (swF x k).toNat = (x.toNat + x.toNat / 2 ^ k) % 2 ^ 64 := by
  rw [swF, BitVec.toNat_add, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem swM1_toNat : swM1.toNat = 8198552921648689607 := rfl
theorem swM2_toNat : swM2.toNat = 17311559823019733055 := rfl

theorem swS1_toNat (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (swS1 (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) swM1).toNat = Verify.sw1 a b := by
  have ea : (BitVec.ofNat 64 a).toNat = a := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]
  have eb : (BitVec.ofNat 64 b).toNat = b := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
  rw [swS1, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_and, BitVec.toNat_and,
    BitVec.toNat_and, BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ushiftRight, ea, eb,
    swM1_toNat, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, show (2 : Nat) ^ 3 = 8 from rfl,
    show (2 : Nat) ^ 64 = 18446744073709551616 from rfl]
  unfold Verify.sw1
  rfl

theorem digitsOfWord_sum_le (d : Nat) : (digitsOfWord d).sum ≤ 147 := by
  have := List.sum_le_card_nsmul (digitsOfWord d) 7 (fun x hx => by
    simp only [digitsOfWord, List.mem_map, List.mem_range] at hx
    obtain ⟨r, _, rfl⟩ := hx; exact Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num)))
  simpa [digitsOfWord] using this

theorem digits_sum_le (a b : Nat) : (digitsOfWord a ++ digitsOfWord b).sum ≤ 294 := by
  rw [List.sum_append]; have := digitsOfWord_sum_le a; have := digitsOfWord_sum_le b; omega

theorem swarW_toNat (a b : Nat) (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) :
    (swarW (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) swM1 swM2).toNat =
      (digitsOfWord a ++ digitsOfWord b).sum := by
  have key := Verify.swar_nat a b ha hb
  have hle := digits_sum_le a b
  have h1 : (swF (swS1 (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) swM1) 6 &&& swM2).toNat =
      Verify.m3 ((Verify.sw1 a b + Verify.sw1 a b / 64) % 18446744073709551616) := by
    rw [BitVec.toNat_and, swF_toNat, swS1_toNat a b (by omega) (by omega), swM2_toNat,
      show (2 : Nat) ^ 6 = 64 from rfl, show (2 : Nat) ^ 64 = 18446744073709551616 from rfl]
    unfold Verify.m3; rfl
  have h2 : ∀ (Y : Word) (y : Nat), Y.toNat = y → (swF (swF (swF Y 12) 24) 48).toNat = Verify.m6 y := by
    intro Y y hY
    rw [swF_toNat, swF_toNat, swF_toNat, hY, show (2 : Nat) ^ 12 = 4096 from rfl,
      show (2 : Nat) ^ 24 = 16777216 from rfl, show (2 : Nat) ^ 48 = 281474976710656 from rfl,
      show (2 : Nat) ^ 64 = 18446744073709551616 from rfl]
    unfold Verify.m6 Verify.m6' Verify.m5 Verify.m4; rfl
  have h3 := h2 _ _ h1
  have h4 : (swarW (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) swM1 swM2).toNat =
      (swF (swF (swF (swF (swS1 (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) swM1) 6 &&& swM2) 12) 24) 48).toNat
        % 2048 := by
    unfold swarW
    rw [BitVec.toNat_and, show (2047 : Word).toNat = 2 ^ 11 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  rw [h4, h3]
  generalize Verify.m6 (Verify.m3 ((Verify.sw1 a b + Verify.sw1 a b / 64) % 18446744073709551616)) = X at key ⊢
  rw [← Nat.mod_mod_of_dvd X (show 2048 ∣ 4096 by norm_num), key]
  omega

theorem swar_check (a b : Nat) (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) :
    (swarW (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) swM1 swM2 + BitVec.ofNat 64 (2 ^ 64 - 184)
      != 0#64) = !decide ((digitsOfWord a ++ digitsOfWord b).sum = 184) := by
  have h := swarW_toNat a b ha hb
  have hle := digits_sum_le a b
  generalize swarW (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) swM1 swM2 = w at h
  have hc : (BitVec.ofNat 64 (2 ^ 64 - 184)).toNat = 2 ^ 64 - 184 := rfl
  by_cases hs : (digitsOfWord a ++ digitsOfWord b).sum = 184
  · have : w + BitVec.ofNat 64 (2 ^ 64 - 184) = 0#64 := by
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add, h, hs, hc]; rfl
    rw [this, decide_eq_true hs]; rfl
  · have : w + BitVec.ofNat 64 (2 ^ 64 - 184) ≠ 0#64 := by
      intro h'
      have := congrArg BitVec.toNat h'
      rw [BitVec.toNat_add, h, hc] at this
      have h0 : (0#64).toNat = 0 := rfl
      rw [h0] at this
      omega
    rw [bne_iff_ne.mpr this, decide_eq_false hs]; rfl

/-- The sign test `(d0 | d1) < 0` (bit 63 of either word). -/
theorem slt_or_ofNat (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    BitVec.slt (BitVec.ofNat 64 a ||| BitVec.ofNat 64 b) (BitVec.ofNat 64 0) =
      decide (2 ^ 63 ≤ a ∨ 2 ^ 63 ≤ b) := by
  rw [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.slt_zero_eq_msb, BitVec.msb_or,
    BitVec.msb_eq_decide, BitVec.msb_eq_decide]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  by_cases h1 : 2 ^ 63 ≤ a <;> by_cases h2 : 2 ^ 63 ≤ b <;> simp [h1, h2]

structure EncMem (lay tau e : Nat) (M : Val) (u : MachineState) : Prop where
  hlay : lay < 6
  htau : tau < 2 ^ 30
  he : e < 2048
  hM : M.length = 16
  eb0 : u.getMem (BitVec.ofNat 64 0x100) = twWord0 4 lay tau 0
  eb8 : u.getMem (BitVec.ofNat 64 0x108) = BitVec.ofNat 64 (tau + 2 ^ 32 * e)
  ebP : u.readWords (BitVec.ofNat 64 0x110) 2 = [0, 0]
  ebM : u.readWords (BitVec.ofNat 64 0x120) 2 = wordsOf M
  eb56 : u.getMem (BitVec.ofNat 64 0x138) = 0
  x5 : u.getReg .x5 = 0
  x7 : u.getReg .x7 = BitVec.ofNat 64 (2 ^ 22)
  x26 : u.getReg .x26 = swM1
  x27 : u.getReg .x27 = swM2

def encW (a : Nat) : Prop := a = 0x130 ∨ (0x140 ≤ a ∧ a < 0x160)

def encRegs : List Reg := [.x1, .x2, .x3, .x6, .x10, .x11, .x12, .x28, .x29]

def EncInv (u : MachineState) (c : Nat) (t : MachineState) : Prop :=
  t.pc = pcOf 302 ∧ t.getReg .x6 = BitVec.ofNat 64 c ∧ c < 2 ^ 22 ∧ RegsEq u t encRegs ∧ Frame u t encW

def EncPost (u : MachineState) : Option (Nat × List Nat) → MachineState → Prop
  | none, t => t.pc = pcOf 337 ∧ t.getReg .x5 = 1 ∧ t.getReg .x10 = 1
  | some (c, x), t => t.pc = pcOf 338 ∧ t.getReg .x6 = BitVec.ofNat 64 c ∧ c < 2 ^ 22 ∧
      (∃ d0 d1, d0 < 2 ^ 63 ∧ d1 < 2 ^ 63 ∧ x = digitsOfWord d0 ++ digitsOfWord d1 ∧ x.sum = 184 ∧
        t.getReg .x1 = BitVec.ofNat 64 d0 ∧ t.getReg .x2 = BitVec.ofNat 64 d1) ∧
      RegsEq u t encRegs ∧ Frame u t encW

theorem searchCounter_succ (lay tau e : Nat) (M : Val) (c f : Nat) :
    searchCounter lay tau e M c (f + 1) = (hash16 (encInput lay tau e M c) >>= fun d =>
      match decodeDigits d with
      | some x => pure (some (c, x))
      | none => searchCounter lay tau e M (c + 1) f) := rfl

theorem encTrial (lay tau e : Nat) (M : Val) (u : MachineState) (hmem : EncMem lay tau e M u)
    (c : Nat) (t : MachineState) (hinv : EncInv u c t) (rest : OracleComp HashSpec (Option (Nat × List Nat)))
    (Wr : Nat)
    (hrest : ∀ t', t'.pc = pcOf 333 → t'.getReg .x6 = BitVec.ofNat 64 c → RegsEq u t' encRegs →
      Frame u t' encW → Sim image t' Wr rest (EncPost u)) :
    Sim image t (38 + Wr) (hash16 (encInput lay tau e M c) >>= fun d =>
      match decodeDigits d with
      | some x => pure (some (c, x))
      | none => rest) (EncPost u) := by
  obtain ⟨tpc, t6, hc, tregs, tframe⟩ := hinv
  have hl := hmem.hlay
  have htau := hmem.htau
  have he := hmem.he
  -- block 294
  have hs1 := symRun_sound blk302 codeAt_302 t tpc (by simp only [blk302.res, rv_simp])
  have hc1 : blk302.res.cycles = 4 := rfl
  rw [hc1] at hs1
  set t1 := blk302.res.toState t with ht1
  have f1 : Frame t t1 (fun x => x = 0x130) := by
    apply frame_toState; intro x hx hW
    simp only [blk302.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq, ofNat_eq_iff]
    omega
  have r1 : RegsEq t t1 [.x10, .x11, .x12] := by
    intro r hr; rw [ht1, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have e1 := symRun_ecall blk302 codeAt_302 t (by simp only [blk302.res, rv_simp]) rfl
  have x10 : t1.getReg .x10 = BitVec.ofNat 64 0x100 := by simp only [ht1, blk302.res, rv_simp]
  have x11 : t1.getReg .x11 = BitVec.ofNat 64 64 := by simp only [ht1, blk302.res, rv_simp]
  have x12 : t1.getReg .x12 = BitVec.ofNat 64 0x140 := by simp only [ht1, blk302.res, rv_simp]
  have x5 : t1.getReg .x5 = 0 := by rw [r1.get .x5, tregs.get .x5, hmem.x5]
  have pc1 : t1.pc = pcOf 306 := by simp only [ht1, blk302.res, rv_simp]
  have hq : hashInput t1 = pad64 (encInput lay tau e M c) := by
    obtain ⟨hn, hw⟩ := words_encInput lay tau e M hmem.hM c
    refine hashInput_eq_pad64 t1 _ 0 hn (by rw [x11]) (by norm_num) (by rw [x10]; decide) ?_
    rw [hw, x10, show 8 * (0 + 1) = 1 + 1 + 2 + 2 + 1 + 1 from rfl]
    rw [readWords_ofNat_add, readWords_ofNat_add, readWords_ofNat_add, readWords_ofNat_add,
      readWords_ofNat_add]
    simp only [Nat.reduceMul, Nat.reduceAdd]
    rw [readWords_ofNat_one, readWords_ofNat_one, readWords_ofNat_one, readWords_ofNat_one,
      f1.getMem (a := 0x100) (by norm_num) (by norm_num),
      tframe.getMem (a := 0x100) (by norm_num) (by simp only [encW]; omega),
      hmem.eb0, f1.getMem (a := 0x108) (by norm_num) (by norm_num),
      tframe.getMem (a := 0x108) (by norm_num) (by simp only [encW]; omega), hmem.eb8,
      f1.readWords _ _ (by norm_num) (by intro i hi; omega),
      tframe.readWords _ _ (by norm_num) (by intro i hi; simp only [encW]; omega), hmem.ebP,
      f1.readWords _ _ (by norm_num) (by intro i hi; omega),
      tframe.readWords _ _ (by norm_num) (by intro i hi; simp only [encW]; omega), hmem.ebM,
      f1.getMem (a := 0x138) (by norm_num) (by norm_num),
      tframe.getMem (a := 0x138) (by norm_num) (by simp only [encW]; omega), hmem.eb56]
    simp only [ht1, blk302.res, rv_simp, t6]
    simp only [twWords_eq, List.cons_append, List.nil_append, List.append_assoc, List.cons.injEq,
      true_and, and_true]
    refine ⟨?_, ?_⟩
    · congr 1; rw [Nat.mod_eq_of_lt (by omega : tau < 2 ^ 32), Nat.mod_eq_of_lt (by omega : e < 2 ^ 32)]
    · rw [if_pos trivial, Nat.mod_eq_of_lt (by omega : c < 2 ^ 32)]
  have hb : (pad64 (encInput lay tau e M c)).blocks = 1 :=
    congrArg (· + 1) (words_encInput lay tau e M hmem.hM c).1
  refine (Sim.steps hs1 (Sim.hash16_bind (W := 26 + Wr) e1 x5
    (hashArgs_of x10 x11 x12 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)) hq (fmt_thInput _ _ _ _ _ _ (by decide)) (fun a => ?_))).mono (by rw [hb]; omega) (fun _ _ h => h)
  set t2 := writeHash t1 a with ht2
  have f2 : Frame t1 t2 (fun x => 0x140 ≤ x ∧ x < 0x140 + 32) := frame_writeHash t1 a _ x12 (by norm_num)
  have pc2 : t2.pc = pcOf 307 := by rw [ht2, writeHash_pc, pc1]; apply BitVec.eq_of_toNat_eq; simp
  have w0 : t2.getMem (BitVec.ofNat 64 0x140) = a.extractLsb' 0 64 := by
    rw [ht2, writeHash_getMem_ofNat t1 a 0x140 0x140 x12 (by norm_num) (by norm_num)]; simp
  have w1 : t2.getMem (BitVec.ofNat 64 0x148) = a.extractLsb' 64 64 := by
    rw [ht2, writeHash_getMem_ofNat t1 a 0x140 0x148 x12 (by norm_num) (by norm_num)]; simp
  set d0 := (a.extractLsb' 0 64).toNat with hd0
  set d1 := (a.extractLsb' 64 64).toNat with hd1
  have hd0' : a.extractLsb' 0 64 = BitVec.ofNat 64 d0 := by rw [hd0, BitVec.ofNat_toNat]; rfl
  have hd1' : a.extractLsb' 64 64 = BitVec.ofNat 64 d1 := by rw [hd1, BitVec.ofNat_toNat]; rfl
  have hd0l : d0 < 2 ^ 64 := BitVec.isLt _
  have hd1l : d1 < 2 ^ 64 := BitVec.isLt _
  rw [decodeDigits_answer]
  -- block 299: load the encoding, sign test
  have hs3 := symRun_sound blk307 codeAt_307 t2 pc2 (by simp only [blk307.res, rv_simp])
  have hc3 : blk307.res.cycles = 4 := rfl
  rw [hc3] at hs3
  set t3 := blk307.res.toState t2 with ht3
  have f3 : Frame t2 t3 (fun _ => False) := by
    apply frame_toState; intro x hx hW; simp [blk307.res]
  have r3 : RegsEq t2 t3 [.x1, .x2, .x3] := by
    intro r hr; rw [ht3, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have y1 : t3.getReg .x1 = BitVec.ofNat 64 d0 := by
    simp only [ht3, blk307.res, rv_simp]; rw [w0, hd0']
  have y2 : t3.getReg .x2 = BitVec.ofNat 64 d1 := by
    simp only [ht3, blk307.res, rv_simp]; rw [w1, hd1']
  have fu3 : Frame u t3 encW := (((tframe.trans f1).trans f2).trans f3).mono (by
    intro x hx; simp only [encW] at hx ⊢; rcases hx with ((h | h) | h) | h
    · exact h
    · omega
    · omega
    · exact h.elim)
  have ru3 : RegsEq u t3 encRegs := ((((tregs.trans r1).trans (regsEq_writeHash _ _ [])).trans r3)).mono
    (by decide)
  have x36 : t3.getReg .x6 = BitVec.ofNat 64 c := by
    rw [r3.get .x6, ht2, writeHash_getReg, r1.get .x6, t6]
  have pc3 : t3.pc = if 2 ^ 63 ≤ d0 ∨ 2 ^ 63 ≤ d1 then pcOf 333 else pcOf 311 := by
    simp only [ht3, blk307.res, rv_simp, CmpOp.eval, w0, w1, hd0', hd1', slt_or_ofNat _ _ hd0l hd1l]
    by_cases h : 2 ^ 63 ≤ d0 ∨ 2 ^ 63 ≤ d1
    · rw [if_pos h, if_pos (by simpa using h)]
    · rw [if_neg h, if_neg (by simpa using h)]
  by_cases h01 : d0 < 2 ^ 63 ∧ d1 < 2 ^ 63
  swap
  · rw [if_neg h01]
    exact (Sim.steps hs3 (hrest t3 (by rw [pc3, if_pos (by omega)]) x36 ru3 fu3)).mono (by omega)
      (fun _ _ h => h)
  obtain ⟨h0, h1⟩ := h01
  rw [if_pos ⟨h0, h1⟩]
  have hs5 := symRun_sound blk311 codeAt_311 t3 (by rw [pc3, if_neg (by omega)])
    (by simp only [blk311.res, rv_simp])
  have hc5 : blk311.res.cycles = 21 := rfl
  rw [hc5] at hs5
  set t5 := blk311.res.toState t3 with ht5
  have f5 : Frame t3 t5 (fun _ => False) := by
    apply frame_toState; intro x hx hW; simp [blk311.res]
  have r5 : RegsEq t3 t5 [.x28, .x29] := by
    intro r hr; rw [ht5, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have fu5 : Frame u t5 encW := (fu3.trans f5).mono (by
    intro x hx; rcases hx with h | h; exact h; exact h.elim)
  have ru5 : RegsEq u t5 encRegs := (ru3.trans r5).mono (by decide)
  have pc5 : t5.pc = if (digitsOfWord d0 ++ digitsOfWord d1).sum = 184 then pcOf 332 else pcOf 333 := by
    rw [ht5, blk311_pc_raw, y1, y2, ru3.get .x26, hmem.x26, ru3.get .x27, hmem.x27,
      swar_check d0 d1 h0 h1]
    by_cases h : (digitsOfWord d0 ++ digitsOfWord d1).sum = 184
    · rw [if_pos h, if_neg (by rw [decide_eq_true h]; decide)]
    · rw [if_neg h, if_pos (by rw [decide_eq_false h]; rfl)]
  by_cases hsum : (digitsOfWord d0 ++ digitsOfWord d1).sum = 184
  · rw [if_pos hsum]
    have hs6 := symRun_sound blk332 codeAt_332 t5 (by rw [pc5, if_pos hsum])
      (by simp only [blk332.res, rv_simp])
    have hc6 : blk332.res.cycles = 1 := rfl
    rw [hc6] at hs6
    set t6 := blk332.res.toState t5 with ht6
    have f6 : Frame t5 t6 (fun _ => False) := by
      apply frame_toState; intro x hx hW; simp [blk332.res]
    have r6 : RegsEq t5 t6 [] := by
      intro r hr; rw [ht6, Result.toState_getReg]
      cases r <;> first | exact absurd (by decide) hr | rfl
    refine (Sim.steps hs3 (Sim.steps hs5 (Sim.pure_steps hs6 ?_))).mono
      (by omega) (fun _ _ h => h)
    refine ⟨by simp only [ht6, blk332.res, rv_simp], ?_, hc, ⟨d0, d1, h0, h1, rfl, hsum, ?_, ?_⟩,
      (ru5.trans r6).mono (by decide), (fu5.trans f6).mono (by
        intro x hx; rcases hx with h | h; exact h; exact h.elim)⟩
    · rw [r6.get .x6, r5.get .x6, x36]
    · rw [r6.get .x1, r5.get .x1, y1]
    · rw [r6.get .x2, r5.get .x2, y2]
  · rw [if_neg hsum]
    exact (Sim.steps hs3 (Sim.steps hs5 (hrest t5 (by rw [pc5, if_neg hsum])
      (by rw [r5.get .x6, x36]) ru5 fu5))).mono (by omega) (fun _ _ h => h)

/-- After a failing trial (instruction 325): `c += 1`, back to the loop or fail. -/
theorem encNext (u : MachineState) (hx7 : u.getReg .x7 = BitVec.ofNat 64 (2 ^ 22)) (c : Nat)
    (hc : c < 2 ^ 22) (t : MachineState) (tpc : t.pc = pcOf 333) (t6 : t.getReg .x6 = BitVec.ofNat 64 c)
    (tregs : RegsEq u t encRegs) (tframe : Frame u t encW) :
    ∃ t', Steps image t 2 2 t' ∧ (c + 1 < 2 ^ 22 → EncInv u (c + 1) t') ∧
      (c + 1 = 2 ^ 22 → t'.pc = pcOf 335) := by
  have hs := symRun_sound blk333 codeAt_333 t tpc (by simp only [blk333.res, rv_simp])
  have r1 : RegsEq t (blk333.res.toState t) [.x6] := by
    intro r hr; rw [Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have t7 : t.getReg .x7 = BitVec.ofNat 64 (2 ^ 22) := by rw [tregs.get .x7, hx7]
  refine ⟨_, hs, ?_, ?_⟩
  · intro h
    refine ⟨?_, ?_, h, (tregs.trans r1).mono (by decide), ?_⟩
    · simp only [blk333.res, rv_simp, t6, t7, ofNat_add_ofNat, ofNat_bne_ofNat]
      rw [if_pos (by rw [bne_cond _ _ (by omega) (by omega)]; omega)]
    · simp only [blk333.res, rv_simp, t6, ofNat_add_ofNat]
    · intro x hx hW
      rw [Result.toState_getMem, show blk333.res.st.mem = [] from rfl, memEval_nil]; exact tframe x hx hW
  · intro h
    simp only [blk333.res, rv_simp, t6, t7, ofNat_add_ofNat, ofNat_bne_ofNat]
    rw [if_neg (by rw [bne_cond _ _ (by omega) (by omega)]; omega)]

/-- **Counter search** of a layer, from counter `c` with `fuel + 1` trials left. -/
theorem encLoop_sim (lay tau e : Nat) (M : Val) (u : MachineState) (hmem : EncMem lay tau e M u) :
    ∀ fuel c t, c + (fuel + 1) = 2 ^ 22 → EncInv u c t →
      Sim image t ((fuel + 1) * 40 + 2) (searchCounter lay tau e M c (fuel + 1)) (EncPost u) := by
  intro fuel
  induction fuel with
  | zero =>
    intro c t hc hinv
    rw [searchCounter_succ]
    refine (encTrial lay tau e M u hmem c t hinv _ 4 ?_).mono (by omega) (fun _ _ h => h)
    intro t' tpc t6 tregs tframe
    obtain ⟨t'', hs, -, hfail⟩ := encNext u hmem.x7 c (by omega) t' tpc t6 tregs tframe
    have hs67 := symRun_sound blk335 codeAt_335 t'' (hfail (by omega)) (by simp only [blk335.res, rv_simp])
    have hc67 : blk335.res.cycles = 2 := rfl
    rw [hc67] at hs67
    have := Sim.steps hs (Sim.pure_steps (a := (none : Option (Nat × List Nat))) (Q := EncPost u) hs67
      ⟨by simp only [blk335.res, rv_simp], by simp only [blk335.res, rv_simp],
       by simp only [blk335.res, rv_simp]⟩)
    simpa [searchCounter] using this
  | succ f ih =>
    intro c t hc hinv
    rw [searchCounter_succ]
    refine (encTrial lay tau e M u hmem c t hinv _ (2 + ((f + 1) * 40 + 2)) ?_).mono
      (by ring_nf; omega) (fun _ _ h => h)
    intro t' tpc t6 tregs tframe
    obtain ⟨t'', hs, hinv', -⟩ := encNext u hmem.x7 c (by omega) t' tpc t6 tregs tframe
    exact Sim.steps hs (ih (c + 1) t'' (by omega) (hinv' (by omega)))

end SigGolfCandidate.Radix27Sign



end


section -- SignClone13.Init

/-! ### cloned Init -/

/-!
# The initial state of `sign`

`initialState submission .sign (sk, cache, m) = some (s0 sk cache m)`; its registers are `0`
except `x2`, its memory holds the secret key at `0x80`, the message at `0x40`, the cache at
`0x44A0`, and zeros elsewhere (`s0_readWords_sk`, `s0_readWords_msg`, `s0_zero`).
-/

namespace SigGolfCandidate.Radix27Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref SigGolfCandidate.Mem

set_option maxRecDepth 100000

abbrev submission : Submission := Radix27Submission.concrete

/-- The loaded initial state. -/
def s0 (sk : SecretKey) (cache : Cache) (m : Message) : MachineState :=
  let blank : MachineState := { regs := fun _ => 0, mem := fun _ => 0, pc := 0x1000 }
  ((((blank.writeBytesAsWords (BitVec.ofNat 64 (dataBase image)) image.data).writeBytesAsWords
      (BitVec.ofNat 64 0x80) (SigGolfCandidate.Legacy.bytes sk)).writeBytesAsWords (BitVec.ofNat 64 0x44A0)
      (SigGolfCandidate.Legacy.bytes cache)).writeBytesAsWords
      (BitVec.ofNat 64 0x40) (SigGolfCandidate.Legacy.bytes m)).setReg .x2 (BitVec.ofNat 64 (dataBase image))

theorem initialState_eq (sk : SecretKey) (cache : Cache) (m : Message) :
    initialState submission .sign (sk, cache, m) = some (s0 sk cache m) := by
  unfold initialState
  rw [if_pos (by exact SigGolfCandidate.Radix27Images.sign_valid)]
  -- (`simp only [List.foldl]` or a direct `rfl` here make the elaborator unfold
  -- `writeBytesAsWords` over the 128 KiB cache; rewrite structurally instead)
  simp only [inputBuffers]
  rw [List.foldl_cons, List.foldl_cons, List.foldl_cons, List.foldl_nil,
    show submission.image .sign = image from rfl,
    show (submission.layout.secretKey, bytes sk).1 = 0x80 from rfl,
    show (submission.layout.cache, bytes cache).1 = 0x44A0 from rfl,
    show (submission.layout.message, bytes m).1 = 0x40 from rfl]
  dsimp only
  rfl

theorem s0_pc (sk : SecretKey) (cache : Cache) (m : Message) : (s0 sk cache m).pc = pcOf 0 := by
  rw [initialState_pc submission .sign (sk, cache, m) _ (initialState_eq sk cache m)]; rfl

theorem regs_writeBytesAsWords (l : List Byte) : ∀ (s : MachineState) (base : Word),
    (s.writeBytesAsWords base l).regs = s.regs := by
  induction l using WellFounded.induction (r := fun x y : List Byte => x.length < y.length) with
  | hwf => exact (measure List.length).wf
  | h l ih =>
    intro s base
    match l with
    | [] => simp [MachineState.writeBytesAsWords]
    | b :: bs =>
      unfold MachineState.writeBytesAsWords
      simp only
      rw [ih _ (by simp only [List.length_drop, List.length_cons]; omega)]
      rfl

theorem s0_getReg (sk : SecretKey) (cache : Cache) (m : Message) (r : Reg) (hr : r ≠ .x2) :
    (s0 sk cache m).getReg r = 0 := by
  unfold s0
  dsimp only
  rw [MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm hr)]
  unfold MachineState.getReg
  rw [regs_writeBytesAsWords, regs_writeBytesAsWords, regs_writeBytesAsWords, regs_writeBytesAsWords]
  cases r <;> rfl

theorem image_data : image.data = [] := by kernel_rfl

theorem length_bytes {n : Nat} (x : Bytes n) : (SigGolfCandidate.Legacy.bytes x).length = n := by
  simp [SigGolfCandidate.Legacy.bytes]

/-- Bytes of the initial memory. -/
theorem s0_getByte (sk : SecretKey) (cache : Cache) (m : Message) (a : Nat) (ha : a < 2 ^ 64) :
    (s0 sk cache m).getByte (BitVec.ofNat 64 a) =
      if 0x40 ≤ a ∧ a < 0x60 then (SigGolfCandidate.Legacy.bytes m).getD (a - 0x40) 0
      else if 0x44A0 ≤ a ∧ a < 0x44A0 + 131072 then (SigGolfCandidate.Legacy.bytes cache).getD (a - 0x44A0) 0
      else if 0x80 ≤ a ∧ a < 0xA0 then (SigGolfCandidate.Legacy.bytes sk).getD (a - 0x80) 0
      else 0 := by
  unfold s0
  simp only [getByte_setReg, image_data]
  have L1 : (SigGolfCandidate.Legacy.bytes m).length = 32 := length_bytes m
  have L2 : (SigGolfCandidate.Legacy.bytes cache).length = 131072 := length_bytes cache
  have L3 : (SigGolfCandidate.Legacy.bytes sk).length = 32 := length_bytes sk
  rw [getByte_writeBytesAsWords _ _ _ _ (by decide) (by rw [L1]; norm_num) ha, L1]
  by_cases h1 : 0x40 ≤ a ∧ a < 0x60
  · rw [if_pos (by omega), if_pos h1]
  rw [if_neg (by omega), if_neg h1, getByte_writeBytesAsWords _ _ _ _ (by decide)
    (by rw [L2]; norm_num) ha, L2]
  by_cases h2 : 0x44A0 ≤ a ∧ a < 0x44A0 + 131072
  · rw [if_pos (by omega), if_pos h2]
  rw [if_neg (by omega), if_neg h2, getByte_writeBytesAsWords _ _ _ _ (by decide)
    (by rw [L3]; norm_num) ha, L3]
  by_cases h3 : 0x80 ≤ a ∧ a < 0xA0
  · rw [if_pos (by omega), if_pos h3]
  rw [if_neg (by omega), if_neg h3]
  simp [MachineState.writeBytesAsWords, MachineState.getByte, MachineState.getMem, extractByte]

/-- A dword from its bytes. -/
theorem getMem_of_bytes (t : MachineState) (A : Nat) (hA : A % 8 = 0) (hA' : A + 8 < 2 ^ 64) :
    t.getMem (BitVec.ofNat 64 A) =
      BitVec.ofNat 64 (leNat ((List.range 8).map fun j => t.getByte (BitVec.ofNat 64 (A + j)))) := by
  have : (List.range 8).map (fun j => t.getByte (BitVec.ofNat 64 (A + j))) =
      bytesOfWord (t.getMem (BitVec.ofNat 64 A)) := by
    unfold bytesOfWord
    apply List.map_congr_left
    intro j hj
    have hj' : j < 8 := List.mem_range.mp hj
    simp only [MachineState.getByte]
    rw [byteOffset_ofNat (by omega), show BitVec.ofNat 64 (A + j) = BitVec.ofNat 64 (A + j) from rfl]
    have : alignToDword (BitVec.ofNat 64 (A + j)) = BitVec.ofNat 64 A := by
      rw [← alignToDword_ofNat_aligned (by omega) hA, alignToDword_ofNat_eq (by omega) (by omega)]
      omega
    rw [this, show (A + j) % 8 = j by omega]
    apply BitVec.eq_of_toNat_eq
    simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth,
      BitVec.toNat_ushiftRight, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
    rw [Nat.mul_comm j 8]
  rw [this, leNat_bytesOfWord, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- `readWords` of a region whose bytes are `l`. -/
theorem readWords_of_bytes (t : MachineState) (A : Nat) (l : List Byte) (n : Nat)
    (hl : l.length = 8 * n) (hA : A % 8 = 0) (hA' : A + 8 * n + 8 < 2 ^ 64)
    (hb : ∀ j < 8 * n, t.getByte (BitVec.ofNat 64 (A + j)) = l.getD j 0) :
    t.readWords (BitVec.ofNat 64 A) n = wordsOf l := by
  induction n generalizing A l with
  | zero => simp at hl; subst hl; rw [wordsOf_nil]; rfl
  | succ n ih =>
    have h8 : 8 ≤ l.length := by omega
    rw [readWords_ofNat_succ, ← List.take_append_drop 8 l, wordsOf_append _ _ (by simp; omega),
      wordsOf_eight _ (by simp; omega), ih (A + 8) (l.drop 8) (by simp; omega) (by omega) (by omega)]
    · rw [getMem_of_bytes t A hA (by omega)]
      congr 3
      apply List.ext_getElem (by simp; omega)
      intro j h1 h2
      simp only [List.getElem_map, List.getElem_range]
      simp at h1
      rw [hb j (by omega), List.getD_eq_getElem?_getD, List.getElem_take,
        List.getElem?_eq_getElem (by omega)]
      rfl
    · intro j hj
      rw [show A + 8 + j = A + (8 + j) by ring, hb (8 + j) (by omega)]
      simp [List.getD_eq_getElem?_getD]

theorem s0_readWords_sk (sk : SecretKey) (cache : Cache) (m : Message) :
    (s0 sk cache m).readWords (BitVec.ofNat 64 0x80) 4 = wordsOf (toList sk) := by
  apply readWords_of_bytes _ _ _ _ (by simp [toList, SigGolfCandidate.Legacy.bytes]) (by norm_num) (by norm_num)
  intro j hj
  rw [s0_getByte _ _ _ _ (by omega), if_neg (by omega), if_neg (by omega),
    if_pos (by omega)]
  simp [toList]

theorem s0_readWords_msg (sk : SecretKey) (cache : Cache) (m : Message) :
    (s0 sk cache m).readWords (BitVec.ofNat 64 0x40) 4 = wordsOf (toList m) := by
  apply readWords_of_bytes _ _ _ _ (by simp [toList, SigGolfCandidate.Legacy.bytes]) (by norm_num) (by norm_num)
  intro j hj
  rw [s0_getByte _ _ _ _ (by omega), if_pos (by omega)]
  simp [toList]

/-- The initial memory is zero outside the message, secret key and cache. -/
theorem s0_zero (sk : SecretKey) (cache : Cache) (m : Message) (A : Nat) (hA : A % 8 = 0)
    (hA' : A + 8 < 2 ^ 64)
    (hout : A + 8 ≤ 0x40 ∨ (0x60 ≤ A ∧ A + 8 ≤ 0x80) ∨ (0xA0 ≤ A ∧ A + 8 ≤ 0x44A0) ∨ 0x244A0 ≤ A) :
    (s0 sk cache m).getMem (BitVec.ofNat 64 A) = 0 := by
  rw [getMem_of_bytes _ A hA hA']
  have : (List.range 8).map (fun j => (s0 sk cache m).getByte (BitVec.ofNat 64 (A + j))) =
      List.replicate 8 0 := by
    apply List.ext_getElem (by simp)
    intro j h1 h2
    simp only [List.getElem_map, List.getElem_range, List.getElem_replicate]
    simp at h1
    rw [s0_getByte _ _ _ _ (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega)]
  rw [this]; rfl

end SigGolfCandidate.Radix27Sign

namespace SigGolfCandidate.Radix27Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref SigGolfCandidate.Mem

theorem getD_slice (l : List Byte) (off len j : Nat) (hj : j < len) (hl : off + len ≤ l.length) :
    (slice l off len).getD j 0 = l.getD (off + j) 0 := by
  simp only [slice, List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop]
  rw [if_pos hj]

/-- The initial cache words: `8 n` bytes at cache offset `off` (8-aligned). -/
theorem s0_readWords_cache (sk : SecretKey) (cache : Cache) (m : Message) (off n : Nat)
    (h8 : off % 8 = 0) (hn : off + 8 * n ≤ 131072) :
    (s0 sk cache m).readWords (BitVec.ofNat 64 (0x44A0 + off)) n =
      wordsOf (slice (toList cache) off (8 * n)) := by
  have hlen : (toList cache).length = 131072 := by simp [toList, SigGolfCandidate.Legacy.bytes]; rfl
  apply readWords_of_bytes _ _ _ _ (by simp [slice, hlen]; omega) (by omega) (by omega)
  intro j hj
  rw [s0_getByte _ _ _ _ (by omega), if_neg (by omega), if_pos (by omega),
    getD_slice _ _ _ _ hj (by rw [hlen]; omega), show 0x44A0 + off + j - 0x44A0 = off + j by omega]
  rfl

end SigGolfCandidate.Radix27Sign



end


section -- SignClone13.Mac

/-! ### cloned Mac -/

/-!
# The cache MAC: hash input and tag comparison (byte ↔ dword lemmas)

* `words_macInput` : the padded MAC input as dwords (`tw_mac | P | S | region | 0^32`).
* `answerBytes_32` / `toList_tag` : a 256-bit answer as four dwords.
* `tag_eq_iff` : a 32-byte tag equals the answer iff the four dwords agree.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace SigGolfCandidate.Radix27Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref SigGolfCandidate.Mem

theorem words_macInput (S region : List Byte) (hS : S.length = 32) (hR : region.length = 65504) :
    padBlocks (macInput S region).length = 1024 ∧
    wordsOf (padTo64 (macInput S region)) =
      twWords 14 0 0 0 0 ++ [0, 0] ++ wordsOf S ++ wordsOf region ++ [0, 0, 0, 0] := by
  obtain ⟨h1, h2⟩ := padTo64_eq (macInput S region) 1024 (by simp [macInput, hS, hR])
    (by simp [macInput, hS, hR])
  refine ⟨h1, ?_⟩
  rw [h2, macInput, wordsOf_thInput_pad]
  simp only [length_thInput, length_tweak, List.length_append, hS, hR]
  rw [List.append_assoc S, wordsOf_append _ _ (by omega), wordsOf_append _ _ (by omega),
    show 64 * (1024 + 1) - (16 + 16 + (32 + 65504)) = 8 * 4 from rfl, wordsOf_zeros]
  simp

theorem answerBytes_32 (a : BitVec 256) :
    answerBytes 32 a = bytesOfWord (a.extractLsb' 0 64) ++ bytesOfWord (a.extractLsb' 64 64) ++
      bytesOfWord (a.extractLsb' 128 64) ++ bytesOfWord (a.extractLsb' 192 64) := by
  unfold answerBytes bytesOfWord
  simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, List.map_append, List.append_assoc]
  simp only [extractLsb'_extractLsb' _ _ _ (by norm_num : (0 : Nat) < 8),
    extractLsb'_extractLsb' _ _ _ (by norm_num : (1 : Nat) < 8),
    extractLsb'_extractLsb' _ _ _ (by norm_num : (2 : Nat) < 8),
    extractLsb'_extractLsb' _ _ _ (by norm_num : (3 : Nat) < 8),
    extractLsb'_extractLsb' _ _ _ (by norm_num : (4 : Nat) < 8),
    extractLsb'_extractLsb' _ _ _ (by norm_num : (5 : Nat) < 8),
    extractLsb'_extractLsb' _ _ _ (by norm_num : (6 : Nat) < 8),
    extractLsb'_extractLsb' _ _ _ (by norm_num : (7 : Nat) < 8)]

theorem toList_tag (a : BitVec 256) :
    toList (n := 32) a = bytesOfWord (a.extractLsb' 0 64) ++ bytesOfWord (a.extractLsb' 64 64) ++
      bytesOfWord (a.extractLsb' 128 64) ++ bytesOfWord (a.extractLsb' 192 64) :=
  answerBytes_32 a

theorem bytesOfWord_inj {w w' : Word} (h : bytesOfWord w = bytesOfWord w') : w = w' := by
  apply BitVec.eq_of_toNat_eq
  rw [← leNat_bytesOfWord, ← leNat_bytesOfWord, h]

/-- An 8-byte list is the bytes of its dword. -/
theorem bytesOfWord_leNat (l : List Byte) (hl : l.length = 8) :
    bytesOfWord (BitVec.ofNat 64 (leNat l)) = l := by
  apply List.ext_getElem (by simp [hl])
  intro j hj1 hj2
  simp only [bytesOfWord, List.getElem_map, List.getElem_range]
  rw [extractByte_ofNat _ _ _ (by simp at hj1; omega)]
  apply BitVec.eq_of_toNat_eq
  rw [byte_toNat, leNat_div_mod, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj2]; rfl

/-- A 32-byte list from its four dwords. -/
theorem eq_of_words4 (l : List Byte) (hl : l.length = 32) (c0 c1 c2 c3 : Word)
    (hw : wordsOf l = [c0, c1, c2, c3]) :
    l = bytesOfWord c0 ++ bytesOfWord c1 ++ bytesOfWord c2 ++ bytesOfWord c3 := by
  have e : l = l.take 8 ++ (l.drop 8).take 8 ++ ((l.drop 8).drop 8).take 8 ++ ((l.drop 8).drop 8).drop 8 := by
    simp only [List.append_assoc, List.take_append_drop]
  rw [e, wordsOf_append _ _ (by simp; omega), wordsOf_append _ _ (by simp; omega),
    wordsOf_append _ _ (by simp; omega), wordsOf_eight _ (by simp; omega), wordsOf_eight _ (by simp; omega),
    wordsOf_eight _ (by simp; omega), wordsOf_eight _ (by simp; omega)] at hw
  simp only [List.cons_append, List.nil_append, List.cons.injEq, and_true] at hw
  obtain ⟨h0, h1, h2, h3⟩ := hw
  rw [e, ← h0, ← h1, ← h2, ← h3, bytesOfWord_leNat _ (by simp; omega), bytesOfWord_leNat _ (by simp; omega),
    bytesOfWord_leNat _ (by simp; omega), bytesOfWord_leNat _ (by simp; omega)]

theorem append4_inj {a0 a1 a2 a3 b0 b1 b2 b3 : Word}
    (h : bytesOfWord a0 ++ bytesOfWord a1 ++ bytesOfWord a2 ++ bytesOfWord a3 =
      bytesOfWord b0 ++ bytesOfWord b1 ++ bytesOfWord b2 ++ bytesOfWord b3) :
    a0 = b0 ∧ a1 = b1 ∧ a2 = b2 ∧ a3 = b3 := by
  simp only [List.append_assoc] at h
  obtain ⟨h0, h⟩ := List.append_inj h (by simp)
  obtain ⟨h1, h⟩ := List.append_inj h (by simp)
  obtain ⟨h2, h3⟩ := List.append_inj h (by simp)
  exact ⟨bytesOfWord_inj h0, bytesOfWord_inj h1, bytesOfWord_inj h2, bytesOfWord_inj h3⟩

/-- The tag comparison, dword by dword. -/
theorem tag_eq_iff (a : BitVec 256) (l : List Byte) (hl : l.length = 32) (c0 c1 c2 c3 : Word)
    (hw : wordsOf l = [c0, c1, c2, c3]) :
    toList (n := 32) a = l ↔ a.extractLsb' 0 64 = c0 ∧ a.extractLsb' 64 64 = c1 ∧
      a.extractLsb' 128 64 = c2 ∧ a.extractLsb' 192 64 = c3 := by
  rw [toList_tag, eq_of_words4 l hl c0 c1 c2 c3 hw]
  constructor
  · exact append4_inj
  · rintro ⟨rfl, rfl, rfl, rfl⟩; rfl

end SigGolfCandidate.Radix27Sign



end


section -- SignClone13.PackData

/-! ### cloned PackData -/
-- Generated by SigGolfCandidate/Sign/gen_pack.py. Do not edit.

namespace SigGolfCandidate.Radix27Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv

/-- For each signature dword `SIG + 2480 + 8 j`: (kind, lo, hi) stage addresses of its 4-byte
halves (kind 0: one `ld` of `lo`; 1: two `lwu`; 2: last dword, one `lwu`). -/
def packTab : List (Nat × Nat × Nat) := [
  (1, 2304, 2312), (1, 2316, 2320), (1, 2324, 2328), (1, 2332, 2336), (1, 2340, 2344), (1, 2348, 2352), (1, 2356, 2360), (1, 2364, 2368),
  (1, 2372, 2376), (1, 2380, 2384), (1, 2388, 2392), (1, 2396, 2400), (1, 2404, 2408), (1, 2412, 2416), (1, 2420, 2424), (1, 2428, 2432),
  (1, 2436, 2440), (1, 2444, 2448), (1, 2452, 2456), (1, 2460, 2464), (1, 2468, 2472), (1, 2476, 2480), (1, 2484, 2488), (1, 2492, 2496),
  (1, 2500, 2504), (1, 2508, 2512), (1, 2516, 2520), (1, 2524, 2528), (1, 2532, 2536), (1, 2540, 2544), (1, 2548, 2552), (1, 2556, 2560),
  (1, 2564, 2568), (1, 2572, 2576), (1, 2580, 2584), (1, 2588, 2592), (1, 2596, 2600), (1, 2604, 2608), (1, 2612, 2616), (1, 2620, 2624),
  (1, 2628, 2632), (1, 2636, 2640), (1, 2644, 2648), (1, 2652, 2656), (1, 2660, 2664), (1, 2668, 2672), (1, 2676, 2680), (1, 2684, 2688),
  (1, 2692, 2696), (1, 2700, 2704), (1, 2708, 2712), (1, 2716, 2720), (1, 2724, 2728), (1, 2732, 2736), (1, 2740, 2744), (1, 2748, 2752),
  (1, 2756, 2760), (1, 2764, 2768), (1, 2772, 2776), (1, 2780, 2784), (1, 2788, 2792), (1, 2796, 2800), (1, 2804, 2808), (1, 2812, 2816),
  (1, 2820, 2824), (1, 2828, 2832), (1, 2836, 2840), (1, 2844, 2848), (1, 2852, 2856), (1, 2860, 2864), (1, 2868, 2872), (1, 2876, 2880),
  (1, 2884, 2888), (1, 2892, 2896), (1, 2900, 2904), (1, 2908, 2912), (1, 2916, 2920), (1, 2924, 2928), (1, 2932, 2936), (1, 2940, 2944),
  (1, 2948, 2952), (1, 2956, 2960), (1, 2964, 2968), (1, 2972, 2976), (1, 2980, 2984), (1, 2988, 2992), (1, 2996, 3000), (1, 3004, 3008),
  (1, 3012, 3016), (1, 3020, 3024), (1, 3028, 3032), (1, 3036, 3040), (1, 3044, 3048), (1, 3052, 3056), (1, 3060, 3064), (1, 3068, 3072),
  (1, 3076, 3080), (1, 3084, 3088), (1, 3092, 3096), (1, 3100, 3104), (1, 3108, 3112), (1, 3116, 3120), (1, 3124, 3128), (1, 3132, 3136),
  (1, 3140, 3144), (1, 3148, 3152), (1, 3156, 3160), (0, 3168, 3172), (0, 3176, 3180), (0, 3184, 3188), (0, 3192, 3196), (0, 3200, 3204),
  (0, 3208, 3212), (0, 3216, 3220), (0, 3224, 3228), (0, 3232, 3236), (0, 3240, 3244), (0, 3248, 3252), (0, 3256, 3260), (0, 3264, 3268),
  (0, 3272, 3276), (0, 3280, 3284), (0, 3288, 3292), (0, 3296, 3300), (0, 3304, 3308), (0, 3312, 3316), (0, 3320, 3324), (0, 3328, 3332),
  (0, 3336, 3340), (0, 3344, 3348), (0, 3352, 3356), (0, 3360, 3364), (0, 3368, 3372), (0, 3376, 3380), (0, 3384, 3388), (0, 3392, 3396),
  (0, 3400, 3404), (0, 3408, 3412), (0, 3416, 3420), (0, 3424, 3428), (0, 3432, 3436), (0, 3440, 3444), (0, 3448, 3452), (0, 3456, 3460),
  (0, 3464, 3468), (0, 3472, 3476), (0, 3480, 3484), (0, 3488, 3492), (0, 3496, 3500), (0, 3504, 3508), (0, 3512, 3516), (0, 3520, 3524),
  (0, 3528, 3532), (0, 3536, 3540), (0, 3544, 3548), (0, 3552, 3556), (0, 3560, 3564), (0, 3568, 3572), (0, 3576, 3580), (0, 3584, 3588),
  (0, 3592, 3596), (0, 3600, 3604), (0, 3608, 3612), (0, 3616, 3620), (0, 3624, 3628), (0, 3632, 3636), (0, 3640, 3644), (0, 3648, 3652),
  (0, 3656, 3660), (0, 3664, 3668), (0, 3672, 3676), (0, 3680, 3684), (0, 3688, 3692), (0, 3696, 3700), (0, 3704, 3708), (0, 3712, 3716),
  (0, 3720, 3724), (0, 3728, 3732), (0, 3736, 3740), (0, 3744, 3748), (0, 3752, 3756), (0, 3760, 3764), (0, 3768, 3772), (0, 3776, 3780),
  (0, 3784, 3788), (0, 3792, 3796), (0, 3800, 3804), (0, 3808, 3812), (0, 3816, 3820), (0, 3824, 3828), (0, 3832, 3836), (0, 3840, 3844),
  (0, 3848, 3852), (0, 3856, 3860), (0, 3864, 3868), (0, 3872, 3876), (0, 3880, 3884), (0, 3888, 3892), (0, 3896, 3900), (0, 3904, 3908),
  (0, 3912, 3916), (0, 3920, 3924), (0, 3928, 3932), (1, 4016, 4024), (1, 4028, 4032), (1, 4036, 4040), (1, 4044, 4048), (1, 4052, 4056),
  (1, 4060, 4064), (1, 4068, 4072), (1, 4076, 4080), (1, 4084, 4088), (1, 4092, 4096), (1, 4100, 4104), (1, 4108, 4112), (1, 4116, 4120),
  (1, 4124, 4128), (1, 4132, 4136), (1, 4140, 4144), (1, 4148, 4152), (1, 4156, 4160), (1, 4164, 4168), (1, 4172, 4176), (1, 4180, 4184),
  (1, 4188, 4192), (1, 4196, 4200), (1, 4204, 4208), (1, 4212, 4216), (1, 4220, 4224), (1, 4228, 4232), (1, 4236, 4240), (1, 4244, 4248),
  (1, 4252, 4256), (1, 4260, 4264), (1, 4268, 4272), (1, 4276, 4280), (1, 4284, 4288), (1, 4292, 4296), (1, 4300, 4304), (1, 4308, 4312),
  (1, 4316, 4320), (1, 4324, 4328), (1, 4332, 4336), (1, 4340, 4344), (1, 4348, 4352), (1, 4356, 4360), (1, 4364, 4368), (1, 4372, 4376),
  (1, 4380, 4384), (1, 4388, 4392), (1, 4396, 4400), (1, 4404, 4408), (1, 4412, 4416), (1, 4420, 4424), (1, 4428, 4432), (1, 4436, 4440),
  (1, 4444, 4448), (1, 4452, 4456), (1, 4460, 4464), (1, 4468, 4472), (1, 4476, 4480), (1, 4484, 4488), (1, 4492, 4496), (1, 4500, 4504),
  (1, 4508, 4512), (1, 4516, 4520), (1, 4524, 4528), (1, 4532, 4536), (1, 4540, 4544), (1, 4548, 4552), (1, 4556, 4560), (1, 4564, 4568),
  (1, 4572, 4576), (1, 4580, 4584), (1, 4588, 4592), (1, 4596, 4600), (1, 4604, 4608), (1, 4612, 4616), (1, 4620, 4624), (1, 4628, 4632),
  (1, 4636, 4640), (1, 4644, 4648), (1, 4652, 4656), (1, 4660, 4664), (1, 4668, 4672), (1, 4676, 4680), (1, 4684, 4688), (1, 4692, 4696),
  (1, 4700, 4704), (1, 4708, 4712), (1, 4716, 4720), (1, 4724, 4728), (1, 4732, 4736), (1, 4740, 4744), (1, 4748, 4752), (1, 4756, 4760),
  (1, 4764, 4768), (1, 4772, 4776), (1, 4780, 4784), (1, 4788, 4872), (0, 4880, 4884), (0, 4888, 4892), (0, 4896, 4900), (0, 4904, 4908),
  (0, 4912, 4916), (0, 4920, 4924), (0, 4928, 4932), (0, 4936, 4940), (0, 4944, 4948), (0, 4952, 4956), (0, 4960, 4964), (0, 4968, 4972),
  (0, 4976, 4980), (0, 4984, 4988), (0, 4992, 4996), (0, 5000, 5004), (0, 5008, 5012), (0, 5016, 5020), (0, 5024, 5028), (0, 5032, 5036),
  (0, 5040, 5044), (0, 5048, 5052), (0, 5056, 5060), (0, 5064, 5068), (0, 5072, 5076), (0, 5080, 5084), (0, 5088, 5092), (0, 5096, 5100),
  (0, 5104, 5108), (0, 5112, 5116), (0, 5120, 5124), (0, 5128, 5132), (0, 5136, 5140), (0, 5144, 5148), (0, 5152, 5156), (0, 5160, 5164),
  (0, 5168, 5172), (0, 5176, 5180), (0, 5184, 5188), (0, 5192, 5196), (0, 5200, 5204), (0, 5208, 5212), (0, 5216, 5220), (0, 5224, 5228),
  (0, 5232, 5236), (0, 5240, 5244), (0, 5248, 5252), (0, 5256, 5260), (0, 5264, 5268), (0, 5272, 5276), (0, 5280, 5284), (0, 5288, 5292),
  (0, 5296, 5300), (0, 5304, 5308), (0, 5312, 5316), (0, 5320, 5324), (0, 5328, 5332), (0, 5336, 5340), (0, 5344, 5348), (0, 5352, 5356),
  (0, 5360, 5364), (0, 5368, 5372), (0, 5376, 5380), (0, 5384, 5388), (0, 5392, 5396), (0, 5400, 5404), (0, 5408, 5412), (0, 5416, 5420),
  (0, 5424, 5428), (0, 5432, 5436), (0, 5440, 5444), (0, 5448, 5452), (0, 5456, 5460), (0, 5464, 5468), (0, 5472, 5476), (0, 5480, 5484),
  (0, 5488, 5492), (0, 5496, 5500), (0, 5504, 5508), (0, 5512, 5516), (0, 5520, 5524), (0, 5528, 5532), (0, 5536, 5540), (0, 5544, 5548),
  (0, 5552, 5556), (0, 5560, 5564), (0, 5568, 5572), (0, 5576, 5580), (0, 5584, 5588), (0, 5592, 5596), (0, 5600, 5604), (0, 5608, 5612),
  (0, 5616, 5620), (0, 5624, 5628), (0, 5632, 5636), (0, 5640, 5644), (1, 5728, 5736), (1, 5740, 5744), (1, 5748, 5752), (1, 5756, 5760),
  (1, 5764, 5768), (1, 5772, 5776), (1, 5780, 5784), (1, 5788, 5792), (1, 5796, 5800), (1, 5804, 5808), (1, 5812, 5816), (1, 5820, 5824),
  (1, 5828, 5832), (1, 5836, 5840), (1, 5844, 5848), (1, 5852, 5856), (1, 5860, 5864), (1, 5868, 5872), (1, 5876, 5880), (1, 5884, 5888),
  (1, 5892, 5896), (1, 5900, 5904), (1, 5908, 5912), (1, 5916, 5920), (1, 5924, 5928), (1, 5932, 5936), (1, 5940, 5944), (1, 5948, 5952),
  (1, 5956, 5960), (1, 5964, 5968), (1, 5972, 5976), (1, 5980, 5984), (1, 5988, 5992), (1, 5996, 6000), (1, 6004, 6008), (1, 6012, 6016),
  (1, 6020, 6024), (1, 6028, 6032), (1, 6036, 6040), (1, 6044, 6048), (1, 6052, 6056), (1, 6060, 6064), (1, 6068, 6072), (1, 6076, 6080),
  (1, 6084, 6088), (1, 6092, 6096), (1, 6100, 6104), (1, 6108, 6112), (1, 6116, 6120), (1, 6124, 6128), (1, 6132, 6136), (1, 6140, 6144),
  (1, 6148, 6152), (1, 6156, 6160), (1, 6164, 6168), (1, 6172, 6176), (1, 6180, 6184), (1, 6188, 6192), (1, 6196, 6200), (1, 6204, 6208),
  (1, 6212, 6216), (1, 6220, 6224), (1, 6228, 6232), (1, 6236, 6240), (1, 6244, 6248), (1, 6252, 6256), (1, 6260, 6264), (1, 6268, 6272),
  (1, 6276, 6280), (1, 6284, 6288), (1, 6292, 6296), (1, 6300, 6304), (1, 6308, 6312), (1, 6316, 6320), (1, 6324, 6328), (1, 6332, 6336),
  (1, 6340, 6344), (1, 6348, 6352), (1, 6356, 6360), (1, 6364, 6368), (1, 6372, 6376), (1, 6380, 6384), (1, 6388, 6392), (1, 6396, 6400),
  (1, 6404, 6408), (1, 6412, 6416), (1, 6420, 6424), (1, 6428, 6432), (1, 6436, 6440), (1, 6444, 6448), (1, 6452, 6456), (1, 6460, 6464),
  (1, 6468, 6472), (1, 6476, 6480), (2, 6484, 0)]

/-- `LWU` as the executor evaluates it. -/
def lwuW (x : Word) (bo : Nat) : Word := LoadKind.fromWord .wu x bo

/-- The dword the pack writes for a table entry. -/
def packDW (t : MachineState) : Nat × Nat × Nat → Word
  | (0, lo, _) => t.getMem (BitVec.ofNat 64 lo)
  | (1, lo, hi) => lwuW (t.getMem (alignToDword (BitVec.ofNat 64 lo))) (byteOffset (BitVec.ofNat 64 lo)) +
      lwuW (t.getMem (alignToDword (BitVec.ofNat 64 hi))) (byteOffset (BitVec.ofNat 64 hi)) <<< ((32#64).toNat % 64)
  | (_, lo, _) => lwuW (t.getMem (alignToDword (BitVec.ofNat 64 lo))) (byteOffset (BitVec.ofNat 64 lo))

end SigGolfCandidate.Radix27Sign



end


section -- SignClone13.Bytes

/-! ### cloned Bytes -/

/-!
# Byte views of memory regions

* `bytesAt t a n` : the `n` bytes at `a`; `bytesAt_add` (split), `bytesAt_of_readWords` (an aligned
  region holding `wordsOf l` has bytes `l`), `readBuffer_bytesAt`.
* bytes of the pack's dwords (`extractByte_packDW`).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace SigGolfCandidate.Radix27Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref SigGolfCandidate.Mem

def bytesAt (t : MachineState) (a n : Nat) : List Byte :=
  (List.range n).map fun i => t.getByte (BitVec.ofNat 64 (a + i))

@[simp] theorem length_bytesAt (t : MachineState) (a n : Nat) : (bytesAt t a n).length = n := by
  simp [bytesAt]

theorem bytesAt_add (t : MachineState) (a n m : Nat) :
    bytesAt t a (n + m) = bytesAt t a n ++ bytesAt t (a + n) m := by
  unfold bytesAt
  rw [List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left; intro i _; simp [Function.comp, Nat.add_assoc]

theorem readBuffer_bytesAt (t : MachineState) (a n : Nat) :
    readBuffer t a n = ofList n (bytesAt t a n) := by
  rw [readBuffer_eq]; rfl

theorem extractByte_toNat' (w : Word) (b : Nat) :
    (extractByte w b).toNat = w.toNat / 2 ^ (8 * b) % 256 := by
  unfold extractByte
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow]
  rw [Nat.mul_comm b 8]

/-- Byte `i` of an aligned dword. -/
theorem getByte_aligned' (t : MachineState) (a i : Nat) (ha : a % 8 = 0) (hi : i < 8)
    (hb : a + 8 < 2 ^ 64) :
    t.getByte (BitVec.ofNat 64 (a + i)) = extractByte (t.getMem (BitVec.ofNat 64 a)) i := by
  simp only [MachineState.getByte]
  rw [byteOffset_ofNat (by omega), show (a + i) % 8 = i by omega]
  congr 2
  apply BitVec.eq_of_toNat_eq
  rw [alignToDword_toNat]; simp only [BitVec.toNat_ofNat]; omega

theorem bytesOfWord_extract (w : Word) (i : Nat) (hi : i < 8) :
    (bytesOfWord w)[i]'(by simp; omega) = extractByte w i := by
  simp only [bytesOfWord, List.getElem_map, List.getElem_range]
  apply BitVec.eq_of_toNat_eq
  rw [extractByte_toNat', BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]

/-- An aligned region holding the dwords `wordsOf l` has the bytes `l`. -/
theorem bytesAt_of_readWords (t : MachineState) : ∀ (k a : Nat) (l : List Byte),
    a % 8 = 0 → a + 8 * k + 8 < 2 ^ 64 → l.length = 8 * k →
    t.readWords (BitVec.ofNat 64 a) k = wordsOf l → bytesAt t a (8 * k) = l := by
  intro k
  induction k with
  | zero => intro a l _ _ hl _; simp at hl; subst hl; rfl
  | succ k ih =>
    intro a l ha hb hl hw
    have h8 : 8 ≤ l.length := by omega
    rw [readWords_ofNat_succ, ← List.take_append_drop 8 l, wordsOf_append _ _ (by simp; omega),
      wordsOf_eight _ (by simp; omega)] at hw
    simp only [List.cons_append, List.nil_append, List.cons.injEq] at hw
    rw [show 8 * (k + 1) = 8 + 8 * k by ring, bytesAt_add, ih (a + 8) (l.drop 8) (by omega) (by omega)
      (by simp; omega) hw.2]
    conv_rhs => rw [← List.take_append_drop 8 l]
    congr 1
    apply List.ext_getElem (by simp; omega)
    intro i h1 h2
    simp only [bytesAt, List.getElem_map, List.getElem_range]
    simp at h1
    rw [getByte_aligned' t a i ha h1 (by omega), hw.1]
    have hl8 : (l.take 8).length = 8 := by simp; omega
    have := val_eq_valOfWords
    rw [← bytesOfWord_extract _ i h1]
    have key : l.take 8 = bytesOfWord (BitVec.ofNat 64 (leNat (l.take 8))) := by
      apply List.ext_getElem (by simp [hl8])
      intro j hj1 hj2
      simp only [bytesOfWord, List.getElem_map, List.getElem_range]
      rw [extractByte_ofNat _ _ _ (by simp at hj2; omega)]
      apply BitVec.eq_of_toNat_eq
      rw [byte_toNat, leNat_div_mod, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj1]; rfl
    exact (List.getElem_of_eq key _).symm

end SigGolfCandidate.Radix27Sign

namespace SigGolfCandidate.Radix27Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref SigGolfCandidate.Mem

theorem lwuW_toNat (w : Word) (bo : Nat) :
    (lwuW w bo).toNat = w.toNat / 2 ^ (32 * (bo / 4)) % 2 ^ 32 := by
  simp only [lwuW, LoadKind.fromWord, extractWord32, BitVec.truncate_eq_setWidth,
    BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (by
    have := Nat.mod_lt (w.toNat / 2 ^ (bo / 4 * 32)) (show 2 ^ 32 > 0 by positivity); omega)]
  rw [Nat.mul_comm (bo / 4) 32]

theorem extractByte_lwuW (w : Word) (bo i : Nat) (hbo : bo = 0 ∨ bo = 4) (hi : i < 8) :
    extractByte (lwuW w bo) i = if i < 4 then extractByte w (bo + i) else 0 := by
  apply BitVec.eq_of_toNat_eq
  have hw := w.isLt
  rw [extractByte_toNat', lwuW_toNat]
  split
  · rw [extractByte_toNat']
    rcases hbo with rfl | rfl <;> interval_cases i <;> simp <;> omega
  · rcases hbo with rfl | rfl <;> interval_cases i <;> simp <;> omega

theorem extractByte_pair (w1 w2 : Word) (bo1 bo2 i : Nat) (h1 : bo1 = 0 ∨ bo1 = 4)
    (h2 : bo2 = 0 ∨ bo2 = 4) (hi : i < 8) :
    extractByte (lwuW w1 bo1 + lwuW w2 bo2 <<< ((32#64).toNat % 64)) i =
      if i < 4 then extractByte w1 (bo1 + i) else extractByte w2 (bo2 + (i - 4)) := by
  apply BitVec.eq_of_toNat_eq
  have hw1 := w1.isLt
  have hw2 := w2.isLt
  have ha := lwuW_toNat w1 bo1
  have hb := lwuW_toNat w2 bo2
  have hsum : (lwuW w1 bo1 + lwuW w2 bo2 <<< ((32#64).toNat % 64)).toNat =
      (lwuW w1 bo1).toNat + 2 ^ 32 * (lwuW w2 bo2).toNat := by
    rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, show (32#64).toNat % 64 = 32 from rfl,
      Nat.shiftLeft_eq]
    have := Nat.mod_lt (w1.toNat / 2 ^ (32 * (bo1 / 4))) (show 2 ^ 32 > 0 by positivity)
    have := Nat.mod_lt (w2.toNat / 2 ^ (32 * (bo2 / 4))) (show 2 ^ 32 > 0 by positivity)
    rw [ha, hb]; omega
  rw [extractByte_toNat', hsum, ha, hb]
  split
  · rw [extractByte_toNat']
    rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;> interval_cases i <;> simp <;> omega
  · rw [extractByte_toNat']
    rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;> interval_cases i <;> simp <;> omega

end SigGolfCandidate.Radix27Sign



end


section -- SignClone13.PackStep

/-! ### cloned PackStep -/

/-!
# The pack, chunk by chunk

The pack (instructions 614 .. 3394) is split into chunks (`PackC*.lean`, one symbolic block and
one file each, to keep the kernel's memory per file small). `PackStep a b f c n` says: from pc
`a`, `n` straight-line steps reach pc `b`, write the signature dwords `f .. f + c - 1`
(`packD + 8 j`) as `packDW t` of the table entries, and nothing else. `packStep_of` builds it
from a symbolic block, `PackStep.comp` chains chunks (the sources, below `0x2650`, are not
written by the pack).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace SigGolfCandidate.Radix27Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Mem

/-- Destination of the pack: `SIG + 2480`. -/
abbrev packD : Nat := 0x2650 + 2480

/-- All sources lie below the signature buffer (checked by the kernel). -/
theorem packTab_src_ok : packTab.all (fun e => decide (e.2.1 < 0x2650 ∧ e.2.2 < 0x2650)) = true := by
  decide +kernel

theorem packTab_src (e : Nat × Nat × Nat) (he : e ∈ packTab) : e.2.1 < 0x2650 ∧ e.2.2 < 0x2650 := by
  have := List.all_eq_true.mp packTab_src_ok e he
  simpa using this

def PackStep (a b f c n : Nat) : Prop :=
  ∀ t : MachineState, t.pc = pcOf a → ∃ u, Steps image t n n u ∧ u.pc = pcOf b ∧
    u.readWords (BitVec.ofNat 64 (packD + 8 * f)) c = ((packTab.drop f).take c).map (packDW t) ∧
    Frame t u (fun x => packD + 8 * f ≤ x ∧ x < packD + 8 * (f + c))

theorem packStep_of {code : List (BitVec 32)} {a b f c n fuel : Nat} {r : Result}
    (hrun : symRun { noAlias := true } code (pcOf a) fuel = some r) (hcode : CodeAt image (pcOf a) code)
    (hobl : r.st.obl = []) (hpc : ∀ t : MachineState, (r.toState t).pc = pcOf b)
    (hs : r.steps = n) (hc : r.cycles = n)
    (hw : ∀ t : MachineState, (r.toState t).readWords (BitVec.ofNat 64 (packD + 8 * f)) c =
      ((packTab.drop f).take c).map (packDW t))
    (haddr : ∀ t : MachineState, r.st.mem.map (fun p => p.1.eval t) =
      ((List.range c).map (fun i => BitVec.ofNat 64 (packD + 8 * f + 8 * i))).reverse)
    (hb : packD + 8 * (f + c) < 2 ^ 64) : PackStep a b f c n := by
  intro t ht
  have hS := symRun_sound hrun hcode t ht (by simp only [Result.obligs, hobl, Oblig.all])
  rw [hs, hc] at hS
  refine ⟨_, hS, hpc t, hw t, frame_toState r t _ ?_⟩
  intro x hx hW p hp heq
  have hm : p.1.eval t ∈ r.st.mem.map (fun p => p.1.eval t) := List.mem_map_of_mem hp
  rw [haddr t, List.mem_reverse, List.mem_map] at hm
  obtain ⟨i, hi, hi'⟩ := hm
  rw [List.mem_range] at hi
  rw [← hi'] at heq
  have := congrArg BitVec.toNat heq
  simp only [BitVec.toNat_ofNat] at this
  rw [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt (by omega)] at this
  omega

theorem getMem_align_frame {t u : MachineState} {W : Nat → Prop} (h : Frame t u W) (x : Nat)
    (hx : x < 2 ^ 64) (hW : ¬ W (x / 8 * 8)) :
    u.getMem (alignToDword (BitVec.ofNat 64 x)) = t.getMem (alignToDword (BitVec.ofNat 64 x)) := by
  have : alignToDword (BitVec.ofNat 64 x) = BitVec.ofNat 64 (x / 8 * 8) := by
    apply BitVec.eq_of_toNat_eq
    rw [alignToDword_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := x) hx,
      Nat.mod_eq_of_lt (a := x / 8 * 8) (by omega)]
    omega
  rw [this]; exact h.getMem (by omega) hW

theorem packDW_frame {t u : MachineState} {W : Nat → Prop} (h : Frame t u W)
    (hW : ∀ x, x < 0x2650 → ¬ W x) (e : Nat × Nat × Nat) (he : e ∈ packTab) :
    packDW u e = packDW t e := by
  obtain ⟨h1, h2⟩ := packTab_src e he
  obtain ⟨k, lo, hi⟩ := e
  simp only at h1 h2
  have g1 := getMem_align_frame h lo (by omega) (hW _ (by omega))
  have g2 := getMem_align_frame h hi (by omega) (hW _ (by omega))
  rcases k with _ | _ | k
  · have : alignToDword (BitVec.ofNat 64 lo) = BitVec.ofNat 64 (lo / 8 * 8) := by
      apply BitVec.eq_of_toNat_eq
      rw [alignToDword_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := lo) (by omega),
        Nat.mod_eq_of_lt (a := lo / 8 * 8) (by omega)]
      omega
    simp only [packDW]
    by_cases h8 : lo % 8 = 0
    · rw [show lo = lo / 8 * 8 by omega]; exact h.getMem (by omega) (hW _ (by omega))
    · exact h.getMem (by omega) (hW _ (by omega))
  · simp only [packDW, g1, g2]
  · simp only [packDW, g1]

theorem PackStep.comp {a b d f c c' n n' : Nat} (h1 : PackStep a b f c n)
    (h2 : PackStep b d (f + c) c' n') (hb : packD + 8 * (f + c + c') < 2 ^ 64) :
    PackStep a d f (c + c') (n + n') := by
  intro t ht
  obtain ⟨u, hs1, pc1, w1, f1⟩ := h1 t ht
  obtain ⟨v, hs2, pc2, w2, f2⟩ := h2 u pc1
  refine ⟨v, hs1.trans hs2, pc2, ?_, f1.trans' f2 (fun x hx => by omega)⟩
  rw [readWords_ofNat_add, List.take_add, List.map_append, List.drop_drop,
    show packD + 8 * f + 8 * c = packD + 8 * (f + c) by ring, w2,
    f2.readWords _ _ (by omega) (fun i hi => by omega), w1]
  congr 1
  apply List.map_congr_left
  intro e he
  exact packDW_frame f1 (fun x hx h => by simp only [packD] at h; omega)
    e (List.mem_of_mem_drop (List.mem_of_mem_take he))

end SigGolfCandidate.Radix27Sign



end


section -- SignClone13.PackC0

/-! ### cloned PackC0 -/
-- Generated by SigGolfCandidate/Sign/gen_code.py. Do not edit.

namespace SigGolfCandidate.Radix27Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv

/-! Pack chunk 0: instructions 675 .. 1113, signature dwords 0 .. 79. -/

set_option maxRecDepth 100000

sym_block blk675 := symRun { noAlias := true } seg675 (pcOf 675) 440

kernel_theorem blk675_pc : ∀ t : MachineState, (blk675.res.toState t).pc = pcOf 1114
kernel_theorem blk675_addrs : ∀ t : MachineState, blk675.res.st.mem.map (fun p => p.1.eval t) =
    ((List.range 80).map (fun i => BitVec.ofNat 64 (packD + 8 * 0 + 8 * i))).reverse
kernel_theorem blk675_words : ∀ t : MachineState,
    (blk675.res.toState t).readWords (BitVec.ofNat 64 (packD + 8 * 0)) 80 =
      ((packTab.drop 0).take 80).map (packDW t)

theorem packStep_675 : PackStep 675 1114 0 80 439 :=
  packStep_of blk675 codeAt_675 rfl blk675_pc rfl rfl blk675_words blk675_addrs (by norm_num)

end SigGolfCandidate.Radix27Sign



end


section -- SignClone13.PackC1

/-! ### cloned PackC1 -/
-- Generated by SigGolfCandidate/Sign/gen_code.py. Do not edit.

namespace SigGolfCandidate.Radix27Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv

/-! Pack chunk 1: instructions 1114 .. 1394, signature dwords 80 .. 159. -/

set_option maxRecDepth 100000

sym_block blk1114 := symRun { noAlias := true } seg1114 (pcOf 1114) 282

kernel_theorem blk1114_pc : ∀ t : MachineState, (blk1114.res.toState t).pc = pcOf 1395
kernel_theorem blk1114_addrs : ∀ t : MachineState, blk1114.res.st.mem.map (fun p => p.1.eval t) =
    ((List.range 80).map (fun i => BitVec.ofNat 64 (packD + 8 * 80 + 8 * i))).reverse
kernel_theorem blk1114_words : ∀ t : MachineState,
    (blk1114.res.toState t).readWords (BitVec.ofNat 64 (packD + 8 * 80)) 80 =
      ((packTab.drop 80).take 80).map (packDW t)

theorem packStep_1114 : PackStep 1114 1395 80 80 281 :=
  packStep_of blk1114 codeAt_1114 rfl blk1114_pc rfl rfl blk1114_words blk1114_addrs (by norm_num)

end SigGolfCandidate.Radix27Sign



end


section -- SignClone13.PackC2

/-! ### cloned PackC2 -/
-- Generated by SigGolfCandidate/Sign/gen_code.py. Do not edit.

namespace SigGolfCandidate.Radix27Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv

/-! Pack chunk 2: instructions 1395 .. 1705, signature dwords 160 .. 239. -/

set_option maxRecDepth 100000

sym_block blk1395 := symRun { noAlias := true } seg1395 (pcOf 1395) 312

kernel_theorem blk1395_pc : ∀ t : MachineState, (blk1395.res.toState t).pc = pcOf 1706
kernel_theorem blk1395_addrs : ∀ t : MachineState, blk1395.res.st.mem.map (fun p => p.1.eval t) =
    ((List.range 80).map (fun i => BitVec.ofNat 64 (packD + 8 * 160 + 8 * i))).reverse
kernel_theorem blk1395_words : ∀ t : MachineState,
    (blk1395.res.toState t).readWords (BitVec.ofNat 64 (packD + 8 * 160)) 80 =
      ((packTab.drop 160).take 80).map (packDW t)

theorem packStep_1395 : PackStep 1395 1706 160 80 311 :=
  packStep_of blk1395 codeAt_1395 rfl blk1395_pc rfl rfl blk1395_words blk1395_addrs (by norm_num)

end SigGolfCandidate.Radix27Sign



end


section -- SignClone13.PackC3

/-! ### cloned PackC3 -/
-- Generated by SigGolfCandidate/Sign/gen_code.py. Do not edit.

namespace SigGolfCandidate.Radix27Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv

/-! Pack chunk 3: instructions 1706 .. 2085, signature dwords 240 .. 319. -/

set_option maxRecDepth 100000

sym_block blk1706 := symRun { noAlias := true } seg1706 (pcOf 1706) 381

kernel_theorem blk1706_pc : ∀ t : MachineState, (blk1706.res.toState t).pc = pcOf 2086
kernel_theorem blk1706_addrs : ∀ t : MachineState, blk1706.res.st.mem.map (fun p => p.1.eval t) =
    ((List.range 80).map (fun i => BitVec.ofNat 64 (packD + 8 * 240 + 8 * i))).reverse
kernel_theorem blk1706_words : ∀ t : MachineState,
    (blk1706.res.toState t).readWords (BitVec.ofNat 64 (packD + 8 * 240)) 80 =
      ((packTab.drop 240).take 80).map (packDW t)

theorem packStep_1706 : PackStep 1706 2086 240 80 380 :=
  packStep_of blk1706 codeAt_1706 rfl blk1706_pc rfl rfl blk1706_words blk1706_addrs (by norm_num)

end SigGolfCandidate.Radix27Sign



end


section -- SignClone13.PackC4

/-! ### cloned PackC4 -/
-- Generated by SigGolfCandidate/Sign/gen_code.py. Do not edit.

namespace SigGolfCandidate.Radix27Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv

/-! Pack chunk 4: instructions 2086 .. 2297, signature dwords 320 .. 399. -/

set_option maxRecDepth 100000

sym_block blk2086 := symRun { noAlias := true } seg2086 (pcOf 2086) 213

kernel_theorem blk2086_pc : ∀ t : MachineState, (blk2086.res.toState t).pc = pcOf 2298
kernel_theorem blk2086_addrs : ∀ t : MachineState, blk2086.res.st.mem.map (fun p => p.1.eval t) =
    ((List.range 80).map (fun i => BitVec.ofNat 64 (packD + 8 * 320 + 8 * i))).reverse
kernel_theorem blk2086_words : ∀ t : MachineState,
    (blk2086.res.toState t).readWords (BitVec.ofNat 64 (packD + 8 * 320)) 80 =
      ((packTab.drop 320).take 80).map (packDW t)

theorem packStep_2086 : PackStep 2086 2298 320 80 212 :=
  packStep_of blk2086 codeAt_2086 rfl blk2086_pc rfl rfl blk2086_words blk2086_addrs (by norm_num)

end SigGolfCandidate.Radix27Sign



end


section -- SignClone13.PackC5

/-! ### cloned PackC5 -/
-- Generated by SigGolfCandidate/Sign/gen_code.py. Do not edit.

namespace SigGolfCandidate.Radix27Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv

/-! Pack chunk 5: instructions 2298 .. 2737, signature dwords 400 .. 479. -/

set_option maxRecDepth 100000

sym_block blk2298 := symRun { noAlias := true } seg2298 (pcOf 2298) 441

kernel_theorem blk2298_pc : ∀ t : MachineState, (blk2298.res.toState t).pc = pcOf 2738
kernel_theorem blk2298_addrs : ∀ t : MachineState, blk2298.res.st.mem.map (fun p => p.1.eval t) =
    ((List.range 80).map (fun i => BitVec.ofNat 64 (packD + 8 * 400 + 8 * i))).reverse
kernel_theorem blk2298_words : ∀ t : MachineState,
    (blk2298.res.toState t).readWords (BitVec.ofNat 64 (packD + 8 * 400)) 80 =
      ((packTab.drop 400).take 80).map (packDW t)

theorem packStep_2298 : PackStep 2298 2738 400 80 440 :=
  packStep_of blk2298 codeAt_2298 rfl blk2298_pc rfl rfl blk2298_words blk2298_addrs (by norm_num)

end SigGolfCandidate.Radix27Sign



end


section -- SignClone13.PackC6

/-! ### cloned PackC6 -/
-- Generated by SigGolfCandidate/Sign/gen_code.py. Do not edit.

namespace SigGolfCandidate.Radix27Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv

/-! Pack chunk 6: instructions 2738 .. 2797, signature dwords 480 .. 490. -/

set_option maxRecDepth 100000

sym_block blk2738 := symRun { noAlias := true } seg2738 (pcOf 2738) 61

kernel_theorem blk2738_pc : ∀ t : MachineState, (blk2738.res.toState t).pc = pcOf 2798
kernel_theorem blk2738_addrs : ∀ t : MachineState, blk2738.res.st.mem.map (fun p => p.1.eval t) =
    ((List.range 11).map (fun i => BitVec.ofNat 64 (packD + 8 * 480 + 8 * i))).reverse
kernel_theorem blk2738_words : ∀ t : MachineState,
    (blk2738.res.toState t).readWords (BitVec.ofNat 64 (packD + 8 * 480)) 11 =
      ((packTab.drop 480).take 11).map (packDW t)

theorem packStep_2738 : PackStep 2738 2798 480 11 60 :=
  packStep_of blk2738 codeAt_2738 rfl blk2738_pc rfl rfl blk2738_words blk2738_addrs (by norm_num)

end SigGolfCandidate.Radix27Sign



end


section -- SignClone13.PackRun

/-! ### cloned PackRun -/
-- Generated by SigGolfCandidate/Sign/gen_code.py. Do not edit.

namespace SigGolfCandidate.Radix27Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv

/-- The whole pack (instructions 675 .. 2797). -/
theorem pack_run : PackStep 675 2798 0 491 2123 :=
  ((((((packStep_675.comp packStep_1114 (by norm_num)).comp packStep_1395 (by norm_num)).comp packStep_1706 (by norm_num)).comp packStep_2086 (by norm_num)).comp packStep_2298 (by norm_num)).comp packStep_2738 (by norm_num))

-- The final HALT.
sym_block blk2798 := symRun { noAlias := true } seg2798 (pcOf 2798) 2

end SigGolfCandidate.Radix27Sign



end
