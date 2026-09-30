import SigGolfCandidate.Sign.Init

/-!
# Byte views of memory regions

* `bytesAt t a n` : the `n` bytes at `a`; `bytesAt_add` (split), `bytesAt_of_readWords` (an aligned
  region holding `wordsOf l` has bytes `l`), `readBuffer_bytesAt`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace SigGolfCandidate.Sign
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

end SigGolfCandidate.Sign

