import SigGolfCandidate.Verify.Mem
import Mathlib.Data.Nat.Bitwise

/-! # Bit-level arithmetic facts about the machine values -/

set_option linter.unusedSimpArgs false

namespace SigGolfCandidate.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

theorem replaceWord32_1_toNat (w : BitVec 64) (p : Nat) (hp : p < 2 ^ 32) :
    (replaceWord32 w 1 ((BitVec.ofNat 64 p).truncate 32)).toNat = w.toNat % 2 ^ 32 + 2 ^ 32 * p := by
  unfold replaceWord32
  have hm : (~~~(0xFFFFFFFF#64 <<< (1 * 32)) : BitVec 64) = BitVec.ofNat 64 (2 ^ 32 - 1) := by
    decide
  rw [hm, BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft]
  simp only [BitVec.toNat_ofNat, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth]
  have e1 : (2 ^ 32 - 1) % 2 ^ 64 = 2 ^ 32 - 1 := by norm_num
  have e2 : p % 2 ^ 64 % 2 ^ 32 = p := by omega
  have e3 : p % 2 ^ 64 * 2 ^ (1 * 32) % 2 ^ 64 = 2 ^ 32 * p := by
    rw [Nat.mod_eq_of_lt (by omega : p < 2 ^ 64)]; rw [Nat.mod_eq_of_lt (by norm_num; omega)]; ring
  rw [e1, e2, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftLeft_eq, e3]
  rw [Nat.or_comm, ← Nat.two_pow_add_eq_or_of_lt (Nat.mod_lt _ (by norm_num))]
  omega

/-- The merged tweak word of a chain step / node level. -/
theorem stMerge_eval (w : BitVec 64) (p lo : Nat) (hp : p < 2 ^ 32) (hw : w.toNat % 2 ^ 32 = lo) :
    StoreKind.merge .w w 4 (BitVec.ofNat 64 p) = BitVec.ofNat 64 (lo + 2 ^ 32 * p) := by
  apply BitVec.eq_of_toNat_eq
  simp only [StoreKind.merge]
  rw [show (4 : Nat) / 4 = 1 from rfl, replaceWord32_1_toNat w p hp, hw, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega)]

theorem stMerge_low (w : BitVec 64) (p : Nat) (hp : p < 2 ^ 32) :
    (StoreKind.merge .w w 4 (BitVec.ofNat 64 p)).toNat % 2 ^ 32 = w.toNat % 2 ^ 32 := by
  simp only [StoreKind.merge]
  rw [show (4 : Nat) / 4 = 1 from rfl, replaceWord32_1_toNat w p hp]
  omega

theorem geu_digit (D : BitVec 64) (r k : Nat) (hr : r ≤ 20) (hk : k < 8) :
    CmpOp.geu.eval (D <<< ((BitVec.ofNat 64 (61 - 3 * r)).toNat % 64)) (BitVec.ofNat 64 k <<< 61) =
      decide (k ≤ D.toNat / 8 ^ r % 8) := by
  simp only [CmpOp.eval, BitVec.ult, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  have hD := D.isLt
  rw [Nat.mod_eq_of_lt (by omega : 61 - 3 * r < 2 ^ 64), Nat.mod_eq_of_lt (by omega : 61 - 3 * r < 64),
    Nat.mod_eq_of_lt (by omega : k < 2 ^ 64)]
  have : k * 2 ^ 61 % 2 ^ 64 = k * 2 ^ 61 := Nat.mod_eq_of_lt (by omega)
  rw [this]
  interval_cases r <;> simp only [Bool.not_eq_eq_eq_not] <;>
    (simp only [Nat.reducePow, Nat.reduceSub, Nat.reduceMul] at *; rw [Bool.eq_iff_iff]; simp; omega)

theorem merge_w4_toNat (w v : BitVec 64) :
    (StoreKind.merge .w w 4 v).toNat = w.toNat % 2 ^ 32 + 2 ^ 32 * (v.toNat % 2 ^ 32) := by
  have := replaceWord32_1_toNat w (v.toNat % 2 ^ 32) (Nat.mod_lt _ (by decide))
  simp only [StoreKind.merge, show (4 : Nat) / 4 = 1 from rfl]
  have e : (BitVec.ofNat 64 (v.toNat % 2 ^ 32)).truncate 32 = v.truncate 32 := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_setWidth]
  rw [← e, this]

theorem land_split (n M w s : Nat) (hws : w ≤ s) :
    n &&& (2 ^ s * M + (2 ^ w - 1)) = 2 ^ s * ((n / 2 ^ s) &&& M) + n % 2 ^ w := by
  have hw : 2 ^ w - 1 < 2 ^ s := by
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) hws
    have : 0 < 2 ^ w := Nat.two_pow_pos _
    omega
  have hm : n % 2 ^ w < 2 ^ s := lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _))
    (Nat.pow_le_pow_right (by decide) hws)
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_land, Nat.testBit_two_pow_mul_add _ hw, Nat.testBit_two_pow_mul_add _ hm]
  split
  · rw [Nat.testBit_two_pow_sub_one, Nat.testBit_mod_two_pow]
    cases n.testBit j <;> simp
  · rw [Nat.testBit_land, Nat.testBit_div_two_pow, Nat.sub_add_cancel (by omega)]

theorem replaceWord32_0_toNat (w : BitVec 64) (v : BitVec 32) :
    (replaceWord32 w 0 v).toNat = w.toNat / 2 ^ 32 % 2 ^ 32 * 2 ^ 32 + v.toNat := by
  unfold replaceWord32
  have hm : (~~~(0xFFFFFFFF#64 <<< (0 * 32)) : BitVec 64) =
      BitVec.ofNat 64 (2 ^ 32 * (2 ^ 32 - 1) + (2 ^ 0 - 1)) := by decide
  rw [hm, BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft]
  simp only [BitVec.toNat_ofNat, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, Nat.zero_mul,
    Nat.shiftLeft_zero]
  have hv := v.isLt
  have hw := w.isLt
  rw [Nat.mod_eq_of_lt (show v.toNat < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show v.toNat < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show 2 ^ 32 * (2 ^ 32 - 1) + (2 ^ 0 - 1) < 2 ^ 64 by norm_num),
    land_split _ _ 0 32 (by decide), Nat.and_two_pow_sub_one_eq_mod, Nat.pow_zero, Nat.mod_one, Nat.add_zero,
    ← Nat.two_pow_add_eq_or_of_lt hv]
  ring

theorem merge_w0_toNat (w v : BitVec 64) :
    (StoreKind.merge .w w 0 v).toNat = w.toNat / 2 ^ 32 % 2 ^ 32 * 2 ^ 32 + v.toNat % 2 ^ 32 := by
  simp only [StoreKind.merge, show (0 : Nat) / 4 = 0 from rfl]
  rw [replaceWord32_0_toNat]
  simp [BitVec.toNat_setWidth]

theorem leNat_slice8 (l : List Byte) (off : Nat) (h : off + 4 ≤ l.length) :
    leNat (slice l off 8) = leNat (slice l off 4) + 2 ^ 32 * leNat (slice l (off + 4) 4) := by
  have : slice l off 8 = slice l off 4 ++ slice l (off + 4) 4 := by
    simp only [slice]
    rw [show (8 : Nat) = 4 + 4 from rfl, List.take_add, List.drop_drop, Nat.add_comm off 4]
  rw [this, leNat_append]
  have : (slice l off 4).length = 4 := by simp [slice]; omega
  rw [this]; norm_num

theorem witCounter_lt (wl : List Byte) (lay : Nat) : witCounter wl lay < 2 ^ 32 := by
  unfold witCounter
  have := leNat_lt (slice wl (witCounters + 4 * lay) 4)
  have l4 : (slice wl (witCounters + 4 * lay) 4).length ≤ 4 := by simp [slice]
  exact lt_of_lt_of_le this (le_trans (Nat.pow_le_pow_right (by decide) l4) (by norm_num))

end SigGolfCandidate.Verify
