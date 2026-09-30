import SigGolfCandidate.Ref
import Mathlib.Data.Nat.Bitwise

/-! # The SWAR nibble sum of the encoding check (Nat level)

Sign's counter search (`enc_loop`) computes the digit sum of an encoding's 32 four-bit digits from
its two 64-bit halves `a`, `b` with the masks `nibM = 0x0F0F…0F` and `laneM = 0x00FF00FF…00FF`:
`t = ((a >> 4) & nibM) + (a & nibM) + ((b >> 4) & nibM) + (b & nibM)` (eight byte lanes, each at
most 60), `t += t >> 8` (lanes `x_j + x_{j+1}`), `t &= laneM` (four 16-bit lanes), `t += t >> 16`,
`t += t >> 32`, `t & 1023`. `swar4_eq`: the result is the digit sum. Numbers are handled as
base-`B` lane lists (`nest`). -/

namespace SigGolfCandidate.Verify
open SigGolfCandidate.Ref

/-- `x0 + B * (x1 + B * (… + B * x_{n-1}))`, the number with base-`B` lanes `xs`. -/
def nest (B : Nat) : List Nat → Nat
  | [] => 0
  | x :: xs => x + B * nest B xs

theorem nest_cons (B x : Nat) (xs : List Nat) : nest B (x :: xs) = x + B * nest B xs := rfl

theorem nest_div (B x : Nat) (xs : List Nat) (hx : x < B) : nest B (x :: xs) / B = nest B xs := by
  rw [nest_cons, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hx, Nat.zero_add]

theorem nest_mod (B x : Nat) (xs : List Nat) (hx : x < B) : nest B (x :: xs) % B = x := by
  rw [nest_cons, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]

theorem nest_lt (B : Nat) (xs : List Nat) (h : ∀ x ∈ xs, x < B) : nest B xs < B ^ xs.length := by
  induction xs with
  | nil => simp [nest]
  | cons x xs ih =>
    have hx := h x (by simp)
    have ih := ih (fun y hy => h y (by simp [hy]))
    rw [nest_cons, List.length_cons, pow_succ, mul_comm (B ^ xs.length) B]
    have h1 : B * (nest B xs + 1) ≤ B * B ^ xs.length := Nat.mul_le_mul_left _ ih
    rw [Nat.mul_add, Nat.mul_one] at h1
    omega

theorem nest_add (B : Nat) : ∀ (xs ys : List Nat), xs.length = ys.length →
    nest B xs + nest B ys = nest B (List.zipWith (· + ·) xs ys)
  | [], [], _ => rfl
  | x :: xs, y :: ys, h => by
    simp only [nest_cons, List.zipWith_cons_cons]
    rw [← nest_add B xs ys (by simpa using h)]; ring

/-- Two base-`B` lanes make one base-`B^2` lane. -/
theorem nest_pair (B a b : Nat) (xs : List Nat) :
    nest B (a :: b :: xs) = (a + B * b) + B ^ 2 * nest B xs := by
  simp only [nest_cons]; ring


def nibM : Nat := 1085102592571150095
def laneM : Nat := 71777214294589695

theorem land_split4 (n M : Nat) : n &&& (256 * M + 15) = 256 * ((n / 256) &&& M) + n % 16 := by
  have hw : (15 : Nat) < 256 := by decide
  have hm : n % 16 < 256 := lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide)
  apply Nat.eq_of_testBit_eq
  intro j
  rw [show (256 : Nat) = 2 ^ 8 by norm_num, Nat.testBit_land, Nat.testBit_two_pow_mul_add _ hw,
    Nat.testBit_two_pow_mul_add _ hm]
  split
  · rw [show (15 : Nat) = 2 ^ 4 - 1 by norm_num, Nat.testBit_two_pow_sub_one,
      show (16 : Nat) = 2 ^ 4 by norm_num, Nat.testBit_mod_two_pow]
    cases n.testBit j <;> simp
  · rw [Nat.testBit_land, Nat.testBit_div_two_pow, Nat.sub_add_cancel (by omega)]

theorem land_split8 (n M : Nat) : n &&& (65536 * M + 255) = 65536 * ((n / 65536) &&& M) + n % 256 := by
  have hw : (255 : Nat) < 65536 := by decide
  have hm : n % 256 < 65536 := lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide)
  apply Nat.eq_of_testBit_eq
  intro j
  rw [show (65536 : Nat) = 2 ^ 16 by norm_num, Nat.testBit_land, Nat.testBit_two_pow_mul_add _ hw,
    Nat.testBit_two_pow_mul_add _ hm]
  split
  · rw [show (255 : Nat) = 2 ^ 8 - 1 by norm_num, Nat.testBit_two_pow_sub_one,
      show (256 : Nat) = 2 ^ 8 by norm_num, Nat.testBit_mod_two_pow]
    cases n.testBit j <;> simp
  · rw [Nat.testBit_land, Nat.testBit_div_two_pow, Nat.sub_add_cancel (by omega)]

theorem and15' (n : Nat) : n &&& 15 = n % 16 := Nat.and_two_pow_sub_one_eq_mod n 4
theorem and255 (n : Nat) : n &&& 255 = n % 256 := Nat.and_two_pow_sub_one_eq_mod n 8
theorem and1023 (n : Nat) : n &&& 1023 = n % 1024 := Nat.and_two_pow_sub_one_eq_mod n 10

/-- The low nibbles of the eight bytes of `n`. -/
def lo (n : Nat) : List Nat :=
  [n % 16, n / 256 % 16, n / 256 ^ 2 % 16, n / 256 ^ 3 % 16, n / 256 ^ 4 % 16, n / 256 ^ 5 % 16,
    n / 256 ^ 6 % 16, n / 256 ^ 7 % 16]

theorem land_nibM (n : Nat) : n &&& nibM = nest 256 (lo n) := by
  rw [show nibM = 256 * (256 * (256 * (256 * (256 * (256 * (256 * 15 + 15) + 15) + 15) + 15) + 15)
    + 15) + 15 by unfold nibM; norm_num]
  simp only [land_split4, and15', Nat.div_div_eq_div_mul, lo, nest]
  norm_num
  ring

theorem land_laneM (n : Nat) : n &&& laneM =
    nest 65536 [n % 256, n / 65536 % 256, n / 65536 ^ 2 % 256, n / 65536 ^ 3 % 256] := by
  rw [show laneM = 65536 * (65536 * (65536 * 255 + 255) + 255) + 255 by unfold laneM; norm_num]
  simp only [land_split8, and255, Nat.div_div_eq_div_mul, nest]
  norm_num
  ring

theorem lt256 (xs : List Nat) (h : ∀ x ∈ xs, x < 256) (hl : xs.length = 8) : nest 256 xs < 2 ^ 64 := by
  have := nest_lt 256 xs h; rw [hl] at this; simpa using this

theorem lt65536 (xs : List Nat) (h : ∀ x ∈ xs, x < 65536) (hl : xs.length = 4) :
    nest 65536 xs < 2 ^ 64 := by
  have := nest_lt 65536 xs h; rw [hl] at this; simpa using this

/-- Eight byte lanes `x_j ≤ 60`: the steps after the first addition sum them. -/
theorem tail4 (x0 x1 x2 x3 x4 x5 x6 x7 : Nat) (h0 : x0 ≤ 60) (h1 : x1 ≤ 60) (h2 : x2 ≤ 60)
    (h3 : x3 ≤ 60) (h4 : x4 ≤ 60) (h5 : x5 ≤ 60) (h6 : x6 ≤ 60) (h7 : x7 ≤ 60) :
    let t1 := nest 256 [x0, x1, x2, x3, x4, x5, x6, x7]
    let t2 := (t1 + t1 / 256) % 2 ^ 64
    let t3 := t2 &&& laneM
    let t4 := (t3 + t3 / 65536) % 2 ^ 64
    let t5 := (t4 + t4 / 4294967296) % 2 ^ 64
    t5 &&& 1023 = x0 + x1 + x2 + x3 + x4 + x5 + x6 + x7 := by
  intro t1 t2 t3 t4 t5
  -- t2: lanes y_j = x_j + x_{j+1}
  have e2 : t2 = nest 256 [x0 + x1, x1 + x2, x2 + x3, x3 + x4, x4 + x5, x5 + x6, x6 + x7, x7 + 0] := by
    have hd : t1 / 256 = nest 256 [x1, x2, x3, x4, x5, x6, x7, 0] := by
      simp only [t1]; rw [nest_div _ _ _ (by omega)]; simp [nest]
    simp only [t2]; rw [hd]
    simp only [t1]; rw [nest_add 256 _ _ (by simp)]
    simp only [List.zipWith_cons_cons, List.zipWith_nil_right]
    exact Nat.mod_eq_of_lt (lt256 _ (by simp; omega) rfl)
  -- t3: the even lanes of t2, in base 65536
  have e3 : t3 = nest 65536 [x0 + x1, x2 + x3, x4 + x5, x6 + x7] := by
    have hp : nest 256 [x0 + x1, x1 + x2, x2 + x3, x3 + x4, x4 + x5, x5 + x6, x6 + x7, x7 + 0] =
        nest 65536 [(x0 + x1) + 256 * (x1 + x2), (x2 + x3) + 256 * (x3 + x4),
          (x4 + x5) + 256 * (x5 + x6), (x6 + x7) + 256 * (x7 + 0)] := by
      simp only [nest]; ring
    simp only [t3]; rw [land_laneM, e2, hp]
    have d1 := nest_div 65536 ((x0 + x1) + 256 * (x1 + x2)) [(x2 + x3) + 256 * (x3 + x4),
      (x4 + x5) + 256 * (x5 + x6), (x6 + x7) + 256 * (x7 + 0)] (by omega)
    have d2 := nest_div 65536 ((x2 + x3) + 256 * (x3 + x4)) [(x4 + x5) + 256 * (x5 + x6),
      (x6 + x7) + 256 * (x7 + 0)] (by omega)
    have d3 := nest_div 65536 ((x4 + x5) + 256 * (x5 + x6)) [(x6 + x7) + 256 * (x7 + 0)] (by omega)
    rw [show (65536 : Nat) ^ 2 = 65536 * 65536 by norm_num, show (65536 : Nat) ^ 3 = 65536 * 65536 * 65536 by norm_num,
      ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, d1, d2, d3]
    simp only [nest_cons, nest]
    congr 1 <;> [omega; congr 2 <;> [omega; congr 2 <;> [omega; omega]]]
  -- t4, t5
  have e4 : t4 = nest 65536 [(x0 + x1) + (x2 + x3), (x2 + x3) + (x4 + x5), (x4 + x5) + (x6 + x7),
      (x6 + x7) + 0] := by
    have hd : t3 / 65536 = nest 65536 [x2 + x3, x4 + x5, x6 + x7, 0] := by
      rw [e3, nest_div _ _ _ (by omega)]; simp [nest]
    simp only [t4]; rw [hd, e3, nest_add 65536 _ _ (by simp)]
    simp only [List.zipWith_cons_cons, List.zipWith_nil_right]
    exact Nat.mod_eq_of_lt (lt65536 _ (by simp; omega) rfl)
  have e5 : t5 = nest 65536 [((x0 + x1) + (x2 + x3)) + ((x4 + x5) + (x6 + x7)),
      ((x2 + x3) + (x4 + x5)) + ((x6 + x7) + 0), ((x4 + x5) + (x6 + x7)) + 0, ((x6 + x7) + 0) + 0] := by
    have hd : t4 / 4294967296 = nest 65536 [(x4 + x5) + (x6 + x7), (x6 + x7) + 0, 0, 0] := by
      rw [show (4294967296 : Nat) = 65536 * 65536 by norm_num, ← Nat.div_div_eq_div_mul, e4,
        nest_div _ _ _ (by omega), nest_div _ _ _ (by omega)]
      simp [nest]
    simp only [t5]; rw [hd, e4, nest_add 65536 _ _ (by simp)]
    simp only [List.zipWith_cons_cons, List.zipWith_nil_right]
    exact Nat.mod_eq_of_lt (lt65536 _ (by simp; omega) rfl)
  rw [and1023, e5]
  simp only [nest]
  omega


/-- The SWAR nibble sum on naturals (every step reduced mod `2^64`, as the machine does). -/
def swar4 (a b : Nat) : Nat :=
  let t1 := (((((a / 16) &&& nibM) + (a &&& nibM)) % 2 ^ 64 + ((b / 16) &&& nibM)) % 2 ^ 64 +
    (b &&& nibM)) % 2 ^ 64
  let t2 := (t1 + t1 / 256) % 2 ^ 64
  let t3 := t2 &&& laneM
  let t4 := (t3 + t3 / 65536) % 2 ^ 64
  let t5 := (t4 + t4 / 4294967296) % 2 ^ 64
  t5 &&& 1023

theorem digits_sum4 (a : Nat) : (digitsOfWord a).sum =
    a % 16 + a / 16 % 16 + a / 16 ^ 2 % 16 + a / 16 ^ 3 % 16 + a / 16 ^ 4 % 16 + a / 16 ^ 5 % 16 +
    a / 16 ^ 6 % 16 + a / 16 ^ 7 % 16 + a / 16 ^ 8 % 16 + a / 16 ^ 9 % 16 + a / 16 ^ 10 % 16 +
    a / 16 ^ 11 % 16 + a / 16 ^ 12 % 16 + a / 16 ^ 13 % 16 + a / 16 ^ 14 % 16 + a / 16 ^ 15 % 16 := by
  simp only [digitsOfWord, List.range, List.range.loop, List.map, List.sum_cons, List.sum_nil]
  norm_num
  omega

theorem swar4_eq (a b : Nat) :
    swar4 a b = (digitsOfWord a).sum + (digitsOfWord b).sum := by
  have lo_lt : ∀ n, ∀ x ∈ lo n, x < 16 := by
    intro n x hx; simp only [lo, List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with h | h | h | h | h | h | h | h <;> (subst h; exact Nat.mod_lt _ (by decide))
  have s1 : (((a / 16) &&& nibM) + (a &&& nibM)) % 2 ^ 64 =
      nest 256 (List.zipWith (· + ·) (lo (a / 16)) (lo a)) := by
    rw [land_nibM, land_nibM, nest_add 256 _ _ (by simp [lo])]
    refine Nat.mod_eq_of_lt (lt256 _ ?_ (by simp [lo]))
    simp only [lo, List.zipWith_cons_cons, List.zipWith_nil_right, List.mem_cons, List.mem_nil_iff,
      or_false]
    intro x hx; rcases hx with h | h | h | h | h | h | h | h <;> (subst h; omega)
  have s2 : (nest 256 (List.zipWith (· + ·) (lo (a / 16)) (lo a)) + ((b / 16) &&& nibM)) % 2 ^ 64 =
      nest 256 (List.zipWith (· + ·) (List.zipWith (· + ·) (lo (a / 16)) (lo a)) (lo (b / 16))) := by
    rw [land_nibM, nest_add 256 _ _ (by simp [lo])]
    refine Nat.mod_eq_of_lt (lt256 _ ?_ (by simp [lo]))
    simp only [lo, List.zipWith_cons_cons, List.zipWith_nil_right, List.mem_cons, List.mem_nil_iff,
      or_false]
    intro x hx; rcases hx with h | h | h | h | h | h | h | h <;> (subst h; omega)
  have s3 : (nest 256 (List.zipWith (· + ·) (List.zipWith (· + ·) (lo (a / 16)) (lo a)) (lo (b / 16)))
      + (b &&& nibM)) % 2 ^ 64 = nest 256 (List.zipWith (· + ·)
        (List.zipWith (· + ·) (List.zipWith (· + ·) (lo (a / 16)) (lo a)) (lo (b / 16))) (lo b)) := by
    rw [land_nibM, nest_add 256 _ _ (by simp [lo])]
    refine Nat.mod_eq_of_lt (lt256 _ ?_ (by simp [lo]))
    simp only [lo, List.zipWith_cons_cons, List.zipWith_nil_right, List.mem_cons, List.mem_nil_iff,
      or_false]
    intro x hx; rcases hx with h | h | h | h | h | h | h | h <;> (subst h; omega)
  unfold swar4
  simp only
  rw [s1, s2, s3]
  simp only [lo, List.zipWith_cons_cons, List.zipWith_nil_right]
  rw [tail4 _ _ _ _ _ _ _ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega), digits_sum4, digits_sum4]
  simp only [Nat.div_div_eq_div_mul]
  norm_num
  omega

end SigGolfCandidate.Verify
