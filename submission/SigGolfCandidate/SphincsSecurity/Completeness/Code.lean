import SigGolfCandidate.SphincsSecurity.Scheme

/-!
# How many digests the target-sum code accepts

The signer's counter search succeeds on a digest whose 32 four-bit digits sum to `T = 312`, so the
search's failure probability is governed by how many of the `2^128` digests that is. The count is
the coefficient of `z^312` in `(1 + z + ... + z^15)^32`, about `2^116.43`: at least one digest in
`codeShare = 3033`.

Counting it is one identity and one division. Packing the polynomial into a single natural number
in base `2^129`, which is above every coefficient, turns the product of the `32` factors into a
`Nat` power and the coefficient into one of its digits, so the kernel evaluates the whole count as
ordinary arithmetic on one large numeral.
-/

open Finset

set_option maxRecDepth 100000
set_option exponentiation.threshold 1024

namespace SphincsSecurity.Completeness

open TargetSum


/-- A base above every coefficient, so the coefficients are the digits. -/
def base : Nat := 2 ^ 129

theorem digit_of_sum (B : Nat) (hB : 0 < B) (c : Nat → Nat) (hc : ∀ s, c s < B) :
    ∀ (n k : Nat), k < n → (∑ s ∈ range n, c s * B ^ s) / B ^ k % B = c k := by
  intro n
  induction n generalizing c with
  | zero => intro k hk; exact absurd hk (Nat.not_lt_zero k)
  | succ n ih =>
      intro k hk
      have hsplit : ∑ s ∈ range (n + 1), c s * B ^ s
          = c 0 + B * ∑ s ∈ range n, c (s + 1) * B ^ s := by
        rw [Finset.sum_range_succ', Finset.mul_sum]
        simp only [pow_zero, mul_one, pow_succ]
        rw [Nat.add_comm]
        congr 1
        apply Finset.sum_congr rfl
        intro s _
        ring
      cases k with
      | zero =>
          rw [hsplit, pow_zero, Nat.div_one, Nat.add_mul_mod_self_left,
            Nat.mod_eq_of_lt (hc 0)]
      | succ k =>
          rw [hsplit, pow_succ']
          rw [← Nat.div_div_eq_div_mul]
          rw [Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt (hc 0), Nat.zero_add]
          exact ih (fun s => c (s + 1)) (fun s => hc (s + 1)) k (Nat.lt_of_succ_lt_succ hk)

theorem weight_pow (B : Nat) :
    (∑ d : Digit, B ^ d.val) ^ numChains = ∑ x : Encoding, B ^ (TargetSum.sum x) := by
  have hcard : (Finset.univ : Finset ChainIndex).card = numChains := by
    simp [Finset.card_univ]
  have h1 : (∑ d : Digit, B ^ d.val) ^ numChains
      = ∏ _i : ChainIndex, ∑ d : Digit, B ^ d.val := by
    rw [Finset.prod_const, hcard]
  rw [h1, Finset.prod_univ_sum, Fintype.piFinset_univ]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.prod_pow_eq_pow_sum]
  rfl


/-- The number of codewords of digit sum `s`. -/
def codeCount (s : Nat) : Nat := (Finset.univ.filter (fun x : Encoding => TargetSum.sum x = s)).card

theorem sum_lt_481 (x : Encoding) : TargetSum.sum x < 481 := by
  have : TargetSum.sum x ≤ ∑ _i : ChainIndex, 15 :=
    Finset.sum_le_sum (fun i _ => Nat.le_of_lt_succ (x i).isLt)
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at this
  have hcard : Fintype.card ChainIndex = 32 := by simp [numChains]
  rw [hcard] at this
  omega

theorem sum_encoding_pow (B : Nat) :
    ∑ x : Encoding, B ^ (TargetSum.sum x) = ∑ s ∈ range 481, codeCount s * B ^ s := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := TargetSum.sum) (t := range 481)
    (fun x _ => Finset.mem_range.mpr (sum_lt_481 x)) (fun x => B ^ (TargetSum.sum x))]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.sum_congr rfl (fun x hx => by rw [(Finset.mem_filter.mp hx).2]),
    Finset.sum_const, codeCount, smul_eq_mul]

theorem codeCount_lt_base (s : Nat) : codeCount s < base := by
  have h : codeCount s ≤ Fintype.card Encoding := Finset.card_filter_le _ _
  have hcard : Fintype.card Encoding = 16 ^ 32 := by
    simp [numChains, chainLength, winternitzBits]
  rw [hcard] at h
  exact Nat.lt_of_le_of_lt h (by decide)

theorem weight_eq : (∑ d : Digit, base ^ d.val) = (base ^ 16 - 1) / (base - 1) := by decide

theorem codeCount_target :
    codeCount targetSum = (∑ d : Digit, base ^ d.val) ^ numChains / base ^ targetSum % base := by
  rw [weight_pow, sum_encoding_pow]
  exact (digit_of_sum base (by decide) codeCount codeCount_lt_base 481 targetSum (by decide)).symm

/-- One digest in `codeShare` or more is a codeword. -/
def codeShare : Nat := 3033

theorem digests_le_codeShare_mul_codeCount : 2 ^ 128 ≤ codeShare * codeCount targetSum := by
  rw [codeCount_target, weight_eq]
  decide


/-- A bounded-digit sum stays below the next power. -/
theorem sum_digits_lt (B : Nat) (hB : 0 < B) (v : Nat → Nat) (hv : ∀ j, v j < B) :
    ∀ n, ∑ j ∈ range n, v j * B ^ j < B ^ n := by
  intro n
  induction n with
  | zero => simpa using hB
  | succ n ih =>
      rw [Finset.sum_range_succ, pow_succ]
      have hle : v n * B ^ n ≤ (B - 1) * B ^ n :=
        Nat.mul_le_mul_right _ (by have := hv n; omega)
      have : B ^ n * B = (B - 1) * B ^ n + B ^ n := by
        cases B with
        | zero => omega
        | succ b => simp [Nat.succ_sub_one]; ring
      omega

/-- Digit `j` of a word, or zero past the last chain. -/
def digitAt (x : Encoding) (j : Nat) : Nat :=
  if h : j < 32 then (x ⟨j, by simp only [numChains]; omega⟩).val else 0

theorem digitAt_lt (x : Encoding) (j : Nat) : digitAt x j < 16 := by
  unfold digitAt
  split
  · exact (x _).isLt
  · decide

/-- The digest of a word: digit `j` at bits `4j, ..., 4j + 3`. -/
def packNat (x : Encoding) : Nat := ∑ j ∈ range 32, digitAt x j * 16 ^ j

def pack (x : Encoding) : Digest := BitVec.ofNat digestBits (packNat x)

theorem packNat_lt (x : Encoding) : packNat x < 2 ^ 128 := by
  have h := sum_digits_lt 16 (by decide) (digitAt x) (digitAt_lt x) 32
  simpa [packNat, show (16 : Nat) ^ 32 = 2 ^ 128 by norm_num] using h

theorem packNat_digit (x : Encoding) (k : Nat) (hk : k < 32) :
    packNat x / 16 ^ k % 16 = digitAt x k :=
  digit_of_sum 16 (by decide) (digitAt x) (digitAt_lt x) 32 k hk

theorem toNat_pack (x : Encoding) : (pack x).toNat = packNat x := by
  rw [pack, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by simpa [digestBits] using packNat_lt x)]

theorem encoding_val (d : Digest) (i : ChainIndex) :
    (digestEncoding d i).val = d.toNat / 2 ^ (digitOffset i) % 16 := by
  simp [digestEncoding, BitVec.extractLsb', winternitzBits, Nat.shiftRight_eq_div_pow]

theorem digestEncoding_pack (x : Encoding) : digestEncoding (pack x) = x := by
  funext i
  apply Fin.ext
  have hi : i.val < 32 := by simpa [numChains] using i.isLt
  rw [encoding_val, toNat_pack, show digitOffset i = 4 * i.val from rfl,
    show (2 : Nat) ^ (4 * i.val) = 16 ^ i.val by rw [pow_mul]; norm_num,
    packNat_digit x i.val hi, digitAt, dif_pos hi]

theorem decodeDigest_pack (x : Encoding) (hx : Valid x) : decodeDigest (pack x) = some x := by
  rw [decodeDigest, if_pos (by rw [digestEncoding_pack]; exact hx), digestEncoding_pack]

/-- The signer's counter search accepts at least one in `codeShare` of the `2^128` digests. -/
theorem digests_le_codeShare_mul_card_accepting :
    2 ^ 128 ≤ codeShare * (Finset.univ.filter fun d : Digest => (decodeDigest d).isSome).card := by
  refine le_trans digests_le_codeShare_mul_codeCount (Nat.mul_le_mul_left _ ?_)
  rw [codeCount]
  apply Finset.card_le_card_of_injOn pack
  · intro x hx
    have hvalid : Valid x := (Finset.mem_filter.mp hx).2
    simp [decodeDigest_pack x hvalid]
  · intro left hleft right hright heq
    have hl : Valid left := (Finset.mem_filter.mp hleft).2
    have hr : Valid right := (Finset.mem_filter.mp hright).2
    have := decodeDigest_pack left hl
    rw [heq, decodeDigest_pack right hr] at this
    exact (Option.some.inj this).symm

end SphincsSecurity.Completeness
