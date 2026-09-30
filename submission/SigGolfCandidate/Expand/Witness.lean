import SigGolfCandidate.Expand.CopyRun
import SigGolfCandidate.Expand.RefFacts

/-!
# `expand`: the witness bytes

`witness_bytes` : the byte view left by the copy phase is `witnessList sig v vs segs`
(`ref.expand`'s witness) on the 6064 witness bytes, given the byte view before the phase
(signature bytes, the segment stream, zero at the unused pi byte).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace SigGolfCandidate.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Ref

theorem getD_app (l1 l2 : List Byte) (i : Nat) :
    (l1 ++ l2).getD i 0 = if i < l1.length then l1.getD i 0 else l2.getD (i - l1.length) 0 := by
  split
  · exact List.getD_append _ _ _ _ (by assumption)
  · exact List.getD_append_right _ _ _ _ (by omega)

theorem getD_slice' (l : List Byte) (off len j : Nat) (hj : j < len) :
    (slice l off len).getD j 0 = l.getD (off + j) 0 := by
  simp only [slice, List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop]
  rw [if_pos hj]

theorem length_slice' (l : List Byte) (off len : Nat) (h : off + len ≤ l.length) :
    (slice l off len).length = len := by
  simp [slice]; omega

/-- The copies read the signature and write the witness only. -/
theorem copyRest_pairwise : copyRest.Pairwise (fun c c' => Disj c.2.1 (4 * c.2.2) c'.2.1 (4 * c'.2.2)) := by
  decide

theorem copyRest_srcdst : ∀ c ∈ copyRest, ∀ c' ∈ copyRest, Disj c.1 (4 * c.2.2) c'.2.1 (4 * c'.2.2) := by
  decide

theorem copy_hit (g : Nat → Byte) (c : Nat × Nat × Nat) (hc : c ∈ copyRest) (x : Nat)
    (h1 : c.2.1 ≤ x) (h2 : x < c.2.1 + 4 * c.2.2) :
    applyCopies copyRest g x = g (x - c.2.1 + c.1) :=
  applyCopies_hit copyRest g copyRest_pairwise copyRest_srcdst c hc x h1 h2

theorem copy_miss (g : Nat → Byte) (x : Nat) (hx : x < 0x820 ∨ (0x910 ≤ x ∧ x < 0x1178)) :
    applyCopies copyRest g x = g x :=
  applyCopies_frame copyRest g x (by
    intro c hc; simp only [copyRest, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp <;> omega)

theorem flatten_slices (l : List Byte) (off len : Nat) :
    ∀ n, ((List.range n).map (fun k => slice l (off + len * k) len)).flatten = slice l off (len * n) := by
  intro n
  induction n with
  | zero => simp [slice]
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.flatten_append, ih]
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil, slice]
    rw [show len * (n + 1) = len * n + len by ring, List.take_add, List.drop_drop]

theorem getD_take' (l : List Byte) (n i : Nat) (hi : i < n) : (l.take n).getD i 0 = l.getD i 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take]; rw [if_pos hi]

theorem witness_bytes (sig : List Byte) (hsig : sig.length = 5784) (N : Nat) (A : Nat → Nat)
    (hSK : SortedKeys N A) (hn : (leavesOf N).Nodup) (segs : List Nat) (f0 : Nat → Byte)
    (h1 : ∀ j < 5784, f0 (0x3300 + j) = sig.getD j 0)
    (h2 : ∀ i < 2152, f0 (0x910 + i) = (curStream sig segs 0).getD i 0) (h3 : f0 0x81F = 0) :
    ∀ i < 6064, applyCopies copyRest (piF A 15 (applyCopy (0x3300, 0x800, 4) f0)) (0x800 + i) =
      (witnessList sig (leavesOf N) (vsOf A) segs).getD i 0 := by
  intro i hi
  set g := piF A 15 (applyCopy (0x3300, 0x800, 4) f0) with hg
  -- the signature under the copies
  have hgs : ∀ j < 5784, g (0x3300 + j) = sig.getD j 0 := by
    intro j hj; simp only [hg, piF, applyCopy]; rw [if_neg (by omega), if_neg (by omega)]; exact h1 j hj
  -- the witness as one concatenation with explicit lengths
  have eS : ((List.range porsK).map (sigItem sig)).flatten = slice sig 16 240 := by
    have := flatten_slices sig 16 16 15
    simp only [show 16 * 15 = 240 from rfl] at this
    rw [← this]; unfold porsK sigItem; rfl
  have eB : ((List.range nLayers).map (sigLayerBody sig)).flatten =
      slice sig 2148 688 ++ (slice sig 2840 592 ++ (slice sig 3436 592 ++ (slice sig 4032 592 ++ (slice sig 4628 576 ++ (slice sig 5208 576))))) := by
    simp only [nLayers, List.range_succ, List.range_zero, List.map_append, List.map_cons, List.map_nil,
      List.nil_append, List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil,
      List.append_assoc]
    unfold sigLayerBody
    rw [show sigLayerOff 0 = 2144 by decide,
      show sigLayerOff 1 = 2836 by decide,
      show sigLayerOff 2 = 3432 by decide,
      show sigLayerOff 3 = 4028 by decide,
      show sigLayerOff 4 = 4624 by decide,
      show sigLayerOff 5 = 5204 by decide,
      show sigLayerBytes 0 = 692 by decide,
      show sigLayerBytes 1 = 596 by decide,
      show sigLayerBytes 2 = 596 by decide,
      show sigLayerBytes 3 = 596 by decide,
      show sigLayerBytes 4 = 580 by decide,
      show sigLayerBytes 5 = 580 by decide]
  have eC : ((List.range nLayers).map (sigCounterBytes sig)).flatten =
      slice sig 2144 4 ++ (slice sig 2836 4 ++ (slice sig 3432 4 ++ (slice sig 4028 4 ++ (slice sig 4624 4 ++ (slice sig 5204 4))))) := by
    simp only [nLayers, List.range_succ, List.range_zero, List.map_append, List.map_cons, List.map_nil,
      List.nil_append, List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil,
      List.append_assoc]
    unfold sigCounterBytes
    rw [show sigLayerOff 0 = 2144 by decide,
      show sigLayerOff 1 = 2836 by decide,
      show sigLayerOff 2 = 3432 by decide,
      show sigLayerOff 3 = 4028 by decide,
      show sigLayerOff 4 = 4624 by decide,
      show sigLayerOff 5 = 5204 by decide]
  have lr : (sigRho sig).length = 16 := length_slice' _ _ _ (by omega)
  have lp : ((vsOf A).map (fun x => byte (8 * (leavesOf N).idxOf x))).length = 15 := by simp [vsOf]
  have lz : (zeros (wSec - wPi - porsK)).length = 1 := by simp [zeros, wSec, wPi, porsK]
  have ls : (slice sig 16 240).length = 240 := length_slice' _ _ _ (by omega)
  have lt : ((segStream sig segs ++ zeros streamBytes).take streamBytes).length = 2152 := by
    rw [List.length_take, List.length_append, streamBytes_eq]; simp only [zeros, List.length_replicate]; omega
  have l0 : (slice sig 2148 688).length = 688 := length_slice' _ _ _ (by omega)
  have l1 : (slice sig 2840 592).length = 592 := length_slice' _ _ _ (by omega)
  have l2 : (slice sig 3436 592).length = 592 := length_slice' _ _ _ (by omega)
  have l3 : (slice sig 4032 592).length = 592 := length_slice' _ _ _ (by omega)
  have l4 : (slice sig 4628 576).length = 576 := length_slice' _ _ _ (by omega)
  have l5 : (slice sig 5208 576).length = 576 := length_slice' _ _ _ (by omega)
  have k0 : (slice sig 2144 4).length = 4 := length_slice' _ _ _ (by omega)
  have k1 : (slice sig 2836 4).length = 4 := length_slice' _ _ _ (by omega)
  have k2 : (slice sig 3432 4).length = 4 := length_slice' _ _ _ (by omega)
  have k3 : (slice sig 4028 4).length = 4 := length_slice' _ _ _ (by omega)
  have k4 : (slice sig 4624 4).length = 4 := length_slice' _ _ _ (by omega)
  have k5 : (slice sig 5204 4).length = 4 := length_slice' _ _ _ (by omega)
  unfold witnessList
  rw [eS, eB, eC]
  simp only [List.append_assoc]
  simp only [getD_app, lr, lp, lz, ls, lt, l0, l1, l2, l3, l4, l5, k0, k1, k2, k3, k4, k5, List.length_nil]
  -- a copied region: `x = 0x800 + i` in `[dst, dst + 4 n)` reads `sig[x - dst + src - 0x3300]`
  have cp : ∀ c ∈ copyRest, c.2.1 ≤ 0x800 + i → 0x800 + i < c.2.1 + 4 * c.2.2 → 0x3300 ≤ c.1 →
      c.1 + 4 * c.2.2 ≤ 0x3300 + 5784 →
      applyCopies copyRest g (0x800 + i) = sig.getD (0x800 + i - c.2.1 + c.1 - 0x3300) 0 := by
    intro c hc h1 h2 h3 h4
    rw [copy_hit g c hc _ h1 h2]
    have := hgs (0x800 + i - c.2.1 + c.1 - 0x3300) (by omega)
    rwa [show 0x3300 + (0x800 + i - c.2.1 + c.1 - 0x3300) = 0x800 + i - c.2.1 + c.1 by omega] at this
  by_cases r0 : i < 16
  · rw [if_pos r0, copy_miss g _ (by omega)]
    simp only [hg, piF, applyCopy]; rw [if_neg (by omega), if_pos (by omega)]
    rw [show 0x800 + i - 0x800 + 0x3300 = 0x3300 + i by omega, h1 i (by omega), sigRho, getD_slice' _ _ _ _ r0,
      Nat.zero_add]
  rw [if_neg r0]
  by_cases r1 : i - 16 < 15
  · rw [if_pos r1, copy_miss g _ (by omega)]
    simp only [hg, piF]; rw [if_pos (by omega)]
    rw [List.getD_eq_getElem?_getD, List.getElem?_map]
    simp only [vsOf, List.getElem?_map, List.getElem?_range r1, Option.map_some, Option.getD_some]
    rw [← idxOf_lv hSK hn (i - 16) r1, show 0x800 + i - 0x810 = i - 16 by omega]
    unfold byte; apply BitVec.eq_of_toNat_eq; simp
  rw [if_neg r1]
  by_cases r2 : i - 16 - 15 < 1
  · rw [if_pos r2, copy_miss g _ (by omega)]
    simp only [hg, piF, applyCopy]; rw [if_neg (by omega), if_neg (by omega), show 0x800 + i = 0x81F by omega, h3]
    simp [zeros, List.getD_eq_getElem?_getD]
  rw [if_neg r2]
  by_cases r3 : i - 16 - 15 - 1 < 240
  · rw [if_pos r3, cp (0x3310, 0x820, 60) (by decide) (by simp; omega) (by simp; omega) (by simp) (by simp),
      getD_slice' _ _ _ _ r3]
    exact congrArg (fun j => sig.getD j 0) (by simp; omega)
  rw [if_neg r3]
  by_cases r4 : i - 16 - 15 - 1 - 240 < 2152
  · rw [if_pos r4, copy_miss g _ (by omega)]
    simp only [hg, piF, applyCopy]; rw [if_neg (by omega), if_neg (by omega)]
    rw [show 0x800 + i = 0x910 + (i - 16 - 15 - 1 - 240) by omega, h2 _ r4, getD_take' _ _ _ (by rw [streamBytes_eq]; exact r4)]
    unfold curStream items
    simp only [List.range_zero, List.map_nil, List.flatten_nil, List.append_nil]
    rw [getD_app, getD_app]
    split
    · rfl
    · rw [getD_zeros, getD_zeros]
  rw [if_neg r4]
  by_cases q0 : i - 16 - 15 - 1 - 240 - 2152 < 688
  · rw [if_pos q0, cp (0x3B64, 0x1178, 172) (by decide) (by simp; omega) (by simp; omega) (by simp) (by simp),
      getD_slice' _ _ _ _ q0]
    exact congrArg (fun j => sig.getD j 0) (by simp; omega)
  rw [if_neg q0]
  by_cases q1 : i - 16 - 15 - 1 - 240 - 2152 - 688 < 592
  · rw [if_pos q1, cp (0x3E18, 0x1428, 148) (by decide) (by simp; omega) (by simp; omega) (by simp) (by simp),
      getD_slice' _ _ _ _ q1]
    exact congrArg (fun j => sig.getD j 0) (by simp; omega)
  rw [if_neg q1]
  by_cases q2 : i - 16 - 15 - 1 - 240 - 2152 - 688 - 592 < 592
  · rw [if_pos q2, cp (0x406C, 0x1678, 148) (by decide) (by simp; omega) (by simp; omega) (by simp) (by simp),
      getD_slice' _ _ _ _ q2]
    exact congrArg (fun j => sig.getD j 0) (by simp; omega)
  rw [if_neg q2]
  by_cases q3 : i - 16 - 15 - 1 - 240 - 2152 - 688 - 592 - 592 < 592
  · rw [if_pos q3, cp (0x42C0, 0x18C8, 148) (by decide) (by simp; omega) (by simp; omega) (by simp) (by simp),
      getD_slice' _ _ _ _ q3]
    exact congrArg (fun j => sig.getD j 0) (by simp; omega)
  rw [if_neg q3]
  by_cases q4 : i - 16 - 15 - 1 - 240 - 2152 - 688 - 592 - 592 - 592 < 576
  · rw [if_pos q4, cp (0x4514, 0x1B18, 144) (by decide) (by simp; omega) (by simp; omega) (by simp) (by simp),
      getD_slice' _ _ _ _ q4]
    exact congrArg (fun j => sig.getD j 0) (by simp; omega)
  rw [if_neg q4]
  by_cases q5 : i - 16 - 15 - 1 - 240 - 2152 - 688 - 592 - 592 - 592 - 576 < 576
  · rw [if_pos q5, cp (0x4758, 0x1D58, 144) (by decide) (by simp; omega) (by simp; omega) (by simp) (by simp),
      getD_slice' _ _ _ _ q5]
    exact congrArg (fun j => sig.getD j 0) (by simp; omega)
  rw [if_neg q5]
  by_cases q6 : i - 16 - 15 - 1 - 240 - 2152 - 688 - 592 - 592 - 592 - 576 - 576 < 4
  · rw [if_pos q6, cp (0x3B60, 0x1F98, 1) (by decide) (by simp; omega) (by simp; omega) (by simp) (by simp),
      getD_slice' _ _ _ _ q6]
    exact congrArg (fun j => sig.getD j 0) (by simp; omega)
  rw [if_neg q6]
  by_cases q7 : i - 16 - 15 - 1 - 240 - 2152 - 688 - 592 - 592 - 592 - 576 - 576 - 4 < 4
  · rw [if_pos q7, cp (0x3E14, 0x1F9C, 1) (by decide) (by simp; omega) (by simp; omega) (by simp) (by simp),
      getD_slice' _ _ _ _ q7]
    exact congrArg (fun j => sig.getD j 0) (by simp; omega)
  rw [if_neg q7]
  by_cases q8 : i - 16 - 15 - 1 - 240 - 2152 - 688 - 592 - 592 - 592 - 576 - 576 - 4 - 4 < 4
  · rw [if_pos q8, cp (0x4068, 0x1FA0, 1) (by decide) (by simp; omega) (by simp; omega) (by simp) (by simp),
      getD_slice' _ _ _ _ q8]
    exact congrArg (fun j => sig.getD j 0) (by simp; omega)
  rw [if_neg q8]
  by_cases q9 : i - 16 - 15 - 1 - 240 - 2152 - 688 - 592 - 592 - 592 - 576 - 576 - 4 - 4 - 4 < 4
  · rw [if_pos q9, cp (0x42BC, 0x1FA4, 1) (by decide) (by simp; omega) (by simp; omega) (by simp) (by simp),
      getD_slice' _ _ _ _ q9]
    exact congrArg (fun j => sig.getD j 0) (by simp; omega)
  rw [if_neg q9]
  by_cases q10 : i - 16 - 15 - 1 - 240 - 2152 - 688 - 592 - 592 - 592 - 576 - 576 - 4 - 4 - 4 - 4 < 4
  · rw [if_pos q10, cp (0x4510, 0x1FA8, 1) (by decide) (by simp; omega) (by simp; omega) (by simp) (by simp),
      getD_slice' _ _ _ _ q10]
    exact congrArg (fun j => sig.getD j 0) (by simp; omega)
  rw [if_neg q10]
  rw [cp (0x4754, 0x1FAC, 1) (by decide) (by simp; omega) (by simp; omega) (by simp) (by simp),
    getD_slice' _ _ _ _ (by omega)]
  exact congrArg (fun j => sig.getD j 0) (by simp; omega)

end SigGolfCandidate.Expand
