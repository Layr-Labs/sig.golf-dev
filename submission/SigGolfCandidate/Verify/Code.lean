import SigGolfCandidate.Verify.Exec

/-! # Fast instruction lookup in the verify image (chunks of 256 words; 17 chunks) -/

namespace SigGolfCandidate.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv

abbrev image : Image := Images.verifyImage

theorem image_eq : submission.image .verify = image := rfl

def vChunks : List (List (BitVec 32)) := [Images.verifyCode_0, Images.verifyCode_1, Images.verifyCode_2, Images.verifyCode_3, Images.verifyCode_4, Images.verifyCode_5, Images.verifyCode_6, Images.verifyCode_7, Images.verifyCode_8, Images.verifyCode_9, Images.verifyCode_10, Images.verifyCode_11, Images.verifyCode_12, Images.verifyCode_13, Images.verifyCode_14, Images.verifyCode_15, Images.verifyCode_16]
def vlook (n : Nat) : Option (BitVec 32) :=
  match vChunks[n / 256]? with
  | some c => c[n % 256]?
  | none => none

theorem lookup_chunks : ∀ (cs : List (List (BitVec 32))) (n : Nat) (w : BitVec 32),
    (cs.dropLast.all fun c => c.length == 256) = true →
    (match cs[n / 256]? with | some c => c[n % 256]? | none => none) = some w →
    cs.flatten[n]? = some w := by
  intro cs
  induction cs with
  | nil => intro n w _ h; simp at h
  | cons c cs ih =>
    intro n w hall h
    by_cases hn : n < 256
    · have h0 : n / 256 = 0 := Nat.div_eq_of_lt hn
      have h1 : n % 256 = n := Nat.mod_eq_of_lt hn
      rw [h0, h1] at h
      simp only [List.getElem?_cons_zero] at h
      simp only [List.flatten_cons]
      rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp h).1]
      exact h
    · cases cs with
      | nil =>
        have : n / 256 ≠ 0 := by omega
        obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero this
        rw [hk] at h; simp at h
      | cons c' cs' =>
        have hlen : c.length = 256 := by
          simp only [List.dropLast_cons_cons, List.all_cons, Bool.and_eq_true, beq_iff_eq] at hall
          exact hall.1
        have hall' : ((c' :: cs').dropLast.all fun c => c.length == 256) = true := by
          simp only [List.dropLast_cons_cons, List.all_cons, Bool.and_eq_true] at hall
          exact hall.2
        have hdiv : n / 256 = (n - 256) / 256 + 1 := by omega
        have hmod : n % 256 = (n - 256) % 256 := by omega
        rw [hdiv, hmod, List.getElem?_cons_succ] at h
        have := ih (n - 256) w hall' h
        simp only [List.flatten_cons]
        rw [List.getElem?_append_right (by omega), hlen]
        simpa using this

set_option maxRecDepth 100000 in
theorem vChunks_ok : (vChunks.dropLast.all fun c => c.length == 256) = true := by decide +kernel

theorem foldl_append_flatten : ∀ (l : List (List (BitVec 32))) (a : List (BitVec 32)),
    l.foldl (· ++ ·) a = a ++ l.flatten
  | [], a => by simp
  | c :: l, a => by simp [foldl_append_flatten l (a ++ c)]

set_option maxRecDepth 100000 in
theorem verifyCode_foldl : Images.verifyCode = vChunks.foldl (· ++ ·) [] := by
  delta Images.verifyCode vChunks
  rfl

theorem verifyCode_eq : Images.verifyCode = vChunks.flatten := by
  rw [verifyCode_foldl, foldl_append_flatten, List.nil_append]

theorem vlook_ok : LookOK image vlook := by
  intro n w h
  show Images.verifyCode[n]? = some w
  rw [verifyCode_eq]
  exact lookup_chunks vChunks n w vChunks_ok h

/-! ## Sequential code access (for runs over consecutive table entries) -/

/-- `verifyCode.drop i`, computed through the chunks. -/
def codeFrom (i : Nat) : List (BitVec 32) := ((vChunks.drop (i / 256)).flatten).drop (i % 256)

theorem drop_chunks : ∀ (cs : List (List (BitVec 32))) (k : Nat),
    (cs.dropLast.all fun c => c.length == 256) = true → k < cs.length →
    cs.flatten.drop (256 * k) = (cs.drop k).flatten := by
  intro cs
  induction cs with
  | nil => intro k _ hk; simp at hk
  | cons c cs ih =>
    intro k hall hk
    cases k with
    | zero => simp
    | succ k =>
      cases cs with
      | nil => simp at hk
      | cons c' cs' =>
        have hlen : c.length = 256 := by
          simp only [List.dropLast_cons_cons, List.all_cons, Bool.and_eq_true, beq_iff_eq] at hall
          exact hall.1
        have hall' : ((c' :: cs').dropLast.all fun c => c.length == 256) = true := by
          simp only [List.dropLast_cons_cons, List.all_cons, Bool.and_eq_true] at hall
          exact hall.2
        have := ih k hall' (by simp at hk ⊢; omega)
        simp only [List.flatten_cons, List.drop_succ_cons] at this ⊢
        rw [show 256 * (k + 1) = c.length + 256 * k by rw [hlen]; ring, ← List.drop_drop,
          List.drop_left]
        exact this

set_option maxRecDepth 100000 in
theorem vChunks_length : vChunks.length = 17 := by decide +kernel

theorem codeFrom_eq (i : Nat) (hi : i / 256 < 17) : codeFrom i = Images.verifyCode.drop i := by
  unfold codeFrom
  rw [verifyCode_eq, ← drop_chunks vChunks (i / 256) vChunks_ok (by rw [vChunks_length]; exact hi),
    List.drop_drop]
  congr 1; omega

set_option maxRecDepth 100000 in
theorem vChunks_le : (vChunks.all fun c => decide (c.length ≤ 256)) = true := by decide +kernel

theorem flatten_len_le : ∀ (cs : List (List (BitVec 32))),
    (cs.all fun c => decide (c.length ≤ 256)) = true → cs.flatten.length ≤ 256 * cs.length
  | [], _ => by simp
  | c :: cs, h => by
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    have := flatten_len_le cs h.2
    simp only [List.flatten_cons, List.length_append, List.length_cons]
    omega

theorem verifyCode_length : Images.verifyCode.length ≤ 256 * 17 := by
  rw [verifyCode_eq, ← vChunks_length]; exact flatten_len_le _ vChunks_le

end SigGolfCandidate.Verify
