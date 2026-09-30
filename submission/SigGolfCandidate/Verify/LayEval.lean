import SigGolfCandidate.Verify.LayCheck

/-!
# The layer section: values of the symbolic words (route, counter, sub-word stores, the SWAR
digit-sum check, the digits) and the hash-input formats
-/

set_option linter.unusedSimpArgs false

namespace SigGolfCandidate.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

/-! ## Layer context -/

structure YCtx where
  wl : List Byte
  pk : List Byte
  idx : Nat
  lay : Nat

def YCtx.ok (c : YCtx) : Prop := c.lay < 6 ∧ c.idx < 2 ^ 34 ∧ c.wl.length = 6064 ∧ c.pk.length = 16
def YCtx.e (c : YCtx) : Nat := c.idx / 2 ^ sT c.lay % 2 ^ hT c.lay
def YCtx.tau (c : YCtx) : Nat := c.idx / 2 ^ (sT c.lay + hT c.lay)
def YCtx.h (c : YCtx) : Nat := hT c.lay
def YCtx.t6 (c : YCtx) : Nat := c.tau + 2 ^ 32 * c.e

theorem YCtx.e_lt (c : YCtx) (hc : c.ok) : c.e < 2048 := by
  have := Nat.mod_lt (c.idx / 2 ^ sT c.lay) (show 0 < 2 ^ hT c.lay from Nat.two_pow_pos _)
  have := Nat.pow_le_pow_right (show 0 < 2 by decide) (hT_bounds c.lay hc.1).2.1
  unfold YCtx.e; omega

theorem YCtx.e_lt_h (c : YCtx) : c.e < 2 ^ c.h := Nat.mod_lt _ (Nat.two_pow_pos _)

theorem YCtx.tau_lt (c : YCtx) (hc : c.ok) : c.tau < 2 ^ 30 := by
  have h4 := (hT_bounds c.lay hc.1).2.2.2
  unfold YCtx.tau
  apply Nat.div_lt_of_lt_mul
  calc c.idx < 2 ^ 34 := hc.2.1
    _ = 2 ^ 4 * 2 ^ 30 := by norm_num
    _ ≤ 2 ^ (sT c.lay + hT c.lay) * 2 ^ 30 :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) h4)

theorem YCtx.route_eq (c : YCtx) (hc : c.ok) : route c.idx c.lay = (c.e, c.tau) := route_eqY _ _ hc.1

theorem YCtx.h_eq (c : YCtx) (hc : c.ok) : c.h = height c.lay := hT_eq _ hc.1

/-! ## Words -/

theorem toNat_ofNat64 (k : Nat) (h : k < 2 ^ 64) : (BitVec.ofNat 64 k).toNat = k := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem srl_eval (s : MachineState) (e : E) (x k : Nat) (hx : x < 2 ^ 64) (hk : k < 64)
    (h : e.eval s = BitVec.ofNat 64 x) :
    (E.bin .srl e (cw k)).eval s = BitVec.ofNat 64 (x / 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [E.eval, BinOp.eval, cw, h, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow]
  have : x / 2 ^ k ≤ x := Nat.div_le_self _ _
  rw [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega), Nat.mod_eq_of_lt hk,
    Nat.mod_eq_of_lt (show x / 2 ^ k < 2 ^ 64 by omega)]

theorem and_mask_eval' (s : MachineState) (e : E) (x k : Nat) (hx : x < 2 ^ 64) (hk : k ≤ 64)
    (h : e.eval s = BitVec.ofNat 64 x) :
    (E.bin .and e (cw (2 ^ k - 1))).eval s = BitVec.ofNat 64 (x % 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [E.eval, BinOp.eval, cw, h, BitVec.toNat_and, BitVec.toNat_ofNat]
  have : 2 ^ k ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) hk
  have : x % 2 ^ k < 2 ^ 64 := lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _)) this
  rw [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt (show 2 ^ k - 1 < 2 ^ 64 by omega),
    Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt this]

theorem x22_eval (c : YCtx) (hc : c.ok) (s : MachineState)
    (h : s.getReg .x22 = BitVec.ofNat 64 c.idx) : (E.reg .x22).eval s = BitVec.ofNat 64 c.idx := h

theorem eE_eval (c : YCtx) (hc : c.ok) (s : MachineState) (h : s.getReg .x22 = BitVec.ofNat 64 c.idx) :
    (eE c.lay).eval s = BitVec.ofNat 64 c.e := by
  have hb := hT_bounds c.lay hc.1
  have hi : c.idx < 2 ^ 64 := lt_trans hc.2.1 (by norm_num)
  have h1 := srl_eval s (.reg .x22) c.idx (sT c.lay) hi (by omega) h
  have : c.idx / 2 ^ sT c.lay ≤ c.idx := Nat.div_le_self _ _
  exact and_mask_eval' s _ _ _ (by omega) (by omega) h1

theorem tauE_eval (c : YCtx) (hc : c.ok) (s : MachineState) (h : s.getReg .x22 = BitVec.ofNat 64 c.idx) :
    (tauE c.lay).eval s = BitVec.ofNat 64 c.tau := by
  have hb := hT_bounds c.lay hc.1
  have hi : c.idx < 2 ^ 64 := lt_trans hc.2.1 (by norm_num)
  exact srl_eval s (.reg .x22) c.idx _ hi (by omega) h

theorem t6E_eval (c : YCtx) (hc : c.ok) (s : MachineState) (h : s.getReg .x22 = BitVec.ofNat 64 c.idx) :
    (t6E c.lay).eval s = BitVec.ofNat 64 c.t6 := by
  have he := c.e_lt hc
  have ht := c.tau_lt hc
  simp only [t6E, E.eval, BinOp.eval, cw]
  rw [tauE_eval c hc s h, eE_eval c hc s h]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, YCtx.t6]
  rw [Nat.mod_eq_of_lt (show c.tau < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show c.e < 2 ^ 64 by omega)]
  norm_num
  omega

/-- The counter `c_lay`. -/
theorem ctrL_eval (c : YCtx) (hc : c.ok) (s : MachineState)
    (hW : ∀ j, 16 ≤ j → j < 880 → s.getMem (BitVec.ofNat 64 (0x800 + 8 * j)) = w64 (slice c.wl (8 * j) 8)) :
    (ctrL c.lay).eval s = BitVec.ofNat 64 (witCounter c.wl c.lay) := by
  have hlay := hc.1
  have hwl := hc.2.2.1
  have hw := hW ((6040 + 8 * (c.lay / 2)) / 8) (by omega) (by omega)
  rw [show 8 * ((6040 + 8 * (c.lay / 2)) / 8) = 6040 + 8 * (c.lay / 2) by omega] at hw
  apply BitVec.eq_of_toNat_eq
  simp only [ctrL, ldE, Rv.E.eval, UnOp.eval, LoadKind.fromWord, cw]
  rw [show 8088 + 8 * (c.lay / 2) = 0x800 + (6040 + 8 * (c.lay / 2)) by omega, hw]
  simp only [extractWord32, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth,
    BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  rw [w64_toNat _ (by simp [slice]), leNat_slice8 _ _ (by omega), witCounter]
  have hA := leNat_lt (slice c.wl (6040 + 8 * (c.lay / 2)) 4)
  have hB := leNat_lt (slice c.wl (6040 + 8 * (c.lay / 2) + 4) 4)
  have l4 : ∀ o, (slice c.wl o 4).length ≤ 4 := fun o => by simp [slice]
  have hA' : leNat (slice c.wl (6040 + 8 * (c.lay / 2)) 4) < 2 ^ 32 :=
    lt_of_lt_of_le hA (le_trans (Nat.pow_le_pow_right (by decide) (l4 _)) (by norm_num))
  have hB' : leNat (slice c.wl (6040 + 8 * (c.lay / 2) + 4) 4) < 2 ^ 32 :=
    lt_of_lt_of_le hB (le_trans (Nat.pow_le_pow_right (by decide) (l4 _)) (by norm_num))
  have hct := witCounter_lt c.wl c.lay
  rcases Nat.mod_two_eq_zero_or_one c.lay with h | h
  · rw [show 4 * (c.lay % 2) / 4 * 32 = 0 by rw [h], show witCounters + 4 * c.lay = 6040 + 8 * (c.lay / 2) by
      rw [witCounters_eq]; omega]
    generalize leNat (slice c.wl (6040 + 8 * (c.lay / 2)) 4) = A at *
    generalize leNat (slice c.wl (6040 + 8 * (c.lay / 2) + 4) 4) = B at *
    norm_num at hA' hB' ⊢
    omega
  · rw [show 4 * (c.lay % 2) / 4 * 32 = 32 by rw [h], show witCounters + 4 * c.lay = 6040 + 8 * (c.lay / 2) + 4 by
      rw [witCounters_eq]; omega]
    generalize leNat (slice c.wl (6040 + 8 * (c.lay / 2)) 4) = A at *
    generalize leNat (slice c.wl (6040 + 8 * (c.lay / 2) + 4) 4) = B at *
    norm_num at hA' hB' ⊢
    omega

/-! ## Sub-word stores -/

theorem replaceByte_toNat (w : BitVec 64) (pos : Nat) (hp : pos < 8) (b : BitVec 8) :
    (replaceByte w pos b).toNat =
      w.toNat % 2 ^ (8 * pos) + 2 ^ (8 * pos) * b.toNat + 2 ^ (8 * pos + 8) * (w.toNat / 2 ^ (8 * pos + 8)) := by
  have hb := b.isLt
  have hw := w.isLt
  have hlt : w.toNat % 2 ^ (8 * pos) + 2 ^ (8 * pos) * b.toNat + 2 ^ (8 * pos + 8) * (w.toNat / 2 ^ (8 * pos + 8)) < 2 ^ 64 := by
    have h1 : w.toNat % 2 ^ (8 * pos) < 2 ^ (8 * pos) := Nat.mod_lt _ (Nat.two_pow_pos _)
    have h2 : 2 ^ (8 * pos + 8) * (w.toNat / 2 ^ (8 * pos + 8)) + w.toNat % 2 ^ (8 * pos + 8) = w.toNat := Nat.div_add_mod _ _
    have h3 : 2 ^ (8 * pos + 8) = 2 ^ (8 * pos) * 256 := by rw [Nat.pow_add]
    have h4 : w.toNat % 2 ^ (8 * pos) ≤ w.toNat % 2 ^ (8 * pos + 8) := by
      rw [h3, Nat.mod_mul]; omega
    have h5 : 2 ^ (8 * pos) * b.toNat + w.toNat % 2 ^ (8 * pos) < 2 ^ (8 * pos + 8) := by
      have := Nat.mul_le_mul_left (2 ^ (8 * pos)) (show b.toNat ≤ 255 by omega)
      rw [h3]; omega
    have h6 : 2 ^ (8 * pos + 8) * (w.toNat / 2 ^ (8 * pos + 8)) ≤ w.toNat := by omega
    have h7 : 2 ^ (8 * pos + 8) ∣ 2 ^ 64 := Nat.pow_dvd_pow 2 (by omega)
    have h8 : w.toNat / 2 ^ (8 * pos + 8) < 2 ^ 64 / 2 ^ (8 * pos + 8) := by
      apply Nat.div_lt_div_of_lt_of_dvd h7 hw
    have h9 : 2 ^ (8 * pos + 8) * (w.toNat / 2 ^ (8 * pos + 8) + 1) ≤ 2 ^ 64 := by
      have := Nat.mul_le_mul_left (2 ^ (8 * pos + 8)) (show w.toNat / 2 ^ (8 * pos + 8) + 1 ≤ 2 ^ 64 / 2 ^ (8 * pos + 8) by omega)
      rwa [Nat.mul_div_cancel' h7] at this
    rw [Nat.mul_add, Nat.mul_one] at h9
    omega
  have key : replaceByte w pos b = BitVec.ofNat 64
      (w.toNat % 2 ^ (8 * pos) + 2 ^ (8 * pos) * b.toNat + 2 ^ (8 * pos + 8) * (w.toNat / 2 ^ (8 * pos + 8))) := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    unfold replaceByte
    simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_ofNat, BitVec.getLsbD_setWidth, hj, decide_true, Bool.true_and]
    have e : w.toNat % 2 ^ (8 * pos) + 2 ^ (8 * pos) * b.toNat + 2 ^ (8 * pos + 8) * (w.toNat / 2 ^ (8 * pos + 8)) =
        2 ^ (8 * pos) * (2 ^ 8 * (w.toNat / 2 ^ (8 * pos + 8)) + b.toNat) + w.toNat % 2 ^ (8 * pos) := by
      rw [Nat.pow_add]; ring
    rw [e, Nat.testBit_two_pow_mul_add _ (Nat.mod_lt _ (Nat.two_pow_pos _)),
      Nat.testBit_two_pow_mul_add _ hb, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
    simp only [← BitVec.testBit_toNat]
    by_cases h1 : j < 8 * pos
    · simp [h1, show j < pos * 8 by omega]
    · by_cases h2 : j - 8 * pos < 8
      · have : Nat.testBit 255 (j - pos * 8) = true := by
          have : j - pos * 8 < 8 := by omega
          interval_cases (j - pos * 8) <;> decide
        simp [h1, show ¬ j < pos * 8 by omega, show j - pos * 8 < 64 by omega, this,
          show j - 8 * pos = j - pos * 8 by omega]
        intro h; omega
      · have : Nat.testBit 255 (j - pos * 8) = false := by
          apply Nat.testBit_lt_two_pow
          exact lt_of_lt_of_le (show 255 < 2 ^ 8 by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega))
        have hb' : b.toNat.testBit (j - pos * 8) = false :=
          Nat.testBit_lt_two_pow (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num) (by omega)))
        simp [h1, h2, show ¬ j < pos * 8 by omega, this, hb', show j - 8 * pos - 8 + (8 * pos + 8) = j by omega]
  rw [key, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]

/-- The chain tweak word `1 | 1 << 8 | lay << 16 | b << 32 | d << 40`. -/
def cbW (lay b d : Nat) : Word := BitVec.ofNat 64 (257 + 65536 * lay + 2 ^ 32 * b + 2 ^ 40 * d)

theorem stB_cb (lay b d x : Nat) (hlay : lay < 6) (hb : b < 256) (hd : d < 256) (hx : x < 256) (pos : Nat)
    (hp : pos = 4 ∨ pos = 5) :
    StoreKind.merge .b (cbW lay b d) pos (BitVec.ofNat 64 x) =
      if pos = 4 then cbW lay x d else cbW lay b x := by
  apply BitVec.eq_of_toNat_eq
  simp only [StoreKind.merge]
  rw [replaceByte_toNat _ _ (by omega)]
  have e8 : ((BitVec.ofNat 64 x).truncate 8).toNat = x := by
    simp [BitVec.toNat_setWidth]; omega
  rw [e8]
  unfold cbW
  rcases hp with rfl | rfl
  · simp only [if_true, BitVec.toNat_ofNat]
    norm_num
    omega
  · simp only [show (5 : Nat) ≠ 4 by decide, if_false, BitVec.toNat_ofNat]
    norm_num
    omega

/-- After the encoding's chain setup: `sw H, CB; sw x0, CB+4`. -/
theorem cb_setup (w : Word) (lay : Nat) (hlay : lay < 6) :
    StoreKind.merge .w (StoreKind.merge .w w 0 (BitVec.ofNat 64 (257 + 65536 * lay))) 4 (BitVec.ofNat 64 0) =
      cbW lay 0 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [merge_w4_toNat, merge_w0_toNat]
  unfold cbW
  simp only [BitVec.toNat_ofNat]
  norm_num
  omega

/-! ## The encoding check -/

theorem nibW_toNat : nibW.toNat = nibM := by unfold nibW nibM; rfl
theorem laneW_toNat : laneW.toNat = laneM := by unfold laneW laneM; rfl

theorem ofNat_toNat_shift (k : Nat) (hk : k < 64) : (BitVec.ofNat 64 k).toNat % 64 = k := by
  simp only [BitVec.toNat_ofNat]; omega

theorem sw_eval (u : MachineState) :
    ((E.bin .and sw5 (cw 1023)).eval u).toNat =
      swar4 (u.getMem (BitVec.ofNat 64 320)).toNat (u.getMem (BitVec.ofNat 64 328)).toNat := by
  generalize ha : (u.getMem (BitVec.ofNat 64 320)) = A
  generalize hb : (u.getMem (BitVec.ofNat 64 328)) = B
  have eA : aE.eval u = A := ha
  have eB : bE.eval u = B := hb
  have s4 : (BitVec.ofNat 64 4).toNat % 64 = 4 := by decide
  have s8 : (BitVec.ofNat 64 8).toNat % 64 = 8 := by decide
  have s16 : (BitVec.ofNat 64 16).toNat % 64 = 16 := by decide
  have s32 : (BitVec.ofNat 64 32).toNat % 64 = 32 := by decide
  have h1 : (sw1.eval u).toNat = (((((A.toNat / 16) &&& nibM) + (A.toNat &&& nibM)) % 2 ^ 64 +
      ((B.toNat / 16) &&& nibM)) % 2 ^ 64 + (B.toNat &&& nibM)) % 2 ^ 64 := by
    simp only [sw1, E.eval, BinOp.eval, eA, eB, nibE, cw, s4, BitVec.toNat_add, BitVec.toNat_and,
      BitVec.toNat_ushiftRight, nibW_toNat, Nat.shiftRight_eq_div_pow]
    all_goals norm_num
  have h2 : (sw2.eval u).toNat = ((sw1.eval u).toNat + (sw1.eval u).toNat / 256) % 2 ^ 64 := by
    simp only [sw2, E.eval, BinOp.eval, cw, s8, BitVec.toNat_add, BitVec.toNat_ushiftRight,
      Nat.shiftRight_eq_div_pow]
    all_goals norm_num
  have h3 : (sw3.eval u).toNat = (sw2.eval u).toNat &&& laneM := by
    simp only [sw3, E.eval, BinOp.eval, laneE, BitVec.toNat_and, laneW_toNat]
  have h4 : (sw4.eval u).toNat = ((sw3.eval u).toNat + (sw3.eval u).toNat / 65536) % 2 ^ 64 := by
    simp only [sw4, E.eval, BinOp.eval, cw, s16, BitVec.toNat_add, BitVec.toNat_ushiftRight,
      Nat.shiftRight_eq_div_pow]
    all_goals norm_num
  have h5 : (sw5.eval u).toNat = ((sw4.eval u).toNat + (sw4.eval u).toNat / 4294967296) % 2 ^ 64 := by
    simp only [sw5, E.eval, BinOp.eval, cw, s32, BitVec.toNat_add, BitVec.toNat_ushiftRight,
      Nat.shiftRight_eq_div_pow]
    all_goals norm_num
  have h6 : ((E.bin .and sw5 (cw 1023)).eval u).toNat = (sw5.eval u).toNat &&& 1023 := by
    simp only [E.eval, BinOp.eval, cw, BitVec.toNat_and, BitVec.toNat_ofNat]
    all_goals norm_num
  rw [h6, h5, h4, h3, h2, h1]
  rfl

theorem swF_eq_zero (u : MachineState) :
    swF.eval u = 0 ↔
      swar4 (u.getMem (BitVec.ofNat 64 320)).toNat (u.getMem (BitVec.ofNat 64 328)).toNat = 312 := by
  have h := sw_eval u
  have hle : ((E.bin .and sw5 (cw 1023)).eval u).toNat ≤ 1023 := by
    simp only [E.eval, BinOp.eval, cw, BitVec.toNat_and, BitVec.toNat_ofNat]
    exact le_trans Nat.and_le_right (by norm_num)
  have e : swF.eval u = (E.bin .and sw5 (cw 1023)).eval u + (-312#64) := rfl
  rw [e, ← h]
  generalize (E.bin .and sw5 (cw 1023)).eval u = X at hle ⊢
  constructor
  · intro h0
    have := congrArg BitVec.toNat h0
    rw [BitVec.toNat_add] at this
    have hn : (-312#64).toNat = 2 ^ 64 - 312 := by decide
    rw [hn] at this
    simp at this
    omega
  · intro h0
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, h0]
    decide

/-! ## Digits -/

theorem shr4_eval (u : MachineState) (e : E) : ∀ k, k ≤ 15 →
    ((shr4 k e).eval u).toNat = (e.eval u).toNat / 16 ^ k
  | 0, _ => by simp [shr4]
  | k + 1, hk => by
    simp only [shr4, E.eval, BinOp.eval, cw, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    rw [shr4_eval u e k (by omega), show (BitVec.ofNat 64 4).toNat % 64 = 4 by decide, Nat.div_div_eq_div_mul,
      ← Nat.pow_succ]

theorem digE_eval (u : MachineState) (i : Nat) (hi : i < 32) :
    (digE i).eval u = BitVec.ofNat 64
      ((if i < 16 then (u.getMem (BitVec.ofNat 64 320)).toNat else (u.getMem (BitVec.ofNat 64 328)).toNat) /
        16 ^ (i % 16) % 16) := by
  apply BitVec.eq_of_toNat_eq
  simp only [digE, E.eval, BinOp.eval, cw, BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [shr4_eval u _ _ (by omega)]
  have : ∀ n, n &&& 15 % 2 ^ 64 = n % 16 := fun n => by
    rw [show 15 % 2 ^ 64 = 2 ^ 4 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]
  rw [this]
  split <;> (simp only [aE, bE, ldE, cw, E.eval]; exact
    (Nat.mod_eq_of_lt (lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by norm_num))).symm)

/-- The digits of an encoding answer (`d0`, `d1` = its two low doublewords). -/
def digitsOf (d0 d1 : Nat) : List Nat := digitsOfWord d0 ++ digitsOfWord d1

theorem length_digitsOf (d0 d1 : Nat) : (digitsOf d0 d1).length = 32 := by
  simp [digitsOf, digitsOfWord]

theorem digitsOf_getD (d0 d1 i : Nat) (hi : i < 32) :
    (digitsOf d0 d1).getD i 0 = (if i < 16 then d0 else d1) / 16 ^ (i % 16) % 16 := by
  unfold digitsOf digitsOfWord
  rw [List.getD_eq_getElem?_getD]
  split
  · rename_i h
    rw [List.getElem?_append_left (by simp; omega)]
    simp [List.getElem?_map, Nat.mod_eq_of_lt h, h]
  · rename_i h
    rw [List.getElem?_append_right (by simp; omega)]
    simp only [List.length_map, List.length_range, List.getElem?_map, List.getElem?_range (show i - 16 < 16 by omega),
      Option.map_some, Option.getD_some]
    rw [show i % 16 = i - 16 by omega]

theorem digitsOf_lt (d0 d1 i : Nat) (hi : i < 32) : (digitsOf d0 d1).getD i 0 < 16 := by
  rw [digitsOf_getD _ _ _ hi]; exact Nat.mod_lt _ (by decide)

theorem answer_d0 (a : BitVec 256) : leNat (slice (answerBytes 16 a) 0 8) = (a.extractLsb' 0 64).toNat := by
  rw [← vw0_answer, vw0, w64_toNat _ (by simp)]
  simp [slice]

theorem answer_d1 (a : BitVec 256) : leNat (slice (answerBytes 16 a) 8 8) = (a.extractLsb' 64 64).toNat := by
  rw [← vw1_answer, vw1, w64_toNat _ (by simp)]
  simp only [slice]
  rw [List.take_of_length_le (by simp)]

theorem decodeDigits_answer (a : BitVec 256) :
    decodeDigits (answerBytes 16 a) =
      if (digitsOf (a.extractLsb' 0 64).toNat (a.extractLsb' 64 64).toNat).sum = targetSum
      then some (digitsOf (a.extractLsb' 0 64).toNat (a.extractLsb' 64 64).toNat) else none := by
  unfold decodeDigits
  simp only [answer_d0, answer_d1]
  rfl

theorem digitsOf_sum (d0 d1 : Nat) : (digitsOf d0 d1).sum = swar4 d0 d1 := by
  rw [swar4_eq, digitsOf, List.sum_append]

/-! ## Hash inputs -/

theorem blk_pad64' (l : List Byte) (hl : l.length = 64) : (⟨0, ofList _ l⟩ : Query) = pad64 l := by
  unfold pad64 padTo64 padBlocks
  rw [hl]
  simp [zeros]

/-- The chain block `tw' || 0^32 || v` of chain step `mu` (`p' = mu - 1 + 256 i`). -/
theorem fmt_chainInput_words (lay tau e i mu : Nat) (v : Val) (hv : v.length = 16) (hmu : 1 ≤ mu)
    (hmu' : mu ≤ 16) (hi : i < 2 ^ 24) :
    fmt (chainInput lay tau e i mu v) = queryOfWords 0
      [BitVec.ofNat 64 (twLo 1 lay tau (mu - 1 + 256 * i)), BitVec.ofNat 64 (twHi tau e), 0, 0, 0, 0,
        vw0 v, vw1 v] := by
  rw [fmt_chainInput _ _ _ _ _ _ hv hmu hmu' hi]
  have hl : (tweak 1 lay tau (mu - 1 + 256 * i) e ++ zeros 32 ++ v).length ≤ 8 * 8 := by
    simp [length_tweak, hv]
  have h8 : wordsOfN 8 (tweak 1 lay tau (mu - 1 + 256 * i) e ++ (zeros 32 ++ v)) =
      wordsOfN 2 (tweak 1 lay tau (mu - 1 + 256 * i) e) ++ wordsOfN 6 (zeros 32 ++ v) :=
    wordsOfN_append 2 6 _ _ (by simp [length_tweak])
  have h6 : wordsOfN 6 (zeros 32 ++ v) = wordsOfN 4 (zeros (8 * 4)) ++ wordsOfN 2 v :=
    wordsOfN_append 4 2 _ _ (by simp [length_zeros])
  have h2 : wordsOfN 2 v = [vw0 v, vw1 v] := by
    have := wordsOfN_val_append v hv 0 []
    simpa [wordsOfN] using this
  have hw : wordsOfN 8 (tweak 1 lay tau (mu - 1 + 256 * i) e ++ zeros 32 ++ v) =
      [BitVec.ofNat 64 (twLo 1 lay tau (mu - 1 + 256 * i)), BitVec.ofNat 64 (twHi tau e), 0, 0, 0, 0,
        vw0 v, vw1 v] := by
    rw [List.append_assoc, h8, h6, wordsOfN_tweak, wordsOfN_zeros, h2]; rfl
  unfold queryOfWords ofList
  rw [← hw, wordsToNat_wordsOfN 8 _ hl]

/-- The node block of a hypertree node (tag 3): the heap index replaces `(lam, j)`. -/
theorem fmt_nodeInput_words (lay tau lam j : Nat) (l r : Val) (hl : l.length = 16) (hr : r.length = 16)
    (hlay : lay < 256) (hlam : lam < 2 ^ 32) (hj : j < 2 ^ 32) :
    fmt (nodeInput lay tau lam j l r) = queryOfWords 0
      [BitVec.ofNat 64 (twLo 3 lay tau 0), BitVec.ofNat 64 (twHi tau (heapIndex (height lay) lam j)), 0, 0,
        vw0 l, vw1 l, vw0 r, vw1 r] := by
  rw [fmt_nodeInput _ _ _ _ _ _ hl hr hlay hlam hj, blk_pad64' _ (by simp [hl, hr])]
  exact pad64_nodeInput _ _ _ _ _ _ hl hr

/-! ## Values -/

theorem leNat_inj : ∀ (l1 l2 : List Byte), l1.length = l2.length → leNat l1 = leNat l2 → l1 = l2
  | [], [], _, _ => rfl
  | a :: l1, b :: l2, hl, h => by
    simp only [leNat] at h
    have ha := a.isLt; have hb := b.isLt
    have h1 : a.toNat = b.toNat := by omega
    have h2 : leNat l1 = leNat l2 := by omega
    rw [BitVec.eq_of_toNat_eq h1, leNat_inj l1 l2 (by simpa using hl) h2]
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

theorem w64_inj (l1 l2 : List Byte) (h1 : l1.length = 8) (h2 : l2.length = 8) :
    w64 l1 = w64 l2 ↔ l1 = l2 := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rw [w64_toNat _ (by omega), w64_toNat _ (by omega)] at this
    exact leNat_inj _ _ (by omega) this
  · intro h; rw [h]

theorem val_eq_iff (M P : Val) (hM : M.length = 16) (hP : P.length = 16) :
    M = P ↔ vw0 M = w64 (P.take 8) ∧ vw1 M = w64 (P.drop 8) := by
  unfold vw0 vw1
  rw [w64_inj _ _ (by simp; omega) (by simp; omega), w64_inj _ _ (by simp; omega) (by simp; omega)]
  constructor
  · intro h; rw [h]; exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    rw [← List.take_append_drop 8 M, ← List.take_append_drop 8 P, h1, h2]

end SigGolfCandidate.Verify
