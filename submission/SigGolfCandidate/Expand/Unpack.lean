import SigGolfCandidate.Expand.Copy

/-!
# `expand`: the trailer's spare-bit check (instructions 139 .. 144) and the counter unpack (232 .. 259)

* `spare_run` : the two spare bits of the 14-byte counter trailer (`sig[6093] ≥ 64`) send the run to
  HALT(1), otherwise it continues at 145 with memory untouched.
* `unpack_run` : the two trailer dwords are split into the five 22-bit counters, written as LE32
  words at `WIT + 6328 = 0x20B8` (three dword stores; the last one also zeroes the 4 bytes after the
  witness).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace SigGolfCandidate.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref SigGolfCandidate.Mem

/-- The trailer's spare bits are clear. -/
def SpareOK (sig : List Byte) : Prop := leNat (slice sig sigTrailerOff trailerBytes) < 2 ^ 110

theorem extractByte_toNat_div (w : Word) (k : Nat) :
    (extractByte w k).toNat = w.toNat / 2 ^ (8 * k) % 256 := by
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow]
  rw [Nat.mul_comm k 8]

theorem extractByte_eq_byte (w : Word) (k : Nat) : extractByte w k = byte (w.toNat / 256 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  rw [extractByte_toNat_div, byte_toNat, Nat.pow_mul]

theorem and3_toNat (x : Word) : (x &&& 3#64).toNat = x.toNat % 4 := by
  rw [BitVec.toNat_and]
  exact Nat.and_two_pow_sub_one_eq_mod x.toNat 2

theorem spareOK_iff (sig : List Byte) (hsig : sig.length = 6094) :
    SpareOK sig ↔ (sig.getD 6093 0).toNat < 64 := by
  unfold SpareOK
  have hlen : (slice sig sigTrailerOff trailerBytes).length = 14 := by
    simp [slice, sigTrailerOff_eq, trailerBytes, hsig]
  have hlt := leNat_lt (slice sig sigTrailerOff trailerBytes)
  have hdm := leNat_div_mod (slice sig sigTrailerOff trailerBytes) 13
  have hg : (slice sig sigTrailerOff trailerBytes).getD 13 0 = sig.getD 6093 0 := by
    simp only [slice, sigTrailerOff_eq, trailerBytes, List.getD_eq_getElem?_getD, List.getElem?_take,
      List.getElem?_drop]
    rfl
  rw [hlen] at hlt
  rw [hg] at hdm
  have hb := (sig.getD 6093 0).isLt
  simp only [Nat.reducePow] at hlt hdm hb ⊢
  omega

theorem spare_run (sig : List Byte) (hsig : sig.length = 6094) (u : MachineState) (hs : SigOK u sig)
    (hpc : u.pc = pcOf 139) :
    Run u 8 (fun v => (SpareOK sig → v.pc = pcOf 145 ∧ ∀ a, v.getMem a = u.getMem a) ∧
      (¬ SpareOK sig → Final none v)) := by
  have hst := symRun_sound blk139 codeAt_139 u hpc (by simp only [blk139.res, rv_simp])
  rw [show blk139.res.cycles = 6 by kernel_rfl] at hst
  refine (Run.steps hst (B := 2) ?_).mono (by norm_num) (fun _ h => h)
  have vm : ∀ a, (blk139.res.toState u).getMem a = u.getMem a := toState_getMem_nil rfl u
  have e := sig_dword_byte hs 6088 5 (by norm_num) (by norm_num) (by norm_num)
  rw [show (0x3300 + 6088 : Nat) = 19144 from rfl] at e
  have et := extractByte_toNat_div (u.getMem (BitVec.ofNat 64 19144)) 5
  rw [e] at et
  have s46 : (46#64).toNat % 64 = 46 := rfl
  have key : (u.getMem (BitVec.ofNat 64 19144) >>> ((46#64).toNat % 64) &&& 3#64).toNat =
      (u.getMem (BitVec.ofNat 64 19144)).toNat / 2 ^ 46 % 4 := by
    rw [and3_toNat, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, s46]
  have hiff := spareOK_iff sig hsig
  have hpc' : (blk139.res.toState u).pc =
      if (u.getMem (BitVec.ofNat 64 19144) >>> ((46#64).toNat % 64) &&& 3#64 != 0#64) = true
      then BitVec.ofNat 64 5148 else BitVec.ofNat 64 4676 := by
    simp only [blk139.res, rv_simp]; rfl
  have hb := (sig.getD 6093 0).isLt
  by_cases hsp : SpareOK sig
  · have hz : (u.getMem (BitVec.ofNat 64 19144) >>> ((46#64).toNat % 64) &&& 3#64) = 0#64 := by
      apply BitVec.eq_of_toNat_eq
      rw [key, BitVec.toNat_ofNat]
      have := hiff.mp hsp
      generalize (u.getMem (BitVec.ofNat 64 19144)).toNat = x at et ⊢
      generalize (sig.getD 6093 0).toNat = y at et this hb ⊢
      simp only [Nat.reducePow, Nat.reduceMul, Nat.zero_mod] at et ⊢
      omega
    refine Run.done' ⟨fun _ => ⟨?_, vm⟩, fun h => absurd hsp h⟩
    rw [hpc', hz]; rfl
  · have hnz : (u.getMem (BitVec.ofNat 64 19144) >>> ((46#64).toNat % 64) &&& 3#64) ≠ 0#64 := by
      intro h0
      have h1 := congrArg BitVec.toNat h0
      rw [key, BitVec.toNat_ofNat] at h1
      apply hsp; apply hiff.mpr
      generalize (u.getMem (BitVec.ofNat 64 19144)).toNat = x at et h1
      generalize (sig.getD 6093 0).toNat = y at et hb ⊢
      simp only [Nat.reducePow, Nat.reduceMul, Nat.zero_mod] at et h1
      omega
    have p : (blk139.res.toState u).pc = pcOf 263 := by
      rw [hpc', if_pos (by simpa using hnz)]
    exact (run_fail _ p).mono (le_refl _) (fun t ht => ⟨fun h => absurd h hsp, fun _ => ht⟩)

/-- The five counters from the two trailer dwords. -/
def fieldOf (w0 w1 l : Nat) : Nat := (w0 + 2 ^ 64 * w1) / 2 ^ (22 * l) % 2 ^ 22

theorem field0 (w0 w1 : Nat) : fieldOf w0 w1 0 = w0 % 2 ^ 22 := by unfold fieldOf; omega
theorem field1 (w0 w1 : Nat) : fieldOf w0 w1 1 = w0 / 2 ^ 22 % 2 ^ 22 := by unfold fieldOf; omega
theorem field2 (w0 w1 : Nat) (h : w0 < 2 ^ 64) : fieldOf w0 w1 2 = w0 / 2 ^ 44 + w1 % 4 * 2 ^ 20 := by
  unfold fieldOf; omega
theorem field3 (w0 w1 : Nat) (h : w0 < 2 ^ 64) : fieldOf w0 w1 3 = w1 / 4 % 2 ^ 22 := by unfold fieldOf; omega
theorem field4 (w0 w1 : Nat) (h : w0 < 2 ^ 64) : fieldOf w0 w1 4 = w1 / 2 ^ 24 % 2 ^ 22 := by
  unfold fieldOf; omega

theorem shl_shr (x k : Nat) (hk : k ≤ 64) : x * 2 ^ k % 2 ^ 64 / 2 ^ k = x % 2 ^ (64 - k) := by
  have h : (2 : Nat) ^ 64 = 2 ^ (64 - k) * 2 ^ k := by rw [← Nat.pow_add]; congr 1; omega
  rw [h, Nat.mul_mod_mul_right, Nat.mul_div_cancel _ (by positivity)]

theorem shl42 (x : Nat) : x * 2 ^ 42 % 2 ^ 64 / 2 ^ 42 = x % 2 ^ 22 := shl_shr x 42 (by norm_num)

/-- The dword with bytes `g a .. g (a + 7)`. -/
def dwOf (g : Nat → Byte) (a : Nat) : Nat := leNat ((List.range 8).map fun k => g (a + k))

/-- The byte view after the unpack: the counter words at `0x20B8`, zero after them up to `0x20D0`. -/
def unpackF (g : Nat → Byte) : Nat → Byte := fun a =>
  if 0x20B8 ≤ a ∧ a < 0x20D0 then
    byte (if (a - 0x20B8) / 4 < 5 then
      fieldOf (dwOf g 19136) (dwOf g 19144) ((a - 0x20B8) / 4) / 256 ^ ((a - 0x20B8) % 4) else 0)
  else g a

theorem dwOf_eq (u : MachineState) (g : Nat → Byte) (hg : BytesEq u g) (a : Nat) (ha : a % 8 = 0)
    (hb : a + 8 < 2 ^ 64) : dwOf g a = (u.getMem (BitVec.ofNat 64 a)).toNat := by
  unfold dwOf
  have h : ((List.range 8).map fun k => g (a + k)) =
      (List.range 8).map fun k => byte ((u.getMem (BitVec.ofNat 64 a)).toNat / 256 ^ k) := by
    apply List.map_congr_left
    intro k hk
    rw [List.mem_range] at hk
    rw [← hg (a + k) (by omega), getByte_ofNat _ _ (by omega), show (a + k) / 8 * 8 = a by omega,
      show (a + k) % 8 = k by omega, extractByte_eq_byte]
  rw [h, leNat_map_range]
  exact Nat.mod_eq_of_lt (by have := (u.getMem (BitVec.ofNat 64 a)).isLt; norm_num at this ⊢; omega)

theorem toState_getMem_three {r : Result} {k₁ k₂ k₃ : Addr} {e₁ e₂ e₃ : E}
    (h : r.st.mem = [(k₁, e₁), (k₂, e₂), (k₃, e₃)]) (t : MachineState) (a : Word) :
    (r.toState t).getMem a = if a = k₁.eval t then e₁.eval t else if a = k₂.eval t then e₂.eval t else
      if a = k₃.eval t then e₃.eval t else t.getMem a := by
  rw [Result.toState_getMem, h]; rfl

theorem unpack_run (u : MachineState) (hpc : u.pc = pcOf 232) (g : Nat → Byte) (hg : BytesEq u g) :
    Run u 28 (fun v => v.pc = pcOf 260 ∧ BytesEq v (unpackF g)) := by
  have hst := symRun_sound blk232 codeAt_232 u hpc (by simp only [blk232.res, rv_simp])
  rw [show blk232.res.cycles = 28 by kernel_rfl] at hst
  refine Run.of hst (le_refl _) ⟨by simp only [blk232.res, rv_simp], ?_⟩
  have d0 : dwOf g 19136 = (u.getMem (BitVec.ofNat 64 19136)).toNat := dwOf_eq u g hg 19136 (by norm_num) (by norm_num)
  have d1 : dwOf g 19144 = (u.getMem (BitVec.ofNat 64 19144)).toNat := dwOf_eq u g hg 19144 (by norm_num) (by norm_num)
  generalize hw0 : u.getMem (BitVec.ofNat 64 19136) = w0 at d0
  generalize hw1 : u.getMem (BitVec.ofNat 64 19144) = w1 at d1
  have b0 := w0.isLt
  have b1 := w1.isLt
  have s42 : (42#64).toNat % 64 = 42 := rfl
  have s22 : (22#64).toNat % 64 = 22 := rfl
  have s44 : (44#64).toNat % 64 = 44 := rfl
  have s20 : (20#64).toNat % 64 = 20 := rfl
  have s2 : (2#64).toNat % 64 = 2 := rfl
  have s24 : (24#64).toNat % 64 = 24 := rfl
  have s32 : (32#64).toNat % 64 = 32 := rfl
  have v0 : (w0 <<< ((42#64).toNat % 64) >>> ((42#64).toNat % 64) +
      w0 >>> ((22#64).toNat % 64) <<< ((42#64).toNat % 64) >>> ((42#64).toNat % 64) <<< ((32#64).toNat % 64)).toNat =
      fieldOf w0.toNat w1.toNat 0 + 2 ^ 32 * fieldOf w0.toNat w1.toNat 1 := by
    rw [field0, field1]
    simp only [s42, s22, s32, BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight,
      Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, shl42]
    simp only [Nat.reducePow, Nat.reduceMul] at b0 b1 ⊢
    omega
  have v1 : (w0 >>> ((44#64).toNat % 64) + (w1 &&& 3#64) <<< ((20#64).toNat % 64) +
      w1 >>> ((2#64).toNat % 64) <<< ((42#64).toNat % 64) >>> ((42#64).toNat % 64) <<< ((32#64).toNat % 64)).toNat =
      fieldOf w0.toNat w1.toNat 2 + 2 ^ 32 * fieldOf w0.toNat w1.toNat 3 := by
    rw [field2 _ _ b0, field3 _ _ b0]
    simp only [s44, s20, s2, s42, s32, BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight,
      and3_toNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, shl42]
    simp only [Nat.reducePow, Nat.reduceMul] at b0 b1 ⊢
    omega
  have v2 : (w1 >>> ((24#64).toNat % 64) <<< ((42#64).toNat % 64) >>> ((42#64).toNat % 64)).toNat =
      fieldOf w0.toNat w1.toNat 4 := by
    rw [field4 _ _ b0]
    simp only [s24, s42, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.shiftLeft_eq,
      Nat.shiftRight_eq_div_pow, shl42]
  have hf : ∀ l, fieldOf w0.toNat w1.toNat l < 2 ^ 22 := fun l => Nat.mod_lt _ (by positivity)
  have f0 := hf 0
  have f1 := hf 1
  have f2 := hf 2
  have f3 := hf 3
  have f4 := hf 4
  simp only [Nat.reducePow] at f0 f1 f2 f3 f4
  intro a ha
  rw [getByte_ofNat _ _ ha, toState_getMem_three rfl]
  simp only [blk232.res, rv_simp]
  rw [hw0, hw1]
  unfold unpackF
  rw [d0, d1]
  have hk : a % 8 < 8 := Nat.mod_lt _ (by norm_num)
  by_cases h8392 : a / 8 * 8 = 8392
  · have e8392 : BitVec.ofNat 64 (a / 8 * 8) = 8392#64 := by rw [h8392]
    simp only [e8392, eq_self_iff_true, if_true, ↓reduceIte]
    rw [if_pos (show 0x20B8 ≤ a ∧ a < 0x20D0 by omega), extractByte_eq_byte, v2]
    apply BitVec.eq_of_toNat_eq
    simp only [byte_toNat]
    have hq : a = 8392 + a % 8 := by omega
    generalize a % 8 = k at hq hk
    subst hq
    interval_cases k <;> simp <;> omega
  have n8392 : ¬ BitVec.ofNat 64 (a / 8 * 8) = 8392#64 := fun h => h8392 (by rw [ofNat_eq_iff] at h; omega)
  simp only [n8392, ↓reduceIte]
  by_cases h8384 : a / 8 * 8 = 8384
  · have e8384 : BitVec.ofNat 64 (a / 8 * 8) = 8384#64 := by rw [h8384]
    simp only [e8384, eq_self_iff_true, if_true, ↓reduceIte]
    rw [if_pos (show 0x20B8 ≤ a ∧ a < 0x20D0 by omega), extractByte_eq_byte, v1]
    apply BitVec.eq_of_toNat_eq
    simp only [byte_toNat]
    have hq : a = 8384 + a % 8 := by omega
    generalize a % 8 = k at hq hk
    subst hq
    interval_cases k <;> simp <;> omega
  have n8384 : ¬ BitVec.ofNat 64 (a / 8 * 8) = 8384#64 := fun h => h8384 (by rw [ofNat_eq_iff] at h; omega)
  simp only [n8384, ↓reduceIte]
  by_cases h8376 : a / 8 * 8 = 8376
  · have e8376 : BitVec.ofNat 64 (a / 8 * 8) = 8376#64 := by rw [h8376]
    simp only [e8376, eq_self_iff_true, if_true, ↓reduceIte]
    rw [if_pos (show 0x20B8 ≤ a ∧ a < 0x20D0 by omega), extractByte_eq_byte, v0]
    apply BitVec.eq_of_toNat_eq
    simp only [byte_toNat]
    have hq : a = 8376 + a % 8 := by omega
    generalize a % 8 = k at hq hk
    subst hq
    interval_cases k <;> simp <;> omega
  have n8376 : ¬ BitVec.ofNat 64 (a / 8 * 8) = 8376#64 := fun h => h8376 (by rw [ofNat_eq_iff] at h; omega)
  simp only [n8376, ↓reduceIte]
  rw [if_neg (show ¬ (0x20B8 ≤ a ∧ a < 0x20D0) by omega), ← getByte_ofNat _ _ ha, hg a ha]

end SigGolfCandidate.Expand
