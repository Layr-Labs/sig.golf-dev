import SigGolfCandidate.Expand.Unpack

/-!
# `expand`: the copy phase (instructions 145 .. 262)

`rho` (4 words), the pi bytes (`pi_loop`: byte `s` = low byte of `KEYS[s]`), the secrets (60 words),
the five layer bodies, the counter unpack; HALT(0). The witness buffer's byte view afterwards is
`unpackF (applyCopies copyRest (piF A 15 (applyCopy rho f0)))` of the byte view `f0` before the phase.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace SigGolfCandidate.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref SigGolfCandidate.Mem


/-- The pi bytes on top of `g`. -/
def piF (A : Nat → Nat) (j : Nat) (g : Nat → Byte) : Nat → Byte := fun a =>
  if 0x810 ≤ a ∧ a < 0x810 + j then byte (A (a - 0x810)) else g a

/-- The copies after the pi loop: the secrets, then the five layer bodies. -/
def copyRest : List (Nat × Nat × Nat) :=
  [(0x3310, 0x820, 60), (0x3B80, 0x1178, 212), (0x3ED0, 0x14C8, 192), (0x41D0, 0x17C8, 192),
    (0x44D0, 0x1AC8, 192), (0x47D0, 0x1DC8, 188)]

theorem pi_loop (A : Nat → Nat) (g : Nat → Byte) :
    ∀ k (v : MachineState), k ≤ 15 → (v.pc = if k = 0 then pcOf 166 else pcOf 159) →
      v.getReg .x8 = BitVec.ofNat 64 (15 - k) → v.getReg .x25 = BitVec.ofNat 64 0x810 →
      BytesEq v (piF A (15 - k) g) → ArrOk v A →
      Run v (7 * k) (fun w => w.pc = pcOf 166 ∧ BytesEq w (piF A 15 g) ∧ ArrOk w A) := by
  intro k
  induction k with
  | zero => intro v _ hpc _ _ hb ha; exact Run.done' ⟨by simpa using hpc, by simpa using hb, ha⟩
  | succ k ih =>
    intro v hk hpc h8 h25 hb ha
    rw [if_neg (Nat.succ_ne_zero k)] at hpc
    have hj : 15 - (k + 1) < 15 := by omega
    have := pi_body v hpc (15 - (k + 1)) (A (15 - (k + 1))) hj h8 h25 (ha _ hj)
    refine (Run.bind this (fun w ⟨w8, w25, wpc, wb, wm⟩ => ih w (by omega) ?_ ?_ w25 ?_ ?_)).mono
      (by ring_nf; omega) (fun _ h => h)
    · rw [wpc]; by_cases h0 : k = 0
      · rw [if_pos (by omega), if_pos h0]
      · rw [if_neg (by omega), if_neg h0]
    · rw [w8]; exact ofNat_congr (by omega)
    · intro a ha'
      rw [wb a ha', hb a ha']
      unfold piF
      by_cases h1 : a = 0x810 + (15 - (k + 1))
      · rw [if_pos h1, if_pos (by omega), show a - 0x810 = 15 - (k + 1) by omega]; rfl
      · rw [if_neg h1]
        by_cases h2 : 0x810 ≤ a ∧ a < 0x810 + (15 - (k + 1))
        · rw [if_pos h2, if_pos (by omega)]
        · rw [if_neg h2, if_neg (by omega)]
    · intro p hp
      rw [wm _ (by rw [Ne, ofNat_eq_iff]; omega)]; exact ha p hp




/-- The copy phase (instructions 145 .. 262): witness bytes, then HALT(0). -/
theorem copy_run (A : Nat → Nat) (u : MachineState) (hpc : u.pc = pcOf 145) (hA : ArrOk u A) :
    Run u 6413 (fun v => fetch image v = some (.base .ECALL) ∧ v.getReg .x5 = 1 ∧ v.getReg .x10 = 0 ∧
      BytesEq v (unpackF (applyCopies copyRest (piF A 15 (applyCopy (0x3300, 0x800, 4)
        (fun a => u.getByte (BitVec.ofNat 64 a))))))) := by
  have hf0 : BytesEq u (fun a => u.getByte (BitVec.ofNat 64 a)) := fun a _ => rfl
  have s1 := stageRun (e := 156) blk145 codeAt_145 rfl rfl rfl rfl rfl rfl codeAt_150 (by decide) (by decide) u hpc _ hf0
  refine Run.seq (B₂ := 6384) s1 (fun v ⟨vpc, vb⟩ => ?_) (by simp only [show blk145.res.cycles = 5 by kernel_rfl]; norm_num)
  -- the keys are untouched by the rho copy
  have hAv : ArrOk v A := by
    intro p hp
    rw [getMem_eq_of_bytes u v (0x6E0 + 8 * p) (by omega) (by omega) (fun k hk => by
      rw [vb _ (by omega)]; unfold applyCopy; dsimp only; rw [if_neg (by omega)]), hA p hp]
  set g := applyCopy (0x3300, 0x800, 4) (fun a => u.getByte (BitVec.ofNat 64 a)) with hg
  refine Run.seq (B₂ := 6381) (Run.steps (symRun_sound blk156 codeAt_156 v vpc (by simp only [blk156.res, rv_simp]))
    (Run.done (P := fun x => x = blk156.res.toState v) rfl)) (fun v1 hv1 => ?_)
    (by simp only [show blk156.res.cycles = 3 by kernel_rfl]; norm_num)
  subst hv1
  have p1 : (blk156.res.toState v).pc = pcOf 159 := by simp only [blk156.res, rv_simp]
  have m1 : ∀ a, (blk156.res.toState v).getMem a = v.getMem a := toState_getMem_nil rfl v
  have hb1 : BytesEq (blk156.res.toState v) (piF A (15 - 15) g) := by
    intro a ha; rw [getByte_ofNat _ _ ha, m1, ← getByte_ofNat _ _ ha, vb a ha]
    simp [piF]
  have pl := pi_loop A g 15 _ le_rfl (by rw [p1]; rfl) (by simp only [blk156.res, rv_simp])
    (by simp only [blk156.res, rv_simp]) hb1 (hAv.frame m1)
  refine Run.seq (B₂ := 6276) pl (fun w ⟨wpc, wb, _⟩ => ?_) (by norm_num)
  set F := piF A 15 g
  have st1 := stageRun (e := 177) blk166 codeAt_166 rfl rfl rfl rfl rfl rfl codeAt_171 (by decide) (by decide) w wpc F wb
  refine Run.seq (B₂ := 5911) st1 (fun w1 ⟨p1, b1⟩ => ?_) (by simp only [show blk166.res.cycles = 5 by kernel_rfl]; norm_num)
  have st2 := stageRun (e := 188) blk177 codeAt_177 rfl rfl rfl rfl rfl rfl codeAt_182 (by decide) (by decide) w1 p1 _ b1
  refine Run.seq (B₂ := 4634) st2 (fun w2 ⟨p2, b2⟩ => ?_) (by simp only [show blk177.res.cycles = 5 by kernel_rfl]; norm_num)
  have st3 := stageRun (e := 199) blk188 codeAt_188 rfl rfl rfl rfl rfl rfl codeAt_193 (by decide) (by decide) w2 p2 _ b2
  refine Run.seq (B₂ := 3477) st3 (fun w3 ⟨p3, b3⟩ => ?_) (by simp only [show blk188.res.cycles = 5 by kernel_rfl]; norm_num)
  have st4 := stageRun (e := 210) blk199 codeAt_199 rfl rfl rfl rfl rfl rfl codeAt_204 (by decide) (by decide) w3 p3 _ b3
  refine Run.seq (B₂ := 2320) st4 (fun w4 ⟨p4, b4⟩ => ?_) (by simp only [show blk199.res.cycles = 5 by kernel_rfl]; norm_num)
  have st5 := stageRun (e := 221) blk210 codeAt_210 rfl rfl rfl rfl rfl rfl codeAt_215 (by decide) (by decide) w4 p4 _ b4
  refine Run.seq (B₂ := 1163) st5 (fun w5 ⟨p5, b5⟩ => ?_) (by simp only [show blk210.res.cycles = 5 by kernel_rfl]; norm_num)
  have st6 := stageRun (e := 232) blk221 codeAt_221 rfl rfl rfl rfl rfl rfl codeAt_226 (by decide) (by decide) w5 p5 _ b5
  refine Run.seq (B₂ := 30) st6 (fun w6 ⟨p6, b6⟩ => ?_) (by simp only [show blk221.res.cycles = 5 by kernel_rfl]; norm_num)
  refine Run.seq (B₂ := 2) (unpack_run w6 p6 _ b6) (fun w7 ⟨p7, b7⟩ => ?_) (by norm_num)
  refine Run.of (symRun_sound blk260 codeAt_260 w7 p7 (by simp only [blk260.res, rv_simp]))
    (by simp only [show blk260.res.cycles = 2 by kernel_rfl]; norm_num) ?_
  refine ⟨symRun_ecall blk260 codeAt_260 w7 (by simp only [blk260.res, rv_simp]) rfl,
    by simp only [blk260.res, rv_simp], by simp only [blk260.res, rv_simp], ?_⟩
  intro a ha
  rw [getByte_ofNat _ _ ha, toState_getMem_nil rfl, ← getByte_ofNat _ _ ha, b7 a ha]
  rfl


end SigGolfCandidate.Expand
