import SigGolfCandidate.Sign.Copy
import SigGolfCandidate.Sign.Blocks

/-!
# `sign`: the pack (instructions 685 .. 750)

Six word-copy loops (`pkLoopCode`): layer `l`'s `(516 + 16 h_l) / 4` words from the staging
`STG + 696 l + 4` (counter word, chain values, path) to the signature `SIG + sigLayerOff l`
(`packCopies`). `pack_run` : the byte view of memory after the pack.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace SigGolfCandidate.Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref SigGolfCandidate.Mem

/-- The six layer copies `(src, dst, words)`: `(STG + 696 l + 4, SIG + sigLayerOff l, sigLayerBytes l / 4)`. -/
def packCopies : List (Nat × Nat × Nat) :=
  [(2308, 15200, 173), (3004, 15892, 149), (3700, 16488, 149), (4396, 17084, 149),
    (5092, 17680, 145), (5788, 18260, 145)]

theorem packCopies_eq : packCopies = (List.range 6).map (fun l =>
    (0x904 + 696 * l, 0x3300 + sigLayerOff l, (516 + 16 * height l) / 4)) := by decide

/-- Cycles (and steps) of the pack: six 5-instruction preludes and `6 n` per copied word. -/
def packCyc : Nat := 6 * 5 + 6 * (173 + 149 + 149 + 149 + 145 + 145)

theorem codeAt_loop690 : CodeAt image (pcOf 690) pkLoopCode := codeAt_690
theorem codeAt_loop701 : CodeAt image (pcOf 701) pkLoopCode := codeAt_701
theorem codeAt_loop712 : CodeAt image (pcOf 712) pkLoopCode := codeAt_712
theorem codeAt_loop723 : CodeAt image (pcOf 723) pkLoopCode := codeAt_723
theorem codeAt_loop734 : CodeAt image (pcOf 734) pkLoopCode := codeAt_734
theorem codeAt_loop745 : CodeAt image (pcOf 745) pkLoopCode := codeAt_745

theorem blk685_steps : blk685.res.steps = 5 := by kernel_rfl
theorem blk685_cycles : blk685.res.cycles = 5 := by kernel_rfl
theorem blk696_steps : blk696.res.steps = 5 := by kernel_rfl
theorem blk696_cycles : blk696.res.cycles = 5 := by kernel_rfl
theorem blk707_steps : blk707.res.steps = 5 := by kernel_rfl
theorem blk707_cycles : blk707.res.cycles = 5 := by kernel_rfl
theorem blk718_steps : blk718.res.steps = 5 := by kernel_rfl
theorem blk718_cycles : blk718.res.cycles = 5 := by kernel_rfl
theorem blk729_steps : blk729.res.steps = 5 := by kernel_rfl
theorem blk729_cycles : blk729.res.cycles = 5 := by kernel_rfl
theorem blk740_steps : blk740.res.steps = 5 := by kernel_rfl
theorem blk740_cycles : blk740.res.cycles = 5 := by kernel_rfl

/-- **The pack**: from `pack_0` to `success`, the byte view is the six copies applied in order. -/
theorem pack_run (t : MachineState) (hpc : t.pc = pcOf 685) :
    ∃ u, Steps image t packCyc packCyc u ∧ u.pc = pcOf 751 ∧
      PkBytesEq u (pkApplyCopies packCopies (fun a => t.getByte (BitVec.ofNat 64 a))) := by
  have hf0 : PkBytesEq t (fun a => t.getByte (BitVec.ofNat 64 a)) := fun a _ => rfl
  obtain ⟨u1, hs1, pc1, hb1⟩ := pk_stage (pcl := pcOf 690) (src := 2308) (dst := 15200) (n := 173)
    blk685 codeAt_685 rfl rfl rfl rfl rfl rfl codeAt_loop690 (by decide) t hpc _ hf0
  obtain ⟨u2, hs2, pc2, hb2⟩ := pk_stage (pcl := pcOf 701) (src := 3004) (dst := 15892) (n := 149)
    blk696 codeAt_696 rfl rfl rfl rfl rfl rfl codeAt_loop701 (by decide) u1 (by rw [pc1]; rfl) _ hb1
  obtain ⟨u3, hs3, pc3, hb3⟩ := pk_stage (pcl := pcOf 712) (src := 3700) (dst := 16488) (n := 149)
    blk707 codeAt_707 rfl rfl rfl rfl rfl rfl codeAt_loop712 (by decide) u2 (by rw [pc2]; rfl) _ hb2
  obtain ⟨u4, hs4, pc4, hb4⟩ := pk_stage (pcl := pcOf 723) (src := 4396) (dst := 17084) (n := 149)
    blk718 codeAt_718 rfl rfl rfl rfl rfl rfl codeAt_loop723 (by decide) u3 (by rw [pc3]; rfl) _ hb3
  obtain ⟨u5, hs5, pc5, hb5⟩ := pk_stage (pcl := pcOf 734) (src := 5092) (dst := 17680) (n := 145)
    blk729 codeAt_729 rfl rfl rfl rfl rfl rfl codeAt_loop734 (by decide) u4 (by rw [pc4]; rfl) _ hb4
  obtain ⟨u6, hs6, pc6, hb6⟩ := pk_stage (pcl := pcOf 745) (src := 5788) (dst := 18260) (n := 145)
    blk740 codeAt_740 rfl rfl rfl rfl rfl rfl codeAt_loop745 (by decide) u5 (by rw [pc5]; rfl) _ hb5
  refine ⟨u6, ((((hs1.trans hs2).trans hs3).trans hs4).trans hs5).trans hs6 |>.of_eq ?_ ?_,
    by rw [pc6]; rfl, hb6⟩
  · rw [blk685_steps, blk696_steps, blk707_steps, blk718_steps, blk729_steps, blk740_steps]; rfl
  · rw [blk685_cycles, blk696_cycles, blk707_cycles, blk718_cycles, blk729_cycles, blk740_cycles]; rfl

end SigGolfCandidate.Sign
