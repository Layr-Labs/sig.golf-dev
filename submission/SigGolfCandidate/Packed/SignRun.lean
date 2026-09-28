import SigGolfCandidate.Packed.Images
import SigGolfCandidate.Expand.Stages
import SigGolfCandidate.Packed.WordCodec
import SigGolfCandidate.Packed.ByteCodec
import SigGolfCandidate.Expand.Cover

/-! Universal trace of the packed signing postprocess. -/

namespace SigGolfCandidate.Packed.SignRun
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.Mem
set_option maxRecDepth 100000

abbrev image : Image := Images.signImage

def L : Rv.Layout :=
  [(0, SigGolfCandidate.Images.signCode.take 2800),
   (2800, SigGolfCandidate.Expand.pre0), (2805, SigGolfCandidate.Expand.loopCode),
   (2811, SigGolfCandidate.Expand.pre1), (2815, SigGolfCandidate.Expand.loopCode),
   (2821, SigGolfCandidate.Expand.pre2), (2826, SigGolfCandidate.Expand.loopCode),
   (2832, SigGolfCandidate.Expand.pre3), (2837, SigGolfCandidate.Expand.loopCode),
   (2843, SigGolfCandidate.Expand.pre4), (2848, SigGolfCandidate.Expand.loopCode),
   (2854, SigGolfCandidate.Expand.pre5), (2859, SigGolfCandidate.Expand.loopCode),
   (2865, SigGolfCandidate.Expand.pre6), (2870, SigGolfCandidate.Expand.loopCode),
   (2876, SigGolfCandidate.Expand.pre7), (2881, SigGolfCandidate.Expand.loopCode),
   (2887, SigGolfCandidate.Expand.pre8), (2892, SigGolfCandidate.Expand.loopCode),
   (2898, SigGolfCandidate.Expand.pre9), (2903, SigGolfCandidate.Expand.loopCode),
   (2909, SigGolfCandidate.Expand.pre10), (2914, SigGolfCandidate.Expand.loopCode),
   (2920, Images.signBodyPrelude), (2925, SigGolfCandidate.Expand.loopCode),
   (2931, Images.signCounterPrelude ++ Images.signCounterPack)]

theorem layout_ok : layoutOk 0 L = true := by decide +kernel
theorem code_eq : image.code = layoutCode L := by decide +kernel

theorem codeAt_pre0 : CodeAt image (BitVec.ofNat 64 (0x1000 + 4 * 2800)) SigGolfCandidate.Expand.pre0 :=
  codeAt_layout code_eq layout_ok (i := 1) (by kernel_rfl) (by decide)
theorem codeAt_loop0 : CodeAt image (BitVec.ofNat 64 (0x1000 + 4 * 2805)) SigGolfCandidate.Expand.loopCode :=
  codeAt_layout code_eq layout_ok (i := 2) (by kernel_rfl) (by decide)

theorem codeAt_pre1 : CodeAt image (BitVec.ofNat 64 (0x1000 + 4 * 2811)) SigGolfCandidate.Expand.pre1 :=
  codeAt_layout code_eq layout_ok (i := 3) (by kernel_rfl) (by decide)
theorem codeAt_loop1 : CodeAt image (BitVec.ofNat 64 (0x1000 + 4 * 2815)) SigGolfCandidate.Expand.loopCode :=
  codeAt_layout code_eq layout_ok (i := 4) (by kernel_rfl) (by decide)

theorem codeAt_pre2 : CodeAt image (BitVec.ofNat 64 (0x1000 + 4 * 2821)) SigGolfCandidate.Expand.pre2 :=
  codeAt_layout code_eq layout_ok (i := 5) (by kernel_rfl) (by decide)
theorem codeAt_loop2 : CodeAt image (BitVec.ofNat 64 (0x1000 + 4 * 2826)) SigGolfCandidate.Expand.loopCode :=
  codeAt_layout code_eq layout_ok (i := 6) (by kernel_rfl) (by decide)

theorem codeAt_pre3 : CodeAt image (BitVec.ofNat 64 (0x1000 + 4 * 2832)) SigGolfCandidate.Expand.pre3 :=
  codeAt_layout code_eq layout_ok (i := 7) (by kernel_rfl) (by decide)
theorem codeAt_loop3 : CodeAt image (BitVec.ofNat 64 (0x1000 + 4 * 2837)) SigGolfCandidate.Expand.loopCode :=
  codeAt_layout code_eq layout_ok (i := 8) (by kernel_rfl) (by decide)

theorem codeAt_pre4 : CodeAt image (BitVec.ofNat 64 (0x1000 + 4 * 2843)) SigGolfCandidate.Expand.pre4 :=
  codeAt_layout code_eq layout_ok (i := 9) (by kernel_rfl) (by decide)
theorem codeAt_loop4 : CodeAt image (BitVec.ofNat 64 (0x1000 + 4 * 2848)) SigGolfCandidate.Expand.loopCode :=
  codeAt_layout code_eq layout_ok (i := 10) (by kernel_rfl) (by decide)

theorem codeAt_pre5 : CodeAt image (BitVec.ofNat 64 (0x1000 + 4 * 2854)) SigGolfCandidate.Expand.pre5 :=
  codeAt_layout code_eq layout_ok (i := 11) (by kernel_rfl) (by decide)
theorem codeAt_loop5 : CodeAt image (BitVec.ofNat 64 (0x1000 + 4 * 2859)) SigGolfCandidate.Expand.loopCode :=
  codeAt_layout code_eq layout_ok (i := 12) (by kernel_rfl) (by decide)

theorem codeAt_pre6 : CodeAt image (BitVec.ofNat 64 (0x1000 + 4 * 2865)) SigGolfCandidate.Expand.pre6 :=
  codeAt_layout code_eq layout_ok (i := 13) (by kernel_rfl) (by decide)
theorem codeAt_loop6 : CodeAt image (BitVec.ofNat 64 (0x1000 + 4 * 2870)) SigGolfCandidate.Expand.loopCode :=
  codeAt_layout code_eq layout_ok (i := 14) (by kernel_rfl) (by decide)

theorem codeAt_pre7 : CodeAt image (BitVec.ofNat 64 (0x1000 + 4 * 2876)) SigGolfCandidate.Expand.pre7 :=
  codeAt_layout code_eq layout_ok (i := 15) (by kernel_rfl) (by decide)
theorem codeAt_loop7 : CodeAt image (BitVec.ofNat 64 (0x1000 + 4 * 2881)) SigGolfCandidate.Expand.loopCode :=
  codeAt_layout code_eq layout_ok (i := 16) (by kernel_rfl) (by decide)

theorem codeAt_pre8 : CodeAt image (BitVec.ofNat 64 (0x1000 + 4 * 2887)) SigGolfCandidate.Expand.pre8 :=
  codeAt_layout code_eq layout_ok (i := 17) (by kernel_rfl) (by decide)
theorem codeAt_loop8 : CodeAt image (BitVec.ofNat 64 (0x1000 + 4 * 2892)) SigGolfCandidate.Expand.loopCode :=
  codeAt_layout code_eq layout_ok (i := 18) (by kernel_rfl) (by decide)

theorem codeAt_pre9 : CodeAt image (BitVec.ofNat 64 (0x1000 + 4 * 2898)) SigGolfCandidate.Expand.pre9 :=
  codeAt_layout code_eq layout_ok (i := 19) (by kernel_rfl) (by decide)
theorem codeAt_loop9 : CodeAt image (BitVec.ofNat 64 (0x1000 + 4 * 2903)) SigGolfCandidate.Expand.loopCode :=
  codeAt_layout code_eq layout_ok (i := 20) (by kernel_rfl) (by decide)

theorem codeAt_pre10 : CodeAt image (BitVec.ofNat 64 (0x1000 + 4 * 2909)) SigGolfCandidate.Expand.pre10 :=
  codeAt_layout code_eq layout_ok (i := 21) (by kernel_rfl) (by decide)
theorem codeAt_loop10 : CodeAt image (BitVec.ofNat 64 (0x1000 + 4 * 2914)) SigGolfCandidate.Expand.loopCode :=
  codeAt_layout code_eq layout_ok (i := 22) (by kernel_rfl) (by decide)

theorem codeAt_bodyPre : CodeAt image (BitVec.ofNat 64 (0x1000 + 4 * 2920)) Images.signBodyPrelude :=
  codeAt_layout code_eq layout_ok (i := 23) (by kernel_rfl) (by decide)
theorem codeAt_bodyLoop : CodeAt image (BitVec.ofNat 64 (0x1000 + 4 * 2925)) SigGolfCandidate.Expand.loopCode :=
  codeAt_layout code_eq layout_ok (i := 24) (by kernel_rfl) (by decide)
theorem codeAt_finish : CodeAt image (BitVec.ofNat 64 (0x1000 + 4 * 2931))
    (Images.signCounterPrelude ++ Images.signCounterPack) :=
  codeAt_layout code_eq layout_ok (i := 25) (by kernel_rfl) (by decide)

sym_block run0 := symRun {} SigGolfCandidate.Expand.pre0 (BitVec.ofNat 64 (0x1000 + 4 * 2800)) 10
sym_block run1 := symRun {} SigGolfCandidate.Expand.pre1 (BitVec.ofNat 64 (0x1000 + 4 * 2811)) 10
sym_block run2 := symRun {} SigGolfCandidate.Expand.pre2 (BitVec.ofNat 64 (0x1000 + 4 * 2821)) 10
sym_block run3 := symRun {} SigGolfCandidate.Expand.pre3 (BitVec.ofNat 64 (0x1000 + 4 * 2832)) 10
sym_block run4 := symRun {} SigGolfCandidate.Expand.pre4 (BitVec.ofNat 64 (0x1000 + 4 * 2843)) 10
sym_block run5 := symRun {} SigGolfCandidate.Expand.pre5 (BitVec.ofNat 64 (0x1000 + 4 * 2854)) 10
sym_block run6 := symRun {} SigGolfCandidate.Expand.pre6 (BitVec.ofNat 64 (0x1000 + 4 * 2865)) 10
sym_block run7 := symRun {} SigGolfCandidate.Expand.pre7 (BitVec.ofNat 64 (0x1000 + 4 * 2876)) 10
sym_block run8 := symRun {} SigGolfCandidate.Expand.pre8 (BitVec.ofNat 64 (0x1000 + 4 * 2887)) 10
sym_block run9 := symRun {} SigGolfCandidate.Expand.pre9 (BitVec.ofNat 64 (0x1000 + 4 * 2898)) 10
sym_block run10 := symRun {} SigGolfCandidate.Expand.pre10 (BitVec.ofNat 64 (0x1000 + 4 * 2909)) 10
sym_block runBody := symRun {} Images.signBodyPrelude (BitVec.ofNat 64 (0x1000 + 4 * 2920)) 10
sym_block runFinish := symRun {} (Images.signCounterPrelude ++ Images.signCounterPack)
  (BitVec.ofNat 64 (0x1000 + 4 * 2931)) 100

theorem stage0 (t : MachineState) (htpc : t.pc = BitVec.ofNat 64 (0x1000 + 4 * 2800))
    (f : Nat → Byte) (hf : SigGolfCandidate.Expand.BytesEq t f) :
    ∃ u, Steps image t (run0.res.steps + 620 * 6) (run0.res.cycles + 620 * 6) u ∧
      u.pc = BitVec.ofNat 64 (0x1000 + 4 * 2805) + 24 ∧
      SigGolfCandidate.Expand.BytesEq u (SigGolfCandidate.Expand.applyCopy (9808, 2048, 620) f) :=
  SigGolfCandidate.Expand.stage run0 codeAt_pre0 rfl rfl rfl rfl rfl rfl codeAt_loop0
    (by decide) t htpc f hf

theorem stage1 (t : MachineState) (htpc : t.pc = BitVec.ofNat 64 (0x1000 + 4 * 2811))
    (f : Nat → Byte) (hf : SigGolfCandidate.Expand.BytesEq t f) :
    ∃ u, Steps image t (run1.res.steps + 1 * 6) (run1.res.cycles + 1 * 6) u ∧
      u.pc = BitVec.ofNat 64 (0x1000 + 4 * 2815) + 24 ∧
      SigGolfCandidate.Expand.BytesEq u (SigGolfCandidate.Expand.applyCopy (12288, 8432, 1) f) :=
  SigGolfCandidate.Expand.stage run1 codeAt_pre1 rfl rfl rfl rfl rfl rfl codeAt_loop1
    (by decide) t htpc f hf

theorem stage2 (t : MachineState) (htpc : t.pc = BitVec.ofNat 64 (0x1000 + 4 * 2821))
    (f : Nat → Byte) (hf : SigGolfCandidate.Expand.BytesEq t f) :
    ∃ u, Steps image t (run2.res.steps + 212 * 6) (run2.res.cycles + 212 * 6) u ∧
      u.pc = BitVec.ofNat 64 (0x1000 + 4 * 2826) + 24 ∧
      SigGolfCandidate.Expand.BytesEq u (SigGolfCandidate.Expand.applyCopy (12292, 4528, 212) f) :=
  SigGolfCandidate.Expand.stage run2 codeAt_pre2 rfl rfl rfl rfl rfl rfl codeAt_loop2
    (by decide) t htpc f hf

theorem stage3 (t : MachineState) (htpc : t.pc = BitVec.ofNat 64 (0x1000 + 4 * 2832))
    (f : Nat → Byte) (hf : SigGolfCandidate.Expand.BytesEq t f) :
    ∃ u, Steps image t (run3.res.steps + 1 * 6) (run3.res.cycles + 1 * 6) u ∧
      u.pc = BitVec.ofNat 64 (0x1000 + 4 * 2837) + 24 ∧
      SigGolfCandidate.Expand.BytesEq u (SigGolfCandidate.Expand.applyCopy (13140, 8436, 1) f) :=
  SigGolfCandidate.Expand.stage run3 codeAt_pre3 rfl rfl rfl rfl rfl rfl codeAt_loop3
    (by decide) t htpc f hf

theorem stage4 (t : MachineState) (htpc : t.pc = BitVec.ofNat 64 (0x1000 + 4 * 2843))
    (f : Nat → Byte) (hf : SigGolfCandidate.Expand.BytesEq t f) :
    ∃ u, Steps image t (run4.res.steps + 192 * 6) (run4.res.cycles + 192 * 6) u ∧
      u.pc = BitVec.ofNat 64 (0x1000 + 4 * 2848) + 24 ∧
      SigGolfCandidate.Expand.BytesEq u (SigGolfCandidate.Expand.applyCopy (13144, 5376, 192) f) :=
  SigGolfCandidate.Expand.stage run4 codeAt_pre4 rfl rfl rfl rfl rfl rfl codeAt_loop4
    (by decide) t htpc f hf

theorem stage5 (t : MachineState) (htpc : t.pc = BitVec.ofNat 64 (0x1000 + 4 * 2854))
    (f : Nat → Byte) (hf : SigGolfCandidate.Expand.BytesEq t f) :
    ∃ u, Steps image t (run5.res.steps + 1 * 6) (run5.res.cycles + 1 * 6) u ∧
      u.pc = BitVec.ofNat 64 (0x1000 + 4 * 2859) + 24 ∧
      SigGolfCandidate.Expand.BytesEq u (SigGolfCandidate.Expand.applyCopy (13912, 8440, 1) f) :=
  SigGolfCandidate.Expand.stage run5 codeAt_pre5 rfl rfl rfl rfl rfl rfl codeAt_loop5
    (by decide) t htpc f hf

theorem stage6 (t : MachineState) (htpc : t.pc = BitVec.ofNat 64 (0x1000 + 4 * 2865))
    (f : Nat → Byte) (hf : SigGolfCandidate.Expand.BytesEq t f) :
    ∃ u, Steps image t (run6.res.steps + 192 * 6) (run6.res.cycles + 192 * 6) u ∧
      u.pc = BitVec.ofNat 64 (0x1000 + 4 * 2870) + 24 ∧
      SigGolfCandidate.Expand.BytesEq u (SigGolfCandidate.Expand.applyCopy (13916, 6144, 192) f) :=
  SigGolfCandidate.Expand.stage run6 codeAt_pre6 rfl rfl rfl rfl rfl rfl codeAt_loop6
    (by decide) t htpc f hf

theorem stage7 (t : MachineState) (htpc : t.pc = BitVec.ofNat 64 (0x1000 + 4 * 2876))
    (f : Nat → Byte) (hf : SigGolfCandidate.Expand.BytesEq t f) :
    ∃ u, Steps image t (run7.res.steps + 1 * 6) (run7.res.cycles + 1 * 6) u ∧
      u.pc = BitVec.ofNat 64 (0x1000 + 4 * 2881) + 24 ∧
      SigGolfCandidate.Expand.BytesEq u (SigGolfCandidate.Expand.applyCopy (14684, 8444, 1) f) :=
  SigGolfCandidate.Expand.stage run7 codeAt_pre7 rfl rfl rfl rfl rfl rfl codeAt_loop7
    (by decide) t htpc f hf

theorem stage8 (t : MachineState) (htpc : t.pc = BitVec.ofNat 64 (0x1000 + 4 * 2887))
    (f : Nat → Byte) (hf : SigGolfCandidate.Expand.BytesEq t f) :
    ∃ u, Steps image t (run8.res.steps + 192 * 6) (run8.res.cycles + 192 * 6) u ∧
      u.pc = BitVec.ofNat 64 (0x1000 + 4 * 2892) + 24 ∧
      SigGolfCandidate.Expand.BytesEq u (SigGolfCandidate.Expand.applyCopy (14688, 6912, 192) f) :=
  SigGolfCandidate.Expand.stage run8 codeAt_pre8 rfl rfl rfl rfl rfl rfl codeAt_loop8
    (by decide) t htpc f hf

theorem stage9 (t : MachineState) (htpc : t.pc = BitVec.ofNat 64 (0x1000 + 4 * 2898))
    (f : Nat → Byte) (hf : SigGolfCandidate.Expand.BytesEq t f) :
    ∃ u, Steps image t (run9.res.steps + 1 * 6) (run9.res.cycles + 1 * 6) u ∧
      u.pc = BitVec.ofNat 64 (0x1000 + 4 * 2903) + 24 ∧
      SigGolfCandidate.Expand.BytesEq u (SigGolfCandidate.Expand.applyCopy (15456, 8448, 1) f) :=
  SigGolfCandidate.Expand.stage run9 codeAt_pre9 rfl rfl rfl rfl rfl rfl codeAt_loop9
    (by decide) t htpc f hf

theorem stage10 (t : MachineState) (htpc : t.pc = BitVec.ofNat 64 (0x1000 + 4 * 2909))
    (f : Nat → Byte) (hf : SigGolfCandidate.Expand.BytesEq t f) :
    ∃ u, Steps image t (run10.res.steps + 188 * 6) (run10.res.cycles + 188 * 6) u ∧
      u.pc = BitVec.ofNat 64 (0x1000 + 4 * 2914) + 24 ∧
      SigGolfCandidate.Expand.BytesEq u (SigGolfCandidate.Expand.applyCopy (15460, 7680, 188) f) :=
  SigGolfCandidate.Expand.stage run10 codeAt_pre10 rfl rfl rfl rfl rfl rfl codeAt_loop10
    (by decide) t htpc f hf

theorem permute_steps (s : MachineState) (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * 2800)) :
    ∃ u, Steps image s 9660 9660 u ∧
      u.pc = BitVec.ofNat 64 (0x1000 + 4 * 2920) ∧
      SigGolfCandidate.Expand.BytesEq u
        (SigGolfCandidate.Expand.applyCopies SigGolfCandidate.Expand.copies
          (fun a => s.getByte (BitVec.ofNat 64 a))) := by
  obtain ⟨u0, st0, pc0, b0⟩ := stage0 s hpc _ (fun a _ => rfl)
  obtain ⟨u1, st1, pc1, b1⟩ := stage1 u0 (by rw [pc0]; decide) _ b0
  obtain ⟨u2, st2, pc2, b2⟩ := stage2 u1 (by rw [pc1]; decide) _ b1
  obtain ⟨u3, st3, pc3, b3⟩ := stage3 u2 (by rw [pc2]; decide) _ b2
  obtain ⟨u4, st4, pc4, b4⟩ := stage4 u3 (by rw [pc3]; decide) _ b3
  obtain ⟨u5, st5, pc5, b5⟩ := stage5 u4 (by rw [pc4]; decide) _ b4
  obtain ⟨u6, st6, pc6, b6⟩ := stage6 u5 (by rw [pc5]; decide) _ b5
  obtain ⟨u7, st7, pc7, b7⟩ := stage7 u6 (by rw [pc6]; decide) _ b6
  obtain ⟨u8, st8, pc8, b8⟩ := stage8 u7 (by rw [pc7]; decide) _ b7
  obtain ⟨u9, st9, pc9, b9⟩ := stage9 u8 (by rw [pc8]; decide) _ b8
  obtain ⟨u10, st10, pc10, b10⟩ := stage10 u9 (by rw [pc9]; decide) _ b9
  exact ⟨u10, Steps.of_eq ((((((((((st0.trans st1).trans st2).trans st3).trans st4).trans st5).trans st6).trans st7).trans st8).trans st9).trans st10) rfl rfl, by rw [pc10]; decide, b10⟩

theorem permute_readBuffer (s u : MachineState)
    (hu : SigGolfCandidate.Expand.BytesEq u
      (SigGolfCandidate.Expand.applyCopies SigGolfCandidate.Expand.copies
        (fun a => s.getByte (BitVec.ofNat 64 a)))) :
    readBuffer u 0x800 6404 = SigGolfCandidate.Ref.expandRef
      (readBuffer s 0x2650 6404) := by
  rw [readBuffer_eq, SigGolfCandidate.Ref.expandRef,
    SigGolfCandidate.Ref.ofList, SigGolfCandidate.Ref.toWitness]
  apply congrArg (BitVec.ofNat (8 * 6404))
  apply congrArg SigGolfCandidate.Ref.leNat
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  obtain ⟨c, hc, h1, h2, h3⟩ := SigGolfCandidate.Expand.copies_cover i hi
  rw [hu _ (by omega), SigGolfCandidate.Expand.applyCopies_hit
    SigGolfCandidate.Expand.copies _ (by decide) (by decide) c hc _ h1 h2, h3,
    readBuffer_byte s 0x2650 6404 _ (SigGolfCandidate.Ref.witnessSrc_lt i hi)]

theorem body_stage (t : MachineState)
    (htpc : t.pc = BitVec.ofNat 64 (0x1000 + 4 * 2920))
    (f : Nat → Byte) (hf : SigGolfCandidate.Expand.BytesEq t f) :
    ∃ u, Steps image t (runBody.res.steps + 1596 * 6)
        (runBody.res.cycles + 1596 * 6) u ∧
      u.pc = BitVec.ofNat 64 (0x1000 + 4 * 2931) ∧
      SigGolfCandidate.Expand.BytesEq u
        (SigGolfCandidate.Expand.applyCopy (0x800, 0x2650, 1596) f) := by
  obtain ⟨u, hst, hpc, hmem⟩ :=
    SigGolfCandidate.Expand.stage runBody codeAt_bodyPre rfl rfl rfl rfl rfl rfl
      codeAt_bodyLoop (by decide) t htpc f hf
  exact ⟨u, hst, by simpa using hpc, hmem⟩

theorem finish_steps (u : MachineState)
    (hpc : u.pc = BitVec.ofNat 64 (0x1000 + 4 * 2931)) :
    Steps image u 29 29 (runFinish.res.toState u) ∧
      fetch image (runFinish.res.toState u) = some (.base .ECALL) ∧
      (runFinish.res.toState u).getReg .x5 = 1 ∧
      (runFinish.res.toState u).getReg .x10 = 0 := by
  have ho : runFinish.res.obligs u := by simp only [runFinish.res, rv_simp]
  exact ⟨by simpa only [runFinish.res] using
      (symRun_sound runFinish codeAt_finish u hpc ho),
    symRun_ecall runFinish codeAt_finish u ho rfl,
    by simp only [runFinish.res, rv_simp],
    by simp only [runFinish.res, rv_simp]⟩

/-- From the old success halt address, the packed signer always reaches its
    success ECALL after a fixed number of ordinary machine steps. -/
theorem sign_suffix_steps (s : MachineState)
    (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * 2800)) :
    ∃ u, Steps image s 19270 19270 u ∧
      fetch image u = some (.base .ECALL) ∧
      u.getReg .x5 = 1 ∧ u.getReg .x10 = 0 := by
  obtain ⟨u0, st0, pc0, b0⟩ := permute_steps s hpc
  obtain ⟨u1, st1, pc1, _⟩ := body_stage u0 pc0 _ b0
  obtain ⟨st2, hf, h5, h10⟩ := finish_steps u1 pc1
  exact ⟨_, Steps.of_eq ((st0.trans st1).trans st2) rfl rfl, hf, h5, h10⟩

def sourceCounters (u : MachineState) : BitVec 160 :=
  (u.getMem (BitVec.ofNat 64 0x2100)).extractLsb' 0 32 ++
  u.getMem (BitVec.ofNat 64 0x20F8) ++
  u.getMem (BitVec.ofNat 64 0x20F0)

private theorem nestedExtract {w : Nat} (x : BitVec w) (a l b n : Nat)
    (h : b + n ≤ l) :
    (x.extractLsb' a l).extractLsb' b n = x.extractLsb' (a + b) n := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb']
  have hib : b + i < l := by omega
  simp [hi, hib, Nat.add_assoc]

private theorem byteExtract (x : BitVec 64) (i : Nat) :
    extractByte x i = x.extractLsb' (8 * i) 8 := by
  simp only [extractByte, BitVec.truncate_eq_setWidth,
    BitVec.setWidth_ushiftRight_eq_extractLsb, Nat.mul_comm]

theorem sourceCounters_byte (u : MachineState) (j : Nat) (hj : j < 20) :
    u.getByte (BitVec.ofNat 64 (0x20F0 + j)) =
      (sourceCounters u).extractLsb' (8 * j) 8 := by
  have ha : alignToDword (BitVec.ofNat 64 (0x20F0 + j)) =
      BitVec.ofNat 64 (0x20F0 + 8 * (j / 8)) := by
    apply BitVec.eq_of_toNat_eq
    rw [alignToDword_toNat]
    simp only [BitVec.toNat_ofNat]
    omega
  have hb : byteOffset (BitVec.ofNat 64 (0x20F0 + j)) = j % 8 := by
    rw [byteOffset_ofNat (by omega)]
    omega
  simp only [MachineState.getByte]
  rw [ha, hb]
  interval_cases j <;>
    simp only [sourceCounters, byteExtract, Nat.reduceDiv, Nat.reduceMod,
      Nat.reduceMul, Nat.reduceAdd] <;>
    (first
      | rw [BitVec.extractLsb'_append_eq_of_add_le (h := by decide)]
      | rw [BitVec.extractLsb'_append_eq_of_le (h := by decide)]) <;>
    (first
      | rw [BitVec.extractLsb'_append_eq_of_add_le (h := by decide)]
      | rw [BitVec.extractLsb'_append_eq_of_le (h := by decide)]) <;>
    simp [nestedExtract]

theorem sourceCounters_readBuffer (u : MachineState) :
    sourceCounters u = readBuffer u 0x20F0 20 := by
  symm
  apply readBuffer_eq_of_bytes
  intro i hi
  rw [sourceCounters_byte u i hi]
  exact (getD_bytes (sourceCounters u) i hi).symm

theorem body_witness_unchanged (u0 u1 : MachineState)
    (hb : SigGolfCandidate.Expand.BytesEq u1
      (SigGolfCandidate.Expand.applyCopy (0x800, 0x2650, 1596)
        (fun a => u0.getByte (BitVec.ofNat 64 a)))) :
    readBuffer u1 0x800 6404 = readBuffer u0 0x800 6404 := by
  apply readBuffer_eq_of_bytes
  intro i hi
  rw [hb _ (by omega)]
  have hne : ¬ (0x2650 ≤ 0x800 + i ∧ 0x800 + i < 0x2650 + 4 * 1596) := by omega
  simp only [SigGolfCandidate.Expand.applyCopy, if_neg hne]
  exact (readBuffer_byte u0 0x800 6404 i hi).symm

theorem sourceCounters_of_body (u0 u1 : MachineState)
    (hb : SigGolfCandidate.Expand.BytesEq u1
      (SigGolfCandidate.Expand.applyCopy (0x800, 0x2650, 1596)
        (fun a => u0.getByte (BitVec.ofNat 64 a)))) :
    sourceCounters u1 = (readBuffer u0 0x800 6404).extractLsb' bodyBits 160 := by
  rw [sourceCounters_readBuffer, readBuffer_witnessCounters,
    body_witness_unchanged u0 u1 hb]

theorem finish_sigWord0 (u : MachineState) :
    (runFinish.res.toState u).getMem (BitVec.ofNat 64 0x3F40) =
      packLoWord (sourceCounters u) := by
  simp only [Result.toState_getMem, runFinish.res, memEval, Addr.eval, E.eval,
    BinOp.eval, UnOp.eval, LoadKind.fromWord, extractWord32, sourceCounters,
    packLoWord, counterWord]
  bv_decide

theorem finish_sigWord1 (u : MachineState) :
    (runFinish.res.toState u).getMem (BitVec.ofNat 64 0x3F48) =
      packHiWord (sourceCounters u) := by
  simp only [Result.toState_getMem, runFinish.res, memEval, Addr.eval, E.eval,
    BinOp.eval, UnOp.eval, LoadKind.fromWord, extractWord32, sourceCounters,
    packHiWord, counterWord]
  bv_decide

theorem finish_mem_frame (u : MachineState) (a : Word)
    (h0 : a ≠ BitVec.ofNat 64 0x3F40)
    (h1 : a ≠ BitVec.ofNat 64 0x3F48) :
    (runFinish.res.toState u).getMem a = u.getMem a := by
  simp only [Result.toState_getMem, runFinish.res, memEval, Addr.eval]
  simp [h0, h1]

theorem finish_body_byte (u : MachineState) (j : Nat) (hj : j < 6384) :
    (runFinish.res.toState u).getByte (BitVec.ofNat 64 (0x2650 + j)) =
      u.getByte (BitVec.ofNat 64 (0x2650 + j)) := by
  have ha : (alignToDword (BitVec.ofNat 64 (0x2650 + j))).toNat < 0x3F40 := by
    rw [alignToDword_toNat, BitVec.toNat_ofNat]
    omega
  have hne (x : Nat) (hx : 0x3F40 ≤ x) (hxb : x < 2 ^ 64) :
      alignToDword (BitVec.ofNat 64 (0x2650 + j)) ≠ BitVec.ofNat 64 x := by
    intro h
    rw [h] at ha
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hxb] at ha
    omega
  simp only [MachineState.getByte]
  rw [finish_mem_frame u _ (hne _ (by omega) (by decide))
    (hne _ (by omega) (by decide))]

theorem finish_counter_byte (u : MachineState) (j : Nat) (hj : j < 14) :
    (runFinish.res.toState u).getByte (BitVec.ofNat 64 (0x3F40 + j)) =
      (shrinkCounterBlockAny (sourceCounters u)).extractLsb' (8 * j) 8 := by
  have ha : alignToDword (BitVec.ofNat 64 (0x3F40 + j)) =
      BitVec.ofNat 64 (0x3F40 + 8 * (j / 8)) := by
    apply BitVec.eq_of_toNat_eq
    rw [alignToDword_toNat]
    simp only [BitVec.toNat_ofNat]
    omega
  have hb : byteOffset (BitVec.ofNat 64 (0x3F40 + j)) = j % 8 := by
    rw [byteOffset_ofNat (by omega)]
    omega
  rw [← packWords_eq_shrinkAny]
  simp only [MachineState.getByte]
  rw [ha, hb]
  interval_cases j <;>
    simp only [Nat.reduceDiv, Nat.reduceMod, Nat.reduceMul, Nat.reduceAdd] <;>
    (first | rw [finish_sigWord0] | rw [finish_sigWord1]) <;>
    simp only [byteExtract] <;>
    (first
      | rw [BitVec.extractLsb'_append_eq_of_add_le (h := by decide)]
      | rw [BitVec.extractLsb'_append_eq_of_le (h := by decide)]) <;>
    simp [nestedExtract]

theorem final_readBuffer (s u0 u1 : MachineState)
    (hp : SigGolfCandidate.Expand.BytesEq u0
      (SigGolfCandidate.Expand.applyCopies SigGolfCandidate.Expand.copies
        (fun a => s.getByte (BitVec.ofNat 64 a))))
    (hb : SigGolfCandidate.Expand.BytesEq u1
      (SigGolfCandidate.Expand.applyCopy (0x800, 0x2650, 1596)
        (fun a => u0.getByte (BitVec.ofNat 64 a)))) :
    readBuffer (runFinish.res.toState u1) 0x2650 6398 =
      packOldAny (readBuffer s 0x2650 6404) := by
  let oldSig : Bytes 6404 := readBuffer s 0x2650 6404
  let w : Bytes 6404 := SigGolfCandidate.Ref.expandRef oldSig
  have hw : readBuffer u0 0x800 6404 = w := permute_readBuffer s u0 hp
  have hc : sourceCounters u1 = w.extractLsb' bodyBits 160 := by
    rw [sourceCounters_of_body u0 u1 hb, hw]
  change readBuffer (runFinish.res.toState u1) 0x2650 6398 = shrinkWitnessAny w
  apply readBuffer_eq_of_bytes
  intro i hi
  by_cases hbody : i < 6384
  · rw [finish_body_byte u1 i hbody, hb _ (by omega)]
    have hhit : 0x2650 ≤ 0x2650 + i ∧
        0x2650 + i < 0x2650 + 4 * 1596 := by omega
    simp only [SigGolfCandidate.Expand.applyCopy, if_pos hhit]
    have heq : 0x2650 + i - 0x2650 + 0x800 = 0x800 + i := by omega
    rw [heq, ← readBuffer_byte u0 0x800 6404 i (by omega), hw]
    rw [← shortBody_byte (shrinkWitnessAny w) i hbody,
      body_shrinkWitnessAny, witnessBody_byte w i hbody]
  · have hj : i - 6384 < 14 := by omega
    have heq : 0x2650 + i = 0x3F40 + (i - 6384) := by omega
    rw [heq, finish_counter_byte u1 (i - 6384) hj, hc]
    have hi' : 6384 + (i - 6384) = i := by omega
    rw [← hi', ← shortCounter_byte (shrinkWitnessAny w) (i - 6384) hj,
      packedCounters_shrinkWitnessAny]
    have hidx : 6384 + (i - 6384) - 6384 = i - 6384 := by omega
    rw [hidx]
    exact (getD_bytes (shrinkCounterBlockAny (w.extractLsb' bodyBits 160))
      (i - 6384) hj).symm

/-- Complete packed-sign success suffix, including its exact output buffer. -/
theorem sign_suffix_output (s : MachineState)
    (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * 2800)) :
    ∃ u, Steps image s 19270 19270 u ∧
      fetch image u = some (.base .ECALL) ∧
      u.getReg .x5 = 1 ∧ u.getReg .x10 = 0 ∧
      readBuffer u 0x2650 6398 = packOldAny (readBuffer s 0x2650 6404) := by
  obtain ⟨u0, st0, pc0, b0⟩ := permute_steps s hpc
  obtain ⟨u1, st1, pc1, b1⟩ := body_stage u0 pc0 _ b0
  have hb : SigGolfCandidate.Expand.BytesEq u1
      (SigGolfCandidate.Expand.applyCopy (0x800, 0x2650, 1596)
        (fun a => u0.getByte (BitVec.ofNat 64 a))) := by
    intro a ha
    rw [b1 a ha]
    by_cases hhit : 0x2650 ≤ a ∧ a < 0x2650 + 4 * 1596
    · simp only [SigGolfCandidate.Expand.applyCopy, if_pos hhit]
      exact (b0 _ (by omega)).symm
    · simp only [SigGolfCandidate.Expand.applyCopy, if_neg hhit]
      exact (b0 a ha).symm
  obtain ⟨st2, hf, h5, h10⟩ := finish_steps u1 pc1
  exact ⟨_, Steps.of_eq ((st0.trans st1).trans st2) rfl rfl,
    hf, h5, h10, final_readBuffer s u0 u1 b0 hb⟩

end SigGolfCandidate.Packed.SignRun
