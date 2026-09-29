import SigGolfCandidate.Packed.SignRun
import SigGolfCandidate.Packed.Radix27ImagesExpand
import SigGolfCandidate.Packed.Radix27Codec
import Mathlib
import RiscvZkvm.Rv64.Word
import SigGolfCandidate.Packed.SignClone.Inv
import SigGolfCandidate.Packed.ByteCodec
import SigGolfCandidate.Packed.Radix27Sign
import SigGolfCandidate.Packed.SignClone.Sim
import SigGolfCandidate.Final.Discharge
import SigGolfCandidate.Budget.Bridge
import SigGolfCandidate.Packed.KeygenEq
import SigGolfCandidate.Transport.SecurityFinal
/-! Auto-collected 13-byte codec certificate. Each section preserves a checked scratch module. -/


section -- Radix27SignPrefix

namespace Radix27SignPrefix
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv
  SigGolfCandidate.Rv SigGolfCandidate.Mem SigGolfCandidate.Packed
set_option maxRecDepth 100000

abbrev image : Image := SigGolfCandidate.Radix27Images.signImage

def L : SigGolfCandidate.Rv.Layout :=
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
   (2920, SigGolfCandidate.Packed.Images.signBodyPrelude), (2925, SigGolfCandidate.Expand.loopCode),
   (2931, SigGolfCandidate.Packed.Images.signCounterPrelude),
   (2935, SigGolfCandidate.Radix27Images.signTail)]

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

theorem codeAt_bodyPre : CodeAt image (BitVec.ofNat 64 (0x1000 + 4 * 2920)) SigGolfCandidate.Packed.Images.signBodyPrelude :=
  codeAt_layout code_eq layout_ok (i := 23) (by kernel_rfl) (by decide)
theorem codeAt_bodyLoop : CodeAt image (BitVec.ofNat 64 (0x1000 + 4 * 2925)) SigGolfCandidate.Expand.loopCode :=
  codeAt_layout code_eq layout_ok (i := 24) (by kernel_rfl) (by decide)
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
sym_block runBody := symRun {} SigGolfCandidate.Packed.Images.signBodyPrelude (BitVec.ofNat 64 (0x1000 + 4 * 2920)) 10
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


#print axioms permute_steps
#print axioms body_stage
end Radix27SignPrefix


end


section -- Radix27SignLoaded

namespace Radix27SignLoaded
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Rv Radix27
open SigGolfCandidate.Packed.SignRun (sourceCounters)

def q (s : MachineState) : BitVec 160 := sourceCounters s

theorem qword0 (s : MachineState) :
    word (q s) 0 = extractWord32 (s.getMem (BitVec.ofNat 64 0x20F0)) 0 := by
  unfold q sourceCounters word
  rw [BitVec.extractLsb'_append_eq_of_add_le (by decide : 0 + 32 ≤ 64)]
  simp only [extractWord32, BitVec.truncate_eq_setWidth,
    BitVec.setWidth_ushiftRight_eq_extractLsb]

theorem qword1 (s : MachineState) :
    word (q s) 1 = extractWord32 (s.getMem (BitVec.ofNat 64 0x20F0)) 1 := by
  unfold q sourceCounters word
  rw [BitVec.extractLsb'_append_eq_of_add_le (by decide : 32 + 32 ≤ 64)]
  simp only [extractWord32, BitVec.truncate_eq_setWidth,
    BitVec.setWidth_ushiftRight_eq_extractLsb]

theorem qword2 (s : MachineState) :
    word (q s) 2 = extractWord32 (s.getMem (BitVec.ofNat 64 0x20F8)) 0 := by
  unfold q sourceCounters word
  rw [BitVec.extractLsb'_append_eq_of_le (by decide : 64 ≤ 64)]
  rw [BitVec.extractLsb'_append_eq_of_add_le (by decide : 0 + 32 ≤ 64)]
  simp only [extractWord32, BitVec.truncate_eq_setWidth,
    BitVec.setWidth_ushiftRight_eq_extractLsb]

theorem qword3 (s : MachineState) :
    word (q s) 3 = extractWord32 (s.getMem (BitVec.ofNat 64 0x20F8)) 1 := by
  unfold q sourceCounters word
  rw [BitVec.extractLsb'_append_eq_of_le (by decide : 64 ≤ 96)]
  rw [BitVec.extractLsb'_append_eq_of_add_le (by decide : 32 + 32 ≤ 64)]
  simp only [extractWord32, BitVec.truncate_eq_setWidth,
    BitVec.setWidth_ushiftRight_eq_extractLsb]

theorem qword4 (s : MachineState) :
    word (q s) 4 = extractWord32 (s.getMem (BitVec.ofNat 64 0x2100)) 0 := by
  unfold q sourceCounters word
  rw [BitVec.extractLsb'_append_eq_of_le (by decide : 64 ≤ 128)]
  rw [BitVec.extractLsb'_append_eq_of_le (by decide : 64 ≤ 64)]
  simp only [extractWord32, BitVec.truncate_eq_setWidth,
    BitVec.setWidth_ushiftRight_eq_extractLsb]
  simp

theorem first_x9 (s : MachineState)
    (h6 : s.getReg .x6 = BitVec.ofNat 64 0x20F0) :
    (SigGolfCandidate.Radix27Images.signFirst.res.toState s).getReg .x9 =
      ((word (q s) 0).zeroExtend 64) := by
  rw [qword0]
  simp only [Result.toState_getReg, SigGolfCandidate.Radix27Images.signFirst.res,
    rv_simp, h6]

theorem first_x10 (s : MachineState)
    (h6 : s.getReg .x6 = BitVec.ofNat 64 0x20F0) :
    (SigGolfCandidate.Radix27Images.signFirst.res.toState s).getReg .x10 =
      ((word (q s) 1).zeroExtend 64) := by
  rw [qword1]
  simp only [Result.toState_getReg, SigGolfCandidate.Radix27Images.signFirst.res,
    rv_simp, h6]

theorem first_x11 (s : MachineState)
    (h6 : s.getReg .x6 = BitVec.ofNat 64 0x20F0) :
    (SigGolfCandidate.Radix27Images.signFirst.res.toState s).getReg .x11 =
      ((word (q s) 2).zeroExtend 64) := by
  rw [qword2]
  simp only [Result.toState_getReg, SigGolfCandidate.Radix27Images.signFirst.res,
    rv_simp, h6]
  rw [show (8432#64) + (8#64) = 8440#64 by decide]

theorem first_x12 (s : MachineState)
    (h6 : s.getReg .x6 = BitVec.ofNat 64 0x20F0) :
    (SigGolfCandidate.Radix27Images.signFirst.res.toState s).getReg .x12 =
      ((word (q s) 3).zeroExtend 64) := by
  rw [qword3]
  simp only [Result.toState_getReg, SigGolfCandidate.Radix27Images.signFirst.res,
    rv_simp, h6]
  rw [show (8432#64) + (8#64) = 8440#64 by decide]

theorem first_x13 (s : MachineState)
    (h6 : s.getReg .x6 = BitVec.ofNat 64 0x20F0) :
    (SigGolfCandidate.Radix27Images.signFirst.res.toState s).getReg .x13 =
      ((word (q s) 4).zeroExtend 64) := by
  rw [qword4]
  simp only [Result.toState_getReg, SigGolfCandidate.Radix27Images.signFirst.res,
    rv_simp, h6]
  rw [show (8432#64) + (16#64) = 8448#64 by decide]

#print axioms first_x9

#print axioms qword4
end Radix27SignLoaded


end


section -- Radix27SignTailProbe

namespace Radix27SignTailProbe
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv
  SigGolfCandidate.Radix27Images SigGolfCandidate.Rv Radix27

theorem valid0_pc (s : MachineState)
    (h13 : ((s.getReg .x13) >>> 16).toNat < 27)
    (h16 : s.getReg .x16 = 27#64) :
    (signValid0.res.toState s).pc = BitVec.ofNat 64 (0x1000 + 4 * 2950) := by
  simp only [Result.toState_pc, signValid0.res, rv_simp]
  simp only [h16, BitVec.toNat_ofNat]
  simpa [BitVec.ult_eq_decide, BitVec.toNat_ushiftRight] using h13

theorem valid0_obligs (s : MachineState) : signValid0.res.obligs s := by
  simp only [signValid0.res, rv_simp]

theorem valid1_pc (s : MachineState)
    (h12 : ((s.getReg .x12) >>> 16).toNat < 27)
    (h16 : s.getReg .x16 = 27#64) :
    (signValid1.res.toState s).pc = BitVec.ofNat 64 (0x1000 + 4 * 2953) := by
  simp only [Result.toState_pc, signValid1.res, rv_simp, h16, BitVec.toNat_ofNat]
  simpa [BitVec.ult_eq_decide, BitVec.toNat_ushiftRight] using h12

theorem valid2_pc (s : MachineState)
    (h11 : ((s.getReg .x11) >>> 16).toNat < 27)
    (h16 : s.getReg .x16 = 27#64) :
    (signValid2.res.toState s).pc = BitVec.ofNat 64 (0x1000 + 4 * 2957) := by
  simp only [Result.toState_pc, signValid2.res, rv_simp, h16, BitVec.toNat_ofNat]
  simpa [BitVec.ult_eq_decide, BitVec.toNat_ushiftRight] using h11

theorem valid3_pc (s : MachineState)
    (h10 : ((s.getReg .x10) >>> 16).toNat < 27)
    (h16 : s.getReg .x16 = 27#64) :
    (signValid3.res.toState s).pc = BitVec.ofNat 64 (0x1000 + 4 * 2961) := by
  simp only [Result.toState_pc, signValid3.res, rv_simp, h16, BitVec.toNat_ofNat]
  simpa [BitVec.ult_eq_decide, BitVec.toNat_ushiftRight] using h10

theorem valid4_pc (s : MachineState)
    (h9 : ((s.getReg .x9) >>> 16).toNat < 27)
    (h16 : s.getReg .x16 = 27#64) :
    (signValid4.res.toState s).pc = BitVec.ofNat 64 (0x1000 + 4 * 2965) := by
  simp only [Result.toState_pc, signValid4.res, rv_simp, h16, BitVec.toNat_ofNat]
  simpa [BitVec.ult_eq_decide, BitVec.toNat_ushiftRight] using h9

theorem valid0_fail_pc (s : MachineState)
    (h13 : 27 ≤ ((s.getReg .x13) >>> 16).toNat)
    (h16 : s.getReg .x16 = 27#64) :
    (signValid0.res.toState s).pc = BitVec.ofNat 64 (0x1000 + 4 * 2980) := by
  simp only [Result.toState_pc, signValid0.res, rv_simp, h16, BitVec.toNat_ofNat]
  simpa [BitVec.ult_eq_decide, BitVec.toNat_ushiftRight] using h13

theorem valid1_fail_pc (s : MachineState)
    (h12 : 27 ≤ ((s.getReg .x12) >>> 16).toNat)
    (h16 : s.getReg .x16 = 27#64) :
    (signValid1.res.toState s).pc = BitVec.ofNat 64 (0x1000 + 4 * 2980) := by
  simp only [Result.toState_pc, signValid1.res, rv_simp, h16, BitVec.toNat_ofNat]
  simpa [BitVec.ult_eq_decide, BitVec.toNat_ushiftRight] using h12

theorem valid2_fail_pc (s : MachineState)
    (h11 : 27 ≤ ((s.getReg .x11) >>> 16).toNat)
    (h16 : s.getReg .x16 = 27#64) :
    (signValid2.res.toState s).pc = BitVec.ofNat 64 (0x1000 + 4 * 2980) := by
  simp only [Result.toState_pc, signValid2.res, rv_simp, h16, BitVec.toNat_ofNat]
  simpa [BitVec.ult_eq_decide, BitVec.toNat_ushiftRight] using h11

theorem valid3_fail_pc (s : MachineState)
    (h10 : 27 ≤ ((s.getReg .x10) >>> 16).toNat)
    (h16 : s.getReg .x16 = 27#64) :
    (signValid3.res.toState s).pc = BitVec.ofNat 64 (0x1000 + 4 * 2980) := by
  simp only [Result.toState_pc, signValid3.res, rv_simp, h16, BitVec.toNat_ofNat]
  simpa [BitVec.ult_eq_decide, BitVec.toNat_ushiftRight] using h10

theorem valid4_fail_pc (s : MachineState)
    (h9 : 27 ≤ ((s.getReg .x9) >>> 16).toNat)
    (h16 : s.getReg .x16 = 27#64) :
    (signValid4.res.toState s).pc = BitVec.ofNat 64 (0x1000 + 4 * 2980) := by
  simp only [Result.toState_pc, signValid4.res, rv_simp, h16, BitVec.toNat_ofNat]
  simpa [BitVec.ult_eq_decide, BitVec.toNat_ushiftRight] using h9

end Radix27SignTailProbe


end


section -- Radix27SignRank

namespace Radix27SignRank
open RiscvZkvm.Rv64 Radix27
open SigGolfCandidate.Radix27Images SigGolfCandidate.Rv

def high64 (w : BitVec 32) : Word := w.zeroExtend 64 >>> 16

theorem high64_nat (w : BitVec 32) :
    (high64 w).toNat = (w.extractLsb' 16 16).toNat := by
  simp [high64, BitVec.toNat_ushiftRight, BitVec.extractLsb'_toNat,
    Nat.shiftRight_eq_div_pow]
  have hw := BitVec.isLt w
  omega

theorem horner_nat (a b : Word) (ha : a.toNat < 14348907)
    (hb : b.toNat < 27) :
    (a * 27#64 + b).toNat = a.toNat * 27 + b.toNat := by
  rw [BitVec.toNat_add, BitVec.toNat_mul]
  simp only [BitVec.toNat_ofNat]
  have hm : a.toNat * 27 < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt hm]
  have hs : a.toNat * 27 + b.toNat < 2 ^ 64 := by omega
  exact Nat.mod_eq_of_lt hs

def rankWord (q : BitVec 160) : Word :=
  (((high64 (word q 4) * 27#64 + high64 (word q 3)) * 27#64 +
    high64 (word q 2)) * 27#64 + high64 (word q 1)) * 27#64 +
    high64 (word q 0)

theorem rankWord_nat (q : BitVec 160) (h : validQ q) :
    (rankWord q).toNat = rankQ q := by
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  let a0 := high64 (word q 0)
  let a1 := high64 (word q 1)
  let a2 := high64 (word q 2)
  let a3 := high64 (word q 3)
  let a4 := high64 (word q 4)
  have n0 : a0.toNat = (highQ q 0).toNat := high64_nat _
  have n1 : a1.toNat = (highQ q 1).toNat := high64_nat _
  have n2 : a2.toNat = (highQ q 2).toNat := high64_nat _
  have n3 : a3.toNat = (highQ q 3).toNat := high64_nat _
  have n4 : a4.toNat = (highQ q 4).toNat := high64_nat _
  have b43 : (a4 * 27#64 + a3).toNat = a4.toNat * 27 + a3.toNat :=
    horner_nat a4 a3 (by omega) (by omega)
  have b432 : ((a4 * 27#64 + a3) * 27#64 + a2).toNat =
      (a4.toNat * 27 + a3.toNat) * 27 + a2.toNat := by
    rw [horner_nat _ _ (by rw [b43]; omega) (by omega), b43]
  have b4321 : (((a4 * 27#64 + a3) * 27#64 + a2) * 27#64 + a1).toNat =
      ((a4.toNat * 27 + a3.toNat) * 27 + a2.toNat) * 27 + a1.toNat := by
    rw [horner_nat _ _ (by rw [b432]; omega) (by omega), b432]
  have b43210 : ((((a4 * 27#64 + a3) * 27#64 + a2) * 27#64 + a1) * 27#64 + a0).toNat =
      (((a4.toNat * 27 + a3.toNat) * 27 + a2.toNat) * 27 + a1.toNat) * 27 + a0.toNat := by
    rw [horner_nat _ _ (by rw [b4321]; omega) (by omega), b4321]
  change ((((a4 * 27#64 + a3) * 27#64 + a2) * 27#64 + a1) * 27#64 + a0).toNat = _
  rw [b43210, n0, n1, n2, n3, n4]
  unfold rankQ rank5
  omega

def v0 (s : MachineState) := signFirst.res.toState s
def v1 (s : MachineState) := signValid0.res.toState (v0 s)
def v2 (s : MachineState) := signValid1.res.toState (v1 s)
def v3 (s : MachineState) := signValid2.res.toState (v2 s)
def v4 (s : MachineState) := signValid3.res.toState (v3 s)
def v5 (s : MachineState) := signValid4.res.toState (v4 s)
def v6 (s : MachineState) := signValidEnd.res.toState (v5 s)

theorem valid_rank (s : MachineState)
    (h6 : s.getReg .x6 = BitVec.ofNat 64 0x20F0) :
    (v6 s).getReg .x14 = rankWord (Radix27SignLoaded.q s) := by
  simp only [v6, v5, v4, v3, v2, v1, v0, Result.toState_getReg,
    signValidEnd.res, signValid4.res, signValid3.res, signValid2.res, signValid1.res,
    signValid0.res, signFirst.res, rv_simp, h6, rankWord,
    Radix27SignLoaded.qword0, Radix27SignLoaded.qword1,
    Radix27SignLoaded.qword2, Radix27SignLoaded.qword3,
    Radix27SignLoaded.qword4]
  simp only [high64, BitVec.toNat_ofNat, Nat.reduceDiv,
    show 8432#64 + 16#64 = 8448#64 by decide,
    show 8432#64 + 8#64 = 8440#64 by decide]

#print axioms high64_nat
#print axioms rankWord_nat
#print axioms valid_rank
end Radix27SignRank


end


section -- Radix27SignValidSteps

namespace Radix27SignValidSteps
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv
  SigGolfCandidate.Radix27Images SigGolfCandidate.Rv Radix27

theorem valid_word0_lt (q : BitVec 160) (h : validQ q) :
    (word q 0).toNat < 4194304 := by
  have h0 := h.1
  have hlo := BitVec.isLt (lowQ q 0)
  have hw := word_high_low q 0
  have hn : (word q 0).toNat =
      (highQ q 0).toNat * 65536 + (lowQ q 0).toNat := by
    rw [← hw, toNat_join16]
  norm_num at hlo
  omega

theorem first_pc_valid (s : MachineState)
    (h6 : s.getReg .x6 = BitVec.ofNat 64 0x20F0)
    (hv : validQ (Radix27SignLoaded.q s)) :
    (Radix27SignRank.v0 s).pc = BitVec.ofNat 64 (0x1000 + 4 * 2948) := by
  rw [Radix27SignRank.v0, signFirst_pc s h6]
  have hq : s.getWord32 (BitVec.ofNat 64 0x20F0) =
      word (Radix27SignLoaded.q s) 0 := by
    rw [Radix27SignLoaded.qword0]
    rfl
  rw [hq, if_pos (valid_word0_lt _ hv)]

theorem valid_h13 (s : MachineState)
    (h6 : s.getReg .x6 = BitVec.ofNat 64 0x20F0)
    (hv : validQ (Radix27SignLoaded.q s)) :
    (((Radix27SignRank.v0 s).getReg .x13) >>> 16).toNat < 27 := by
  unfold Radix27SignRank.v0
  rw [Radix27SignLoaded.first_x13 s h6]
  change (Radix27SignRank.high64 (word (Radix27SignLoaded.q s) 4)).toNat < 27
  rw [Radix27SignRank.high64_nat]
  exact hv.2.2.2.2

theorem valid_h12 (s : MachineState)
    (h6 : s.getReg .x6 = BitVec.ofNat 64 0x20F0)
    (hv : validQ (Radix27SignLoaded.q s)) :
    (((Radix27SignRank.v1 s).getReg .x12) >>> 16).toNat < 27 := by
  have heq : (Radix27SignRank.v1 s).getReg .x12 =
      (Radix27SignRank.v0 s).getReg .x12 := by
    simp only [Radix27SignRank.v1, Result.toState_getReg,
      signValid0.res, rv_simp]
  rw [heq]
  unfold Radix27SignRank.v0
  rw [Radix27SignLoaded.first_x12 s h6]
  change (Radix27SignRank.high64 (word (Radix27SignLoaded.q s) 3)).toNat < 27
  rw [Radix27SignRank.high64_nat]
  exact hv.2.2.2.1

theorem valid_h11 (s : MachineState)
    (h6 : s.getReg .x6 = BitVec.ofNat 64 0x20F0)
    (hv : validQ (Radix27SignLoaded.q s)) :
    (((Radix27SignRank.v2 s).getReg .x11) >>> 16).toNat < 27 := by
  have heq : (Radix27SignRank.v2 s).getReg .x11 =
      (Radix27SignRank.v0 s).getReg .x11 := by
    simp only [Radix27SignRank.v2, Radix27SignRank.v1,
      Result.toState_getReg, signValid1.res, signValid0.res, rv_simp]
  rw [heq]
  unfold Radix27SignRank.v0
  rw [Radix27SignLoaded.first_x11 s h6]
  change (Radix27SignRank.high64 (word (Radix27SignLoaded.q s) 2)).toNat < 27
  rw [Radix27SignRank.high64_nat]
  exact hv.2.2.1

theorem valid_h10 (s : MachineState)
    (h6 : s.getReg .x6 = BitVec.ofNat 64 0x20F0)
    (hv : validQ (Radix27SignLoaded.q s)) :
    (((Radix27SignRank.v3 s).getReg .x10) >>> 16).toNat < 27 := by
  have heq : (Radix27SignRank.v3 s).getReg .x10 =
      (Radix27SignRank.v0 s).getReg .x10 := by
    simp only [Radix27SignRank.v3, Radix27SignRank.v2,
      Radix27SignRank.v1, Result.toState_getReg,
      signValid2.res, signValid1.res, signValid0.res, rv_simp]
  rw [heq]
  unfold Radix27SignRank.v0
  rw [Radix27SignLoaded.first_x10 s h6]
  change (Radix27SignRank.high64 (word (Radix27SignLoaded.q s) 1)).toNat < 27
  rw [Radix27SignRank.high64_nat]
  exact hv.2.1

theorem valid_h9 (s : MachineState)
    (h6 : s.getReg .x6 = BitVec.ofNat 64 0x20F0)
    (hv : validQ (Radix27SignLoaded.q s)) :
    (((Radix27SignRank.v4 s).getReg .x9) >>> 16).toNat < 27 := by
  have heq : (Radix27SignRank.v4 s).getReg .x9 =
      (Radix27SignRank.v0 s).getReg .x9 := by
    simp only [Radix27SignRank.v4, Radix27SignRank.v3,
      Radix27SignRank.v2, Radix27SignRank.v1,
      Result.toState_getReg, signValid3.res,
      signValid2.res, signValid1.res, signValid0.res, rv_simp]
  rw [heq]
  unfold Radix27SignRank.v0
  rw [Radix27SignLoaded.first_x9 s h6]
  change (Radix27SignRank.high64 (word (Radix27SignLoaded.q s) 0)).toNat < 27
  rw [Radix27SignRank.high64_nat]
  exact hv.1

theorem valid_path (s : MachineState)
    (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * 2935))
    (h6 : s.getReg .x6 = BitVec.ofNat 64 0x20F0)
    (h7 : s.getReg .x7 = BitVec.ofNat 64 0x3F40)
    (hv : validQ (Radix27SignLoaded.q s)) :
    ∃ k c, Steps signImage s k c (Radix27SignRank.v6 s) ∧
      k < 100 ∧ c < 100 ∧
      (Radix27SignRank.v6 s).pc = BitVec.ofNat 64 (0x1000 + 4 * 2983) := by
  let u0 := Radix27SignRank.v0 s
  let u1 := Radix27SignRank.v1 s
  let u2 := Radix27SignRank.v2 s
  let u3 := Radix27SignRank.v3 s
  let u4 := Radix27SignRank.v4 s
  let u5 := Radix27SignRank.v5 s
  let u6 := Radix27SignRank.v6 s
  have st0 : Steps signImage s 12 12 u0 := signFirst_steps s hpc h6
  have hp0 : u0.pc = BitVec.ofNat 64 (0x1000 + 4 * 2948) := first_pc_valid s h6 hv
  have h16 (u : MachineState) (hu : u = u0 ∨ u = u1 ∨ u = u2 ∨ u = u3 ∨ u = u4) :
      u.getReg .x16 = 27#64 := by
    rcases hu with rfl | rfl | rfl | rfl | rfl <;>
      simp only [u0, u1, u2, u3, u4,
        Radix27SignRank.v4, Radix27SignRank.v3, Radix27SignRank.v2,
        Radix27SignRank.v1, Radix27SignRank.v0,
        Result.toState_getReg, signValid3.res, signValid2.res,
        signValid1.res, signValid0.res, signFirst.res, rv_simp]
  have ho1 : signValid0.res.obligs u0 := by simp only [signValid0.res, rv_simp]
  have st1 : Steps signImage u0 signValid0.res.steps signValid0.res.cycles u1 :=
    symRun_sound signValid0 codeAt_signValid0 u0 hp0 ho1
  have hp1 : u1.pc = BitVec.ofNat 64 (0x1000 + 4 * 2950) :=
    Radix27SignTailProbe.valid0_pc u0 (valid_h13 s h6 hv) (h16 u0 (Or.inl rfl))
  have ho2 : signValid1.res.obligs u1 := by simp only [signValid1.res, rv_simp]
  have st2 : Steps signImage u1 signValid1.res.steps signValid1.res.cycles u2 :=
    symRun_sound signValid1 codeAt_signValid1 u1 hp1 ho2
  have hp2 : u2.pc = BitVec.ofNat 64 (0x1000 + 4 * 2953) :=
    Radix27SignTailProbe.valid1_pc u1 (valid_h12 s h6 hv) (h16 u1 (Or.inr (Or.inl rfl)))
  have ho3 : signValid2.res.obligs u2 := by simp only [signValid2.res, rv_simp]
  have st3 : Steps signImage u2 signValid2.res.steps signValid2.res.cycles u3 :=
    symRun_sound signValid2 codeAt_signValid2 u2 hp2 ho3
  have hp3 : u3.pc = BitVec.ofNat 64 (0x1000 + 4 * 2957) :=
    Radix27SignTailProbe.valid2_pc u2 (valid_h11 s h6 hv)
      (h16 u2 (Or.inr (Or.inr (Or.inl rfl))))
  have ho4 : signValid3.res.obligs u3 := by simp only [signValid3.res, rv_simp]
  have st4 : Steps signImage u3 signValid3.res.steps signValid3.res.cycles u4 :=
    symRun_sound signValid3 codeAt_signValid3 u3 hp3 ho4
  have hp4 : u4.pc = BitVec.ofNat 64 (0x1000 + 4 * 2961) :=
    Radix27SignTailProbe.valid3_pc u3 (valid_h10 s h6 hv)
      (h16 u3 (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have ho5 : signValid4.res.obligs u4 := by simp only [signValid4.res, rv_simp]
  have st5 : Steps signImage u4 signValid4.res.steps signValid4.res.cycles u5 :=
    symRun_sound signValid4 codeAt_signValid4 u4 hp4 ho5
  have hp5 : u5.pc = BitVec.ofNat 64 (0x1000 + 4 * 2965) :=
    Radix27SignTailProbe.valid4_pc u4 (valid_h9 s h6 hv)
      (h16 u4 (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
  have h7u5 : u5.getReg .x7 = BitVec.ofNat 64 0x3F40 := by
    simpa only [u5, u4, u3, u2, u1, u0,
      Radix27SignRank.v5, Radix27SignRank.v4, Radix27SignRank.v3,
      Radix27SignRank.v2, Radix27SignRank.v1, Radix27SignRank.v0,
      Result.toState_getReg, signValid4.res, signValid3.res,
      signValid2.res, signValid1.res, signValid0.res, signFirst.res,
      rv_simp] using h7
  have ho6 : signValidEnd.res.obligs u5 := signValidEnd_obligs u5 h7u5
  have st6 : Steps signImage u5 signValidEnd.res.steps signValidEnd.res.cycles u6 :=
    symRun_sound signValidEnd codeAt_signValidEnd u5 hp5 ho6
  have hp6 : u6.pc = BitVec.ofNat 64 (0x1000 + 4 * 2983) := by
    simp only [u6, Radix27SignRank.v6, Result.toState_pc, signValidEnd.res, rv_simp]
  have ht := (((((st0.trans st1).trans st2).trans st3).trans st4).trans st5).trans st6
  exact ⟨_, _, ht, by decide, by decide, hp6⟩

end Radix27SignValidSteps


end


section -- Radix27SignHighs

namespace Radix27SignHighs
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv
  SigGolfCandidate.Radix27Images SigGolfCandidate.Rv Radix27

theorem high13_nat (s : MachineState)
    (h6 : s.getReg .x6 = BitVec.ofNat 64 0x20F0) :
    (((Radix27SignRank.v0 s).getReg .x13) >>> 16).toNat =
      (highQ (Radix27SignLoaded.q s) 4).toNat := by
  unfold Radix27SignRank.v0
  rw [Radix27SignLoaded.first_x13 s h6]
  exact Radix27SignRank.high64_nat _

theorem high12_nat (s : MachineState)
    (h6 : s.getReg .x6 = BitVec.ofNat 64 0x20F0) :
    (((Radix27SignRank.v1 s).getReg .x12) >>> 16).toNat =
      (highQ (Radix27SignLoaded.q s) 3).toNat := by
  have heq : (Radix27SignRank.v1 s).getReg .x12 =
      (Radix27SignRank.v0 s).getReg .x12 := by
    simp only [Radix27SignRank.v1, Result.toState_getReg,
      signValid0.res, rv_simp]
  rw [heq]
  unfold Radix27SignRank.v0
  rw [Radix27SignLoaded.first_x12 s h6]
  exact Radix27SignRank.high64_nat _

theorem high11_nat (s : MachineState)
    (h6 : s.getReg .x6 = BitVec.ofNat 64 0x20F0) :
    (((Radix27SignRank.v2 s).getReg .x11) >>> 16).toNat =
      (highQ (Radix27SignLoaded.q s) 2).toNat := by
  have heq : (Radix27SignRank.v2 s).getReg .x11 =
      (Radix27SignRank.v0 s).getReg .x11 := by
    simp only [Radix27SignRank.v2, Radix27SignRank.v1,
      Result.toState_getReg, signValid1.res, signValid0.res, rv_simp]
  rw [heq]
  unfold Radix27SignRank.v0
  rw [Radix27SignLoaded.first_x11 s h6]
  exact Radix27SignRank.high64_nat _

theorem high10_nat (s : MachineState)
    (h6 : s.getReg .x6 = BitVec.ofNat 64 0x20F0) :
    (((Radix27SignRank.v3 s).getReg .x10) >>> 16).toNat =
      (highQ (Radix27SignLoaded.q s) 1).toNat := by
  have heq : (Radix27SignRank.v3 s).getReg .x10 =
      (Radix27SignRank.v0 s).getReg .x10 := by
    simp only [Radix27SignRank.v3, Radix27SignRank.v2,
      Radix27SignRank.v1, Result.toState_getReg,
      signValid2.res, signValid1.res, signValid0.res, rv_simp]
  rw [heq]
  unfold Radix27SignRank.v0
  rw [Radix27SignLoaded.first_x10 s h6]
  exact Radix27SignRank.high64_nat _

theorem high9_nat (s : MachineState)
    (h6 : s.getReg .x6 = BitVec.ofNat 64 0x20F0) :
    (((Radix27SignRank.v4 s).getReg .x9) >>> 16).toNat =
      (highQ (Radix27SignLoaded.q s) 0).toNat := by
  have heq : (Radix27SignRank.v4 s).getReg .x9 =
      (Radix27SignRank.v0 s).getReg .x9 := by
    simp only [Radix27SignRank.v4, Radix27SignRank.v3,
      Radix27SignRank.v2, Radix27SignRank.v1,
      Result.toState_getReg, signValid3.res,
      signValid2.res, signValid1.res, signValid0.res, rv_simp]
  rw [heq]
  unfold Radix27SignRank.v0
  rw [Radix27SignLoaded.first_x9 s h6]
  exact Radix27SignRank.high64_nat _

#print axioms high13_nat
#print axioms high9_nat
end Radix27SignHighs


end


section -- Radix27SignTrailer

namespace Radix27SignTrailer
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv
  SigGolfCandidate.Radix27Images SigGolfCandidate.Rv
  SigGolfCandidate.Packed SigGolfCandidate.Ref SigGolfCandidate.Mem

def tailData (u : MachineState) : BitVec 104 :=
  (u.getReg .x14).truncate 24 ++ (u.getReg .x17).truncate 16 ++
    u.getMem (BitVec.ofNat 64 0x3F40)

theorem tailData_split (u : MachineState) :
    toList (n := 13) (tailData u) =
      toList (n := 8) (u.getMem (BitVec.ofNat 64 0x3F40)) ++
      toList (n := 2) ((u.getReg .x17).truncate 16) ++
      toList (n := 3) ((u.getReg .x14).truncate 24) := by
  unfold tailData
  have h1 := toList_concat (n := 8) (m := 5)
    (u.getMem (BitVec.ofNat 64 0x3F40))
    ((u.getReg .x14).truncate 24 ++ (u.getReg .x17).truncate 16)
  have h2 := toList_concat (n := 2) (m := 3)
    ((u.getReg .x17).truncate 16) ((u.getReg .x14).truncate 24)
  simp only [BitVec.cast_eq] at h1 h2
  rw [h2] at h1
  simpa only [List.append_assoc] using h1

theorem trailer_low_mem (u : MachineState)
    (h7 : u.getReg .x7 = BitVec.ofNat 64 0x3F40) :
    (signTrailer.res.toState u).getMem (BitVec.ofNat 64 0x3F40) =
      u.getMem (BitVec.ofNat 64 0x3F40) := by
  simp only [Result.toState_getMem, signTrailer.res, rv_simp, h7]
  simp only [show 16192#64 ≠ 16192#64 + 8#64 by decide, if_false]

theorem tailData_low_byte (u : MachineState) (j : Nat) (hj : j < 8) :
    (toList (n := 13) (tailData u)).getD j 0 =
      (toList (n := 8) (u.getMem (BitVec.ofNat 64 0x3F40))).getD j 0 := by
  rw [tailData_split]
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by simp [length_toList]; omega)]
  rw [List.getElem?_append_left (by rw [length_toList]; exact hj)]

theorem tailData_mid_byte (u : MachineState) (j : Nat) (hj : j < 2) :
    (toList (n := 13) (tailData u)).getD (8 + j) 0 =
      (toList (n := 2) ((u.getReg .x17).truncate 16)).getD j 0 := by
  rw [tailData_split]
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by simp [length_toList]; omega)]
  rw [List.getElem?_append_right (by rw [length_toList]; omega)]
  simp only [length_toList, Nat.add_sub_cancel_left]

theorem tailData_rank_byte (u : MachineState) (j : Nat) (hj : j < 3) :
    (toList (n := 13) (tailData u)).getD (10 + j) 0 =
      (toList (n := 3) ((u.getReg .x14).truncate 24)).getD j 0 := by
  rw [tailData_split]
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by simp [length_toList])]
  simp only [List.length_append, length_toList]
  have heq : 10 + j - (8 + 2) = j := by omega
  rw [heq]

theorem tailData_high_byte (u : MachineState) (j : Nat) (hj : j < 5) :
    (toList (n := 13) (tailData u)).getD (8 + j) 0 =
      (toList (n := 5)
        ((u.getReg .x14).truncate 24 ++ (u.getReg .x17).truncate 16)).getD j 0 := by
  rw [tailData_split]
  have hp := toList_concat (n := 2) (m := 3)
    ((u.getReg .x17).truncate 16) ((u.getReg .x14).truncate 24)
  simp only [BitVec.cast_eq] at hp
  simp only [List.append_assoc]
  rw [← hp]
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by rw [length_toList]; omega)]
  simp only [length_toList, Nat.add_sub_cancel_left]

def trailerHighWord (u : MachineState) : Word :=
  replaceByte
    (replaceWord32 (u.getMem (BitVec.ofNat 64 0x3F48)) 0
      ((u.getReg .x14 <<< 16 ||| u.getReg .x17).truncate 32))
    4 ((u.getReg .x14 >>> 16).truncate 8)

theorem trailer_high_mem (u : MachineState)
    (h7 : u.getReg .x7 = BitVec.ofNat 64 0x3F40) :
    (signTrailer.res.toState u).getMem (BitVec.ofNat 64 0x3F48) =
      trailerHighWord u := by
  simp only [Result.toState_getMem, signTrailer.res, rv_simp, h7,
    trailerHighWord]
  simp only [show 16192#64 + 8#64 = 16200#64 by decide, if_true]
  norm_num

theorem trailer_steps (u : MachineState)
    (hpc : u.pc = BitVec.ofNat 64 (0x1000 + 4 * 2983))
    (h7 : u.getReg .x7 = BitVec.ofNat 64 0x3F40) :
    Steps signImage u signTrailer.res.steps signTrailer.res.cycles
      (signTrailer.res.toState u) ∧
    fetch signImage (signTrailer.res.toState u) = some (.base .ECALL) ∧
    (signTrailer.res.toState u).getReg .x5 = 1 ∧
    (signTrailer.res.toState u).getReg .x10 = 0 := by
  have ho : signTrailer.res.obligs u := by
    simp only [signTrailer.res, rv_simp, h7]
    decide
  exact ⟨symRun_sound signTrailer codeAt_signTrailer u hpc ho,
    symRun_ecall signTrailer codeAt_signTrailer u ho rfl,
    by simp only [Result.toState_getReg, signTrailer.res, rv_simp],
    by simp only [Result.toState_getReg, signTrailer.res, rv_simp]⟩

theorem rankLow16Word (r : Word) (l : BitVec 16) :
    ((r <<< 16 ||| l.zeroExtend 64).truncate 32) =
      r.truncate 16 ++ l := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_append]
  interval_cases i <;> simp [BitVec.getLsbD_ofNat, Nat.testBit]

theorem high40_byte (m r : Word) (l : BitVec 16) (j : Nat)
    (hj : j < 5) :
    extractByte
      (replaceByte (replaceWord32 m 0 (r.truncate 16 ++ l)) 4
        ((r >>> 16).truncate 8)) j =
      (toList (n := 5) (r.truncate 24 ++ l)).getD j 0 := by
  interval_cases j <;>
    simp [toList, SigGolfCandidate.Legacy.bytes,
      replaceByte, extractByte,
      replaceWord32, BitVec.truncate_eq_setWidth,
      BitVec.setWidth_ushiftRight_eq_extractLsb] <;>
    bv_normalize <;>
    simp_all [BitVec.extractLsb'_extractLsb'_of_le,
      BitVec.extractLsb'_append_eq_right,
      BitVec.extractLsb'_append_eq_of_add_le,
      BitVec.extractLsb'_append_eq_of_le] <;>
    (have hlast : BitVec.extractLsb' 0 8
        (0#56 ++ BitVec.extractLsb' 16 8 r) = BitVec.extractLsb' 16 8 r :=
          BitVec.extractLsb'_append_eq_right
     simp_all [hlast])

theorem lowReg_eq (x : Word) (hx : x.toNat < 65536) :
    x = (x.truncate 16).zeroExtend 64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.zeroExtend, BitVec.truncate,
    BitVec.toNat_setWidth]
  omega

theorem trailer_high_byte (u : MachineState)
    (h7 : u.getReg .x7 = BitVec.ofNat 64 0x3F40)
    (hx : (u.getReg .x17).toNat < 65536)
    (j : Nat) (hj : j < 5) :
    (signTrailer.res.toState u).getByte (BitVec.ofNat 64 (0x3F48 + j)) =
      (toList (n := 5)
        ((u.getReg .x14).truncate 24 ++ (u.getReg .x17).truncate 16)).getD j 0 := by
  have ha : alignToDword (BitVec.ofNat 64 (0x3F48 + j)) =
      BitVec.ofNat 64 0x3F48 := by
    apply BitVec.eq_of_toNat_eq
    rw [alignToDword_toNat]
    simp only [BitVec.toNat_ofNat]
    omega
  have hb : byteOffset (BitVec.ofNat 64 (0x3F48 + j)) = j := by
    rw [byteOffset_ofNat (by omega)]
    omega
  simp only [MachineState.getByte]
  rw [ha, hb, trailer_high_mem u h7]
  unfold trailerHighWord
  have htrunc : (((u.getReg .x17).truncate 16).zeroExtend 64).truncate 16 =
      (u.getReg .x17).truncate 16 := by
    simpa only [BitVec.truncate_eq_setWidth, BitVec.zeroExtend_eq_setWidth,
      BitVec.setWidth_eq] using
      (BitVec.setWidth_setWidth_of_le
        ((u.getReg .x17).truncate 16) (by decide : 16 ≤ 64))
  rw [lowReg_eq _ hx, rankLow16Word, htrunc]
  exact high40_byte _ _ _ j hj

theorem trailer_low_byte (u : MachineState)
    (h7 : u.getReg .x7 = BitVec.ofNat 64 0x3F40)
    (j : Nat) (hj : j < 8) :
    (signTrailer.res.toState u).getByte (BitVec.ofNat 64 (0x3F40 + j)) =
      u.getByte (BitVec.ofNat 64 (0x3F40 + j)) := by
  have ha : alignToDword (BitVec.ofNat 64 (0x3F40 + j)) =
      BitVec.ofNat 64 0x3F40 := by
    apply BitVec.eq_of_toNat_eq
    rw [alignToDword_toNat]
    simp only [BitVec.toNat_ofNat]
    omega
  simp only [MachineState.getByte]
  rw [ha, trailer_low_mem u h7]

theorem trailer_output (u : MachineState)
    (h7 : u.getReg .x7 = BitVec.ofNat 64 0x3F40)
    (hx : (u.getReg .x17).toNat < 65536) :
    readBuffer (signTrailer.res.toState u) 0x3F40 13 = tailData u := by
  apply readBuffer_eq_of_bytes
  intro i hi
  by_cases hlo : i < 8
  · rw [trailer_low_byte u h7 i hlo, tailData_low_byte u i hlo]
    have ha : alignToDword (BitVec.ofNat 64 (0x3F40 + i)) =
        BitVec.ofNat 64 0x3F40 := by
      apply BitVec.eq_of_toNat_eq
      rw [alignToDword_toNat]
      simp only [BitVec.toNat_ofNat]
      omega
    have hb : byteOffset (BitVec.ofNat 64 (0x3F40 + i)) = i := by
      rw [byteOffset_ofNat (by omega)]
      omega
    simp only [MachineState.getByte]
    rw [ha, hb]
    simp [toList, SigGolfCandidate.Legacy.bytes, hlo, extractByte,
      BitVec.truncate_eq_setWidth,
      BitVec.setWidth_ushiftRight_eq_extractLsb, Nat.mul_comm]
  · have hj : i - 8 < 5 := by omega
    have heq : 0x3F40 + i = 0x3F48 + (i - 8) := by omega
    rw [heq, trailer_high_byte u h7 hx (i - 8) hj]
    have hi' : 8 + (i - 8) = i := by omega
    rw [← hi', tailData_high_byte u (i - 8) hj]
    simp only [Nat.add_sub_cancel_left]

#print axioms rankLow16Word
#print axioms high40_byte

end Radix27SignTrailer


end


section -- Radix27ByteLemmas

namespace Radix27StoreByteTry
open RiscvZkvm.Rv64

theorem byte_ext {w1 w2 : Word}
    (h : ∀ j, j < 8 → extractByte w1 j = extractByte w2 j) : w1 = w2 := by
  apply BitVec.eq_of_getLsbD_eq
  intro p hp
  have hmod : p % 8 < 8 := Nat.mod_lt _ (by decide)
  have h2 : p / 8 * 8 + p % 8 = p := by omega
  have hbit := congrArg (fun bb => bb.getLsbD (p % 8)) (h (p / 8) (by omega))
  simp only [extractByte, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, h2, hmod,
    decide_true, Bool.true_and] at hbit
  exact hbit

local macro "byte_algebra" : tactic =>
  `(tactic| (ext i (hi : i < 8); simp [BitVec.truncate, BitVec.zeroExtend];
             try { interval_cases i <;> simp_all }))

theorem byte_replaceHalfword (w : Word) (h : BitVec 16) {pos j : Nat}
    (hpos : pos < 4) (hj : j < 8) :
    extractByte (replaceHalfword w pos h) j
      = if j = 2 * pos then h.truncate 8
        else if j = 2 * pos + 1 then (h >>> 8).truncate 8
        else extractByte w j := by
  interval_cases pos <;> interval_cases j <;>
    simp only [replaceHalfword, extractByte, Nat.reduceMul, Nat.reduceAdd,
      reduceIte, Nat.zero_ne_add_one, Nat.add_one_ne_zero] <;>
    byte_algebra

#print axioms byte_replaceHalfword
end Radix27StoreByteTry


end


section -- Radix27StoreByteFinal

namespace Radix27StoreByteFinal
open RiscvZkvm.Rv64 Radix27StoreByteTry

example (a b : BitVec 16) :
    BitVec.extractLsb' 8 8 a = BitVec.extractLsb' 8 8 (b ++ a) := by
  rw [BitVec.extractLsb'_append_eq_of_add_le (by decide)]

theorem four_halfwords (m : Word) (a b c d : BitVec 16) :
    replaceHalfword (replaceHalfword (replaceHalfword (replaceHalfword m 0 a) 1 b) 2 c) 3 d
      = d ++ c ++ b ++ a := by
  apply byte_ext
  intro j hj
  interval_cases j <;>
    (repeat rw [byte_replaceHalfword _ _ (by decide) (by decide)]) <;>
    simp [extractByte, BitVec.truncate, BitVec.setWidth_ushiftRight_eq_extractLsb]
  case «0» =>
    rw [BitVec.setWidth_eq_extractLsb' (by decide)]
    rw [BitVec.setWidth_eq_extractLsb' (by decide)]
    rw [BitVec.extractLsb'_append_eq_of_add_le (by decide)]
  case «1» => rw [BitVec.extractLsb'_append_eq_of_add_le (by decide)]
  case «2» =>
    rw [BitVec.extractLsb'_append_eq_of_le (by decide)]
    rw [BitVec.extractLsb'_append_eq_of_add_le (by decide)]
    rw [BitVec.setWidth_eq_extractLsb' (by decide)]
  case «3» =>
    rw [BitVec.extractLsb'_append_eq_of_le (by decide)]
    rw [BitVec.extractLsb'_append_eq_of_add_le (by decide)]
  case «4» =>
    rw [BitVec.extractLsb'_append_eq_of_le (by decide)]
    rw [BitVec.extractLsb'_append_eq_of_le (by decide)]
    rw [BitVec.extractLsb'_append_eq_of_add_le (by decide)]
    rw [BitVec.setWidth_eq_extractLsb' (by decide)]
  case «5» =>
    rw [BitVec.extractLsb'_append_eq_of_le (by decide)]
    rw [BitVec.extractLsb'_append_eq_of_le (by decide)]
    rw [BitVec.extractLsb'_append_eq_of_add_le (by decide)]
  case «6» =>
    rw [BitVec.extractLsb'_append_eq_of_le (by decide)]
    rw [BitVec.extractLsb'_append_eq_of_le (by decide)]
    rw [BitVec.extractLsb'_append_eq_of_le (by decide)]
    rw [BitVec.setWidth_eq_extractLsb' (by decide)]
  case «7» =>
    rw [BitVec.extractLsb'_append_eq_of_le (by decide)]
    rw [BitVec.extractLsb'_append_eq_of_le (by decide)]
    rw [BitVec.extractLsb'_append_eq_of_le (by decide)]

#print axioms four_halfwords
end Radix27StoreByteFinal


end


section -- Radix27AppendDrop

namespace Radix27AppendDrop
theorem drop16 (a b c d e : BitVec 16) :
    (e ++ d ++ c ++ b ++ a).extractLsb' 0 64 = d ++ c ++ b ++ a := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
  simp only [zero_add, decide_eq_true hi, Bool.true_and]
  interval_cases i <;> simp

#print axioms drop16
end Radix27AppendDrop


end


section -- Radix27SignWords

namespace Radix27SignWords
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv
  SigGolfCandidate.Radix27Images SigGolfCandidate.Rv Radix27

theorem valid_low64 (s : MachineState)
    (h6 : s.getReg .x6 = BitVec.ofNat 64 0x20F0)
    (h7 : s.getReg .x7 = BitVec.ofNat 64 0x3F40) :
    (Radix27SignRank.v6 s).getMem (BitVec.ofNat 64 0x3F40) =
      (lowPack (Radix27SignLoaded.q s)).extractLsb' 0 64 := by
  simp only [Radix27SignRank.v6, Radix27SignRank.v5,
    Radix27SignRank.v4, Radix27SignRank.v3,
    Radix27SignRank.v2, Radix27SignRank.v1, Radix27SignRank.v0,
    Result.toState_getMem, Result.toState_getReg,
    signValidEnd.res, signValid4.res, signValid3.res,
    signValid2.res, signValid1.res, signValid0.res,
    signFirst.res, rv_simp, h6, h7]
  simp only [ite_true, Nat.reduceDiv,
    show 8432#64 + 8#64 = 8440#64 by decide]
  rw [Radix27StoreByteFinal.four_halfwords]
  unfold lowPack lowQ
  rw [Radix27SignLoaded.qword0, Radix27SignLoaded.qword1,
    Radix27SignLoaded.qword2, Radix27SignLoaded.qword3]
  simp only [Radix27AppendDrop.drop16]
  bv_normalize

#print axioms valid_low64

end Radix27SignWords


end


section -- Radix27SignValidOutput

namespace Radix27SignValidOutput
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv
  SigGolfCandidate.Radix27Images SigGolfCandidate.Rv Radix27

theorem valid_x17 (s : MachineState)
    (h6 : s.getReg .x6 = BitVec.ofNat 64 0x20F0) :
    (Radix27SignRank.v6 s).getReg .x17 =
      (lowQ (Radix27SignLoaded.q s) 4).zeroExtend 64 := by
  simp only [Radix27SignRank.v6, Radix27SignRank.v5,
    Radix27SignRank.v4, Radix27SignRank.v3,
    Radix27SignRank.v2, Radix27SignRank.v1,
    Radix27SignRank.v0, Result.toState_getReg,
    signValidEnd.res, signValid4.res, signValid3.res,
    signValid2.res, signValid1.res, signValid0.res,
    signFirst.res, rv_simp, h6]
  unfold lowQ
  rw [Radix27SignLoaded.qword4]
  bv_normalize

theorem valid_x17_lt (s : MachineState)
    (h6 : s.getReg .x6 = BitVec.ofNat 64 0x20F0) :
    ((Radix27SignRank.v6 s).getReg .x17).toNat < 65536 := by
  rw [valid_x17 s h6]
  have hlo := BitVec.isLt (lowQ (Radix27SignLoaded.q s) 4)
  simp only [BitVec.zeroExtend_eq_setWidth, BitVec.toNat_setWidth]
  rw [Nat.mod_eq_of_lt (by omega : (lowQ (Radix27SignLoaded.q s) 4).toNat < 2 ^ 64)]
  simpa using hlo

theorem valid_rank24 (s : MachineState)
    (h6 : s.getReg .x6 = BitVec.ofNat 64 0x20F0)
    (hv : validQ (Radix27SignLoaded.q s)) :
    ((Radix27SignRank.v6 s).getReg .x14).truncate 24 =
      BitVec.ofNat 24 (rankQ (Radix27SignLoaded.q s)) := by
  rw [Radix27SignRank.valid_rank s h6]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.truncate_eq_setWidth,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    Radix27SignRank.rankWord_nat _ hv]

theorem lowPack_split4 (q : BitVec 160) :
    lowQ q 4 ++ (lowPack q).extractLsb' 0 64 = lowPack q := by
  have h4 := lowPack_part4 q
  change (lowPack q).extractLsb' 64 16 = lowQ q 4 at h4
  rw [← h4]
  exact BitVec.extractLsb'_append_extractLsb'

theorem valid_tailData (s : MachineState)
    (h6 : s.getReg .x6 = BitVec.ofNat 64 0x20F0)
    (h7 : s.getReg .x7 = BitVec.ofNat 64 0x3F40)
    (hv : validQ (Radix27SignLoaded.q s)) :
    Radix27SignTrailer.tailData (Radix27SignRank.v6 s) =
      pack13 (Radix27SignLoaded.q s) := by
  let q := Radix27SignLoaded.q s
  rw [Radix27SignTrailer.tailData, valid_rank24 s h6 hv,
    valid_x17 s h6, Radix27SignWords.valid_low64 s h6 h7,
    pack13_validQ q hv]
  have hz : ((lowQ q 4).zeroExtend 64).truncate 16 = lowQ q 4 := by
    simp only [BitVec.zeroExtend_eq_setWidth, BitVec.truncate_eq_setWidth]
    rw [BitVec.setWidth_setWidth_of_le (lowQ q 4) (by decide : 16 ≤ 64)]
    rw [BitVec.setWidth_eq]
  rw [hz, BitVec.append_assoc, lowPack_split4]
  rfl

#print axioms valid_x17
#print axioms valid_rank24
#print axioms valid_tailData
end Radix27SignValidOutput


end


section -- Radix27SignTailValid

namespace Radix27SignTailValid
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv
  SigGolfCandidate.Radix27Images SigGolfCandidate.Rv Radix27

theorem valid_h7_v6 (s : MachineState)
    (h7 : s.getReg .x7 = BitVec.ofNat 64 0x3F40) :
    (Radix27SignRank.v6 s).getReg .x7 = BitVec.ofNat 64 0x3F40 := by
  simpa only [Radix27SignRank.v6, Radix27SignRank.v5,
    Radix27SignRank.v4, Radix27SignRank.v3,
    Radix27SignRank.v2, Radix27SignRank.v1, Radix27SignRank.v0,
    Result.toState_getReg, signValidEnd.res,
    signValid4.res, signValid3.res, signValid2.res,
    signValid1.res, signValid0.res, signFirst.res, rv_simp] using h7

theorem valid_tail_steps (s : MachineState)
    (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * 2935))
    (h6 : s.getReg .x6 = BitVec.ofNat 64 0x20F0)
    (h7 : s.getReg .x7 = BitVec.ofNat 64 0x3F40)
    (hv : validQ (Radix27SignLoaded.q s)) :
    ∃ k c u, Steps signImage s k c u ∧ k < 120 ∧ c < 120 ∧
      fetch signImage u = some (.base .ECALL) ∧
      u.getReg .x5 = 1 ∧ u.getReg .x10 = 0 ∧
      readBuffer u 0x3F40 13 = pack13 (Radix27SignLoaded.q s) := by
  obtain ⟨k, c, hs, hk, hc, hpc6⟩ :=
    Radix27SignValidSteps.valid_path s hpc h6 h7 hv
  let v := Radix27SignRank.v6 s
  let u := signTrailer.res.toState v
  obtain ⟨ht, hf, h5, h10⟩ :=
    Radix27SignTrailer.trailer_steps v hpc6 (valid_h7_v6 s h7)
  have hout : readBuffer u 0x3F40 13 = pack13 (Radix27SignLoaded.q s) := by
    rw [Radix27SignTrailer.trailer_output v (valid_h7_v6 s h7)
      (Radix27SignValidOutput.valid_x17_lt s h6)]
    exact Radix27SignValidOutput.valid_tailData s h6 h7 hv
  have hsAll := hs.trans ht
  refine ⟨_, _, u, hsAll, ?_, ?_, hf, h5, h10, hout⟩
  · have hst : signTrailer.res.steps < 20 := by decide
    omega
  · have hct : signTrailer.res.cycles < 20 := by decide
    omega

#print axioms valid_tail_steps
end Radix27SignTailValid


end


section -- Radix27SignFallback

namespace Radix27SignFallback
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv
  SigGolfCandidate.Radix27Images SigGolfCandidate.Rv Radix27

def fb (t : MachineState) : MachineState := signFallback.res.toState t

theorem fallback_steps (t : MachineState)
    (hpc : t.pc = BitVec.ofNat 64 (0x1000 + 4 * 2980))
    (h7 : t.getReg .x7 = BitVec.ofNat 64 0x3F40) :
    Steps signImage t signFallback.res.steps signFallback.res.cycles (fb t) ∧
      (fb t).pc = BitVec.ofNat 64 (0x1000 + 4 * 2983) := by
  have ho : signFallback.res.obligs t := by
    simp only [signFallback.res, rv_simp, h7]
    decide
  exact ⟨symRun_sound signFallback codeAt_signFallback t hpc ho,
    by simp only [fb, Result.toState_pc, signFallback.res, rv_simp]⟩

theorem fallback_h7 (t : MachineState) :
    (fb t).getReg .x7 = t.getReg .x7 := by
  simp only [fb, Result.toState_getReg, signFallback.res, rv_simp]

theorem fallback_x17 (t : MachineState) :
    (fb t).getReg .x17 = 0 := by
  simp only [fb, Result.toState_getReg, signFallback.res, rv_simp]

theorem fallback_x14 (t : MachineState) :
    (fb t).getReg .x14 = t.getReg .x21 := by
  simp only [fb, Result.toState_getReg, signFallback.res, rv_simp]

theorem fallback_low64 (t : MachineState)
    (h7 : t.getReg .x7 = BitVec.ofNat 64 0x3F40) :
    (fb t).getMem (BitVec.ofNat 64 0x3F40) = 0 := by
  simp only [fb, Result.toState_getMem, signFallback.res, rv_simp, h7]
  simp

theorem fallback_tailData (t : MachineState)
    (h7 : t.getReg .x7 = BitVec.ofNat 64 0x3F40)
    (h21 : t.getReg .x21 = BitVec.ofNat 64 14348907) :
    Radix27SignTrailer.tailData (fb t) = fallback13 := by
  simp only [Radix27SignTrailer.tailData, fallback_x14, fallback_x17,
    fallback_low64 t h7, h21, fallback13]
  decide

theorem fallback_tail_steps (t : MachineState)
    (hpc : t.pc = BitVec.ofNat 64 (0x1000 + 4 * 2980))
    (h7 : t.getReg .x7 = BitVec.ofNat 64 0x3F40)
    (h21 : t.getReg .x21 = BitVec.ofNat 64 14348907) :
    ∃ k c u, Steps signImage t k c u ∧ k < 20 ∧ c < 20 ∧
      fetch signImage u = some (.base .ECALL) ∧
      u.getReg .x5 = 1 ∧ u.getReg .x10 = 0 ∧
      readBuffer u 0x3F40 13 = fallback13 := by
  obtain ⟨hs, hp⟩ := fallback_steps t hpc h7
  let v := fb t
  let u := signTrailer.res.toState v
  have hv7 : v.getReg .x7 = BitVec.ofNat 64 0x3F40 := by
    rw [fallback_h7, h7]
  obtain ⟨ht, hf, h5, h10⟩ := Radix27SignTrailer.trailer_steps v hp hv7
  have hout : readBuffer u 0x3F40 13 = fallback13 := by
    rw [Radix27SignTrailer.trailer_output v hv7]
    · exact fallback_tailData t h7 h21
    · rw [fallback_x17]; decide
  have hsAll := hs.trans ht
  refine ⟨_, _, u, hsAll, ?_, ?_, hf, h5, h10, hout⟩
  · decide
  · decide

#print axioms fallback_tail_steps
end Radix27SignFallback


end


section -- Radix27SignFallbackPath

namespace Radix27SignFallbackPath
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv
  SigGolfCandidate.Radix27Images SigGolfCandidate.Rv Radix27

def GateRegs (u : MachineState) : Prop :=
  u.getReg .x7 = BitVec.ofNat 64 0x3F40 ∧
  u.getReg .x16 = 27#64 ∧
  u.getReg .x21 = BitVec.ofNat 64 14348907

theorem gateRegs_v0 (s : MachineState)
    (h7 : s.getReg .x7 = BitVec.ofNat 64 0x3F40) :
    GateRegs (Radix27SignRank.v0 s) := by
  simp only [GateRegs, Radix27SignRank.v0, Result.toState_getReg,
    signFirst.res, rv_simp, h7, and_self]

theorem gateRegs_v1 (s : MachineState) (h : GateRegs s) :
    GateRegs (signValid0.res.toState s) := by
  rcases h with ⟨h7,h16,h21⟩
  simp only [GateRegs, Result.toState_getReg, signValid0.res, rv_simp,
    h7,h16,h21, and_self]

theorem gateRegs_v2 (s : MachineState) (h : GateRegs s) :
    GateRegs (signValid1.res.toState s) := by
  rcases h with ⟨h7,h16,h21⟩
  simp only [GateRegs, Result.toState_getReg, signValid1.res, rv_simp,
    h7,h16,h21, and_self]

theorem gateRegs_v3 (s : MachineState) (h : GateRegs s) :
    GateRegs (signValid2.res.toState s) := by
  rcases h with ⟨h7,h16,h21⟩
  simp only [GateRegs, Result.toState_getReg, signValid2.res, rv_simp,
    h7,h16,h21, and_self]

theorem gateRegs_v4 (s : MachineState) (h : GateRegs s) :
    GateRegs (signValid3.res.toState s) := by
  rcases h with ⟨h7,h16,h21⟩
  simp only [GateRegs, Result.toState_getReg, signValid3.res, rv_simp,
    h7,h16,h21, and_self]

theorem gateRegs_v5 (s : MachineState) (h : GateRegs s) :
    GateRegs (signValid4.res.toState s) := by
  rcases h with ⟨h7,h16,h21⟩
  simp only [GateRegs, Result.toState_getReg, signValid4.res, rv_simp,
    h7,h16,h21, and_self]

theorem from_valid_entry (s : MachineState)
    (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * 2935))
    (h6 : s.getReg .x6 = BitVec.ofNat 64 0x20F0)
    (h7 : s.getReg .x7 = BitVec.ofNat 64 0x3F40)
    (hfirst : (word (Radix27SignLoaded.q s) 0).toNat < 4194304)
    (hnv : ¬ validQ (Radix27SignLoaded.q s)) :
    ∃ k c t, Steps signImage s k c t ∧ k < 100 ∧ c < 100 ∧
      t.pc = BitVec.ofNat 64 (0x1000 + 4 * 2980) ∧ GateRegs t := by
  let u0 := Radix27SignRank.v0 s
  let u1 := Radix27SignRank.v1 s
  let u2 := Radix27SignRank.v2 s
  let u3 := Radix27SignRank.v3 s
  let u4 := Radix27SignRank.v4 s
  let u5 := Radix27SignRank.v5 s
  have st0 : Steps signImage s 12 12 u0 := signFirst_steps s hpc h6
  have hp0 : u0.pc = BitVec.ofNat 64 (0x1000 + 4 * 2948) := by
    change (signFirst.res.toState s).pc = _
    rw [signFirst_pc s h6]
    have hf : (s.getWord32 (BitVec.ofNat 64 0x20F0)).toNat < 4194304 := by
      rw [Radix27SignLoaded.qword0] at hfirst
      simpa only [MachineState.getWord32,
        show alignToDword (8432#64) = 8432#64 by decide,
        show byteOffset (8432#64) / 4 = 0 by decide] using hfirst
    rw [if_pos hf]
  have hr0 : GateRegs u0 := gateRegs_v0 s h7
  by_cases h4 : (highQ (Radix27SignLoaded.q s) 4).toNat < 27
  · have ho1 : signValid0.res.obligs u0 := by simp only [signValid0.res, rv_simp]
    have st1 : Steps signImage u0 signValid0.res.steps signValid0.res.cycles u1 :=
      symRun_sound signValid0 codeAt_signValid0 u0 hp0 ho1
    have hp1 : u1.pc = BitVec.ofNat 64 (0x1000 + 4 * 2950) :=
      Radix27SignTailProbe.valid0_pc u0
        (by rw [Radix27SignHighs.high13_nat s h6]; exact h4) hr0.2.1
    have hr1 : GateRegs u1 := gateRegs_v1 u0 hr0
    by_cases h3 : (highQ (Radix27SignLoaded.q s) 3).toNat < 27
    · have ho2 : signValid1.res.obligs u1 := by simp only [signValid1.res, rv_simp]
      have st2 : Steps signImage u1 signValid1.res.steps signValid1.res.cycles u2 :=
        symRun_sound signValid1 codeAt_signValid1 u1 hp1 ho2
      have hp2 : u2.pc = BitVec.ofNat 64 (0x1000 + 4 * 2953) :=
        Radix27SignTailProbe.valid1_pc u1
          (by rw [Radix27SignHighs.high12_nat s h6]; exact h3) hr1.2.1
      have hr2 : GateRegs u2 := gateRegs_v2 u1 hr1
      by_cases h2 : (highQ (Radix27SignLoaded.q s) 2).toNat < 27
      · have ho3 : signValid2.res.obligs u2 := by simp only [signValid2.res, rv_simp]
        have st3 : Steps signImage u2 signValid2.res.steps signValid2.res.cycles u3 :=
          symRun_sound signValid2 codeAt_signValid2 u2 hp2 ho3
        have hp3 : u3.pc = BitVec.ofNat 64 (0x1000 + 4 * 2957) :=
          Radix27SignTailProbe.valid2_pc u2
            (by rw [Radix27SignHighs.high11_nat s h6]; exact h2) hr2.2.1
        have hr3 : GateRegs u3 := gateRegs_v3 u2 hr2
        by_cases h1 : (highQ (Radix27SignLoaded.q s) 1).toNat < 27
        · have ho4 : signValid3.res.obligs u3 := by simp only [signValid3.res, rv_simp]
          have st4 : Steps signImage u3 signValid3.res.steps signValid3.res.cycles u4 :=
            symRun_sound signValid3 codeAt_signValid3 u3 hp3 ho4
          have hp4 : u4.pc = BitVec.ofNat 64 (0x1000 + 4 * 2961) :=
            Radix27SignTailProbe.valid3_pc u3
              (by rw [Radix27SignHighs.high10_nat s h6]; exact h1) hr3.2.1
          have hr4 : GateRegs u4 := gateRegs_v4 u3 hr3
          by_cases h0 : (highQ (Radix27SignLoaded.q s) 0).toNat < 27
          · exact False.elim (hnv ⟨h0,h1,h2,h3,h4⟩)
          · have ho5 : signValid4.res.obligs u4 := by simp only [signValid4.res, rv_simp]
            have st5 : Steps signImage u4 signValid4.res.steps signValid4.res.cycles u5 :=
              symRun_sound signValid4 codeAt_signValid4 u4 hp4 ho5
            have hp5 : u5.pc = BitVec.ofNat 64 (0x1000 + 4 * 2980) :=
              Radix27SignTailProbe.valid4_fail_pc u4
                (by rw [Radix27SignHighs.high9_nat s h6]; omega) hr4.2.1
            exact ⟨_,_,u5,((((st0.trans st1).trans st2).trans st3).trans st4).trans st5,
              by decide,by decide,hp5,gateRegs_v5 u4 hr4⟩
        · have ho4 : signValid3.res.obligs u3 := by simp only [signValid3.res, rv_simp]
          have st4 : Steps signImage u3 signValid3.res.steps signValid3.res.cycles u4 :=
            symRun_sound signValid3 codeAt_signValid3 u3 hp3 ho4
          have hp4 : u4.pc = BitVec.ofNat 64 (0x1000 + 4 * 2980) :=
            Radix27SignTailProbe.valid3_fail_pc u3
              (by rw [Radix27SignHighs.high10_nat s h6]; omega) hr3.2.1
          exact ⟨_,_,u4,(((st0.trans st1).trans st2).trans st3).trans st4,
            by decide,by decide,hp4,gateRegs_v4 u3 hr3⟩
      · have ho3 : signValid2.res.obligs u2 := by simp only [signValid2.res, rv_simp]
        have st3 : Steps signImage u2 signValid2.res.steps signValid2.res.cycles u3 :=
          symRun_sound signValid2 codeAt_signValid2 u2 hp2 ho3
        have hp3 : u3.pc = BitVec.ofNat 64 (0x1000 + 4 * 2980) :=
          Radix27SignTailProbe.valid2_fail_pc u2
            (by rw [Radix27SignHighs.high11_nat s h6]; omega) hr2.2.1
        exact ⟨_,_,u3,((st0.trans st1).trans st2).trans st3,
          by decide,by decide,hp3,gateRegs_v3 u2 hr2⟩
    · have ho2 : signValid1.res.obligs u1 := by simp only [signValid1.res, rv_simp]
      have st2 : Steps signImage u1 signValid1.res.steps signValid1.res.cycles u2 :=
        symRun_sound signValid1 codeAt_signValid1 u1 hp1 ho2
      have hp2 : u2.pc = BitVec.ofNat 64 (0x1000 + 4 * 2980) :=
        Radix27SignTailProbe.valid1_fail_pc u1
          (by rw [Radix27SignHighs.high12_nat s h6]; omega) hr1.2.1
      exact ⟨_,_,u2,(st0.trans st1).trans st2,
        by decide,by decide,hp2,gateRegs_v2 u1 hr1⟩
  · have ho1 : signValid0.res.obligs u0 := by simp only [signValid0.res, rv_simp]
    have st1 : Steps signImage u0 signValid0.res.steps signValid0.res.cycles u1 :=
      symRun_sound signValid0 codeAt_signValid0 u0 hp0 ho1
    have hp1 : u1.pc = BitVec.ofNat 64 (0x1000 + 4 * 2980) :=
      Radix27SignTailProbe.valid0_fail_pc u0
        (by rw [Radix27SignHighs.high13_nat s h6]; omega) hr0.2.1
    exact ⟨_,_,u1,st0.trans st1,by decide,by decide,hp1,gateRegs_v1 u0 hr0⟩

#print axioms gateRegs_v5
end Radix27SignFallbackPath


end


section -- Radix27SignReservedPath

namespace Radix27SignReservedPath
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv
  SigGolfCandidate.Radix27Images SigGolfCandidate.Rv Radix27

def first (s : MachineState) := signFirst.res.toState s
def second (s : MachineState) := signSecond.res.toState (first s)
def reserved (s : MachineState) := signReserved.res.toState (second s)

theorem first_pc_reserved (s : MachineState)
    (h6 : s.getReg .x6 = BitVec.ofNat 64 0x20F0)
    (hr : reservedMarker (Radix27SignLoaded.q s)) :
    (first s).pc = BitVec.ofNat 64 (0x1000 + 4*2947) := by
  rw [first, signFirst_pc s h6]
  have hf : ¬ (s.getWord32 (BitVec.ofNat 64 0x20F0)).toNat < 4194304 := by
    have h0 := hr.1
    rw [Radix27SignLoaded.qword0] at h0
    simpa only [MachineState.getWord32,
      show alignToDword (8432#64) = 8432#64 by decide,
      show byteOffset (8432#64) / 4 = 0 by decide] using (Nat.not_lt.mpr h0)
  rw [if_neg hf]

theorem first_x19 (s : MachineState) :
    (first s).getReg .x19 = BitVec.ofNat 64 6622613 := by
  simp only [first, Result.toState_getReg, signFirst.res, rv_simp]

theorem second_pc_reserved (s : MachineState)
    (h6 : s.getReg .x6 = BitVec.ofNat 64 0x20F0)
    (hr : reservedMarker (Radix27SignLoaded.q s)) :
    (second s).pc = BitVec.ofNat 64 (0x1000 + 4*2973) := by
  have h9 : ((first s).getReg .x9).toNat < 6622613 := by
    rw [first, Radix27SignLoaded.first_x9 s h6]
    have hn := BitVec.isLt (word (Radix27SignLoaded.q s) 0)
    simp only [BitVec.zeroExtend_eq_setWidth, BitVec.toNat_setWidth]
    rw [Nat.mod_eq_of_lt (by omega : (word (Radix27SignLoaded.q s) 0).toNat < 2^64)]
    exact hr.2
  simp only [second, Result.toState_pc, signSecond.res, rv_simp, first_x19]
  simpa [BitVec.ult_eq_decide] using h9

theorem reserved_steps (s : MachineState)
    (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4*2935))
    (h6 : s.getReg .x6 = BitVec.ofNat 64 0x20F0)
    (h7 : s.getReg .x7 = BitVec.ofNat 64 0x3F40)
    (hr : reservedMarker (Radix27SignLoaded.q s)) :
    Steps signImage s
      (signFirst.res.steps+signSecond.res.steps+signReserved.res.steps)
      (signFirst.res.cycles+signSecond.res.cycles+signReserved.res.cycles)
      (reserved s) ∧
    (reserved s).pc = BitVec.ofNat 64 (0x1000 + 4*2983) := by
  have st0 := signFirst_steps s hpc h6
  have ho1 : signSecond.res.obligs (first s) := by
    simp only [signSecond.res, rv_simp]
  have st1 := symRun_sound signSecond codeAt_signSecond (first s)
    (first_pc_reserved s h6 hr) ho1
  have h7s : (second s).getReg .x7 = BitVec.ofNat 64 0x3F40 := by
    simpa only [second, first, Result.toState_getReg,
      signSecond.res, signFirst.res, rv_simp] using h7
  have ho2 : signReserved.res.obligs (second s) := by
    simp only [signReserved.res, rv_simp, h7s]
    decide
  have st2 := symRun_sound signReserved codeAt_signReserved (second s)
    (second_pc_reserved s h6 hr) ho2
  constructor
  · exact (st0.trans st1).trans st2
  · simp only [reserved, Result.toState_pc, signReserved.res, rv_simp]

#print axioms reserved_steps
end Radix27SignReservedPath


end


section -- Radix27SignUpperPath

namespace Radix27SignUpperPath
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv
  SigGolfCandidate.Radix27Images SigGolfCandidate.Rv Radix27

def w0 (s : MachineState) := Radix27SignReservedPath.second s
def w1 (s : MachineState) := signValid0.res.toState (w0 s)
def w2 (s : MachineState) := signValid1.res.toState (w1 s)
def w3 (s : MachineState) := signValid2.res.toState (w2 s)
def w4 (s : MachineState) := signValid3.res.toState (w3 s)
def w5 (s : MachineState) := signValid4.res.toState (w4 s)

theorem first_pc_upper (s : MachineState)
    (h6 : s.getReg .x6 = BitVec.ofNat 64 0x20F0)
    (hbig : 6622613 ≤ (word (Radix27SignLoaded.q s) 0).toNat) :
    (Radix27SignReservedPath.first s).pc = BitVec.ofNat 64 (0x1000 + 4*2947) := by
  rw [Radix27SignReservedPath.first, signFirst_pc s h6]
  have hf : ¬ (s.getWord32 (BitVec.ofNat 64 0x20F0)).toNat < 4194304 := by
    rw [Radix27SignLoaded.qword0] at hbig
    have hn : 4194304 ≤ (extractWord32 (s.getMem (8432#64)) 0).toNat := by omega
    simpa only [MachineState.getWord32,
      show alignToDword (8432#64) = 8432#64 by decide,
      show byteOffset (8432#64) / 4 = 0 by decide] using (Nat.not_lt.mpr hn)
  rw [if_neg hf]

theorem second_pc_upper (s : MachineState)
    (h6 : s.getReg .x6 = BitVec.ofNat 64 0x20F0)
    (hbig : 6622613 ≤ (word (Radix27SignLoaded.q s) 0).toNat) :
    (w0 s).pc = BitVec.ofNat 64 (0x1000 + 4*2948) := by
  have h9 : 6622613 ≤ ((Radix27SignReservedPath.first s).getReg .x9).toNat := by
    rw [Radix27SignReservedPath.first, Radix27SignLoaded.first_x9 s h6]
    simp only [BitVec.zeroExtend_eq_setWidth, BitVec.toNat_setWidth]
    rw [Nat.mod_eq_of_lt (by have := BitVec.isLt (word (Radix27SignLoaded.q s) 0); omega)]
    exact hbig
  simp only [w0, Radix27SignReservedPath.second, Result.toState_pc,
    signSecond.res, rv_simp, Radix27SignReservedPath.first_x19]
  simpa [BitVec.ult_eq_decide] using h9

theorem gateRegs_w0 (s : MachineState)
    (h7 : s.getReg .x7 = BitVec.ofNat 64 0x3F40) :
    Radix27SignFallbackPath.GateRegs (w0 s) := by
  have hr := Radix27SignFallbackPath.gateRegs_v0 s h7
  have hr' : Radix27SignFallbackPath.GateRegs
      (Radix27SignReservedPath.first s) := hr
  simpa only [Radix27SignFallbackPath.GateRegs, w0,
    Radix27SignReservedPath.second, Result.toState_getReg,
    signSecond.res, rv_simp] using hr'

theorem high9_w4 (s : MachineState)
    (h6 : s.getReg .x6 = BitVec.ofNat 64 0x20F0) :
    (((w4 s).getReg .x9) >>> 16).toNat =
      (highQ (Radix27SignLoaded.q s) 0).toNat := by
  have heq : (w4 s).getReg .x9 =
      (Radix27SignReservedPath.first s).getReg .x9 := by
    simp only [w4,w3,w2,w1,w0,Radix27SignReservedPath.second,
      Result.toState_getReg, signValid3.res,signValid2.res,
      signValid1.res,signValid0.res,signSecond.res,rv_simp]
  rw [heq, Radix27SignReservedPath.first,
    Radix27SignLoaded.first_x9 s h6]
  exact Radix27SignRank.high64_nat _

theorem high0_big (q : BitVec 160)
    (hbig : 6622613 ≤ (word q 0).toNat) :
    27 ≤ (highQ q 0).toNat := by
  have hlo := BitVec.isLt (lowQ q 0)
  have hw := word_high_low q 0
  have hn : (word q 0).toNat =
      (highQ q 0).toNat * 65536 + (lowQ q 0).toNat := by
    rw [← hw, toNat_join16]
  norm_num at hlo
  omega

theorem upper_to_fallback (s : MachineState)
    (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4*2935))
    (h6 : s.getReg .x6 = BitVec.ofNat 64 0x20F0)
    (h7 : s.getReg .x7 = BitVec.ofNat 64 0x3F40)
    (hbig : 6622613 ≤ (word (Radix27SignLoaded.q s) 0).toNat) :
    ∃ k c t, Steps signImage s k c t ∧ k < 100 ∧ c < 100 ∧
      t.pc = BitVec.ofNat 64 (0x1000 + 4*2980) ∧
      Radix27SignFallbackPath.GateRegs t := by
  have stF := signFirst_steps s hpc h6
  have hoS : signSecond.res.obligs (Radix27SignReservedPath.first s) := by
    simp only [signSecond.res, rv_simp]
  have stS := symRun_sound signSecond codeAt_signSecond
    (Radix27SignReservedPath.first s) (first_pc_upper s h6 hbig) hoS
  have st0 : Steps signImage s 13 13 (w0 s) := stF.trans stS
  have hp0 := second_pc_upper s h6 hbig
  have hr0 := gateRegs_w0 s h7
  by_cases h4 : (((w0 s).getReg .x13) >>> 16).toNat < 27
  · have ho1 : signValid0.res.obligs (w0 s) := by simp only [signValid0.res,rv_simp]
    have st1 := symRun_sound signValid0 codeAt_signValid0 (w0 s) hp0 ho1
    have hp1 : (w1 s).pc = BitVec.ofNat 64 (0x1000+4*2950) :=
      Radix27SignTailProbe.valid0_pc (w0 s) h4 hr0.2.1
    have hr1 : Radix27SignFallbackPath.GateRegs (w1 s) :=
      Radix27SignFallbackPath.gateRegs_v1 (w0 s) hr0
    by_cases h3 : (((w1 s).getReg .x12) >>> 16).toNat < 27
    · have ho2 : signValid1.res.obligs (w1 s) := by simp only [signValid1.res,rv_simp]
      have st2 := symRun_sound signValid1 codeAt_signValid1 (w1 s) hp1 ho2
      have hp2 : (w2 s).pc = BitVec.ofNat 64 (0x1000+4*2953) :=
        Radix27SignTailProbe.valid1_pc (w1 s) h3 hr1.2.1
      have hr2 : Radix27SignFallbackPath.GateRegs (w2 s) :=
        Radix27SignFallbackPath.gateRegs_v2 (w1 s) hr1
      by_cases h2 : (((w2 s).getReg .x11) >>> 16).toNat < 27
      · have ho3 : signValid2.res.obligs (w2 s) := by simp only [signValid2.res,rv_simp]
        have st3 := symRun_sound signValid2 codeAt_signValid2 (w2 s) hp2 ho3
        have hp3 : (w3 s).pc = BitVec.ofNat 64 (0x1000+4*2957) :=
          Radix27SignTailProbe.valid2_pc (w2 s) h2 hr2.2.1
        have hr3 : Radix27SignFallbackPath.GateRegs (w3 s) :=
          Radix27SignFallbackPath.gateRegs_v3 (w2 s) hr2
        by_cases h1 : (((w3 s).getReg .x10) >>> 16).toNat < 27
        · have ho4 : signValid3.res.obligs (w3 s) := by simp only [signValid3.res,rv_simp]
          have st4 := symRun_sound signValid3 codeAt_signValid3 (w3 s) hp3 ho4
          have hp4 : (w4 s).pc = BitVec.ofNat 64 (0x1000+4*2961) :=
            Radix27SignTailProbe.valid3_pc (w3 s) h1 hr3.2.1
          have hr4 : Radix27SignFallbackPath.GateRegs (w4 s) :=
            Radix27SignFallbackPath.gateRegs_v4 (w3 s) hr3
          have h0 : 27 ≤ (((w4 s).getReg .x9) >>> 16).toNat := by
            rw [high9_w4 s h6]
            exact high0_big _ hbig
          have ho5 : signValid4.res.obligs (w4 s) := by simp only [signValid4.res,rv_simp]
          have st5 := symRun_sound signValid4 codeAt_signValid4 (w4 s) hp4 ho5
          have hp5 : (w5 s).pc = BitVec.ofNat 64 (0x1000+4*2980) :=
            Radix27SignTailProbe.valid4_fail_pc (w4 s) h0 hr4.2.1
          exact ⟨_,_,w5 s,((((st0.trans st1).trans st2).trans st3).trans st4).trans st5,
            by decide,by decide,hp5,Radix27SignFallbackPath.gateRegs_v5 (w4 s) hr4⟩
        · have ho4 : signValid3.res.obligs (w3 s) := by simp only [signValid3.res,rv_simp]
          have st4 := symRun_sound signValid3 codeAt_signValid3 (w3 s) hp3 ho4
          have hp4 : (w4 s).pc = BitVec.ofNat 64 (0x1000+4*2980) :=
            Radix27SignTailProbe.valid3_fail_pc (w3 s) (by omega) hr3.2.1
          exact ⟨_,_,w4 s,(((st0.trans st1).trans st2).trans st3).trans st4,
            by decide,by decide,hp4,Radix27SignFallbackPath.gateRegs_v4 (w3 s) hr3⟩
      · have ho3 : signValid2.res.obligs (w2 s) := by simp only [signValid2.res,rv_simp]
        have st3 := symRun_sound signValid2 codeAt_signValid2 (w2 s) hp2 ho3
        have hp3 : (w3 s).pc = BitVec.ofNat 64 (0x1000+4*2980) :=
          Radix27SignTailProbe.valid2_fail_pc (w2 s) (by omega) hr2.2.1
        exact ⟨_,_,w3 s,((st0.trans st1).trans st2).trans st3,
          by decide,by decide,hp3,Radix27SignFallbackPath.gateRegs_v3 (w2 s) hr2⟩
    · have ho2 : signValid1.res.obligs (w1 s) := by simp only [signValid1.res,rv_simp]
      have st2 := symRun_sound signValid1 codeAt_signValid1 (w1 s) hp1 ho2
      have hp2 : (w2 s).pc = BitVec.ofNat 64 (0x1000+4*2980) :=
        Radix27SignTailProbe.valid1_fail_pc (w1 s) (by omega) hr1.2.1
      exact ⟨_,_,w2 s,(st0.trans st1).trans st2,
        by decide,by decide,hp2,Radix27SignFallbackPath.gateRegs_v2 (w1 s) hr1⟩
  · have ho1 : signValid0.res.obligs (w0 s) := by simp only [signValid0.res,rv_simp]
    have st1 := symRun_sound signValid0 codeAt_signValid0 (w0 s) hp0 ho1
    have hp1 : (w1 s).pc = BitVec.ofNat 64 (0x1000+4*2980) :=
      Radix27SignTailProbe.valid0_fail_pc (w0 s) (by omega) hr0.2.1
    exact ⟨_,_,w1 s,st0.trans st1,by decide,by decide,hp1,
      Radix27SignFallbackPath.gateRegs_v1 (w0 s) hr0⟩

#print axioms high9_w4
#print axioms upper_to_fallback
end Radix27SignUpperPath


end


section -- Radix27StoreWords

namespace Radix27StoreWords
open RiscvZkvm.Rv64
open Radix27StoreByteTry

local macro "byte_algebra" : tactic =>
  `(tactic| (ext i (hi : i < 8); simp [BitVec.truncate, BitVec.zeroExtend];
             try { interval_cases i <;> simp_all }))

theorem byte_replaceWord32 (w : Word) (v : BitVec 32) {pos j : Nat}
    (hpos : pos < 2) (hj : j < 8) :
    extractByte (replaceWord32 w pos v) j
      = if j = 4 * pos then v.truncate 8
        else if j = 4 * pos + 1 then (v >>> 8).truncate 8
        else if j = 4 * pos + 2 then (v >>> 16).truncate 8
        else if j = 4 * pos + 3 then (v >>> 24).truncate 8
        else extractByte w j := by
  interval_cases pos <;> interval_cases j <;>
    simp only [replaceWord32, extractByte, Nat.reduceMul, Nat.reduceAdd,
      reduceIte, Nat.zero_ne_add_one, Nat.add_one_ne_zero] <;>
    byte_algebra

theorem two_words (m : Word) (a b : BitVec 32) :
    replaceWord32 (replaceWord32 m 0 a) 1 b = b ++ a := by
  apply byte_ext
  intro j hj
  interval_cases j <;>
    (repeat rw [byte_replaceWord32 _ _ (by decide) (by decide)]) <;>
    simp [extractByte, BitVec.truncate, BitVec.setWidth_ushiftRight_eq_extractLsb]
  case «0» =>
    rw [BitVec.setWidth_eq_extractLsb' (by decide)]
    rw [BitVec.setWidth_eq_extractLsb' (by decide)]
    rw [BitVec.extractLsb'_append_eq_of_add_le (by decide)]
  case «1» => rw [BitVec.extractLsb'_append_eq_of_add_le (by decide)]
  case «2» => rw [BitVec.extractLsb'_append_eq_of_add_le (by decide)]
  case «3» => rw [BitVec.extractLsb'_append_eq_of_add_le (by decide)]
  case «4» =>
    rw [BitVec.extractLsb'_append_eq_of_le (by decide)]
    rw [BitVec.setWidth_eq_extractLsb' (by decide)]
  case «5» => rw [BitVec.extractLsb'_append_eq_of_le (by decide)]
  case «6» => rw [BitVec.extractLsb'_append_eq_of_le (by decide)]
  case «7» => rw [BitVec.extractLsb'_append_eq_of_le (by decide)]

#print axioms two_words
end Radix27StoreWords


end


section -- Radix27SignReservedOutput

namespace Radix27SignReservedOutput
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv
  SigGolfCandidate.Radix27Images SigGolfCandidate.Rv Radix27

theorem reserved_x14 (s : MachineState)
    (h6 : s.getReg .x6 = BitVec.ofNat 64 0x20F0) :
    (Radix27SignReservedPath.reserved s).getReg .x14 =
      ((word (Radix27SignLoaded.q s) 0).zeroExtend 64 - 4194304#64) + 14348907#64 := by
  simp only [Radix27SignReservedPath.reserved, Radix27SignReservedPath.second,
    Radix27SignReservedPath.first, Result.toState_getReg,
    signReserved.res, signSecond.res, signFirst.res, rv_simp, h6]
  rw [Radix27SignLoaded.qword0]

theorem reserved_x17 (s : MachineState)
    (h6 : s.getReg .x6 = BitVec.ofNat 64 0x20F0) :
    (Radix27SignReservedPath.reserved s).getReg .x17 =
      (word (Radix27SignLoaded.q s) 3).zeroExtend 64 <<< 48 >>> 48 := by
  simp only [Radix27SignReservedPath.reserved, Radix27SignReservedPath.second,
    Radix27SignReservedPath.first, Result.toState_getReg,
    signReserved.res, signSecond.res, signFirst.res, rv_simp, h6]
  rw [Radix27SignLoaded.qword3]
  rw [show (8432#64) + (8#64) = 8440#64 by decide]
  simp only [Nat.reduceDiv, BitVec.toNat_ofNat]

theorem reserved_low64 (s : MachineState)
    (h6 : s.getReg .x6 = BitVec.ofNat 64 0x20F0)
    (h7 : s.getReg .x7 = BitVec.ofNat 64 0x3F40) :
    (Radix27SignReservedPath.reserved s).getMem (BitVec.ofNat 64 0x3F40) =
      word (Radix27SignLoaded.q s) 2 ++ word (Radix27SignLoaded.q s) 1 := by
  simp only [Radix27SignReservedPath.reserved, Radix27SignReservedPath.second,
    Radix27SignReservedPath.first, Result.toState_getMem,
    Result.toState_getReg, signReserved.res, signSecond.res,
    signFirst.res, rv_simp, h6, h7]
  rw [show (8432#64) + (8#64) = 8440#64 by decide]
  rw [Radix27StoreWords.two_words]
  rw [Radix27SignLoaded.qword1, Radix27SignLoaded.qword2]
  simp only [ite_true, Nat.reduceDiv, BitVec.truncate_eq_setWidth]
  simp

theorem reserved_rank_nat (s : MachineState)
    (h6 : s.getReg .x6 = BitVec.ofNat 64 0x20F0)
    (hr : reservedMarker (Radix27SignLoaded.q s)) :
    ((Radix27SignReservedPath.reserved s).getReg .x14).toNat =
      (word (Radix27SignLoaded.q s) 0).toNat - 4194304 + 14348907 := by
  let w := word (Radix27SignLoaded.q s) 0
  have hext : (w.zeroExtend 64).toNat = w.toNat := by
    simp only [BitVec.zeroExtend_eq_setWidth, BitVec.toNat_setWidth]
    exact Nat.mod_eq_of_lt (by have := BitVec.isLt w; omega)
  have hle : (4194304#64) ≤ w.zeroExtend 64 := by
    rw [BitVec.le_def, hext]
    simpa only [BitVec.toNat_ofNat] using hr.1
  have hsub : (w.zeroExtend 64 - 4194304#64).toNat = w.toNat - 4194304 := by
    rw [BitVec.toNat_sub_of_le hle, hext, BitVec.toNat_ofNat]
  have hadd : (w.zeroExtend 64 - 4194304#64).toNat + (14348907#64).toNat < 2^64 := by
    rw [hsub, BitVec.toNat_ofNat]
    omega
  rw [reserved_x14 s h6, BitVec.toNat_add_of_lt hadd, hsub]
  rfl

theorem reserved_rank24 (s : MachineState)
    (h6 : s.getReg .x6 = BitVec.ofNat 64 0x20F0)
    (hr : reservedMarker (Radix27SignLoaded.q s)) :
    ((Radix27SignReservedPath.reserved s).getReg .x14).truncate 24 =
      BitVec.ofNat 24
        ((word (Radix27SignLoaded.q s) 0).toNat - 4194304 + 14348907) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [reserved_rank_nat s h6 hr]

theorem reserved_x17_low (s : MachineState)
    (h6 : s.getReg .x6 = BitVec.ofNat 64 0x20F0) :
    ((Radix27SignReservedPath.reserved s).getReg .x17).truncate 16 =
      (word (Radix27SignLoaded.q s) 3).extractLsb' 0 16 := by
  rw [reserved_x17 s h6]
  bv_normalize

theorem reserved_x17_lt (s : MachineState)
    (h6 : s.getReg .x6 = BitVec.ofNat 64 0x20F0) :
    ((Radix27SignReservedPath.reserved s).getReg .x17).toNat < 65536 := by
  rw [reserved_x17 s h6]
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft]
  omega

theorem reserved_tailData (s : MachineState)
    (h6 : s.getReg .x6 = BitVec.ofNat 64 0x20F0)
    (h7 : s.getReg .x7 = BitVec.ofNat 64 0x3F40)
    (hr : reservedMarker (Radix27SignLoaded.q s)) :
    Radix27SignTrailer.tailData (Radix27SignReservedPath.reserved s) =
      pack13 (Radix27SignLoaded.q s) := by
  rw [Radix27SignTrailer.tailData, reserved_rank24 s h6 hr,
    reserved_x17_low s h6, reserved_low64 s h6 h7]
  rw [pack13, if_pos hr]
  unfold reservedLows
  simp only [BitVec.append_assoc, BitVec.extractLsb'_append_extractLsb', BitVec.cast_eq]

theorem reserved_h7 (s : MachineState)
    (h7 : s.getReg .x7 = BitVec.ofNat 64 0x3F40) :
    (Radix27SignReservedPath.reserved s).getReg .x7 = BitVec.ofNat 64 0x3F40 := by
  simpa only [Radix27SignReservedPath.reserved, Radix27SignReservedPath.second,
    Radix27SignReservedPath.first, Result.toState_getReg,
    signReserved.res, signSecond.res, signFirst.res, rv_simp] using h7

theorem reserved_tail_steps (s : MachineState)
    (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4*2935))
    (h6 : s.getReg .x6 = BitVec.ofNat 64 0x20F0)
    (h7 : s.getReg .x7 = BitVec.ofNat 64 0x3F40)
    (hr : reservedMarker (Radix27SignLoaded.q s)) :
    ∃ k c u, Steps signImage s k c u ∧ k < 120 ∧ c < 120 ∧
      fetch signImage u = some (.base .ECALL) ∧
      u.getReg .x5 = 1 ∧ u.getReg .x10 = 0 ∧
      readBuffer u 0x3F40 13 = pack13 (Radix27SignLoaded.q s) := by
  obtain ⟨hs, hp⟩ := Radix27SignReservedPath.reserved_steps s hpc h6 h7 hr
  let v := Radix27SignReservedPath.reserved s
  let u := signTrailer.res.toState v
  have hv7 : v.getReg .x7 = BitVec.ofNat 64 0x3F40 := reserved_h7 s h7
  obtain ⟨ht, hf, h5, h10⟩ := Radix27SignTrailer.trailer_steps v hp hv7
  have hout : readBuffer u 0x3F40 13 = pack13 (Radix27SignLoaded.q s) := by
    rw [Radix27SignTrailer.trailer_output v hv7 (reserved_x17_lt s h6)]
    exact reserved_tailData s h6 h7 hr
  exact ⟨_,_,u,hs.trans ht,by decide,by decide,hf,h5,h10,hout⟩

#print axioms reserved_x14
#print axioms reserved_low64
#print axioms reserved_tailData
#print axioms reserved_tail_steps
end Radix27SignReservedOutput


end


section -- Radix27SignAll

namespace Radix27SignAll
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv
  SigGolfCandidate.Radix27Images SigGolfCandidate.Rv Radix27

theorem invalid_to_fallback (s : MachineState)
    (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4*2935))
    (h6 : s.getReg .x6 = BitVec.ofNat 64 0x20F0)
    (h7 : s.getReg .x7 = BitVec.ofNat 64 0x3F40)
    (hr : ¬ reservedMarker (Radix27SignLoaded.q s))
    (hv : ¬ validQ (Radix27SignLoaded.q s)) :
    ∃ k c t, Steps signImage s k c t ∧ k < 100 ∧ c < 100 ∧
      t.pc = BitVec.ofNat 64 (0x1000 + 4*2980) ∧
      Radix27SignFallbackPath.GateRegs t := by
  by_cases hlo : (word (Radix27SignLoaded.q s) 0).toNat < 4194304
  · exact Radix27SignFallbackPath.from_valid_entry s hpc h6 h7 hlo hv
  · have hbig : 6622613 ≤ (word (Radix27SignLoaded.q s) 0).toNat := by
      unfold reservedMarker at hr
      omega
    exact Radix27SignUpperPath.upper_to_fallback s hpc h6 h7 hbig

theorem sign_tail_all (s : MachineState)
    (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4*2935))
    (h6 : s.getReg .x6 = BitVec.ofNat 64 0x20F0)
    (h7 : s.getReg .x7 = BitVec.ofNat 64 0x3F40) :
    ∃ k c u, Steps signImage s k c u ∧ k < 120 ∧ c < 120 ∧
      fetch signImage u = some (.base .ECALL) ∧
      u.getReg .x5 = 1 ∧ u.getReg .x10 = 0 ∧
      readBuffer u 0x3F40 13 = pack13 (Radix27SignLoaded.q s) := by
  by_cases hr : reservedMarker (Radix27SignLoaded.q s)
  · exact Radix27SignReservedOutput.reserved_tail_steps s hpc h6 h7 hr
  by_cases hv : validQ (Radix27SignLoaded.q s)
  · exact Radix27SignTailValid.valid_tail_steps s hpc h6 h7 hv
  obtain ⟨k,c,t,ht,hk,hc,hpcT,hregs⟩ := invalid_to_fallback s hpc h6 h7 hr hv
  obtain ⟨k2,c2,u,h2,hk2,hc2,hf,h5,h10,hout⟩ :=
    Radix27SignFallback.fallback_tail_steps t hpcT hregs.1 hregs.2.2
  refine ⟨k+k2,c+c2,u,ht.trans h2,by omega,by omega,hf,h5,h10,?_⟩
  rw [pack13_unrepresentable _ hr hv]
  exact hout

#print axioms invalid_to_fallback
#print axioms sign_tail_all
end Radix27SignAll


end


section -- Radix27SignPrelude

namespace Radix27SignPrelude
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv
  SigGolfCandidate.Radix27Images SigGolfCandidate.Rv
  SigGolfCandidate.Mem SigGolfCandidate.Packed

abbrev image := Radix27SignPrefix.image

theorem codeAt_counter : CodeAt image
    (BitVec.ofNat 64 (0x1000 + 4*2931))
    SigGolfCandidate.Packed.Images.signCounterPrelude :=
  codeAt_layout Radix27SignPrefix.code_eq Radix27SignPrefix.layout_ok
    (i := 25) (by kernel_rfl) (by decide)

sym_block runCounter := symRun {}
  SigGolfCandidate.Packed.Images.signCounterPrelude
  (BitVec.ofNat 64 (0x1000 + 4*2931)) 10

def after (s : MachineState) := runCounter.res.toState s

theorem steps (s : MachineState)
    (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4*2931)) :
    Steps image s runCounter.res.steps runCounter.res.cycles (after s) := by
  have ho : runCounter.res.obligs s := by
    simp only [runCounter.res, rv_simp]
  exact symRun_sound runCounter codeAt_counter s hpc ho

theorem pc (s : MachineState) :
    (after s).pc = BitVec.ofNat 64 (0x1000 + 4*2935) := by
  simp only [after, Result.toState_pc, runCounter.res, rv_simp]

theorem x6 (s : MachineState) :
    (after s).getReg .x6 = BitVec.ofNat 64 0x20F0 := by
  simp only [after, Result.toState_getReg, runCounter.res, rv_simp]

theorem x7 (s : MachineState) :
    (after s).getReg .x7 = BitVec.ofNat 64 0x3F40 := by
  simp only [after, Result.toState_getReg, runCounter.res, rv_simp]

theorem mem (s : MachineState) (a : Word) :
    (after s).getMem a = s.getMem a := by
  simp only [after, Result.toState_getMem, runCounter.res, rv_simp]

theorem byte (s : MachineState) (a : Word) :
    (after s).getByte a = s.getByte a := by
  simp only [MachineState.getByte, mem]

theorem buffer (s : MachineState) (a n : Nat) :
    readBuffer (after s) a n = readBuffer s a n := by
  apply readBuffer_eq_of_bytes
  intro i hi
  rw [readBuffer_byte s a n i hi]
  exact byte s (BitVec.ofNat 64 (a+i))

theorem sourceCounters (s : MachineState) :
    SigGolfCandidate.Packed.SignRun.sourceCounters (after s) =
      SigGolfCandidate.Packed.SignRun.sourceCounters s := by
  rw [SigGolfCandidate.Packed.SignRun.sourceCounters_readBuffer,
    SigGolfCandidate.Packed.SignRun.sourceCounters_readBuffer, buffer]

#print axioms steps
#print axioms buffer
end Radix27SignPrelude


end


section -- Radix27SignPreTail

namespace Radix27SignPreTail
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv
  SigGolfCandidate.Radix27Images SigGolfCandidate.Rv SigGolfCandidate.Mem
  SigGolfCandidate.Packed Radix27

theorem body_of_copy (u0 u1 : MachineState)
    (hb : SigGolfCandidate.Expand.BytesEq u1
      (SigGolfCandidate.Expand.applyCopy (0x800, 0x2650, 1596)
        (fun a => u0.getByte (BitVec.ofNat 64 a)))) :
    readBuffer u1 0x2650 6384 =
      (readBuffer u0 0x800 6404).extractLsb' 0 bodyBits13 := by
  apply readBuffer_eq_of_bytes
  intro i hi
  rw [hb _ (by omega)]
  have hhit : 0x2650 ≤ 0x2650 + i ∧ 0x2650 + i < 0x2650 + 4*1596 := by omega
  simp only [SigGolfCandidate.Expand.applyCopy, if_pos hhit]
  have heq : 0x2650 + i - 0x2650 + 0x800 = 0x800+i := by omega
  rw [heq, ← readBuffer_byte u0 0x800 6404 i (by omega)]
  exact (SigGolfCandidate.Packed.witnessBody_byte _ i hi).symm

theorem short_body (w : Bytes 6404) :
    body13 (shrinkWitnessAny13 w) = w.extractLsb' 0 bodyBits13 := by
  simp only [body13, shrinkWitnessAny13, BitVec.extractLsb'_append_eq_right]

theorem short_trailer (w : Bytes 6404) :
    trailer13 (shrinkWitnessAny13 w) =
      pack13 (w.extractLsb' bodyBits13 160) := by
  simp only [trailer13, shrinkWitnessAny13, BitVec.extractLsb'_append_eq_left]

theorem pre_tail (s : MachineState)
    (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4*2800)) :
    ∃ k c t, Steps Radix27SignPrefix.image s k c t ∧
      k < 19300 ∧ c < 19300 ∧
      t.pc = BitVec.ofNat 64 (0x1000+4*2935) ∧
      t.getReg .x6 = BitVec.ofNat 64 0x20F0 ∧
      t.getReg .x7 = BitVec.ofNat 64 0x3F40 ∧
      readBuffer t 0x2650 6384 =
        body13 (packOldAny13 (readBuffer s 0x2650 6404)) ∧
      Radix27SignLoaded.q t =
        (SigGolfCandidate.Ref.expandRef (readBuffer s 0x2650 6404)).extractLsb' bodyBits13 160 := by
  obtain ⟨u0, st0, pc0, b0⟩ := Radix27SignPrefix.permute_steps s hpc
  obtain ⟨u1, st1, pc1, b1⟩ := Radix27SignPrefix.body_stage u0 pc0 _ b0
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
  let t := Radix27SignPrelude.after u1
  have st2 := Radix27SignPrelude.steps u1 pc1
  have hw : readBuffer u0 0x800 6404 =
      SigGolfCandidate.Ref.expandRef (readBuffer s 0x2650 6404) :=
    Radix27SignPrefix.permute_readBuffer s u0 b0
  have hbody : readBuffer t 0x2650 6384 =
      body13 (packOldAny13 (readBuffer s 0x2650 6404)) := by
    rw [Radix27SignPrelude.buffer, body_of_copy u0 u1 hb,
      hw, packOldAny13, short_body]
  have hq : Radix27SignLoaded.q t =
      (SigGolfCandidate.Ref.expandRef (readBuffer s 0x2650 6404)).extractLsb' bodyBits13 160 := by
    rw [Radix27SignLoaded.q, Radix27SignPrelude.sourceCounters,
      SigGolfCandidate.Packed.SignRun.sourceCounters_of_body u0 u1 hb, hw]
  exact ⟨_,_,t,(st0.trans st1).trans st2,by decide,by decide,
    Radix27SignPrelude.pc u1,Radix27SignPrelude.x6 u1,
    Radix27SignPrelude.x7 u1,hbody,hq⟩

#print axioms body_of_copy
#print axioms pre_tail
end Radix27SignPreTail


end


section -- Radix27SignBodyJoin

namespace Radix27SignBodyJoin
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Packed
  SigGolfCandidate.Mem Radix27

theorem join_output (s : MachineState) (packed : Bytes 6397)
    (hbody : readBuffer s 0x2650 6384 = body13 packed)
    (htrailer : readBuffer s 0x3F40 13 = trailer13 packed) :
    readBuffer s 0x2650 6397 = packed := by
  apply readBuffer_eq_of_bytes
  intro i hi
  by_cases hlow : i < 6384
  · rw [← readBuffer_byte s 0x2650 6384 i hlow, hbody,
      Radix27ByteCodec.body13_byte packed i hlow]
  · have hj : i - 6384 < 13 := by omega
    have ha : 0x2650 + i = 0x3F40 + (i - 6384) := by omega
    rw [ha, ← readBuffer_byte s 0x3F40 13 (i - 6384) hj, htrailer,
      Radix27ByteCodec.trailer13_byte packed (i - 6384) hj]
    have hh : 6384 + (i - 6384) = i := by omega
    rw [hh]

#print axioms join_output
end Radix27SignBodyJoin


end


section -- Radix27BodyFrame

namespace Radix27BodyFrame
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Packed
  SigGolfCandidate.Packed.Sign SigGolfCandidate.Rv

theorem body_byte {s t : MachineState}
    (hf : Frame s t (fun a => 0x3F40 ≤ a))
    (j : Nat) (hj : j < 6384) :
    t.getByte (BitVec.ofNat 64 (0x2650 + j)) =
      s.getByte (BitVec.ofNat 64 (0x2650 + j)) := by
  let a := alignToDword (BitVec.ofNat 64 (0x2650 + j))
  have ha : a.toNat < 0x3F40 := by
    dsimp [a]
    rw [alignToDword_toNat, BitVec.toNat_ofNat]
    omega
  have hm := hf a.toNat (BitVec.isLt a) (by omega)
  rw [BitVec.ofNat_toNat] at hm
  simp only [MachineState.getByte]
  exact congrArg (fun w => extractByte w (byteOffset (BitVec.ofNat 64 (0x2650 + j)))) hm

theorem body_buffer {s t : MachineState}
    (hf : Frame s t (fun a => 0x3F40 ≤ a)) :
    readBuffer t 0x2650 6384 = readBuffer s 0x2650 6384 := by
  apply readBuffer_eq_of_bytes
  intro j hj
  rw [readBuffer_byte s 0x2650 6384 j hj]
  exact body_byte hf j hj

#print axioms body_buffer
end Radix27BodyFrame


end


section -- Radix27TailFrame

namespace Radix27TailFrame
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv
  SigGolfCandidate.Radix27Images SigGolfCandidate.Rv SigGolfCandidate.Packed.Sign
  Radix27

private abbrev W : Nat → Prop := fun a => 0x3F40 ≤ a

private theorem addr_ne (a d : Nat) (ha : a < 2 ^ 64)
    (hW : ¬ W a) (hd : 0x3F40 ≤ d) (hd' : d < 2 ^ 64) :
    BitVec.ofNat 64 a ≠ BitVec.ofNat 64 d := by
  intro he
  have heq := congrArg BitVec.toNat he
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
    Nat.mod_eq_of_lt hd'] at heq
  exact hW (by change 0x3F40 ≤ a; omega)

theorem first_frame (s : MachineState) :
    Frame s (signFirst.res.toState s) W := by
  intro a ha hW
  simp only [Result.toState_getMem, signFirst.res, rv_simp]

theorem second_frame (s : MachineState) :
    Frame s (signSecond.res.toState s) W := by
  intro a ha hW
  simp only [Result.toState_getMem, signSecond.res, rv_simp]

theorem valid0_frame (s : MachineState) :
    Frame s (signValid0.res.toState s) W := by
  intro a ha hW
  simp only [Result.toState_getMem, signValid0.res, rv_simp]

theorem valid1_frame (s : MachineState) :
    Frame s (signValid1.res.toState s) W := by
  intro a ha hW
  simp only [Result.toState_getMem, signValid1.res, rv_simp]

theorem valid2_frame (s : MachineState) :
    Frame s (signValid2.res.toState s) W := by
  intro a ha hW
  simp only [Result.toState_getMem, signValid2.res, rv_simp]

theorem valid3_frame (s : MachineState) :
    Frame s (signValid3.res.toState s) W := by
  intro a ha hW
  simp only [Result.toState_getMem, signValid3.res, rv_simp]

theorem valid4_frame (s : MachineState) :
    Frame s (signValid4.res.toState s) W := by
  intro a ha hW
  simp only [Result.toState_getMem, signValid4.res, rv_simp]

theorem validEnd_frame (s : MachineState)
    (h7 : s.getReg .x7 = BitVec.ofNat 64 0x3F40) :
    Frame s (signValidEnd.res.toState s) W := by
  intro a ha hW
  simp only [Result.toState_getMem, signValidEnd.res, rv_simp, h7]
  simp only [if_neg (addr_ne a 0x3F40 ha hW (by decide) (by decide))]

theorem reserved_frame (s : MachineState)
    (h7 : s.getReg .x7 = BitVec.ofNat 64 0x3F40) :
    Frame s (signReserved.res.toState s) W := by
  intro a ha hW
  simp only [Result.toState_getMem, signReserved.res, rv_simp, h7]
  simp only [if_neg (addr_ne a 0x3F40 ha hW (by decide) (by decide))]

theorem fallback_frame (s : MachineState)
    (h7 : s.getReg .x7 = BitVec.ofNat 64 0x3F40) :
    Frame s (signFallback.res.toState s) W := by
  intro a ha hW
  simp only [Result.toState_getMem, signFallback.res, rv_simp, h7]
  simp only [if_neg (addr_ne a 0x3F40 ha hW (by decide) (by decide))]

theorem trailer_frame (s : MachineState)
    (h7 : s.getReg .x7 = BitVec.ofNat 64 0x3F40) :
    Frame s (signTrailer.res.toState s) W := by
  intro a ha hW
  simp only [Result.toState_getMem, signTrailer.res, rv_simp, h7]
  have he : (16192#64 + 8#64) = BitVec.ofNat 64 0x3F48 := by decide
  rw [he]
  simp only [if_neg (addr_ne a 0x3F48 ha hW (by decide) (by decide))]

private theorem frame_trans {s t u : MachineState}
    (h₁ : Frame s t W) (h₂ : Frame t u W) : Frame s u W :=
  (h₁.trans h₂).mono (by intro a h; rcases h with h|h <;> exact h)

theorem frame_v0 (s : MachineState) :
    Frame s (Radix27SignRank.v0 s) W := first_frame s
theorem frame_v1 (s : MachineState) :
    Frame s (Radix27SignRank.v1 s) W :=
  frame_trans (frame_v0 s) (valid0_frame _)
theorem frame_v2 (s : MachineState) :
    Frame s (Radix27SignRank.v2 s) W :=
  frame_trans (frame_v1 s) (valid1_frame _)
theorem frame_v3 (s : MachineState) :
    Frame s (Radix27SignRank.v3 s) W :=
  frame_trans (frame_v2 s) (valid2_frame _)
theorem frame_v4 (s : MachineState) :
    Frame s (Radix27SignRank.v4 s) W :=
  frame_trans (frame_v3 s) (valid3_frame _)
theorem frame_v5 (s : MachineState) :
    Frame s (Radix27SignRank.v5 s) W :=
  frame_trans (frame_v4 s) (valid4_frame _)

theorem frame_w0 (s : MachineState) :
    Frame s (Radix27SignUpperPath.w0 s) W :=
  frame_trans (first_frame s) (second_frame _)
theorem frame_w1 (s : MachineState) :
    Frame s (Radix27SignUpperPath.w1 s) W :=
  frame_trans (frame_w0 s) (valid0_frame _)
theorem frame_w2 (s : MachineState) :
    Frame s (Radix27SignUpperPath.w2 s) W :=
  frame_trans (frame_w1 s) (valid1_frame _)
theorem frame_w3 (s : MachineState) :
    Frame s (Radix27SignUpperPath.w3 s) W :=
  frame_trans (frame_w2 s) (valid2_frame _)
theorem frame_w4 (s : MachineState) :
    Frame s (Radix27SignUpperPath.w4 s) W :=
  frame_trans (frame_w3 s) (valid3_frame _)
theorem frame_w5 (s : MachineState) :
    Frame s (Radix27SignUpperPath.w5 s) W :=
  frame_trans (frame_w4 s) (valid4_frame _)

theorem frame_valid_final (s : MachineState)
    (h7 : s.getReg .x7 = BitVec.ofNat 64 0x3F40) :
    Frame s (signTrailer.res.toState (Radix27SignRank.v6 s)) W := by
  have h7v5 : (Radix27SignRank.v5 s).getReg .x7 = BitVec.ofNat 64 0x3F40 := by
    simpa only [Radix27SignRank.v5, Radix27SignRank.v4,
      Radix27SignRank.v3, Radix27SignRank.v2,
      Radix27SignRank.v1, Radix27SignRank.v0,
      Result.toState_getReg, signValid4.res, signValid3.res,
      signValid2.res, signValid1.res, signValid0.res,
      signFirst.res, rv_simp] using h7
  exact frame_trans
    (frame_trans (frame_v5 s) (validEnd_frame _ h7v5))
    (trailer_frame _ (Radix27SignTailValid.valid_h7_v6 s h7))

theorem frame_reserved_final (s : MachineState)
    (h7 : s.getReg .x7 = BitVec.ofNat 64 0x3F40) :
    Frame s (signTrailer.res.toState (Radix27SignReservedPath.reserved s)) W := by
  have h7second : (Radix27SignReservedPath.second s).getReg .x7 =
      BitVec.ofNat 64 0x3F40 := by
    simpa only [Radix27SignReservedPath.second,
      Radix27SignReservedPath.first, Result.toState_getReg,
      signSecond.res, signFirst.res, rv_simp] using h7
  exact frame_trans
    (frame_trans (frame_w0 s) (reserved_frame _ h7second))
    (trailer_frame _ (Radix27SignReservedOutput.reserved_h7 s h7))

#print axioms first_frame
end Radix27TailFrame


end


section -- Radix27FallbackFrame

namespace Radix27FallbackFrame
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv
  SigGolfCandidate.Radix27Images SigGolfCandidate.Rv Radix27
open Radix27SignFallbackPath Radix27SignUpperPath

theorem from_valid_entry_frame (s : MachineState)
    (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * 2935))
    (h6 : s.getReg .x6 = BitVec.ofNat 64 0x20F0)
    (h7 : s.getReg .x7 = BitVec.ofNat 64 0x3F40)
    (hfirst : (word (Radix27SignLoaded.q s) 0).toNat < 4194304)
    (hnv : ¬ validQ (Radix27SignLoaded.q s)) :
    ∃ k c t, Steps signImage s k c t ∧ k < 100 ∧ c < 100 ∧
      t.pc = BitVec.ofNat 64 (0x1000 + 4 * 2980) ∧ GateRegs t ∧
      SigGolfCandidate.Packed.Sign.Frame s t (fun a => 0x3F40 ≤ a) := by
  let u0 := Radix27SignRank.v0 s
  let u1 := Radix27SignRank.v1 s
  let u2 := Radix27SignRank.v2 s
  let u3 := Radix27SignRank.v3 s
  let u4 := Radix27SignRank.v4 s
  let u5 := Radix27SignRank.v5 s
  have st0 : Steps signImage s 12 12 u0 := signFirst_steps s hpc h6
  have hp0 : u0.pc = BitVec.ofNat 64 (0x1000 + 4 * 2948) := by
    change (signFirst.res.toState s).pc = _
    rw [signFirst_pc s h6]
    have hf : (s.getWord32 (BitVec.ofNat 64 0x20F0)).toNat < 4194304 := by
      rw [Radix27SignLoaded.qword0] at hfirst
      simpa only [MachineState.getWord32,
        show alignToDword (8432#64) = 8432#64 by decide,
        show byteOffset (8432#64) / 4 = 0 by decide] using hfirst
    rw [if_pos hf]
  have hr0 : GateRegs u0 := gateRegs_v0 s h7
  by_cases h4 : (highQ (Radix27SignLoaded.q s) 4).toNat < 27
  · have ho1 : signValid0.res.obligs u0 := by simp only [signValid0.res, rv_simp]
    have st1 : Steps signImage u0 signValid0.res.steps signValid0.res.cycles u1 :=
      symRun_sound signValid0 codeAt_signValid0 u0 hp0 ho1
    have hp1 : u1.pc = BitVec.ofNat 64 (0x1000 + 4 * 2950) :=
      Radix27SignTailProbe.valid0_pc u0
        (by rw [Radix27SignHighs.high13_nat s h6]; exact h4) hr0.2.1
    have hr1 : GateRegs u1 := gateRegs_v1 u0 hr0
    by_cases h3 : (highQ (Radix27SignLoaded.q s) 3).toNat < 27
    · have ho2 : signValid1.res.obligs u1 := by simp only [signValid1.res, rv_simp]
      have st2 : Steps signImage u1 signValid1.res.steps signValid1.res.cycles u2 :=
        symRun_sound signValid1 codeAt_signValid1 u1 hp1 ho2
      have hp2 : u2.pc = BitVec.ofNat 64 (0x1000 + 4 * 2953) :=
        Radix27SignTailProbe.valid1_pc u1
          (by rw [Radix27SignHighs.high12_nat s h6]; exact h3) hr1.2.1
      have hr2 : GateRegs u2 := gateRegs_v2 u1 hr1
      by_cases h2 : (highQ (Radix27SignLoaded.q s) 2).toNat < 27
      · have ho3 : signValid2.res.obligs u2 := by simp only [signValid2.res, rv_simp]
        have st3 : Steps signImage u2 signValid2.res.steps signValid2.res.cycles u3 :=
          symRun_sound signValid2 codeAt_signValid2 u2 hp2 ho3
        have hp3 : u3.pc = BitVec.ofNat 64 (0x1000 + 4 * 2957) :=
          Radix27SignTailProbe.valid2_pc u2
            (by rw [Radix27SignHighs.high11_nat s h6]; exact h2) hr2.2.1
        have hr3 : GateRegs u3 := gateRegs_v3 u2 hr2
        by_cases h1 : (highQ (Radix27SignLoaded.q s) 1).toNat < 27
        · have ho4 : signValid3.res.obligs u3 := by simp only [signValid3.res, rv_simp]
          have st4 : Steps signImage u3 signValid3.res.steps signValid3.res.cycles u4 :=
            symRun_sound signValid3 codeAt_signValid3 u3 hp3 ho4
          have hp4 : u4.pc = BitVec.ofNat 64 (0x1000 + 4 * 2961) :=
            Radix27SignTailProbe.valid3_pc u3
              (by rw [Radix27SignHighs.high10_nat s h6]; exact h1) hr3.2.1
          have hr4 : GateRegs u4 := gateRegs_v4 u3 hr3
          by_cases h0 : (highQ (Radix27SignLoaded.q s) 0).toNat < 27
          · exact False.elim (hnv ⟨h0,h1,h2,h3,h4⟩)
          · have ho5 : signValid4.res.obligs u4 := by simp only [signValid4.res, rv_simp]
            have st5 : Steps signImage u4 signValid4.res.steps signValid4.res.cycles u5 :=
              symRun_sound signValid4 codeAt_signValid4 u4 hp4 ho5
            have hp5 : u5.pc = BitVec.ofNat 64 (0x1000 + 4 * 2980) :=
              Radix27SignTailProbe.valid4_fail_pc u4
                (by rw [Radix27SignHighs.high9_nat s h6]; omega) hr4.2.1
            exact ⟨_,_,u5,((((st0.trans st1).trans st2).trans st3).trans st4).trans st5,
              by decide,by decide,hp5,gateRegs_v5 u4 hr4, Radix27TailFrame.frame_v5 s⟩
        · have ho4 : signValid3.res.obligs u3 := by simp only [signValid3.res, rv_simp]
          have st4 : Steps signImage u3 signValid3.res.steps signValid3.res.cycles u4 :=
            symRun_sound signValid3 codeAt_signValid3 u3 hp3 ho4
          have hp4 : u4.pc = BitVec.ofNat 64 (0x1000 + 4 * 2980) :=
            Radix27SignTailProbe.valid3_fail_pc u3
              (by rw [Radix27SignHighs.high10_nat s h6]; omega) hr3.2.1
          exact ⟨_,_,u4,(((st0.trans st1).trans st2).trans st3).trans st4,
            by decide,by decide,hp4,gateRegs_v4 u3 hr3, Radix27TailFrame.frame_v4 s⟩
      · have ho3 : signValid2.res.obligs u2 := by simp only [signValid2.res, rv_simp]
        have st3 : Steps signImage u2 signValid2.res.steps signValid2.res.cycles u3 :=
          symRun_sound signValid2 codeAt_signValid2 u2 hp2 ho3
        have hp3 : u3.pc = BitVec.ofNat 64 (0x1000 + 4 * 2980) :=
          Radix27SignTailProbe.valid2_fail_pc u2
            (by rw [Radix27SignHighs.high11_nat s h6]; omega) hr2.2.1
        exact ⟨_,_,u3,((st0.trans st1).trans st2).trans st3,
          by decide,by decide,hp3,gateRegs_v3 u2 hr2, Radix27TailFrame.frame_v3 s⟩
    · have ho2 : signValid1.res.obligs u1 := by simp only [signValid1.res, rv_simp]
      have st2 : Steps signImage u1 signValid1.res.steps signValid1.res.cycles u2 :=
        symRun_sound signValid1 codeAt_signValid1 u1 hp1 ho2
      have hp2 : u2.pc = BitVec.ofNat 64 (0x1000 + 4 * 2980) :=
        Radix27SignTailProbe.valid1_fail_pc u1
          (by rw [Radix27SignHighs.high12_nat s h6]; omega) hr1.2.1
      exact ⟨_,_,u2,(st0.trans st1).trans st2,
        by decide,by decide,hp2,gateRegs_v2 u1 hr1, Radix27TailFrame.frame_v2 s⟩
  · have ho1 : signValid0.res.obligs u0 := by simp only [signValid0.res, rv_simp]
    have st1 : Steps signImage u0 signValid0.res.steps signValid0.res.cycles u1 :=
      symRun_sound signValid0 codeAt_signValid0 u0 hp0 ho1
    have hp1 : u1.pc = BitVec.ofNat 64 (0x1000 + 4 * 2980) :=
      Radix27SignTailProbe.valid0_fail_pc u0
        (by rw [Radix27SignHighs.high13_nat s h6]; omega) hr0.2.1
    exact ⟨_,_,u1,st0.trans st1,by decide,by decide,hp1,gateRegs_v1 u0 hr0, Radix27TailFrame.frame_v1 s⟩


theorem upper_to_fallback_frame (s : MachineState)
    (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4*2935))
    (h6 : s.getReg .x6 = BitVec.ofNat 64 0x20F0)
    (h7 : s.getReg .x7 = BitVec.ofNat 64 0x3F40)
    (hbig : 6622613 ≤ (word (Radix27SignLoaded.q s) 0).toNat) :
    ∃ k c t, Steps signImage s k c t ∧ k < 100 ∧ c < 100 ∧
      t.pc = BitVec.ofNat 64 (0x1000 + 4*2980) ∧
      Radix27SignFallbackPath.GateRegs t ∧
      SigGolfCandidate.Packed.Sign.Frame s t (fun a => 0x3F40 ≤ a) := by
  have stF := signFirst_steps s hpc h6
  have hoS : signSecond.res.obligs (Radix27SignReservedPath.first s) := by
    simp only [signSecond.res, rv_simp]
  have stS := symRun_sound signSecond codeAt_signSecond
    (Radix27SignReservedPath.first s) (first_pc_upper s h6 hbig) hoS
  have st0 : Steps signImage s 13 13 (w0 s) := stF.trans stS
  have hp0 := second_pc_upper s h6 hbig
  have hr0 := gateRegs_w0 s h7
  by_cases h4 : (((w0 s).getReg .x13) >>> 16).toNat < 27
  · have ho1 : signValid0.res.obligs (w0 s) := by simp only [signValid0.res,rv_simp]
    have st1 := symRun_sound signValid0 codeAt_signValid0 (w0 s) hp0 ho1
    have hp1 : (w1 s).pc = BitVec.ofNat 64 (0x1000+4*2950) :=
      Radix27SignTailProbe.valid0_pc (w0 s) h4 hr0.2.1
    have hr1 : Radix27SignFallbackPath.GateRegs (w1 s) :=
      Radix27SignFallbackPath.gateRegs_v1 (w0 s) hr0
    by_cases h3 : (((w1 s).getReg .x12) >>> 16).toNat < 27
    · have ho2 : signValid1.res.obligs (w1 s) := by simp only [signValid1.res,rv_simp]
      have st2 := symRun_sound signValid1 codeAt_signValid1 (w1 s) hp1 ho2
      have hp2 : (w2 s).pc = BitVec.ofNat 64 (0x1000+4*2953) :=
        Radix27SignTailProbe.valid1_pc (w1 s) h3 hr1.2.1
      have hr2 : Radix27SignFallbackPath.GateRegs (w2 s) :=
        Radix27SignFallbackPath.gateRegs_v2 (w1 s) hr1
      by_cases h2 : (((w2 s).getReg .x11) >>> 16).toNat < 27
      · have ho3 : signValid2.res.obligs (w2 s) := by simp only [signValid2.res,rv_simp]
        have st3 := symRun_sound signValid2 codeAt_signValid2 (w2 s) hp2 ho3
        have hp3 : (w3 s).pc = BitVec.ofNat 64 (0x1000+4*2957) :=
          Radix27SignTailProbe.valid2_pc (w2 s) h2 hr2.2.1
        have hr3 : Radix27SignFallbackPath.GateRegs (w3 s) :=
          Radix27SignFallbackPath.gateRegs_v3 (w2 s) hr2
        by_cases h1 : (((w3 s).getReg .x10) >>> 16).toNat < 27
        · have ho4 : signValid3.res.obligs (w3 s) := by simp only [signValid3.res,rv_simp]
          have st4 := symRun_sound signValid3 codeAt_signValid3 (w3 s) hp3 ho4
          have hp4 : (w4 s).pc = BitVec.ofNat 64 (0x1000+4*2961) :=
            Radix27SignTailProbe.valid3_pc (w3 s) h1 hr3.2.1
          have hr4 : Radix27SignFallbackPath.GateRegs (w4 s) :=
            Radix27SignFallbackPath.gateRegs_v4 (w3 s) hr3
          have h0 : 27 ≤ (((w4 s).getReg .x9) >>> 16).toNat := by
            rw [high9_w4 s h6]
            exact high0_big _ hbig
          have ho5 : signValid4.res.obligs (w4 s) := by simp only [signValid4.res,rv_simp]
          have st5 := symRun_sound signValid4 codeAt_signValid4 (w4 s) hp4 ho5
          have hp5 : (w5 s).pc = BitVec.ofNat 64 (0x1000+4*2980) :=
            Radix27SignTailProbe.valid4_fail_pc (w4 s) h0 hr4.2.1
          exact ⟨_,_,w5 s,((((st0.trans st1).trans st2).trans st3).trans st4).trans st5,
            by decide,by decide,hp5,Radix27SignFallbackPath.gateRegs_v5 (w4 s) hr4, Radix27TailFrame.frame_w5 s⟩
        · have ho4 : signValid3.res.obligs (w3 s) := by simp only [signValid3.res,rv_simp]
          have st4 := symRun_sound signValid3 codeAt_signValid3 (w3 s) hp3 ho4
          have hp4 : (w4 s).pc = BitVec.ofNat 64 (0x1000+4*2980) :=
            Radix27SignTailProbe.valid3_fail_pc (w3 s) (by omega) hr3.2.1
          exact ⟨_,_,w4 s,(((st0.trans st1).trans st2).trans st3).trans st4,
            by decide,by decide,hp4,Radix27SignFallbackPath.gateRegs_v4 (w3 s) hr3, Radix27TailFrame.frame_w4 s⟩
      · have ho3 : signValid2.res.obligs (w2 s) := by simp only [signValid2.res,rv_simp]
        have st3 := symRun_sound signValid2 codeAt_signValid2 (w2 s) hp2 ho3
        have hp3 : (w3 s).pc = BitVec.ofNat 64 (0x1000+4*2980) :=
          Radix27SignTailProbe.valid2_fail_pc (w2 s) (by omega) hr2.2.1
        exact ⟨_,_,w3 s,((st0.trans st1).trans st2).trans st3,
          by decide,by decide,hp3,Radix27SignFallbackPath.gateRegs_v3 (w2 s) hr2, Radix27TailFrame.frame_w3 s⟩
    · have ho2 : signValid1.res.obligs (w1 s) := by simp only [signValid1.res,rv_simp]
      have st2 := symRun_sound signValid1 codeAt_signValid1 (w1 s) hp1 ho2
      have hp2 : (w2 s).pc = BitVec.ofNat 64 (0x1000+4*2980) :=
        Radix27SignTailProbe.valid1_fail_pc (w1 s) (by omega) hr1.2.1
      exact ⟨_,_,w2 s,(st0.trans st1).trans st2,
        by decide,by decide,hp2,Radix27SignFallbackPath.gateRegs_v2 (w1 s) hr1, Radix27TailFrame.frame_w2 s⟩
  · have ho1 : signValid0.res.obligs (w0 s) := by simp only [signValid0.res,rv_simp]
    have st1 := symRun_sound signValid0 codeAt_signValid0 (w0 s) hp0 ho1
    have hp1 : (w1 s).pc = BitVec.ofNat 64 (0x1000+4*2980) :=
      Radix27SignTailProbe.valid0_fail_pc (w0 s) (by omega) hr0.2.1
    exact ⟨_,_,w1 s,st0.trans st1,by decide,by decide,hp1,
      Radix27SignFallbackPath.gateRegs_v1 (w0 s) hr0, Radix27TailFrame.frame_w1 s⟩


#print axioms from_valid_entry_frame
#print axioms upper_to_fallback_frame
end Radix27FallbackFrame


end


section -- Radix27TailFrameAll

namespace Radix27TailFrameAll
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv
  SigGolfCandidate.Radix27Images SigGolfCandidate.Rv Radix27
open SigGolfCandidate.Packed.Sign

private abbrev W : Nat → Prop := fun a => 0x3F40 ≤ a

private theorem frame_trans {s t u : MachineState}
    (h₁ : Frame s t W) (h₂ : Frame t u W) : Frame s u W :=
  (h₁.trans h₂).mono (by intro a h; rcases h with h|h <;> exact h)

theorem valid_tail_frame (s : MachineState)
    (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4*2935))
    (h6 : s.getReg .x6 = BitVec.ofNat 64 0x20F0)
    (h7 : s.getReg .x7 = BitVec.ofNat 64 0x3F40)
    (hv : validQ (Radix27SignLoaded.q s)) :
    ∃ k c u, Steps signImage s k c u ∧ k < 120 ∧ c < 120 ∧
      fetch signImage u = some (.base .ECALL) ∧
      u.getReg .x5 = 1 ∧ u.getReg .x10 = 0 ∧
      readBuffer u 0x3F40 13 = pack13 (Radix27SignLoaded.q s) ∧
      Frame s u W := by
  obtain ⟨k, c, hs, hk, hc, hpc6⟩ :=
    Radix27SignValidSteps.valid_path s hpc h6 h7 hv
  let v := Radix27SignRank.v6 s
  let u := signTrailer.res.toState v
  obtain ⟨ht, hf, h5, h10⟩ :=
    Radix27SignTrailer.trailer_steps v hpc6
      (Radix27SignTailValid.valid_h7_v6 s h7)
  have hout : readBuffer u 0x3F40 13 = pack13 (Radix27SignLoaded.q s) := by
    rw [Radix27SignTrailer.trailer_output v
      (Radix27SignTailValid.valid_h7_v6 s h7)
      (Radix27SignValidOutput.valid_x17_lt s h6)]
    exact Radix27SignValidOutput.valid_tailData s h6 h7 hv
  refine ⟨_, _, u, hs.trans ht, ?_, ?_, hf, h5, h10, hout, ?_⟩
  · have hst : signTrailer.res.steps < 20 := by decide
    omega
  · have hct : signTrailer.res.cycles < 20 := by decide
    omega
  · exact Radix27TailFrame.frame_valid_final s h7

theorem reserved_tail_frame (s : MachineState)
    (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4*2935))
    (h6 : s.getReg .x6 = BitVec.ofNat 64 0x20F0)
    (h7 : s.getReg .x7 = BitVec.ofNat 64 0x3F40)
    (hr : reservedMarker (Radix27SignLoaded.q s)) :
    ∃ k c u, Steps signImage s k c u ∧ k < 120 ∧ c < 120 ∧
      fetch signImage u = some (.base .ECALL) ∧
      u.getReg .x5 = 1 ∧ u.getReg .x10 = 0 ∧
      readBuffer u 0x3F40 13 = pack13 (Radix27SignLoaded.q s) ∧
      Frame s u W := by
  obtain ⟨hs, hp⟩ := Radix27SignReservedPath.reserved_steps s hpc h6 h7 hr
  let v := Radix27SignReservedPath.reserved s
  let u := signTrailer.res.toState v
  have hv7 : v.getReg .x7 = BitVec.ofNat 64 0x3F40 :=
    Radix27SignReservedOutput.reserved_h7 s h7
  obtain ⟨ht, hf, h5, h10⟩ :=
    Radix27SignTrailer.trailer_steps v hp hv7
  have hout : readBuffer u 0x3F40 13 = pack13 (Radix27SignLoaded.q s) := by
    rw [Radix27SignTrailer.trailer_output v hv7
      (Radix27SignReservedOutput.reserved_x17_lt s h6)]
    exact Radix27SignReservedOutput.reserved_tailData s h6 h7 hr
  exact ⟨_,_,u,hs.trans ht,by decide,by decide,hf,h5,h10,hout,
    Radix27TailFrame.frame_reserved_final s h7⟩

theorem fallback_tail_frame (t : MachineState)
    (hpc : t.pc = BitVec.ofNat 64 (0x1000 + 4 * 2980))
    (h7 : t.getReg .x7 = BitVec.ofNat 64 0x3F40)
    (h21 : t.getReg .x21 = BitVec.ofNat 64 14348907) :
    ∃ k c u, Steps signImage t k c u ∧ k < 20 ∧ c < 20 ∧
      fetch signImage u = some (.base .ECALL) ∧
      u.getReg .x5 = 1 ∧ u.getReg .x10 = 0 ∧
      readBuffer u 0x3F40 13 = fallback13 ∧
      Frame t u W := by
  obtain ⟨hs, hp⟩ := Radix27SignFallback.fallback_steps t hpc h7
  let v := Radix27SignFallback.fb t
  let u := signTrailer.res.toState v
  have hv7 : v.getReg .x7 = BitVec.ofNat 64 0x3F40 := by
    rw [Radix27SignFallback.fallback_h7, h7]
  obtain ⟨ht, hf, h5, h10⟩ :=
    Radix27SignTrailer.trailer_steps v hp hv7
  have hout : readBuffer u 0x3F40 13 = fallback13 := by
    rw [Radix27SignTrailer.trailer_output v hv7]
    · exact Radix27SignFallback.fallback_tailData t h7 h21
    · rw [Radix27SignFallback.fallback_x17]; decide
  refine ⟨_,_,u,hs.trans ht,by decide,by decide,hf,h5,h10,hout,?_⟩
  exact frame_trans (Radix27TailFrame.fallback_frame t h7)
    (Radix27TailFrame.trailer_frame v hv7)

theorem invalid_to_fallback_frame (s : MachineState)
    (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4*2935))
    (h6 : s.getReg .x6 = BitVec.ofNat 64 0x20F0)
    (h7 : s.getReg .x7 = BitVec.ofNat 64 0x3F40)
    (hr : ¬ reservedMarker (Radix27SignLoaded.q s))
    (hv : ¬ validQ (Radix27SignLoaded.q s)) :
    ∃ k c t, Steps signImage s k c t ∧ k < 100 ∧ c < 100 ∧
      t.pc = BitVec.ofNat 64 (0x1000 + 4*2980) ∧
      Radix27SignFallbackPath.GateRegs t ∧ Frame s t W := by
  by_cases hlo : (word (Radix27SignLoaded.q s) 0).toNat < 4194304
  · exact Radix27FallbackFrame.from_valid_entry_frame s hpc h6 h7 hlo hv
  · have hbig : 6622613 ≤ (word (Radix27SignLoaded.q s) 0).toNat := by
      unfold reservedMarker at hr
      omega
    exact Radix27FallbackFrame.upper_to_fallback_frame s hpc h6 h7 hbig

theorem sign_tail_all_frame (s : MachineState)
    (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4*2935))
    (h6 : s.getReg .x6 = BitVec.ofNat 64 0x20F0)
    (h7 : s.getReg .x7 = BitVec.ofNat 64 0x3F40) :
    ∃ k c u, Steps signImage s k c u ∧ k < 120 ∧ c < 120 ∧
      fetch signImage u = some (.base .ECALL) ∧
      u.getReg .x5 = 1 ∧ u.getReg .x10 = 0 ∧
      readBuffer u 0x3F40 13 = pack13 (Radix27SignLoaded.q s) ∧
      Frame s u W := by
  by_cases hr : reservedMarker (Radix27SignLoaded.q s)
  · exact reserved_tail_frame s hpc h6 h7 hr
  by_cases hv : validQ (Radix27SignLoaded.q s)
  · exact valid_tail_frame s hpc h6 h7 hv
  obtain ⟨k,c,t,ht,hk,hc,hpcT,hregs,hfr⟩ :=
    invalid_to_fallback_frame s hpc h6 h7 hr hv
  obtain ⟨k2,c2,u,h2,hk2,hc2,hf,h5,h10,hout,hfr2⟩ :=
    fallback_tail_frame t hpcT hregs.1 hregs.2.2
  refine ⟨k+k2,c+c2,u,ht.trans h2,by omega,by omega,hf,h5,h10,?_,?_⟩
  · rw [pack13_unrepresentable _ hr hv]
    exact hout
  · exact frame_trans hfr hfr2

theorem sign_tail_all_body (s : MachineState)
    (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4*2935))
    (h6 : s.getReg .x6 = BitVec.ofNat 64 0x20F0)
    (h7 : s.getReg .x7 = BitVec.ofNat 64 0x3F40) :
    ∃ k c u, Steps signImage s k c u ∧ k < 120 ∧ c < 120 ∧
      fetch signImage u = some (.base .ECALL) ∧
      u.getReg .x5 = 1 ∧ u.getReg .x10 = 0 ∧
      readBuffer u 0x3F40 13 = pack13 (Radix27SignLoaded.q s) ∧
      readBuffer u 0x2650 6384 = readBuffer s 0x2650 6384 := by
  obtain ⟨k,c,u,hs,hk,hc,hf,h5,h10,hout,hframe⟩ :=
    sign_tail_all_frame s hpc h6 h7
  exact ⟨k,c,u,hs,hk,hc,hf,h5,h10,hout,
    Radix27BodyFrame.body_buffer hframe⟩

#print axioms sign_tail_all_frame
#print axioms sign_tail_all_body
end Radix27TailFrameAll


end


section -- Radix27SignSuffix

namespace Radix27SignSuffix
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv
  SigGolfCandidate.Radix27Images SigGolfCandidate.Rv SigGolfCandidate.Mem
  SigGolfCandidate.Packed Radix27

def TailComplete : Prop :=
  ∀ (t : MachineState)
    (hpc : t.pc = BitVec.ofNat 64 (0x1000 + 4*2935))
    (h6 : t.getReg .x6 = BitVec.ofNat 64 0x20F0)
    (h7 : t.getReg .x7 = BitVec.ofNat 64 0x3F40),
    ∃ k c u, Steps Radix27SignPrefix.image t k c u ∧
      k < 120 ∧ c < 120 ∧
      fetch Radix27SignPrefix.image u = some (.base .ECALL) ∧
      u.getReg .x5 = 1 ∧ u.getReg .x10 = 0 ∧
      readBuffer u 0x2650 6384 = readBuffer t 0x2650 6384 ∧
      readBuffer u 0x3F40 13 = pack13 (Radix27SignLoaded.q t)

theorem sign_suffix_output (hTail : TailComplete) (s : MachineState)
    (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4*2800)) :
    ∃ k c u, Steps Radix27SignPrefix.image s k c u ∧
      k < 19420 ∧ c < 19420 ∧
      fetch Radix27SignPrefix.image u = some (.base .ECALL) ∧
      u.getReg .x5 = 1 ∧ u.getReg .x10 = 0 ∧
      readBuffer u 0x2650 6397 =
        packOldAny13 (readBuffer s 0x2650 6404) := by
  obtain ⟨k0,c0,t,st0,hk0,hc0,hpt,h6,h7,hbody,hq⟩ :=
    Radix27SignPreTail.pre_tail s hpc
  obtain ⟨k1,c1,u,st1,hk1,hc1,hf,h5,h10,hbu,htu⟩ := hTail t hpt h6 h7
  have hbody' : readBuffer u 0x2650 6384 =
      body13 (packOldAny13 (readBuffer s 0x2650 6404)) := by
    rw [hbu, hbody]
  have htrail' : readBuffer u 0x3F40 13 =
      trailer13 (packOldAny13 (readBuffer s 0x2650 6404)) := by
    rw [htu, hq, packOldAny13, Radix27SignPreTail.short_trailer]
  exact ⟨k0+k1,c0+c1,u,st0.trans st1,by omega,by omega,hf,h5,h10,
    Radix27SignBodyJoin.join_output u _ hbody' htrail'⟩

theorem tailComplete : TailComplete := by
  intro t hpc h6 h7
  obtain ⟨k,c,u,hs,hk,hc,hf,h5,h10,hout,hbody⟩ :=
    Radix27TailFrameAll.sign_tail_all_body t hpc h6 h7
  exact ⟨k,c,u,hs,hk,hc,hf,h5,h10,hbody,hout⟩

theorem sign_suffix_output_concrete (s : MachineState)
    (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4*2800)) :
    ∃ k c u, Steps Radix27SignPrefix.image s k c u ∧
      k < 19420 ∧ c < 19420 ∧
      fetch Radix27SignPrefix.image u = some (.base .ECALL) ∧
      u.getReg .x5 = 1 ∧ u.getReg .x10 = 0 ∧
      readBuffer u 0x2650 6397 =
        packOldAny13 (readBuffer s 0x2650 6404) :=
  sign_suffix_output tailComplete s hpc

#print axioms sign_suffix_output
#print axioms sign_suffix_output_concrete
end Radix27SignSuffix


end


section -- Radix27SignRefinement

namespace SigGolfCandidate.Radix27Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
  SigGolfCandidate.Rv SigGolfCandidate.Ref SigGolfCandidate.Mem OracleComp
  Radix27

set_option maxRecDepth 100000

private theorem terminal (hTail : Radix27SignSuffix.TailComplete)
    (a : Option (Bytes 6404)) (t : MachineState)
    (h : SignPost a t) :
    ∃ e : Execution,
      (∀ fuel, 19421 ≤ fuel → Riscv.execute fuel image t = Pure.pure e) ∧
      (toRunResult submission .sign e).value = a.map packOldAny13 ∧
      e.hashCalls = 0 ∧ e.hashCompressions = 0 ∧
      e.exit ≠ .unfinished ∧ e.cycles ≤ 19421 := by
  obtain ⟨_, h5, ha, hsuccess, hfailure⟩ := h
  by_cases h10 : t.getReg .x10 = 0
  · have hpc := hsuccess h10
    obtain ⟨k,c,u,hs,hk,hc,hf,hu5,hu10,huout⟩ :=
      Radix27SignSuffix.sign_suffix_output hTail t (by simpa [pcOf] using hpc)
    refine ⟨⟨.success,u,c+1,0,0⟩, ?_, ?_, rfl, rfl, by simp, by simp; omega⟩
    · intro fuel hL
      rw [hs.execute_le (by omega)]
      obtain ⟨n,hn⟩ : ∃ n, fuel-k=n+1 := ⟨fuel-k-1, by omega⟩
      rw [hn, execute_halt n hf hu5]
      simp [hu10, Execution.charge]
    · have ha' : a = some (readBuffer t 0x2650 6404) := by
        simpa only [if_pos h10] using ha
      have hr : readOutput submission.sizes submission.layout .sign u =
          packOldAny13 (readBuffer t 0x2650 6404) := huout
      simp [toRunResult, ha', hr]
      rfl
  · have hf := hfailure h10
    refine ⟨⟨.failure,t,1,0,0⟩, ?_, ?_, rfl, rfl, by simp, by simp⟩
    · intro fuel hL
      obtain ⟨n,hn⟩ : ∃ n, fuel=n+1 := ⟨fuel-1,by omega⟩
      rw [hn, execute_halt n hf h5]
      simpa only [if_neg h10]
    · have ha' : a = none := by simpa only [if_neg h10] using ha
      simp [toRunResult,ha']
      rfl

theorem signW_post_lt : signW + 19421 < CYCLE_LIMIT := by
  unfold signW restW forsTreeW layCyc topCyc treeCyc tleafCyc CYCLE_LIMIT
  norm_num

theorem sign_refines13 (hTail : Radix27SignSuffix.TailComplete)
    (sk : SecretKey) (cache : Cache) (m : Message) :
    (fun r => (r.value,r.hashCalls,r.hashCompressions)) <$>
      submission.run .sign (sk,cache,m) =
    (fun p => (p.1.map packOldAny13,p.2.1,p.2.2)) <$>
      countBoth (signRef sk cache m) := by
  exact Sim.run_eq_terminal submission .sign (sk,cache,m)
    (initialState_eq sk cache m) (signRef_sim sk cache m) signW_post_lt
    (fun a => a.map packOldAny13) (fun a t h => by
      obtain ⟨e,he,hv,hc,hb,_,_⟩ := terminal hTail a t h
      exact ⟨e,he,hv,hc,hb⟩)

theorem sign_terminates13 (hTail : Radix27SignSuffix.TailComplete)
    (hash : Hash) (sk : SecretKey) (cache : Cache) (m : Message) :
    (submission.runWith hash .sign (sk,cache,m)).finished = true ∧
      (submission.runWith hash .sign (sk,cache,m)).cycles ≤ signW+19421 := by
  exact Sim.runWith_terminal submission .sign (sk,cache,m)
    (initialState_eq sk cache m) (signRef_sim sk cache m) signW_post_lt
    (fun a t h => by
      obtain ⟨e,he,_,_,_,hx,hc⟩ := terminal hTail a t h
      exact ⟨e,he,hx,hc⟩) hash

theorem sign_refines13_concrete (sk : SecretKey) (cache : Cache) (m : Message) :
    (fun r => (r.value,r.hashCalls,r.hashCompressions)) <$>
      submission.run .sign (sk,cache,m) =
    (fun p => (p.1.map packOldAny13,p.2.1,p.2.2)) <$>
      countBoth (signRef sk cache m) :=
  sign_refines13 Radix27SignSuffix.tailComplete sk cache m

theorem sign_terminates13_concrete (hash : Hash)
    (sk : SecretKey) (cache : Cache) (m : Message) :
    (submission.runWith hash .sign (sk,cache,m)).finished = true ∧
      (submission.runWith hash .sign (sk,cache,m)).cycles ≤ signW+19421 :=
  sign_terminates13 Radix27SignSuffix.tailComplete hash sk cache m

#print axioms sign_refines13
#print axioms sign_terminates13
#print axioms sign_refines13_concrete
#print axioms sign_terminates13_concrete
end SigGolfCandidate.Radix27Sign


end


section -- Radix27CompleteCore

namespace Radix27CompleteCore
open SigGolfCandidate SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv
  OracleComp OracleSpec SigGolfCandidate.Radix27
open SigGolfCandidate.Packed.Sign
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000
set_option allowUnsafeReducibility true in
attribute [local reducible] SigGolfCandidate.Legacy.Input SigGolfCandidate.Legacy.Output
  SigGolfCandidate.Final.shortSub13 Radix27Submission.concrete

private abbrev concrete := Radix27Submission.concrete
private abbrev baseLayout : Layout := SigGolfCandidate.submission.layout
private abbrev newImages : Phase → Riscv.Image := concrete.image

def SignRefinement13 : Prop :=
  ∀ (sk : SecretKey) (cache : Cache) (m : Message),
    (fun r => (r.value, r.hashCalls, r.hashCompressions)) <$>
      concrete.run .sign (sk, cache, m) =
    (fun p => (p.1.map packOldAny13, p.2.1, p.2.2)) <$>
      countBoth (Ref.signRef sk cache m)

theorem sign_value (hS : SignRefinement13)
    (sk : SecretKey) (cache : Cache) (m : Message) :
    (fun r => r.value) <$> concrete.run .sign (sk, cache, m) =
      Option.map packOldAny13 <$> Ref.signRef sk cache m := by
  have h := congrArg (fun x => Prod.fst <$> x) (hS sk cache m)
  simp only [Functor.map_map] at h
  calc
    (fun r => r.value) <$> concrete.run .sign (sk, cache, m) =
      (fun p => Option.map packOldAny13 p.1) <$>
        countBoth (Ref.signRef sk cache m) := h
    _ = _ := by
      calc
        (fun p => Option.map packOldAny13 p.1) <$>
            countBoth (Ref.signRef sk cache m) =
          Option.map packOldAny13 <$>
            (Prod.fst <$> countBoth (Ref.signRef sk cache m)) := by
              rw [Functor.map_map]
        _ = _ := by rw [fst_countBoth]

theorem complete_of_phase_refinements
    (hK : ∀ sk : SecretKey,
      (fun r => r.value) <$> concrete.run .keygen sk =
        some <$> Ref.keygenRef sk)
    (hS : SignRefinement13)
    (hV : ∀ (m : Message) (pk : PublicKey) (w : Bytes 6404),
      (fun r => r.value.isSome) <$>
        concrete.run .verify (m, pk, w) = Ref.verifyRef m pk w) :
    concrete.Complete := by
  change (SigGolfCandidate.Final.shortSub13 baseLayout newImages).Complete
  apply SigGolfCandidate.Final.complete13_of_phase_refinements
  · exact hK
  · exact sign_value hS
  · intro m pk σ
    obtain ⟨_, _, he⟩ := Radix27ExpandWrapper.expand_run m pk σ
    change (fun r => r.value) <$> concrete.run .expand (m, pk, σ) = _
    rw [he]
    rfl
  · exact hV

#print axioms complete_of_phase_refinements
end Radix27CompleteCore


end


section -- Radix27SecurityBridge

namespace Radix27SecurityBridge
open SigGolfCandidate SigGolfCandidate.Legacy OracleComp SigGolfCandidate.Radix27
open SigGolfCandidate.Packed (oldSubmission observed)
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
set_option allowUnsafeReducibility true in
attribute [local reducible] SigGolfCandidate.Legacy.Input SigGolfCandidate.Legacy.Output
  SigGolfCandidate.Packed.oldSubmission SigGolfCandidate.Packed.shortSubmission
  SigGolfCandidate.submission Radix27Submission.concrete

private abbrev baseLayout : Layout := SigGolfCandidate.submission.layout
private abbrev oldImages : Phase → Riscv.Image := SigGolfCandidate.submission.image
private abbrev newImages : Phase → Riscv.Image := Radix27Submission.concrete.image
private abbrev concrete := Radix27Submission.concrete

theorem verify_valid :
    ((shortSubmission baseLayout newImages).image .verify).Valid
      (shortSubmission baseLayout newImages).sizes
      (shortSubmission baseLayout newImages).layout := by
  constructor
  · exact SigGolfCandidate.submission_verify_valid.1
  · decide +kernel

theorem initial_verify_eq (message : Message) (pk : PublicKey)
    (witness : Bytes 6404) :
    initialState (shortSubmission baseLayout newImages) .verify
      (message, pk, witness) =
      initialState (oldSubmission baseLayout oldImages) .verify
      (message, pk, witness) := by
  have old_valid :
      ((oldSubmission baseLayout oldImages).image .verify).Valid
        (oldSubmission baseLayout oldImages).sizes
        (oldSubmission baseLayout oldImages).layout := by
    exact SigGolfCandidate.submission_verify_valid
  unfold initialState
  rw [if_pos verify_valid, if_pos old_valid]
  rfl

private theorem runVerifyEq (a b : Submission)
    (x : Input a.sizes .verify) (y : Input b.sizes .verify)
    (hi : initialState a .verify x = initialState b .verify y)
    (hc : a.image .verify = b.image .verify) :
    a.run .verify x = b.run .verify y := by
  unfold Submission.run
  rw [hi, hc]

theorem verify_run_eq (message : Message) (pk : PublicKey)
    (witness : Bytes 6404) :
    (shortSubmission baseLayout newImages).run .verify (message, pk, witness) =
      (oldSubmission baseLayout oldImages).run .verify (message, pk, witness) := by
  apply runVerifyEq
  · exact initial_verify_eq message pk witness
  · change SigGolfCandidate.submission.image .verify =
      SigGolfCandidate.submission.image .verify
    rfl

theorem assumptions_of_sign
    (hS : ∀ (sk : SecretKey) (cache : Bytes CACHE_BYTES) (message : Message),
      (observed <$> (shortSubmission baseLayout newImages).run .sign (sk, cache, message)) =
      ((fun r => (r.value.map packOldAny13, r.hashCalls)) <$>
        (oldSubmission baseLayout oldImages).run .sign (sk, cache, message))) :
    AssumptionsAny baseLayout oldImages newImages where
  keygen sk := by
    rfl
  sign sk cache message := hS sk cache message
  expand message pk signature := by
    change (observed <$> concrete.run .expand (message, pk, signature)) =
      (observed <$> SigGolfCandidate.submission.run .expand
        (message, pk, unpackOld13 signature))
    rw [SigGolfCandidate.Expand.expand_run]
    obtain ⟨_, _, he⟩ := Radix27ExpandWrapper.expand_run message pk signature
    rw [he, expand_unpackOld13]
    rfl
  verify message pk witness := by
    exact congrArg (fun comp => observed <$> comp)
      (verify_run_eq message pk witness)

theorem secure_of_sign
    (hS : ∀ (sk : SecretKey) (cache : Bytes CACHE_BYTES) (message : Message),
      (observed <$> (shortSubmission baseLayout newImages).run .sign (sk, cache, message)) =
      ((fun r => (r.value.map packOldAny13, r.hashCalls)) <$>
        (oldSubmission baseLayout oldImages).run .sign (sk, cache, message))) :
    concrete.Secure := by
  have hOld : (oldSubmission baseLayout oldImages).Secure := by
    change SigGolfCandidate.submission.Secure
    exact SigGolfCandidate.Final.certificate.security
  exact secureAny (assumptions_of_sign hS) hOld

#print axioms secure_of_sign
end Radix27SecurityBridge


end


section -- Radix27BudgetTerm

namespace Radix27BudgetTerm
open SigGolfCandidate SigGolfCandidate.Legacy OracleComp SigGolfCandidate.Radix27
open SigGolfCandidate.Packed (oldSubmission observed)
set_option maxRecDepth 200000
set_option maxHeartbeats 3000000
set_option allowUnsafeReducibility true in
attribute [local reducible] SigGolfCandidate.Legacy.Input SigGolfCandidate.Legacy.Output
  Radix27Submission.concrete

private abbrev concrete := Radix27Submission.concrete
private abbrev baseLayout : Layout := SigGolfCandidate.submission.layout
private abbrev oldImages : Phase → Riscv.Image := SigGolfCandidate.submission.image
private abbrev newImages : Phase → Riscv.Image := concrete.image

theorem keygen_valid :
    ((shortSubmission baseLayout newImages).image .keygen).Valid
      (shortSubmission baseLayout newImages).sizes
      (shortSubmission baseLayout newImages).layout := by
  constructor
  · exact SigGolfCandidate.submission_keygen_valid.1
  · decide +kernel

theorem keygen_run_eq (sk : SecretKey) :
    (shortSubmission baseLayout newImages).run .keygen sk =
      (oldSubmission baseLayout oldImages).run .keygen sk := by
  have old_valid :
      ((oldSubmission baseLayout oldImages).image .keygen).Valid
        (oldSubmission baseLayout oldImages).sizes
        (oldSubmission baseLayout oldImages).layout :=
    SigGolfCandidate.submission_keygen_valid
  have hi : initialState (shortSubmission baseLayout newImages) .keygen sk =
      initialState (oldSubmission baseLayout oldImages) .keygen sk := by
    unfold initialState
    rw [if_pos keygen_valid, if_pos old_valid]
    rfl
  unfold Submission.run
  rw [hi]
  rfl

theorem keygen_runWith_eq (hash : Hash) (sk : SecretKey) :
    concrete.runWith hash .keygen sk =
      SigGolfCandidate.submission.runWith hash .keygen sk := by
  unfold Submission.runWith
  change evalWithAnswerFn hash
    ((shortSubmission baseLayout newImages).run .keygen sk) =
    evalWithAnswerFn hash
    ((oldSubmission baseLayout oldImages).run .keygen sk)
  rw [keygen_run_eq]
  rfl

theorem verify_runWith_eq (hash : Hash) (m : Message) (pk : PublicKey)
    (w : Bytes 6404) :
    concrete.runWith hash .verify (m, pk, w) =
      SigGolfCandidate.submission.runWith hash .verify (m, pk, w) := by
  unfold Submission.runWith
  change evalWithAnswerFn hash
    ((shortSubmission baseLayout newImages).run .verify (m, pk, w)) =
    evalWithAnswerFn hash
    ((oldSubmission baseLayout oldImages).run .verify (m, pk, w))
  rw [Radix27SecurityBridge.verify_run_eq]

theorem keygen_value (sk : SecretKey) :
    (fun r => r.value) <$> concrete.run .keygen sk =
      some <$> Ref.keygenRef sk := by
  change (fun r => r.value) <$>
    (shortSubmission baseLayout newImages).run .keygen sk = _
  rw [keygen_run_eq]
  exact SigGolfCandidate.Final.keygen_value
    SigGolfCandidate.Final.keygenRefinement sk

theorem verify_value (m : Message) (pk : PublicKey) (w : Bytes 6404) :
    (fun r => r.value.isSome) <$> concrete.run .verify (m, pk, w) =
      Ref.verifyRef m pk w := by
  change (fun r => r.value.isSome) <$>
    (shortSubmission baseLayout newImages).run .verify (m, pk, w) = _
  rw [Radix27SecurityBridge.verify_run_eq]
  exact SigGolfCandidate.Final.verify_value
    SigGolfCandidate.Final.verifyRefinement m pk w

theorem budget_of_sign (hS : Radix27CompleteCore.SignRefinement13) :
    concrete.CompressionBounds := by
  apply SigGolfCandidate.Budget.compressionBounds_of_refinement concrete
  · apply SigGolfCandidate.Budget.keygenRefines_of_counts concrete
    intro sk
    refine ⟨some, ?_⟩
    change (fun r => (r.value, r.hashCalls, r.hashCompressions)) <$>
      SigGolfCandidate.submission.run .keygen sk = _
    exact SigGolfCandidate.Final.keygenRefinement sk
  · apply SigGolfCandidate.Budget.signRefines_of_counts concrete rfl
    intro sk cache m
    refine ⟨Option.map packOldAny13, ?_⟩
    exact hS sk cache m
  · apply SigGolfCandidate.Budget.expandNoHash_of_counts concrete
    rintro ⟨m, pk, σ⟩
    refine ⟨Unit, (), fun _ => some (expandWitness13 σ), ?_⟩
    obtain ⟨cyc, _, he⟩ := Radix27ExpandWrapper.expand_run m pk σ
    rw [he]
    rfl

theorem terminates_of_sign
    (hS : ∀ (hash : Hash) (sk : SecretKey) (cache : Cache) (m : Message),
      (concrete.runWith hash .sign (sk, cache, m)).finished = true ∧
        (concrete.runWith hash .sign (sk, cache, m)).cycles < CYCLE_LIMIT) :
    concrete.Terminates := by
  intro hash phase input
  cases phase with
  | keygen =>
      dsimp only
      change (concrete.runWith hash .keygen input).finished = true ∧
        (concrete.runWith hash .keygen input).cycles < CYCLE_LIMIT
      rw [keygen_runWith_eq]
      exact SigGolfCandidate.Final.keygenTermination hash input
  | sign =>
      obtain ⟨sk, cache, m⟩ := input
      exact hS hash sk cache m
  | expand =>
      obtain ⟨m, pk, σ⟩ := input
      dsimp only
      obtain ⟨cyc, hcyc, he⟩ :=
        Radix27ExpandWrapper.expand_runWith hash m pk σ
      rw [he]
      exact ⟨rfl, hcyc⟩
  | verify =>
      obtain ⟨m, pk, w⟩ := input
      dsimp only
      change (concrete.runWith hash .verify (m, pk, w)).finished = true ∧
        (concrete.runWith hash .verify (m, pk, w)).cycles < CYCLE_LIMIT
      rw [verify_runWith_eq]
      exact SigGolfCandidate.Final.verifyTermination hash m pk w

theorem verificationBound : concrete.VerificationBound 11530 := by
  intro hash sk m
  dsimp only
  intro h
  obtain ⟨⟨m', pk, w⟩, hacc, hcyc⟩ :=
    SigGolfCandidate.Final.honest_success_verify concrete hash sk m h
  rw [hcyc]
  have hb := (SigGolfCandidate.Verify.verify_terminates hash (m', pk, w)).2.1
  rw [verify_runWith_eq]
  change (SigGolfCandidate.submission.runWith hash .verify (m', pk, w)).cycles + 26 ≤ 11530
  change (SigGolfCandidate.submission.runWith hash .verify (m', pk, w)).cycles ≤ 11504 at hb
  omega

#print axioms budget_of_sign
#print axioms terminates_of_sign
#print axioms verificationBound
end Radix27BudgetTerm


end


section -- Radix27FinalCert

namespace Radix27FinalCert
open SigGolfCandidate SigGolfCandidate.Legacy OracleComp OracleSpec SigGolfCandidate.Radix27
open SigGolfCandidate.Packed (oldSubmission observed)
open SigGolfCandidate.Packed.Sign
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000
set_option allowUnsafeReducibility true in
attribute [local reducible] SigGolfCandidate.Legacy.Input SigGolfCandidate.Legacy.Output
  Radix27Submission.concrete

private abbrev concrete := Radix27Submission.concrete

theorem admissible : concrete.Admissible := by
  refine ⟨?_, ?_⟩
  · change SigGolfCandidate.Radix27Images.sizes13.Valid
    unfold Sizes.Valid
    decide
  · intro phase
    cases phase with
    | keygen => exact Radix27BudgetTerm.keygen_valid
    | sign => exact SigGolfCandidate.Radix27Images.sign_valid
    | expand => exact SigGolfCandidate.Radix27Images.expand_valid
    | verify => exact Radix27SecurityBridge.verify_valid

theorem sign_observed (hS : Radix27CompleteCore.SignRefinement13)
    (sk : SecretKey) (cache : Cache) (message : Message) :
    (observed <$> concrete.run .sign (sk, cache, message)) =
      ((fun r => (r.value.map packOldAny13, r.hashCalls)) <$>
        SigGolfCandidate.submission.run .sign (sk, cache, message)) := by
  have hs := congrArg (fun X =>
    (fun p : Option (Bytes 6397) × Nat × Nat => (p.1, p.2.1)) <$> X)
      (hS sk cache message)
  have ho := congrArg (fun X =>
    (fun p : Option (Bytes 6404) × Nat × Nat =>
      (p.1.map packOldAny13, p.2.1)) <$> X)
      (SigGolfCandidate.Final.signRefinement sk cache message)
  simp only [Functor.map_map] at hs
  change (observed <$> concrete.run .sign (sk, cache, message)) =
    ((fun r => (r.value.map packOldAny13, r.hashCalls)) <$>
      SigGolfCandidate.submission.run .sign (sk, cache, message))
  calc
    observed <$> concrete.run .sign (sk, cache, message) =
      (fun p => (p.1.map packOldAny13, p.2.1)) <$>
        countBoth (Ref.signRef sk cache message) := by
      change (fun r => (r.value, r.hashCalls)) <$>
        concrete.run .sign (sk, cache, message) = _
      simpa only using hs
    _ = (fun r => (r.value.map packOldAny13, r.hashCalls)) <$>
        SigGolfCandidate.submission.run .sign (sk, cache, message) := by
      calc
        (fun p => (p.1.map packOldAny13, p.2.1)) <$>
            countBoth (Ref.signRef sk cache message) =
          (fun p : Option (Bytes 6404) × Nat × Nat =>
            (p.1.map packOldAny13, p.2.1)) <$>
            ((fun r => (r.value, r.hashCalls, r.hashCompressions)) <$>
              SigGolfCandidate.submission.run .sign (sk, cache, message)) := ho.symm
        _ = _ := by rw [Functor.map_map]

theorem certificate_of_sign
    (hS : Radix27CompleteCore.SignRefinement13)
    (hTerm : ∀ (hash : Hash) (sk : SecretKey) (cache : Cache) (m : Message),
      (concrete.runWith hash .sign (sk, cache, m)).finished = true ∧
        (concrete.runWith hash .sign (sk, cache, m)).cycles < CYCLE_LIMIT) :
    Certificate concrete 11530 where
  admissible := admissible
  termination := Radix27BudgetTerm.terminates_of_sign hTerm
  completeness := Radix27CompleteCore.complete_of_phase_refinements
    Radix27BudgetTerm.keygen_value hS Radix27BudgetTerm.verify_value
  compressionBounds := Radix27BudgetTerm.budget_of_sign hS
  security := Radix27SecurityBridge.secure_of_sign (sign_observed hS)
  verificationBound := Radix27BudgetTerm.verificationBound

#print axioms certificate_of_sign
end Radix27FinalCert


end
