import SigGolfCandidate.Packed.Images
import SigGolfCandidate.Packed.WordCodec
import SigGolfCandidate.Packed.ByteCodec
import SigGolfCandidate.Expand.Mem

/-!
# Packed expansion machine trace

The body uses the generic 1596-word copy-loop theorem. A single straight-line
symbolic block unpacks the fourteen-byte trailer and halts.
-/

namespace SigGolfCandidate.Packed.ExpandRun

open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv
  SigGolfCandidate.Rv SigGolfCandidate.Mem

set_option maxRecDepth 100000

abbrev image : Image := Images.expandImage

def finishCode : List (BitVec 32) :=
  Images.expandCounterPrelude ++ Images.expandCounterUnpack

def L : Rv.Layout :=
  [(0, Images.expandBodyPrelude),
   (5, SigGolfCandidate.Expand.loopCode),
   (11, finishCode)]

theorem layout_ok : layoutOk 0 L = true := by decide +kernel
theorem code_eq : image.code = layoutCode L := by decide +kernel

theorem codeAt_pre :
    CodeAt image (BitVec.ofNat 64 (0x1000 + 4 * 0)) Images.expandBodyPrelude :=
  codeAt_layout code_eq layout_ok (i := 0) (by kernel_rfl) (by decide)

theorem codeAt_loop :
    CodeAt image (BitVec.ofNat 64 (0x1000 + 4 * 5)) SigGolfCandidate.Expand.loopCode :=
  codeAt_layout code_eq layout_ok (i := 1) (by kernel_rfl) (by decide)

theorem codeAt_finish :
    CodeAt image (BitVec.ofNat 64 (0x1000 + 4 * 11)) finishCode :=
  codeAt_layout code_eq layout_ok (i := 2) (by kernel_rfl) (by decide)

sym_block runPre := symRun {} Images.expandBodyPrelude (BitVec.ofNat 64 0x1000) 10
sym_block runFinish := symRun {} finishCode (BitVec.ofNat 64 (0x1000 + 4 * 11)) 100

theorem body_stage (t : MachineState) (htpc : t.pc = 0x1000)
    (f : Nat → Byte) (hf : SigGolfCandidate.Expand.BytesEq t f) :
    ∃ u, Steps image t (runPre.res.steps + 1596 * 6)
        (runPre.res.cycles + 1596 * 6) u ∧
      u.pc = BitVec.ofNat 64 (0x1000 + 4 * 11) ∧
      SigGolfCandidate.Expand.BytesEq u
        (SigGolfCandidate.Expand.applyCopy (0x2650, 0x800, 1596) f) := by
  obtain ⟨u, hsteps, hpc, hmem⟩ :=
    SigGolfCandidate.Expand.stage runPre codeAt_pre rfl rfl rfl rfl rfl rfl
      codeAt_loop (by decide) t htpc f hf
  exact ⟨u, hsteps, by simpa using hpc, hmem⟩

theorem finish_steps (u : MachineState)
    (hpc : u.pc = BitVec.ofNat 64 (0x1000 + 4 * 11)) :
    Steps image u 25 25 (runFinish.res.toState u) ∧
      fetch image (runFinish.res.toState u) = some (.base .ECALL) ∧
      (runFinish.res.toState u).getReg .x5 = 1 ∧
      (runFinish.res.toState u).getReg .x10 = 0 := by
  have ho : runFinish.res.obligs u := by simp only [runFinish.res, rv_simp]
  exact ⟨by simpa only [runFinish.res] using
      (symRun_sound runFinish codeAt_finish u hpc ho),
    symRun_ecall runFinish codeAt_finish u ho rfl,
    by simp only [runFinish.res, rv_simp],
    by simp only [runFinish.res, rv_simp]⟩

def loadedCounters (u : MachineState) : BitVec 160 :=
  unpackCounterWords (u.getMem (BitVec.ofNat 64 0x3F40))
    (u.getMem (BitVec.ofNat 64 0x3F48))

theorem finish_word0 (u : MachineState) :
    (runFinish.res.toState u).getMem (BitVec.ofNat 64 0x20F0) =
      (loadedCounters u).extractLsb' 0 64 := by
  simp only [Result.toState_getMem, runFinish.res, memEval, Addr.eval, E.eval,
    BinOp.eval, StoreKind.merge, replaceWord32, loadedCounters,
    unpackCounterWords]
  simp only [show (8432#64) ≠ (8448#64) by decide,
    show (8432#64) ≠ (8440#64) by decide, if_false]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_and,
    BitVec.getLsbD_or, BitVec.getLsbD_not, BitVec.getLsbD_append,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_ushiftRight]
  interval_cases i <;> simp [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_ofNat, Nat.testBit]


theorem finish_word1 (u : MachineState) :
    (runFinish.res.toState u).getMem (BitVec.ofNat 64 0x20F8) =
      (loadedCounters u).extractLsb' 64 64 := by
  simp only [Result.toState_getMem, runFinish.res, memEval, Addr.eval, E.eval,
    BinOp.eval, StoreKind.merge, replaceWord32, loadedCounters,
    unpackCounterWords]
  simp only [show (8440#64) ≠ (8448#64) by decide,
    show (8440#64) ≠ (8432#64) by decide, if_false]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_and,
    BitVec.getLsbD_or, BitVec.getLsbD_not, BitVec.getLsbD_append,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_ushiftRight]
  interval_cases i <;> simp [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_ofNat, Nat.testBit]


theorem finish_word2 (u : MachineState) :
    ((runFinish.res.toState u).getMem (BitVec.ofNat 64 0x2100)).extractLsb' 0 32 =
      (loadedCounters u).extractLsb' 128 32 := by
  simp only [Result.toState_getMem, runFinish.res, memEval, Addr.eval, E.eval,
    BinOp.eval, StoreKind.merge, replaceWord32, loadedCounters,
    unpackCounterWords]
  simp only [show (8448#64) ≠ (8432#64) by decide,
    show (8448#64) ≠ (8440#64) by decide, if_false]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_and,
    BitVec.getLsbD_or, BitVec.getLsbD_not, BitVec.getLsbD_append,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_ushiftRight]
  interval_cases i <;> simp [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_ofNat, Nat.testBit]


theorem finish_mem_frame (u : MachineState) (a : Word)
    (h0 : a ≠ BitVec.ofNat 64 0x20F0)
    (h1 : a ≠ BitVec.ofNat 64 0x20F8)
    (h2 : a ≠ BitVec.ofNat 64 0x2100) :
    (runFinish.res.toState u).getMem a = u.getMem a := by
  simp only [Result.toState_getMem, runFinish.res, memEval, Addr.eval]
  simp [h0, h1, h2]

theorem finish_body_byte (u : MachineState) (j : Nat) (hj : j < 6384) :
    (runFinish.res.toState u).getByte (BitVec.ofNat 64 (0x800 + j)) =
      u.getByte (BitVec.ofNat 64 (0x800 + j)) := by
  have ha : (alignToDword (BitVec.ofNat 64 (0x800 + j))).toNat < 0x20F0 := by
    rw [alignToDword_toNat, BitVec.toNat_ofNat]
    omega
  have hne (x : Nat) (hx : 0x20F0 ≤ x) (hxb : x < 2 ^ 64) :
      alignToDword (BitVec.ofNat 64 (0x800 + j)) ≠ BitVec.ofNat 64 x := by
    intro h
    rw [h] at ha
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hxb] at ha
    omega
  simp only [MachineState.getByte]
  rw [finish_mem_frame u _ (hne _ (by omega) (by decide))
    (hne _ (by omega) (by decide)) (hne _ (by omega) (by decide))]

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

theorem finish_counter_byte (u : MachineState) (j : Nat) (hj : j < 20) :
    (runFinish.res.toState u).getByte (BitVec.ofNat 64 (0x20F0 + j)) =
      (loadedCounters u).extractLsb' (8 * j) 8 := by
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
  by_cases hj0 : j < 8
  · have hd : j / 8 = 0 := by omega
    have hm : j % 8 = j := by omega
    simp only [hd, hm, Nat.mul_zero, Nat.add_zero]
    rw [finish_word0, byteExtract]
    simpa only [Nat.zero_add] using
      nestedExtract (loadedCounters u) 0 64 (8 * j) 8 (by omega)
  · by_cases hj1 : j < 16
    · have hd : j / 8 = 1 := by omega
      have hm : j % 8 = j - 8 := by omega
      simp only [hd, hm, Nat.mul_one, Nat.reduceAdd]
      rw [finish_word1, byteExtract]
      rw [nestedExtract (loadedCounters u) 64 64 (8 * (j - 8)) 8 (by omega)]
      congr 1
      omega
    · have hd : j / 8 = 2 := by omega
      have hm : j % 8 = j - 16 := by omega
      simp only [hd, hm, Nat.reduceMul, Nat.reduceAdd]
      let x := (runFinish.res.toState u).getMem (BitVec.ofNat 64 0x2100)
      calc
        extractByte x (j - 16) =
            (x.extractLsb' 0 32).extractLsb' (8 * (j - 16)) 8 := by
          rw [byteExtract]
          simpa only [Nat.zero_add] using
            (nestedExtract x 0 32 (8 * (j - 16)) 8 (by omega)).symm
        _ = ((loadedCounters u).extractLsb' 128 32).extractLsb'
            (8 * (j - 16)) 8 := by
          exact congrArg (fun v : BitVec 32 => v.extractLsb' (8 * (j - 16)) 8)
            (finish_word2 u)
        _ = (loadedCounters u).extractLsb' (8 * j) 8 := by
          rw [nestedExtract (loadedCounters u) 128 32 (8 * (j - 16)) 8 (by omega)]
          congr 1
          omega

def packedLoaded (u : MachineState) : BitVec 112 :=
  (u.getMem (BitVec.ofNat 64 0x3F48)).extractLsb' 0 48 ++
  u.getMem (BitVec.ofNat 64 0x3F40)

theorem packedLoaded_byte (u : MachineState) (j : Nat) (hj : j < 14) :
    u.getByte (BitVec.ofNat 64 (0x3F40 + j)) =
      (packedLoaded u).extractLsb' (8 * j) 8 := by
  have ha : alignToDword (BitVec.ofNat 64 (0x3F40 + j)) =
      BitVec.ofNat 64 (0x3F40 + 8 * (j / 8)) := by
    apply BitVec.eq_of_toNat_eq
    rw [alignToDword_toNat]
    simp only [BitVec.toNat_ofNat]
    omega
  have hb : byteOffset (BitVec.ofNat 64 (0x3F40 + j)) = j % 8 := by
    rw [byteOffset_ofNat (by omega)]
    omega
  simp only [MachineState.getByte]
  rw [ha, hb]
  by_cases hj0 : j < 8
  · have hd : j / 8 = 0 := by omega
    have hm : j % 8 = j := by omega
    simp only [hd, hm, Nat.mul_zero, Nat.add_zero]
    rw [byteExtract]
    unfold packedLoaded
    rw [BitVec.extractLsb'_append_eq_of_add_le (by omega : 8 * j + 8 ≤ 64)]
  · have hd : j / 8 = 1 := by omega
    have hm : j % 8 = j - 8 := by omega
    simp only [hd, hm, Nat.mul_one, Nat.reduceAdd]
    rw [byteExtract]
    unfold packedLoaded
    rw [BitVec.extractLsb'_append_eq_of_le (by omega : 64 ≤ 8 * j)]
    rw [nestedExtract (u.getMem (BitVec.ofNat 64 0x3F48)) 0 48
      (8 * j - 64) 8 (by omega)]
    congr 1
    omega

theorem packedLoaded_readBuffer (u : MachineState) :
    packedLoaded u = packedCounters (readBuffer u 0x2650 6398) := by
  calc
    packedLoaded u = readBuffer u 0x3F40 14 := by
      symm
      apply readBuffer_eq_of_bytes
      intro i hi
      rw [packedLoaded_byte u i hi]
      exact (getD_bytes (packedLoaded u) i hi).symm
    _ = packedCounters (readBuffer u 0x2650 6398) := readBuffer_shortCounters u

theorem body_sig_unchanged (u0 u1 : MachineState)
    (hb : SigGolfCandidate.Expand.BytesEq u1
      (SigGolfCandidate.Expand.applyCopy (0x2650, 0x800, 1596)
        (fun a => u0.getByte (BitVec.ofNat 64 a)))) :
    readBuffer u1 0x2650 6398 = readBuffer u0 0x2650 6398 := by
  apply readBuffer_eq_of_bytes
  intro i hi
  rw [hb _ (by omega)]
  have hne : ¬ (0x800 ≤ 0x2650 + i ∧ 0x2650 + i < 0x800 + 4 * 1596) := by omega
  simp only [SigGolfCandidate.Expand.applyCopy, if_neg hne]
  exact (readBuffer_byte u0 0x2650 6398 i hi).symm

theorem loadedCounters_of_body (u0 u1 : MachineState)
    (hb : SigGolfCandidate.Expand.BytesEq u1
      (SigGolfCandidate.Expand.applyCopy (0x2650, 0x800, 1596)
        (fun a => u0.getByte (BitVec.ofNat 64 a)))) :
    loadedCounters u1 = expandCounterBlock
      (packedCounters (readBuffer u0 0x2650 6398)) := by
  rw [loadedCounters, unpackWords_eq_expand, ← packedLoaded,
    packedLoaded_readBuffer, body_sig_unchanged u0 u1 hb]

theorem final_readBuffer (s u1 : MachineState)
    (hb : SigGolfCandidate.Expand.BytesEq u1
      (SigGolfCandidate.Expand.applyCopy (0x2650, 0x800, 1596)
        (fun a => s.getByte (BitVec.ofNat 64 a)))) :
    readBuffer (runFinish.res.toState u1) 0x800 6404 =
      expandWitness (readBuffer s 0x2650 6398) := by
  let sig : Bytes 6398 := readBuffer s 0x2650 6398
  have hc : loadedCounters u1 = expandCounterBlock (packedCounters sig) :=
    loadedCounters_of_body s u1 hb
  change readBuffer (runFinish.res.toState u1) 0x800 6404 = expandWitness sig
  apply readBuffer_eq_of_bytes
  intro i hi
  by_cases hbody : i < 6384
  · rw [finish_body_byte u1 i hbody, hb _ (by omega)]
    have hhit : 0x800 ≤ 0x800 + i ∧ 0x800 + i < 0x800 + 4 * 1596 := by omega
    simp only [SigGolfCandidate.Expand.applyCopy, if_pos hhit]
    have heq : 0x800 + i - 0x800 + 0x2650 = 0x2650 + i := by omega
    rw [heq, ← readBuffer_byte s 0x2650 6398 i (by omega)]
    rw [expandWitness_body_byte sig i hbody, shortBody_byte sig i hbody]
  · have hj : i - 6384 < 20 := by omega
    have heq : 0x800 + i = 0x20F0 + (i - 6384) := by omega
    rw [heq, finish_counter_byte u1 (i - 6384) hj, hc]
    have hi' : 6384 + (i - 6384) = i := by omega
    rw [← hi', expandWitness_counter_byte sig (i - 6384) hj]
    have hidx : 6384 + (i - 6384) - 6384 = i - 6384 := by omega
    rw [hidx]
    exact (getD_bytes (expandCounterBlock (packedCounters sig))
      (i - 6384) hj).symm

theorem expand_steps (s : MachineState) (hpc : s.pc = 0x1000) :
    ∃ u, Steps image s 9606 9606 u ∧
      fetch image u = some (.base .ECALL) ∧
      u.getReg .x5 = 1 ∧ u.getReg .x10 = 0 ∧
      readBuffer u 0x800 6404 = expandWitness (readBuffer s 0x2650 6398) := by
  obtain ⟨u, st1, pc1, hb⟩ := body_stage s hpc _ (fun a _ => rfl)
  obtain ⟨st2, hf, h5, h10⟩ := finish_steps u pc1
  exact ⟨_, Steps.of_eq (st1.trans st2) rfl rfl,
    hf, h5, h10, final_readBuffer s u hb⟩

end SigGolfCandidate.Packed.ExpandRun
