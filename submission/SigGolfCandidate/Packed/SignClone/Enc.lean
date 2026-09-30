import SigGolfCandidate.Packed.SignClone.Inv

/-! ### cloned Digest -/

/-!
# `sign`, phase 1: the digest search (`dig_loop`, instructions 27 .. 45)

`digLoop_sim` : from `dig_loop` with counter `a`, the machine refines `searchDigest S m a (2^20 - a)`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace SigGolfCandidate.Packed.Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

/-- Facts about the buffers used by the digest search (at the start of the loop). -/
structure DigMem (S mm : List Byte) (u : MachineState) : Prop where
  rbS : u.readWords (BitVec.ofNat 64 0x640) 4 = wordsOf S
  rbM : u.readWords (BitVec.ofNat 64 0x660) 4 = wordsOf mm
  rbZ : u.readWords (BitVec.ofNat 64 0x680) 4 = [0, 0, 0, 0]
  rbP : u.readWords (BitVec.ofNat 64 0x628) 3 = [0, 0, 0]
  rb0 : lo32 (u.getMem (BitVec.ofNat 64 0x620)) = BitVec.ofNat 32 0x701
  db0 : u.readWords (BitVec.ofNat 64 0x20) 2 = [twWord0 12 0 0 0, 0]
  dbM : u.readWords (BitVec.ofNat 64 0x40) 4 = wordsOf mm

/-- Addresses written by the digest search. -/
def digW (a : Nat) : Prop := a = 0x620 ∨ (0x30 ≤ a ∧ a < 0x40) ∨ (0x140 ≤ a ∧ a < 0x180)

def digRegs : List Reg := [.x1, .x2, .x3, .x6, .x10, .x11, .x12]

/-- Loop invariant at `dig_loop` with counter `a`. -/
def DigInv (u : MachineState) (a : Nat) (t : MachineState) : Prop :=
  t.pc = pcOf 65 ∧ t.getReg .x6 = BitVec.ofNat 64 a ∧ a < 2 ^ 20 ∧ RegsEq u t digRegs ∧
    Frame u t digW ∧ lo32 (t.getMem (BitVec.ofNat 64 0x620)) = lo32 (u.getMem (BitVec.ofNat 64 0x620))

/-- Result of the digest search. -/
def DigPost (u : MachineState) : Option (Val × Nat) → MachineState → Prop
  | none, t => t.pc = pcOf 86 ∧ t.getReg .x5 = 1 ∧ t.getReg .x10 = 1
  | some (rho, N), t => t.pc = pcOf 90 ∧ RegsEq u t digRegs ∧ Frame u t digW ∧
      rho.length = 16 ∧ t.readWords (BitVec.ofNat 64 0x30) 2 = wordsOf rho ∧
      (∃ ans : BitVec 256, N = ans.toNat % 2 ^ 184 ∧
        t.readWords (BitVec.ofNat 64 0x160) 3 =
          [ans.extractLsb' 0 64, ans.extractLsb' 64 64, ans.extractLsb' 128 64]) ∧
      uOf N 14 = 0

theorem admissible_iff (ans : BitVec 256) :
    (ans.extractLsb' 128 64 <<< 8 >>> 54 = BitVec.ofNat 64 0) ↔ uOf (ans.toNat % 2 ^ 184) 14 = 0 := by
  rw [← BitVec.toNat_inj]
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.extractLsb'_toNat,
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, BitVec.toNat_ofNat, uOf, totalH, ftsA,
    BitVec.toNat_zero, Nat.reducePow, Nat.reduceAdd, Nat.reduceMul, Nat.reduceMod]
  have := ans.isLt
  constructor <;> intro h <;> omega

theorem pcOf_eq (i : Nat) (h : 0x1000 + 4 * i < 2 ^ 64) (w : Word) (hw : w.toNat = 0x1000 + 4 * i) :
    w = pcOf i := by
  apply BitVec.eq_of_toNat_eq; rw [hw]; simp; omega

theorem pcOf_add4 (i : Nat) : pcOf i + 4 = pcOf (i + 1) := by
  apply BitVec.eq_of_toNat_eq; simp; omega

/-- One trial: from `dig_loop` (counter `a`) the rnd hash, the digest hash, and the test;
`rest` is what follows a non-admissible trial (from instruction 41). -/
theorem digTrial (sk : SecretKey) (m : Message) (u : MachineState)
    (hmem : DigMem (toList sk) (toList m) u) (hx5 : u.getReg .x5 = 0) (a : Nat) (t : MachineState)
    (hinv : DigInv u a t) (rest : OracleComp HashSpec (Option (Val × Nat))) (Wr : Nat)
    (hrest : ∀ t', t'.pc = pcOf 82 → t'.getReg .x6 = BitVec.ofNat 64 a → RegsEq u t' digRegs →
      Frame u t' digW → lo32 (t'.getMem (BitVec.ofNat 64 0x620)) = lo32 (u.getMem (BitVec.ofNat 64 0x620)) →
      Sim image t' Wr rest (DigPost u)) :
    Sim image t (44 + Wr) (hash16 (rndInput (toList sk) (toList m) a) >>= fun rho =>
      (liftM (HashSpec.query (fmt (digestInput rho (toList m)))) : OracleComp HashSpec _) >>= fun ans =>
        if admissible (ans.toNat % 2 ^ 184) then pure (some (rho, ans.toNat % 2 ^ 184)) else rest)
      (DigPost u) := by
  have hS : (toList sk).length = 32 := length_toList sk
  have hm : (toList m).length = 32 := length_toList m
  obtain ⟨tpc, t6, ha, tregs, tframe, tlo⟩ := hinv
  -- block 27
  have hs1 := symRun_sound blk65 codeAt_65 t tpc (by simp only [blk65.res, rv_simp])
  set t1 := blk65.res.toState t with ht1
  have f1 : Frame t t1 (fun x => x = 0x620) := by
    apply frame_toState; intro x hx hW
    simp only [blk65.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq, ofNat_eq_iff]
    omega
  have r1 : RegsEq t t1 [.x10, .x11, .x12] := by
    intro r hr; simp only [ht1, Result.toState_getReg]
    cases r <;> simp_all [blk65.res, rv_simp] <;> rfl
  have e1 : fetch image t1 = some (.base .ECALL) := symRun_ecall blk65 codeAt_65 t (by simp only [blk65.res, rv_simp]) rfl
  have x10 : t1.getReg .x10 = BitVec.ofNat 64 0x620 := by simp only [ht1, blk65.res, rv_simp]
  have x11 : t1.getReg .x11 = BitVec.ofNat 64 128 := by simp only [ht1, blk65.res, rv_simp]
  have x12 : t1.getReg .x12 = BitVec.ofNat 64 0x140 := by simp only [ht1, blk65.res, rv_simp]
  have x5 : t1.getReg .x5 = 0 := by rw [r1.get .x5, tregs.get .x5, hx5]
  have pc1 : t1.pc = pcOf 69 := by simp only [ht1, blk65.res, rv_simp]
  have m620 : t1.getMem (BitVec.ofNat 64 0x620) = twWord0 7 0 0 a := by
    rvs [ht1, blk65.res, t6]
    refine (word_of_halves _ 0x701 a (by rw [lo32_replace1, tlo, hmem.rb0]) (by rw [hi32_replace1])).trans ?_
    unfold twWord0; congr 1
  have hq1 : hashInput t1 = pad64 (rndInput (toList sk) (toList m) a) := by
    obtain ⟨hn, hw⟩ := words_rndInput _ _ hS hm a
    refine hashInput_eq_pad64 t1 _ 1 hn (by rw [x11]) (by norm_num) (by rw [x10]; decide) ?_
    rw [hw, x10, show 8 * (1 + 1) = 1 + 3 + 4 + 4 + 4 from rfl]
    rw [readWords_ofNat_add, readWords_ofNat_add, readWords_ofNat_add, readWords_ofNat_add]
    simp only [Nat.reduceMul, Nat.reduceAdd]
    rw [readWords_ofNat_one, m620]
    rw [f1.readWords _ _ (by norm_num) (by intro i hi; omega),
      f1.readWords _ _ (by norm_num) (by intro i hi; omega),
      f1.readWords _ _ (by norm_num) (by intro i hi; omega),
      f1.readWords _ _ (by norm_num) (by intro i hi; omega),
      tframe.readWords _ _ (by norm_num) (by intro i hi; simp only [digW]; omega),
      tframe.readWords _ _ (by norm_num) (by intro i hi; simp only [digW]; omega),
      tframe.readWords _ _ (by norm_num) (by intro i hi; simp only [digW]; omega),
      tframe.readWords _ _ (by norm_num) (by intro i hi; simp only [digW]; omega),
      hmem.rbP, hmem.rbS, hmem.rbM, hmem.rbZ]
    simp [twWords_eq]
  have hc1 : blk65.res.cycles = 4 := rfl
  rw [hc1] at hs1
  have hb1 : (pad64 (rndInput (toList sk) (toList m) a)).blocks = 2 := by
    simp [pad64, Query.blocks, (words_rndInput _ _ hS hm a).1]
  refine (Sim.steps hs1 (Sim.hash16_bind (W := 4 + (16 + (4 + Wr))) e1 x5
    (hashArgs_of x10 x11 x12 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)) hq1 (fmt_thInput _ _ _ _ _ _ (by decide)) (fun ans1 => ?_))).mono (by rw [hb1]; omega) (fun _ _ h => h)
  -- after the rnd hash
  set rho := answerBytes 16 ans1 with hrho
  set t2 := writeHash t1 ans1 with ht2
  have f2 : Frame t1 t2 (fun x => 0x140 ≤ x ∧ x < 0x140 + 32) := frame_writeHash t1 ans1 0x140 x12 (by norm_num)
  have v2 : t2.readWords (BitVec.ofNat 64 0x140) 2 = wordsOf rho := writeHash_readWords_val t1 ans1 0x140 x12 (by norm_num)
  have pc2 : t2.pc = pcOf 70 := by rw [ht2, writeHash_pc, pc1, pcOf_add4]
  have hs2 := symRun_sound blk70 codeAt_70 t2 pc2 (by simp only [blk70.res, rv_simp])
  set t3 := blk70.res.toState t2 with ht3
  have f3 : Frame t2 t3 (fun x => x = 0x30 ∨ x = 0x38) := by
    apply frame_toState; intro x hx hW
    simp only [blk70.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq, ofNat_eq_iff]
    omega
  have r3 : RegsEq t2 t3 [.x1, .x2, .x10, .x11, .x12] := by
    intro r hr; simp only [ht3, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have e3 : fetch image t3 = some (.base .ECALL) := symRun_ecall blk70 codeAt_70 t2 (by simp only [blk70.res, rv_simp]) rfl
  have y10 : t3.getReg .x10 = BitVec.ofNat 64 0x20 := by simp only [ht3, blk70.res, rv_simp]
  have y11 : t3.getReg .x11 = BitVec.ofNat 64 64 := by simp only [ht3, blk70.res, rv_simp]
  have y12 : t3.getReg .x12 = BitVec.ofNat 64 0x160 := by simp only [ht3, blk70.res, rv_simp]
  have y5 : t3.getReg .x5 = 0 := by rw [r3.get .x5, ht2, writeHash_getReg, x5]
  have pc3 : t3.pc = pcOf 77 := by simp only [ht3, blk70.res, rv_simp]
  have v3 : t3.readWords (BitVec.ofNat 64 0x30) 2 = wordsOf rho := by
    rw [← v2, readWords_ofNat_two, readWords_ofNat_two]; simp only [ht3, blk70.res, rv_simp]; rfl
  -- frame from u to t3 outside digW
  have fu3 : Frame u t3 digW := (((tframe.trans f1).trans f2).trans f3).mono (by
    intro x hx; simp only [digW, false_or, or_false] at hx ⊢; omega)
  have hlen : rho.length = 16 := by simp [hrho]
  have hq2 : hashInput t3 = fmt (digestInput rho (toList m)) := by
    refine hashInput_eq_digest t3 _ _ hlen hm y11 (by rw [y10]; decide) ?_
    rw [y10, show (8 : Nat) = 2 + 2 + 4 from rfl]
    rw [readWords_ofNat_add, readWords_ofNat_add]
    simp only [Nat.reduceMul, Nat.reduceAdd]
    rw [fu3.readWords _ _ (by norm_num) (by intro i hi; simp only [digW]; omega), hmem.db0, v3,
      fu3.readWords _ _ (by norm_num) (by intro i hi; simp only [digW]; omega), hmem.dbM]
    simp [twWords_eq, twWord0]
  have hc2 : blk70.res.cycles = 7 := rfl
  rw [hc2] at hs2
  have hb2 : (fmt (digestInput rho (toList m))).blocks = 1 := by
    rw [fmt_digestInput _ _ hlen hm]; rfl
  refine (Sim.steps hs2 (Sim.query_bind (W := 4 + Wr) e3 y5
    (hashArgs_of y10 y11 y12 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)) hq2 (fun ans2 => ?_))).mono (by rw [hb2]; omega) (fun _ _ h => h)
  -- after the digest hash
  set t4 := writeHash t3 ans2 with ht4
  have f4 : Frame t3 t4 (fun x => 0x160 ≤ x ∧ x < 0x160 + 32) :=
    frame_writeHash t3 ans2 0x160 y12 (by norm_num)
  have pc4 : t4.pc = pcOf 78 := by rw [ht4, writeHash_pc, pc3, pcOf_add4]
  have w4 : ∀ k, k < 3 → t4.getMem (BitVec.ofNat 64 (0x160 + 8 * k)) = ans2.extractLsb' (64 * k) 64 := by
    intro k hk
    rw [ht4, writeHash_getMem_ofNat t3 ans2 0x160 _ y12 (by norm_num) (by omega)]
    interval_cases k <;> simp
  have hs3 := symRun_sound blk78 codeAt_78 t4 pc4 (by simp only [blk78.res, rv_simp])
  have hc3 : blk78.res.cycles = 4 := rfl
  rw [hc3] at hs3
  set t5 := blk78.res.toState t4 with ht5
  have f5 : Frame t4 t5 (fun _ => False) := by
    apply frame_toState; intro x hx hW; simp [blk78.res]
  have r5 : RegsEq t4 t5 [.x3] := by
    intro r hr; simp only [ht5, Result.toState_getReg]
    cases r <;> simp_all [blk78.res, rv_simp]
  have fu5 : Frame u t5 digW := ((fu3.trans f4).trans f5).mono (by
    intro x hx; simp only [digW, false_or, or_false] at hx ⊢; omega)
  have ru5 : RegsEq u t5 digRegs := (((((tregs.trans r1).trans (regsEq_writeHash _ _ [])).trans r3).trans
    (regsEq_writeHash _ _ [])).trans r5).mono (by decide)
  have pc5 : t5.pc = if admissible (ans2.toNat % 2 ^ 184) then pcOf 90 else pcOf 82 := by
    have h368 := w4 2 (by norm_num)
    simp only [Nat.reduceMul, Nat.reduceAdd] at h368
    simp only [ht5, blk78.res, rv_simp, h368]
    simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, admissible, beq_iff_eq]
    by_cases h : uOf (ans2.toNat % 2 ^ 184) 14 = 0
    · rw [if_pos ((admissible_iff ans2).mpr h), if_pos (by simpa using h)]
    · rw [if_neg (mt (admissible_iff ans2).mp h), if_neg (by simpa using h)]
  by_cases hadm : admissible (ans2.toNat % 2 ^ 184) = true
  · rw [if_pos hadm]
    refine (Sim.pure_steps hs3 ?_).mono (by omega) (fun _ _ h => h)
    refine ⟨by rw [pc5, if_pos hadm], ru5, fu5, hlen, ?_, ⟨ans2, rfl, ?_⟩, ?_⟩
    · rw [f5.readWords _ _ (by norm_num) (by simp), f4.readWords _ _ (by norm_num) (by intro i hi; omega), v3]
    · rw [f5.readWords _ _ (by norm_num) (by simp)]
      simp only [readWords_ofNat_succ, MachineState.readWords]
      have := w4 0 (by norm_num); have := w4 1 (by norm_num); have := w4 2 (by norm_num)
      simp_all
    · simpa [admissible] using hadm
  · rw [if_neg hadm]
    refine Sim.steps hs3 (hrest t5 (by rw [pc5, if_neg hadm]) ?_ ru5 fu5 ?_)
    · rw [r5.get .x6, ht4, writeHash_getReg, r3.get .x6, ht2, writeHash_getReg, r1.get .x6, t6]
    · rw [f5.getMem (by norm_num) (by simp), f4.getMem (by norm_num) (by omega),
        f3.getMem (by norm_num) (by omega), f2.getMem (by norm_num) (by omega)]
      simp only [ht1, blk65.res, rv_simp, ite_true, lo32_replace1, Nat.reduceDiv]
      exact tlo

theorem searchDigest_succ (S mm : List Byte) (a f : Nat) :
    searchDigest S mm a (f + 1) = (hash16 (rndInput S mm a) >>= fun rho =>
      (liftM (HashSpec.query (fmt (digestInput rho mm))) : OracleComp HashSpec _) >>= fun ans =>
        if admissible (ans.toNat % 2 ^ 184) then pure (some (rho, ans.toNat % 2 ^ 184))
        else searchDigest S mm (a + 1) f) := by
  simp only [searchDigest, digest, H, bind_assoc, pure_bind]

/-- After a non-admissible trial (instruction 41): `a += 1`, back to the loop or fail. -/
theorem digNext (u : MachineState) (hx7 : u.getReg .x7 = BitVec.ofNat 64 (2 ^ 20)) (a : Nat)
    (ha : a < 2 ^ 20) (t : MachineState) (tpc : t.pc = pcOf 82) (t6 : t.getReg .x6 = BitVec.ofNat 64 a)
    (tregs : RegsEq u t digRegs) (tframe : Frame u t digW)
    (tlo : lo32 (t.getMem (BitVec.ofNat 64 0x620)) = lo32 (u.getMem (BitVec.ofNat 64 0x620))) :
    ∃ t', Steps image t 2 2 t' ∧
      (a + 1 < 2 ^ 20 → DigInv u (a + 1) t') ∧ (a + 1 = 2 ^ 20 → t'.pc = pcOf 84) ∧
      RegsEq t t' [.x6] := by
  have hs := symRun_sound blk82 codeAt_82 t tpc (by simp only [blk82.res, rv_simp])
  have r41 : RegsEq t (blk82.res.toState t) [.x6] := by
    intro r hr
    rw [Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  refine ⟨_, hs, ?_, ?_, r41⟩
  · intro h
    refine ⟨?_, ?_, h, ?_, ?_, ?_⟩
    · simp only [blk82.res, rv_simp, t6, tregs.get .x7 (by simp [digRegs]), hx7, ofNat_add_ofNat,
        ofNat_bne_ofNat]
      rw [if_pos (by simp; omega)]
    · simp only [blk82.res, rv_simp, t6, ofNat_add_ofNat]
    · exact (tregs.trans r41).mono (by intro r hr; simp [digRegs] at hr ⊢; tauto)
    · intro x hx hW
      rw [Result.toState_getMem, show blk82.res.st.mem = [] from rfl, memEval_nil]; exact tframe x hx hW
    · rw [Result.toState_getMem, show blk82.res.st.mem = [] from rfl, memEval_nil]; exact tlo
  · intro h
    simp only [blk82.res, rv_simp, t6, tregs.get .x7 (by simp [digRegs]), hx7, ofNat_add_ofNat,
      ofNat_bne_ofNat]
    rw [if_neg (by simp; omega)]

/-- The digest search. -/
theorem digLoop_sim (sk : SecretKey) (m : Message) (u : MachineState)
    (hmem : DigMem (toList sk) (toList m) u) (hx5 : u.getReg .x5 = 0)
    (hx7 : u.getReg .x7 = BitVec.ofNat 64 (2 ^ 20)) :
    ∀ fuel a t, a + (fuel + 1) = 2 ^ 20 → DigInv u a t →
      Sim image t ((fuel + 1) * 46 + 2) (searchDigest (toList sk) (toList m) a (fuel + 1))
        (DigPost u) := by
  have hS : (toList sk).length = 32 := length_toList sk
  have hm : (toList m).length = 32 := length_toList m
  intro fuel
  induction fuel with
  | zero =>
    intro a t ha hinv
    rw [searchDigest_succ]
    refine (digTrial sk m u hmem hx5 a t hinv _ 4 ?_).mono (by omega) (fun _ _ h => h)
    intro t' tpc t6 tregs tframe tlo
    obtain ⟨t'', hs, -, hfail, -⟩ := digNext u hx7 a (by omega) t' tpc t6 tregs tframe tlo
    have hs43 := symRun_sound blk84 codeAt_84 t'' (hfail (by omega)) (by simp only [blk84.res, rv_simp])
    have hc : blk84.res.cycles = 2 := rfl
    rw [hc] at hs43
    have := Sim.steps hs (Sim.pure_steps (a := (none : Option (Val × Nat))) (Q := DigPost u) hs43
      ⟨by simp only [blk84.res, rv_simp], by simp only [blk84.res, rv_simp],
       by simp only [blk84.res, rv_simp]⟩)
    simpa [searchDigest] using this
  | succ f ih =>
    intro a t ha hinv
    rw [searchDigest_succ]
    refine (digTrial sk m u hmem hx5 a t hinv _ (2 + ((f + 1) * 46 + 2)) ?_).mono (by ring_nf; omega)
      (fun _ _ h => h)
    intro t' tpc t6 tregs tframe tlo
    obtain ⟨t'', hs, hinv', -, -⟩ := digNext u hx7 a (by omega) t' tpc t6 tregs tframe tlo
    exact Sim.steps hs (ih (a + 1) t'' (by omega) (hinv' (by omega)))

end SigGolfCandidate.Packed.Sign

/-! ### cloned Enc -/

/-!
# `sign`, the counter search of a layer (`enc_loop`, instructions 294 .. 329)

`encLoop_sim` : from `enc_loop` with counter `c`, the machine refines
`searchCounter lay tau e M c (2^22 - c)`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace SigGolfCandidate.Packed.Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

theorem slice_valOfWords_0 (w0 w1 : Word) : slice (valOfWords w0 w1) 0 8 = bytesOfWord w0 := by
  simp [slice, valOfWords]

theorem slice_valOfWords_8 (w0 w1 : Word) : slice (valOfWords w0 w1) 8 8 = bytesOfWord w1 := by
  simp [slice, valOfWords, List.drop_append_of_le_length]

/-- `decodeDigits` of a hash answer, in terms of its first two dwords. -/
theorem decodeDigits_answer (a : BitVec 256) :
    decodeDigits (answerBytes 16 a) =
      if (a.extractLsb' 0 64).toNat < 2 ^ 63 ∧ (a.extractLsb' 64 64).toNat < 2 ^ 63 then
        (if (digitsOfWord (a.extractLsb' 0 64).toNat ++ digitsOfWord (a.extractLsb' 64 64).toNat).sum
            = 184 then
          some (digitsOfWord (a.extractLsb' 0 64).toNat ++ digitsOfWord (a.extractLsb' 64 64).toNat)
        else none)
      else none := by
  rw [answerBytes_16]
  unfold decodeDigits
  rw [slice_valOfWords_0, slice_valOfWords_8, leNat_bytesOfWord, leNat_bytesOfWord]
  rfl

theorem slt_zero_ofNat (d : Nat) (hd : d < 2 ^ 64) :
    BitVec.slt (BitVec.ofNat 64 d) (BitVec.ofNat 64 0) = decide (2 ^ 63 ≤ d) := by
  rw [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.slt_zero_eq_msb, BitVec.msb_eq_decide]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd]

theorem land7 (n : Nat) : n &&& 7 = n % 8 := Nat.and_two_pow_sub_one_eq_mod n 3

/-! ## The SWAR digit sum (shared with verify: `Verify.swar_nat`) -/

/-- The digit-sum masks `M1 = 0x71C7..` (3-bit digits, even positions of 6-bit lanes) and
`M2 = 0xF03F..` (6-bit lanes, even positions of 12-bit lanes). -/
abbrev swM1 : Word := BitVec.ofNat 64 8198552921648689607
abbrev swM2 : Word := BitVec.ofNat 64 17311559823019733055

/-- The four masked digit lanes. -/
def swS1 (a b m1 : Word) : Word := ((a >>> 3) &&& m1) + (a &&& m1) + ((b >>> 3) &&& m1) + (b &&& m1)

/-- One folding step `x + (x >> k)`. -/
def swF (x : Word) (k : Nat) : Word := x + (x >>> k)

/-- The machine's SWAR digit sum of `(d0, d1)` (instructions 309 .. 327). -/
def swarW (a b m1 m2 : Word) : Word :=
  swF (swF (swF (swF (swS1 a b m1) 6 &&& m2) 12) 24) 48 &&& 2047

-- The final pc of the SWAR block (`bne t3, x0` after `addi t3, t3, -184`).
kernel_theorem blk311_pc_raw : ∀ t : MachineState, (blk311.res.toState t).pc =
    if (swarW (t.getReg .x1) (t.getReg .x2) (t.getReg .x26) (t.getReg .x27) +
        BitVec.ofNat 64 (2 ^ 64 - 184) != 0#64) = true then pcOf 333 else pcOf 332

theorem swF_toNat (x : Word) (k : Nat) : (swF x k).toNat = (x.toNat + x.toNat / 2 ^ k) % 2 ^ 64 := by
  rw [swF, BitVec.toNat_add, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem swM1_toNat : swM1.toNat = 8198552921648689607 := rfl
theorem swM2_toNat : swM2.toNat = 17311559823019733055 := rfl

theorem swS1_toNat (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (swS1 (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) swM1).toNat = Verify.sw1 a b := by
  have ea : (BitVec.ofNat 64 a).toNat = a := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]
  have eb : (BitVec.ofNat 64 b).toNat = b := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
  rw [swS1, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_and, BitVec.toNat_and,
    BitVec.toNat_and, BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ushiftRight, ea, eb,
    swM1_toNat, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, show (2 : Nat) ^ 3 = 8 from rfl,
    show (2 : Nat) ^ 64 = 18446744073709551616 from rfl]
  unfold Verify.sw1
  rfl

theorem digitsOfWord_sum_le (d : Nat) : (digitsOfWord d).sum ≤ 147 := by
  have := List.sum_le_card_nsmul (digitsOfWord d) 7 (fun x hx => by
    simp only [digitsOfWord, List.mem_map, List.mem_range] at hx
    obtain ⟨r, _, rfl⟩ := hx; exact Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num)))
  simpa [digitsOfWord] using this

theorem digits_sum_le (a b : Nat) : (digitsOfWord a ++ digitsOfWord b).sum ≤ 294 := by
  rw [List.sum_append]; have := digitsOfWord_sum_le a; have := digitsOfWord_sum_le b; omega

theorem swarW_toNat (a b : Nat) (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) :
    (swarW (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) swM1 swM2).toNat =
      (digitsOfWord a ++ digitsOfWord b).sum := by
  have key := Verify.swar_nat a b ha hb
  have hle := digits_sum_le a b
  have h1 : (swF (swS1 (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) swM1) 6 &&& swM2).toNat =
      Verify.m3 ((Verify.sw1 a b + Verify.sw1 a b / 64) % 18446744073709551616) := by
    rw [BitVec.toNat_and, swF_toNat, swS1_toNat a b (by omega) (by omega), swM2_toNat,
      show (2 : Nat) ^ 6 = 64 from rfl, show (2 : Nat) ^ 64 = 18446744073709551616 from rfl]
    unfold Verify.m3; rfl
  have h2 : ∀ (Y : Word) (y : Nat), Y.toNat = y → (swF (swF (swF Y 12) 24) 48).toNat = Verify.m6 y := by
    intro Y y hY
    rw [swF_toNat, swF_toNat, swF_toNat, hY, show (2 : Nat) ^ 12 = 4096 from rfl,
      show (2 : Nat) ^ 24 = 16777216 from rfl, show (2 : Nat) ^ 48 = 281474976710656 from rfl,
      show (2 : Nat) ^ 64 = 18446744073709551616 from rfl]
    unfold Verify.m6 Verify.m6' Verify.m5 Verify.m4; rfl
  have h3 := h2 _ _ h1
  have h4 : (swarW (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) swM1 swM2).toNat =
      (swF (swF (swF (swF (swS1 (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) swM1) 6 &&& swM2) 12) 24) 48).toNat
        % 2048 := by
    unfold swarW
    rw [BitVec.toNat_and, show (2047 : Word).toNat = 2 ^ 11 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  rw [h4, h3]
  generalize Verify.m6 (Verify.m3 ((Verify.sw1 a b + Verify.sw1 a b / 64) % 18446744073709551616)) = X at key ⊢
  rw [← Nat.mod_mod_of_dvd X (show 2048 ∣ 4096 by norm_num), key]
  omega

theorem swar_check (a b : Nat) (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) :
    (swarW (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) swM1 swM2 + BitVec.ofNat 64 (2 ^ 64 - 184)
      != 0#64) = !decide ((digitsOfWord a ++ digitsOfWord b).sum = 184) := by
  have h := swarW_toNat a b ha hb
  have hle := digits_sum_le a b
  generalize swarW (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) swM1 swM2 = w at h
  have hc : (BitVec.ofNat 64 (2 ^ 64 - 184)).toNat = 2 ^ 64 - 184 := rfl
  by_cases hs : (digitsOfWord a ++ digitsOfWord b).sum = 184
  · have : w + BitVec.ofNat 64 (2 ^ 64 - 184) = 0#64 := by
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add, h, hs, hc]; rfl
    rw [this, decide_eq_true hs]; rfl
  · have : w + BitVec.ofNat 64 (2 ^ 64 - 184) ≠ 0#64 := by
      intro h'
      have := congrArg BitVec.toNat h'
      rw [BitVec.toNat_add, h, hc] at this
      have h0 : (0#64).toNat = 0 := rfl
      rw [h0] at this
      omega
    rw [bne_iff_ne.mpr this, decide_eq_false hs]; rfl

/-- The sign test `(d0 | d1) < 0` (bit 63 of either word). -/
theorem slt_or_ofNat (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    BitVec.slt (BitVec.ofNat 64 a ||| BitVec.ofNat 64 b) (BitVec.ofNat 64 0) =
      decide (2 ^ 63 ≤ a ∨ 2 ^ 63 ≤ b) := by
  rw [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.slt_zero_eq_msb, BitVec.msb_or,
    BitVec.msb_eq_decide, BitVec.msb_eq_decide]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  by_cases h1 : 2 ^ 63 ≤ a <;> by_cases h2 : 2 ^ 63 ≤ b <;> simp [h1, h2]

structure EncMem (lay tau e : Nat) (M : Val) (u : MachineState) : Prop where
  hlay : lay < 6
  htau : tau < 2 ^ 30
  he : e < 2048
  hM : M.length = 16
  eb0 : u.getMem (BitVec.ofNat 64 0x100) = twWord0 4 lay tau 0
  eb8 : u.getMem (BitVec.ofNat 64 0x108) = BitVec.ofNat 64 (tau + 2 ^ 32 * e)
  ebP : u.readWords (BitVec.ofNat 64 0x110) 2 = [0, 0]
  ebM : u.readWords (BitVec.ofNat 64 0x120) 2 = wordsOf M
  eb56 : u.getMem (BitVec.ofNat 64 0x138) = 0
  x5 : u.getReg .x5 = 0
  x7 : u.getReg .x7 = BitVec.ofNat 64 (2 ^ 22)
  x26 : u.getReg .x26 = swM1
  x27 : u.getReg .x27 = swM2

def encW (a : Nat) : Prop := a = 0x130 ∨ (0x140 ≤ a ∧ a < 0x160)

def encRegs : List Reg := [.x1, .x2, .x3, .x6, .x10, .x11, .x12, .x28, .x29]

def EncInv (u : MachineState) (c : Nat) (t : MachineState) : Prop :=
  t.pc = pcOf 302 ∧ t.getReg .x6 = BitVec.ofNat 64 c ∧ c < 2 ^ 22 ∧ RegsEq u t encRegs ∧ Frame u t encW

def EncPost (u : MachineState) : Option (Nat × List Nat) → MachineState → Prop
  | none, t => t.pc = pcOf 337 ∧ t.getReg .x5 = 1 ∧ t.getReg .x10 = 1
  | some (c, x), t => t.pc = pcOf 338 ∧ t.getReg .x6 = BitVec.ofNat 64 c ∧ c < 2 ^ 22 ∧
      (∃ d0 d1, d0 < 2 ^ 63 ∧ d1 < 2 ^ 63 ∧ x = digitsOfWord d0 ++ digitsOfWord d1 ∧ x.sum = 184 ∧
        t.getReg .x1 = BitVec.ofNat 64 d0 ∧ t.getReg .x2 = BitVec.ofNat 64 d1) ∧
      RegsEq u t encRegs ∧ Frame u t encW

theorem searchCounter_succ (lay tau e : Nat) (M : Val) (c f : Nat) :
    searchCounter lay tau e M c (f + 1) = (hash16 (encInput lay tau e M c) >>= fun d =>
      match decodeDigits d with
      | some x => pure (some (c, x))
      | none => searchCounter lay tau e M (c + 1) f) := rfl

theorem encTrial (lay tau e : Nat) (M : Val) (u : MachineState) (hmem : EncMem lay tau e M u)
    (c : Nat) (t : MachineState) (hinv : EncInv u c t) (rest : OracleComp HashSpec (Option (Nat × List Nat)))
    (Wr : Nat)
    (hrest : ∀ t', t'.pc = pcOf 333 → t'.getReg .x6 = BitVec.ofNat 64 c → RegsEq u t' encRegs →
      Frame u t' encW → Sim image t' Wr rest (EncPost u)) :
    Sim image t (38 + Wr) (hash16 (encInput lay tau e M c) >>= fun d =>
      match decodeDigits d with
      | some x => pure (some (c, x))
      | none => rest) (EncPost u) := by
  obtain ⟨tpc, t6, hc, tregs, tframe⟩ := hinv
  have hl := hmem.hlay
  have htau := hmem.htau
  have he := hmem.he
  -- block 294
  have hs1 := symRun_sound blk302 codeAt_302 t tpc (by simp only [blk302.res, rv_simp])
  have hc1 : blk302.res.cycles = 4 := rfl
  rw [hc1] at hs1
  set t1 := blk302.res.toState t with ht1
  have f1 : Frame t t1 (fun x => x = 0x130) := by
    apply frame_toState; intro x hx hW
    simp only [blk302.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq, ofNat_eq_iff]
    omega
  have r1 : RegsEq t t1 [.x10, .x11, .x12] := by
    intro r hr; rw [ht1, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have e1 := symRun_ecall blk302 codeAt_302 t (by simp only [blk302.res, rv_simp]) rfl
  have x10 : t1.getReg .x10 = BitVec.ofNat 64 0x100 := by simp only [ht1, blk302.res, rv_simp]
  have x11 : t1.getReg .x11 = BitVec.ofNat 64 64 := by simp only [ht1, blk302.res, rv_simp]
  have x12 : t1.getReg .x12 = BitVec.ofNat 64 0x140 := by simp only [ht1, blk302.res, rv_simp]
  have x5 : t1.getReg .x5 = 0 := by rw [r1.get .x5, tregs.get .x5, hmem.x5]
  have pc1 : t1.pc = pcOf 306 := by simp only [ht1, blk302.res, rv_simp]
  have hq : hashInput t1 = pad64 (encInput lay tau e M c) := by
    obtain ⟨hn, hw⟩ := words_encInput lay tau e M hmem.hM c
    refine hashInput_eq_pad64 t1 _ 0 hn (by rw [x11]) (by norm_num) (by rw [x10]; decide) ?_
    rw [hw, x10, show 8 * (0 + 1) = 1 + 1 + 2 + 2 + 1 + 1 from rfl]
    rw [readWords_ofNat_add, readWords_ofNat_add, readWords_ofNat_add, readWords_ofNat_add,
      readWords_ofNat_add]
    simp only [Nat.reduceMul, Nat.reduceAdd]
    rw [readWords_ofNat_one, readWords_ofNat_one, readWords_ofNat_one, readWords_ofNat_one,
      f1.getMem (a := 0x100) (by norm_num) (by norm_num),
      tframe.getMem (a := 0x100) (by norm_num) (by simp only [encW]; omega),
      hmem.eb0, f1.getMem (a := 0x108) (by norm_num) (by norm_num),
      tframe.getMem (a := 0x108) (by norm_num) (by simp only [encW]; omega), hmem.eb8,
      f1.readWords _ _ (by norm_num) (by intro i hi; omega),
      tframe.readWords _ _ (by norm_num) (by intro i hi; simp only [encW]; omega), hmem.ebP,
      f1.readWords _ _ (by norm_num) (by intro i hi; omega),
      tframe.readWords _ _ (by norm_num) (by intro i hi; simp only [encW]; omega), hmem.ebM,
      f1.getMem (a := 0x138) (by norm_num) (by norm_num),
      tframe.getMem (a := 0x138) (by norm_num) (by simp only [encW]; omega), hmem.eb56]
    simp only [ht1, blk302.res, rv_simp, t6]
    simp only [twWords_eq, List.cons_append, List.nil_append, List.append_assoc, List.cons.injEq,
      true_and, and_true]
    refine ⟨?_, ?_⟩
    · congr 1; rw [Nat.mod_eq_of_lt (by omega : tau < 2 ^ 32), Nat.mod_eq_of_lt (by omega : e < 2 ^ 32)]
    · rw [if_pos trivial, Nat.mod_eq_of_lt (by omega : c < 2 ^ 32)]
  have hb : (pad64 (encInput lay tau e M c)).blocks = 1 :=
    congrArg (· + 1) (words_encInput lay tau e M hmem.hM c).1
  refine (Sim.steps hs1 (Sim.hash16_bind (W := 26 + Wr) e1 x5
    (hashArgs_of x10 x11 x12 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)) hq (fmt_thInput _ _ _ _ _ _ (by decide)) (fun a => ?_))).mono (by rw [hb]; omega) (fun _ _ h => h)
  set t2 := writeHash t1 a with ht2
  have f2 : Frame t1 t2 (fun x => 0x140 ≤ x ∧ x < 0x140 + 32) := frame_writeHash t1 a _ x12 (by norm_num)
  have pc2 : t2.pc = pcOf 307 := by rw [ht2, writeHash_pc, pc1]; apply BitVec.eq_of_toNat_eq; simp
  have w0 : t2.getMem (BitVec.ofNat 64 0x140) = a.extractLsb' 0 64 := by
    rw [ht2, writeHash_getMem_ofNat t1 a 0x140 0x140 x12 (by norm_num) (by norm_num)]; simp
  have w1 : t2.getMem (BitVec.ofNat 64 0x148) = a.extractLsb' 64 64 := by
    rw [ht2, writeHash_getMem_ofNat t1 a 0x140 0x148 x12 (by norm_num) (by norm_num)]; simp
  set d0 := (a.extractLsb' 0 64).toNat with hd0
  set d1 := (a.extractLsb' 64 64).toNat with hd1
  have hd0' : a.extractLsb' 0 64 = BitVec.ofNat 64 d0 := by rw [hd0, BitVec.ofNat_toNat]; rfl
  have hd1' : a.extractLsb' 64 64 = BitVec.ofNat 64 d1 := by rw [hd1, BitVec.ofNat_toNat]; rfl
  have hd0l : d0 < 2 ^ 64 := BitVec.isLt _
  have hd1l : d1 < 2 ^ 64 := BitVec.isLt _
  rw [decodeDigits_answer]
  -- block 299: load the encoding, sign test
  have hs3 := symRun_sound blk307 codeAt_307 t2 pc2 (by simp only [blk307.res, rv_simp])
  have hc3 : blk307.res.cycles = 4 := rfl
  rw [hc3] at hs3
  set t3 := blk307.res.toState t2 with ht3
  have f3 : Frame t2 t3 (fun _ => False) := by
    apply frame_toState; intro x hx hW; simp [blk307.res]
  have r3 : RegsEq t2 t3 [.x1, .x2, .x3] := by
    intro r hr; rw [ht3, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have y1 : t3.getReg .x1 = BitVec.ofNat 64 d0 := by
    simp only [ht3, blk307.res, rv_simp]; rw [w0, hd0']
  have y2 : t3.getReg .x2 = BitVec.ofNat 64 d1 := by
    simp only [ht3, blk307.res, rv_simp]; rw [w1, hd1']
  have fu3 : Frame u t3 encW := (((tframe.trans f1).trans f2).trans f3).mono (by
    intro x hx; simp only [encW] at hx ⊢; rcases hx with ((h | h) | h) | h
    · exact h
    · omega
    · omega
    · exact h.elim)
  have ru3 : RegsEq u t3 encRegs := ((((tregs.trans r1).trans (regsEq_writeHash _ _ [])).trans r3)).mono
    (by decide)
  have x36 : t3.getReg .x6 = BitVec.ofNat 64 c := by
    rw [r3.get .x6, ht2, writeHash_getReg, r1.get .x6, t6]
  have pc3 : t3.pc = if 2 ^ 63 ≤ d0 ∨ 2 ^ 63 ≤ d1 then pcOf 333 else pcOf 311 := by
    simp only [ht3, blk307.res, rv_simp, CmpOp.eval, w0, w1, hd0', hd1', slt_or_ofNat _ _ hd0l hd1l]
    by_cases h : 2 ^ 63 ≤ d0 ∨ 2 ^ 63 ≤ d1
    · rw [if_pos h, if_pos (by simpa using h)]
    · rw [if_neg h, if_neg (by simpa using h)]
  by_cases h01 : d0 < 2 ^ 63 ∧ d1 < 2 ^ 63
  swap
  · rw [if_neg h01]
    exact (Sim.steps hs3 (hrest t3 (by rw [pc3, if_pos (by omega)]) x36 ru3 fu3)).mono (by omega)
      (fun _ _ h => h)
  obtain ⟨h0, h1⟩ := h01
  rw [if_pos ⟨h0, h1⟩]
  have hs5 := symRun_sound blk311 codeAt_311 t3 (by rw [pc3, if_neg (by omega)])
    (by simp only [blk311.res, rv_simp])
  have hc5 : blk311.res.cycles = 21 := rfl
  rw [hc5] at hs5
  set t5 := blk311.res.toState t3 with ht5
  have f5 : Frame t3 t5 (fun _ => False) := by
    apply frame_toState; intro x hx hW; simp [blk311.res]
  have r5 : RegsEq t3 t5 [.x28, .x29] := by
    intro r hr; rw [ht5, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have fu5 : Frame u t5 encW := (fu3.trans f5).mono (by
    intro x hx; rcases hx with h | h; exact h; exact h.elim)
  have ru5 : RegsEq u t5 encRegs := (ru3.trans r5).mono (by decide)
  have pc5 : t5.pc = if (digitsOfWord d0 ++ digitsOfWord d1).sum = 184 then pcOf 332 else pcOf 333 := by
    rw [ht5, blk311_pc_raw, y1, y2, ru3.get .x26, hmem.x26, ru3.get .x27, hmem.x27,
      swar_check d0 d1 h0 h1]
    by_cases h : (digitsOfWord d0 ++ digitsOfWord d1).sum = 184
    · rw [if_pos h, if_neg (by rw [decide_eq_true h]; decide)]
    · rw [if_neg h, if_pos (by rw [decide_eq_false h]; rfl)]
  by_cases hsum : (digitsOfWord d0 ++ digitsOfWord d1).sum = 184
  · rw [if_pos hsum]
    have hs6 := symRun_sound blk332 codeAt_332 t5 (by rw [pc5, if_pos hsum])
      (by simp only [blk332.res, rv_simp])
    have hc6 : blk332.res.cycles = 1 := rfl
    rw [hc6] at hs6
    set t6 := blk332.res.toState t5 with ht6
    have f6 : Frame t5 t6 (fun _ => False) := by
      apply frame_toState; intro x hx hW; simp [blk332.res]
    have r6 : RegsEq t5 t6 [] := by
      intro r hr; rw [ht6, Result.toState_getReg]
      cases r <;> first | exact absurd (by decide) hr | rfl
    refine (Sim.steps hs3 (Sim.steps hs5 (Sim.pure_steps hs6 ?_))).mono
      (by omega) (fun _ _ h => h)
    refine ⟨by simp only [ht6, blk332.res, rv_simp], ?_, hc, ⟨d0, d1, h0, h1, rfl, hsum, ?_, ?_⟩,
      (ru5.trans r6).mono (by decide), (fu5.trans f6).mono (by
        intro x hx; rcases hx with h | h; exact h; exact h.elim)⟩
    · rw [r6.get .x6, r5.get .x6, x36]
    · rw [r6.get .x1, r5.get .x1, y1]
    · rw [r6.get .x2, r5.get .x2, y2]
  · rw [if_neg hsum]
    exact (Sim.steps hs3 (Sim.steps hs5 (hrest t5 (by rw [pc5, if_neg hsum])
      (by rw [r5.get .x6, x36]) ru5 fu5))).mono (by omega) (fun _ _ h => h)

/-- After a failing trial (instruction 325): `c += 1`, back to the loop or fail. -/
theorem encNext (u : MachineState) (hx7 : u.getReg .x7 = BitVec.ofNat 64 (2 ^ 22)) (c : Nat)
    (hc : c < 2 ^ 22) (t : MachineState) (tpc : t.pc = pcOf 333) (t6 : t.getReg .x6 = BitVec.ofNat 64 c)
    (tregs : RegsEq u t encRegs) (tframe : Frame u t encW) :
    ∃ t', Steps image t 2 2 t' ∧ (c + 1 < 2 ^ 22 → EncInv u (c + 1) t') ∧
      (c + 1 = 2 ^ 22 → t'.pc = pcOf 335) := by
  have hs := symRun_sound blk333 codeAt_333 t tpc (by simp only [blk333.res, rv_simp])
  have r1 : RegsEq t (blk333.res.toState t) [.x6] := by
    intro r hr; rw [Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have t7 : t.getReg .x7 = BitVec.ofNat 64 (2 ^ 22) := by rw [tregs.get .x7, hx7]
  refine ⟨_, hs, ?_, ?_⟩
  · intro h
    refine ⟨?_, ?_, h, (tregs.trans r1).mono (by decide), ?_⟩
    · simp only [blk333.res, rv_simp, t6, t7, ofNat_add_ofNat, ofNat_bne_ofNat]
      rw [if_pos (by rw [bne_cond _ _ (by omega) (by omega)]; omega)]
    · simp only [blk333.res, rv_simp, t6, ofNat_add_ofNat]
    · intro x hx hW
      rw [Result.toState_getMem, show blk333.res.st.mem = [] from rfl, memEval_nil]; exact tframe x hx hW
  · intro h
    simp only [blk333.res, rv_simp, t6, t7, ofNat_add_ofNat, ofNat_bne_ofNat]
    rw [if_neg (by rw [bne_cond _ _ (by omega) (by omega)]; omega)]

/-- **Counter search** of a layer, from counter `c` with `fuel + 1` trials left. -/
theorem encLoop_sim (lay tau e : Nat) (M : Val) (u : MachineState) (hmem : EncMem lay tau e M u) :
    ∀ fuel c t, c + (fuel + 1) = 2 ^ 22 → EncInv u c t →
      Sim image t ((fuel + 1) * 40 + 2) (searchCounter lay tau e M c (fuel + 1)) (EncPost u) := by
  intro fuel
  induction fuel with
  | zero =>
    intro c t hc hinv
    rw [searchCounter_succ]
    refine (encTrial lay tau e M u hmem c t hinv _ 4 ?_).mono (by omega) (fun _ _ h => h)
    intro t' tpc t6 tregs tframe
    obtain ⟨t'', hs, -, hfail⟩ := encNext u hmem.x7 c (by omega) t' tpc t6 tregs tframe
    have hs67 := symRun_sound blk335 codeAt_335 t'' (hfail (by omega)) (by simp only [blk335.res, rv_simp])
    have hc67 : blk335.res.cycles = 2 := rfl
    rw [hc67] at hs67
    have := Sim.steps hs (Sim.pure_steps (a := (none : Option (Nat × List Nat))) (Q := EncPost u) hs67
      ⟨by simp only [blk335.res, rv_simp], by simp only [blk335.res, rv_simp],
       by simp only [blk335.res, rv_simp]⟩)
    simpa [searchCounter] using this
  | succ f ih =>
    intro c t hc hinv
    rw [searchCounter_succ]
    refine (encTrial lay tau e M u hmem c t hinv _ (2 + ((f + 1) * 40 + 2)) ?_).mono
      (by ring_nf; omega) (fun _ _ h => h)
    intro t' tpc t6 tregs tframe
    obtain ⟨t'', hs, hinv', -⟩ := encNext u hmem.x7 c (by omega) t' tpc t6 tregs tframe
    exact Sim.steps hs (ih (c + 1) t'' (by omega) (hinv' (by omega)))

end SigGolfCandidate.Packed.Sign

