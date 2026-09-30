import SigGolfCandidate.Packed.Radix27ImagesExpand
import SigGolfCandidate.Rv.Steps
/-! Auto-collected 13-byte codec certificate. Each section preserves a checked scratch module. -/


section -- SignClone13.Pair

/-! ### cloned Pair -/

/-!
# Paired PRF secrets (SPEC-v5)

One seed-derivation query `prf2 x` yields two 16-byte secrets: the low and the high half of the
32-byte answer. The programs query on even items into `SEC = EO = 0x140` (32 bytes) and copy the
half `SEC + 16 (i & 1)` for item `i`.

* `prf2_eq` : `prf2 x = H x >>= fun a => pure (answerBytes 16 a, hiVal a)`.
* `sec_lo` / `sec_hi` : the two halves as dwords at `SEC` / `SEC + 16` after the query.
* `and_one_ofNat`, `secAddr` : the address `SEC + 16 (i & 1)`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace SigGolfCandidate.Radix27Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

/-- The high 16 bytes of an answer. -/
def hiVal (a : BitVec 256) : Val := valOfWords (a.extractLsb' 128 64) (a.extractLsb' 192 64)

theorem answerBytes_32_take (a : BitVec 256) : (answerBytes 32 a).take 16 = answerBytes 16 a := by
  unfold answerBytes
  rw [← List.map_take, List.take_range, Nat.min_eq_left (by norm_num)]

theorem answerBytes_32_drop (a : BitVec 256) : (answerBytes 32 a).drop 16 = hiVal a := by
  rw [answerBytes_32, hiVal, valOfWords]
  simp only [List.append_assoc]
  rw [show (16 : Nat) = (bytesOfWord (a.extractLsb' 0 64) ++ bytesOfWord (a.extractLsb' 64 64)).length by simp,
    ← List.append_assoc, List.drop_left]

theorem prf2_eq (x : List Byte) :
    prf2 x = H x >>= fun a => pure (answerBytes 16 a, hiVal a) := by
  unfold prf2
  simp only [answerBytes_32_take, answerBytes_32_drop]

@[simp] theorem length_hiVal (a : BitVec 256) : (hiVal a).length = 16 := by simp [hiVal]

theorem sec_lo (s : MachineState) (a : BitVec 256) (h12 : s.getReg .x12 = BitVec.ofNat 64 0x140) :
    (writeHash s a).readWords (BitVec.ofNat 64 0x140) 2 = wordsOf (answerBytes 16 a) :=
  writeHash_readWords_val s a _ h12 (by norm_num)

theorem sec_hi (s : MachineState) (a : BitVec 256) (h12 : s.getReg .x12 = BitVec.ofNat 64 0x140) :
    (writeHash s a).readWords (BitVec.ofNat 64 0x150) 2 = wordsOf (hiVal a) := by
  rw [readWords_ofNat_two, writeHash_getMem_ofNat _ _ _ _ h12 (by norm_num) (by norm_num),
    writeHash_getMem_ofNat _ _ _ _ h12 (by norm_num) (by norm_num), hiVal, wordsOf_valOfWords]
  simp

theorem and_one_ofNat (j : Nat) (hj : j < 2 ^ 64) :
    BitVec.ofNat 64 j &&& 1#64 = BitVec.ofNat 64 (j % 2) := by
  apply BitVec.eq_of_toNat_eq
  have h1 : (1#64 : Word).toNat = 2 ^ 1 - 1 := rfl
  rw [BitVec.toNat_and, h1, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj,
    Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem secAddr (j : Nat) (hj : j < 2 ^ 64) (o : Nat) (ho : o < 2 ^ 32) :
    (BitVec.ofNat 64 j &&& 1#64) <<< ((4#64).toNat % 64) + BitVec.ofNat 64 o =
      BitVec.ofNat 64 (o + 16 * (j % 2)) := by
  rw [and_one_ofNat j hj]
  apply BitVec.eq_of_toNat_eq
  have h2 : j % 2 < 2 := Nat.mod_lt _ (by norm_num)
  rw [show (4#64 : Word).toNat % 64 = 4 from rfl]
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (a := j % 2) (by omega), Nat.mod_eq_of_lt (a := o) (by omega)]
  omega

end SigGolfCandidate.Radix27Sign



end


section -- SignClone13.ForsLeaf

/-! ### cloned ForsLeaf -/

/-!
# `sign`, FORS leaves (`fors_leaf_loop`, instructions 120 .. 139)

`forsLeaves_sim` : from `fors_leaf_loop` with `J = 0`, the machine refines
`buildFtsLeaves S k idx 10 u`: leaf `j` is stored at `FA + 16 j`, the secret of leaf `u` at
`SIGL + 16`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace SigGolfCandidate.Radix27Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref


/-- The (fixed) facts at the start of the leaf loop of tree `k`. -/
structure LeafCtx (S : List Byte) (k idx u : Nat) (t0 : MachineState) : Prop where
  pb0 : t0.getMem (BitVec.ofNat 64 0x6A0) = twWord0 8 k idx 0
  pb8 : lo32 (t0.getMem (BitVec.ofNat 64 0x6A8)) = BitVec.ofNat 32 idx
  pbP : t0.readWords (BitVec.ofNat 64 0x6B0) 2 = [0, 0]
  pbS : t0.readWords (BitVec.ofNat 64 0x6C0) 4 = wordsOf S
  cb0 : t0.getMem (BitVec.ofNat 64 0xC0) = twWord0 9 k idx 0
  cb8 : lo32 (t0.getMem (BitVec.ofNat 64 0xC8)) = BitVec.ofNat 32 idx
  cbP : t0.readWords (BitVec.ofNat 64 0xD0) 2 = [0, 0]
  cbZ : t0.readWords (BitVec.ofNat 64 0xF0) 2 = [0, 0]
  x5 : t0.getReg .x5 = 0
  x13 : t0.getReg .x13 = BitVec.ofNat 64 u
  x18 : t0.getReg .x18 = BitVec.ofNat 64 (0x2650 + 176 * k)
  x19 : t0.getReg .x19 = BitVec.ofNat 64 0x30000

/-- Addresses written by the leaf loop of tree `k`. -/
def leafW (k : Nat) (a : Nat) : Prop :=
  a = 0x6A8 ∨ a = 0xC8 ∨ (0xE0 ≤ a ∧ a < 0xF0) ∨ (0x140 ≤ a ∧ a < 0x160) ∨
    (0x30000 ≤ a ∧ a < 0x30000 + 16 * 1025) ∨
    a = 0x2650 + 176 * k + 16 ∨ a = 0x2650 + 176 * k + 24

def leafRegs : List Reg := [.x1, .x2, .x3, .x9, .x10, .x11, .x12]

/-- Invariant after `j` leaves. -/
def LeafInv (k u : Nat) (t0 : MachineState) (j : Nat) (st : List Val × Val) (t : MachineState) : Prop :=
  j ≤ 1024 ∧ st.1.length = j ∧ (∀ v ∈ st.1, v.length = 16) ∧ Slots t 0x30000 st.1 ∧
  (u < j → st.2.length = 16 ∧ t.readWords (BitVec.ofNat 64 (0x2650 + 176 * k + 16)) 2 = wordsOf st.2) ∧
  t.pc = (if j < 1024 then pcOf 164 else pcOf 191) ∧ t.getReg .x9 = BitVec.ofNat 64 j ∧
  RegsEq t0 t leafRegs ∧ Frame t0 t (leafW k) ∧
  lo32 (t.getMem (BitVec.ofNat 64 0x6A8)) = lo32 (t0.getMem (BitVec.ofNat 64 0x6A8)) ∧
  lo32 (t.getMem (BitVec.ofNat 64 0xC8)) = lo32 (t0.getMem (BitVec.ofNat 64 0xC8))

/-- From `fors_nocap` (instruction 132): the leaf hash and the loop step. -/
theorem forsLeaf_tail (S : List Byte) (k idx u : Nat) (hk : k < 14) (hidx : idx < 2 ^ 34) (hu : u < 1024)
    (t0 : MachineState) (ctx : LeafCtx S k idx u t0) (j : Nat) (hj : j < 1024)
    (acc : List Val) (hlen : acc.length = j) (hvals : ∀ v ∈ acc, v.length = 16) (s cap : Val)
    (hs : s.length = 16) (t : MachineState) (tpc : t.pc = pcOf 183)
    (t9 : t.getReg .x9 = BitVec.ofNat 64 j) (t11 : t.getReg .x11 = BitVec.ofNat 64 64)
    (tregs : RegsEq t0 t leafRegs) (tframe : Frame t0 t (leafW k))
    (tlo1 : lo32 (t.getMem (BitVec.ofNat 64 0x6A8)) = lo32 (t0.getMem (BitVec.ofNat 64 0x6A8)))
    (tlo2 : lo32 (t.getMem (BitVec.ofNat 64 0xC8)) = lo32 (t0.getMem (BitVec.ofNat 64 0xC8)))
    (tsv : t.readWords (BitVec.ofNat 64 0xE0) 2 = wordsOf s)
    (tz : t.readWords (BitVec.ofNat 64 0xF0) 2 = [0, 0]) (hslots : Slots t 0x30000 acc)
    (hcap : u < j + 1 → cap.length = 16 ∧
      t.readWords (BitVec.ofNat 64 (0x2650 + 176 * k + 16)) 2 = wordsOf cap) :
    Sim image t 15 (hash16 (ftsLeafInput k idx j s) >>= fun leaf => pure (acc ++ [leaf], cap))
      (fun r t' => LeafInv k u t0 (j + 1) r t' ∧ t'.getReg .x11 = BitVec.ofNat 64 64 ∧
        ∀ x, x < 2 ^ 64 → 0x140 ≤ x → x < 0x160 →
        t'.getMem (BitVec.ofNat 64 x) = t.getMem (BitVec.ofNat 64 x)) := by
  have tx5 : t.getReg .x5 = 0 := by rw [tregs.get .x5 (by simp [leafRegs]), ctx.x5]
  have tx19 : t.getReg .x19 = BitVec.ofNat 64 0x30000 := by
    rw [tregs.get .x19 (by simp [leafRegs]), ctx.x19]
  have hs1 := symRun_sound blk183 codeAt_183 t tpc (by simp only [blk183.res, rv_simp])
  have hc1 : blk183.res.cycles = 4 := rfl
  rw [hc1] at hs1
  set t1 := blk183.res.toState t with ht1
  have f1 : Frame t t1 (fun x => x = 0xC8) := by
    apply frame_toState; intro x hx hW
    simp only [blk183.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq, ofNat_eq_iff]
    omega
  have r1 : RegsEq t t1 [.x3, .x10, .x12] := by
    intro r hr; rw [ht1, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have e1 := symRun_ecall blk183 codeAt_183 t (by simp only [blk183.res, rv_simp]) rfl
  have x10 : t1.getReg .x10 = BitVec.ofNat 64 0xC0 := by simp only [ht1, blk183.res, rv_simp]
  have x11 : t1.getReg .x11 = BitVec.ofNat 64 64 := by rw [r1.get .x11, t11]
  have x12 : t1.getReg .x12 = BitVec.ofNat 64 (0x30000 + 16 * j) := by
    rvs [ht1, blk183.res, t9, tx19]; congr 1; ring
  have x5 : t1.getReg .x5 = 0 := by rw [r1.get .x5, tx5]
  have pc1 : t1.pc = pcOf 187 := by simp only [ht1, blk183.res, rv_simp]
  have mC8 : t1.getMem (BitVec.ofNat 64 0xC8) =
      BitVec.ofNat 64 (idx % 2 ^ 32 + 2 ^ 32 * (j % 2 ^ 32)) := by
    rvs [ht1, blk183.res, t9]
    exact word_of_halves _ idx j (by rw [lo32_replace1, tlo2, ctx.cb8]) (by rw [hi32_replace1])
  have hq : hashInput t1 = pad64 (ftsLeafInput k idx j s) := by
    obtain ⟨hn, hw⟩ := words_th16 9 k idx 0 j s hs
    refine hashInput_eq_pad64 t1 _ 0 hn (by rw [x11]) (by norm_num) (by rw [x10]; decide) ?_
    rw [ftsLeafInput, hw, x10, show 8 * (0 + 1) = 1 + 1 + 2 + 2 + 2 from rfl]
    rw [readWords_ofNat_add, readWords_ofNat_add, readWords_ofNat_add, readWords_ofNat_add]
    simp only [Nat.reduceMul, Nat.reduceAdd]
    rw [readWords_ofNat_one, readWords_ofNat_one, mC8, f1.getMem (by norm_num) (by norm_num),
      tframe.getMem (by norm_num) (by simp only [leafW]; omega), ctx.cb0,
      f1.readWords _ _ (by norm_num) (by intro i hi; omega),
      f1.readWords _ _ (by norm_num) (by intro i hi; omega),
      f1.readWords _ _ (by norm_num) (by intro i hi; omega),
      tframe.readWords _ _ (by norm_num) (by intro i hi; simp only [leafW]; omega), ctx.cbP, tsv, tz]
    simp [twWords_eq]
  have hb : (pad64 (ftsLeafInput k idx j s)).blocks = 1 :=
    congrArg (· + 1) (words_th16 9 k idx 0 j s hs).1
  refine (Sim.steps hs1 (Sim.hash16_bind (W := 3) e1 x5
    (hashArgs_of x10 x11 x12 (by norm_num) (by norm_num) (by norm_num) (by omega) (by omega)
      (by norm_num)) hq (fmt_thInput _ _ _ _ _ _ (by decide)) (fun a => ?_))).mono (by rw [hb]) (fun _ _ h => h)
  set t2 := writeHash t1 a with ht2
  have f2 : Frame t1 t2 (fun x => 0x30000 + 16 * j ≤ x ∧ x < 0x30000 + 16 * j + 32) :=
    frame_writeHash t1 a _ x12 (by omega)
  have v2 : t2.readWords (BitVec.ofNat 64 (0x30000 + 16 * j)) 2 = wordsOf (answerBytes 16 a) :=
    writeHash_readWords_val t1 a _ x12 (by omega)
  have pc2 : t2.pc = pcOf 188 := by rw [ht2, writeHash_pc, pc1]; apply BitVec.eq_of_toNat_eq; simp
  have hs2 := symRun_sound blk188 codeAt_188 t2 pc2 (by simp only [blk188.res, rv_simp])
  have hc2 : blk188.res.cycles = 3 := rfl
  rw [hc2] at hs2
  set t3 := blk188.res.toState t2 with ht3
  have f3 : Frame t2 t3 (fun _ => False) := by
    apply frame_toState; intro x hx hW; simp [blk188.res]
  have r3 : RegsEq t2 t3 [.x3, .x9] := by
    intro r hr; rw [ht3, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have t29 : t2.getReg .x9 = BitVec.ofNat 64 j := by rw [ht2, writeHash_getReg, r1.get .x9, t9]
  have ftot : Frame t t3 (fun x => x = 0xC8 ∨ (0x30000 + 16 * j ≤ x ∧ x < 0x30000 + 16 * j + 32)) :=
    ((f1.trans f2).trans f3).mono (by intro x hx; (try simp only [or_false] at hx ⊢); omega)
  refine Sim.pure_steps hs2 ⟨⟨by omega, by simp [hlen], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    by rw [r3.get .x11, ht2, writeHash_getReg, x11], fun x hx h1 h2 => ftot.getMem hx (by omega)⟩
  · intro v hv; rcases List.mem_append.mp hv with hv | hv
    · exact hvals v hv
    · simp at hv; subst hv; simp
  · apply Slots.snoc
    · exact hslots.frame ftot (by omega) (by intro i hi; constructor <;> ((try simp only); omega))
    · rw [hlen, f3.readWords _ _ (by omega) (by simp), v2]
  · intro h
    obtain ⟨h1, h2⟩ := hcap h
    refine ⟨h1, ?_⟩
    rw [ftot.readWords _ _ (by omega) (by intro i hi; omega), h2]
  · simp only [ht3, blk188.res, rv_simp, t29, ofNat_add_ofNat, ofNat_bne_ofNat]
    by_cases h : j + 1 < 1024
    · rw [if_pos (by simp; omega), if_pos h]
    · rw [if_neg (by simp; omega), if_neg h]
  · simp only [ht3, blk188.res, rv_simp, t29, ofNat_add_ofNat]
  · exact ((((tregs.trans r1).trans (regsEq_writeHash _ _ [])).trans r3)).mono (by decide)
  · exact (tframe.trans ftot).mono (by intro x hx; simp only [leafW] at hx ⊢; omega)
  · rw [ftot.getMem (by norm_num) (by omega), tlo1]
  · rw [f3.getMem (by norm_num) (by simp), f2.getMem (by norm_num) (by omega)]
    rvs [ht1, blk183.res, t9]
    rw [lo32_replace1, tlo2]

/-- From `prf_have` (instruction 169) for leaf `j` whose secret `s` sits at `SEC + 16 (j & 1)`: the
copy to `CB+32`, the capture, the leaf hash, the loop step. -/
theorem forsLeaf_B (S : List Byte) (k idx u : Nat) (hk : k < 14) (hidx : idx < 2 ^ 34) (hu : u < 1024)
    (t0 : MachineState) (ctx : LeafCtx S k idx u t0) (j : Nat) (hj : j < 1024)
    (acc : List Val) (hlen : acc.length = j) (hvals : ∀ v ∈ acc, v.length = 16) (s cap : Val)
    (hs : s.length = 16) (t : MachineState) (tpc : t.pc = pcOf 172)
    (t9 : t.getReg .x9 = BitVec.ofNat 64 j) (t11 : t.getReg .x11 = BitVec.ofNat 64 64)
    (hsec : t.readWords (BitVec.ofNat 64 (0x140 + 16 * (j % 2))) 2 = wordsOf s)
    (hslots : Slots t 0x30000 acc)
    (hcap : u < j → cap.length = 16 ∧ t.readWords (BitVec.ofNat 64 (0x2650 + 176 * k + 16)) 2 = wordsOf cap)
    (tregs : RegsEq t0 t leafRegs) (tframe : Frame t0 t (leafW k))
    (tlo1 : lo32 (t.getMem (BitVec.ofNat 64 0x6A8)) = lo32 (t0.getMem (BitVec.ofNat 64 0x6A8)))
    (tlo2 : lo32 (t.getMem (BitVec.ofNat 64 0xC8)) = lo32 (t0.getMem (BitVec.ofNat 64 0xC8))) :
    Sim image t 26 (hash16 (ftsLeafInput k idx j s) >>= fun leaf => pure (acc ++ [leaf], if j = u then s else cap))
      (fun r t' => LeafInv k u t0 (j + 1) r t' ∧ t'.getReg .x11 = BitVec.ofNat 64 64 ∧
        ∀ x, x < 2 ^ 64 → 0x140 ≤ x → x < 0x160 →
        t'.getMem (BitVec.ofNat 64 x) = t.getMem (BitVec.ofNat 64 x)) := by
  have tx13 : t.getReg .x13 = BitVec.ofNat 64 u := by rw [tregs.get .x13 (by simp [leafRegs]), ctx.x13]
  have tx18 : t.getReg .x18 = BitVec.ofNat 64 (0x2650 + 176 * k) := by
    rw [tregs.get .x18 (by simp [leafRegs]), ctx.x18]
  have hj2 : j % 2 < 2 := Nat.mod_lt _ (by norm_num)
  -- block 169: copy the secret to CB+32, test J = U
  have hs3 := symRun_sound blk172 codeAt_172 t tpc (by
    simp only [blk172.res, rv_simp, t9]; rw [secAddr j (by omega) 328 (by norm_num), secAddr j (by omega) 320 (by norm_num)]
    simp only [accessValid_ofNat]; omega)
  have hc3 : blk172.res.cycles = 7 := rfl
  rw [hc3] at hs3
  set t3 := blk172.res.toState t with ht3
  have f3 : Frame t t3 (fun x => x = 0xE0 ∨ x = 0xE8) := by
    apply frame_toState; intro x hx hW
    simp only [blk172.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq, ofNat_eq_iff]
    omega
  have r3 : RegsEq t t3 [.x1, .x2, .x3] := by
    intro r hr; rw [ht3, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have x39 : t3.getReg .x9 = BitVec.ofNat 64 j := by rw [r3.get .x9, t9]
  have x311 : t3.getReg .x11 = BitVec.ofNat 64 64 := by rw [r3.get .x11, t11]
  have v3 : t3.readWords (BitVec.ofNat 64 0xE0) 2 = wordsOf s := by
    rw [← hsec, readWords_ofNat_two, readWords_ofNat_two]
    simp only [ht3, blk172.res, rv_simp, t9]
    rw [secAddr j (by omega) 328 (by norm_num), secAddr j (by omega) 320 (by norm_num)]
    simp (config := { decide := true }) only [↓reduceIte]
    rw [show 328 + 16 * (j % 2) = 0x140 + 16 * (j % 2) + 8 by omega]
  have pc3 : t3.pc = if j = u then pcOf 179 else pcOf 183 := by
    simp only [ht3, blk172.res, rv_simp, t9, tx13, ofNat_bne_ofNat]
    by_cases h : j = u
    · rw [if_pos h, if_neg (by simp; omega)]
    · rw [if_neg h, if_pos (by simp; omega)]
  have ft3 : Frame t0 t3 (leafW k) := (tframe.trans f3).mono (by
    intro x hx; simp only [leafW] at hx ⊢; omega)
  have rt3 : RegsEq t0 t3 leafRegs := (tregs.trans r3).mono (by decide)
  have z3 : t3.readWords (BitVec.ofNat 64 0xF0) 2 = [0, 0] := by
    rw [ft3.readWords _ _ (by norm_num) (by intro i hi; simp only [leafW]; omega), ctx.cbZ]
  have lo3a : lo32 (t3.getMem (BitVec.ofNat 64 0x6A8)) = lo32 (t0.getMem (BitVec.ofNat 64 0x6A8)) := by
    rw [f3.getMem (by norm_num) (by omega), tlo1]
  have lo3b : lo32 (t3.getMem (BitVec.ofNat 64 0xC8)) = lo32 (t0.getMem (BitVec.ofNat 64 0xC8)) := by
    rw [f3.getMem (by norm_num) (by omega), tlo2]
  have hslots3 : Slots t3 0x30000 acc := hslots.frame f3 (by omega)
    (by intro i hi; constructor <;> omega)
  have sec3 : ∀ x, x < 2 ^ 64 → 0x140 ≤ x → x < 0x160 →
      t3.getMem (BitVec.ofNat 64 x) = t.getMem (BitVec.ofNat 64 x) := fun x hx h1 h2 =>
    f3.getMem hx (by omega)
  by_cases hju : j = u
  · -- capture
    have hs4 := symRun_sound blk179 codeAt_179 t3 (by rw [pc3, if_pos hju]) (by
      simp only [blk179.res, rv_simp, r3.get .x18, tx18,
        ofNat_add_ofNat, accessValid_ofNat, Nat.reducePow]
      bvomega)
    have hc4 : blk179.res.cycles = 4 := rfl
    rw [hc4] at hs4
    set t4 := blk179.res.toState t3 with ht4
    have t318 : t3.getReg .x18 = BitVec.ofNat 64 (0x2650 + 176 * k) := by rw [r3.get .x18, tx18]
    have f4 : Frame t3 t4 (fun x => x = 0x2650 + 176 * k + 16 ∨ x = 0x2650 + 176 * k + 24) := by
      apply frame_toState; intro x hx hW
      simp only [blk179.res, rv_simp, t318, ofNat_add_ofNat, List.forall_mem_cons, List.not_mem_nil,
        IsEmpty.forall_iff, implies_true, and_true, ne_eq, ofNat_eq_iff]
      omega
    have r4 : RegsEq t3 t4 [.x1, .x2] := by
      intro r hr; rw [ht4, Result.toState_getReg]
      cases r <;> first | exact absurd (by decide) hr | rfl
    have sig4 : t4.readWords (BitVec.ofNat 64 (0x2650 + 176 * k + 16)) 2 = wordsOf s := by
      rw [← v3, readWords_ofNat_two, readWords_ofNat_two]
      simp only [ht4, blk179.res, rv_simp, t318, ofNat_add_ofNat, ofNat_eq_iff]
      simp (disch := bvomega) only [if_pos, if_neg, if_true, Nat.reduceAdd]
    have := forsLeaf_tail S k idx u hk hidx hu t0 ctx j hj acc hlen hvals s s hs t4
      (by simp only [ht4, blk179.res, rv_simp])
      (by rw [r4.get .x9, x39]) (by rw [r4.get .x11, x311])
      (rt3.trans r4 |>.mono (by decide))
      ((ft3.trans f4).mono (by
        intro x hx; (try simp only [or_false] at hx ⊢); simp only [leafW] at hx ⊢; omega))
      (by rw [f4.getMem (by norm_num) (by omega), lo3a])
      (by rw [f4.getMem (by norm_num) (by omega), lo3b])
      (by rw [f4.readWords _ _ (by norm_num) (by intro i hi; omega), v3])
      (by rw [f4.readWords _ _ (by norm_num) (by intro i hi; omega), z3])
      (hslots3.frame f4 (by omega) (by intro i hi; constructor <;> ((try simp only); omega)))
      (fun _ => ⟨hs, sig4⟩)
    rw [if_pos hju]
    exact (Sim.steps hs3 (Sim.steps hs4 this)).mono (by norm_num) (fun _ _ h => ⟨h.1, h.2.1, fun x hx h1 h2 => by
      rw [h.2.2 x hx h1 h2, f4.getMem hx (by omega), sec3 x hx h1 h2]⟩)
  · have := forsLeaf_tail S k idx u hk hidx hu t0 ctx j hj acc hlen hvals s cap hs t3
      (by rw [pc3, if_neg hju]) x39 x311 rt3 ft3 lo3a lo3b v3 z3 hslots3
      (fun h => by
        obtain ⟨h1, h2⟩ := hcap (by omega)
        exact ⟨h1, by rw [f3.readWords _ _ (by omega) (by intro i hi; omega), h2]⟩)
    rw [if_neg hju]
    exact (Sim.steps hs3 this).mono (by norm_num) (fun _ _ h => ⟨h.1, h.2.1, fun x hx h1 h2 => by
      rw [h.2.2 x hx h1 h2, sec3 x hx h1 h2]⟩)

theorem LeafInv.init (k u : Nat) (t0 : MachineState) (hpc : t0.pc = pcOf 164)
    (h9 : t0.getReg .x9 = BitVec.ofNat 64 0) : LeafInv k u t0 0 ([], []) t0 :=
  ⟨by norm_num, rfl, by simp, Slots.nil _ _, fun h => absurd h (by omega), by simpa using hpc, h9,
    RegsEq.refl _ _, Frame.refl _ _, rfl, rfl⟩

end SigGolfCandidate.Radix27Sign

namespace SigGolfCandidate.Radix27Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

theorem fors_pair_spec (S : List Byte) (k idx u p : Nat) (st : List Val × Val) :
    (do
      let (s0, s1) ← prf2 (ftsPrfInput S k idx p)
      let l0 ← hash16 (ftsLeafInput k idx (2 * p) s0)
      let l1 ← hash16 (ftsLeafInput k idx (2 * p + 1) s1)
      pure (st.1 ++ [l0, l1], if 2 * p = u then s0 else if 2 * p + 1 = u then s1 else st.2) :
        OracleComp HashSpec (List Val × Val)) =
    H (ftsPrfInput S k idx p) >>= fun a =>
      (hash16 (ftsLeafInput k idx (2 * p) (answerBytes 16 a)) >>= fun l0 =>
        pure (st.1 ++ [l0], if 2 * p = u then answerBytes 16 a else st.2)) >>= fun r =>
      hash16 (ftsLeafInput k idx (2 * p + 1) (hiVal a)) >>= fun l1 =>
        pure (r.1 ++ [l1], if 2 * p + 1 = u then hiVal a else r.2) := by
  simp only [prf2_eq, bind_assoc, pure_bind, List.append_assoc, List.cons_append, List.nil_append]
  congr 1; funext a; congr 1; funext l0; congr 1; funext l1
  congr 2
  by_cases h1 : 2 * p = u
  · rw [if_pos h1, if_neg (by omega), if_pos h1]
  · rw [if_neg h1, if_neg h1]

theorem forsLeaf_pair (S : List Byte) (hS : S.length = 32) (k idx u : Nat) (hk : k < 14)
    (hidx : idx < 2 ^ 34) (hu : u < 1024) (t0 : MachineState) (ctx : LeafCtx S k idx u t0)
    (p : Nat) (hp : p < 512) (st : List Val × Val) (t : MachineState)
    (hinv : LeafInv k u t0 (2 * p) st t) :
    Sim image t 70 (do
        let (s0, s1) ← prf2 (ftsPrfInput S k idx p)
        let l0 ← hash16 (ftsLeafInput k idx (2 * p) s0)
        let l1 ← hash16 (ftsLeafInput k idx (2 * p + 1) s1)
        pure (st.1 ++ [l0, l1], if 2 * p = u then s0 else if 2 * p + 1 = u then s1 else st.2))
      (LeafInv k u t0 (2 * p + 2)) := by
  rw [fors_pair_spec]
  obtain ⟨-, hlen, hvals, hslots, hcap, tpc, t9, tregs, tframe, tlo1, tlo2⟩ := hinv
  have tpc' : t.pc = pcOf 164 := by rw [tpc, if_pos (by omega)]
  have tx5 : t.getReg .x5 = 0 := by rw [tregs.get .x5 (by simp [leafRegs]), ctx.x5]
  -- block 161: even
  have hs0 := symRun_sound blk164 codeAt_164 t tpc' (by simp only [blk164.res, rv_simp])
  have hc0 : blk164.res.cycles = 2 := rfl
  rw [hc0] at hs0
  set t1 := blk164.res.toState t with ht1
  have m1 : ∀ z, t1.getMem z = t.getMem z := fun z => by
    rw [ht1, Result.toState_getMem, show blk164.res.st.mem = [] from rfl, memEval_nil]
  have r1 : RegsEq t t1 [.x3] := by
    intro r hr; rw [ht1, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have pc1 : t1.pc = pcOf 166 := by
    simp only [ht1, blk164.res, rv_simp, t9]
    rw [and_one_ofNat _ (by omega), if_neg (by rw [ofNat_bne_ofNat]; simp)]
  -- block 163: the paired prf query
  have hs2 := symRun_sound blk166 codeAt_166 t1 pc1 (by simp only [blk166.res, rv_simp])
  have hc2 : blk166.res.cycles = 5 := rfl
  rw [hc2] at hs2
  set t2 := blk166.res.toState t1 with ht2
  have f2 : Frame t1 t2 (fun x => x = 0x6A8) := by
    apply frame_toState; intro x hx hW
    simp only [blk166.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq, ofNat_eq_iff]
    omega
  have r2 : RegsEq t1 t2 [.x3, .x10, .x11, .x12] := by
    intro r hr; rw [ht2, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have e2 := symRun_ecall blk166 codeAt_166 t1 (by simp only [blk166.res, rv_simp]) rfl
  have x10 : t2.getReg .x10 = BitVec.ofNat 64 0x6A0 := by simp only [ht2, blk166.res, rv_simp]
  have x11 : t2.getReg .x11 = BitVec.ofNat 64 64 := by simp only [ht2, blk166.res, rv_simp]
  have x12 : t2.getReg .x12 = BitVec.ofNat 64 0x140 := by simp only [ht2, blk166.res, rv_simp]
  have x5 : t2.getReg .x5 = 0 := by rw [r2.get .x5, r1.get .x5, tx5]
  have pc2 : t2.pc = pcOf 171 := by simp only [ht2, blk166.res, rv_simp]
  have t19 : t1.getReg .x9 = BitVec.ofNat 64 (2 * p) := by rw [r1.get .x9, t9]
  have m6A8 : t2.getMem (BitVec.ofNat 64 0x6A8) =
      BitVec.ofNat 64 (idx % 2 ^ 32 + 2 ^ 32 * (p % 2 ^ 32)) := by
    simp only [ht2, blk166.res, rv_simp, t19]
    bvsimp []
    rw [show 2 * p / 2 = p by omega]
    refine (word_of_halves _ idx p ?_ ?_).trans (ofNat_congr (by omega))
    · rw [lo32_replace1, m1, tlo1, ctx.pb8]
    · rw [hi32_replace1]
  have ft2 : Frame t t2 (fun x => x = 0x6A8) := fun z hz hW => by rw [f2.getMem hz hW, m1]
  have hq : hashInput t2 = pad64 (ftsPrfInput S k idx p) := by
    obtain ⟨hn, hw⟩ := words_ftsPrfInput S hS k idx p
    refine hashInput_eq_pad64 t2 _ 0 hn (by rw [x11]) (by norm_num) (by rw [x10]; decide) ?_
    rw [hw, x10, show 8 * (0 + 1) = 1 + 1 + 2 + 4 from rfl]
    rw [readWords_ofNat_add, readWords_ofNat_add, readWords_ofNat_add]
    simp only [Nat.reduceMul, Nat.reduceAdd]
    rw [readWords_ofNat_one, readWords_ofNat_one, m6A8, ft2.getMem (by norm_num) (by norm_num),
      tframe.getMem (by norm_num) (by simp only [leafW]; omega), ctx.pb0,
      ft2.readWords _ _ (by norm_num) (by intro i hi; omega),
      ft2.readWords _ _ (by norm_num) (by intro i hi; omega),
      tframe.readWords _ _ (by norm_num) (by intro i hi; simp only [leafW]; omega),
      tframe.readWords _ _ (by norm_num) (by intro i hi; simp only [leafW]; omega), ctx.pbP, ctx.pbS]
    simp [twWords_eq]
  have hb : (pad64 (ftsPrfInput S k idx p)).blocks = 1 := by
    simp [pad64, Query.blocks, (words_ftsPrfInput S hS k idx p).1]
  refine (Sim.steps hs0 (Sim.steps hs2 (Sim.query_bind (W := 26 + (2 + 26)) e2 x5
    (hashArgs_of x10 x11 x12 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)) (hq.trans (fmt_thInput _ _ _ _ _ _ (by decide)).symm) (fun a => ?_)))).mono
    (by rw [show ftsPrfInput S k idx p = thInput (tweak 8 k idx 0 p) S from rfl] at *; rw [blocks_fmt_th _ _ _ _ _ _ (by decide)]; rw [hb]; norm_num)
    (fun _ _ h => h)
  set t3 := writeHash t2 a with ht3
  have f3 : Frame t2 t3 (fun x => 0x140 ≤ x ∧ x < 0x140 + 32) := frame_writeHash t2 a _ x12 (by norm_num)
  have pc3 : t3.pc = pcOf 172 := by rw [ht3, writeHash_pc, pc2]; apply BitVec.eq_of_toNat_eq; simp
  have g3 : ∀ q, t3.getReg q = t2.getReg q := fun q => by rw [ht3, writeHash_getReg]
  have ft3 : Frame t t3 (fun x => x = 0x6A8 ∨ (0x140 ≤ x ∧ x < 0x140 + 32)) := ft2.trans f3
  have rt3 : RegsEq t0 t3 leafRegs := ((tregs.trans r1).trans r2 |>.trans
    (show RegsEq t2 t3 [] from fun q _ => g3 q)).mono (by decide)
  have lo3 : lo32 (t3.getMem (BitVec.ofNat 64 0x6A8)) = lo32 (t0.getMem (BitVec.ofNat 64 0x6A8)) := by
    rw [f3.getMem (by norm_num) (by omega), m6A8, ctx.pb8, lo32_ofNat]
    apply BitVec.eq_of_toNat_eq; simp
  have hA := forsLeaf_B S k idx u hk hidx hu t0 ctx (2 * p) (by omega) st.1 hlen hvals (answerBytes 16 a)
    st.2 (by simp) t3 pc3 (by rw [g3, r2.get .x9, t19]) (by rw [g3, x11])
    (by rw [show 0x140 + 16 * (2 * p % 2) = 0x140 by omega]; exact sec_lo t2 a x12)
    (hslots.frame ft3 (by omega) (by intro i hi; constructor <;> omega))
    (fun h => by
      obtain ⟨h1, h2⟩ := hcap h
      exact ⟨h1, by rw [ft3.readWords _ _ (by omega) (by intro i hi; omega), h2]⟩)
    rt3 ((tframe.trans ft3).mono (by intro x hx; simp only [leafW] at hx ⊢; omega)) lo3
    (by rw [ft3.getMem (by norm_num) (by omega), tlo2])
  refine Sim.bind hA (fun r t4 h4 => ?_)
  obtain ⟨⟨-, hlen4, hvals4, hslots4, hcap4, tpc4, t49, tregs4, tframe4, tlo14, tlo24⟩, x411, sec4⟩ := h4
  -- block 161: odd
  have hs5 := symRun_sound blk164 codeAt_164 t4 (by rw [tpc4, if_pos (by omega)])
    (by simp only [blk164.res, rv_simp])
  have hc5 : blk164.res.cycles = 2 := rfl
  rw [hc5] at hs5
  set t5 := blk164.res.toState t4 with ht5
  have m5 : ∀ z, t5.getMem z = t4.getMem z := fun z => by
    rw [ht5, Result.toState_getMem, show blk164.res.st.mem = [] from rfl, memEval_nil]
  have r5 : RegsEq t4 t5 [.x3] := by
    intro r hr; rw [ht5, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have pc5 : t5.pc = pcOf 172 := by
    simp only [ht5, blk164.res, rv_simp, t49]
    rw [and_one_ofNat _ (by omega), if_pos (by rw [ofNat_bne_ofNat]; simp)]
  have fr5 : Frame t4 t5 (fun _ => False) := fun z _ _ => m5 _
  have hB := forsLeaf_B S k idx u hk hidx hu t0 ctx (2 * p + 1) (by omega) r.1 hlen4 hvals4 (hiVal a)
    r.2 (by simp) t5 pc5 (by rw [r5.get .x9, t49]) (by rw [r5.get .x11, x411])
    (by
      rw [show 0x140 + 16 * ((2 * p + 1) % 2) = 0x150 by omega, readWords_ofNat_two, m5, m5,
        sec4 _ (by norm_num) (by norm_num) (by norm_num), sec4 _ (by norm_num) (by norm_num) (by norm_num),
        ← readWords_ofNat_two]
      exact sec_hi t2 a x12)
    (hslots4.frame fr5 (by omega) (by simp))
    (fun h => by
      obtain ⟨h1, h2⟩ := hcap4 h
      exact ⟨h1, by rw [fr5.readWords _ _ (by omega) (by simp), h2]⟩)
    ((tregs4.trans r5).mono (by decide)) ((tframe4.trans fr5).mono (by intro x hx; rcases hx with h | h; exact h; exact h.elim))
    (by rw [m5, tlo14]) (by rw [m5, tlo24])
  exact (Sim.steps hs5 hB).mono (by norm_num) (fun _ _ h => h.1)

/-- **FORS leaves** of tree `k` (pairs `p = 0 .. 511`). -/
theorem forsLeaves_sim (S : List Byte) (hS : S.length = 32) (k idx u : Nat) (hk : k < 14)
    (hidx : idx < 2 ^ 34) (hu : u < 1024) (t0 : MachineState) (ctx : LeafCtx S k idx u t0)
    (hpc : t0.pc = pcOf 164) (h9 : t0.getReg .x9 = BitVec.ofNat 64 0) :
    Sim image t0 (512 * 70) (buildFtsLeaves S k idx 10 u) (LeafInv k u t0 1024) := by
  unfold buildFtsLeaves
  exact Sim.foldlM_range (2 ^ 10 / 2) _ ([], []) (fun p => LeafInv k u t0 (2 * p)) 70
    (fun p hp st t h => forsLeaf_pair S hS k idx u hk hidx hu t0 ctx p (by omega) st t h)
    (LeafInv.init k u t0 hpc h9)

end SigGolfCandidate.Radix27Sign



end


section -- SignClone13.Setup

/-! ### cloned Setup -/

/-!
# `sign`: setup and the cache MAC check (instructions 0 .. 64)

* block 0 (0 .. 53): `S`, `m` into the buffers, the tag (cache bytes 0 .. 32) into `x13 .. x16`,
  the in-place MAC input `tw_mac | P | S | region | 0^32` at `CACHE - 32`; HASH at 54.
* 55 .. 62: compare the answer (`DO`) with the tag, dword by dword (`fail_mac` at 84 .. 86).
* 63 .. 64: `LIM = 2^20`, `CNT = 0`; the digest loop starts at 65.

`mac_sim` : the machine refines `H(macInput S region) >>= fun tag => if tag = cacheTag then rest
else pure none`, given a simulation of `rest` from the digest loop.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace SigGolfCandidate.Radix27Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref SigGolfCandidate.Mem

-- Memory / register effect of the setup block (kernel-checked with a variable state).
kernel_theorem blk0_pbS : ∀ t : MachineState,
    (blk0.res.toState t).readWords (BitVec.ofNat 64 0x6C0) 4 = t.readWords (BitVec.ofNat 64 0x80) 4
kernel_theorem blk0_rbS : ∀ t : MachineState,
    (blk0.res.toState t).readWords (BitVec.ofNat 64 0x640) 4 = t.readWords (BitVec.ofNat 64 0x80) 4
kernel_theorem blk0_rbM : ∀ t : MachineState,
    (blk0.res.toState t).readWords (BitVec.ofNat 64 0x660) 4 = t.readWords (BitVec.ofNat 64 0x40) 4
kernel_theorem blk0_macS : ∀ t : MachineState,
    (blk0.res.toState t).readWords (BitVec.ofNat 64 0x44A0) 4 = t.readWords (BitVec.ofNat 64 0x80) 4
kernel_theorem blk0_db0 : ∀ t : MachineState,
    (blk0.res.toState t).getMem (BitVec.ofNat 64 0x20) = BitVec.ofNat 64 0xC01
kernel_theorem blk0_mac0 : ∀ t : MachineState,
    (blk0.res.toState t).getMem (BitVec.ofNat 64 0x4480) = BitVec.ofNat 64 0xE01
kernel_theorem blk0_macZ : ∀ t : MachineState,
    (blk0.res.toState t).readWords (BitVec.ofNat 64 0x144A0) 4 = [0, 0, 0, 0]
kernel_theorem blk0_tag : ∀ t : MachineState,
    [(blk0.res.toState t).getReg .x13, (blk0.res.toState t).getReg .x14,
      (blk0.res.toState t).getReg .x15, (blk0.res.toState t).getReg .x16] =
    t.readWords (BitVec.ofNat 64 0x44A0) 4
theorem blk0_rb0 (t : MachineState) :
    lo32 ((blk0.res.toState t).getMem (BitVec.ofNat 64 0x620)) = BitVec.ofNat 32 0x701 := by
  simp (config := { decide := true }) only [blk0.res, rv_simp, lo32_replace0, Nat.zero_div, ↓reduceIte]

/-- Addresses written by the setup block. -/
def setupW (a : Nat) : Prop :=
  a = 0x20 ∨ a = 0x620 ∨ (0x640 ≤ a ∧ a < 0x680) ∨ (0x6C0 ≤ a ∧ a < 0x6E0) ∨ a = 0x4480 ∨
    (0x44A0 ≤ a ∧ a < 0x44C0) ∨ (0x144A0 ≤ a ∧ a < 0x144C0)

/-- Addresses written up to the digest loop (setup, the MAC answer). -/
def macW (a : Nat) : Prop := setupW a ∨ (0x160 ≤ a ∧ a < 0x180)

/-- Facts at the start of the digest loop. -/
structure MacOk (sk : SecretKey) (cache : Cache) (m : Message) (u : MachineState) : Prop where
  pc : u.pc = pcOf 65
  mem : DigMem (toList sk) (toList m) u
  x5 : u.getReg .x5 = 0
  x6 : u.getReg .x6 = 0
  x7 : u.getReg .x7 = BitVec.ofNat 64 (2 ^ 20)
  pbS : u.readWords (BitVec.ofNat 64 0x6C0) 4 = wordsOf (toList sk)
  frame : Frame (s0 sk cache m) u macW

theorem MacOk.inv {sk : SecretKey} {cache : Cache} {m : Message} {u : MachineState}
    (h : MacOk sk cache m u) : DigInv u 0 u :=
  ⟨h.pc, by rw [h.x6]; rfl, by norm_num, RegsEq.refl _ _, Frame.refl _ _, rfl⟩

theorem length_cacheRegion (cache : Cache) : (cacheRegion (toList cache)).length = 65504 := by
  have hlen : (toList cache).length = 131072 := by simp [toList, SigGolfCandidate.Legacy.bytes]; rfl
  simp [cacheRegion, slice, hlen, regionBytes]; decide

theorem length_cacheTag (cache : Cache) : (cacheTag (toList cache)).length = 32 := by
  have hlen : (toList cache).length = 131072 := by simp [toList, SigGolfCandidate.Legacy.bytes]; rfl
  simp [cacheTag, slice, hlen]

/-- A compare block `ld ra, D; bne ra, aK, fail`. -/
theorem cmp_block {r : Result} {code : List (BitVec 32)} {a b : Nat} (hrun : symRun { noAlias := true } code (pcOf a) 3 = some r)
    (hcode : CodeAt image (pcOf a) code) (hobl : r.st.obl = []) (hc : r.cycles = 2) (hk : r.steps = 2)
    (t : MachineState) (hpc : t.pc = pcOf a) (x y : Word)
    (hpc' : (r.toState t).pc = if x = y then pcOf (a + 2) else pcOf b)
    (hmem : r.st.mem = []) (hregs : RegsEq t (r.toState t) [.x1]) :
    Steps image t 2 2 (r.toState t) ∧ (r.toState t).pc = (if x = y then pcOf (a + 2) else pcOf b) ∧
      (∀ z, (r.toState t).getMem z = t.getMem z) ∧ RegsEq t (r.toState t) [.x1] := by
  have hs := symRun_sound hrun hcode t hpc (by simp only [Result.obligs, hobl, Oblig.all])
  rw [hc, hk] at hs
  refine ⟨hs, hpc', fun z => ?_, hregs⟩
  rw [Result.toState_getMem, hmem, memEval_nil]

kernel_theorem blk55_pc : ∀ t : MachineState, (blk55.res.toState t).pc =
    if (t.getMem (BitVec.ofNat 64 0x160) != t.getReg .x13) = true then pcOf 87 else pcOf 57
kernel_theorem blk57_pc : ∀ t : MachineState, (blk57.res.toState t).pc =
    if (t.getMem (BitVec.ofNat 64 0x168) != t.getReg .x14) = true then pcOf 87 else pcOf 59
kernel_theorem blk59_pc : ∀ t : MachineState, (blk59.res.toState t).pc =
    if (t.getMem (BitVec.ofNat 64 0x170) != t.getReg .x15) = true then pcOf 87 else pcOf 61
kernel_theorem blk61_pc : ∀ t : MachineState, (blk61.res.toState t).pc =
    if (t.getMem (BitVec.ofNat 64 0x178) != t.getReg .x16) = true then pcOf 87 else pcOf 63

/-- A compare block `ld ra, D(x0); bne ra, R, fail_mac`. -/
theorem blk_cmp {code : List (BitVec 32)} {a : Nat} {r : Result} {P : MachineState → Word}
    (hrun : symRun { noAlias := true } code (pcOf a) 3 = some r) (hcode : CodeAt image (pcOf a) code)
    (hobl : r.st.obl = []) (hc : r.cycles = 2) (hk : r.steps = 2) (hmem : r.st.mem = [])
    (hpc : ∀ t : MachineState, (r.toState t).pc = P t) (hregs : ∀ t : MachineState, RegsEq t (r.toState t) [.x1])
    (t : MachineState) (tpc : t.pc = pcOf a) :
    Steps image t 2 2 (r.toState t) ∧ (r.toState t).pc = P t ∧
      (∀ z, (r.toState t).getMem z = t.getMem z) ∧ RegsEq t (r.toState t) [.x1] := by
  have hs := symRun_sound hrun hcode t tpc (by simp only [Result.obligs, hobl, Oblig.all])
  rw [hc, hk] at hs
  exact ⟨hs, hpc t, fun z => by rw [Result.toState_getMem, hmem, memEval_nil], hregs t⟩

theorem setup_frame (t : MachineState) : Frame t (blk0.res.toState t) setupW := by
  apply frame_toState; intro x hx hW
  simp only [blk0.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
    implies_true, and_true, ne_eq, ofNat_eq_iff]
  simp only [setupW] at hW
  omega

theorem setup_regs (t : MachineState) :
    RegsEq t (blk0.res.toState t) [.x1, .x3, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x29] := by
  intro r hr; rw [Result.toState_getReg]
  cases r <;> first | exact absurd (by decide) hr | rfl

/-- **The MAC check.** -/
theorem mac_sim (sk : SecretKey) (cache : Cache) (m : Message) {β : Type}
    (rest : OracleComp HashSpec (Option β)) (Wr : Nat) (Q : Option β → MachineState → Prop)
    (hrest : ∀ u, MacOk sk cache m u → Sim image u Wr rest Q)
    (hbad : ∀ t, t.pc = pcOf 89 → t.getReg .x5 = 1 → t.getReg .x10 = 1 → Q none t) :
    Sim image (s0 sk cache m) (54 + (8 * 1025 + (10 + Wr)))
      (H (macInput (toList sk) (cacheRegion (toList cache))) >>= fun tag =>
        if toList (n := 32) tag = cacheTag (toList cache) then rest else pure none) Q := by
  set s := s0 sk cache m with hs0
  have hS : (toList sk).length = 32 := length_toList sk
  have hs := symRun_sound blk0 codeAt_0 s (s0_pc sk cache m) (by simp only [blk0.res, rv_simp])
  have hk : blk0.res.cycles = 54 := rfl
  have hk' : blk0.res.steps = 54 := rfl
  rw [hk, hk'] at hs
  set u := blk0.res.toState s with hu
  have f := setup_frame s
  have rg := setup_regs s
  have e1 := symRun_ecall blk0 codeAt_0 s (by simp only [blk0.res, rv_simp]) rfl
  have x5 : u.getReg .x5 = 0 := by rw [rg.get .x5]; exact s0_getReg sk cache m .x5 (by decide)
  have x10 : u.getReg .x10 = BitVec.ofNat 64 0x4480 := by simp only [hu, blk0.res, rv_simp]
  have x11 : u.getReg .x11 = BitVec.ofNat 64 65600 := by simp only [hu, blk0.res, rv_simp]
  have x12 : u.getReg .x12 = BitVec.ofNat 64 0x160 := by simp only [hu, blk0.res, rv_simp]
  have pc1 : u.pc = pcOf 54 := by simp only [hu, blk0.res, rv_simp]
  have hR := length_cacheRegion cache
  obtain ⟨hn, hw⟩ := words_macInput (toList sk) (cacheRegion (toList cache)) hS hR
  have hq : hashInput u = pad64 (macInput (toList sk) (cacheRegion (toList cache))) := by
    refine hashInput_eq_pad64 u _ 1024 hn (by rw [x11]) (by norm_num) (by rw [x10]; decide) ?_
    rw [hw, x10, show 8 * (1024 + 1) = 1 + 1 + 2 + 4 + 8188 + 4 from rfl]
    rw [readWords_ofNat_add, readWords_ofNat_add, readWords_ofNat_add, readWords_ofNat_add,
      readWords_ofNat_add]
    simp only [Nat.reduceMul, Nat.reduceAdd]
    rw [readWords_ofNat_one, readWords_ofNat_one, hu, blk0_mac0, ← hu,
      f.getMem (a := 0x4488) (by norm_num) (by simp only [setupW]; omega),
      s0_zero sk cache m 0x4488 (by norm_num) (by norm_num) (by omega),
      f.readWords _ _ (by norm_num) (by intro i hi; simp only [setupW]; omega),
      show (0x4490 : Nat) = 0x4490 from rfl, readWords_ofNat_two,
      s0_zero sk cache m 0x4490 (by norm_num) (by norm_num) (by omega),
      s0_zero sk cache m 0x4498 (by norm_num) (by norm_num) (by omega),
      hu, blk0_macS, blk0_macZ, ← hu,
      f.readWords _ _ (by norm_num) (by intro i hi; simp only [setupW]; omega),
      show (0x44C0 : Nat) = 0x44A0 + 32 from rfl, s0_readWords_cache sk cache m 32 8188 (by norm_num) (by norm_num),
      s0_readWords_sk]
    simp only [twWords_eq, twWord0, List.cons_append, List.nil_append, List.append_assoc]
    rfl
  have hb : (pad64 (macInput (toList sk) (cacheRegion (toList cache)))).blocks = 1025 := by
    simp [pad64, Query.blocks, hn]
  have hq' : hashInput u = fmt (macInput (toList sk) (cacheRegion (toList cache))) :=
    hq.trans (fmt_thInput _ _ _ _ _ _ (by decide)).symm
  refine (Sim.steps hs (Sim.query_bind (W := 10 + Wr) e1 x5
    (hashArgs_of x10 x11 x12 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)) hq' (fun a => ?_))).mono (by rw [show macInput (toList sk) (cacheRegion (toList cache)) = thInput (tweak 14 0 0 0 0) _ from rfl, blocks_fmt_th _ _ _ _ _ _ (by decide)]; rw [← show macInput (toList sk) (cacheRegion (toList cache)) = thInput (tweak 14 0 0 0 0) _ from rfl, hb]) (fun _ _ h => h)
  set t2 := writeHash u a with ht2
  have pc2 : t2.pc = pcOf 55 := by rw [ht2, writeHash_pc, pc1]; apply BitVec.eq_of_toNat_eq; simp
  have f2 : Frame u t2 (fun x => 0x160 ≤ x ∧ x < 0x160 + 32) := frame_writeHash u a _ x12 (by norm_num)
  have wd : ∀ k, k < 4 → t2.getMem (BitVec.ofNat 64 (0x160 + 8 * k)) = a.extractLsb' (64 * k) 64 := by
    intro k hk
    rw [ht2, writeHash_getMem_ofNat u a 0x160 _ x12 (by norm_num) (by omega)]
    interval_cases k <;> simp
  have r2 : ∀ r, t2.getReg r = u.getReg r := fun r => by rw [ht2, writeHash_getReg]
  -- the tag words
  have htag := blk0_tag s
  rw [← hu, show (0x44A0 : Nat) = 0x44A0 + 0 from rfl, s0_readWords_cache sk cache m 0 4 (by norm_num)
    (by norm_num)] at htag
  have hct : slice (toList cache) 0 (8 * 4) = cacheTag (toList cache) := rfl
  rw [hct] at htag
  have heq := tag_eq_iff a _ (length_cacheTag cache) _ _ _ _ htag.symm
  -- the failure exit
  have fail : ∀ t, t.pc = pcOf 87 → Sim image t 2 (pure none) Q := by
    intro t tpc
    have hs84 := symRun_sound blk87 codeAt_87 t tpc (by simp only [blk87.res, rv_simp])
    have hc84 : blk87.res.cycles = 2 := rfl
    rw [hc84] at hs84
    exact Sim.pure_steps hs84 (hbad _ (by simp only [blk87.res, rv_simp]) (by simp only [blk87.res, rv_simp])
      (by simp only [blk87.res, rv_simp]))
  obtain ⟨e0, e1, e2, e3⟩ : t2.getMem (BitVec.ofNat 64 0x160) = a.extractLsb' 0 64 ∧
      t2.getMem (BitVec.ofNat 64 0x168) = a.extractLsb' 64 64 ∧
      t2.getMem (BitVec.ofNat 64 0x170) = a.extractLsb' 128 64 ∧
      t2.getMem (BitVec.ofNat 64 0x178) = a.extractLsb' 192 64 :=
    ⟨wd 0 (by norm_num), wd 1 (by norm_num), wd 2 (by norm_num), wd 3 (by norm_num)⟩
  -- the compare chain
  obtain ⟨hs3, pc3, m3, r3⟩ := blk_cmp blk55 codeAt_55 rfl rfl rfl rfl blk55_pc (fun t r hr => by
    rw [Result.toState_getReg]; cases r <;> first | exact absurd (by decide) hr | rfl) t2 pc2
  set t3 := blk55.res.toState t2
  rw [e0, r2] at pc3
  by_cases h0 : a.extractLsb' 0 64 = u.getReg .x13
  swap
  · rw [if_neg (fun h => h0 (heq.mp h).1)]
    exact (Sim.steps hs3 (fail t3 (by rw [pc3, if_pos (by simpa using h0)]))).mono (by omega) (fun _ _ h => h)
  obtain ⟨hs4, pc4, m4, r4⟩ := blk_cmp blk57 codeAt_57 rfl rfl rfl rfl blk57_pc (fun t r hr => by
    rw [Result.toState_getReg]; cases r <;> first | exact absurd (by decide) hr | rfl) t3
    (by rw [pc3, if_neg (by simp [h0])])
  set t4 := blk57.res.toState t3
  rw [m3, e1, r3.get .x14, r2] at pc4
  by_cases h1 : a.extractLsb' 64 64 = u.getReg .x14
  swap
  · rw [if_neg (fun h => h1 (heq.mp h).2.1)]
    exact (Sim.steps hs3 (Sim.steps hs4 (fail t4 (by rw [pc4, if_pos (by simpa using h1)])))).mono
      (by omega) (fun _ _ h => h)
  obtain ⟨hs5, pc5, m5, r5⟩ := blk_cmp blk59 codeAt_59 rfl rfl rfl rfl blk59_pc (fun t r hr => by
    rw [Result.toState_getReg]; cases r <;> first | exact absurd (by decide) hr | rfl) t4
    (by rw [pc4, if_neg (by simp [h1])])
  set t5 := blk59.res.toState t4
  rw [m4, m3, e2, r4.get .x15, r3.get .x15, r2] at pc5
  by_cases h2 : a.extractLsb' 128 64 = u.getReg .x15
  swap
  · rw [if_neg (fun h => h2 (heq.mp h).2.2.1)]
    exact (Sim.steps hs3 (Sim.steps hs4 (Sim.steps hs5 (fail t5 (by rw [pc5, if_pos (by simpa using h2)]))))).mono
      (by omega) (fun _ _ h => h)
  obtain ⟨hs6, pc6, m6, r6⟩ := blk_cmp blk61 codeAt_61 rfl rfl rfl rfl blk61_pc (fun t r hr => by
    rw [Result.toState_getReg]; cases r <;> first | exact absurd (by decide) hr | rfl) t5
    (by rw [pc5, if_neg (by simp [h2])])
  set t6 := blk61.res.toState t5
  rw [m5, m4, m3, e3, r5.get .x16, r4.get .x16, r3.get .x16, r2] at pc6
  by_cases h3 : a.extractLsb' 192 64 = u.getReg .x16
  swap
  · rw [if_neg (fun h => h3 (heq.mp h).2.2.2)]
    exact (Sim.steps hs3 (Sim.steps hs4 (Sim.steps hs5 (Sim.steps hs6 (fail t6
      (by rw [pc6, if_pos (by simpa using h3)])))))).mono (by omega) (fun _ _ h => h)
  rw [if_pos (heq.mpr ⟨h0, h1, h2, h3⟩)]
  have hs7 := symRun_sound blk63 codeAt_63 t6 (by rw [pc6, if_neg (by simp [h3])])
    (by simp only [blk63.res, rv_simp])
  have hc7 : blk63.res.cycles = 2 := rfl
  rw [hc7] at hs7
  set t7 := blk63.res.toState t6 with ht7
  have n7 : ∀ z, t7.getMem z = t2.getMem z := fun z => by
    rw [ht7, Result.toState_getMem, show blk63.res.st.mem = [] from rfl, memEval_nil, m6, m5, m4, m3]
  have r7 : RegsEq t6 t7 [.x6, .x7] := by
    intro r hr; rw [ht7, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have g7 : ∀ q, q ≠ .x1 → q ≠ .x6 → q ≠ .x7 → t7.getReg q = u.getReg q := by
    intro q h1 h6 h7
    rw [r7.get q (by simp [h6, h7]), r6.get q (by simp [h1]), r5.get q (by simp [h1]),
      r4.get q (by simp [h1]), r3.get q (by simp [h1]), r2]
  have fr : Frame s t7 macW := by
    intro x hx hW
    rw [n7, f2.getMem hx (by simp only [macW, setupW] at hW; omega),
      f.getMem hx (by simp only [macW, setupW] at hW ⊢; omega)]
  have fu : ∀ a n, a + 8 * n < 2 ^ 64 → (∀ i < n, ¬ macW (a + 8 * i)) →
      t7.readWords (BitVec.ofNat 64 a) n = s.readWords (BitVec.ofNat 64 a) n :=
    fun a n h1 h2 => fr.readWords a n h1 h2
  have fu7 : ∀ a n, a + 8 * n < 2 ^ 64 → (∀ i < n, ¬ (0x160 ≤ a + 8 * i ∧ a + 8 * i < 0x180)) →
      t7.readWords (BitVec.ofNat 64 a) n = u.readWords (BitVec.ofNat 64 a) n := by
    intro a n h1 h2
    exact readWords_congr _ _ a n (fun i hi => by rw [n7, f2.getMem (by omega) (by have := h2 i hi; omega)])
  have hz : ∀ a n, a % 8 = 0 → a + 8 * n + 8 < 2 ^ 64 →
      (∀ i < n, a + 8 * i + 8 ≤ 0x40 ∨ (0x60 ≤ a + 8 * i ∧ a + 8 * i + 8 ≤ 0x80) ∨
        (0xA0 ≤ a + 8 * i ∧ a + 8 * i + 8 ≤ 0x44A0) ∨ 0x244A0 ≤ a + 8 * i) →
      s.readWords (BitVec.ofNat 64 a) n = List.replicate n 0 := by
    intro a n h8 hb hout
    induction n generalizing a with
    | zero => rfl
    | succ n ih =>
      rw [readWords_ofNat_succ, s0_zero sk cache m a h8 (by omega) (by simpa using hout 0 (by omega)),
        ih (a + 8) (by omega) (by omega)
          (fun i hi => by rw [show a + 8 + 8 * i = a + 8 * (i + 1) by ring]; exact hout _ (by omega))]
      rfl
  have ok : MacOk sk cache m t7 := by
    refine ⟨by simp only [ht7, blk63.res, rv_simp], ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, fr⟩
    · rw [fu7 _ _ (by norm_num) (by intro i hi; omega), hu, blk0_rbS, s0_readWords_sk]
    · rw [fu7 _ _ (by norm_num) (by intro i hi; omega), hu, blk0_rbM, s0_readWords_msg]
    · rw [fu _ _ (by norm_num) (by intro i hi; simp only [macW, setupW]; omega),
        hz _ _ (by norm_num) (by norm_num) (by intro i hi; omega)]; rfl
    · rw [fu _ _ (by norm_num) (by intro i hi; simp only [macW, setupW]; omega),
        hz _ _ (by norm_num) (by norm_num) (by intro i hi; omega)]; rfl
    · rw [n7, f2.getMem (by norm_num) (by omega), hu, blk0_rb0]
    · rw [readWords_ofNat_succ, n7, f2.getMem (by norm_num) (by omega), hu, blk0_db0,
        fu _ _ (by norm_num) (by intro i hi; simp only [macW, setupW]; omega),
        hz _ _ (by norm_num) (by norm_num) (by intro i hi; omega)]; rfl
    · rw [fu _ _ (by norm_num) (by intro i hi; simp only [macW, setupW]; omega), s0_readWords_msg]
    · rw [g7 .x5 (by decide) (by decide) (by decide), x5]
    · simp only [ht7, blk63.res, rv_simp]
    · simp only [ht7, blk63.res, rv_simp]; rfl
    · rw [fu7 _ _ (by norm_num) (by intro i hi; omega), hu, blk0_pbS, s0_readWords_sk]
  exact (Sim.steps hs3 (Sim.steps hs4 (Sim.steps hs5 (Sim.steps hs6 (Sim.steps hs7
    (hrest t7 ok)))))).mono (by omega) (fun _ _ h => h)

end SigGolfCandidate.Radix27Sign



end


section -- SignClone13.TreeBuildNode

/-! ### cloned TreeBuildNode -/

/-!
# The node loop (`node_hash`), shared by sign (FORS, tree_build) and keygen (tree_build)

Code (identical words wherever it occurs; relocatable):
```
L: add sp,a6,a7; sw sp,460(x0) (heap index NCNT + JJ); slli gp,a6,5; add gp,gp,s3;
   ld/sd ×4 (FA[2JJ],FA[2JJ+1] → NB+32..64);
   addi a0,x0,448; addi a1,x0,64; slli gp,a6,4; add a2,s3,gp; ecall      -- nodeSegA (17 words)
   addi a6,a6,1; bne a6,a7,L                                             -- nodeSegB (2 words)
```
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace SigGolfCandidate.Radix27Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

def nodeSegA : List (BitVec 32) := [0x01180133#32, 0x1c202623#32, 0x00581193#32, 0x013181b3#32, 0x0001b083#32,
  0x1e103023#32, 0x0081b083#32, 0x1e103423#32, 0x0101b083#32, 0x1e103823#32, 0x0181b083#32,
  0x1e103c23#32, 0x1c000513#32, 0x04000593#32, 0x00481193#32, 0x00398633#32, 0x00000073#32]
def nodeSegB : List (BitVec 32) := [0x00180813#32, 0xfb181ce3#32]

sym_block nodeA0 := symRun { noAlias := true } nodeSegA 0x1000 18
sym_block nodeB0 := symRun { noAlias := true } nodeSegB 0x1000 3

def nodeARes (pc : Word) : Result := { nodeA0.res with pc := .c (addN pc 16) }
def nodeBRes (pc : Word) : Result :=
  { nodeB0.res with pc := retarget nodeB0.res.pc (addN pc 1 + 0xffffffffffffffb8#64) (addN pc 1 + 4) }

kernel_theorem nodeA_run : ∀ pc : Word, symRun { noAlias := true } nodeSegA pc 18 = some (nodeARes pc)
kernel_theorem nodeB_run : ∀ pc : Word, symRun { noAlias := true } nodeSegB pc 3 = some (nodeBRes pc)

theorem nodeA_spec {image : Image} {P : Nat} (hcode : CodeAt image (pcOf P) nodeSegA)
    (s : MachineState) (hpc : s.pc = pcOf P) (j m B : Nat) (h16 : s.getReg .x16 = BitVec.ofNat 64 j)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 m) (hjm : j + m < 2 ^ 32)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 B) (hB : 0x210 ≤ B) (hB8 : B % 8 = 0)
    (hjB : B + 32 * j + 32 ≤ 2 ^ 24) :
    ∃ t, Steps image s 16 16 t ∧ fetch image t = some (.base .ECALL) ∧ t.pc = pcOf (P + 16) ∧
      t.getReg .x10 = BitVec.ofNat 64 448 ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 (B + 16 * j) ∧
      (∀ r, r ≠ .x1 → r ≠ .x2 → r ≠ .x3 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → t.getReg r = s.getReg r) ∧
      ∀ a : Nat, a < 2 ^ 64 → t.getMem (BitVec.ofNat 64 a) =
        if a = 504 then s.getMem (BitVec.ofNat 64 (B + 32 * j + 24))
        else if a = 496 then s.getMem (BitVec.ofNat 64 (B + 32 * j + 16))
        else if a = 488 then s.getMem (BitVec.ofNat 64 (B + 32 * j + 8))
        else if a = 480 then s.getMem (BitVec.ofNat 64 (B + 32 * j))
        else if a = 456 then replaceWord32 (s.getMem (BitVec.ofNat 64 456)) 1 (BitVec.ofNat 32 (j + m))
        else s.getMem (BitVec.ofNat 64 a) := by
  have hobl : (nodeARes (pcOf P)).obligs s := by
    simp only [nodeARes, nodeA0.res, rv_simp, h16, h19, ofNat_shiftLeft, ofNat_add_ofNat,
      ne_eq, ofNat_eq_iff, accessValid_ofNat, BitVec.toNat_ofNat]
    norm_num
    omega
  refine ⟨_, symRun_sound (nodeA_run _) hcode s hpc hobl, symRun_ecall (nodeA_run _) hcode s hobl rfl,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [nodeARes, nodeA0.res, rv_simp, addN_pcOf]
  · simp only [nodeARes, nodeA0.res, rv_simp]
  · simp only [nodeARes, nodeA0.res, rv_simp]
  · simp only [nodeARes, nodeA0.res, rv_simp, h16, h19, ofNat_shiftLeft, ofNat_add_ofNat,
      BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow]
    congr 1; ring
  · intro r h1 h2 h3 h10 h11 h12
    cases r <;> (try contradiction) <;> simp only [nodeARes, nodeA0.res, rv_simp] <;> rfl
  · intro a ha
    simp only [nodeARes, nodeA0.res, rv_simp, h16, h17, h19, ofNat_shiftLeft, ofNat_add_ofNat,
      ofNat_eq_iff, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, truncate32_ofNat]
    split_ifs <;> first | rfl | (exfalso; omega) | (congr 2; omega)

/-- Block B at index `L + 17` (loop head `L`): `JJ += 1`, back to `L` unless `JJ = NCNT`. -/
theorem nodeB_spec {image : Image} {L : Nat} (hcode : CodeAt image (pcOf (L + 17)) nodeSegB)
    (s : MachineState) (hpc : s.pc = pcOf (L + 17)) (j m : Nat) (h16 : s.getReg .x16 = BitVec.ofNat 64 j)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 m) (hj : j + 1 < 2 ^ 64) (hm : m < 2 ^ 64) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = (if j + 1 = m then pcOf (L + 19) else pcOf L) ∧
      t.getReg .x16 = BitVec.ofNat 64 (j + 1) ∧
      (∀ r, r ≠ .x16 → t.getReg r = s.getReg r) ∧ (∀ a, t.getMem a = s.getMem a) := by
  have hobl : (nodeBRes (pcOf (L + 17))).obligs s := by
    simp only [nodeBRes, nodeB0.res, rv_simp]
  refine ⟨_, symRun_sound (nodeB_run _) hcode s hpc hobl, ?_, ?_, ?_, ?_⟩
  · simp only [nodeBRes, nodeB0.res, retarget, rv_simp, addN_pcOf, h16, h17, ofNat_add_ofNat,
      ofNat_bne_ofNat]
    by_cases h : j + 1 = m
    · subst h; simp only [if_true]; apply BitVec.eq_of_toNat_eq; simp; omega
    · rw [if_neg h]
      simp only [show ¬ ((j + 1) % 2 ^ 64 = m % 2 ^ 64) by omega, decide_false, Bool.not_false,
        if_true]
      apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub]; omega
  · simp only [nodeBRes, nodeB0.res, rv_simp, h16, ofNat_add_ofNat]
  · intro r h
    cases r <;> (try contradiction) <;> simp only [nodeBRes, nodeB0.res, rv_simp] <;> rfl
  · intro a; simp only [nodeBRes, nodeB0.res, rv_simp]

/-- Tree / FORS node format `tw(tt, lay, tau, lam, j) | P | l | r`. -/
def nodeFmt (tt lay tau : Nat) : NodeFmt := fun lam j l r => thInput (tweak tt lay tau lam j) (l ++ r)

theorem nodeInput_eq (lay tau : Nat) : nodeInput lay tau = nodeFmt 3 lay tau := rfl
theorem ftsNodeInput_eq (k idx : Nat) : ftsNodeInput k idx = nodeFmt 10 k idx := rfl

/-- The node-loop state facts (`NB` buffer, registers) at iteration `j`. -/
structure NodeCtx where
  tt : Nat
  lay : Nat
  tau : Nat
  lam : Nat
  B : Nat
  m : Nat

/-- Memory frame of the node loop: outside the array prefix `[B, B + 32 m)` and the `NB` dwords
`456, 480, 488, 496, 504` nothing changes. -/
def NodeFrame (c : NodeCtx) (s t : MachineState) : Prop :=
  (∀ a : Nat, a < 2 ^ 64 → (a < c.B ∨ c.B + 32 * c.m ≤ a) → a ≠ 456 → a ≠ 480 → a ≠ 488 → a ≠ 496 →
    a ≠ 504 → t.getMem (BitVec.ofNat 64 a) = s.getMem (BitVec.ofNat 64 a)) ∧
  lo32 (t.getMem (BitVec.ofNat 64 456)) = lo32 (s.getMem (BitVec.ofNat 64 456))

/-- Registers clobbered by the node loop. -/
def NodeRegs (s t : MachineState) : Prop :=
  ∀ r, r ≠ .x1 → r ≠ .x2 → r ≠ .x3 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → r ≠ .x16 → t.getReg r = s.getReg r

/-- Loop invariant after `j` nodes. -/
def NodeInv (c : NodeCtx) (L : Nat) (lvl : List Val) (s : MachineState) (j : Nat) (acc : List Val)
    (t : MachineState) : Prop :=
  j ≤ c.m ∧ acc.length = j ∧ (∀ v ∈ acc, v.length = 16) ∧
  (∀ i (hi : i < acc.length), t.readWords (BitVec.ofNat 64 (c.B + 16 * i)) 2 = wordsOf acc[i]) ∧
  (∀ i (hi : i < lvl.length), 2 * j ≤ i →
    t.readWords (BitVec.ofNat 64 (c.B + 16 * i)) 2 = wordsOf lvl[i]) ∧
  t.pc = (if j < c.m then pcOf L else pcOf (L + 19)) ∧
  t.getReg .x16 = BitVec.ofNat 64 j ∧ NodeRegs s t ∧ NodeFrame c s t

theorem getD_of_lt {α : Type} {l : List α} {i : Nat} {d : α} (h : i < l.length) :
    l.getD i d = l[i] := by
  simp [List.getD, List.getElem?_eq_getElem h]

theorem pad64_len64 (x : List Byte) (h : x.length = 64) : pad64 x = ⟨0, ofList _ x⟩ := by
  unfold pad64 padTo64
  have hp : padBlocks x.length = 0 := by rw [h]; rfl
  rw [hp]; simp [h, zeros]

theorem length_nodeFmt (tt lay tau lam j : Nat) (l r : Val) (hl : l.length = 16) (hr : r.length = 16) :
    (nodeFmt tt lay tau lam j l r).length = 64 := by
  simp [nodeFmt, hl, hr]

theorem pad64_blocks_one (x : List Byte) (h : padBlocks x.length = 0) : (pad64 x).blocks = 1 := by
  simp [pad64, Query.blocks, h]

/-- The HASH input of the node buffer `NB = 448`. -/
theorem node_hashInput (t : MachineState) (tt lay tau lam j : Nat) (l r : Val) (hl : l.length = 16)
    (hr : r.length = 16) (h10 : t.getReg .x10 = BitVec.ofNat 64 448)
    (h11 : t.getReg .x11 = BitVec.ofNat 64 64)
    (hw0 : t.getMem (BitVec.ofNat 64 448) = twWord0 tt lay tau lam)
    (hw1 : t.getMem (BitVec.ofNat 64 456) = BitVec.ofNat 64 (tau % 2 ^ 32 + 2 ^ 32 * (j % 2 ^ 32)))
    (hz0 : t.getMem (BitVec.ofNat 64 464) = 0) (hz1 : t.getMem (BitVec.ofNat 64 472) = 0)
    (hL : t.readWords (BitVec.ofNat 64 480) 2 = wordsOf l)
    (hR : t.readWords (BitVec.ofNat 64 496) 2 = wordsOf r) :
    hashInput t = pad64 (nodeFmt tt lay tau lam j l r) := by
  obtain ⟨hn, hw⟩ := words_th32 tt lay tau lam j l r hl hr
  refine hashInput_eq_pad64 t _ 0 hn (by rw [h11]) (by norm_num) (by rw [h10]; decide) ?_
  rw [nodeFmt, hw, h10, twWords_eq, ← hL, ← hR,
    show 8 * (0 + 1) = 4 + 2 + 2 from rfl, readWords_ofNat_add, readWords_ofNat_add]
  simp only [readWords_ofNat_succ, hw0, hw1, hz0, hz1]
  rfl

/-- **Node loop**: `m` nodes of level `lam` from the `2m` values `lvl` in slots `B + 16 i`;
the results land in slots `0 .. m-1`; `25 m` cycles. -/
theorem nodeLoop_sim {image : Image} {L : Nat} (hA : CodeAt image (pcOf L) nodeSegA)
    (hB : CodeAt image (pcOf (L + 17)) nodeSegB) (c : NodeCtx) (lvl : List Val)
    (hlen : lvl.length = 2 * c.m) (hvals : ∀ v ∈ lvl, v.length = 16) (hm : 0 < c.m)
    (hB0 : 0x210 ≤ c.B) (hB8 : c.B % 8 = 0) (hBm : c.B + 32 * c.m + 32 ≤ 2 ^ 24)
    (s : MachineState) (hpc : s.pc = pcOf L) (h16 : s.getReg .x16 = 0)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 c.m) (h19 : s.getReg .x19 = BitVec.ofNat 64 c.B)
    (h5 : s.getReg .x5 = 0) (hm32 : 2 * c.m < 2 ^ 32)
    (hfmt : ∀ j l r, j < c.m → l.length = 16 → r.length = 16 →
      fmt (nodeFmt c.tt c.lay c.tau c.lam j l r) = pad64 (nodeFmt c.tt c.lay c.tau 0 (c.m + j) l r))
    (hw0 : s.getMem (BitVec.ofNat 64 448) = twWord0 c.tt c.lay c.tau 0)
    (hw1 : lo32 (s.getMem (BitVec.ofNat 64 456)) = BitVec.ofNat 32 c.tau)
    (hz0 : s.getMem (BitVec.ofNat 64 464) = 0) (hz1 : s.getMem (BitVec.ofNat 64 472) = 0)
    (hslots : ∀ i (hi : i < lvl.length), s.readWords (BitVec.ofNat 64 (c.B + 16 * i)) 2 = wordsOf lvl[i]) :
    Sim image s (c.m * 26) (buildLevel (nodeFmt c.tt c.lay c.tau) c.lam lvl)
      (NodeInv c L lvl s c.m) := by
  unfold buildLevel
  rw [hlen, show 2 * c.m / 2 = c.m by omega]
  apply Sim.foldlM_range c.m _ [] (NodeInv c L lvl s) 26
  · intro j hj acc t ⟨hjm, hacc, haccv, hslot, hlvl, tpc, t16, tregs, tframe⟩
    have t19 : t.getReg .x19 = BitVec.ofNat 64 c.B := by rw [tregs .x19 (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide), h19]
    have t17 : t.getReg .x17 = BitVec.ofNat 64 c.m := by rw [tregs .x17 (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide), h17]
    have t5 : t.getReg .x5 = 0 := by rw [tregs .x5 (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide), h5]
    obtain ⟨t1, st1, f1, pc1, a10, a11, a12, regs1, mem1⟩ :=
      nodeA_spec hA t (by rw [tpc, if_pos hj]) j c.m c.B t16 t17 (by omega) t19 hB0 hB8 (by omega)
    have hl : (lvl.getD (2 * j) []).length = 16 := by
      rw [getD_of_lt (by omega)]; exact hvals _ (List.getElem_mem _)
    have hr : (lvl.getD (2 * j + 1) []).length = 16 := by
      rw [getD_of_lt (by omega)]; exact hvals _ (List.getElem_mem _)
    have hmemT : ∀ a : Nat, a < 2 ^ 64 → c.B ≤ a → t1.getMem (BitVec.ofNat 64 a) = t.getMem (BitVec.ofNat 64 a) := by
      intro a ha hBa
      rw [mem1 a ha, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega)]
    have hq : hashInput t1 = pad64 (nodeFmt c.tt c.lay c.tau 0 (c.m + j) (lvl.getD (2 * j) [])
        (lvl.getD (2 * j + 1) [])) := by
      apply node_hashInput t1 _ _ _ _ _ _ _ hl hr (by rw [a10]) (by rw [a11])
      · rw [mem1 _ (by norm_num), if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num)]
        rw [tframe.1 448 (by norm_num) (by omega) (by norm_num) (by norm_num) (by norm_num)
          (by norm_num) (by norm_num), hw0]
      · rw [mem1 _ (by norm_num), if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num),
          if_neg (by norm_num), if_pos rfl]
        exact word_of_halves _ c.tau (c.m + j) (by rw [lo32_replace1, tframe.2, hw1])
          (by rw [hi32_replace1, Nat.add_comm])
      · rw [mem1 _ (by norm_num), if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num)]
        rw [tframe.1 464 (by norm_num) (by omega) (by norm_num) (by norm_num) (by norm_num)
          (by norm_num) (by norm_num), hz0]
      · rw [mem1 _ (by norm_num), if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num)]
        rw [tframe.1 472 (by norm_num) (by omega) (by norm_num) (by norm_num) (by norm_num)
          (by norm_num) (by norm_num), hz1]
      · rw [readWords_ofNat_two, mem1 _ (by norm_num), mem1 _ (by norm_num), getD_of_lt (by omega),
          ← hlvl (2 * j) (by omega) (le_refl _), readWords_ofNat_two]
        simp; constructor <;> congr 2 <;> omega
      · rw [readWords_ofNat_two, mem1 _ (by norm_num), mem1 _ (by norm_num), getD_of_lt (by omega),
          ← hlvl (2 * j + 1) (by omega) (by omega), readWords_ofNat_two]
        simp; constructor <;> congr 2 <;> omega
    have hblk : (pad64 (nodeFmt c.tt c.lay c.tau c.lam j (lvl.getD (2 * j) [])
        (lvl.getD (2 * j + 1) []))).blocks = 1 :=
      pad64_blocks_one _ (words_th32 c.tt c.lay c.tau c.lam j _ _ hl hr).1
    have := Sim.steps st1 (Sim.hash16_bindF (f := fun v => pure (acc ++ [v])) (W := 2) (Q := NodeInv c L lvl s (j + 1)) f1
      (by rw [regs1 .x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), t5])
      (hashArgs_of a10 a11 a12 (by norm_num) (by norm_num) (by norm_num) (by omega) (by omega) (by omega))
      (hq.trans (hfmt j _ _ hj hl hr).symm) (fun a => by
        obtain ⟨t3, st3, pc3, x16', regs3, mem3⟩ := nodeB_spec (L := L) hB (writeHash t1 a)
          (by rw [writeHash_pc, pc1]; apply BitVec.eq_of_toNat_eq; simp; omega) j c.m
          (by rw [writeHash_getReg, regs1 .x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), t16])
          (by rw [writeHash_getReg, regs1 .x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), t17])
          (by omega) (by omega)
        apply Sim.pure_steps st3
        have hwf : ∀ x : Nat, x < 2 ^ 64 → (x < c.B + 16 * j ∨ c.B + 16 * j + 32 ≤ x) →
            t3.getMem (BitVec.ofNat 64 x) = t1.getMem (BitVec.ofNat 64 x) := by
          intro x hx hout
          rw [mem3, writeHash_getMem_frame t1 a (c.B + 16 * j) x a12 (by omega) hx (by omega)]
        refine ⟨by omega, by simp [hacc], ?_, ?_, ?_, ?_, x16', ?_, ?_, ?_⟩
        · intro v hv; rcases List.mem_append.mp hv with hv | hv
          · exact haccv v hv
          · simp at hv; subst hv; simp
        · intro i hi
          simp only [List.length_append, List.length_singleton] at hi
          rw [readWords_ofNat_two]
          by_cases hij : i < acc.length
          · rw [List.getElem_append_left hij, ← hslot i hij, readWords_ofNat_two,
              hwf _ (by omega) (by omega), hwf _ (by omega) (by omega), hmemT _ (by omega) (by omega),
              hmemT _ (by omega) (by omega)]
          · have hij' : i = acc.length := by omega
            subst hij'
            rw [List.getElem_append_right (le_refl _)]
            simp only [Nat.sub_self, List.getElem_singleton]
            rw [← writeHash_readWords_val t1 a (c.B + 16 * acc.length) (by rw [a12, hacc]) (by omega),
              readWords_ofNat_two, mem3, mem3, hacc]
        · intro i hi h2
          rw [readWords_ofNat_two, hwf _ (by omega) (by omega), hwf _ (by omega) (by omega),
            hmemT _ (by omega) (by omega), hmemT _ (by omega) (by omega), ← readWords_ofNat_two]
          exact hlvl i hi (by omega)
        · rw [pc3]; by_cases h : j + 1 = c.m
          · simp [h]
          · rw [if_neg h, if_pos (by omega)]
        · intro r h1 h2 h3 h10 h11 h12 h16'
          rw [regs3 r h16', writeHash_getReg, regs1 r h1 h2 h3 h10 h11 h12, tregs r h1 h2 h3 h10 h11 h12 h16']
        · intro x hx hout n1 n2 n3 n4 n5
          rw [hwf x hx (by omega), mem1 x hx, if_neg n5, if_neg n4, if_neg n3, if_neg n2, if_neg n1]
          exact tframe.1 x hx hout n1 n2 n3 n4 n5
        · rw [hwf 456 (by norm_num) (by omega), mem1 456 (by norm_num)]
          simp only [show ¬ ((456 : Nat) = 504) by norm_num, show ¬ ((456 : Nat) = 496) by norm_num,
            show ¬ ((456 : Nat) = 488) by norm_num, show ¬ ((456 : Nat) = 480) by norm_num, if_false,
            if_true, lo32_replace1]
          exact tframe.2))
    refine this.mono ?_ (fun _ _ h => h)
    rw [hfmt j _ _ hj hl hr, nodeFmt, pad64_blocks_one _ (words_th32 c.tt c.lay c.tau 0 (c.m + j) _ _ hl hr).1]
  · refine ⟨Nat.zero_le _, rfl, by simp, by simp, fun i hi _ => hslots i hi, by simp [hpc, hm],
      by simpa using h16, fun r _ _ _ _ _ _ _ => rfl, fun a _ _ _ _ _ _ _ => rfl, rfl⟩

theorem NodeRegs.toRegsEq {s t : MachineState} (h : NodeRegs s t) :
    RegsEq s t [.x1, .x2, .x3, .x10, .x11, .x12, .x16] := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  exact h r hr.1 hr.2.1 hr.2.2.1 hr.2.2.2.1 hr.2.2.2.2.1 hr.2.2.2.2.2.1 hr.2.2.2.2.2.2

theorem NodeFrame.toFrame {c : NodeCtx} {s t : MachineState} (h : NodeFrame c s t) :
    Frame s t (fun a => (c.B ≤ a ∧ a < c.B + 32 * c.m) ∨ a = 456 ∨ a = 480 ∨ a = 488 ∨ a = 496 ∨
      a = 504) := by
  intro a ha hW
  simp only [not_or, not_and, not_lt] at hW
  exact h.1 a ha (by omega) hW.2.1 hW.2.2.1 hW.2.2.2.1 hW.2.2.2.2.1 hW.2.2.2.2.2

end SigGolfCandidate.Radix27Sign



end


section -- SignClone13.ForsLevel

/-! ### cloned ForsLevel -/

/-!
# `sign`, FORS levels (`fors_level_loop`, instructions 142 .. 181)

`forsLevels_sim` : from `fors_level_loop` with `LAM = 1`, `NCNT = 1024` and the 1024 leaves in
`FA`, the machine refines the level fold of `buildLevels (ftsNodeInput k idx) u 10 leaves`:
the root ends in `FA[0]` and the authentication path at `SIGL + 32 + 16 l`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace SigGolfCandidate.Radix27Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

theorem seg210_eq : seg210 = nodeSegA := rfl
theorem seg227_eq : seg227 = nodeSegB := rfl

theorem codeAt_node210 : CodeAt image (pcOf 210) nodeSegA := seg210_eq ▸ codeAt_210
theorem codeAt_node227 : CodeAt image (pcOf (210 + 17)) nodeSegB := seg227_eq ▸ codeAt_227

/-- Facts at the start of the level loop of tree `k`. -/
structure LevCtx (k idx u : Nat) (t0 : MachineState) : Prop where
  x5 : t0.getReg .x5 = 0
  x8 : t0.getReg .x8 = BitVec.ofNat 64 k
  x13 : t0.getReg .x13 = BitVec.ofNat 64 u
  x14 : t0.getReg .x14 = BitVec.ofNat 64 (0x801 + 2 ^ 24 * (idx / 2 ^ 32))
  x18 : t0.getReg .x18 = BitVec.ofNat 64 (0x2650 + 176 * k)
  x19 : t0.getReg .x19 = BitVec.ofNat 64 0x30000
  nb8 : lo32 (t0.getMem (BitVec.ofNat 64 0x1C8)) = BitVec.ofNat 32 idx
  nbP : t0.readWords (BitVec.ofNat 64 0x1D0) 2 = [0, 0]

def levW (k : Nat) (a : Nat) : Prop :=
  a = 0x1C0 ∨ a = 0x1C8 ∨ (0x1E0 ≤ a ∧ a < 0x200) ∨ (0x30000 ≤ a ∧ a < 0x30000 + 16 * 1025) ∨
    (0x2650 + 176 * k + 32 ≤ a ∧ a < 0x2650 + 176 * k + 192)

def levRegs : List Reg := [.x1, .x2, .x3, .x10, .x11, .x12, .x15, .x16, .x17, .x29]

/-- Invariant after `j` levels. -/
def LevInv (k : Nat) (t0 : MachineState) (j : Nat) (st : List Val × List Val) (t : MachineState) : Prop :=
  j ≤ 10 ∧ st.1.length = 2 ^ (10 - j) ∧ (∀ v ∈ st.1, v.length = 16) ∧ Slots t 0x30000 st.1 ∧
  st.2.length = j ∧ (∀ v ∈ st.2, v.length = 16) ∧ Slots t (0x2650 + 176 * k + 32) st.2 ∧
  t.pc = (if j < 10 then pcOf 193 else pcOf 232) ∧ t.getReg .x15 = BitVec.ofNat 64 (j + 1) ∧
  t.getReg .x17 = BitVec.ofNat 64 (2 ^ (10 - j)) ∧
  RegsEq t0 t levRegs ∧ Frame t0 t (levW k) ∧
  lo32 (t.getMem (BitVec.ofNat 64 0x1C8)) = lo32 (t0.getMem (BitVec.ofNat 64 0x1C8))

theorem xor1_lt (a n : Nat) (ha : a < 2 ^ n) (hn : 1 ≤ n) : a ^^^ 1 < 2 ^ n :=
  Nat.xor_lt_two_pow ha (lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hn))

theorem forsLevel_body (k idx u : Nat) (hk : k < 14) (hidx : idx < 2 ^ 34) (hu : u < 1024)
    (t0 : MachineState) (ctx : LevCtx k idx u t0) (j : Nat) (hj : j < 10)
    (st : List Val × List Val) (t : MachineState) (hinv : LevInv k t0 j st t) :
    Sim image t (17 + (2 ^ (9 - j) * 26 + 3))
      (levelStep (ftsNodeInput k idx) u st (1 + j)) (LevInv k t0 (j + 1)) := by
  obtain ⟨-, hlen, hvals, hslots, hplen, hpvals, hpath, tpc, t15, t17, tregs, tframe, tlo⟩ := hinv
  have tpc' : t.pc = pcOf 193 := by rw [tpc, if_pos hj]
  have tx5 : t.getReg .x5 = 0 := by rw [tregs.get .x5 (by decide), ctx.x5]
  have tx8 : t.getReg .x8 = BitVec.ofNat 64 k := by rw [tregs.get .x8 (by decide), ctx.x8]
  have tx13 : t.getReg .x13 = BitVec.ofNat 64 u := by rw [tregs.get .x13 (by decide), ctx.x13]
  have tx14 : t.getReg .x14 = BitVec.ofNat 64 (0x801 + 2 ^ 24 * (idx / 2 ^ 32)) := by
    rw [tregs.get .x14 (by decide), ctx.x14]
  have tx18 : t.getReg .x18 = BitVec.ofNat 64 (0x2650 + 176 * k) := by
    rw [tregs.get .x18 (by decide), ctx.x18]
  have tx19 : t.getReg .x19 = BitVec.ofNat 64 0x30000 := by rw [tregs.get .x19 (by decide), ctx.x19]
  have hpow : 2 ^ (10 - j) = 2 * 2 ^ (9 - j) := by
    rw [show 10 - j = 9 - j + 1 by omega, Nat.pow_succ]; ring
  have hp9 : 2 ^ (9 - j) ≤ 512 := by
    calc 2 ^ (9 - j) ≤ 2 ^ 9 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 512 := by norm_num
  set sib := (u / 2 ^ j) ^^^ 1 with hsib
  have hsib_lt : sib < 2 ^ (10 - j) := by
    apply xor1_lt _ _ _ (by omega)
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← Nat.pow_add, show 10 - j + j = 10 by omega]
    exact hu
  have hsib' : sib < 1024 := lt_of_lt_of_le hsib_lt (by
    calc 2 ^ (10 - j) ≤ 2 ^ 10 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 1024 := by norm_num)
  -- block 142: capture sibling, node tweak
  have hudiv : u / 2 ^ j ≤ u := Nat.div_le_self _ _
  have hs1 := symRun_sound blk193 codeAt_193 t tpc' (by
    simp only [blk193.res, rv_simp]
    bvsimp [t15, tx13, tx18, tx19, accessValid_ofNat]
    rw [← hsib]; omega)
  have hc1 : blk193.res.cycles = 17 := rfl
  rw [hc1] at hs1
  set t1 := blk193.res.toState t with ht1
  have hP : 0x2650 + 176 * k + 32 + 16 * j + 8 < 2 ^ 64 := by omega
  have f1 : Frame t t1 (fun x => x = 0x1C0 ∨ x = 0x2650 + 176 * k + 32 + 16 * j ∨
      x = 0x2650 + 176 * k + 32 + 16 * j + 8) := by
    apply frame_toState; intro x hx hW
    simp only [blk193.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq]
    bvsimp [t15, tx18, ofNat_eq_iff]
    omega
  have r1 : RegsEq t t1 [.x1, .x2, .x3, .x16, .x17, .x29] := by
    intro r hr; rw [ht1, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have pc1 : t1.pc = pcOf 210 := by simp only [ht1, blk193.res, rv_simp]
  have y16 : t1.getReg .x16 = 0 := by simp only [ht1, blk193.res, rv_simp]
  have y17 : t1.getReg .x17 = BitVec.ofNat 64 (2 ^ (9 - j)) := by
    simp only [ht1, blk193.res, rv_simp]
    bvsimp [t17]
    congr 1; rw [hpow]; omega
  have y19 : t1.getReg .x19 = BitVec.ofNat 64 0x30000 := by rw [r1.get .x19, tx19]
  have y5 : t1.getReg .x5 = 0 := by rw [r1.get .x5, tx5]
  have w448 : t1.getMem (BitVec.ofNat 64 448) = twWord0 10 k idx 0 := by
    simp only [ht1, blk193.res, rv_simp]
    bvsimp [t15, tx8, tx14, tx18, ofNat_eq_iff]
    unfold twWord0; congr 1
    have : idx / 2 ^ 32 < 4 := by omega
    rw [Nat.mod_eq_of_lt (a := idx / 2 ^ 32) (by omega), Nat.mod_eq_of_lt (a := k) (by omega)]
    omega
  have hcap1 : t1.readWords (BitVec.ofNat 64 (0x2650 + 176 * k + 32 + 16 * j)) 2 =
      wordsOf (st.1.getD sib []) := by
    rw [← hslots.getD sib (by omega), readWords_ofNat_two, readWords_ofNat_two]
    simp only [ht1, blk193.res, rv_simp]
    bvsimp [t15, tx13, tx18, tx19, ofNat_eq_iff]
    simp (disch := bvomega) only [if_pos, if_neg]
    have e : (u / 2 ^ j ^^^ 1) * 16 = 16 * sib := by rw [hsib, Nat.mul_comm]
    rw [e, Nat.add_comm (16 * sib) 196608]
  -- node loop
  let c : NodeCtx := ⟨10, k, idx, 1 + j, 0x30000, 2 ^ (9 - j)⟩
  have hB : ∀ a, 0x2650 + 176 * k + 32 ≤ a → a < 0x2650 + 176 * k + 192 →
      ¬ ((c.B ≤ a ∧ a < c.B + 32 * c.m) ∨ a = 456 ∨ a = 480 ∨ a = 488 ∨ a = 496 ∨ a = 504) := by
    intro a h1 h2; simp only [c]; omega
  have hnode := nodeLoop_sim codeAt_node210 codeAt_node227 c st.1 (by simp only [c]; rw [hlen, hpow])
    hvals (by simp only [c]; positivity) (by simp only [c]; norm_num) (by simp only [c])
    (by simp only [c]; omega) t1 pc1 y16 y17 y19 y5 (by simp only [c]; omega)
    (fun j' l r hj' hl hr => by
      simp only [c] at hj' ⊢
      show fmt (ftsNodeInput k idx (1 + j) j' l r) = pad64 (nodeFmt 10 k idx 0 (2 ^ (9 - j) + j') l r)
      rw [fmt_ftsNodeInput _ _ _ _ _ _ hl hr (by omega) (by omega),
        pad64_len64 _ (length_nodeFmt _ _ _ _ _ _ _ hl hr)]
      unfold heapIndex ftsA nodeFmt
      rw [show 10 - (1 + j) = 9 - j by omega])
    w448
    (by rw [f1.getMem (by norm_num) (by omega), tlo, ctx.nb8])
    (by rw [f1.getMem (by norm_num) (by omega), tframe.getMem (by norm_num) (by simp only [levW]; omega)]
        have := ctx.nbP; rw [readWords_ofNat_two] at this; simp only [List.cons.injEq] at this
        exact this.1)
    (by rw [f1.getMem (by norm_num) (by omega), tframe.getMem (by norm_num) (by simp only [levW]; omega)]
        have := ctx.nbP; rw [readWords_ofNat_two] at this; simp only [List.cons.injEq] at this
        exact this.2.1)
    (hslots.frame f1 (by omega) (by intro i hi; constructor <;> ((try simp only); omega)))
  have hstep : levelStep (ftsNodeInput k idx) u st (1 + j) =
      buildLevel (nodeFmt 10 k idx) (1 + j) st.1 >>= fun level =>
        pure (level, st.2 ++ [st.1.getD sib []]) := by
    simp only [levelStep, hsib, show 1 + j - 1 = j by omega]; rfl
  rw [hstep]
  refine Sim.steps hs1 (Sim.bind hnode (fun acc t2 hn => ?_))
  obtain ⟨-, hacc, haccv, haccs, -, pc2, x216, nregs, nframe⟩ := hn
  have pc2' : t2.pc = pcOf 229 := by rw [pc2, if_neg (lt_irrefl _)]
  have hs3 := symRun_sound blk229 codeAt_229 t2 pc2' (by simp only [blk229.res, rv_simp])
  have hc3 : blk229.res.cycles = 3 := rfl
  rw [hc3] at hs3
  set t3 := blk229.res.toState t2 with ht3
  have r3 : RegsEq t2 t3 [.x3, .x15] := by
    intro r hr; rw [ht3, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have f3 : Frame t2 t3 (fun _ => False) := by
    apply frame_toState; intro x hx hW; simp [blk229.res]
  have x215 : t2.getReg .x15 = BitVec.ofNat 64 (j + 1) := by
    rw [nregs.toRegsEq.get .x15, r1.get .x15, t15]
  have ft13 : Frame t t3 (fun x => (x = 0x1C0 ∨ x = 0x2650 + 176 * k + 32 + 16 * j ∨
      x = 0x2650 + 176 * k + 32 + 16 * j + 8) ∨ ((c.B ≤ x ∧ x < c.B + 32 * c.m) ∨ x = 456 ∨ x = 480 ∨
        x = 488 ∨ x = 496 ∨ x = 504) ∨ False) := f1.trans (nframe.toFrame.trans f3)
  refine Sim.pure_steps hs3 ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hacc, show 10 - (j + 1) = 9 - j by omega]
  · exact haccv
  · show Slots t3 0x30000 acc
    have hm512 : acc.length ≤ 512 := by rw [hacc]; exact hp9
    exact (show Slots t2 0x30000 acc from haccs).frame f3 (by omega) (by simp)
  · simp [hplen]
  · intro v hv; rcases List.mem_append.mp hv with hv | hv
    · exact hpvals v hv
    · simp at hv; subst hv
      simp only [List.getElem?_eq_getElem (show sib < st.1.length by omega), Option.getD_some]
      exact hvals _ (List.getElem_mem _)
  · apply Slots.snoc
    · exact hpath.frame ft13 (by omega) (by
        intro i hi; constructor <;> (simp only [c, or_false, not_or]; omega))
    · rw [hplen, f3.readWords _ _ (by omega) (by simp),
        nframe.toFrame.readWords _ _ (by omega) (by intro i hi; simp only [c]; omega), hcap1]
  · simp only [ht3, blk229.res, rv_simp, x215, ofNat_add_ofNat]
    rw [ofNat_slt_ofNat _ _ (by norm_num) (by omega)]
    by_cases h : j + 1 < 10
    · rw [if_pos h]; simp; omega
    · rw [if_neg h]; simp; omega
  · simp only [ht3, blk229.res, rv_simp, x215, ofNat_add_ofNat]
  · rw [r3.get .x17, nregs.toRegsEq.get .x17, y17, show 10 - (j + 1) = 9 - j by omega]
  · exact (((tregs.trans r1).trans nregs.toRegsEq).trans r3).mono (by decide)
  · exact (tframe.trans ft13).mono (by
      intro x hx; simp only [levW, c, or_false] at hx ⊢; omega)
  · rw [f3.getMem (by norm_num) (by simp), nframe.2, f1.getMem (by norm_num) (by omega), tlo]

end SigGolfCandidate.Radix27Sign

namespace SigGolfCandidate.Radix27Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

/-- **FORS levels** of tree `k` (from `fors_level_loop` with `LAM = 1`, `NCNT = 1024`). -/
theorem forsLevels_sim (k idx u : Nat) (hk : k < 14) (hidx : idx < 2 ^ 34) (hu : u < 1024)
    (t0 : MachineState) (ctx : LevCtx k idx u t0) (leaves : List Val) (hlen : leaves.length = 1024)
    (hvals : ∀ v ∈ leaves, v.length = 16) (hslots : Slots t0 0x30000 leaves)
    (hpc : t0.pc = pcOf 193) (h15 : t0.getReg .x15 = BitVec.ofNat 64 1)
    (h17 : t0.getReg .x17 = BitVec.ofNat 64 1024) :
    Sim image t0 (10 * 13334) ((List.range' 1 10).foldlM (levelStep (ftsNodeInput k idx) u)
      (leaves, [])) (LevInv k t0 10) := by
  apply Sim.foldlM_range' 1 10 _ _ (LevInv k t0) 13334
  · intro j hj st t h
    refine (forsLevel_body k idx u hk hidx hu t0 ctx j hj st t h).mono ?_ (fun _ _ h => h)
    have : 2 ^ (9 - j) ≤ 512 := by
      calc 2 ^ (9 - j) ≤ 2 ^ 9 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 512 := by norm_num
    omega
  · exact ⟨by norm_num, by simpa using hlen, hvals, hslots, rfl, by simp, Slots.nil _ _,
      by simpa using hpc, h15, by simpa using h17, RegsEq.refl _ _, Frame.refl _ _, rfl⟩

end SigGolfCandidate.Radix27Sign



end


section -- SignClone13.Fors

/-! ### cloned Fors -/

/-!
# `sign`, the FORS trees (`fors_loop`, instructions 112 .. 190)

`fors_sim` : from `fors_loop` with `KAP = 0`, the machine refines `signFors S N`: opening `k`
(`s_k`, path) at `SIG + 16 + 176 k`, root `k` at `RB2 + 32 + 16 k`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace SigGolfCandidate.Radix27Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

/-- `FW` register value. -/
def fwVal (idx : Nat) : Nat := 0x801 + 2 ^ 24 * (idx / 2 ^ 32)

/-- Facts at the start of the FORS loop. -/
structure ForsCtx (S : List Byte) (idx N : Nat) (tF : MachineState) : Prop where
  x5 : tF.getReg .x5 = 0
  x14 : tF.getReg .x14 = BitVec.ofNat 64 (fwVal idx)
  x19 : tF.getReg .x19 = BitVec.ofNat 64 0x30000
  us : ∀ k < 14, tF.getMem (BitVec.ofNat 64 (0x710 + 8 * k)) = BitVec.ofNat 64 (uOf N k)
  pb0 : hi32 (tF.getMem (BitVec.ofNat 64 0x6A0)) = 0
  cb0 : hi32 (tF.getMem (BitVec.ofNat 64 0xC0)) = 0
  pb8 : lo32 (tF.getMem (BitVec.ofNat 64 0x6A8)) = BitVec.ofNat 32 idx
  cb8 : lo32 (tF.getMem (BitVec.ofNat 64 0xC8)) = BitVec.ofNat 32 idx
  nb8 : lo32 (tF.getMem (BitVec.ofNat 64 0x1C8)) = BitVec.ofNat 32 idx
  pbP : tF.readWords (BitVec.ofNat 64 0x6B0) 2 = [0, 0]
  pbS : tF.readWords (BitVec.ofNat 64 0x6C0) 4 = wordsOf S
  cbP : tF.readWords (BitVec.ofNat 64 0xD0) 2 = [0, 0]
  nbP : tF.readWords (BitVec.ofNat 64 0x1D0) 2 = [0, 0]
  cbZ : tF.readWords (BitVec.ofNat 64 0xF0) 2 = [0, 0]

def forsW (a : Nat) : Prop :=
  a = 0x6A0 ∨ a = 0x6A8 ∨ a = 0xC0 ∨ a = 0xC8 ∨ (0xE0 ≤ a ∧ a < 0xF0) ∨ (0x140 ≤ a ∧ a < 0x160) ∨
    a = 0x1C0 ∨ a = 0x1C8 ∨
    (0x1E0 ≤ a ∧ a < 0x200) ∨ (0x30000 ≤ a ∧ a < 0x30000 + 16 * 1025) ∨
    (0x2650 + 16 ≤ a ∧ a < 0x2650 + 2480) ∨ (0x240 ≤ a ∧ a < 0x320)

def forsRegs : List Reg :=
  [.x1, .x2, .x3, .x8, .x9, .x10, .x11, .x12, .x13, .x15, .x16, .x17, .x18, .x29]

/-- An opening `(s, path)` stored at `B` (`s`, then the 10 path nodes). -/
def OpenAt (t : MachineState) (B : Nat) (o : Val × List Val) : Prop :=
  o.1.length = 16 ∧ o.2.length = 10 ∧ (∀ v ∈ o.2, v.length = 16) ∧ Slots t B (o.1 :: o.2)

/-- Invariant after `k` trees. -/
def ForsInv (tF : MachineState) (k : Nat) (st : List (Val × List Val) × List Val) (t : MachineState) :
    Prop :=
  k ≤ 14 ∧ st.1.length = k ∧ st.2.length = k ∧
  (∀ i (hi : i < st.1.length), OpenAt t (0x2650 + 16 + 176 * i) st.1[i]) ∧
  (∀ v ∈ st.2, v.length = 16) ∧ Slots t 0x240 st.2 ∧
  t.pc = (if k < 14 then pcOf 156 else pcOf 241) ∧ t.getReg .x8 = BitVec.ofNat 64 k ∧
  t.getReg .x18 = BitVec.ofNat 64 (0x2650 + 176 * k) ∧
  RegsEq tF t forsRegs ∧ Frame tF t forsW ∧
  lo32 (t.getMem (BitVec.ofNat 64 0x6A8)) = lo32 (tF.getMem (BitVec.ofNat 64 0x6A8)) ∧
  lo32 (t.getMem (BitVec.ofNat 64 0xC8)) = lo32 (tF.getMem (BitVec.ofNat 64 0xC8)) ∧
  lo32 (t.getMem (BitVec.ofNat 64 0x1C8)) = lo32 (tF.getMem (BitVec.ofNat 64 0x1C8)) ∧
  hi32 (t.getMem (BitVec.ofNat 64 0x6A0)) = hi32 (tF.getMem (BitVec.ofNat 64 0x6A0)) ∧
  hi32 (t.getMem (BitVec.ofNat 64 0xC0)) = hi32 (tF.getMem (BitVec.ofNat 64 0xC0))

theorem buildFtsTree_bind {β : Type} (S : List Byte) (k idx u : Nat)
    (g : Val × List Val × Val → OracleComp HashSpec β) :
    buildFtsTree S k idx 10 u >>= g =
      buildFtsLeaves S k idx 10 u >>= fun p =>
        (List.range' 1 10).foldlM (levelStep (ftsNodeInput k idx) u) (p.1, []) >>= fun st =>
          g (p.2, st.2, st.1.getD 0 []) := by
  simp only [buildFtsTree, buildLevels, bind_assoc, pure_bind]

theorem fors_body (S : List Byte) (hS : S.length = 32) (idx N : Nat) (hidx : idx < 2 ^ 34)
    (hu : ∀ k, uOf N k < 1024) (tF : MachineState) (ctx : ForsCtx S idx N tF) (k : Nat) (hk : k < 14)
    (st : List (Val × List Val) × List Val) (t : MachineState) (hinv : ForsInv tF k st t) :
    Sim image t (8 + (512 * 70 + (2 + (10 * 13334 + 9))))
      (do
        let (s, path, root) ← buildFtsTree S k idx 10 (uOf N k)
        pure (st.1 ++ [(s, path)], st.2 ++ [root]))
      (ForsInv tF (k + 1)) := by
  obtain ⟨-, hl1, hl2, hopen, hrv, hroots, tpc, t8, t18, tregs, tframe, lo1, lo2, lo3, hi1, hi2⟩ := hinv
  have tpc' : t.pc = pcOf 156 := by rw [tpc, if_pos hk]
  have tx5 : t.getReg .x5 = 0 := by rw [tregs.get .x5 (by decide), ctx.x5]
  have tx14 : t.getReg .x14 = BitVec.ofNat 64 (fwVal idx) := by rw [tregs.get .x14 (by decide), ctx.x14]
  have tx19 : t.getReg .x19 = BitVec.ofNat 64 0x30000 := by rw [tregs.get .x19 (by decide), ctx.x19]
  have hu' := hu k
  have hi4 : idx / 2 ^ 32 < 4 := by omega
  -- block 112: tree setup
  have hs1 := symRun_sound blk156 codeAt_156 t tpc' (by
    simp only [blk156.res, rv_simp]; bvsimp [t8, accessValid_ofNat]; omega)
  have hc1 : blk156.res.cycles = 8 := rfl
  rw [hc1] at hs1
  set t1 := blk156.res.toState t with ht1
  have f1 : Frame t t1 (fun x => x = 0x6A0 ∨ x = 0xC0) := by
    apply frame_toState; intro x hx hW
    simp only [blk156.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq, ofNat_eq_iff]
    omega
  have r1 : RegsEq t t1 [.x3, .x9, .x13, .x29] := by
    intro r hr; rw [ht1, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have y13 : t1.getReg .x13 = BitVec.ofNat 64 (uOf N k) := by
    simp only [ht1, blk156.res, rv_simp]; bvsimp [t8]
    rw [show k * 8 + 1808 = 0x710 + 8 * k by ring, tframe.getMem (by omega) (by simp only [forsW]; omega),
      ctx.us k hk]
  have y9 : t1.getReg .x9 = BitVec.ofNat 64 0 := by simp only [ht1, blk156.res, rv_simp]
  have pc1 : t1.pc = pcOf 164 := by simp only [ht1, blk156.res, rv_simp]
  have hfw : fwVal idx + k * 65536 < 2 ^ 32 := by unfold fwVal; omega
  have pb0 : t1.getMem (BitVec.ofNat 64 0x6A0) = twWord0 8 k idx 0 := by
    simp only [ht1, blk156.res, rv_simp]; bvsimp [t8, tx14, ofNat_eq_iff]
    refine (word_of_halves _ (fwVal idx + k * 65536) 0 (by rw [lo32_replace0]) (by
      rw [hi32_replace0, hi1, ctx.pb0]; rfl)).trans ?_
    unfold twWord0 fwVal; congr 1; omega
  have cb0 : t1.getMem (BitVec.ofNat 64 0xC0) = twWord0 9 k idx 0 := by
    simp only [ht1, blk156.res, rv_simp]; bvsimp [t8, tx14, ofNat_eq_iff]
    refine (word_of_halves _ (fwVal idx + k * 65536 + 256) 0 (by rw [lo32_replace0]) (by
      rw [hi32_replace0, hi2, ctx.cb0]; rfl)).trans ?_
    unfold twWord0 fwVal; congr 1; omega
  have hWt : ∀ x, ¬ forsW x → x ≠ 0x6A0 → x ≠ 0xC0 → ¬ (x = 0x6A0 ∨ x = 0xC0) := by
    intro x _ h1 h2 h; omega
  have lctx : LeafCtx S k idx (uOf N k) t1 := by
    refine ⟨pb0, ?_, ?_, ?_, cb0, ?_, ?_, ?_, ?_, y13, ?_, ?_⟩
    · rw [f1.getMem (by norm_num) (by omega), lo1, ctx.pb8]
    · rw [f1.readWords _ _ (by norm_num) (by intro i hi; omega),
        tframe.readWords _ _ (by norm_num) (by intro i hi; simp only [forsW]; omega), ctx.pbP]
    · rw [f1.readWords _ _ (by norm_num) (by intro i hi; omega),
        tframe.readWords _ _ (by norm_num) (by intro i hi; simp only [forsW]; omega), ctx.pbS]
    · rw [f1.getMem (by norm_num) (by omega), lo2, ctx.cb8]
    · rw [f1.readWords _ _ (by norm_num) (by intro i hi; omega),
        tframe.readWords _ _ (by norm_num) (by intro i hi; simp only [forsW]; omega), ctx.cbP]
    · rw [f1.readWords _ _ (by norm_num) (by intro i hi; omega),
        tframe.readWords _ _ (by norm_num) (by intro i hi; simp only [forsW]; omega), ctx.cbZ]
    · rw [r1.get .x5, tx5]
    · rw [r1.get .x18, t18]
    · rw [r1.get .x19, tx19]
  rw [buildFtsTree_bind]
  refine Sim.steps hs1 (Sim.bind (forsLeaves_sim S hS k idx (uOf N k) hk hidx hu' t1 lctx pc1 y9)
    (fun p t2 h2 => ?_))
  obtain ⟨-, hlv, hlvv, hlvs, hsec, pc2, -, lregs, lframe, llo1, llo2⟩ := h2
  have pc2' : t2.pc = pcOf 191 := by rw [pc2]; rfl
  obtain ⟨hsl, hsw⟩ := hsec hu'
  -- block 140
  have hs3 := symRun_sound blk191 codeAt_191 t2 pc2' (by simp only [blk191.res, rv_simp])
  have hc3 : blk191.res.cycles = 2 := rfl
  rw [hc3] at hs3
  set t3 := blk191.res.toState t2 with ht3
  have f3 : Frame t2 t3 (fun _ => False) := by
    apply frame_toState; intro x hx hW; simp [blk191.res]
  have r3 : RegsEq t2 t3 [.x15, .x17] := by
    intro r hr; rw [ht3, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have ft13 : Frame t t3 (fun x => (x = 0x6A0 ∨ x = 0xC0) ∨ leafW k x) :=
    (f1.trans (lframe.trans f3)).mono (by
      intro x hx; rcases hx with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact h.elim)
  have rt13 : RegsEq t t3 ([.x3, .x9, .x13, .x29] ++ leafRegs ++ [.x15, .x17]) :=
    (r1.trans lregs).trans r3
  have vctx : LevCtx k idx (uOf N k) t3 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [rt13.get .x5, tx5]
    · rw [rt13.get .x8, t8]
    · rw [r3.get .x13, lregs.get .x13 (by decide), y13]
    · rw [rt13.get .x14, tx14]; rfl
    · rw [rt13.get .x18, t18]
    · rw [rt13.get .x19, tx19]
    · rw [ft13.getMem (by norm_num) (by simp only [leafW]; omega), lo3, ctx.nb8]
    · rw [ft13.readWords _ _ (by norm_num) (by intro i hi; simp only [leafW]; omega),
        tframe.readWords _ _ (by norm_num) (by intro i hi; simp only [forsW]; omega), ctx.nbP]
  refine Sim.steps hs3 (Sim.bind (forsLevels_sim k idx (uOf N k) hk hidx hu' t3 vctx p.1 hlv hlvv
    (hlvs.frame f3 (by omega) (by simp)) (by simp only [ht3, blk191.res, rv_simp])
    (by simp only [ht3, blk191.res, rv_simp]) (by simp only [ht3, blk191.res, rv_simp]))
    (fun st' t4 h4 => ?_))
  obtain ⟨-, hl4, hv4, hs4, hp4, hpv4, hps4, pc4, -, -, vregs, vframe, vlo⟩ := h4
  have pc4' : t4.pc = pcOf 232 := by rw [pc4]; rfl
  have rt4 : RegsEq t t4 ([.x3, .x9, .x13, .x29] ++ leafRegs ++ [.x15, .x17] ++ levRegs) :=
    rt13.trans vregs
  have x48 : t4.getReg .x8 = BitVec.ofNat 64 k := by rw [rt4.get .x8, t8]
  have x418 : t4.getReg .x18 = BitVec.ofNat 64 (0x2650 + 176 * k) := by rw [rt4.get .x18, t18]
  have x419 : t4.getReg .x19 = BitVec.ofNat 64 0x30000 := by rw [rt4.get .x19, tx19]
  -- block 182: root, next tree
  have hs5 := symRun_sound blk232 codeAt_232 t4 pc4' (by
    simp only [blk232.res, rv_simp]; bvsimp [x48, x419, accessValid_ofNat]; omega)
  have hc5 : blk232.res.cycles = 9 := rfl
  rw [hc5] at hs5
  set t5 := blk232.res.toState t4 with ht5
  have f5 : Frame t4 t5 (fun x => x = 0x240 + 16 * k ∨ x = 0x240 + 16 * k + 8) := by
    apply frame_toState; intro x hx hW
    simp only [blk232.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq]
    bvsimp [x48, ofNat_eq_iff]
    omega
  have r5 : RegsEq t4 t5 [.x1, .x2, .x3, .x8, .x18] := by
    intro r hr; rw [ht5, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have root5 : t5.readWords (BitVec.ofNat 64 (0x240 + 16 * k)) 2 = wordsOf (st'.1.getD 0 []) := by
    rw [← hs4.getD 0 (by rw [hl4]; norm_num), readWords_ofNat_two, readWords_ofNat_two]
    simp only [ht5, blk232.res, rv_simp]
    bvsimp [x48, x419, ofNat_eq_iff]
    simp (disch := bvomega) only [if_pos, if_neg]
  -- the frame from `t` to `t5`
  have ft5 : Frame t t5 (fun x => ((x = 0x6A0 ∨ x = 0xC0) ∨ leafW k x) ∨ levW k x ∨
      (x = 0x240 + 16 * k ∨ x = 0x240 + 16 * k + 8)) := ft13.trans (vframe.trans f5)
  have hsec5 : t5.readWords (BitVec.ofNat 64 (0x2650 + 176 * k + 16)) 2 = wordsOf p.2 := by
    rw [f5.readWords _ _ (by omega) (by intro i hi; omega),
      vframe.readWords _ _ (by omega) (by intro i hi; simp only [levW]; omega),
      f3.readWords _ _ (by omega) (by simp), hsw]
  have hpath5 : Slots t5 (0x2650 + 176 * k + 32) st'.2 :=
    hps4.frame f5 (by omega) (by intro i hi; rw [hp4] at hi; constructor <;> omega)
  refine Sim.pure_steps hs5 ⟨by omega, by simp [hl1], by simp [hl2], ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    simp only [List.length_append, List.length_singleton] at hi
    by_cases hik : i < st.1.length
    · rw [List.getElem_append_left hik]
      obtain ⟨o1, o2, o3, o4⟩ := hopen i hik
      refine ⟨o1, o2, o3, o4.frame ft5 (by simp [o2]; omega) ?_⟩
      intro j hj
      simp only [List.length_cons, o2] at hj
      simp only [leafW, levW]
      constructor <;> omega
    · have : i = st.1.length := by omega
      subst this
      rw [List.getElem_append_right (le_refl _)]
      simp only [Nat.sub_self, List.getElem_singleton]
      refine ⟨hsl, hp4, hpv4, Slots.cons ?_ ?_⟩
      · rw [hl1, show 0x2650 + 16 + 176 * k = 0x2650 + 176 * k + 16 by ring]; exact hsec5
      · rw [hl1, show 0x2650 + 16 + 176 * k + 16 = 0x2650 + 176 * k + 32 by ring]; exact hpath5
  · intro v hv; rcases List.mem_append.mp hv with hv | hv
    · exact hrv v hv
    · simp at hv; subst hv
      simp only [List.getElem?_eq_getElem (show 0 < st'.1.length by rw [hl4]; norm_num),
        Option.getD_some]
      exact hv4 _ (List.getElem_mem _)
  · apply Slots.snoc
    · exact hroots.frame ft5 (by omega) (by
        intro i hi; simp only [leafW, levW]; constructor <;> omega)
    · rw [hl2]; exact root5
  · simp only [ht5, blk232.res, rv_simp]
    bvsimp [x48, ofNat_bne_ofNat]
    by_cases h : k + 1 < 14
    · rw [if_pos h, if_pos (by simp; omega)]
    · rw [if_neg h, if_neg (by simp; omega)]
  · simp only [ht5, blk232.res, rv_simp]; bvsimp [x48]
  · simp only [ht5, blk232.res, rv_simp]; bvsimp [x418]
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]; omega
  · exact ((tregs.trans rt4).trans r5).mono (by decide)
  · exact (tframe.trans ft5).mono (by intro x hx; simp only [forsW, leafW, levW] at hx ⊢; omega)
  · rw [f5.getMem (by norm_num) (by omega), vframe.getMem (by norm_num) (by simp only [levW]; omega),
      f3.getMem (by norm_num) (by simp), llo1, f1.getMem (by norm_num) (by omega), lo1]
  · rw [f5.getMem (by norm_num) (by omega), vframe.getMem (by norm_num) (by simp only [levW]; omega),
      f3.getMem (by norm_num) (by simp), llo2, f1.getMem (by norm_num) (by omega), lo2]
  · rw [f5.getMem (by norm_num) (by omega), vlo, ft13.getMem (by norm_num) (by simp only [leafW]; omega),
      lo3]
  · rw [f5.getMem (by norm_num) (by omega), vframe.getMem (by norm_num) (by simp only [levW]; omega),
      f3.getMem (by norm_num) (by simp), lframe.getMem (by norm_num) (by simp only [leafW]; omega), pb0,
      ctx.pb0, twWord0, hi32_ofNat]
    rw [Nat.div_eq_of_lt (by omega)]; rfl
  · rw [f5.getMem (by norm_num) (by omega), vframe.getMem (by norm_num) (by simp only [levW]; omega),
      f3.getMem (by norm_num) (by simp), lframe.getMem (by norm_num) (by simp only [leafW]; omega), cb0,
      ctx.cb0, twWord0, hi32_ofNat]
    rw [Nat.div_eq_of_lt (by omega)]; rfl

end SigGolfCandidate.Radix27Sign

namespace SigGolfCandidate.Radix27Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

/-- Cycle bound of one FORS tree. -/
abbrev forsTreeW : Nat := 8 + (512 * 70 + (2 + (10 * 13334 + 9)))

/-- **FORS**: the 14 trees. -/
theorem fors_sim (S : List Byte) (hS : S.length = 32) (N : Nat) (tF : MachineState)
    (ctx : ForsCtx S (idxOf N) N tF) (hpc : tF.pc = pcOf 156)
    (h8 : tF.getReg .x8 = BitVec.ofNat 64 0) (h18 : tF.getReg .x18 = BitVec.ofNat 64 0x2650) :
    Sim image tF (14 * forsTreeW) (signFors S N) (ForsInv tF 14) := by
  have hidx : idxOf N < 2 ^ 34 := Nat.mod_lt _ (by norm_num)
  have hu : ∀ k, uOf N k < 1024 := fun k => Nat.mod_lt _ (by norm_num)
  unfold signFors ftsTrees ftsA
  apply Sim.foldlM_range 14 _ ([], []) (ForsInv tF) forsTreeW
  · intro k hk st t h
    exact fors_body S hS (idxOf N) N hidx hu tF ctx k hk st t h
  · exact ⟨by norm_num, rfl, rfl, fun i hi => absurd hi (by simp), by simp, Slots.nil _ _,
      by simpa using hpc, h8, by simpa using h18, RegsEq.refl _ _, Frame.refl _ _, rfl, rfl, rfl,
      rfl, rfl⟩

end SigGolfCandidate.Radix27Sign



end


section -- SignClone13.DigOk

/-! ### cloned DigOk -/

/-!
# `sign`: `dig_ok` (instructions 46 .. 111)

`digok_run` : after an admissible digest, `rho` goes to the signature, `idx` to `s6`, the `u_k` to
`US`, and the FORS tweak words are set up (`ForsCtx`).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace SigGolfCandidate.Radix27Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

/-- The `u_k` dwords as the machine computes them from the digest dwords. -/
def ukList (w0 w1 w2 : Word) : List Word :=
  [(w0 >>> 34) &&& 1023, (w0 >>> 44) &&& 1023, w0 >>> 54, w1 &&& 1023, (w1 >>> 10) &&& 1023,
   (w1 >>> 20) &&& 1023, (w1 >>> 30) &&& 1023, (w1 >>> 40) &&& 1023, (w1 >>> 50) &&& 1023,
   ((w2 &&& 63) <<< 4) + (w1 >>> 60), (w2 >>> 6) &&& 1023, (w2 >>> 16) &&& 1023,
   (w2 >>> 26) &&& 1023, (w2 >>> 36) &&& 1023]

-- Memory effect of `dig_ok` (kernel-checked with a variable state).
kernel_theorem blk90_us : ∀ t : MachineState,
    (blk90.res.toState t).readWords (BitVec.ofNat 64 0x710) 14 =
      ukList (t.getMem (BitVec.ofNat 64 0x160)) (t.getMem (BitVec.ofNat 64 0x168))
        (t.getMem (BitVec.ofNat 64 0x170))
kernel_theorem blk90_sig : ∀ t : MachineState,
    (blk90.res.toState t).readWords (BitVec.ofNat 64 0x2650) 2 = t.readWords (BitVec.ofNat 64 0x30) 2

theorem ukList_eq (A : Nat) (hA : A < 2 ^ 256) :
    ukList (BitVec.ofNat 64 (A % 2 ^ 64)) (BitVec.ofNat 64 (A / 2 ^ 64 % 2 ^ 64))
      (BitVec.ofNat 64 (A / 2 ^ 128 % 2 ^ 64)) =
      (List.range 14).map (fun k => BitVec.ofNat 64 (uOf (A % 2 ^ 184) k)) := by
  simp only [ukList, List.range_succ, List.range_zero, List.map_append, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, List.cons.injEq, and_true]
  simp only [uOf, totalH, ftsA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_add,
      BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Nat.reducePow, Nat.reduceMul,
      Nat.reduceAdd, show (1023 : Word).toNat = 1023 from rfl, show (63 : Word).toNat = 63 from rfl]
    first
      | omega
      | (rw [show (1023 : Nat) = 2 ^ 10 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]; omega)
      | (rw [show (63 : Nat) = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]; omega)

end SigGolfCandidate.Radix27Sign

namespace SigGolfCandidate.Radix27Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

def digokW (a : Nat) : Prop :=
  a = 0x2650 ∨ a = 0x2658 ∨ (0x710 ≤ a ∧ a < 0x780) ∨ a = 0x6A8 ∨ a = 0xC8 ∨ a = 0x1C8 ∨ a = 0x228 ∨
    a = 0x6A0 ∨ a = 0xC0

def digokRegs : List Reg := [.x1, .x2, .x3, .x4, .x8, .x14, .x18, .x19, .x22, .x28, .x29]

theorem idxExpr_eq (A : Nat) :
    (BitVec.ofNat 64 (A % 18446744073709551616) <<< 30) >>> 30 = BitVec.ofNat 64 (A % 17179869184) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  omega

theorem digok_run (S : List Byte) (rho : Val) (ans : BitVec 256) (t : MachineState)
    (tpc : t.pc = pcOf 90) (t5 : t.getReg .x5 = 0)
    (hd : t.readWords (BitVec.ofNat 64 0x160) 3 =
      [ans.extractLsb' 0 64, ans.extractLsb' 64 64, ans.extractLsb' 128 64])
    (hpbP : t.readWords (BitVec.ofNat 64 0x6B0) 2 = [0, 0])
    (hpbS : t.readWords (BitVec.ofNat 64 0x6C0) 4 = wordsOf S)
    (hcbP : t.readWords (BitVec.ofNat 64 0xD0) 2 = [0, 0])
    (hnbP : t.readWords (BitVec.ofNat 64 0x1D0) 2 = [0, 0])
    (hcbZ : t.readWords (BitVec.ofNat 64 0xF0) 2 = [0, 0]) :
    ∃ tF, Steps image t 66 66 tF ∧ ForsCtx S (idxOf (ans.toNat % 2 ^ 184)) (ans.toNat % 2 ^ 184) tF ∧
      tF.pc = pcOf 156 ∧ tF.getReg .x8 = BitVec.ofNat 64 0 ∧
      tF.getReg .x18 = BitVec.ofNat 64 0x2650 ∧
      tF.getReg .x22 = BitVec.ofNat 64 (idxOf (ans.toNat % 2 ^ 184)) ∧
      tF.readWords (BitVec.ofNat 64 0x2650) 2 = t.readWords (BitVec.ofNat 64 0x30) 2 ∧
      lo32 (tF.getMem (BitVec.ofNat 64 0x228)) = BitVec.ofNat 32 (idxOf (ans.toNat % 2 ^ 184)) ∧
      hi32 (tF.getMem (BitVec.ofNat 64 0x228)) = hi32 (t.getMem (BitVec.ofNat 64 0x228)) ∧
      RegsEq t tF digokRegs ∧ Frame t tF digokW := by
  set A := ans.toNat with hA
  have hAl : A < 2 ^ 256 := ans.isLt
  have e0 : ans.extractLsb' 0 64 = BitVec.ofNat 64 (A % 2 ^ 64) := by
    apply BitVec.eq_of_toNat_eq; simp [hA]
  have e1 : ans.extractLsb' 64 64 = BitVec.ofNat 64 (A / 2 ^ 64 % 2 ^ 64) := by
    apply BitVec.eq_of_toNat_eq; simp [hA, Nat.shiftRight_eq_div_pow]
  have e2 : ans.extractLsb' 128 64 = BitVec.ofNat 64 (A / 2 ^ 128 % 2 ^ 64) := by
    apply BitVec.eq_of_toNat_eq; simp [hA, Nat.shiftRight_eq_div_pow]
  have m160 : t.getMem (BitVec.ofNat 64 0x160) = BitVec.ofNat 64 (A % 2 ^ 64) := by
    have := getMem_of_readWords t 3 0x160 0 _ hd (by norm_num); simpa [e0] using this
  have m168 : t.getMem (BitVec.ofNat 64 0x168) = BitVec.ofNat 64 (A / 2 ^ 64 % 2 ^ 64) := by
    have := getMem_of_readWords t 3 0x160 1 _ hd (by norm_num); simpa [e1] using this
  have m170 : t.getMem (BitVec.ofNat 64 0x170) = BitVec.ofNat 64 (A / 2 ^ 128 % 2 ^ 64) := by
    have := getMem_of_readWords t 3 0x160 2 _ hd (by norm_num); simpa [e2] using this
  have hidx : idxOf (A % 2 ^ 184) = A % 2 ^ 34 := by unfold idxOf totalH; omega
  have hidx' : idxOf (A % 24519928653854221733733552434404946937899825954937634816) = A % 17179869184 := by
    unfold idxOf totalH; omega
  have hs := symRun_sound blk90 codeAt_90 t tpc (by simp only [blk90.res, rv_simp])
  have hc : blk90.res.cycles = 66 := rfl
  have hk : blk90.res.steps = 66 := rfl
  rw [hc, hk] at hs
  set tF := blk90.res.toState t with htF
  have f : Frame t tF digokW := by
    apply frame_toState; intro x hx hW
    simp only [blk90.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq, ofNat_eq_iff]
    simp only [digokW] at hW
    omega
  have r : RegsEq t tF digokRegs := by
    intro r hr; rw [htF, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have x22 : tF.getReg .x22 = BitVec.ofNat 64 (A % 2 ^ 34) := by
    simp only [htF, blk90.res, rv_simp, m160, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow,
      idxExpr_eq]
  have hus := blk90_us t
  rw [m160, m168, m170, ukList_eq A hAl] at hus
  refine ⟨tF, hs, ?_, by simp only [htF, blk90.res, rv_simp], by simp only [htF, blk90.res, rv_simp],
    by simp only [htF, blk90.res, rv_simp], by rw [x22, hidx], blk90_sig t, ?_, ?_, r, f⟩
  · refine ⟨by rw [r.get .x5, t5], ?_, by simp only [htF, blk90.res, rv_simp], ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [htF, blk90.res, rv_simp, m160, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow,
        idxExpr_eq]
      unfold fwVal; simp only [Nat.reducePow, hidx']
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
        Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, show (2049 : Word).toNat = 2049 from rfl]
      omega
    · intro k hk
      rw [getMem_of_readWords tF 14 0x710 k _ hus hk]
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]; rfl
    · simp only [htF, blk90.res, rv_simp]; simp
    · simp only [htF, blk90.res, rv_simp]; simp
    · simp only [htF, blk90.res, rv_simp, m160, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow,
        idxExpr_eq]
      simp only [if_true, ite_true, lo32_replace0, truncate32_ofNat, hidx', Nat.zero_div, ofNat_eq_iff,
        Nat.reducePow, Nat.reduceMod, Nat.reduceEqDiff, if_false, ite_false]
    · simp only [htF, blk90.res, rv_simp, m160, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow,
        idxExpr_eq]
      simp only [if_true, ite_true, lo32_replace0, truncate32_ofNat, hidx', Nat.zero_div, ofNat_eq_iff,
        Nat.reducePow, Nat.reduceMod, Nat.reduceEqDiff, if_false, ite_false]
    · simp only [htF, blk90.res, rv_simp, m160, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow,
        idxExpr_eq]
      simp only [if_true, ite_true, lo32_replace0, truncate32_ofNat, hidx', Nat.zero_div, ofNat_eq_iff,
        Nat.reducePow, Nat.reduceMod, Nat.reduceEqDiff, if_false, ite_false]
    · rw [f.readWords _ _ (by norm_num) (by intro i hi; simp only [digokW]; omega), hpbP]
    · rw [f.readWords _ _ (by norm_num) (by intro i hi; simp only [digokW]; omega), hpbS]
    · rw [f.readWords _ _ (by norm_num) (by intro i hi; simp only [digokW]; omega), hcbP]
    · rw [f.readWords _ _ (by norm_num) (by intro i hi; simp only [digokW]; omega), hnbP]
    · rw [f.readWords _ _ (by norm_num) (by intro i hi; simp only [digokW]; omega), hcbZ]
  · simp only [htF, blk90.res, rv_simp, m160, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow,
      idxExpr_eq]
    simp only [if_true, ite_true, lo32_replace0, truncate32_ofNat, hidx', Nat.zero_div, ofNat_eq_iff,
        Nat.reducePow, Nat.reduceMod, Nat.reduceEqDiff, if_false, ite_false]
  · simp only [htF, blk90.res, rv_simp]; simp

end SigGolfCandidate.Radix27Sign



end


section -- SignClone13.Pack

/-! ### cloned Pack -/

/-!
# `sign`: the pack (instructions 614 .. 3394)

`pack_bytes` : after the pack, the signature layer region `SIG + 2480 ..` holds the staged bytes
in signature order: layer `l` = the 4 counter bytes at `STG + 856 l`, then its body at
`STG + 856 l + 8`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 100000

namespace SigGolfCandidate.Radix27Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref SigGolfCandidate.Mem

theorem packTab_length : packTab.length = 491 := by decide +kernel

/-- Table sanity (checked by the kernel). -/
theorem packTab_ok : packTab.all (fun e => decide (e.1 ≤ 2) &&
    (if e.1 = 0 then decide (e.2.1 % 8 = 0) else decide (e.2.1 % 4 = 0 ∧ e.2.2 % 4 = 0)) &&
    decide (e.2.1 + 8 < 0x2650 ∧ e.2.2 + 8 < 0x2650)) = true := by decide +kernel

/-- The stage address of byte `i` of the dword of entry `e`. -/
def srcA (e : Nat × Nat × Nat) (i : Nat) : Nat :=
  if e.1 = 0 then e.2.1 + i else if i < 4 then e.2.1 + i else e.2.2 + (i - 4)

theorem packDW_byte (t : MachineState) (e : Nat × Nat × Nat) (he : e ∈ packTab) (i : Nat) (hi : i < 8)
    (h2 : e.1 = 2 → i < 4) :
    extractByte (packDW t e) i = t.getByte (BitVec.ofNat 64 (srcA e i)) := by
  have hok := List.all_eq_true.mp packTab_ok e he
  obtain ⟨k, lo, hi'⟩ := e
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨hk, hal⟩, hlo, hhi⟩ := hok
  have hbo : ∀ a, a % 4 = 0 → a + 8 < 2 ^ 64 → byteOffset (BitVec.ofNat 64 a) = 0 ∨
      byteOffset (BitVec.ofNat 64 a) = 4 := by
    intro a ha hb; rw [byteOffset_ofNat (by omega)]; omega
  have hgb : ∀ a j, a % 4 = 0 → a + 8 < 0x2650 → j < 4 →
      extractByte (t.getMem (alignToDword (BitVec.ofNat 64 a))) (byteOffset (BitVec.ofNat 64 a) + j) =
        t.getByte (BitVec.ofNat 64 (a + j)) := by
    intro a j ha hb hj
    rw [byteOffset_ofNat (by omega), show alignToDword (BitVec.ofNat 64 a) = BitVec.ofNat 64 (a / 8 * 8) by
      apply BitVec.eq_of_toNat_eq; rw [alignToDword_toNat]; simp; omega]
    rw [← getByte_aligned' t (a / 8 * 8) (a % 8 + j) (by omega) (by omega) (by omega)]
    congr 2; omega
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 by omega) with rfl | rfl | rfl
  · simp only [packDW, srcA, if_true, decide_eq_true_eq] at hal ⊢
    rw [getByte_aligned' t lo i hal hi (by omega)]
  · simp only [packDW, srcA, if_neg (show (1 : Nat) ≠ 0 by decide), decide_eq_true_eq] at hal ⊢
    rw [extractByte_pair _ _ _ _ i (hbo lo hal.1 (by omega)) (hbo hi' hal.2 (by omega)) hi]
    split
    · exact hgb lo i hal.1 hlo (by omega)
    · exact hgb hi' (i - 4) hal.2 hhi (by omega)
  · simp only [packDW, srcA, if_neg (show (2 : Nat) ≠ 0 by decide), decide_eq_true_eq] at hal ⊢
    have := h2 rfl
    rw [extractByte_lwuW _ _ i (hbo lo hal.1 (by omega)) hi, if_pos this, if_pos this]
    exact hgb lo i hal.1 hlo this

theorem packTab_kind2_ok : (packTab.take 490).all (fun e => decide (e.1 ≠ 2)) = true := by
  decide +kernel

theorem packTab_kind2 : ∀ j < 490, (packTab.getD j (0, 0, 0)).1 ≠ 2 := by
  intro j hj
  rw [getD_of_lt (by rw [packTab_length]; omega)]
  have hm : packTab[j]'(by rw [packTab_length]; omega) ∈ packTab.take 490 :=
    List.mem_iff_getElem.mpr ⟨j, by simp [packTab_length]; omega, by simp⟩
  simpa using List.all_eq_true.mp packTab_kind2_ok _ hm

/-- **Pack**: the signature layer region after the pack, as stage bytes. -/
theorem pack_bytes (t u : MachineState)
    (hw : u.readWords (BitVec.ofNat 64 (0x2650 + 2480)) 491 = packTab.map (packDW t)) :
    bytesAt u (0x2650 + 2480) 3924 =
      (List.range 3924).map (fun p =>
        t.getByte (BitVec.ofNat 64 (srcA (packTab.getD (p / 8) (0, 0, 0)) (p % 8)))) := by
  apply List.ext_getElem (by simp)
  intro p h1 h2
  simp only [length_bytesAt] at h1
  simp only [bytesAt, List.getElem_map, List.getElem_range]
  rw [show 0x2650 + 2480 + p = (0x2650 + 2480 + 8 * (p / 8)) + p % 8 by omega,
    getByte_aligned' _ _ _ (by omega) (by omega) (by omega),
    getMem_of_readWords _ 491 _ (p / 8) _ hw (by omega)]
  have hmem : packTab.getD (p / 8) (0, 0, 0) ∈ packTab := by
    rw [getD_of_lt (by rw [packTab_length]; omega)]; exact List.getElem_mem _
  rw [show (packTab.map (packDW t)).getD (p / 8) 0 = packDW t (packTab.getD (p / 8) (0, 0, 0)) by
    rw [getD_of_lt (by simp [packTab_length]; omega), getD_of_lt (by rw [packTab_length]; omega)]
    simp]
  apply packDW_byte t _ hmem _ (by omega)
  intro h
  by_cases hp : p / 8 < 490
  · exact absurd h (packTab_kind2 _ hp)
  · omega

end SigGolfCandidate.Radix27Sign

namespace SigGolfCandidate.Radix27Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref SigGolfCandidate.Mem

/-- The source addresses of the table entries, 8 per entry. -/
def blocks8 (T : List (Nat × Nat × Nat)) : List Nat := T.flatMap (fun e => (List.range 8).map (srcA e))

theorem length_blocks8 (T : List (Nat × Nat × Nat)) : (blocks8 T).length = 8 * T.length := by
  induction T with
  | nil => rfl
  | cons e T ih => simp only [blocks8, List.flatMap_cons, List.length_append, List.length_map,
      List.length_range] at ih ⊢; rw [ih, List.length_cons]; ring

theorem getElem_blocks8 (T : List (Nat × Nat × Nat)) (p : Nat) (hp : p < (blocks8 T).length) :
    (blocks8 T)[p] = srcA (T.getD (p / 8) (0, 0, 0)) (p % 8) := by
  induction T generalizing p with
  | nil => simp [blocks8] at hp
  | cons e T ih =>
    simp only [blocks8, List.flatMap_cons] at hp ⊢
    by_cases h8 : p < 8
    · rw [List.getElem_append_left (by simp; omega)]
      simp [Nat.div_eq_of_lt h8, Nat.mod_eq_of_lt h8]
    · rw [List.getElem_append_right (by simp; omega)]
      simp only [List.length_map, List.length_range]
      have hp' : p - 8 < (blocks8 T).length := by
        simp only [List.length_append, List.length_map, List.length_range] at hp
        exact (by unfold blocks8; omega)
      refine (ih (p - 8) hp').trans ?_
      rw [show p / 8 = (p - 8) / 8 + 1 by omega, show p % 8 = (p - 8) % 8 by omega]
      rfl

/-- The pack's source addresses, layer by layer (checked by the kernel, linear size). -/
theorem blocks8_packTab : (blocks8 packTab).take 3924 =
    (List.range 5).flatMap (fun l => (List.range 4).map (fun i => 0x900 + 856 * l + i) ++
      (List.range (672 + 16 * height l)).map (fun i => 0x900 + 856 * l + 8 + i)) := by
  decide +kernel

theorem pack_addrs : (List.range 3924).map (fun p => srcA (packTab.getD (p / 8) (0, 0, 0)) (p % 8)) =
    (List.range 5).flatMap (fun l => (List.range 4).map (fun i => 0x900 + 856 * l + i) ++
      (List.range (672 + 16 * height l)).map (fun i => 0x900 + 856 * l + 8 + i)) := by
  rw [← blocks8_packTab]
  apply List.ext_getElem (by simp [length_blocks8, packTab_length])
  intro p h1 h2
  simp only [List.getElem_map, List.getElem_range, List.getElem_take]
  rw [getElem_blocks8]

theorem pack_layers (t u : MachineState)
    (hw : u.readWords (BitVec.ofNat 64 (0x2650 + 2480)) 491 = packTab.map (packDW t)) :
    bytesAt u (0x2650 + 2480) 3924 =
      (List.range 5).flatMap (fun l => bytesAt t (0x900 + 856 * l) 4 ++
        bytesAt t (0x900 + 856 * l + 8) (672 + 16 * height l)) := by
  rw [pack_bytes t u hw]
  have h := congrArg (List.map (fun a => t.getByte (BitVec.ofNat 64 a))) pack_addrs
  simp only [List.map_map, List.map_flatMap, List.map_append] at h
  rw [show (fun p => t.getByte (BitVec.ofNat 64 (srcA (packTab.getD (p / 8) (0, 0, 0)) (p % 8)))) =
    ((fun a => t.getByte (BitVec.ofNat 64 a)) ∘ fun p => srcA (packTab.getD (p / 8) (0, 0, 0)) (p % 8))
    from rfl, h]
  rfl

end SigGolfCandidate.Radix27Sign



end


section -- SignClone13.TreeStep

/-! ### cloned TreeStep -/

/-!
# `sign`, tree_build: the chain steps (`tb_step_loop`, instructions 533 .. 547)

Value-last chain format: the chain block is `CB = 0xC0`: tweak, 32 zero bytes (`CB+16 .. CB+48`),
the value at `CB+48 = 0xF0`; every answer is written at `a2 = CB+48` (its junk half lands at
`0x100 .. 0x110`).

`steps_sim` : from `tb_step_loop` with `MU = 0` (value `v0` at `CB+48`), the machine refines the
seven chain steps `foldlM (step) (v0, v0) (range' 1 7)` of `buildChain`, including the capture of
the value at position `x` into the stage slot `SIGL + 8 + 16 I` (only in leaf `e`).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace SigGolfCandidate.Radix27Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

/-- The split chain position `(p >> 3) << 8 | (p & 7)` of `p = 8 i + j`. -/
theorem splitP_word (i j : Nat) (hj : j < 8) (hi : i < 2 ^ 24) :
    (BitVec.ofNat 64 (8 * i + j) >>> ((3#64).toNat % 64) <<< ((8#64).toNat % 64) |||
      BitVec.ofNat 64 (8 * i + j) &&& 7#64) = BitVec.ofNat 64 (j + 256 * i) := by
  have h1 : BitVec.ofNat 64 (8 * i + j) >>> ((3#64).toNat % 64) <<< ((8#64).toNat % 64) =
      BitVec.ofNat 64 (256 * i) := by
    rw [show (3#64 : Word).toNat % 64 = 3 from rfl, show (8#64 : Word).toNat % 64 = 8 from rfl]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (a := 8 * i + j) (by omega),
      show (8 * i + j) / 2 ^ 3 = i by omega, Nat.mod_eq_of_lt (a := 256 * i) (by omega),
      Nat.mod_eq_of_lt (by omega)]
    ring
  have h2 : BitVec.ofNat 64 (8 * i + j) &&& 7#64 = BitVec.ofNat 64 j := by
    apply BitVec.eq_of_toNat_eq
    have h7 : (7#64 : Word).toNat = 2 ^ 3 - 1 := rfl
    rw [BitVec.toNat_and, h7, Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (a := 8 * i + j) (by omega), Nat.mod_eq_of_lt (a := j) (by omega)]
    omega
  rw [h1, h2, ofNat_or_disjoint (256 * i) j 8 (by omega) (by omega) (by omega), Nat.add_comm]

/-- Fixed parameters of the chain steps: layer, tree, capture leaf, current leaf, chain, digit. -/
structure StepPar where
  lay : Nat
  tau : Nat
  e : Nat
  ep : Nat
  i : Nat
  xi : Nat
  sigl : Nat

/-- Facts at the start of the step loop. -/
structure StepCtx (p : StepPar) (ts : MachineState) : Prop where
  hlay : p.lay < 7
  htau : p.tau < 2 ^ 30
  he : p.e < 64
  hep : p.ep < 64
  hi : p.i < 42
  hxi : p.xi < 8
  hsigl : p.sigl = 0x900 + 856 * p.lay
  x5 : ts.getReg .x5 = 0
  x11 : ts.getReg .x11 = BitVec.ofNat 64 64
  x12 : ts.getReg .x12 = BitVec.ofNat 64 0xF0
  x13 : ts.getReg .x13 = BitVec.ofNat 64 p.e
  x18 : ts.getReg .x18 = BitVec.ofNat 64 p.sigl
  x20 : ts.getReg .x20 = BitVec.ofNat 64 p.ep
  x21 : ts.getReg .x21 = BitVec.ofNat 64 p.i
  x25 : ts.getReg .x25 = BitVec.ofNat 64 p.xi
  cb0 : lo32 (ts.getMem (BitVec.ofNat 64 0xC0)) = BitVec.ofNat 32 (0x101 + 65536 * p.lay)
  cb8 : ts.getMem (BitVec.ofNat 64 0xC8) = BitVec.ofNat 64 (p.tau + 2 ^ 32 * p.ep)
  cbP : ts.readWords (BitVec.ofNat 64 0xD0) 4 = [0, 0, 0, 0]

/-- Addresses written by the step loop. -/
def stepW (p : StepPar) (a : Nat) : Prop :=
  a = 0xC0 ∨ (0xF0 ≤ a ∧ a < 0x110) ∨
    (p.ep = p.e ∧ (a = p.sigl + 8 + 16 * p.i ∨ a = p.sigl + 16 + 16 * p.i))

def stepRegs : List Reg := [.x1, .x2, .x3, .x10, .x23, .x24, .x29]

/-- Invariant after `j` steps. -/
def StepInv (p : StepPar) (ts : MachineState) (j : Nat) (st : Val × Val) (t : MachineState) : Prop :=
  j ≤ 7 ∧ st.1.length = 16 ∧ st.2.length = 16 ∧
  t.readWords (BitVec.ofNat 64 0xF0) 2 = wordsOf st.1 ∧
  t.readWords (BitVec.ofNat 64 0xD0) 4 = [0, 0, 0, 0] ∧
  t.pc = (if j < 7 then pcOf 513 else pcOf 532) ∧ t.getReg .x23 = BitVec.ofNat 64 j ∧
  t.getReg .x24 = BitVec.ofNat 64 (8 * p.i + j) ∧
  (p.ep = p.e → p.xi ≤ j →
    t.readWords (BitVec.ofNat 64 (p.sigl + 8 + 16 * p.i)) 2 = wordsOf st.2) ∧
  RegsEq ts t stepRegs ∧ Frame ts t (stepW p) ∧
  lo32 (t.getMem (BitVec.ofNat 64 0xC0)) = lo32 (ts.getMem (BitVec.ofNat 64 0xC0))

/-- The loop test (`tb_cap1_2`, instruction 546). -/
theorem step_tail (p : StepPar) (ts : MachineState) (ctx : StepCtx p ts) (j : Nat) (hj : j < 7)
    (v cap : Val) (hv : v.length = 16) (hc : cap.length = 16) (t : MachineState)
    (tpc : t.pc = pcOf 530) (tv : t.readWords (BitVec.ofNat 64 0xF0) 2 = wordsOf v)
    (tz : t.readWords (BitVec.ofNat 64 0xD0) 4 = [0, 0, 0, 0]) (t23 : t.getReg .x23 = BitVec.ofNat 64 (j + 1))
    (t24 : t.getReg .x24 = BitVec.ofNat 64 (8 * p.i + (j + 1)))
    (tcap : p.ep = p.e → p.xi ≤ j + 1 →
      t.readWords (BitVec.ofNat 64 (p.sigl + 8 + 16 * p.i)) 2 = wordsOf cap)
    (tregs : RegsEq ts t stepRegs) (tframe : Frame ts t (stepW p))
    (tlo : lo32 (t.getMem (BitVec.ofNat 64 0xC0)) = lo32 (ts.getMem (BitVec.ofNat 64 0xC0))) :
    Sim image t 2 (pure (v, cap)) (StepInv p ts (j + 1)) := by
  have hsig := ctx.hsigl
  have hl := ctx.hlay
  have hi := ctx.hi
  have hs := symRun_sound blk530 codeAt_530 t tpc (by simp only [blk530.res, rv_simp])
  have hc2 : blk530.res.cycles = 2 := rfl
  rw [hc2] at hs
  set t1 := blk530.res.toState t with ht1
  have f1 : Frame t t1 (fun _ => False) := by
    apply frame_toState; intro x hx hW; simp [blk530.res]
  have r1 : RegsEq t t1 [.x3] := by
    intro r hr; rw [ht1, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  refine Sim.pure_steps hs ⟨by omega, hv, hc, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [f1.readWords _ _ (by norm_num) (by simp), tv]
  · rw [f1.readWords _ _ (by norm_num) (by simp), tz]
  · simp only [ht1, blk530.res, rv_simp]
    bvsimp [t23, ofNat_bne_ofNat]
    by_cases h : j + 1 < 7
    · rw [if_pos h, if_pos (by simp; omega)]
    · rw [if_neg h, if_neg (by simp; omega)]
  · rw [r1.get .x23, t23]
  · rw [r1.get .x24, t24]
  · intro h1 h2
    rw [f1.readWords _ _ (by rw [ctx.hsigl]; omega) (by simp), tcap h1 h2]
  · exact (tregs.trans r1).mono (by decide)
  · exact (tframe.trans f1).mono (by intro x hx; rcases hx with h | h; exact h; exact h.elim)
  · rw [f1.getMem (by norm_num) (by simp), tlo]

/-- The capture copy (`CB+48 → SIGL + 8 + 16 I`, instructions 540 .. 545). -/
theorem step_capture (p : StepPar) (ts : MachineState) (ctx : StepCtx p ts) (t : MachineState)
    (tpc : t.pc = pcOf 524) (tregs : RegsEq ts t stepRegs) :
    ∃ t', Steps image t 6 6 t' ∧ t'.pc = pcOf 530 ∧ RegsEq t t' [.x1, .x2, .x3] ∧
      Frame t t' (fun x => x = p.sigl + 8 + 16 * p.i ∨ x = p.sigl + 16 + 16 * p.i) ∧
      t'.readWords (BitVec.ofNat 64 (p.sigl + 8 + 16 * p.i)) 2 =
        t.readWords (BitVec.ofNat 64 0xF0) 2 := by
  have hsig := ctx.hsigl
  have hl := ctx.hlay
  have hi := ctx.hi
  have t21 : t.getReg .x21 = BitVec.ofNat 64 p.i := by rw [tregs.get .x21, ctx.x21]
  have t18 : t.getReg .x18 = BitVec.ofNat 64 p.sigl := by rw [tregs.get .x18, ctx.x18]
  have hs := symRun_sound blk524 codeAt_524 t tpc (by
    simp only [blk524.res, rv_simp]; bvsimp [t21, t18, accessValid_ofNat]; omega)
  refine ⟨_, hs, by simp only [blk524.res, rv_simp], ?_, ?_, ?_⟩
  · intro r hr; rw [Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  · apply frame_toState; intro x hx hW
    simp only [blk524.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq]
    bvsimp [t21, t18, ofNat_eq_iff]
    omega
  · rw [readWords_ofNat_two, readWords_ofNat_two]
    simp only [blk524.res, rv_simp]
    bvsimp [t21, t18, ofNat_eq_iff]
    simp (disch := bvomega) only [if_pos, if_neg]

theorem step_body (p : StepPar) (ts : MachineState) (ctx : StepCtx p ts) (j : Nat) (hj : j < 7)
    (st : Val × Val) (t : MachineState) (hinv : StepInv p ts j st t) :
    Sim image t 29 (do
        let v ← hash16 (chainInput p.lay p.tau p.ep p.i (1 + j) st.1)
        pure (v, if 1 + j = p.xi then v else st.2))
      (StepInv p ts (j + 1)) := by
  obtain ⟨-, hl1, hl2, tv, tz, tpc, t23, t24, tcap, tregs, tframe, tlo⟩ := hinv
  have hsig := ctx.hsigl
  have hl := ctx.hlay
  have hi := ctx.hi
  have htau := ctx.htau
  have hep := ctx.hep
  have hxi := ctx.hxi
  have he := ctx.he
  have tpc' : t.pc = pcOf 513 := by rw [tpc, if_pos hj]
  have tx5 : t.getReg .x5 = 0 := by rw [tregs.get .x5, ctx.x5]
  have tx11 : t.getReg .x11 = BitVec.ofNat 64 64 := by rw [tregs.get .x11, ctx.x11]
  have tx12 : t.getReg .x12 = BitVec.ofNat 64 0xF0 := by rw [tregs.get .x12, ctx.x12]
  -- block 533: step input
  have hs1 := symRun_sound blk513 codeAt_513 t tpc' (by simp only [blk513.res, rv_simp])
  have hc1 : blk513.res.cycles = 7 := rfl
  rw [hc1] at hs1
  set t1 := blk513.res.toState t with ht1
  have f1 : Frame t t1 (fun x => x = 0xC0) := by
    apply frame_toState; intro x hx hW
    simp only [blk513.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq, ofNat_eq_iff]
    omega
  have r1 : RegsEq t t1 [.x3, .x10, .x23, .x29] := by
    intro r hr; rw [ht1, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have e1 := symRun_ecall blk513 codeAt_513 t (by simp only [blk513.res, rv_simp]) rfl
  have x10 : t1.getReg .x10 = BitVec.ofNat 64 0xC0 := by simp only [ht1, blk513.res, rv_simp]
  have x11 : t1.getReg .x11 = BitVec.ofNat 64 64 := by rw [r1.get .x11, tx11]
  have x12 : t1.getReg .x12 = BitVec.ofNat 64 0xF0 := by rw [r1.get .x12, tx12]
  have x5 : t1.getReg .x5 = 0 := by rw [r1.get .x5, tx5]
  have x23 : t1.getReg .x23 = BitVec.ofNat 64 (j + 1) := by
    simp only [ht1, blk513.res, rv_simp]; bvsimp [t23]
  have pc1 : t1.pc = pcOf 520 := by simp only [ht1, blk513.res, rv_simp]
  have mC0 : t1.getMem (BitVec.ofNat 64 0xC0) = twWord0 1 p.lay p.tau (j + 256 * p.i) := by
    simp only [ht1, blk513.res, rv_simp, t24, splitP_word p.i j (by omega) (by omega)]
    bvsimp []
    refine (word_of_halves _ (0x101 + 65536 * p.lay) (j + 256 * p.i) (by rw [lo32_replace1, tlo, ctx.cb0])
      (by rw [hi32_replace1])).trans ?_
    unfold twWord0; congr 1
    rw [Nat.div_eq_of_lt (by omega : p.tau < 2 ^ 32)]; omega
  have hq : hashInput t1 = fmt (chainInput p.lay p.tau p.ep p.i (1 + j) st.1) := by
    refine hashInput_eq_chain t1 _ _ _ _ _ _ hl1 (by omega) (by omega) (by omega) x11 (by rw [x10]; decide) ?_
    rw [x10, show (8 : Nat) = 1 + 1 + 4 + 2 from rfl]
    rw [readWords_ofNat_add, readWords_ofNat_add, readWords_ofNat_add]
    simp only [Nat.reduceMul, Nat.reduceAdd]
    rw [readWords_ofNat_one, readWords_ofNat_one, mC0, f1.getMem (by norm_num) (by norm_num),
      tframe.getMem (by norm_num) (by simp only [stepW]; omega), ctx.cb8,
      f1.readWords _ _ (by norm_num) (by intro i hi; omega),
      f1.readWords _ _ (by norm_num) (by intro i hi; omega), tz, tv]
    simp only [twWords_eq, show 1 + j - 1 + 256 * p.i = j + 256 * p.i by omega]
    simp only [List.cons_append, List.nil_append, List.cons.injEq, and_true, true_and]
    congr 1; omega
  have hb : (fmt (chainInput p.lay p.tau p.ep p.i (1 + j) st.1)).blocks = 1 := by
    rw [fmt_chainInput _ _ _ _ _ _ hl1 (by omega) (by omega) (by omega)]; rfl
  refine (Sim.steps hs1 (Sim.hash16_bindF (W := 4 + 7 + 3) e1 x5
    (hashArgs_of x10 x11 x12 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)) hq (fun a => ?_))).mono (by rw [hb]) (fun _ _ h => h)
  set v := answerBytes 16 a with hv
  have hvl : v.length = 16 := by simp [hv]
  set t2 := writeHash t1 a with ht2
  have f2 : Frame t1 t2 (fun x => 0xF0 ≤ x ∧ x < 0xF0 + 32) := frame_writeHash t1 a _ x12 (by norm_num)
  have v2 : t2.readWords (BitVec.ofNat 64 0xF0) 2 = wordsOf v := writeHash_readWords_val t1 a _ x12 (by norm_num)
  have pc2 : t2.pc = pcOf 521 := by rw [ht2, writeHash_pc, pc1]; apply BitVec.eq_of_toNat_eq; simp
  -- block 537: P++, test EP = e
  have hs3 := symRun_sound blk521 codeAt_521 t2 pc2 (by simp only [blk521.res, rv_simp])
  have hc3 : blk521.res.cycles = 2 := rfl
  rw [hc3] at hs3
  set t3 := blk521.res.toState t2 with ht3
  have f3 : Frame t2 t3 (fun _ => False) := by
    apply frame_toState; intro x hx hW; simp [blk521.res]
  have r3 : RegsEq t2 t3 [.x24] := by
    intro r hr; rw [ht3, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have rt3 : RegsEq t t3 ([.x3, .x10, .x23, .x29] ++ [] ++ [.x24]) :=
    (r1.trans (regsEq_writeHash _ _ [])).trans r3
  have x320 : t3.getReg .x20 = BitVec.ofNat 64 p.ep := by
    rw [rt3.get .x20, tregs.get .x20, ctx.x20]
  have x313 : t3.getReg .x13 = BitVec.ofNat 64 p.e := by
    rw [rt3.get .x13, tregs.get .x13, ctx.x13]
  have x323 : t3.getReg .x23 = BitVec.ofNat 64 (j + 1) := by
    rw [r3.get .x23, ht2, writeHash_getReg, x23]
  have t224 : t2.getReg .x24 = BitVec.ofNat 64 (8 * p.i + j) := by
    rw [ht2, writeHash_getReg, r1.get .x24, t24]
  have t220 : t2.getReg .x20 = BitVec.ofNat 64 p.ep := by
    rw [ht2, writeHash_getReg, r1.get .x20, tregs.get .x20, ctx.x20]
  have t213 : t2.getReg .x13 = BitVec.ofNat 64 p.e := by
    rw [ht2, writeHash_getReg, r1.get .x13, tregs.get .x13, ctx.x13]
  have x324 : t3.getReg .x24 = BitVec.ofNat 64 (8 * p.i + (j + 1)) := by
    simp only [ht3, blk521.res, rv_simp, t224, ofNat_add_ofNat]
    rw [show 8 * p.i + j + 1 = 8 * p.i + (j + 1) by ring]
  have v3 : t3.readWords (BitVec.ofNat 64 0xF0) 2 = wordsOf v := by
    rw [f3.readWords _ _ (by norm_num) (by simp), v2]
  have ft3 : Frame t t3 (fun x => x = 0xC0 ∨ (0xF0 ≤ x ∧ x < 0x110)) :=
    ((f1.trans f2).trans f3).mono (by intro x hx; simp only [or_false] at hx; omega)
  have z3 : t3.readWords (BitVec.ofNat 64 0xD0) 4 = [0, 0, 0, 0] := by
    rw [ft3.readWords _ _ (by norm_num) (by intro i hi; omega), tz]
  have fts3 : Frame ts t3 (stepW p) := (tframe.trans ft3).mono (by
    intro x hx; simp only [stepW] at hx ⊢; omega)
  have rts3 : RegsEq ts t3 stepRegs := (tregs.trans rt3).mono (by decide)
  have lo3 : lo32 (t3.getMem (BitVec.ofNat 64 0xC0)) = lo32 (ts.getMem (BitVec.ofNat 64 0xC0)) := by
    rw [f3.getMem (by norm_num) (by simp), f2.getMem (by norm_num) (by omega), mC0, ctx.cb0]
    simp only [twWord0, lo32_ofNat]
    apply BitVec.eq_of_toNat_eq; simp; omega
  have pc3 : t3.pc = if p.ep = p.e then pcOf 523 else pcOf 530 := by
    simp only [ht3, blk521.res, rv_simp, t220, t213, ofNat_bne_ofNat]
    by_cases h : p.ep = p.e
    · rw [if_pos h, if_neg (by simp; omega)]
    · rw [if_neg h, if_pos (by simp; omega)]
  have hcapold : p.ep = p.e → p.xi ≤ j →
      t3.readWords (BitVec.ofNat 64 (p.sigl + 8 + 16 * p.i)) 2 = wordsOf st.2 := by
    intro h1 h2
    rw [ft3.readWords _ _ (by omega) (by intro i hi; omega), tcap h1 h2]
  by_cases hep' : p.ep = p.e
  · -- capture leaf: test MU = X
    have hs4 := symRun_sound blk523 codeAt_523 t3 (by rw [pc3, if_pos hep'])
      (by simp only [blk523.res, rv_simp])
    have hc4 : blk523.res.cycles = 1 := rfl
    rw [hc4] at hs4
    set t4 := blk523.res.toState t3 with ht4
    have f4 : Frame t3 t4 (fun _ => False) := by
      apply frame_toState; intro x hx hW; simp [blk523.res]
    have r4 : RegsEq t3 t4 [] := by
      intro r hr; rw [ht4, Result.toState_getReg]
      cases r <;> first | exact absurd (by decide) hr | rfl
    have x325 : t3.getReg .x25 = BitVec.ofNat 64 p.xi := by
      rw [rt3.get .x25, tregs.get .x25, ctx.x25]
    have pc4 : t4.pc = if p.xi = j + 1 then pcOf 524 else pcOf 530 := by
      simp only [ht4, blk523.res, rv_simp]; bvsimp [x323, x325, ofNat_bne_ofNat]
      by_cases h : p.xi = j + 1
      · rw [if_pos h, if_neg (by simp; omega)]
      · rw [if_neg h, if_pos (by simp; omega)]
    have fts4 : Frame ts t4 (stepW p) := (fts3.trans f4).mono (by
      intro x hx; rcases hx with h | h; exact h; exact h.elim)
    by_cases hx1 : p.xi = j + 1
    · obtain ⟨t5, hs5, pc5, r5, f5, cap5⟩ := step_capture p ts ctx t4 (by rw [pc4, if_pos hx1])
        ((rts3.trans r4).mono (by decide))
      have := step_tail p ts ctx j hj v v hvl hvl t5 pc5
        (by rw [f5.readWords _ _ (by norm_num) (by intro i hi; omega),
          f4.readWords _ _ (by norm_num) (by simp), v3])
        (by rw [f5.readWords _ _ (by norm_num) (by intro i hi; omega),
          f4.readWords _ _ (by norm_num) (by simp), z3])
        (by rw [r5.get .x23, r4.get .x23, x323]) (by rw [r5.get .x24, r4.get .x24, x324])
        (fun _ _ => by rw [cap5, f4.readWords _ _ (by norm_num) (by simp), v3])
        (((rts3.trans r4).trans r5).mono (by decide))
        ((fts4.trans f5).mono (by intro x hx; simp only [stepW] at hx ⊢; omega))
        (by rw [f5.getMem (by norm_num) (by omega), f4.getMem (by norm_num) (by simp), lo3])
      rw [if_pos (by omega)]
      exact (Sim.steps hs3 (Sim.steps hs4 (Sim.steps hs5 this))).mono (by norm_num) (fun _ _ h => h)
    · have := step_tail p ts ctx j hj v st.2 hvl hl2 t4 (by rw [pc4, if_neg hx1])
        (by rw [f4.readWords _ _ (by norm_num) (by simp), v3])
        (by rw [f4.readWords _ _ (by norm_num) (by simp), z3])
        (by rw [r4.get .x23, x323]) (by rw [r4.get .x24, x324])
        (fun h1 h2 => by
          rw [f4.readWords _ _ (by omega) (by simp)]; exact hcapold h1 (by omega))
        ((rts3.trans r4).mono (by decide)) fts4
        (by rw [f4.getMem (by norm_num) (by simp), lo3])
      rw [if_neg (by omega)]
      exact (Sim.steps hs3 (Sim.steps hs4 this)).mono (by norm_num) (fun _ _ h => h)
  · have := step_tail p ts ctx j hj v (if 1 + j = p.xi then v else st.2) hvl
      (by split <;> assumption) t3 (by rw [pc3, if_neg hep']) v3 z3 x323 x324
      (fun h => absurd h hep') rts3 fts3 lo3
    exact (Sim.steps hs3 this).mono (by norm_num) (fun _ _ h => h)

/-- **Chain steps** `mu = 1 .. 7` (with capture). -/
theorem steps_sim (p : StepPar) (ts : MachineState) (ctx : StepCtx p ts) (v0 : Val)
    (h0 : StepInv p ts 0 (v0, v0) ts) :
    Sim image ts (7 * 29) ((List.range' 1 7).foldlM (fun (st : Val × Val) mu => do
        let v ← hash16 (chainInput p.lay p.tau p.ep p.i mu st.1)
        pure (v, if mu = p.xi then v else st.2)) (v0, v0)) (StepInv p ts 7) :=
  Sim.foldlM_range' 1 7 _ (v0, v0) (StepInv p ts) 29
    (fun j hj st t h => step_body p ts ctx j hj st t h) h0

end SigGolfCandidate.Radix27Sign



end


section -- SignClone13.Top

/-! ### cloned Top -/

/-!
# `sign`, layer 0 (the cached top tree): `top_layer` (instructions 572 .. 638)

* `topChains_sim` : chains `i = 0 .. 41` of leaf `e` up to position `x_i` only (`chainTo`); chain
  value `i` staged at `STG + 8 + 16 i`.
* `topPath_sim` : the path from the cache: for `l = 0 .. 10`, `mask(l, s)` with
  `s = (e >> l) ^ 1`, path node `cache node (l, s) xor mask` staged at `STG + 680 + 16 l`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace SigGolfCandidate.Radix27Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

/-! ## Bytewise XOR as dwords -/

theorem xor_byte_add (x y A B : Nat) (hx : x < 256) (hy : y < 256) :
    (x + 256 * A) ^^^ (y + 256 * B) = (x ^^^ y) + 256 * (A ^^^ B) := by
  have hxy : x ^^^ y < 2 ^ 8 := Nat.xor_lt_two_pow (by omega) (by omega)
  rw [show x + 256 * A = 2 ^ 8 * A + x by ring, show y + 256 * B = 2 ^ 8 * B + y by ring,
    show (x ^^^ y) + 256 * (A ^^^ B) = 2 ^ 8 * (A ^^^ B) + (x ^^^ y) by ring]
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_xor, Nat.testBit_two_pow_mul_add _ (by omega : x < 2 ^ 8),
    Nat.testBit_two_pow_mul_add _ (by omega : y < 2 ^ 8), Nat.testBit_two_pow_mul_add _ hxy]
  split <;> simp [Nat.testBit_xor]

theorem leNat_xorBytes : ∀ (a b : List Byte), a.length = b.length →
    leNat (xorBytes a b) = leNat a ^^^ leNat b
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: as, y :: bs, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    have ih := leNat_xorBytes as bs h
    simp only [xorBytes, List.zipWith_cons_cons, leNat] at ih ⊢
    rw [ih, BitVec.toNat_xor, xor_byte_add _ _ _ _ x.isLt y.isLt]

theorem length_xorBytes' (a b : List Byte) (h : a.length = b.length) :
    (xorBytes a b).length = a.length := by
  simp [xorBytes, h]

theorem xorBytes_append (a1 a2 b1 b2 : List Byte) (h : a1.length = b1.length) :
    xorBytes (a1 ++ a2) (b1 ++ b2) = xorBytes a1 b1 ++ xorBytes a2 b2 := by
  simp [xorBytes, List.zipWith_append h]

theorem wordsOf_xorBytes (u v : Val) (hu : u.length = 16) (hv : v.length = 16) (u0 u1 v0 v1 : Word)
    (hwu : wordsOf u = [u0, u1]) (hwv : wordsOf v = [v0, v1]) :
    wordsOf (xorBytes u v) = [u0 ^^^ v0, u1 ^^^ v1] := by
  have su : u = u.take 8 ++ u.drop 8 := (List.take_append_drop 8 u).symm
  have sv : v = v.take 8 ++ v.drop 8 := (List.take_append_drop 8 v).symm
  rw [su, wordsOf_append _ _ (by simp; omega), wordsOf_eight _ (by simp; omega),
    wordsOf_eight _ (by simp; omega)] at hwu
  rw [sv, wordsOf_append _ _ (by simp; omega), wordsOf_eight _ (by simp; omega),
    wordsOf_eight _ (by simp; omega)] at hwv
  simp only [List.cons_append, List.nil_append, List.cons.injEq, and_true] at hwu hwv
  rw [su, sv, xorBytes_append _ _ _ _ (by simp; omega),
    wordsOf_append _ _ (by rw [length_xorBytes' _ _ (by simp; omega)]; simp; omega),
    wordsOf_eight _ (by rw [length_xorBytes' _ _ (by simp; omega)]; simp; omega),
    wordsOf_eight _ (by rw [length_xorBytes' _ _ (by simp; omega)]; simp; omega),
    leNat_xorBytes _ _ (by simp; omega), leNat_xorBytes _ _ (by simp; omega),
    BitVec.ofNat_xor, BitVec.ofNat_xor, hwu.1, hwu.2, hwv.1, hwv.2]
  rfl

/-! ## The context at `top_layer` -/

/-- Facts at `top_layer` (instruction 572): layer 0, leaf `e`, digits `x`. -/
structure TopCtx (S cache : List Byte) (x : List Nat) (tau e : Nat) (t : MachineState) : Prop where
  htau : tau < 2 ^ 30
  he : e < 2048
  hx : ∀ i, x.getD i 0 < 8
  x5 : t.getReg .x5 = 0
  x13 : t.getReg .x13 = BitVec.ofNat 64 e
  x18 : t.getReg .x18 = BitVec.ofNat 64 0x900
  x31 : t.getReg .x31 = BitVec.ofNat 64 (tau + 2 ^ 32 * e)
  dig : ∀ i < 42, t.getMem (BitVec.ofNat 64 (0x780 + 8 * i)) = BitVec.ofNat 64 (x.getD i 0)
  pbP : t.readWords (BitVec.ofNat 64 0x6B0) 2 = [0, 0]
  pbS : t.readWords (BitVec.ofNat 64 0x6C0) 4 = wordsOf S
  cbP : t.readWords (BitVec.ofNat 64 0xD0) 2 = [0, 0]
  node : ∀ l j, l < 11 → j < 2 ^ (11 - l) →
    t.readWords (BitVec.ofNat 64 (0x44A0 + cacheNodeOff l j)) 2 = wordsOf (cacheNode cache l j)
  nodeLen : ∀ l j, l < 11 → j < 2 ^ (11 - l) → (cacheNode cache l j).length = 16

/-- Addresses written by the top layer. -/
def topW (a : Nat) : Prop :=
  a = 0x6A0 ∨ a = 0x6A8 ∨ a = 0xC0 ∨ a = 0xC8 ∨ (0xE0 ≤ a ∧ a < 0x110) ∨ (0x140 ≤ a ∧ a < 0x160) ∨
    (0x908 ≤ a ∧ a < 0x908 + 672) ∨ (0xBA8 ≤ a ∧ a < 0xBA8 + 176)

theorem topN_eq (l : Nat) (hl : l ≤ 11) : topN l = 4096 - 2 ^ (12 - l) := by
  interval_cases l <;> rfl

theorem topN_succ (l : Nat) (hl : l < 11) : topN (l + 1) = topN l + 2 ^ (11 - l) := by
  interval_cases l <;> rfl

theorem topN_add_lt (l j : Nat) (hl : l < 11) (hj : j < 2 ^ (11 - l)) : topN l + j < 4094 := by
  rw [topN_eq l (by omega)]
  interval_cases l <;> norm_num at hj ⊢ <;> omega

theorem cacheNodeOff_lt (l j : Nat) (hl : l < 11) (hj : j < 2 ^ (11 - l)) :
    cacheNodeOff l j + 16 ≤ 32 + 65504 := by
  have h := topN_add_lt l j hl hj
  unfold cacheNodeOff; omega


/-! ## Chains up to `x_i` -/

/-- The chain buffers during the top chains (fixed for the whole phase). -/
structure TopMem (S : List Byte) (x : List Nat) (tau e : Nat) (t : MachineState) : Prop where
  htau : tau < 2 ^ 30
  he : e < 2048
  hx : ∀ i, x.getD i 0 < 8
  x5 : t.getReg .x5 = 0
  x18 : t.getReg .x18 = BitVec.ofNat 64 0x900
  dig : ∀ i < 42, t.getMem (BitVec.ofNat 64 (0x780 + 8 * i)) = BitVec.ofNat 64 (x.getD i 0)
  pb0 : lo32 (t.getMem (BitVec.ofNat 64 0x6A0)) = BitVec.ofNat 32 1
  pb8 : t.getMem (BitVec.ofNat 64 0x6A8) = BitVec.ofNat 64 (tau + 2 ^ 32 * e)
  pbP : t.readWords (BitVec.ofNat 64 0x6B0) 2 = [0, 0]
  pbS : t.readWords (BitVec.ofNat 64 0x6C0) 4 = wordsOf S
  cb0 : lo32 (t.getMem (BitVec.ofNat 64 0xC0)) = BitVec.ofNat 32 0x101
  cb8 : t.getMem (BitVec.ofNat 64 0xC8) = BitVec.ofNat 64 (tau + 2 ^ 32 * e)
  cbP : t.readWords (BitVec.ofNat 64 0xD0) 4 = [0, 0, 0, 0]

/-- Addresses written by a top chain. -/
def tchainW (a : Nat) : Prop :=
  a = 0x6A0 ∨ a = 0xC0 ∨ (0xF0 ≤ a ∧ a < 0x110) ∨ (0x140 ≤ a ∧ a < 0x160) ∨ (0x908 ≤ a ∧ a < 0x908 + 672)

/-- The words `twWord0 t 0 tau p` for `tau < 2^32`. -/
theorem twWord0_top (tt tau p : Nat) (htau : tau < 2 ^ 32) :
    twWord0 tt 0 tau p = BitVec.ofNat 64 (1 + 256 * (tt % 256) + 2 ^ 32 * (p % 2 ^ 32)) := by
  unfold twWord0; congr 1; rw [Nat.div_eq_of_lt htau]; omega

theorem mem_top_frame {S : List Byte} {x : List Nat} {tau e : Nat} {s t : MachineState}
    (h : TopMem S x tau e s) (hf : Frame s t tchainW) (h5 : t.getReg .x5 = 0) (h18 : t.getReg .x18 = BitVec.ofNat 64 0x900)
    (hpb0 : lo32 (t.getMem (BitVec.ofNat 64 0x6A0)) = BitVec.ofNat 32 1)
    (hcb0 : lo32 (t.getMem (BitVec.ofNat 64 0xC0)) = BitVec.ofNat 32 0x101) : TopMem S x tau e t := by
  refine ⟨h.htau, h.he, h.hx, h5, h18, fun i hi => ?_, hpb0, ?_, ?_, ?_, hcb0, ?_, ?_⟩
  · rw [hf.getMem (by omega) (by simp only [tchainW]; omega), h.dig i hi]
  · rw [hf.getMem (by norm_num) (by simp only [tchainW]; omega), h.pb8]
  · rw [hf.readWords _ _ (by norm_num) (by intro i hi; simp only [tchainW]; omega), h.pbP]
  · rw [hf.readWords _ _ (by norm_num) (by intro i hi; simp only [tchainW]; omega), h.pbS]
  · rw [hf.getMem (by norm_num) (by simp only [tchainW]; omega), h.cb8]
  · rw [hf.readWords _ _ (by norm_num) (by intro i hi; simp only [tchainW]; omega), h.cbP]

/-- Step-loop invariant of chain `i` after `j` steps (value `v` at `CB+48`). -/
def TStepInv (S : List Byte) (x : List Nat) (tau e i : Nat) (ts : MachineState) (j : Nat) (v : Val)
    (t : MachineState) : Prop :=
  j ≤ x.getD i 0 ∧ v.length = 16 ∧ t.pc = pcOf 622 ∧ t.readWords (BitVec.ofNat 64 0xF0) 2 = wordsOf v ∧
  t.getReg .x23 = BitVec.ofNat 64 j ∧ t.getReg .x24 = BitVec.ofNat 64 (8 * i + j) ∧
  t.getReg .x25 = BitVec.ofNat 64 (x.getD i 0) ∧
  t.getReg .x11 = BitVec.ofNat 64 64 ∧ t.getReg .x12 = BitVec.ofNat 64 0xF0 ∧
  RegsEq ts t [.x3, .x10, .x23, .x24, .x29] ∧ Frame ts t (fun a => a = 0xC0 ∨ (0xF0 ≤ a ∧ a < 0x110)) ∧
  lo32 (t.getMem (BitVec.ofNat 64 0xC0)) = BitVec.ofNat 32 0x101

theorem tstep_body (S : List Byte) (x : List Nat) (tau e i : Nat) (hi : i < 42) (ts : MachineState)
    (hm : TopMem S x tau e ts) (j : Nat) (hj : j < x.getD i 0) (v : Val) (t : MachineState)
    (hinv : TStepInv S x tau e i ts j v t) :
    Sim image t 18 (hash16 (chainInput 0 tau e i (1 + j) v)) (TStepInv S x tau e i ts (j + 1)) := by
  obtain ⟨-, hvl, tpc, tv, t23, t24, t25, t11, t12, tregs, tframe, tlo⟩ := hinv
  have htau := hm.htau
  have he := hm.he
  have hxi := hm.hx i
  -- block 590: loop test
  have hs0 := symRun_sound blk622 codeAt_622 t tpc (by simp only [blk622.res, rv_simp])
  have hc0 : blk622.res.cycles = 1 := rfl
  rw [hc0] at hs0
  set t0 := blk622.res.toState t with ht0
  have pc0 : t0.pc = pcOf 623 := by
    simp only [ht0, blk622.res, rv_simp, t23, t25, ofNat_beq_ofNat]
    rw [if_neg (by rw [decide_eq_true_eq, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega)]
  have m0 : ∀ z, t0.getMem z = t.getMem z := fun z => by
    rw [ht0, Result.toState_getMem, show blk622.res.st.mem = [] from rfl, memEval_nil]
  have r0 : RegsEq t t0 [] := by
    intro r hr; rw [ht0, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  -- block 591: step tweak, HASH
  have hs1 := symRun_sound blk623 codeAt_623 t0 pc0 (by simp only [blk623.res, rv_simp])
  have hc1 : blk623.res.cycles = 6 := rfl
  rw [hc1] at hs1
  set t1 := blk623.res.toState t0 with ht1
  have f1 : Frame t0 t1 (fun x => x = 0xC0) := by
    apply frame_toState; intro x hx hW
    simp only [blk623.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq, ofNat_eq_iff]
    omega
  have r1 : RegsEq t0 t1 [.x3, .x10, .x29] := by
    intro r hr; rw [ht1, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have e1 := symRun_ecall blk623 codeAt_623 t0 (by simp only [blk623.res, rv_simp]) rfl
  have x10 : t1.getReg .x10 = BitVec.ofNat 64 0xC0 := by simp only [ht1, blk623.res, rv_simp]
  have x11 : t1.getReg .x11 = BitVec.ofNat 64 64 := by rw [r1.get .x11, r0.get .x11, t11]
  have x12 : t1.getReg .x12 = BitVec.ofNat 64 0xF0 := by rw [r1.get .x12, r0.get .x12, t12]
  have x5 : t1.getReg .x5 = 0 := by rw [r1.get .x5, r0.get .x5, tregs.get .x5, hm.x5]
  have pc1 : t1.pc = pcOf 629 := by simp only [ht1, blk623.res, rv_simp]
  have mC0 : t1.getMem (BitVec.ofNat 64 0xC0) = twWord0 1 0 tau (j + 256 * i) := by
    simp only [ht1, blk623.res, rv_simp, r0.get .x24, t24, splitP_word i j (by omega) (by omega)]
    bvsimp []
    rw [twWord0_top _ _ _ (by omega)]
    refine (word_of_halves _ 0x101 (j + 256 * i) (by rw [lo32_replace1, m0, tlo])
      (by rw [hi32_replace1])).trans ?_
    congr 1
  have hq : hashInput t1 = fmt (chainInput 0 tau e i (1 + j) v) := by
    refine hashInput_eq_chain t1 _ _ _ _ _ _ hvl (by omega) (by omega) (by omega) x11 (by rw [x10]; decide) ?_
    rw [x10, show (8 : Nat) = 1 + 1 + 4 + 2 from rfl]
    rw [readWords_ofNat_add, readWords_ofNat_add, readWords_ofNat_add]
    simp only [Nat.reduceMul, Nat.reduceAdd]
    rw [readWords_ofNat_one, readWords_ofNat_one, mC0, f1.getMem (by norm_num) (by norm_num), m0,
      tframe.getMem (by norm_num) (by omega), hm.cb8,
      f1.readWords _ _ (by norm_num) (by intro i hi; omega),
      f1.readWords _ _ (by norm_num) (by intro i hi; omega),
      readWords_congr _ _ _ _ (fun k hk => m0 _), readWords_congr _ _ 0xF0 2 (fun k hk => m0 _),
      tframe.readWords _ _ (by norm_num) (by intro i hi; omega), hm.cbP, tv]
    simp only [twWords_eq, show 1 + j - 1 + 256 * i = j + 256 * i by omega]
    simp only [List.cons_append, List.nil_append, List.cons.injEq, and_true, true_and]
    congr 1; omega
  have hb : (fmt (chainInput 0 tau e i (1 + j) v)).blocks = 1 := by
    rw [fmt_chainInput _ _ _ _ _ _ hvl (by omega) (by omega) (by omega)]; rfl
  have hstep : hash16 (chainInput 0 tau e i (1 + j) v) =
      hash16 (chainInput 0 tau e i (1 + j) v) >>= fun w => pure w := by rw [bind_pure]
  rw [hstep]
  refine (Sim.steps hs0 (Sim.steps hs1 (Sim.hash16_bindF (W := 3) e1 x5
    (hashArgs_of x10 x11 x12 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)) hq (fun a => ?_)))).mono (by rw [hb]) (fun _ _ h => h)
  set w := answerBytes 16 a with hw
  have hwl : w.length = 16 := by simp [hw]
  set t2 := writeHash t1 a with ht2
  have f2 : Frame t1 t2 (fun x => 0xF0 ≤ x ∧ x < 0xF0 + 32) := frame_writeHash t1 a _ x12 (by norm_num)
  have v2 : t2.readWords (BitVec.ofNat 64 0xF0) 2 = wordsOf w := writeHash_readWords_val t1 a _ x12 (by norm_num)
  have pc2 : t2.pc = pcOf 630 := by rw [ht2, writeHash_pc, pc1]; apply BitVec.eq_of_toNat_eq; simp
  have r2 : ∀ q, t2.getReg q = t1.getReg q := fun q => by rw [ht2, writeHash_getReg]
  have r2' : RegsEq t1 t2 [] := fun q _ => r2 q
  -- block 594: counters, back to the loop test
  have hs3 := symRun_sound blk630 codeAt_630 t2 pc2 (by simp only [blk630.res, rv_simp])
  have hc3 : blk630.res.cycles = 3 := rfl
  rw [hc3] at hs3
  set t3 := blk630.res.toState t2 with ht3
  have m3 : ∀ z, t3.getMem z = t2.getMem z := fun z => by
    rw [ht3, Result.toState_getMem, show blk630.res.st.mem = [] from rfl, memEval_nil]
  have r3 : RegsEq t2 t3 [.x23, .x24] := by
    intro r hr; rw [ht3, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have ft3 : Frame t t3 (fun a => a = 0xC0 ∨ (0xF0 ≤ a ∧ a < 0x110)) := by
    intro z hz hW
    rw [m3, f2.getMem hz (by omega), f1.getMem hz (by omega), m0]
  refine Sim.pure_steps hs3 ⟨by omega, hwl, by simp only [ht3, blk630.res, rv_simp],
    by rw [readWords_congr _ _ 0xF0 2 (fun k hk => m3 _), v2], ?_, ?_, ?_, ?_, ?_, ?_,
    (tframe.trans ft3).mono (by intro z hz; omega), ?_⟩
  · simp only [ht3, blk630.res, rv_simp, r2, r1.get .x23, r0.get .x23, t23, ofNat_add_ofNat]
  · simp only [ht3, blk630.res, rv_simp, r2, r1.get .x24, r0.get .x24, t24, ofNat_add_ofNat]
    exact ofNat_congr (by omega)
  · rw [r3.get .x25, r2, r1.get .x25, r0.get .x25, t25]
  · rw [r3.get .x11, r2, x11]
  · rw [r3.get .x12, r2, x12]
  · exact ((((tregs.trans r0).trans r1).trans r2').trans r3).mono (by decide)
  · rw [m3, f2.getMem (by norm_num) (by omega), mC0]
    simp only [twWord0, lo32_ofNat]
    apply BitVec.eq_of_toNat_eq; simp; omega

def topRegs : List Reg := [.x1, .x2, .x3, .x10, .x11, .x12, .x21, .x23, .x24, .x25, .x29]

/-- Chain-loop invariant after `i` chains. -/
def TChainInv (S : List Byte) (x : List Nat) (tau e : Nat) (tm : MachineState) (i : Nat) (acc : List Val)
    (t : MachineState) : Prop :=
  i ≤ 42 ∧ acc.length = i ∧ (∀ v ∈ acc, v.length = 16) ∧ Slots t 0x908 acc ∧
  t.pc = (if i < 42 then pcOf 603 else pcOf 642) ∧ t.getReg .x21 = BitVec.ofNat 64 i ∧
  TopMem S x tau e t ∧ RegsEq tm t topRegs ∧ Frame tm t tchainW

/-- `SEC` untouched. -/
def TSec (s t : MachineState) : Prop :=
  ∀ x, x < 2 ^ 64 → 0x140 ≤ x → x < 0x160 → t.getMem (BitVec.ofNat 64 x) = s.getMem (BitVec.ofNat 64 x)

/-- Chain `i` of the top leaf from `prf_have` (instruction 606): its secret `s` at `SEC + 16 (i & 1)`. -/
theorem tchain_B (S : List Byte) (x : List Nat) (tau e : Nat) (tm : MachineState)
    (i : Nat) (hi : i < 42) (s : Val) (hs : s.length = 16) (acc : List Val) (hl1 : acc.length = i)
    (hv1 : ∀ v ∈ acc, v.length = 16) (t : MachineState) (hsl : Slots t 0x908 acc)
    (tpc : t.pc = pcOf 611) (t21 : t.getReg .x21 = BitVec.ofNat 64 i) (t11 : t.getReg .x11 = BitVec.ofNat 64 64)
    (tsec : t.readWords (BitVec.ofNat 64 (0x140 + 16 * (i % 2))) 2 = wordsOf s)
    (hm : TopMem S x tau e t) (tregs : RegsEq tm t topRegs) (tframe : Frame tm t tchainW) :
    Sim image t 150 (chainTo 0 tau e i (x.getD i 0) s >>= fun v => pure (acc ++ [v]))
      (fun r t' => TChainInv S x tau e tm (i + 1) r t' ∧ t'.getReg .x11 = BitVec.ofNat 64 64 ∧ TSec t t') := by
  have htau := hm.htau
  have he := hm.he
  have hxi := hm.hx i
  have hi2 : i % 2 < 2 := Nat.mod_lt _ (by norm_num)
  -- block 606: secret → CB+48, digit, step counters
  have hs3 := symRun_sound blk611 codeAt_611 t tpc (by
    simp only [blk611.res, rv_simp]
    rw [t21, secAddr i (by omega) 328 (by norm_num), secAddr i (by omega) 320 (by norm_num)]
    bvsimp [accessValid_ofNat, ne_eq, ofNat_eq_iff]; omega)
  have hc3 : blk611.res.cycles = 11 := rfl
  rw [hc3] at hs3
  set t3 := blk611.res.toState t with ht3
  have f3 : Frame t t3 (fun x => x = 0xF0 ∨ x = 0xF8) := by
    apply frame_toState; intro x hx hW
    simp only [blk611.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq, ofNat_eq_iff]
    omega
  have r3 : RegsEq t t3 [.x1, .x2, .x3, .x12, .x23, .x24, .x25] := by
    intro r hr; rw [ht3, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have v3 : t3.readWords (BitVec.ofNat 64 0xF0) 2 = wordsOf s := by
    rw [← tsec, readWords_ofNat_two, readWords_ofNat_two]
    simp only [ht3, blk611.res, rv_simp, t21]
    rw [secAddr i (by omega) 328 (by norm_num), secAddr i (by omega) 320 (by norm_num)]
    simp (config := { decide := true }) only [↓reduceIte]
    rw [show 328 + 16 * (i % 2) = 0x140 + 16 * (i % 2) + 8 by omega]
  have ft3 : Frame t t3 (fun x => 0xF0 ≤ x ∧ x < 0x110) := f3.mono (by intro x hx; omega)
  have hm3 : TopMem S x tau e t3 := mem_top_frame hm (ft3.mono (by intro z hz; simp only [tchainW]; omega))
    (by rw [r3.get .x5, hm.x5]) (by rw [r3.get .x18, hm.x18])
    (by rw [ft3.getMem (by norm_num) (by omega), hm.pb0])
    (by rw [ft3.getMem (by norm_num) (by omega), hm.cb0])
  have x325 : t3.getReg .x25 = BitVec.ofNat 64 (x.getD i 0) := by
    simp only [ht3, blk611.res, rv_simp, t21]; bvsimp []
    rw [show i * 8 + 1920 = 0x780 + 8 * i by ring, hm.dig i hi]
  have h0 : TStepInv S x tau e i t3 0 s t3 := by
    refine ⟨by omega, hs, by simp only [ht3, blk611.res, rv_simp], v3, ?_, ?_, x325, ?_, ?_,
      RegsEq.refl _ _, Frame.refl _ _, hm3.cb0⟩
    · simp only [ht3, blk611.res, rv_simp]
    · simp only [ht3, blk611.res, rv_simp, t21]; bvsimp []; exact ofNat_congr (by omega)
    · rw [r3.get .x11, t11]
    · simp only [ht3, blk611.res, rv_simp]
  have hsteps := Sim.foldlM_range' 1 (x.getD i 0) (fun v mu => hash16 (chainInput 0 tau e i mu v)) s
    (TStepInv S x tau e i t3) 18 (fun j hj v t h => tstep_body S x tau e i hi t3 hm3 j hj v t h) h0
  unfold chainTo
  refine (Sim.steps hs3 (Sim.bind (W₂ := 10) hsteps (fun v t4 h4 => ?_))).mono
    (by have := Nat.mul_le_mul_right 18 (show x.getD i 0 ≤ 7 by omega); omega) (fun _ _ h => h)
  obtain ⟨-, hvl, pc4, v4, x423, x424, x425, x411, x412, r4, f4, lo4⟩ := h4
  -- block 617: exit
  have hs5 := symRun_sound blk622 codeAt_622 t4 pc4 (by simp only [blk622.res, rv_simp])
  have hc5 : blk622.res.cycles = 1 := rfl
  rw [hc5] at hs5
  set t5 := blk622.res.toState t4 with ht5
  have pc5 : t5.pc = pcOf 633 := by
    simp only [ht5, blk622.res, rv_simp, x423, x425, ofNat_beq_ofNat]
    rw [if_pos (by simp)]
  have m5 : ∀ z, t5.getMem z = t4.getMem z := fun z => by
    rw [ht5, Result.toState_getMem, show blk622.res.st.mem = [] from rfl, memEval_nil]
  have r5 : RegsEq t4 t5 [] := by
    intro r hr; rw [ht5, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  -- block 624: stage the value, next chain
  have rt5 : RegsEq t t5 ([.x1, .x2, .x3, .x12, .x23, .x24, .x25] ++ [.x3, .x10, .x23, .x24, .x29] ++ []) :=
    (r3.trans r4).trans r5
  have y21 : t5.getReg .x21 = BitVec.ofNat 64 i := by rw [rt5.get .x21, t21]
  have y18 : t5.getReg .x18 = BitVec.ofNat 64 0x900 := by rw [rt5.get .x18, hm.x18]
  have hs6 := symRun_sound blk633 codeAt_633 t5 pc5 (by
    simp only [blk633.res, rv_simp]; bvsimp [y21, y18, accessValid_ofNat]; omega)
  have hc6 : blk633.res.cycles = 9 := rfl
  rw [hc6] at hs6
  set t6 := blk633.res.toState t5 with ht6
  have f6 : Frame t5 t6 (fun z => z = 0x908 + 16 * i ∨ z = 0x908 + 16 * i + 8) := by
    apply frame_toState; intro z hz hW
    simp only [blk633.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq]
    bvsimp [y21, y18, ofNat_eq_iff]
    omega
  have r6 : RegsEq t5 t6 [.x1, .x2, .x3, .x21] := by
    intro r hr; rw [ht6, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have ft5 : Frame t t5 (fun z => z = 0xC0 ∨ (0xF0 ≤ z ∧ z < 0x110)) := by
    intro z hz hW
    rw [m5, f4.getMem hz (by omega), ft3.getMem hz (by omega)]
  have ft6 : Frame t t6 tchainW := by
    intro z hz hW
    simp only [tchainW] at hW
    rw [f6.getMem hz (by omega), m5, f4.getMem hz (by omega), ft3.getMem hz (by omega)]
  refine Sim.pure_steps (hs5.trans hs6) ⟨⟨by omega, by simp [hl1], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    by rw [r6.get .x11, r5.get .x11, x411], fun z hz h1 h2 => by
      rw [f6.getMem hz (by omega), m5, f4.getMem hz (by omega), ft3.getMem hz (by omega)]⟩
  · intro w hw; rcases List.mem_append.mp hw with hw | hw
    · exact hv1 w hw
    · simp at hw; subst hw; exact hvl
  · apply Slots.snoc
    · exact hsl.frame (ft5.trans f6) (by omega) (by intro k hk; constructor <;> omega)
    · rw [hl1, readWords_ofNat_two, show 0x908 + 16 * i + 8 = 0x908 + 16 * i + 8 from rfl]
      rw [← v4, readWords_ofNat_two]
      simp only [ht6, blk633.res, rv_simp, m5]
      bvsimp [y21, y18, ofNat_eq_iff]
      simp (disch := bvomega) only [if_pos, if_neg]
  · simp only [ht6, blk633.res, rv_simp, y21, ofNat_add_ofNat, ofNat_bne_ofNat]
    by_cases h : i + 1 < 42
    · rw [if_pos h, if_pos (by rw [bne_cond _ _ (by omega) (by norm_num)]; omega)]
    · rw [if_neg h, if_neg (by rw [bne_cond _ _ (by omega) (by norm_num)]; omega)]
  · simp only [ht6, blk633.res, rv_simp, y21, ofNat_add_ofNat]
  · exact mem_top_frame hm ft6 (by rw [r6.get .x5, rt5.get .x5, hm.x5]) (by rw [r6.get .x18, y18])
      (by rw [f6.getMem (by norm_num) (by omega), m5, f4.getMem (by norm_num) (by omega),
            ft3.getMem (by norm_num) (by omega)]; exact hm.pb0)
      (by rw [f6.getMem (by norm_num) (by omega), m5, lo4])
  · exact ((tregs.trans rt5).trans r6).mono (by decide)
  · exact (tframe.trans ft6).mono (by intro z hz; rcases hz with h | h <;> exact h)

theorem top_pair_spec (S : List Byte) (tau e k : Nat) (x : List Nat) (acc : List Val) :
    (do
      let (s0, s1) ← prf2 (prfInput S 0 tau e k)
      let v0 ← chainTo 0 tau e (2 * k) (x.getD (2 * k) 0) s0
      let v1 ← chainTo 0 tau e (2 * k + 1) (x.getD (2 * k + 1) 0) s1
      pure (acc ++ [v0, v1]) : OracleComp HashSpec (List Val)) =
    H (prfInput S 0 tau e k) >>= fun a =>
      (chainTo 0 tau e (2 * k) (x.getD (2 * k) 0) (answerBytes 16 a) >>= fun v => pure (acc ++ [v])) >>= fun r =>
      chainTo 0 tau e (2 * k + 1) (x.getD (2 * k + 1) 0) (hiVal a) >>= fun v => pure (r ++ [v]) := by
  simp only [prf2_eq, bind_assoc, pure_bind, List.append_assoc, List.cons_append, List.nil_append]

theorem tchain_pair (S : List Byte) (hS : S.length = 32) (x : List Nat) (tau e : Nat) (tm : MachineState)
    (k : Nat) (hk : k < 21) (acc : List Val) (t : MachineState) (hinv : TChainInv S x tau e tm (2 * k) acc t) :
    Sim image t 320 (do
        let (s0, s1) ← prf2 (prfInput S 0 tau e k)
        let v0 ← chainTo 0 tau e (2 * k) (x.getD (2 * k) 0) s0
        let v1 ← chainTo 0 tau e (2 * k + 1) (x.getD (2 * k + 1) 0) s1
        pure (acc ++ [v0, v1])) (TChainInv S x tau e tm (2 * k + 2)) := by
  rw [top_pair_spec]
  obtain ⟨-, hl1, hv1, hsl, tpc, t21, hm, tregs, tframe⟩ := hinv
  have htau := hm.htau
  have he := hm.he
  have tpc' : t.pc = pcOf 603 := by rw [tpc, if_pos (by omega)]
  -- block 598: even
  have hs0 := symRun_sound blk603 codeAt_603 t tpc' (by simp only [blk603.res, rv_simp])
  have hc0 : blk603.res.cycles = 2 := rfl
  rw [hc0] at hs0
  set t1 := blk603.res.toState t with ht1
  have m1 : ∀ z, t1.getMem z = t.getMem z := fun z => by
    rw [ht1, Result.toState_getMem, show blk603.res.st.mem = [] from rfl, memEval_nil]
  have r1 : RegsEq t t1 [.x3] := by
    intro r hr; rw [ht1, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have pc1 : t1.pc = pcOf 605 := by
    simp only [ht1, blk603.res, rv_simp, t21]
    rw [and_one_ofNat _ (by omega), if_neg (by rw [ofNat_bne_ofNat]; simp)]
  -- block 600: the paired prf query
  have hs2 := symRun_sound blk605 codeAt_605 t1 pc1 (by simp only [blk605.res, rv_simp])
  have hc2 : blk605.res.cycles = 5 := rfl
  rw [hc2] at hs2
  set t2 := blk605.res.toState t1 with ht2
  have f2 : Frame t1 t2 (fun x => x = 0x6A0) := by
    apply frame_toState; intro x hx hW
    simp only [blk605.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq, ofNat_eq_iff]
    omega
  have r2 : RegsEq t1 t2 [.x3, .x10, .x11, .x12] := by
    intro r hr; rw [ht2, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have e2 := symRun_ecall blk605 codeAt_605 t1 (by simp only [blk605.res, rv_simp]) rfl
  have x10 : t2.getReg .x10 = BitVec.ofNat 64 0x6A0 := by simp only [ht2, blk605.res, rv_simp]
  have x11 : t2.getReg .x11 = BitVec.ofNat 64 64 := by simp only [ht2, blk605.res, rv_simp]
  have x12 : t2.getReg .x12 = BitVec.ofNat 64 0x140 := by simp only [ht2, blk605.res, rv_simp]
  have x5 : t2.getReg .x5 = 0 := by rw [r2.get .x5, r1.get .x5, hm.x5]
  have pc2 : t2.pc = pcOf 610 := by simp only [ht2, blk605.res, rv_simp]
  have t121 : t1.getReg .x21 = BitVec.ofNat 64 (2 * k) := by rw [r1.get .x21, t21]
  have m6A0 : t2.getMem (BitVec.ofNat 64 0x6A0) = twWord0 0 0 tau k := by
    simp only [ht2, blk605.res, rv_simp, t121]
    bvsimp []
    rw [show 2 * k / 2 = k by omega, twWord0_top _ _ _ (by omega)]
    refine (word_of_halves _ 1 k (by rw [lo32_replace1, m1, hm.pb0]) (by rw [hi32_replace1])).trans ?_
    congr 1
  have ft2 : Frame t t2 (fun x => x = 0x6A0) := fun z hz hW => by rw [f2.getMem hz hW, m1]
  have hq : hashInput t2 = pad64 (prfInput S 0 tau e k) := by
    obtain ⟨hn, hw⟩ := words_prfInput S hS 0 tau e k
    refine hashInput_eq_pad64 t2 _ 0 hn (by rw [x11]) (by norm_num) (by rw [x10]; decide) ?_
    rw [hw, x10, show 8 * (0 + 1) = 1 + 1 + 2 + 4 from rfl]
    rw [readWords_ofNat_add, readWords_ofNat_add, readWords_ofNat_add]
    simp only [Nat.reduceMul, Nat.reduceAdd]
    rw [readWords_ofNat_one, readWords_ofNat_one, m6A0, ft2.getMem (by norm_num) (by norm_num), hm.pb8,
      ft2.readWords _ _ (by norm_num) (by intro i hi; omega),
      ft2.readWords _ _ (by norm_num) (by intro i hi; omega), hm.pbP, hm.pbS]
    simp only [twWords_eq, List.cons_append, List.nil_append, List.cons.injEq, and_true, true_and]
    congr 1; omega
  have hb : (pad64 (prfInput S 0 tau e k)).blocks = 1 := by
    simp [pad64, Query.blocks, (words_prfInput S hS 0 tau e k).1]
  refine (Sim.steps hs0 (Sim.steps hs2 (Sim.query_bind (W := 150 + (2 + 150)) e2 x5
    (hashArgs_of x10 x11 x12 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)) (hq.trans (fmt_thInput _ _ _ _ _ _ (by decide)).symm) (fun a => ?_)))).mono
    (by rw [show prfInput S 0 tau e k = thInput (tweak 0 0 tau k e) S from rfl] at *; rw [blocks_fmt_th _ _ _ _ _ _ (by decide)]
        rw [hb]; norm_num)
    (fun _ _ h => h)
  set t3 := writeHash t2 a with ht3
  have f3 : Frame t2 t3 (fun x => 0x140 ≤ x ∧ x < 0x140 + 32) := frame_writeHash t2 a _ x12 (by norm_num)
  have pc3 : t3.pc = pcOf 611 := by rw [ht3, writeHash_pc, pc2]; apply BitVec.eq_of_toNat_eq; simp
  have g3 : ∀ q, t3.getReg q = t2.getReg q := fun q => by rw [ht3, writeHash_getReg]
  have ft3 : Frame t t3 (fun x => x = 0x6A0 ∨ (0x140 ≤ x ∧ x < 0x140 + 32)) := ft2.trans f3
  have rt3 : RegsEq tm t3 topRegs := ((tregs.trans r1).trans r2 |>.trans
    (show RegsEq t2 t3 [] from fun q _ => g3 q)).mono (by decide)
  have hm3 : TopMem S x tau e t3 := mem_top_frame hm (ft3.mono (by intro z hz; simp only [tchainW]; omega))
    (by rw [g3, r2.get .x5, r1.get .x5, hm.x5]) (by rw [g3, r2.get .x18, r1.get .x18, hm.x18])
    (by rw [f3.getMem (by norm_num) (by omega), m6A0]; simp only [twWord0, lo32_ofNat]
        apply BitVec.eq_of_toNat_eq; simp; omega)
    (by rw [ft3.getMem (by norm_num) (by omega), hm.cb0])
  have hA := tchain_B S x tau e tm (2 * k) (by omega) (answerBytes 16 a) (by simp) acc hl1 hv1 t3
    (hsl.frame ft3 (by omega) (by intro i hi; constructor <;> omega))
    pc3 (by rw [g3, r2.get .x21, t121]) (by rw [g3, x11])
    (by rw [show 0x140 + 16 * (2 * k % 2) = 0x140 by omega]; exact sec_lo t2 a x12)
    hm3 rt3 ((tframe.trans ft3).mono (by intro x hx; simp only [tchainW] at hx ⊢; omega))
  refine Sim.bind hA (fun r t4 h4 => ?_)
  obtain ⟨⟨-, hl14, hv14, hsl4, tpc4, t421, hm4, tregs4, tframe4⟩, x411, sec4⟩ := h4
  -- block 598: odd
  have hs5 := symRun_sound blk603 codeAt_603 t4 (by rw [tpc4, if_pos (by omega)])
    (by simp only [blk603.res, rv_simp])
  have hc5 : blk603.res.cycles = 2 := rfl
  rw [hc5] at hs5
  set t5 := blk603.res.toState t4 with ht5
  have m5 : ∀ z, t5.getMem z = t4.getMem z := fun z => by
    rw [ht5, Result.toState_getMem, show blk603.res.st.mem = [] from rfl, memEval_nil]
  have r5 : RegsEq t4 t5 [.x3] := by
    intro r hr; rw [ht5, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have pc5 : t5.pc = pcOf 611 := by
    simp only [ht5, blk603.res, rv_simp, t421]
    rw [and_one_ofNat _ (by omega), if_pos (by rw [ofNat_bne_ofNat]; simp)]
  have fr5 : Frame t4 t5 (fun _ => False) := fun z _ _ => m5 _
  have hB := tchain_B S x tau e tm (2 * k + 1) (by omega) (hiVal a) (by simp) r hl14 hv14 t5
    (hsl4.frame fr5 (by omega) (by simp)) pc5 (by rw [r5.get .x21, t421]) (by rw [r5.get .x11, x411])
    (by
      rw [show 0x140 + 16 * ((2 * k + 1) % 2) = 0x150 by omega, readWords_ofNat_two, m5, m5,
        sec4 _ (by norm_num) (by norm_num) (by norm_num), sec4 _ (by norm_num) (by norm_num) (by norm_num),
        ← readWords_ofNat_two]
      exact sec_hi t2 a x12)
    (mem_top_frame hm4 (fr5.mono (by intro z hz; exact hz.elim)) (by rw [r5.get .x5, hm4.x5])
      (by rw [r5.get .x18, hm4.x18]) (by rw [m5, hm4.pb0]) (by rw [m5, hm4.cb0]))
    ((tregs4.trans r5).mono (by decide))
    ((tframe4.trans fr5).mono (by intro x hx; rcases hx with h | h; exact h; exact h.elim))
  exact (Sim.steps hs5 hB).mono (by norm_num) (fun _ _ h => h.1)

/-- **Top chains** `i = 0 .. 41` (pairs `k = 0 .. 20`, up to `x_i`). -/
theorem topChains_sim (S : List Byte) (hS : S.length = 32) (x : List Nat) (tau e : Nat) (tm : MachineState)
    (h0 : TChainInv S x tau e tm 0 [] tm) :
    Sim image tm (21 * 320) ((List.range (nChains / 2)).foldlM (fun (acc : List Val) k => do
        let (s0, s1) ← prf2 (prfInput S 0 tau e k)
        let v0 ← chainTo 0 tau e (2 * k) (x.getD (2 * k) 0) s0
        let v1 ← chainTo 0 tau e (2 * k + 1) (x.getD (2 * k + 1) 0) s1
        pure (acc ++ [v0, v1])) []) (TChainInv S x tau e tm 42) := by
  unfold nChains
  exact Sim.foldlM_range 21 _ [] (fun k => TChainInv S x tau e tm (2 * k)) 320
    (fun k hk acc t h => by
      rw [show 2 * (k + 1) = 2 * k + 2 by ring]; exact tchain_pair S hS x tau e tm k hk acc t h) h0

/-- The entry block of the top layer (572 .. 580): PB / CB tweaks, `CB+32..48` cleared. -/
theorem top_entry (S cache : List Byte) (x : List Nat) (tau e : Nat) (t : MachineState)
    (hc : TopCtx S cache x tau e t) (tpc : t.pc = pcOf 594) :
    ∃ u, Steps image t 9 9 u ∧ TChainInv S x tau e u 0 [] u ∧
      RegsEq t u [.x3, .x21] ∧
      Frame t u (fun a => a = 0x6A0 ∨ a = 0x6A8 ∨ a = 0xC0 ∨ a = 0xC8 ∨ a = 0xE0 ∨ a = 0xE8) := by
  have hs := symRun_sound blk594 codeAt_594 t tpc (by simp only [blk594.res, rv_simp])
  have hk : blk594.res.cycles = 9 := rfl
  have hk' : blk594.res.steps = 9 := rfl
  rw [hk, hk'] at hs
  set u := blk594.res.toState t with hu
  have f : Frame t u (fun a => a = 0x6A0 ∨ a = 0x6A8 ∨ a = 0xC0 ∨ a = 0xC8 ∨ a = 0xE0 ∨ a = 0xE8) := by
    apply frame_toState; intro x hx hW
    simp only [blk594.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq, ofNat_eq_iff]
    omega
  have r : RegsEq t u [.x3, .x21] := by
    intro r hr; rw [hu, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  refine ⟨u, hs, ⟨by norm_num, rfl, by simp, Slots.nil _ _, by rw [if_pos (by norm_num)]; simp only [hu, blk594.res, rv_simp],
    by simp only [hu, blk594.res, rv_simp], ?_, RegsEq.refl _ _, Frame.refl _ _⟩, r, f⟩
  refine ⟨hc.htau, hc.he, hc.hx, by rw [r.get .x5, hc.x5], by rw [r.get .x18, hc.x18], fun i hi => ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [f.getMem (by omega) (by omega), hc.dig i hi]
  · simp (config := { decide := true }) only [hu, blk594.res, rv_simp, ↓reduceIte]
  · simp (config := { decide := true }) only [hu, blk594.res, rv_simp, hc.x31, ↓reduceIte]
  · rw [f.readWords _ _ (by norm_num) (by intro i hi; omega), hc.pbP]
  · rw [f.readWords _ _ (by norm_num) (by intro i hi; omega), hc.pbS]
  · simp (config := { decide := true }) only [hu, blk594.res, rv_simp, ↓reduceIte, Nat.zero_div]
    rw [lo32_replace0]; rfl
  · simp (config := { decide := true }) only [hu, blk594.res, rv_simp, hc.x31, ↓reduceIte]
  · rw [show (4 : Nat) = 2 + 2 from rfl, readWords_ofNat_add,
      f.readWords _ _ (by norm_num) (by intro i hi; omega), hc.cbP, readWords_ofNat_two]
    simp only [hu, blk594.res, rv_simp]; rfl

/-! ## The path from the cache -/

theorem words_maskInput (S : List Byte) (hS : S.length = 32) (l j : Nat) :
    padBlocks (maskInput S l j).length = 0 ∧
    wordsOf (padTo64 (maskInput S l j)) = twWords 13 0 0 l j ++ [0, 0] ++ wordsOf S := by
  obtain ⟨h1, h2⟩ := padTo64_eq (maskInput S l j) 0 (by simp [maskInput, hS])
    (by simp [maskInput, hS])
  refine ⟨h1, ?_⟩
  rw [h2, maskInput, wordsOf_thInput_pad]
  simp [hS, zeros]

/-- Addresses written by the path loop. -/
def tpathW (a : Nat) : Prop := a = 0x6A0 ∨ a = 0x6A8 ∨ (0x140 ≤ a ∧ a < 0x160) ∨ (0xBA8 ≤ a ∧ a < 0xBA8 + 176)

def pathRegs : List Reg := [.x1, .x2, .x3, .x10, .x11, .x12, .x15, .x16, .x17, .x19, .x29]

/-- Path-loop invariant after `l` levels. -/
def TPathInv (S cache : List Byte) (e : Nat) (tp : MachineState) (l : Nat) (acc : List Val)
    (t : MachineState) : Prop :=
  l ≤ 11 ∧ acc.length = l ∧ (∀ v ∈ acc, v.length = 16) ∧ Slots t 0xBA8 acc ∧
  t.pc = (if l < 11 then pcOf 646 else pcOf 675) ∧ t.getReg .x15 = BitVec.ofNat 64 l ∧
  t.getReg .x19 = BitVec.ofNat 64 (0x44C0 + 16 * topN l) ∧
  t.getReg .x17 = BitVec.ofNat 64 (16 * 2 ^ (11 - l)) ∧
  RegsEq tp t pathRegs ∧ Frame tp t tpathW

/-- The facts the path loop needs (fixed). -/
structure PathCtx (S cache : List Byte) (e : Nat) (t : MachineState) : Prop where
  he : e < 2048
  x5 : t.getReg .x5 = 0
  x13 : t.getReg .x13 = BitVec.ofNat 64 e
  x18 : t.getReg .x18 = BitVec.ofNat 64 0x900
  pbP : t.readWords (BitVec.ofNat 64 0x6B0) 2 = [0, 0]
  pbS : t.readWords (BitVec.ofNat 64 0x6C0) 4 = wordsOf S
  node : ∀ l j, l < 11 → j < 2 ^ (11 - l) →
    t.readWords (BitVec.ofNat 64 (0x44A0 + cacheNodeOff l j)) 2 = wordsOf (cacheNode cache l j)
  nodeLen : ∀ l j, l < 11 → j < 2 ^ (11 - l) → (cacheNode cache l j).length = 16

theorem sib_lt (e l : Nat) (he : e < 2048) (hl : l < 11) : (e / 2 ^ l) ^^^ 1 < 2 ^ (11 - l) := by
  have h1 : e / 2 ^ l < 2 ^ (11 - l) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add, show 11 - l + l = 11 by omega]; omega
  exact Nat.xor_lt_two_pow h1 (Nat.one_lt_two_pow (by omega))

theorem tpath_body (S cache : List Byte) (hS : S.length = 32) (e : Nat) (tp : MachineState)
    (pc : PathCtx S cache e tp) (l : Nat) (hl : l < 11) (acc : List Val) (t : MachineState)
    (hinv : TPathInv S cache e tp l acc t) :
    Sim image t 36 (do
        let mk ← hash16 (maskInput S l ((e / 2 ^ l) ^^^ 1))
        pure (acc ++ [xorBytes (cacheNode cache l ((e / 2 ^ l) ^^^ 1)) mk]))
      (TPathInv S cache e tp (l + 1)) := by
  obtain ⟨-, hl1, hv1, hsl, tpc, t15, t19, t17, tregs, tframe⟩ := hinv
  have he := pc.he
  set sb := (e / 2 ^ l) ^^^ 1 with hsb
  have hsbl : sb < 2 ^ (11 - l) := sib_lt e l he hl
  have hp11 : 2 ^ (11 - l) ≤ 2048 := by
    calc 2 ^ (11 - l) ≤ 2 ^ 11 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 2048 := by norm_num
  have tpc' : t.pc = pcOf 646 := by rw [tpc, if_pos hl]
  have t13 : t.getReg .x13 = BitVec.ofNat 64 e := by rw [tregs.get .x13, pc.x13]
  -- block 610: mask tweak, HASH
  have hs1 := symRun_sound blk646 codeAt_646 t tpc' (by simp only [blk646.res, rv_simp])
  have hc1 : blk646.res.cycles = 11 := rfl
  rw [hc1] at hs1
  set t1 := blk646.res.toState t with ht1
  have f1 : Frame t t1 (fun x => x = 0x6A0 ∨ x = 0x6A8) := by
    apply frame_toState; intro x hx hW
    simp only [blk646.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq, ofNat_eq_iff]
    omega
  have r1 : RegsEq t t1 [.x3, .x10, .x11, .x12, .x16] := by
    intro r hr; rw [ht1, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have e1 := symRun_ecall blk646 codeAt_646 t (by simp only [blk646.res, rv_simp]) rfl
  have x10 : t1.getReg .x10 = BitVec.ofNat 64 0x6A0 := by simp only [ht1, blk646.res, rv_simp]
  have x11 : t1.getReg .x11 = BitVec.ofNat 64 64 := by simp only [ht1, blk646.res, rv_simp]
  have x12 : t1.getReg .x12 = BitVec.ofNat 64 0x140 := by simp only [ht1, blk646.res, rv_simp]
  have x5 : t1.getReg .x5 = 0 := by rw [r1.get .x5, tregs.get .x5, pc.x5]
  have pc1 : t1.pc = pcOf 657 := by simp only [ht1, blk646.res, rv_simp]
  have hsbw : (t.getReg .x13 >>> ((BitVec.ofNat 64 l).toNat % 64) ^^^ 1#64) = BitVec.ofNat 64 sb := by
    rw [t13]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_xor, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (a := e) (by omega), Nat.mod_eq_of_lt (a := l) (by omega),
      Nat.mod_eq_of_lt (a := l) (by omega), Nat.mod_eq_of_lt (a := sb) (by omega)]
  have x16 : t1.getReg .x16 = BitVec.ofNat 64 sb := by
    simp only [ht1, blk646.res, rv_simp, t15, hsbw]
  have hq : hashInput t1 = pad64 (maskInput S l sb) := by
    obtain ⟨hn, hw⟩ := words_maskInput S hS l sb
    refine hashInput_eq_pad64 t1 _ 0 hn (by rw [x11]) (by norm_num) (by rw [x10]; decide) ?_
    rw [hw, x10, show 8 * (0 + 1) = 1 + 1 + 2 + 4 from rfl]
    rw [readWords_ofNat_add, readWords_ofNat_add, readWords_ofNat_add]
    simp only [Nat.reduceMul, Nat.reduceAdd]
    rw [readWords_ofNat_one, readWords_ofNat_one,
      f1.readWords _ _ (by norm_num) (by intro i hi; omega),
      f1.readWords _ _ (by norm_num) (by intro i hi; omega),
      tframe.readWords _ _ (by norm_num) (by intro i hi; simp only [tpathW]; omega),
      tframe.readWords _ _ (by norm_num) (by intro i hi; simp only [tpathW]; omega), pc.pbP, pc.pbS]
    simp (config := { decide := true }) only [ht1, blk646.res, rv_simp, t15, twWords_eq, twWord0,
      ↓reduceIte, hsbw]
    simp only [List.cons_append, List.nil_append, List.cons.injEq, and_true]
    bvsimp []
    constructor <;> apply ofNat_congr <;> omega
  have hb : (pad64 (maskInput S l sb)).blocks = 1 := by
    simp [pad64, Query.blocks, (words_maskInput S hS l sb).1]
  have hnode := pc.node l sb hl hsbl
  have hnl := pc.nodeLen l sb hl hsbl
  have hoff := cacheNodeOff_lt l sb hl hsbl
  have htn := topN_add_lt l sb hl hsbl
  refine (Sim.steps hs1 (Sim.hash16_bind (W := 17) e1 x5
    (hashArgs_of x10 x11 x12 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)) hq (fmt_thInput _ _ _ _ _ _ (by decide)) (fun a => ?_))).mono (by rw [hb]) (fun _ _ h => h)
  set mk := answerBytes 16 a with hmk
  set t2 := writeHash t1 a with ht2
  have f2 : Frame t1 t2 (fun x => 0x140 ≤ x ∧ x < 0x140 + 32) := frame_writeHash t1 a _ x12 (by norm_num)
  have pc2 : t2.pc = pcOf 658 := by rw [ht2, writeHash_pc, pc1]; apply BitVec.eq_of_toNat_eq; simp
  have r2 : RegsEq t1 t2 [] := fun q _ => by rw [ht2, writeHash_getReg]
  have w0 : t2.getMem (BitVec.ofNat 64 0x140) = a.extractLsb' 0 64 := by
    rw [ht2, writeHash_getMem_ofNat t1 a 0x140 0x140 x12 (by norm_num) (by norm_num)]; simp
  have w1 : t2.getMem (BitVec.ofNat 64 0x148) = a.extractLsb' 64 64 := by
    rw [ht2, writeHash_getMem_ofNat t1 a 0x140 0x148 x12 (by norm_num) (by norm_num)]; simp
  have ft2 : Frame t t2 (fun x => x = 0x6A0 ∨ x = 0x6A8 ∨ (0x140 ≤ x ∧ x < 0x160)) :=
    (f1.trans f2).mono (by intro x hx; omega)
  -- the node words (region untouched)
  have nw : t2.readWords (BitVec.ofNat 64 (0x44A0 + cacheNodeOff l sb)) 2 = wordsOf (cacheNode cache l sb) := by
    rw [ft2.readWords _ _ (by unfold cacheNodeOff; omega) (by intro i hi; unfold cacheNodeOff; omega),
      tframe.readWords _ _ (by unfold cacheNodeOff; omega) (by intro i hi; simp only [tpathW]; unfold cacheNodeOff; omega),
      hnode]
  rw [readWords_ofNat_two] at nw
  obtain ⟨n0, n1, hn⟩ : ∃ n0 n1, wordsOf (cacheNode cache l sb) = [n0, n1] := by
    rw [← nw]; exact ⟨_, _, rfl⟩
  rw [hn] at nw
  simp only [List.cons.injEq, and_true] at nw
  obtain ⟨nw0, nw1⟩ := nw
  -- block 622: store node xor mask, next level
  have y15 : t2.getReg .x15 = BitVec.ofNat 64 l := by rw [r2.get .x15, r1.get .x15, t15]
  have y16 : t2.getReg .x16 = BitVec.ofNat 64 sb := by rw [r2.get .x16, x16]
  have y18 : t2.getReg .x18 = BitVec.ofNat 64 0x900 := by rw [r2.get .x18, r1.get .x18, tregs.get .x18, pc.x18]
  have y19 : t2.getReg .x19 = BitVec.ofNat 64 (0x44C0 + 16 * topN l) := by rw [r2.get .x19, r1.get .x19, t19]
  have y17 : t2.getReg .x17 = BitVec.ofNat 64 (16 * 2 ^ (11 - l)) := by rw [r2.get .x17, r1.get .x17, t17]
  have hs3 := symRun_sound blk658 codeAt_658 t2 pc2 (by
    simp only [blk658.res, rv_simp]; bvsimp [y15, y16, y18, y19, accessValid_ofNat, ne_eq, ofNat_eq_iff]
    omega)
  have hc3 : blk658.res.cycles = 17 := rfl
  rw [hc3] at hs3
  set t3 := blk658.res.toState t2 with ht3
  have f3 : Frame t2 t3 (fun z => z = 0xBA8 + 16 * l ∨ z = 0xBA8 + 16 * l + 8) := by
    apply frame_toState; intro z hz hW
    simp only [blk658.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq]
    bvsimp [y15, y18, ofNat_eq_iff]
    omega
  have r3 : RegsEq t2 t3 [.x1, .x2, .x3, .x15, .x17, .x19, .x29] := by
    intro r hr; rw [ht3, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have hxor : wordsOf (xorBytes (cacheNode cache l sb) mk) =
      [n0 ^^^ a.extractLsb' 0 64, n1 ^^^ a.extractLsb' 64 64] :=
    wordsOf_xorBytes _ _ hnl (by simp [hmk]) _ _ _ _ hn (by rw [hmk, wordsOf_answerBytes_16])
  refine Sim.pure_steps hs3 ⟨by omega, by simp [hl1], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro w hw; rcases List.mem_append.mp hw with hw | hw
    · exact hv1 w hw
    · simp at hw; subst hw; rw [length_xorBytes' _ _ (by simp [hmk, hnl])]; exact hnl
  · apply Slots.snoc
    · exact hsl.frame (ft2.trans f3) (by omega) (by intro k hk; constructor <;> omega)
    · rw [hl1, hxor, readWords_ofNat_two]
      simp only [ht3, blk658.res, rv_simp]
      bvsimp [y15, y16, y18, y19, ofNat_eq_iff]
      simp (disch := bvomega) only [if_pos, if_neg]
      rw [show sb * 16 + (17600 + 16 * topN l) = 0x44A0 + cacheNodeOff l sb by unfold cacheNodeOff; ring,
        show 0x44A0 + cacheNodeOff l sb + 8 = 0x44A0 + cacheNodeOff l sb + 8 from rfl, nw0, nw1,
        show (320#64 : Word) = BitVec.ofNat 64 0x140 from rfl, show (328#64 : Word) = BitVec.ofNat 64 0x148 from rfl,
        w0, w1]
  · simp only [ht3, blk658.res, rv_simp, y15, ofNat_add_ofNat, ofNat_bne_ofNat]
    by_cases h : l + 1 < 11
    · rw [if_pos h, if_pos (by rw [bne_cond _ _ (by omega) (by norm_num)]; omega)]
    · rw [if_neg h, if_neg (by rw [bne_cond _ _ (by omega) (by norm_num)]; omega)]
  · simp only [ht3, blk658.res, rv_simp, y15, ofNat_add_ofNat]
  · simp only [ht3, blk658.res, rv_simp, y19, y17, ofNat_add_ofNat]
    rw [topN_succ l hl]; exact ofNat_congr (by ring_nf)
  · simp only [ht3, blk658.res, rv_simp, y17]; bvsimp []
    exact ofNat_congr (by
      rw [show 11 - l = (11 - (l + 1)) + 1 by omega, Nat.pow_succ]; omega)
  · exact (((tregs.trans r1).trans r2).trans r3).mono (by decide)
  · exact (tframe.trans (ft2.trans f3)).mono (by
      intro z hz; simp only [tpathW] at hz ⊢; omega)

/-- **Top path** `l = 0 .. 10`. -/
theorem topPath_sim (S cache : List Byte) (hS : S.length = 32) (e : Nat) (tp : MachineState)
    (pc : PathCtx S cache e tp) (h0 : TPathInv S cache e tp 0 [] tp) :
    Sim image tp (11 * 36) (topPath S cache e) (TPathInv S cache e tp 11) := by
  unfold topPath
  rw [show topH = 11 from rfl]
  exact Sim.foldlM_range 11 _ [] (TPathInv S cache e tp) 36
    (fun l hl acc t h => tpath_body S cache hS e tp pc l hl acc t h) h0

/-- Result of the top layer. -/
def TopPost (t0 : MachineState) (r : List Val × List Val) (t : MachineState) : Prop :=
  r.1.length = 42 ∧ (∀ v ∈ r.1, v.length = 16) ∧ Slots t 0x908 r.1 ∧
  r.2.length = 11 ∧ (∀ v ∈ r.2, v.length = 16) ∧ Slots t 0xBA8 r.2 ∧
  t.pc = pcOf 675 ∧ t.getReg .x5 = 0 ∧ Frame t0 t topW

/-- **The top layer** (chains up to `x_i`, path from the cache). -/
theorem top_sim (S cache : List Byte) (hS : S.length = 32) (x : List Nat) (tau e : Nat) (t : MachineState)
    (hc : TopCtx S cache x tau e t) (tpc : t.pc = pcOf 594) :
    Sim image t (9 + (21 * 320 + (4 + 11 * 36)))
      ((List.range (nChains / 2)).foldlM (fun (acc : List Val) k => do
        let (s0, s1) ← prf2 (prfInput S 0 tau e k)
        let v0 ← chainTo 0 tau e (2 * k) (x.getD (2 * k) 0) s0
        let v1 ← chainTo 0 tau e (2 * k + 1) (x.getD (2 * k + 1) 0) s1
        pure (acc ++ [v0, v1])) [] >>= fun vals => topPath S cache e >>= fun path => pure (vals, path))
      (TopPost t) := by
  obtain ⟨u, hsu, hu0, ru, fu⟩ := top_entry S cache x tau e t hc tpc
  refine Sim.steps hsu (Sim.bind (topChains_sim S hS x tau e u hu0) (fun vals t1 h1 => ?_))
  obtain ⟨-, hl1, hv1, hsl1, pc1, -, hm1, r1, f1⟩ := h1
  have pc1' : t1.pc = pcOf 642 := by rw [pc1]; rfl
  -- block 606: path loop setup
  have hs2 := symRun_sound blk642 codeAt_642 t1 pc1' (by simp only [blk642.res, rv_simp])
  have hc2 : blk642.res.cycles = 4 := rfl
  rw [hc2] at hs2
  set t2 := blk642.res.toState t1 with ht2
  have m2 : ∀ z, t2.getMem z = t1.getMem z := fun z => by
    rw [ht2, Result.toState_getMem, show blk642.res.st.mem = [] from rfl, memEval_nil]
  have r2 : RegsEq t1 t2 [.x15, .x17, .x19] := by
    intro r hr; rw [ht2, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have ft2 : Frame t t2 (fun a => (a = 0x6A0 ∨ a = 0x6A8 ∨ a = 0xC0 ∨ a = 0xC8 ∨ a = 0xE0 ∨ a = 0xE8) ∨
      tchainW a) := fun z hz hW => by rw [m2, (fu.trans f1).getMem hz hW]
  have rt2 : RegsEq t t2 ([.x3, .x21] ++ topRegs ++ [.x15, .x17, .x19]) := (ru.trans r1).trans r2
  have pc : PathCtx S cache e t2 := by
    refine ⟨hc.he, by rw [rt2.get .x5, hc.x5], by rw [rt2.get .x13, hc.x13], by rw [rt2.get .x18, hc.x18],
      ?_, ?_, fun l j hl hj => ?_, hc.nodeLen⟩
    · rw [ft2.readWords _ _ (by norm_num) (by intro i hi; simp only [tchainW]; omega), hc.pbP]
    · rw [ft2.readWords _ _ (by norm_num) (by intro i hi; simp only [tchainW]; omega), hc.pbS]
    · have := cacheNodeOff_lt l j hl hj
      have : 32 ≤ cacheNodeOff l j := by unfold cacheNodeOff; omega
      rw [ft2.readWords _ _ (by omega) (by intro i hi; simp only [tchainW]; omega), hc.node l j hl hj]
  have h0 : TPathInv S cache e t2 0 [] t2 := by
    refine ⟨by norm_num, rfl, by simp, Slots.nil _ _,
      by rw [if_pos (by norm_num)]; simp only [ht2, blk642.res, rv_simp],
      by simp only [ht2, blk642.res, rv_simp], ?_, ?_, RegsEq.refl _ _, Frame.refl _ _⟩
    · simp only [ht2, blk642.res, rv_simp]; rfl
    · simp only [ht2, blk642.res, rv_simp]; rfl
  refine Sim.steps hs2 (Sim.bind (W₂ := 0) (topPath_sim S cache hS e t2 pc h0) (fun path t3 h3 => ?_))
  obtain ⟨-, hl3, hv3, hsl3, pc3, -, -, -, r3, f3⟩ := h3
  refine Sim.pure ⟨hl1, hv1, ?_, hl3, hv3, hsl3, by rw [pc3]; rfl, ?_, ?_⟩
  · have fr : Frame t1 t3 tpathW := fun z hz hW => by rw [f3.getMem hz hW, m2]
    exact hsl1.frame fr (by omega) (by intro k hk; simp only [tpathW]; constructor <;> omega)
  · rw [r3.get .x5, rt2.get .x5, hc.x5]
  · exact (ft2.trans f3).mono (by intro z hz; simp only [tchainW, tpathW, topW] at hz ⊢; omega)

end SigGolfCandidate.Radix27Sign



end


section -- SignClone13.TreeChain

/-! ### cloned TreeChain -/

/-!
# `sign`, tree_build: the chains of one leaf (`tb_chain_loop`, instructions 517 .. 556)

`chains_sim` : from `tb_chain_loop` with `I = 0`, the machine refines the 42 chains of
`buildLeaf` (ends at `LB + 32 + 16 i`, captured values at `SIGL + 8 + 16 i` in leaf `e`).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace SigGolfCandidate.Radix27Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

/-- Parameters of the chains of leaf `ep` of tree `(lay, tau)` with capture leaf `e`. -/
structure LeafPar where
  lay : Nat
  tau : Nat
  e : Nat
  ep : Nat
  sigl : Nat

/-- Facts at the start of the chain loop of leaf `ep`. -/
structure ChainCtx (S : List Byte) (x : List Nat) (p : LeafPar) (tl : MachineState) : Prop where
  hlay : p.lay < 7
  htau : p.tau < 2 ^ 30
  he : p.e < 64
  hep : p.ep < 64
  hsigl : p.sigl = 0x900 + 856 * p.lay
  hx : ∀ i, x.getD i 0 < 8
  x5 : tl.getReg .x5 = 0
  x13 : tl.getReg .x13 = BitVec.ofNat 64 p.e
  x18 : tl.getReg .x18 = BitVec.ofNat 64 p.sigl
  x20 : tl.getReg .x20 = BitVec.ofNat 64 p.ep
  dig : ∀ i < 42, tl.getMem (BitVec.ofNat 64 (0x780 + 8 * i)) = BitVec.ofNat 64 (x.getD i 0)
  pb0 : lo32 (tl.getMem (BitVec.ofNat 64 0x6A0)) = BitVec.ofNat 32 (1 + 65536 * p.lay)
  pb8 : tl.getMem (BitVec.ofNat 64 0x6A8) = BitVec.ofNat 64 (p.tau + 2 ^ 32 * p.ep)
  pbP : tl.readWords (BitVec.ofNat 64 0x6B0) 2 = [0, 0]
  pbS : tl.readWords (BitVec.ofNat 64 0x6C0) 4 = wordsOf S
  cb0 : lo32 (tl.getMem (BitVec.ofNat 64 0xC0)) = BitVec.ofNat 32 (0x101 + 65536 * p.lay)
  cb8 : tl.getMem (BitVec.ofNat 64 0xC8) = BitVec.ofNat 64 (p.tau + 2 ^ 32 * p.ep)
  cbP : tl.readWords (BitVec.ofNat 64 0xD0) 4 = [0, 0, 0, 0]

/-- Addresses written by the chain loop. -/
def chainW (p : LeafPar) (a : Nat) : Prop :=
  a = 0x6A0 ∨ a = 0xC0 ∨ (0xF0 ≤ a ∧ a < 0x110) ∨ (0x140 ≤ a ∧ a < 0x160) ∨ (0x360 ≤ a ∧ a < 0x360 + 672) ∨
    (p.ep = p.e ∧ p.sigl + 8 ≤ a ∧ a < p.sigl + 8 + 672)

def chainRegs : List Reg := [.x1, .x2, .x3, .x10, .x11, .x12, .x21, .x23, .x24, .x25, .x29]

/-- Invariant after `i` chains. -/
def ChainInv (p : LeafPar) (tl : MachineState) (i : Nat) (st : List Val × List Val) (t : MachineState) :
    Prop :=
  i ≤ 42 ∧ st.1.length = i ∧ st.2.length = i ∧ (∀ v ∈ st.1, v.length = 16) ∧
  (∀ v ∈ st.2, v.length = 16) ∧ Slots t 0x360 st.1 ∧ (p.ep = p.e → Slots t (p.sigl + 8) st.2) ∧
  t.pc = (if i < 42 then pcOf 486 else pcOf 541) ∧ t.getReg .x21 = BitVec.ofNat 64 i ∧
  t.getReg .x24 = BitVec.ofNat 64 (8 * i) ∧
  RegsEq tl t chainRegs ∧ Frame tl t (chainW p) ∧
  lo32 (t.getMem (BitVec.ofNat 64 0x6A0)) = lo32 (tl.getMem (BitVec.ofNat 64 0x6A0)) ∧
  lo32 (t.getMem (BitVec.ofNat 64 0xC0)) = lo32 (tl.getMem (BitVec.ofNat 64 0xC0))

/-- The paired-secret leaf body as a bind chain. -/
theorem chain_pair_spec (S : List Byte) (lay tau ep k : Nat) (x : List Nat) (st : List Val × List Val) :
    (do
      let (s0, s1) ← prf2 (prfInput S lay tau ep k)
      let (v0, c0) ← chainSteps lay tau ep (2 * k) (x.getD (2 * k) 0) s0
      let (v1, c1) ← chainSteps lay tau ep (2 * k + 1) (x.getD (2 * k + 1) 0) s1
      pure (st.1 ++ [v0, v1], st.2 ++ [c0, c1]) : OracleComp HashSpec (List Val × List Val)) =
    H (prfInput S lay tau ep k) >>= fun a =>
      (chainSteps lay tau ep (2 * k) (x.getD (2 * k) 0) (answerBytes 16 a) >>= fun q =>
        pure (st.1 ++ [q.1], st.2 ++ [q.2])) >>= fun r =>
      chainSteps lay tau ep (2 * k + 1) (x.getD (2 * k + 1) 0) (hiVal a) >>= fun q =>
        pure (r.1 ++ [q.1], r.2 ++ [q.2]) := by
  simp only [prf2_eq, bind_assoc, pure_bind, List.append_assoc, List.cons_append, List.nil_append]

/-- The secret region `SEC` is untouched. -/
def SecPres (s t : MachineState) : Prop :=
  ∀ x, x < 2 ^ 64 → 0x140 ≤ x → x < 0x160 → t.getMem (BitVec.ofNat 64 x) = s.getMem (BitVec.ofNat 64 x)

/-- From the step loop to the end of chain `i` (steps, then instructions 548 .. 556). -/
theorem chain_rest (p : LeafPar) (tl : MachineState) (i xi : Nat) (hi : i < 42) (hxi : xi < 8)
    (st : List Val × List Val) (hl1 : st.1.length = i) (hl2 : st.2.length = i)
    (hv1 : ∀ v ∈ st.1, v.length = 16) (hv2 : ∀ v ∈ st.2, v.length = 16)
    (ts : MachineState) (sctx : StepCtx ⟨p.lay, p.tau, p.e, p.ep, i, xi, p.sigl⟩ ts) (v0 : Val)
    (h0 : StepInv ⟨p.lay, p.tau, p.e, p.ep, i, xi, p.sigl⟩ ts 0 (v0, v0) ts)
    (hends : Slots ts 0x360 st.1) (hcaps : p.ep = p.e → Slots ts (p.sigl + 8) st.2)
    (tregs : RegsEq tl ts chainRegs) (tframe : Frame tl ts (chainW p))
    (tlo1 : lo32 (ts.getMem (BitVec.ofNat 64 0x6A0)) = lo32 (tl.getMem (BitVec.ofNat 64 0x6A0)))
    (tlo2 : lo32 (ts.getMem (BitVec.ofNat 64 0xC0)) = lo32 (tl.getMem (BitVec.ofNat 64 0xC0))) :
    Sim image ts (7 * 29 + 9) ((List.range' 1 7).foldlM (fun (st : Val × Val) mu => do
        let v ← hash16 (chainInput p.lay p.tau p.ep i mu st.1)
        pure (v, if mu = xi then v else st.2)) (v0, v0) >>= fun q =>
          pure (st.1 ++ [q.1], st.2 ++ [q.2]))
      (fun r t' => ChainInv p tl (i + 1) r t' ∧ t'.getReg .x11 = BitVec.ofNat 64 64 ∧ SecPres ts t') := by
  have hsig : p.sigl = 0x900 + 856 * p.lay := sctx.hsigl
  have hl : p.lay < 7 := sctx.hlay
  refine Sim.bind (steps_sim ⟨p.lay, p.tau, p.e, p.ep, i, xi, p.sigl⟩ ts sctx v0 h0)
    (fun q t5 h5 => ?_)
  obtain ⟨-, hq1, hq2, tv5, -, pc5, -, x524, cap5, sregs, sframe, slo⟩ := h5
  have pc5' : t5.pc = pcOf 532 := by rw [pc5]; rfl
  have x521 : t5.getReg .x21 = BitVec.ofNat 64 i := by rw [sregs.get .x21, sctx.x21]
  have hs6 := symRun_sound blk532 codeAt_532 t5 pc5' (by
    simp only [blk532.res, rv_simp]; bvsimp [x521, accessValid_ofNat]; omega)
  have hc6 : blk532.res.cycles = 9 := rfl
  rw [hc6] at hs6
  set t6 := blk532.res.toState t5 with ht6
  have f6 : Frame t5 t6 (fun x => x = 0x360 + 16 * i ∨ x = 0x360 + 16 * i + 8) := by
    apply frame_toState; intro x hx hW
    simp only [blk532.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq]
    bvsimp [x521, ofNat_eq_iff]
    omega
  have r6 : RegsEq t5 t6 [.x1, .x2, .x3, .x21, .x24] := by
    intro r hr; rw [ht6, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have fs6 : Frame ts t6 (fun x => stepW ⟨p.lay, p.tau, p.e, p.ep, i, xi, p.sigl⟩ x ∨
      (x = 0x360 + 16 * i ∨ x = 0x360 + 16 * i + 8)) := sframe.trans f6
  refine Sim.pure_steps hs6 ⟨⟨by omega, by simp [hl1], by simp [hl2], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩, by rw [r6.get .x11, sregs.get .x11, sctx.x11],
    fun x hx h1 h2 => fs6.getMem hx (by dsimp only [stepW]; omega)⟩
  · intro v hv; rcases List.mem_append.mp hv with hv | hv
    · exact hv1 v hv
    · simp at hv; subst hv; exact hq1
  · intro v hv; rcases List.mem_append.mp hv with hv | hv
    · exact hv2 v hv
    · simp at hv; subst hv; exact hq2
  · apply Slots.snoc
    · exact hends.frame fs6 (by omega) (by
        intro j hj; dsimp only [stepW]; constructor <;> omega)
    · rw [hl1, readWords_ofNat_two, ← tv5, readWords_ofNat_two]
      simp only [ht6, blk532.res, rv_simp]
      bvsimp [x521, ofNat_eq_iff]
      simp (disch := bvomega) only [if_pos, if_neg]
  · intro hee
    apply Slots.snoc
    · exact (hcaps hee).frame fs6 (by omega) (by
        intro j hj; dsimp only [stepW]; constructor <;> omega)
    · rw [hl2, f6.readWords _ _ (by omega) (by intro j hj; omega)]
      exact cap5 hee (show xi ≤ 7 by omega)
  · simp only [ht6, blk532.res, rv_simp]
    bvsimp [x521, ofNat_bne_ofNat]
    by_cases h : i + 1 < 42
    · rw [if_pos h, if_pos (by simp; omega)]
    · rw [if_neg h, if_neg (by simp; omega)]
  · simp only [ht6, blk532.res, rv_simp]; bvsimp [x521]
  · simp only [ht6, blk532.res, rv_simp]; bvsimp [x524]
    rw [show 8 * i + 7 + 1 = 8 * (i + 1) by ring]
  · exact ((tregs.trans sregs).trans r6).mono (by decide)
  · exact (tframe.trans fs6).mono (by
      intro x hx; dsimp only [chainW, stepW] at hx ⊢; omega)
  · rw [f6.getMem (by norm_num) (by omega), sframe.getMem (by norm_num) (by dsimp only [stepW]; omega),
      tlo1]
  · rw [f6.getMem (by norm_num) (by omega), slo, tlo2]

/-- The capture at `MU = 0` (instructions 527 .. 532, same code as 540 .. 545). -/
theorem chain_capture (sigl i : Nat) (hsig : sigl < 0x900 + 856 * 7) (hsig8 : sigl % 8 = 0) (hi : i < 42) (t : MachineState)
    (tpc : t.pc = pcOf 507) (t21 : t.getReg .x21 = BitVec.ofNat 64 i)
    (t18 : t.getReg .x18 = BitVec.ofNat 64 sigl) :
    ∃ t', Steps image t 6 6 t' ∧ t'.pc = pcOf 513 ∧ RegsEq t t' [.x1, .x2, .x3] ∧
      Frame t t' (fun x => x = sigl + 8 + 16 * i ∨ x = sigl + 16 + 16 * i) ∧
      t'.readWords (BitVec.ofNat 64 (sigl + 8 + 16 * i)) 2 = t.readWords (BitVec.ofNat 64 0xF0) 2 := by
  have hs := symRun_sound blk507 codeAt_507 t tpc (by
    simp only [blk507.res, rv_simp]; bvsimp [t21, t18, accessValid_ofNat]; omega)
  refine ⟨_, hs, by simp only [blk507.res, rv_simp], ?_, ?_, ?_⟩
  · intro r hr; rw [Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  · apply frame_toState; intro x hx hW
    simp only [blk507.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq]
    bvsimp [t21, t18, ofNat_eq_iff]
    omega
  · rw [readWords_ofNat_two, readWords_ofNat_two]
    simp only [blk507.res, rv_simp]
    bvsimp [t21, t18, ofNat_eq_iff]
    simp (disch := bvomega) only [if_pos, if_neg]

/-- Chain `i` of leaf `ep` from `prf_have` (instruction 492): its secret `s` at `SEC + 16 (i & 1)`. -/
theorem chain_B (x : List Nat) (p : LeafPar) (S : List Byte)
    (tl : MachineState) (ctx : ChainCtx S x p tl) (i : Nat) (hi : i < 42) (s : Val) (hs : s.length = 16)
    (st : List Val × List Val) (hl1 : st.1.length = i) (hl2 : st.2.length = i)
    (hv1 : ∀ v ∈ st.1, v.length = 16) (hv2 : ∀ v ∈ st.2, v.length = 16)
    (t : MachineState) (hends : Slots t 0x360 st.1) (hcaps : p.ep = p.e → Slots t (p.sigl + 8) st.2)
    (tpc : t.pc = pcOf 494) (t21 : t.getReg .x21 = BitVec.ofNat 64 i)
    (t24 : t.getReg .x24 = BitVec.ofNat 64 (8 * i)) (t11 : t.getReg .x11 = BitVec.ofNat 64 64)
    (tsec : t.readWords (BitVec.ofNat 64 (0x140 + 16 * (i % 2))) 2 = wordsOf s)
    (tregs : RegsEq tl t chainRegs) (tframe : Frame tl t (chainW p))
    (tlo1 : lo32 (t.getMem (BitVec.ofNat 64 0x6A0)) = lo32 (tl.getMem (BitVec.ofNat 64 0x6A0)))
    (tlo2 : lo32 (t.getMem (BitVec.ofNat 64 0xC0)) = lo32 (tl.getMem (BitVec.ofNat 64 0xC0))) :
    Sim image t (12 + (1 + (6 + (7 * 29 + 9))))
      (chainSteps p.lay p.tau p.ep i (x.getD i 0) s >>= fun q => pure (st.1 ++ [q.1], st.2 ++ [q.2]))
      (fun r t' => ChainInv p tl (i + 1) r t' ∧ t'.getReg .x11 = BitVec.ofNat 64 64 ∧ SecPres t t') := by
  have hsig := ctx.hsigl
  have hl := ctx.hlay
  have htau := ctx.htau
  have hep := ctx.hep
  have he := ctx.he
  have hxi := ctx.hx i
  have tx5 : t.getReg .x5 = 0 := by rw [tregs.get .x5, ctx.x5]
  have tx13 : t.getReg .x13 = BitVec.ofNat 64 p.e := by rw [tregs.get .x13, ctx.x13]
  have tx18 : t.getReg .x18 = BitVec.ofNat 64 p.sigl := by rw [tregs.get .x18, ctx.x18]
  have tx20 : t.getReg .x20 = BitVec.ofNat 64 p.ep := by rw [tregs.get .x20, ctx.x20]
  have hi2 : i % 2 < 2 := Nat.mod_lt _ (by norm_num)
  -- block 492: secret → CB+48, step setup, digit, test EP = e
  have hs3 := symRun_sound blk494 codeAt_494 t tpc (by
    simp only [blk494.res, rv_simp]
    rw [t21, secAddr i (by omega) 328 (by norm_num), secAddr i (by omega) 320 (by norm_num)]
    bvsimp [accessValid_ofNat, ne_eq, ofNat_eq_iff]; omega)
  have hc3 : blk494.res.cycles = 12 := rfl
  rw [hc3] at hs3
  set t3 := blk494.res.toState t with ht3
  have f3 : Frame t t3 (fun x => x = 0xF0 ∨ x = 0xF8) := by
    apply frame_toState; intro x hx hW
    simp only [blk494.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq, ofNat_eq_iff]
    omega
  have r3 : RegsEq t t3 [.x1, .x2, .x3, .x10, .x12, .x23, .x25] := by
    intro r hr; rw [ht3, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have ft3 : Frame t t3 (fun x => 0xF0 ≤ x ∧ x < 0x110) :=
    f3.mono (by intro x hx; omega)
  have x325 : t3.getReg .x25 = BitVec.ofNat 64 (x.getD i 0) := by
    simp only [ht3, blk494.res, rv_simp]; bvsimp [t21]
    rw [show i * 8 + 1920 = 0x780 + 8 * i by ring, tframe.getMem (by omega) (by simp only [chainW]; omega),
      ctx.dig i hi]
  have x323 : t3.getReg .x23 = BitVec.ofNat 64 0 := by simp only [ht3, blk494.res, rv_simp]
  have x312 : t3.getReg .x12 = BitVec.ofNat 64 0xF0 := by simp only [ht3, blk494.res, rv_simp]
  have v3 : t3.readWords (BitVec.ofNat 64 0xF0) 2 = wordsOf s := by
    rw [← tsec, readWords_ofNat_two, readWords_ofNat_two]
    simp only [ht3, blk494.res, rv_simp, t21]
    rw [secAddr i (by omega) 328 (by norm_num), secAddr i (by omega) 320 (by norm_num)]
    simp (config := { decide := true }) only [↓reduceIte]
    rw [show 328 + 16 * (i % 2) = 0x140 + 16 * (i % 2) + 8 by omega]
  have z3 : t3.readWords (BitVec.ofNat 64 0xD0) 4 = [0, 0, 0, 0] := by
    rw [ft3.readWords _ _ (by norm_num) (by intro i hi; omega),
      tframe.readWords _ _ (by norm_num) (by intro i hi; simp only [chainW]; omega), ctx.cbP]
  have pc3 : t3.pc = if p.ep = p.e then pcOf 506 else pcOf 513 := by
    simp only [ht3, blk494.res, rv_simp, tx20, tx13, ofNat_bne_ofNat]
    by_cases h : p.ep = p.e
    · rw [if_pos h, if_neg (by simp; omega)]
    · rw [if_neg h, if_pos (by simp; omega)]
  -- common continuation from `tb_step_loop`
  have hrest : ∀ ts : MachineState, ts.pc = pcOf 513 → RegsEq t3 ts [.x1, .x2, .x3] →
      Frame t3 ts (fun x => p.ep = p.e ∧ (x = p.sigl + 8 + 16 * i ∨ x = p.sigl + 16 + 16 * i)) →
      (p.ep = p.e → x.getD i 0 ≤ 0 →
        ts.readWords (BitVec.ofNat 64 (p.sigl + 8 + 16 * i)) 2 = wordsOf s) →
      Sim image ts (7 * 29 + 9)
        (chainSteps p.lay p.tau p.ep i (x.getD i 0) s >>= fun q => pure (st.1 ++ [q.1], st.2 ++ [q.2]))
        (fun r t' => ChainInv p tl (i + 1) r t' ∧ t'.getReg .x11 = BitVec.ofNat 64 64 ∧ SecPres t t') := by
    intro ts tspc tsr tsf tscap
    have fts : Frame t ts (fun x => (0xF0 ≤ x ∧ x < 0x110) ∨
        (p.ep = p.e ∧ (x = p.sigl + 8 + 16 * i ∨ x = p.sigl + 16 + 16 * i))) := ft3.trans tsf
    have rts : RegsEq t ts ([.x1, .x2, .x3, .x10, .x12, .x23, .x25] ++ [.x1, .x2, .x3]) :=
      r3.trans tsr
    have sctx : StepCtx ⟨p.lay, p.tau, p.e, p.ep, i, x.getD i 0, p.sigl⟩ ts := by
      refine ⟨hl, htau, he, hep, hi, hxi, hsig, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [rts.get .x5, tx5]
      · rw [rts.get .x11, t11]
      · rw [tsr.get .x12, x312]
      · rw [rts.get .x13, tx13]
      · rw [rts.get .x18, tx18]
      · rw [rts.get .x20, tx20]
      · rw [rts.get .x21, t21]
      · rw [tsr.get .x25, x325]
      · rw [fts.getMem (by norm_num) (by omega), tlo2, ctx.cb0]
      · rw [fts.getMem (by norm_num) (by omega), tframe.getMem (by norm_num) (by simp only [chainW]; omega),
          ctx.cb8]
      · rw [fts.readWords _ _ (by norm_num) (by intro j hj; omega),
          tframe.readWords _ _ (by norm_num) (by intro j hj; simp only [chainW]; omega), ctx.cbP]
    have h0 : StepInv ⟨p.lay, p.tau, p.e, p.ep, i, x.getD i 0, p.sigl⟩ ts 0 (s, s) ts := by
      refine ⟨by norm_num, hs, hs, ?_, ?_, by rw [tspc]; rfl, ?_, ?_, tscap,
        RegsEq.refl _ _, Frame.refl _ _, rfl⟩
      · rw [tsf.readWords _ _ (by norm_num) (by intro j hj; omega), v3]
      · rw [tsf.readWords _ _ (by norm_num) (by intro j hj; omega), z3]
      · rw [tsr.get .x23, x323]
      · show ts.getReg .x24 = BitVec.ofNat 64 (8 * i + 0)
        rw [rts.get .x24, t24, Nat.add_zero]
    have := chain_rest p tl i (x.getD i 0) hi hxi st hl1 hl2 hv1 hv2 ts sctx s h0
      (hends.frame fts (by omega) (by intro j hj; constructor <;> omega))
      (fun hee => (hcaps hee).frame fts (by omega) (by intro j hj; constructor <;> omega))
      ((tregs.trans rts).mono (by decide))
      ((tframe.trans fts).mono (by intro x hx; simp only [chainW] at hx ⊢; omega))
      (by rw [fts.getMem (by norm_num) (by omega), tlo1])
      (by rw [fts.getMem (by norm_num) (by omega), tlo2])
    unfold chainSteps
    exact this.mono (le_refl _) (fun r t' h => ⟨h.1, h.2.1, fun y hy h1 h2 => by
      rw [h.2.2 y hy h1 h2, fts.getMem hy (by omega)]⟩)
  by_cases hee : p.ep = p.e
  · have hs4 := symRun_sound blk506 codeAt_506 t3 (by rw [pc3, if_pos hee])
      (by simp only [blk506.res, rv_simp])
    have hc4 : blk506.res.cycles = 1 := rfl
    rw [hc4] at hs4
    set t4 := blk506.res.toState t3 with ht4
    have f4 : Frame t3 t4 (fun _ => False) := by
      apply frame_toState; intro x hx hW; simp [blk506.res]
    have r4 : RegsEq t3 t4 [] := by
      intro r hr; rw [ht4, Result.toState_getReg]
      cases r <;> first | exact absurd (by decide) hr | rfl
    have pc4 : t4.pc = if x.getD i 0 = 0 then pcOf 507 else pcOf 513 := by
      simp only [ht4, blk506.res, rv_simp, x323, x325, ofNat_bne_ofNat]
      by_cases h : x.getD i 0 = 0
      · rw [if_pos h, if_neg (by rw [bne_cond _ _ (by norm_num) (by omega)]; omega)]
      · rw [if_neg h, if_pos (by rw [bne_cond _ _ (by norm_num) (by omega)]; omega)]
    by_cases hx0 : x.getD i 0 = 0
    · obtain ⟨t5, hs5, pc5, r5, f5, cap5⟩ := chain_capture p.sigl i (by omega) (by omega) hi t4
        (by rw [pc4, if_pos hx0]) (by rw [r4.get .x21, r3.get .x21, t21])
        (by rw [r4.get .x18, r3.get .x18, tx18])
      have := hrest t5 pc5 ((r4.trans r5).mono (by decide))
        ((f4.trans f5).mono (by intro x hx; rcases hx with h | h; exact h.elim; exact ⟨hee, h⟩))
        (fun _ _ => by rw [cap5, f4.readWords _ _ (by norm_num) (by simp), v3])
      exact (Sim.steps hs3 (Sim.steps hs4 (Sim.steps hs5 this))).mono (by norm_num) (fun _ _ h => h)
    · have := hrest t4 (by rw [pc4, if_neg hx0]) (r4.mono (by decide))
        (f4.mono (by intro x hx; exact hx.elim)) (fun _ h => absurd (Nat.le_zero.mp h) hx0)
      exact (Sim.steps hs3 (Sim.steps hs4 this)).mono (by norm_num) (fun _ _ h => h)
  · have := hrest t3 (by rw [pc3, if_neg hee]) (RegsEq.refl _ _) (Frame.refl _ _)
      (fun h => absurd h hee)
    exact (Sim.steps hs3 this).mono (by norm_num) (fun _ _ h => h)

theorem chain_pair (S : List Byte) (hS : S.length = 32) (x : List Nat) (p : LeafPar)
    (tl : MachineState) (ctx : ChainCtx S x p tl) (k : Nat) (hk : k < 21)
    (st : List Val × List Val) (t : MachineState) (hinv : ChainInv p tl (2 * k) st t) :
    Sim image t 480
      (do
        let (s0, s1) ← prf2 (prfInput S p.lay p.tau p.ep k)
        let (v0, c0) ← chainSteps p.lay p.tau p.ep (2 * k) (x.getD (2 * k) 0) s0
        let (v1, c1) ← chainSteps p.lay p.tau p.ep (2 * k + 1) (x.getD (2 * k + 1) 0) s1
        pure (st.1 ++ [v0, v1], st.2 ++ [c0, c1]))
      (ChainInv p tl (2 * k + 2)) := by
  rw [chain_pair_spec]
  obtain ⟨-, hl1, hl2, hv1, hv2, hends, hcaps, tpc, t21, t24, tregs, tframe, tlo1, tlo2⟩ := hinv
  have hsig := ctx.hsigl
  have hl := ctx.hlay
  have htau := ctx.htau
  have hep := ctx.hep
  have tpc' : t.pc = pcOf 486 := by rw [tpc, if_pos (by omega)]
  have tx5 : t.getReg .x5 = 0 := by rw [tregs.get .x5, ctx.x5]
  -- block 484: even
  have hs0 := symRun_sound blk486 codeAt_486 t tpc' (by simp only [blk486.res, rv_simp])
  have hc0 : blk486.res.cycles = 2 := rfl
  rw [hc0] at hs0
  set t1 := blk486.res.toState t with ht1
  have m1 : ∀ z, t1.getMem z = t.getMem z := fun z => by
    rw [ht1, Result.toState_getMem, show blk486.res.st.mem = [] from rfl, memEval_nil]
  have r1 : RegsEq t t1 [.x3] := by
    intro r hr; rw [ht1, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have pc1 : t1.pc = pcOf 488 := by
    simp only [ht1, blk486.res, rv_simp, t21]
    rw [and_one_ofNat _ (by omega), if_neg (by rw [ofNat_bne_ofNat]; simp)]
  -- block 486: the paired prf query
  have hs2 := symRun_sound blk488 codeAt_488 t1 pc1 (by simp only [blk488.res, rv_simp])
  have hc2 : blk488.res.cycles = 5 := rfl
  rw [hc2] at hs2
  set t2 := blk488.res.toState t1 with ht2
  have f2 : Frame t1 t2 (fun x => x = 0x6A0) := by
    apply frame_toState; intro x hx hW
    simp only [blk488.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq, ofNat_eq_iff]
    omega
  have r2 : RegsEq t1 t2 [.x3, .x10, .x11, .x12] := by
    intro r hr; rw [ht2, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have e2 := symRun_ecall blk488 codeAt_488 t1 (by simp only [blk488.res, rv_simp]) rfl
  have x10 : t2.getReg .x10 = BitVec.ofNat 64 0x6A0 := by simp only [ht2, blk488.res, rv_simp]
  have x11 : t2.getReg .x11 = BitVec.ofNat 64 64 := by simp only [ht2, blk488.res, rv_simp]
  have x12 : t2.getReg .x12 = BitVec.ofNat 64 0x140 := by simp only [ht2, blk488.res, rv_simp]
  have x5 : t2.getReg .x5 = 0 := by rw [r2.get .x5, r1.get .x5, tx5]
  have pc2 : t2.pc = pcOf 493 := by simp only [ht2, blk488.res, rv_simp]
  have t121 : t1.getReg .x21 = BitVec.ofNat 64 (2 * k) := by rw [r1.get .x21, t21]
  have m6A0 : t2.getMem (BitVec.ofNat 64 0x6A0) = twWord0 0 p.lay p.tau k := by
    simp only [ht2, blk488.res, rv_simp, t121]
    bvsimp []
    rw [show 2 * k / 2 = k by omega]
    refine (word_of_halves _ (1 + 65536 * p.lay) k (by rw [lo32_replace1, m1, tlo1, ctx.pb0])
      (by rw [hi32_replace1])).trans ?_
    unfold twWord0; congr 1
    rw [Nat.div_eq_of_lt (by omega : p.tau < 2 ^ 32)]; omega
  have ft2 : Frame t t2 (fun x => x = 0x6A0) := fun z hz hW => by rw [f2.getMem hz hW, m1]
  have hq : hashInput t2 = pad64 (prfInput S p.lay p.tau p.ep k) := by
    obtain ⟨hn, hw⟩ := words_prfInput S hS p.lay p.tau p.ep k
    refine hashInput_eq_pad64 t2 _ 0 hn (by rw [x11]) (by norm_num) (by rw [x10]; decide) ?_
    rw [hw, x10, show 8 * (0 + 1) = 1 + 1 + 2 + 4 from rfl]
    rw [readWords_ofNat_add, readWords_ofNat_add, readWords_ofNat_add]
    simp only [Nat.reduceMul, Nat.reduceAdd]
    rw [readWords_ofNat_one, readWords_ofNat_one, m6A0, ft2.getMem (by norm_num) (by norm_num),
      tframe.getMem (by norm_num) (by simp only [chainW]; omega), ctx.pb8,
      ft2.readWords _ _ (by norm_num) (by intro i hi; omega),
      ft2.readWords _ _ (by norm_num) (by intro i hi; omega),
      tframe.readWords _ _ (by norm_num) (by intro i hi; simp only [chainW]; omega),
      tframe.readWords _ _ (by norm_num) (by intro i hi; simp only [chainW]; omega), ctx.pbP, ctx.pbS]
    simp only [twWords_eq, List.cons_append, List.nil_append, List.cons.injEq, and_true, true_and]
    congr 1; omega
  have hb : (pad64 (prfInput S p.lay p.tau p.ep k)).blocks = 1 := by
    simp [pad64, Query.blocks, (words_prfInput S hS p.lay p.tau p.ep k).1]
  refine (Sim.steps hs0 (Sim.steps hs2 (Sim.query_bind (W := 231 + (2 + 231)) e2 x5
    (hashArgs_of x10 x11 x12 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)) (hq.trans (fmt_thInput _ _ _ _ _ _ (by decide)).symm) (fun a => ?_)))).mono
    (by rw [show prfInput S p.lay p.tau p.ep k = thInput (tweak 0 p.lay p.tau k p.ep) S from rfl] at *; rw [blocks_fmt_th _ _ _ _ _ _ (by decide)]
        rw [hb]; norm_num)
    (fun _ _ h => h)
  set t3 := writeHash t2 a with ht3
  have f3 : Frame t2 t3 (fun x => 0x140 ≤ x ∧ x < 0x140 + 32) := frame_writeHash t2 a _ x12 (by norm_num)
  have pc3 : t3.pc = pcOf 494 := by rw [ht3, writeHash_pc, pc2]; apply BitVec.eq_of_toNat_eq; simp
  have g3 : ∀ q, t3.getReg q = t2.getReg q := fun q => by rw [ht3, writeHash_getReg]
  have ft3 : Frame t t3 (fun x => x = 0x6A0 ∨ (0x140 ≤ x ∧ x < 0x140 + 32)) := ft2.trans f3
  have rt3 : RegsEq tl t3 chainRegs := ((tregs.trans r1).trans r2 |>.trans
    (show RegsEq t2 t3 [] from fun q _ => g3 q)).mono (by decide)
  have hA := chain_B x p S tl ctx (2 * k) (by omega) (answerBytes 16 a) (by simp) st hl1 hl2 hv1 hv2 t3
    (hends.frame ft3 (by omega) (by intro i hi; constructor <;> omega))
    (fun hee => (hcaps hee).frame ft3 (by rw [ctx.hsigl]; omega) (by
      intro i hi; rw [ctx.hsigl]; constructor <;> omega))
    pc3 (by rw [g3, r2.get .x21, t121]) (by rw [g3, r2.get .x24, r1.get .x24, t24])
    (by rw [g3, x11])
    (by rw [show 0x140 + 16 * (2 * k % 2) = 0x140 by omega]; exact sec_lo t2 a x12)
    rt3 ((tframe.trans ft3).mono (by intro x hx; simp only [chainW] at hx ⊢; omega))
    (by rw [f3.getMem (by norm_num) (by omega), m6A0, ctx.pb0]; simp only [twWord0, lo32_ofNat]
        apply BitVec.eq_of_toNat_eq; simp; omega)
    (by rw [ft3.getMem (by norm_num) (by omega), tlo2])
  refine Sim.bind hA (fun r t4 h4 => ?_)
  obtain ⟨⟨-, hl14, hl24, hv14, hv24, hends4, hcaps4, tpc4, t421, t424, tregs4, tframe4, tlo14, tlo24⟩,
    x411, sec4⟩ := h4
  -- block 484: odd
  have hs5 := symRun_sound blk486 codeAt_486 t4 (by rw [tpc4, if_pos (by omega)])
    (by simp only [blk486.res, rv_simp])
  have hc5 : blk486.res.cycles = 2 := rfl
  rw [hc5] at hs5
  set t5 := blk486.res.toState t4 with ht5
  have m5 : ∀ z, t5.getMem z = t4.getMem z := fun z => by
    rw [ht5, Result.toState_getMem, show blk486.res.st.mem = [] from rfl, memEval_nil]
  have r5 : RegsEq t4 t5 [.x3] := by
    intro r hr; rw [ht5, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have pc5 : t5.pc = pcOf 494 := by
    simp only [ht5, blk486.res, rv_simp, t421]
    rw [and_one_ofNat _ (by omega), if_pos (by rw [ofNat_bne_ofNat]; simp)]
  have fr5 : Frame t4 t5 (fun _ => False) := fun z _ _ => m5 _
  have hB := chain_B x p S tl ctx (2 * k + 1) (by omega) (hiVal a) (by simp) r hl14 hl24 hv14 hv24 t5
    (hends4.frame fr5 (by omega) (by simp)) (fun hee => (hcaps4 hee).frame fr5 (by rw [ctx.hsigl]; omega)
      (by simp)) pc5 (by rw [r5.get .x21, t421]) (by rw [r5.get .x24, t424]) (by rw [r5.get .x11, x411])
    (by
      rw [show 0x140 + 16 * ((2 * k + 1) % 2) = 0x150 by omega, readWords_ofNat_two, m5, m5,
        sec4 _ (by norm_num) (by norm_num) (by norm_num), sec4 _ (by norm_num) (by norm_num) (by norm_num),
        ← readWords_ofNat_two]
      exact sec_hi t2 a x12)
    ((tregs4.trans r5).mono (by decide))
    ((tframe4.trans fr5).mono (by intro x hx; rcases hx with h | h; exact h; exact h.elim))
    (by rw [m5, tlo14]) (by rw [m5, tlo24])
  exact (Sim.steps hs5 hB).mono (by norm_num) (fun _ _ h => h.1)

/-- **Chains** `i = 0 .. 41` of leaf `ep` (pairs `k = 0 .. 20`). -/
theorem chains_sim (S : List Byte) (hS : S.length = 32) (x : List Nat) (p : LeafPar)
    (tl : MachineState) (ctx : ChainCtx S x p tl) (hpc : tl.pc = pcOf 486)
    (h21 : tl.getReg .x21 = BitVec.ofNat 64 0) (h24 : tl.getReg .x24 = BitVec.ofNat 64 0) :
    Sim image tl (21 * 480) ((List.range (nChains / 2)).foldlM (fun (st : List Val × List Val) k => do
        let (s0, s1) ← prf2 (prfInput S p.lay p.tau p.ep k)
        let (v0, c0) ← chainSteps p.lay p.tau p.ep (2 * k) (x.getD (2 * k) 0) s0
        let (v1, c1) ← chainSteps p.lay p.tau p.ep (2 * k + 1) (x.getD (2 * k + 1) 0) s1
        pure (st.1 ++ [v0, v1], st.2 ++ [c0, c1])) ([], [])) (ChainInv p tl 42) := by
  unfold nChains
  exact Sim.foldlM_range 21 _ ([], []) (fun k => ChainInv p tl (2 * k)) 480
    (fun k hk st t h => by rw [show 2 * (k + 1) = 2 * k + 2 by ring]; exact chain_pair S hS x p tl ctx k hk st t h)
    ⟨by norm_num, rfl, rfl, by simp, by simp, Slots.nil _ _, fun _ => Slots.nil _ _,
      by simpa using hpc, h21, by simpa using h24, RegsEq.refl _ _, Frame.refl _ _, rfl, rfl⟩

end SigGolfCandidate.Radix27Sign



end


section -- SignClone13.TreeLeaf

/-! ### cloned TreeLeaf -/

/-!
# `sign`, tree_build: the leaves (`tb_leaf_loop`, instructions 510 .. 563)

`leaves_sim` : from `tb_leaf_loop` with `EP = 0`, the machine refines `buildLeaves S lay tau h e x`:
leaf `j` in `TA + 16 j`, the captured chain values of leaf `e` at `SIGL + 8 + 16 i`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace SigGolfCandidate.Radix27Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

/-- Parameters of a tree: layer, tree index, height, capture leaf, stage base. -/
structure TreePar where
  lay : Nat
  tau : Nat
  h : Nat
  e : Nat
  sigl : Nat

/-- Facts at the start of tree_build's leaf loop. -/
structure TreeCtx (S : List Byte) (x : List Nat) (p : TreePar) (tt : MachineState) : Prop where
  hlay : p.lay < 7
  htau : p.tau < 2 ^ 30
  hh : p.h ≤ 6
  he : p.e < 2 ^ p.h
  hsigl : p.sigl = 0x900 + 856 * p.lay
  hheight : p.h = height p.lay
  hx : ∀ i, x.getD i 0 < 8
  x5 : tt.getReg .x5 = 0
  x8 : tt.getReg .x8 = BitVec.ofNat 64 p.lay
  x9 : tt.getReg .x9 = BitVec.ofNat 64 p.h
  x13 : tt.getReg .x13 = BitVec.ofNat 64 p.e
  x17 : tt.getReg .x17 = BitVec.ofNat 64 (2 ^ p.h)
  x18 : tt.getReg .x18 = BitVec.ofNat 64 p.sigl
  x19 : tt.getReg .x19 = BitVec.ofNat 64 0x34100
  x30 : tt.getReg .x30 = BitVec.ofNat 64 p.tau
  dig : ∀ i < 42, tt.getMem (BitVec.ofNat 64 (0x780 + 8 * i)) = BitVec.ofNat 64 (x.getD i 0)
  pb0 : lo32 (tt.getMem (BitVec.ofNat 64 0x6A0)) = BitVec.ofNat 32 (1 + 65536 * p.lay)
  pbP : tt.readWords (BitVec.ofNat 64 0x6B0) 2 = [0, 0]
  pbS : tt.readWords (BitVec.ofNat 64 0x6C0) 4 = wordsOf S
  cb0 : lo32 (tt.getMem (BitVec.ofNat 64 0xC0)) = BitVec.ofNat 32 (0x101 + 65536 * p.lay)
  cbP : tt.readWords (BitVec.ofNat 64 0xD0) 4 = [0, 0, 0, 0]
  lb0 : tt.getMem (BitVec.ofNat 64 0x340) = twWord0 2 p.lay p.tau 0
  lbP : tt.readWords (BitVec.ofNat 64 0x350) 2 = [0, 0]
  nbP : tt.readWords (BitVec.ofNat 64 0x1D0) 2 = [0, 0]

/-- Addresses written by the leaf loop. -/
def leavesW (p : TreePar) (a : Nat) : Prop :=
  a = 0x6A0 ∨ a = 0x6A8 ∨ a = 0xC0 ∨ a = 0xC8 ∨ (0xF0 ≤ a ∧ a < 0x110) ∨ (0x140 ≤ a ∧ a < 0x160) ∨ a = 0x348 ∨
    (0x360 ≤ a ∧ a < 0x360 + 672) ∨ (p.sigl + 8 ≤ a ∧ a < p.sigl + 8 + 672) ∨
    (0x34100 ≤ a ∧ a < 0x34100 + 16 * 65)

def leavesRegs : List Reg := [.x1, .x2, .x3, .x10, .x11, .x12, .x20, .x21, .x23, .x24, .x25, .x29]

/-- Invariant after `j` leaves. -/
def TLeafInv (p : TreePar) (tt : MachineState) (j : Nat) (st : List Val × List Val) (t : MachineState) :
    Prop :=
  j ≤ 2 ^ p.h ∧ st.1.length = j ∧ (∀ v ∈ st.1, v.length = 16) ∧ Slots t 0x34100 st.1 ∧
  (p.e < j → st.2.length = 42 ∧ (∀ v ∈ st.2, v.length = 16) ∧ Slots t (p.sigl + 8) st.2) ∧
  t.pc = (if j < 2 ^ p.h then pcOf 479 else pcOf 548) ∧ t.getReg .x20 = BitVec.ofNat 64 j ∧
  RegsEq tt t leavesRegs ∧ Frame tt t (leavesW p) ∧
  lo32 (t.getMem (BitVec.ofNat 64 0x6A0)) = lo32 (tt.getMem (BitVec.ofNat 64 0x6A0)) ∧
  lo32 (t.getMem (BitVec.ofNat 64 0xC0)) = lo32 (tt.getMem (BitVec.ofNat 64 0xC0))

theorem buildLeaf_bind {β : Type} (S : List Byte) (lay tau e : Nat) (x : List Nat)
    (g : Val × List Val → OracleComp HashSpec β) :
    buildLeaf S lay tau e x >>= g =
      (List.range (nChains / 2)).foldlM (fun (st : List Val × List Val) k => do
        let (s0, s1) ← prf2 (prfInput S lay tau e k)
        let (v0, c0) ← chainSteps lay tau e (2 * k) (x.getD (2 * k) 0) s0
        let (v1, c1) ← chainSteps lay tau e (2 * k + 1) (x.getD (2 * k + 1) 0) s1
        pure (st.1 ++ [v0, v1], st.2 ++ [c0, c1])) ([], []) >>= fun st =>
          hash16 (leafInput lay tau e st.1) >>= fun leaf => g (leaf, st.2) := by
  simp only [buildLeaf, bind_assoc, pure_bind]

theorem pow_le32 (h : Nat) (hh : h ≤ 6) : 2 ^ h ≤ 64 :=
  calc 2 ^ h ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) hh
    _ = 64 := by norm_num

theorem tleaf_body (S : List Byte) (hS : S.length = 32) (x : List Nat) (p : TreePar)
    (tt : MachineState) (ctx : TreeCtx S x p tt) (j : Nat) (hj : j < 2 ^ p.h)
    (st : List Val × List Val) (t : MachineState) (hinv : TLeafInv p tt j st t) :
    Sim image t (7 + (21 * 480 + (4 + (88 + 2))))
      (do
        let (leaf, c) ← buildLeaf S p.lay p.tau j x
        pure (st.1 ++ [leaf], if j = p.e then c else st.2))
      (TLeafInv p tt (j + 1)) := by
  obtain ⟨-, hl1, hv1, hsl, hcap, tpc, t20, tregs, tframe, tlo1, tlo2⟩ := hinv
  have hsig := ctx.hsigl
  have hl := ctx.hlay
  have htau := ctx.htau
  have h32 := pow_le32 p.h ctx.hh
  have he := ctx.he
  have tpc' : t.pc = pcOf 479 := by rw [tpc, if_pos hj]
  have tx30 : t.getReg .x30 = BitVec.ofNat 64 p.tau := by rw [tregs.get .x30, ctx.x30]
  -- block 510: leaf tweak words
  have hs1 := symRun_sound blk479 codeAt_479 t tpc' (by simp only [blk479.res, rv_simp])
  have hc1 : blk479.res.cycles = 7 := rfl
  rw [hc1] at hs1
  set tl := blk479.res.toState t with htl
  have f1 : Frame t tl (fun x => x = 0x6A8 ∨ x = 0xC8 ∨ x = 0x348) := by
    apply frame_toState; intro x hx hW
    simp only [blk479.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq, ofNat_eq_iff]
    omega
  have r1 : RegsEq t tl [.x3, .x21, .x24] := by
    intro r hr; rw [htl, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have hw : ∀ a, a = 0x6A8 ∨ a = 0xC8 ∨ a = 0x348 →
      tl.getMem (BitVec.ofNat 64 a) = BitVec.ofNat 64 (p.tau + 2 ^ 32 * j) := by
    intro a ha
    simp only [htl, blk479.res, rv_simp]
    bvsimp [t20, tx30, ofNat_eq_iff]
    rw [ofNat_or_disjoint (j * 4294967296) p.tau 32 (by omega) (by omega) (by omega)]
    rcases ha with rfl | rfl | rfl <;> simp (disch := bvomega) only [if_pos, if_neg, if_true] <;>
      (congr 1; ring)
  have ft1 : Frame tt tl (leavesW p) := (tframe.trans f1).mono (by
    intro x hx; simp only [leavesW] at hx ⊢; omega)
  have rt1 : RegsEq tt tl leavesRegs := (tregs.trans r1).mono (by decide)
  have cctx : ChainCtx S x ⟨p.lay, p.tau, p.e, j, p.sigl⟩ tl := by
    refine ⟨hl, htau, show p.e < 64 by omega, show j < 64 by omega, hsig, ctx.hx, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [rt1.get .x5, ctx.x5]
    · rw [rt1.get .x13, ctx.x13]
    · rw [rt1.get .x18, ctx.x18]
    · simp only [htl, blk479.res, rv_simp, t20]
    · intro i hi
      rw [ft1.getMem (by omega) (by simp only [leavesW]; omega), ctx.dig i hi]
    · rw [f1.getMem (by norm_num) (by omega), tlo1, ctx.pb0]
    · exact hw _ (Or.inl rfl)
    · rw [ft1.readWords _ _ (by norm_num) (by intro i hi; simp only [leavesW]; omega), ctx.pbP]
    · rw [ft1.readWords _ _ (by norm_num) (by intro i hi; simp only [leavesW]; omega), ctx.pbS]
    · rw [f1.getMem (by norm_num) (by omega), tlo2, ctx.cb0]
    · exact hw _ (Or.inr (Or.inl rfl))
    · rw [ft1.readWords _ _ (by norm_num) (by intro i hi; simp only [leavesW]; omega), ctx.cbP]
  rw [buildLeaf_bind]
  refine Sim.steps hs1 (Sim.bind (chains_sim S hS x ⟨p.lay, p.tau, p.e, j, p.sigl⟩ tl cctx
    (by simp only [htl, blk479.res, rv_simp]) (by simp only [htl, blk479.res, rv_simp])
    (by simp only [htl, blk479.res, rv_simp])) (fun cs t2 h2 => ?_))
  obtain ⟨-, hc1', hc2', hcv1, hcv2, hends, hcaps, pc2, -, -, cregs, cframe, clo1, clo2⟩ := h2
  have pc2' : t2.pc = pcOf 541 := by rw [pc2]; rfl
  have hcaps' : j = p.e → Slots t2 (p.sigl + 8) cs.2 := hcaps
  have rt2 : RegsEq tt t2 (leavesRegs ++ chainRegs) := rt1.trans cregs
  have x220 : t2.getReg .x20 = BitVec.ofNat 64 j := by
    rw [cregs.get .x20]; simp only [htl, blk479.res, rv_simp, t20]
  have x219 : t2.getReg .x19 = BitVec.ofNat 64 0x34100 := by rw [rt2.get .x19, ctx.x19]
  -- block 557: leaf hash
  have hs3 := symRun_sound blk541 codeAt_541 t2 pc2' (by simp only [blk541.res, rv_simp])
  have hc3 : blk541.res.cycles = 4 := rfl
  rw [hc3] at hs3
  set t3 := blk541.res.toState t2 with ht3
  have f3 : Frame t2 t3 (fun _ => False) := by
    apply frame_toState; intro x hx hW; simp [blk541.res]
  have r3 : RegsEq t2 t3 [.x3, .x10, .x11, .x12] := by
    intro r hr; rw [ht3, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have e3 := symRun_ecall blk541 codeAt_541 t2 (by simp only [blk541.res, rv_simp]) rfl
  have x10 : t3.getReg .x10 = BitVec.ofNat 64 0x340 := by simp only [ht3, blk541.res, rv_simp]
  have x11 : t3.getReg .x11 = BitVec.ofNat 64 704 := by simp only [ht3, blk541.res, rv_simp]
  have x12 : t3.getReg .x12 = BitVec.ofNat 64 (0x34100 + 16 * j) := by
    simp only [ht3, blk541.res, rv_simp]; bvsimp [x220, x219]; congr 1; ring
  have x5 : t3.getReg .x5 = 0 := by rw [r3.get .x5, rt2.get .x5, ctx.x5]
  have pc3 : t3.pc = pcOf 545 := by simp only [ht3, blk541.res, rv_simp]
  have fl3 : Frame tl t3 (chainW ⟨p.lay, p.tau, p.e, j, p.sigl⟩) := (cframe.trans f3).mono (by
    intro x hx; rcases hx with h | h; exact h; exact h.elim)
  have hq : hashInput t3 = pad64 (leafInput p.lay p.tau j cs.1) := by
    obtain ⟨hn, hw'⟩ := words_thVals 2 p.lay p.tau 0 j cs.1 hcv1 10 (by rw [hc1'])
    refine hashInput_eq_pad64 t3 _ 10 hn (by rw [x11]) (by norm_num) (by rw [x10]; decide) ?_
    rw [leafInput, hw', x10, show 8 * (10 + 1) = 1 + 1 + 2 + 2 * 42 from rfl]
    rw [readWords_ofNat_add, readWords_ofNat_add, readWords_ofNat_add]
    simp only [Nat.reduceMul, Nat.reduceAdd]
    rw [readWords_ofNat_one, readWords_ofNat_one,
      fl3.getMem (by norm_num) (by dsimp only [chainW, LeafPar.e, LeafPar.ep, LeafPar.sigl]; omega),
      f1.getMem (by norm_num) (by omega), tframe.getMem (by norm_num) (by simp only [leavesW]; omega),
      ctx.lb0, fl3.getMem (by norm_num) (by dsimp only [chainW, LeafPar.e, LeafPar.ep, LeafPar.sigl]; omega), hw _ (Or.inr (Or.inr rfl)),
      fl3.readWords _ _ (by norm_num) (by intro i hi; dsimp only [chainW, LeafPar.e, LeafPar.ep, LeafPar.sigl]; omega),
      ft1.readWords _ _ (by norm_num) (by intro i hi; simp only [leavesW]; omega), ctx.lbP,
      show (84 : Nat) = 2 * cs.1.length by rw [hc1'], f3.readWords _ _ (by rw [hc1']; norm_num) (by simp),
      readWords_slots t2 0x360 cs.1 hends]
    simp only [twWords_eq, twWord0, List.cons_append, List.nil_append, List.cons.injEq, true_and]
    refine ⟨?_, trivial⟩
    congr 1
    rw [Nat.mod_eq_of_lt (by omega : p.tau < 2 ^ 32), Nat.mod_eq_of_lt (by omega : j < 2 ^ 32)]
  have hb : (pad64 (leafInput p.lay p.tau j cs.1)).blocks = 11 :=
    congrArg (· + 1) (words_thVals 2 p.lay p.tau 0 j cs.1 hcv1 10 (by rw [hc1'])).1
  refine (Sim.steps hs3 (Sim.hash16_bind (W := 2) e3 x5
    (hashArgs_of x10 x11 x12 (by norm_num) (by norm_num) (by norm_num) (by omega) (by omega)
      (by norm_num)) hq (fmt_thInput _ _ _ _ _ _ (by decide)) (fun a => ?_))).mono (by rw [hb]) (fun _ _ h => h)
  set t4 := writeHash t3 a with ht4
  have f4 : Frame t3 t4 (fun x => 0x34100 + 16 * j ≤ x ∧ x < 0x34100 + 16 * j + 32) :=
    frame_writeHash t3 a _ x12 (by omega)
  have v4 : t4.readWords (BitVec.ofNat 64 (0x34100 + 16 * j)) 2 = wordsOf (answerBytes 16 a) :=
    writeHash_readWords_val t3 a _ x12 (by omega)
  have pc4 : t4.pc = pcOf 546 := by rw [ht4, writeHash_pc, pc3]; apply BitVec.eq_of_toNat_eq; simp
  have hs5 := symRun_sound blk546 codeAt_546 t4 pc4 (by simp only [blk546.res, rv_simp])
  have hc5 : blk546.res.cycles = 2 := rfl
  rw [hc5] at hs5
  set t5 := blk546.res.toState t4 with ht5
  have f5 : Frame t4 t5 (fun _ => False) := by
    apply frame_toState; intro x hx hW; simp [blk546.res]
  have r5 : RegsEq t4 t5 [.x20] := by
    intro r hr; rw [ht5, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have x420 : t4.getReg .x20 = BitVec.ofNat 64 j := by rw [ht4, writeHash_getReg, r3.get .x20, x220]
  have x417 : t4.getReg .x17 = BitVec.ofNat 64 (2 ^ p.h) := by
    rw [ht4, writeHash_getReg, r3.get .x17, rt2.get .x17, ctx.x17]
  have ftot : Frame t t5 (fun x => (x = 0x6A8 ∨ x = 0xC8 ∨ x = 0x348) ∨
      chainW ⟨p.lay, p.tau, p.e, j, p.sigl⟩ x ∨ (0x34100 + 16 * j ≤ x ∧ x < 0x34100 + 16 * j + 32)) :=
    (f1.trans (fl3.trans f4)).trans f5 |>.mono (by
      intro x hx; rcases hx with (h | h | h) | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
      · exact h.elim)
  refine Sim.pure_steps hs5 ⟨by omega, by simp [hl1], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv; rcases List.mem_append.mp hv with hv | hv
    · exact hv1 v hv
    · simp at hv; subst hv; simp
  · apply Slots.snoc
    · exact hsl.frame ftot (by omega) (by
        intro i hi; dsimp only [chainW, LeafPar.e, LeafPar.ep, LeafPar.sigl]; constructor <;> omega)
    · rw [hl1, f5.readWords _ _ (by omega) (by simp), v4]
  · intro hej
    by_cases hje : j = p.e
    · rw [if_pos hje]
      refine ⟨hc2', hcv2, ?_⟩
      exact (hcaps' hje).frame ((f4.trans f5).mono (fun x hx => hx)) (by omega) (by
        intro i hi; rw [hc2'] at hi; constructor <;> (try simp only [or_false]) <;> omega)
    · rw [if_neg hje]
      obtain ⟨c1, c2, c3⟩ := hcap (by omega)
      refine ⟨c1, c2, c3.frame ftot (by omega) ?_⟩
      intro i hi; rw [c1] at hi; dsimp only [chainW, LeafPar.e, LeafPar.ep, LeafPar.sigl]; constructor <;> omega
  · simp only [ht5, blk546.res, rv_simp, x420, x417, ofNat_add_ofNat, ofNat_bne_ofNat]
    by_cases h : j + 1 < 2 ^ p.h
    · rw [if_pos h, if_pos (by rw [bne_cond _ _ (by omega) (by omega)]; omega)]
    · rw [if_neg h, if_neg (by rw [bne_cond _ _ (by omega) (by omega)]; omega)]
  · simp only [ht5, blk546.res, rv_simp, x420, ofNat_add_ofNat]
  · exact ((((rt2.trans r3).trans (regsEq_writeHash _ _ [])).trans r5)).mono (by decide)
  · exact (tframe.trans ftot).mono (by intro x hx; simp only [leavesW] at hx ⊢; dsimp only [chainW, LeafPar.e, LeafPar.ep, LeafPar.sigl] at hx; omega)
  · rw [f5.getMem (by norm_num) (by simp), f4.getMem (by norm_num) (by omega),
      f3.getMem (by norm_num) (by simp), clo1, f1.getMem (by norm_num) (by omega), tlo1]
  · rw [f5.getMem (by norm_num) (by simp), f4.getMem (by norm_num) (by omega),
      f3.getMem (by norm_num) (by simp), clo2, f1.getMem (by norm_num) (by omega), tlo2]

end SigGolfCandidate.Radix27Sign

namespace SigGolfCandidate.Radix27Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

/-- Cycle bound of one leaf. -/
def tleafCyc : Nat := 7 + (21 * 480 + (4 + (88 + 2)))

/-- **Leaves** `0 .. 2^h - 1` of a tree (with capture of leaf `e`). -/
theorem leaves_sim (S : List Byte) (hS : S.length = 32) (x : List Nat) (p : TreePar)
    (tt : MachineState) (ctx : TreeCtx S x p tt) (hpc : tt.pc = pcOf 479)
    (h20 : tt.getReg .x20 = BitVec.ofNat 64 0) :
    Sim image tt (2 ^ p.h * tleafCyc) (buildLeaves S p.lay p.tau p.h p.e x) (TLeafInv p tt (2 ^ p.h)) := by
  unfold buildLeaves
  exact Sim.foldlM_range (2 ^ p.h) _ ([], []) (TLeafInv p tt) tleafCyc
    (fun j hj st t h => by unfold tleafCyc; exact tleaf_body S hS x p tt ctx j hj st t h)
    ⟨Nat.zero_le _, rfl, by simp, Slots.nil _ _, fun h => absurd h (by omega),
      by rw [hpc, if_pos (Nat.two_pow_pos _)], h20, RegsEq.refl _ _,
      Frame.refl _ _, rfl, rfl⟩

end SigGolfCandidate.Radix27Sign



end


section -- SignClone13.TreeLevel

/-! ### cloned TreeLevel -/

/-!
# `sign`, tree_build: the levels (`tb_level_loop`, instructions 565 .. 603)

`tlevels_sim` : from `tb_level_loop` with `LAM = 1`, `NCNT = 2^h` and the leaves in `TA`, the
machine refines the level fold of `buildLevels (nodeInput lay tau) e h leaves`; the path node of
level `l` is staged at `SIGL + 680 + 16 l`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace SigGolfCandidate.Radix27Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

theorem seg566_eq : seg566 = nodeSegA := rfl
theorem seg583_eq : seg583 = nodeSegB := rfl

theorem codeAt_node566 : CodeAt image (pcOf 566) nodeSegA := seg566_eq ▸ codeAt_566
theorem codeAt_node583 : CodeAt image (pcOf (566 + 17)) nodeSegB := seg583_eq ▸ codeAt_583

/-- Facts at the start of the tree level loop. -/
structure TLevCtx (p : TreePar) (t0 : MachineState) : Prop where
  hlay : p.lay < 7
  htau : p.tau < 2 ^ 30
  hh : 1 ≤ p.h ∧ p.h ≤ 6
  he : p.e < 2 ^ p.h
  hsigl : p.sigl = 0x900 + 856 * p.lay
  hheight : p.h = height p.lay
  x5 : t0.getReg .x5 = 0
  x8 : t0.getReg .x8 = BitVec.ofNat 64 p.lay
  x9 : t0.getReg .x9 = BitVec.ofNat 64 p.h
  x13 : t0.getReg .x13 = BitVec.ofNat 64 p.e
  x18 : t0.getReg .x18 = BitVec.ofNat 64 p.sigl
  x19 : t0.getReg .x19 = BitVec.ofNat 64 0x34100
  x30 : t0.getReg .x30 = BitVec.ofNat 64 p.tau
  nbP : t0.readWords (BitVec.ofNat 64 0x1D0) 2 = [0, 0]

def tlevW (p : TreePar) (a : Nat) : Prop :=
  a = 0x1C0 ∨ a = 0x1C8 ∨ (0x1E0 ≤ a ∧ a < 0x200) ∨ (0x34100 ≤ a ∧ a < 0x34100 + 16 * 65) ∨
    (p.sigl + 680 ≤ a ∧ a < p.sigl + 856)

def tlevRegs : List Reg := [.x1, .x2, .x3, .x10, .x11, .x12, .x15, .x16, .x17, .x29]

/-- Invariant after `j` levels. -/
def TLevInv (p : TreePar) (t0 : MachineState) (j : Nat) (st : List Val × List Val) (t : MachineState) :
    Prop :=
  j ≤ p.h ∧ st.1.length = 2 ^ (p.h - j) ∧ (∀ v ∈ st.1, v.length = 16) ∧ Slots t 0x34100 st.1 ∧
  st.2.length = j ∧ (∀ v ∈ st.2, v.length = 16) ∧ Slots t (p.sigl + 680) st.2 ∧
  t.pc = (if j < p.h then pcOf 549 else pcOf 587) ∧ t.getReg .x15 = BitVec.ofNat 64 (j + 1) ∧
  t.getReg .x17 = BitVec.ofNat 64 (2 ^ (p.h - j)) ∧
  RegsEq t0 t tlevRegs ∧ Frame t0 t (tlevW p)

theorem tlev_path_ne (sigl lay i j m : Nat) (hsig : sigl = 0x900 + 856 * lay) (hl : lay < 7)
    (hij : i < j) (hj : j < 6) (hm : m ≤ 32) :
    ((¬sigl + 680 + 16 * i = 448 ∧ ¬sigl + 680 + 16 * i = 456 ∧
        ¬sigl + 680 + 16 * i = sigl + 680 + 16 * j ∧ ¬sigl + 680 + 16 * i = sigl + 680 + 16 * j + 8) ∧
      ¬(213248 ≤ sigl + 680 + 16 * i ∧ sigl + 680 + 16 * i < 213248 + 32 * m) ∧
        ¬sigl + 680 + 16 * i = 456 ∧ ¬sigl + 680 + 16 * i = 480 ∧
          ¬sigl + 680 + 16 * i = 488 ∧ ¬sigl + 680 + 16 * i = 496 ∧ ¬sigl + 680 + 16 * i = 504) ∧
    ((¬sigl + 680 + 16 * i + 8 = 448 ∧ ¬sigl + 680 + 16 * i + 8 = 456 ∧
        ¬sigl + 680 + 16 * i + 8 = sigl + 680 + 16 * j ∧
          ¬sigl + 680 + 16 * i + 8 = sigl + 680 + 16 * j + 8) ∧
      ¬(213248 ≤ sigl + 680 + 16 * i + 8 ∧ sigl + 680 + 16 * i + 8 < 213248 + 32 * m) ∧
        ¬sigl + 680 + 16 * i + 8 = 456 ∧ ¬sigl + 680 + 16 * i + 8 = 480 ∧
          ¬sigl + 680 + 16 * i + 8 = 488 ∧ ¬sigl + 680 + 16 * i + 8 = 496 ∧
            ¬sigl + 680 + 16 * i + 8 = 504) := by
  subst hsig; omega

theorem tlevel_body (p : TreePar) (t0 : MachineState) (ctx : TLevCtx p t0) (j : Nat) (hj : j < p.h)
    (st : List Val × List Val) (t : MachineState) (hinv : TLevInv p t0 j st t) :
    Sim image t (17 + (2 ^ (p.h - 1 - j) * 26 + 2))
      (levelStep (nodeInput p.lay p.tau) p.e st (1 + j)) (TLevInv p t0 (j + 1)) := by
  obtain ⟨-, hlen, hvals, hslots, hplen, hpvals, hpath, tpc, t15, t17, tregs, tframe⟩ := hinv
  have hsig := ctx.hsigl
  have hl := ctx.hlay
  have htau := ctx.htau
  have hh := ctx.hh
  have he := ctx.he
  have tpc' : t.pc = pcOf 549 := by rw [tpc, if_pos hj]
  have tx5 : t.getReg .x5 = 0 := by rw [tregs.get .x5, ctx.x5]
  have tx8 : t.getReg .x8 = BitVec.ofNat 64 p.lay := by rw [tregs.get .x8, ctx.x8]
  have tx9 : t.getReg .x9 = BitVec.ofNat 64 p.h := by rw [tregs.get .x9, ctx.x9]
  have tx13 : t.getReg .x13 = BitVec.ofNat 64 p.e := by rw [tregs.get .x13, ctx.x13]
  have tx18 : t.getReg .x18 = BitVec.ofNat 64 p.sigl := by rw [tregs.get .x18, ctx.x18]
  have tx19 : t.getReg .x19 = BitVec.ofNat 64 0x34100 := by rw [tregs.get .x19, ctx.x19]
  have tx30 : t.getReg .x30 = BitVec.ofNat 64 p.tau := by rw [tregs.get .x30, ctx.x30]
  have hpow : 2 ^ (p.h - j) = 2 * 2 ^ (p.h - 1 - j) := by
    rw [show p.h - j = p.h - 1 - j + 1 by omega, Nat.pow_succ]; ring
  have hp32 : 2 ^ (p.h - j) ≤ 64 := pow_le32 _ (by omega)
  set sib := (p.e / 2 ^ j) ^^^ 1 with hsib
  have hsib_lt : sib < 2 ^ (p.h - j) := by
    apply xor1_lt _ _ _ (by omega)
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← Nat.pow_add, show p.h - j + j = p.h by omega]
    exact he
  have hudiv : p.e / 2 ^ j ≤ p.e := Nat.div_le_self _ _
  have he32 : p.e < 64 := lt_of_lt_of_le he (pow_le32 _ hh.2)
  -- block 565: capture sibling, node tweak
  have hs1 := symRun_sound blk549 codeAt_549 t tpc' (by
    simp only [blk549.res, rv_simp]
    bvsimp [t15, tx13, tx18, tx19, accessValid_ofNat, ne_eq, ofNat_eq_iff]
    rw [← hsib]; omega)
  have hc1 : blk549.res.cycles = 17 := rfl
  rw [hc1] at hs1
  set t1 := blk549.res.toState t with ht1
  have f1 : Frame t t1 (fun x => x = 0x1C0 ∨ x = 0x1C8 ∨ x = p.sigl + 680 + 16 * j ∨
      x = p.sigl + 680 + 16 * j + 8) := by
    apply frame_toState; intro x hx hW
    simp only [blk549.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq]
    bvsimp [t15, tx18, ofNat_eq_iff]
    omega
  have r1 : RegsEq t t1 [.x1, .x2, .x3, .x16, .x17, .x29] := by
    intro r hr; rw [ht1, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have pc1 : t1.pc = pcOf 566 := by simp only [ht1, blk549.res, rv_simp]
  have y16 : t1.getReg .x16 = 0 := by simp only [ht1, blk549.res, rv_simp]
  have y17 : t1.getReg .x17 = BitVec.ofNat 64 (2 ^ (p.h - 1 - j)) := by
    simp only [ht1, blk549.res, rv_simp]
    bvsimp [t17]
    congr 1; rw [hpow]; omega
  have y19 : t1.getReg .x19 = BitVec.ofNat 64 0x34100 := by rw [r1.get .x19, tx19]
  have y5 : t1.getReg .x5 = 0 := by rw [r1.get .x5, tx5]
  have w448 : t1.getMem (BitVec.ofNat 64 448) = twWord0 3 p.lay p.tau 0 := by
    simp only [ht1, blk549.res, rv_simp]
    bvsimp [t15, tx8, tx18, ofNat_eq_iff]
    rw [ofNat_or_disjoint (p.lay * 65536) 769 16 (by omega) (by omega) (by omega)]
    unfold twWord0; congr 1
    rw [Nat.div_eq_of_lt (by omega : p.tau < 2 ^ 32), Nat.mod_eq_of_lt (a := p.lay) (by omega)]
    omega
  have w456 : lo32 (t1.getMem (BitVec.ofNat 64 456)) = BitVec.ofNat 32 p.tau := by
    simp only [ht1, blk549.res, rv_simp]
    bvsimp [t15, tx18, tx30, ofNat_eq_iff]
    rw [lo32_replace0]
  have hcap1 : t1.readWords (BitVec.ofNat 64 (p.sigl + 680 + 16 * j)) 2 =
      wordsOf (st.1.getD sib []) := by
    rw [← hslots.getD sib (by omega), readWords_ofNat_two, readWords_ofNat_two]
    simp only [ht1, blk549.res, rv_simp]
    bvsimp [t15, tx13, tx18, tx19, ofNat_eq_iff]
    simp (disch := bvomega) only [if_pos, if_neg]
    have e : (p.e / 2 ^ j ^^^ 1) * 16 = 16 * sib := by rw [hsib, Nat.mul_comm]
    rw [e, Nat.add_comm (16 * sib) 213248]
  -- node loop
  let c : NodeCtx := ⟨3, p.lay, p.tau, 1 + j, 0x34100, 2 ^ (p.h - 1 - j)⟩
  have hnode := nodeLoop_sim codeAt_node566 codeAt_node583 c st.1 (by simp only [c]; rw [hlen, hpow])
    hvals (by simp only [c]; positivity) (by simp only [c]; norm_num) (by simp only [c])
    (by simp only [c]; omega) t1 pc1 y16 y17 y19 y5 (by simp only [c]; omega)
    (fun j' l r hj' hl hr => by
      simp only [c] at hj' ⊢
      show fmt (nodeInput p.lay p.tau (1 + j) j' l r) =
        pad64 (nodeFmt 3 p.lay p.tau 0 (2 ^ (p.h - 1 - j) + j') l r)
      rw [fmt_nodeInput _ _ _ _ _ _ hl hr (by omega) (by omega) (by omega),
        pad64_len64 _ (length_nodeFmt _ _ _ _ _ _ _ hl hr)]
      unfold heapIndex nodeFmt
      rw [← ctx.hheight, show p.h - (1 + j) = p.h - 1 - j by omega])
    w448 w456
    (by rw [f1.getMem (by norm_num) (by omega), tframe.getMem (by norm_num) (by simp only [tlevW]; omega)]
        have := ctx.nbP; rw [readWords_ofNat_two] at this; simp only [List.cons.injEq] at this
        exact this.1)
    (by rw [f1.getMem (by norm_num) (by omega), tframe.getMem (by norm_num) (by simp only [tlevW]; omega)]
        have := ctx.nbP; rw [readWords_ofNat_two] at this; simp only [List.cons.injEq] at this
        exact this.2.1)
    (hslots.frame f1 (by omega) (by intro i hi; constructor <;> ((try simp only); omega)))
  have hstep : levelStep (nodeInput p.lay p.tau) p.e st (1 + j) =
      buildLevel (nodeFmt 3 p.lay p.tau) (1 + j) st.1 >>= fun level =>
        pure (level, st.2 ++ [st.1.getD sib []]) := by
    simp only [levelStep, hsib, show 1 + j - 1 = j by omega]; rfl
  rw [hstep]
  refine Sim.steps hs1 (Sim.bind hnode (fun acc t2 hn => ?_))
  obtain ⟨-, hacc, haccv, haccs, -, pc2, x216, nregs, nframe⟩ := hn
  have pc2' : t2.pc = pcOf 585 := by rw [pc2, if_neg (lt_irrefl _)]
  have hs3 := symRun_sound blk585 codeAt_585 t2 pc2' (by simp only [blk585.res, rv_simp])
  have hc3 : blk585.res.cycles = 2 := rfl
  rw [hc3] at hs3
  set t3 := blk585.res.toState t2 with ht3
  have r3 : RegsEq t2 t3 [.x15] := by
    intro r hr; rw [ht3, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have f3 : Frame t2 t3 (fun _ => False) := by
    apply frame_toState; intro x hx hW; simp [blk585.res]
  have x215 : t2.getReg .x15 = BitVec.ofNat 64 (j + 1) := by
    rw [nregs.toRegsEq.get .x15, r1.get .x15, t15]
  have x29 : t2.getReg .x9 = BitVec.ofNat 64 p.h := by
    rw [nregs.toRegsEq.get .x9, r1.get .x9, tx9]
  have ft13 : Frame t t3 (fun x => (x = 0x1C0 ∨ x = 0x1C8 ∨ x = p.sigl + 680 + 16 * j ∨
      x = p.sigl + 680 + 16 * j + 8) ∨ ((c.B ≤ x ∧ x < c.B + 32 * c.m) ∨ x = 456 ∨ x = 480 ∨
        x = 488 ∨ x = 496 ∨ x = 504)) := (f1.trans (nframe.toFrame.trans f3)).mono (by
      intro x hx; rcases hx with h | h | h; exact Or.inl h; exact Or.inr h; exact h.elim)
  refine Sim.pure_steps hs3 ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hacc, show p.h - (j + 1) = p.h - 1 - j by omega]
  · exact haccv
  · show Slots t3 0x34100 acc
    have hm32 : acc.length ≤ 64 := by
      rw [hacc]; have := pow_le32 (p.h - 1 - j) (by omega); simp only [c]; omega
    exact (show Slots t2 0x34100 acc from haccs).frame f3 (by omega) (by simp)
  · simp [hplen]
  · intro v hv; rcases List.mem_append.mp hv with hv | hv
    · exact hpvals v hv
    · simp at hv; subst hv
      simp only [List.getElem?_eq_getElem (show sib < st.1.length by omega), Option.getD_some]
      exact hvals _ (List.getElem_mem _)
  · apply Slots.snoc
    · have hb : p.sigl + 680 + 16 * st.2.length + 16 < 2 ^ 64 := by rw [hplen]; omega
      refine hpath.frame ft13 hb ?_
      intro i hi
      have hij : i < j := by rw [hplen] at hi; exact hi
      have hm16 : 2 ^ (p.h - 1 - j) ≤ 32 := by
        have := pow_le32 (p.h - j) (by omega)
        have hp : 2 ^ (p.h - j) = 2 * 2 ^ (p.h - 1 - j) := by
          rw [show p.h - j = p.h - 1 - j + 1 by omega, Nat.pow_succ]; ring
        omega
      simp only [c, not_or]
      generalize 2 ^ (p.h - 1 - j) = m at hm16 ⊢
      exact tlev_path_ne p.sigl p.lay i j m hsig hl hij (by omega) hm16
    · rw [hplen, f3.readWords _ _ (by omega) (by simp),
        nframe.toFrame.readWords _ _ (by omega) (by intro i hi; simp only [c]; omega), hcap1]
  · simp only [ht3, blk585.res, rv_simp, x215, x29, ofNat_add_ofNat]
    rw [ofNat_slt_ofNat _ _ (by omega) (by omega)]
    by_cases h : j + 1 < p.h
    · rw [if_pos h]; simp; omega
    · rw [if_neg h]; simp; omega
  · simp only [ht3, blk585.res, rv_simp, x215, ofNat_add_ofNat]
  · rw [r3.get .x17, nregs.toRegsEq.get .x17, y17, show p.h - (j + 1) = p.h - 1 - j by omega]
  · exact (((tregs.trans r1).trans nregs.toRegsEq).trans r3).mono (by decide)
  · exact (tframe.trans ft13).mono (by
      intro x hx; simp only [tlevW, c] at hx ⊢; omega)

end SigGolfCandidate.Radix27Sign

namespace SigGolfCandidate.Radix27Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

/-- **Tree levels** `1 .. h` (with capture of the path of leaf `e`). -/
theorem tlevels_sim (p : TreePar) (t0 : MachineState) (ctx : TLevCtx p t0) (leaves : List Val)
    (hlen : leaves.length = 2 ^ p.h) (hvals : ∀ v ∈ leaves, v.length = 16)
    (hslots : Slots t0 0x34100 leaves) (hpc : t0.pc = pcOf 549) (h15 : t0.getReg .x15 = BitVec.ofNat 64 1)
    (h17 : t0.getReg .x17 = BitVec.ofNat 64 (2 ^ p.h)) :
    Sim image t0 (p.h * 853) ((List.range' 1 p.h).foldlM (levelStep (nodeInput p.lay p.tau) p.e)
      (leaves, [])) (TLevInv p t0 p.h) := by
  have hh := ctx.hh
  apply Sim.foldlM_range' 1 p.h _ _ (TLevInv p t0) 853
  · intro j hj st t h
    refine (tlevel_body p t0 ctx j hj st t h).mono ?_ (fun _ _ h => h)
    have : 2 ^ (p.h - 1 - j) ≤ 32 := by
      have := pow_le32 (p.h - j) (by omega)
      have hp : 2 ^ (p.h - j) = 2 * 2 ^ (p.h - 1 - j) := by
        rw [show p.h - j = p.h - 1 - j + 1 by omega, Nat.pow_succ]; ring
      omega
    omega
  · exact ⟨Nat.zero_le _, by simpa using hlen, hvals, hslots, rfl, by simp, Slots.nil _ _,
      by rw [hpc, if_pos (by omega)], h15, by simpa using h17, RegsEq.refl _ _, Frame.refl _ _⟩

end SigGolfCandidate.Radix27Sign



end


section -- SignClone13.Tree

/-! ### cloned Tree -/

/-!
# `sign`, tree_build as a whole (instructions 510 .. 603)

`tree_sim` : from `tb_leaf_loop` (`EP = 0`) the machine refines `buildTree S lay tau h e x`: the
root in `TA[0]`, the captured chain values at `SIGL + 8`, the path at `SIGL + 680`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace SigGolfCandidate.Radix27Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

def treeW (p : TreePar) (a : Nat) : Prop := leavesW p a ∨ tlevW p a

def treeRegs : List Reg := leavesRegs ++ [.x15] ++ tlevRegs

/-- Result of tree_build. -/
def TreePost (p : TreePar) (tt : MachineState) (r : Val × List Val × List Val) (t : MachineState) :
    Prop :=
  t.pc = pcOf 587 ∧ r.1.length = 16 ∧ Slots t 0x34100 [r.1] ∧
  r.2.1.length = 42 ∧ (∀ v ∈ r.2.1, v.length = 16) ∧ Slots t (p.sigl + 8) r.2.1 ∧
  r.2.2.length = p.h ∧ (∀ v ∈ r.2.2, v.length = 16) ∧ Slots t (p.sigl + 680) r.2.2 ∧
  RegsEq tt t treeRegs ∧ Frame tt t (treeW p)

theorem buildTree_eq (S : List Byte) (lay tau h e : Nat) (x : List Nat) :
    buildTree S lay tau h e x =
      buildLeaves S lay tau h e x >>= fun q =>
        (List.range' 1 h).foldlM (levelStep (nodeInput lay tau) e) (q.1, []) >>= fun st =>
          pure (st.1.getD 0 [], q.2, st.2) := by
  simp only [buildTree, buildLevels, bind_assoc, pure_bind]

/-- Cycle bound of tree_build. -/
def treeCyc : Nat := 64 * tleafCyc + (1 + 6 * 853)

theorem tree_sim (S : List Byte) (hS : S.length = 32) (x : List Nat) (p : TreePar)
    (tt : MachineState) (ctx : TreeCtx S x p tt) (h1 : 1 ≤ p.h) (hpc : tt.pc = pcOf 479)
    (h20 : tt.getReg .x20 = BitVec.ofNat 64 0) :
    Sim image tt treeCyc (buildTree S p.lay p.tau p.h p.e x) (TreePost p tt) := by
  have hh := ctx.hh
  have h32 := pow_le32 p.h hh
  have hsig := ctx.hsigl
  have hlay := ctx.hlay
  rw [buildTree_eq]
  have hW : 2 ^ p.h * tleafCyc + (1 + p.h * 853) ≤ treeCyc := by
    unfold treeCyc
    have := Nat.mul_le_mul_right tleafCyc h32
    have := Nat.mul_le_mul_right 853 hh
    omega
  refine (Sim.bind (leaves_sim S hS x p tt ctx hpc h20) (fun q t2 h2 => ?_)).mono hW
    (fun _ _ h => h)
  obtain ⟨-, hlv, hlvv, hlvs, hcap, pc2, -, lregs, lframe, -, -⟩ := h2
  obtain ⟨hc1, hc2, hc3⟩ := hcap ctx.he
  have pc2' : t2.pc = pcOf 548 := by rw [pc2, if_neg (lt_irrefl _)]
  have hs3 := symRun_sound blk548 codeAt_548 t2 pc2' (by simp only [blk548.res, rv_simp])
  have hc67 : blk548.res.cycles = 1 := rfl
  rw [hc67] at hs3
  set t3 := blk548.res.toState t2 with ht3
  have f3 : Frame t2 t3 (fun _ => False) := by
    apply frame_toState; intro x hx hW; simp [blk548.res]
  have r3 : RegsEq t2 t3 [.x15] := by
    intro r hr; rw [ht3, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have rt3 : RegsEq tt t3 (leavesRegs ++ [.x15]) := lregs.trans r3
  have ft3 : Frame tt t3 (leavesW p) := (lframe.trans f3).mono (by
    intro x hx; rcases hx with h | h; exact h; exact h.elim)
  have vctx : TLevCtx p t3 := by
    refine ⟨ctx.hlay, ctx.htau, ⟨h1, hh⟩, ctx.he, ctx.hsigl, ctx.hheight, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [rt3.get .x5, ctx.x5]
    · rw [rt3.get .x8, ctx.x8]
    · rw [rt3.get .x9, ctx.x9]
    · rw [rt3.get .x13, ctx.x13]
    · rw [rt3.get .x18, ctx.x18]
    · rw [rt3.get .x19, ctx.x19]
    · rw [rt3.get .x30, ctx.x30]
    · have := ctx.hsigl
      rw [ft3.readWords _ _ (by norm_num) (by intro i hi; simp only [leavesW]; omega), ctx.nbP]
  refine (Sim.steps hs3 (Sim.bind (W₂ := 0) (tlevels_sim p t3 vctx q.1 hlv hlvv
    (hlvs.frame f3 (by omega) (by simp)) (by simp only [ht3, blk548.res, rv_simp])
    (by simp only [ht3, blk548.res, rv_simp]) (by rw [rt3.get .x17, ctx.x17]))
    (fun st t4 h4 => ?_))).mono (by omega) (fun _ _ h => h)
  obtain ⟨-, hl4, hv4, hs4, hp4, hpv4, hps4, pc4, -, -, vregs, vframe⟩ := h4
  refine Sim.pure ⟨by rw [pc4, if_neg (lt_irrefl _)], ?_, ?_, hc1, hc2, ?_, hp4, hpv4, hps4, ?_, ?_⟩
  · rw [getD_of_lt (by rw [hl4]; simp)]; exact hv4 _ (List.getElem_mem _)
  · intro i hi
    simp at hi; subst hi
    have := hs4.getD 0 (by rw [hl4]; simp)
    simpa using this
  · refine hc3.frame (f3.trans vframe) (by rw [hc1]; omega) ?_
    intro i hi; rw [hc1] at hi
    have := ctx.hsigl; have := ctx.hlay
    constructor <;> (simp only [tlevW, or_false, false_or]; omega)
  · exact (rt3.trans vregs).mono (by decide)
  · exact (ft3.trans (f3.trans vframe)).mono (by
      intro x hx; simp only [treeW]; rcases hx with h | h | h
      · exact Or.inl h
      · exact h.elim
      · exact Or.inr h)

end SigGolfCandidate.Radix27Sign



end


section -- SignClone13.Layer

/-! ### cloned Layer -/

/-!
# `sign`, the hypertree layers (`layer_loop`, instructions 205 .. 613)

`layers_sim` : from `layer_loop` with `KAP = n - 1` and the message `M` at `EB + 32`, the machine
refines `signLayers S idx n M`; layer `l`'s counter, chain values and path are staged at
`STG + 760 l` (counter dword, `+8`: 42 values, `+680`: path).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace SigGolfCandidate.Radix27Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

/-- Buffers that stay constant during the layer phase (P slots, `S`). -/
structure Statics (S : List Byte) (t : MachineState) : Prop where
  ebP : t.readWords (BitVec.ofNat 64 0x110) 2 = [0, 0]
  pbP : t.readWords (BitVec.ofNat 64 0x6B0) 2 = [0, 0]
  pbS : t.readWords (BitVec.ofNat 64 0x6C0) 4 = wordsOf S
  cbP : t.readWords (BitVec.ofNat 64 0xD0) 2 = [0, 0]
  lbP : t.readWords (BitVec.ofNat 64 0x350) 2 = [0, 0]
  nbP : t.readWords (BitVec.ofNat 64 0x1D0) 2 = [0, 0]

/-- Addresses of the static buffers. -/
def staticA (a : Nat) : Prop :=
  (0x110 ≤ a ∧ a < 0x120) ∨ (0x6B0 ≤ a ∧ a < 0x6E0) ∨ (0xD0 ≤ a ∧ a < 0xE0) ∨
    (0x350 ≤ a ∧ a < 0x360) ∨ (0x1D0 ≤ a ∧ a < 0x1E0)

theorem Statics.frame {S : List Byte} {s t : MachineState} {W : Nat → Prop} (h : Statics S s)
    (hf : Frame s t W) (hW : ∀ a, staticA a → ¬ W a) : Statics S t := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hf.readWords _ _ (by norm_num) (fun i hi => hW _ (by simp only [staticA]; omega)), h.ebP]
  · rw [hf.readWords _ _ (by norm_num) (fun i hi => hW _ (by simp only [staticA]; omega)), h.pbP]
  · rw [hf.readWords _ _ (by norm_num) (fun i hi => hW _ (by simp only [staticA]; omega)), h.pbS]
  · rw [hf.readWords _ _ (by norm_num) (fun i hi => hW _ (by simp only [staticA]; omega)), h.cbP]
  · rw [hf.readWords _ _ (by norm_num) (fun i hi => hW _ (by simp only [staticA]; omega)), h.lbP]
  · rw [hf.readWords _ _ (by norm_num) (fun i hi => hW _ (by simp only [staticA]; omega)), h.nbP]

/-- The cache region (masked top-tree nodes), untouched by `sign`. -/
def RegionOk (cache : List Byte) (t : MachineState) : Prop :=
  ∀ l j, l < 11 → j < 2 ^ (11 - l) →
    t.readWords (BitVec.ofNat 64 (0x44A0 + cacheNodeOff l j)) 2 = wordsOf (cacheNode cache l j)

/-- Addresses of the cache region. -/
def regionA (a : Nat) : Prop := 0x44C0 ≤ a ∧ a < 0x144A0

theorem RegionOk.frame {cache : List Byte} {s t : MachineState} {W : Nat → Prop} (h : RegionOk cache s)
    (hf : Frame s t W) (hW : ∀ a, regionA a → ¬ W a) : RegionOk cache t := by
  intro l j hl hj
  have := cacheNodeOff_lt l j hl hj
  have : 32 ≤ cacheNodeOff l j := by unfold cacheNodeOff; omega
  rw [hf.readWords _ _ (by omega) (fun i hi => hW _ (by simp only [regionA]; omega)), h l j hl hj]

/-- The state at `layer_loop` for layer `lay` with message `M`. -/
structure LayHead (S cache : List Byte) (idx lay : Nat) (M : Val) (t : MachineState) : Prop where
  hlay : lay < 5
  hidx : idx < 2 ^ 34
  hM : M.length = 16
  pc : t.pc = pcOf 272
  x5 : t.getReg .x5 = 0
  x7 : t.getReg .x7 = BitVec.ofNat 64 (2 ^ 22)
  x8 : t.getReg .x8 = BitVec.ofNat 64 lay
  x18 : t.getReg .x18 = BitVec.ofNat 64 (0x900 + 856 * lay)
  x22 : t.getReg .x22 = BitVec.ofNat 64 idx
  x26 : t.getReg .x26 = swM1
  x27 : t.getReg .x27 = swM2
  ebM : t.readWords (BitVec.ofNat 64 0x120) 2 = wordsOf M
  st : Statics S t
  region : RegionOk cache t

theorem shiftBelow_eq (lay : Nat) (h : lay < 5) :
    shiftBelow lay = if lay = 0 then 23 else if lay < 4 then 23 - 6 * lay else 0 := by
  interval_cases lay <;> decide

theorem height_eq (lay : Nat) (h : lay < 5) :
    height lay = if lay = 0 then 11 else if lay < 4 then 6 else 5 := by
  interval_cases lay <;> decide

theorem shiftBelow_add (lay : Nat) (h : lay < 5) : 4 ≤ shiftBelow lay + height lay ∧ shiftBelow lay + height lay ≤ 34 ∧
    shiftBelow lay ≤ 23 ∧ 4 ≤ height lay ∧ height lay ≤ 11 := by
  interval_cases lay <;> decide

/-- Route and header state at `enc_loop`. -/
theorem layer_header (S cache : List Byte) (idx lay : Nat) (M : Val) (t : MachineState)
    (hh : LayHead S cache idx lay M t) :
    ∃ k c t4, Steps image t k c t4 ∧ c ≤ 26 ∧ t4.pc = pcOf 302 ∧
      t4.getReg .x6 = BitVec.ofNat 64 0 ∧ t4.getReg .x9 = BitVec.ofNat 64 (height lay) ∧
      t4.getReg .x13 = BitVec.ofNat 64 ((route idx lay).1) ∧
      t4.getReg .x30 = BitVec.ofNat 64 ((route idx lay).2) ∧
      t4.getReg .x31 = BitVec.ofNat 64 ((route idx lay).2 + 2 ^ 32 * (route idx lay).1) ∧
      EncMem lay (route idx lay).2 (route idx lay).1 M t4 ∧
      RegsEq t t4 [.x3, .x6, .x9, .x13, .x28, .x29, .x30, .x31] ∧
      Frame t t4 (fun a => a = 0x100 ∨ a = 0x108 ∨ a = 0x138) := by
  have hl := hh.hlay
  have hidx := hh.hidx
  obtain ⟨hsh1, hsh2, hsb, hhg1, hhg2⟩ := shiftBelow_add lay hl
  -- block 263: test lay < 4
  have hs1 := symRun_sound blk272 codeAt_272 t hh.pc (by simp only [blk272.res, rv_simp])
  have r1 : RegsEq t (blk272.res.toState t) [.x3] := by
    intro r hr; rw [Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have f1 : Frame t (blk272.res.toState t) (fun _ => False) := by
    apply frame_toState; intro x hx hW; simp [blk272.res]
  have x8' : (blk272.res.toState t).getReg .x8 = BitVec.ofNat 64 lay := by rw [r1.get .x8, hh.x8]
  have pc1 : (blk272.res.toState t).pc = if lay < 4 then pcOf 277 else pcOf 274 := by
    simp only [blk272.res, rv_simp, hh.x8]
    rw [show (4#64 : Word) = BitVec.ofNat 64 4 from rfl, ofNat_slt_ofNat _ _ (by omega) (by norm_num)]
    by_cases h : lay < 4
    · rw [if_pos h, if_pos (by simpa using h)]
    · rw [if_neg h, if_neg (by simpa using h)]
  -- the three ways to (s, h)
  obtain ⟨k2, c2, t2, hs2, hc2, pc2, x28, x9, r2, f2⟩ : ∃ k c t2, Steps image (blk272.res.toState t) k c t2 ∧
      c ≤ 9 ∧ t2.pc = pcOf 287 ∧ t2.getReg .x28 = BitVec.ofNat 64 (shiftBelow lay) ∧
      t2.getReg .x9 = BitVec.ofNat 64 (height lay) ∧ RegsEq (blk272.res.toState t) t2 [.x3, .x9, .x28] ∧
      Frame (blk272.res.toState t) t2 (fun _ => False) := by
    by_cases h4 : lay < 4
    · have hs3 := symRun_sound blk277 codeAt_277 _ (by rw [pc1, if_pos h4]) (by simp only [blk277.res, rv_simp])
      have r3 : RegsEq (blk272.res.toState t) (blk277.res.toState (blk272.res.toState t)) [] := by
        intro r hr; rw [Result.toState_getReg]
        cases r <;> first | exact absurd (by decide) hr | rfl
      have pc3 : (blk277.res.toState (blk272.res.toState t)).pc = if lay = 0 then pcOf 285 else pcOf 278 := by
        simp only [blk277.res, rv_simp, x8', ofNat_beq_ofNat]
        by_cases h : lay = 0
        · rw [if_pos h, if_pos (by simp [h])]
        · rw [if_neg h, if_neg (by rw [decide_eq_true_eq, Nat.mod_eq_of_lt (by omega)]; simpa using h)]
      have f3 : Frame (blk272.res.toState t) (blk277.res.toState (blk272.res.toState t)) (fun _ => False) := by
        apply frame_toState; intro x hx hW; simp [blk277.res]
      by_cases h0 : lay = 0
      · subst h0
        have hs4 := symRun_sound blk285 codeAt_285 _ (by rw [pc3, if_pos rfl]) (by simp only [blk285.res, rv_simp])
        refine ⟨_, _, _, hs3.trans hs4, by decide, by simp only [blk285.res, rv_simp], ?_, ?_, ?_, ?_⟩
        · simp only [blk285.res, rv_simp]; rfl
        · simp only [blk285.res, rv_simp]; rfl
        · exact (r3.trans (show RegsEq _ (blk285.res.toState _) [.x3, .x9, .x28] by
            intro r hr; rw [Result.toState_getReg]
            cases r <;> first | exact absurd (by decide) hr | rfl)).mono (by decide)
        · exact (f3.trans (by apply frame_toState; intro x hx hW; simp [blk285.res])).mono
            (by intro x hx; rcases hx with h | h <;> exact h)
      · have x8'' : (blk277.res.toState (blk272.res.toState t)).getReg .x8 = BitVec.ofNat 64 lay := by
          rw [r3.get .x8, x8']
        have hs4 := symRun_sound blk278 codeAt_278 _ (by rw [pc3, if_neg h0]) (by simp only [blk278.res, rv_simp])
        refine ⟨_, _, _, hs3.trans hs4, by decide, by simp only [blk278.res, rv_simp], ?_, ?_, ?_, ?_⟩
        · simp only [blk278.res, rv_simp, x8'']
          bvsimp []
          rw [shiftBelow_eq lay hl, if_neg h0, if_pos h4]; exact ofNat_congr (by omega)
        · simp only [blk278.res, rv_simp]; rw [height_eq lay hl, if_neg h0, if_pos h4]
        · exact (r3.trans (show RegsEq _ (blk278.res.toState _) [.x3, .x9, .x28] by
            intro r hr; rw [Result.toState_getReg]
            cases r <;> first | exact absurd (by decide) hr | rfl)).mono (by decide)
        · exact (f3.trans (by apply frame_toState; intro x hx hW; simp [blk278.res])).mono
            (by intro x hx; rcases hx with h | h <;> exact h)
    · refine ⟨_, _, _, symRun_sound blk274 codeAt_274 _ (by rw [pc1, if_neg h4])
        (by simp only [blk274.res, rv_simp]), by decide, by simp only [blk274.res, rv_simp], ?_, ?_, ?_, ?_⟩
      · simp only [blk274.res, rv_simp]
        rw [shiftBelow_eq lay hl, if_neg (by omega), if_neg h4]
      · simp only [blk274.res, rv_simp]; rw [height_eq lay hl, if_neg (by omega), if_neg h4]
      · intro r hr; rw [Result.toState_getReg]
        cases r <;> first | exact absurd (by decide) hr | rfl
      · apply frame_toState; intro x hx hW; simp [blk274.res]
  -- block 279: route, encoding tweak
  have rt2 : RegsEq t t2 ([.x3] ++ [.x3, .x9, .x28]) := r1.trans r2
  have y22 : t2.getReg .x22 = BitVec.ofNat 64 idx := by rw [rt2.get .x22, hh.x22]
  have y8 : t2.getReg .x8 = BitVec.ofNat 64 lay := by rw [rt2.get .x8, hh.x8]
  have hs3 := symRun_sound blk287 codeAt_287 t2 pc2 (by simp only [blk287.res, rv_simp])
  set t4 := blk287.res.toState t2 with ht4
  have hp1 : 1 ≤ 2 ^ height lay := Nat.one_le_two_pow
  set e := (route idx lay).1 with he
  set tau := (route idx lay).2 with htau
  have he' : e = idx / 2 ^ shiftBelow lay % 2 ^ height lay := rfl
  have htau' : tau = idx / 2 ^ (shiftBelow lay + height lay) := rfl
  have hpw : 2 ^ height lay ≤ 2048 := by
    calc 2 ^ height lay ≤ 2 ^ 11 := Nat.pow_le_pow_right (by norm_num) hhg2
      _ = 2048 := by norm_num
  have he2048 : e < 2048 := by
    rw [he']; have := Nat.mod_lt (idx / 2 ^ shiftBelow lay) (Nat.two_pow_pos (height lay)); omega
  have htau30 : tau < 2 ^ 30 := by
    rw [htau', Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
    calc idx < 2 ^ 34 := hidx
      _ = 2 ^ 30 * 2 ^ 4 := by norm_num
      _ ≤ 2 ^ 30 * 2 ^ (shiftBelow lay + height lay) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hsh1)
  have hdiv1 : idx / 2 ^ shiftBelow lay ≤ idx := Nat.div_le_self _ _
  have hdiv2 : idx / 2 ^ (shiftBelow lay + height lay) ≤ idx := Nat.div_le_self _ _
  have z13 : t4.getReg .x13 = BitVec.ofNat 64 e := by
    simp only [ht4, blk287.res, rv_simp, y22, x28, x9]
    bvsimp [Nat.one_mul, Nat.and_two_pow_sub_one_eq_mod]
    rw [he']
  have z30 : t4.getReg .x30 = BitVec.ofNat 64 tau := by
    simp only [ht4, blk287.res, rv_simp, y22, x28, x9]
    bvsimp []
    rw [htau']
  have z31 : t4.getReg .x31 = BitVec.ofNat 64 (tau + 2 ^ 32 * e) := by
    simp only [ht4, blk287.res, rv_simp, y22, x28, x9]
    bvsimp [ofNat_eq_iff, Nat.one_mul, Nat.and_two_pow_sub_one_eq_mod]
    rw [htau', he']; congr 1; ring
  have f4 : Frame t2 t4 (fun a => a = 0x100 ∨ a = 0x108 ∨ a = 0x138) := by
    apply frame_toState; intro x hx hW
    simp only [blk287.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq, ofNat_eq_iff]
    omega
  have r4 : RegsEq t2 t4 [.x3, .x6, .x13, .x29, .x30, .x31] := by
    intro r hr; rw [ht4, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have ft4 : Frame t t4 (fun a => a = 0x100 ∨ a = 0x108 ∨ a = 0x138) :=
    (f1.trans (f2.trans f4)).mono (by intro x hx; rcases hx with h | h | h; exact h.elim; exact h.elim; exact h)
  have hc3 : blk287.res.cycles = 15 := rfl
  have hc1 : blk272.res.cycles = 2 := rfl
  refine ⟨_, _, t4, (hs1.trans (hs2.trans hs3)), by rw [hc1, hc3]; omega,
    by simp only [ht4, blk287.res, rv_simp], by simp only [ht4, blk287.res, rv_simp],
    by rw [r4.get .x9, x9], z13, z30, z31, ?_, ?_, ft4⟩
  · refine ⟨by omega, htau30, he2048, hh.hM, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [ht4, blk287.res, rv_simp, y8]
      bvsimp [ofNat_eq_iff]
      unfold twWord0; congr 1
      rw [Nat.div_eq_of_lt (by omega : tau < 2 ^ 32), Nat.mod_eq_of_lt (a := lay) (by omega)]; omega
    · have : t4.getMem (BitVec.ofNat 64 0x108) = t4.getReg .x31 := by
        simp (config := { decide := true }) only [ht4, blk287.res, rv_simp, ↓reduceIte]
      rw [this, z31]
    · rw [ft4.readWords _ _ (by norm_num) (by intro i hi; omega), hh.st.ebP]
    · rw [ft4.readWords _ _ (by norm_num) (by intro i hi; omega), hh.ebM]
    · simp only [ht4, blk287.res, rv_simp]; rfl
    · rw [r4.get .x5, rt2.get .x5, hh.x5]
    · rw [r4.get .x7, rt2.get .x7, hh.x7]
    · rw [r4.get .x26, rt2.get .x26, hh.x26]
    · rw [r4.get .x27, rt2.get .x27, hh.x27]
  · exact (rt2.trans r4).mono (by decide)

/-! ## `enc_ok`: counter, digits, tree setup (instructions 370 .. 507) -/

def digList (a : Word) : List Word := (a &&& 7) :: (List.range' 1 20).map (fun r => (a >>> (3 * r)) &&& 7)

-- The digit dwords written by `enc_ok` (kernel check with a variable state).
kernel_theorem blk338_dig : ∀ t : MachineState, (blk338.res.toState t).readWords (BitVec.ofNat 64 0x780) 42 =
    digList (t.getReg .x1) ++ digList (t.getReg .x2)

theorem digit_toNat (a : Word) (r : Nat) : ((a >>> (3 * r)) &&& 7).toNat = a.toNat / 2 ^ (3 * r) % 8 := by
  rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  exact land7 _

theorem digList_ofNat (d : Nat) (hd : d < 2 ^ 64) :
    digList (BitVec.ofNat 64 d) = (digitsOfWord d).map (BitVec.ofNat 64) := by
  unfold digList digitsOfWord
  rw [show List.range 21 = 0 :: List.range' 1 20 from rfl]
  simp only [List.map_cons, List.map_map, Nat.pow_zero, Nat.div_one]
  congr 1
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd,
      show (7 : Word).toNat = 7 from rfl, land7]
    have : d % 8 < 8 := Nat.mod_lt _ (by norm_num)
    omega
  · apply List.map_congr_left
    intro r hr
    simp only [Function.comp]
    apply BitVec.eq_of_toNat_eq
    rw [digit_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd, Nat.pow_mul]
    have : d / 8 ^ r % 8 < 8 := Nat.mod_lt _ (by norm_num)
    norm_num
    omega

theorem getD_append_left' {α : Type} (l1 l2 : List α) (i : Nat) (d : α) (h : i < l1.length) :
    (l1 ++ l2).getD i d = l1.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_right' {α : Type} (l1 l2 : List α) (i : Nat) (d : α) (h : l1.length ≤ i) :
    (l1 ++ l2).getD i d = l2.getD (i - l1.length) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

theorem digitsOfWord_lt (d i : Nat) : (digitsOfWord d).getD i 0 < 8 := by
  unfold digitsOfWord
  by_cases h : i < 21
  · rw [getD_of_lt (by simpa using h)]; simp; exact Nat.mod_lt _ (by norm_num)
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]; simp

theorem digits_lt (d0 d1 i : Nat) : (digitsOfWord d0 ++ digitsOfWord d1).getD i 0 < 8 := by
  by_cases h : i < 21
  · rw [getD_append_left' _ _ _ _ (by simp [digitsOfWord]; omega)]; exact digitsOfWord_lt _ _
  · rw [getD_append_right' _ _ _ _ (by simp [digitsOfWord]; omega)]; exact digitsOfWord_lt _ _

/-- `enc_ok` (330 .. 456): counter → stage, digits → `DIG8`, branch to the top layer or tree_build. -/
theorem enc_digits (lay c d0 d1 : Nat) (hlay : lay < 6) (hd0 : d0 < 2 ^ 63) (hd1 : d1 < 2 ^ 63)
    (t : MachineState) (tpc : t.pc = pcOf 338) (t1 : t.getReg .x1 = BitVec.ofNat 64 d0)
    (t2 : t.getReg .x2 = BitVec.ofNat 64 d1) (t6 : t.getReg .x6 = BitVec.ofNat 64 c)
    (t8 : t.getReg .x8 = BitVec.ofNat 64 lay) (t18 : t.getReg .x18 = BitVec.ofNat 64 (0x900 + 856 * lay)) :
    ∃ u, Steps image t 127 127 u ∧ u.pc = (if lay = 0 then pcOf 594 else pcOf 465) ∧
      u.readWords (BitVec.ofNat 64 0x780) 42 = (digitsOfWord d0 ++ digitsOfWord d1).map (BitVec.ofNat 64) ∧
      u.getMem (BitVec.ofNat 64 (0x900 + 856 * lay)) = BitVec.ofNat 64 c ∧
      RegsEq t u [.x3, .x14] ∧ Frame t u (fun a => a = 0x900 + 856 * lay ∨ (0x780 ≤ a ∧ a < 0x8D0)) := by
  have hs := symRun_sound blk338 codeAt_338 t tpc (by
    simp only [blk338.res, rv_simp]; bvsimp [t18, accessValid_ofNat, ne_eq, ofNat_eq_iff]; omega)
  have hc1 : blk338.res.cycles = 127 := rfl
  have hk1 : blk338.res.steps = 127 := rfl
  rw [hc1, hk1] at hs
  set u := blk338.res.toState t with hu
  refine ⟨u, hs, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [hu, blk338.res, rv_simp, t8, ofNat_beq_ofNat]
    by_cases h : lay = 0
    · rw [if_pos h, if_pos (by simp [h])]
    · rw [if_neg h, if_neg (by rw [decide_eq_true_eq, Nat.mod_eq_of_lt (by omega)]; simpa using h)]
  · rw [hu, blk338_dig, t1, t2, digList_ofNat _ (by omega), digList_ofNat _ (by omega), ← List.map_append]
  · have hread := Result.toState_getMem_of_read blk338.res t (cfg := { noAlias := true })
      (k := ⟨some (.reg .x18), 0⟩) (by sym_eval) (by
        simp only [rv_simp, t18]; bvsimp [ne_eq, ofNat_eq_iff]; omega)
    rw [show (⟨some (.reg .x18), 0⟩ : Addr).eval t = BitVec.ofNat 64 (0x900 + 856 * lay) by
      simp [Addr.eval, E.eval, t18]] at hread
    rw [hu, hread]; simp [E.eval, t6]
  · intro r hr; rw [hu, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  · apply frame_toState; intro x hx hW
    simp only [blk338.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq]
    bvsimp [t18, ofNat_eq_iff]
    omega

/-- Tree setup (457 .. 470): TA, the PB/CB/LB tweak words, `NCNT = 2^h`, `CB+32..48` cleared. -/
theorem tree_setup (S : List Byte) (lay tau h e d0 d1 : Nat) (hlay : lay < 6) (htau : tau < 2 ^ 30)
    (hh : 1 ≤ h ∧ h ≤ 6) (hheight : h = height lay) (he : e < 2 ^ h) (t : MachineState) (tpc : t.pc = pcOf 465)
    (hdig : t.readWords (BitVec.ofNat 64 0x780) 42 = (digitsOfWord d0 ++ digitsOfWord d1).map (BitVec.ofNat 64))
    (t5 : t.getReg .x5 = 0) (t8 : t.getReg .x8 = BitVec.ofNat 64 lay) (t9 : t.getReg .x9 = BitVec.ofNat 64 h)
    (t13 : t.getReg .x13 = BitVec.ofNat 64 e) (t18 : t.getReg .x18 = BitVec.ofNat 64 (0x900 + 856 * lay))
    (t30 : t.getReg .x30 = BitVec.ofNat 64 tau) (tst : Statics S t) :
    ∃ tt, Steps image t 14 14 tt ∧
      TreeCtx S (digitsOfWord d0 ++ digitsOfWord d1) ⟨lay, tau, h, e, 0x900 + 856 * lay⟩ tt ∧
      tt.pc = pcOf 479 ∧ tt.getReg .x20 = BitVec.ofNat 64 0 ∧
      RegsEq t tt [.x3, .x17, .x19, .x20, .x29] ∧
      Frame t tt (fun a => a = 0x6A0 ∨ a = 0xC0 ∨ a = 0x340 ∨ a = 0xE0 ∨ a = 0xE8) := by
  have hs := symRun_sound blk465 codeAt_465 t tpc (by simp only [blk465.res, rv_simp])
  have hc1 : blk465.res.cycles = 14 := rfl
  have hk1 : blk465.res.steps = 14 := rfl
  rw [hc1, hk1] at hs
  set tt := blk465.res.toState t with htt
  have f : Frame t tt (fun a => a = 0x6A0 ∨ a = 0xC0 ∨ a = 0x340 ∨ a = 0xE0 ∨ a = 0xE8) := by
    apply frame_toState; intro x hx hW
    simp only [blk465.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq, ofNat_eq_iff]
    omega
  have r : RegsEq t tt [.x3, .x17, .x19, .x20, .x29] := by
    intro r hr; rw [htt, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have hdig' : tt.readWords (BitVec.ofNat 64 0x780) 42 =
      (digitsOfWord d0 ++ digitsOfWord d1).map (BitVec.ofNat 64) := by
    rw [f.readWords _ _ (by norm_num) (by intro i hi; omega), hdig]
  have hp1 : 1 ≤ 2 ^ h := Nat.one_le_two_pow
  have hp32 : 2 ^ h ≤ 64 := pow_le32 _ hh.2
  refine ⟨tt, hs, ?_, by simp only [htt, blk465.res, rv_simp], by simp only [htt, blk465.res, rv_simp], r, f⟩
  refine ⟨by show lay < 7; omega, htau, hh.2, he, rfl, hheight, fun i => digits_lt d0 d1 i, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [r.get .x5, t5]
  · rw [r.get .x8, t8]
  · rw [r.get .x9, t9]
  · rw [r.get .x13, t13]
  · simp only [htt, blk465.res, rv_simp, t9]; bvsimp [Nat.one_mul]
  · rw [r.get .x18, t18]
  · simp only [htt, blk465.res, rv_simp]
  · rw [r.get .x30, t30]
  · intro i hi
    rw [getMem_of_readWords tt 42 0x780 i _ hdig' hi]
    rw [List.getD_eq_getElem?_getD, List.getElem?_map]
    rw [List.getD_eq_getElem?_getD]
    cases (digitsOfWord d0 ++ digitsOfWord d1)[i]? <;> rfl
  · simp only [htt, blk465.res, rv_simp, t8]
    bvsimp [ofNat_eq_iff]
    rw [lo32_replace0, ofNat_or_disjoint (lay * 65536) 1 16 (by omega) (by norm_num) (by omega)]
    simp only [truncate32_ofNat]; congr 1; ring
  · rw [f.readWords _ _ (by norm_num) (by intro i hi; omega), tst.pbP]
  · rw [f.readWords _ _ (by norm_num) (by intro i hi; omega), tst.pbS]
  · simp only [htt, blk465.res, rv_simp, t8]
    bvsimp [ofNat_eq_iff]
    rw [lo32_replace0, ofNat_or_disjoint (lay * 65536) 257 16 (by omega) (by norm_num) (by omega)]
    simp only [truncate32_ofNat]; congr 1; ring
  · rw [show (4 : Nat) = 2 + 2 from rfl, readWords_ofNat_add,
      f.readWords _ _ (by norm_num) (by intro i hi; omega), tst.cbP, readWords_ofNat_two]
    simp only [htt, blk465.res, rv_simp]; rfl
  · simp only [htt, blk465.res, rv_simp, t8]
    bvsimp [ofNat_eq_iff]
    rw [ofNat_or_disjoint (lay * 65536) 513 16 (by omega) (by norm_num) (by omega)]
    unfold twWord0; congr 1
    rw [Nat.div_eq_of_lt (by omega : tau < 2 ^ 32), Nat.mod_eq_of_lt (a := lay) (by omega)]; omega
  · rw [f.readWords _ _ (by norm_num) (by intro i hi; omega), tst.lbP]
  · rw [f.readWords _ _ (by norm_num) (by intro i hi; omega), tst.nbP]

end SigGolfCandidate.Radix27Sign

namespace SigGolfCandidate.Radix27Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

theorem signLayers_succ (S cache : List Byte) (idx lay : Nat) (M : Val) :
    signLayers S cache idx (lay + 1) M =
      searchCounter (lay + 1) (route idx (lay + 1)).2 (route idx (lay + 1)).1 M 0 cMax >>= fun r =>
        match r with
        | none => pure none
        | some (c, x) =>
          buildTree S (lay + 1) (route idx (lay + 1)).2 (height (lay + 1)) (route idx (lay + 1)).1 x >>= fun tr =>
            signLayers S cache idx lay tr.1 >>= fun r2 =>
              match r2 with
              | none => pure none
              | some rest => pure (some (rest ++ [(c, tr.2.1, tr.2.2)])) := by
  simp only [signLayers]
  rfl

theorem signTop_eq (S cache : List Byte) (idx : Nat) (M : Val) :
    signLayers S cache idx 0 M =
      searchCounter 0 (route idx 0).2 (route idx 0).1 M 0 cMax >>= fun r =>
        match r with
        | none => pure none
        | some (c, x) =>
          ((List.range (nChains / 2)).foldlM (fun (acc : List Val) k => do
              let (s0, s1) ← prf2 (prfInput S 0 (route idx 0).2 (route idx 0).1 k)
              let v0 ← chainTo 0 (route idx 0).2 (route idx 0).1 (2 * k) (x.getD (2 * k) 0) s0
              let v1 ← chainTo 0 (route idx 0).2 (route idx 0).1 (2 * k + 1) (x.getD (2 * k + 1) 0) s1
              pure (acc ++ [v0, v1])) [] >>= fun vals => topPath S cache (route idx 0).1 >>= fun path =>
                pure (vals, path)) >>= fun r => pure (some [(c, r.1, r.2)]) := by
  simp only [signLayers, signTop, bind_assoc, pure_bind]
  rfl

end SigGolfCandidate.Radix27Sign

namespace SigGolfCandidate.Radix27Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

/-- A staged layer signature (counter, 42 chain values, path) of layer `l`. -/
def StageAt (t : MachineState) (l : Nat) (ls : LayerSig) : Prop :=
  t.getMem (BitVec.ofNat 64 (0x900 + 856 * l)) = BitVec.ofNat 64 ls.1 ∧ ls.1 < 2 ^ 22 ∧
  ls.2.1.length = 42 ∧ (∀ v ∈ ls.2.1, v.length = 16) ∧ Slots t (0x900 + 856 * l + 8) ls.2.1 ∧
  ls.2.2.length = height l ∧ (∀ v ∈ ls.2.2, v.length = 16) ∧ Slots t (0x900 + 856 * l + 680) ls.2.2

theorem height_le (l : Nat) (hl : l < 6) : height l ≤ 11 := by interval_cases l <;> decide

theorem StageAt.frame {s t : MachineState} {W : Nat → Prop} {l : Nat} {ls : LayerSig}
    (h : StageAt s l ls) (hf : Frame s t W) (hl : l < 6)
    (hW : ∀ a, 0x900 + 856 * l ≤ a → a < 0x900 + 856 * (l + 1) → ¬ W a) : StageAt t l ls := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  have hh := height_le l hl
  refine ⟨?_, h2, h3, h4, ?_, h6, h7, ?_⟩
  · rw [hf.getMem (by omega) (hW _ (by omega) (by omega)), h1]
  · exact h5.frame hf (by omega) (fun i hi => ⟨hW _ (by omega) (by omega), hW _ (by omega) (by omega)⟩)
  · exact h8.frame hf (by omega) (fun i hi => ⟨hW _ (by omega) (by omega), hW _ (by omega) (by omega)⟩)

/-- Addresses written by layers `n .. 0`. -/
def layW (n : Nat) (a : Nat) : Prop := a < 0x900 ∨ (0x900 ≤ a ∧ a < 0x900 + 856 * (n + 1)) ∨ 0x30000 ≤ a

/-- Result of `signLayers n`. -/
def LaysPost (t0 : MachineState) (n : Nat) : Option (List LayerSig) → MachineState → Prop
  | none, t => t.pc = pcOf 337 ∧ t.getReg .x5 = 1 ∧ t.getReg .x10 = 1
  | some lays, t => lays.length = n + 1 ∧ (∀ l (hl : l < lays.length), StageAt t l lays[l]) ∧
      t.pc = pcOf 675 ∧ t.getReg .x5 = 0 ∧ Frame t0 t (layW n)

/-- Cycle bound of one layer below the top. -/
def layCyc : Nat := 26 + ((2 ^ 22) * 40 + 2) + (127 + (14 + (treeCyc + 7)))

/-- Cycle bound of the top layer. -/
def topCyc : Nat := 26 + ((2 ^ 22) * 40 + 2) + (127 + (9 + (21 * 320 + (4 + 11 * 36))))

/-- End of a layer (instructions 565 .. 571): root → `EB+32`, next layer. -/
theorem layer_tail (lay : Nat) (hlay : lay < 6) (h1 : 1 ≤ lay) (t : MachineState) (tpc : t.pc = pcOf 587)
    (t8 : t.getReg .x8 = BitVec.ofNat 64 lay) (t18 : t.getReg .x18 = BitVec.ofNat 64 (0x900 + 856 * lay))
    (t19 : t.getReg .x19 = BitVec.ofNat 64 0x34100) :
    ∃ t', Steps image t 7 7 t' ∧ t'.pc = pcOf 272 ∧ t'.getReg .x8 = BitVec.ofNat 64 (lay - 1) ∧
      t'.getReg .x18 = BitVec.ofNat 64 (0x900 + 856 * (lay - 1)) ∧
      t'.readWords (BitVec.ofNat 64 0x120) 2 = t.readWords (BitVec.ofNat 64 0x34100) 2 ∧
      RegsEq t t' [.x1, .x2, .x8, .x18] ∧ Frame t t' (fun a => a = 0x120 ∨ a = 0x128) := by
  have hs := symRun_sound blk587 codeAt_587 t tpc (by
    simp only [blk587.res, rv_simp]; bvsimp [t19, accessValid_ofNat]; norm_num)
  set t' := blk587.res.toState t with ht'
  refine ⟨t', hs, by simp only [ht', blk587.res, rv_simp], ?_, ?_, ?_, ?_, ?_⟩
  · simp only [ht', blk587.res, rv_simp, t8]; bvsimp []
  · simp only [ht', blk587.res, rv_simp, t18]; bvsimp []; exact ofNat_congr (by omega)
  · rw [readWords_ofNat_two, readWords_ofNat_two]
    simp only [ht', blk587.res, rv_simp, t19]; bvsimp []; simp
  · intro r hr; rw [ht', Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  · apply frame_toState; intro x hx hW
    simp only [blk587.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq, ofNat_eq_iff]
    omega

end SigGolfCandidate.Radix27Sign

namespace SigGolfCandidate.Radix27Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

theorem length_cacheNode (cache : List Byte) (hc : cache.length = 131072) (l j : Nat) (hl : l < 11)
    (hj : j < 2 ^ (11 - l)) : (cacheNode cache l j).length = 16 := by
  have := cacheNodeOff_lt l j hl hj
  simp [cacheNode, slice, hc]; omega

/-- The top layer, from `layer_loop` with `LAY = 0`. -/
theorem top_layer_sim (S cache : List Byte) (hS : S.length = 32) (hcache : cache.length = 131072)
    (idx : Nat) (M : Val) (t : MachineState) (hh : LayHead S cache idx 0 M t) :
    Sim image t topCyc (signLayers S cache idx 0 M) (LaysPost t 0) := by
  have hidx := hh.hidx
  obtain ⟨k, c0, t4, hs4, hc4, pc4, x46, x49, x413, x430, x431, emem, r4, f4⟩ := layer_header S cache idx 0 M t hh
  set e := (route idx 0).1 with he
  set tau := (route idx 0).2 with htau
  have he2048 := emem.he
  have htau30 := emem.htau
  rw [signTop_eq, show cMax = 2 ^ 22 - 1 + 1 from rfl]
  have henc := encLoop_sim 0 tau e M t4 emem (2 ^ 22 - 1) 0 t4 (by norm_num)
    ⟨pc4, x46, by norm_num, RegsEq.refl _ _, Frame.refl _ _⟩
  refine (Sim.steps hs4 (Sim.bind (W₂ := 127 + (9 + (21 * 320 + (4 + 11 * 36)))) henc
    (fun r t5 h5 => ?_))).mono (by unfold topCyc; omega) (fun _ _ h => h)
  rcases r with _ | ⟨c, x⟩
  · exact (Sim.pure (Q := LaysPost t 0) (a := none) (s := t5) h5).mono (by omega) (fun _ _ h => h)
  obtain ⟨pc5, x56, hc, ⟨d0, d1, hd0, hd1, hx, hsum, x51, x52⟩, r5, f5⟩ := h5
  subst hx
  have rt5 : RegsEq t t5 ([.x3, .x6, .x9, .x13, .x28, .x29, .x30, .x31] ++ encRegs) := r4.trans r5
  have ft5 : Frame t t5 (fun a => (a = 0x100 ∨ a = 0x108 ∨ a = 0x138) ∨ encW a) := f4.trans f5
  obtain ⟨u, hsu, pcu, digu, cntu, ru, fu⟩ := enc_digits 0 c d0 d1 (by norm_num) hd0 hd1 t5 pc5 x51 x52 x56
    (by rw [rt5.get .x8, hh.x8]) (by rw [rt5.get .x18, hh.x18])
  rw [if_pos rfl] at pcu
  have rtu : RegsEq t u (([.x3, .x6, .x9, .x13, .x28, .x29, .x30, .x31] ++ encRegs) ++ [.x3, .x14]) := rt5.trans ru
  have ftu : Frame t u (fun a => ((a = 0x100 ∨ a = 0x108 ∨ a = 0x138) ∨ encW a) ∨
      (a = 0x900 + 856 * 0 ∨ (0x780 ≤ a ∧ a < 0x8D0))) := ft5.trans fu
  have tctx : TopCtx S cache (digitsOfWord d0 ++ digitsOfWord d1) tau e u := by
    refine ⟨htau30, he2048, fun i => digits_lt d0 d1 i, by rw [rtu.get .x5, hh.x5],
      by rw [ru.get .x13, r5.get .x13, x413], by rw [rtu.get .x18, hh.x18],
      by rw [ru.get .x31, r5.get .x31, x431], fun i hi => ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [getMem_of_readWords u 42 0x780 i _ digu hi]
      rw [List.getD_eq_getElem?_getD, List.getElem?_map]
      rw [List.getD_eq_getElem?_getD]
      cases (digitsOfWord d0 ++ digitsOfWord d1)[i]? <;> rfl
    · rw [ftu.readWords _ _ (by norm_num) (by intro i hi; simp only [encW]; omega), hh.st.pbP]
    · rw [ftu.readWords _ _ (by norm_num) (by intro i hi; simp only [encW]; omega), hh.st.pbS]
    · rw [ftu.readWords _ _ (by norm_num) (by intro i hi; simp only [encW]; omega), hh.st.cbP]
    · exact hh.region.frame ftu (by intro a ha; simp only [regionA] at ha; simp only [encW]; omega)
    · exact fun l j hl hj => length_cacheNode cache hcache l j hl hj
  refine Sim.steps hsu (Sim.bind (W₂ := 0) (top_sim S cache hS _ tau e u tctx pcu) (fun r t6 h6 => ?_))
  obtain ⟨hl1, hv1, hs1, hl2, hv2, hs2, pc6, x65, f6⟩ := h6
  refine Sim.pure ⟨rfl, fun l hl => ?_, pc6, x65, ?_⟩
  · simp only [List.length_singleton] at hl
    have : l = 0 := by omega
    subst this
    refine ⟨?_, hc, hl1, hv1, hs1, hl2, hv2, hs2⟩
    rw [f6.getMem (by norm_num) (by simp only [topW]; omega), cntu]; rfl
  · exact (ftu.trans f6).mono (by intro a ha; simp only [encW, topW, layW] at ha ⊢; omega)

theorem height_bounds (lay : Nat) (h1 : 1 ≤ lay) (h6 : lay < 5) : 4 ≤ height lay ∧ height lay ≤ 6 := by
  interval_cases lay <;> decide

/-- **The layers** `n .. 0` (layer 0 is the cached top tree). -/
theorem layers_sim (S cache : List Byte) (hS : S.length = 32) (hcache : cache.length = 131072)
    (idx : Nat) (hidx : idx < 2 ^ 34) :
    ∀ n, n ≤ 4 → ∀ (M : Val) (t : MachineState), LayHead S cache idx n M t →
      Sim image t (n * layCyc + topCyc) (signLayers S cache idx n M) (LaysPost t n) := by
  intro n
  induction n with
  | zero =>
    intro _ M t hh
    simpa using top_layer_sim S cache hS hcache idx M t hh
  | succ n ih =>
    intro hn M t hh
    have hl : n + 1 < 5 := by omega
    have hhb := height_bounds (n + 1) (by omega) hl
    obtain ⟨k, c0, t4, hs4, hc4, pc4, x46, x49, x413, x430, x431, emem, r4, f4⟩ :=
      layer_header S cache idx (n + 1) M t hh
    set e := (route idx (n + 1)).1 with he
    set tau := (route idx (n + 1)).2 with htau
    have he32 : e < 2 ^ height (n + 1) := Nat.mod_lt _ (Nat.two_pow_pos _)
    have htau30 := emem.htau
    rw [signLayers_succ, show cMax = 2 ^ 22 - 1 + 1 from rfl]
    have henc := encLoop_sim (n + 1) tau e M t4 emem (2 ^ 22 - 1) 0 t4 (by norm_num)
      ⟨pc4, x46, by norm_num, RegsEq.refl _ _, Frame.refl _ _⟩
    have hW : c0 + ((2 ^ 22 - 1 + 1) * 40 + 2 + (127 + (14 + (treeCyc + (7 + (n * layCyc + topCyc + 0)))))) ≤
        (n + 1) * layCyc + topCyc := by
      have hL : 26 + ((2 ^ 22) * 40 + 2) + (127 + (14 + (treeCyc + 7))) = layCyc := rfl
      rw [Nat.add_mul n 1 layCyc, Nat.one_mul]; omega
    refine (Sim.steps hs4 (Sim.bind henc (fun r t5 h5 => ?_))).mono hW (fun _ _ h => h)
    rcases r with _ | ⟨c, x⟩
    · exact (Sim.pure (Q := LaysPost t (n + 1)) (a := none) (s := t5) h5).mono (by omega)
        (fun _ _ h => h)
    · obtain ⟨pc5, x56, hc, ⟨d0, d1, hd0, hd1, hx, hsum, x51, x52⟩, r5, f5⟩ := h5
      subst hx
      have rt5 : RegsEq t t5 ([.x3, .x6, .x9, .x13, .x28, .x29, .x30, .x31] ++ encRegs) := r4.trans r5
      have ft5 : Frame t t5 (fun a => (a = 0x100 ∨ a = 0x108 ∨ a = 0x138) ∨ encW a) := f4.trans f5
      obtain ⟨u, hsu, pcu, digu, cntu, ru, fu⟩ := enc_digits (n + 1) c d0 d1 (by omega) hd0 hd1 t5 pc5 x51 x52 x56
        (by rw [rt5.get .x8, hh.x8]) (by rw [rt5.get .x18, hh.x18])
      rw [if_neg (by omega)] at pcu
      have rtu : RegsEq t u (([.x3, .x6, .x9, .x13, .x28, .x29, .x30, .x31] ++ encRegs) ++ [.x3, .x14]) :=
        rt5.trans ru
      have ftu := ft5.trans fu
      have stu : Statics S u := hh.st.frame ftu (by
        intro a ha; simp only [staticA] at ha; simp only [encW]; omega)
      obtain ⟨tt, hs6, tctx, pc6, x620, r6, f6⟩ := tree_setup S (n + 1) tau (height (n + 1)) e d0 d1 (by omega) htau30
        ⟨by omega, hhb.2⟩ rfl he32 u pcu digu (by rw [rtu.get .x5, hh.x5]) (by rw [rtu.get .x8, hh.x8])
        (by rw [ru.get .x9, r5.get .x9, x49]) (by rw [ru.get .x13, r5.get .x13, x413])
        (by rw [rtu.get .x18, hh.x18]) (by rw [ru.get .x30, r5.get .x30, x430]) stu
      refine Sim.steps hsu (Sim.steps hs6 (Sim.bind (tree_sim S hS _ ⟨n + 1, tau, height (n + 1), e,
        0x900 + 856 * (n + 1)⟩ tt tctx (show 1 ≤ height (n + 1) by omega) pc6 x620) (fun tr t7 h7 => ?_)))
      obtain ⟨pc7, hr1, hroot, hv1, hvv, hvs, hp1, hpv, hps, r7, f7⟩ := h7
      have rt7 : RegsEq t t7 ((([.x3, .x6, .x9, .x13, .x28, .x29, .x30, .x31] ++ encRegs) ++ [.x3, .x14]) ++
          [.x3, .x17, .x19, .x20, .x29] ++ treeRegs) := (rtu.trans r6).trans r7
      obtain ⟨t8, hs8, pc8, x88, x818, heb, r8, f8⟩ := layer_tail (n + 1) (by omega) (by omega) t7 pc7
        (by rw [rt7.get .x8, hh.x8]) (by rw [rt7.get .x18, hh.x18])
        (by rw [r7.get .x19, tctx.x19])
      have rt8 : RegsEq t t8 _ := rt7.trans r8
      have ft8' := ((ftu.trans f6).trans f7).trans f8
      have ft8 : Frame t t8 (layW (n + 1)) := ft8'.mono (by
        intro a ha
        simp only [encW, treeW, leavesW, tlevW] at ha
        simp only [layW]; omega)
      have st8 : Statics S t8 := hh.st.frame ft8' (by
        intro a ha h
        simp only [staticA] at ha; simp only [encW, treeW, leavesW, tlevW] at h; omega)
      have rg8 : RegionOk cache t8 := hh.region.frame ft8' (by
        intro a ha h
        simp only [regionA] at ha; simp only [encW, treeW, leavesW, tlevW] at h; omega)
      -- the layers below
      have hroot16 : tr.1.length = 16 := hr1
      have hih := ih (by omega) tr.1 t8 ⟨by omega, hidx, hroot16, pc8, by rw [rt8.get .x5, hh.x5],
          by rw [rt8.get .x7, hh.x7], by rw [x88]; exact ofNat_congr (by omega),
          by rw [x818]; exact ofNat_congr (by omega), by rw [rt8.get .x22, hh.x22],
          by rw [rt8.get .x26, hh.x26], by rw [rt8.get .x27, hh.x27],
          by rw [heb, hroot 0 (by simp)]; simp, st8, rg8⟩
      refine Sim.steps hs8 (Sim.bind (W₂ := 0) hih (fun r2 t9 h9 => ?_))
      rcases r2 with _ | rest
      · exact Sim.pure h9
      · obtain ⟨hlen, hstages, pc9, x95, f9⟩ := h9
        refine Sim.pure ⟨by simp [hlen], ?_, pc9, x95, ?_⟩
        · intro l hl'
          simp only [List.length_append, List.length_singleton] at hl'
          by_cases hln : l < rest.length
          · rw [List.getElem_append_left hln]; exact hstages l hln
          · have : l = n + 1 := by omega
            subst this
            rw [List.getElem_append_right (by omega)]
            simp only [hlen, Nat.sub_self, List.getElem_singleton]
            have hst7 : StageAt t7 (n + 1) (c, tr.2.1, tr.2.2) := by
              refine ⟨?_, hc, hv1, hvv, hvs, hp1, hpv, hps⟩
              rw [f7.getMem (by omega) (by simp only [treeW, leavesW, tlevW]; omega),
                f6.getMem (by omega) (by omega), cntu]
            exact (hst7.frame (f8.trans f9) (by omega) (by
              intro a h1 h2 h; rcases h with h | h
              · omega
              · simp only [layW] at h; omega))
        · exact (ft8.trans f9).mono (by
            intro a ha; simp only [layW] at ha ⊢; omega)

end SigGolfCandidate.Radix27Sign



end


section -- SignClone13.Roots

/-! ### cloned Roots -/

/-!
# `sign`: FORS roots hash and layer-loop entry (instructions 232 .. 262)
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace SigGolfCandidate.Radix27Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

/-- From `pc 191` (after the FORS trees): the roots hash `M`, then the layer loop entry. -/
theorem roots_sim (S cache : List Byte) (idx : Nat) (hidx : idx < 2 ^ 34) (roots : List Val)
    (hlen : roots.length = 14) (hv : ∀ v ∈ roots, v.length = 16) (t : MachineState)
    (tpc : t.pc = pcOf 241) (t5 : t.getReg .x5 = 0)
    (t22 : t.getReg .x22 = BitVec.ofNat 64 idx) (hroots : Slots t 0x240 roots)
    (h8lo : lo32 (t.getMem (BitVec.ofNat 64 0x228)) = BitVec.ofNat 32 idx)
    (h8hi : hi32 (t.getMem (BitVec.ofNat 64 0x228)) = 0)
    (hP : t.readWords (BitVec.ofNat 64 0x230) 2 = [0, 0]) (hst : Statics S t) (hrg : RegionOk cache t) :
    Sim image t (10 + (8 * 4 + 20)) (hash16 (rootsInput idx roots))
      (fun M t' => LayHead S cache idx 4 M t' ∧ Frame t t' (fun a => a = 0x220 ∨ (0x120 ≤ a ∧ a < 0x140))) := by
  have hs1 := symRun_sound blk241 codeAt_241 t tpc (by simp only [blk241.res, rv_simp])
  have hc1 : blk241.res.cycles = 10 := rfl
  rw [hc1] at hs1
  set t1 := blk241.res.toState t with ht1
  have f1 : Frame t t1 (fun x => x = 0x220) := by
    apply frame_toState; intro x hx hW
    simp only [blk241.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq, ofNat_eq_iff]
    omega
  have r1 : RegsEq t t1 [.x3, .x10, .x11, .x12, .x29] := by
    intro r hr; rw [ht1, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have e1 := symRun_ecall blk241 codeAt_241 t (by simp only [blk241.res, rv_simp]) rfl
  have x10 : t1.getReg .x10 = BitVec.ofNat 64 0x220 := by simp only [ht1, blk241.res, rv_simp]
  have x11 : t1.getReg .x11 = BitVec.ofNat 64 256 := by simp only [ht1, blk241.res, rv_simp]
  have x12 : t1.getReg .x12 = BitVec.ofNat 64 0x120 := by simp only [ht1, blk241.res, rv_simp]
  have x5 : t1.getReg .x5 = 0 := by rw [r1.get .x5, t5]
  have pc1 : t1.pc = pcOf 251 := by simp only [ht1, blk241.res, rv_simp]
  have m220 : t1.getMem (BitVec.ofNat 64 0x220) = twWord0 11 0 idx 0 := by
    simp only [ht1, blk241.res, rv_simp, t22]
    bvsimp []
    refine (word_of_halves _ (idx / 2 ^ 32 * 2 ^ 24 + 2817) 0 ?_ ?_).trans ?_
    · simp only [ite_true, lo32_replace1, lo32_replace0, truncate32_ofNat]; rfl
    · simp only [ite_true, hi32_replace1]
    · unfold twWord0; apply ofNat_congr; omega
  have hq : hashInput t1 = pad64 (rootsInput idx roots) := by
    obtain ⟨hn, hw⟩ := words_thVals 11 0 idx 0 0 roots hv 3 (by rw [hlen])
    refine hashInput_eq_pad64 t1 _ 3 hn (by rw [x11]) (by norm_num) (by rw [x10]; decide) ?_
    rw [rootsInput, hw, x10, show 8 * (3 + 1) = 1 + 1 + 2 + 2 * 14 from rfl]
    rw [readWords_ofNat_add, readWords_ofNat_add, readWords_ofNat_add]
    simp only [Nat.reduceMul, Nat.reduceAdd]
    rw [readWords_ofNat_one, readWords_ofNat_one, m220, f1.getMem (a := 0x228) (by norm_num) (by norm_num),
      f1.readWords _ _ (by norm_num) (by intro i hi; omega), hP,
      show (28 : Nat) = 2 * roots.length by rw [hlen],
      f1.readWords _ _ (by rw [hlen]; norm_num) (by intro i hi; rw [hlen] at hi; omega),
      readWords_slots t 0x240 roots hroots]
    simp only [twWords_eq, List.cons_append, List.nil_append, List.cons.injEq, true_and]
    refine ⟨?_, trivial⟩
    rw [word_of_halves _ idx 0 h8lo (by rw [h8hi]; rfl)]
    (try (apply ofNat_congr; omega))
  have hb : (pad64 (rootsInput idx roots)).blocks = 4 :=
    congrArg (· + 1) (words_thVals 11 0 idx 0 0 roots hv 3 (by rw [hlen])).1
  refine (Sim.steps hs1 (Sim.hash16 (W := 20) e1 x5
    (hashArgs_of x10 x11 x12 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)) hq (fmt_thInput _ _ _ _ _ _ (by decide)) (fun a => ?_))).mono (by rw [hb]) (fun _ _ h => h)
  set t2 := writeHash t1 a with ht2
  have f2 : Frame t1 t2 (fun x => 0x120 ≤ x ∧ x < 0x120 + 32) := frame_writeHash t1 a _ x12 (by norm_num)
  have pc2 : t2.pc = pcOf 252 := by rw [ht2, writeHash_pc, pc1]; apply BitVec.eq_of_toNat_eq; simp
  have hs3 := symRun_sound blk252 codeAt_252 t2 pc2 (by simp only [blk252.res, rv_simp])
  have hc3 : blk252.res.cycles = 20 := rfl
  rw [hc3] at hs3
  set t3 := blk252.res.toState t2 with ht3
  have f3 : Frame t2 t3 (fun _ => False) := by
    apply frame_toState; intro x hx hW; simp [blk252.res]
  have r3 : RegsEq t2 t3 [.x7, .x8, .x18, .x26, .x27] := by
    intro r hr; rw [ht3, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have rt3 : RegsEq t t3 ([.x3, .x10, .x11, .x12, .x29] ++ [] ++ [.x7, .x8, .x18, .x26, .x27]) :=
    (r1.trans (regsEq_writeHash _ _ [])).trans r3
  have ft3 : Frame t t3 (fun a => a = 0x220 ∨ (0x120 ≤ a ∧ a < 0x140)) :=
    ((f1.trans f2).trans f3).mono (by
      intro x hx
      rcases hx with (h | h) | h
      · exact Or.inl h
      · exact Or.inr (by omega)
      · exact h.elim)
  refine Sim.pure_steps hs3 ⟨⟨by norm_num, hidx, by simp, by simp only [ht3, blk252.res, rv_simp],
    by rw [rt3.get .x5, t5], by simp only [ht3, blk252.res, rv_simp]; rfl, by simp only [ht3, blk252.res, rv_simp],
    by simp only [ht3, blk252.res, rv_simp], by rw [rt3.get .x22, t22],
    by simp only [ht3, blk252.res, rv_simp], by simp only [ht3, blk252.res, rv_simp],
    by rw [f3.readWords _ _ (by norm_num) (by simp), writeHash_readWords_val t1 a _ x12 (by norm_num)],
    hst.frame ft3 (by intro a ha h; simp only [staticA] at ha; omega),
    hrg.frame ft3 (by intro a ha h; simp only [regionA] at ha; omega)⟩, ft3⟩

end SigGolfCandidate.Radix27Sign


end


section -- SignClone13.Main

/-!
# `sign` refines `signRef` (main theorems)
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace SigGolfCandidate.Radix27Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref SigGolfCandidate.Mem

theorem decode_ecall : decodeInstruction 0x00000073#32 = some (.base .ECALL) := rfl

theorem fetch_ecall (t : MachineState) (i : Nat) (hi : image.code[i]? = some 0x00000073#32)
    (hlt : 0x1000 + 4 * i < 2 ^ 64) (hpc : t.pc = pcOf i) : fetch image t = some (.base .ECALL) := by
  unfold fetch
  rw [hpc]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  rw [if_neg (by simp <;> omega), show (0x1000 + 4 * i - 0x1000) / 4 = i by omega, hi]
  exact decode_ecall

theorem fetch_old_ecall (t : MachineState) (i : Nat)
    (hi : SigGolfCandidate.Images.signImage.code[i]? = some 0x00000073#32)
    (hlt : 0x1000 + 4 * i < 2 ^ 64) (hpc : t.pc = pcOf i) :
    fetch SigGolfCandidate.Images.signImage t = some (.base .ECALL) := by
  unfold fetch
  rw [hpc]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  rw [if_neg (by simp <;> omega), show (0x1000 + 4 * i - 0x1000) / 4 = i by omega, hi]
  exact decode_ecall

theorem oldCode86 : SigGolfCandidate.Images.signImage.code[86]? = some 0x00000073#32 := by decide +kernel
theorem oldCode89 : SigGolfCandidate.Images.signImage.code[89]? = some 0x00000073#32 := by decide +kernel
theorem oldCode337 : SigGolfCandidate.Images.signImage.code[337]? = some 0x00000073#32 := by decide +kernel

theorem code86 : image.code[86]? = some 0x00000073#32 := by decide +kernel
theorem code89 : image.code[89]? = some 0x00000073#32 := by decide +kernel
theorem code337 : image.code[337]? = some 0x00000073#32 := by decide +kernel
theorem oldCode2800 : SigGolfCandidate.Images.signImage.code[2800]? = some 0x00000073#32 := by decide +kernel

end SigGolfCandidate.Radix27Sign

namespace SigGolfCandidate.Radix27Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref SigGolfCandidate.Mem

theorem openAt_words (t : MachineState) (B : Nat) (o : Val × List Val) (h : OpenAt t B o) :
    t.readWords (BitVec.ofNat 64 B) 22 = wordsOf (o.1 ++ o.2.flatten) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hv : ∀ v ∈ o.1 :: o.2, v.length = 16 := by
    intro v hv; rcases List.mem_cons.mp hv with rfl | hv; exact h1; exact h3 v hv
  rw [show (22 : Nat) = 2 * (o.1 :: o.2).length by simp [h2], readWords_slots t B _ h4,
    ← wordsOf_flatten _ hv, List.flatten_cons]

theorem fors_words (t : MachineState) : ∀ (fors : List (Val × List Val)) (B : Nat),
    (∀ i (hi : i < fors.length), OpenAt t (B + 176 * i) fors[i]) →
    t.readWords (BitVec.ofNat 64 B) (22 * fors.length) =
      wordsOf (fors.map (fun o => o.1 ++ o.2.flatten)).flatten := by
  intro fors
  induction fors with
  | nil => intro B _; simp [wordsOf_nil]
  | cons o os ih =>
    intro B h
    have h0 := h 0 (by simp)
    simp only [Nat.mul_zero, Nat.add_zero, List.getElem_cons_zero] at h0
    rw [List.length_cons, show 22 * (os.length + 1) = 22 + 22 * os.length by ring, readWords_ofNat_add,
      openAt_words t B o h0, ih (B + 176) (fun i hi => by
        have := h (i + 1) (by simp; omega)
        rw [show B + 176 + 176 * i = B + 176 * (i + 1) by ring]; simpa using this),
      List.map_cons, List.flatten_cons, wordsOf_append (o.1 ++ o.2.flatten) _ (by
        obtain ⟨h1, h2, h3, _⟩ := h0
        simp [h1, length_flatten_vals o.2 h3, h2])]

theorem le32_bytes (t : MachineState) (a c : Nat) (ha : a % 8 = 0) (hb : a + 8 < 2 ^ 64)
    (hc : c < 2 ^ 32) (h : t.getMem (BitVec.ofNat 64 a) = BitVec.ofNat 64 c) :
    bytesAt t a 4 = le32 c := by
  apply List.ext_getElem (by simp [le32])
  intro i h1 h2
  simp only [length_bytesAt] at h1
  simp only [bytesAt, List.getElem_map, List.getElem_range, le32, leBytes]
  rw [getByte_aligned' t a i ha (by omega) hb, h]
  apply BitVec.eq_of_toNat_eq
  rw [extractByte_toNat', byte_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show c < 2 ^ 64 by omega),
    show (256 : Nat) ^ i = 2 ^ (8 * i) by rw [Nat.pow_mul]]

theorem stage_bytes (t : MachineState) (l : Nat) (hl : l < 5) (ls : LayerSig) (h : StageAt t l ls) :
    bytesAt t (0x900 + 856 * l) 4 ++ bytesAt t (0x900 + 856 * l + 8) (672 + 16 * height l) =
      le32 ls.1 ++ ls.2.1.flatten ++ ls.2.2.flatten := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  have hh := height_le l (by omega)
  rw [le32_bytes t _ ls.1 (by omega) (by omega) (by omega) h1, List.append_assoc]
  congr 1
  have hv : ∀ v ∈ ls.2.1 ++ ls.2.2, v.length = 16 := by
    intro v hv; rcases List.mem_append.mp hv with hv | hv; exact h4 v hv; exact h7 v hv
  have hsl : Slots t (0x900 + 856 * l + 8) (ls.2.1 ++ ls.2.2) :=
    Slots.append h5 (by rw [h3, show 0x900 + 856 * l + 8 + 16 * 42 = 0x900 + 856 * l + 680 by ring]; exact h8)
  have hw := readWords_slots t _ _ hsl
  rw [← wordsOf_flatten _ hv, List.flatten_append] at hw
  have hlen : (ls.2.1 ++ ls.2.2).length = 42 + height l := by simp [h3, h6]
  rw [show 672 + 16 * height l = 8 * (2 * (ls.2.1 ++ ls.2.2).length) by rw [hlen]; ring]
  refine bytesAt_of_readWords t _ _ _ (by omega) (by rw [hlen]; omega) ?_ hw
  rw [List.length_append, length_flatten_vals _ h4, length_flatten_vals _ h7, hlen, h3, h6]; ring

end SigGolfCandidate.Radix27Sign

namespace SigGolfCandidate.Radix27Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref SigGolfCandidate.Mem

theorem flatMap_range_eq {β γ : Type} (xs : List β) (g : Nat → List γ) (f : β → List γ)
    (h : ∀ l (hl : l < xs.length), g l = f xs[l]) :
    (List.range xs.length).flatMap g = (xs.map f).flatten := by
  induction xs using List.reverseRecOn with
  | nil => simp
  | append_singleton xs x ih =>
    rw [List.length_append, List.length_singleton, List.range_succ, List.flatMap_append,
      ih (fun l hl => by rw [h l (by simp; omega), List.getElem_append_left hl]),
      List.map_append, List.flatten_append]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_cons, List.map_nil,
      List.flatten_cons, List.flatten_nil]
    rw [h xs.length (by simp), List.getElem_append_right (le_refl _)]
    simp

set_option maxRecDepth 100000 in
/-- The signature bytes after the pack. -/
theorem final_bytes (t4 : MachineState) (rho : Val) (fors : List (Val × List Val)) (lays : List LayerSig)
    (hrho : rho.length = 16) (hrw : t4.readWords (BitVec.ofNat 64 0x2650) 2 = wordsOf rho)
    (hfl : fors.length = 14)
    (hopen : ∀ i (hi : i < fors.length), OpenAt t4 (0x2650 + 16 + 176 * i) fors[i])
    (hll : lays.length = 5) (hst : ∀ l (hl : l < lays.length), StageAt t4 l lays[l]) (t5 : MachineState)
    (hw5 : t5.readWords (BitVec.ofNat 64 (0x2650 + 2480)) 491 = packTab.map (packDW t4))
    (hf5 : Frame t4 t5 (fun x => packD ≤ x ∧ x < packD + 8 * 491)) :
    bytesAt t5 0x2650 6404 = serialize rho fors lays := by
  have hfb : (fors.map (fun o => o.1 ++ o.2.flatten)).flatten.length = 2464 := by
    have : ∀ os : List (Val × List Val), (∀ i (hi : i < os.length), OpenAt t4 (0x2650 + 16 + 176 * i) os[i]) →
        True := fun _ _ => trivial
    rw [List.length_flatten, List.map_map]
    have hlen : ∀ o ∈ fors, (o.1 ++ o.2.flatten).length = 176 := by
      intro o ho
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ho
      obtain ⟨h1, h2, h3, _⟩ := hopen i hi
      simp [h1, length_flatten_vals _ h3, h2]
    rw [List.map_congr_left (fun o ho => by simp only [Function.comp]; exact hlen o ho)]
    simp [hfl]
  rw [show (6404 : Nat) = 2480 + 3924 from rfl, bytesAt_add, pack_layers t4 t5 hw5]
  unfold serialize
  congr 1
  · have hw : t5.readWords (BitVec.ofNat 64 0x2650) 310 =
        wordsOf (rho ++ (fors.map (fun o => o.1 ++ o.2.flatten)).flatten) := by
      rw [hf5.readWords _ _ (by norm_num) (fun i hi => by simp only [packD]; omega), show (310 : Nat) = 2 + 22 * fors.length by rw [hfl], readWords_ofNat_add, hrw,
        fors_words t4 fors _ hopen, wordsOf_append rho _ (by omega)]
    rw [show (2480 : Nat) = 8 * 310 from rfl]
    exact bytesAt_of_readWords _ 310 _ _ (by norm_num) (by norm_num) (by simp [hrho, hfb]) hw
  · rw [← hll]
    refine flatMap_range_eq lays _ _ (fun l hl => ?_)
    rw [List.append_assoc]
    exact (stage_bytes t4 l (by omega) lays[l] (hst l hl)).trans (by rw [List.append_assoc])

end SigGolfCandidate.Radix27Sign

namespace SigGolfCandidate.Radix27Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref SigGolfCandidate.Mem

theorem OpenAt.frame {s t : MachineState} {W : Nat → Prop} {B : Nat} {o : Val × List Val}
    (h : OpenAt s B o) (hf : Frame s t W) (hB : B + 176 + 16 < 2 ^ 64)
    (hW : ∀ a, B ≤ a → a < B + 176 → ¬ W a) : OpenAt t B o := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2, h3, h4.frame hf (by simp [h2]; omega) (fun i hi => ?_)⟩
  simp [h2] at hi
  exact ⟨hW _ (by omega) (by omega), hW _ (by omega) (by omega)⟩

/-- `signList` after the MAC check. -/
def signRest (S cache m : List Byte) : OracleComp HashSpec (Option (List Byte)) :=
  searchDigest S m 0 (2 ^ 20 - 1 + 1) >>= fun r =>
    match r with
    | none => pure none
    | some (rho, N) =>
      signFors S N >>= fun p =>
        hash16 (rootsInput (idxOf N) p.2) >>= fun M =>
          signLayers S cache (idxOf N) 4 M >>= fun r2 =>
            match r2 with
            | none => pure none
            | some lays => pure (some (serialize rho p.1 lays))

theorem signList_eq (S cache m : List Byte) :
    signList S cache m = (H (macInput S (cacheRegion cache)) >>= fun tag =>
      if toList (n := 32) tag = cacheTag cache then signRest S cache m else pure none) := by
  simp only [signList, signRest]
  rfl

/-- Result of `signList`: at a HALT, `a0 = 1` (failure) or `a0 = 0` and the signature. -/
def ListPost (r : Option (List Byte)) (t : MachineState) : Prop :=
  fetch SigGolfCandidate.Images.signImage t = some (.base .ECALL) ∧ t.getReg .x5 = 1 ∧
  match r with
  | none => fetch image t = some (.base .ECALL) ∧ t.getReg .x10 = 1
  | some l => t.pc = pcOf 2800 ∧ t.getReg .x10 = 0 ∧ readBuffer t 0x2650 6404 = ofList 6404 l

/-- The zero buffers used as padding / P slots, never written by `sign` after the setup. -/
def ZA (a : Nat) : Prop :=
  (0x110 ≤ a ∧ a < 0x120) ∨ (0x6B0 ≤ a ∧ a < 0x6C0) ∨ (0xD0 ≤ a ∧ a < 0xE0) ∨
    (0x350 ≤ a ∧ a < 0x360) ∨ (0x1D0 ≤ a ∧ a < 0x1E0) ∨ (0x230 ≤ a ∧ a < 0x240) ∨ (0xF0 ≤ a ∧ a < 0x100)

end SigGolfCandidate.Radix27Sign

namespace SigGolfCandidate.Radix27Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref SigGolfCandidate.Mem

/-- Cycle bound after the MAC check (digest search, dig_ok, FORS, roots, layers, pack, HALT prep). -/
def restW : Nat :=
  (2 ^ 20 - 1 + 1) * 46 + 2 + (66 + (14 * forsTreeW + (10 + (8 * 4 + 20) + (4 * layCyc + topCyc + (2123 + 2)))))

/-- Cycle bound of `signList`. -/
def signW : Nat := 54 + (8 * 1025 + (10 + restW))

theorem region_s0 (sk : SecretKey) (cache : Cache) (m : Message) :
    RegionOk (toList cache) (s0 sk cache m) := by
  intro l j hl hj
  have := cacheNodeOff_lt l j hl hj
  have h8 : cacheNodeOff l j % 8 = 0 := by unfold cacheNodeOff; omega
  rw [s0_readWords_cache sk cache m _ 2 h8 (by omega)]; rfl

theorem signRest_sim (sk : SecretKey) (cache : Cache) (m : Message) (u : MachineState)
    (hu : MacOk sk cache m u) :
    Sim image u restW (signRest (toList sk) (toList cache) (toList m)) ListPost := by
  have hS : (toList sk).length = 32 := length_toList sk
  have hcache : (toList cache).length = 131072 := by simp [toList, SigGolfCandidate.Legacy.bytes]; rfl
  have dmem := hu.mem
  have u5 := hu.x5
  have u7 := hu.x7
  have dinv := hu.inv
  have upbS := hu.pbS
  have fs0 := hu.frame
  unfold signRest restW
  refine Sim.bind (digLoop_sim sk m u dmem u5 u7 (2 ^ 20 - 1) 0 u (by norm_num) dinv)
    (fun r t h => ?_)
  rcases r with _ | ⟨rho, N⟩
  · obtain ⟨tpc, t5, t10⟩ := h
    exact (Sim.pure ⟨fetch_old_ecall t 86 oldCode86 (by norm_num) tpc, t5,
      fetch_ecall t 86 code86 (by norm_num) tpc, t10⟩).mono (by omega)
      (fun _ _ h => h)
  · obtain ⟨tpc, tregs, tframe, hrl, hrw, ⟨ans, hN, hd⟩, hadm⟩ := h
    subst hN
    set N := ans.toNat % 2 ^ 184 with hNdef
    set idx := idxOf N with hidxdef
    have hidx : idx < 2 ^ 34 := Nat.mod_lt _ (by norm_num)
    -- the zero buffers at `t`
    have z0 : ∀ a, a % 8 = 0 → ZA a → (s0 sk cache m).getMem (BitVec.ofNat 64 a) = 0 := by
      intro a h8 hz; simp only [ZA] at hz; exact s0_zero sk cache m a h8 (by omega) (by omega)
    have zt : ∀ a, a % 8 = 0 → ZA a → t.getMem (BitVec.ofNat 64 a) = 0 := by
      intro a h8 hz
      have : ¬ macW a := by simp only [ZA] at hz; simp only [macW, setupW]; omega
      have : ¬ digW a := by simp only [ZA] at hz; simp only [digW]; omega
      rw [tframe.getMem (by simp only [ZA] at hz; omega) (by assumption),
        fs0.getMem (by simp only [ZA] at hz; omega) (by assumption), z0 a h8 hz]
    have zrw : ∀ a, a % 8 = 0 → ZA a → ZA (a + 8) → t.readWords (BitVec.ofNat 64 a) 2 = [0, 0] := by
      intro a h8 h1 h2
      rw [readWords_ofNat_two, zt a h8 h1, zt (a + 8) (by omega) h2]
    have tS : t.readWords (BitVec.ofNat 64 0x6C0) 4 = wordsOf (toList sk) := by
      rw [tframe.readWords _ _ (by norm_num) (by intro i hi; simp only [digW]; omega), upbS]
    have rgt : RegionOk (toList cache) t :=
      ((region_s0 sk cache m).frame fs0 (by intro a ha; simp only [regionA] at ha; simp only [macW, setupW]; omega)).frame
        tframe (by intro a ha; simp only [regionA] at ha; simp only [digW]; omega)
    obtain ⟨tF, hsF, ctx, pcF, x8F, x18F, x22F, sigF, lo228, hi228, rF, fF⟩ :=
      digok_run (toList sk) rho ans t tpc (by rw [tregs.get .x5, u5]) hd
        (zrw _ (by norm_num) (by simp [ZA]) (by simp [ZA])) tS
        (zrw _ (by norm_num) (by simp [ZA]) (by simp [ZA])) (zrw _ (by norm_num) (by simp [ZA]) (by simp [ZA]))
        (zrw _ (by norm_num) (by simp [ZA]) (by simp [ZA]))
    have zF : ∀ a, a % 8 = 0 → ZA a → tF.getMem (BitVec.ofNat 64 a) = 0 := by
      intro a h8 hz
      rw [fF.getMem (by simp only [ZA] at hz; omega) (by simp only [ZA] at hz; simp only [digokW]; omega),
        zt a h8 hz]
    have rgF : RegionOk (toList cache) tF :=
      rgt.frame fF (by intro a ha; simp only [regionA] at ha; simp only [digokW]; omega)
    refine Sim.steps hsF (Sim.bind (fors_sim (toList sk) hS N tF ctx pcF x8F x18F) (fun p t2 h2 => ?_))
    obtain ⟨-, hl1, hl2, hopen, hrv, hroots, pc2, -, -, fregs, fframe, -, -, -, -, -⟩ := h2
    have pc2' : t2.pc = pcOf 241 := by rw [pc2]; rfl
    have z2 : ∀ a, a % 8 = 0 → ZA a → t2.getMem (BitVec.ofNat 64 a) = 0 := by
      intro a h8 hz
      rw [fframe.getMem (by simp only [ZA] at hz; omega) (by simp only [ZA] at hz; simp only [forsW]; omega),
        zF a h8 hz]
    have z2rw : ∀ a, a % 8 = 0 → ZA a → ZA (a + 8) → t2.readWords (BitVec.ofNat 64 a) 2 = [0, 0] := by
      intro a h8 h1 h2
      rw [readWords_ofNat_two, z2 a h8 h1, z2 (a + 8) (by omega) h2]
    have st2 : Statics (toList sk) t2 := by
      refine ⟨z2rw _ (by norm_num) (by simp [ZA]) (by simp [ZA]), z2rw _ (by norm_num) (by simp [ZA]) (by simp [ZA]),
        ?_, z2rw _ (by norm_num) (by simp [ZA]) (by simp [ZA]), z2rw _ (by norm_num) (by simp [ZA]) (by simp [ZA]),
        z2rw _ (by norm_num) (by simp [ZA]) (by simp [ZA])⟩
      rw [fframe.readWords _ _ (by norm_num) (by intro i hi; simp only [forsW]; omega),
        fF.readWords _ _ (by norm_num) (by intro i hi; simp only [digokW]; omega), tS]
    have rg2 : RegionOk (toList cache) t2 :=
      rgF.frame fframe (by intro a ha; simp only [regionA] at ha; simp only [forsW]; omega)
    have h228 := fframe.getMem (a := 0x228) (by norm_num) (by simp only [forsW]; omega)
    refine Sim.bind (roots_sim (toList sk) (toList cache) idx hidx p.2 (by rw [hl2]) hrv t2 pc2'
      (by rw [fregs.get .x5, ctx.x5]) (by rw [fregs.get .x22, x22F]) hroots (by rw [h228, lo228])
      (by rw [h228, hi228, tframe.getMem (by norm_num) (by simp only [digW]; omega),
        fs0.getMem (by norm_num) (by simp only [macW, setupW]; omega),
        s0_zero sk cache m 0x228 (by norm_num) (by norm_num) (by omega)]; rfl)
      (z2rw _ (by norm_num) (by simp [ZA]) (by simp [ZA])) st2 rg2) (fun M t3 h3 => ?_)
    obtain ⟨hhead, rframe⟩ := h3
    refine Sim.bind (layers_sim (toList sk) (toList cache) hS hcache idx hidx 4 (le_refl _) M t3 hhead)
      (fun r2 t4 h4 => ?_)
    rcases r2 with _ | lays
    · obtain ⟨pc4, x45, x410⟩ := h4
      exact (Sim.pure ⟨fetch_old_ecall t4 337 oldCode337 (by norm_num) pc4, x45,
        fetch_ecall t4 337 code337 (by norm_num) pc4, x410⟩).mono (by omega)
        (fun _ _ h => h)
    · obtain ⟨hll, hst, pc4, x45, lframe⟩ := h4
      obtain ⟨t5, hs5, pc5, hw5, hf5⟩ := pack_run t4 pc4
      rw [List.drop_zero, List.take_of_length_le (by rw [packTab_length])] at hw5
      have hf5' : Frame t4 t5 (fun x => packD ≤ x ∧ x < packD + 8 * 491) :=
        hf5.mono (fun x hx => by simp only [packD] at hx ⊢; omega)
      have hs6 := symRun_sound blk2798 codeAt_2798 t5 pc5 (by simp only [blk2798.res, rv_simp])
      set t6 := blk2798.res.toState t5 with ht6
      have hc : 2123 + blk2798.res.cycles = 2123 + 2 := rfl
      have mem6 : ∀ a, t6.getMem a = t5.getMem a := by
        intro a; rw [ht6, Result.toState_getMem, show blk2798.res.st.mem = [] from rfl, memEval_nil]
      have by6 : bytesAt t6 0x2650 6404 = bytesAt t5 0x2650 6404 := by
        unfold bytesAt; apply List.map_congr_left; intro i _
        simp only [MachineState.getByte, mem6]
      -- the rho and FORS parts at `t4`
      have ft24 : Frame t2 t4 (fun a => (a = 0x220 ∨ (0x120 ≤ a ∧ a < 0x140)) ∨ layW 4 a) :=
        rframe.trans lframe
      have hrho4 : t4.readWords (BitVec.ofNat 64 0x2650) 2 = wordsOf rho := by
        rw [ft24.readWords _ _ (by norm_num) (by intro i hi; simp only [layW]; omega),
          fframe.readWords _ _ (by norm_num) (by intro i hi; simp only [forsW]; omega), sigF, hrw]
      have hopen4 : ∀ i (hi : i < p.1.length), OpenAt t4 (0x2650 + 16 + 176 * i) p.1[i] := by
        intro i hi
        rw [hl1] at hi
        exact (hopen i (by rw [hl1]; exact hi)).frame ft24 (by omega) (by
          intro a h1 h2; simp only [layW]; omega)
      refine (Sim.pure_steps (hs5.trans hs6) ⟨fetch_old_ecall t6 2800 oldCode2800 (by norm_num) rfl,
        by simp only [ht6, blk2798.res, rv_simp], rfl,
        by simp only [ht6, blk2798.res, rv_simp], ?_⟩).mono
        (by rw [hc]) (fun _ _ h => h)
      rw [readBuffer_bytesAt, by6, final_bytes t4 rho p.1 lays hrl hrho4 hl1 hopen4 hll hst t5 hw5 hf5']

theorem signList_sim (sk : SecretKey) (cache : Cache) (m : Message) :
    Sim image (s0 sk cache m) signW (signList (toList sk) (toList cache) (toList m)) ListPost := by
  rw [signList_eq]
  exact mac_sim sk cache m _ restW ListPost (fun u hu => signRest_sim sk cache m u hu)
    (fun t tpc t5 t10 => ⟨fetch_old_ecall t 89 oldCode89 (by norm_num) tpc, t5,
      fetch_ecall t 89 code89 (by norm_num) tpc, t10⟩)

end SigGolfCandidate.Radix27Sign

namespace SigGolfCandidate.Radix27Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref SigGolfCandidate.Mem

/-- Final states: at a HALT whose output is `signRef`'s value. -/
def SignPost (a : Option (Bytes 6404)) (t : MachineState) : Prop :=
  fetch SigGolfCandidate.Images.signImage t = some (.base .ECALL) ∧ t.getReg .x5 = 1 ∧
  a = (if t.getReg .x10 = 0 then some (readBuffer t 0x2650 6404) else none) ∧
  (t.getReg .x10 = 0 → t.pc = pcOf 2800) ∧
  (t.getReg .x10 ≠ 0 → fetch image t = some (.base .ECALL))
set_option maxRecDepth 100000 in

theorem signRef_sim (sk : SecretKey) (cache : Cache) (m : Message) :
    Sim image (s0 sk cache m) signW (signRef sk cache m) SignPost := by
  unfold signRef
  refine (Sim.bind (signList_sim sk cache m) (fun r t h => Sim.pure ?_)).mono (by omega) (fun _ _ h => h)
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, h2, ?_, ?_, ?_⟩
  · rcases r with _ | l
    · simp only at h3; rw [h3.2]; simp
    · obtain ⟨_, h4, h5⟩ := h3
      rw [h4, if_pos rfl, h5]; rfl
  · rcases r with _ | l
    · simp only at h3; simp [h3.2]
    · exact fun _ => h3.1
  · rcases r with _ | l
    · exact fun _ => h3.1
    · exact fun hz => False.elim (by have := h3.2; simp [this] at hz)

theorem signW_lt : signW + 1 < CYCLE_LIMIT := by
  unfold signW restW forsTreeW layCyc topCyc treeCyc tleafCyc CYCLE_LIMIT; norm_num

end SigGolfCandidate.Radix27Sign


end


section -- SignClone13.Terminal

/-! A terminal hook for a simulated segment whose successful HALT has been
replaced by an ordinary postprocessor. -/

namespace SigGolfCandidate.Radix27Sign

open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
  SigGolfCandidate.Rv OracleComp OracleSpec

set_option maxRecDepth 100000

theorem toRunResult_charge_value (submission : Submission) (phase : Phase)
    (e : Execution) (c h b : Nat) :
    (toRunResult submission phase (e.charge c h b)).value =
      (toRunResult submission phase e).value := by
  cases e
  rfl

theorem toRunResult_charge_hashCalls (submission : Submission) (phase : Phase)
    (e : Execution) (c h b : Nat) :
    (toRunResult submission phase (e.charge c h b)).hashCalls = h + e.hashCalls := rfl

theorem toRunResult_charge_hashCompressions (submission : Submission) (phase : Phase)
    (e : Execution) (c h b : Nat) :
    (toRunResult submission phase (e.charge c h b)).hashCompressions = b + e.hashCompressions := rfl

theorem Sim.run_eq_terminal (submission : Submission) (phase : Phase)
    (input : Input submission.sizes phase)
    {s : MachineState} (hinit : initialState submission phase input = some s)
    {α : Type} {W L : Nat} {oa : OracleComp HashSpec α}
    {Q : α → MachineState → Prop}
    (hsim : Sim (submission.image phase) s W oa Q)
    (hW : W + L < CYCLE_LIMIT)
    (F : α → Option (Output submission.sizes phase))
    (hQ : ∀ a t, Q a t → ∃ e : Execution,
      (∀ fuel, L ≤ fuel → Riscv.execute fuel (submission.image phase) t = Pure.pure e) ∧
      (toRunResult submission phase e).value = F a ∧
      e.hashCalls = 0 ∧ e.hashCompressions = 0) :
    (fun r => (r.value, r.hashCalls, r.hashCompressions)) <$>
        submission.run phase input =
      (fun p => (F p.1, p.2.1, p.2.2)) <$> countBoth oa := by
  obtain ⟨oc, hp, hf⟩ := hsim
  rw [Rv.run_eq submission phase input s hinit,
    hf CYCLE_LIMIT (by omega), ← hp, Functor.map_map]
  simp only [map_bind, Functor.map_map]
  rw [map_eq_bind_pure_comp (x := oc)]
  congr 1
  funext o
  obtain ⟨e, he, heval, hecalls, heblocks⟩ := hQ _ _ o.2.2.2
  have hle : L ≤ CYCLE_LIMIT - o.1.steps := by
    have := o.2.1
    have := o.2.2.1
    omega
  rw [he _ hle]
  simp only [map_pure, Function.comp]
  simp only [toRunResult_charge_value, toRunResult_charge_hashCalls,
    toRunResult_charge_hashCompressions, heval, hecalls, heblocks, Nat.add_zero]

theorem Sim.runWith_terminal (submission : Submission) (phase : Phase)
    (input : Input submission.sizes phase)
    {s : MachineState} (hinit : initialState submission phase input = some s)
    {α : Type} {W L : Nat} {oa : OracleComp HashSpec α}
    {Q : α → MachineState → Prop}
    (hsim : Sim (submission.image phase) s W oa Q)
    (hW : W + L < CYCLE_LIMIT)
    (hQ : ∀ a t, Q a t → ∃ e : Execution,
      (∀ fuel, L ≤ fuel → Riscv.execute fuel (submission.image phase) t = Pure.pure e) ∧
      e.exit ≠ .unfinished ∧ e.cycles ≤ L)
    (hash : Hash) :
    (submission.runWith hash phase input).finished = true ∧
      (submission.runWith hash phase input).cycles ≤ W + L := by
  obtain ⟨oc, _, hf⟩ := hsim
  rw [runWith_eq submission hash phase input s hinit,
    hf CYCLE_LIMIT (by omega), evalWithAnswerFn_bind, evalWithAnswerFn_map]
  generalize evalWithAnswerFn hash oc = o
  obtain ⟨e, he, hexit, hcycles⟩ := hQ _ _ o.2.2.2
  have hle : L ≤ CYCLE_LIMIT - o.1.steps := by
    have := o.2.1
    have := o.2.2.1
    omega
  rw [he _ hle]
  simp only [evalWithAnswerFn_pure, toRunResult, Execution.charge]
  constructor
  · simp [hexit]
  · have := o.2.2.1
    omega

end SigGolfCandidate.Radix27Sign


end
