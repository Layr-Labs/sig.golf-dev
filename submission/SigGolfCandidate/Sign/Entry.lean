import SigGolfCandidate.Sign.Head
import SigGolfCandidate.Sign.Layer
import SigGolfCandidate.Sign.Pack

/-!
# `sign`: layer-loop entry (296 .. 315) and the signature's layer bytes

* `layer_entry` : the layer constants (`LIM = 2^22`, the SWAR masks, `LAY = 4`, `SIGL` = stage 4).
* `stage_bytes`, `layers_bytes` : the packed layer region `SIG + 2176 ..` from the stages.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace SigGolfCandidate.Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref SigGolfCandidate.Mem

theorem layer_entry (S cache : List Byte) (idx : Nat) (hidx : idx < 2 ^ 34) (M : Val) (hM : M.length = 16)
    (t : MachineState) (tpc : t.pc = pcOf 296) (t5 : t.getReg .x5 = 0)
    (t22 : t.getReg .x22 = BitVec.ofNat 64 idx) (heb : t.readWords (BitVec.ofNat 64 0x120) 2 = wordsOf M)
    (hst : Statics S t) (hrg : RegionOk cache t) :
    ∃ t', Steps image t 20 20 t' ∧ LayHead S cache idx 4 M t' ∧ (∀ z, t'.getMem z = t.getMem z) ∧
      RegsEq t t' [.x7, .x8, .x18, .x26, .x27] := by
  have hs := symRun_sound blk296 codeAt_296 t tpc (by simp only [blk296.res, rv_simp])
  have hc : blk296.res.cycles = 20 := rfl
  have hk : blk296.res.steps = 20 := rfl
  rw [hc, hk] at hs
  set t' := blk296.res.toState t with ht'
  have m : ∀ z, t'.getMem z = t.getMem z := fun z => by
    rw [ht', Result.toState_getMem, show blk296.res.st.mem = [] from rfl, memEval_nil]
  have r : RegsEq t t' [.x7, .x8, .x18, .x26, .x27] := by
    intro q hq; rw [ht', Result.toState_getReg]
    cases q <;> first | exact absurd (by decide) hq | rfl
  have f : Frame t t' (fun _ => False) := fun a _ _ => m _
  refine ⟨t', hs, ⟨by norm_num, hidx, hM, by simp only [ht', blk296.res, rv_simp],
    by rw [r.get .x5, t5], by simp only [ht', blk296.res, rv_simp]; rfl, by simp only [ht', blk296.res, rv_simp],
    by simp only [ht', blk296.res, rv_simp], by rw [r.get .x22, t22],
    by simp only [ht', blk296.res, rv_simp], by simp only [ht', blk296.res, rv_simp],
    by rw [readWords_congr t t' _ 2 (fun k _ => m _), heb],
    hst.frame f (fun _ _ h => h), hrg.frame f (fun _ _ h => h)⟩, m, r⟩

theorem pack_full : (packTab.drop 0).take 490 = packTab := by
  rw [List.drop_zero]; exact List.take_of_length_le (by rw [packTab_length])

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

theorem stage_body_bytes (t : MachineState) (l : Nat) (hl : l < 5) (ls : LayerSig) (h : StageAt t l ls) :
    bytesAt t (0x900 + 856 * l + 8) (672 + 16 * height l) = ls.2.1.flatten ++ ls.2.2.flatten := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  have hh := height_le l (by omega)
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

/-- The staged counter word read by the trailer pack. -/
theorem ctrW_stage (t : MachineState) (l : Nat) (hl : l < 5) (ls : LayerSig) (h : StageAt t l ls) :
    ctrW t (0x900 + 856 * l) = BitVec.ofNat 64 ls.1 := by
  obtain ⟨h1, h2, _⟩ := h
  have ha : (0x900 + 856 * l) % 8 = 0 := by omega
  have hb : 0x900 + 856 * l < 2 ^ 64 := by omega
  apply BitVec.eq_of_toNat_eq
  rw [ctrW, alignToDword_ofNat_aligned hb ha, byteOffset_ofNat hb, ha, h1, lwuW_toNat]
  simp only [BitVec.toNat_ofNat, Nat.zero_div, Nat.mul_zero, Nat.pow_zero, Nat.div_one]
  rw [Nat.mod_eq_of_lt (show ls.1 < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show ls.1 < 2 ^ 32 by omega)]

theorem leBytes_add' (a b v : Nat) :
    leBytes (a + b) v = leBytes a v ++ leBytes b (v / 256 ^ a) := by
  unfold leBytes
  rw [List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply, Nat.pow_add, Nat.div_div_eq_div_mul]

theorem leBytes_take (a b v : Nat) : (leBytes (a + b) v).take a = leBytes a v := by
  rw [leBytes_add', List.take_left' (by simp [leBytes])]

theorem leBytes_drop (a b v : Nat) : (leBytes (a + b) v).drop a = leBytes b (v / 256 ^ a) := by
  rw [leBytes_add', List.drop_left' (by simp [leBytes])]

set_option maxRecDepth 100000 in
/-- `packCounters` of a 5-element counter list, unfolded. -/
theorem packCounters_five (c0 c1 c2 c3 c4 : Nat) (h0 : c0 < 2 ^ 22) (h1 : c1 < 2 ^ 22)
    (h2 : c2 < 2 ^ 22) (h3 : c3 < 2 ^ 22) (h4 : c4 < 2 ^ 22) :
    packCounters [c0, c1, c2, c3, c4] = c0 + c1 * 2 ^ 22 + c2 * 2 ^ 44 + c3 * 2 ^ 66 + c4 * 2 ^ 88 := by
  simp only [packCounters, List.foldr_cons, List.foldr_nil, Nat.mod_eq_of_lt h0, Nat.mod_eq_of_lt h1,
    Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt h3, Nat.mod_eq_of_lt h4]
  ring

theorem map_fst_five (lays : List LayerSig) (hll : lays.length = 5) :
    lays.map (·.1) = [lays[0].1, lays[1].1, lays[2].1, lays[3].1, lays[4].1] := by
  apply List.ext_getElem (by simp [hll])
  intro i h1 h2
  simp only [List.length_map, hll] at h1
  simp only [List.getElem_map]
  interval_cases i <;> rfl

/-- The two trailer dwords written by the pack, as a function of the five counters. -/
theorem trailer_words (t : MachineState) (lays : List LayerSig) (hll : lays.length = 5)
    (hst : ∀ l (hl : l < lays.length), StageAt t l lays[l]) :
    packDW t (3, 0x900, 0) = BitVec.ofNat 64 (packCounters (lays.map (·.1)) % 2 ^ 64) ∧
    packDW t (4, 0x900, 0) = BitVec.ofNat 64 (packCounters (lays.map (·.1)) / 2 ^ 64) := by
  have c0 := ctrW_stage t 0 (by omega) lays[0] (hst 0 (by omega))
  have c1 := ctrW_stage t 1 (by omega) lays[1] (hst 1 (by omega))
  have c2 := ctrW_stage t 2 (by omega) lays[2] (hst 2 (by omega))
  have c3 := ctrW_stage t 3 (by omega) lays[3] (hst 3 (by omega))
  have c4 := ctrW_stage t 4 (by omega) lays[4] (hst 4 (by omega))
  have b0 : lays[0].1 < 2 ^ 22 := (hst 0 (by omega)).2.1
  have b1 : lays[1].1 < 2 ^ 22 := (hst 1 (by omega)).2.1
  have b2 : lays[2].1 < 2 ^ 22 := (hst 2 (by omega)).2.1
  have b3 : lays[3].1 < 2 ^ 22 := (hst 3 (by omega)).2.1
  have b4 : lays[4].1 < 2 ^ 22 := (hst 4 (by omega)).2.1
  rw [map_fst_five lays hll, packCounters_five _ _ _ _ _ b0 b1 b2 b3 b4]
  have s22 : ((22#64).toNat % 64) = 22 := rfl
  have s44 : ((44#64).toNat % 64) = 44 := rfl
  have s20 : ((20#64).toNat % 64) = 20 := rfl
  have s2 : ((2#64).toNat % 64) = 2 := rfl
  have s24 : ((24#64).toNat % 64) = 24 := rfl
  constructor
  · show ctrW t 0x900 + ctrW t (0x900 + 856) <<< _ + ctrW t (0x900 + 1712) <<< _ = _
    rw [show (0x900 : Nat) = 0x900 + 856 * 0 from rfl, show (0x900 + 856 : Nat) = 0x900 + 856 * 1 from rfl,
      show (0x900 + 1712 : Nat) = 0x900 + 856 * 2 from rfl, c0, c1, c2]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_shiftLeft, s22, s44]
    simp only [BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.reducePow] at b0 b1 b2 b3 b4 ⊢
    omega
  · show ctrW t (0x900 + 1712) >>> _ + ctrW t (0x900 + 2568) <<< _ + ctrW t (0x900 + 3424) <<< _ = _
    rw [show (0x900 + 1712 : Nat) = 0x900 + 856 * 2 from rfl,
      show (0x900 + 2568 : Nat) = 0x900 + 856 * 3 from rfl,
      show (0x900 + 3424 : Nat) = 0x900 + 856 * 4 from rfl, c2, c3, c4]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft,
      BitVec.toNat_shiftLeft, s20, s2, s24]
    simp only [BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Nat.reducePow]
      at b0 b1 b2 b3 b4 ⊢
    omega

theorem bytesAt_take (t : MachineState) (a n m : Nat) (h : m ≤ n) :
    (bytesAt t a n).take m = bytesAt t a m := by
  apply List.ext_getElem (by simp; omega)
  intro i h1 h2
  simp [bytesAt]

theorem packTab_drop_488 : packTab.drop 488 = [(3, 0x900, 0), (4, 0x900, 0)] := by
  decide +kernel

theorem wordsOf_leBytes16 (PC : Nat) (hPC : PC / 2 ^ 64 < 2 ^ 64) :
    wordsOf (leBytes 16 PC) = [BitVec.ofNat 64 (PC % 2 ^ 64), BitVec.ofNat 64 (PC / 2 ^ 64)] := by
  rw [show (16 : Nat) = 8 + 8 from rfl, leBytes_add', wordsOf_append _ _ (by simp [leBytes]),
    wordsOf_eight _ (by simp [leBytes]), wordsOf_eight _ (by simp [leBytes]),
    leNat_leBytes, leNat_leBytes]
  have h1 : (256 : Nat) ^ 8 = 2 ^ 64 := by norm_num
  rw [h1, Nat.mod_eq_of_lt hPC]
  rfl

theorem trailer_bytes (t u : MachineState) (lays : List LayerSig) (hll : lays.length = 5)
    (hst : ∀ l (hl : l < lays.length), StageAt t l lays[l])
    (hw : u.readWords (BitVec.ofNat 64 (0x3300 + 2176)) 490 = packTab.map (packDW t)) :
    bytesAt u (0x3300 + 6080) 14 = leBytes 14 (packCounters (lays.map (·.1))) := by
  obtain ⟨hw0, hw1⟩ := trailer_words t lays hll hst
  have b0 : lays[0].1 < 2 ^ 22 := (hst 0 (by omega)).2.1
  have b1 : lays[1].1 < 2 ^ 22 := (hst 1 (by omega)).2.1
  have b2 : lays[2].1 < 2 ^ 22 := (hst 2 (by omega)).2.1
  have b3 : lays[3].1 < 2 ^ 22 := (hst 3 (by omega)).2.1
  have b4 : lays[4].1 < 2 ^ 22 := (hst 4 (by omega)).2.1
  have hPC : packCounters (lays.map (·.1)) =
      lays[0].1 + lays[1].1 * 2 ^ 22 + lays[2].1 * 2 ^ 44 + lays[3].1 * 2 ^ 66 +
        lays[4].1 * 2 ^ 88 := by rw [map_fst_five lays hll, packCounters_five _ _ _ _ _ b0 b1 b2 b3 b4]
  have hPC64 : packCounters (lays.map (·.1)) / 2 ^ 64 < 2 ^ 64 := by
    have : packCounters (lays.map (·.1)) < 2 ^ 110 := by omega
    omega
  have h2 : u.readWords (BitVec.ofNat 64 (0x3300 + 6080)) 2 =
      [BitVec.ofNat 64 (packCounters (lays.map (·.1)) % 2 ^ 64),
       BitVec.ofNat 64 (packCounters (lays.map (·.1)) / 2 ^ 64)] := by
    have hw' := hw
    rw [show (490 : Nat) = 488 + 2 from rfl, readWords_ofNat_add,
      show (0x3300 + 2176 + 8 * 488 : Nat) = 0x3300 + 6080 from rfl] at hw'
    have hlen : (u.readWords (BitVec.ofNat 64 (0x3300 + 2176)) 488).length = 488 :=
      readWords_length _ _ _
    have hdrop := congrArg (List.drop 488) hw'
    rw [List.drop_left' hlen, ← List.map_drop, packTab_drop_488] at hdrop
    rw [hdrop]
    simp only [List.map_cons, List.map_nil, hw0, hw1]
  have h16 : bytesAt u (0x3300 + 6080) 16 = leBytes 16 (packCounters (lays.map (·.1))) := by
    have h := bytesAt_of_readWords u 2 (0x3300 + 6080) (leBytes 16 (packCounters (lays.map (·.1))))
      (by omega) (by omega) (by simp [leBytes]) (by rw [wordsOf_leBytes16 _ hPC64]; exact h2)
    rw [show 8 * 2 = (16 : Nat) from rfl] at h
    exact h
  rw [← bytesAt_take u (0x3300 + 6080) 16 14 (by omega), h16,
    show (16 : Nat) = 14 + 2 from rfl, leBytes_take]

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
theorem final_bytes (t4 : MachineState) (rho : Val) (fts : List Val) (lays : List LayerSig)
    (hhead : bytesAt t4 0x3300 2176 = rho ++ fts.flatten)
    (hll : lays.length = 5) (hst : ∀ l (hl : l < lays.length), StageAt t4 l lays[l]) (t5 : MachineState)
    (hw5 : t5.readWords (BitVec.ofNat 64 (0x3300 + 2176)) 490 = packTab.map (packDW t4))
    (hf5 : Frame t4 t5 (fun x => packD ≤ x ∧ x < packD + 8 * 490)) :
    bytesAt t5 0x3300 6094 = serialize rho fts lays := by
  rw [show (6094 : Nat) = 2176 + (3904 + 14) from rfl, bytesAt_add, bytesAt_add,
    pack_layers t4 t5 hw5, trailer_bytes t4 t5 lays hll hst hw5]
  unfold serialize
  rw [← List.append_assoc]
  congr 1
  · congr 1
    · rw [← hhead]
      unfold bytesAt; apply List.map_congr_left; intro i hi
      simp only [List.mem_range] at hi
      simp only [MachineState.getByte]
      have h8 : alignToDword (BitVec.ofNat 64 (0x3300 + i)) = BitVec.ofNat 64 ((0x3300 + i) / 8 * 8) := by
        rw [← alignToDword_ofNat_aligned (x := (0x3300 + i) / 8 * 8) (by omega) (by omega)]
        exact (alignToDword_ofNat_eq (by omega) (by omega)).mpr (by omega)
      rw [h8, hf5.getMem (by omega) (by simp only [packD]; omega)]
    · rw [← hll]
      refine flatMap_range_eq lays _ _ (fun l hl => ?_)
      exact stage_body_bytes t4 l (by omega) lays[l] (hst l hl)

end SigGolfCandidate.Sign
