import SigGolfCandidate.Sign.Head
import SigGolfCandidate.Sign.Layer
import SigGolfCandidate.Sign.Pack

/-!
# `sign`: layer-loop entry (296 .. 314) and the signature's layer bytes

* `layer_entry` : the layer constants (`LIM = 2^22`, the SWAR masks, `LAY = 5`, `SIGL` = stage 5).
* `stage_bytes`, `final_bytes` : the packed layer region `SIG + 2144 ..` from the stages.
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
    ∃ t', Steps image t 19 19 t' ∧ LayHead S cache idx 5 M t' ∧ (∀ z, t'.getMem z = t.getMem z) ∧
      RegsEq t t' [.x7, .x8, .x18, .x26, .x27] := by
  have hs := symRun_sound blk296 codeAt_296 t tpc (by simp only [blk296.res, rv_simp])
  have hc : blk296.res.cycles = 19 := rfl
  have hk : blk296.res.steps = 19 := rfl
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

/-- The 4 bytes at `a + 4` of an aligned dword whose high word is `c`. -/
theorem hi32_bytes (t : MachineState) (a c : Nat) (ha : a % 8 = 0) (hb : a + 8 < 2 ^ 64)
    (hc : c < 2 ^ 32) (h : hi32 (t.getMem (BitVec.ofNat 64 a)) = BitVec.ofNat 32 c) :
    bytesAt t (a + 4) 4 = le32 c := by
  have hw := congrArg BitVec.toNat h
  simp only [hi32, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hc] at hw
  apply List.ext_getElem (by simp [le32, leBytes])
  intro i h1 h2
  simp only [length_bytesAt] at h1
  simp only [bytesAt, List.getElem_map, List.getElem_range, le32, leBytes]
  rw [show a + 4 + i = a + (4 + i) by omega, getByte_aligned' t a (4 + i) ha (by omega) hb]
  apply BitVec.eq_of_toNat_eq
  rw [extractByte_toNat', byte_toNat]
  have hlt := (t.getMem (BitVec.ofNat 64 a)).isLt
  generalize (t.getMem (BitVec.ofNat 64 a)).toNat = w at hw hlt
  subst hw
  interval_cases i <;> norm_num <;> omega

/-- The staged bytes of layer `l` (counter word, chain values, path) as in the signature. -/
theorem stage_bytes (t : MachineState) (l : Nat) (hl : l < 6) (ls : LayerSig) (h : StageAt t l ls) :
    bytesAt t (0x904 + 696 * l) (516 + 16 * height l) = le32 ls.1 ++ ls.2.1.flatten ++ ls.2.2.flatten := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  have hh := height_le l (by omega)
  rw [show 516 + 16 * height l = 4 + (512 + 16 * height l) by ring, bytesAt_add,
    show 0x904 + 696 * l = (0x900 + 696 * l) + 4 by ring,
    hi32_bytes t _ ls.1 (by omega) (by omega) (by omega) h1, List.append_assoc]
  congr 1
  have hv : ∀ v ∈ ls.2.1 ++ ls.2.2, v.length = 16 := by
    intro v hv; rcases List.mem_append.mp hv with hv | hv; exact h4 v hv; exact h7 v hv
  have hsl : Slots t (0x900 + 696 * l + 8) (ls.2.1 ++ ls.2.2) :=
    Slots.append h5 (by rw [h3, show 0x900 + 696 * l + 8 + 16 * 32 = 0x900 + 696 * l + 520 by ring]; exact h8)
  have hw := readWords_slots t _ _ hsl
  rw [← wordsOf_flatten _ hv, List.flatten_append] at hw
  have hlen : (ls.2.1 ++ ls.2.2).length = 32 + height l := by simp [h3, h6]
  rw [show 0x900 + 696 * l + 4 + 4 = 0x900 + 696 * l + 8 by ring,
    show 512 + 16 * height l = 8 * (2 * (ls.2.1 ++ ls.2.2).length) by rw [hlen]; ring]
  refine bytesAt_of_readWords t _ _ _ (by omega) (by rw [hlen]; omega) ?_ hw
  rw [List.length_append, length_flatten_vals _ h4, length_flatten_vals _ h7, hlen, h3, h6]; ring

theorem packCopies_pairwise :
    packCopies.Pairwise (fun c c' => PkDisj c.2.1 (4 * c.2.2) c'.2.1 (4 * c'.2.2)) := by decide

theorem packCopies_disj :
    ∀ c ∈ packCopies, ∀ c' ∈ packCopies, PkDisj c.1 (4 * c.2.2) c'.2.1 (4 * c'.2.2) := by decide

/-- A copied region after the pack holds the bytes of its source before the pack. -/
theorem bytesAt_copy (t u : MachineState)
    (hb : PkBytesEq u (pkApplyCopies packCopies (fun a => t.getByte (BitVec.ofNat 64 a))))
    (src dst n : Nat) (hc : (src, dst, n) ∈ packCopies) :
    bytesAt u dst (4 * n) = bytesAt t src (4 * n) := by
  have hlt : dst + 4 * n < 2 ^ 64 := by
    simp only [packCopies, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hc
    omega
  unfold bytesAt
  apply List.map_congr_left
  intro i hi
  simp only [List.mem_range] at hi
  rw [hb _ (by omega), pk_applyCopies_hit packCopies _ packCopies_pairwise packCopies_disj _ hc _
    (by dsimp only; omega) (by dsimp only; omega)]
  dsimp only
  congr 2; omega

/-- Bytes below the first copy destination are not changed by the pack. -/
theorem bytesAt_nocopy (t u : MachineState)
    (hb : PkBytesEq u (pkApplyCopies packCopies (fun a => t.getByte (BitVec.ofNat 64 a))))
    (a n : Nat) (h : a + n ≤ 15200) :
    bytesAt u a n = bytesAt t a n := by
  unfold bytesAt
  apply List.map_congr_left
  intro i hi
  simp only [List.mem_range] at hi
  rw [hb _ (by omega), pk_applyCopies_frame packCopies _ _ (fun c hc => by
    simp only [packCopies, List.mem_cons, List.mem_nil_iff, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> (dsimp only; omega))]

set_option maxRecDepth 100000 in
/-- The signature bytes after the pack. -/
theorem final_bytes (t4 : MachineState) (rho : Val) (fts : List Val) (lays : List LayerSig)
    (hhead : bytesAt t4 0x3300 2144 = rho ++ fts.flatten)
    (hll : lays.length = 6) (hst : ∀ l (hl : l < lays.length), StageAt t4 l lays[l]) (t5 : MachineState)
    (hb5 : PkBytesEq t5 (pkApplyCopies packCopies (fun a => t4.getByte (BitVec.ofNat 64 a)))) :
    bytesAt t5 0x3300 5784 = serialize rho fts lays := by
  obtain ⟨L0, L1, L2, L3, L4, L5, rfl⟩ : ∃ L0 L1 L2 L3 L4 L5, lays = [L0, L1, L2, L3, L4, L5] := by
    rcases lays with _ | ⟨L0, _ | ⟨L1, _ | ⟨L2, _ | ⟨L3, _ | ⟨L4, _ | ⟨L5, _ | ⟨L6, rest⟩⟩⟩⟩⟩⟩⟩ <;>
      simp at hll
    exact ⟨L0, L1, L2, L3, L4, L5, rfl⟩
  have s0 := stage_bytes t4 0 (by norm_num) L0 (hst 0 (by simp))
  have s1 := stage_bytes t4 1 (by norm_num) L1 (hst 1 (by simp))
  have s2 := stage_bytes t4 2 (by norm_num) L2 (hst 2 (by simp))
  have s3 := stage_bytes t4 3 (by norm_num) L3 (hst 3 (by simp))
  have s4 := stage_bytes t4 4 (by norm_num) L4 (hst 4 (by simp))
  have s5 := stage_bytes t4 5 (by norm_num) L5 (hst 5 (by simp))
  rw [show 0x904 + 696 * 0 = 2308 from rfl, show 516 + 16 * height 0 = 4 * 173 from rfl] at s0
  rw [show 0x904 + 696 * 1 = 3004 from rfl, show 516 + 16 * height 1 = 4 * 149 from rfl] at s1
  rw [show 0x904 + 696 * 2 = 3700 from rfl, show 516 + 16 * height 2 = 4 * 149 from rfl] at s2
  rw [show 0x904 + 696 * 3 = 4396 from rfl, show 516 + 16 * height 3 = 4 * 149 from rfl] at s3
  rw [show 0x904 + 696 * 4 = 5092 from rfl, show 516 + 16 * height 4 = 4 * 145 from rfl] at s4
  rw [show 0x904 + 696 * 5 = 5788 from rfl, show 516 + 16 * height 5 = 4 * 145 from rfl] at s5
  have c0 := bytesAt_copy t4 t5 hb5 2308 15200 173 (by simp [packCopies])
  have c1 := bytesAt_copy t4 t5 hb5 3004 15892 149 (by simp [packCopies])
  have c2 := bytesAt_copy t4 t5 hb5 3700 16488 149 (by simp [packCopies])
  have c3 := bytesAt_copy t4 t5 hb5 4396 17084 149 (by simp [packCopies])
  have c4 := bytesAt_copy t4 t5 hb5 5092 17680 145 (by simp [packCopies])
  have c5 := bytesAt_copy t4 t5 hb5 5788 18260 145 (by simp [packCopies])
  rw [show (5784 : Nat) = 2144 + (4 * 173 + (4 * 149 + (4 * 149 + (4 * 149 + (4 * 145 + 4 * 145))))) from rfl,
    bytesAt_add, bytesAt_add, bytesAt_add, bytesAt_add, bytesAt_add, bytesAt_add,
    show 0x3300 + 2144 = 15200 from rfl, show 15200 + 4 * 173 = 15892 from rfl,
    show 15892 + 4 * 149 = 16488 from rfl, show 16488 + 4 * 149 = 17084 from rfl,
    show 17084 + 4 * 149 = 17680 from rfl, show 17680 + 4 * 145 = 18260 from rfl,
    c0, c1, c2, c3, c4, c5, s0, s1, s2, s3, s4, s5,
    bytesAt_nocopy t4 t5 hb5 0x3300 2144 (by norm_num), hhead]
  simp only [serialize, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
    List.append_nil, List.append_assoc]

end SigGolfCandidate.Sign
