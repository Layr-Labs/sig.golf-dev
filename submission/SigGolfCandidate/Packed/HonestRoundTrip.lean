import SigGolfCandidate.Packed.ByteCodec
import SigGolfCandidate.Packed.SignerRange

namespace SigGolfCandidate.Packed

open SigGolfCandidate.Legacy SigGolfCandidate.Ref OracleComp OracleSpec

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

theorem shrinkAny_eq_honest (q : BitVec 160) (h : CanonicalCounterBlock q) :
    shrinkCounterBlockAny q = shrinkCounterBlockHonest q := by
  have h0 := h.1
  have hz : q.extractLsb' 22 2 = 0#2 := by
    have hz' := congrArg (fun z : BitVec 10 => z.setWidth 2) h0
    simpa [BitVec.setWidth_extractLsb'_of_le (show 2 ≤ 10 by decide)] using hz'
  have h24 : q.extractLsb' 0 24 = (0#2) ++ q.extractLsb' 0 22 := by
    calc
      q.extractLsb' 0 24 = q.extractLsb' 22 2 ++ q.extractLsb' 0 22 := by
        simpa only [Nat.reduceAdd] using
          (BitVec.extractLsb'_append_extractLsb'_eq_extractLsb'
            (x := q) (show 22 = 0 + 22 by decide)).symm
      _ = _ := by rw [hz]
  unfold shrinkCounterBlockAny shrinkCounterBlockHonest
  rw [h24]

theorem expand_shrinkAny_canonical (w : Bytes 6404) (h : CanonicalWitness w) :
    expandWitness (shrinkWitnessAny w) = w := by
  have heq : shrinkWitnessAny w = shrinkWitnessHonest w := by
    unfold shrinkWitnessAny shrinkWitnessHonest
    rw [shrinkAny_eq_honest _ h]
  rw [heq]
  exact expand_shrinkWitnessHonest w h

theorem unpack_packOldAny (σ : Bytes 6404)
    (h : CanonicalWitness (Ref.expandRef σ)) :
    unpackOld (packOldAny σ) = σ := by
  unfold unpackOld packOldAny
  rw [expand_shrinkAny_canonical _ h, Ref.unexpandRef_expandRef]

theorem leNat_drop (l : List Byte) (k : Nat) :
    Ref.leNat (l.drop k) = Ref.leNat l / 256 ^ k := by
  induction l generalizing k with
  | nil => simp [Ref.leNat]
  | cons b bs ih =>
      cases k with
      | zero => simp
      | succ k =>
          simp only [List.drop_succ_cons, Ref.leNat, Nat.pow_succ]
          rw [ih]
          have hb := b.isLt
          rw [Nat.mul_comm (256 ^ k) 256, ← Nat.div_div_eq_div_mul,
            show (b.toNat + 256 * Ref.leNat bs) / 256 = Ref.leNat bs by omega]

theorem leNat_take (l : List Byte) (k : Nat) :
    Ref.leNat (l.take k) = Ref.leNat l % 256 ^ k := by
  induction l generalizing k with
  | nil => simp [Ref.leNat]
  | cons b bs ih =>
      cases k with
      | zero => simp [Ref.leNat, Nat.mod_one]
      | succ k =>
          simp only [List.take_succ_cons, Ref.leNat, Nat.pow_succ]
          rw [ih]
          have hb := b.isLt
          have hpow : 0 < 256 ^ k := pow_pos (by omega) _
          have hr := Nat.mod_lt (Ref.leNat bs) hpow
          have hn := Nat.mod_add_div (Ref.leNat bs) (256 ^ k)
          have hmul : 256 * Ref.leNat bs = 256 * (Ref.leNat bs % 256 ^ k) +
              (256 * 256 ^ k) * (Ref.leNat bs / 256 ^ k) := by
            calc
              256 * Ref.leNat bs = 256 * (Ref.leNat bs % 256 ^ k +
                256 ^ k * (Ref.leNat bs / 256 ^ k)) := by rw [hn]
              _ = _ := by ring
          rw [hmul, ← Nat.add_assoc]
          rw [show 256 ^ k * 256 = 256 * 256 ^ k by omega,
            Nat.add_mul_mod_self_left]
          exact (Nat.mod_eq_of_lt (by nlinarith)).symm

theorem leNat_slice (l : List Byte) (off len : Nat) :
    Ref.leNat (Ref.slice l off len) = Ref.leNat l / 256 ^ off % 256 ^ len := by
  simp [Ref.slice, leNat_take, leNat_drop]

theorem leNat_slice_toList {n : Nat} (x : Bytes n) (off len : Nat) :
    Ref.leNat (Ref.slice (Ref.toList x) off len) =
      x.toNat / 2 ^ (8 * off) % 2 ^ (8 * len) := by
  rw [leNat_slice, Ref.leNat_toList]
  simp only [Nat.pow_mul]

theorem witCounter_toNat_block (w : Bytes 6404) (lay : Nat) :
    Ref.witCounter (Ref.toList w) lay =
      ((w.extractLsb' bodyBits 160).extractLsb' (32 * lay) 32).toNat := by
  let q := w.extractLsb' bodyBits 160
  have hsplit := toList_splitWitness w
  have hbody : (Ref.toList (w.extractLsb' 0 bodyBits)).length = 6384 :=
    Ref.length_toList _
  have hs : Ref.slice (Ref.toList w) (6384 + 4 * lay) 4 =
      Ref.slice (Ref.toList (n := 20) q) (4 * lay) 4 := by
    rw [hsplit]
    simp only [Ref.slice]
    rw [List.drop_append]
    have hd : (Ref.toList (w.extractLsb' 0 bodyBits)).drop (6384 + 4 * lay) = [] :=
      List.drop_eq_nil_iff.mpr (by omega)
    simp only [hd, List.nil_append, hbody, Nat.add_sub_cancel_left]
    rfl
  unfold Ref.witCounter
  rw [Ref.witCounters_eq, hs, leNat_slice_toList]
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  have hq : q.toNat = w.toNat / 2 ^ bodyBits % 2 ^ 160 := by
    simp only [q, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  rw [← hq]
  have hoff : 8 * (4 * lay) = 32 * lay := by omega
  rw [hoff]

theorem high_zero_of_word_bound (q : BitVec 160) (lay : Nat)
    (h : (q.extractLsb' (32 * lay) 32).toNat < 2 ^ 22) :
    q.extractLsb' (32 * lay + 22) 10 = 0 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  change q.toNat / 2 ^ (32 * lay + 22) % 2 ^ 10 = 0
  rw [pow_add, ← Nat.div_div_eq_div_mul]
  have h' : (q.toNat / 2 ^ (32 * lay)) % 2 ^ 32 < 2 ^ 22 := by
    simpa only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow] using h
  have hmod := Nat.mod_mul_right_div_self (q.toNat / 2 ^ (32 * lay)) (2 ^ 22) (2 ^ 10)
  have hpow : 2 ^ 22 * 2 ^ 10 = 2 ^ 32 := by norm_num
  rw [hpow] at hmod
  rw [← hmod]
  exact Nat.div_eq_zero_iff.mpr (Or.inr h')

theorem countersOk_to_canonical (w : Bytes 6404)
    (h : Ref.countersOk (Ref.toList w) = true) : CanonicalWitness w := by
  let q : BitVec 160 := w.extractLsb' bodyBits 160
  have hall := List.all_eq_true.mp h
  have hword (lay : Nat) (hlay : lay < 5) :
      (q.extractLsb' (32 * lay) 32).toNat < 2 ^ 22 := by
    have hc := hall lay (List.mem_range.mpr hlay)
    have hn : Ref.witCounter (Ref.toList w) lay < Ref.cMax := of_decide_eq_true hc
    rw [witCounter_toNat_block] at hn
    simpa only [q, Ref.cMax] using hn
  change q.extractLsb' 22 10 = 0 ∧ q.extractLsb' 54 10 = 0 ∧
    q.extractLsb' 86 10 = 0 ∧ q.extractLsb' 118 10 = 0 ∧ q.extractLsb' 150 10 = 0
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa using high_zero_of_word_bound q 0 (hword 0 (by decide))
  · simpa using high_zero_of_word_bound q 1 (hword 1 (by decide))
  · simpa using high_zero_of_word_bound q 2 (hword 2 (by decide))
  · simpa using high_zero_of_word_bound q 3 (hword 3 (by decide))
  · simpa using high_zero_of_word_bound q 4 (hword 4 (by decide))

theorem verifyRef_accept_canonical (m : Message) (pk : PublicKey)
    (w : Bytes 6404) (h : true ∈ support (Ref.verifyRef m pk w)) :
    CanonicalWitness w := by
  by_cases hc : Ref.countersOk (Ref.toList w) = true
  · exact countersOk_to_canonical w hc
  · have hfalse : Ref.countersOk (Ref.toList w) = false := Bool.eq_false_iff.mpr hc
    simp only [Ref.verifyRef, Ref.verifyList, hfalse, Bool.not_false, if_true,
      support_pure, Set.mem_singleton_iff] at h
    cases h

end SigGolfCandidate.Packed
