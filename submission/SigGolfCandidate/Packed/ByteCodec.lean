import SigGolfCandidate.Packed.WordCodec
import SigGolfCandidate.Expand.Mem

/-!
# Byte-list view of packed bitvector concatenation
-/

namespace SigGolfCandidate.Packed

open SigGolfCandidate.Legacy SigGolfCandidate.Ref
open SigGolfCandidate.Mem
set_option maxHeartbeats 1000000

theorem leNat_append_bytes (a b : List Byte) :
    leNat (a ++ b) = leNat a + 2 ^ (8 * a.length) * leNat b := by
  induction a with
  | nil => simp [leNat]
  | cons x xs ih =>
      simp only [List.cons_append, leNat, ih, List.length_cons]
      rw [show 8 * (xs.length + 1) = 8 + 8 * xs.length by ring, Nat.pow_add]
      ring

theorem ofList_concat {n m : Nat} (low : Bytes n) (high : Bytes m) :
    ofList (n + m) (toList low ++ toList high) =
      (high ++ low).cast (by omega : 8 * m + 8 * n = 8 * (n + m)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [ofList, BitVec.toNat_ofNat, leNat_append_bytes,
    length_toList, leNat_toList, BitVec.toNat_cast, BitVec.toNat_append]
  rw [← Nat.shiftLeft_add_eq_or_of_lt (by
    have := low.isLt
    simpa only [Nat.pow_mul] using this)]
  simp only [Nat.shiftLeft_eq, Nat.mul_comm]
  have hl := low.isLt
  have hh := high.isLt
  have hbound : low.toNat + 2 ^ (8 * n) * high.toNat <
      2 ^ (8 * (n + m)) := by
    calc
      _ < 2 ^ (8 * n) * (high.toNat + 1) := by
        have h := Nat.add_lt_add_right hl (2 ^ (8 * n) * high.toNat)
        simpa [mul_add, add_comm, add_left_comm, add_assoc] using h
      _ ≤ 2 ^ (8 * n) * 2 ^ (8 * m) :=
        Nat.mul_le_mul_left _ (Nat.succ_le_iff.mpr hh)
      _ = _ := by rw [← Nat.pow_add]; congr 1; ring
  simp only [show n * 8 = 8 * n by ring,
    show (n + m) * 8 = 8 * (n + m) by ring]
  rw [Nat.mod_eq_of_lt (by simpa only [Nat.mul_comm] using hbound)]
  ring

theorem toList_concat {n m : Nat} (low : Bytes n) (high : Bytes m) :
    toList ((high ++ low).cast (by omega : 8 * m + 8 * n = 8 * (n + m))) =
      toList low ++ toList high := by
  rw [← ofList_concat low high, toList_ofList]
  simp only [List.length_append, length_toList]

theorem toList_expandWitness (b : Bytes 6398) :
    toList (expandWitness b) =
      toList (body b) ++ toList (n := 20) (expandCounterBlock (packedCounters b)) := by
  have h := toList_concat (n := 6384) (m := 20)
    (body b) (expandCounterBlock (packedCounters b))
  change toList (expandWitness b) =
    toList (body b) ++ toList (n := 20) (expandCounterBlock (packedCounters b))
  exact h

theorem toList_readBuffer (t : RiscvZkvm.Rv64.MachineState) (addr n : Nat) :
    toList (SigGolfCandidate.Legacy.readBuffer t addr n) =
      (List.range n).map (fun i => t.getByte (BitVec.ofNat 64 (addr + i))) := by
  rw [readBuffer_eq]
  change toList (ofList n ((List.range n).map
    (fun i => t.getByte (BitVec.ofNat 64 (addr + i))))) = _
  exact toList_ofList n _ (by simp)

theorem readBuffer_byte (t : RiscvZkvm.Rv64.MachineState)
    (addr n i : Nat) (hi : i < n) :
    (toList (SigGolfCandidate.Legacy.readBuffer t addr n)).getD i 0 =
      t.getByte (BitVec.ofNat 64 (addr + i)) := by
  rw [toList_readBuffer]
  simp [List.getD_eq_getElem?_getD, hi]

theorem readBuffer_eq_of_bytes (t : RiscvZkvm.Rv64.MachineState)
    (addr : Nat) {n : Nat} (x : Bytes n)
    (h : ∀ i < n, t.getByte (BitVec.ofNat 64 (addr + i)) =
      (toList x).getD i 0) :
    SigGolfCandidate.Legacy.readBuffer t addr n = x := by
  rw [readBuffer_eq, ← ofList_toList x]
  change ofList n ((List.range n).map
    (fun i => t.getByte (BitVec.ofNat 64 (addr + i)))) = ofList n (toList x)
  congr 1
  apply List.ext_getElem (by simp [length_toList])
  intro i hi hi'
  simp only [List.getElem_map, List.getElem_range]
  rw [h i (by simpa using hi)]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some]

theorem toList_splitWitness (w : Bytes 6404) :
    toList w = toList (w.extractLsb' 0 bodyBits) ++
      toList (n := 20) (w.extractLsb' bodyBits 160) := by
  have h := toList_concat (n := 6384) (m := 20) (w.extractLsb' 0 bodyBits)
    (w.extractLsb' bodyBits 160)
  have hsplit : w.extractLsb' bodyBits 160 ++ w.extractLsb' 0 bodyBits = w := by
    simpa only [bodyBits] using
      (BitVec.extractLsb'_append_extractLsb' (x := w) (w := 160) (len := 8 * 6384))
  simpa only [hsplit, bodyBits, BitVec.cast_eq] using h

theorem toList_witnessBody (w : Bytes 6404) :
    toList (w.extractLsb' 0 bodyBits) = (toList w).take 6384 := by
  rw [toList_splitWitness]
  simp [length_toList]

theorem toList_witnessCounters (w : Bytes 6404) :
    toList (n := 20) (w.extractLsb' bodyBits 160) = (toList w).drop 6384 := by
  rw [toList_splitWitness]
  simp [length_toList]

theorem witnessBody_byte (w : Bytes 6404) (i : Nat) (hi : i < 6384) :
    (toList (w.extractLsb' 0 bodyBits)).getD i 0 = (toList w).getD i 0 := by
  rw [toList_witnessBody]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, if_pos hi]

theorem witnessCounter_byte (w : Bytes 6404) (i : Nat) (hi : i < 20) :
    (toList (n := 20) (w.extractLsb' bodyBits 160)).getD i 0 =
      (toList w).getD (6384 + i) 0 := by
  rw [toList_witnessCounters]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem readBuffer_witnessCounters (t : RiscvZkvm.Rv64.MachineState) :
    SigGolfCandidate.Legacy.readBuffer t 0x20F0 20 =
      (SigGolfCandidate.Legacy.readBuffer t 0x800 6404).extractLsb' bodyBits 160 := by
  apply readBuffer_eq_of_bytes
  intro i hi
  rw [witnessCounter_byte _ i hi,
    readBuffer_byte t 0x800 6404 (6384 + i) (by omega)]
  have heq : 0x20F0 + i = 0x800 + (6384 + i) := by omega
  rw [heq]

theorem toList_splitShort (b : Bytes 6398) :
    toList b = toList (body b) ++ toList (n := 14) (packedCounters b) := by
  have h := toList_concat (n := 6384) (m := 14) (body b) (packedCounters b)
  have hj := join_parts b
  calc
    toList b = toList (join (packedCounters b) (body b)) := congrArg toList hj.symm
    _ = _ := by simpa only [join, BitVec.cast_eq] using h

theorem toList_shortBody (b : Bytes 6398) :
    toList (body b) = (toList b).take 6384 := by
  rw [toList_splitShort]
  simp [length_toList]

theorem toList_shortCounters (b : Bytes 6398) :
    toList (n := 14) (packedCounters b) = (toList b).drop 6384 := by
  rw [toList_splitShort]
  simp [length_toList]

theorem shortBody_byte (b : Bytes 6398) (i : Nat) (hi : i < 6384) :
    (toList (body b)).getD i 0 = (toList b).getD i 0 := by
  rw [toList_shortBody]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, if_pos hi]

theorem shortCounter_byte (b : Bytes 6398) (i : Nat) (_hi : i < 14) :
    (toList (n := 14) (packedCounters b)).getD i 0 =
      (toList b).getD (6384 + i) 0 := by
  rw [toList_shortCounters]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem body_shrinkWitnessAny (w : Bytes 6404) :
    body (shrinkWitnessAny w) = w.extractLsb' 0 bodyBits := by
  simp only [body, shrinkWitnessAny, BitVec.extractLsb'_append_eq_right]

theorem packedCounters_shrinkWitnessAny (w : Bytes 6404) :
    packedCounters (shrinkWitnessAny w) =
      shrinkCounterBlockAny (w.extractLsb' bodyBits 160) := by
  simp only [packedCounters, shrinkWitnessAny, BitVec.extractLsb'_append_eq_left]

theorem readBuffer_shortCounters (t : RiscvZkvm.Rv64.MachineState) :
    SigGolfCandidate.Legacy.readBuffer t 0x3F40 14 =
      packedCounters (SigGolfCandidate.Legacy.readBuffer t 0x2650 6398) := by
  apply readBuffer_eq_of_bytes
  intro i hi
  rw [shortCounter_byte _ i hi,
    readBuffer_byte t 0x2650 6398 (6384 + i) (by omega)]
  have heq : 0x3F40 + i = 0x2650 + (6384 + i) := by omega
  rw [heq]

theorem expandWitness_body_byte (b : Bytes 6398) (i : Nat) (hi : i < 6384) :
    (toList (expandWitness b)).getD i 0 = (toList (body b)).getD i 0 := by
  rw [toList_expandWitness]
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by rw [length_toList]; exact hi)]

theorem expandWitness_counter_byte (b : Bytes 6398) (i : Nat) (_hi : i < 20) :
    (toList (expandWitness b)).getD (6384 + i) 0 =
      (toList (n := 20) (expandCounterBlock (packedCounters b))).getD i 0 := by
  rw [toList_expandWitness]
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by rw [length_toList]; omega)]
  simp only [length_toList, Nat.add_sub_cancel_left]

end SigGolfCandidate.Packed
