import SigGolfCandidate.Packed.Codec
import Mathlib.Tactic

/-!
# Word-level equations for the RV64 packed trailer

These are the values computed by the two machine-code trailer blocks.
The two high bytes of the second stored word are outside the signature.
-/

namespace SigGolfCandidate.Packed

set_option maxHeartbeats 1000000

def counterWord (q : BitVec 160) (i : Nat) : BitVec 64 :=
  (q.extractLsb' (32 * i) 32).setWidth 64

def packLoWord (q : BitVec 160) : BitVec 64 :=
  ((counterWord q 0 <<< 40) >>> 40) |||
  ((counterWord q 1 <<< 42) >>> 18) |||
  (counterWord q 2 <<< 46)

def packHiWord (q : BitVec 160) : BitVec 64 :=
  ((counterWord q 2 >>> 18) &&& 15) |||
  ((counterWord q 3 <<< 42) >>> 38) |||
  ((counterWord q 4 <<< 42) >>> 16)

def unpackCounterWords (lo hi : BitVec 64) : BitVec 160 :=
  (((hi <<< 16) >>> 42).setWidth 32) ++
  (((hi <<< 38) >>> 42).setWidth 32) ++
  (((lo >>> 46) ||| ((hi <<< 60) >>> 42)).setWidth 32) ++
  (((lo <<< 18) >>> 42).setWidth 32) ++
  (((lo <<< 40) >>> 40).setWidth 32)

theorem packWords_eq_shrinkAny (q : BitVec 160) :
    (packHiWord q).extractLsb' 0 48 ++ packLoWord q =
      shrinkCounterBlockAny q := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi_i
  unfold packHiWord packLoWord counterWord shrinkCounterBlockAny
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_extractLsb', BitVec.getLsbD_append,
    BitVec.getLsbD_setWidth]
  interval_cases i <;> norm_num <;>
    simp [BitVec.getElem_eq_testBit_toNat, Nat.testBit]

theorem unpackWords_eq_expand (lo hi : BitVec 64) :
    unpackCounterWords lo hi =
      expandCounterBlock ((hi.extractLsb' 0 48) ++ lo) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi_i
  unfold unpackCounterWords expandCounterBlock
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_append, BitVec.getLsbD_setWidth]
  interval_cases i <;> norm_num

theorem unpack_packWords (q : BitVec 160) :
    unpackCounterWords (packLoWord q) (packHiWord q) =
      expandCounterBlock (shrinkCounterBlockAny q) := by
  rw [unpackWords_eq_expand, packWords_eq_shrinkAny]

end SigGolfCandidate.Packed
