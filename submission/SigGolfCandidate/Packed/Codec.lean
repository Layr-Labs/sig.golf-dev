import SigGolfCandidate.Ref.Lemmas
import Std.Tactic.BVDecide

/-!
# Lossless packed counter codec

The first 6384 bytes of the packed signature are the unchanged witness body. The
last 14 bytes hold five counters: 24 bits for counter zero and 22 bits for each
remaining counter. Bits 22 and 23 of counter zero are padding. They are retained
by expansion, so a nonzero padding value becomes an out-of-range counter and is
rejected by the existing verifier. In particular, expansion is injective on *all*
packed signatures, which is needed for strong unforgeability.
-/

namespace SigGolfCandidate.Packed

open SigGolfCandidate.Legacy

set_option maxHeartbeats 1000000

abbrev sizes : Sizes := ⟨6398, 6404, CACHE_BYTES⟩

abbrev bodyBits : Nat := 8 * 6384

def body (b : Bytes 6398) : Bytes 6384 := b.extractLsb' 0 bodyBits

def packedCounters (b : Bytes 6398) : BitVec 112 := b.extractLsb' bodyBits 112

def join (c : BitVec 112) (v : Bytes 6384) : Bytes 6398 := c ++ v

theorem join_parts (b : Bytes 6398) : join (packedCounters b) (body b) = b := by
  simpa only [join, packedCounters, body, bodyBits] using
    (BitVec.extractLsb'_append_extractLsb' (x := b) (w := 112) (len := 8 * 6384))

/-- The five packed counters become ordinary little-endian 32-bit words. -/
def expandCounterBlock (p : BitVec 112) : BitVec 160 :=
  (p.extractLsb' 90 22).setWidth 32 ++
  (p.extractLsb' 68 22).setWidth 32 ++
  (p.extractLsb' 46 22).setWidth 32 ++
  (p.extractLsb' 24 22).setWidth 32 ++
  (p.extractLsb' 0 24).setWidth 32

/-- An inverse on every expanded counter block, including nonzero padding bits. -/
def shrinkCounterBlockAny (q : BitVec 160) : BitVec 112 :=
  q.extractLsb' 128 22 ++ q.extractLsb' 96 22 ++ q.extractLsb' 64 22 ++
  q.extractLsb' 32 22 ++ q.extractLsb' 0 24

/-- The signer writes zero in the two padding bits. -/
def shrinkCounterBlockHonest (q : BitVec 160) : BitVec 112 :=
  q.extractLsb' 128 22 ++ q.extractLsb' 96 22 ++ q.extractLsb' 64 22 ++
  q.extractLsb' 32 22 ++ ((0#2) ++ q.extractLsb' 0 22)

theorem shrinkAny_expand (p : BitVec 112) :
    shrinkCounterBlockAny (expandCounterBlock p) = p := by
  unfold shrinkCounterBlockAny expandCounterBlock
  bv_normalize

/-- A canonical signer output has all five counters below `2^22`. -/
def CanonicalCounterBlock (q : BitVec 160) : Prop :=
  q.extractLsb' 22 10 = 0 ∧ q.extractLsb' 54 10 = 0 ∧
  q.extractLsb' 86 10 = 0 ∧ q.extractLsb' 118 10 = 0 ∧
  q.extractLsb' 150 10 = 0

theorem expand_shrinkHonest (q : BitVec 160) (h : CanonicalCounterBlock q) :
    expandCounterBlock (shrinkCounterBlockHonest q) = q := by
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  unfold expandCounterBlock shrinkCounterBlockHonest
  bv_normalize
  simp_all
  rename_i hneq
  apply hneq
  nth_rewrite 1 [← h4]
  nth_rewrite 1 [← h3]
  nth_rewrite 1 [← h2]
  nth_rewrite 1 [← h1]
  nth_rewrite 1 [← h0]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (show 150 = 128 + 22 by decide)]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (show 118 = 96 + 22 by decide)]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (show 86 = 64 + 22 by decide)]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (show 54 = 32 + 22 by decide)]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (show 22 = 0 + 22 by decide)]
  simp only [Nat.reduceAdd]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (show 128 = 96 + 32 by decide)]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (show 96 = 64 + 32 by decide)]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (show 64 = 32 + 32 by decide)]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (show 32 = 0 + 32 by decide)]
  simpa only [Nat.reduceAdd] using (BitVec.extractLsb'_eq_self (x := q))

/-- The packed signature expands directly into the existing 6404-byte witness. -/
def expandWitness (b : Bytes 6398) : Bytes 6404 :=
  expandCounterBlock (packedCounters b) ++ body b

def shrinkWitnessAny (w : Bytes 6404) : Bytes 6398 :=
  shrinkCounterBlockAny (w.extractLsb' bodyBits 160) ++ w.extractLsb' 0 bodyBits

/-- This inverse is used only on successful output of the old signer. -/
def shrinkWitnessHonest (w : Bytes 6404) : Bytes 6398 :=
  shrinkCounterBlockHonest (w.extractLsb' bodyBits 160) ++ w.extractLsb' 0 bodyBits

theorem shrinkAny_expandWitness (b : Bytes 6398) :
    shrinkWitnessAny (expandWitness b) = b := by
  simp only [shrinkWitnessAny, expandWitness, packedCounters, body,
    BitVec.extractLsb'_append_eq_left, BitVec.extractLsb'_append_eq_right,
    shrinkAny_expand]
  exact join_parts b

theorem expandWitness_injective : Function.Injective expandWitness := by
  intro x y h
  have h' := congrArg shrinkWitnessAny h
  simpa only [shrinkAny_expandWitness] using h'

def CanonicalWitness (w : Bytes 6404) : Prop :=
  CanonicalCounterBlock (w.extractLsb' bodyBits 160)

theorem expand_shrinkWitnessHonest (w : Bytes 6404) (h : CanonicalWitness w) :
    expandWitness (shrinkWitnessHonest w) = w := by
  simp only [expandWitness, shrinkWitnessHonest, packedCounters, body,
    BitVec.extractLsb'_append_eq_left, BitVec.extractLsb'_append_eq_right]
  rw [expand_shrinkHonest _ h]
  simpa only [bodyBits] using
    (BitVec.extractLsb'_append_extractLsb' (x := w) (w := 160) (len := 8 * 6384))

/-- The embedding into the old raw-signature type. -/
def unpackOld (b : Bytes 6398) : Bytes 6404 :=
  Ref.unexpandRef (expandWitness b)

def packOld (b : Bytes 6404) : Bytes 6398 :=
  shrinkWitnessHonest (Ref.expandRef b)

/-- The total compression map used by the security reduction. It preserves the
two padding bits of counter zero, so it is a left inverse of `unpackOld` on
every possible packed signature, including malformed ones. -/
def packOldAny (b : Bytes 6404) : Bytes 6398 :=
  shrinkWitnessAny (Ref.expandRef b)

theorem packAny_unpackOld (b : Bytes 6398) : packOldAny (unpackOld b) = b := by
  unfold packOldAny unpackOld
  rw [Ref.expandRef_unexpandRef, shrinkAny_expandWitness]

theorem expand_unpackOld (b : Bytes 6398) :
    Ref.expandRef (unpackOld b) = expandWitness b := by
  exact Ref.expandRef_unexpandRef _

theorem unpackOld_injective : Function.Injective unpackOld := by
  intro x y h
  apply expandWitness_injective
  simpa only [expand_unpackOld] using congrArg Ref.expandRef h

theorem unpack_packOld (b : Bytes 6404)
    (h : CanonicalWitness (Ref.expandRef b)) : unpackOld (packOld b) = b := by
  unfold unpackOld packOld
  rw [expand_shrinkWitnessHonest _ h, Ref.unexpandRef_expandRef]

end SigGolfCandidate.Packed
