import SigGolfCandidate.SphincsSecurity.Completeness.Search
import SigGolfCandidate.SphincsSecurity.Completeness.Counter
import SigGolfCandidate.SphincsSecurity.Completeness.Decay
import SigGolfCandidate.SphincsSecurity.Completeness.Encoding
import SigGolfCandidate.SphincsSecurity.Completeness.Signing
import SigGolfCandidate.SphincsSecurity.Completeness.Assembly
import SigGolfCandidate.Final.Abstract
import SigGolfCandidate.Final.Completeness
import Mathlib.Tactic
import Std.Tactic.BVDecide
import SigGolfCandidate.Packed.Codec
import SigGolfCandidate.Packed.HonestRoundTrip
import SigGolfCandidate.Packed.TypedRange
import SigGolfCandidate.Packed.Reduction
import SigGolfCandidate.Packed.ByteCodec
/-! Auto-collected 13-byte codec certificate. Each section preserves a checked scratch module. -/


section -- CounterPrefixTail

open OracleComp OracleSpec
namespace SphincsSecurity.Completeness

/-! A generic first-success search decomposes into a prefix and continuation.
    This is scratch for a 13-byte counter trailer; it is not a submitted proof. -/

theorem searchLoop_split {β γ : Type}
    (inputs : Nat → HashInput) (decode : HashOutput → Option β)
    (success : Nat → β → OracleComp HashSpec γ)
    (head rest start : Nat) :
    searchLoop inputs decode success (head + rest) start =
      (searchLoop inputs decode success head start >>= fun r =>
        match r with
        | none => searchLoop inputs decode success rest (start + head)
        | some v => pure (some v)) := by
  induction head generalizing start with
  | zero => simp [searchLoop]
  | succ head ih =>
      simp only [Nat.succ_add, searchLoop]
      rw [ih]
      simp only [bind_assoc]
      refine bind_congr fun answer => ?_
      cases decode answer with
      | none =>
          simp [Nat.add_comm, Nat.add_left_comm]
      | some v => simp

theorem searchLoop_tagged_range {β : Type}
    (inputs : Nat → HashInput) (decode : HashOutput → Option β) :
    ∀ (n start : Nat) (out : Option (Nat × β)),
      out ∈ support (searchLoop inputs decode
        (fun c v => pure (c, v)) n start) →
      ∀ c v, out = some (c, v) → start ≤ c ∧ c < start + n := by
  intro n
  induction n with
  | zero =>
      intro start out h c v heq
      simp only [searchLoop, support_pure, Set.mem_singleton_iff] at h
      rw [heq] at h
      cases h
  | succ n ih =>
      intro start out h c v heq
      rw [searchLoop] at h
      obtain ⟨answer, _, hrest⟩ := (mem_support_bind_iff _ _ _).mp h
      cases hdecode : decode answer with
      | none =>
          simp only [hdecode] at hrest
          obtain ⟨hlo, hhi⟩ := ih (start + 1) out hrest c v heq
          omega
      | some value =>
          simp only [hdecode, support_map, support_pure,
            Set.mem_singleton_iff, Set.mem_image] at hrest
          obtain ⟨word, hword, hpair⟩ := hrest
          subst word
          rw [heq] at hpair
          simp only [Option.some.injEq] at hpair
          have hfst := congrArg Prod.fst hpair
          omega

/-- The real encoding search returns a 32-bit counter rather than a `Nat`.
    Mapping the tagged abstract result commutes with the whole search. -/
theorem searchLoop_map_tagged {β γ : Type}
    (inputs : Nat → HashInput) (decode : HashOutput → Option β)
    (make : Nat → β → γ) :
    ∀ n start,
      searchLoop inputs decode (fun c v => pure (make c v)) n start =
        (Option.map (fun p : Nat × β => make p.1 p.2)) <$>
          searchLoop inputs decode (fun c v => pure (c, v)) n start := by
  intro n
  induction n with
  | zero => intro start; simp [searchLoop]
  | succ n ih =>
      intro start
      rw [searchLoop, searchLoop]
      rw [map_bind]
      refine bind_congr fun answer => ?_
      cases hdecode : decode answer with
      | none => simpa only [hdecode] using ih (start + 1)
      | some value => simp

/-- A tagged search either exhausted every trial or succeeded after the short cutoff. -/
def searchLoopTailEvent {β : Type} (start head : Nat)
    (r : Option (Nat × β) × QueryCache HashSpec) : Prop :=
  match r.1 with
  | none => True
  | some (c, _) => start + head ≤ c


/-- Exhausting the search or reaching a counter outside a short trailer's
    range requires every trial in the initial range to fail. This generic
    lemma is independent of the particular 13-byte codec. -/
theorem searchLoop_tagged_tail_le {β : Type}
    (inputs : Nat → HashInput) (decode : HashOutput → Option β)
    (bound head rest start : Nat) (cache : QueryCache HashSpec)
    (hinj : ∀ s s', s < bound → s' < bound → inputs s = inputs s' → s = s')
    (hbound : start + head + rest ≤ bound)
    (hfresh : ∀ s, start ≤ s → s < bound → cache (inputs s) = none) :
    Pr[searchLoopTailEvent start head |
      (simulateQ randomOracle (searchLoop inputs decode
        (fun c v => pure (c, v)) (head + rest) start)).run cache]
      ≤ failMass decode ^ head := by
  let part : OracleComp HashSpec (Option (Nat × β)) :=
    searchLoop inputs decode (fun c v => pure (c, v)) head start
  let tail : Option (Nat × β) → OracleComp HashSpec (Option (Nat × β)) :=
    fun r => match r with
      | none => searchLoop inputs decode (fun c v => pure (c, v)) rest (start + head)
      | some v => pure (some v)
  have hsplit : searchLoop inputs decode (fun c v => pure (c, v)) (head + rest) start =
      part >>= tail := by
    refine (searchLoop_split inputs decode (fun c v => pure (c, v))
      head rest start).trans ?_
    unfold part tail
    congr 1
    funext r
    cases r <;> rfl
  rw [hsplit]
  have hprefix :
      Pr[fun r => r.1 = none | (simulateQ randomOracle part).run cache] ≤
        failMass decode ^ head := by
    exact probEvent_searchLoop inputs decode (fun c v => pure (c, v)) bound
      hinj head start (by omega) cache hfresh
  have hbind :
      Pr[searchLoopTailEvent start head |
        (simulateQ randomOracle (part >>= tail)).run cache] ≤
        Pr[fun r => r.1 = none | (simulateQ randomOracle part).run cache] + 0 := by
    apply probEvent_bind_le_add part tail (fun r => r.1 = none)
      (searchLoopTailEvent start head) cache 0
    intro r hr hnot
    cases hres : r.1 with
    | none => exact (hnot hres).elim
    | some cv =>
        rcases cv with ⟨c, v⟩
        have hmem : some (c, v) ∈ support part := by
          apply support_simulateQ_run'_subset randomOracle part cache
          rw [StateT.run'_eq, support_map]
          exact ⟨r, hr, by simp [hres]⟩
        have hrange := searchLoop_tagged_range inputs decode head start
          (some (c, v)) hmem c v rfl
        simp only [tail, simulateQ_pure, StateT.run_pure]
        simp [searchLoopTailEvent, show ¬ start + head ≤ c by omega]
  exact hbind.trans (by simpa using hprefix)

#print axioms searchLoop_split
#print axioms searchLoop_tagged_range
#print axioms searchLoop_map_tagged
#print axioms searchLoop_tagged_tail_le

open ENNReal
open SphincsSecurity.Concrete
open SphincsSecurity.TargetSum

theorem encodingSearch_map_tagged (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : Digest) (n start : Nat) :
    (encodingSearch parameter lay tree leaf message n start :
      OracleComp HashSpec (Option (Counter × Encoding))) =
      (Option.map (fun p : Nat × Encoding =>
        (BitVec.ofNat counterBits p.1, p.2))) <$>
        searchLoop (encodeInput parameter lay tree leaf message)
          (fun out => decodeDigest (truncateHash out))
          (fun c v => pure (c, v)) n start := by
  rw [encodingSearch_eq_searchLoop]
  exact searchLoop_map_tagged
    (encodeInput parameter lay tree leaf message)
    (fun out => decodeDigest (truncateHash out))
    (fun c v => (BitVec.ofNat counterBits c, v)) n start

#print axioms encodingSearch_map_tagged

def radix27CounterLimit : Nat := 27 * 2 ^ 16

theorem radix27CounterLimit_large : codeShare * 530 ≤ radix27CounterLimit := by
  norm_num [codeShare, radix27CounterLimit]

theorem radix27CounterTail_le :
    failMass (fun out => decodeDigest (truncateHash out)) ^
      radix27CounterLimit ≤ (2⁻¹ : ℝ≥0∞) ^ 530 := by
  have hroom := failMass_encoding_add_le
  have hhalf := pow_le_half_ennreal codeShare (by decide)
    (failMass (fun out => decodeDigest (truncateHash out))) hroom
  have hone : failMass (fun out => decodeDigest (truncateHash out)) ≤ 1 :=
    le_trans le_self_add hroom
  calc
    failMass (fun out => decodeDigest (truncateHash out)) ^ radix27CounterLimit
        ≤ failMass (fun out => decodeDigest (truncateHash out)) ^ (codeShare * 530) :=
          pow_le_pow_right_of_le_one' hone radix27CounterLimit_large
    _ = (failMass (fun out => decodeDigest (truncateHash out)) ^ codeShare) ^ 530 :=
          pow_mul _ _ _
    _ ≤ (2⁻¹ : ℝ≥0∞) ^ 530 := pow_le_pow_left₀ (by positivity) hhalf _

theorem radix27_allMessages_extra_le :
    (2 : ℝ≥0∞) ^ 256 * (5 * (2⁻¹ : ℝ≥0∞) ^ 530) ≤
      (2⁻¹ : ℝ≥0∞) ^ 271 := by
  have hfive : (5 : ℝ≥0∞) ≤ 8 := by norm_num
  have hterm : 5 * (2⁻¹ : ℝ≥0∞) ^ 530 ≤
      (2⁻¹ : ℝ≥0∞) ^ 527 := by
    calc
      5 * (2⁻¹ : ℝ≥0∞) ^ 530 ≤ 8 * (2⁻¹ : ℝ≥0∞) ^ 530 :=
        mul_le_mul' hfive le_rfl
      _ = (2⁻¹ : ℝ≥0∞) ^ 527 := by
        rw [show (8 : ℝ≥0∞) = 2 ^ 3 by norm_num, ← ENNReal.inv_pow,
          mul_comm, ← ENNReal.div_eq_inv_mul,
          show (530 : Nat) = 3 + 527 by norm_num,
          two_pow_div_two_pow]
  calc
    (2 : ℝ≥0∞) ^ 256 * (5 * (2⁻¹ : ℝ≥0∞) ^ 530) ≤
        (2 : ℝ≥0∞) ^ 256 * (2⁻¹ : ℝ≥0∞) ^ 527 :=
      mul_le_mul' le_rfl hterm
    _ = (2⁻¹ : ℝ≥0∞) ^ 271 := by
      rw [← ENNReal.inv_pow, mul_comm, ← ENNReal.div_eq_inv_mul,
        show (527 : Nat) = 256 + 271 by norm_num,
        two_pow_div_two_pow]

theorem radix27_complete_numeric :
    (2 : ℝ≥0∞) ^ 256 *
      ((2⁻¹ : ℝ≥0∞) ^ 1023 +
        5 * (2⁻¹ : ℝ≥0∞) ^ 1256 +
        5 * (2⁻¹ : ℝ≥0∞) ^ 530) ≤
      ((2 ^ 256 : Nat) : ℝ≥0∞)⁻¹ := by
  let x : ℝ≥0∞ := 2⁻¹
  have holdA : x ^ 1023 ≤ x ^ 529 := inv_two_pow_anti (by norm_num)
  have holdB : 5 * x ^ 1256 ≤ x ^ 529 := by
    have hpow : x ^ 1256 ≤ x ^ 532 := inv_two_pow_anti (by norm_num)
    calc
      5 * x ^ 1256 ≤ 8 * x ^ 532 := mul_le_mul' (by norm_num) hpow
      _ = x ^ 529 := by
        dsimp [x]
        rw [show (8 : ℝ≥0∞) = 2 ^ 3 by norm_num,
          ← ENNReal.inv_pow, mul_comm, ← ENNReal.div_eq_inv_mul,
          show (532 : Nat) = 3 + 529 by norm_num,
          two_pow_div_two_pow]
  have hold : x ^ 1023 + 5 * x ^ 1256 ≤ x ^ 528 :=
    (add_le_add holdA holdB).trans_eq (inv_two_pow_succ_add 528)
  have hnew : 5 * x ^ 530 ≤ x ^ 527 := by
    calc
      5 * x ^ 530 ≤ 8 * x ^ 530 := mul_le_mul' (by norm_num) le_rfl
      _ = x ^ 527 := by
        dsimp [x]
        rw [show (8 : ℝ≥0∞) = 2 ^ 3 by norm_num,
          ← ENNReal.inv_pow, mul_comm, ← ENNReal.div_eq_inv_mul,
          show (530 : Nat) = 3 + 527 by norm_num,
          two_pow_div_two_pow]
  have hsum : x ^ 1023 + 5 * x ^ 1256 + 5 * x ^ 530 ≤ x ^ 526 := by
    calc
      _ ≤ x ^ 528 + x ^ 527 := add_le_add hold hnew
      _ ≤ x ^ 527 + x ^ 527 :=
        add_le_add (inv_two_pow_anti (by norm_num)) le_rfl
      _ = x ^ 526 := inv_two_pow_succ_add 526
  have hcast : ((2 ^ 256 : Nat) : ℝ≥0∞)⁻¹ = x ^ 256 := by
    simp only [x, Nat.cast_pow, Nat.cast_ofNat, ENNReal.inv_pow]
  rw [hcast]
  calc
    (2 : ℝ≥0∞) ^ 256 *
        (x ^ 1023 + 5 * x ^ 1256 + 5 * x ^ 530) ≤
        (2 : ℝ≥0∞) ^ 256 * x ^ 526 := mul_le_mul' le_rfl hsum
    _ = x ^ 270 := by
      dsimp [x]
      rw [← ENNReal.inv_pow, mul_comm, ← ENNReal.div_eq_inv_mul,
        show (526 : Nat) = 256 + 270 by norm_num,
        two_pow_div_two_pow]
    _ ≤ x ^ 256 := inv_two_pow_anti (by norm_num)

def radix27EncodingBad
    (r : Option (Counter × Encoding) × QueryCache HashSpec) : Prop :=
  match r.1 with
  | none => True
  | some (counter, _) => radix27CounterLimit ≤ counter.toNat

/-- The concrete 32-bit encoding search's combined exhaustion/overflow event
    has the same prefix bound as the tagged `Nat` search. -/
theorem radix27EncodingBad_le (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : Digest) (cache : QueryCache HashSpec)
    (hfresh : ∀ c, c < encodingAttemptLimit →
      cache (encodeInput parameter lay tree leaf message c) = none) :
    Pr[radix27EncodingBad |
      (simulateQ randomOracle (encodingSearch parameter lay tree leaf message
        encodingAttemptLimit 0 :
          OracleComp HashSpec (Option (Counter × Encoding)))).run cache] ≤
      (2⁻¹ : ℝ≥0∞) ^ 530 := by
  let inp := encodeInput parameter lay tree leaf message
  let dec : HashOutput → Option Encoding :=
    fun out => decodeDigest (truncateHash out)
  let tagged : OracleComp HashSpec (Option (Nat × Encoding)) :=
    searchLoop inp dec (fun c v => pure (c, v)) encodingAttemptLimit 0
  have hmap :
      (encodingSearch parameter lay tree leaf message encodingAttemptLimit 0 :
        OracleComp HashSpec (Option (Counter × Encoding))) =
      (Option.map (fun p : Nat × Encoding =>
        (BitVec.ofNat counterBits p.1, p.2))) <$> tagged :=
    encodingSearch_map_tagged parameter lay tree leaf message _ _
  rw [hmap, simulateQ_map, StateT.run_map, probEvent_map]
  have hmono :
      Pr[radix27EncodingBad ∘
        (fun r : Option (Nat × Encoding) × QueryCache HashSpec =>
          (Option.map (fun p : Nat × Encoding =>
            (BitVec.ofNat counterBits p.1, p.2)) r.1, r.2)) |
        (simulateQ randomOracle tagged).run cache] ≤
      Pr[searchLoopTailEvent 0 radix27CounterLimit |
        (simulateQ randomOracle tagged).run cache] := by
    apply probEvent_mono
    intro r hr hbad
    cases hres : r.1 with
    | none => simp [searchLoopTailEvent, hres]
    | some pair =>
        rcases pair with ⟨c, v⟩
        have hmem : some (c, v) ∈ support tagged := by
          apply support_simulateQ_run'_subset randomOracle tagged cache
          rw [StateT.run'_eq, support_map]
          exact ⟨r, hr, by simp [hres]⟩
        have hrange := searchLoop_tagged_range inp dec encodingAttemptLimit 0
          (some (c, v)) hmem c v rfl
        have hc32 : c < 2 ^ 32 := by
          have := hrange.2
          norm_num [encodingAttemptLimit] at this ⊢
          omega
        simp only [Function.comp_apply, radix27EncodingBad,
          searchLoopTailEvent, hres, Option.map_some,
          BitVec.toNat_ofNat, counterBits] at hbad ⊢
        have hcmod : c % 4294967296 = c := Nat.mod_eq_of_lt (by omega)
        simpa [hcmod] using hbad
  have hprefix :
      Pr[searchLoopTailEvent 0 radix27CounterLimit |
        (simulateQ randomOracle tagged).run cache] ≤
      failMass dec ^ radix27CounterLimit := by
    apply searchLoop_tagged_tail_le inp dec encodingAttemptLimit
      radix27CounterLimit (encodingAttemptLimit - radix27CounterLimit) 0 cache
    · intro s s' hs hs' heq
      exact encodeInput_inj parameter lay tree leaf message
        (by have := hs; norm_num [encodingAttemptLimit] at this ⊢; omega)
        (by have := hs'; norm_num [encodingAttemptLimit] at this ⊢; omega) heq
    · norm_num [encodingAttemptLimit, radix27CounterLimit]
    · intro s _ hs
      exact hfresh s hs
  exact (hmono.trans hprefix).trans radix27CounterTail_le

#print axioms radix27CounterTail_le
#print axioms radix27_allMessages_extra_le
#print axioms radix27_complete_numeric
#print axioms radix27EncodingBad_le

end SphincsSecurity.Completeness


end


section -- CounterLayerPure

namespace SphincsSecurity.Completeness

open Concrete

def LayerCountersSmall (remaining : Nat)
    (out : Option (Layer → LayerOutput)) : Prop :=
  ∃ parts, out = some parts ∧
    ∀ lay : Layer, lay.val < remaining →
      (parts lay).1.toNat < radix27CounterLimit

theorem layerCountersSmall_zero :
    LayerCountersSmall 0 (some fun _ => (0, fun _ => 0, fun _ => 0)) := by
  refine ⟨_, rfl, ?_⟩
  intro lay h
  omega

theorem layerCountersSmall_top (counter : Counter)
    (values : ChainIndex → Digest) (path : Nat → Digest)
    (hcounter : counter.toNat < radix27CounterLimit) :
    LayerCountersSmall 1 (some fun other =>
      if other = topLayer then (counter, values, path)
      else (0, fun _ => 0, fun _ => 0)) := by
  refine ⟨_, rfl, ?_⟩
  intro lay h
  have htop : lay = topLayer := Fin.ext (by simp [topLayer]; omega)
  simp [htop, hcounter]

theorem layerCountersSmall_extend (r : Nat) (hr : r < numLayers)
    (counter : Counter) (values : ChainIndex → Digest)
    (path : Nat → Digest) (rest : Layer → LayerOutput)
    (hcounter : counter.toNat < radix27CounterLimit)
    (hrest : LayerCountersSmall r (some rest)) :
    LayerCountersSmall (r + 1)
      (some fun other =>
        if other = (⟨r, hr⟩ : Layer) then (counter, values, path)
        else rest other) := by
  refine ⟨_, rfl, ?_⟩
  intro lay hlt
  by_cases heq : lay = (⟨r, hr⟩ : Layer)
  · simp [heq, hcounter]
  · have hval : lay.val < r := by
      have hne : lay.val ≠ r := by
        intro h
        apply heq
        exact Fin.ext h
      omega
    obtain ⟨parts, hparts, hsmall⟩ := hrest
    have hrest_eq_parts : rest = parts := Option.some.inj hparts
    simpa [heq, hrest_eq_parts] using hsmall lay hval

#print axioms layerCountersSmall_zero
#print axioms layerCountersSmall_top
#print axioms layerCountersSmall_extend

end SphincsSecurity.Completeness


end


section -- CounterLayerStep

namespace SphincsSecurity.Completeness

open Concrete

def radix27LayerContinuation (parameter : PublicParameter) (index : Index)
    (secret : Layer → TreeIndex → LeafIndex → ChainPair → OracleComp HashSpec (Digest × Digest))
    (topNode : Nat → Nat → OracleComp HashSpec Digest)
    (r : Nat) (hlayer : r < numLayers)
    (out : Option (Counter × Encoding)) :
    OracleComp HashSpec (Option (Layer → LayerOutput)) :=
  let lay : Layer := ⟨r, hlayer⟩
  let tree := treeIndexAt index lay
  let leaf := leafIndexAt index lay
  match out with
  | none => pure none
  | some (counter, encoding) => do
      let (values, path, root) ←
        buildLayerTreePaired parameter lay tree (secret lay tree) leaf encoding
      let some rest ← signLayersPaired parameter index secret topNode r root
        | return none
      return some fun other =>
        if other = lay then (counter, values, path) else rest other

theorem signLayersPaired_succ_bind (parameter : PublicParameter) (index : Index)
    (secret : Layer → TreeIndex → LeafIndex → ChainPair → OracleComp HashSpec (Digest × Digest))
    (topNode : Nat → Nat → OracleComp HashSpec Digest)
    (r : Nat) (hlayer : r < numLayers) (hnzero : r ≠ 0) (message : Digest) :
    signLayersPaired parameter index secret topNode (r + 1) message =
      encodingSearch parameter ⟨r, hlayer⟩ (treeIndexAt index ⟨r, hlayer⟩)
        (leafIndexAt index ⟨r, hlayer⟩) message encodingAttemptLimit 0 >>=
          radix27LayerContinuation parameter index secret topNode r hlayer := by
  rw [signLayersPaired]
  simp only [dif_pos hlayer, if_neg hnzero]
  unfold radix27LayerContinuation
  refine bind_congr fun out => ?_
  cases out with
  | none => rfl
  | some pair =>
      rcases pair with ⟨counter, encoding⟩
      rfl

#print axioms signLayersPaired_succ_bind

end SphincsSecurity.Completeness


end


section -- CounterFiveLayer

open OracleComp OracleSpec ENNReal

namespace SphincsSecurity.Completeness

open Concrete
set_option maxRecDepth 10000
set_option maxHeartbeats 200000
attribute [local irreducible] Seeded.signDigestLoop Concrete.buildLayerTreePaired Concrete.buildForestPaired
  Concrete.encodingSearch digestAttemptLimit encodingAttemptLimit SphincsSecurity.deriveKey
  Seeded.signChecked

def TopCounterSmall (out : Option LayerOutput) : Prop :=
  ∃ value, out = some value ∧ value.1.toNat < radix27CounterLimit

theorem probEvent_signTopLayerPaired_notSmall
    (parameter : PublicParameter) (index : Index)
    (secret : LeafIndex → ChainPair → OracleComp HashSpec (Digest × Digest))
    (topNode : Nat → Nat → OracleComp HashSpec Digest)
    (message : Digest) (cache : QueryCache HashSpec)
    (hfresh : EncodingFresh parameter (fun l => l.val < 1) cache) :
    Pr[fun r => ¬ TopCounterSmall r.1 |
      (simulateQ randomOracle
        (signTopLayerPaired parameter index secret topNode message)).run cache] ≤
      (2⁻¹ : ℝ≥0∞) ^ 530 := by
  rw [signTopLayerPaired]
  refine le_trans (probEvent_bind_le_add _ _
    (fun r => radix27EncodingBad r)
    (fun r => ¬ TopCounterSmall r.1) cache 0 ?_) ?_
  · rintro ⟨result, c1⟩ _ hgood
    cases result with
    | none =>
        exact (hgood (by simp [radix27EncodingBad])).elim
    | some pair =>
        obtain ⟨counter, encoding⟩ := pair
        have hcounter : counter.toNat < radix27CounterLimit := by
          have hnot : ¬ radix27CounterLimit ≤ counter.toNat := by
            simpa [radix27EncodingBad] using hgood
          omega
        dsimp only
        refine probEvent_bind_le _ _ _ c1 0 (fun r1 _ => ?_)
        refine probEvent_bind_le _ _ _ r1.2 0 (fun r2 _ => ?_)
        simp [TopCounterSmall, hcounter]
  · rw [add_zero]
    exact radix27EncodingBad_le parameter _ _ _ message cache
      (fun c _ => hfresh topLayer (by decide) _ _ _)

#print axioms probEvent_signTopLayerPaired_notSmall

theorem probEvent_signLayersPaired_notSmall (sk : Seeded.SecretKey) (index : Index)
    (topNode : Nat → Nat → OracleComp HashSpec Digest) :
    ∀ (remaining : Nat), remaining ≤ numLayers → ∀ (message : Digest) (cache : QueryCache HashSpec),
      EncodingFresh sk.parameter (fun l => l.val < remaining) cache →
      Pr[fun r => ¬ LayerCountersSmall remaining r.1 |
        (simulateQ (randomOracle : QueryImpl HashSpec _)
          (signLayersPaired sk.parameter index (Seeded.otsSecret sk.parameter sk.seed)
            topNode remaining message : OracleComp HashSpec (Option (Layer → LayerOutput)))).run cache]
        ≤ (remaining : ℝ≥0∞) * (2⁻¹ : ℝ≥0∞) ^ 530 := by
  intro remaining
  induction remaining with
  | zero =>
      intro _ message cache _
      simp [signLayersPaired, LayerCountersSmall]
  | succ r ih =>
      intro hrem message cache hfresh
      by_cases hzero : r = 0
      · subst hzero
        rw [signLayersPaired]
        split
        next hlayer =>
          rw [if_pos rfl]
          refine le_trans (probEvent_bind_le_add _ _
            (fun out => ¬ TopCounterSmall out.1)
            (fun out => ¬ LayerCountersSmall 1 out.1) cache 0 ?_) ?_
          · rintro ⟨result, c1⟩ _ hgood
            obtain ⟨⟨counter, values, path⟩, hresult, hcounter⟩ :=
              (not_not.mp hgood : TopCounterSmall result)
            subst result
            have hsmall := layerCountersSmall_top counter values path hcounter
            simp [LayerCountersSmall]
            intro x hx
            have htop : x = topLayer := Fin.ext (by simp [topLayer]; omega)
            simpa [htop] using hcounter
          · rw [add_zero, Nat.zero_add, Nat.cast_one, one_mul]
            exact probEvent_signTopLayerPaired_notSmall sk.parameter index _ topNode message cache hfresh
        next hlayer => exact absurd (show 0 < numLayers by decide) hlayer
      · have hlayer : r < numLayers := Nat.lt_of_succ_le hrem
        rw [signLayersPaired_succ_bind sk.parameter index
          (Seeded.otsSecret sk.parameter sk.seed) topNode r hlayer hzero message]
        refine le_trans (probEvent_bind_le_add
          (encodingSearch sk.parameter ⟨r, hlayer⟩
            (treeIndexAt index ⟨r, hlayer⟩) (leafIndexAt index ⟨r, hlayer⟩)
            message encodingAttemptLimit 0)
          (radix27LayerContinuation sk.parameter index
            (Seeded.otsSecret sk.parameter sk.seed) topNode r hlayer)
          radix27EncodingBad
          (fun out => ¬ LayerCountersSmall (r + 1) out.1) cache
          ((r : ℝ≥0∞) * (2⁻¹ : ℝ≥0∞) ^ 530) ?_) ?_
        · rintro ⟨result, c1⟩ hr hgood
          cases result with
          | none => exact (hgood (by simp [radix27EncodingBad])).elim
          | some pair =>
              obtain ⟨counter, encoding⟩ := pair
              have hcounter : counter.toNat < radix27CounterLimit := by
                have hnot : ¬ radix27CounterLimit ≤ counter.toNat := by
                  simpa [radix27EncodingBad] using hgood
                omega
              dsimp only
              have h1 : EncodingFresh sk.parameter (fun l => l.val < r) c1 :=
                (hfresh.mono fun l hl => Nat.lt_succ_of_lt hl).step _ ⟨_, c1⟩ hr
                  (fun f l hl tree leaf payload => Avoids.encodingSearch f _ _ _ _ _ _
                    (fun _ => encodingInput_ne_of_layer_ne _
                      (fun h => by rw [← h] at hl; exact absurd hl (Nat.lt_irrefl _)) _ _ _ _ _ _) _ _)
              refine probEvent_bind_le _ _ _ c1 _ (fun built hbuilt => ?_)
              have h2 := h1.step _ built hbuilt (fun f l _ tree leaf payload =>
                Avoids.buildLayerTreePaired_of_structural f _ _ _ _ _ _ _
                  (structural_encoding sk.parameter sk.seed l tree leaf payload))
              obtain ⟨⟨values, path, root⟩, c2⟩ := built
              dsimp only
              refine le_trans (probEvent_bind_le_add _ _
                (fun out => ¬ LayerCountersSmall r out.1)
                (fun out => ¬ LayerCountersSmall (r + 1) out.1) c2 0 ?_) ?_
              · rintro ⟨result3, c3⟩ _ hsmall
                obtain ⟨rest, hresult, hrest⟩ :=
                  (not_not.mp hsmall : LayerCountersSmall r result3)
                subst result3
                simp [LayerCountersSmall]
                intro x hx
                by_cases heq : x = (⟨r, hlayer⟩ : Layer)
                · simpa [heq] using hcounter
                · have hval : x.val < r := by
                    have hne : x.val ≠ r := by
                      intro h
                      exact heq (Fin.ext h)
                    omega
                  simpa [heq] using hrest x hval
              · rw [add_zero]
                exact ih (Nat.le_of_succ_le hrem) root c2 h2
        · calc
            _ ≤ (2⁻¹ : ℝ≥0∞) ^ 530 +
                  (r : ℝ≥0∞) * (2⁻¹ : ℝ≥0∞) ^ 530 := by
                  refine add_le_add ?_ le_rfl
                  exact radix27EncodingBad_le sk.parameter _ _ _ message cache
                    (fun c _ => hfresh ⟨r, hlayer⟩ (by simp) _ _ _)
            _ = ((r + 1 : Nat) : ℝ≥0∞) * (2⁻¹ : ℝ≥0∞) ^ 530 := by
                  push_cast
                  ring

#print axioms probEvent_signLayersPaired_notSmall

end SphincsSecurity.Completeness


end


section -- CounterSignFrom

open OracleComp OracleSpec ENNReal

namespace SphincsSecurity.Completeness

open Concrete
set_option maxRecDepth 10000
set_option maxHeartbeats 300000
attribute [local irreducible] Concrete.buildForestPaired

def SignatureCountersSmall (out : Option Signature) : Prop :=
  ∃ σ, out = some σ ∧
    ∀ lay : Layer, (σ.layers lay).counter.toNat < radix27CounterLimit

theorem layerCountersSmall_signature (randomness : Randomness)
    (secrets : FtsTree → Digest) (ftsPath : FtsTree → Fin ftsTreeHeight → Digest)
    (out : Option (Layer → LayerOutput))
    (h : LayerCountersSmall numLayers out) :
    SignatureCountersSmall (do
      let parts ← out
      some ⟨randomness, secrets, ftsPath,
        fun lay => LayerOutput.toSignature lay (parts lay)⟩) := by
  obtain ⟨parts, hout, hsmall⟩ := h
  subst out
  refine ⟨_, rfl, ?_⟩
  intro lay
  exact hsmall lay lay.isLt

theorem probEvent_signFrom_notSmall (sk : Seeded.SecretKey) (index : Index)
    (topNode : Nat → Nat → OracleComp HashSpec Digest) (randomness : Randomness)
    (leaves : IndexGroup → FtsLeaf) (cache : QueryCache HashSpec)
    (hfresh : EncodingFresh sk.parameter (fun _ => True) cache) :
    Pr[fun r => ¬ SignatureCountersSmall r.1 |
      (simulateQ (randomOracle : QueryImpl HashSpec _)
        (signFromPaired sk.parameter index (Seeded.ftsSecret sk.parameter sk.seed index)
          (Seeded.otsSecret sk.parameter sk.seed) topNode randomness leaves
          : OracleComp HashSpec (Option Signature))).run cache]
      ≤ (numLayers : ℝ≥0∞) * (2⁻¹ : ℝ≥0∞) ^ 530 := by
  rw [signFromPaired]
  refine probEvent_bind_le _ _ _ cache _ (fun forest hforest => ?_)
  have h1 := hfresh.step _ forest hforest (fun f l _ tree leaf payload =>
    Avoids.buildForestPaired_of_structural f _ _ _ _ _
      (structural_encoding sk.parameter sk.seed l tree leaf payload))
  obtain ⟨⟨secrets, ftsPath, ftsPublicKey⟩, c1⟩ := forest
  dsimp only
  refine le_trans (probEvent_bind_le_add _ _
    (fun out => ¬ LayerCountersSmall numLayers out.1)
    (fun out => ¬ SignatureCountersSmall out.1) c1 0 ?_) ?_
  · rintro ⟨result, c2⟩ _ hsmall
    obtain ⟨parts, hresult, hparts⟩ := (not_not.mp hsmall : LayerCountersSmall numLayers result)
    subst result
    simp [SignatureCountersSmall, LayerOutput.toSignature, hparts]
  · rw [add_zero]
    exact probEvent_signLayersPaired_notSmall sk index topNode numLayers le_rfl
      ftsPublicKey c1 (h1.mono fun _ _ => trivial)

#print axioms layerCountersSmall_signature
#print axioms probEvent_signFrom_notSmall

end SphincsSecurity.Completeness


end


section -- CounterSignChecked

open OracleComp OracleSpec ENNReal

namespace SphincsSecurity.Completeness

open Concrete
set_option maxRecDepth 10000
set_option maxHeartbeats 300000
attribute [local irreducible] Seeded.signDigestLoop

theorem probEvent_signChecked_notSmall (sk : Seeded.SecretKey)
    (topCache : TopCache) (message : Message) (cache : QueryCache HashSpec)
    (hrand : ∀ s, cache (randInput sk message s) = none)
    (hmsg : ∀ ρ, cache (msgInput sk message ρ) = none)
    (henc : EncodingFresh sk.parameter (fun _ => True) cache) :
    Pr[fun r => ¬ SignatureCountersSmall r.1 |
      (simulateQ (randomOracle : QueryImpl HashSpec _)
        (Seeded.signChecked sk topCache message : OracleComp HashSpec (Option Signature))).run cache]
      ≤ digestFactor ^ digestAttemptLimit +
        (numLayers : ℝ≥0∞) * (2⁻¹ : ℝ≥0∞) ^ 530 := by
  rw [Seeded.signChecked]
  refine le_trans (probEvent_bind_le_add _ _ (fun r => r.1 = none) _ cache
    ((numLayers : ℝ≥0∞) * (2⁻¹ : ℝ≥0∞) ^ 530) ?_) ?_
  · rintro ⟨result, c1⟩ hr hsome
    obtain ⟨⟨randomness, index, leaves⟩, rfl⟩ := Option.ne_none_iff_exists'.mp hsome
    dsimp only
    have h1 : EncodingFresh sk.parameter (fun _ => True) c1 :=
      henc.step _ ⟨_, c1⟩ hr (fun f l _ tree leaf payload =>
        Avoids.signDigestLoop_of_structural f _ sk message
          (structural_encoding sk.parameter sk.seed l tree leaf payload) _ _)
    exact probEvent_signFrom_notSmall sk index _ randomness leaves c1 h1
  · exact add_le_add (probEvent_signDigestLoop sk message digestAttemptLimit 0 cache ∅
      (by rw [digestAttemptLimit]; omega) (by simp) (fun s _ _ => hrand s) (fun ρ _ => hmsg ρ)) le_rfl

theorem probEvent_sign_notSmall (sk : Seeded.SecretKey)
    (topCache : TopCache) (message : Message) (cache : QueryCache HashSpec)
    (hmac : cache (macHashInput sk.parameter sk.seed topCache.region) = some topCache.tag)
    (hrand : ∀ s, cache (randInput sk message s) = none)
    (hmsg : ∀ ρ, cache (msgInput sk message ρ) = none)
    (henc : EncodingFresh sk.parameter (fun _ => True) cache) :
    Pr[fun r => ¬ SignatureCountersSmall r.1 |
      (simulateQ (randomOracle : QueryImpl HashSpec _)
        (Seeded.sign sk topCache message : OracleComp HashSpec (Option Signature))).run cache]
      ≤ digestFactor ^ digestAttemptLimit +
        (numLayers : ℝ≥0∞) * (2⁻¹ : ℝ≥0∞) ^ 530 := by
  rw [Seeded.sign]
  simp only [oracleHash, HasQuery.query, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
  rw [cached_run _ _ _ hmac, pure_bind, if_pos rfl]
  exact probEvent_signChecked_notSmall sk topCache message cache hrand hmsg henc

#print axioms probEvent_signChecked_notSmall
#print axioms probEvent_sign_notSmall

end SphincsSecurity.Completeness


end


section -- CounterKeygen

open OracleComp OracleSpec ENNReal

namespace SphincsSecurity.Completeness

open Concrete
set_option maxRecDepth 10000
set_option maxHeartbeats 300000

theorem probEvent_signedWithKeys_notSmall (seed : MasterSeed) (message : Message) :
    Pr[fun r => ¬ SignatureCountersSmall r.1.2 |
      (simulateQ (randomOracle : QueryImpl HashSpec _)
        (signedWithKeys seed message)).run ∅]
      ≤ digestFactor ^ digestAttemptLimit +
        (numLayers : ℝ≥0∞) * (2⁻¹ : ℝ≥0∞) ^ 530 := by
  rw [signedWithKeys]
  refine probEvent_bind_le _ _ _ ∅ _ (fun r hr => ?_)
  obtain ⟨hrand, hmsg, henc⟩ := keygen_fresh seed r hr message
  have hmac := keygen_mac_cached seed r hr
  refine le_trans (probEvent_bind_le_add _ _
    (fun out => ¬ SignatureCountersSmall out.1)
    (fun (out : ((PublicKey × TopCache × Seeded.SecretKey) × Option Signature) × QueryCache HashSpec) =>
      ¬ SignatureCountersSmall out.1.2) r.2 0 ?_) ?_
  · rintro ⟨result, c⟩ _ hsmall
    obtain ⟨signature, hresult, hcnt⟩ := (not_not.mp hsmall : SignatureCountersSmall result)
    subst result
    simp [SignatureCountersSmall, hcnt]
  · rw [add_zero]
    exact probEvent_sign_notSmall r.1.2.2 r.1.2.1 message r.2 hmac hrand hmsg henc

#print axioms probEvent_signedWithKeys_notSmall

end SphincsSecurity.Completeness


end


section -- CounterSmallHQ

open OracleComp OracleSpec
namespace SigGolfCandidate.Final
open SphincsSecurity
open SphincsSecurity.Completeness

noncomputable def smallSuccess (result : Option Signature) : Bool := by
  classical
  exact decide (SignatureCountersSmall result)

noncomputable def smallGame (seed : MasterSeed) (message : Message) :
    OracleComp SphincsSecurity.HashSpec Bool := by
  classical
  exact do
    let (_, cache, sk) ← Seeded.keygenFromSeed seed
    let result ← (Seeded.sign sk cache message : OracleComp SphincsSecurity.HashSpec (Option Signature))
    pure (smallSuccess result)

theorem hq_smallGame (seed : MasterSeed) (message : Message) :
    Equiv.HQ (smallGame seed message) := by
  classical
  unfold smallGame Seeded.keygenFromSeed Seeded.maskRegion
  simp only [bind_assoc, pure_bind]
  refine Equiv.hq_bind (Equiv.hq_buildLayerTablePaired _ rfl _ _ _
    (fun _ _ => Equiv.hq_otsSecret _ _ _ _ _ _) _ _) fun t => ?_
  refine Equiv.hq_bind (Equiv.hq_sequenceFin _ fun _ =>
    Equiv.hq_bind (Equiv.hq_sequenceFin _ fun _ =>
      Equiv.hq_bind (Equiv.hq_maskSecret _ _ _ _) fun _ => Equiv.hq_pure _)
      fun _ => Equiv.hq_pure _) fun _ => ?_
  refine Equiv.hq_bind (Equiv.hq_mac _ _ _) fun _ => ?_
  refine Equiv.hq_bind (Equiv.hq_sign _ rfl _ _) fun _ => Equiv.hq_pure _

#print axioms hq_smallGame
end SigGolfCandidate.Final


end


section -- CounterSmallEq

open OracleComp OracleSpec
namespace SigGolfCandidate.Final
open SphincsSecurity
open SphincsSecurity.Completeness

theorem smallGame_eq (seed : MasterSeed) (message : Message) :
    smallGame seed message =
      (fun kr => smallSuccess kr.2) <$>
        signedWithKeys seed message := by
  classical
  unfold smallGame signedWithKeys
  rw [map_bind]
  refine bind_congr fun keys => ?_
  rcases keys with ⟨pk, cache, sk⟩
  rw [map_bind]
  refine bind_congr fun result => ?_
  simp only [map_pure, pure_bind]

#print axioms smallGame_eq
end SigGolfCandidate.Final


end


section -- CounterSmallSim

open OracleComp OracleSpec
namespace SigGolfCandidate.Final
open SphincsSecurity
open SphincsSecurity.Completeness

set_option maxHeartbeats 30000

theorem smallGame_simulated_eq (seed : MasterSeed) (message : Message) :
    (simulateQ (randomOracle : QueryImpl SphincsSecurity.HashSpec _)
      (smallGame seed message)).run' ∅ =
    (fun kr => smallSuccess kr.2) <$>
      (simulateQ (randomOracle : QueryImpl SphincsSecurity.HashSpec _)
        (signedWithKeys seed message)).run' ∅ := by
  rw [smallGame_eq, simulateQ_map]
  rw [StateT.run'_eq, StateT.run_map]
  simp only [Functor.map_map, Function.comp_def, StateT.run'_eq]

#print axioms smallGame_simulated_eq
end SigGolfCandidate.Final


end


section -- CounterSmallEvent

open OracleComp OracleSpec ENNReal
namespace SigGolfCandidate.Final
open SphincsSecurity
open SphincsSecurity.Completeness

theorem smallSuccess_false_iff (result : Option Signature) :
    smallSuccess result = false ↔ ¬ SignatureCountersSmall result := by
  classical
  simp [smallSuccess]

set_option maxHeartbeats 40000
theorem probOutput_smallGame_false_eq (seed : MasterSeed) (message : Message) :
    Pr[= false | (simulateQ (randomOracle : QueryImpl SphincsSecurity.HashSpec _)
      (smallGame seed message)).run' ∅] =
    Pr[fun r => ¬ SignatureCountersSmall r.1.2 |
      (simulateQ (randomOracle : QueryImpl SphincsSecurity.HashSpec _)
        (signedWithKeys seed message)).run ∅] := by
  rw [smallGame_simulated_eq, StateT.run'_eq, probOutput_map, probEvent_map]
  simp only [Function.comp_def, smallSuccess_false_iff]

#print axioms probOutput_smallGame_false_eq
end SigGolfCandidate.Final


end


section -- CounterSmallBound

open OracleComp OracleSpec ENNReal
namespace SigGolfCandidate.Final
open SphincsSecurity
open SphincsSecurity.Completeness

theorem probOutput_smallGame_false_le (seed : MasterSeed) (message : Message) :
    Pr[= false | (simulateQ (randomOracle : QueryImpl SphincsSecurity.HashSpec _)
      (smallGame seed message)).run' ∅] ≤
      digestFactor ^ digestAttemptLimit +
        (numLayers : ℝ≥0∞) * (2⁻¹ : ℝ≥0∞) ^ 530 := by
  rw [probOutput_smallGame_false_eq]
  exact probEvent_signedWithKeys_notSmall seed message

#print axioms probOutput_smallGame_false_le
end SigGolfCandidate.Final


end


section -- CounterSmallHD

open OracleComp OracleSpec ENNReal
namespace SigGolfCandidate.Final
open SphincsSecurity
open SphincsSecurity.Completeness
open SigGolfCandidate.Bridge (relabel relabel_relabel)

noncomputable def smallGameHD (seed : MasterSeed) (message : Message) :
    OracleComp (HD →ₒ SphincsSecurity.HashOutput) Bool :=
  relabel toHD (smallGame seed message)

theorem relabel_val_smallGameHD (seed : MasterSeed) (message : Message) :
    relabel Subtype.val (smallGameHD seed message) = smallGame seed message := by
  unfold smallGameHD
  rw [relabel_relabel]
  exact Bridge.relabel_eq_self_of_allQ Equiv.Honest _ (fun x hx => val_toHD x hx)
    (hq_smallGame seed message)

theorem probOutput_smallGameHD_false_le (seed : MasterSeed) (message : Message) :
    Pr[= false | (simulateQ randomOracle (smallGameHD seed message)).run' ∅] ≤
      digestFactor ^ digestAttemptLimit +
        (numLayers : ℝ≥0∞) * (2⁻¹ : ℝ≥0∞) ^ 530 := by
  rw [run'_relabel Subtype.val Subtype.val_injective (smallGameHD seed message) ∅ ∅
    (fun _ => rfl), relabel_val_smallGameHD]
  exact probOutput_smallGame_false_le seed message

#print axioms probOutput_smallGameHD_false_le
end SigGolfCandidate.Final


end


section -- CounterSmallAll

open OracleComp OracleSpec ENNReal
namespace SigGolfCandidate.Final
open SphincsSecurity
open SphincsSecurity.Completeness

private noncomputable abbrev x : ℝ≥0∞ := 2⁻¹

theorem smallGame_failure_seeded (seed : MasterSeed) :
    ∑' message : Message,
      Pr[= false | (simulateQ randomOracle (smallGameHD seed message)).run' ∅] ≤
      ((2 ^ 256 : Nat) : ℝ≥0∞)⁻¹ := by
  calc
    ∑' message : Message,
        Pr[= false | (simulateQ randomOracle (smallGameHD seed message)).run' ∅]
        ≤ ∑' _message : Message,
          (x ^ 1023 + 5 * x ^ 530) := by
            apply ENNReal.tsum_le_tsum
            intro message
            refine (probOutput_smallGameHD_false_le seed message).trans ?_
            rw [show ((numLayers : Nat) : ℝ≥0∞) = 5 by norm_num [numLayers]]
            exact add_le_add digestFactor_pow_le le_rfl
    _ = (2 : ℝ≥0∞) ^ 256 * (x ^ 1023 + 5 * x ^ 530) := by
          rw [tsum_fintype, Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
            show Fintype.card Message = 2 ^ 256 by simp [messageBits], Nat.cast_pow, Nat.cast_ofNat]
    _ ≤ ((2 ^ 256 : Nat) : ℝ≥0∞)⁻¹ := by
      refine le_trans ?_ radix27_complete_numeric
      apply mul_le_mul' le_rfl
      have h : x ^ 1023 ≤ x ^ 1023 + 5 * x ^ 1256 :=
        le_add_of_nonneg_right (show (0 : ℝ≥0∞) ≤ 5 * x ^ 1256 from bot_le)
      exact add_le_add_left h _

#print axioms smallGame_failure_seeded
end SigGolfCandidate.Final


end


section -- Radix27Bit

namespace Radix27

open SigGolfCandidate.Legacy

def rank5 (h0 h1 h2 h3 h4 : Nat) : Nat :=
  h0 + 27 * (h1 + 27 * (h2 + 27 * (h3 + 27 * h4)))

theorem rank5_lt (h0 h1 h2 h3 h4 : Nat)
    (H0 : h0 < 27) (H1 : h1 < 27) (H2 : h2 < 27)
    (H3 : h3 < 27) (H4 : h4 < 27) :
    rank5 h0 h1 h2 h3 h4 < 14348907 := by
  unfold rank5
  omega

theorem rank5_split (h0 h1 h2 h3 h4 : Nat)
    (H0 : h0 < 27) (H1 : h1 < 27) (H2 : h2 < 27)
    (H3 : h3 < 27) (H4 : h4 < 27) :
    (rank5 h0 h1 h2 h3 h4 % 27 = h0) ∧
    (rank5 h0 h1 h2 h3 h4 / 27 % 27 = h1) ∧
    (rank5 h0 h1 h2 h3 h4 / 729 % 27 = h2) ∧
    (rank5 h0 h1 h2 h3 h4 / 19683 % 27 = h3) ∧
    (rank5 h0 h1 h2 h3 h4 / 531441 % 27 = h4) := by
  unfold rank5
  omega

theorem rank5_join (t : Nat) (H : t < 14348907) :
    rank5 (t % 27) (t / 27 % 27) (t / 729 % 27)
      (t / 19683 % 27) (t / 531441 % 27) = t := by
  unfold rank5
  omega

def lo16 (b : BitVec 80) (i : Nat) : BitVec 16 := b.extractLsb' (16 * i) 16
def word (q : BitVec 160) (i : Nat) : BitVec 32 := q.extractLsb' (32 * i) 32
def lowQ (q : BitVec 160) (i : Nat) : BitVec 16 := (word q i).extractLsb' 0 16
def highQ (q : BitVec 160) (i : Nat) : BitVec 16 := (word q i).extractLsb' 16 16

def lowPack (q : BitVec 160) : BitVec 80 :=
  lowQ q 4 ++ lowQ q 3 ++ lowQ q 2 ++ lowQ q 1 ++ lowQ q 0

def validQ (q : BitVec 160) : Prop :=
  (highQ q 0).toNat < 27 ∧ (highQ q 1).toNat < 27 ∧
  (highQ q 2).toNat < 27 ∧ (highQ q 3).toNat < 27 ∧
  (highQ q 4).toNat < 27

def rankQ (q : BitVec 160) : Nat :=
  rank5 (highQ q 0).toNat (highQ q 1).toNat (highQ q 2).toNat
    (highQ q 3).toNat (highQ q 4).toNat

theorem lowPack_part0 (q : BitVec 160) : lo16 (lowPack q) 0 = lowQ q 0 := by
  unfold lo16 lowPack
  bv_normalize
theorem lowPack_part1 (q : BitVec 160) : lo16 (lowPack q) 1 = lowQ q 1 := by
  unfold lo16 lowPack
  bv_normalize
theorem lowPack_part2 (q : BitVec 160) : lo16 (lowPack q) 2 = lowQ q 2 := by
  unfold lo16 lowPack
  bv_normalize
theorem lowPack_part3 (q : BitVec 160) : lo16 (lowPack q) 3 = lowQ q 3 := by
  unfold lo16 lowPack
  bv_normalize
theorem lowPack_part4 (q : BitVec 160) : lo16 (lowPack q) 4 = lowQ q 4 := by
  unfold lo16 lowPack
  bv_normalize

theorem ofNat_highQ (q : BitVec 160) (i : Nat) :
    BitVec.ofNat 16 (highQ q i).toNat = highQ q i := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem word_high_low (q : BitVec 160) (i : Nat) :
    highQ q i ++ lowQ q i = word q i := by
  unfold highQ lowQ
  exact BitVec.extractLsb'_append_extractLsb' (x := word q i) (w := 16) (len := 16)

theorem words_join (q : BitVec 160) :
    word q 4 ++ word q 3 ++ word q 2 ++ word q 1 ++ word q 0 = q := by
  unfold word
  bv_normalize

def validBlock (l : BitVec 80) (t : Nat) : BitVec 160 :=
  ((BitVec.ofNat 16 (t / 531441 % 27)) ++ lo16 l 4) ++
  ((BitVec.ofNat 16 (t / 19683 % 27)) ++ lo16 l 3) ++
  ((BitVec.ofNat 16 (t / 729 % 27)) ++ lo16 l 2) ++
  ((BitVec.ofNat 16 (t / 27 % 27)) ++ lo16 l 1) ++
  ((BitVec.ofNat 16 (t % 27)) ++ lo16 l 0)

def reservedBlock (l : BitVec 80) (t : Nat) : BitVec 160 :=
  (0#32) ++ ((0#16) ++ lo16 l 4) ++
  (lo16 l 3 ++ lo16 l 2) ++
  (lo16 l 1 ++ lo16 l 0) ++
  BitVec.ofNat 32 (4194304 + (t - 14348907))

def reservedLows (q : BitVec 160) : BitVec 80 :=
  (word q 3).extractLsb' 0 16 ++
  (word q 2).extractLsb' 16 16 ++
  (word q 2).extractLsb' 0 16 ++
  (word q 1).extractLsb' 16 16 ++
  (word q 1).extractLsb' 0 16

theorem lowPieces_eq (l : BitVec 80) :
    lo16 l 4 ++ lo16 l 3 ++ lo16 l 2 ++ lo16 l 1 ++ lo16 l 0 = l := by
  unfold lo16
  bv_normalize

theorem extract_nested {n : Nat} (x : BitVec n) (a b len mid : Nat)
    (h : b + len ≤ mid) :
    (x.extractLsb' a mid).extractLsb' b len = x.extractLsb' (a + b) len := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb']
  have h1 : i < len := hi
  have h2 : b + i < mid := by omega
  simp [h1, h2, Nat.add_assoc]

theorem reserved_top (l : BitVec 80) :
    BitVec.extractLsb' 0 16
      (BitVec.extractLsb' 0 32 (0#48 ++ BitVec.extractLsb' 64 16 l)) = lo16 l 4 := by
  unfold lo16
  rw [extract_nested (h := by decide), BitVec.extractLsb'_append_eq_right]

theorem nested3 (l : BitVec 80) :
    BitVec.extractLsb' 16 16 (BitVec.extractLsb' 32 32 l) = lo16 l 3 := by
  unfold lo16
  rw [extract_nested (h := by decide)]
theorem nested2 (l : BitVec 80) :
    BitVec.extractLsb' 0 16 (BitVec.extractLsb' 32 32 l) = lo16 l 2 := by
  unfold lo16
  rw [extract_nested (h := by decide)]
theorem nested1 (l : BitVec 80) :
    BitVec.extractLsb' 16 16 (BitVec.extractLsb' 0 32 l) = lo16 l 1 := by
  unfold lo16
  rw [extract_nested (h := by decide)]
theorem nested0 (l : BitVec 80) :
    BitVec.extractLsb' 0 16 (BitVec.extractLsb' 0 32 l) = lo16 l 0 := by
  unfold lo16
  rw [extract_nested (h := by decide)]

theorem validBlock_lows (l : BitVec 80) (t : Nat) :
    lowPack (validBlock l t) = l := by
  unfold lowPack lowQ word validBlock lo16
  bv_normalize

theorem validBlock_high0 (l : BitVec 80) (t : Nat) :
    (highQ (validBlock l t) 0).toNat = t % 27 := by
  unfold highQ word validBlock lo16
  bv_normalize
  simp [BitVec.toNat_ofNat] at *
  omega

theorem validBlock_high1 (l : BitVec 80) (t : Nat) :
    (highQ (validBlock l t) 1).toNat = t / 27 % 27 := by
  unfold highQ word validBlock lo16
  bv_normalize
  simp [BitVec.toNat_ofNat] at *
  omega

theorem validBlock_high2 (l : BitVec 80) (t : Nat) :
    (highQ (validBlock l t) 2).toNat = t / 729 % 27 := by
  unfold highQ word validBlock lo16
  bv_normalize
  simp [BitVec.toNat_ofNat] at *
  omega

theorem validBlock_high3 (l : BitVec 80) (t : Nat) :
    (highQ (validBlock l t) 3).toNat = t / 19683 % 27 := by
  unfold highQ word validBlock lo16
  bv_normalize
  simp [BitVec.toNat_ofNat] at *
  omega

theorem validBlock_high4 (l : BitVec 80) (t : Nat) :
    (highQ (validBlock l t) 4).toNat = t / 531441 % 27 := by
  unfold highQ word validBlock lo16
  bv_normalize
  simp [BitVec.toNat_ofNat] at *
  omega

theorem validBlock_valid (l : BitVec 80) (t : Nat) :
    validQ (validBlock l t) := by
  unfold validQ
  rw [validBlock_high0, validBlock_high1, validBlock_high2,
    validBlock_high3, validBlock_high4]
  omega

theorem validBlock_rank (l : BitVec 80) (t : Nat)
    (ht : t < 14348907) :
    rankQ (validBlock l t) = t := by
  unfold rankQ
  rw [validBlock_high0, validBlock_high1, validBlock_high2,
    validBlock_high3, validBlock_high4]
  exact rank5_join t ht

theorem validBlock_rankQ (q : BitVec 160) (h : validQ q) :
    validBlock (lowPack q) (rankQ q) = q := by
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  obtain ⟨s0, s1, s2, s3, s4⟩ :=
    rank5_split (highQ q 0).toNat (highQ q 1).toNat
      (highQ q 2).toNat (highQ q 3).toNat (highQ q 4).toNat
      h0 h1 h2 h3 h4
  have e0 : BitVec.ofNat 16 (rankQ q % 27) = highQ q 0 := by
    rw [show rankQ q % 27 = (highQ q 0).toNat from s0]
    exact ofNat_highQ q 0
  have e1 : BitVec.ofNat 16 (rankQ q / 27 % 27) = highQ q 1 := by
    rw [show rankQ q / 27 % 27 = (highQ q 1).toNat from s1]
    exact ofNat_highQ q 1
  have e2 : BitVec.ofNat 16 (rankQ q / 729 % 27) = highQ q 2 := by
    rw [show rankQ q / 729 % 27 = (highQ q 2).toNat from s2]
    exact ofNat_highQ q 2
  have e3 : BitVec.ofNat 16 (rankQ q / 19683 % 27) = highQ q 3 := by
    rw [show rankQ q / 19683 % 27 = (highQ q 3).toNat from s3]
    exact ofNat_highQ q 3
  have e4 : BitVec.ofNat 16 (rankQ q / 531441 % 27) = highQ q 4 := by
    rw [show rankQ q / 531441 % 27 = (highQ q 4).toNat from s4]
    exact ofNat_highQ q 4
  unfold validBlock
  rw [e0, e1, e2, e3, e4]
  rw [lowPack_part0, lowPack_part1, lowPack_part2, lowPack_part3, lowPack_part4]
  rw [word_high_low q 0, word_high_low q 1,
    word_high_low q 2, word_high_low q 3, word_high_low q 4]
  exact words_join q

theorem reservedBlock_lows (l : BitVec 80) (t : Nat) :
    reservedLows (reservedBlock l t) = l := by
  unfold reservedLows word reservedBlock lo16
  bv_normalize
  rename_i hneq
  rw [Bool.not_eq_true_eq_eq_false, beq_eq_false_iff_ne] at hneq
  apply hneq
  rw [reserved_top, nested3, nested2, nested1, nested0]
  exact lowPieces_eq l

theorem toNat_join16 (hi lo : BitVec 16) :
    (hi ++ lo).toNat = hi.toNat * 65536 + lo.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt (BitVec.isLt lo)]
  simp [Nat.shiftLeft_eq]

theorem validBlock_word0 (l : BitVec 80) (t : Nat) :
    word (validBlock l t) 0 = BitVec.ofNat 16 (t % 27) ++ lo16 l 0 := by
  unfold word validBlock lo16
  bv_normalize

theorem validBlock_word0_lt (l : BitVec 80) (t : Nat) :
    (word (validBlock l t) 0).toNat < 4194304 := by
  rw [validBlock_word0, toNat_join16, BitVec.toNat_ofNat]
  have ht : t % 27 < 65536 := by omega
  rw [Nat.mod_eq_of_lt ht]
  have hlo := BitVec.isLt (lo16 l 0)
  norm_num at hlo
  omega

theorem reservedBlock_word0 (l : BitVec 80) (t : Nat) :
    word (reservedBlock l t) 0 = BitVec.ofNat 32 (4194304 + (t - 14348907)) := by
  unfold word reservedBlock lo16
  bv_normalize

theorem reservedBlock_word0_nat (l : BitVec 80) (t : Nat)
    (ht : t < 16777216) :
    (word (reservedBlock l t) 0).toNat = 4194304 + (t - 14348907) := by
  rw [reservedBlock_word0, BitVec.toNat_ofNat]
  have hn : 4194304 + (t - 14348907) < 2 ^ 32 := by omega
  exact Nat.mod_eq_of_lt hn

def reservedMarker (q : BitVec 160) : Prop :=
  4194304 ≤ (word q 0).toNat ∧ (word q 0).toNat < 6622613

instance (q : BitVec 160) : Decidable (validQ q) := by
  unfold validQ
  infer_instance

instance (q : BitVec 160) : Decidable (reservedMarker q) := by
  unfold reservedMarker
  infer_instance

theorem validBlock_not_reserved (l : BitVec 80) (t : Nat) :
    ¬ reservedMarker (validBlock l t) := by
  intro h
  exact (Nat.not_le.mpr (validBlock_word0_lt l t)) h.1

theorem validQ_not_reserved (q : BitVec 160) (h : validQ q) :
    ¬ reservedMarker q := by
  intro hr
  have h0 : (highQ q 0).toNat < 27 := h.1
  have hlo := BitVec.isLt (lowQ q 0)
  have hw := word_high_low q 0
  have hn : (word q 0).toNat =
      (highQ q 0).toNat * 65536 + (lowQ q 0).toNat := by
    rw [← hw, toNat_join16]
  unfold reservedMarker at hr
  norm_num at hlo
  omega

theorem rankQ_lt (q : BitVec 160) (h : validQ q) : rankQ q < 14348907 := by
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  exact rank5_lt _ _ _ _ _ h0 h1 h2 h3 h4

theorem reservedBlock_marker (l : BitVec 80) (t : Nat)
    (hlo : 14348907 ≤ t) (hhi : t < 16777216) :
    reservedMarker (reservedBlock l t) := by
  rw [reservedMarker, reservedBlock_word0_nat l t hhi]
  omega

def expand13 (p : BitVec 104) : BitVec 160 :=
  let t := (p.extractLsb' 80 24).toNat
  let l := p.extractLsb' 0 80
  if t < 14348907 then validBlock l t else reservedBlock l t

def pack13 (q : BitVec 160) : BitVec 104 :=
  if reservedMarker q then
    BitVec.ofNat 24 ((word q 0).toNat - 4194304 + 14348907) ++ reservedLows q
  else if validQ q then
    BitVec.ofNat 24 (rankQ q) ++ lowPack q
  else
    BitVec.ofNat 24 14348907 ++ (0#80)

theorem pack13_validBlock (l : BitVec 80) (t : Nat)
    (ht : t < 14348907) :
    pack13 (validBlock l t) = BitVec.ofNat 24 t ++ l := by
  simp only [pack13, if_neg (validBlock_not_reserved l t),
    if_pos (validBlock_valid l t), validBlock_rank l t ht,
    validBlock_lows]

theorem pack13_validQ (q : BitVec 160) (h : validQ q) :
    pack13 q = BitVec.ofNat 24 (rankQ q) ++ lowPack q := by
  simp only [pack13, if_neg (validQ_not_reserved q h), if_pos h]

theorem expand13_join_valid (l : BitVec 80) (t : Nat)
    (ht : t < 14348907) :
    expand13 (BitVec.ofNat 24 t ++ l) = validBlock l t := by
  unfold expand13
  rw [BitVec.extractLsb'_append_eq_left, BitVec.extractLsb'_append_eq_right,
    BitVec.toNat_ofNat]
  have h24 : t < 2 ^ 24 := by omega
  rw [Nat.mod_eq_of_lt h24, if_pos ht]

theorem expand13_join_reserved (l : BitVec 80) (t : Nat)
    (hlo : 14348907 ≤ t) (hhi : t < 16777216) :
    expand13 (BitVec.ofNat 24 t ++ l) = reservedBlock l t := by
  unfold expand13
  rw [BitVec.extractLsb'_append_eq_left, BitVec.extractLsb'_append_eq_right,
    BitVec.toNat_ofNat]
  have h24 : t < 2 ^ 24 := by omega
  rw [Nat.mod_eq_of_lt h24, if_neg (by omega : ¬t < 14348907)]

theorem reservedCode_invalid (p : BitVec 104)
    (h : 14348907 ≤ (p.extractLsb' 80 24).toNat) :
    4194304 ≤ (word (expand13 p) 0).toNat := by
  let t := (p.extractLsb' 80 24).toNat
  let l := p.extractLsb' 0 80
  have ht24 : t < 16777216 := by
    change (p.extractLsb' 80 24).toNat < 2 ^ 24
    exact BitVec.isLt _
  change 4194304 ≤
    (word (if t < 14348907 then validBlock l t else reservedBlock l t) 0).toNat
  rw [if_neg (by omega : ¬t < 14348907), reservedBlock_word0_nat l t ht24]
  omega

def fallback13 : BitVec 104 := BitVec.ofNat 24 14348907 ++ (0#80)

theorem fallback13_invalid :
    4194304 ≤ (word (expand13 fallback13) 0).toNat := by
  apply reservedCode_invalid
  simp [fallback13, BitVec.toNat_ofNat]

theorem pack13_unrepresentable (q : BitVec 160)
    (hr : ¬ reservedMarker q) (hv : ¬ validQ q) :
    pack13 q = fallback13 := by
  simp only [pack13, if_neg hr, if_neg hv, fallback13]

theorem unrepresentable_invalid (q : BitVec 160)
    (hr : ¬ reservedMarker q) (hv : ¬ validQ q) :
    4194304 ≤ (word (expand13 (pack13 q)) 0).toNat := by
  rw [pack13_unrepresentable q hr hv]
  exact fallback13_invalid

theorem expand13_pack13_valid (q : BitVec 160) (h : validQ q) :
    expand13 (pack13 q) = q := by
  rw [pack13_validQ q h, expand13_join_valid _ _ (rankQ_lt q h)]
  exact validBlock_rankQ q h

theorem pack13_reservedBlock (l : BitVec 80) (t : Nat)
    (hlo : 14348907 ≤ t) (hhi : t < 16777216) :
    pack13 (reservedBlock l t) = BitVec.ofNat 24 t ++ l := by
  rw [pack13, if_pos (reservedBlock_marker l t hlo hhi),
    reservedBlock_word0_nat l t hhi, reservedBlock_lows]
  have hn : 4194304 + (t - 14348907) - 4194304 + 14348907 = t := by omega
  rw [hn]

theorem pack13_expand13 (p : BitVec 104) :
    pack13 (expand13 p) = p := by
  let t := (p.extractLsb' 80 24).toNat
  let l := p.extractLsb' 0 80
  have ht24 : t < 16777216 := by
    change (p.extractLsb' 80 24).toNat < 2 ^ 24
    exact BitVec.isLt _
  have hj : BitVec.ofNat 24 t ++ l = p := by
    simpa only [t, l, BitVec.ofNat_toNat, BitVec.setWidth_eq] using
      (BitVec.extractLsb'_append_extractLsb' (x := p) (w := 24) (len := 80))
  change pack13 (if t < 14348907 then validBlock l t else reservedBlock l t) = p
  by_cases ht : t < 14348907
  · rw [if_pos ht, pack13_validBlock l t ht]
    exact hj
  · have hlo : 14348907 ≤ t := by omega
    rw [if_neg ht, pack13_reservedBlock l t hlo ht24]
    exact hj

abbrev shortSizes13 : Sizes := ⟨6397, 6404, 131072⟩
abbrev bodyBits13 : Nat := 8 * 6384

def body13 (b : Bytes 6397) : Bytes 6384 := b.extractLsb' 0 bodyBits13
def trailer13 (b : Bytes 6397) : BitVec 104 := b.extractLsb' bodyBits13 104
def join13 (c : BitVec 104) (v : Bytes 6384) : Bytes 6397 := c ++ v

theorem join13_parts (b : Bytes 6397) : join13 (trailer13 b) (body13 b) = b := by
  simpa only [join13, trailer13, body13, bodyBits13] using
    (BitVec.extractLsb'_append_extractLsb' (x := b) (w := 104) (len := 8 * 6384))

def expandWitness13 (b : Bytes 6397) : Bytes 6404 :=
  expand13 (trailer13 b) ++ body13 b

def shrinkWitnessAny13 (w : Bytes 6404) : Bytes 6397 :=
  pack13 (w.extractLsb' bodyBits13 160) ++ w.extractLsb' 0 bodyBits13

theorem shrinkAny_expandWitness13 (b : Bytes 6397) :
    shrinkWitnessAny13 (expandWitness13 b) = b := by
  simp only [shrinkWitnessAny13, expandWitness13, trailer13, body13,
    BitVec.extractLsb'_append_eq_left, BitVec.extractLsb'_append_eq_right,
    pack13_expand13]
  exact join13_parts b

def validWitness13 (w : Bytes 6404) : Prop :=
  validQ (w.extractLsb' bodyBits13 160)

theorem expand_shrinkWitnessAny13 (w : Bytes 6404) (h : validWitness13 w) :
    expandWitness13 (shrinkWitnessAny13 w) = w := by
  simp only [expandWitness13, shrinkWitnessAny13, trailer13, body13,
    BitVec.extractLsb'_append_eq_left, BitVec.extractLsb'_append_eq_right]
  rw [expand13_pack13_valid _ h]
  simpa only [bodyBits13] using
    (BitVec.extractLsb'_append_extractLsb' (x := w) (w := 160) (len := 8 * 6384))

def unpackOld13 (b : Bytes 6397) : Bytes 6404 :=
  SigGolfCandidate.Ref.unexpandRef (expandWitness13 b)

def packOldAny13 (b : Bytes 6404) : Bytes 6397 :=
  shrinkWitnessAny13 (SigGolfCandidate.Ref.expandRef b)

theorem packAny_unpackOld13 (b : Bytes 6397) :
    packOldAny13 (unpackOld13 b) = b := by
  unfold packOldAny13 unpackOld13
  rw [SigGolfCandidate.Ref.expandRef_unexpandRef,
    shrinkAny_expandWitness13]

theorem expand_unpackOld13 (b : Bytes 6397) :
    SigGolfCandidate.Ref.expandRef (unpackOld13 b) = expandWitness13 b := by
  exact SigGolfCandidate.Ref.expandRef_unexpandRef _

theorem unpack_packOldAny13 (σ : Bytes 6404)
    (h : validWitness13 (SigGolfCandidate.Ref.expandRef σ)) :
    unpackOld13 (packOldAny13 σ) = σ := by
  unfold unpackOld13 packOldAny13
  rw [expand_shrinkWitnessAny13 _ h,
    SigGolfCandidate.Ref.unexpandRef_expandRef]

#print axioms pack13_expand13
#print axioms packAny_unpackOld13
#print axioms unpack_packOldAny13
#print axioms expand13_pack13_valid
#print axioms reservedCode_invalid
#print axioms unrepresentable_invalid

#print axioms validBlock_lows
#print axioms validBlock_high0
#print axioms validBlock_high1
#print axioms validBlock_high4
#print axioms reservedBlock_lows
#print axioms lowPieces_eq
#print axioms validBlock_word0_lt
#print axioms reservedBlock_word0_nat

end Radix27


end


section -- CounterCodecSmall

open SphincsSecurity
open SphincsSecurity.Completeness
open SigGolfCandidate.Legacy

namespace Radix27
set_option maxRecDepth 100000
set_option maxHeartbeats 300000

theorem highQ_lt_of_word_lt (q : BitVec 160) (i : Nat)
    (h : (word q i).toNat < radix27CounterLimit) :
    (highQ q i).toNat < 27 := by
  have hdiv : (highQ q i).toNat = (word q i).toNat / 2 ^ 16 := by
    simp only [highQ, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
    exact Nat.mod_eq_of_lt (by have := (word q i).isLt; omega)
  rw [hdiv]
  unfold radix27CounterLimit at h
  omega

theorem smallSignature_validWitness13 (σ : Signature)
    (hsmall : SignatureCountersSmall (some σ)) :
    validWitness13 (SigGolfCandidate.Ref.expandRef
      (SigGolfCandidate.Equiv.sigCodec.symm σ)) := by
  obtain ⟨sig, heq, hcnt⟩ := hsmall
  injection heq with heq
  subst sig
  let w := SigGolfCandidate.Ref.expandRef (SigGolfCandidate.Equiv.sigCodec.symm σ)
  let q : BitVec 160 := w.extractLsb' bodyBits13 160
  have hdec : SigGolfCandidate.Equiv.sigOfWit
      (SigGolfCandidate.Ref.toList w) = σ := by
    have hd := SigGolfCandidate.Equiv.witDec_expandRef
      (SigGolfCandidate.Equiv.sigCodec.symm σ)
    change SigGolfCandidate.Equiv.sigOfWit (SigGolfCandidate.Ref.toList w) =
      SigGolfCandidate.Equiv.sigCodec (SigGolfCandidate.Equiv.sigCodec.symm σ) at hd
    simpa only [Equiv.apply_symm_apply] using hd
  have hcounter (lay : Layer) :
      (word q lay.val).toNat = (σ.layers lay).counter.toNat := by
    change ((w.extractLsb' SigGolfCandidate.Packed.bodyBits 160).extractLsb'
      (32 * lay.val) 32).toNat = (σ.layers lay).counter.toNat
    rw [← SigGolfCandidate.Packed.witCounter_toNat_block w lay.val]
    rw [← SigGolfCandidate.Equiv.witCounter_toNat (SigGolfCandidate.Ref.toList w)
      (SigGolfCandidate.Ref.length_toList w) lay]
    rw [hdec]
  change validQ q
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact highQ_lt_of_word_lt q 0 (by rw [hcounter ⟨0, by decide⟩]; exact hcnt ⟨0, by decide⟩)
  · exact highQ_lt_of_word_lt q 1 (by rw [hcounter ⟨1, by decide⟩]; exact hcnt ⟨1, by decide⟩)
  · exact highQ_lt_of_word_lt q 2 (by rw [hcounter ⟨2, by decide⟩]; exact hcnt ⟨2, by decide⟩)
  · exact highQ_lt_of_word_lt q 3 (by rw [hcounter ⟨3, by decide⟩]; exact hcnt ⟨3, by decide⟩)
  · exact highQ_lt_of_word_lt q 4 (by rw [hcounter ⟨4, by decide⟩]; exact hcnt ⟨4, by decide⟩)

theorem word_lt_of_highQ_lt (q : BitVec 160) (i : Nat)
    (h : (highQ q i).toNat < 27) :
    (word q i).toNat < radix27CounterLimit := by
  rw [← word_high_low q i, toNat_join16]
  have hlo := (lowQ q i).isLt
  unfold radix27CounterLimit
  omega

theorem validWitness13_smallSignature (σ : Signature)
    (hvalid : validWitness13 (SigGolfCandidate.Ref.expandRef
      (SigGolfCandidate.Equiv.sigCodec.symm σ))) :
    SignatureCountersSmall (some σ) := by
  let w := SigGolfCandidate.Ref.expandRef (SigGolfCandidate.Equiv.sigCodec.symm σ)
  let q : BitVec 160 := w.extractLsb' bodyBits13 160
  have hdec : SigGolfCandidate.Equiv.sigOfWit
      (SigGolfCandidate.Ref.toList w) = σ := by
    have hd := SigGolfCandidate.Equiv.witDec_expandRef
      (SigGolfCandidate.Equiv.sigCodec.symm σ)
    change SigGolfCandidate.Equiv.sigOfWit (SigGolfCandidate.Ref.toList w) =
      SigGolfCandidate.Equiv.sigCodec (SigGolfCandidate.Equiv.sigCodec.symm σ) at hd
    simpa only [Equiv.apply_symm_apply] using hd
  have hcounter (lay : Layer) :
      (word q lay.val).toNat = (σ.layers lay).counter.toNat := by
    change ((w.extractLsb' SigGolfCandidate.Packed.bodyBits 160).extractLsb'
      (32 * lay.val) 32).toNat = (σ.layers lay).counter.toNat
    rw [← SigGolfCandidate.Packed.witCounter_toNat_block w lay.val]
    rw [← SigGolfCandidate.Equiv.witCounter_toNat (SigGolfCandidate.Ref.toList w)
      (SigGolfCandidate.Ref.length_toList w) lay]
    rw [hdec]
  change validQ q at hvalid
  refine ⟨σ, rfl, ?_⟩
  intro lay
  have hlo : lay.val < 5 := lay.isLt
  have hv : (highQ q lay.val).toNat < 27 := by
    rcases hvalid with ⟨h0, h1, h2, h3, h4⟩
    rcases (show lay.val = 0 ∨ lay.val = 1 ∨ lay.val = 2 ∨
      lay.val = 3 ∨ lay.val = 4 by omega) with h | h | h | h | h
    · simpa only [h] using h0
    · simpa only [h] using h1
    · simpa only [h] using h2
    · simpa only [h] using h3
    · simpa only [h] using h4
  rw [← hcounter]
  exact word_lt_of_highQ_lt q lay.val hv

theorem smallSignature_iff_validWitness13 (σ : Signature) :
    SignatureCountersSmall (some σ) ↔ validWitness13
      (SigGolfCandidate.Ref.expandRef (SigGolfCandidate.Equiv.sigCodec.symm σ)) := by
  exact ⟨smallSignature_validWitness13 σ, validWitness13_smallSignature σ⟩

#print axioms smallSignature_validWitness13
#print axioms smallSignature_iff_validWitness13
end Radix27


end


section -- CounterRefSmall

open OracleComp OracleSpec
namespace SigGolfCandidate.Final
open SigGolfCandidate.Legacy
open SigGolfCandidate.Bridge (relabel relabel_pure relabel_bind relabel_map)
open SphincsSecurity (Digest TopCache Signature)
open SphincsSecurity.Completeness

set_option allowUnsafeReducibility true in
attribute [local reducible] SphincsSecurity.hashOutputBits SphincsSecurity.digestBits
  SphincsSecurity.messageBits SphincsSecurity.publicParameterBits SphincsSecurity.counterBits

noncomputable def refShortValid (σ : Bytes 6404) : Bool := by
  classical
  exact decide (Radix27.validWitness13 (Ref.expandRef σ))

noncomputable def refSmallGame (sk : SecretKey) (m : Message) : OracleComp HashSpec Bool := do
  let (_, cache) ← Ref.keygenRef sk
  match ← Ref.signRef sk cache m with
  | none => pure false
  | some σ => pure (refShortValid σ)

theorem smallSuccess_none : smallSuccess none = false := by
  classical
  simp [smallSuccess, SignatureCountersSmall]

theorem smallSuccess_some (σ : Signature) :
    smallSuccess (some σ) = refShortValid (Equiv.sigCodec.symm σ) := by
  classical
  unfold smallSuccess refShortValid
  simp only [Radix27.smallSignature_iff_validWitness13]

set_option maxRecDepth 100000
set_option maxHeartbeats 100000
theorem refSmallGame_eq (sk : SecretKey) (m : Message) :
    refSmallGame sk m = relabel Equiv.fmtQ (smallGame sk m) := by
  have hs : ∀ (root : Digest) (c : TopCache),
      Ref.signRef sk (Equiv.cacheEnc c) m =
        Option.map Equiv.sigCodec.symm <$>
          relabel Equiv.fmtQ (SphincsSecurity.Seeded.sign (m := Equiv.AComp)
            ⟨sk, 0, root⟩ c m) :=
    fun root c => by rw [Equiv.signRef_eq ⟨sk, 0, root⟩ rfl (Equiv.cacheEnc c) m,
      Equiv.cacheDec_cacheEnc]
  unfold refSmallGame
  rw [Equiv.keygenRef_eq]
  unfold smallGame SphincsSecurity.Seeded.keygenFromSeed
  simp only [relabel_bind, bind_assoc, relabel_pure, pure_bind, map_bind,
    relabel_map, map_pure]
  refine bind_congr fun t => ?_
  refine bind_congr fun region => ?_
  refine bind_congr fun tag => ?_
  rw [hs, bind_map_left]
  refine bind_congr fun s => ?_
  rcases s with _ | σ
  · simp only [Option.map_none, smallSuccess_none]
  · simp only [Option.map_some, smallSuccess_some]

#print axioms refSmallGame_eq
end SigGolfCandidate.Final


end


section -- CounterGame13Shape

open OracleComp OracleSpec
namespace SigGolfCandidate.Final
open SphincsSecurity
open SphincsSecurity.Completeness

noncomputable def game13 (seed : MasterSeed) (message : SphincsSecurity.Message) :
    OracleComp SphincsSecurity.HashSpec Bool := do
  let (pk, cache, sk) ← Seeded.keygenFromSeed seed
  let result ← (Seeded.sign sk cache message : OracleComp SphincsSecurity.HashSpec (Option Signature))
  match result with
  | none => pure false
  | some σ =>
      if smallSuccess (some σ) then
        (Concrete.verify pk message σ : OracleComp SphincsSecurity.HashSpec Bool)
      else pure false

theorem game13_eq_signedWithKeys (seed : MasterSeed) (message : SphincsSecurity.Message) :
    game13 seed message = signedWithKeys seed message >>= fun kr =>
      match kr.2 with
      | none => pure false
      | some σ =>
          if smallSuccess (some σ) then
            (Concrete.verify kr.1.1 message σ : OracleComp SphincsSecurity.HashSpec Bool)
          else pure false := by
  unfold game13 signedWithKeys
  simp only [bind_assoc, pure_bind]

theorem hq_game13 (seed : MasterSeed) (message : SphincsSecurity.Message) :
    Equiv.HQ (game13 seed message) := by
  unfold game13 Seeded.keygenFromSeed Seeded.maskRegion
  simp only [bind_assoc, pure_bind]
  refine Equiv.hq_bind (Equiv.hq_buildLayerTablePaired _ rfl _ _ _
    (fun _ _ => Equiv.hq_otsSecret _ _ _ _ _ _) _ _) fun t => ?_
  refine Equiv.hq_bind (Equiv.hq_sequenceFin _ fun _ =>
    Equiv.hq_bind (Equiv.hq_sequenceFin _ fun _ =>
      Equiv.hq_bind (Equiv.hq_maskSecret _ _ _ _) fun _ => Equiv.hq_pure _)
      fun _ => Equiv.hq_pure _) fun _ => ?_
  refine Equiv.hq_bind (Equiv.hq_mac _ _ _) fun _ => ?_
  refine Equiv.hq_bind (Equiv.hq_sign _ rfl _ _) fun s => ?_
  rcases s with _ | σ
  · exact Equiv.hq_pure _
  · by_cases h : smallSuccess (some σ) = true
    · simp only [h, if_true]
      exact Equiv.hq_verify _ rfl _ _
    · simp only [h, if_false]
      exact Equiv.hq_pure _

#print axioms game13_eq_signedWithKeys
#print axioms hq_game13
end SigGolfCandidate.Final


end


section -- CounterGame13Bound

open OracleComp OracleSpec ENNReal
namespace SigGolfCandidate.Final
open SphincsSecurity SphincsSecurity.Completeness

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
attribute [local irreducible] Seeded.signDigestLoop Concrete.signFrom Concrete.buildLayerTree
  Concrete.sequenceFin digestAttemptLimit encodingAttemptLimit

theorem probEvent_game13_false_le (seed : MasterSeed) (message : SphincsSecurity.Message) :
    Pr[fun r => r.1 = false |
      (simulateQ (randomOracle : QueryImpl SphincsSecurity.HashSpec _)
        (game13 seed message)).run ∅] ≤
    Pr[fun r => ¬ SignatureCountersSmall r.1.2 |
      (simulateQ (randomOracle : QueryImpl SphincsSecurity.HashSpec _)
        (signedWithKeys seed message)).run ∅] := by
  rw [game13_eq_signedWithKeys]
  refine le_trans (probEvent_bind_le_add _ _
    (fun r => ¬ SignatureCountersSmall r.1.2) _ ∅ 0 ?_) (by rw [add_zero])
  rintro ⟨⟨⟨pk, topCache, sk⟩, result⟩, cache⟩ hr hgood
  obtain ⟨signature, hresult, _⟩ :=
    (not_not.mp hgood : SignatureCountersSmall result)
  subst result
  have hv : smallSuccess (some signature) = true := by
    cases h : smallSuccess (some signature) with
    | false => exact (hgood ((smallSuccess_false_iff _).mp h)).elim
    | true => rfl
  dsimp only
  rw [hv]
  rw [nonpos_iff_eq_zero, probEvent_eq_zero_iff]
  rintro ⟨b, cache'⟩ hr'
  obtain ⟨f, hf⟩ := QueryCache.exists_agreesWithFn (spec := SphincsSecurity.HashSpec) cache'
  obtain ⟨hle, hverify, _⟩ := replay_of_mem_support _ cache b cache' hr' f hf
  obtain ⟨hsigned, _⟩ := replay_of_mem_support_of_le _ ∅ _ cache cache' hr hle f hf
  simp only [signedWithKeys, evalWithAnswerFn_bind, evalWithAnswerFn_pure] at hsigned
  have hkeys : evalWithAnswerFn f (Seeded.keygenFromSeed seed) = (pk, topCache, sk) :=
    congrArg Prod.fst hsigned
  have hsign := congrArg Prod.snd hsigned
  rw [hkeys] at hsign
  have htrue := verify_of_keygen_sign f seed message hkeys hsign
  simp only [if_true] at hverify
  rw [htrue] at hverify
  try dsimp only
  rw [← hverify]
  decide

theorem probOutput_game13_false_le (seed : MasterSeed) (message : SphincsSecurity.Message) :
    Pr[= false | (simulateQ (randomOracle : QueryImpl SphincsSecurity.HashSpec _)
      (game13 seed message)).run' ∅] ≤
      digestFactor ^ digestAttemptLimit +
        (numLayers : ℝ≥0∞) * (2⁻¹ : ℝ≥0∞) ^ 530 := by
  rw [StateT.run'_eq, probOutput_map]
  exact (probEvent_game13_false_le seed message).trans
    (probEvent_signedWithKeys_notSmall seed message)

#print axioms probOutput_game13_false_le
end SigGolfCandidate.Final


end


section -- CounterGame13All

open OracleComp OracleSpec ENNReal
namespace SigGolfCandidate.Final
open SphincsSecurity SphincsSecurity.Completeness
open SigGolfCandidate.Bridge (relabel relabel_relabel)

noncomputable def game13HD (seed : MasterSeed) (message : SphincsSecurity.Message) :
    OracleComp (HD →ₒ SphincsSecurity.HashOutput) Bool :=
  relabel toHD (game13 seed message)

theorem relabel_val_game13HD (seed : MasterSeed) (message : SphincsSecurity.Message) :
    relabel Subtype.val (game13HD seed message) = game13 seed message := by
  unfold game13HD
  rw [relabel_relabel]
  exact Bridge.relabel_eq_self_of_allQ Equiv.Honest _ (fun x hx => val_toHD x hx)
    (hq_game13 seed message)

theorem probOutput_game13HD_false_le (seed : MasterSeed) (message : SphincsSecurity.Message) :
    Pr[= false | (simulateQ randomOracle (game13HD seed message)).run' ∅] ≤
      digestFactor ^ digestAttemptLimit +
        (numLayers : ℝ≥0∞) * (2⁻¹ : ℝ≥0∞) ^ 530 := by
  rw [run'_relabel Subtype.val Subtype.val_injective (game13HD seed message) ∅ ∅
    (fun _ => rfl), relabel_val_game13HD]
  exact probOutput_game13_false_le seed message

theorem game13_failure_seeded (seed : MasterSeed) :
    ∑' message : SphincsSecurity.Message,
      Pr[= false | (simulateQ randomOracle (game13HD seed message)).run' ∅] ≤
      ((2 ^ 256 : Nat) : ℝ≥0∞)⁻¹ := by
  calc
    ∑' message : SphincsSecurity.Message,
        Pr[= false | (simulateQ randomOracle (game13HD seed message)).run' ∅]
        ≤ ∑' _message : SphincsSecurity.Message,
          ((2⁻¹ : ℝ≥0∞) ^ 1023 + 5 * (2⁻¹ : ℝ≥0∞) ^ 530) := by
            apply ENNReal.tsum_le_tsum
            intro message
            refine (probOutput_game13HD_false_le seed message).trans ?_
            rw [show ((numLayers : Nat) : ℝ≥0∞) = 5 by norm_num [numLayers]]
            exact add_le_add digestFactor_pow_le le_rfl
    _ = (2 : ℝ≥0∞) ^ 256 *
      ((2⁻¹ : ℝ≥0∞) ^ 1023 + 5 * (2⁻¹ : ℝ≥0∞) ^ 530) := by
        rw [tsum_fintype, Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
          show Fintype.card SphincsSecurity.Message = 2 ^ 256 by simp [messageBits],
          Nat.cast_pow, Nat.cast_ofNat]
    _ ≤ ((2 ^ 256 : Nat) : ℝ≥0∞)⁻¹ := by
      refine le_trans ?_ radix27_complete_numeric
      apply mul_le_mul' le_rfl
      have h : (2⁻¹ : ℝ≥0∞) ^ 1023 ≤
          (2⁻¹ : ℝ≥0∞) ^ 1023 + 5 * (2⁻¹ : ℝ≥0∞) ^ 1256 :=
        le_add_of_nonneg_right (show (0 : ℝ≥0∞) ≤
          5 * (2⁻¹ : ℝ≥0∞) ^ 1256 from bot_le)
      exact add_le_add_left h _

#print axioms game13_failure_seeded
end SigGolfCandidate.Final


end


section -- CounterRefGame13

open OracleComp OracleSpec
namespace SigGolfCandidate.Final
open SigGolfCandidate.Legacy
open SigGolfCandidate.Bridge (relabel relabel_pure relabel_bind relabel_map)
open SphincsSecurity (Digest TopCache Signature)

set_option allowUnsafeReducibility true in
attribute [local reducible] SphincsSecurity.hashOutputBits SphincsSecurity.digestBits
  SphincsSecurity.messageBits SphincsSecurity.publicParameterBits SphincsSecurity.counterBits

noncomputable def refGame13 (sk : SecretKey) (m : Message) : OracleComp HashSpec Bool := do
  let (pk, cache) ← Ref.keygenRef sk
  match ← Ref.signRef sk cache m with
  | none => pure false
  | some σ =>
      if refShortValid σ then Ref.verifyRef m pk (Ref.expandRef σ)
      else pure false

set_option maxRecDepth 100000
set_option maxHeartbeats 100000
theorem refGame13_eq (sk : SecretKey) (m : Message) :
    refGame13 sk m = relabel Equiv.fmtQ (game13 sk m) := by
  have hs : ∀ (root : Digest) (c : TopCache),
      Ref.signRef sk (Equiv.cacheEnc c) m =
        Option.map Equiv.sigCodec.symm <$>
          relabel Equiv.fmtQ (SphincsSecurity.Seeded.sign (m := Equiv.AComp)
            ⟨sk, 0, root⟩ c m) :=
    fun root c => by rw [Equiv.signRef_eq ⟨sk, 0, root⟩ rfl (Equiv.cacheEnc c) m,
      Equiv.cacheDec_cacheEnc]
  unfold refGame13
  rw [Equiv.keygenRef_eq]
  unfold game13 SphincsSecurity.Seeded.keygenFromSeed
  simp only [relabel_bind, bind_assoc, relabel_pure, pure_bind, map_bind,
    relabel_map, map_pure]
  refine bind_congr fun t => ?_
  refine bind_congr fun region => ?_
  refine bind_congr fun tag => ?_
  rw [hs, bind_map_left]
  refine bind_congr fun s => ?_
  rcases s with _ | σ
  · rfl
  · simp only [Option.map_some, smallSuccess_some]
    by_cases h : refShortValid (Equiv.sigCodec.symm σ) = true
    · simp only [h, if_true]
      show Ref.verifySigRef m _ (Equiv.sigCodec.symm σ) = _
      rw [Equiv.verifySigRef_eq, Equiv.sigCodec.apply_symm_apply]
    · simp only [h, Bool.false_eq_true, if_false, relabel_pure]

#print axioms refGame13_eq
end SigGolfCandidate.Final


end


section -- CounterGenericComplete

open OracleComp OracleSpec
namespace SigGolfCandidate.Final
open SigGolfCandidate.Legacy
open SigGolfCandidate.Packed

def shortSub13 (layout : Layout) (images : Phase → Riscv.Image) : Submission where
  sizes := Radix27.shortSizes13
  layout := layout
  image := images

set_option allowUnsafeReducibility true in
attribute [local reducible] SigGolfCandidate.Legacy.Input SigGolfCandidate.Legacy.Output
  shortSub13 Radix27.shortSizes13

example (layout : Layout) (images : Phase → Riscv.Image) :
    Output (shortSub13 layout images).sizes .keygen = (PublicKey × Cache) := rfl

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem successPipe13_eq_refGame13 (layout : Layout) (images : Phase → Riscv.Image)
    (hK : ∀ sk : SecretKey,
      (fun r => r.value) <$> (shortSub13 layout images).run .keygen sk =
        some <$> Ref.keygenRef sk)
    (hS : ∀ (sk : SecretKey) (cache : Cache) (m : Message),
      (fun r => r.value) <$> (shortSub13 layout images).run .sign (sk, cache, m) =
        Option.map Radix27.packOldAny13 <$> Ref.signRef sk cache m)
    (hE : ∀ (m : Message) (pk : PublicKey) (σ : Bytes 6397),
      (fun r => r.value) <$> (shortSub13 layout images).run .expand (m, pk, σ) =
        pure (some (Radix27.expandWitness13 σ)))
    (hV : ∀ (m : Message) (pk : PublicKey) (w : Bytes 6404),
      (fun r => r.value.isSome) <$> (shortSub13 layout images).run .verify (m, pk, w) =
        Ref.verifyRef m pk w)
    (hBad : ∀ (m : Message) (pk : PublicKey) (σ : Bytes 6404),
      CanonicalWitness (Ref.expandRef σ) →
      ¬ Radix27.validWitness13 (Ref.expandRef σ) →
      Ref.verifyRef m pk (Radix27.expandWitness13 (Radix27.packOldAny13 σ)) = pure false)
    (sk : SecretKey) (m : Message) :
    successPipe (shortSub13 layout images) sk m = refGame13 sk m := by
  unfold successPipe refGame13
  rw [hK]
  change ((some <$> Ref.keygenRef sk) >>= fun kc : Option (PublicKey × Cache) => _) = _
  have hmap (f : Option (PublicKey × Cache) → OracleComp HashSpec Bool) :
      ((some <$> Ref.keygenRef sk) >>= f) =
        (Ref.keygenRef sk >>= fun kc => f (some kc)) := by
    rw [bind_map_left]
  rw [hmap]
  refine bind_congr fun kc => ?_
  rcases kc with ⟨pk, cache⟩
  simp only
  rw [hS, bind_map_left]
  apply OracleComp.bind_congr_of_forall_mem_support
  intro s hs
  rcases s with _ | σ
  · rfl
  simp only [Option.map_some]
  rw [hE, pure_bind]
  dsimp only
  rw [hV]
  have hc := signRef_support_canonical sk cache m (some σ) hs σ rfl
  by_cases hv : Radix27.validWitness13 (Ref.expandRef σ)
  · have hbool : refShortValid σ = true := by
      classical
      simp [refShortValid, hv]
    rw [show Radix27.expandWitness13 (Radix27.packOldAny13 σ) =
      Ref.expandRef σ by
        exact Radix27.expand_shrinkWitnessAny13 _ hv]
    simp only [hbool, if_true]
  · have hbool : refShortValid σ = false := by
      classical
      simp [refShortValid, hv]
    rw [hBad m pk σ hc hv]
    simp only [hbool, Bool.false_eq_true, if_false]

#print axioms successPipe13_eq_refGame13
end SigGolfCandidate.Final


end


section -- CounterComplete13

open OracleComp OracleSpec ENNReal
namespace SigGolfCandidate.Final
open SigGolfCandidate.Legacy
open SigGolfCandidate.Bridge (relabel relabel_relabel)

set_option allowUnsafeReducibility true in
attribute [local reducible] SphincsSecurity.hashOutputBits SphincsSecurity.digestBits
  SphincsSecurity.messageBits SphincsSecurity.publicParameterBits SphincsSecurity.counterBits
  SigGolfCandidate.Legacy.Input SigGolfCandidate.Legacy.Output
  shortSub13 Radix27.shortSizes13

structure Ref13 (layout : Layout) (images : Phase → Riscv.Image) : Prop where
  keygen : ∀ sk : SecretKey,
    (fun r => r.value) <$> (shortSub13 layout images).run .keygen sk =
      some <$> Ref.keygenRef sk
  sign : ∀ (sk : SecretKey) (cache : Cache) (m : Message),
    (fun r => r.value) <$> (shortSub13 layout images).run .sign (sk, cache, m) =
      Option.map Radix27.packOldAny13 <$> Ref.signRef sk cache m
  expand : ∀ (m : Message) (pk : PublicKey) (σ : Bytes 6397),
    (fun r => r.value) <$> (shortSub13 layout images).run .expand (m, pk, σ) =
      pure (some (Radix27.expandWitness13 σ))
  verify : ∀ (m : Message) (pk : PublicKey) (w : Bytes 6404),
    (fun r => r.value.isSome) <$> (shortSub13 layout images).run .verify (m, pk, w) =
      Ref.verifyRef m pk w
  bad : ∀ (m : Message) (pk : PublicKey) (σ : Bytes 6404),
    SigGolfCandidate.Packed.CanonicalWitness (Ref.expandRef σ) →
    ¬ Radix27.validWitness13 (Ref.expandRef σ) →
    Ref.verifyRef m pk (Radix27.expandWitness13 (Radix27.packOldAny13 σ)) = pure false

theorem success_honest13_eq_game13 (layout : Layout) (images : Phase → Riscv.Image)
    (h : Ref13 layout images) (sk : SecretKey) (m : Message) :
    HonestResult.success <$> (shortSub13 layout images).honest sk m =
      relabel Equiv.fmtQ (game13 sk m) := by
  rw [success_honest_eq, successPipe13_eq_refGame13 layout images
    h.keygen h.sign h.expand h.verify h.bad sk m, refGame13_eq]

theorem allSucceed13_eq_relabel (layout : Layout) (images : Phase → Riscv.Image)
    (h : Ref13 layout images) (sk : SecretKey) :
    HonestSummary.allSucceed <$> (shortSub13 layout images).allMessages sk =
      relabel encHD (foldAll (Finset.univ : Finset Message).toList (game13HD sk) true) := by
  rw [allSucceed_allMessages, ← foldAll_relabel]
  refine congrArg (fun P => foldAll _ P true) (funext fun m => ?_)
  rw [success_honest13_eq_game13 layout images h sk m,
    ← relabel_val_game13HD, relabel_relabel]
  rfl

theorem complete13 (layout : Layout) (images : Phase → Riscv.Image)
    (h : Ref13 layout images) : (shortSub13 layout images).Complete := by
  intro sk
  set L := (Finset.univ : Finset Message).toList
  set F := foldAll L (game13HD sk) true
  have hP : Pr[fun summary => summary.allSucceed = true |
        withRandomOracle ((shortSub13 layout images).allMessages sk)] =
      Pr[= true | (simulateQ randomOracle F).run' ∅] := by
    have e1 : Pr[fun summary => summary.allSucceed = true |
          withRandomOracle ((shortSub13 layout images).allMessages sk)] =
        Pr[= true | withRandomOracle
          (HonestSummary.allSucceed <$> (shortSub13 layout images).allMessages sk)] := by
      rw [withRandomOracle_map, ← probEvent_eq_eq_probOutput, probEvent_map]
      rfl
    rw [e1, allSucceed13_eq_relabel layout images h]
    unfold withRandomOracle
    rw [← run'_relabel encHD encHD_injective F ∅ ∅ (fun _ => rfl)]
  have hF : Pr[= false | (simulateQ randomOracle F).run' ∅] ≤ FAILURE := by
    refine (probOutput_false_foldAll_le L (game13HD sk)).trans ?_
    rw [Finset.sum_map_toList]
    refine le_trans ?_ failure_ge
    rw [← tsum_fintype (L := SummationFilter.unconditional Message)]
    exact game13_failure_seeded sk
  have h1 : Pr[= true | (simulateQ randomOracle F).run' ∅] +
      Pr[= false | (simulateQ randomOracle F).run' ∅] = 1 := by
    simp
  rw [hP, tsub_le_iff_right, ← h1]
  exact add_le_add le_rfl hF

#print axioms complete13
end SigGolfCandidate.Final


end


section -- Radix27InvalidOnly

namespace Radix27
open SigGolfCandidate.Legacy

theorem canonical_counter0_lt (w : Bytes 6404)
    (h : SigGolfCandidate.Packed.CanonicalWitness w) :
    (word (w.extractLsb' bodyBits13 160) 0).toNat < 4194304 := by
  let q := w.extractLsb' bodyBits13 160
  have hz : q.extractLsb' 22 10 = 0 := h.1
  have hs : word q 0 = q.extractLsb' 22 10 ++ q.extractLsb' 0 22 := by
    unfold word
    bv_normalize
  rw [hs, hz]
  have hzero : (0#10 ++ q.extractLsb' 0 22).toNat =
      (q.extractLsb' 0 22).toNat := by
    rw [BitVec.toNat_append]
    simp
  change (0#10 ++ q.extractLsb' 0 22).toNat < 4194304
  rw [hzero]
  simpa using BitVec.isLt (q.extractLsb' 0 22)

theorem counter0_ge_not_countersOk (w : Bytes 6404)
    (h0 : 4194304 ≤ (word (w.extractLsb' bodyBits13 160) 0).toNat) :
    SigGolfCandidate.Ref.countersOk (SigGolfCandidate.Ref.toList w) = false := by
  cases hc : SigGolfCandidate.Ref.countersOk (SigGolfCandidate.Ref.toList w) with
  | false => rfl
  | true =>
    have hall := List.all_eq_true.mp hc
    have h := hall 0 (List.mem_range.mpr (by decide : 0 < 5))
    have hlt : SigGolfCandidate.Ref.witCounter (SigGolfCandidate.Ref.toList w) 0 <
        SigGolfCandidate.Ref.cMax := of_decide_eq_true h
    rw [SigGolfCandidate.Packed.witCounter_toNat_block] at hlt
    change (word (w.extractLsb' bodyBits13 160) 0).toNat < 2 ^ 22 at hlt
    omega

theorem invalid_fallback_counter0 (w : Bytes 6404)
    (h0 : (word (w.extractLsb' bodyBits13 160) 0).toNat < 4194304)
    (hb : ¬ validWitness13 w) :
    4194304 ≤
      (word ((expandWitness13 (shrinkWitnessAny13 w)).extractLsb' bodyBits13 160) 0).toNat := by
  let q := w.extractLsb' bodyBits13 160
  have hr : ¬ reservedMarker q := by
    intro h
    exact Nat.not_le.mpr h0 h.1
  have hv : ¬ validQ q := hb
  have hi := unrepresentable_invalid q hr hv
  have heq : (expandWitness13 (shrinkWitnessAny13 w)).extractLsb' bodyBits13 160 =
      expand13 (pack13 q) := by
    simp only [expandWitness13, shrinkWitnessAny13, trailer13,
      BitVec.extractLsb'_append_eq_left]
    rfl
  rw [heq]
  exact hi

theorem invalid_fallback_verify_false (m : Message) (pk : PublicKey)
    (w : Bytes 6404)
    (h0 : (word (w.extractLsb' bodyBits13 160) 0).toNat < 4194304)
    (hb : ¬ validWitness13 w) :
    SigGolfCandidate.Ref.verifyRef m pk
      (expandWitness13 (shrinkWitnessAny13 w)) = pure false := by
  have h0bad := invalid_fallback_counter0 w h0 hb
  have hc : SigGolfCandidate.Ref.countersOk
      (SigGolfCandidate.Ref.toList (expandWitness13 (shrinkWitnessAny13 w))) = false :=
    counter0_ge_not_countersOk _ h0bad
  simp only [SigGolfCandidate.Ref.verifyRef, SigGolfCandidate.Ref.verifyList,
    hc, Bool.not_false, if_true]

#print axioms invalid_fallback_verify_false
end Radix27


end


section -- CounterComplete13Discharged

open OracleComp OracleSpec
namespace SigGolfCandidate.Final
open SigGolfCandidate.Legacy

theorem complete13_of_phase_refinements
    (layout : Layout) (images : Phase → Riscv.Image)
    (hK : ∀ sk : SecretKey,
      (fun r => r.value) <$> (shortSub13 layout images).run .keygen sk =
        some <$> Ref.keygenRef sk)
    (hS : ∀ (sk : SecretKey) (cache : Cache) (m : Message),
      (fun r => r.value) <$> (shortSub13 layout images).run .sign (sk, cache, m) =
        Option.map Radix27.packOldAny13 <$> Ref.signRef sk cache m)
    (hE : ∀ (m : Message) (pk : PublicKey) (σ : Bytes 6397),
      (fun r => r.value) <$> (shortSub13 layout images).run .expand (m, pk, σ) =
        pure (some (Radix27.expandWitness13 σ)))
    (hV : ∀ (m : Message) (pk : PublicKey) (w : Bytes 6404),
      (fun r => r.value.isSome) <$> (shortSub13 layout images).run .verify (m, pk, w) =
        Ref.verifyRef m pk w) :
    (shortSub13 layout images).Complete := by
  apply complete13 layout images
  refine ⟨hK, hS, hE, hV, ?_⟩
  intro m pk σ hc hv
  exact Radix27.invalid_fallback_verify_false m pk (Ref.expandRef σ)
    (Radix27.canonical_counter0_lt _ hc) hv

#print axioms complete13_of_phase_refinements
end SigGolfCandidate.Final


end


section -- Radix27ReductionTry

namespace SigGolfCandidate.Radix27

open SigGolfCandidate.Legacy

def rank5 (h0 h1 h2 h3 h4 : Nat) : Nat :=
  h0 + 27 * (h1 + 27 * (h2 + 27 * (h3 + 27 * h4)))

theorem rank5_lt (h0 h1 h2 h3 h4 : Nat)
    (H0 : h0 < 27) (H1 : h1 < 27) (H2 : h2 < 27)
    (H3 : h3 < 27) (H4 : h4 < 27) :
    rank5 h0 h1 h2 h3 h4 < 14348907 := by
  unfold rank5
  omega

theorem rank5_split (h0 h1 h2 h3 h4 : Nat)
    (H0 : h0 < 27) (H1 : h1 < 27) (H2 : h2 < 27)
    (H3 : h3 < 27) (H4 : h4 < 27) :
    (rank5 h0 h1 h2 h3 h4 % 27 = h0) ∧
    (rank5 h0 h1 h2 h3 h4 / 27 % 27 = h1) ∧
    (rank5 h0 h1 h2 h3 h4 / 729 % 27 = h2) ∧
    (rank5 h0 h1 h2 h3 h4 / 19683 % 27 = h3) ∧
    (rank5 h0 h1 h2 h3 h4 / 531441 % 27 = h4) := by
  unfold rank5
  omega

theorem rank5_join (t : Nat) (H : t < 14348907) :
    rank5 (t % 27) (t / 27 % 27) (t / 729 % 27)
      (t / 19683 % 27) (t / 531441 % 27) = t := by
  unfold rank5
  omega

def lo16 (b : BitVec 80) (i : Nat) : BitVec 16 := b.extractLsb' (16 * i) 16
def word (q : BitVec 160) (i : Nat) : BitVec 32 := q.extractLsb' (32 * i) 32
def lowQ (q : BitVec 160) (i : Nat) : BitVec 16 := (word q i).extractLsb' 0 16
def highQ (q : BitVec 160) (i : Nat) : BitVec 16 := (word q i).extractLsb' 16 16

def lowPack (q : BitVec 160) : BitVec 80 :=
  lowQ q 4 ++ lowQ q 3 ++ lowQ q 2 ++ lowQ q 1 ++ lowQ q 0

def validQ (q : BitVec 160) : Prop :=
  (highQ q 0).toNat < 27 ∧ (highQ q 1).toNat < 27 ∧
  (highQ q 2).toNat < 27 ∧ (highQ q 3).toNat < 27 ∧
  (highQ q 4).toNat < 27

def rankQ (q : BitVec 160) : Nat :=
  rank5 (highQ q 0).toNat (highQ q 1).toNat (highQ q 2).toNat
    (highQ q 3).toNat (highQ q 4).toNat

theorem lowPack_part0 (q : BitVec 160) : lo16 (lowPack q) 0 = lowQ q 0 := by
  unfold lo16 lowPack
  bv_normalize
theorem lowPack_part1 (q : BitVec 160) : lo16 (lowPack q) 1 = lowQ q 1 := by
  unfold lo16 lowPack
  bv_normalize
theorem lowPack_part2 (q : BitVec 160) : lo16 (lowPack q) 2 = lowQ q 2 := by
  unfold lo16 lowPack
  bv_normalize
theorem lowPack_part3 (q : BitVec 160) : lo16 (lowPack q) 3 = lowQ q 3 := by
  unfold lo16 lowPack
  bv_normalize
theorem lowPack_part4 (q : BitVec 160) : lo16 (lowPack q) 4 = lowQ q 4 := by
  unfold lo16 lowPack
  bv_normalize

theorem ofNat_highQ (q : BitVec 160) (i : Nat) :
    BitVec.ofNat 16 (highQ q i).toNat = highQ q i := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem word_high_low (q : BitVec 160) (i : Nat) :
    highQ q i ++ lowQ q i = word q i := by
  unfold highQ lowQ
  exact BitVec.extractLsb'_append_extractLsb' (x := word q i) (w := 16) (len := 16)

theorem words_join (q : BitVec 160) :
    word q 4 ++ word q 3 ++ word q 2 ++ word q 1 ++ word q 0 = q := by
  unfold word
  bv_normalize

def validBlock (l : BitVec 80) (t : Nat) : BitVec 160 :=
  ((BitVec.ofNat 16 (t / 531441 % 27)) ++ lo16 l 4) ++
  ((BitVec.ofNat 16 (t / 19683 % 27)) ++ lo16 l 3) ++
  ((BitVec.ofNat 16 (t / 729 % 27)) ++ lo16 l 2) ++
  ((BitVec.ofNat 16 (t / 27 % 27)) ++ lo16 l 1) ++
  ((BitVec.ofNat 16 (t % 27)) ++ lo16 l 0)

def reservedBlock (l : BitVec 80) (t : Nat) : BitVec 160 :=
  (0#32) ++ ((0#16) ++ lo16 l 4) ++
  (lo16 l 3 ++ lo16 l 2) ++
  (lo16 l 1 ++ lo16 l 0) ++
  BitVec.ofNat 32 (4194304 + (t - 14348907))

def reservedLows (q : BitVec 160) : BitVec 80 :=
  (word q 3).extractLsb' 0 16 ++
  (word q 2).extractLsb' 16 16 ++
  (word q 2).extractLsb' 0 16 ++
  (word q 1).extractLsb' 16 16 ++
  (word q 1).extractLsb' 0 16

theorem lowPieces_eq (l : BitVec 80) :
    lo16 l 4 ++ lo16 l 3 ++ lo16 l 2 ++ lo16 l 1 ++ lo16 l 0 = l := by
  unfold lo16
  bv_normalize

theorem extract_nested {n : Nat} (x : BitVec n) (a b len mid : Nat)
    (h : b + len ≤ mid) :
    (x.extractLsb' a mid).extractLsb' b len = x.extractLsb' (a + b) len := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb']
  have h1 : i < len := hi
  have h2 : b + i < mid := by omega
  simp [h1, h2, Nat.add_assoc]

theorem reserved_top (l : BitVec 80) :
    BitVec.extractLsb' 0 16
      (BitVec.extractLsb' 0 32 (0#48 ++ BitVec.extractLsb' 64 16 l)) = lo16 l 4 := by
  unfold lo16
  rw [extract_nested (h := by decide), BitVec.extractLsb'_append_eq_right]

theorem nested3 (l : BitVec 80) :
    BitVec.extractLsb' 16 16 (BitVec.extractLsb' 32 32 l) = lo16 l 3 := by
  unfold lo16
  rw [extract_nested (h := by decide)]
theorem nested2 (l : BitVec 80) :
    BitVec.extractLsb' 0 16 (BitVec.extractLsb' 32 32 l) = lo16 l 2 := by
  unfold lo16
  rw [extract_nested (h := by decide)]
theorem nested1 (l : BitVec 80) :
    BitVec.extractLsb' 16 16 (BitVec.extractLsb' 0 32 l) = lo16 l 1 := by
  unfold lo16
  rw [extract_nested (h := by decide)]
theorem nested0 (l : BitVec 80) :
    BitVec.extractLsb' 0 16 (BitVec.extractLsb' 0 32 l) = lo16 l 0 := by
  unfold lo16
  rw [extract_nested (h := by decide)]

theorem validBlock_lows (l : BitVec 80) (t : Nat) :
    lowPack (validBlock l t) = l := by
  unfold lowPack lowQ word validBlock lo16
  bv_normalize

theorem validBlock_high0 (l : BitVec 80) (t : Nat) :
    (highQ (validBlock l t) 0).toNat = t % 27 := by
  unfold highQ word validBlock lo16
  bv_normalize
  simp [BitVec.toNat_ofNat] at *
  omega

theorem validBlock_high1 (l : BitVec 80) (t : Nat) :
    (highQ (validBlock l t) 1).toNat = t / 27 % 27 := by
  unfold highQ word validBlock lo16
  bv_normalize
  simp [BitVec.toNat_ofNat] at *
  omega

theorem validBlock_high2 (l : BitVec 80) (t : Nat) :
    (highQ (validBlock l t) 2).toNat = t / 729 % 27 := by
  unfold highQ word validBlock lo16
  bv_normalize
  simp [BitVec.toNat_ofNat] at *
  omega

theorem validBlock_high3 (l : BitVec 80) (t : Nat) :
    (highQ (validBlock l t) 3).toNat = t / 19683 % 27 := by
  unfold highQ word validBlock lo16
  bv_normalize
  simp [BitVec.toNat_ofNat] at *
  omega

theorem validBlock_high4 (l : BitVec 80) (t : Nat) :
    (highQ (validBlock l t) 4).toNat = t / 531441 % 27 := by
  unfold highQ word validBlock lo16
  bv_normalize
  simp [BitVec.toNat_ofNat] at *
  omega

theorem validBlock_valid (l : BitVec 80) (t : Nat) :
    validQ (validBlock l t) := by
  unfold validQ
  rw [validBlock_high0, validBlock_high1, validBlock_high2,
    validBlock_high3, validBlock_high4]
  omega

theorem validBlock_rank (l : BitVec 80) (t : Nat)
    (ht : t < 14348907) :
    rankQ (validBlock l t) = t := by
  unfold rankQ
  rw [validBlock_high0, validBlock_high1, validBlock_high2,
    validBlock_high3, validBlock_high4]
  exact rank5_join t ht

theorem validBlock_rankQ (q : BitVec 160) (h : validQ q) :
    validBlock (lowPack q) (rankQ q) = q := by
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  obtain ⟨s0, s1, s2, s3, s4⟩ :=
    rank5_split (highQ q 0).toNat (highQ q 1).toNat
      (highQ q 2).toNat (highQ q 3).toNat (highQ q 4).toNat
      h0 h1 h2 h3 h4
  have e0 : BitVec.ofNat 16 (rankQ q % 27) = highQ q 0 := by
    rw [show rankQ q % 27 = (highQ q 0).toNat from s0]
    exact ofNat_highQ q 0
  have e1 : BitVec.ofNat 16 (rankQ q / 27 % 27) = highQ q 1 := by
    rw [show rankQ q / 27 % 27 = (highQ q 1).toNat from s1]
    exact ofNat_highQ q 1
  have e2 : BitVec.ofNat 16 (rankQ q / 729 % 27) = highQ q 2 := by
    rw [show rankQ q / 729 % 27 = (highQ q 2).toNat from s2]
    exact ofNat_highQ q 2
  have e3 : BitVec.ofNat 16 (rankQ q / 19683 % 27) = highQ q 3 := by
    rw [show rankQ q / 19683 % 27 = (highQ q 3).toNat from s3]
    exact ofNat_highQ q 3
  have e4 : BitVec.ofNat 16 (rankQ q / 531441 % 27) = highQ q 4 := by
    rw [show rankQ q / 531441 % 27 = (highQ q 4).toNat from s4]
    exact ofNat_highQ q 4
  unfold validBlock
  rw [e0, e1, e2, e3, e4]
  rw [lowPack_part0, lowPack_part1, lowPack_part2, lowPack_part3, lowPack_part4]
  rw [word_high_low q 0, word_high_low q 1,
    word_high_low q 2, word_high_low q 3, word_high_low q 4]
  exact words_join q

theorem reservedBlock_lows (l : BitVec 80) (t : Nat) :
    reservedLows (reservedBlock l t) = l := by
  unfold reservedLows word reservedBlock lo16
  bv_normalize
  rename_i hneq
  rw [Bool.not_eq_true_eq_eq_false, beq_eq_false_iff_ne] at hneq
  apply hneq
  rw [reserved_top, nested3, nested2, nested1, nested0]
  exact lowPieces_eq l

theorem toNat_join16 (hi lo : BitVec 16) :
    (hi ++ lo).toNat = hi.toNat * 65536 + lo.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt (BitVec.isLt lo)]
  simp [Nat.shiftLeft_eq]

theorem validBlock_word0 (l : BitVec 80) (t : Nat) :
    word (validBlock l t) 0 = BitVec.ofNat 16 (t % 27) ++ lo16 l 0 := by
  unfold word validBlock lo16
  bv_normalize

theorem validBlock_word0_lt (l : BitVec 80) (t : Nat) :
    (word (validBlock l t) 0).toNat < 4194304 := by
  rw [validBlock_word0, toNat_join16, BitVec.toNat_ofNat]
  have ht : t % 27 < 65536 := by omega
  rw [Nat.mod_eq_of_lt ht]
  have hlo := BitVec.isLt (lo16 l 0)
  norm_num at hlo
  omega

theorem reservedBlock_word0 (l : BitVec 80) (t : Nat) :
    word (reservedBlock l t) 0 = BitVec.ofNat 32 (4194304 + (t - 14348907)) := by
  unfold word reservedBlock lo16
  bv_normalize

theorem reservedBlock_word0_nat (l : BitVec 80) (t : Nat)
    (ht : t < 16777216) :
    (word (reservedBlock l t) 0).toNat = 4194304 + (t - 14348907) := by
  rw [reservedBlock_word0, BitVec.toNat_ofNat]
  have hn : 4194304 + (t - 14348907) < 2 ^ 32 := by omega
  exact Nat.mod_eq_of_lt hn

def reservedMarker (q : BitVec 160) : Prop :=
  4194304 ≤ (word q 0).toNat ∧ (word q 0).toNat < 6622613

instance (q : BitVec 160) : Decidable (validQ q) := by
  unfold validQ
  infer_instance

instance (q : BitVec 160) : Decidable (reservedMarker q) := by
  unfold reservedMarker
  infer_instance

theorem validBlock_not_reserved (l : BitVec 80) (t : Nat) :
    ¬ reservedMarker (validBlock l t) := by
  intro h
  exact (Nat.not_le.mpr (validBlock_word0_lt l t)) h.1

theorem validQ_not_reserved (q : BitVec 160) (h : validQ q) :
    ¬ reservedMarker q := by
  intro hr
  have h0 : (highQ q 0).toNat < 27 := h.1
  have hlo := BitVec.isLt (lowQ q 0)
  have hw := word_high_low q 0
  have hn : (word q 0).toNat =
      (highQ q 0).toNat * 65536 + (lowQ q 0).toNat := by
    rw [← hw, toNat_join16]
  unfold reservedMarker at hr
  norm_num at hlo
  omega

theorem rankQ_lt (q : BitVec 160) (h : validQ q) : rankQ q < 14348907 := by
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  exact rank5_lt _ _ _ _ _ h0 h1 h2 h3 h4

theorem reservedBlock_marker (l : BitVec 80) (t : Nat)
    (hlo : 14348907 ≤ t) (hhi : t < 16777216) :
    reservedMarker (reservedBlock l t) := by
  rw [reservedMarker, reservedBlock_word0_nat l t hhi]
  omega

def expand13 (p : BitVec 104) : BitVec 160 :=
  let t := (p.extractLsb' 80 24).toNat
  let l := p.extractLsb' 0 80
  if t < 14348907 then validBlock l t else reservedBlock l t

def pack13 (q : BitVec 160) : BitVec 104 :=
  if reservedMarker q then
    BitVec.ofNat 24 ((word q 0).toNat - 4194304 + 14348907) ++ reservedLows q
  else if validQ q then
    BitVec.ofNat 24 (rankQ q) ++ lowPack q
  else
    BitVec.ofNat 24 14348907 ++ (0#80)

theorem pack13_validBlock (l : BitVec 80) (t : Nat)
    (ht : t < 14348907) :
    pack13 (validBlock l t) = BitVec.ofNat 24 t ++ l := by
  simp only [pack13, if_neg (validBlock_not_reserved l t),
    if_pos (validBlock_valid l t), validBlock_rank l t ht,
    validBlock_lows]

theorem pack13_validQ (q : BitVec 160) (h : validQ q) :
    pack13 q = BitVec.ofNat 24 (rankQ q) ++ lowPack q := by
  simp only [pack13, if_neg (validQ_not_reserved q h), if_pos h]

theorem expand13_join_valid (l : BitVec 80) (t : Nat)
    (ht : t < 14348907) :
    expand13 (BitVec.ofNat 24 t ++ l) = validBlock l t := by
  unfold expand13
  rw [BitVec.extractLsb'_append_eq_left, BitVec.extractLsb'_append_eq_right,
    BitVec.toNat_ofNat]
  have h24 : t < 2 ^ 24 := by omega
  rw [Nat.mod_eq_of_lt h24, if_pos ht]

theorem expand13_join_reserved (l : BitVec 80) (t : Nat)
    (hlo : 14348907 ≤ t) (hhi : t < 16777216) :
    expand13 (BitVec.ofNat 24 t ++ l) = reservedBlock l t := by
  unfold expand13
  rw [BitVec.extractLsb'_append_eq_left, BitVec.extractLsb'_append_eq_right,
    BitVec.toNat_ofNat]
  have h24 : t < 2 ^ 24 := by omega
  rw [Nat.mod_eq_of_lt h24, if_neg (by omega : ¬t < 14348907)]

theorem reservedCode_invalid (p : BitVec 104)
    (h : 14348907 ≤ (p.extractLsb' 80 24).toNat) :
    4194304 ≤ (word (expand13 p) 0).toNat := by
  let t := (p.extractLsb' 80 24).toNat
  let l := p.extractLsb' 0 80
  have ht24 : t < 16777216 := by
    change (p.extractLsb' 80 24).toNat < 2 ^ 24
    exact BitVec.isLt _
  change 4194304 ≤
    (word (if t < 14348907 then validBlock l t else reservedBlock l t) 0).toNat
  rw [if_neg (by omega : ¬t < 14348907), reservedBlock_word0_nat l t ht24]
  omega

def fallback13 : BitVec 104 := BitVec.ofNat 24 14348907 ++ (0#80)

theorem fallback13_invalid :
    4194304 ≤ (word (expand13 fallback13) 0).toNat := by
  apply reservedCode_invalid
  simp [fallback13, BitVec.toNat_ofNat]

theorem pack13_unrepresentable (q : BitVec 160)
    (hr : ¬ reservedMarker q) (hv : ¬ validQ q) :
    pack13 q = fallback13 := by
  simp only [pack13, if_neg hr, if_neg hv, fallback13]

theorem unrepresentable_invalid (q : BitVec 160)
    (hr : ¬ reservedMarker q) (hv : ¬ validQ q) :
    4194304 ≤ (word (expand13 (pack13 q)) 0).toNat := by
  rw [pack13_unrepresentable q hr hv]
  exact fallback13_invalid

theorem expand13_pack13_valid (q : BitVec 160) (h : validQ q) :
    expand13 (pack13 q) = q := by
  rw [pack13_validQ q h, expand13_join_valid _ _ (rankQ_lt q h)]
  exact validBlock_rankQ q h

theorem pack13_reservedBlock (l : BitVec 80) (t : Nat)
    (hlo : 14348907 ≤ t) (hhi : t < 16777216) :
    pack13 (reservedBlock l t) = BitVec.ofNat 24 t ++ l := by
  rw [pack13, if_pos (reservedBlock_marker l t hlo hhi),
    reservedBlock_word0_nat l t hhi, reservedBlock_lows]
  have hn : 4194304 + (t - 14348907) - 4194304 + 14348907 = t := by omega
  rw [hn]

theorem pack13_expand13 (p : BitVec 104) :
    pack13 (expand13 p) = p := by
  let t := (p.extractLsb' 80 24).toNat
  let l := p.extractLsb' 0 80
  have ht24 : t < 16777216 := by
    change (p.extractLsb' 80 24).toNat < 2 ^ 24
    exact BitVec.isLt _
  have hj : BitVec.ofNat 24 t ++ l = p := by
    simpa only [t, l, BitVec.ofNat_toNat, BitVec.setWidth_eq] using
      (BitVec.extractLsb'_append_extractLsb' (x := p) (w := 24) (len := 80))
  change pack13 (if t < 14348907 then validBlock l t else reservedBlock l t) = p
  by_cases ht : t < 14348907
  · rw [if_pos ht, pack13_validBlock l t ht]
    exact hj
  · have hlo : 14348907 ≤ t := by omega
    rw [if_neg ht, pack13_reservedBlock l t hlo ht24]
    exact hj

abbrev shortSizes13 : Sizes := ⟨6397, 6404, 131072⟩
abbrev bodyBits13 : Nat := 8 * 6384

def body13 (b : Bytes 6397) : Bytes 6384 := b.extractLsb' 0 bodyBits13
def trailer13 (b : Bytes 6397) : BitVec 104 := b.extractLsb' bodyBits13 104
def join13 (c : BitVec 104) (v : Bytes 6384) : Bytes 6397 := c ++ v

theorem join13_parts (b : Bytes 6397) : join13 (trailer13 b) (body13 b) = b := by
  simpa only [join13, trailer13, body13, bodyBits13] using
    (BitVec.extractLsb'_append_extractLsb' (x := b) (w := 104) (len := 8 * 6384))

def expandWitness13 (b : Bytes 6397) : Bytes 6404 :=
  expand13 (trailer13 b) ++ body13 b

def shrinkWitnessAny13 (w : Bytes 6404) : Bytes 6397 :=
  pack13 (w.extractLsb' bodyBits13 160) ++ w.extractLsb' 0 bodyBits13

theorem shrinkAny_expandWitness13 (b : Bytes 6397) :
    shrinkWitnessAny13 (expandWitness13 b) = b := by
  simp only [shrinkWitnessAny13, expandWitness13, trailer13, body13,
    BitVec.extractLsb'_append_eq_left, BitVec.extractLsb'_append_eq_right,
    pack13_expand13]
  exact join13_parts b

def validWitness13 (w : Bytes 6404) : Prop :=
  validQ (w.extractLsb' bodyBits13 160)

theorem expand_shrinkWitnessAny13 (w : Bytes 6404) (h : validWitness13 w) :
    expandWitness13 (shrinkWitnessAny13 w) = w := by
  simp only [expandWitness13, shrinkWitnessAny13, trailer13, body13,
    BitVec.extractLsb'_append_eq_left, BitVec.extractLsb'_append_eq_right]
  rw [expand13_pack13_valid _ h]
  simpa only [bodyBits13] using
    (BitVec.extractLsb'_append_extractLsb' (x := w) (w := 160) (len := 8 * 6384))

def unpackOld13 (b : Bytes 6397) : Bytes 6404 :=
  SigGolfCandidate.Ref.unexpandRef (expandWitness13 b)

def packOldAny13 (b : Bytes 6404) : Bytes 6397 :=
  shrinkWitnessAny13 (SigGolfCandidate.Ref.expandRef b)

theorem packAny_unpackOld13 (b : Bytes 6397) :
    packOldAny13 (unpackOld13 b) = b := by
  unfold packOldAny13 unpackOld13
  rw [SigGolfCandidate.Ref.expandRef_unexpandRef,
    shrinkAny_expandWitness13]

theorem expand_unpackOld13 (b : Bytes 6397) :
    SigGolfCandidate.Ref.expandRef (unpackOld13 b) = expandWitness13 b := by
  exact SigGolfCandidate.Ref.expandRef_unexpandRef _

theorem unpack_packOldAny13 (σ : Bytes 6404)
    (h : validWitness13 (SigGolfCandidate.Ref.expandRef σ)) :
    unpackOld13 (packOldAny13 σ) = σ := by
  unfold unpackOld13 packOldAny13
  rw [expand_shrinkWitnessAny13 _ h,
    SigGolfCandidate.Ref.unexpandRef_expandRef]



end SigGolfCandidate.Radix27

namespace SigGolfCandidate.Radix27
open SigGolfCandidate.Legacy OracleComp OracleSpec SigGolfCandidate.Packed
abbrev sizes : Sizes := shortSizes13
def shortSubmission (layout : Layout) (images : Phase → Riscv.Image) : Submission where
  sizes := sizes
  layout := layout
  image := images
def liftForgery : Forgery sizes → Forgery SigGolfCandidate.Packed.oldSizes
  | .witness message witness => .witness message witness
  | .signature message signature => .signature message (unpackOld13 signature)
end SigGolfCandidate.Radix27

/-!
# Total counter compression and one-way strong security

The total compression map is a left inverse of expansion on every packed
signature. Thus a fresh packed forgery expands to a fresh old forgery, even if
some old signing-oracle outputs had out-of-range counters. The converse need
not hold because compression discards high bits of old counters.
-/

namespace SigGolfCandidate.Radix27
open SigGolfCandidate.Packed

open SigGolfCandidate.Legacy OracleComp OracleSpec

set_option maxRecDepth 200000
set_option maxHeartbeats 1000000

set_option allowUnsafeReducibility true in
attribute [local reducible] SigGolfCandidate.Legacy.Input SigGolfCandidate.Legacy.Output
  oldSubmission shortSubmission

def liftActionAny {state : Type} : Action sizes state → Action oldSizes state
  | .submit candidate => .submit (liftForgery candidate)
  | .hash input resume => .hash input resume
  | .sign request resume =>
      .sign ⟨request.message, request.cache⟩ (fun answer => resume (answer.map packOldAny13))
  | .sample n resume => .sample n resume
  | .step next => .step next

def liftAdversaryAny (A : Adversary sizes) : Adversary oldSizes where
  State := A.State
  initial := A.initial
  step state := liftActionAny (A.step state)

structure TranscriptRelAny (short : Transcript sizes) (long : Transcript oldSizes) : Prop where
  signed : short.signed = long.signed.map (fun e => (e.1, packOldAny13 e.2))
  signingRequests : short.signingRequests = long.signingRequests
  hashCalls : short.hashCalls = long.hashCalls

/-- If an expanded packed signature occurred in the old transcript, the
original packed signature occurred in the short transcript. -/
theorem signed_old_implies_short {short : Transcript sizes} {long : Transcript oldSizes}
    (h : TranscriptRelAny short long) (message : Message) (signature : Bytes 6397) :
    (message, unpackOld13 signature) ∈ long.signed →
      (message, signature) ∈ short.signed := by
  intro hm
  rw [h.signed, ← packAny_unpackOld13 signature]
  exact List.mem_map.mpr ⟨(message, unpackOld13 signature), hm, rfl⟩

/-- Strong freshness transfers in exactly the direction needed for a security
reduction. -/
theorem freshSignature_imp {short : Transcript sizes} {long : Transcript oldSizes}
    (h : TranscriptRelAny short long) (message : Message) (signature : Bytes 6397) :
    short.freshSignature message signature = true →
      long.freshSignature message (unpackOld13 signature) = true := by
  intro hshort
  cases hlong : long.signed.contains (message, unpackOld13 signature) with
  | false =>
      have hn : (message, unpackOld13 signature) ∉ long.signed := by
        intro hm
        have hc := List.contains_iff_mem.mpr hm
        rw [hlong] at hc
        cases hc
      simpa [Transcript.freshSignature] using hn
  | true =>
      have hm : (message, unpackOld13 signature) ∈ long.signed :=
        List.contains_iff_mem.mp hlong
      have hs := signed_old_implies_short h message signature hm
      have hn : (message, signature) ∉ short.signed := by
        simpa [Transcript.freshSignature] using hshort
      exact (hn hs).elim

theorem freshMessage_any_eq {short : Transcript sizes} {long : Transcript oldSizes}
    (h : TranscriptRelAny short long) (message : Message) :
    short.freshMessage message = long.freshMessage message := by
  unfold Transcript.freshMessage
  rw [h.signed, List.any_map]
  rfl

theorem record_any_rel {short : Transcript sizes} {long : Transcript oldSizes}
    (h : TranscriptRelAny short long) (message : Message)
    (value : Option (Bytes 6404)) (calls : Nat) :
    TranscriptRelAny (recordVC short message (value.map packOldAny13) calls)
      (recordVC long message value calls) := by
  cases value with
  | none =>
      refine ⟨by simpa [recordVC] using h.signed,
        by simpa [recordVC] using h.signingRequests,
        by simpa [recordVC] using congrArg (· + calls) h.hashCalls⟩
  | some σ =>
      refine ⟨?_, ?_, ?_⟩
      · simp only [recordVC, Option.map_some, List.map_cons]
        rw [h.signed]
      · simpa [recordVC] using h.signingRequests
      · simpa [recordVC] using congrArg (· + calls) h.hashCalls

theorem hash_any_rel {short : Transcript sizes} {long : Transcript oldSizes}
    (h : TranscriptRelAny short long) :
    TranscriptRelAny { short with hashCalls := short.hashCalls + 1 }
      { long with hashCalls := long.hashCalls + 1 } := by
  exact ⟨h.signed, h.signingRequests, congrArg (· + 1) h.hashCalls⟩

structure AssumptionsAny (layout : Layout) (oldImages shortImages : Phase → Riscv.Image) : Prop where
  keygen : ∀ sk : SecretKey,
    (observed <$> (shortSubmission layout shortImages).run .keygen sk) =
      (observed <$> (oldSubmission layout oldImages).run .keygen sk)
  sign : ∀ (sk : SecretKey) (cache : Bytes CACHE_BYTES) (message : Message),
    (observed <$> (shortSubmission layout shortImages).run .sign (sk, cache, message)) =
      ((fun r => (r.value.map packOldAny13, r.hashCalls)) <$>
        (oldSubmission layout oldImages).run .sign (sk, cache, message))
  expand : ∀ (message : Message) (pk : PublicKey) (signature : Bytes 6397),
    (observed <$> (shortSubmission layout shortImages).run .expand (message, pk, signature)) =
      (observed <$> (oldSubmission layout oldImages).run .expand
        (message, pk, unpackOld13 signature))
  verify : ∀ (message : Message) (pk : PublicKey) (witness : Bytes 6404),
    (observed <$> (shortSubmission layout shortImages).run .verify (message, pk, witness)) =
      (observed <$> (oldSubmission layout oldImages).run .verify (message, pk, witness))

/-- Both games pay the same hash cost. A short win is also an old win. -/
def AttackRel (short long : AttackResult) : Prop :=
  short.hashCalls = long.hashCalls ∧ (short.won = true → long.won = true)

theorem attackRel_false (shortCalls longCalls : Nat) (h : shortCalls = longCalls) :
    AttackRel ⟨false, shortCalls⟩ ⟨false, longCalls⟩ :=
  ⟨h, by simp⟩

/-- Run one common expansion and verification, returning both games' answers. -/
def checkPair (layout : Layout) (oldImages : Phase → Riscv.Image)
    (pk : PublicKey) (short : Transcript sizes) (long : Transcript oldSizes)
    (candidate : Forgery sizes) : OracleComp HashSpec (AttackResult × AttackResult) :=
  match candidate with
  | .witness message witness =>
      (fun p : Option Unit × Nat =>
        (⟨p.1.isSome && short.freshMessage message, short.hashCalls + p.2⟩,
         ⟨p.1.isSome && long.freshMessage message, long.hashCalls + p.2⟩)) <$>
        (observed <$> (oldSubmission layout oldImages).run .verify (message, pk, witness))
  | .signature message signature => do
      let p ← observed <$> (oldSubmission layout oldImages).run .expand
        (message, pk, unpackOld13 signature)
      match p.1 with
      | none =>
          pure (⟨false, short.hashCalls + p.2⟩, ⟨false, long.hashCalls + p.2⟩)
      | some witness =>
          (fun q : Option Unit × Nat =>
            (⟨q.1.isSome && short.freshSignature message signature,
                short.hashCalls + p.2 + q.2⟩,
             ⟨q.1.isSome && long.freshSignature message (unpackOld13 signature),
                long.hashCalls + p.2 + q.2⟩)) <$>
            (observed <$> (oldSubmission layout oldImages).run .verify
              (message, pk, witness))

theorem checkPair_rel {layout : Layout} {oldImages : Phase → Riscv.Image}
    (pk : PublicKey) {short : Transcript sizes} {long : Transcript oldSizes}
    (h : TranscriptRelAny short long) (candidate : Forgery sizes)
    (answer : AttackResult × AttackResult)
    (ha : answer ∈ support (checkPair layout oldImages pk short long candidate)) :
    AttackRel answer.1 answer.2 := by
  cases candidate with
  | witness message witness =>
      simp only [checkPair, support_map] at ha
      obtain ⟨p, _, rfl⟩ := ha
      exact ⟨by rw [h.hashCalls], by
        simp only [Bool.and_eq_true]
        rintro ⟨hv, hs⟩
        exact ⟨hv, by rw [← freshMessage_any_eq h]; exact hs⟩⟩
  | signature message signature =>
      simp only [checkPair] at ha
      obtain ⟨p, _, hrest⟩ := (mem_support_bind_iff _ _ _).mp ha
      cases hp : p.1 with
      | none =>
          simp only [hp] at hrest
          simp only [support_pure, Set.mem_singleton_iff] at hrest
          subst answer
          exact attackRel_false _ _ (by rw [h.hashCalls])
      | some witness =>
          simp only [hp] at hrest
          rw [support_map] at hrest
          obtain ⟨q, _, rfl⟩ := hrest
          refine ⟨by rw [h.hashCalls], ?_⟩
          simp only [Bool.and_eq_true]
          rintro ⟨hv, hs⟩
          exact ⟨hv, freshSignature_imp h message signature hs⟩

theorem checkPair_fst {layout : Layout} {oldImages shortImages : Phase → Riscv.Image}
    (H : AssumptionsAny layout oldImages shortImages) (pk : PublicKey)
    {short : Transcript sizes} {long : Transcript oldSizes}
    (candidate : Forgery sizes) :
    (Prod.fst <$> checkPair layout oldImages pk short long candidate) =
      (shortSubmission layout shortImages).checkForgery pk short candidate := by
  cases candidate with
  | witness message witness =>
      rw [check_witness_observed, H.verify message pk witness]
      simp only [checkPair, Functor.map_map]
  | signature message signature =>
      rw [check_signature_observed, H.expand message pk signature]
      simp only [checkPair, map_bind]
      apply bind_congr
      intro p
      cases hp : p.1 with
      | none => simp only [hp]; rfl
      | some witness =>
          simp only [hp]
          rw [H.verify message pk witness]
          simp only [Functor.map_map]

theorem checkPair_snd {layout : Layout} {oldImages : Phase → Riscv.Image}
    (pk : PublicKey) {short : Transcript sizes} {long : Transcript oldSizes}
    (candidate : Forgery sizes) :
    (Prod.snd <$> checkPair layout oldImages pk short long candidate) =
      (oldSubmission layout oldImages).checkForgery pk long (liftForgery candidate) := by
  cases candidate with
  | witness message witness =>
      simp only [liftForgery]
      rw [check_witness_observed]
      simp only [checkPair, Functor.map_map]
  | signature message signature =>
      simp only [liftForgery]
      rw [check_signature_observed]
      simp only [checkPair, map_bind]
      apply bind_congr
      intro p
      cases hp : p.1 with
      | none => simp only [hp]; rfl
      | some witness =>
          simp only [hp]
          simp only [Functor.map_map]

/-- A common execution of the two interactive games. Hashes, private coins,
key generation, signing, expansion, and verification are sampled once. -/
def interactPair (layout : Layout) (oldImages : Phase → Riscv.Image)
    (A : Adversary sizes) (sk : SecretKey) (pk : PublicKey) :
    Nat → A.State → Transcript sizes → Transcript oldSizes →
      OracleComp World (AttackResult × AttackResult)
  | 0, _, short, long =>
      pure (⟨false, short.hashCalls⟩, ⟨false, long.hashCalls⟩)
  | rounds + 1, state, short, long =>
      match A.step state with
      | .submit candidate =>
          liftM (checkPair layout oldImages pk short long candidate)
      | .hash input resume => do
          let answer ← liftM (HashSpec.query input)
          interactPair layout oldImages A sk pk rounds (resume answer)
            { short with hashCalls := short.hashCalls + 1 }
            { long with hashCalls := long.hashCalls + 1 }
      | .sample n resume => do
          let answer ← liftM (unifSpec.query n)
          interactPair layout oldImages A sk pk rounds (resume answer) short long
      | .step next =>
          interactPair layout oldImages A sk pk rounds next short long
      | .sign request resume => do
          if short.signingRequests < LIFETIME then
            let result ← liftM ((oldSubmission layout oldImages).run .sign
              (sk, request.cache, request.message))
            interactPair layout oldImages A sk pk rounds (resume (result.value.map packOldAny13))
              (recordVC short request.message (result.value.map packOldAny13) result.hashCalls)
              (recordVC long request.message result.value result.hashCalls)
          else
            pure (⟨false, short.hashCalls⟩, ⟨false, long.hashCalls⟩)

theorem interactPair_rel {layout : Layout} {oldImages : Phase → Riscv.Image}
    (A : Adversary sizes) (sk : SecretKey) (pk : PublicKey) :
    ∀ rounds (state : A.State) (short : Transcript sizes) (long : Transcript oldSizes),
      TranscriptRelAny short long →
      ∀ answer ∈ support (interactPair layout oldImages A sk pk rounds state short long),
        AttackRel answer.1 answer.2 := by
  intro rounds
  induction rounds with
  | zero =>
      intro state short long h answer ha
      simp only [interactPair, support_pure, Set.mem_singleton_iff] at ha
      subst answer
      exact attackRel_false _ _ h.hashCalls
  | succ rounds ih =>
      intro state short long h answer ha
      cases hstep : A.step state with
      | submit candidate =>
          simp only [interactPair, hstep] at ha
          change answer ∈ support ((checkPair layout oldImages pk short long candidate).liftComp World) at ha
          exact checkPair_rel pk h candidate answer
            ((OracleComp.mem_support_liftComp_iff _ _).mp ha)
      | hash input resume =>
          simp only [interactPair, hstep] at ha
          obtain ⟨sample, _, hrest⟩ := (mem_support_bind_iff _ _ _).mp ha
          exact ih (resume sample) _ _ (hash_any_rel h) answer hrest
      | sample n resume =>
          simp only [interactPair, hstep] at ha
          obtain ⟨sample, _, hrest⟩ := (mem_support_bind_iff _ _ _).mp ha
          exact ih (resume sample) _ _ h answer hrest
      | step next =>
          simp only [interactPair, hstep] at ha
          exact ih next _ _ h answer ha
      | sign request resume =>
          by_cases hk : short.signingRequests < LIFETIME
          · simp only [interactPair, hstep, hk, if_true] at ha
            obtain ⟨result, _, hrest⟩ := (mem_support_bind_iff _ _ _).mp ha
            exact ih (resume (result.value.map packOldAny13)) _ _
              (record_any_rel h request.message result.value result.hashCalls) answer hrest
          · simp only [interactPair, hstep, hk, if_false, support_pure,
              Set.mem_singleton_iff] at ha
            subst answer
            exact attackRel_false _ _ h.hashCalls

theorem interactPair_fst {layout : Layout} {oldImages shortImages : Phase → Riscv.Image}
    (H : AssumptionsAny layout oldImages shortImages) (A : Adversary sizes)
    (sk : SecretKey) (pk : PublicKey) :
    ∀ rounds (state : A.State) (short : Transcript sizes) (long : Transcript oldSizes),
      TranscriptRelAny short long →
      (Prod.fst <$> interactPair layout oldImages A sk pk rounds state short long) =
        (shortSubmission layout shortImages).interact A sk pk rounds state short := by
  intro rounds
  induction rounds with
  | zero =>
      intro state short long h
      simp only [interactPair, Submission.interact, map_pure]
  | succ rounds ih =>
      intro state short long h
      cases hstep : A.step state with
      | submit candidate =>
          simp only [interactPair, hstep, Submission.interact]
          rw [← liftM_map, checkPair_fst H pk candidate]
      | hash input resume =>
          simp only [interactPair, hstep, Submission.interact, map_bind]
          apply bind_congr
          intro answer
          exact ih (resume answer) _ _ (hash_any_rel h)
      | sample n resume =>
          simp only [interactPair, hstep, Submission.interact, map_bind]
          apply bind_congr
          intro answer
          exact ih (resume answer) _ _ h
      | step next =>
          simp only [interactPair, hstep, Submission.interact]
          exact ih next _ _ h
      | sign request resume =>
          by_cases hk : short.signingRequests < LIFETIME
          · simp only [interactPair, hstep, hk, if_true, map_bind]
            let newX : OracleComp HashSpec (RunResult (Bytes 6397)) :=
              (shortSubmission layout shortImages).run .sign
                (sk, request.cache, request.message)
            let oldX : OracleComp HashSpec (RunResult (Bytes 6404)) :=
              (oldSubmission layout oldImages).run .sign
                (sk, request.cache, request.message)
            have hshort :
                (shortSubmission layout shortImages).interact A sk pk (rounds + 1)
                  state short =
                  (liftM newX : OracleComp World _) >>= fun r =>
                    (shortSubmission layout shortImages).interact A sk pk rounds
                      (resume r.value)
                      (recordVC short request.message r.value r.hashCalls) := by
              simp only [Submission.interact, hstep, Submission.signingOracle,
                hk, if_true, record_eq_recordVC]
              rfl
            rw [hshort]
            change ((liftM oldX : OracleComp World _) >>= fun r =>
                Prod.fst <$> interactPair layout oldImages A sk pk rounds
                  (resume (r.value.map packOldAny13))
                  (recordVC short request.message (r.value.map packOldAny13) r.hashCalls)
                  (recordVC long request.message r.value r.hashCalls)) = _
            calc
              _ = (liftM oldX : OracleComp World _) >>= fun r =>
                    (shortSubmission layout shortImages).interact A sk pk rounds
                      (resume (r.value.map packOldAny13))
                      (recordVC short request.message (r.value.map packOldAny13)
                        r.hashCalls) := by
                apply bind_congr
                intro r
                exact ih (resume (r.value.map packOldAny13)) _ _
                  (record_any_rel h request.message r.value r.hashCalls)
              _ = (liftM ((fun r : RunResult (Bytes 6404) =>
                    (r.value.map packOldAny13, r.hashCalls)) <$> oldX) :
                    OracleComp World _) >>= fun p =>
                    (shortSubmission layout shortImages).interact A sk pk rounds
                      (resume p.1) (recordVC short request.message p.1 p.2) :=
                (liftM_bind_map oldX
                  (fun r : RunResult (Bytes 6404) =>
                    (r.value.map packOldAny13, r.hashCalls))
                  (fun p : Option (Bytes 6397) × Nat =>
                    (shortSubmission layout shortImages).interact A sk pk rounds
                      (resume p.1) (recordVC short request.message p.1 p.2))).symm
              _ = (liftM (observed <$> newX) : OracleComp World _) >>= fun p =>
                    (shortSubmission layout shortImages).interact A sk pk rounds
                      (resume p.1) (recordVC short request.message p.1 p.2) := by
                rw [H.sign sk request.cache request.message]
              _ = _ := (liftM_bind_observed newX _).symm
          · simp only [interactPair, hstep, hk, if_false]
            have hkL : ¬ short.signingRequests < LIFETIME := hk
            simp only [Submission.interact, hstep, hkL, if_false, h.hashCalls,
              map_pure]

theorem interactPair_snd {layout : Layout} {oldImages : Phase → Riscv.Image}
    (A : Adversary sizes) (sk : SecretKey) (pk : PublicKey) :
    ∀ rounds (state : A.State) (short : Transcript sizes) (long : Transcript oldSizes),
      TranscriptRelAny short long →
      (Prod.snd <$> interactPair layout oldImages A sk pk rounds state short long) =
        (oldSubmission layout oldImages).interact (liftAdversaryAny A) sk pk
          rounds state long := by
  intro rounds
  induction rounds with
  | zero =>
      intro state short long h
      simp only [interactPair, Submission.interact, map_pure, h.hashCalls]
  | succ rounds ih =>
      intro state short long h
      cases hstep : A.step state with
      | submit candidate =>
          simp only [interactPair, hstep, Submission.interact, liftAdversaryAny,
            liftActionAny]
          rw [← liftM_map, checkPair_snd pk candidate]
      | hash input resume =>
          simp only [interactPair, hstep, Submission.interact, liftAdversaryAny,
            liftActionAny, map_bind]
          apply bind_congr
          intro answer
          exact ih (resume answer) _ _ (hash_any_rel h)
      | sample n resume =>
          simp only [interactPair, hstep, Submission.interact, liftAdversaryAny,
            liftActionAny, map_bind]
          apply bind_congr
          intro answer
          exact ih (resume answer) _ _ h
      | step next =>
          simp only [interactPair, hstep, Submission.interact, liftAdversaryAny,
            liftActionAny]
          exact ih next _ _ h
      | sign request resume =>
          by_cases hk : short.signingRequests < LIFETIME
          · have hkL : long.signingRequests < LIFETIME := by
              simpa [h.signingRequests] using hk
            simp only [interactPair, hstep, hk, if_true, map_bind,
              Submission.interact, liftAdversaryAny, liftActionAny,
              hkL, Submission.signingOracle, record_eq_recordVC]
            apply bind_congr
            intro r
            exact ih (resume (r.value.map packOldAny13)) _ _
              (record_any_rel h request.message r.value r.hashCalls)
          · have hkL : ¬ long.signingRequests < LIFETIME := by
              simpa [h.signingRequests] using hk
            simp only [interactPair, hstep, hk, hkL, if_false, map_pure,
              Submission.interact, liftAdversaryAny, liftActionAny, h.hashCalls]

end SigGolfCandidate.Radix27

/-!
# Strong-security transfer for packed signatures

The paired game shares all oracle answers and signing results. Projection
recovers the short and old games, and every short win implies an old win.
-/

namespace SigGolfCandidate.Radix27
open SigGolfCandidate.Packed

open SigGolfCandidate.Legacy OracleComp OracleSpec

set_option maxRecDepth 200000
set_option maxHeartbeats 1000000

set_option allowUnsafeReducibility true in
attribute [local reducible] SigGolfCandidate.Legacy.Input SigGolfCandidate.Legacy.Output
  oldSubmission shortSubmission

def pairKeygenTail (layout : Layout) (oldImages : Phase → Riscv.Image)
    (A : Adversary sizes) (rounds : Nat) (sk : SecretKey)
    (p : Option (PublicKey × Bytes CACHE_BYTES) × Nat) :
    OracleComp World (AttackResult × AttackResult) :=
  match p.1 with
  | none => pure (⟨false, p.2⟩, ⟨false, p.2⟩)
  | some (pk, cache) =>
      interactPair layout oldImages A sk pk rounds (A.initial pk cache)
        { hashCalls := p.2 } { hashCalls := p.2 }

theorem pairKeygenTail_fst {layout : Layout} {oldImages shortImages : Phase → Riscv.Image}
    (H : AssumptionsAny layout oldImages shortImages) (A : Adversary sizes)
    (rounds : Nat) (sk : SecretKey)
    (p : Option (PublicKey × Bytes CACHE_BYTES) × Nat) :
    (Prod.fst <$> pairKeygenTail layout oldImages A rounds sk p) =
      keygenTail (shortSubmission layout shortImages) A rounds sk p := by
  rcases p with ⟨value, calls⟩
  cases value with
  | none => rfl
  | some pair =>
      rcases pair with ⟨pk, cache⟩
      simpa only [pairKeygenTail, keygenTail] using
        (interactPair_fst H A sk pk rounds (A.initial pk cache)
          { hashCalls := calls } { hashCalls := calls } ⟨rfl, rfl, rfl⟩)

theorem pairKeygenTail_snd {layout : Layout} {oldImages : Phase → Riscv.Image}
    (A : Adversary sizes) (rounds : Nat) (sk : SecretKey)
    (p : Option (PublicKey × Bytes CACHE_BYTES) × Nat) :
    (Prod.snd <$> pairKeygenTail layout oldImages A rounds sk p) =
      keygenTail (oldSubmission layout oldImages) (liftAdversaryAny A) rounds sk p := by
  rcases p with ⟨value, calls⟩
  cases value with
  | none => rfl
  | some pair =>
      rcases pair with ⟨pk, cache⟩
      simpa only [pairKeygenTail, keygenTail, liftAdversaryAny] using
        (interactPair_snd A sk pk rounds (A.initial pk cache)
          { hashCalls := calls } { hashCalls := calls } ⟨rfl, rfl, rfl⟩)

theorem pairKeygenTail_rel {layout : Layout} {oldImages : Phase → Riscv.Image}
    (A : Adversary sizes) (rounds : Nat) (sk : SecretKey)
    (p : Option (PublicKey × Bytes CACHE_BYTES) × Nat)
    (answer : AttackResult × AttackResult)
    (ha : answer ∈ support (pairKeygenTail layout oldImages A rounds sk p)) :
    AttackRel answer.1 answer.2 := by
  rcases p with ⟨value, calls⟩
  cases value with
  | none =>
      simp only [pairKeygenTail, support_pure, Set.mem_singleton_iff] at ha
      subst answer
      exact attackRel_false calls calls rfl
  | some pair =>
      rcases pair with ⟨pk, cache⟩
      exact interactPair_rel A sk pk rounds (A.initial pk cache)
        { hashCalls := calls } { hashCalls := calls } ⟨rfl, rfl, rfl⟩ answer ha

noncomputable def pairProgram (layout : Layout) (oldImages : Phase → Riscv.Image)
    (A : Adversary sizes) (rounds : Nat) :
    OracleComp World (AttackResult × AttackResult) := do
  let sk ← liftM sampleSecretKey
  let p ← liftM (observed <$> (oldSubmission layout oldImages).run .keygen sk)
  pairKeygenTail layout oldImages A rounds sk p

noncomputable def securityPair (layout : Layout) (oldImages : Phase → Riscv.Image)
    (A : Adversary sizes) (rounds : Nat) : ProbComp (AttackResult × AttackResult) :=
  withRandomness (pairProgram layout oldImages A rounds)

theorem withRandomness_map {α β : Type} (f : α → β) (program : OracleComp World α) :
    withRandomness (f <$> program) = f <$> withRandomness program := by
  simp only [withRandomness, simulateQ_map, StateT.run'_eq, StateT.run_map,
    Functor.map_map]

theorem pairProgram_fst {layout : Layout} {oldImages shortImages : Phase → Riscv.Image}
    (H : AssumptionsAny layout oldImages shortImages) (A : Adversary sizes)
    (rounds : Nat) :
    (Prod.fst <$> pairProgram layout oldImages A rounds) =
      (do
        let sk ← liftM sampleSecretKey
        let p ← liftM (observed <$> (shortSubmission layout shortImages).run .keygen sk)
        keygenTail (shortSubmission layout shortImages) A rounds sk p) := by
  simp only [pairProgram, map_bind]
  apply bind_congr
  intro sk
  rw [H.keygen sk]
  apply bind_congr
  intro p
  exact pairKeygenTail_fst H A rounds sk p

theorem pairProgram_snd {layout : Layout} {oldImages : Phase → Riscv.Image}
    (A : Adversary sizes) (rounds : Nat) :
    (Prod.snd <$> pairProgram layout oldImages A rounds) =
      (do
        let sk ← liftM sampleSecretKey
        let p ← liftM (observed <$> (oldSubmission layout oldImages).run .keygen sk)
        keygenTail (oldSubmission layout oldImages) (liftAdversaryAny A) rounds sk p) := by
  simp only [pairProgram, map_bind]
  apply bind_congr
  intro sk
  apply bind_congr
  intro p
  exact pairKeygenTail_snd A rounds sk p

theorem securityPair_fst {layout : Layout} {oldImages shortImages : Phase → Riscv.Image}
    (H : AssumptionsAny layout oldImages shortImages) (A : Adversary sizes)
    (rounds : Nat) :
    (Prod.fst <$> securityPair layout oldImages A rounds) =
      (shortSubmission layout shortImages).securityExperiment A rounds := by
  rw [securityExperiment_observed]
  change (Prod.fst <$> withRandomness (pairProgram layout oldImages A rounds)) = _
  rw [← withRandomness_map, pairProgram_fst H A rounds]

theorem securityPair_snd {layout : Layout} {oldImages : Phase → Riscv.Image}
    (A : Adversary sizes) (rounds : Nat) :
    (Prod.snd <$> securityPair layout oldImages A rounds) =
      (oldSubmission layout oldImages).securityExperiment (liftAdversaryAny A) rounds := by
  rw [securityExperiment_observed]
  change (Prod.snd <$> withRandomness (pairProgram layout oldImages A rounds)) = _
  rw [← withRandomness_map, pairProgram_snd A rounds]

theorem pairProgram_rel {layout : Layout} {oldImages : Phase → Riscv.Image}
    (A : Adversary sizes) (rounds : Nat)
    (answer : AttackResult × AttackResult)
    (ha : answer ∈ support (pairProgram layout oldImages A rounds)) :
    AttackRel answer.1 answer.2 := by
  unfold pairProgram at ha
  obtain ⟨sk, _, hrest⟩ := (mem_support_bind_iff _ _ _).mp ha
  obtain ⟨p, _, htail⟩ := (mem_support_bind_iff _ _ _).mp hrest
  exact pairKeygenTail_rel A rounds sk p answer htail

theorem securityPair_rel {layout : Layout} {oldImages : Phase → Riscv.Image}
    (A : Adversary sizes) (rounds : Nat)
    (answer : AttackResult × AttackResult)
    (ha : answer ∈ support (securityPair layout oldImages A rounds)) :
    AttackRel answer.1 answer.2 := by
  exact pairProgram_rel A rounds answer
    (support_simulateQ_run'_subset _ _ ∅ ha)

theorem secureAny {layout : Layout} {oldImages shortImages : Phase → Riscv.Image}
    (H : AssumptionsAny layout oldImages shortImages)
    (hOld : (oldSubmission layout oldImages).Secure) :
    (shortSubmission layout shortImages).Secure := by
  intro A rounds Q hQ
  let pair := securityPair layout oldImages A rounds
  have hmono :
      Pr[fun r : AttackResult × AttackResult =>
        r.1.won = true ∧ r.1.hashCalls ≤ Q | pair] ≤
      Pr[fun r : AttackResult × AttackResult =>
        r.2.won = true ∧ r.2.hashCalls ≤ Q | pair] := by
    apply probEvent_mono
    intro r hr hw
    have hrel := securityPair_rel A rounds r hr
    exact ⟨hrel.2 hw.1, hrel.1 ▸ hw.2⟩
  calc
    Pr[fun r => r.won = true ∧ r.hashCalls ≤ Q |
      (shortSubmission layout shortImages).securityExperiment A rounds] =
      Pr[fun r : AttackResult × AttackResult =>
        r.1.won = true ∧ r.1.hashCalls ≤ Q | pair] := by
        rw [← securityPair_fst H A rounds, probEvent_map]
        rfl
    _ ≤ Pr[fun r : AttackResult × AttackResult =>
        r.2.won = true ∧ r.2.hashCalls ≤ Q | pair] := hmono
    _ = Pr[fun r => r.won = true ∧ r.hashCalls ≤ Q |
      (oldSubmission layout oldImages).securityExperiment
        (liftAdversaryAny A) rounds] := by
        rw [← securityPair_snd A rounds, probEvent_map]
        rfl
    _ ≤ (Q : ENNReal) / 2 ^ SECURITY_BITS :=
      hOld (liftAdversaryAny A) rounds Q hQ

end SigGolfCandidate.Radix27

#print axioms SigGolfCandidate.Radix27.secureAny


end


section -- Radix27ByteCodec

namespace Radix27ByteCodec
open Radix27 SigGolfCandidate.Legacy SigGolfCandidate.Packed SigGolfCandidate.Ref
set_option maxRecDepth 100000

theorem toList_split13 (b : Bytes 6397) :
    toList b = toList (body13 b) ++ toList (n := 13) (trailer13 b) := by
  have h := toList_concat (n := 6384) (m := 13) (body13 b) (trailer13 b)
  have hs : trailer13 b ++ body13 b = b := join13_parts b
  simpa only [hs, BitVec.cast_eq] using h

theorem toList_body13 (b : Bytes 6397) :
    toList (body13 b) = (toList b).take 6384 := by
  rw [toList_split13]
  simp [length_toList]

theorem toList_trailer13 (b : Bytes 6397) :
    toList (n := 13) (trailer13 b) = (toList b).drop 6384 := by
  rw [toList_split13]
  simp [length_toList]

theorem body13_byte (b : Bytes 6397) (i : Nat) (hi : i < 6384) :
    (toList (body13 b)).getD i 0 = (toList b).getD i 0 := by
  rw [toList_body13]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, if_pos hi]

theorem trailer13_byte (b : Bytes 6397) (i : Nat) (_hi : i < 13) :
    (toList (n := 13) (trailer13 b)).getD i 0 =
      (toList b).getD (6384 + i) 0 := by
  rw [toList_trailer13]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem readBuffer_trailer13 (s : RiscvZkvm.Rv64.MachineState) :
    readBuffer s 0x3F40 13 = trailer13 (readBuffer s 0x2650 6397) := by
  apply readBuffer_eq_of_bytes
  intro i hi
  rw [trailer13_byte _ i hi,
    readBuffer_byte s 0x2650 6397 (6384 + i) (by omega)]
  have heq : 0x3F40 + i = 0x2650 + (6384 + i) := by omega
  rw [heq]

theorem toList_expandWitness13 (b : Bytes 6397) :
    toList (expandWitness13 b) =
      toList (body13 b) ++ toList (n := 20) (expand13 (trailer13 b)) := by
  have h := toList_concat (n := 6384) (m := 20)
    (body13 b) (expand13 (trailer13 b))
  change toList (expandWitness13 b) = _
  exact h

theorem expandWitness13_body_byte (b : Bytes 6397) (i : Nat)
    (hi : i < 6384) :
    (toList (expandWitness13 b)).getD i 0 =
      (toList (body13 b)).getD i 0 := by
  rw [toList_expandWitness13]
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by rw [length_toList]; exact hi)]

theorem expandWitness13_counter_byte (b : Bytes 6397) (i : Nat)
    (_hi : i < 20) :
    (toList (expandWitness13 b)).getD (6384 + i) 0 =
      (toList (n := 20) (expand13 (trailer13 b))).getD i 0 := by
  rw [toList_expandWitness13]
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by rw [length_toList]; omega)]
  simp only [length_toList, Nat.add_sub_cancel_left]

#print axioms readBuffer_trailer13
end Radix27ByteCodec


end
