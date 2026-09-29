import SigGolfCandidate.Bridge.Basic
import SigGolfCandidate.SphincsSecurity.Scheme
import SigGolfCandidate.Packed.HonestRoundTrip
import SigGolfCandidate.Equiv.Verify

namespace SigGolfCandidate.Packed

open OracleComp OracleSpec
open SigGolfCandidate.Bridge (relabel relabel_pure relabel_query_bind)

theorem support_relabel {ι ι' R α : Type} (f : ι → ι')
    (oa : OracleComp (ι →ₒ R) α) : support (relabel f oa) = support oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => rfl
  | query_bind t k ih =>
      rw [relabel_query_bind, support_bind, support_bind]
      simp only [support_query]
      ext x
      simp only [Set.mem_iUnion, Set.mem_univ]
      exact ⟨fun ⟨r, hr⟩ => ⟨r, by simpa only [ih r] using hr⟩,
        fun ⟨r, hr⟩ => ⟨r, by simpa only [ih r] using hr⟩⟩

open SphincsSecurity SphincsSecurity.Concrete

set_option maxHeartbeats 1000000
set_option allowUnsafeReducibility true in
attribute [local reducible] SphincsSecurity.hashOutputBits SphincsSecurity.digestBits
  SphincsSecurity.messageBits SphincsSecurity.publicParameterBits SphincsSecurity.counterBits

theorem encodingSearch_support_range (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (message : Digest) :
    ∀ fuel start, start + fuel ≤ 2 ^ 32 →
      ∀ out : Option (Counter × Encoding),
        out ∈ support (encodingSearch (m := OracleComp HashSpec)
          parameter lay tree leaf message fuel start) →
        ∀ counter digits, out = some (counter, digits) →
          start ≤ counter.toNat ∧ counter.toNat < start + fuel := by
  intro fuel
  induction fuel with
  | zero =>
      intro start _ out h counter digits heq
      simp only [encodingSearch, support_pure, Set.mem_singleton_iff] at h
      subst out
      cases h
  | succ fuel ih =>
      intro start hwrap out h counter digits heq
      rw [encodingSearch] at h
      obtain ⟨found, _, hrest⟩ := (mem_support_bind_iff _ _ _).mp h
      cases found with
      | none =>
          obtain ⟨hlo, hhi⟩ := ih (start + 1) (by omega) out hrest counter digits heq
          exact ⟨by omega, by omega⟩
      | some digits' =>
          simp only [support_pure, Set.mem_singleton_iff] at hrest
          subst out
          have hpair : (counter, digits) = (BitVec.ofNat counterBits start, digits') :=
            Option.some.inj hrest
          have hcounter : counter = BitVec.ofNat counterBits start :=
            congrArg Prod.fst hpair
          rw [hcounter]
          simp only [BitVec.toNat_ofNat, counterBits,
            Nat.mod_eq_of_lt (by omega : start < 2 ^ 32)]
          omega

theorem signTopLayerPaired_support_range (parameter : PublicParameter)
    (index : Index) (secret : LeafIndex → ChainPair → OracleComp HashSpec (Digest × Digest))
    (topNode : Nat → Nat → OracleComp HashSpec Digest) (message : Digest)
    (out : Option LayerOutput)
    (h : out ∈ support (signTopLayerPaired parameter index secret topNode message)) :
    ∀ part, out = some part → part.1.toNat < encodingAttemptLimit := by
  rw [signTopLayerPaired] at h
  obtain ⟨search, hsearch, hrest⟩ := (mem_support_bind_iff _ _ _).mp h
  cases search with
  | none =>
      intro part heq
      have hr : out = none := by simpa using hrest
      rw [hr] at heq
      cases heq
  | some result =>
      obtain ⟨counter, encoding⟩ := result
      have hcounter : counter.toNat < encodingAttemptLimit :=
        (encodingSearch_support_range parameter SphincsSecurity.topLayer
          (treeIndexAt index SphincsSecurity.topLayer)
          (leafIndexAt index SphincsSecurity.topLayer) message
          encodingAttemptLimit 0 (by norm_num [encodingAttemptLimit])
          (some (counter, encoding)) hsearch counter encoding rfl).2
      obtain ⟨pairs, _, hrest⟩ := (mem_support_bind_iff _ _ _).mp hrest
      obtain ⟨path, _, hrest⟩ := (mem_support_bind_iff _ _ _).mp hrest
      intro part heq
      have hr : out = some (counter, unpairChains pairs,
          fun level => if h : level < maxLayerHeight then path ⟨level, h⟩ else 0) := by
        simpa using hrest
      rw [hr] at heq
      have hp := Option.some.inj heq
      have hc := congrArg Prod.fst hp
      rw [← hc]
      exact hcounter

def PartsInRange (n : Nat) (out : Option (Layer → LayerOutput)) : Prop :=
  ∀ parts, out = some parts → ∀ lay : Layer, lay.val < n →
    (parts lay).1.toNat < encodingAttemptLimit

theorem signLayersPaired_support_range (parameter : PublicParameter) (index : Index)
    (secret : Layer → TreeIndex → LeafIndex → ChainPair →
      OracleComp HashSpec (Digest × Digest))
    (topNode : Nat → Nat → OracleComp HashSpec Digest) :
    ∀ n message (hn : n ≤ numLayers) out,
      out ∈ support (signLayersPaired parameter index secret topNode n message) →
      PartsInRange n out := by
  intro n
  induction n with
  | zero =>
      intro message hn out h parts heq lay hlay
      omega
  | succ remaining ih =>
      intro message hn out h
      rw [signLayersPaired] at h
      have hlayer : remaining < numLayers := by omega
      simp only [dif_pos hlayer] at h
      by_cases htop : remaining = 0
      · simp only [htop, if_pos rfl] at h
        obtain ⟨selected, hs, hrest⟩ := (mem_support_bind_iff _ _ _).mp h
        cases selected with
        | none =>
            intro parts heq lay hlay
            have hr : out = none := by simpa using hrest
            rw [hr] at heq
            cases heq
        | some part =>
            have hc := signTopLayerPaired_support_range parameter index
              (secret topLayer (treeIndexAt index topLayer)) topNode message
              (some part) hs part rfl
            intro parts heq lay hlay
            have hr : out = some (fun other =>
                if other = topLayer then part else (0, fun _ => 0, fun _ => 0)) := by
              simpa using hrest
            rw [hr] at heq
            have hp := Option.some.inj heq
            rw [← hp]
            have hlay : lay = topLayer := Fin.ext (by change lay.val = 0; omega)
            subst lay
            simp only [if_pos rfl]
            exact hc
      · simp only [if_neg htop] at h
        obtain ⟨selected, hs, hrest⟩ := (mem_support_bind_iff _ _ _).mp h
        cases selected with
        | none =>
            intro parts heq lay hlay
            have hr : out = none := by simpa using hrest
            rw [hr] at heq
            cases heq
        | some result =>
            obtain ⟨counter, encoding⟩ := result
            have hcounter : counter.toNat < encodingAttemptLimit :=
              (encodingSearch_support_range parameter ⟨remaining, hlayer⟩
                (treeIndexAt index ⟨remaining, hlayer⟩)
                (leafIndexAt index ⟨remaining, hlayer⟩) message
                encodingAttemptLimit 0 (by norm_num [encodingAttemptLimit])
                (some (counter, encoding)) hs counter encoding rfl).2
            obtain ⟨built, _, hrest⟩ := (mem_support_bind_iff _ _ _).mp hrest
            obtain ⟨values, path, root⟩ := built
            obtain ⟨prior, hprior, hrest⟩ := (mem_support_bind_iff _ _ _).mp hrest
            cases prior with
            | none =>
                intro parts heq lay hlay
                have hr : out = none := by simpa using hrest
                rw [hr] at heq
                cases heq
            | some rest =>
                have hrec := ih root (by omega) (some rest) hprior rest rfl
                intro parts heq other hother
                have hr : out = some (fun lay => if lay = ⟨remaining, hlayer⟩
                    then (counter, values, path) else rest lay) := by
                  simpa using hrest
                rw [hr] at heq
                have hp := Option.some.inj heq
                rw [← hp]
                by_cases he : other = ⟨remaining, hlayer⟩
                · subst other
                  simp only [if_pos rfl]
                  exact hcounter
                · simp only [if_neg he]
                  have hv : other.val ≠ remaining := by
                    intro hv
                    exact he (Fin.ext hv)
                  exact hrec other (by omega)

theorem signFromPaired_support_range (parameter : PublicParameter) (index : Index)
    (ftsSecret : FtsTree → FtsPair → OracleComp HashSpec (Digest × Digest))
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainPair →
      OracleComp HashSpec (Digest × Digest))
    (topNode : Nat → Nat → OracleComp HashSpec Digest)
    (randomness : Randomness) (leaves : IndexGroup → FtsLeaf)
    (out : Option Signature)
    (h : out ∈ support (signFromPaired parameter index ftsSecret otsSecret
      topNode randomness leaves)) :
    ∀ σ, out = some σ → CountersInRange σ := by
  rw [signFromPaired] at h
  obtain ⟨built, _, hrest⟩ := (mem_support_bind_iff _ _ _).mp h
  obtain ⟨secrets, ftsPath, ftsPublicKey⟩ := built
  obtain ⟨parts, hparts, hrest⟩ := (mem_support_bind_iff _ _ _).mp hrest
  cases parts with
  | none =>
      intro σ heq
      have hr : out = none := by simpa using hrest
      rw [hr] at heq
      cases heq
  | some chosen =>
      have hchosen := signLayersPaired_support_range parameter index otsSecret topNode
        numLayers ftsPublicKey (by omega) (some chosen) hparts chosen rfl
      intro σ heq
      have hr : out = some ⟨randomness, secrets, ftsPath,
          fun lay => LayerOutput.toSignature lay (chosen lay)⟩ := by
        simpa using hrest
      rw [hr] at heq
      have hp := Option.some.inj heq
      rw [← hp]
      intro lay
      exact hchosen lay lay.isLt

theorem seeded_signChecked_support_range (sk : SphincsSecurity.Seeded.SecretKey)
    (cache : TopCache) (message : Message) (out : Option Signature)
    (h : out ∈ support (SphincsSecurity.Seeded.signChecked
      (m := OracleComp HashSpec) sk cache message)) :
    ∀ σ, out = some σ → CountersInRange σ := by
  rw [SphincsSecurity.Seeded.signChecked] at h
  obtain ⟨digest, _, hrest⟩ := (mem_support_bind_iff _ _ _).mp h
  cases digest with
  | none =>
      intro σ heq
      have hr : out = none := by simpa using hrest
      rw [hr] at heq
      cases heq
  | some r =>
      obtain ⟨randomness, index, leaves⟩ := r
      exact signFromPaired_support_range sk.parameter index
        (SphincsSecurity.Seeded.ftsSecret sk.parameter sk.seed index)
        (SphincsSecurity.Seeded.otsSecret sk.parameter sk.seed)
        (SphincsSecurity.Seeded.cachedTopNode sk.parameter sk.seed cache)
        randomness leaves out hrest

theorem seeded_sign_support_range (sk : SphincsSecurity.Seeded.SecretKey)
    (cache : TopCache) (message : Message) (out : Option Signature)
    (h : out ∈ support (SphincsSecurity.Seeded.sign
      (m := OracleComp HashSpec) sk cache message)) :
    ∀ σ, out = some σ → CountersInRange σ := by
  rw [SphincsSecurity.Seeded.sign] at h
  obtain ⟨tag, _, hrest⟩ := (mem_support_bind_iff _ _ _).mp h
  by_cases htag : tag = cache.tag
  · simp only [htag, if_true] at hrest
    exact seeded_signChecked_support_range sk cache message out hrest
  · simp only [htag, if_false, support_pure, Set.mem_singleton_iff] at hrest
    intro σ heq
    rw [hrest] at heq
    cases heq

theorem typed_signature_canonical (σ : Signature) (h : CountersInRange σ) :
    CanonicalWitness (SigGolfCandidate.Ref.expandRef (SigGolfCandidate.Equiv.sigCodec.symm σ)) := by
  let w := SigGolfCandidate.Ref.expandRef (SigGolfCandidate.Equiv.sigCodec.symm σ)
  apply countersOk_to_canonical
  have hdec : SigGolfCandidate.Equiv.sigOfWit (SigGolfCandidate.Ref.toList w) = σ := by
    have hd := SigGolfCandidate.Equiv.witDec_expandRef
      (SigGolfCandidate.Equiv.sigCodec.symm σ)
    change SigGolfCandidate.Equiv.sigOfWit (SigGolfCandidate.Ref.toList w) =
      SigGolfCandidate.Equiv.sigCodec (SigGolfCandidate.Equiv.sigCodec.symm σ) at hd
    simpa only [Equiv.apply_symm_apply] using hd
  rw [SigGolfCandidate.Equiv.countersOk_eq (SigGolfCandidate.Ref.toList w)
    (SigGolfCandidate.Ref.length_toList w), hdec]
  exact decide_eq_true h

/-- Every successful reference signer output has five counters below 2^22, for any
cache request and every possible oracle response. -/
theorem signRef_support_canonical (sk : SigGolfCandidate.Legacy.SecretKey)
    (cache : SigGolfCandidate.Cache) (message : SigGolfCandidate.Legacy.Message)
    (out : Option (SigGolfCandidate.Legacy.Bytes 6404))
    (h : out ∈ support (SigGolfCandidate.Ref.signRef sk cache message)) :
    ∀ σ, out = some σ → CanonicalWitness (SigGolfCandidate.Ref.expandRef σ) := by
  let key : SphincsSecurity.Seeded.SecretKey := ⟨sk, 0, 0⟩
  have heq := SigGolfCandidate.Equiv.signRef_eq key rfl cache message
  rw [heq, support_map] at h
  obtain ⟨typedOut, htyped, hmap⟩ := h
  have htyped' : typedOut ∈ support (SphincsSecurity.Seeded.sign
      (m := OracleComp HashSpec) key (SigGolfCandidate.Equiv.cacheDec cache) message) := by
    rw [← support_relabel SigGolfCandidate.Equiv.fmtQ]
    exact htyped
  cases typedOut with
  | none =>
      intro σ heqout
      simp only [Option.map_none] at hmap
      rw [← hmap] at heqout
      cases heqout
  | some typed =>
      have hc := seeded_sign_support_range key
        (SigGolfCandidate.Equiv.cacheDec cache) message (some typed) htyped' typed rfl
      intro σ heqout
      have hs : σ = SigGolfCandidate.Equiv.sigCodec.symm typed := by
        simpa only [Option.map_some, Option.some.injEq] using heqout.symm.trans hmap.symm
      rw [hs]
      exact typed_signature_canonical typed hc

end SigGolfCandidate.Packed
