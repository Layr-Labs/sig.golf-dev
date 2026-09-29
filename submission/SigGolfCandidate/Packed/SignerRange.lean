import SigGolfCandidate.Packed.CounterRange

/-!
# Canonical signer counters

The reference signer chooses each layer counter by searching from zero for
`cMax = 2^22` attempts. Its five outputs therefore have high ten bits zero,
regardless of the cache supplied to the signer.
-/

namespace SigGolfCandidate.Packed

open SigGolfCandidate.Legacy SigGolfCandidate.Ref OracleComp OracleSpec

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-- Direct support form of the search range lemma, without a message-length
premise. This form is convenient under arbitrary intermediate hash outputs. -/
theorem searchCounter_support_range (lay tau leaf : Nat) (message : Val) :
    ∀ fuel start out,
      out ∈ support (searchCounter lay tau leaf message start fuel) →
      SearchRange start fuel out := by
  intro fuel
  induction fuel with
  | zero =>
      intro start out h
      simp only [searchCounter, support_pure, Set.mem_singleton_iff] at h
      subst out
      simp [SearchRange]
  | succ fuel ih =>
      intro start out h
      rw [searchCounter] at h
      obtain ⟨digest, _, hrest⟩ := (mem_support_bind_iff _ _ _).mp h
      cases hdecode : decodeDigits digest with
      | some digits =>
          simp only [hdecode, support_pure, Set.mem_singleton_iff] at hrest
          subst out
          intro counter digits' heq
          simp only [Option.some.injEq, Prod.mk.injEq] at heq
          omega
      | none =>
          simp only [hdecode] at hrest
          intro counter digits heq
          obtain ⟨hlo, hhi⟩ := ih (start + 1) out hrest counter digits heq
          omega

/-- Every successful layer search yields a 22-bit counter. -/
theorem searchCounter_support_cMax (lay tau leaf : Nat) (message : Val)
    (out : Option (Nat × List Nat))
    (h : out ∈ support (searchCounter lay tau leaf message 0 cMax)) :
    ∀ counter digits, out = some (counter, digits) → counter < cMax := by
  intro counter digits heq
  exact (searchCounter_support_range lay tau leaf message cMax 0 out h counter digits heq).2

/-- All counters in an optional list of signed layers are below the signer limit. -/
def LayersInRange (out : Option (List LayerSig)) : Prop :=
  ∀ layers, out = some layers → ∀ layer ∈ layers, layer.1 < cMax

theorem signTop_support_range (secret cache : List Byte) (index : Nat) (message : Val)
    (out : Option (List LayerSig))
    (h : out ∈ support (signTop secret cache index message)) : LayersInRange out := by
  rw [signTop] at h
  rcases hroute : route index 0 with ⟨leaf, tree⟩
  simp only [hroute] at h
  obtain ⟨search, hsearch, hrest⟩ := (mem_support_bind_iff _ _ _).mp h
  cases search with
  | none =>
      simp only [support_pure, Set.mem_singleton_iff] at hrest
      subst out
      intro layers heq
      cases heq
  | some result =>
      obtain ⟨counter, digits⟩ := result
      have hcounter : counter < cMax :=
        searchCounter_support_cMax 0 tree leaf message _ hsearch counter digits rfl
      obtain ⟨values, _, hrest⟩ := (mem_support_bind_iff _ _ _).mp hrest
      obtain ⟨path, _, hrest⟩ := (mem_support_bind_iff _ _ _).mp hrest
      simp only [support_pure, Set.mem_singleton_iff] at hrest
      subst out
      intro layers heq layer hmem
      cases heq
      simp only [List.mem_singleton] at hmem
      subst layer
      exact hcounter

theorem signLayers_support_range (secret cache : List Byte) (index : Nat) :
    ∀ depth message out,
      out ∈ support (signLayers secret cache index depth message) → LayersInRange out := by
  intro depth
  induction depth with
  | zero =>
      intro message out h
      exact signTop_support_range secret cache index message out h
  | succ depth ih =>
      intro message out h
      rw [signLayers] at h
      rcases hroute : route index (depth + 1) with ⟨leaf, tree⟩
      simp only [hroute] at h
      obtain ⟨search, hsearch, hrest⟩ := (mem_support_bind_iff _ _ _).mp h
      cases search with
      | none =>
          simp only [support_pure, Set.mem_singleton_iff] at hrest
          subst out
          intro layers heq
          cases heq
      | some result =>
          obtain ⟨counter, digits⟩ := result
          have hcounter : counter < cMax :=
            searchCounter_support_cMax (depth + 1) tree leaf message _ hsearch counter digits rfl
          obtain ⟨built, _, hrest⟩ := (mem_support_bind_iff _ _ _).mp hrest
          obtain ⟨root, values, path⟩ := built
          obtain ⟨rest, hrec, hrest⟩ := (mem_support_bind_iff _ _ _).mp hrest
          cases rest with
          | none =>
              simp only [support_pure, Set.mem_singleton_iff] at hrest
              subst out
              intro layers heq
              cases heq
          | some prior =>
              simp only [support_pure, Set.mem_singleton_iff] at hrest
              subst out
              intro layers heq layer hmem
              cases heq
              rw [List.mem_append] at hmem
              rcases hmem with hmem | hmem
              · exact ih root (some prior) hrec prior rfl layer hmem
              · simp only [List.mem_singleton] at hmem
                subst layer
                exact hcounter

/-- A successful reference signature was serialized from layers whose counters
are all below `cMax`. -/
def SignedLayout (out : Option (List Byte)) : Prop :=
  ∀ bytes, out = some bytes →
    ∃ (randomness : Val) (forest : List (Val × List Val)) (layers : List LayerSig),
      bytes = serialize randomness forest layers ∧
      ∀ layer ∈ layers, layer.1 < cMax

theorem signList_support_layout (secret cache message : List Byte)
    (out : Option (List Byte)) (h : out ∈ support (signList secret cache message)) :
    SignedLayout out := by
  rw [signList] at h
  obtain ⟨tag, _, hrest⟩ := (mem_support_bind_iff _ _ _).mp h
  by_cases htag : toList (n := 32) tag = cacheTag cache
  · simp only [htag, if_true] at hrest
    obtain ⟨search, _, hrest⟩ := (mem_support_bind_iff _ _ _).mp hrest
    cases search with
    | none =>
        simp only [support_pure, Set.mem_singleton_iff] at hrest
        subst out
        intro bytes heq
        cases heq
    | some found =>
        obtain ⟨randomness, index⟩ := found
        obtain ⟨built, _, hrest⟩ := (mem_support_bind_iff _ _ _).mp hrest
        obtain ⟨forest, roots⟩ := built
        obtain ⟨rootMessage, _, hrest⟩ := (mem_support_bind_iff _ _ _).mp hrest
        obtain ⟨layers, hlayers, hrest⟩ := (mem_support_bind_iff _ _ _).mp hrest
        cases layers with
        | none =>
            simp only [support_pure, Set.mem_singleton_iff] at hrest
            subst out
            intro bytes heq
            cases heq
        | some selected =>
            simp only [support_pure, Set.mem_singleton_iff] at hrest
            subst out
            intro bytes heq
            cases heq
            exact ⟨randomness, forest, selected, rfl,
              signLayers_support_range secret cache (idxOf index) (nLayers - 1)
                rootMessage (some selected) hlayers selected rfl⟩
  · simp only [htag, if_false, support_pure, Set.mem_singleton_iff] at hrest
    subst out
    intro bytes heq
    cases heq

end SigGolfCandidate.Packed
