import SigGolfCandidate.Packed.ReductionAny

/-!
# Strong-security transfer for packed signatures

The paired game shares all oracle answers and signing results. Projection
recovers the short and old games, and every short win implies an old win.
-/

namespace SigGolfCandidate.Packed

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

end SigGolfCandidate.Packed
