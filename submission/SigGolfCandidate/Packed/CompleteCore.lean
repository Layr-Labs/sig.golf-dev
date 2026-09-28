import SigGolfCandidate.Packed.SignClone.Sim
import SigGolfCandidate.Packed.ExpandMain
import SigGolfCandidate.Packed.TypedRange
import SigGolfCandidate.Packed.KeygenEq
import SigGolfCandidate.Packed.SecureBridge
import SigGolfCandidate.Final.Refine
import SigGolfCandidate.Final.Completeness

/-! Honest completeness transfer for the 6398-byte packed image. -/

namespace SigGolfCandidate.Packed

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open SigGolfCandidate.Legacy SigGolfCandidate.Final OracleComp OracleSpec

set_option allowUnsafeReducibility true in
attribute [local reducible] SigGolfCandidate.Legacy.Input SigGolfCandidate.Legacy.Output
  SigGolfCandidate.Packed.submission SigGolfCandidate.Packed.ExpandMain.concrete
  SigGolfCandidate.Packed.shortSubmission SigGolfCandidate.Packed.oldSubmission

private abbrev concrete := ExpandMain.concrete

def SignRefinementStatement : Prop :=
  ∀ (sk : SecretKey) (cache : Cache) (m : Message),
    (fun r => (r.value, r.hashCalls, r.hashCompressions)) <$>
      concrete.run .sign (sk, cache, m) =
    (fun p => (p.1.map packOldAny, p.2.1, p.2.2)) <$>
      Sign.countBoth (Ref.signRef sk cache m)

private theorem projectValue {α β : Type}
    (F : OracleComp HashSpec (RunResult α))
    (G : OracleComp HashSpec (β × Nat × Nat))
    (f : β → Option α)
    (h : (fun r => (r.value, r.hashCalls, r.hashCompressions)) <$> F =
      (fun p => (f p.1, p.2.1, p.2.2)) <$> G) :
    (fun r => r.value) <$> F = f <$> (Prod.fst <$> G) := by
  have hp := congrArg (fun X => Prod.fst <$> X) h
  simpa only [Functor.map_map, Function.comp_def, Prod.fst] using hp

theorem keygen_value_packed (hK : Final.KeygenRefinementStatement) (sk : SecretKey) :
    (fun r => r.value) <$> concrete.run .keygen sk =
      some <$> Ref.keygenRef sk := by
  change (fun r => r.value) <$>
    (shortSubmission SigGolfCandidate.submission.layout ExpandMain.concrete.image).run .keygen sk =
      some <$> Ref.keygenRef sk
  rw [keygen_run_eq]
  change (fun r => r.value) <$> SigGolfCandidate.submission.run .keygen sk =
    some <$> Ref.keygenRef sk
  exact Final.keygen_value hK sk

theorem sign_value_packed (hPacked : SignRefinementStatement)
    (sk : SecretKey) (cache : Cache) (m : Message) :
    (fun r => r.value) <$> concrete.run .sign (sk, cache, m) =
      Option.map packOldAny <$> Ref.signRef sk cache m := by
  have hp := projectValue (concrete.run .sign (sk, cache, m))
    (Sign.countBoth (Ref.signRef sk cache m))
    (Option.map packOldAny) (hPacked sk cache m)
  rw [Sign.fst_countBoth] at hp
  exact hp

theorem expand_value_packed (m : Message) (pk : PublicKey) (σ : Bytes 6398) :
    (fun r => r.value) <$> concrete.run .expand (m, pk, σ) =
      pure (some (expandWitness σ)) := by
  rw [ExpandMain.expand_run, map_pure]

theorem verify_value_packed (hV : Final.VerifyRefinementStatement)
    (m : Message) (pk : PublicKey) (w : Bytes 6404) :
    (fun r => r.value.isSome) <$> concrete.run .verify (m, pk, w) =
      Ref.verifyRef m pk w := by
  change (fun r => r.value.isSome) <$>
    (shortSubmission SigGolfCandidate.submission.layout ExpandMain.concrete.image).run .verify
      (m, pk, w) = Ref.verifyRef m pk w
  rw [verify_run_eq]
  change (fun r => r.value.isSome) <$>
    SigGolfCandidate.submission.run .verify (m, pk, w) = Ref.verifyRef m pk w
  exact Final.verify_value hV m pk w

/-- All successful reference signatures are canonical, so the short honest
pipeline has exactly the old reference success bit. -/
theorem successPipe_packed_eq_ref (hPacked : SignRefinementStatement)
    (hK : Final.KeygenRefinementStatement)
    (hV : Final.VerifyRefinementStatement) (sk : SecretKey) (m : Message) :
    Final.successPipe concrete sk m = (do
      let (pk, cache) ← Ref.keygenRef sk
      match ← Ref.signRef sk cache m with
      | none => pure false
      | some σ => Ref.verifyRef m pk (Ref.expandRef σ)) := by
  unfold Final.successPipe
  rw [keygen_value_packed hK, bind_map_left]
  refine bind_congr fun kc => ?_
  rcases kc with ⟨pk, cache⟩
  simp only
  rw [sign_value_packed hPacked, bind_map_left]
  apply OracleComp.bind_congr_of_forall_mem_support
  intro s hs
  rcases s with _ | σ
  · rfl
  simp only [Option.map_some]
  rw [expand_value_packed, pure_bind]
  dsimp only
  rw [verify_value_packed hV m pk (expandWitness (packOldAny σ))]
  have hc := signRef_support_canonical sk cache m (some σ) hs σ rfl
  change Ref.verifyRef m pk (expandWitness (packOldAny σ)) =
    Ref.verifyRef m pk (Ref.expandRef σ)
  rw [packOldAny, expand_shrinkAny_canonical _ hc]

theorem success_honest_packed_eq_old (hPacked : SignRefinementStatement)
    (hK : Final.KeygenRefinementStatement)
    (hS : Final.SignRefinementStatement) (hV : Final.VerifyRefinementStatement)
    (sk : SecretKey) (m : Message) :
    HonestResult.success <$> concrete.honest sk m =
      HonestResult.success <$> SigGolfCandidate.submission.honest sk m := by
  rw [Final.success_honest_eq, Final.success_honest_eq,
    successPipe_packed_eq_ref hPacked hK hV, Final.successPipe_eq_ref hK hS hV]
  rfl

theorem allSucceed_packed_eq_old (hPacked : SignRefinementStatement)
    (hK : Final.KeygenRefinementStatement)
    (hS : Final.SignRefinementStatement) (hV : Final.VerifyRefinementStatement)
    (sk : SecretKey) :
    HonestSummary.allSucceed <$> concrete.allMessages sk =
      HonestSummary.allSucceed <$> SigGolfCandidate.submission.allMessages sk := by
  rw [Final.allSucceed_allMessages, Final.allSucceed_allMessages]
  refine congrArg (fun P => foldAll (Finset.univ : Finset Message).toList P true)
    (funext fun m => ?_)
  exact success_honest_packed_eq_old hPacked hK hS hV sk m

theorem complete_packed (hPacked : SignRefinementStatement)
    (hK : Final.KeygenRefinementStatement)
    (hS : Final.SignRefinementStatement) (hV : Final.VerifyRefinementStatement) :
    concrete.Complete := by
  intro sk
  have peq (sub : Submission) :
      Pr[fun summary => summary.allSucceed = true |
        withRandomOracle (sub.allMessages sk)] =
      Pr[= true | withRandomOracle (HonestSummary.allSucceed <$> sub.allMessages sk)] := by
    rw [Final.withRandomOracle_map, ← probEvent_eq_eq_probOutput, probEvent_map]
    rfl
  rw [peq concrete, allSucceed_packed_eq_old hPacked hK hS hV sk,
    ← peq SigGolfCandidate.submission]
  exact Final.submission_complete hK hS hV sk

#print axioms sign_value_packed
#print axioms successPipe_packed_eq_ref
#print axioms complete_packed

end SigGolfCandidate.Packed
