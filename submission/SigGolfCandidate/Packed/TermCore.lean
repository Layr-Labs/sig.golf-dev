import SigGolfCandidate.Packed.ExpandMain
import SigGolfCandidate.Packed.RunWithEq
import SigGolfCandidate.Final.Discharge

/-! Final legacy certificate for the 6398-byte packed signature image. -/

namespace SigGolfCandidate.Packed

open SigGolfCandidate.Legacy OracleComp OracleSpec
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000
set_option allowUnsafeReducibility true in
attribute [local reducible] SigGolfCandidate.Legacy.Input SigGolfCandidate.Legacy.Output
  SigGolfCandidate.Packed.submission SigGolfCandidate.Packed.ExpandMain.concrete

private abbrev concrete := ExpandMain.concrete

theorem terminates_packed
    (hS : ∀ (hash : Hash) (sk : SecretKey) (cache : Cache) (m : Message),
      (concrete.runWith hash .sign (sk, cache, m)).finished = true ∧
        (concrete.runWith hash .sign (sk, cache, m)).cycles < CYCLE_LIMIT) :
    concrete.Terminates := by
  intro hash phase input
  cases phase with
  | keygen =>
      dsimp only
      change (concrete.runWith hash .keygen input).finished = true ∧
        (concrete.runWith hash .keygen input).cycles < CYCLE_LIMIT
      rw [keygen_runWith_eq]
      exact Final.keygenTermination hash input
  | sign =>
      obtain ⟨sk, cache, m⟩ := input
      exact hS hash sk cache m
  | expand =>
      obtain ⟨m, pk, σ⟩ := input
      change Bytes 6398 at σ
      dsimp only
      rw [ExpandMain.expand_runWith]
      exact ⟨rfl, by change 9607 < CYCLE_LIMIT; decide⟩
  | verify =>
      obtain ⟨m, pk, w⟩ := input
      dsimp only
      change (concrete.runWith hash .verify (m, pk, w)).finished = true ∧
        (concrete.runWith hash .verify (m, pk, w)).cycles < CYCLE_LIMIT
      rw [verify_runWith_eq]
      exact Final.verifyTermination hash m pk w


theorem verificationBound_packed : concrete.VerificationBound 11523 := by
  intro hash sk m
  dsimp only
  intro h
  obtain ⟨⟨m', pk, w⟩, hacc, hcyc⟩ :=
    Final.honest_success_verify concrete hash sk m h
  rw [hcyc]
  have hb := (Verify.verify_terminates hash (m', pk, w)).2.1
  rw [verify_runWith_eq]
  change (SigGolfCandidate.submission.runWith hash .verify (m', pk, w)).cycles + 26 ≤ 11523
  change (SigGolfCandidate.submission.runWith hash .verify (m', pk, w)).cycles ≤ 11497 at hb
  omega



#print axioms terminates_packed
#print axioms verificationBound_packed
end SigGolfCandidate.Packed
