import SigGolf
import SigGolfCandidate.Transport.SecurityFinal
import SigGolfCandidate.Packed.CompleteCore
import SigGolfCandidate.Packed.BudgetBridge
import SigGolfCandidate.Packed.TermCore

/-!
# sig.golf: packed five-counter stateless hash-based signature

Five 22-bit WOTS counters are packed in 14 bytes. The unchanged body is
6384 bytes; the resulting signature is 6398 bytes. The witness is 6404
bytes and the cache is 131072 bytes. The accepted-path verifier has
11498 concrete RV64 cycles; the organizer charges 26 witness cycles.

The packed legacy certificate proves admission, all-input termination,
all-message per-seed completeness, honest compression budgets, 127-bit
adaptive unforgeability, and the 11524 accepting-cycle bound. The codec
proves an exact left inverse on every packed string and exact honest
round-trip, including the signing oracle trace.
-/

namespace SigGolfCandidate.Packed
open SigGolfCandidate.Legacy OracleComp OracleSpec
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000
set_option allowUnsafeReducibility true in
attribute [local reducible] SigGolfCandidate.Legacy.Input SigGolfCandidate.Legacy.Output
  SigGolfCandidate.Packed.submission SigGolfCandidate.Packed.ExpandMain.concrete

private abbrev concrete := ExpandMain.concrete

theorem admissible_packed : concrete.Admissible := by
  refine ⟨?_, ?_⟩
  · change sizes.Valid
    unfold Sizes.Valid
    decide
  · intro phase
    cases phase with
    | keygen => exact packed_keygen_valid
    | sign => exact Images.sign_valid
    | expand => exact Images.expand_valid
    | verify => exact packed_verify_valid

theorem signRefinementPacked : SignRefinementStatement := by
  intro sk cache m
  change (fun r => (r.value, r.hashCalls, r.hashCompressions)) <$>
      Sign.submission.run .sign (sk, cache, m) =
    (fun p => (p.1.map packOldAny, p.2.1, p.2.2)) <$>
      Sign.countBoth (Ref.signRef sk cache m)
  exact Sign.sign_refines_packed sk cache m

theorem signTerminationPacked :
    ∀ (hash : Hash) (sk : SecretKey) (cache : Cache) (m : Message),
      (concrete.runWith hash .sign (sk, cache, m)).finished = true ∧
        (concrete.runWith hash .sign (sk, cache, m)).cycles < CYCLE_LIMIT := by
  intro hash sk cache m
  have hs := Sign.sign_terminates_packed hash sk cache m
  exact ⟨hs.1, lt_of_le_of_lt hs.2 Sign.signW_post_lt⟩

theorem certificate_packed : Certificate concrete 11524 where
  admissible := admissible_packed
  termination := terminates_packed signTerminationPacked
  completeness := complete_packed signRefinementPacked
    Final.keygenRefinement Final.signRefinement Final.verifyRefinement
  compressionBounds := budget_packed Final.keygenRefinement
  security := packed_secure
  verificationBound := verificationBound_packed

#print axioms admissible_packed
#print axioms signRefinementPacked
#print axioms signTerminationPacked
#print axioms certificate_packed
end SigGolfCandidate.Packed

namespace SigGolf.Challenge

private abbrev concrete := SigGolfCandidate.Packed.ExpandMain.concrete

def submission : SigGolf.Submission :=
  SigGolfCandidate.Transport.submission concrete

theorem signature_bytes : submission.sizes.signature = 6398 := rfl

theorem witness_bytes : submission.sizes.witness = 6404 := rfl

theorem cache_bytes : submission.sizes.cache = 131072 := rfl

theorem layout_offsets : submission.layout =
  { message := 64, secretKey := 128, publicKey := 160,
    cache := 17568, signature := 9808, witness := 2048 } := rfl

theorem certificate : SigGolf.Certificate submission 11524 := by
  have old := SigGolfCandidate.Packed.certificate_packed
  exact {
    admission := SigGolfCandidate.Transport.admission _ old.admissible
    completeness := SigGolfCandidate.Transport.completeness _ old.admissible old.completeness
    compressionBudgets := SigGolfCandidate.Transport.compressionBudgets _ old.admissible old.compressionBounds
    verificationCycles := SigGolfCandidate.Transport.verificationCycles _ old.admissible _ old.verificationBound
    security := SigGolfCandidate.Transport.security _ old.admissible old.security
    termination := SigGolfCandidate.Transport.termination _ old.admissible old.termination
  }

#print axioms certificate
end SigGolf.Challenge
