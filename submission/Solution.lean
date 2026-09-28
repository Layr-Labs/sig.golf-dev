import SigGolf
import SigGolfCandidate.Packed.Radix27Sign
import SigGolfCandidate.Packed.Radix27Final
import SigGolfCandidate.Transport.SecurityFinal

/-!
# sig.golf: 13-byte radix-27 counter trailer

The five low 16-bit counters occupy ten bytes. Their bounded high parts are
ranked in base 27 and stored in three bytes. The 6384-byte signature body
therefore gives a 6397-byte signature. The witness remains 6404 bytes.

The certificate covers the codec, every signer and expander RISC-V branch,
all-message completeness, adaptive security, honest compression budgets,
all-input termination, and the 11530-cycle accepting verification bound.
-/

namespace SigGolfCandidate.Radix27Final
open SigGolfCandidate SigGolfCandidate.Legacy OracleComp
set_option maxRecDepth 200000
set_option maxHeartbeats 3000000
set_option allowUnsafeReducibility true in
attribute [local reducible] SigGolfCandidate.Legacy.Input SigGolfCandidate.Legacy.Output
  Radix27Submission.concrete

theorem signRefinement13 : Radix27CompleteCore.SignRefinement13 := by
  intro sk cache m
  exact SigGolfCandidate.Radix27Sign.sign_refines13_concrete sk cache m

theorem signTermination13 :
    ∀ (hash : Hash) (sk : SecretKey) (cache : Cache) (m : Message),
      (Radix27Submission.concrete.runWith hash .sign (sk, cache, m)).finished = true ∧
        (Radix27Submission.concrete.runWith hash .sign (sk, cache, m)).cycles < CYCLE_LIMIT := by
  intro hash sk cache m
  have hs := SigGolfCandidate.Radix27Sign.sign_terminates13_concrete hash sk cache m
  exact ⟨hs.1, lt_of_le_of_lt hs.2 SigGolfCandidate.Radix27Sign.signW_post_lt⟩

theorem certificate13 : SigGolfCandidate.Legacy.Certificate Radix27Submission.concrete 11530 :=
  Radix27FinalCert.certificate_of_sign signRefinement13 signTermination13

#print axioms certificate13
end SigGolfCandidate.Radix27Final

namespace SigGolf.Challenge

private abbrev concrete := Radix27Submission.concrete

def submission : SigGolf.Submission :=
  SigGolfCandidate.Transport.submission concrete

theorem signature_bytes : submission.sizes.signature = 6397 := rfl
theorem witness_bytes : submission.sizes.witness = 6404 := rfl
theorem cache_bytes : submission.sizes.cache = 131072 := rfl
theorem layout_offsets : submission.layout =
  { message := 64, secretKey := 128, publicKey := 160,
    cache := 17568, signature := 9808, witness := 2048 } := rfl

theorem certificate : SigGolf.Certificate submission 11530 := by
  have old := SigGolfCandidate.Radix27Final.certificate13
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
