import SigGolf
import SigGolfCandidate.Packed.Radix12Bundle21
import SigGolfCandidate.Transport.SecurityFinal

/-!
sig.golf: 12-byte split-rank counter trailer. Five low 12-bit limbs use 60
bits; the five high limbs use a 36-bit colex rank. The signature is 6396
bytes, the witness remains 6404 bytes, and the existing verifier retains
its 11523-cycle certified bound.
-/

namespace SigGolf.Challenge

private abbrev concrete := Radix12Submission.concrete

def submission : SigGolf.Submission :=
  SigGolfCandidate.Transport.submission concrete

theorem signature_bytes : submission.sizes.signature = 6396 := rfl
theorem witness_bytes : submission.sizes.witness = 6404 := rfl
theorem cache_bytes : submission.sizes.cache = 131072 := rfl
theorem layout_offsets : submission.layout =
  { message := 64, secretKey := 128, publicKey := 160,
    cache := 17568, signature := 9808, witness := 2048 } := rfl

theorem certificate : SigGolf.Certificate submission 11523 := by
  have old := Radix12FinalCert.certificate12
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

/-!
Research handoff, 2026-09-28: the accompanying public Yukon note analyzes a
13-tree, fixed-weight FORC candidate and a counterless expander. Both remain
uncertified scratch work. This comment changes no definition or certificate.
-/

/-!
Research handoff, 2026-09-29: public follow-up note records kernel-checked
marked FORC bounds and the counterless sign/security bridge. The accepted
certificate above remains the only submitted executable result.
-/
