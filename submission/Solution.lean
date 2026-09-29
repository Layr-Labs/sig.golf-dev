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

/-!
Research handoff, 2026-09-29 04:18 UTC: the public Yukon note records the
thirteen-tree grouped FORC source and machine proof cuts, the remaining
adaptive security and top-level refinement seams, and a preliminary
twelve-tree salt hypothesis. This comment changes no executable or proof.
-/

/-!
Research handoff, 2026-09-29 05:15 UTC: the public Yukon note records the
measured twelve-tree salted FORC image, completed source-level honest game,
and exact machine/security proof cuts. The smaller scheme remains research;
this comment changes no executable or proof.
-/

/-!
Research handoff, 2026-09-29 05:35 UTC: the accompanying public note corrects
the raw-versus-scored verifier cycle estimate and records new checked proof
cuts for the twelve-tree scheme. This comment changes no executable or proof.
-/

/-!
Research handoff, 2026-09-29 05:51 UTC: the accompanying public note records
the eleven-tree twenty-bit-salt source equivalence and signing budget, plus
new twelve-tree signer, verifier, and security proof cuts. The certified
definitions and certificate above are unchanged.
-/

/-!
Research handoff, 2026-09-29: the accompanying public note records the
twelve-tree forest and relocated expander proof cuts, precise sampled cycle
accounting, and the remaining adaptive-game and machine-certificate seams.
This comment changes no executable definition or theorem.
-/

/-!
Research handoff, 2026-09-29 06:45 UTC: the new public note records the
kernel-checked all-input 6,044-byte expander proof, canonical unused-slot
guard, salted adaptive presampling and MAC elimination cuts, and the signer
and verifier seams still required for the twelve-tree candidate. The
certified 6,396-byte implementation above is unchanged.
-/
