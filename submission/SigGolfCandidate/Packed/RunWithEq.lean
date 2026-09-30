import SigGolfCandidate.Packed.KeygenEq
import SigGolfCandidate.Packed.SecureBridge

namespace SigGolfCandidate.Packed
open SigGolfCandidate.Legacy OracleComp
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000

private abbrev concrete := ExpandMain.concrete
private abbrev baseLayout : Layout := SigGolfCandidate.submission.layout
private abbrev oldImages : Phase → Riscv.Image := SigGolfCandidate.submission.image
private abbrev packedImages : Phase → Riscv.Image := concrete.image

theorem keygen_runWith_eq (hash : Hash) (sk : SecretKey) :
    concrete.runWith hash .keygen sk =
      SigGolfCandidate.submission.runWith hash .keygen sk := by
  unfold Submission.runWith
  change evalWithAnswerFn hash
    ((shortSubmission baseLayout packedImages).run .keygen sk) =
    evalWithAnswerFn hash
    ((oldSubmission baseLayout oldImages).run .keygen sk)
  rw [keygen_run_eq]
  rfl

theorem verify_runWith_eq (hash : Hash) (message : Message)
    (pk : PublicKey) (witness : Bytes 6404) :
    concrete.runWith hash .verify (message, pk, witness) =
      SigGolfCandidate.submission.runWith hash .verify (message, pk, witness) := by
  unfold Submission.runWith
  change evalWithAnswerFn hash
    ((shortSubmission baseLayout packedImages).run .verify (message, pk, witness)) =
    evalWithAnswerFn hash
    ((oldSubmission baseLayout oldImages).run .verify (message, pk, witness))
  rw [verify_run_eq]
  rfl

#print axioms keygen_runWith_eq
#print axioms verify_runWith_eq
end SigGolfCandidate.Packed
