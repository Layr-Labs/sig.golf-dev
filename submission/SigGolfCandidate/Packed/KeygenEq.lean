import SigGolfCandidate.Packed.ExpandMain
import SigGolfCandidate.Packed.ReductionFinal
import SigGolfCandidate.Submission

namespace SigGolfCandidate.Packed
open SigGolfCandidate.Legacy
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000

private abbrev baseLayout : Layout := SigGolfCandidate.submission.layout
private abbrev oldImages : Phase → Riscv.Image := SigGolfCandidate.submission.image
private abbrev packedImages : Phase → Riscv.Image := ExpandMain.concrete.image

theorem packed_keygen_valid :
    ((shortSubmission baseLayout packedImages).image .keygen).Valid
      (shortSubmission baseLayout packedImages).sizes
      (shortSubmission baseLayout packedImages).layout := by
  constructor
  · exact SigGolfCandidate.submission_keygen_valid.1
  · decide +kernel

theorem initial_keygen_eq (sk : SecretKey) :
    initialState (shortSubmission baseLayout packedImages) .keygen sk =
    initialState (oldSubmission baseLayout oldImages) .keygen sk := by
  have old_valid :
      ((oldSubmission baseLayout oldImages).image .keygen).Valid
        (oldSubmission baseLayout oldImages).sizes
        (oldSubmission baseLayout oldImages).layout :=
    SigGolfCandidate.submission_keygen_valid
  unfold initialState
  rw [if_pos packed_keygen_valid, if_pos old_valid]
  rfl

theorem keygen_run_eq (sk : SecretKey) :
    (shortSubmission baseLayout packedImages).run .keygen sk =
    (oldSubmission baseLayout oldImages).run .keygen sk := by
  unfold Submission.run
  rw [initial_keygen_eq]
  have hc : (shortSubmission baseLayout packedImages).image .keygen =
      (oldSubmission baseLayout oldImages).image .keygen := rfl
  rw [hc]
  rfl

#print axioms packed_keygen_valid
#print axioms initial_keygen_eq
#print axioms keygen_run_eq

end SigGolfCandidate.Packed
