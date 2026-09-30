import SigGolfCandidate.Packed.Codec
import SigGolfCandidate.Submission

/-!
# An isolated submission for packed signatures

The certified 6404-byte submission remains available unchanged. The packed
candidate shares its keygen and verifier bytecode and supplies only new signer
and expander images. Keeping these as parameters lets the security reduction be
proved before the RISC-V implementations are final.
-/

namespace SigGolfCandidate.Packed

open SigGolfCandidate.Legacy

def submission (signImage expandImage : Riscv.Image) : Submission where
  sizes := sizes
  layout := SigGolfCandidate.submission.layout
  image
    | .keygen => SigGolfCandidate.submission.image .keygen
    | .sign => signImage
    | .expand => expandImage
    | .verify => SigGolfCandidate.submission.image .verify

theorem submission_sizes (signImage expandImage : Riscv.Image) :
    (submission signImage expandImage).sizes = sizes := rfl

end SigGolfCandidate.Packed
