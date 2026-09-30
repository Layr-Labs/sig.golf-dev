import SigGolf
import SigGolfCandidate.Transfer.Final

/-!
# sig.golf solution: SPHINCS+ with PORS+FP (forced-pruning single-tree few-time signature)

Small-signature variant: 4-bit target-sum WOTS (32 chains, target sum 312) on a 6-layer hypertree
(heights 11, 5, 5, 5, 4, 4), with the PORS+FP few-time part unchanged.
`S = 5784` bytes, `W = 6064` bytes, `K = 131072` bytes (cache), `C = 20593` cycles (verify bound
`20569` plus the witness charge `⌈6064 / 256⌉ = 24`). Layout (bytes): message 64, secret key 128,
public key 160, cache 19200, signature 13056, witness 2048.

The certificate is `SigGolfCandidate.certificateNew`. It is transferred from
`SigGolfCandidate.Final.certificate`, a certificate for the same images under the previous
organizer contract (70ba436, kept verbatim as `SigGolfCandidate.Legacy`): `SigGolfCandidate.Transfer`
proves that both contracts' machines and runs agree on admissible images and transfers each statement.
In the legacy certificate the four RISC-V images are proved to refine a byte-level reference
(`SigGolfCandidate.Ref`), which is proved equal to the abstract SPHINCS+ scheme with PORS+FP
(`SphincsSecurity`) up to the oracle input format; the abstract scheme's 127-bit event-form
security, per-seed completeness and correctness are transported to the organizer's game through
`SigGolfCandidate.Bridge`.
-/

namespace SigGolf.Challenge

def submission : SigGolf.Submission := SigGolfCandidate.submissionNew

theorem signature_bytes : submission.sizes.signature = 5784 := rfl

theorem witness_bytes : submission.sizes.witness = 6064 := rfl

theorem cache_bytes : submission.sizes.cache = 131072 := rfl

theorem layout_offsets : submission.layout =
  { message := 64, secretKey := 128, publicKey := 160,
    cache := 19200, signature := 13056, witness := 2048 } := rfl

theorem certificate : SigGolf.Certificate submission 20593 :=
  SigGolfCandidate.certificateNew

end SigGolf.Challenge
