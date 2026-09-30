import SigGolfCandidate.Packed.SignClone.Run
import SigGolfCandidate.Packed.ExpandMain
import SigGolfCandidate.Packed.ReductionFinal
import SigGolfCandidate.Final.Discharge

/-! Security transfer from the certified 6404-byte baseline to the packed image. -/
namespace SigGolfCandidate.Packed

open SigGolfCandidate.Legacy OracleComp

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

set_option allowUnsafeReducibility true in
attribute [local reducible] SigGolfCandidate.submission oldSubmission shortSubmission
  SigGolfCandidate.Packed.submission SigGolfCandidate.Legacy.Input
  SigGolfCandidate.Legacy.Output

private abbrev baseLayout : Layout := SigGolfCandidate.submission.layout
private abbrev oldImages : Phase → Riscv.Image := SigGolfCandidate.submission.image
private abbrev packedImages : Phase → Riscv.Image := ExpandMain.concrete.image

theorem packed_verify_valid :
    ((shortSubmission baseLayout packedImages).image .verify).Valid
      (shortSubmission baseLayout packedImages).sizes
      (shortSubmission baseLayout packedImages).layout := by
  constructor
  · exact SigGolfCandidate.submission_verify_valid.1
  · decide +kernel
theorem initial_verify_eq (message : Message) (pk : PublicKey)
    (witness : Bytes 6404) :
    initialState (shortSubmission baseLayout packedImages) .verify
      (message, pk, witness) =
    initialState (oldSubmission baseLayout oldImages) .verify
      (message, pk, witness) := by
  have old_valid :
      ((oldSubmission baseLayout oldImages).image .verify).Valid
        (oldSubmission baseLayout oldImages).sizes
        (oldSubmission baseLayout oldImages).layout := by
    exact SigGolfCandidate.submission_verify_valid
  unfold initialState
  rw [if_pos packed_verify_valid, if_pos old_valid]
  rfl

private theorem runVerifyEq (a b : Submission)
    (x : Input a.sizes .verify) (y : Input b.sizes .verify)
    (hi : initialState a .verify x = initialState b .verify y)
    (hc : a.image .verify = b.image .verify) :
    a.run .verify x = b.run .verify y := by
  unfold Submission.run
  rw [hi, hc]

theorem verify_run_eq (message : Message) (pk : PublicKey)
    (witness : Bytes 6404) :
    (shortSubmission baseLayout packedImages).run .verify (message, pk, witness) =
    (oldSubmission baseLayout oldImages).run .verify (message, pk, witness) := by
  apply runVerifyEq
  · exact initial_verify_eq message pk witness
  · change SigGolfCandidate.submission.image .verify =
        SigGolfCandidate.submission.image .verify
    rfl

theorem assumptionsAny : AssumptionsAny baseLayout oldImages packedImages where
  keygen sk := by
    rfl
  sign sk cache message := by
    change (observed <$> ExpandMain.concrete.run .sign (sk, cache, message)) =
      ((fun r => (r.value.map packOldAny, r.hashCalls)) <$>
        SigGolfCandidate.submission.run .sign (sk, cache, message))
    have hs := congrArg (fun X =>
      (fun p : Option (Bytes 6398) × Nat × Nat => (p.1, p.2.1)) <$> X)
      (Sign.sign_refines_packed sk cache message)
    have ho := congrArg (fun X =>
      (fun p : Option (Bytes 6404) × Nat × Nat => (p.1.map packOldAny, p.2.1)) <$> X)
      (Final.signRefinement sk cache message)
    simp only [Functor.map_map] at hs
    calc
      observed <$> ExpandMain.concrete.run .sign (sk, cache, message) =
          (fun p => (p.1.map packOldAny, p.2.1)) <$>
            Sign.countBoth (Ref.signRef sk cache message) := by
        change (fun r => (r.value, r.hashCalls)) <$>
          Sign.submission.run .sign (sk, cache, message) = _
        simpa only using hs
      _ = (fun r => (r.value.map packOldAny, r.hashCalls)) <$>
          SigGolfCandidate.submission.run .sign (sk, cache, message) := by
        calc
          (fun p => (p.1.map packOldAny, p.2.1)) <$>
              Sign.countBoth (Ref.signRef sk cache message) =
            (fun p : Option (Bytes 6404) × Nat × Nat =>
              (p.1.map packOldAny, p.2.1)) <$>
              ((fun r => (r.value, r.hashCalls, r.hashCompressions)) <$>
                SigGolfCandidate.submission.run .sign (sk, cache, message)) := ho.symm
          _ = _ := by rw [Functor.map_map]
  expand message pk signature := by
    change (observed <$> ExpandMain.concrete.run .expand (message, pk, signature)) =
      (observed <$> SigGolfCandidate.submission.run .expand
        (message, pk, unpackOld signature))
    rw [ExpandMain.expand_run, SigGolfCandidate.Expand.expand_run, expand_unpackOld]
    simp [observed]
  verify message pk witness := by
    exact congrArg (fun comp => observed <$> comp)
      (verify_run_eq message pk witness)

theorem packed_secure : ExpandMain.concrete.Secure := by
  have hOld : (oldSubmission baseLayout oldImages).Secure := by
    change SigGolfCandidate.submission.Secure
    exact Final.certificate.security
  have h := secureAny assumptionsAny hOld
  exact h

end SigGolfCandidate.Packed
