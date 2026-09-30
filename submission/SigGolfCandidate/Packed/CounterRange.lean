import SigGolfCandidate.Budget.Loops

/-!
# Counter search range

The signing search starts at zero and tries at most `2^22` counters.  This
structural bound holds for every oracle answer and every cache, including a
cache supplied by an adversary to the signing oracle.
-/

namespace SigGolfCandidate.Packed

open SigGolfCandidate.Legacy SigGolfCandidate.Ref SigGolfCandidate.Budget OracleComp OracleSpec

/-- An optional search result lies in the interval of counters the search tried. -/
def SearchRange (start fuel : Nat) (out : Option (Nat × List Nat)) : Prop :=
  ∀ counter digits, out = some (counter, digits) →
    start ≤ counter ∧ counter < start + fuel

/-- Every possible result of `searchCounter` lies in its trial interval. -/
theorem spec_searchCounter_range (lay tau leaf : Nat) (message : Val)
    (hmessage : message.length ≤ 16) (hlay : lay < 256) :
    ∀ fuel start, Spec (PC lay) (SearchRange start fuel) fuel
      (searchCounter lay tau leaf message start fuel) := by
  intro fuel
  induction fuel with
  | zero =>
      intro start
      exact Spec.pure _ _ (by simp [SearchRange])
  | succ fuel ih =>
      intro start
      unfold searchCounter
      obtain ⟨hquery, hcost⟩ := enc_ok lay tau leaf message hmessage start hlay
      refine spec_hash16_bind _ hquery hcost (l := fuel) (fun digest _ => ?_) (by omega)
      cases hdecode : decodeDigits digest with
      | some digits =>
          exact Spec.pure _ _ (by
            intro counter digits' h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            omega)
      | none =>
          exact (ih (start + 1)).mono (fun _ h => h) (fun out hout => by
            intro counter digits h
            obtain ⟨hlo, hhi⟩ := hout counter digits h
            omega)

/-- The signer always calls its layer search from zero, with `cMax` trials. -/
theorem spec_searchCounter_sign (lay tau leaf : Nat) (message : Val)
    (hmessage : message.length ≤ 16) (hlay : lay < 256) :
    Spec (PC lay) (fun out : Option (Nat × List Nat) =>
      ∀ counter digits, out = some (counter, digits) → counter < cMax)
      cMax (searchCounter lay tau leaf message 0 cMax) := by
  refine (spec_searchCounter_range lay tau leaf message hmessage hlay cMax 0).mono
    (fun _ h => h) (fun out hout => ?_)
  intro counter digits h
  exact (hout counter digits h).2

end SigGolfCandidate.Packed
