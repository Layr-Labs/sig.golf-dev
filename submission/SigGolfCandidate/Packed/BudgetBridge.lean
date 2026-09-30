import SigGolfCandidate.Packed.SignClone.Run
import SigGolfCandidate.Packed.ExpandMain
import SigGolfCandidate.Budget.Bridge
import SigGolfCandidate.Final.Discharge

namespace SigGolfCandidate.Packed
open SigGolfCandidate.Legacy OracleComp
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option allowUnsafeReducibility true in
attribute [local reducible] SigGolfCandidate.Legacy.Input SigGolfCandidate.Legacy.Output

private abbrev concrete := ExpandMain.concrete

theorem budget_packed (hK : Final.KeygenRefinementStatement) :
    concrete.CompressionBounds := by
  apply Budget.compressionBounds_of_refinement concrete
  · apply Budget.keygenRefines_of_counts concrete
    intro sk
    refine ⟨some, ?_⟩
    change (fun r => (r.value, r.hashCalls, r.hashCompressions)) <$>
      SigGolfCandidate.submission.run .keygen sk = _
    exact hK sk
  · apply Budget.signRefines_of_counts concrete rfl
    intro sk cache m
    refine ⟨Option.map packOldAny, ?_⟩
    change (fun r => (r.value, r.hashCalls, r.hashCompressions)) <$>
      Sign.submission.run .sign (sk, cache, m) = _
    exact Sign.sign_refines_packed sk cache m
  · apply Budget.expandNoHash_of_counts concrete
    rintro ⟨m, pk, σ⟩
    change Bytes 6398 at σ
    refine ⟨Unit, (), fun _ => some (expandWitness σ), ?_⟩
    rw [ExpandMain.expand_run]
    rfl

#print axioms budget_packed
end SigGolfCandidate.Packed
