import SigGolfCandidate.Packed.SignClone.Sim
import SigGolfCandidate.Rv.Steps

/-! A terminal hook for a simulated segment whose successful HALT has been
replaced by an ordinary postprocessor. -/

namespace SigGolfCandidate.Packed.Sign

open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
  SigGolfCandidate.Rv OracleComp OracleSpec

set_option maxRecDepth 100000

theorem toRunResult_charge_value (submission : Submission) (phase : Phase)
    (e : Execution) (c h b : Nat) :
    (toRunResult submission phase (e.charge c h b)).value =
      (toRunResult submission phase e).value := by
  cases e
  rfl

theorem toRunResult_charge_hashCalls (submission : Submission) (phase : Phase)
    (e : Execution) (c h b : Nat) :
    (toRunResult submission phase (e.charge c h b)).hashCalls = h + e.hashCalls := rfl

theorem toRunResult_charge_hashCompressions (submission : Submission) (phase : Phase)
    (e : Execution) (c h b : Nat) :
    (toRunResult submission phase (e.charge c h b)).hashCompressions = b + e.hashCompressions := rfl

theorem Sim.run_eq_terminal (submission : Submission) (phase : Phase)
    (input : Input submission.sizes phase)
    {s : MachineState} (hinit : initialState submission phase input = some s)
    {α : Type} {W L : Nat} {oa : OracleComp HashSpec α}
    {Q : α → MachineState → Prop}
    (hsim : Sim (submission.image phase) s W oa Q)
    (hW : W + L < CYCLE_LIMIT)
    (F : α → Option (Output submission.sizes phase))
    (hQ : ∀ a t, Q a t → ∃ e : Execution,
      (∀ fuel, L ≤ fuel → Riscv.execute fuel (submission.image phase) t = Pure.pure e) ∧
      (toRunResult submission phase e).value = F a ∧
      e.hashCalls = 0 ∧ e.hashCompressions = 0) :
    (fun r => (r.value, r.hashCalls, r.hashCompressions)) <$>
        submission.run phase input =
      (fun p => (F p.1, p.2.1, p.2.2)) <$> countBoth oa := by
  obtain ⟨oc, hp, hf⟩ := hsim
  rw [Rv.run_eq submission phase input s hinit,
    hf CYCLE_LIMIT (by omega), ← hp, Functor.map_map]
  simp only [map_bind, Functor.map_map]
  rw [map_eq_bind_pure_comp (x := oc)]
  congr 1
  funext o
  obtain ⟨e, he, heval, hecalls, heblocks⟩ := hQ _ _ o.2.2.2
  have hle : L ≤ CYCLE_LIMIT - o.1.steps := by
    have := o.2.1
    have := o.2.2.1
    omega
  rw [he _ hle]
  simp only [map_pure, Function.comp]
  simp only [toRunResult_charge_value, toRunResult_charge_hashCalls,
    toRunResult_charge_hashCompressions, heval, hecalls, heblocks, Nat.add_zero]

theorem Sim.runWith_terminal (submission : Submission) (phase : Phase)
    (input : Input submission.sizes phase)
    {s : MachineState} (hinit : initialState submission phase input = some s)
    {α : Type} {W L : Nat} {oa : OracleComp HashSpec α}
    {Q : α → MachineState → Prop}
    (hsim : Sim (submission.image phase) s W oa Q)
    (hW : W + L < CYCLE_LIMIT)
    (hQ : ∀ a t, Q a t → ∃ e : Execution,
      (∀ fuel, L ≤ fuel → Riscv.execute fuel (submission.image phase) t = Pure.pure e) ∧
      e.exit ≠ .unfinished ∧ e.cycles ≤ L)
    (hash : Hash) :
    (submission.runWith hash phase input).finished = true ∧
      (submission.runWith hash phase input).cycles ≤ W + L := by
  obtain ⟨oc, _, hf⟩ := hsim
  rw [runWith_eq submission hash phase input s hinit,
    hf CYCLE_LIMIT (by omega), evalWithAnswerFn_bind, evalWithAnswerFn_map]
  generalize evalWithAnswerFn hash oc = o
  obtain ⟨e, he, hexit, hcycles⟩ := hQ _ _ o.2.2.2
  have hle : L ≤ CYCLE_LIMIT - o.1.steps := by
    have := o.2.1
    have := o.2.2.1
    omega
  rw [he _ hle]
  simp only [evalWithAnswerFn_pure, toRunResult, Execution.charge]
  constructor
  · simp [hexit]
  · have := o.2.2.1
    omega

end SigGolfCandidate.Packed.Sign
