import SigGolfCandidate.Packed.SignClone.Main
import SigGolfCandidate.Packed.SignClone.Terminal
import SigGolfCandidate.Packed.SignRun

/-! The symbolic signer prefix followed by the packed success postprocessor. -/

namespace SigGolfCandidate.Packed.Sign

open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
  SigGolfCandidate.Rv SigGolfCandidate.Ref SigGolfCandidate.Mem OracleComp

set_option maxRecDepth 100000

private theorem terminal (a : Option (Bytes 6404)) (t : MachineState)
    (h : SignPost a t) :
    ∃ e : Execution,
      (∀ fuel, 19271 ≤ fuel → Riscv.execute fuel image t = Pure.pure e) ∧
      (toRunResult submission .sign e).value = a.map packOldAny ∧
      e.hashCalls = 0 ∧ e.hashCompressions = 0 ∧
      e.exit ≠ .unfinished ∧ e.cycles ≤ 19271 := by
  obtain ⟨_, h5, ha, hsuccess, hfailure⟩ := h
  by_cases h10 : t.getReg .x10 = 0
  · have hpc := hsuccess h10
    obtain ⟨u, hs, hf, hu5, hu10, huout⟩ :=
      SigGolfCandidate.Packed.SignRun.sign_suffix_output t (by simpa [pcOf] using hpc)
    refine ⟨⟨.success, u, 19271, 0, 0⟩, ?_, ?_, rfl, rfl, by simp, by simp⟩
    · intro fuel hL
      rw [hs.execute_le (by omega)]
      obtain ⟨n, hn⟩ : ∃ n, fuel - 19270 = n + 1 := ⟨fuel - 19271, by omega⟩
      rw [hn, execute_halt n hf hu5]
      simp [hu10, Execution.charge]
    · have ha' : a = some (readBuffer t 0x2650 6404) := by simpa only [if_pos h10] using ha
      have hr : readOutput submission.sizes submission.layout .sign u =
          packOldAny (readBuffer t 0x2650 6404) := huout
      simp [toRunResult, ha', hr]
      rfl
  · have hf := hfailure h10
    refine ⟨⟨.failure, t, 1, 0, 0⟩, ?_, ?_, rfl, rfl, by simp, by simp⟩
    · intro fuel hL
      obtain ⟨n, hn⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by omega⟩
      rw [hn, execute_halt n hf h5]
      simpa only [if_neg h10]
    · have ha' : a = none := by simpa only [if_neg h10] using ha
      simp [toRunResult, ha']
      rfl

theorem signW_post_lt : signW + 19271 < CYCLE_LIMIT := by
  unfold signW restW forsTreeW layCyc topCyc treeCyc tleafCyc CYCLE_LIMIT
  norm_num

theorem sign_refines_packed (sk : SecretKey) (cache : Cache) (m : Message) :
    (fun r => (r.value, r.hashCalls, r.hashCompressions)) <$>
        submission.run .sign (sk, cache, m) =
      (fun p => (p.1.map packOldAny, p.2.1, p.2.2)) <$>
        countBoth (signRef sk cache m) := by
  exact Sim.run_eq_terminal submission .sign (sk, cache, m)
    (initialState_eq sk cache m) (signRef_sim sk cache m) signW_post_lt
    (fun a => a.map packOldAny) (fun a t h => by
      obtain ⟨e, he, hv, hc, hb, _, _⟩ := terminal a t h
      exact ⟨e, he, hv, hc, hb⟩)

theorem sign_terminates_packed (hash : Hash) (sk : SecretKey)
    (cache : Cache) (m : Message) :
    (submission.runWith hash .sign (sk, cache, m)).finished = true ∧
      (submission.runWith hash .sign (sk, cache, m)).cycles ≤ signW + 19271 := by
  exact Sim.runWith_terminal submission .sign (sk, cache, m)
    (initialState_eq sk cache m) (signRef_sim sk cache m) signW_post_lt
    (fun a t h => by
      obtain ⟨e, he, _, _, _, hx, hc⟩ := terminal a t h
      exact ⟨e, he, hx, hc⟩) hash

end SigGolfCandidate.Packed.Sign
