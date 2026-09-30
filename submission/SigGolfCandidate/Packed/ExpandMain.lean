import SigGolfCandidate.Packed.ExpandRun
import SigGolfCandidate.Packed.Submission

/-! Concrete refinement of the packed 6398-byte expansion phase. -/

namespace SigGolfCandidate.Packed.ExpandMain

open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv
  SigGolfCandidate.Rv SigGolfCandidate.Mem OracleComp

set_option maxRecDepth 100000

abbrev concrete : Submission :=
  SigGolfCandidate.Packed.submission Images.signImage Images.expandImage

def initState (m : Message) (pk : PublicKey) (σ : Bytes 6398) : MachineState :=
  let blank : MachineState := { regs := fun _ => 0, mem := fun _ => 0, pc := 0x1000 }
  ((((blank.writeBytesAsWords (BitVec.ofNat 64 (dataBase Images.expandImage))
      Images.expandImage.data).writeBytesAsWords
      (BitVec.ofNat 64 0x40) (bytes m)).writeBytesAsWords
      (BitVec.ofNat 64 0xA0) (bytes pk)).writeBytesAsWords
      (BitVec.ofNat 64 0x2650) (bytes σ)).setReg .x2
      (BitVec.ofNat 64 (dataBase Images.expandImage))

theorem initialState_eq (m : Message) (pk : PublicKey) (σ : Bytes 6398) :
    initialState concrete .expand (m, pk, σ) = some (initState m pk σ) := by
  unfold initialState
  rw [if_pos (by exact Images.expand_valid)]
  rfl

theorem initState_sig (m : Message) (pk : PublicKey) (σ : Bytes 6398)
    (j : Nat) (hj : j < 6398) :
    (initState m pk σ).getByte (BitVec.ofNat 64 (0x2650 + j)) =
      (bytes σ).getD j 0 := by
  unfold initState
  simp only [getByte_setReg]
  rw [getByte_writeBytesAsWords _ _ _ _ (by decide)
    (by simp [SigGolfCandidate.Legacy.bytes]) (by omega),
    if_pos (by simp [SigGolfCandidate.Legacy.bytes]; omega)]
  congr 1
  omega

theorem initState_readSig (m : Message) (pk : PublicKey) (σ : Bytes 6398) :
    readBuffer (initState m pk σ) 0x2650 6398 = σ := by
  apply readBuffer_eq_of_bytes
  intro i hi
  exact initState_sig m pk σ i hi

theorem expand_run (m : Message) (pk : PublicKey)
    (σ : Bytes 6398) :
    concrete.run .expand (m, pk, σ) =
      pure ⟨some (expandWitness σ), true, 9607, 0, 0⟩ := by
  rw [run_eq concrete .expand _ _ (initialState_eq m pk σ)]
  change toRunResult concrete .expand <$>
    execute CYCLE_LIMIT Images.expandImage (initState m pk σ) = _
  obtain ⟨u, hst, hf, h5, h10, hb⟩ :=
    ExpandRun.expand_steps (initState m pk σ)
      (initialState_pc _ _ _ _ (initialState_eq m pk σ))
  rw [hst.execute_le (by decide : 9606 ≤ CYCLE_LIMIT),
    show CYCLE_LIMIT - 9606 = (CYCLE_LIMIT - 9607) + 1 by decide,
    execute_halt _ hf h5, map_pure]
  have hr : readOutput concrete.sizes concrete.layout .expand u =
      expandWitness σ := by
    rw [initState_readSig m pk σ] at hb
    exact hb
  rw [h10, if_pos rfl, map_pure]
  unfold toRunResult
  simp only [Execution.charge_exit, Execution.charge_state, if_pos, hr]
  rfl

theorem expand_runWith (hash : Hash) (m : Message) (pk : PublicKey)
    (σ : Bytes 6398) :
    concrete.runWith hash .expand (m, pk, σ) =
      ⟨some (expandWitness σ), true, 9607, 0, 0⟩ := by
  unfold Submission.runWith
  rw [expand_run]
  rfl

end SigGolfCandidate.Packed.ExpandMain
