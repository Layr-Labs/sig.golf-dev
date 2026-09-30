import SigGolfCandidate.Verify.LayRuns

/-! Kernel checks of the layer section's code blocks (all layers, chains, fold levels). -/

namespace SigGolfCandidate.Verify

theorem proCheck_ok : proCheck = true := by decide +kernel
theorem stepCheck_ok : stepCheck = true := by decide +kernel
theorem cmpCheck_ok : cmpCheck = true := by decide +kernel
theorem layCheck_0 : layCheck 0 = true := by decide +kernel
theorem layCheck_1 : layCheck 1 = true := by decide +kernel
theorem layCheck_2 : layCheck 2 = true := by decide +kernel
theorem layCheck_3 : layCheck 3 = true := by decide +kernel
theorem layCheck_4 : layCheck 4 = true := by decide +kernel
theorem layCheck_5 : layCheck 5 = true := by decide +kernel
theorem chainCheckY_lo : (List.range 16).all chainCheckY = true := by decide +kernel
theorem chainCheckY_hi : (List.range' 16 16).all chainCheckY = true := by decide +kernel

theorem layCheck_at (lay : Nat) (h : lay < 6) : layCheck lay = true := by
  interval_cases lay
  exacts [layCheck_0, layCheck_1, layCheck_2, layCheck_3, layCheck_4, layCheck_5]

theorem chainCheckY_at (i : Nat) (h : i < 32) : chainCheckY i = true := by
  by_cases h16 : i < 16
  · exact List.all_eq_true.mp chainCheckY_lo i (List.mem_range.mpr h16)
  · exact List.all_eq_true.mp chainCheckY_hi i (List.mem_range'_1.mpr ⟨by omega, by omega⟩)

end SigGolfCandidate.Verify
