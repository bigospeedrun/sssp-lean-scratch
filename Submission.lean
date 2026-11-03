import Submission.SsspStatement

/-! Maintainer control run (not a submission): the proof is `sorry`, so the verifier must refuse it. -/

theorem Race.bound : BigOSpeedrun.DirectedSSSP.Bound ((1 : ℚ) / 1) ((3 : ℚ) / 4) ((1 : ℚ) / 1) ((11 : ℚ) / 12) ((0 : ℚ) / 1) := by
  sorry
