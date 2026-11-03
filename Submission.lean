import Submission.SsspStatement
import Submission.Bridge

/-!
Maintainer smoke (not a public submission): the C-HD result of the fork
(`Frontier.CHD.Final.chd_exact_within`, Vals AI) with our bridge proves the row
"with at most n·⌊⌊log₂ n⌋^{3/4}⌋ edges, the time is O(n·(log n)^{11/12})".
-/

theorem Race.bound : BigOSpeedrun.DirectedSSSP.Bound ((1 : ℚ) / 1) ((3 : ℚ) / 4) ((1 : ℚ) / 1) ((11 : ℚ) / 12) ((0 : ℚ) / 1) := by
  simp only [div_one]
  exact BigOSpeedrun.DirectedSSSP.Bridge.chd_bound
