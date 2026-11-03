import Submission.Validation
import Frontier.CHD.Final

/-!
The bridge for the smoke submission: the C-HD result of the fork
(`Frontier.CHD.Final.chd_exact_within`) proves the race row
"with at most n·⌊⌊log₂ n⌋^{3/4}⌋ edges, the time is O(n·(log n)^{11/12})",
that is `Bound 1 (3/4) 1 (11/12) 0`.
-/

namespace BigOSpeedrun.DirectedSSSP.Bridge

open Frontier Frontier.RAM BigOSpeedrun.DirectedSSSP.Validation

lemma correctWithin_of_exact {P : Program} {G : Graph} {s : Fin G.n} {T : ℝ}
    (hE : P.Exact) (hR : P.RunsWithin G s T) : CorrectWithin P G s T := by
  obtain ⟨f, r, hr, hs⟩ := hE G s
  exact ⟨f, r, hr, hs, Program.runsWithin_unique hR hr⟩

lemma correctWithin_mono_const {P : Program} {G : Graph} {s : Fin G.n} {K T : ℝ}
    (h : CorrectWithin P G s (K * T)) (hT : 0 ≤ T) : CorrectWithin P G s ((|K| + 1) * T) :=
  CorrectWithin.mono h (mul_le_mul_of_nonneg_right (by linarith [le_abs_self K]) hT)

/-! ### The cap and the dispatch threshold -/

lemma sparse_iff {n m : ℕ} :
    Sparse 1 (3 / 4) n m ↔ (m : ℝ) ≤ n * ⌊((Nat.log 2 n : ℕ) : ℝ) ^ ((3 : ℝ) / 4)⌋₊ := by
  unfold Sparse Cap
  norm_num

/-- A sparse graph takes the C-HD branch of the program's dispatch. -/
lemma sparse_le_F {n m : ℕ} (h : Sparse 1 (3 / 4) n m) : m ≤ n * GateCCalc.F n := by
  have hk : ⌊((Nat.log 2 n : ℕ) : ℝ) ^ ((3 : ℝ) / 4)⌋₊ ≤ GateCCalc.F n := by
    unfold GateCCalc.F
    exact GateCCalc.le_sqrt_sqrt_of_real (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  have h' : m ≤ n * ⌊((Nat.log 2 n : ℕ) : ℝ) ^ ((3 : ℝ) / 4)⌋₊ := by
    exact_mod_cast sparse_iff.1 h
  exact h'.trans (Nat.mul_le_mul_left n hk)

lemma F_le_natLog (n : ℕ) : GateCCalc.F n ≤ Nat.log 2 n := by
  unfold GateCCalc.F
  set L := Nat.log 2 n
  have h34 : L ^ 3 ≤ (L ^ 2) ^ 2 := by
    rcases Nat.eq_zero_or_pos L with h | h
    · simp [h]
    · rw [← pow_mul]
      exact Nat.pow_le_pow_right h (by norm_num)
  calc Nat.sqrt (Nat.sqrt (L ^ 3)) ≤ Nat.sqrt (Nat.sqrt ((L ^ 2) ^ 2)) :=
        Nat.sqrt_le_sqrt (Nat.sqrt_le_sqrt h34)
    _ = L := by rw [Nat.sqrt_eq', Nat.sqrt_eq']

/-! ### `Tchd` on the cap -/

lemma key_eq {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    (A * B ^ ((3 : ℝ) / 4)) ^ ((1 : ℝ) / 3) * (A * B) ^ ((2 : ℝ) / 3) =
      A * B ^ ((11 : ℝ) / 12) := by
  rw [Real.mul_rpow hA.le (Real.rpow_nonneg hB.le _), Real.mul_rpow hA.le hB.le,
    ← Real.rpow_mul hB.le]
  have e1 : A ^ ((1 : ℝ) / 3) * A ^ ((2 : ℝ) / 3) = A := by
    rw [← Real.rpow_add hA]
    norm_num
  have e2 : B ^ ((3 : ℝ) / 4 * (1 / 3)) * B ^ ((2 : ℝ) / 3) = B ^ ((11 : ℝ) / 12) := by
    rw [← Real.rpow_add hB]
    norm_num
  calc _ = (A ^ ((1 : ℝ) / 3) * A ^ ((2 : ℝ) / 3)) *
        (B ^ ((3 : ℝ) / 4 * (1 / 3)) * B ^ ((2 : ℝ) / 3)) := by ring
    _ = _ := by rw [e1, e2]

/-- On the cap, `Tchd n m ≤ 21 · n · (log n)^{11/12}` for `n ≥ 16`. -/
lemma tchd_le {n m : ℕ} (hn : 16 ≤ n) (hm : (m : ℝ) ≤ 2 * n * Real.log n ^ ((3 : ℝ) / 4)) :
    GateCCalc.Tchd n m ≤ 21 * ((n : ℝ) * Real.log n ^ ((11 : ℝ) / 12)) := by
  have hx16 : (16 : ℝ) ≤ n := by exact_mod_cast hn
  have hx : (0 : ℝ) < n := by linarith
  set ℓ := Real.log n with hℓ
  have hℓ1 : 1 ≤ ℓ := one_le_log hn
  have hℓ0 : 0 < ℓ := by linarith
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have h1112 : 1 ≤ ℓ ^ ((11 : ℝ) / 12) := Real.one_le_rpow hℓ1 (by norm_num)
  have h34 : ℓ ^ ((3 : ℝ) / 4) ≤ ℓ ^ ((11 : ℝ) / 12) :=
    Real.rpow_le_rpow_of_exponent_le hℓ1 (by norm_num)
  have h34le : ℓ ^ ((3 : ℝ) / 4) ≤ ℓ := by
    simpa using Real.rpow_le_rpow_of_exponent_le hℓ1 (show (3 : ℝ) / 4 ≤ 1 by norm_num)
  have h16 : 1 ≤ ℓ ^ ((1 : ℝ) / 6) := Real.one_le_rpow hℓ1 (by norm_num)
  -- First two terms.
  have t1 : (n : ℝ) ≤ n * ℓ ^ ((11 : ℝ) / 12) := le_mul_of_one_le_right hx.le h1112
  have t2 : (m : ℝ) ≤ 2 * (n * ℓ ^ ((11 : ℝ) / 12)) := by
    calc (m : ℝ) ≤ 2 * n * ℓ ^ ((3 : ℝ) / 4) := hm
      _ ≤ 2 * n * ℓ ^ ((11 : ℝ) / 12) := mul_le_mul_of_nonneg_left h34 (by positivity)
      _ = _ := by ring
  -- Third term: `log (m/(n+1) + 2) ≤ 8 ℓ^{1/6}`.
  have hq : (m : ℝ) / (n + 1) ≤ 2 * ℓ := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left h34le hx.le]
  have harg0 : 0 < (m : ℝ) / (n + 1) + 2 := by positivity
  have hlog : Real.log ((m : ℝ) / (n + 1) + 2) ≤ 8 * ℓ ^ ((1 : ℝ) / 6) := by
    have hle : (m : ℝ) / (n + 1) + 2 ≤ 4 * ℓ := by linarith
    have h4 : Real.log 4 < 2 := by
      have : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        norm_num
      have := Real.log_two_lt_d9
      linarith
    have hll : Real.log ℓ ≤ ℓ ^ ((1 : ℝ) / 6) / (1 / 6) :=
      Real.log_le_rpow_div hℓ0.le (by norm_num)
    calc Real.log ((m : ℝ) / (n + 1) + 2) ≤ Real.log (4 * ℓ) := Real.log_le_log harg0 hle
      _ = Real.log 4 + Real.log ℓ := Real.log_mul (by norm_num) hℓ0.ne'
      _ ≤ 2 + 6 * ℓ ^ ((1 : ℝ) / 6) := by
          have : ℓ ^ ((1 : ℝ) / 6) / (1 / 6) = 6 * ℓ ^ ((1 : ℝ) / 6) := by ring
          linarith
      _ ≤ 8 * ℓ ^ ((1 : ℝ) / 6) := by linarith
  have t3 : (m : ℝ) * Real.log ((m : ℝ) / (n + 1) + 2) ≤ 16 * (n * ℓ ^ ((11 : ℝ) / 12)) := by
    have hlog0 : 0 ≤ Real.log ((m : ℝ) / (n + 1) + 2) := Real.log_nonneg (by
      have : 0 ≤ (m : ℝ) / (n + 1) := by positivity
      linarith)
    have e : ℓ ^ ((3 : ℝ) / 4) * ℓ ^ ((1 : ℝ) / 6) = ℓ ^ ((11 : ℝ) / 12) := by
      rw [← Real.rpow_add hℓ0]
      norm_num
    calc (m : ℝ) * Real.log ((m : ℝ) / (n + 1) + 2)
        ≤ (2 * n * ℓ ^ ((3 : ℝ) / 4)) * (8 * ℓ ^ ((1 : ℝ) / 6)) :=
          mul_le_mul hm hlog hlog0 (mul_nonneg (by positivity) (Real.rpow_nonneg hℓ0.le _))
      _ = 16 * (n * (ℓ ^ ((3 : ℝ) / 4) * ℓ ^ ((1 : ℝ) / 6))) := by ring
      _ = _ := by rw [e]
  -- Fourth term: `m^{1/3} (n log(n+2))^{2/3} ≤ 2 n ℓ^{11/12}`.
  have hlog2 : Real.log ((n : ℝ) + 2) ≤ 2 * ℓ := by
    have : (n : ℝ) + 2 ≤ (n : ℝ) ^ 2 := by nlinarith
    calc Real.log ((n : ℝ) + 2) ≤ Real.log ((n : ℝ) ^ 2) := Real.log_le_log (by positivity) this
      _ = 2 * ℓ := by rw [Real.log_pow, ← hℓ]; norm_num
  have t4 : (m : ℝ) ^ ((1 : ℝ) / 3) * ((n : ℝ) * Real.log ((n : ℝ) + 2)) ^ ((2 : ℝ) / 3) ≤
      2 * (n * ℓ ^ ((11 : ℝ) / 12)) := by
    have hA : (0 : ℝ) < 2 * n := by positivity
    have hlogn2 : 0 ≤ Real.log ((n : ℝ) + 2) := Real.log_nonneg (by linarith)
    calc (m : ℝ) ^ ((1 : ℝ) / 3) * ((n : ℝ) * Real.log ((n : ℝ) + 2)) ^ ((2 : ℝ) / 3)
        ≤ (2 * n * ℓ ^ ((3 : ℝ) / 4)) ^ ((1 : ℝ) / 3) * (2 * n * ℓ) ^ ((2 : ℝ) / 3) := by
          apply mul_le_mul
          · exact Real.rpow_le_rpow hm0 hm (by norm_num)
          · refine Real.rpow_le_rpow (mul_nonneg hx.le hlogn2) ?_ (by norm_num)
            nlinarith [mul_le_mul_of_nonneg_left hlog2 hx.le]
          · exact Real.rpow_nonneg (mul_nonneg hx.le hlogn2) _
          · exact Real.rpow_nonneg (mul_nonneg hA.le (Real.rpow_nonneg hℓ0.le _)) _
      _ = 2 * n * ℓ ^ ((11 : ℝ) / 12) := key_eq hA hℓ0
      _ = _ := by ring
  unfold GateCCalc.Tchd
  linarith

/-- The cap gives `m ≤ 2 n (log n)^{3/4}`. -/
lemma sparse_le_real {n m : ℕ} (hn : 16 ≤ n) (h : Sparse 1 (3 / 4) n m) :
    (m : ℝ) ≤ 2 * n * Real.log n ^ ((3 : ℝ) / 4) := by
  have hx : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hK := natLog_le_two_log (n := n) (by omega)
  have hK0 : (0 : ℝ) ≤ ((Nat.log 2 n : ℕ) : ℝ) := Nat.cast_nonneg _
  have hL : 0 ≤ Real.log n := by linarith [one_le_log hn]
  have h2 : (2 : ℝ) ^ ((3 : ℝ) / 4) ≤ 2 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num)
      (show (3 : ℝ) / 4 ≤ 1 by norm_num)
  calc (m : ℝ) ≤ n * ⌊((Nat.log 2 n : ℕ) : ℝ) ^ ((3 : ℝ) / 4)⌋₊ := sparse_iff.1 h
    _ ≤ n * ((Nat.log 2 n : ℕ) : ℝ) ^ ((3 : ℝ) / 4) :=
        mul_le_mul_of_nonneg_left (Nat.floor_le (Real.rpow_nonneg hK0 _)) hx
    _ ≤ n * (2 * Real.log n) ^ ((3 : ℝ) / 4) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hK0 hK (by norm_num)) hx
    _ = n * ((2 : ℝ) ^ ((3 : ℝ) / 4) * Real.log n ^ ((3 : ℝ) / 4)) := by
        rw [Real.mul_rpow (by norm_num) hL]
    _ ≤ n * (2 * Real.log n ^ ((3 : ℝ) / 4)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hL _)) hx
    _ = _ := by ring

/-! ### `Tdisp` on every graph -/

lemma tchd_nonneg (n m : ℕ) : 0 ≤ GateCCalc.Tchd n m := by
  unfold GateCCalc.Tchd
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h1 : 0 ≤ Real.log ((m : ℝ) / ((n : ℝ) + 1) + 2) := Real.log_nonneg (by
    have : 0 ≤ (m : ℝ) / ((n : ℝ) + 1) := by positivity
    linarith)
  have h2 : 0 ≤ Real.log ((n : ℝ) + 2) := Real.log_nonneg (by linarith)
  have h3 := mul_nonneg hm h1
  have h4 := mul_nonneg (Real.rpow_nonneg hm ((1 : ℝ) / 3))
    (Real.rpow_nonneg (mul_nonneg hn h2) ((2 : ℝ) / 3))
  linarith

lemma tdisp_nonneg (n m : ℕ) : 0 ≤ GateCTarget.Tdisp GateCCalc.F n m := by
  unfold GateCTarget.Tdisp
  split_ifs
  · exact tchd_nonneg n m
  · positivity

/-- `Tdisp ≤ 8 (n+1)(m+1)` on every graph with `n ≥ 1`. -/
lemma tdisp_le_poly {n m : ℕ} (hn : 1 ≤ n) :
    GateCTarget.Tdisp GateCCalc.F n m ≤ 8 * (((n : ℝ) + 1) * ((m : ℝ) + 1)) := by
  have hx1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hP : 0 ≤ ((n : ℝ) + 1) * ((m : ℝ) + 1) := by positivity
  unfold GateCTarget.Tdisp
  split_ifs with hd
  swap
  · linarith
  -- `F n ≤ 2 n`.
  have hF : (GateCCalc.F n : ℝ) ≤ 2 * n := by
    have h1 : (GateCCalc.F n : ℝ) ≤ ((Nat.log 2 n : ℕ) : ℝ) := by exact_mod_cast F_le_natLog n
    have h2 := natLog_le_two_log (n := n) (by omega)
    have h3 := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < n)
    linarith
  have hmF : (m : ℝ) ≤ n * GateCCalc.F n := by exact_mod_cast hd
  have hq : (m : ℝ) / ((n : ℝ) + 1) ≤ 2 * n := by
    rw [div_le_iff₀ (by positivity)]
    have : (0 : ℝ) ≤ GateCCalc.F n := Nat.cast_nonneg _
    nlinarith
  -- Third term.
  have t3 : (m : ℝ) * Real.log ((m : ℝ) / ((n : ℝ) + 1) + 2) ≤
      2 * (((n : ℝ) + 1) * ((m : ℝ) + 1)) := by
    have hl := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < (m : ℝ) / ((n : ℝ) + 1) + 2)
    calc (m : ℝ) * Real.log ((m : ℝ) / ((n : ℝ) + 1) + 2) ≤ m * (2 * n + 1) :=
          mul_le_mul_of_nonneg_left (by linarith) hm0
      _ ≤ _ := by nlinarith
  -- Fourth term.
  have t4 : (m : ℝ) ^ ((1 : ℝ) / 3) * ((n : ℝ) * Real.log ((n : ℝ) + 2)) ^ ((2 : ℝ) / 3) ≤
      4 * (((n : ℝ) + 1) * ((m : ℝ) + 1)) := by
    have hy0 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    have hlog0 : 0 ≤ Real.log ((n : ℝ) + 2) := Real.log_nonneg (by linarith)
    -- `n log(n+2) ≤ 2 (n+2)^{3/2}`.
    have hY : (n : ℝ) * Real.log ((n : ℝ) + 2) ≤ 2 * ((n : ℝ) + 2) ^ ((3 : ℝ) / 2) := by
      have hl : Real.log ((n : ℝ) + 2) ≤ ((n : ℝ) + 2) ^ ((1 : ℝ) / 2) / (1 / 2) :=
        Real.log_le_rpow_div hy0.le (by norm_num)
      have e : ((n : ℝ) + 2) ^ ((3 : ℝ) / 2) = ((n : ℝ) + 2) * ((n : ℝ) + 2) ^ ((1 : ℝ) / 2) := by
        rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hy0, Real.rpow_one]
      have hs : 0 ≤ ((n : ℝ) + 2) ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hy0.le _
      have h2x : ((n : ℝ) + 2) ^ ((1 : ℝ) / 2) / (1 / 2) = 2 * ((n : ℝ) + 2) ^ ((1 : ℝ) / 2) := by
        ring
      rw [e]
      calc (n : ℝ) * Real.log ((n : ℝ) + 2) ≤ ((n : ℝ) + 2) * (2 * ((n : ℝ) + 2) ^ ((1 : ℝ) / 2)) := by
            apply mul_le_mul (by linarith) (by linarith) hlog0 (by linarith)
        _ = _ := by ring
    have hYp : ((n : ℝ) * Real.log ((n : ℝ) + 2)) ^ ((2 : ℝ) / 3) ≤ 4 * ((n : ℝ) + 1) := by
      calc ((n : ℝ) * Real.log ((n : ℝ) + 2)) ^ ((2 : ℝ) / 3)
          ≤ (2 * ((n : ℝ) + 2) ^ ((3 : ℝ) / 2)) ^ ((2 : ℝ) / 3) :=
            Real.rpow_le_rpow (mul_nonneg (by positivity) hlog0) hY (by norm_num)
        _ = (2 : ℝ) ^ ((2 : ℝ) / 3) * ((n : ℝ) + 2) := by
            rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hy0.le _), ← Real.rpow_mul hy0.le]
            norm_num
        _ ≤ 2 * ((n : ℝ) + 2) := by
            apply mul_le_mul_of_nonneg_right _ hy0.le
            simpa using Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num)
              (show (2 : ℝ) / 3 ≤ 1 by norm_num)
        _ ≤ 4 * ((n : ℝ) + 1) := by linarith
    have hm13 : (m : ℝ) ^ ((1 : ℝ) / 3) ≤ m := by
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · subst h0
        simp
      · have : (1 : ℝ) ≤ m := by exact_mod_cast h0
        simpa using Real.rpow_le_rpow_of_exponent_le this (show (1 : ℝ) / 3 ≤ 1 by norm_num)
    calc (m : ℝ) ^ ((1 : ℝ) / 3) * ((n : ℝ) * Real.log ((n : ℝ) + 2)) ^ ((2 : ℝ) / 3)
        ≤ m * (4 * ((n : ℝ) + 1)) :=
          mul_le_mul hm13 hYp (Real.rpow_nonneg (mul_nonneg (by positivity) hlog0) _) hm0
      _ ≤ _ := by nlinarith
  have hnm : (n : ℝ) + m ≤ ((n : ℝ) + 1) * ((m : ℝ) + 1) := by nlinarith
  unfold GateCCalc.Tchd
  linarith

/-! ### The row -/

/-- An exact program within `K · Tdisp F n m` on every graph proves the C-HD row. -/
theorem bound_of_tdisp {P : Program} (hE : P.Exact) {K : ℝ}
    (hR : ∀ (G : Graph) (s : Fin G.n),
      P.RunsWithin G s (K * GateCTarget.Tdisp GateCCalc.F G.n G.m)) :
    Bound 1 (3 / 4) 1 (11 / 12) 0 := by
  refine ⟨P, hE, (|K| + 1) * 21, by positivity, 16, le_rfl, ?_, ?_⟩
  · intro G s hn hsp
    have hd : GateCTarget.Tdisp GateCCalc.F G.n G.m = GateCCalc.Tchd G.n G.m := by
      unfold GateCTarget.Tdisp
      exact ite_cond_eq_true _ _ (eq_true (sparse_le_F hsp))
    have h := correctWithin_mono_const (correctWithin_of_exact hE (hR G s)) (tdisp_nonneg _ _)
    refine CorrectWithin.mono h ?_
    rw [hd]
    have ht := tchd_le hn (sparse_le_real hn hsp)
    have hT : Time 1 (11 / 12) 0 G.n = (G.n : ℝ) * Real.log G.n ^ ((11 : ℝ) / 12) := by
      unfold Time
      norm_num
    rw [hT, mul_assoc]
    exact mul_le_mul_of_nonneg_left ht (by positivity)
  · intro G s
    have hn : 1 ≤ G.n := s.pos
    have h := correctWithin_mono_const (correctWithin_of_exact hE (hR G s)) (tdisp_nonneg _ _)
    refine CorrectWithin.mono h ?_
    have ht := tdisp_le_poly (m := G.m) hn
    have hP : 0 ≤ ((G.n : ℝ) + 1) * ((G.m : ℝ) + 1) := by positivity
    calc (|K| + 1) * GateCTarget.Tdisp GateCCalc.F G.n G.m
        ≤ (|K| + 1) * (8 * (((G.n : ℝ) + 1) * ((G.m : ℝ) + 1))) :=
          mul_le_mul_of_nonneg_left ht (by positivity)
      _ ≤ (|K| + 1) * 21 * ((G.n : ℝ) + 1) * ((G.m : ℝ) + 1) := by
          have : 0 ≤ |K| + 1 := by positivity
          nlinarith

/-- **The smoke row.** -/
theorem chd_bound : Bound 1 (3 / 4) 1 (11 / 12) 0 :=
  bound_of_tdisp Frontier.CHD.Final.chd_exact_within.1 Frontier.CHD.Final.chd_exact_within.2

end BigOSpeedrun.DirectedSSSP.Bridge
