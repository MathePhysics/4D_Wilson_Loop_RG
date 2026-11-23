import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The logarithm series in a Banach algebra

For a Banach algebra `𝔸` over `𝕂 = ℝ` or `ℂ`, the series

  `log (1 + u) = ∑_{n ≥ 1} (-1)^(n+1) uⁿ / n`

as a `FormalMultilinearSeries` (`logSeries 𝕂 𝔸 = ofScalars 𝔸 (logCoeff 𝕂)`) and its sum
`log1p 𝕂 u`.  The coefficients have norm at most `1 / n`, so the radius of convergence is at
least `1` and `log1p 𝕂` is analytic on the unit ball.

## Main results

* `norm_logSeries_succ_le`, `one_le_radius_logSeries`: `‖logSeries 𝕂 𝔸 (n + 1)‖ ≤ 1 / (n + 1)`,
  radius `≥ 1`.
* `hasFPowerSeriesOnBall_log1p`, `analyticOnNhd_log1p`: `log1p 𝕂` is the sum of `logSeries` on
  the unit ball, hence analytic there.
* `hasSum_log1p`: `∑ (-1)^(n+1) uⁿ / n = log1p 𝕂 u` for `‖u‖ < 1`.
* `Commute.log1p_right`: whatever commutes with `u` commutes with `log1p 𝕂 u`.
* `norm_log1p_le`, `norm_log1p_le_div`: `‖log1p 𝕂 u‖ ≤ -log (1 - ‖u‖) ≤ ‖u‖ / (1 - ‖u‖)`.

The identity `exp (log1p 𝕂 u) = 1 + u` is proved in `BakerCampbellHausdorff.ExpLog`.
-/

noncomputable section

open FormalMultilinearSeries
open scoped ENNReal NNReal

namespace BakerCampbellHausdorff

section Coeff

variable (𝕂 : Type*) [RCLike 𝕂]

/-- The coefficients of `log (1 + z) = ∑_{n ≥ 1} (-1)^(n+1) zⁿ / n`: `logCoeff 𝕂 0 = 0` (the
constant term, `log 1 = 0`) and `logCoeff 𝕂 (n + 1) = (-1)ⁿ / (n + 1)`.  The only inverse taken
is that of `n + 1 ≠ 0`. -/
def logCoeff : ℕ → 𝕂
  | 0 => 0
  | n + 1 => (-1) ^ n * ((n : 𝕂) + 1)⁻¹

@[simp]
theorem logCoeff_zero : logCoeff 𝕂 0 = 0 := rfl

theorem logCoeff_succ (n : ℕ) : logCoeff 𝕂 (n + 1) = (-1) ^ n * ((n : 𝕂) + 1)⁻¹ := rfl

@[simp]
theorem logCoeff_one : logCoeff 𝕂 1 = 1 := by simp [logCoeff_succ]

theorem logCoeff_two : logCoeff 𝕂 2 = -2⁻¹ := by
  rw [logCoeff_succ]
  norm_num

theorem natCast_add_one_ne_zero (n : ℕ) : (n : 𝕂) + 1 ≠ 0 := by
  exact_mod_cast Nat.succ_ne_zero n

theorem norm_logCoeff_succ (n : ℕ) : ‖logCoeff 𝕂 (n + 1)‖ = ((n : ℝ) + 1)⁻¹ := by
  rw [logCoeff_succ, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_inv]
  congr 1
  exact_mod_cast RCLike.norm_natCast (K := 𝕂) (n + 1)

theorem norm_logCoeff_le_one (n : ℕ) : ‖logCoeff 𝕂 n‖ ≤ 1 := by
  rcases n with _ | n
  · simp
  · rw [norm_logCoeff_succ]
    exact inv_le_one_of_one_le₀ (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])

theorem logCoeff_succ_mul (n : ℕ) : logCoeff 𝕂 (n + 1) * ((n : 𝕂) + 1) = (-1) ^ n := by
  rw [logCoeff_succ, mul_assoc, inv_mul_cancel₀ (natCast_add_one_ne_zero 𝕂 n), mul_one]

end Coeff

variable (𝕂 𝔸 : Type*) [RCLike 𝕂] [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸]

/-- The power series of `u ↦ log (1 + u)` at `0`: its `n`-th coefficient is
`logCoeff 𝕂 n • (x₁ ⋯ xₙ)`, i.e. `(-1)^(n+1)/n • (x₁ ⋯ xₙ)` for `n ≥ 1`. -/
def logSeries : FormalMultilinearSeries 𝕂 𝔸 𝔸 := ofScalars 𝔸 (logCoeff 𝕂)

variable {𝕂 𝔸}

theorem logSeries_apply_eq (n : ℕ) (u : 𝔸) :
    (logSeries 𝕂 𝔸 n fun _ => u) = logCoeff 𝕂 n • u ^ n :=
  ofScalars_apply_eq (logCoeff 𝕂) u n

@[simp]
theorem logSeries_zero : logSeries 𝕂 𝔸 0 = 0 :=
  ofScalars_eq_zero_of_scalar_zero _ (logCoeff_zero 𝕂)

theorem norm_logSeries_succ_le (n : ℕ) : ‖logSeries 𝕂 𝔸 (n + 1)‖ ≤ ((n : ℝ) + 1)⁻¹ :=
  (ofScalars_norm_le _ _ _ n.succ_pos).trans_eq (norm_logCoeff_succ 𝕂 n)

theorem norm_logSeries_le_one (n : ℕ) : ‖logSeries 𝕂 𝔸 n‖ ≤ 1 := by
  rcases n with _ | n
  · simp
  · exact (ofScalars_norm_le _ _ _ n.succ_pos).trans (norm_logCoeff_le_one 𝕂 _)

variable (𝕂 𝔸) in
/-- The logarithm series converges on the unit ball. -/
theorem one_le_radius_logSeries : 1 ≤ (logSeries 𝕂 𝔸).radius := by
  have h := (logSeries 𝕂 𝔸).le_radius_of_bound (r := 1) 1 fun n => by
    rw [NNReal.coe_one, one_pow, mul_one]
    exact norm_logSeries_le_one n
  simpa using h

variable (𝕂) in
/-- `log1p 𝕂 u = log (1 + u) = ∑_{n ≥ 1} (-1)^(n+1) uⁿ / n`, the sum of `logSeries 𝕂 𝔸`.  It is
meaningful for `‖u‖ < 1`. -/
def log1p (u : 𝔸) : 𝔸 := (logSeries 𝕂 𝔸).sum u

theorem log1p_eq_tsum (u : 𝔸) :
    log1p 𝕂 u = ∑' n, logCoeff 𝕂 n • u ^ n :=  -- totalisation-audit: allow definition of log1p
  ofScalars_sum_eq _ _

@[simp]
theorem log1p_zero : log1p 𝕂 (0 : 𝔸) = 0 := by
  have h := ofScalarsSum_zero (E := 𝔸) (logCoeff 𝕂)
  rw [logCoeff_zero, zero_smul] at h
  exact h

/-- Whatever commutes with `u` commutes with `log (1 + u)`. -/
theorem _root_.Commute.log1p_right {a u : 𝔸} (h : Commute a u) : Commute a (log1p 𝕂 u) := by
  rw [log1p_eq_tsum]
  exact Commute.tsum_right a fun n => (h.pow_right n).smul_right _

theorem _root_.Commute.log1p_left {a u : 𝔸} (h : Commute u a) : Commute (log1p 𝕂 u) a :=
  (h.symm.log1p_right).symm

variable [CompleteSpace 𝔸]

omit [CompleteSpace 𝔸] in
theorem mem_eball_one_iff {u : 𝔸} : u ∈ Metric.eball (0 : 𝔸) 1 ↔ ‖u‖ < 1 := by
  rw [Metric.mem_eball, edist_zero_right, ← ofReal_norm, ENNReal.ofReal_lt_one]

/-- `log1p 𝕂` is the sum of the logarithm series on the unit ball. -/
theorem hasFPowerSeriesOnBall_log1p :
    HasFPowerSeriesOnBall (log1p 𝕂) (logSeries 𝕂 𝔸) (0 : 𝔸) 1 :=
  ((logSeries 𝕂 𝔸).hasFPowerSeriesOnBall
    (zero_lt_one.trans_le (one_le_radius_logSeries 𝕂 𝔸))).mono zero_lt_one
    (one_le_radius_logSeries 𝕂 𝔸)

theorem hasFPowerSeriesAt_log1p : HasFPowerSeriesAt (log1p 𝕂) (logSeries 𝕂 𝔸) (0 : 𝔸) :=
  hasFPowerSeriesOnBall_log1p.hasFPowerSeriesAt

/-- `log1p 𝕂` is analytic on the unit ball. -/
theorem analyticOnNhd_log1p : AnalyticOnNhd 𝕂 (log1p 𝕂) (Metric.ball (0 : 𝔸) 1) :=
  fun _ hu => hasFPowerSeriesOnBall_log1p.analyticAt_of_mem
    (mem_eball_one_iff.mpr (mem_ball_zero_iff.mp hu))

theorem analyticAt_log1p {u : 𝔸} (hu : ‖u‖ < 1) : AnalyticAt 𝕂 (log1p 𝕂) u :=
  analyticOnNhd_log1p u (mem_ball_zero_iff.mpr hu)

theorem continuousOn_log1p : ContinuousOn (log1p 𝕂) (Metric.ball (0 : 𝔸) 1) :=
  analyticOnNhd_log1p.continuousOn

/-- The defining series of `log (1 + u)` converges to `log1p 𝕂 u` for `‖u‖ < 1`. -/
theorem hasSum_log1p {u : 𝔸} (hu : ‖u‖ < 1) :
    HasSum (fun n => logCoeff 𝕂 n • u ^ n) (log1p 𝕂 u) := by
  have h := (hasFPowerSeriesOnBall_log1p (𝕂 := 𝕂) (𝔸 := 𝔸)).hasSum (mem_eball_one_iff.mpr hu)
  simp only [zero_add, logSeries_apply_eq] at h
  exact h

/-- `‖log (1 + u)‖ ≤ -log (1 - ‖u‖)`. -/
theorem norm_log1p_le {u : 𝔸} (hu : ‖u‖ < 1) :
    ‖log1p 𝕂 u‖ ≤ -Real.log (1 - ‖u‖) := by  -- totalisation-audit: allow 1 - ‖u‖ > 0 by hu
  have h0 := hasSum_log1p (𝕂 := 𝕂) hu
  have h1 : HasSum (fun n => logCoeff 𝕂 (n + 1) • u ^ (n + 1)) (log1p 𝕂 u) := by
    rw [← hasSum_nat_add_iff' 1] at h0
    simpa using h0
  have h2 := Real.hasSum_pow_div_log_of_abs_lt_one
    (by rwa [abs_of_nonneg (norm_nonneg u)] : |‖u‖| < 1)
  refine h1.norm_le_of_bounded h2 fun n => ?_
  rw [norm_smul, norm_logCoeff_succ, div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left (norm_pow_le' u n.succ_pos) (by positivity)

/-- `‖log (1 + u)‖ ≤ ‖u‖ / (1 - ‖u‖)`. -/
theorem norm_log1p_le_div {u : 𝔸} (hu : ‖u‖ < 1) :
    ‖log1p 𝕂 u‖ ≤ ‖u‖ / (1 - ‖u‖) := by  -- totalisation-audit: allow 1 - ‖u‖ > 0 by hu
  refine (norm_log1p_le hu).trans ?_
  have h1 : 0 < 1 - ‖u‖ := by linarith
  have h2 := Real.log_le_sub_one_of_pos (inv_pos.mpr h1)
  rw [Real.log_inv] at h2
  refine h2.trans_eq ?_
  field_simp
  ring

end BakerCampbellHausdorff
