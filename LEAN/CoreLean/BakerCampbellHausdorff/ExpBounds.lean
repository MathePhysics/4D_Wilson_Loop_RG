import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Complex.Exponential

/-!
# Norm bounds for the exponential in a Banach algebra

Elementary facts about `NormedSpace.exp` on a Banach algebra `𝔸` over `𝕂 = ℝ` or `ℂ` that
mathlib states only over `ℚ`-algebras or not at all.

## Main results

* `exp_add_of_commute'`, `exp_mul_exp_neg`, `exp_neg_mul_exp`: `exp (x + y) = exp x exp y` for
  commuting `x`, `y`, and `exp (-x)` is a two-sided inverse of `exp x`.  (Mathlib's versions ask
  for a `NormedAlgebra ℚ 𝔸` instance, which a `𝕂`-algebra does not provide.)
* `norm_exp_sub_one_le`: `‖exp x - 1‖ ≤ e^‖x‖ - 1`.
* `norm_exp_sub_one_sub_le`: `‖exp x - 1 - x‖ ≤ e^‖x‖ - 1 - ‖x‖`.
* `norm_exp_mul_exp_sub_one_le`: `‖exp x exp y - 1‖ ≤ e^(‖x‖ + ‖y‖) - 1`.
* `eq_zero_of_exp_eq_one`: `exp w = 1` and `‖w‖ < 1` imply `w = 0`.

The bounds compare the exponential series term by term with the real series of `e^‖x‖`; the
last one follows from the second, since `e^t - 1 - t ≤ t² < t` for `0 < t < 1`.
-/

noncomputable section

open NormedSpace
open scoped Nat

namespace BakerCampbellHausdorff

/-- The real exponential series `∑ tⁿ/n! = eᵗ`. -/
theorem hasSum_real_exp (t : ℝ) : HasSum (fun n => (n !⁻¹ : ℝ) • t ^ n) (Real.exp t) := by
  rw [Real.exp_eq_exp_ℝ]
  exact exp_series_hasSum_exp' t

variable (𝕂 : Type*) {𝔸 : Type*} [RCLike 𝕂] [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸]
  [CompleteSpace 𝔸]

omit [CompleteSpace 𝔸] in
theorem mem_eball_expSeries_radius (x : 𝔸) :
    x ∈ Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius := by
  rw [expSeries_radius_eq_top]
  exact edist_lt_top _ _

include 𝕂

/-- `exp (x + y) = exp x * exp y` for commuting `x` and `y` in a Banach algebra over `𝕂`. -/
theorem exp_add_of_commute' {x y : 𝔸} (h : Commute x y) : exp (x + y) = exp x * exp y :=
  exp_add_of_commute_of_mem_ball h (mem_eball_expSeries_radius 𝕂 x)
    (mem_eball_expSeries_radius 𝕂 y)

theorem exp_mul_exp_neg (x : 𝔸) : exp x * exp (-x) = 1 := by
  rw [← exp_add_of_commute' 𝕂 (Commute.neg_right (Commute.refl x)), add_neg_cancel, exp_zero]

theorem exp_neg_mul_exp (x : 𝔸) : exp (-x) * exp x = 1 := by
  rw [← exp_add_of_commute' 𝕂 (Commute.neg_left (Commute.refl x)), neg_add_cancel, exp_zero]

omit [CompleteSpace 𝔸] in
theorem norm_expSeries_term_le (x : 𝔸) {n : ℕ} (hn : 0 < n) :
    ‖(n !⁻¹ : 𝕂) • x ^ n‖ ≤ (n !⁻¹ : ℝ) • ‖x‖ ^ n := by
  rw [norm_smul, norm_inv, RCLike.norm_natCast, smul_eq_mul]
  exact mul_le_mul_of_nonneg_left (norm_pow_le' x hn) (by positivity)

/-- The tail of the exponential series after the constant term. -/
theorem norm_exp_sub_one_le (x : 𝔸) : ‖exp x - 1‖ ≤ Real.exp ‖x‖ - 1 := by
  have h1 := (hasSum_nat_add_iff' 1).mpr (exp_series_hasSum_exp' (𝕂 := 𝕂) x)
  have h2 := (hasSum_nat_add_iff' 1).mpr (hasSum_real_exp ‖x‖)
  have e1 : ∑ i ∈ Finset.range 1, ((i ! : 𝕂)⁻¹ • x ^ i) = 1 := by simp
  have e2 : ∑ i ∈ Finset.range 1, (i !⁻¹ : ℝ) • ‖x‖ ^ i = 1 := by simp
  rw [e1] at h1
  rw [e2] at h2
  exact h1.norm_le_of_bounded h2 fun n => norm_expSeries_term_le 𝕂 x n.succ_pos

/-- The tail of the exponential series after the linear term. -/
theorem norm_exp_sub_one_sub_le (x : 𝔸) : ‖exp x - 1 - x‖ ≤ Real.exp ‖x‖ - 1 - ‖x‖ := by
  have h1 := (hasSum_nat_add_iff' 2).mpr (exp_series_hasSum_exp' (𝕂 := 𝕂) x)
  have h2 := (hasSum_nat_add_iff' 2).mpr (hasSum_real_exp ‖x‖)
  have e1 : ∑ i ∈ Finset.range 2, ((i ! : 𝕂)⁻¹ • x ^ i) = 1 + x := by
    simp [Finset.sum_range_succ]
  have e2 : ∑ i ∈ Finset.range 2, (i !⁻¹ : ℝ) • ‖x‖ ^ i = 1 + ‖x‖ := by
    simp [Finset.sum_range_succ]
  rw [e1] at h1
  rw [e2] at h2
  rw [sub_sub, sub_sub]
  exact h1.norm_le_of_bounded h2 fun n => norm_expSeries_term_le 𝕂 x (by omega)

/-- `‖exp x exp y - 1‖ ≤ e^(‖x‖ + ‖y‖) - 1`. -/
theorem norm_exp_mul_exp_sub_one_le (x y : 𝔸) :
    ‖exp x * exp y - 1‖ ≤ Real.exp (‖x‖ + ‖y‖) - 1 := by
  have hx := norm_exp_sub_one_le 𝕂 x
  have hy := norm_exp_sub_one_le 𝕂 y
  have hid : exp x * exp y - 1 =
      (exp x - 1) * (exp y - 1) + (exp x - 1) + (exp y - 1) := by noncomm_ring
  have hA : 0 ≤ Real.exp ‖x‖ - 1 := by
    linarith [Real.add_one_le_exp ‖x‖, norm_nonneg x]
  have hB : 0 ≤ Real.exp ‖y‖ - 1 := by
    linarith [Real.add_one_le_exp ‖y‖, norm_nonneg y]
  rw [hid, Real.exp_add]
  calc ‖(exp x - 1) * (exp y - 1) + (exp x - 1) + (exp y - 1)‖
      ≤ ‖exp x - 1‖ * ‖exp y - 1‖ + ‖exp x - 1‖ + ‖exp y - 1‖ := by
        refine (norm_add₃_le).trans ?_
        gcongr
        exact norm_mul_le _ _
    _ ≤ (Real.exp ‖x‖ - 1) * (Real.exp ‖y‖ - 1) + (Real.exp ‖x‖ - 1) + (Real.exp ‖y‖ - 1) := by
        gcongr
    _ = Real.exp ‖x‖ * Real.exp ‖y‖ - 1 := by ring

/-- `exp` is injective near `0` in the weak form needed here: `exp w = 1` with `‖w‖ < 1` forces
`w = 0`. -/
theorem eq_zero_of_exp_eq_one {w : 𝔸} (h : exp w = 1) (hw : ‖w‖ < 1) : w = 0 := by
  have h1 := norm_exp_sub_one_sub_le 𝕂 w
  rw [h, sub_self, zero_sub, norm_neg] at h1
  have h0 : 0 ≤ ‖w‖ := norm_nonneg w
  have h2 : |Real.exp ‖w‖ - 1 - ‖w‖| ≤ ‖w‖ ^ 2 :=
    Real.abs_exp_sub_one_sub_id_le (by rw [abs_of_nonneg h0]; exact hw.le)
  have h3 : ‖w‖ ≤ ‖w‖ ^ 2 := h1.trans ((le_abs_self _).trans h2)
  have h4 : ‖w‖ = 0 := by nlinarith
  exact norm_eq_zero.mp h4

end BakerCampbellHausdorff
