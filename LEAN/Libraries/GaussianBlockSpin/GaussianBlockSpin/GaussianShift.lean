import GaussianBlockSpin.GaussianGraphs

/-! Completing the square against the normalised Gaussian measure: a lintegral of `e^{-(½⟪x, T x⟫ - ⟪b, x⟫ + c) - W(x)}`
over `x` is the constant `e^{½⟪x₀, b⟫ - c} ∫ e^{-½⟪y, T y⟫} dy` times the expectation of `e^{-W(x₀ + y)}` under `gaussProb T`,
`T x₀ = b` (lintegral_exp_quadratic_shift). Used to write the bracket of I.(3.35), whose exponent at `e' = λ' = 0` is a
non-centred quadratic polynomial, as a Gaussian expectation. -/

open MeasureTheory
open scoped RealInnerProductSpace

namespace GaussianBlockSpin

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Completing the square against the normalised Gaussian measure**: for `T` symmetric positive definite and
`T x₀ = b`, `∫ e^{-(½⟪x, T x⟫ - ⟪b, x⟫ + c) - W(x)} dx = e^{½⟪x₀, b⟫ - c} (∫ e^{-½⟪y, T y⟫} dy) ∫ e^{-W(x₀ + y)} dμ_T(y)`
(as lintegrals of nonnegative functions; `W` measurable). -/
theorem lintegral_exp_quadratic_shift {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) (hpos : ∀ x, x ≠ 0 → 0 < ⟪x, T x⟫)
    {x₀ b : E} (hTx : T x₀ = b) (c : ℝ) {W : E → ℝ} (hW : Measurable W) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (-(1 / 2 * ⟪x, T x⟫ - ⟪b, x⟫ + c) - W x)) =
      ENNReal.ofReal (Real.exp (1 / 2 * ⟪x₀, b⟫ - c) * ∫ y, gaussWeight T y) *
        ∫⁻ y, ENNReal.ofReal (Real.exp (-W (x₀ + y))) ∂gaussProb T := by
  have hZ := integral_gaussWeight_pos hT hpos
  rw [← lintegral_add_left_eq_self _ x₀]
  have hpt : ∀ y, ENNReal.ofReal (Real.exp (-(1 / 2 * ⟪x₀ + y, T (x₀ + y)⟫ - ⟪b, x₀ + y⟫ + c) - W (x₀ + y))) =
      ENNReal.ofReal (Real.exp (1 / 2 * ⟪x₀, b⟫ - c)) *
        (ENNReal.ofReal (gaussWeight T y) * ENNReal.ofReal (Real.exp (-W (x₀ + y)))) := by
    intro y
    rw [← ENNReal.ofReal_mul (gaussWeight_pos T y).le, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    congr 1
    unfold gaussWeight
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    have h1 : ⟪x₀, T y⟫ = ⟪b, y⟫ := by rw [← hT, hTx]
    have h2 : ⟪y, T x₀⟫ = ⟪y, b⟫ := by rw [hTx]
    rw [map_add, inner_add_left, inner_add_right, inner_add_right, h1, h2, hTx, inner_add_right,
      real_inner_comm y b, real_inner_comm x₀ b]
    ring
  simp_rw [hpt]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ENNReal.ofReal_mul (Real.exp_pos _).le, mul_assoc]
  congr 1
  have hg : Measurable fun y => ENNReal.ofReal (Real.exp (-W (x₀ + y))) :=
    ENNReal.measurable_ofReal.comp ((hW.comp (measurable_const_add x₀)).neg.exp)
  rw [gaussProb, lintegral_withDensity_eq_lintegral_mul _ (measurable_gaussDensity T).coe_nnreal_ennreal hg,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun y => ?_
  simp only [Pi.mul_apply]
  rw [← mul_assoc]
  congr 1
  show ENNReal.ofReal (gaussWeight T y) =
    ENNReal.ofReal (∫ y, gaussWeight T y) * ENNReal.ofReal (gaussWeight T y / ∫ y, gaussWeight T y)
  rw [← ENNReal.ofReal_mul hZ.le]
  congr 1
  field_simp

end GaussianBlockSpin
