import GaussianBlockSpin.GaussianGraphs

/-! **Factoring out Gaussian normalisations** in lower integrals (Bałaban I (3.22), (3.55)): for `T` symmetric positive
definite, `∫⁻ e^{-½⟪x, T x⟫} f(x) dx = Z_T ∫⁻ f dμ_T` with `Z_T = ∫ e^{-½⟪y, T y⟫} dy` and the normalised Gaussian
measure `μ_T = gaussProb T` (lintegral_gaussWeight_mul), its form for two independent fields
(lintegral_gaussWeight_mul₂), and lintegral_gauss_factorisation: factors that equal `1` wherever the remaining
characteristic functions do not vanish drop out, and the Gaussian weights become the normalisations times the
expectation. No measurability or integrability is needed. -/

open MeasureTheory
open scoped RealInnerProductSpace ENNReal NNReal

namespace GaussianBlockSpin

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

/-- **Factoring out a Gaussian normalisation**: `∫⁻ e^{-½⟪x, T x⟫} f(x) dx = Z_T ∫⁻ f dμ_T`, `Z_T = ∫ e^{-½⟪y, T y⟫} dy`. -/
theorem lintegral_gaussWeight_mul {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) (hpos : ∀ x, x ≠ 0 → 0 < ⟪x, T x⟫)
    (f : E → ℝ≥0∞) :
    ∫⁻ x, ENNReal.ofReal (gaussWeight T x) * f x =
      ENNReal.ofReal (∫ y, gaussWeight T y) * ∫⁻ x, f x ∂gaussProb T := by
  have hZ := integral_gaussWeight_pos hT hpos
  rw [gaussProb, lintegral_withDensity_eq_lintegral_mul_non_measurable _
    (measurable_gaussDensity T).coe_nnreal_ennreal (Filter.Eventually.of_forall fun _ => ENNReal.coe_lt_top),
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun x => ?_
  rw [Pi.mul_apply, ← mul_assoc]
  congr 1
  show ENNReal.ofReal (gaussWeight T x) =
    ENNReal.ofReal (∫ y, gaussWeight T y) * ENNReal.ofReal (gaussWeight T x / ∫ y, gaussWeight T y)
  rw [← ENNReal.ofReal_mul hZ.le, mul_div_cancel₀ _ hZ.ne']

/-- **Two independent Gaussian fields**: `∫⁻∫⁻ e^{-½⟪x, T x⟫} e^{-½⟪y, S y⟫} f(x, y) dy dx = Z_T Z_S ∫⁻∫⁻ f dμ_S dμ_T`. -/
theorem lintegral_gaussWeight_mul₂ {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) (hTpos : ∀ x, x ≠ 0 → 0 < ⟪x, T x⟫)
    {S : F →ₗ[ℝ] F} (hS : S.IsSymmetric) (hSpos : ∀ y, y ≠ 0 → 0 < ⟪y, S y⟫) (f : E → F → ℝ≥0∞) :
    ∫⁻ x, ∫⁻ y, ENNReal.ofReal (gaussWeight T x) * ENNReal.ofReal (gaussWeight S y) * f x y =
      ENNReal.ofReal (∫ x, gaussWeight T x) * ENNReal.ofReal (∫ y, gaussWeight S y) *
        ∫⁻ x, ∫⁻ y, f x y ∂gaussProb S ∂gaussProb T := by
  have hin : ∀ x, ∫⁻ y, ENNReal.ofReal (gaussWeight T x) * ENNReal.ofReal (gaussWeight S y) * f x y =
      ENNReal.ofReal (gaussWeight T x) * (ENNReal.ofReal (∫ y, gaussWeight S y) * ∫⁻ y, f x y ∂gaussProb S) := by
    intro x
    simp only [mul_assoc]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_gaussWeight_mul hS hSpos]
  simp only [hin]
  rw [lintegral_gaussWeight_mul hT hTpos, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, mul_assoc]

/-- **Removing factors that equal `1` where the others do not vanish, and factoring out the Gaussian
normalisations** (Bałaban I (3.22), (3.55)): if `c χ₁(x) χ₂(y) R(x, y) = c χ₁(x) χ₂(y)` for all `x`, `y`, then
`c ∫⁻∫⁻ R χ₁ χ₂ e^{-½⟪x, T x⟫ - ½⟪y, S y⟫ + W} = c Z_T Z_S ∫⁻∫⁻ χ₁ χ₂ e^{W} dμ_S dμ_T`. -/
theorem lintegral_gauss_factorisation {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) (hTpos : ∀ x, x ≠ 0 → 0 < ⟪x, T x⟫)
    {S : F →ₗ[ℝ] F} (hS : S.IsSymmetric) (hSpos : ∀ y, y ≠ 0 → 0 < ⟪y, S y⟫) {c : ℝ≥0∞} (hc : c ≠ ∞)
    (χ₁ : E → ℝ≥0∞) (χ₂ : F → ℝ≥0∞) (R : E → F → ℝ≥0∞) (hR : ∀ x y, c * χ₁ x * χ₂ y * R x y = c * χ₁ x * χ₂ y)
    (W : E → F → ℝ) :
    c * ∫⁻ x, ∫⁻ y, R x y * χ₁ x * χ₂ y *
        ENNReal.ofReal (Real.exp (-(1 / 2) * ⟪x, T x⟫ - (1 / 2) * ⟪y, S y⟫ + W x y)) =
      c * ENNReal.ofReal (∫ x, gaussWeight T x) * ENNReal.ofReal (∫ y, gaussWeight S y) *
        ∫⁻ x, ∫⁻ y, χ₁ x * χ₂ y * ENNReal.ofReal (Real.exp (W x y)) ∂gaussProb S ∂gaussProb T := by
  have hpt : ∀ x y, c * (R x y * χ₁ x * χ₂ y *
      ENNReal.ofReal (Real.exp (-(1 / 2) * ⟪x, T x⟫ - (1 / 2) * ⟪y, S y⟫ + W x y))) =
      c * (ENNReal.ofReal (gaussWeight T x) * ENNReal.ofReal (gaussWeight S y) *
        (χ₁ x * χ₂ y * ENNReal.ofReal (Real.exp (W x y)))) := by
    intro x y
    have hexp : ENNReal.ofReal (Real.exp (-(1 / 2) * ⟪x, T x⟫ - (1 / 2) * ⟪y, S y⟫ + W x y)) =
        ENNReal.ofReal (gaussWeight T x) * ENNReal.ofReal (gaussWeight S y) *
          ENNReal.ofReal (Real.exp (W x y)) := by
      rw [gaussWeight, gaussWeight, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
        ← ENNReal.ofReal_mul (by positivity), ← Real.exp_add, ← Real.exp_add]
      congr 2
      ring
    rw [hexp]
    calc c * (R x y * χ₁ x * χ₂ y * (ENNReal.ofReal (gaussWeight T x) * ENNReal.ofReal (gaussWeight S y) *
          ENNReal.ofReal (Real.exp (W x y))))
        = (c * χ₁ x * χ₂ y * R x y) * (ENNReal.ofReal (gaussWeight T x) * ENNReal.ofReal (gaussWeight S y) *
          ENNReal.ofReal (Real.exp (W x y))) := by ring
      _ = (c * χ₁ x * χ₂ y) * (ENNReal.ofReal (gaussWeight T x) * ENNReal.ofReal (gaussWeight S y) *
          ENNReal.ofReal (Real.exp (W x y))) := by rw [hR]
      _ = _ := by ring
  rw [← lintegral_const_mul' _ _ hc]
  simp only [← lintegral_const_mul' _ _ hc, hpt]
  simp only [lintegral_const_mul' _ _ hc]
  rw [lintegral_gaussWeight_mul₂ hT hTpos hS hSpos, mul_assoc c, mul_assoc c]

end GaussianBlockSpin
