/-
`lem:square-root-walks` of BALABAN_CORE.tex (`a021c13be348`), the integrals of its proof.

* The representation of the square root of the covariance in the eigenvalues: for `λ > 0`,
  `π⁻¹∫_0^∞ x^{-1/2}(x + λ)⁻¹ dx = λ^{-1/2}` (`inv_sqrt_integral`), with the antiderivative `2λ^{-1/2}arctan√(x/λ)`.
* The constant `C_{1/2}`: `π⁻¹∫_0^γ x^{-1/2}·2C dx = (4/π)γ^{1/2}C` and `π⁻¹∫_γ^∞ x^{-3/2}K dx = (2/π)γ^{-1/2}K`
  (`small_x_integral`, `large_x_integral`), the two parts of `C_{1/2}` with `C = C^U_inv` and
  `K = (1 + 2C_U)(1 + 2c₁N''θ_J)`.
-/
import Mathlib

open MeasureTheory Set Filter Topology

noncomputable section

namespace CoreLean
namespace SquareRootIntegral

/-- The antiderivative `F(x) = 2λ^{-1/2}arctan√(x/λ)`. -/
lemma hasDerivAt_F {l x : ℝ} (hl : 0 < l) (hx : 0 < x) :
    HasDerivAt (fun x => 2 / Real.sqrt l * Real.arctan (Real.sqrt (x / l)))
      (1 / (Real.sqrt x * (x + l))) x := by
  have hxl : 0 < x / l := div_pos hx hl
  have h1 : HasDerivAt (fun x => x / l) (1 / l) x := by
    simpa using (hasDerivAt_id x).div_const l
  have h2 : HasDerivAt (fun x => Real.sqrt (x / l)) (1 / l / (2 * Real.sqrt (x / l))) x :=
    (Real.hasDerivAt_sqrt hxl.ne').comp x h1 |>.congr_deriv (by field_simp)
  have h3 := (Real.hasDerivAt_arctan (Real.sqrt (x / l))).comp x h2
  have h4 : HasDerivAt (fun x => 2 / Real.sqrt l * Real.arctan (Real.sqrt (x / l)))
      (2 / Real.sqrt l * (1 / (1 + Real.sqrt (x / l) ^ 2) * (1 / l / (2 * Real.sqrt (x / l))))) x :=
    h3.const_mul (2 / Real.sqrt l)
  convert h4 using 1
  have hs : Real.sqrt (x / l) = Real.sqrt x / Real.sqrt l := Real.sqrt_div hx.le l
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hsl : 0 < Real.sqrt l := Real.sqrt_pos.2 hl
  have hsq : Real.sqrt (x / l) ^ 2 = x / l := Real.sq_sqrt hxl.le
  rw [hs]
  have hl' : Real.sqrt l ^ 2 = l := Real.sq_sqrt hl.le
  have hx' : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx.le
  generalize Real.sqrt x = a at hsx hx' ⊢
  generalize Real.sqrt l = b at hsl hl' ⊢
  subst hx' hl'
  field_simp
  ring

/-- **The integral of the square root**: `π⁻¹∫_0^∞ x^{-1/2}(x + λ)⁻¹ dx = λ^{-1/2}`. -/
theorem inv_sqrt_integral {l : ℝ} (hl : 0 < l) :
    Real.pi⁻¹ * ∫ x in Ioi (0 : ℝ), 1 / (Real.sqrt x * (x + l)) = 1 / Real.sqrt l := by
  set F : ℝ → ℝ := fun x => 2 / Real.sqrt l * Real.arctan (Real.sqrt (x / l))
  have hsl : 0 < Real.sqrt l := Real.sqrt_pos.2 hl
  have hcont : ContinuousWithinAt F (Ici 0) 0 := by
    have : Continuous F := by
      unfold F
      exact continuous_const.mul (Real.continuous_arctan.comp (Real.continuous_sqrt.comp
        (continuous_id.div_const l)))
    exact this.continuousWithinAt
  have hderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt F (1 / (Real.sqrt x * (x + l))) x := fun x hx =>
    hasDerivAt_F hl hx
  have hpos : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ 1 / (Real.sqrt x * (x + l)) := fun x hx => by
    rw [mem_Ioi] at hx; positivity
  have hlim : Tendsto F atTop (𝓝 (2 / Real.sqrt l * (Real.pi / 2))) := by
    refine (tendsto_const_nhds.mul (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds |>.comp ?_))
    exact Real.tendsto_sqrt_atTop.comp (tendsto_id.atTop_div_const hl)
  rw [integral_Ioi_of_hasDerivAt_of_nonneg hcont hderiv hpos hlim]
  simp only [F, zero_div, Real.sqrt_zero, Real.arctan_zero, mul_zero, sub_zero]
  field_simp

/-- **The small `x`**: `π⁻¹∫_0^γ x^{-1/2}·2C dx = (4/π)γ^{1/2}C`. -/
theorem small_x_integral {γ C : ℝ} (hγ : 0 < γ) :
    Real.pi⁻¹ * ∫ x in (0 : ℝ)..γ, x ^ (-(1 / 2 : ℝ)) * (2 * C) = 4 / Real.pi * γ ^ (1 / 2 : ℝ) * C := by
  rw [intervalIntegral.integral_mul_const, integral_rpow (Or.inl (by norm_num))]
  rw [Real.zero_rpow (by norm_num)]
  norm_num
  ring

/-- **The large `x`**: `π⁻¹∫_γ^∞ x^{-3/2}K dx = (2/π)γ^{-1/2}K`. -/
theorem large_x_integral {γ K : ℝ} (hγ : 0 < γ) :
    Real.pi⁻¹ * ∫ x in Ioi γ, x ^ (-(3 / 2 : ℝ)) * K = 2 / Real.pi * γ ^ (-(1 / 2 : ℝ)) * K := by
  rw [integral_mul_const, integral_Ioi_rpow_of_lt (by norm_num) hγ]
  norm_num
  ring

end SquareRootIntegral
end CoreLean

end
