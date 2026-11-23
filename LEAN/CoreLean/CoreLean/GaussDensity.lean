/-
Gaussian measures by their density and as images of the standard Gaussian measure, for `lem:gaussian-conditioning` of
BALABAN_CORE.tex (`a021c13be348`). For a positive definite `Γ` on `ℝ^ι` with `C = Γ⁻¹`:
(a) the measure `det(Γ/2π)^{1/2}e^{-½⟨A, ΓA⟩}dA` is the Gaussian measure `μ_C` of the covariance `C` (Mathlib's
`multivariateGaussian 0 C`), by the characteristic functions, which are `eq:complex-gaussian` at `v = -iξ`;
(b) if `TTᵀ = C`, the image of the standard Gaussian measure under `T` is `μ_C`.
-/
import CoreLean.GaussComplex

open Matrix Complex MeasureTheory Real ProbabilityTheory WithLp
open scoped RealInnerProductSpace

noncomputable section

namespace CoreLean
namespace ComplexGauss

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma cM_mem_of_posDef {Γ : Matrix ι ι ℝ} (hΓ : Γ.PosDef) : cM Γ ∈ QSet := by
  refine ⟨?_, ?_⟩
  · have h : Γᵀ = Γ := by
      have := hΓ.1; unfold Matrix.IsHermitian at this; rwa [conjTranspose_eq_transpose_of_trivial] at this
    rw [← Matrix.transpose_map, h]
  · have : reM (cM Γ) = Γ := by ext i j; simp [reM, cM]
    rw [this]; exact hΓ

/-- The density `det(Γ/2π)^{1/2}e^{-½⟨A, ΓA⟩}`. -/
def gdens (Γ : Matrix ι ι ℝ) (x : ι → ℝ) : ℝ := (root (cM Γ)).re * Real.exp (-(1 / 2) * (x ⬝ᵥ (Γ *ᵥ x)))

/-- The measure with the density `gdens`. -/
def gaussM (Γ : Matrix ι ι ℝ) : Measure (ι → ℝ) := volume.withDensity fun x => ENNReal.ofReal (gdens Γ x)

lemma root_re_pos {Γ : Matrix ι ι ℝ} (hΓ : Γ.PosDef) : 0 < (root (cM Γ)).re ∧ root (cM Γ) = (root (cM Γ)).re := by
  obtain ⟨s, hs, hrs⟩ := root_real (cM_mem_of_posDef hΓ)
  rw [hrs]; simp [hs]

lemma gdens_nonneg {Γ : Matrix ι ι ℝ} (hΓ : Γ.PosDef) (x : ι → ℝ) : 0 ≤ gdens Γ x :=
  mul_nonneg (root_re_pos hΓ).1.le (Real.exp_pos _).le

lemma continuous_quad (Γ : Matrix ι ι ℝ) : Continuous fun x : ι → ℝ => x ⬝ᵥ (Γ *ᵥ x) := by
  simp only [dotProduct, mulVec]
  exact continuous_finsetSum _ fun i _ => (continuous_apply i).mul
    (continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_apply j))

lemma continuous_gdens (Γ : Matrix ι ι ℝ) : Continuous (gdens Γ) := by
  unfold gdens
  exact continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul (continuous_quad Γ)))

/-- `|e^{-½⟨A, ΓA⟩}|` is dominated by a product of one-dimensional Gaussians. -/
lemma integrable_gdens {Γ : Matrix ι ι ℝ} (hΓ : Γ.PosDef) : Integrable (gdens Γ) := by
  obtain ⟨c, hc, hlow⟩ := posDef_lower hΓ
  refine (integrable_dom hc ((root (cM Γ)).re * Real.exp (Fintype.card ι * (0 ^ 2 / c)))).mono'
    (continuous_gdens Γ).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (gdens_nonneg hΓ x), gdens, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (root_re_pos hΓ).1.le
  have h := dom_le hc 0 x
  simp only [zero_mul, add_zero] at h
  refine le_trans (Real.exp_le_exp.2 ?_) h
  have := hlow x
  nlinarith [nsq_nonneg x]

lemma isFiniteMeasure_gaussM {Γ : Matrix ι ι ℝ} (hΓ : Γ.PosDef) : IsFiniteMeasure (gaussM Γ) :=
  isFiniteMeasure_withDensity_ofReal (integrable_gdens hΓ).hasFiniteIntegral

lemma inner_toLp (x : ι → ℝ) (ξ : EuclideanSpace ℝ ι) : ⟪toLp 2 x, ξ⟫ = ∑ i, x i * ξ i := by
  simp [PiLp.inner_apply, mul_comm]

/-- **The characteristic function of the density measure**: `∫e^{i⟨A, ξ⟩}dμ = e^{-½⟨ξ, Cξ⟩}`. -/
lemma charFun_gaussM {Γ : Matrix ι ι ℝ} (hΓ : Γ.PosDef) (ξ : EuclideanSpace ℝ ι) :
    charFun ((gaussM Γ).map (toLp 2)) ξ = cexp (-((ofLp ξ) ⬝ᵥ (Γ⁻¹ *ᵥ ofLp ξ) : ℝ) / 2) := by
  have hQ := cM_mem_of_posDef hΓ
  have hdet : Γ.det ≠ 0 := hΓ.det_pos.ne'
  rw [charFun_apply, integral_map (by fun_prop) (by fun_prop)]
  have hg : gaussM Γ = volume.withDensity fun x => ((gdens Γ x).toNNReal : ENNReal) := rfl
  have hmeas : Measurable fun x => (gdens Γ x).toNNReal :=
    (continuous_gdens Γ).measurable.real_toNNReal
  rw [hg, integral_withDensity_eq_integral_smul hmeas]
  set v : ι → ℂ := fun i => -Complex.I * (ξ i : ℂ) with hv
  have h := complex_gaussian hQ v
  have hint : ∀ x : ι → ℝ, (gdens Γ x).toNNReal • cexp (⟪toLp 2 x, ξ⟫ * Complex.I) =
      root (cM Γ) * cexp (-(1 / 2) * qf (cM Γ) x - cV x ⬝ᵥ v) := by
    intro x
    rw [NNReal.smul_def, Real.coe_toNNReal _ (gdens_nonneg hΓ x), Complex.real_smul, gdens,
      (root_re_pos hΓ).2, inner_toLp, qf_cM, Complex.ofReal_mul, Complex.ofReal_exp, mul_assoc, ← Complex.exp_add]
    · congr 2
      simp only [hv, cV, dotProduct]
      push_cast
      rw [Finset.sum_mul, sub_eq_add_neg, ← Finset.sum_neg_distrib]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by ring
  simp_rw [hint]
  rw [integral_const_mul]
  unfold Zv at h
  rw [h, cM_inv hdet]
  congr 1
  simp only [hv, dotProduct, mulVec, cM, Matrix.map_apply, Complex.ofRealHom_eq_coe]
  push_cast
  simp only [Finset.mul_sum, Finset.sum_div, neg_div, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  linear_combination (1 / 2 * ((ofLp ξ) i : ℂ) * ((Γ⁻¹ i j : ℝ) : ℂ) * ((ofLp ξ) j : ℂ)) * Complex.I_sq

/-- **(a)** `det(Γ/2π)^{1/2}e^{-½⟨A, ΓA⟩}dA` is the Gaussian measure of the covariance `Γ⁻¹`. -/
theorem gaussM_eq {Γ : Matrix ι ι ℝ} (hΓ : Γ.PosDef) :
    (gaussM Γ).map (toLp 2) = multivariateGaussian 0 Γ⁻¹ := by
  haveI := isFiniteMeasure_gaussM hΓ
  have hC : (Γ⁻¹).PosSemidef := hΓ.inv.posSemidef
  refine Measure.ext_of_charFun (funext fun ξ => ?_)
  rw [charFun_gaussM hΓ, charFun_multivariateGaussian hC]
  simp [neg_div]

/-- **(b)** If `TTᵀ = C`, the image of the standard Gaussian measure under `T` is `μ_C`. -/
theorem stdGaussian_map_eq {ι' : Type*} [Fintype ι'] (C : Matrix ι ι ℝ) (hC : C.PosSemidef) (T : Matrix ι ι' ℝ)
    (hT : T * Tᵀ = C) :
    (stdGaussian (EuclideanSpace ℝ ι')).map (fun X => toLp 2 (T *ᵥ ofLp X)) = multivariateGaussian 0 C := by
  have hmeas : Measurable fun X : EuclideanSpace ℝ ι' => toLp 2 (T *ᵥ ofLp X) := by
    have : Continuous fun X : EuclideanSpace ℝ ι' => toLp 2 (T *ᵥ ofLp X) :=
      (PiLp.continuous_toLp 2 _).comp (continuous_const.matrix_mulVec (PiLp.continuous_ofLp 2 _))
    exact this.measurable
  refine Measure.ext_of_charFun (funext fun ξ => ?_)
  rw [charFun_apply, integral_map hmeas.aemeasurable (by fun_prop), charFun_multivariateGaussian hC]
  have hinner : ∀ X : EuclideanSpace ℝ ι', ⟪toLp 2 (T *ᵥ ofLp X), ξ⟫ = ⟪X, toLp 2 (Tᵀ *ᵥ ofLp ξ)⟫ := by
    intro X
    rw [inner_toLp]
    simp only [PiLp.inner_apply, PiLp.toLp_apply, RCLike.inner_apply, conj_trivial, mulVec, dotProduct,
      transpose_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  simp_rw [hinner]
  rw [← charFun_apply, charFun_stdGaussian]
  have hsq : ∑ i, (toLp 2 (Tᵀ *ᵥ ofLp ξ)) i ^ 2 = ofLp ξ ⬝ᵥ (C *ᵥ ofLp ξ) := by
    simp only [PiLp.toLp_apply]
    have hvt : ofLp ξ ᵥ* T = Tᵀ *ᵥ ofLp ξ := by simpa using (vecMul_transpose Tᵀ (ofLp ξ))
    rw [← hT, ← mulVec_mulVec, dotProduct_mulVec, hvt]
    simp [dotProduct, pow_two]
  rw [inner_zero_right, Complex.ofReal_zero, zero_mul, zero_sub, ← Complex.ofReal_pow,
    EuclideanSpace.real_norm_sq_eq, hsq]
  push_cast; ring

end ComplexGauss
end CoreLean

end
