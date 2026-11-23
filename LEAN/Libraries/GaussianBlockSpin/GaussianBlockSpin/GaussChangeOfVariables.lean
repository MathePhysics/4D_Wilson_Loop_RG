import GaussianBlockSpin.ProductDensities
import GaussianBlockSpin.GaussPushforward
import GaussianBlockSpin.GaussianGraphs

/-! **The Gaussian change of variables**: for a symmetric invertible `A` with `A A = Q⁻¹`, the law `A_* N(0,1)^{⊗ι}`
has the density `(2π)^{-|ι|/2} |det A|⁻¹ e^{-½ z·Qz}` (gaussPush_eq_withDensity); transported to a field space `E`
by a volume-preserving linear coordinate map `φ` with `⟪φ z, T φ z⟫ = z·Qz`, it is the normalised Gaussian measure
`gaussProb T` (gaussProb_eq_map_gaussPush). -/

namespace GaussianBlockSpin

open MeasureTheory ProbabilityTheory Real Matrix
open scoped ENNReal RealInnerProductSpace

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- **Pushing a density forward by a linear equivalence**: `(vol with density g).map e = vol with density
|det e|⁻¹ g(e⁻¹ z)`. -/
lemma map_withDensity_linearEquiv (e : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ)) {g : (ι → ℝ) → ℝ≥0∞} (hg : Measurable g) :
    (volume.withDensity g).map e =
      volume.withDensity fun z => ENNReal.ofReal |LinearMap.det (e : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))|⁻¹ * g (e.symm z) := by
  have he : Measurable e := (LinearMap.continuous_on_pi (e : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))).measurable
  have hes : Measurable e.symm := (LinearMap.continuous_on_pi (e.symm : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))).measurable
  have hdet : LinearMap.det (e : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) ≠ 0 := (LinearEquiv.isUnit_det' e).ne_zero
  ext s hs
  rw [Measure.map_apply he hs, withDensity_apply _ (he hs), withDensity_apply _ hs,
    ← lintegral_indicator (he hs), ← lintegral_indicator hs]
  have hF : ((e : (ι → ℝ) → (ι → ℝ)) ⁻¹' s).indicator g =
      fun ξ => (s.indicator fun z => g (e.symm z)) (e ξ) := by
    funext ξ
    by_cases hξ : e ξ ∈ s
    · rw [Set.indicator_of_mem (show ξ ∈ (e : (ι → ℝ) → (ι → ℝ)) ⁻¹' s from hξ), Set.indicator_of_mem hξ,
        LinearEquiv.symm_apply_apply]
    · rw [Set.indicator_of_notMem (show ξ ∉ (e : (ι → ℝ) → (ι → ℝ)) ⁻¹' s from hξ), Set.indicator_of_notMem hξ]
  have hcomp : ∫⁻ ξ, (s.indicator fun z => g (e.symm z)) (e ξ) =
      ∫⁻ z, (s.indicator fun z => g (e.symm z)) z ∂(volume.map e) :=
    (lintegral_map ((hg.comp hes).indicator hs) he).symm
  rw [hF, hcomp]
  have hmap := map_linearMap_volume_pi_eq_smul_volume_pi hdet
  rw [show (e : (ι → ℝ) → (ι → ℝ)) = ((e : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) : (ι → ℝ) → (ι → ℝ)) from rfl, hmap,
    lintegral_smul_measure, smul_eq_mul,
    ← lintegral_const_mul (f := s.indicator fun z => g (e.symm z)) _ ((hg.comp hes).indicator hs)]
  refine lintegral_congr fun z => ?_
  by_cases hz : z ∈ s
  · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz, abs_inv]
  · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, mul_zero]

omit [DecidableEq ι] in
/-- `(M z)·(M z) = z·(Mᵀ M z)`. -/
lemma dotProduct_mulVec_self (M : Matrix ι ι ℝ) (z : ι → ℝ) :
    (M *ᵥ z) ⬝ᵥ (M *ᵥ z) = z ⬝ᵥ ((Mᵀ * M) *ᵥ z) := by
  rw [← mulVec_mulVec, mulVec_transpose, dotProduct_comm z, ← dotProduct_mulVec]

/-- **The density of `A_* N(0,1)^{⊗ι}`**: for `A` symmetric with `A A = Q⁻¹` (`Q` invertible), the density is
`(2π)^{-|ι|/2} |det A|⁻¹ e^{-½ z·Qz}`. -/
theorem gaussPush_eq_withDensity {A Q : Matrix ι ι ℝ} (hA : Aᵀ = A) (hAA : A * A = Q⁻¹) (hQ : IsUnit Q.det) :
    gaussPush A = volume.withDensity fun z => ENNReal.ofReal
      ((Real.sqrt (2 * π))⁻¹ ^ Fintype.card ι * |A.det|⁻¹ * Real.exp (-(1 / 2) * (z ⬝ᵥ Q *ᵥ z))) := by
  have hdetA : IsUnit A.det := by
    have h : (A * A).det ≠ 0 := by
      rw [hAA]
      exact (isUnit_nonsing_inv_det_iff.mpr hQ).ne_zero
    rw [det_mul] at h
    exact isUnit_iff_ne_zero.mpr (left_ne_zero_of_mul h)
  set e : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ) := LinearEquiv.ofLinearMap (toLin' A) (toLin' A⁻¹)
    (by rw [← toLin'_mul, mul_nonsing_inv _ hdetA, toLin'_one])
    (by rw [← toLin'_mul, nonsing_inv_mul _ hdetA, toLin'_one]) with he
  have hesymm : ∀ z, e.symm z = A⁻¹ *ᵥ z := fun z => rfl
  have hdet : LinearMap.det (e : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) = A.det := LinearMap.det_toLin' A
  have hg : Measurable fun ξ : ι → ℝ =>
      ENNReal.ofReal ((Real.sqrt (2 * π))⁻¹ ^ Fintype.card ι * Real.exp (-(1 / 2) * ∑ i, ξ i ^ 2)) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul (Real.measurable_exp.comp
      (measurable_const.mul (Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).pow_const 2))))
  unfold gaussPush
  rw [pi_gaussianReal_eq_withDensity, show (fun ξ => A *ᵥ ξ) = (e : (ι → ℝ) → (ι → ℝ)) from funext fun z => rfl,
    map_withDensity_linearEquiv e hg, hdet]
  congr 1
  funext z
  rw [← ENNReal.ofReal_mul (inv_nonneg.mpr (abs_nonneg _))]
  congr 1
  rw [hesymm]
  have hsum : ∑ i, (A⁻¹ *ᵥ z) i ^ 2 = z ⬝ᵥ Q *ᵥ z := by
    have h1 : ∑ i, (A⁻¹ *ᵥ z) i ^ 2 = (A⁻¹ *ᵥ z) ⬝ᵥ (A⁻¹ *ᵥ z) := by
      simp [dotProduct, sq]
    rw [h1, dotProduct_mulVec_self, transpose_nonsing_inv, hA, ← Matrix.mul_inv_rev, hAA,
      nonsing_inv_nonsing_inv _ hQ]
  rw [hsum]
  ring

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
  [BorelSpace E]

omit [DecidableEq ι] in
/-- Pushing a density forward by a volume-preserving linear equivalence. -/
lemma map_withDensity_measurePreserving (φ : (ι → ℝ) ≃ₗ[ℝ] E) (hφ : MeasurePreserving φ volume volume)
    {ρ : (ι → ℝ) → ℝ≥0∞} (hρ : Measurable ρ) :
    (volume.withDensity ρ).map φ = volume.withDensity fun x => ρ (φ.symm x) := by
  have hφm : Measurable φ := hφ.measurable
  have hφs : Measurable φ.symm := (LinearMap.continuous_of_finiteDimensional
    (φ.symm : E →ₗ[ℝ] (ι → ℝ))).measurable
  ext s hs
  rw [Measure.map_apply hφm hs, withDensity_apply _ (hφm hs), withDensity_apply _ hs,
    ← lintegral_indicator (hφm hs), ← lintegral_indicator hs]
  have hF : ((φ : (ι → ℝ) → E) ⁻¹' s).indicator ρ = fun z => (s.indicator fun x => ρ (φ.symm x)) (φ z) := by
    funext z
    by_cases hz : φ z ∈ s
    · rw [Set.indicator_of_mem (show z ∈ (φ : (ι → ℝ) → E) ⁻¹' s from hz), Set.indicator_of_mem hz,
        LinearEquiv.symm_apply_apply]
    · rw [Set.indicator_of_notMem (show z ∉ (φ : (ι → ℝ) → E) ⁻¹' s from hz), Set.indicator_of_notMem hz]
  have hcomp : ∫⁻ z, (s.indicator fun x => ρ (φ.symm x)) (φ z) =
      ∫⁻ x, (s.indicator fun x => ρ (φ.symm x)) x ∂(volume.map φ) :=
    (lintegral_map ((hρ.comp hφs).indicator hs) hφm).symm
  rw [hF, hcomp, hφ.map_eq]

/-- A probability measure with density `c g` (`g ≥ 0` integrable) has `c = (∫ g)⁻¹`. -/
lemma eq_inv_integral_of_withDensity_prob {g : E → ℝ} (hg0 : ∀ x, 0 ≤ g x) (hgi : Integrable g) {c : ℝ}
    (hc : 0 ≤ c) (hprob : IsProbabilityMeasure (volume.withDensity fun x => ENNReal.ofReal (c * g x))) :
    c = (∫ x, g x)⁻¹ := by
  have h1 := hprob.measure_univ
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (hgi.const_mul c) (ae_of_all _ fun x => mul_nonneg hc (hg0 x)),
    integral_const_mul] at h1
  have h2 : c * ∫ x, g x = 1 := by
    have := (ENNReal.ofReal_eq_one).mp h1
    exact this
  have hZ : (∫ x, g x) ≠ 0 := by
    intro h; rw [h, mul_zero] at h2; exact zero_ne_one h2
  field_simp
  linarith

/-- **The normalised Gaussian measure in coordinates**: if `φ : (ι → ℝ) ≃ E` is linear and volume preserving and
`⟪φ z, T φ z⟫ = z·Qz`, then `gaussProb T = (A_* N(0,1)^{⊗ι}).map φ` for every symmetric `A` with `A A = Q⁻¹`. -/
theorem gaussProb_eq_map_gaussPush (φ : (ι → ℝ) ≃ₗ[ℝ] E) (hφ : MeasurePreserving φ volume volume)
    {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) (hpos : ∀ x, x ≠ 0 → 0 < ⟪x, T x⟫) {Q A : Matrix ι ι ℝ}
    (hQT : ∀ z, ⟪φ z, T (φ z)⟫ = z ⬝ᵥ Q *ᵥ z) (hA : Aᵀ = A) (hAA : A * A = Q⁻¹) (hQ : IsUnit Q.det) :
    gaussProb T = (gaussPush A).map φ := by
  set c : ℝ := (Real.sqrt (2 * π))⁻¹ ^ Fintype.card ι * |A.det|⁻¹ with hc
  have hc0 : 0 ≤ c := by positivity
  have hρ : Measurable fun z : ι → ℝ => ENNReal.ofReal (c * Real.exp (-(1 / 2) * (z ⬝ᵥ Q *ᵥ z))) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul (Real.measurable_exp.comp (measurable_const.mul
      (by fun_prop))))
  have hpush : (gaussPush A).map φ = volume.withDensity fun x => ENNReal.ofReal (c * gaussWeight T x) := by
    rw [gaussPush_eq_withDensity hA hAA hQ, map_withDensity_measurePreserving φ hφ hρ]
    congr 1
    funext x
    have := hQT (φ.symm x)
    rw [LinearEquiv.apply_symm_apply] at this
    rw [gaussWeight, this]
  have hprob : IsProbabilityMeasure (volume.withDensity fun x => ENNReal.ofReal (c * gaussWeight T x)) := by
    rw [← hpush]
    infer_instance
  have hcZ := eq_inv_integral_of_withDensity_prob (fun x => (gaussWeight_pos T x).le) (integrable_gaussWeight hT hpos)
    hc0 hprob
  rw [hpush, gaussProb]
  congr 1
  funext x
  rw [hcZ, ENNReal.ofReal, inv_mul_eq_div]

end GaussianBlockSpin
