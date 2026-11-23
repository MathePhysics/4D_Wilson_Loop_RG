import Mathlib

/-! Densities of product measures:
* lmarginal_prod_apply, lintegral_pi_prod: `∫⁻ ∏_i h_i(x_i) d(⊗_i μ_i) = ∏_i ∫⁻ h_i dμ_i` (σ-finite factors);
* pi_withDensity: `⊗_i (μ_i with density f_i) = (⊗_i μ_i) with density ∏_i f_i(x_i)`;
* pi_gaussianReal_eq_withDensity: `N(0,1)^{⊗ι}` has the density `(2π)^{-|ι|/2} e^{-|ξ|²/2}`. -/

namespace GaussianBlockSpin

open MeasureTheory ProbabilityTheory Real Function
open scoped ENNReal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Partial integrals of products**: integrating `∏_i h_i(x_i)` over the coordinates in `s` gives
`(∏_{i ∈ s} ∫⁻ h_i dμ_i) ∏_{i ∉ s} h_i(x_i)`. -/
lemma lmarginal_prod_apply (μ : ι → Measure ℝ) [∀ i, SigmaFinite (μ i)] (h : ι → ℝ → ℝ≥0∞)
    (hh : ∀ i, Measurable (h i)) (s : Finset ι) (x : ι → ℝ) :
    (∫⋯∫⁻_s, (fun y => ∏ i, h i (y i)) ∂μ) x =
      (∏ i ∈ s, ∫⁻ t, h i t ∂(μ i)) * ∏ i ∈ Finset.univ \ s, h i (x i) := by
  induction s using Finset.induction_on generalizing x with
  | empty => simp
  | insert j s hj ih =>
    have hmeas : Measurable fun y : ι → ℝ => ∏ i, h i (y i) :=
      Finset.measurable_prod _ fun i _ => (hh i).comp (measurable_pi_apply i)
    rw [lmarginal_insert _ hmeas hj]
    simp_rw [ih]
    have hsplit : ∀ t : ℝ, ∏ i ∈ Finset.univ \ s, h i (update x j t i) =
        h j t * ∏ i ∈ Finset.univ \ insert j s, h i (x i) := fun t => by
      have hmem : j ∈ Finset.univ \ s := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hj⟩
      rw [← Finset.mul_prod_erase _ _ hmem, update_self]
      congr 1
      have herase : (Finset.univ \ s).erase j = Finset.univ \ insert j s := by
        ext i; simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert]
        tauto
      rw [herase]
      refine Finset.prod_congr rfl fun i hi => ?_
      have hij : i ≠ j := fun h => (Finset.mem_sdiff.mp hi).2 (Finset.mem_insert.mpr (Or.inl h))
      rw [update_of_ne hij]
    simp_rw [hsplit]
    have hfun : (fun t => (∏ i ∈ s, ∫⁻ t, h i t ∂(μ i)) * (h j t * ∏ i ∈ Finset.univ \ insert j s, h i (x i))) =
        fun t => ((∏ i ∈ s, ∫⁻ t, h i t ∂(μ i)) * ∏ i ∈ Finset.univ \ insert j s, h i (x i)) * h j t := by
      funext t; ring
    rw [hfun, lintegral_const_mul _ (hh j), Finset.prod_insert hj]
    ring

/-- **The integral of a product of functions of single coordinates** under a product of σ-finite measures. -/
theorem lintegral_pi_prod (μ : ι → Measure ℝ) [∀ i, SigmaFinite (μ i)] (h : ι → ℝ → ℝ≥0∞)
    (hh : ∀ i, Measurable (h i)) :
    ∫⁻ x, ∏ i, h i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ t, h i t ∂(μ i) := by
  rw [lintegral_eq_lmarginal_univ (0 : ι → ℝ), lmarginal_prod_apply μ h hh Finset.univ 0, Finset.sdiff_self,
    Finset.prod_empty, mul_one]

/-- **The product of measures with densities** has the product density. -/
theorem pi_withDensity (μ : ι → Measure ℝ) [∀ i, SigmaFinite (μ i)] (f : ι → ℝ → ℝ≥0∞) (hf : ∀ i, Measurable (f i))
    (hfin : ∀ i, SigmaFinite ((μ i).withDensity (f i))) :
    Measure.pi (fun i => (μ i).withDensity (f i)) = (Measure.pi μ).withDensity fun x => ∏ i, f i (x i) := by
  refine Measure.pi_eq fun s hs => ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), ← lintegral_indicator (MeasurableSet.univ_pi hs)]
  have hind : (Set.univ.pi s).indicator (fun x : ι → ℝ => ∏ i, f i (x i)) =
      fun x => ∏ i, (s i).indicator (f i) (x i) := by
    funext x
    by_cases hx : x ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem hx]
      exact Finset.prod_congr rfl fun i _ => (Set.indicator_of_mem (hx i (Set.mem_univ i)) _).symm
    · rw [Set.indicator_of_notMem hx]
      obtain ⟨i, hi⟩ : ∃ i, x i ∉ s i := by
        by_contra hcon
        push Not at hcon
        exact hx fun i _ => hcon i
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)).symm
  rw [hind, lintegral_pi_prod μ _ fun i => (hf i).indicator (hs i)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [withDensity_apply _ (hs i), lintegral_indicator (hs i)]

/-- **The density of `N(0,1)^{⊗ι}`**: `(2π)^{-|ι|/2} e^{-|ξ|²/2}`. -/
theorem pi_gaussianReal_eq_withDensity :
    Measure.pi (fun _ : ι => gaussianReal 0 1) = volume.withDensity fun ξ : ι → ℝ =>
      ENNReal.ofReal ((Real.sqrt (2 * π))⁻¹ ^ Fintype.card ι * Real.exp (-(1 / 2) * ∑ i, ξ i ^ 2)) := by
  have h1 : (fun _ : ι => gaussianReal 0 1) = fun _ : ι => volume.withDensity (gaussianPDF 0 1) :=
    funext fun _ => gaussianReal_of_var_ne_zero 0 one_ne_zero
  rw [h1, pi_withDensity (fun _ => volume) (fun _ => gaussianPDF 0 1) (fun _ => measurable_gaussianPDF 0 1)
    (fun _ => by rw [← gaussianReal_of_var_ne_zero 0 one_ne_zero]; infer_instance), volume_pi]
  congr 1
  funext ξ
  simp only [gaussianPDF]
  rw [← ENNReal.ofReal_prod_of_nonneg fun i _ => gaussianPDFReal_nonneg 0 1 _]
  congr 1
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← Real.exp_sum, Finset.mul_sum]
  congr 2
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

end GaussianBlockSpin
