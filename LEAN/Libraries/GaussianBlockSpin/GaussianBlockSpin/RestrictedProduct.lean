import Mathlib

/-! The cut-off of the independent coordinates: for a probability law `γ₁` on `ℝ` and `I = [-β, β]` with
`γ₁(I) > 0`, the product of the restrictions is `γ₁(I)^{|ι|}` times the product of the conditioned laws, so
`∫ 1_{I^ι} g d(γ₁^{⊗ι}) = γ₁(I)^{|ι|} ∫ g d(γ₁(· | I)^{⊗ι})` (lintegral_indicator_box_eq). -/

namespace GaussianBlockSpin

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {ι : Type*} [Fintype ι] (γ₁ : Measure ℝ) [IsProbabilityMeasure γ₁]

lemma pi_restrict_eq_smul_pi_cond {I : Set ℝ} (hI : MeasurableSet I) (hpos : γ₁ I ≠ 0) :
    Measure.pi (fun _ : ι => γ₁.restrict I) = (γ₁ I) ^ Fintype.card ι • Measure.pi (fun _ : ι => cond γ₁ I) := by
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.smul_apply, Measure.pi_pi, smul_eq_mul, ← Finset.card_univ, ← Finset.prod_const,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [cond_apply hI, Measure.restrict_apply (hs i), ← mul_assoc, ENNReal.mul_inv_cancel hpos (measure_ne_top _ _),
    one_mul, Set.inter_comm]

/-- **The cut-off**: `∫ 1_{I^ι} g d(γ₁^{⊗ι}) = γ₁(I)^{|ι|} ∫ g d(γ₁(· | I)^{⊗ι})`. -/
theorem lintegral_indicator_box_eq {I : Set ℝ} (hI : MeasurableSet I) (hpos : γ₁ I ≠ 0)
    (g : (ι → ℝ) → ℝ≥0∞) :
    ∫⁻ ξ, (Set.univ.pi fun _ : ι => I).indicator g ξ ∂(Measure.pi fun _ : ι => γ₁) =
      (γ₁ I) ^ Fintype.card ι * ∫⁻ ξ, g ξ ∂(Measure.pi fun _ : ι => cond γ₁ I) := by
  rw [lintegral_indicator (MeasurableSet.univ_pi fun _ => hI), Measure.restrict_pi_pi,
    pi_restrict_eq_smul_pi_cond γ₁ hI hpos, lintegral_smul_measure, smul_eq_mul]

end GaussianBlockSpin
