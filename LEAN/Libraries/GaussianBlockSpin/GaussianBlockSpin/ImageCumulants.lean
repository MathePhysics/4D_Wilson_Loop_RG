import GaussianBlockSpin.UnitScaleLaws
import GaussianBlockSpin.Cumulants

/-! Helpers for the two-field lemma:
* cumulantSum_map_of_measurable: truncated expectations under an image measure;
* norm_le_sqrt_card_mul: a vector of `EuclideanSpace ℝ (Fin N)` with components at most `b` has norm `≤ √N b`. -/

namespace GaussianBlockSpin

open MeasureTheory

/-- Truncated expectations under the image of a measure. -/
lemma cumulantSum_map_of_measurable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {f : Ω → Ω'} (hf : Measurable f) {V : Ω' → ℝ} (hV : Measurable V) (t : ℕ) :
    cumulantSum (μ.map f) V t = cumulantSum μ (fun ω => V (f ω)) t := by
  have hm : moments (μ.map f) V = moments μ (fun ω => V (f ω)) := by
    funext n
    unfold moments
    rw [integral_map hf.aemeasurable (hV.pow_const n).aestronglyMeasurable]
  unfold cumulantSum
  rw [hm]

/-- A vector with components at most `b` has norm at most `√N b`. -/
lemma norm_le_sqrt_card_mul {N : ℕ} (v : EuclideanSpace ℝ (Fin N)) {b : ℝ} (hb : ∀ j, |v j| ≤ b) :
    ‖v‖ ≤ Real.sqrt N * b := by
  rcases Nat.eq_zero_or_pos N with h | h
  · subst h
    simp [EuclideanSpace.norm_eq]
  have hb0 : 0 ≤ b := (abs_nonneg _).trans (hb ⟨0, h⟩)
  rw [EuclideanSpace.norm_eq]
  calc Real.sqrt (∑ j, ‖v j‖ ^ 2) ≤ Real.sqrt (∑ _j : Fin N, b ^ 2) := by
        refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun j _ => ?_)
        rw [Real.norm_eq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hb j) 2
    _ = Real.sqrt N * b := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Real.sqrt_mul (Nat.cast_nonneg _),
          Real.sqrt_sq hb0]

end GaussianBlockSpin
