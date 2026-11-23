/-
`lem:unit-average-bond`(i) of BALABAN_CORE.tex (`a021c13be348`), the inverse of `q_c`, in abstract form. In a complete
normed ring with `‖1‖ = 1` (the linear maps of `𝔤^c`): if `‖E_c‖ ≤ ¼`, then `I + E_c` is invertible with
`‖(I + E_c)⁻¹‖ ≤ 4/3 ≤ 2` (`inverse_bound`); with `Lq_c = L^{-3}(I + E_c)Ad_u` and `Ad_u` an isometry with an
isometric inverse, `(Lq_c)⁻¹ = L³Ad_u⁻¹(I + E_c)⁻¹` and `‖(Lq_c)⁻¹‖ ≤ 2L³` (`q_inverse_bound`). The bound of `E_c`:
`8L³‖A‖_c/r₀² ≤ ¼` for `‖A‖_c ≤ r₀²/(32L³)` (`E_small`).
-/
import Mathlib

noncomputable section

namespace CoreLean
namespace UnitAverageQ

variable {R : Type*} [NormedRing R] [CompleteSpace R] [NormOneClass R]

lemma norm_pow_le_quarter {E : R} (hE : ‖E‖ ≤ 1 / 4) (n : ℕ) : ‖(-E) ^ n‖ ≤ (1 / 4) ^ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · calc ‖(-E) ^ n‖ ≤ ‖-E‖ ^ n := norm_pow_le' _ hn
      _ ≤ (1 / 4) ^ n := by rw [norm_neg]; exact pow_le_pow_left₀ (norm_nonneg _) hE n

/-- **`‖(I + E)⁻¹‖ ≤ 4/3`** for `‖E‖ ≤ ¼`, by the series of Neumann. -/
theorem inverse_bound {E : R} (hE : ‖E‖ ≤ 1 / 4) :
    ∃ V : R, (1 + E) * V = 1 ∧ V * (1 + E) = 1 ∧ ‖V‖ ≤ 4 / 3 := by
  have hlt : ‖-E‖ < 1 := by rw [norm_neg]; linarith
  refine ⟨∑' n : ℕ, (-E) ^ n, ?_, ?_, ?_⟩
  · have := mul_neg_geom_series (-E) hlt
    rwa [sub_neg_eq_add] at this
  · have := geom_series_mul_neg (-E) hlt
    rwa [sub_neg_eq_add] at this
  · have hs : Summable fun n : ℕ => (1 / 4 : ℝ) ^ n := summable_geometric_of_lt_one (by norm_num) (by norm_num)
    calc ‖∑' n : ℕ, (-E) ^ n‖ ≤ ∑' n : ℕ, (1 / 4 : ℝ) ^ n :=
          tsum_of_norm_bounded hs.hasSum (norm_pow_le_quarter hE)
      _ = 4 / 3 := by rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; norm_num

/-- **`‖(Lq_c)⁻¹‖ ≤ 2L³`**. -/
theorem q_inverse_bound [NormedAlgebra ℝ R] {E Ad Adinv : R} {L : ℝ} (hL : 0 < L) (hE : ‖E‖ ≤ 1 / 4) (hAd : Ad * Adinv = 1)
    (hAd' : Adinv * Ad = 1) (hAdn : ‖Adinv‖ ≤ 1) :
    ∃ W : R, ((L ^ 3)⁻¹ • ((1 + E) * Ad)) * W = 1 ∧ W * ((L ^ 3)⁻¹ • ((1 + E) * Ad)) = 1 ∧
      ‖W‖ ≤ 2 * L ^ 3 := by
  obtain ⟨V, hV1, hV2, hVn⟩ := inverse_bound hE
  have hL3 : (L ^ 3 : ℝ) ≠ 0 := by positivity
  refine ⟨L ^ 3 • (Adinv * V), ?_, ?_, ?_⟩
  · rw [smul_mul_smul_comm, inv_mul_cancel₀ hL3, one_smul, mul_assoc, ← mul_assoc Ad, hAd, one_mul, hV1]
  · rw [smul_mul_smul_comm, mul_inv_cancel₀ hL3, one_smul, mul_assoc, ← mul_assoc V, hV2, one_mul, hAd']
  · calc ‖L ^ 3 • (Adinv * V)‖ = L ^ 3 * ‖Adinv * V‖ := by
          rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      _ ≤ L ^ 3 * (‖Adinv‖ * ‖V‖) := mul_le_mul_of_nonneg_left (norm_mul_le _ _) (by positivity)
      _ ≤ L ^ 3 * (1 * (4 / 3)) := by gcongr
      _ ≤ 2 * L ^ 3 := by nlinarith [pow_pos hL 3]

/-- **The bound of `E_c`**: `8L³‖A‖/r₀² ≤ ¼` for `‖A‖ ≤ r₀²/(32L³)`. -/
theorem E_small {L r₀ nA : ℝ} (hL : 0 < L) (hr₀ : 0 < r₀) (hA : nA ≤ r₀ ^ 2 / (32 * L ^ 3)) :
    8 * L ^ 3 * nA / r₀ ^ 2 ≤ 1 / 4 := by
  rw [div_le_iff₀ (by positivity)]
  have : 8 * L ^ 3 * nA ≤ 8 * L ^ 3 * (r₀ ^ 2 / (32 * L ^ 3)) := mul_le_mul_of_nonneg_left hA (by positivity)
  calc 8 * L ^ 3 * nA ≤ 8 * L ^ 3 * (r₀ ^ 2 / (32 * L ^ 3)) := this
    _ = 1 / 4 * r₀ ^ 2 := by field_simp; ring

end UnitAverageQ
end CoreLean

end
