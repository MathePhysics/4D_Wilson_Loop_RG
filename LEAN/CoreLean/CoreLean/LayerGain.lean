/-
`lem:layer-gain` of BALABAN_CORE.tex (`a021c13be348`), the arithmetic of its proof. With `k = m - j ≥ 1`, a weighted
distance `d ≥ 27M_c(k - 1)` (`lem:distance`(ii)), `δ₂/2 ≥ 2δ_⋆`, and `27δ_⋆M_c ≥ 8 log L` (the second condition of
`eq:layer-condition`): `e^{-(δ₂/2)d} ≤ L^{-8(k-1)}e^{-δ_⋆d}` (`exp_gain`), and with the factor `L^{3k}` of the passage
from the unit `a_j` to `a_m = L^ka_j`, `L^{3k}e^{-(δ₂/2)d} ≤ L⁸(L^{-k})⁵e^{-δ_⋆d}` (`layer_gain`), which is the factor
`L⁸(a_j/a_m)⁵` of `eq:layer-gain`.
-/
import Mathlib

noncomputable section

namespace CoreLean
namespace LayerGain

/-- `e^{-(δ₂/2)d} ≤ L^{-8(k-1)}e^{-δ_⋆d}`. -/
theorem exp_gain {L δ₂ δs Mc d : ℝ} {k : ℕ} (hL : 1 ≤ L) (hk : 1 ≤ k) (hδs : 0 ≤ δs) (hδ : 2 * δs ≤ δ₂ / 2)
    (hd0 : 0 ≤ d) (hd : 27 * Mc * ((k : ℝ) - 1) ≤ d) (hcond : 8 * Real.log L ≤ 27 * δs * Mc) :
    Real.exp (-(δ₂ / 2) * d) ≤ (L ^ (k - 1))⁻¹ ^ 8 * Real.exp (-δs * d) := by
  have hL0 : 0 < L := by linarith
  have hk1 : (0 : ℝ) ≤ (k : ℝ) - 1 := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hX : 0 < (L ^ (k - 1))⁻¹ ^ 8 := by positivity
  rw [← Real.exp_log hX, ← Real.exp_add, Real.exp_le_exp, Real.log_pow, Real.log_inv, Real.log_pow]
  push_cast [Nat.cast_sub hk]
  have h1 : δs * (27 * Mc * ((k : ℝ) - 1)) ≤ δs * d := mul_le_mul_of_nonneg_left hd hδs
  have h2 : 8 * Real.log L * ((k : ℝ) - 1) ≤ 27 * δs * Mc * ((k : ℝ) - 1) :=
    mul_le_mul_of_nonneg_right hcond hk1
  have h3 : 2 * δs * d ≤ δ₂ / 2 * d := mul_le_mul_of_nonneg_right hδ hd0
  nlinarith

/-- **`eq:layer-gain`**, the factor: `L^{3k}e^{-(δ₂/2)d} ≤ L⁸(L^{-k})⁵e^{-δ_⋆d}`. -/
theorem layer_gain {L δ₂ δs Mc d : ℝ} {k : ℕ} (hL : 1 ≤ L) (hk : 1 ≤ k) (hδs : 0 ≤ δs)
    (hδ : 2 * δs ≤ δ₂ / 2) (hd0 : 0 ≤ d) (hd : 27 * Mc * ((k : ℝ) - 1) ≤ d)
    (hcond : 8 * Real.log L ≤ 27 * δs * Mc) :
    L ^ (3 * k) * Real.exp (-(δ₂ / 2) * d) ≤ L ^ 8 * ((L ^ k)⁻¹) ^ 5 * Real.exp (-δs * d) := by
  have hL0 : 0 < L := by linarith
  have h := exp_gain hL hk hδs hδ hd0 hd hcond
  have e : L ^ (3 * k) * ((L ^ (k - 1))⁻¹ ^ 8) = L ^ 8 * ((L ^ k)⁻¹) ^ 5 := by
    obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    field_simp
    ring
  calc L ^ (3 * k) * Real.exp (-(δ₂ / 2) * d) ≤ L ^ (3 * k) * ((L ^ (k - 1))⁻¹ ^ 8 * Real.exp (-δs * d)) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = L ^ 8 * ((L ^ k)⁻¹) ^ 5 * Real.exp (-δs * d) := by rw [← mul_assoc, e]

end LayerGain
end CoreLean

end
