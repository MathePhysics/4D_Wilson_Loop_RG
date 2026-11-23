/-
`lem:critical-membership` of BALABAN_CORE.tex (`a021c13be348`), the scalings of its proof.

* `plaquette_scale`: for `0 < a_i ≤ a_j`, `α₀(a₀/a_j)² ≤ α₀(a₀/a_i)²` (the plaquettes on the layers `i ≤ j`).
* `derived_bounds`: for `0 < a_m ≤ a_j`, `α₀(a₀/a_j)² = (a_m/a_j)²α₀(a₀/a_m)² ≤ (a_m/a_j)α₀(a₀/a_m)²` and
  `(a_m/a_j)³α₀ ≤ (a_m/a_j)α₀`, which are the bounds `eq:pair-space-derived`.
-/
import Mathlib

noncomputable section

namespace CoreLean
namespace CriticalMembershipArith

/-- `α₀(a₀/a_j)² ≤ α₀(a₀/a_i)²` for `0 < a_i ≤ a_j`. -/
theorem plaquette_scale {α a₀ ai aj : ℝ} (hα : 0 ≤ α) (hai : 0 < ai) (hij : ai ≤ aj) :
    α * (a₀ / aj) ^ 2 ≤ α * (a₀ / ai) ^ 2 := by
  apply mul_le_mul_of_nonneg_left _ hα
  rw [div_pow, div_pow]
  exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (pow_le_pow_left₀ hai.le hij 2)

/-- **The bounds `eq:pair-space-derived`** for the derived configurations of `U`. -/
theorem derived_bounds {α a₀ am aj : ℝ} (hα : 0 ≤ α) (ham : 0 < am) (hmj : am ≤ aj) :
    α * (a₀ / aj) ^ 2 = (am / aj) ^ 2 * α * (a₀ / am) ^ 2 ∧
      (am / aj) ^ 2 * α * (a₀ / am) ^ 2 ≤ am / aj * α * (a₀ / am) ^ 2 ∧ (am / aj) ^ 3 * α ≤ am / aj * α := by
  have haj : 0 < aj := ham.trans_le hmj
  have hr0 : 0 ≤ am / aj := by positivity
  have hr1 : am / aj ≤ 1 := (div_le_one haj).2 hmj
  refine ⟨by field_simp, ?_, ?_⟩
  · have : (am / aj) ^ 2 ≤ am / aj := by nlinarith
    have h0 : 0 ≤ α * (a₀ / am) ^ 2 := by positivity
    nlinarith
  · have : (am / aj) ^ 3 ≤ am / aj := by
      have h2 : (am / aj) ^ 2 ≤ 1 := by nlinarith
      calc (am / aj) ^ 3 = am / aj * (am / aj) ^ 2 := by ring
        _ ≤ am / aj * 1 := mul_le_mul_of_nonneg_left h2 hr0
        _ = am / aj := mul_one _
    exact mul_le_mul_of_nonneg_right this hα

end CriticalMembershipArith
end CoreLean

end
