/-
`lem:reference-setting` of BALABAN_CORE.tex (`a021c13be348`), the arithmetic of its proof.

* `separation_product`: `R₁M₁ ≤ M_c/L` (`eq:layer-condition`) gives `27M_c ≥ 27LR₁M₁ ≥ 6LR₁M₁`.
* `neighbourhood`: `(21 + 5R₁)M₁ ≤ 6R₁M₁ ≤ M_c` for `R₁ ≥ 21` and `6R₁M₁ ≤ M_c`, and a point within `4a₀` of `Y'` has
  its neighbourhood of radius `(20 + 5R₁)M₁a_j ≤ (20 + 5R₁)M₁a_n` within `(21 + 5R₁)M₁a_n ≤ M_ca_n` of `Y'`, for
  `M₁ ≥ 4`, `a₀ ≤ a_j ≤ a_n`.
-/
import Mathlib

noncomputable section

namespace CoreLean
namespace ReferenceSettingArith

/-- `27M_c ≥ 6LR₁M₁` from `R₁M₁ ≤ M_c/L`. -/
theorem separation_product {R₁ M₁ Mc L : ℝ} (hL : 0 < L) (hRM : 0 ≤ R₁ * M₁) (h : R₁ * M₁ ≤ Mc / L) :
    6 * L * R₁ * M₁ ≤ 27 * Mc := by
  have h1 : L * (R₁ * M₁) ≤ Mc := by rw [le_div_iff₀ hL] at h; linarith
  nlinarith

/-- **The neighbourhood**: `4a₀ + (20 + 5R₁)M₁a_j ≤ (21 + 5R₁)M₁a_n ≤ 6R₁M₁a_n ≤ M_ca_n`. -/
theorem neighbourhood {R₁ M₁ Mc a₀ aj an : ℝ} (hR : 21 ≤ R₁) (hM : 4 ≤ M₁) (h6 : 6 * R₁ * M₁ ≤ Mc)
    (ha₀ : 0 ≤ a₀) (h0j : a₀ ≤ aj) (hjn : aj ≤ an) :
    4 * a₀ + (20 + 5 * R₁) * M₁ * aj ≤ (21 + 5 * R₁) * M₁ * an ∧ (21 + 5 * R₁) * M₁ ≤ 6 * R₁ * M₁ ∧
      (21 + 5 * R₁) * M₁ * an ≤ Mc * an := by
  have hM0 : 0 ≤ M₁ := by linarith
  have han : 0 ≤ an := ha₀.trans (h0j.trans hjn)
  have hR1 : (21 + 5 * R₁) * M₁ ≤ 6 * R₁ * M₁ := by nlinarith
  refine ⟨?_, hR1, mul_le_mul_of_nonneg_right (hR1.trans h6) han⟩
  have h1 : 4 * a₀ ≤ M₁ * an := by nlinarith
  have h2 : (20 + 5 * R₁) * M₁ * aj ≤ (20 + 5 * R₁) * M₁ * an :=
    mul_le_mul_of_nonneg_left hjn (by nlinarith)
  nlinarith

end ReferenceSettingArith
end CoreLean

end
