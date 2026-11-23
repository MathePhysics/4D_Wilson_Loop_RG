/-
`thm:support` of BALABAN_CORE.tex (`a021c13be348`), the arithmetic of its proof (lengths in units of `a₀`, `a₁ = La₀`).

* `inner_domain`: from `R₂ ≥ L(20 + 5R₁) + 6`, `L ≥ 2`, `M₁ ≥ L`, `R₁ ≥ 0`:
  `LR₂M₁ ≥ (27 + 5R₁)M₁ ≥ (22 + 5R₁)M₁ + 5L`, hence `R₂M₁a₁ - 5a₁ - M₁a₀ ≥ (21 + 5R₁)M₁a₀`: the cube `Q_y` of a
  site within `5a₁` of `Ω₁` lies in `W°`.
* `set_N_zero`: `(20 + 5R₁)M₁ + 4 < (21 + 5R₁)M₁` for `M₁ > 4` (the case `j = 0` of the set `𝒩`).
* `set_N_one`: `20 + 5R₁ ≤ R₂` (the case `j = 1`).
* `set_N_high`: `L(20 + 5R₁)M₁ < RM₁` for `R ≥ R₂` (the case `j ≥ 2`).
* `product_N`: `RM₁ ≥ R₂M₁ ≥ 6LR₁M₁` when `R₂ ≥ 6LR₁`.
-/
import Mathlib

noncomputable section

namespace CoreLean
namespace SupportArith

variable {L R₁ R₂ M₁ : ℝ}

/-- **The inner domain**: `R₂M₁a₁ - 5a₁ - M₁a₀ ≥ (21 + 5R₁)M₁a₀` with `a₁ = La₀`. -/
theorem inner_domain (hL : 2 ≤ L) (hM : L ≤ M₁) (hR₁ : 0 ≤ R₁) (hR₂ : L * (20 + 5 * R₁) + 6 ≤ R₂) :
    (27 + 5 * R₁) * M₁ ≤ L * R₂ * M₁ ∧ (22 + 5 * R₁) * M₁ + 5 * L ≤ (27 + 5 * R₁) * M₁ ∧
      (21 + 5 * R₁) * M₁ ≤ R₂ * M₁ * L - 5 * L - M₁ := by
  have hM0 : 0 ≤ M₁ := by linarith
  have hLR : 27 + 5 * R₁ ≤ L * R₂ := by
    have h1 : L * (L * (20 + 5 * R₁) + 6) ≤ L * R₂ := mul_le_mul_of_nonneg_left hR₂ (by linarith)
    have h2 : 2 * (20 + 5 * R₁) ≤ L * (20 + 5 * R₁) := mul_le_mul_of_nonneg_right hL (by linarith)
    nlinarith
  have h1 : (27 + 5 * R₁) * M₁ ≤ L * R₂ * M₁ := mul_le_mul_of_nonneg_right hLR hM0
  have h2 : (22 + 5 * R₁) * M₁ + 5 * L ≤ (27 + 5 * R₁) * M₁ := by nlinarith
  refine ⟨h1, h2, ?_⟩
  nlinarith

/-- The case `j = 0` of the set `𝒩`: `(20 + 5R₁)M₁ + 4 < (21 + 5R₁)M₁` for `M₁ > 4`. -/
theorem set_N_zero (hM : 4 < M₁) : (20 + 5 * R₁) * M₁ + 4 < (21 + 5 * R₁) * M₁ := by nlinarith

/-- The case `j = 1`: `20 + 5R₁ ≤ R₂`. -/
theorem set_N_one (hL : 2 ≤ L) (hR₁ : 0 ≤ R₁) (hR₂ : L * (20 + 5 * R₁) + 6 ≤ R₂) : 20 + 5 * R₁ ≤ R₂ := by
  nlinarith

/-- The case `j ≥ 2`: `L(20 + 5R₁)M₁ < RM₁` for `R ≥ R₂ ≥ L(20 + 5R₁) + 6`, `M₁ > 0`. -/
theorem set_N_high {R : ℝ} (hM : 0 < M₁) (hR₂ : L * (20 + 5 * R₁) + 6 ≤ R₂) (hR : R₂ ≤ R) :
    L * (20 + 5 * R₁) * M₁ < R * M₁ := by
  have : L * (20 + 5 * R₁) < R := by linarith
  exact mul_lt_mul_of_pos_right this hM

/-- `RM₁ ≥ R₂M₁ ≥ 6LR₁M₁`. -/
theorem product_N {R : ℝ} (hM : 0 ≤ M₁) (hR : R₂ ≤ R) (h6 : 6 * L * R₁ ≤ R₂) :
    6 * L * R₁ * M₁ ≤ R₂ * M₁ ∧ R₂ * M₁ ≤ R * M₁ :=
  ⟨mul_le_mul_of_nonneg_right h6 hM, mul_le_mul_of_nonneg_right hR hM⟩

end SupportArith
end CoreLean

end
