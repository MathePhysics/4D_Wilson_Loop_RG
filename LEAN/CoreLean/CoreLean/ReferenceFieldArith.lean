/-
`lem:reference-field` of BALABAN_CORE.tex (`a021c13be348`), the distance arithmetic of the proof of (i), from
`M_c ≥ LR₂M₁` (`eq:layer-condition`), `R₂ ≥ 1`, `L ≥ 3`.

* `first_fact`: `(2R₂ + 1)M₁ ≤ 3M_c/L`.
* `neighbourhood_x`: `4R₂M₁ ≤ 4M_c/L`, and `2LR₂ ≥ 4R₂`.
* `neighbourhood_plus`: `(4R₂ + 1)LM₁ ≤ 5M_c`.
* `class_cube`: `20M_c/L + 2M₁ ≤ 22M_c/L` and `(24/L + 2)M_c ≤ 10M_c`.
-/
import Mathlib

noncomputable section

namespace CoreLean
namespace ReferenceFieldArith

variable {L R₂ M₁ Mc : ℝ}

/-- `(2R₂ + 1)M₁ ≤ 3M_c/L`. -/
theorem first_fact (hL : 0 < L) (hR : 1 ≤ R₂) (hM : 0 ≤ M₁) (h : L * R₂ * M₁ ≤ Mc) :
    (2 * R₂ + 1) * M₁ ≤ 3 * Mc / L := by
  rw [le_div_iff₀ hL]
  have : (2 * R₂ + 1) * M₁ ≤ 3 * (R₂ * M₁) := by nlinarith
  nlinarith

/-- `4R₂M₁ ≤ 4M_c/L` and `2LR₂ ≥ 4R₂` for `L ≥ 2`. -/
theorem neighbourhood_x (hL : 2 ≤ L) (hR : 0 ≤ R₂) (h : L * R₂ * M₁ ≤ Mc) :
    4 * R₂ * M₁ ≤ 4 * Mc / L ∧ 4 * R₂ ≤ 2 * L * R₂ := by
  have hL0 : 0 < L := by linarith
  refine ⟨?_, by nlinarith⟩
  rw [le_div_iff₀ hL0]; nlinarith

/-- `(4R₂ + 1)LM₁ ≤ 5M_c`. -/
theorem neighbourhood_plus (hL : 0 ≤ L) (hR : 1 ≤ R₂) (hM : 0 ≤ M₁) (h : L * R₂ * M₁ ≤ Mc) :
    (4 * R₂ + 1) * L * M₁ ≤ 5 * Mc := by
  have h1 : L * M₁ ≤ L * R₂ * M₁ := by nlinarith [mul_nonneg hL hM]
  nlinarith

/-- `20M_c/L + 2M₁ ≤ 22M_c/L` and `(24/L + 2)M_c ≤ 10M_c` for `L ≥ 3`. -/
theorem class_cube (hL : 3 ≤ L) (hR : 1 ≤ R₂) (hM : 0 ≤ M₁) (hMc : 0 ≤ Mc) (h : L * R₂ * M₁ ≤ Mc) :
    20 * Mc / L + 2 * M₁ ≤ 22 * Mc / L ∧ (24 / L + 2) * Mc ≤ 10 * Mc := by
  have hL0 : 0 < L := by linarith
  refine ⟨?_, ?_⟩
  · have hLM : L * M₁ ≤ Mc := by nlinarith [mul_nonneg hL0.le hM]
    have e : 22 * Mc / L = 20 * Mc / L + 2 * (Mc / L) := by ring
    rw [e]
    have : M₁ ≤ Mc / L := by rw [le_div_iff₀ hL0]; linarith
    linarith
  · have : 24 / L ≤ 8 := by rw [div_le_iff₀ hL0]; linarith
    nlinarith

end ReferenceFieldArith
end CoreLean

end
