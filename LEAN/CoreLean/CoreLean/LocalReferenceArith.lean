/-
`lem:local-reference` of BALABAN_CORE.tex (`a021c13be348`), the arithmetic of its proof, from `M_c ≥ LR₂M₁`,
`R₂ ≥ R₁ ≥ 1`, `C_R = 9B'₂L³R₁M₁`, `c_R = c'₅/(22L³M_c)`.

* `unit_gauges`: `(2R₁ + 2)M₁ ≤ 5M_c/L`, and `9B'₂M₁L³α ≤ C_Rα`.
* `class_cubes`: `s_C + 2M₁ ≤ 22M_c ≤ 2.2s_C` (in units of `a_{j'}`) for `10M_c ≤ s_C ≤ 20M_c`, and
  `2.2B'₂L³α ≤ C_Rα` for `R₁M₁ ≥ 1`.
* `landau_condition`: `M'L³α ≤ 22M_cL³c_R = c'₅` for `M' ≤ 22M_c`, `α ≤ c_R`.
-/
import Mathlib

noncomputable section

namespace CoreLean
namespace LocalReferenceArith

/-- The gauges of the units. -/
theorem unit_gauges {L R₁ R₂ M₁ Mc B α : ℝ} (hL : 0 < L) (hR₁ : 1 ≤ R₁) (hR : R₁ ≤ R₂) (hM : 0 ≤ M₁)
    (h : L * R₂ * M₁ ≤ Mc) (hB : 0 ≤ B) (hα : 0 ≤ α) :
    (2 * R₁ + 2) * M₁ ≤ 5 * Mc / L ∧ 9 * B * M₁ * L ^ 3 * α ≤ 9 * B * L ^ 3 * R₁ * M₁ * α := by
  refine ⟨?_, ?_⟩
  · rw [le_div_iff₀ hL]
    have h1 : (2 * R₁ + 2) * M₁ ≤ 4 * (R₂ * M₁) := by nlinarith
    have h2 : (2 * R₁ + 2) * M₁ * L ≤ 4 * (R₂ * M₁) * L := mul_le_mul_of_nonneg_right h1 hL.le
    have h3 : 4 * (R₂ * M₁) * L = 4 * (L * R₂ * M₁) := by ring
    have hR₂ : 0 ≤ R₂ := by linarith
    have hMc : 0 ≤ Mc := le_trans (mul_nonneg (mul_nonneg hL.le hR₂) hM) h
    nlinarith
  · have : M₁ ≤ R₁ * M₁ := le_mul_of_one_le_left hM hR₁
    have h0 : 0 ≤ 9 * B * L ^ 3 * α := by positivity
    nlinarith

/-- The cubes of the class. -/
theorem class_cubes {s M₁ Mc B L R₁ α : ℝ} (_hM : 0 ≤ M₁) (hMMc : M₁ ≤ Mc) (hs1 : 10 * Mc ≤ s) (hs2 : s ≤ 20 * Mc)
    (hB : 0 ≤ B) (hL : 0 ≤ L) (hα : 0 ≤ α) (hRM : 1 ≤ R₁ * M₁) :
    s + 2 * M₁ ≤ 22 * Mc ∧ 22 * Mc ≤ 2.2 * s ∧ 2.2 * B * L ^ 3 * α ≤ 9 * B * L ^ 3 * R₁ * M₁ * α := by
  refine ⟨by linarith, by linarith, ?_⟩
  have h0 : 0 ≤ B * L ^ 3 * α := by positivity
  nlinarith

/-- The condition of `prop:landau-variants`: `M'L³α ≤ c'₅`. -/
theorem landau_condition {M' Mc L α c₅ : ℝ} (hMc : 0 < Mc) (hL : 0 < L) (hM' : M' ≤ 22 * Mc) (hα0 : 0 ≤ α)
    (hα : α ≤ c₅ / (22 * L ^ 3 * Mc)) : M' * L ^ 3 * α ≤ c₅ := by
  have hD : 0 < 22 * L ^ 3 * Mc := by positivity
  have h1 : α * (22 * L ^ 3 * Mc) ≤ c₅ := (le_div_iff₀ hD).1 hα
  have hL3 : 0 ≤ L ^ 3 * α := by positivity
  nlinarith

end LocalReferenceArith
end CoreLean

end
