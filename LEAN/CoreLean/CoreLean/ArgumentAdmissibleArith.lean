/-
`lem:argument-admissible` of BALABAN_CORE.tex (`a021c13be348`), the arithmetic of the second entry in its proof (this
part of the core takes `L ≥ 28`).

* `weighted_sum`: `2(L² + 3L³)γ₀ + L³γ₀ ≤ (15/2)L³γ₀` for `L ≥ 4` (it fails for `L = 3`, see `weighted_sum_three`).
* `moduli_and_p`: for `α₁ ≤ 1/48`, `L ≥ 1`: `16α₁L²γ₀ ≤ ½L³γ₀` and `40α₁L²γ₀ ≤ L³γ₀`.
* `total`: `(15/2 + 1/2 + 1)L³γ₀ = 9L³γ₀ < γ` from `16L³γ₀ < γ`, `γ₀ ≥ 0` with `L³γ₀ > 0`.
* `unit_change`: `a_j ≤ La` turns `a‖A‖, a²‖∇A‖ ≤ x` into `a_j‖A‖, a_j²‖∇A‖ ≤ L²x` (for `α = 2L²B'₂M^F_⋆t` and
  `α₁ = L²n'`).
-/
import Mathlib

noncomputable section

namespace CoreLean
namespace ArgumentAdmissibleArith

/-- `2(L² + 3L³)γ₀ + L³γ₀ ≤ (15/2)L³γ₀` for `L ≥ 4`. -/
theorem weighted_sum {L γ : ℝ} (hL : 4 ≤ L) (hγ : 0 ≤ γ) : 2 * (L ^ 2 + 3 * L ^ 3) * γ + L ^ 3 * γ ≤ 15 / 2 * L ^ 3 * γ := by
  have h : 2 * L ^ 2 ≤ 1 / 2 * L ^ 3 := by nlinarith
  nlinarith

/-- For `L = 3` the inequality fails (`207 > 202.5`); the section's `L ≥ 28` is needed. -/
theorem weighted_sum_three : 15 / 2 * (3 : ℝ) ^ 3 < 2 * (3 ^ 2 + 3 * 3 ^ 3) + 3 ^ 3 := by norm_num

/-- `16α₁L²γ₀ ≤ ½L³γ₀` and `40α₁L²γ₀ ≤ L³γ₀` for `α₁ ≤ 1/48`, `L ≥ 1`. -/
theorem moduli_and_p {α L γ : ℝ} (hα0 : 0 ≤ α) (hα : α ≤ 1 / 48) (hL : 1 ≤ L) (hγ : 0 ≤ γ) :
    16 * α * L ^ 2 * γ ≤ 1 / 2 * L ^ 3 * γ ∧ 40 * α * L ^ 2 * γ ≤ L ^ 3 * γ := by
  have hL2γ : 0 ≤ L ^ 2 * γ := by positivity
  have e3 : L ^ 3 * γ = L * (L ^ 2 * γ) := by ring
  refine ⟨?_, ?_⟩
  · have : 16 * α ≤ 1 / 2 * L := by linarith
    nlinarith
  · have : 40 * α ≤ L := by linarith
    nlinarith

/-- `9L³γ₀ < γ` from `16L³γ₀ < γ`. -/
theorem total {L γ₀ γ : ℝ} (hpos : 0 ≤ L ^ 3 * γ₀) (h : 16 * (L ^ 3 * γ₀) < γ) :
    (15 / 2 + 1 / 2 + 1) * (L ^ 3 * γ₀) < γ := by nlinarith

/-- The change of the unit: `a_j ≤ La`, `L ≥ 1`. -/
theorem unit_change {aj a L nA nD x : ℝ} (hL : 1 ≤ L) (ha : 0 ≤ a) (haj0 : 0 ≤ aj) (haj : aj ≤ L * a) (hA : 0 ≤ nA)
    (hD : 0 ≤ nD) (h1 : a * nA ≤ x) (h2 : a ^ 2 * nD ≤ x) : aj * nA ≤ L ^ 2 * x ∧ aj ^ 2 * nD ≤ L ^ 2 * x := by
  have hx : 0 ≤ x := le_trans (by positivity) h1
  refine ⟨?_, ?_⟩
  · calc aj * nA ≤ L * a * nA := mul_le_mul_of_nonneg_right haj hA
      _ = L * (a * nA) := by ring
      _ ≤ L * x := mul_le_mul_of_nonneg_left h1 (by linarith)
      _ ≤ L ^ 2 * x := by
          have : L ≤ L ^ 2 := by nlinarith
          exact mul_le_mul_of_nonneg_right this hx
  · have hsq : aj ^ 2 ≤ (L * a) ^ 2 := pow_le_pow_left₀ haj0 haj 2
    calc aj ^ 2 * nD ≤ (L * a) ^ 2 * nD := mul_le_mul_of_nonneg_right hsq hD
      _ = L ^ 2 * (a ^ 2 * nD) := by ring
      _ ≤ L ^ 2 * x := mul_le_mul_of_nonneg_left h2 (sq_nonneg L)

end ArgumentAdmissibleArith
end CoreLean

end
