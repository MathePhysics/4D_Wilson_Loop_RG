/-
`lem:box-gauge` of BALABAN_CORE.tex (`a021c13be348`), the arithmetic of its four cases, with `L ≥ 28` (this section),
`R₂ ≥ 1`, `(2R₂ + 1)M₁ ≤ 3M/L`, `2M₁ ≤ M`.

* `second_case`: `111Ma_n < 27Ma_{n+1}` for `a_{n+1} = La_n`.
* `third_case`: `104M/L ≤ 4M`, `(4R₂ + 3)M₁ ≤ (7/3)(2R₂ + 1)M₁ ≤ 7M/L`, and `7M < 27M`.
* `fourth_case`: `4M + 7M/L + 2M ≤ 7M`.
* `minimiser_condition`: `(107M + 2M₁)ε₁ ≤ 108Mε₁ ≤ 2a^v₁R₂M₁` for `ε₁ ≤ a^v₁R₂M₁/(54M)`.
-/
import Mathlib

noncomputable section

namespace CoreLean
namespace BoxGaugeArith

/-- `111Ma_n < 27M(La_n)` for `L ≥ 28`. -/
theorem second_case {M L a : ℝ} (hL : 28 ≤ L) (hM : 0 < M) (ha : 0 < a) : 111 * M * a < 27 * M * (L * a) := by
  have hMa : 0 < M * a := mul_pos hM ha
  nlinarith

/-- The third case. -/
theorem third_case {M L R₂ M₁ : ℝ} (hL : 28 ≤ L) (hM : 0 < M) (hR : 1 ≤ R₂) (hM₁ : 0 ≤ M₁)
    (h : (2 * R₂ + 1) * M₁ ≤ 3 * M / L) :
    104 * M / L ≤ 4 * M ∧ (4 * R₂ + 3) * M₁ ≤ 7 / 3 * ((2 * R₂ + 1) * M₁) ∧
      7 / 3 * ((2 * R₂ + 1) * M₁) ≤ 7 * M / L ∧ 7 * M < 27 * M := by
  have hL0 : 0 < L := by linarith
  refine ⟨?_, by nlinarith, ?_, by linarith⟩
  · rw [div_le_iff₀ hL0]; nlinarith
  · have : 7 / 3 * (3 * M / L) = 7 * M / L := by ring
    linarith

/-- The fourth case: `4M + 7M/L + 2M ≤ 7M` for `L ≥ 7`. -/
theorem fourth_case {M L : ℝ} (hL : 7 ≤ L) (hM : 0 ≤ M) : 4 * M + 7 * M / L + 2 * M ≤ 7 * M := by
  have hL0 : 0 < L := by linarith
  have : 7 * M / L ≤ M := by rw [div_le_iff₀ hL0]; nlinarith
  linarith

/-- The condition of `thm:minimiser`(iv). -/
theorem minimiser_condition {M M₁ ε av R₂ : ℝ} (hM : 0 < M) (hM₁ : 2 * M₁ ≤ M) (hε0 : 0 ≤ ε)
    (hε : ε ≤ av * R₂ * M₁ / (54 * M)) :
    (107 * M + 2 * M₁) * ε ≤ 108 * M * ε ∧ 108 * M * ε ≤ 2 * av * R₂ * M₁ := by
  have h : ε * (54 * M) ≤ av * R₂ * M₁ := (le_div_iff₀ (by positivity)).1 hε
  refine ⟨?_, by nlinarith⟩
  have : 107 * M + 2 * M₁ ≤ 108 * M := by linarith
  exact mul_le_mul_of_nonneg_right this hε0

end BoxGaugeArith
end CoreLean

end
