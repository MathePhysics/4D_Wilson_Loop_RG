/-
`lem:block-extension` of BALABAN_CORE.tex (`a021c13be348`), the arithmetic of its proof, with `s = α + α₁`.

* `d_bound`: `16s + 16(2 + C_χ)s = 16(3 + C_χ)s < 16(3 + C_χ)c` for `s < c` ((d)).
* `regular_constant`: with `a_n ≤ La_j`, `a_n‖𝐁‖ ≤ 16Ls` and `a_n²‖∇𝐁‖ ≤ 16(2 + C_χ)L²s`, both at most `C_Es` with
  `C_E = 16(2 + C_χ)L²` ((b)).
* `cube_admissible`: `(L + L²)α₁^♭ ≤ 2L²α₁^♭ < c_cube` for `L ≥ 1` and `2L²α₁^♭ < c_cube`.
-/
import Mathlib

noncomputable section

namespace CoreLean
namespace BlockExtensionArith

/-- (d): `16s + 16(2 + C_χ)s < 16(3 + C_χ)c`. -/
theorem d_bound {s c Cχ : ℝ} (hC : 0 ≤ Cχ) (hs : s < c) : 16 * s + 16 * (2 + Cχ) * s < 16 * (3 + Cχ) * c := by
  have : 16 * s + 16 * (2 + Cχ) * s = 16 * (3 + Cχ) * s := by ring
  rw [this]
  exact mul_lt_mul_of_pos_left hs (by positivity)

/-- (b): the constant of `eq:regular-complex` in the units of the scales of the points. -/
theorem regular_constant {an aj L Cχ s nB nD : ℝ} (hL : 1 ≤ L) (hC : 0 ≤ Cχ) (hs : 0 ≤ s) (haj : 0 ≤ aj)
    (han0 : 0 ≤ an) (han : an ≤ L * aj) (hB : 0 ≤ nB) (hD : 0 ≤ nD) (h1 : aj * nB ≤ 16 * s)
    (h2 : aj ^ 2 * nD ≤ 16 * (2 + Cχ) * s) :
    an * nB ≤ 16 * (2 + Cχ) * L ^ 2 * s ∧ an ^ 2 * nD ≤ 16 * (2 + Cχ) * L ^ 2 * s := by
  have hL0 : 0 ≤ L := by linarith
  refine ⟨?_, ?_⟩
  · calc an * nB ≤ L * aj * nB := mul_le_mul_of_nonneg_right han hB
      _ = L * (aj * nB) := by ring
      _ ≤ L * (16 * s) := mul_le_mul_of_nonneg_left h1 hL0
      _ ≤ 16 * (2 + Cχ) * L ^ 2 * s := by
          have hL2 : L ≤ (2 + Cχ) * L ^ 2 := by nlinarith
          have := mul_le_mul_of_nonneg_right hL2 (by positivity : (0 : ℝ) ≤ 16 * s)
          nlinarith
  · have hsq : an ^ 2 ≤ (L * aj) ^ 2 := pow_le_pow_left₀ han0 han 2
    calc an ^ 2 * nD ≤ (L * aj) ^ 2 * nD := mul_le_mul_of_nonneg_right hsq hD
      _ = L ^ 2 * (aj ^ 2 * nD) := by ring
      _ ≤ L ^ 2 * (16 * (2 + Cχ) * s) := mul_le_mul_of_nonneg_left h2 (sq_nonneg L)
      _ = 16 * (2 + Cχ) * L ^ 2 * s := by ring

/-- `(L + L²)α₁^♭ ≤ 2L²α₁^♭ < c_cube`. -/
theorem cube_admissible {L α c : ℝ} (hL : 1 ≤ L) (hα : 0 ≤ α) (h : 2 * L ^ 2 * α < c) :
    (L + L ^ 2) * α < c := by
  have : L + L ^ 2 ≤ 2 * L ^ 2 := by nlinarith
  have := mul_le_mul_of_nonneg_right this hα
  linarith

end BlockExtensionArith
end CoreLean

end
