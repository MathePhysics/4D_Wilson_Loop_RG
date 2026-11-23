/-
`lem:localised-background` of BALABAN_CORE.tex (`a021c13be348`), the arithmetic of its proof.

* `star_bounds`: from `ε' ≤ a_⋆`, `8C_sB₃ε' ≤ 8C_sB₃a_⋆ = m_⋆`, and with `m_⋆ ≤ ε_⋆/L²`, `C_s ≥ 1`: the regularity
  constant of the averages `2L²B₃ε' ≤ ε_⋆`.
* `boundary_distance`: `20M_ca_{n+1} + a_n ≤ 21M_ca_{n+1}` for `a_n ≤ a_{n+1}`, `M_c ≥ 1`, and `a_n < 2a_{n+1}`.
-/
import Mathlib

noncomputable section

namespace CoreLean
namespace LocalisedBackgroundArith

/-- The bounds from the definition of `a_⋆`. -/
theorem star_bounds {Cs B₃ ε a εs L : ℝ} (hCs : 1 ≤ Cs) (hB : 0 ≤ B₃) (hε : 0 ≤ ε) (hεa : ε ≤ a) (hL : 0 < L)
    (hm : 8 * Cs * B₃ * a ≤ εs / L ^ 2) :
    8 * Cs * B₃ * ε ≤ 8 * Cs * B₃ * a ∧ 2 * L ^ 2 * B₃ * ε ≤ εs := by
  have hCB : 0 ≤ 8 * Cs * B₃ := by positivity
  have h1 : 8 * Cs * B₃ * ε ≤ 8 * Cs * B₃ * a := mul_le_mul_of_nonneg_left hεa hCB
  refine ⟨h1, ?_⟩
  have hL2 : 0 < L ^ 2 := by positivity
  have h2 : 8 * Cs * B₃ * ε * L ^ 2 ≤ εs := by
    have := (le_div_iff₀ hL2).1 (h1.trans hm)
    linarith
  have h3 : 2 * L ^ 2 * B₃ * ε ≤ 8 * Cs * B₃ * ε * L ^ 2 := by
    have : 0 ≤ L ^ 2 * B₃ * ε := by positivity
    nlinarith
  linarith

/-- `20M_ca_{n+1} + a_n ≤ 21M_ca_{n+1}` and `a_n < 2a_{n+1}`. -/
theorem boundary_distance {Mc an an1 : ℝ} (hMc : 1 ≤ Mc) (han0 : 0 ≤ an) (han : an ≤ an1) (han1 : 0 < an1) :
    20 * Mc * an1 + an ≤ 21 * Mc * an1 ∧ an < 2 * an1 := by
  refine ⟨by nlinarith, by linarith⟩

end LocalisedBackgroundArith
end CoreLean

end
