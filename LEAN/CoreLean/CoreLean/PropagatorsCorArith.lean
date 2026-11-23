/-
`cor:propagators` of BALABAN_CORE.tex (`a021c13be348`), the admissibility of `ā₀ = a_w` in its proof:
`a_w = min{c_sf, c''₄/(√NL²)}/(40L³)` with `c_sf = min{1/(32L), a_sf/(18L²)}` is at most `1/(32L)`, at most
`c''₄/(30√NL⁵)`, and at most `a_sf` (`aw_bounds`); and `M₁ ≥ LR₀M₀ ≥ LR_sfM_sf ≥ 21` (`M1_bound`).
-/
import Mathlib

noncomputable section

namespace CoreLean
namespace PropagatorsCorArith

/-- The three bounds of `a_w`. -/
theorem aw_bounds {L c₄ N asf : ℝ} (hL : 1 ≤ L) (hc₄ : 0 ≤ c₄) (hN : 0 < N) (hasf : 0 ≤ asf) :
    min (min (1 / (32 * L)) (asf / (18 * L ^ 2))) (c₄ / (Real.sqrt N * L ^ 2)) / (40 * L ^ 3) ≤ 1 / (32 * L) ∧
      min (min (1 / (32 * L)) (asf / (18 * L ^ 2))) (c₄ / (Real.sqrt N * L ^ 2)) / (40 * L ^ 3) ≤
        c₄ / (30 * Real.sqrt N * L ^ 5) ∧
      min (min (1 / (32 * L)) (asf / (18 * L ^ 2))) (c₄ / (Real.sqrt N * L ^ 2)) / (40 * L ^ 3) ≤ asf := by
  set m := min (min (1 / (32 * L)) (asf / (18 * L ^ 2))) (c₄ / (Real.sqrt N * L ^ 2))
  have hL0 : 0 < L := by linarith
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 hN
  have h40 : 1 ≤ 40 * L ^ 3 := by nlinarith [one_le_pow₀ hL (n := 3)]
  have hm0 : 0 ≤ m := le_min (le_min (by positivity) (by positivity)) (by positivity)
  have hdiv : m / (40 * L ^ 3) ≤ m := div_le_self hm0 h40
  refine ⟨hdiv.trans ((min_le_left _ _).trans (min_le_left _ _)), ?_, ?_⟩
  · have h1 : m ≤ c₄ / (Real.sqrt N * L ^ 2) := min_le_right _ _
    calc m / (40 * L ^ 3) ≤ c₄ / (Real.sqrt N * L ^ 2) / (40 * L ^ 3) :=
          div_le_div_of_nonneg_right h1 (by positivity)
      _ = c₄ / (40 * Real.sqrt N * L ^ 5) := by field_simp
      _ ≤ c₄ / (30 * Real.sqrt N * L ^ 5) := by
          apply div_le_div_of_nonneg_left hc₄ (by positivity); nlinarith [pow_pos hL0 5]
  · have h1 : m ≤ asf / (18 * L ^ 2) := (min_le_left _ _).trans (min_le_right _ _)
    have h2 : asf / (18 * L ^ 2) ≤ asf := div_le_self hasf (by nlinarith)
    exact hdiv.trans (h1.trans h2)

/-- `M₁ ≥ LR₀M₀ ≥ LR_sfM_sf ≥ 21` for `R_sf ≥ 21L`, `M_sf ≥ 1`, `L ≥ 1`. -/
theorem M1_bound {M₁ L R₀ M₀ Rsf Msf : ℝ} (hL : 1 ≤ L) (hM₁ : L * (R₀ * M₀) ≤ M₁) (hRM : Rsf * Msf ≤ R₀ * M₀)
    (hR : 21 * L ≤ Rsf) (hM : 1 ≤ Msf) : 21 ≤ M₁ := by
  have h1 : 21 ≤ Rsf * Msf := by nlinarith
  have h2 : 21 ≤ R₀ * M₀ := h1.trans hRM
  nlinarith

end PropagatorsCorArith
end CoreLean

end
