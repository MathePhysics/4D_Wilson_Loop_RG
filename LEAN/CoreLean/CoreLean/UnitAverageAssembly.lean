/-
`lem:unit-average-bond`(ii)–(iii) of BALABAN_CORE.tex (`a021c13be348`) assembled: for a remainder `𝒞` which is
analytic on the ball of the radius `r₀` of the forms, bounded there by `2`, and vanishes at `0` with its derivative
(the function `g` of the proof of (ii)), the bounds of `eq:unit-remainder` hold (`UnitRemainder.lean`), and the
equation `z = 𝒞(B - ιz)` has exactly one solution in the ball of the radius `a₇ = r₀²/(192L⁶)`, with
`‖z‖ ≤ 16‖B‖²/r₀²` (`unit_fixed_point_analytic`), for `‖ιz‖ ≤ 2L³‖z‖`, `L ≥ 1`, `0 < r₀ ≤ 1`, `‖B‖ ≤ a₇`.
-/
import CoreLean.UnitAverageBond
import CoreLean.UnitRemainder

open Metric

noncomputable section

namespace CoreLean
namespace UnitAverageBond

variable {Z F : Type*} [NormedAddCommGroup Z] [NormedSpace ℂ Z] [CompleteSpace Z] [NormedAddCommGroup F]
  [NormedSpace ℂ F]

/-- **(ii)–(iii)** for an analytic remainder. -/
theorem unit_fixed_point_analytic {L r₀ : ℝ} (hL : 1 ≤ L) (hr₀ : 0 < r₀) (hr₁ : r₀ ≤ 1) (ι : Z →L[ℝ] F)
    (hι : ∀ z, ‖ι z‖ ≤ 2 * L ^ 3 * ‖z‖) (𝒞 : F → Z) (hg : AnalyticOnNhd ℂ 𝒞 (ball 0 r₀))
    (hb : ∀ x ∈ ball (0 : F) r₀, ‖𝒞 x‖ ≤ 2) (h0 : 𝒞 0 = 0) (hD0 : HasFDerivAt 𝒞 (0 : F →L[ℂ] Z) 0) (B : F)
    (hB : ‖B‖ ≤ r₀ ^ 2 / (192 * L ^ 6)) :
    ∃ z : Z, (‖z‖ ≤ r₀ ^ 2 / (192 * L ^ 6) ∧ 𝒞 (B - ι z) = z) ∧
      (∀ z' : Z, ‖z'‖ ≤ r₀ ^ 2 / (192 * L ^ 6) ∧ 𝒞 (B - ι z') = z' → z' = z) ∧ ‖z‖ ≤ 16 * ‖B‖ ^ 2 / r₀ ^ 2 := by
  have hfd0 : fderiv ℂ 𝒞 0 = 0 := hD0.fderiv
  have hC : ∀ X, ‖X‖ ≤ r₀ / 4 → ‖𝒞 X‖ ≤ 4 * ‖X‖ ^ 2 / r₀ ^ 2 := fun X hX =>
    UnitRemainder.remainder_square hr₀ hg hb h0 hD0 (by rw [mem_ball, dist_zero_right]; linarith)
  have hCL : ∀ X X', ‖X‖ ≤ r₀ / 4 → ‖X'‖ ≤ r₀ / 4 →
      ‖𝒞 X - 𝒞 X'‖ ≤ 16 / r₀ ^ 2 * max ‖X‖ ‖X'‖ * ‖X - X'‖ := fun X X' hX hX' =>
    UnitRemainder.remainder_lipschitz hr₀ hg hb hfd0 hX hX'
  obtain ⟨z, ⟨hz, hfix⟩, huniq⟩ := unit_fixed_point hL hr₀ hr₁ ι hι 𝒞 hC hCL B hB
  exact ⟨z, ⟨hz, hfix⟩, fun z' hz' => huniq z' hz', unit_fixed_bound hL hr₀ hr₁ ι hι 𝒞 hC B hB hz hfix⟩

end UnitAverageBond
end CoreLean

end
