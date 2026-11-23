/-
`thm:fluctuation-coordinates` of BALABAN_CORE.tex (`a021c13be348`), the bounds at the beginning of its proof. With
`CB̃ = B̃ - hLQ̃B̃`, `‖LQ̃B̃‖ ≤ C_ul‖B̃‖` and `‖h‖ ≤ 2L³` (`prop:unit-linearising`(i)), `‖B̃‖ ≤ a₈` and
`(2 + 4L³C_ul)a₈ ≤ a₇` (`eq:coordinates-constant`): `‖CB̃‖ ≤ (1 + 2L³C_ul)‖B̃‖ ≤ ½a₇` (`coordinates_C`); and with
`‖D̃(CB̃)‖ ≤ C_ul‖CB̃‖²` and `12L³C_ula₇ ≤ 1`, `‖B'‖ ≤ ½a₇ + 2L³C_ula₇² ≤ a₇` for `B' = CB̃ - hD̃(CB̃)`
(`coordinates_B'`).
-/
import Mathlib

noncomputable section

namespace CoreLean
namespace FluctuationCoordinates

/-- `‖CB̃‖ ≤ (1 + 2L³C_ul)‖B̃‖ ≤ ½a₇`. -/
theorem coordinates_C {L Cul a7 a8 nB nC : ℝ} (hL : 0 ≤ L) (hC : 0 ≤ Cul) (hB : nB ≤ a8) (hB0 : 0 ≤ nB)
    (hnC : nC ≤ nB + 2 * L ^ 3 * (Cul * nB)) (ha : (2 + 4 * L ^ 3 * Cul) * a8 ≤ a7) :
    nC ≤ (1 + 2 * L ^ 3 * Cul) * nB ∧ nC ≤ a7 / 2 := by
  have h1 : nC ≤ (1 + 2 * L ^ 3 * Cul) * nB := by nlinarith
  refine ⟨h1, h1.trans ?_⟩
  have h2 : 0 ≤ 1 + 2 * L ^ 3 * Cul := by positivity
  calc (1 + 2 * L ^ 3 * Cul) * nB ≤ (1 + 2 * L ^ 3 * Cul) * a8 := mul_le_mul_of_nonneg_left hB h2
    _ = (2 + 4 * L ^ 3 * Cul) * a8 / 2 := by ring
    _ ≤ a7 / 2 := by linarith

/-- `‖B'‖ ≤ ½a₇ + 2L³C_ula₇² ≤ a₇`. -/
theorem coordinates_B' {L Cul a7 nC nD nB' : ℝ} (hL : 0 ≤ L) (hC : 0 ≤ Cul) (ha7 : 0 ≤ a7) (hnC0 : 0 ≤ nC)
    (hnC : nC ≤ a7 / 2) (hD : nD ≤ Cul * nC ^ 2) (hB' : nB' ≤ nC + 2 * L ^ 3 * nD)
    (hsmall : 12 * L ^ 3 * Cul * a7 ≤ 1) : nB' ≤ a7 := by
  have h1 : nC ^ 2 ≤ a7 ^ 2 := by
    have : nC ≤ a7 := by linarith
    exact pow_le_pow_left₀ hnC0 this 2
  have h2 : 2 * L ^ 3 * nD ≤ 2 * L ^ 3 * (Cul * a7 ^ 2) := by
    have h3 : nD ≤ Cul * a7 ^ 2 := hD.trans (mul_le_mul_of_nonneg_left h1 hC)
    exact mul_le_mul_of_nonneg_left h3 (by positivity)
  have h4 : 2 * L ^ 3 * (Cul * a7 ^ 2) ≤ a7 / 6 := by
    have : 2 * L ^ 3 * (Cul * a7 ^ 2) = (12 * L ^ 3 * Cul * a7) * a7 / 6 := by ring
    rw [this]
    have := mul_le_mul_of_nonneg_right hsmall ha7
    linarith
  linarith

end FluctuationCoordinates
end CoreLean

end
