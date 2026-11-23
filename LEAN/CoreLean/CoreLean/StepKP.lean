/-
`cor:step-kp` of BALABAN_CORE.tex (`a021c13be348`), its proof. With `κ₂ = 2^{10}(3 log 2 + 1)` and
`κ_vac = 2^9(1 + 16 log 2)`: `10κ₂ ≥ κ_vac` (`kappa_vac_le`), so that `κ ≥ 10κ₂` gives `κ ≥ κ_vac`; and
`|𝖧(Z)| ≤ C₁₁ε^f e^{-(1 + δ_L)κd} ≤ e^{-5κ}e^{-κd}` when `C₁₁ε^f ≤ e^{-5κ}` (`kp_bound`), which is
`eq:vacuum-activity-bound`, the hypothesis of `lem:fluctuation-kp` (`ClusterFluct.lean`).
-/
import Mathlib

noncomputable section

namespace CoreLean
namespace StepKP

/-- `10κ₂ = 2^9·20(3 log 2 + 1) ≥ 2^9(1 + 16 log 2) = κ_vac`. -/
theorem kappa_vac_le : 2 ^ 9 * (1 + 16 * Real.log 2) ≤ 10 * (2 ^ 10 * (3 * Real.log 2 + 1)) := by
  have h : 0 < Real.log 2 := Real.log_pos (by norm_num)
  nlinarith

/-- The activity bound: `|𝖧| ≤ C₁₁ε^f e^{-(1 + δ_L)κd} ≤ e^{-5κ}e^{-κd}`. -/
theorem kp_bound {H C11 εf κ δL d : ℝ} (hκ : 0 ≤ κ) (hδ : 0 ≤ δL) (hd : 0 ≤ d)
    (hH : H ≤ C11 * εf * Real.exp (-((1 + δL) * κ * d))) (hC : C11 * εf ≤ Real.exp (-(5 * κ))) :
    H ≤ Real.exp (-(5 * κ)) * Real.exp (-(κ * d)) := by
  have h1 : Real.exp (-((1 + δL) * κ * d)) ≤ Real.exp (-(κ * d)) := by
    apply Real.exp_le_exp.2
    have : κ * d ≤ (1 + δL) * κ * d := by nlinarith [mul_nonneg hκ hd, mul_nonneg (mul_nonneg hδ hκ) hd]
    linarith
  calc H ≤ C11 * εf * Real.exp (-((1 + δL) * κ * d)) := hH
    _ ≤ Real.exp (-(5 * κ)) * Real.exp (-((1 + δL) * κ * d)) :=
        mul_le_mul_of_nonneg_right hC (Real.exp_pos _).le
    _ ≤ Real.exp (-(5 * κ)) * Real.exp (-(κ * d)) := mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le

end StepKP
end CoreLean

end
