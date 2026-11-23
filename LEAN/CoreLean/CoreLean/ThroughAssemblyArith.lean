/-
`cor:through-assembly` of BALABAN_CORE.tex (`a021c13be348`), the limits of the functions of its proof.

* `d2_tendsto`: `x^C e^{x/2 - cx²} → 0` as `x → ∞` for `c > 0` (the function `d₂` with `c = δ₂LM/32`).
* The function `d₃(x) = CL²(1 + log x)^{1/2}x^{p₁ - p₀ - a_ε}` tends to zero by
  `ChainConditionsArith.power_log_tendsto`, since `p₁ < p₀ ≤ p₀ + a_ε`.
-/
import Mathlib

open Filter Topology

noncomputable section

namespace CoreLean
namespace ThroughAssemblyArith

/-- **`x^C e^{x/2 - cx²} → 0`.** -/
theorem d2_tendsto {C c : ℝ} (hc : 0 < c) :
    Tendsto (fun x : ℝ => x ^ C * Real.exp (x / 2 - c * x ^ 2)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun x : ℝ => x ^ C * Real.exp (-1 * x)) atTop (𝓝 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero C 1 one_pos
  apply squeeze_zero' _ _ h1
  · filter_upwards [eventually_gt_atTop 0] with x hx
    positivity
  · filter_upwards [eventually_ge_atTop (3 / (2 * c)), eventually_gt_atTop 0] with x hx hx0
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.2
    -- `x/2 - cx² ≤ -x` for `x ≥ 3/(2c)`
    have h : 3 / 2 ≤ c * x := by
      rw [div_le_iff₀ (by positivity)] at hx; linarith
    nlinarith

end ThroughAssemblyArith
end CoreLean

end
