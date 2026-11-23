/-
`lem:through-conditions` of BALABAN_CORE.tex (`a021c13be348`), the exponent of its statement.

* `a_eps_condition`: with `a_ε = max{a₁, q₁ - p₀}`, `p₀ + a₁ < q₀ + r` and `q₁ < q₀ + r` (`eq:chain-exponents`) give
  `p₀ + a_ε < q₀ + r`, the condition of `lem:chain-conditions` on `a_ε`.
* `C_eps_ge_one`: `C_ε = 4K_th²(2C₁ + C^α₀/(fA₀) + 1) ≥ 1` for `K_th ≥ 1`, `C₁ ≥ 0`, `C^α₀/(fA₀) ≥ 0`.
-/
import Mathlib

noncomputable section

namespace CoreLean
namespace ThroughConditionsArith

/-- `p₀ + max{a₁, q₁ - p₀} < q₀ + r`. -/
theorem a_eps_condition {p₀ a₁ q₀ q₁ r : ℝ} (h1 : p₀ + a₁ < q₀ + r) (h2 : q₁ < q₀ + r) :
    p₀ + max a₁ (q₁ - p₀) < q₀ + r := by
  rcases le_total a₁ (q₁ - p₀) with h | h
  · rw [max_eq_right h]; linarith
  · rw [max_eq_left h]; exact h1

/-- `C_ε ≥ 1`. -/
theorem C_eps_ge_one {K C₁ c : ℝ} (hK : 1 ≤ K) (hC : 0 ≤ C₁) (hc : 0 ≤ c) : 1 ≤ 4 * K ^ 2 * (2 * C₁ + c + 1) := by
  have hK2 : 1 ≤ K ^ 2 := by nlinarith
  nlinarith

end ThroughConditionsArith
end CoreLean

end
