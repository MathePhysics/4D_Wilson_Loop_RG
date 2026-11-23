/-
`lem:activity-sum` of BALABAN_CORE.tex (`a021c13be348`), the analytic steps of "the sum" in its proof.

* The sum over the pairs `(𝐃, P) ≠ (∅, ∅)` of the products of the weights is at most
  `Π_Y(1 + w(Y))(1 + w_P)^{N_Z} - 1 ≤ e^W - 1 ≤ We^W` with `W = Σ_Yw(Y) + N_Zw_P` (`prod_sub_one_le`).
* `1 + 2^{12}M⁴(1 + d) ≤ (1 + 2^{12}M⁴)e^d` for `d ≥ 0` (`factor_exp`).
* The rates: `τ = 11κ/10 + 2 ≤ 6κ/5` for `κ ≥ 20`, `4κ - 1 ≥ 18κ/5` for `κ ≥ 5/2` (`rates`), and with
  `κ₂ = 2^9(6 log 2 + 2)`, `κ ≥ 10κ₂` gives `κ/5 - 2^9 - 1 ≥ 2^9(6 log 2 + 1)` (`domain_rate`).
* The count of the bonds: `L⁴#(Z)` cubes, `2M⁴` sites each, four bonds per site: `N_Z ≤ 8(LM)⁴#(Z)` (`bond_count`).
-/
import Mathlib

open Finset

noncomputable section

namespace CoreLean
namespace ActivitySumArith

/-- `Π(1 + w_i) - 1 ≤ e^W - 1 ≤ We^W`, `W = Σw_i`, for `w_i ≥ 0`. -/
theorem prod_sub_one_le {ι : Type*} (s : Finset ι) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    ∏ i ∈ s, (1 + w i) - 1 ≤ Real.exp (∑ i ∈ s, w i) - 1 ∧
      Real.exp (∑ i ∈ s, w i) - 1 ≤ (∑ i ∈ s, w i) * Real.exp (∑ i ∈ s, w i) := by
  set W := ∑ i ∈ s, w i
  have hW : 0 ≤ W := Finset.sum_nonneg fun i _ => hw i
  constructor
  · have : ∏ i ∈ s, (1 + w i) ≤ Real.exp W := by
      rw [Real.exp_sum]
      refine Finset.prod_le_prod₀ (fun i _ => by linarith [hw i]) fun i _ => ?_
      have := Real.add_one_le_exp (w i); linarith
    linarith
  · -- `e^W - 1 ≤ We^W` from `1 - W ≤ e^{-W}`
    have h1 := Real.add_one_le_exp (-W)
    have h2 : Real.exp W * Real.exp (-W) = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have h3 : 0 < Real.exp W := Real.exp_pos W
    nlinarith

/-- `1 + c(1 + d) ≤ (1 + c)e^d` for `c, d ≥ 0`. -/
theorem factor_exp {c d : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d) : 1 + c * (1 + d) ≤ (1 + c) * Real.exp d := by
  have h1 : 1 + d ≤ Real.exp d := by have := Real.add_one_le_exp d; linarith
  have h2 : 1 + c * (1 + d) ≤ (1 + c) * (1 + d) := by nlinarith
  exact h2.trans (mul_le_mul_of_nonneg_left h1 (by linarith))

/-- The rates. -/
theorem rates {κ : ℝ} (hκ : 20 ≤ κ) : 11 / 10 * κ + 2 ≤ 6 / 5 * κ ∧ 18 / 5 * κ ≤ 4 * κ - 1 := by
  constructor <;> linarith

/-- The rate of the domain sum: `κ ≥ 10κ₂`, `κ₂ = 2^9(6 log 2 + 2)`, gives `κ/5 - 2^9 - 1 ≥ 2^9(6 log 2 + 1)`. -/
theorem domain_rate {κ : ℝ} (hκ : 10 * (2 ^ 9 * (6 * Real.log 2 + 2)) ≤ κ) :
    2 ^ 9 * (6 * Real.log 2 + 1) ≤ κ / 5 - 2 ^ 9 - 1 := by
  have h : 0 < Real.log 2 := Real.log_pos (by norm_num)
  nlinarith

/-- The count of the bonds: `N_Z ≤ L⁴#(Z)·2M⁴·4 = 8(LM)⁴#(Z)`. -/
theorem bond_count {N L M nZ : ℝ} (hN : N ≤ L ^ 4 * nZ * (2 * M ^ 4) * 4) : N ≤ 8 * (L * M) ^ 4 * nZ := by
  calc N ≤ L ^ 4 * nZ * (2 * M ^ 4) * 4 := hN
    _ = 8 * (L * M) ^ 4 * nZ := by ring

/-- **The final bound**: with `W ≤ ε_H#(Z)`, `#(Z) ≤ 2^9(1 + d)`, `2^9ε_H ≤ 1`, the sum `≤ We^W` and the factor
`e^{-τd}`, `τ = 11κ/10 + 2`: `|𝖧(Z)| ≤ 2^{11}Kε_He^{-11κd/10}`. -/
theorem final_bound {W εH nZ d K κ H : ℝ} (hd : 0 ≤ d) (hK : 0 ≤ K) (hεH : 0 ≤ εH) (hW0 : 0 ≤ W)
    (hW : W ≤ εH * nZ) (hnZ : nZ ≤ 2 ^ 9 * (1 + d)) (hsmall : 2 ^ 9 * εH ≤ 1)
    (hH : H ≤ K * Real.exp (-((11 / 10 * κ + 2) * d)) * (W * Real.exp W)) :
    H ≤ 2 ^ 11 * K * εH * Real.exp (-(11 / 10 * κ * d)) := by
  have hW1 : W ≤ 2 ^ 9 * εH * (1 + d) := by nlinarith
  have hW2 : W ≤ 1 + d := by nlinarith
  have hexp1 : 1 + d ≤ Real.exp d := by have := Real.add_one_le_exp d; linarith
  have he : Real.exp 1 ≤ 4 := by have := Real.exp_one_lt_d9; linarith
  have hWe : W * Real.exp W ≤ 2 ^ 9 * εH * Real.exp 1 * Real.exp (2 * d) := by
    have h1 : Real.exp W ≤ Real.exp (1 + d) := Real.exp_le_exp.2 hW2
    have h2 : W * Real.exp W ≤ (2 ^ 9 * εH * (1 + d)) * Real.exp (1 + d) :=
      mul_le_mul hW1 h1 (Real.exp_pos _).le (by positivity)
    have h3 : (2 ^ 9 * εH * (1 + d)) * Real.exp (1 + d) ≤ (2 ^ 9 * εH * Real.exp d) * Real.exp (1 + d) := by
      gcongr
    have h4 : (2 ^ 9 * εH * Real.exp d) * Real.exp (1 + d) = 2 ^ 9 * εH * Real.exp 1 * Real.exp (2 * d) := by
      rw [show (2 : ℝ) * d = d + d by ring, Real.exp_add, Real.exp_add]; ring
    linarith
  have hsplit : Real.exp (-((11 / 10 * κ + 2) * d)) * Real.exp (2 * d) = Real.exp (-(11 / 10 * κ * d)) := by
    rw [← Real.exp_add]; congr 1; ring
  calc H ≤ K * Real.exp (-((11 / 10 * κ + 2) * d)) * (W * Real.exp W) := hH
    _ ≤ K * Real.exp (-((11 / 10 * κ + 2) * d)) * (2 ^ 9 * εH * Real.exp 1 * Real.exp (2 * d)) := by
        gcongr
    _ = 2 ^ 9 * Real.exp 1 * K * εH * (Real.exp (-((11 / 10 * κ + 2) * d)) * Real.exp (2 * d)) := by ring
    _ = 2 ^ 9 * Real.exp 1 * K * εH * Real.exp (-(11 / 10 * κ * d)) := by rw [hsplit]
    _ ≤ 2 ^ 9 * 4 * K * εH * Real.exp (-(11 / 10 * κ * d)) := by gcongr
    _ = 2 ^ 11 * K * εH * Real.exp (-(11 / 10 * κ * d)) := by ring

end ActivitySumArith
end CoreLean

end
