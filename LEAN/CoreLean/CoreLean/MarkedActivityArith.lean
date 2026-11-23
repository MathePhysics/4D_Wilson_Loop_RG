/-
`lem:marked-activity` of BALABAN_CORE.tex (`a021c13be348`), the analytic steps of "the sum" in its proof.

* The rates: `τ = 9κ/10 + 1 ≤ 19κ/20` for `κ ≥ 20`; `4/5 - 19/30 = 1/6`; with `κ₂ = 2^9(6 log 2 + 2)`, `κ ≥ 6κ₂` gives
  `κ/6 - 2^9 ≥ 2^9(6 log 2 + 1)` (`marked_rates`).
* `W ≤ ε_M#(M)`, `#(M) ≤ 81#(D') + 324d'` (`lem:contracted-geometry`(v)) and `324ε_M ≤ 1` give `W ≤ #(D') + d'`
  (`W_bound`).
* The bound: `‖𝖧‖ ≤ ‖𝒳‖e^{L⁴#(D') + 11κm_D}e^We^{-τd'}` with `W ≤ #(D') + d'` is `eq:marked-activity-bound`,
  `‖𝒳‖e^{(L⁴ + 1)#(D')}e^{11κm_D}e^{-9κd'/10}` (`marked_bound`).
-/
import Mathlib

noncomputable section

namespace CoreLean
namespace MarkedActivityArith

/-- The rates. -/
theorem marked_rates {κ : ℝ} (hκ : 6 * (2 ^ 9 * (6 * Real.log 2 + 2)) ≤ κ) :
    9 / 10 * κ + 1 ≤ 19 / 20 * κ ∧ (4 / 5 : ℝ) - 19 / 30 = 1 / 6 ∧ 2 ^ 9 * (6 * Real.log 2 + 1) ≤ κ / 6 - 2 ^ 9 := by
  have h : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨by nlinarith, by norm_num, by nlinarith⟩

/-- `W ≤ #(D') + d'`. -/
theorem W_bound {W εM nM nD d : ℝ} (hεM : 0 ≤ εM) (hnD : 0 ≤ nD) (hd : 0 ≤ d) (hW : W ≤ εM * nM)
    (hnM : nM ≤ 81 * nD + 324 * d) (hsmall : 324 * εM ≤ 1) : W ≤ nD + d := by
  have h1 : εM * nM ≤ εM * (81 * nD + 324 * d) := mul_le_mul_of_nonneg_left hnM hεM
  have h2 : εM * (81 * nD + 324 * d) ≤ nD + d := by nlinarith
  linarith

/-- **`eq:marked-activity-bound`**. -/
theorem marked_bound {H X L nD κ mD W d : ℝ} (hX : 0 ≤ X) (hW : W ≤ nD + d)
    (hH : H ≤ X * Real.exp (L ^ 4 * nD + 11 * κ * mD) * Real.exp W * Real.exp (-((9 / 10 * κ + 1) * d))) :
    H ≤ X * Real.exp ((L ^ 4 + 1) * nD) * Real.exp (11 * κ * mD) * Real.exp (-(9 / 10 * κ * d)) := by
  have h1 : Real.exp W ≤ Real.exp (nD + d) := Real.exp_le_exp.2 hW
  calc H ≤ X * Real.exp (L ^ 4 * nD + 11 * κ * mD) * Real.exp W * Real.exp (-((9 / 10 * κ + 1) * d)) := hH
    _ ≤ X * Real.exp (L ^ 4 * nD + 11 * κ * mD) * Real.exp (nD + d) * Real.exp (-((9 / 10 * κ + 1) * d)) := by
        gcongr
    _ = X * Real.exp ((L ^ 4 + 1) * nD) * Real.exp (11 * κ * mD) * Real.exp (-(9 / 10 * κ * d)) := by
        rw [mul_assoc X, mul_assoc X, mul_assoc X, mul_assoc X, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add,
          ← Real.exp_add]
        congr 2; ring

end MarkedActivityArith
end CoreLean

end
