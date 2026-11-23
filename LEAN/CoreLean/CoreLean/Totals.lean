/-
`cor:totals` of BALABAN_CORE.tex (`a021c13be348`), the summation of its proof. With `q = L^{-β'} < 1` and the bounds
`|E_j| ≤ E₁Σ_{i=j}^n q^{i-j}#Γ_i` of the terms of the orders `j ≤ n` (`eq:theorem-two` for `Ω = Λ_j^{∼-1}`, the hypothesis
here): exchanging the sums, `Σ_{j=1}^n Σ_{i=j}^n q^{i-j}a_i ≤ (1 - q)⁻¹Σ_{i=1}^n a_i` (`double_sum_le`), and
`|𝐄_n| ≤ E₁(1 - L^{-β'})⁻¹Σ_{i=1}^n#Γ_i` (`totals_E`), the first bound of `eq:totals`.
-/
import Mathlib

open Finset

noncomputable section

namespace CoreLean
namespace Totals

/-- `Σ_{j ≤ i}q^{i-j} ≤ (1 - q)⁻¹`. -/
lemma geom_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (i : ℕ) :
    ∑ j ∈ Icc 1 i, q ^ (i - j) ≤ (1 - q)⁻¹ := by
  have e : ∑ j ∈ Icc 1 i, q ^ (i - j) ≤ ∑ m ∈ range i, q ^ m := by
    refine le_of_eq ?_
    refine Finset.sum_nbij' (fun j => i - j) (fun m => i - m) ?_ ?_ ?_ ?_ ?_
    · intro j hj; simp only [mem_Icc, mem_range] at hj ⊢; omega
    · intro m hm; simp only [mem_Icc, mem_range] at hm ⊢; omega
    · intro j hj; simp only [mem_Icc] at hj; omega
    · intro m hm; simp only [mem_range] at hm; omega
    · intro j _; rfl
  refine e.trans ?_
  rw [geom_sum_eq (by linarith : q ≠ 1)]
  have h1 : 0 < 1 - q := by linarith
  rw [div_le_iff_of_neg (by linarith)]
  have : 0 ≤ q ^ i := pow_nonneg hq0 i
  rw [show (1 - q)⁻¹ * (q - 1) = -1 by field_simp; ring]
  linarith

/-- **The exchange of the sums**. -/
theorem double_sum_le (a : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (n : ℕ) :
    ∑ j ∈ Icc 1 n, ∑ i ∈ Icc j n, q ^ (i - j) * a i ≤ (1 - q)⁻¹ * ∑ i ∈ Icc 1 n, a i := by
  have e : ∑ j ∈ Icc 1 n, ∑ i ∈ Icc j n, q ^ (i - j) * a i =
      ∑ i ∈ Icc 1 n, ∑ j ∈ Icc 1 i, q ^ (i - j) * a i := by
    refine Finset.sum_comm' fun j i => ?_
    simp only [mem_Icc]; omega
  rw [e, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← Finset.sum_mul, mul_comm]
  exact mul_le_mul_of_nonneg_left (geom_le hq0 hq1 i) (ha i) |>.trans_eq (mul_comm _ _)

/-- **`eq:totals`**, the first bound. -/
theorem totals_E (E : ℕ → ℝ) (Γ : ℕ → ℝ) (hΓ : ∀ i, 0 ≤ Γ i) {E₁ q : ℝ} (hE₁ : 0 ≤ E₁) (hq0 : 0 ≤ q)
    (hq1 : q < 1) (n : ℕ) (hE : ∀ j ∈ Icc 1 n, |E j| ≤ E₁ * ∑ i ∈ Icc j n, q ^ (i - j) * Γ i) :
    |∑ j ∈ Icc 1 n, E j| ≤ E₁ * (1 - q)⁻¹ * ∑ i ∈ Icc 1 n, Γ i := by
  calc |∑ j ∈ Icc 1 n, E j| ≤ ∑ j ∈ Icc 1 n, |E j| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Icc 1 n, E₁ * ∑ i ∈ Icc j n, q ^ (i - j) * Γ i := Finset.sum_le_sum hE
    _ = E₁ * ∑ j ∈ Icc 1 n, ∑ i ∈ Icc j n, q ^ (i - j) * Γ i := (Finset.mul_sum _ _ _).symm
    _ ≤ E₁ * ((1 - q)⁻¹ * ∑ i ∈ Icc 1 n, Γ i) :=
        mul_le_mul_of_nonneg_left (double_sum_le Γ hΓ hq0 hq1 n) hE₁
    _ = E₁ * (1 - q)⁻¹ * ∑ i ∈ Icc 1 n, Γ i := by ring

end Totals
end CoreLean

end
