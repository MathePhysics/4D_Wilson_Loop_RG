/-
`lem:factor-field` of BALABAN_CORE.tex (`a021c13be348`), (i) and the summation of (ii).

* (i): with `α_{0,g} = C^α_0ĝ_g(log ĝ_g^{-2})^{q₀}` (`def:admissible`) and `ĝ_i ≤ ĝ_g ≤ (1 + β₀)(g - i)^{1/2}ĝ_i < 1`,
  `α_{0,g} ≤ (1 + β₀)(g - i)^{1/2}α_{0,i}` (`radius_compare`), because `log ĝ_g^{-2} ≤ log ĝ_i^{-2}`.
* (ii), the tail: for `s ≥ n - i`, `(s + 1)^{1/2}L^{-s} ≤ 2^{-(n-i)}(s + 1)^{1/2}(2/L)^s` (`tail_term`), and the sum over
  distinct scales `s ≥ n - i` is at most `2^{-(n-i)}Σ_{s ≥ 0}(s + 1)^{1/2}(2/L)^s` (`tail_sum`), the series converging
  for `L ≥ 3` (`summable_hat`); this is the factor `ĉ/(8(1 + β₀))` of `eq:factor-field`.
-/
import Mathlib

open Finset

noncomputable section

namespace CoreLean
namespace FactorField

/-- **(i)**: `α_{0,g} ≤ (1 + β₀)r·α_{0,i}` from `ĝ_i ≤ ĝ_g ≤ (1 + β₀)rĝ_i < 1`. -/
theorem radius_compare {C gi gg β₀ r q₀ : ℝ} (hC : 0 ≤ C) (hgi : 0 < gi) (hig : gi ≤ gg) (hg1 : gg < 1)
    (hgg : gg ≤ (1 + β₀) * r * gi) (hq : 0 ≤ q₀) :
    C * gg * Real.log (gg⁻¹ ^ 2) ^ q₀ ≤ (1 + β₀) * r * (C * gi * Real.log (gi⁻¹ ^ 2) ^ q₀) := by
  have hgg0 : 0 < gg := lt_of_lt_of_le hgi hig
  -- the logarithms are nonnegative and decrease
  have hlog0 : 0 ≤ Real.log (gg⁻¹ ^ 2) := by
    apply Real.log_nonneg
    have : 1 ≤ gg⁻¹ := by rw [one_le_inv₀ hgg0]; exact hg1.le
    nlinarith
  have hlog : Real.log (gg⁻¹ ^ 2) ≤ Real.log (gi⁻¹ ^ 2) := by
    apply Real.log_le_log (by positivity)
    have : gg⁻¹ ≤ gi⁻¹ := inv_anti₀ hgi hig
    exact pow_le_pow_left₀ (by positivity) this 2
  have hpow : Real.log (gg⁻¹ ^ 2) ^ q₀ ≤ Real.log (gi⁻¹ ^ 2) ^ q₀ := Real.rpow_le_rpow hlog0 hlog hq
  have hp0 : 0 ≤ Real.log (gg⁻¹ ^ 2) ^ q₀ := Real.rpow_nonneg hlog0 q₀
  calc C * gg * Real.log (gg⁻¹ ^ 2) ^ q₀ ≤ C * ((1 + β₀) * r * gi) * Real.log (gg⁻¹ ^ 2) ^ q₀ := by gcongr
    _ ≤ C * ((1 + β₀) * r * gi) * Real.log (gi⁻¹ ^ 2) ^ q₀ := by
        refine mul_le_mul_of_nonneg_left hpow ?_
        have : 0 ≤ (1 + β₀) * r * gi := le_trans hgg0.le hgg
        positivity
    _ = (1 + β₀) * r * (C * gi * Real.log (gi⁻¹ ^ 2) ^ q₀) := by ring

/-- **(ii)**, one term of the tail. -/
theorem tail_term {L : ℝ} (hL : 2 ≤ L) {k s : ℕ} (hks : k ≤ s) :
    Real.sqrt (s + 1) * (L⁻¹) ^ s ≤ (1 / 2) ^ k * (Real.sqrt (s + 1) * (2 / L) ^ s) := by
  have hL0 : 0 < L := by linarith
  have e : (L⁻¹) ^ s = (1 / 2) ^ s * (2 / L) ^ s := by
    rw [← mul_pow]; congr 1; field_simp
  rw [e]
  have h1 : (1 / 2 : ℝ) ^ s ≤ (1 / 2) ^ k := pow_le_pow_of_le_one (by norm_num) (by norm_num) hks
  have h2 : 0 ≤ Real.sqrt (s + 1) * (2 / L) ^ s := by positivity
  calc Real.sqrt (s + 1) * ((1 / 2) ^ s * (2 / L) ^ s) = (1 / 2) ^ s * (Real.sqrt (s + 1) * (2 / L) ^ s) := by
        ring
    _ ≤ (1 / 2) ^ k * (Real.sqrt (s + 1) * (2 / L) ^ s) := mul_le_mul_of_nonneg_right h1 h2

/-- The series `Σ_{s ≥ 0}(s + 1)^{1/2}(2/L)^s` converges for `L ≥ 3`. -/
theorem summable_hat {L : ℝ} (hL : 3 ≤ L) : Summable fun s : ℕ => Real.sqrt (s + 1) * (2 / L) ^ s := by
  have hq0 : 0 ≤ 2 / L := by positivity
  have hq1 : 2 / L < 1 := by rw [div_lt_one (by linarith)]; linarith
  have hs : Summable fun s : ℕ => ((s : ℝ) + 1) * (2 / L) ^ s := by
    have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 (r := 2 / L) (by rw [Real.norm_of_nonneg hq0]; exact hq1)
    have h2 := summable_geometric_of_lt_one hq0 hq1
    have := h1.add h2
    refine this.congr fun s => ?_
    simp only [pow_one]; ring
  refine Summable.of_nonneg_of_le (fun s => by positivity) (fun s => ?_) hs
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  have h : (1 : ℝ) ≤ s + 1 := by have := Nat.cast_nonneg (α := ℝ) s; linarith
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith

/-- **(ii)**, the tail over distinct scales: `Σ_{s ∈ S, s ≥ k}(s + 1)^{1/2}L^{-s} ≤ 2^{-k}Σ_{s ≥ 0}(s + 1)^{1/2}(2/L)^s`. -/
theorem tail_sum {L : ℝ} (hL : 3 ≤ L) (k : ℕ) (S : Finset ℕ) (hS : ∀ s ∈ S, k ≤ s) :
    ∑ s ∈ S, Real.sqrt (s + 1) * (L⁻¹) ^ s ≤ (1 / 2) ^ k * ∑' s : ℕ, Real.sqrt (s + 1) * (2 / L) ^ s := by
  calc ∑ s ∈ S, Real.sqrt (s + 1) * (L⁻¹) ^ s ≤ ∑ s ∈ S, (1 / 2) ^ k * (Real.sqrt (s + 1) * (2 / L) ^ s) :=
        Finset.sum_le_sum fun s hs => tail_term (by linarith) (hS s hs)
    _ = (1 / 2) ^ k * ∑ s ∈ S, Real.sqrt (s + 1) * (2 / L) ^ s := by rw [Finset.mul_sum]
    _ ≤ (1 / 2) ^ k * ∑' s : ℕ, Real.sqrt (s + 1) * (2 / L) ^ s := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact (summable_hat hL).sum_le_tsum S fun s _ => by positivity

end FactorField
end CoreLean

end
