/-
`lem:interior-averages` of BALABAN_CORE.tex (`a021c13be348`), the induction of the case (c) of its proof and its
constants, in abstract form.

* *The downward induction*: with `δ_l ≤ C_axα₀^{(l)} + δ_{l+1}` whenever `α₀^{(l)} + δ_{l+1} ≤ c_ax` (`lem:axial-smallness`
  at the order `l + 1`), the top value `δ_{n_*} ≤ D`, `α₀^{(l)} ≤ A`, `Σ_{l ≤ i < n_*}α₀^{(i)} ≤ S`, and
  `A + D + C_axS ≤ c_ax`, every `δ_l`, `n ≤ l ≤ n_*`, is at most `D + C_axS` (`downward`).
* *The geometric sum*: `Σ_{l < n_*}2L²α₀L^{-2(n_* - 1 - l)} ≤ 2L²α₀/(1 - L^{-2}) ≤ 3L²α₀` for `L ≥ 3` (`geom_alpha`).
* *The constant*: with `D = (1 + 48πL)α₁ + 2L²C_axα₀` (`eq:interior-straddling`) and `S = 3L²α₀`,
  `D + C_axS = α'₁ = (1 + 48πL)α₁ + 5L²C_axα₀` (`alpha_prime`).
-/
import Mathlib

open Finset

noncomputable section

namespace CoreLean
namespace InteriorAverages

/-- **The downward induction**. -/
theorem downward (nstar : ℕ) (δ a : ℕ → ℝ) {C D A S c : ℝ} (hC : 0 ≤ C) (ha : ∀ l, 0 ≤ a l)
    (haA : ∀ l, a l ≤ A) (hS : ∀ l ≤ nstar, ∑ i ∈ Ico l nstar, a i ≤ S) (htop : δ nstar ≤ D)
    (hsmall : A + D + C * S ≤ c)
    (hstep : ∀ l < nstar, a l + δ (l + 1) ≤ c → δ l ≤ C * a l + δ (l + 1)) :
    ∀ l ≤ nstar, δ l ≤ D + C * ∑ i ∈ Ico l nstar, a i := by
  -- induction on `m = nstar - l`
  have key : ∀ m ≤ nstar, δ (nstar - m) ≤ D + C * ∑ i ∈ Ico (nstar - m) nstar, a i := by
    intro m
    induction m with
    | zero => intro _; simp [htop]
    | succ m ih =>
      intro hm
      have hl : nstar - (m + 1) < nstar := by omega
      have e : nstar - (m + 1) + 1 = nstar - m := by omega
      have ih' := ih (by omega)
      have hsplit : ∑ i ∈ Ico (nstar - (m + 1)) nstar, a i = a (nstar - (m + 1)) +
          ∑ i ∈ Ico (nstar - m) nstar, a i := by
        rw [← e, Finset.sum_eq_sum_Ico_succ_bot (by omega)]
      have hSm : C * ∑ i ∈ Ico (nstar - m) nstar, a i ≤ C * S :=
        mul_le_mul_of_nonneg_left (hS _ (by omega)) hC
      have hcond : a (nstar - (m + 1)) + δ (nstar - (m + 1) + 1) ≤ c := by
        rw [e]; linarith [haA (nstar - (m + 1))]
      have := hstep _ hl hcond
      rw [e] at this
      rw [hsplit]
      nlinarith [ha (nstar - (m + 1))]
  intro l hl
  have := key (nstar - l) (Nat.sub_le _ _)
  rwa [Nat.sub_sub_self hl] at this

/-- **The geometric sum** `Σ_{l < n_*}2L²α₀L^{-2(n_* - 1 - l)} ≤ 3L²α₀`. -/
theorem geom_alpha {L α₀ : ℝ} (hL : 3 ≤ L) (hα : 0 ≤ α₀) (nstar l : ℕ) :
    ∑ i ∈ Ico l nstar, 2 * L ^ 2 * α₀ * (L ^ 2)⁻¹ ^ (nstar - 1 - i) ≤ 3 * L ^ 2 * α₀ := by
  have hL2 : 9 ≤ L ^ 2 := by nlinarith
  set q := (L ^ 2)⁻¹
  have hq0 : 0 ≤ q := by positivity
  have hq : q ≤ 1 / 9 := by
    simp only [q]; rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hL2
  have hc : 0 ≤ 2 * L ^ 2 * α₀ := by positivity
  -- the sum over `Ico l nstar` of `q^{nstar - 1 - i}` is at most the geometric series
  have h1 : ∑ i ∈ Ico l nstar, q ^ (nstar - 1 - i) ≤ ∑ m ∈ range nstar, q ^ m := by
    have : ∑ i ∈ Ico l nstar, q ^ (nstar - 1 - i) ≤ ∑ i ∈ range nstar, q ^ (nstar - 1 - i) :=
      Finset.sum_le_sum_of_subset_of_nonneg (fun i hi => by
        simp only [mem_Ico, mem_range] at hi ⊢; omega) fun i _ _ => pow_nonneg hq0 _
    refine this.trans (le_of_eq ?_)
    exact Finset.sum_range_reflect (fun m => q ^ m) nstar
  have h2 : ∑ m ∈ range nstar, q ^ m ≤ 9 / 8 := by
    have hq1 : q < 1 := by linarith
    calc ∑ m ∈ range nstar, q ^ m ≤ (1 - q)⁻¹ := by
          rw [geom_sum_eq hq1.ne, div_le_iff_of_neg (by linarith)]
          rw [show (1 - q)⁻¹ * (q - 1) = -1 by field_simp; ring]
          linarith [pow_nonneg hq0 nstar]
      _ ≤ 9 / 8 := by
          rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  calc ∑ i ∈ Ico l nstar, 2 * L ^ 2 * α₀ * q ^ (nstar - 1 - i)
      = 2 * L ^ 2 * α₀ * ∑ i ∈ Ico l nstar, q ^ (nstar - 1 - i) := by rw [Finset.mul_sum]
    _ ≤ 2 * L ^ 2 * α₀ * (9 / 8) := mul_le_mul_of_nonneg_left (h1.trans h2) hc
    _ ≤ 3 * L ^ 2 * α₀ := by nlinarith [sq_nonneg L]

/-- **The constant** `α'₁`. -/
theorem alpha_prime (L α₀ α₁ Cax : ℝ) :
    (1 + 48 * Real.pi * L) * α₁ + 2 * L ^ 2 * Cax * α₀ + Cax * (3 * L ^ 2 * α₀) =
      (1 + 48 * Real.pi * L) * α₁ + 5 * L ^ 2 * Cax * α₀ := by ring

end InteriorAverages
end CoreLean

end
