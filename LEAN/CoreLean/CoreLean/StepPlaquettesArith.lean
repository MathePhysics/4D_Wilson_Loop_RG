/-
`lem:step-plaquettes` of BALABAN_CORE.tex (`a021c13be348`) and the summation after it, the arithmetic.

* `log_size`: `‖V^{(n)}V_n⁻¹ - 1‖ ≤ 2C₁₂ε` from `‖V_nV^{(n)}⁻¹ - 1‖ ≤ C₁₂ε ≤ ¼` (in a normed ring with `‖1‖ = 1`,
  `X - 1 = -(Y - 1)X` for `X = Y⁻¹`), so that the logarithm, at most twice the distance, is at most `4C₁₂ε`.
* `rate`: `e^{-½δ₂·27M_ck} ≤ L^{-16k}` for `½δ₂ ≥ 2δ_⋆`, `27δ_⋆M_c ≥ 8 log L`.
* `step_sum`: `Σ_{s ≥ 0} L^{-16 max{s - 2, 0}}(1 + β₀)max{1, s^{1/2}} ≤ 5` for `L ≥ 3`, `1 + β₀ ≤ √2`
  (`β₀ ≤ √2 - 1`, `def:admissible`); the first three terms give `2√2 + 2 < 4.83`.
-/
import Mathlib

noncomputable section

namespace CoreLean
namespace StepPlaquettesArith

/-- `‖X - 1‖ ≤ 2‖Y - 1‖` for `X = Y⁻¹`, `‖Y - 1‖ ≤ ½`. -/
theorem log_size {R : Type*} [NormedRing R] [NormOneClass R] (X Y : R) (hXY : Y * X = 1) {t : ℝ}
    (hY : ‖Y - 1‖ ≤ t) (ht : t ≤ 1 / 2) : ‖X - 1‖ ≤ 2 * t := by
  have e : X - 1 = -((Y - 1) * X) := by
    rw [sub_mul, hXY, one_mul]; abel
  have h1 : ‖X - 1‖ ≤ t * ‖X‖ := by
    rw [e, norm_neg]; exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hY (norm_nonneg _))
  have h2 : ‖X‖ ≤ 1 + ‖X - 1‖ := by
    calc ‖X‖ = ‖1 + (X - 1)‖ := by rw [add_sub_cancel]
      _ ≤ ‖(1 : R)‖ + ‖X - 1‖ := norm_add_le _ _
      _ = 1 + ‖X - 1‖ := by rw [norm_one]
  have ht0 : 0 ≤ t := (norm_nonneg _).trans hY
  have h3 : ‖X - 1‖ ≤ t * (1 + ‖X - 1‖) := h1.trans (mul_le_mul_of_nonneg_left h2 ht0)
  nlinarith [norm_nonneg (X - 1)]

/-- `e^{-½δ₂·27M_ck} ≤ L^{-16k}`. -/
theorem rate {δ₂ δs Mc L : ℝ} (k : ℕ) (hL : 1 ≤ L) (hδ : 2 * δs ≤ 1 / 2 * δ₂) (hMc : 0 ≤ Mc)
    (hlog : 8 * Real.log L ≤ 27 * δs * Mc) :
    Real.exp (-(1 / 2) * δ₂ * (27 * Mc * k)) ≤ (L ^ (16 * k))⁻¹ := by
  have hL0 : 0 < L := by linarith
  rw [← Real.exp_log (by positivity : (0 : ℝ) < (L ^ (16 * k))⁻¹), Real.log_inv, Real.log_pow]
  apply Real.exp_le_exp.2
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h1 : 2 * δs * (27 * Mc * k) ≤ 1 / 2 * δ₂ * (27 * Mc * k) :=
    mul_le_mul_of_nonneg_right hδ (by positivity)
  have h2 : 16 * Real.log L * k ≤ 2 * (27 * δs * Mc) * k := by nlinarith
  push_cast
  nlinarith

/-- The terms of the sum. -/
def term (L c : ℝ) (s : ℕ) : ℝ := (L ^ (16 * (s - 2)))⁻¹ * (c * max 1 (Real.sqrt s))

lemma sqrt_le_pow (k : ℕ) : Real.sqrt (k + 3) ≤ 2 ^ (k + 1) := by
  rw [Real.sqrt_le_left (by positivity)]
  have : ((k : ℝ) + 3) ≤ 4 ^ (k + 1) := by
    induction k with
    | zero => norm_num
    | succ n ih => push_cast at ih ⊢; rw [pow_succ]; nlinarith
  calc ((k : ℝ) + 3) ≤ 4 ^ (k + 1) := this
    _ = (2 ^ (k + 1)) ^ 2 := by rw [← pow_mul, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]; ring_nf

/-- **The sum over the steps is at most `5`.** -/
theorem step_sum {L c : ℝ} (hL : 3 ≤ L) (hc0 : 0 ≤ c) (hc : c ≤ Real.sqrt 2) :
    Summable (term L c) ∧ ∑' s, term L c s ≤ 5 := by
  have hL0 : 0 < L := by linarith
  set q : ℝ := 2 * (3 ^ 16 : ℝ)⁻¹
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := by norm_num [q]
  -- the tail `s = k + 3`
  have htail : ∀ k : ℕ, term L c (k + 3) ≤ c * q ^ (k + 1) := fun k => by
    have hs : max 1 (Real.sqrt ((k + 3 : ℕ) : ℝ)) = Real.sqrt (k + 3) := by
      push_cast
      exact max_eq_right (by rw [Real.one_le_sqrt]; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
    have hexp : 16 * (k + 3 - 2) = 16 * (k + 1) := by omega
    simp only [term, hs, hexp]
    have hpow : (L ^ (16 * (k + 1)))⁻¹ ≤ ((3 : ℝ) ^ 16)⁻¹ ^ (k + 1) := by
      calc (L ^ (16 * (k + 1)))⁻¹ ≤ ((3 : ℝ) ^ (16 * (k + 1)))⁻¹ :=
            inv_anti₀ (by positivity) (pow_le_pow_left₀ (by norm_num) hL (16 * (k + 1)))
        _ = ((3 : ℝ) ^ 16)⁻¹ ^ (k + 1) := by rw [pow_mul, inv_pow]
    calc (L ^ (16 * (k + 1)))⁻¹ * (c * Real.sqrt (k + 3))
        ≤ ((3 : ℝ) ^ 16)⁻¹ ^ (k + 1) * (c * 2 ^ (k + 1)) := by
          apply mul_le_mul hpow (mul_le_mul_of_nonneg_left (sqrt_le_pow k) hc0) (by positivity) (by positivity)
      _ = c * q ^ (k + 1) := by simp only [q]; rw [mul_pow]; ring
  have hnn : ∀ s, 0 ≤ term L c s := fun s => by unfold term; positivity
  have hgeo : Summable fun k : ℕ => c * q ^ (k + 1) :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left (c * q) |>.congr fun k => by ring
  have hsum3 : Summable fun k : ℕ => term L c (k + 3) :=
    Summable.of_nonneg_of_le (fun k => hnn _) htail hgeo
  have hsum : Summable (term L c) := (summable_nat_add_iff 3).1 hsum3
  refine ⟨hsum, ?_⟩
  rw [← hsum.sum_add_tsum_nat_add 3]
  have h0 : term L c 0 = c := by simp [term]
  have h1 : term L c 1 = c := by simp [term]
  have h2 : term L c 2 = c * Real.sqrt 2 := by
    simp only [term]
    norm_num
  have htsum : ∑' k, term L c (k + 3) ≤ c * q / (1 - q) := by
    calc ∑' k, term L c (k + 3) ≤ ∑' k : ℕ, c * q ^ (k + 1) := hsum3.tsum_le_tsum htail hgeo
      _ = c * q / (1 - q) := by
          rw [show (fun k : ℕ => c * q ^ (k + 1)) = fun k => c * q * q ^ k from funext fun k => by ring,
            tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
          field_simp
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, h0, h1, h2]
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hsq : Real.sqrt 2 < 1.4143 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hcq : c * q / (1 - q) ≤ 2 * q := by
    rw [div_le_iff₀ (by linarith)]
    have hc15 : c ≤ 3 / 2 := hc.trans (by linarith)
    have hq' : q ≤ 1 / 4 := by norm_num [q]
    have h1 : c * q ≤ 3 / 2 * q := mul_le_mul_of_nonneg_right hc15 hq0
    have h2 : q * q ≤ 1 / 4 * q := mul_le_mul_of_nonneg_right hq' hq0
    calc c * q ≤ 3 / 2 * q := h1
      _ = 2 * q - 2 * (1 / 4 * q) := by ring
      _ ≤ 2 * q - 2 * (q * q) := by linarith [h2]
      _ = 2 * q * (1 - q) := by ring
  have hq2 : 2 * q ≤ 1 / 100 := by norm_num [q]
  have hcs : c * Real.sqrt 2 ≤ 2 := by
    calc c * Real.sqrt 2 ≤ Real.sqrt 2 * Real.sqrt 2 := mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg _)
      _ = 2 := hs2
  linarith

end StepPlaquettesArith
end CoreLean

end
