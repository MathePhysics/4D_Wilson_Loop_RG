import Mathlib

/-! Taylor's formula with integral remainder for the exponential of a complete normed real algebra,
`exp z = ∑_{m ≤ n} z^m / m! + z^{n+1} / (n+1)! · R_{n+1}(z)` with `R_{n+1}(z) = (n+1) ∫_0^1 (1-t)^n exp(t z) dt`,
and the bound `‖R_{n+1}(z)‖ ≤ 1` when `‖exp(t z)‖ ≤ 1` on `[0, 1]`. -/

namespace BakerCampbellHausdorff

open NormedSpace

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- The integral remainder `R_{n+1}(z) = (n+1) ∫_0^1 (1-t)^n exp(t z) dt`. -/
noncomputable def expRem (n : ℕ) (z : 𝔸) : 𝔸 :=
  ((n : ℝ) + 1) • ∫ t in (0 : ℝ)..1, (1 - t) ^ n • exp (t • z)  -- totalisation-audit: allow interval integral of a continuous integrand on [0, 1]

lemma continuous_exp_smul_const (z : 𝔸) : Continuous fun t : ℝ => exp (t • z) :=
  (differentiable_exp_smul_const ℝ z).continuous

lemma intervalIntegrable_pow_smul_exp (n : ℕ) (z : 𝔸) :
    IntervalIntegrable (fun t : ℝ => (1 - t) ^ n • exp (t • z)) MeasureTheory.volume 0 1 :=
  (((continuous_const.sub continuous_id).pow n).smul (continuous_exp_smul_const z)).intervalIntegrable 0 1

lemma hasDerivAt_pow_smul_exp (n : ℕ) (z : 𝔸) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (1 - s) ^ (n + 1) • exp (s • z))
      ((1 - t) ^ (n + 1) • (z * exp (t • z)) - (((n : ℝ) + 1) * (1 - t) ^ n) • exp (t • z)) t := by
  have h1 : HasDerivAt (fun s : ℝ => (1 - s) ^ (n + 1)) (-(((n : ℝ) + 1) * (1 - t) ^ n)) t := by
    have := ((hasDerivAt_id' t).const_sub 1).pow (n + 1)
    convert this using 1
    rw [Nat.add_sub_cancel]
    push_cast
    ring
  have h2 := hasDerivAt_exp_smul_const' (𝕂 := ℝ) z t
  convert h1.smul h2 using 1
  rw [neg_smul, sub_eq_add_neg]

/-- `z ∫_0^1 exp(t z) dt = exp z - 1`. -/
lemma mul_integral_exp_smul (z : 𝔸) :
    z * (∫ t in (0 : ℝ)..1, exp (t • z)) = exp z - 1 := by  -- totalisation-audit: allow interval integral of a continuous integrand on [0, 1]
  have hc := continuous_exp_smul_const z
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hasDerivAt_exp_smul_const' (𝕂 := ℝ) z t)
    ((continuous_const.mul hc).intervalIntegrable 0 1)
  simp only [one_smul, zero_smul, exp_zero] at hFTC
  have h := ContinuousLinearMap.intervalIntegral_comp_comm (ContinuousLinearMap.mul ℝ 𝔸 z)
    (hc.intervalIntegrable (μ := MeasureTheory.volume) 0 1)
  simp only [ContinuousLinearMap.mul_apply'] at h
  rw [← hFTC, h]

/-- The recursion `(n+1) ∫_0^1 (1-t)^n exp(t z) dt = 1 + z ∫_0^1 (1-t)^{n+1} exp(t z) dt` (integration by parts). -/
lemma smul_integral_pow_smul_exp (n : ℕ) (z : 𝔸) :
    ((n : ℝ) + 1) • (∫ t in (0 : ℝ)..1, (1 - t) ^ n • exp (t • z)) =  -- totalisation-audit: allow interval integral of a continuous integrand on [0, 1]
      1 + z * ∫ t in (0 : ℝ)..1, (1 - t) ^ (n + 1) • exp (t • z) := by  -- totalisation-audit: allow interval integral of a continuous integrand on [0, 1]
  have hc := continuous_exp_smul_const z
  have hint1 : IntervalIntegrable (fun t : ℝ => (1 - t) ^ (n + 1) • (z * exp (t • z))) MeasureTheory.volume 0 1 :=
    (((continuous_const.sub continuous_id).pow (n + 1)).smul (continuous_const.mul hc)).intervalIntegrable 0 1
  have hint2 : IntervalIntegrable (fun t : ℝ => (((n : ℝ) + 1) * (1 - t) ^ n) • exp (t • z))
      MeasureTheory.volume 0 1 :=
    ((continuous_const.mul ((continuous_const.sub continuous_id).pow n)).smul hc).intervalIntegrable 0 1
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hasDerivAt_pow_smul_exp n z t)
    (hint1.sub hint2)
  rw [intervalIntegral.integral_sub hint1 hint2] at hFTC
  simp only [sub_self, ne_eq, Nat.add_one_ne_zero, not_false_eq_true, zero_pow, zero_smul, sub_zero, one_pow,
    one_smul, exp_zero, zero_sub] at hFTC
  have e1 : (fun t : ℝ => (1 - t) ^ (n + 1) • (z * exp (t • z))) =
      fun t => ContinuousLinearMap.mul ℝ 𝔸 z ((1 - t) ^ (n + 1) • exp (t • z)) := by
    funext t
    rw [ContinuousLinearMap.mul_apply', mul_smul_comm]
  have e2 : (fun t : ℝ => (((n : ℝ) + 1) * (1 - t) ^ n) • exp (t • z)) =
      fun t => ((n : ℝ) + 1) • ((1 - t) ^ n • exp (t • z)) := by
    funext t
    rw [mul_smul]
  rw [e1, e2, ContinuousLinearMap.intervalIntegral_comp_comm _ (intervalIntegrable_pow_smul_exp (n + 1) z),
    intervalIntegral.integral_smul, ContinuousLinearMap.mul_apply'] at hFTC
  rw [← sub_eq_zero]
  have : ((n : ℝ) + 1) • (∫ t in (0 : ℝ)..1, (1 - t) ^ n • exp (t • z)) -  -- totalisation-audit: allow interval integral of a continuous integrand on [0, 1]
      (1 + z * ∫ t in (0 : ℝ)..1, (1 - t) ^ (n + 1) • exp (t • z)) =  -- totalisation-audit: allow interval integral of a continuous integrand on [0, 1]
      -((z * ∫ t in (0 : ℝ)..1, (1 - t) ^ (n + 1) • exp (t • z)) -  -- totalisation-audit: allow interval integral of a continuous integrand on [0, 1]
        ((n : ℝ) + 1) • (∫ t in (0 : ℝ)..1, (1 - t) ^ n • exp (t • z)) - -1) := by abel  -- totalisation-audit: allow interval integral of a continuous integrand on [0, 1]
  rw [this, hFTC, sub_self, neg_zero]

/-- Taylor's formula with the remainder written through `∫_0^1 (1-t)^n exp(t z) dt`. -/
lemma exp_eq_sum_add_integral (n : ℕ) (z : 𝔸) :
    exp z = ∑ m ∈ Finset.range (n + 1), ((m.factorial : ℝ)⁻¹) • z ^ m +  -- totalisation-audit: allow inverse of a positive factorial
      ((n.factorial : ℝ)⁻¹) • (z ^ (n + 1) * ∫ t in (0 : ℝ)..1, (1 - t) ^ n • exp (t • z)) := by  -- totalisation-audit: allow continuous integrand on [0, 1]; inverse of a positive factorial
  induction n with
  | zero =>
    have h := mul_integral_exp_smul z
    simp only [zero_add, Finset.range_one, Finset.sum_singleton, Nat.factorial_zero, Nat.cast_one, inv_one,
      one_smul, pow_zero, pow_one, one_smul]
    rw [h]
    abel
  | succ n ih =>
    have hI : (∫ t in (0 : ℝ)..1, (1 - t) ^ n • exp (t • z)) =  -- totalisation-audit: allow interval integral of a continuous integrand on [0, 1]
        ((n : ℝ) + 1)⁻¹ • (1 + z * ∫ t in (0 : ℝ)..1, (1 - t) ^ (n + 1) • exp (t • z)) := by  -- totalisation-audit: allow interval integral of a continuous integrand on [0, 1]
      rw [← smul_integral_pow_smul_exp n z, smul_smul, inv_mul_cancel₀ (by positivity), one_smul]
    rw [ih, hI, Finset.sum_range_succ _ (n + 1), mul_smul_comm, mul_add, mul_one, ← mul_assoc, ← pow_succ,
      Nat.factorial_succ, Nat.cast_mul, mul_inv]
    push_cast
    module

/-- **Taylor's formula with integral remainder** for `exp`:
`exp z = ∑_{m ≤ n} z^m / m! + z^{n+1} / (n+1)! · R_{n+1}(z)`. -/
theorem exp_eq_sum_add_expRem (n : ℕ) (z : 𝔸) :
    exp z = ∑ m ∈ Finset.range (n + 1), ((m.factorial : ℝ)⁻¹) • z ^ m +  -- totalisation-audit: allow inverse of a positive factorial
      (((n + 1).factorial : ℝ)⁻¹) • (z ^ (n + 1) * expRem n z) := by
  rw [exp_eq_sum_add_integral n z, expRem, mul_smul_comm, smul_smul, Nat.factorial_succ, Nat.cast_mul]
  congr 2
  push_cast
  field_simp

omit [CompleteSpace 𝔸] in
/-- `‖R_{n+1}(z)‖ ≤ 1` when `‖exp(t z)‖ ≤ 1` for `t ∈ [0, 1]`. -/
theorem norm_expRem_le_one (n : ℕ) (z : 𝔸) (h : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖exp (t • z)‖ ≤ 1) :
    ‖expRem n z‖ ≤ 1 := by
  have hb : ‖∫ t in (0 : ℝ)..1, (1 - t) ^ n • exp (t • z)‖ ≤ ∫ t in (0 : ℝ)..1, (1 - t) ^ n := by  -- totalisation-audit: allow interval integral of a continuous integrand on [0, 1]
    refine intervalIntegral.norm_integral_le_of_norm_le zero_le_one
      (Filter.Eventually.of_forall fun t ht => ?_) ?_
    · have ht' : t ∈ Set.Icc (0 : ℝ) 1 := Set.Ioc_subset_Icc_self ht
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (by linarith [ht'.2]) n)]
      exact mul_le_of_le_one_right (pow_nonneg (by linarith [ht'.2]) n) (h t ht')
    · exact ((continuous_const.sub continuous_id).pow n).intervalIntegrable 0 1
  have hval : ∫ t in (0 : ℝ)..1, (1 - t) ^ n = ((n : ℝ) + 1)⁻¹ := by  -- totalisation-audit: allow interval integral of a continuous integrand on [0, 1]
    rw [intervalIntegral.integral_comp_sub_left (fun t : ℝ => t ^ n) 1]
    simp only [sub_self, sub_zero, integral_pow]
    simp
  rw [expRem, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
  calc ((n : ℝ) + 1) * ‖∫ t in (0 : ℝ)..1, (1 - t) ^ n • exp (t • z)‖  -- totalisation-audit: allow interval integral of a continuous integrand on [0, 1]
      ≤ ((n : ℝ) + 1) * ((n : ℝ) + 1)⁻¹ := by
        rw [← hval]
        exact mul_le_mul_of_nonneg_left hb (by positivity)
    _ = 1 := mul_inv_cancel₀ (by positivity)

end BakerCampbellHausdorff
