import GaussianBlockSpin.ProductMoments

/-! Moments of powers under a law `γ₁` with `∫ e^{2|x|} dγ₁ ≤ K` and under its restriction `ν₁ = γ₁(· | [-β, β])`
(`γ₁([-β, β]) ≥ 1/2`):
* abs_integral_pow_le: `|∫ x^q dγ₁| ≤ q! K`;
* abs_integral_pow_cond_le: `|∫ x^q dν₁| ≤ 2 q! K` (integral_cond_le_two_mul: `ν₁` has at most twice the integrals of
  nonnegative functions);
* abs_integral_pow_cond_sub_le: `|∫ x^q dν₁ - ∫ x^q dγ₁| ≤ (2K + 1) q! K e^{-β}`;
* one_le_K: `K ≥ 1`.
The bounds for products of monomials are in ProductMomentBounds. -/

namespace GaussianBlockSpin

open MeasureTheory ProbabilityTheory Real

variable (γ₁ : Measure ℝ) [IsProbabilityMeasure γ₁] {K β : ℝ}

/-- `|x|^q ≤ q! e^{2|x|}`. -/
lemma abs_pow_le_factorial_mul_exp (q : ℕ) (x : ℝ) : |x| ^ q ≤ q.factorial * exp (2 * |x|) := by
  have h := abs_pow_mul_exp_le q x
  have h1 : |x| ^ q ≤ |x| ^ q * exp |x| := le_mul_of_one_le_right (by positivity) (one_le_exp (abs_nonneg x))
  linarith

omit [IsProbabilityMeasure γ₁] in
lemma integrable_pow_of_exp (hint : Integrable (fun x => exp (2 * |x|)) γ₁) (q : ℕ) :
    Integrable (fun x : ℝ => x ^ q) γ₁ :=
  (hint.const_mul (q.factorial : ℝ)).mono' (by fun_prop) (ae_of_all _ fun x => by
    rw [Real.norm_eq_abs, abs_pow]; exact abs_pow_le_factorial_mul_exp q x)

omit [IsProbabilityMeasure γ₁] in
lemma abs_integral_pow_le (hint : Integrable (fun x => exp (2 * |x|)) γ₁) (hK : ∫ x, exp (2 * |x|) ∂γ₁ ≤ K)
    (q : ℕ) : |∫ x, x ^ q ∂γ₁| ≤ q.factorial * K := by
  calc |∫ x, x ^ q ∂γ₁| ≤ ∫ x, |x ^ q| ∂γ₁ := abs_integral_le_integral_abs
    _ ≤ ∫ x, (q.factorial : ℝ) * exp (2 * |x|) ∂γ₁ :=
        integral_mono (integrable_pow_of_exp γ₁ hint q).abs (hint.const_mul _) fun x => by
          rw [abs_pow]; exact abs_pow_le_factorial_mul_exp q x
    _ = q.factorial * ∫ x, exp (2 * |x|) ∂γ₁ := integral_const_mul _ _
    _ ≤ q.factorial * K := by gcongr

omit [IsProbabilityMeasure γ₁] in
/-- The restricted law has the doubled exponential moment bound. -/
lemma integral_cond_le_two_mul {f : ℝ → ℝ} (hf0 : ∀ x, 0 ≤ f x) (hfi : Integrable f γ₁)
    (hp : 1 / 2 ≤ (γ₁ (Set.Icc (-β) β)).toReal) :
    ∫ x, f x ∂(ProbabilityTheory.cond γ₁ (Set.Icc (-β) β)) ≤ 2 * ∫ x, f x ∂γ₁ := by
  have hp0 : 0 < (γ₁ (Set.Icc (-β) β)).toReal := by linarith
  rw [ProbabilityTheory.cond, integral_smul_measure, smul_eq_mul, ENNReal.toReal_inv]
  have hinv : (γ₁ (Set.Icc (-β) β)).toReal⁻¹ ≤ 2 := by rw [inv_le_comm₀ hp0 two_pos]; linarith
  have hset : ∫ x in Set.Icc (-β) β, f x ∂γ₁ ≤ ∫ x, f x ∂γ₁ :=
    setIntegral_le_integral hfi (ae_of_all _ hf0)
  have hnn : 0 ≤ ∫ x in Set.Icc (-β) β, f x ∂γ₁ := setIntegral_nonneg measurableSet_Icc fun x _ => hf0 x
  calc (γ₁ (Set.Icc (-β) β)).toReal⁻¹ * ∫ x in Set.Icc (-β) β, f x ∂γ₁
      ≤ 2 * ∫ x in Set.Icc (-β) β, f x ∂γ₁ := mul_le_mul_of_nonneg_right hinv hnn
    _ ≤ 2 * ∫ x, f x ∂γ₁ := by gcongr

omit [IsProbabilityMeasure γ₁] in
lemma integrable_cond_of_integrable {f : ℝ → ℝ} (hfi : Integrable f γ₁)
    (hp : 1 / 2 ≤ (γ₁ (Set.Icc (-β) β)).toReal) :
    Integrable f (ProbabilityTheory.cond γ₁ (Set.Icc (-β) β)) := by
  rw [ProbabilityTheory.cond]
  refine (hfi.restrict).smul_measure (ENNReal.inv_ne_top.mpr fun h => ?_)
  rw [h, ENNReal.toReal_zero] at hp
  linarith

lemma one_le_K (hint : Integrable (fun x => exp (2 * |x|)) γ₁) (hK : ∫ x, exp (2 * |x|) ∂γ₁ ≤ K) : 1 ≤ K := by
  have : ∫ x, (1 : ℝ) ∂γ₁ ≤ ∫ x, exp (2 * |x|) ∂γ₁ :=
    integral_mono (integrable_const 1) hint fun x => one_le_exp (by positivity)
  simp at this
  linarith

omit [IsProbabilityMeasure γ₁] in
lemma abs_integral_pow_cond_le (hint : Integrable (fun x => exp (2 * |x|)) γ₁)
    (hK : ∫ x, exp (2 * |x|) ∂γ₁ ≤ K) (hp : 1 / 2 ≤ (γ₁ (Set.Icc (-β) β)).toReal) (q : ℕ) :
    |∫ x, x ^ q ∂(ProbabilityTheory.cond γ₁ (Set.Icc (-β) β))| ≤ 2 * (q.factorial * K) := by
  have hpow := integrable_pow_of_exp γ₁ hint q
  calc |∫ x, x ^ q ∂(ProbabilityTheory.cond γ₁ (Set.Icc (-β) β))|
      ≤ ∫ x, |x ^ q| ∂(ProbabilityTheory.cond γ₁ (Set.Icc (-β) β)) := abs_integral_le_integral_abs
    _ ≤ 2 * ∫ x, |x ^ q| ∂γ₁ := integral_cond_le_two_mul γ₁ (fun x => abs_nonneg _) hpow.abs hp
    _ ≤ 2 * ∫ x, (q.factorial : ℝ) * exp (2 * |x|) ∂γ₁ := by
        refine mul_le_mul_of_nonneg_left (integral_mono hpow.abs (hint.const_mul _) fun x => ?_) two_pos.le
        show |x ^ q| ≤ (q.factorial : ℝ) * exp (2 * |x|)
        rw [abs_pow]; exact abs_pow_le_factorial_mul_exp q x
    _ = 2 * (q.factorial * ∫ x, exp (2 * |x|) ∂γ₁) := by rw [integral_const_mul]
    _ ≤ 2 * (q.factorial * K) := by gcongr

lemma abs_integral_pow_cond_sub_le (hβ : 0 ≤ β) (hint : Integrable (fun x => exp (2 * |x|)) γ₁)
    (hK : ∫ x, exp (2 * |x|) ∂γ₁ ≤ K) (hp : 1 / 2 ≤ (γ₁ (Set.Icc (-β) β)).toReal) (q : ℕ) :
    |∫ x, x ^ q ∂(ProbabilityTheory.cond γ₁ (Set.Icc (-β) β)) - ∫ x, x ^ q ∂γ₁| ≤
      (2 * K + 1) * q.factorial * K * exp (-β) := by
  refine abs_integral_cond_sub_le γ₁ hβ hint hK hp (by fun_prop) (Nat.cast_nonneg _) fun x => ?_
  have h := Real.pow_div_factorial_le_exp |x| (abs_nonneg x) q
  have hf : (0 : ℝ) < q.factorial := by exact_mod_cast Nat.factorial_pos q
  rw [div_le_iff₀ hf] at h
  rw [abs_pow]
  linarith

end GaussianBlockSpin
