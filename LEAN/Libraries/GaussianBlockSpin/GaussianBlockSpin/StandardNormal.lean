import GaussianBlockSpin.MonomialBounds

/-! The standard normal law `γ₁ = N(0, 1)` as the law of the independent coordinates:
* integrable_exp_two_abs, integral_exp_two_abs_le: `∫ e^{2|x|} dγ₁ ≤ 2 e²`;
* integrable_one_add_abs_pow: every `(1 + |x|)^r` is integrable;
* half_le_measure_Icc: `γ₁([-β, β]) ≥ 1/2` for `β ≥ 2`. -/

namespace GaussianBlockSpin

open MeasureTheory ProbabilityTheory Real

/-- `e^{c|x|} ≤ e^{cx} + e^{-cx}`. -/
lemma exp_mul_abs_le (c x : ℝ) : exp (c * |x|) ≤ exp (c * x) + exp (-c * x) := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]; linarith [exp_pos (-c * x)]
  · rw [abs_of_nonpos hx, show c * -x = -c * x by ring]; linarith [exp_pos (c * x)]

lemma integrable_exp_mul_abs (c : ℝ) :
    Integrable (fun x => exp (c * |x|)) (gaussianReal 0 1) := by
  refine ((integrable_exp_mul_gaussianReal c).add (integrable_exp_mul_gaussianReal (-c))).mono' (by fun_prop)
    (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
  exact exp_mul_abs_le c x

lemma integrable_exp_two_abs : Integrable (fun x => exp (2 * |x|)) (gaussianReal 0 1) :=
  integrable_exp_mul_abs 2

lemma integral_exp_two_abs_le : ∫ x, exp (2 * |x|) ∂(gaussianReal 0 1) ≤ 2 * exp 2 := by
  have h1 := integrable_exp_mul_gaussianReal (μ := 0) (v := 1) 2
  have h2 := integrable_exp_mul_gaussianReal (μ := 0) (v := 1) (-2)
  have hm : ∀ t : ℝ, ∫ x, exp (t * x) ∂(gaussianReal 0 1) = exp (t ^ 2 / 2) := fun t => by
    have := congrFun (mgf_fun_id_gaussianReal (μ := 0) (v := 1)) t
    simp only [mgf] at this
    rw [this]; congr 1; push_cast; ring
  calc ∫ x, exp (2 * |x|) ∂(gaussianReal 0 1)
      ≤ ∫ x, (exp (2 * x) + exp (-2 * x)) ∂(gaussianReal 0 1) :=
        integral_mono integrable_exp_two_abs (h1.add h2) fun x => exp_mul_abs_le 2 x
    _ = exp 2 + exp 2 := by
        rw [integral_add h1 h2, hm 2, hm (-2)]
        norm_num
    _ = 2 * exp 2 := by ring

/-- `(1 + |x|)^r ≤ r! e · e^{|x|}`. -/
lemma integrable_one_add_abs_pow (r : ℕ) :
    Integrable (fun x : ℝ => (1 + |x|) ^ r) (gaussianReal 0 1) := by
  refine ((integrable_exp_mul_abs 1).const_mul ((r.factorial : ℝ) * exp 1)).mono' (by fun_prop)
    (ae_of_all _ fun x => ?_)
  have hpos : 0 ≤ 1 + |x| := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hpos r)]
  have h := Real.pow_div_factorial_le_exp (1 + |x|) hpos r
  have hf : (0 : ℝ) < r.factorial := by exact_mod_cast Nat.factorial_pos r
  rw [div_le_iff₀ hf] at h
  calc (1 + |x|) ^ r ≤ exp (1 + |x|) * r.factorial := h
    _ = r.factorial * exp 1 * exp (1 * |x|) := by rw [exp_add, one_mul]; ring

/-- `γ₁([-β, β]) ≥ 1/2` for `β ≥ 2`. -/
lemma half_le_measure_Icc {β : ℝ} (hβ : 2 ≤ β) : 1 / 2 ≤ ((gaussianReal 0 1) (Set.Icc (-β) β)).toReal := by
  have htail := measure_abs_gt_le (gaussianReal 0 1) integrable_exp_two_abs integral_exp_two_abs_le β
  rw [← compl_Icc_eq] at htail
  have hcompl : ((gaussianReal 0 1) (Set.Icc (-β) β)ᶜ).toReal = 1 - ((gaussianReal 0 1) (Set.Icc (-β) β)).toReal := by
    rw [prob_compl_eq_one_sub measurableSet_Icc, ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top,
      ENNReal.toReal_one]
  rw [hcompl] at htail
  have hsmall : 2 * exp 2 * exp (-(2 * β)) ≤ 1 / 2 := by
    rw [mul_assoc, ← exp_add]
    have h1 : exp (2 + -(2 * β)) ≤ exp (-2) := exp_le_exp.mpr (by linarith)
    have h2 : exp (-2 : ℝ) < 1 / 4 := by
      rw [exp_neg, inv_lt_comm₀ (exp_pos 2) (by norm_num)]
      have he := Real.exp_one_gt_d9
      have h22 : exp (2 : ℝ) = exp 1 * exp 1 := by rw [← exp_add]; norm_num
      rw [h22]
      nlinarith
    nlinarith [exp_pos (-2 : ℝ)]
  linarith

end GaussianBlockSpin
