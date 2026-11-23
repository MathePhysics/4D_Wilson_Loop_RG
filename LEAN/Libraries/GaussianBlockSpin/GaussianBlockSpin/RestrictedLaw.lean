import Mathlib

/-! One coordinate of the independent variables: a probability law `γ₁` on `ℝ` with `∫ e^{2|x|} dγ₁ ≤ K`, and its
restriction `ν₁ = γ₁(· | [-β, β])` (the cut-off of [2]'s `χ̂` moved to the independent variables).
* measure_abs_gt_le: `γ₁(|x| > β) ≤ K e^{-2β}` (Markov);
* abs_pow_mul_exp_le: `|x|^q e^{|x|} ≤ q! e^{2|x|}`;
* abs_integral_cond_sub_le: for `|g(x)| ≤ G e^{|x|}`, `|∫ g dν₁ - ∫ g dγ₁| ≤ (2 K + 1) G K e^{-β}` when
  `γ₁([-β, β]) ≥ 1/2`. -/

namespace GaussianBlockSpin

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

variable (γ₁ : Measure ℝ) [IsProbabilityMeasure γ₁]

/-- `γ₁(|x| > β) ≤ e^{-2β} ∫ e^{2|x|}` (Markov's inequality). -/
lemma measure_abs_gt_le {K : ℝ} (hint : Integrable (fun x => exp (2 * |x|)) γ₁)
    (hK : ∫ x, exp (2 * |x|) ∂γ₁ ≤ K) (β : ℝ) :
    (γ₁ {x | β < |x|}).toReal ≤ K * exp (-(2 * β)) := by
  have hmarkov := mul_meas_ge_le_integral_of_nonneg (ae_of_all _ fun x => (exp_pos (2 * |x|)).le) hint
    (exp (2 * β))
  have hsub : {x : ℝ | β < |x|} ⊆ {x | exp (2 * β) ≤ exp (2 * |x|)} := fun x hx => by
    simp only [Set.mem_ofPred_eq] at hx ⊢
    exact exp_le_exp.mpr (by linarith)
  have hmono : (γ₁ {x | β < |x|}).toReal ≤ (γ₁ {x | exp (2 * β) ≤ exp (2 * |x|)}).toReal :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)
  have hpos := exp_pos (2 * β)
  calc (γ₁ {x | β < |x|}).toReal ≤ (γ₁ {x | exp (2 * β) ≤ exp (2 * |x|)}).toReal := hmono
    _ ≤ (∫ x, exp (2 * |x|) ∂γ₁) / exp (2 * β) := by
        rw [le_div_iff₀ hpos, mul_comm]
        simpa [Measure.real] using hmarkov
    _ ≤ K / exp (2 * β) := by gcongr
    _ = K * exp (-(2 * β)) := by rw [exp_neg, div_eq_mul_inv]

/-- `|x|^q e^{|x|} ≤ q! e^{2|x|}`. -/
lemma abs_pow_mul_exp_le (q : ℕ) (x : ℝ) : |x| ^ q * exp |x| ≤ q.factorial * exp (2 * |x|) := by
  have h := Real.pow_div_factorial_le_exp |x| (abs_nonneg x) q
  have hf : (0 : ℝ) < q.factorial := by exact_mod_cast Nat.factorial_pos q
  calc |x| ^ q * exp |x| = (|x| ^ q / q.factorial) * q.factorial * exp |x| := by field_simp
    _ ≤ exp |x| * q.factorial * exp |x| := by gcongr
    _ = q.factorial * exp (2 * |x|) := by rw [show 2 * |x| = |x| + |x| by ring, exp_add]; ring

lemma compl_Icc_eq (β : ℝ) : (Set.Icc (-β) β)ᶜ = {x : ℝ | β < |x|} := by
  ext x
  simp only [Set.mem_compl_iff, Set.mem_Icc, Set.mem_ofPred_eq, not_and_or, not_le, lt_abs]
  constructor
  · rintro (h | h)
    · right; linarith
    · left; exact h
  · rintro (h | h)
    · right; exact h
    · left; linarith

/-- **Restricted versus full law**: for `|g(x)| ≤ G e^{|x|}` and `γ₁([-β, β]) ≥ 1/2`,
`|∫ g d γ₁(· | [-β, β]) - ∫ g dγ₁| ≤ (2K + 1) G K e^{-β}`. -/
theorem abs_integral_cond_sub_le {β K G : ℝ} (hβ : 0 ≤ β) (hint : Integrable (fun x => exp (2 * |x|)) γ₁)
    (hK : ∫ x, exp (2 * |x|) ∂γ₁ ≤ K) (hp : 1 / 2 ≤ (γ₁ (Set.Icc (-β) β)).toReal) {g : ℝ → ℝ}
    (hg : Measurable g) (hG : 0 ≤ G) (hgb : ∀ x, |g x| ≤ G * exp |x|) :
    |∫ x, g x ∂(ProbabilityTheory.cond γ₁ (Set.Icc (-β) β)) - ∫ x, g x ∂γ₁| ≤ (2 * K + 1) * G * K * exp (-β) := by
  set s := Set.Icc (-β) β with hs
  have hsm : MeasurableSet s := measurableSet_Icc
  set p := (γ₁ s).toReal with hpdef
  have hp0 : 0 < p := by linarith
  have hK0 : 0 ≤ K := (integral_nonneg fun x => (exp_pos _).le).trans hK
  -- integrability of `g` and of the exponential weights
  have hint1 : Integrable (fun x => exp |x|) γ₁ :=
    hint.mono' (by fun_prop) (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]; exact exp_le_exp.mpr (by linarith [abs_nonneg x]))
  have hgi : Integrable g γ₁ :=
    (hint1.const_mul G).mono' hg.aestronglyMeasurable (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]; exact hgb x)
  have hE1 : ∫ x, exp |x| ∂γ₁ ≤ K := (integral_mono hint1 hint fun x =>
    exp_le_exp.mpr (by linarith [abs_nonneg x])).trans hK
  -- the conditional integral
  have hcond : ∫ x, g x ∂(ProbabilityTheory.cond γ₁ s) = p⁻¹ * ∫ x in s, g x ∂γ₁ := by
    rw [ProbabilityTheory.cond, integral_smul_measure, smul_eq_mul, ENNReal.toReal_inv]
  have hsplit : ∫ x, g x ∂γ₁ = ∫ x in s, g x ∂γ₁ + ∫ x in sᶜ, g x ∂γ₁ :=
    (integral_add_compl hsm hgi).symm
  have hIs : |∫ x in s, g x ∂γ₁| ≤ G * K := by
    calc |∫ x in s, g x ∂γ₁| ≤ ∫ x in s, |g x| ∂γ₁ := abs_integral_le_integral_abs
      _ ≤ ∫ x, |g x| ∂γ₁ := setIntegral_le_integral hgi.abs (ae_of_all _ fun x => abs_nonneg _)
      _ ≤ ∫ x, G * exp |x| ∂γ₁ := integral_mono hgi.abs (hint1.const_mul G) hgb
      _ = G * ∫ x, exp |x| ∂γ₁ := integral_const_mul _ _
      _ ≤ G * K := mul_le_mul_of_nonneg_left hE1 hG
  have hcompl : (γ₁ sᶜ).toReal ≤ K * exp (-(2 * β)) := by
    rw [hs, compl_Icc_eq]; exact measure_abs_gt_le γ₁ hint hK β
  have h1p : 1 - p = (γ₁ sᶜ).toReal := by
    rw [hpdef, prob_compl_eq_one_sub hsm, ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top,
      ENNReal.toReal_one]
  have hIc : |∫ x in sᶜ, g x ∂γ₁| ≤ G * K * exp (-β) := by
    calc |∫ x in sᶜ, g x ∂γ₁| ≤ ∫ x in sᶜ, |g x| ∂γ₁ := abs_integral_le_integral_abs
      _ ≤ ∫ x in sᶜ, G * exp (-β) * exp (2 * |x|) ∂γ₁ := by
          refine setIntegral_mono_on hgi.abs.integrableOn ((hint.const_mul _).integrableOn) hsm.compl
            fun x hx => ?_
          rw [hs, compl_Icc_eq] at hx
          refine (hgb x).trans ?_
          rw [mul_assoc, ← exp_add]
          exact mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by simp only [Set.mem_ofPred_eq] at hx; linarith)) hG
      _ ≤ ∫ x, G * exp (-β) * exp (2 * |x|) ∂γ₁ :=
          setIntegral_le_integral (hint.const_mul _) (ae_of_all _ fun x =>
            mul_nonneg (mul_nonneg hG (exp_pos _).le) (exp_pos _).le)
      _ = G * exp (-β) * ∫ x, exp (2 * |x|) ∂γ₁ := integral_const_mul _ _
      _ ≤ G * exp (-β) * K := mul_le_mul_of_nonneg_left hK (mul_nonneg hG (exp_pos _).le)
      _ = G * K * exp (-β) := by ring
  rw [hcond, hsplit]
  have hβ2 : exp (-(2 * β)) ≤ exp (-β) := exp_le_exp.mpr (by linarith)
  calc |p⁻¹ * ∫ x in s, g x ∂γ₁ - (∫ x in s, g x ∂γ₁ + ∫ x in sᶜ, g x ∂γ₁)|
      = |(1 - p) * p⁻¹ * ∫ x in s, g x ∂γ₁ - ∫ x in sᶜ, g x ∂γ₁| := by
        congr 1; field_simp; ring
    _ ≤ (1 - p) * p⁻¹ * |∫ x in s, g x ∂γ₁| + |∫ x in sᶜ, g x ∂γ₁| := by
        refine (abs_sub _ _).trans (add_le_add ?_ le_rfl)
        rw [abs_mul, abs_of_nonneg (mul_nonneg (by rw [h1p]; exact ENNReal.toReal_nonneg) (inv_nonneg.mpr hp0.le))]
    _ ≤ (K * exp (-β)) * 2 * (G * K) + G * K * exp (-β) := by
        have hinv : p⁻¹ ≤ 2 := by rw [inv_le_comm₀ hp0 two_pos]; linarith
        have h1 : 1 - p ≤ K * exp (-β) := by
          rw [h1p]; exact hcompl.trans (mul_le_mul_of_nonneg_left hβ2 hK0)
        have h1' : 0 ≤ 1 - p := by rw [h1p]; exact ENNReal.toReal_nonneg
        gcongr
    _ = (2 * K + 1) * G * K * exp (-β) := by ring

end GaussianBlockSpin
