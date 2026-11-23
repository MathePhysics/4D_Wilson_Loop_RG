import GaussianBlockSpin.StandardNormal
import GaussianBlockSpin.Pullback
import GaussianBlockSpin.RestrictedProduct

/-! Ingredients of the Gaussian part of the assembly, for the Gaussian law `μ_A = A_* N(0,1)^{⊗ι}`:
* cumulantSum_map: the truncated expectations under `μ_A` are those of `H ∘ A` under `N(0,1)^{⊗ι}`;
* abs_mulVec_le: `|ξ|_∞ ≤ β` gives `|(A ξ)_x| ≤ K_A β` (row sums `≤ K_A`);
* measure_Icc_pow_ge: `N(0,1)([-β, β])^n ≥ e^{-4 e² e^{-2β} n}` for `β ≥ 2`. -/

namespace GaussianBlockSpin

open MeasureTheory ProbabilityTheory Real Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Gaussian law `μ_A = A_* N(0,1)^{⊗ι}`. -/
noncomputable def gaussPush (A : Matrix ι ι ℝ) : Measure (ι → ℝ) :=
  (Measure.pi fun _ : ι => gaussianReal 0 1).map fun ξ => A *ᵥ ξ

omit [DecidableEq ι] in
lemma measurable_mulVec (A : Matrix ι ι ℝ) : Measurable fun ξ : ι → ℝ => A *ᵥ ξ :=
  (Continuous.matrix_mulVec continuous_const continuous_id).measurable

instance (A : Matrix ι ι ℝ) : IsProbabilityMeasure (gaussPush A) := by
  unfold gaussPush
  exact ⟨by rw [Measure.map_apply (measurable_mulVec A) MeasurableSet.univ]; simp⟩

omit [DecidableEq ι] in
/-- Truncated expectations under the pushforward. -/
lemma cumulantSum_map (A : Matrix ι ι ℝ) {H : (ι → ℝ) → ℝ} (hH : Measurable H) (t : ℕ) :
    cumulantSum (gaussPush A) H t = cumulantSum (Measure.pi fun _ : ι => gaussianReal 0 1) (fun ξ => H (A *ᵥ ξ)) t := by
  have hm : moments (gaussPush A) H = moments (Measure.pi fun _ : ι => gaussianReal 0 1) (fun ξ => H (A *ᵥ ξ)) := by
    funext n
    unfold moments gaussPush
    rw [integral_map (measurable_mulVec A).aemeasurable (hH.pow_const n).aestronglyMeasurable]
  unfold cumulantSum
  rw [hm]

omit [DecidableEq ι] in
/-- The sup-norm cube is preserved up to the row sums. -/
lemma abs_mulVec_le (A : Matrix ι ι ℝ) {KA β : ℝ} (hKA : ∀ x, ∑ y, |A x y| ≤ KA) (hβ : 0 ≤ β) {ξ : ι → ℝ}
    (hξ : ∀ c, ξ c ∈ Set.Icc (-β) β) (x : ι) : |(A *ᵥ ξ) x| ≤ KA * β := by
  calc |(A *ᵥ ξ) x| = |∑ y, A x y * ξ y| := rfl
    _ ≤ ∑ y, |A x y| * |ξ y| := (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq (by simp [abs_mul]))
    _ ≤ ∑ y, |A x y| * β := Finset.sum_le_sum fun y _ =>
        mul_le_mul_of_nonneg_left (abs_le.mpr ⟨(hξ y).1, (hξ y).2⟩) (abs_nonneg _)
    _ = (∑ y, |A x y|) * β := by rw [Finset.sum_mul]
    _ ≤ KA * β := mul_le_mul_of_nonneg_right (hKA x) hβ

/-- `1 - q ≥ e^{-2q}` for `0 ≤ q ≤ 1/2`. -/
lemma exp_neg_two_mul_le_one_sub {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2) : exp (-(2 * q)) ≤ 1 - q := by
  have hpos : 0 < 1 - q := by linarith
  have hlog := Real.one_sub_inv_le_log_of_pos hpos
  have h1 : 1 - (1 - q)⁻¹ ≥ -(2 * q) := by
    have h2 : (1 - q)⁻¹ ≤ 1 + 2 * q := by
      rw [inv_le_iff_one_le_mul₀ hpos]
      nlinarith
    linarith
  calc exp (-(2 * q)) ≤ exp (log (1 - q)) := exp_le_exp.mpr (h1.le.trans hlog)
    _ = 1 - q := exp_log hpos

/-- **The cut-off normalisation**: `N(0,1)([-β, β])^n ≥ e^{-4 e² e^{-2β} n}` for `β ≥ 2`. -/
lemma measure_Icc_pow_ge {β : ℝ} (hβ : 2 ≤ β) (n : ℕ) :
    ENNReal.ofReal (exp (-(4 * exp 2 * exp (-(2 * β)) * n))) ≤ (gaussianReal 0 1 (Set.Icc (-β) β)) ^ n := by
  set q := 2 * exp 2 * exp (-(2 * β)) with hq
  have htail := measure_abs_gt_le (gaussianReal 0 1) integrable_exp_two_abs integral_exp_two_abs_le β
  rw [← compl_Icc_eq, prob_compl_eq_one_sub measurableSet_Icc,
    ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top, ENNReal.toReal_one] at htail
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q ≤ 1 / 2 := by
    have h := half_le_measure_Icc hβ
    have hsmall : q ≤ 1 / 2 := by
      rw [hq, mul_assoc, ← exp_add]
      have h1 : exp (2 + -(2 * β)) ≤ exp (-2) := exp_le_exp.mpr (by linarith)
      have h2 : exp (-2 : ℝ) < 1 / 4 := by
        rw [exp_neg, inv_lt_comm₀ (exp_pos 2) (by norm_num)]
        have he := Real.exp_one_gt_d9
        have h22 : exp (2 : ℝ) = exp 1 * exp 1 := by rw [← exp_add]; norm_num
        rw [h22]; nlinarith
      nlinarith [exp_pos (-2 : ℝ)]
    exact hsmall
  have hge : exp (-(2 * q)) ≤ (gaussianReal 0 1 (Set.Icc (-β) β)).toReal := by
    refine (exp_neg_two_mul_le_one_sub hq0 hq1).trans ?_
    linarith
  rw [← ENNReal.ofReal_toReal (measure_ne_top (gaussianReal 0 1) (Set.Icc (-β) β)), ← ENNReal.ofReal_pow
    ENNReal.toReal_nonneg]
  refine ENNReal.ofReal_le_ofReal ?_
  calc exp (-(4 * exp 2 * exp (-(2 * β)) * n)) = exp (-(2 * q)) ^ n := by
        rw [← exp_nat_mul]; congr 1; rw [hq]; ring
    _ ≤ _ := pow_le_pow_left₀ (exp_pos _).le hge n

end GaussianBlockSpin
