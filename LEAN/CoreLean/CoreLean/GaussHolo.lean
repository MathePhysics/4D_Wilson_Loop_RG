/-
Holomorphy of parametric Gaussian integrals, for `lem:complex-gaussian` of BALABAN_CORE.tex (`9c56d4590aff`): if
`‖Φ(A)‖ ≤ We^{½α|A|²}` and `Re⟨A, QA⟩ - α|A|² ≥ q|A|²` for the `(Q, v)` of an open set `U`, then
`J(Q, v) = ∫e^{-½⟨A, QA⟩ - ⟨A, v⟩}Φ(A)dA` is holomorphic on `U` (differentiation under the integral, dominated by a
product of one-dimensional Gaussians). The matrices `Q` are taken as functions `ι → ι → ℂ`, with the supremum norm.
-/
import CoreLean.GaussIntegral

open Matrix Complex MeasureTheory Real

noncomputable section

namespace CoreLean
namespace ComplexGauss

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `|A|² = Σ_iA_i²`. -/
def nsq (x : ι → ℝ) : ℝ := ∑ i, x i ^ 2

/-- `Σ_i|A_i|`. -/
def l1 (x : ι → ℝ) : ℝ := ∑ i, |x i|

lemma nsq_nonneg (x : ι → ℝ) : 0 ≤ nsq x := Finset.sum_nonneg fun i _ => sq_nonneg _

lemma l1_nonneg (x : ι → ℝ) : 0 ≤ l1 x := Finset.sum_nonneg fun i _ => abs_nonneg _

/-- `|Re⟨A, v⟩| ≤ Σ_i|A_i|·‖v‖`. -/
lemma norm_dot_le (x : ι → ℝ) (v : ι → ℂ) : ‖cV x ⬝ᵥ v‖ ≤ l1 x * ‖v‖ := by
  unfold dotProduct l1
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (norm_le_pi_norm v i) (abs_nonneg _)

/-- The entry `(i, j)` of the matrix component, a continuous linear functional of norm at most `1`. -/
def entryL (i j : ι) : ((ι → ι → ℂ) × (ι → ℂ)) →L[ℂ] ℂ :=
  (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => ℂ) j).comp
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => ι → ℂ) i).comp
      (ContinuousLinearMap.fst ℂ (ι → ι → ℂ) (ι → ℂ)))

/-- The coordinate `i` of the vector component. -/
def coordL (i : ι) : ((ι → ι → ℂ) × (ι → ℂ)) →L[ℂ] ℂ :=
  (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => ℂ) i).comp (ContinuousLinearMap.snd ℂ (ι → ι → ℂ) (ι → ℂ))

/-- The exponent `ℓ_A(Q, v) = -½⟨A, QA⟩ - ⟨A, v⟩` as a continuous linear functional of `(Q, v)`. -/
def ellL (x : ι → ℝ) : ((ι → ι → ℂ) × (ι → ℂ)) →L[ℂ] ℂ :=
  ∑ i, ∑ j, ((-(1 / 2) * x i * x j : ℝ) : ℂ) • entryL i j + ∑ i, ((-x i : ℝ) : ℂ) • coordL i

lemma ellL_apply (x : ι → ℝ) (p : (ι → ι → ℂ) × (ι → ℂ)) :
    ellL x p = -(1 / 2) * qf (Matrix.of p.1) x - cV x ⬝ᵥ p.2 := by
  simp only [ellL, ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_sum', Finset.sum_apply,
    ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul, entryL, coordL, ContinuousLinearMap.coe_comp',
    Function.comp_apply, ContinuousLinearMap.coe_snd', ContinuousLinearMap.coe_fst', ContinuousLinearMap.proj_apply,
    qf, dotProduct, mulVec, cV, Matrix.of_apply]
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast; ring
  · exact Finset.sum_congr rfl fun i _ => by push_cast; ring

/-- `|⟨A, QA⟩| ≤ (Σ_i|A_i|)²‖Q‖`. -/
lemma norm_qf_le (Q : ι → ι → ℂ) (x : ι → ℝ) : ‖qf (Matrix.of Q) x‖ ≤ l1 x ^ 2 * ‖Q‖ := by
  unfold qf l1
  simp only [dotProduct, mulVec, Matrix.of_apply, cV]
  have hrow : ∀ i, ‖∑ j, Q i j * (x j : ℂ)‖ ≤ ∑ j, ‖Q‖ * |x j| := fun i =>
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right ((norm_le_pi_norm (Q i) j).trans (norm_le_pi_norm Q i)) (abs_nonneg _))
  calc ‖∑ i, (x i : ℂ) * ∑ j, Q i j * (x j : ℂ)‖ ≤ ∑ i, ∑ j, |x i| * |x j| * ‖Q‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          calc |x i| * ‖∑ j, Q i j * (x j : ℂ)‖ ≤ |x i| * ∑ j, ‖Q‖ * |x j| :=
                mul_le_mul_of_nonneg_left (hrow i) (abs_nonneg _)
            _ = ∑ j, |x i| * |x j| * ‖Q‖ := by
                rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring)
    _ = (∑ i, |x i|) ^ 2 * ‖Q‖ := by
        rw [pow_two, Finset.sum_mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by rw [Finset.sum_mul]

lemma norm_ellL (x : ι → ℝ) : ‖ellL x‖ ≤ 1 / 2 * l1 x ^ 2 + l1 x := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by have := l1_nonneg x; positivity) fun p => ?_
  rw [ellL_apply]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, norm_neg, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]
  have h1 := norm_qf_le p.1 x
  have h2 := norm_dot_le x p.2
  have h3 : ‖p.1‖ ≤ ‖p‖ := norm_fst_le p
  have h4 : ‖p.2‖ ≤ ‖p‖ := norm_snd_le p
  have hl := l1_nonneg x
  calc 1 / 2 * ‖qf (Matrix.of p.1) x‖ + ‖cV x ⬝ᵥ p.2‖ ≤ 1 / 2 * (l1 x ^ 2 * ‖p‖) + l1 x * ‖p‖ := by
        gcongr
        · exact h1.trans (mul_le_mul_of_nonneg_left h3 (sq_nonneg _))
        · exact h2.trans (mul_le_mul_of_nonneg_left h4 hl)
    _ = (1 / 2 * l1 x ^ 2 + l1 x) * ‖p‖ := by ring

lemma continuous_ellL : Continuous (ellL (ι := ι)) := by
  unfold ellL
  refine Continuous.add (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_)
    (continuous_finsetSum _ fun i _ => ?_)
  · exact (Complex.continuous_ofReal.comp (((continuous_const.mul (continuous_apply i)).mul
      (continuous_apply j)))).smul continuous_const
  · exact (Complex.continuous_ofReal.comp (continuous_apply i).neg).smul continuous_const

/-- `½s² + s ≤ e^s` for `s ≥ 0`. -/
lemma poly_le_exp {s : ℝ} (hs : 0 ≤ s) : 1 / 2 * s ^ 2 + s ≤ Real.exp s := by
  have h := Real.quadratic_le_exp_of_nonneg hs
  linarith

/-- `-½qt² + ct ≤ -¼qt² + c²/q`. -/
lemma gauss_lin_le {q : ℝ} (hq : 0 < q) (c t : ℝ) : -(1 / 2) * q * t ^ 2 + c * t ≤ -(q / 4) * t ^ 2 + c ^ 2 / q := by
  have : 0 ≤ (q * t - 2 * c) ^ 2 / (4 * q) := by positivity
  have e : (q * t - 2 * c) ^ 2 / (4 * q) = q / 4 * t ^ 2 - c * t + c ^ 2 / q := by field_simp; ring
  linarith

/-- **The dominating function**: `e^{-½q|A|² + cΣ|A_i|} ≤ e^{nc²/q}Π_ie^{-¼qA_i²}`. -/
lemma dom_le {q : ℝ} (hq : 0 < q) (c : ℝ) (x : ι → ℝ) :
    Real.exp (-(1 / 2) * q * nsq x + c * l1 x) ≤
      Real.exp (Fintype.card ι * (c ^ 2 / q)) * ∏ i, Real.exp (-(q / 4) * x i ^ 2) := by
  rw [← Real.exp_sum, ← Real.exp_add, Real.exp_le_exp]
  unfold nsq l1
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  have h : ∀ i, -(1 / 2) * q * x i ^ 2 + c * |x i| ≤ -(q / 4) * x i ^ 2 + c ^ 2 / q := fun i => by
    have := gauss_lin_le hq c |x i|
    rwa [sq_abs] at this
  calc ∑ i, (-(1 / 2) * q * x i ^ 2 + c * |x i|) ≤ ∑ i, (-(q / 4) * x i ^ 2 + c ^ 2 / q) :=
        Finset.sum_le_sum fun i _ => h i
    _ = Fintype.card ι * (c ^ 2 / q) + ∑ i, -(q / 4) * x i ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, add_comm]

lemma integrable_dom {q : ℝ} (hq : 0 < q) (K : ℝ) :
    Integrable (fun x : ι → ℝ => K * ∏ i, Real.exp (-(q / 4) * x i ^ 2)) := by
  refine Integrable.const_mul ?_ K
  exact Integrable.fintype_prod (f := fun _ (t : ℝ) => Real.exp (-(q / 4) * t ^ 2))
    fun i => integrable_exp_neg_mul_sq (by positivity)

/-- `Re ℓ_A(Q, v) ≤ -½Re⟨A, QA⟩ + Σ|A_i|‖v‖`. -/
lemma re_ell_le (x : ι → ℝ) (p : (ι → ι → ℂ) × (ι → ℂ)) :
    (ellL x p).re ≤ -(1 / 2) * (qf (Matrix.of p.1) x).re + l1 x * ‖p.2‖ := by
  rw [ellL_apply, Complex.sub_re]
  have h1 : (-(1 / 2) * qf (Matrix.of p.1) x).re = -(1 / 2) * (qf (Matrix.of p.1) x).re := by simp
  have h2 : -(cV x ⬝ᵥ p.2).re ≤ l1 x * ‖p.2‖ :=
    (neg_le_abs _).trans ((Complex.abs_re_le_norm _).trans (norm_dot_le x p.2))
  rw [h1]; linarith

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- **Holomorphy of the parametric Gaussian integral**. -/
theorem differentiableOn_J (Φ : (ι → ℝ) → F) (hΦm : AEStronglyMeasurable Φ volume) {W α q : ℝ} (hq : 0 < q)
    (hΦ : ∀ x, ‖Φ x‖ ≤ W * Real.exp (1 / 2 * α * nsq x)) {U : Set ((ι → ι → ℂ) × (ι → ℂ))} (hU : IsOpen U)
    (hUq : ∀ p ∈ U, ∀ x, (qf (Matrix.of p.1) x).re - α * nsq x ≥ q * nsq x) :
    DifferentiableOn ℂ (fun p => ∫ x, cexp (ellL x p) • Φ x) U := by
  intro p0 hp0
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU p0 hp0
  have hW : 0 ≤ W := by
    have := (norm_nonneg _).trans (hΦ 0)
    exact nonneg_of_mul_nonneg_left this (Real.exp_pos _)
  set V := ‖p0‖ + ε with hV
  set c := V + 1 with hc
  set bound : (ι → ℝ) → ℝ := fun x => W * (Real.exp (Fintype.card ι * (c ^ 2 / q)) *
    ∏ i, Real.exp (-(q / 4) * x i ^ 2)) with hbound
  -- the pointwise estimate on the ball
  have hest : ∀ p ∈ Metric.ball p0 ε, ∀ x, ‖cexp (ellL x p)‖ * ‖Φ x‖ * Real.exp (l1 x) ≤ bound x := by
    intro p hp x
    have hpU := hball hp
    have hq' := hUq p hpU x
    have hv : ‖p.2‖ ≤ V := by
      have h1 : ‖p‖ ≤ ‖p0‖ + ε := by
        have := norm_le_norm_add_norm_sub' p p0
        rw [Metric.mem_ball, dist_eq_norm] at hp
        linarith
      exact (norm_snd_le p).trans h1
    rw [Complex.norm_exp]
    calc Real.exp (ellL x p).re * ‖Φ x‖ * Real.exp (l1 x)
        ≤ Real.exp (-(1 / 2) * (qf (Matrix.of p.1) x).re + l1 x * V) * (W * Real.exp (1 / 2 * α * nsq x)) *
            Real.exp (l1 x) := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul (Real.exp_le_exp.2 ((re_ell_le x p).trans ?_)) (hΦ x)
            (norm_nonneg _) (Real.exp_pos _).le) (Real.exp_pos _).le
          have := mul_le_mul_of_nonneg_left hv (l1_nonneg x)
          linarith
      _ = W * Real.exp (-(1 / 2) * (qf (Matrix.of p.1) x).re + l1 x * V + 1 / 2 * α * nsq x + l1 x) := by
          simp only [Real.exp_add]; ring
      _ = W * Real.exp (-(1 / 2) * ((qf (Matrix.of p.1) x).re - α * nsq x) + c * l1 x) := by
          rw [hc]; refine congrArg (fun t => W * Real.exp t) ?_; ring
      _ ≤ W * Real.exp (-(1 / 2) * q * nsq x + c * l1 x) := by
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hW
          nlinarith
      _ ≤ bound x := mul_le_mul_of_nonneg_left (dom_le hq c x) hW
  have hbint : Integrable bound := by
    rw [hbound]
    simp_rw [← mul_assoc]
    exact integrable_dom hq _
  -- measurability
  have hmeas : ∀ p, AEStronglyMeasurable (fun x => cexp (ellL x p) • Φ x) volume := fun p =>
    ((Complex.continuous_exp.comp ((ContinuousLinearMap.apply ℂ ℂ p).continuous.comp continuous_ellL)).aestronglyMeasurable).smul hΦm
  set F' : ((ι → ι → ℂ) × (ι → ℂ)) → (ι → ℝ) → (((ι → ι → ℂ) × (ι → ℂ)) →L[ℂ] F) :=
    fun p x => (cexp (ellL x p) • ellL x).smulRight (Φ x) with hF'
  have hderiv : ∀ x, ∀ p, HasFDerivAt (fun p => cexp (ellL x p) • Φ x) (F' p x) p := fun x p =>
    ((ellL x).hasFDerivAt.cexp).smul_const (Φ x)
  have hF'meas : AEStronglyMeasurable (F' p0) volume := by
    have hc1 : Continuous fun x => cexp (ellL x p0) • ellL x :=
      ((Complex.continuous_exp.comp ((ContinuousLinearMap.apply ℂ ℂ p0).continuous.comp continuous_ellL))).smul
        continuous_ellL
    have h2 := (ContinuousLinearMap.smulRightL ℂ ((ι → ι → ℂ) × (ι → ℂ)) F).aestronglyMeasurable_comp₂
      hc1.aestronglyMeasurable hΦm
    refine h2.congr (Filter.Eventually.of_forall fun x => ?_)
    rfl
  have hF'bound : ∀ x, ∀ p ∈ Metric.ball p0 ε, ‖F' p x‖ ≤ bound x := by
    intro x p hp
    rw [hF', ContinuousLinearMap.norm_smulRight_apply, norm_smul]
    calc ‖cexp (ellL x p)‖ * ‖ellL x‖ * ‖Φ x‖ ≤ ‖cexp (ellL x p)‖ * Real.exp (l1 x) * ‖Φ x‖ := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ((norm_ellL x).trans
            (poly_le_exp (l1_nonneg x))) (norm_nonneg _)) (norm_nonneg _)
      _ = ‖cexp (ellL x p)‖ * ‖Φ x‖ * Real.exp (l1 x) := by ring
      _ ≤ bound x := hest p hp x
  have hFint : Integrable (fun x => cexp (ellL x p0) • Φ x) := by
    refine hbint.mono' (hmeas p0) (Filter.Eventually.of_forall fun x => ?_)
    rw [norm_smul]
    calc ‖cexp (ellL x p0)‖ * ‖Φ x‖ ≤ ‖cexp (ellL x p0)‖ * ‖Φ x‖ * Real.exp (l1 x) :=
          le_mul_of_one_le_right (by positivity) (Real.one_le_exp (l1_nonneg x))
      _ ≤ bound x := hest p0 (Metric.mem_ball_self hε) x
  have h := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume) (F := fun p x => cexp (ellL x p) • Φ x)
    (F' := F') (Metric.ball_mem_nhds p0 hε) (Filter.Eventually.of_forall hmeas) hFint hF'meas
    (Filter.Eventually.of_forall fun x p hp => hF'bound x p hp) hbint
    (Filter.Eventually.of_forall fun x p _ => hderiv x p)
  exact h.differentiableAt.differentiableWithinAt

end ComplexGauss
end CoreLean

end
