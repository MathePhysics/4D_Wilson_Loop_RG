import GaussianBlockSpin.GaussianIntegral

/-! Wick's theorem (Isserlis) for Gaussian weights on a finite-dimensional real inner product space, by Gaussian
integration by parts: for `T` symmetric positive definite and `C` with `T C = 1`,
`∫ ⟪x, T u⟫ F(x) e^{-½⟪x, T x⟫} dx = ∫ (DF)(x) u e^{-½⟪x, T x⟫} dx`, hence for products of linear forms
`M(s) = ∫ ∏_{i ∈ s} ⟪v_i, x⟫ e^{-½⟪x, T x⟫} dx` the recursion `M(s) = Σ_{j ∈ s \ a} ⟪v_j, C v_a⟫ M(s \ {a, j})`
(`a ∈ s`), and `M(s) = M(∅) W(s)` with the pairing sum `W` defined by that recursion (for legs indexed by `Fin m`
and symmetric `C` it is the sum over perfect matchings of `∏ ⟪v_i, C v_j⟫`: wickSum_eq_sum_matchings and
gaussMoment_eq_sum_matchings in Matchings).
This is the base of the graph expansion of Bałaban III, Sect. 1 (layer C1 of notes/PHASE_C_PLAN.md in
Projects/higgs23_lower_bound). -/

open MeasureTheory Real
open scoped RealInnerProductSpace

namespace GaussianBlockSpin

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A positive definite quadratic form is coercive: `c ‖x‖² ≤ ⟪x, T x⟫` for some `c > 0`. -/
lemma exists_coercive {T : E →ₗ[ℝ] E} (hpos : ∀ x, x ≠ 0 → 0 < ⟪x, T x⟫) :
    ∃ c : ℝ, 0 < c ∧ ∀ x, c * ‖x‖ ^ 2 ≤ ⟪x, T x⟫ := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · refine ⟨1, one_pos, fun x => ?_⟩
    rw [Subsingleton.elim x 0]
    simp
  have hcont : Continuous fun x : E => ⟪x, T x⟫ :=
    continuous_id.inner (LinearMap.continuous_of_finiteDimensional T)
  obtain ⟨u, hu, hmin⟩ := (isCompact_sphere (0 : E) 1).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr zero_le_one) hcont.continuousOn
  have hu1 : ‖u‖ = 1 := by simpa using hu
  have hu0 : u ≠ 0 := by
    intro h
    rw [h, norm_zero] at hu1
    exact zero_ne_one hu1
  refine ⟨⟪u, T u⟫, hpos u hu0, fun x => ?_⟩
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hy : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : E) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hn.le), inv_mul_cancel₀ hn.ne']
  have h := isMinOn_iff.mp hmin _ hy
  have hyx : ⟪‖x‖⁻¹ • x, T (‖x‖⁻¹ • x)⟫ = ‖x‖⁻¹ ^ 2 * ⟪x, T x⟫ := by
    rw [map_smul, inner_smul_left, inner_smul_right]
    simp only [conj_trivial]
    ring
  rw [hyx] at h
  have h2 : ⟪u, T u⟫ * ‖x‖ ^ 2 ≤ ‖x‖⁻¹ ^ 2 * ⟪x, T x⟫ * ‖x‖ ^ 2 :=
    mul_le_mul_of_nonneg_right h (by positivity)
  have h3 : ‖x‖⁻¹ ^ 2 * ⟪x, T x⟫ * ‖x‖ ^ 2 = ⟪x, T x⟫ := by
    field_simp
  linarith

/-- The Gaussian weight `e^{-½⟪x, T x⟫}`. -/
noncomputable def gaussWeight (T : E →ₗ[ℝ] E) (x : E) : ℝ := Real.exp (-(1 / 2) * ⟪x, T x⟫)

omit [FiniteDimensional ℝ E] in
lemma gaussWeight_pos (T : E →ₗ[ℝ] E) (x : E) : 0 < gaussWeight T x := Real.exp_pos _

lemma continuous_gaussWeight (T : E →ₗ[ℝ] E) : Continuous (gaussWeight T) := by
  unfold gaussWeight
  exact Real.continuous_exp.comp (continuous_const.mul
    (continuous_id.inner (LinearMap.continuous_of_finiteDimensional T)))

/-- `t^n e^{-c t²/4} ≤ 1 + n! (4/c)^n` for `t ≥ 0` (from `e^y ≥ y^n/n!`). -/
lemma pow_mul_exp_neg_le {c : ℝ} (hc : 0 < c) (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    t ^ n * Real.exp (-(c / 4) * t ^ 2) ≤ 1 + (n.factorial : ℝ) * (4 / c) ^ n := by
  have hy : 0 ≤ c / 4 * t ^ 2 := by positivity
  have h1 := Real.pow_div_factorial_le_exp _ hy n
  have hfac : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have h2 : t ^ (2 * n) ≤ (n.factorial : ℝ) * (4 / c) ^ n * Real.exp (c / 4 * t ^ 2) := by
    rw [div_le_iff₀ hfac] at h1
    have : (c / 4 * t ^ 2) ^ n = (c / 4) ^ n * t ^ (2 * n) := by rw [mul_pow, ← pow_mul, mul_comm 2 n]
    rw [this] at h1
    have hc4 : 0 < (c / 4) ^ n := by positivity
    have : t ^ (2 * n) = ((c / 4) ^ n * t ^ (2 * n)) * (4 / c) ^ n := by
      rw [mul_comm ((c / 4) ^ n), mul_assoc, ← mul_pow, show c / 4 * (4 / c) = 1 by field_simp, one_pow, mul_one]
    rw [this]
    calc (c / 4) ^ n * t ^ (2 * n) * (4 / c) ^ n ≤ Real.exp (c / 4 * t ^ 2) * n.factorial * (4 / c) ^ n :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = _ := by ring
  have h3 : t ^ n ≤ 1 + t ^ (2 * n) := by
    rcases le_or_gt t 1 with h | h
    · have : t ^ n ≤ 1 := pow_le_one₀ ht h
      have : 0 ≤ t ^ (2 * n) := by positivity
      linarith
    · have : t ^ n ≤ t ^ (2 * n) := pow_le_pow_right₀ h.le (by omega)
      linarith
  have he : Real.exp (-(c / 4) * t ^ 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith [sq_nonneg t]
  have he0 : 0 < Real.exp (-(c / 4) * t ^ 2) := Real.exp_pos _
  have hprod : Real.exp (c / 4 * t ^ 2) * Real.exp (-(c / 4) * t ^ 2) = 1 := by
    rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  calc t ^ n * Real.exp (-(c / 4) * t ^ 2) ≤ (1 + t ^ (2 * n)) * Real.exp (-(c / 4) * t ^ 2) :=
        mul_le_mul_of_nonneg_right h3 he0.le
    _ = Real.exp (-(c / 4) * t ^ 2) + t ^ (2 * n) * Real.exp (-(c / 4) * t ^ 2) := by ring
    _ ≤ 1 + (n.factorial : ℝ) * (4 / c) ^ n * Real.exp (c / 4 * t ^ 2) * Real.exp (-(c / 4) * t ^ 2) :=
        add_le_add he (mul_le_mul_of_nonneg_right h2 he0.le)
    _ = 1 + (n.factorial : ℝ) * (4 / c) ^ n := by rw [mul_assoc _ (Real.exp _), hprod, mul_one]

omit [FiniteDimensional ℝ E] in
lemma isSymmetric_smul_of {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) (r : ℝ) : (r • T).IsSymmetric := by
  intro x y
  simp only [LinearMap.smul_apply, inner_smul_left, inner_smul_right, hT x y, conj_trivial]

variable [MeasurableSpace E] [BorelSpace E]

/-- `e^{-½⟪x, T x⟫}` is integrable (its integral is `(2π)^{n/2}/√det T ≠ 0`). -/
lemma integrable_gaussWeight {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) (hpos : ∀ x, x ≠ 0 → 0 < ⟪x, T x⟫) :
    Integrable (gaussWeight T) := by
  refine Integrable.of_integral_ne_zero ?_
  have hG := integral_exp_neg_half_inner hT hpos
  unfold gaussWeight
  rw [hG]
  exact (div_pos (by positivity) (Real.sqrt_pos.mpr (det_pos_of_pos hT hpos))).ne'

/-- `‖x‖^n e^{-½⟪x, T x⟫}` is integrable: it is at most `(1 + n! (4/c)^n) e^{-¼⟪x, T x⟫}`. -/
lemma integrable_norm_pow_mul_gaussWeight {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric)
    (hpos : ∀ x, x ≠ 0 → 0 < ⟪x, T x⟫) (n : ℕ) : Integrable (fun x => ‖x‖ ^ n * gaussWeight T x) := by
  obtain ⟨c, hc, hcoer⟩ := exists_coercive hpos
  have hT2 := isSymmetric_smul_of hT (1 / 2)
  have hpos2 : ∀ x, x ≠ 0 → 0 < ⟪x, ((1 / 2 : ℝ) • T) x⟫ := by
    intro x hx
    rw [LinearMap.smul_apply, inner_smul_right]
    have := hpos x hx
    positivity
  have hI := (integrable_gaussWeight hT2 hpos2).const_mul (1 + (n.factorial : ℝ) * (4 / c) ^ n)
  refine hI.mono' ((continuous_norm.pow n).mul (continuous_gaussWeight T)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  have hsplit : gaussWeight T x = Real.exp (-(1 / 4) * ⟪x, T x⟫) * gaussWeight ((1 / 2 : ℝ) • T) x := by
    unfold gaussWeight
    rw [← Real.exp_add, LinearMap.smul_apply, inner_smul_right]
    ring_nf
  have he : Real.exp (-(1 / 4) * ⟪x, T x⟫) ≤ Real.exp (-(c / 4) * ‖x‖ ^ 2) :=
    Real.exp_le_exp.mpr (by nlinarith [hcoer x])
  have hb := pow_mul_exp_neg_le hc n ‖x‖ (norm_nonneg x)
  rw [Real.norm_eq_abs, abs_of_nonneg (by have := gaussWeight_pos T x; positivity), hsplit]
  have hg2 := (gaussWeight_pos ((1 / 2 : ℝ) • T) x).le
  calc ‖x‖ ^ n * (Real.exp (-(1 / 4) * ⟪x, T x⟫) * gaussWeight ((1 / 2 : ℝ) • T) x)
      ≤ ‖x‖ ^ n * (Real.exp (-(c / 4) * ‖x‖ ^ 2) * gaussWeight ((1 / 2 : ℝ) • T) x) := by gcongr
    _ = (‖x‖ ^ n * Real.exp (-(c / 4) * ‖x‖ ^ 2)) * gaussWeight ((1 / 2 : ℝ) • T) x := by ring
    _ ≤ (1 + (n.factorial : ℝ) * (4 / c) ^ n) * gaussWeight ((1 / 2 : ℝ) • T) x :=
        mul_le_mul_of_nonneg_right hb hg2

/-- A continuous function bounded by `K ‖x‖^n` times the Gaussian weight is integrable. -/
lemma integrable_mul_gaussWeight_of_le {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric)
    (hpos : ∀ x, x ≠ 0 → 0 < ⟪x, T x⟫) {P : E → ℝ} (hP : Continuous P) {K : ℝ} (n : ℕ)
    (hb : ∀ x, |P x| ≤ K * ‖x‖ ^ n) : Integrable (fun x => P x * gaussWeight T x) := by
  refine ((integrable_norm_pow_mul_gaussWeight hT hpos n).const_mul K).mono'
    (hP.mul (continuous_gaussWeight T)).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (gaussWeight_pos T x), ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (hb x) (gaussWeight_pos T x).le

omit [MeasurableSpace E] [BorelSpace E] in
/-- The derivative of the Gaussian weight: `D(e^{-½⟪x, T x⟫}) u = -⟪x, T u⟫ e^{-½⟪x, T x⟫}` (`T` symmetric). -/
lemma hasFDerivAt_gaussWeight {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) (x : E) :
    HasFDerivAt (gaussWeight T) (-(gaussWeight T x) • (innerSL ℝ x).comp (LinearMap.toContinuousLinearMap T)) x := by
  have hq : HasFDerivAt (fun y : E => ⟪y, T y⟫)
      ((fderivInnerCLM ℝ (x, T x)).comp ((ContinuousLinearMap.id ℝ E).prod (LinearMap.toContinuousLinearMap T))) x :=
    (hasFDerivAt_id x).inner ℝ (LinearMap.toContinuousLinearMap T).hasFDerivAt
  have hexp := ((hq.const_mul (-(1 / 2) : ℝ)).exp)
  refine hexp.congr_fderiv ?_
  ext u
  simp only [FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply, fderivInnerCLM_apply,
    LinearMap.coe_toContinuousLinearMap', innerSL_apply_apply, smul_eq_mul, gaussWeight]
  rw [← hT u x, real_inner_comm x (T u)]
  ring

/-- **Gaussian integration by parts**: `∫ ⟪x, T u⟫ F(x) e^{-½⟪x, T x⟫} dx = ∫ (DF)(x) u e^{-½⟪x, T x⟫} dx`. -/
theorem integral_inner_mul_gaussWeight {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) {F : E → ℝ}
    {F' : E → (E →L[ℝ] ℝ)} (hF : ∀ x, HasFDerivAt F (F' x) x) (u : E)
    (h1 : Integrable fun x => F' x u * gaussWeight T x)
    (h2 : Integrable fun x => F x * (⟪x, T u⟫ * gaussWeight T x))
    (h3 : Integrable fun x => F x * gaussWeight T x) :
    ∫ x, ⟪x, T u⟫ * F x * gaussWeight T x = ∫ x, F' x u * gaussWeight T x := by
  have hFd : ∀ x, fderiv ℝ F x = F' x := fun x => (hF x).fderiv
  have hgd : ∀ x, fderiv ℝ (gaussWeight T) x u = -(gaussWeight T x * ⟪x, T u⟫) := by
    intro x
    rw [(hasFDerivAt_gaussWeight hT x).fderiv]
    simp only [FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.comp_apply,
      LinearMap.coe_toContinuousLinearMap', innerSL_apply_apply, smul_eq_mul]
    ring
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) (f := F) (g := gaussWeight T) (v := u)
    (by simpa only [hFd] using h1)
    (by
      simp only [hgd]
      have := h2.neg
      refine this.congr (Filter.Eventually.of_forall fun x => ?_)
      simp only [Pi.neg_apply]
      ring)
    h3 (fun x _ => (hF x).differentiableAt) (fun x _ => (hasFDerivAt_gaussWeight hT x).differentiableAt)
  simp only [hFd, hgd] at hibp
  have hl : ∫ x, F x * -(gaussWeight T x * ⟪x, T u⟫) = -∫ x, ⟪x, T u⟫ * F x * gaussWeight T x := by
    rw [← integral_neg]
    congr 1
    funext x
    ring
  rw [hl] at hibp
  linarith

/-- The product of linear forms `∏_{i ∈ s} ⟪v_i, x⟫`. -/
noncomputable def linProd {ι : Type*} (s : Finset ι) (v : ι → E) (x : E) : ℝ := ∏ i ∈ s, ⟪v i, x⟫

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma continuous_linProd {ι : Type*} (s : Finset ι) (v : ι → E) : Continuous (linProd s v) := by
  unfold linProd
  exact continuous_finsetProd s fun i _ => continuous_const.inner continuous_id

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma abs_linProd_le {ι : Type*} (s : Finset ι) (v : ι → E) (x : E) :
    |linProd s v x| ≤ (∏ i ∈ s, ‖v i‖) * ‖x‖ ^ s.card := by
  unfold linProd
  rw [Finset.abs_prod, ← Finset.prod_const, ← Finset.prod_mul_distrib]
  exact Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) fun i _ => abs_real_inner_le_norm _ _

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma hasFDerivAt_linProd {ι : Type*} [DecidableEq ι] (s : Finset ι) (v : ι → E) (x : E) :
    HasFDerivAt (linProd s v) (∑ i ∈ s, (∏ j ∈ s.erase i, ⟪v j, x⟫) • innerSL ℝ (v i)) x := by
  unfold linProd
  exact HasFDerivAt.finsetProd fun i _ => (innerSL ℝ (v i)).hasFDerivAt

lemma integrable_linProd_mul_gaussWeight {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric)
    (hpos : ∀ x, x ≠ 0 → 0 < ⟪x, T x⟫) {ι : Type*} (s : Finset ι) (v : ι → E) :
    Integrable fun x => linProd s v x * gaussWeight T x :=
  integrable_mul_gaussWeight_of_le hT hpos (continuous_linProd s v) s.card (abs_linProd_le s v)

lemma integrable_linProd_inner_mul_gaussWeight {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric)
    (hpos : ∀ x, x ≠ 0 → 0 < ⟪x, T x⟫) {ι : Type*} (s : Finset ι) (v : ι → E) (w : E) :
    Integrable fun x => linProd s v x * (⟪x, w⟫ * gaussWeight T x) := by
  have h := integrable_mul_gaussWeight_of_le hT hpos (P := fun x => linProd s v x * ⟪x, w⟫)
    ((continuous_linProd s v).mul (continuous_id.inner continuous_const)) (K := (∏ i ∈ s, ‖v i‖) * ‖w‖)
    (s.card + 1) (fun x => by
      rw [abs_mul, pow_succ]
      have h1 := abs_linProd_le s v x
      have h2 : |⟪x, w⟫| ≤ ‖x‖ * ‖w‖ := abs_real_inner_le_norm x w
      calc |linProd s v x| * |⟪x, w⟫| ≤ ((∏ i ∈ s, ‖v i‖) * ‖x‖ ^ s.card) * (‖x‖ * ‖w‖) :=
            mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
        _ = _ := by ring)
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only
  ring

/-- The Gaussian moment `M(s) = ∫ ∏_{i ∈ s} ⟪v_i, x⟫ e^{-½⟪x, T x⟫} dx` (unnormalised). -/
noncomputable def gaussMoment (T : E →ₗ[ℝ] E) {ι : Type*} (s : Finset ι) (v : ι → E) : ℝ :=
  ∫ x, linProd s v x * gaussWeight T x

/-- **Wick's recursion**: for `T` symmetric positive definite, `T C = 1` and `a ∈ s`,
`M(s) = Σ_{j ∈ s \ a} ⟪v_j, C v_a⟫ M(s \ {a, j})`. -/
theorem gaussMoment_eq_sum {T C : E →ₗ[ℝ] E} (hT : T.IsSymmetric) (hpos : ∀ x, x ≠ 0 → 0 < ⟪x, T x⟫)
    (hTC : ∀ w, T (C w) = w) {ι : Type*} [DecidableEq ι] (s : Finset ι) (v : ι → E) {a : ι} (ha : a ∈ s) :
    gaussMoment T s v = ∑ j ∈ s.erase a, ⟪v j, C (v a)⟫ * gaussMoment T ((s.erase a).erase j) v := by
  set u := C (v a) with hu
  have hsplit : ∀ x, linProd s v x * gaussWeight T x = ⟪x, T u⟫ * linProd (s.erase a) v x * gaussWeight T x := by
    intro x
    unfold linProd
    rw [← Finset.mul_prod_erase s _ ha, hu, hTC, real_inner_comm]
  have hF := hasFDerivAt_linProd (s.erase a) v
  have hibp := integral_inner_mul_gaussWeight hT hF u
    (by
      simp only [FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul, Pi.smul_apply,
        innerSL_apply_apply, smul_eq_mul, Finset.sum_mul]
      refine integrable_finsetSum _ fun j _ => ?_
      have := (integrable_linProd_mul_gaussWeight hT hpos ((s.erase a).erase j) v).const_mul ⟪v j, u⟫
      refine this.congr (Filter.Eventually.of_forall fun x => ?_)
      simp only [linProd]
      ring)
    (integrable_linProd_inner_mul_gaussWeight hT hpos (s.erase a) v (T u))
    (integrable_linProd_mul_gaussWeight hT hpos (s.erase a) v)
  unfold gaussMoment
  simp_rw [hsplit]
  rw [hibp]
  simp only [FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul, Pi.smul_apply,
    innerSL_apply_apply, smul_eq_mul, Finset.sum_mul]
  rw [integral_finsetSum _ fun j _ => by
    have := (integrable_linProd_mul_gaussWeight hT hpos ((s.erase a).erase j) v).const_mul ⟪v j, u⟫
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [linProd]
    ring]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← integral_const_mul]
  congr 1
  funext x
  simp only [linProd]
  ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma card_erase_erase_lt {ι : Type*} [DecidableEq ι] {s : Finset ι} {a j : ι} (ha : a ∈ s) :
    ((s.erase a).erase j).card < s.card :=
  lt_of_le_of_lt (Finset.card_erase_le) (Finset.card_erase_lt_of_mem ha)

/-- **The pairing sum**, defined by the recursion of gaussMoment_eq_sum with the least element of `s` as the pivot:
`W(∅) = 1`, `W(s) = Σ_{j ∈ s \ a} ⟪v_j, C v_a⟫ W(s \ {a, j})`, `a = min s`. For legs indexed by `Fin m` and
symmetric `C` it is the sum over the perfect matchings `σ` of `s` of `∏_{i < σ i} ⟪v_i, C v_{σ i}⟫`
(wickSum_eq_sum_matchings in Matchings); for non-symmetric `C` the recursion fixes the order `⟪v_larger, C v_smaller⟫`. -/
noncomputable def wickSum (C : E →ₗ[ℝ] E) {ι : Type*} [LinearOrder ι] (v : ι → E) (s : Finset ι) : ℝ :=
  if h : s.Nonempty then
    ∑ j ∈ (s.erase (s.min' h)).attach,
      ⟪v j, C (v (s.min' h))⟫ * wickSum C v (((s.erase (s.min' h)).erase j))
  else 1
termination_by s.card
decreasing_by exact card_erase_erase_lt (s.min'_mem h)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma wickSum_empty (C : E →ₗ[ℝ] E) {ι : Type*} [LinearOrder ι] (v : ι → E) :
    wickSum C v (∅ : Finset ι) = 1 := by
  rw [wickSum]
  simp

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma wickSum_of_nonempty (C : E →ₗ[ℝ] E) {ι : Type*} [LinearOrder ι] (v : ι → E) {s : Finset ι}
    (h : s.Nonempty) :
    wickSum C v s = ∑ j ∈ s.erase (s.min' h), ⟪v j, C (v (s.min' h))⟫ * wickSum C v ((s.erase (s.min' h)).erase j) := by
  rw [wickSum]
  simp only [h, ↓reduceDIte]
  exact Finset.sum_attach (s.erase (s.min' h)) fun j => ⟪v j, C (v (s.min' h))⟫ * wickSum C v ((s.erase (s.min' h)).erase j)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The pairing sum of an odd number of factors vanishes. -/
lemma wickSum_eq_zero_of_odd (C : E →ₗ[ℝ] E) {ι : Type*} [LinearOrder ι] (v : ι → E) (s : Finset ι)
    (hs : Odd s.card) : wickSum C v s = 0 := by
  induction h : s.card using Nat.strong_induction_on generalizing s with
  | _ n ih =>
    have hne : s.Nonempty := Finset.card_pos.mp (by rw [h]; exact (h ▸ hs).pos)
    rw [wickSum_of_nonempty C v hne]
    refine Finset.sum_eq_zero fun j hj => ?_
    have hm := s.min'_mem hne
    have hc : ((s.erase (s.min' hne)).erase j).card + 2 = n := by
      rw [Finset.card_erase_of_mem hj, Finset.card_erase_of_mem hm, ← h]
      have : 1 ≤ (s.erase (s.min' hne)).card := Finset.card_pos.mpr ⟨j, hj⟩
      rw [Finset.card_erase_of_mem hm] at this
      omega
    obtain ⟨k, hk⟩ := h ▸ hs
    rw [ih _ (by omega) _ ⟨k - 1, by omega⟩ rfl, mul_zero]

/-- **Wick's theorem** (Isserlis): for `T` symmetric positive definite and `T C = 1`,
`∫ ∏_{i ∈ s} ⟪v_i, x⟫ e^{-½⟪x, T x⟫} dx = (∫ e^{-½⟪x, T x⟫} dx) · W(s)`, `W` the pairing sum of `⟪v_i, C v_j⟫`
(zero for `s` of odd cardinality, wickSum_eq_zero_of_odd). -/
theorem gaussMoment_eq_wickSum {T C : E →ₗ[ℝ] E} (hT : T.IsSymmetric) (hpos : ∀ x, x ≠ 0 → 0 < ⟪x, T x⟫)
    (hTC : ∀ w, T (C w) = w) {ι : Type*} [LinearOrder ι] (v : ι → E) (s : Finset ι) :
    gaussMoment T s v = gaussMoment T (∅ : Finset ι) v * wickSum C v s := by
  induction h : s.card using Nat.strong_induction_on generalizing s with
  | _ n ih =>
    by_cases hs : s.Nonempty
    · rw [gaussMoment_eq_sum hT hpos hTC s v (s.min'_mem hs), wickSum_of_nonempty C v hs, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [ih _ (h ▸ card_erase_erase_lt (s.min'_mem hs)) _ rfl]
      ring
    · rw [Finset.not_nonempty_iff_eq_empty.mp hs, wickSum_empty, mul_one]

end GaussianBlockSpin
