import GaussianBlockSpin.ModerateFamilies
import GaussianBlockSpin.ParametricIntegrals
import GaussianBlockSpin.GaussianGraphs

/-! **Differentiation under the integral sign for `∫ e^F` with a moderate exponent.** For `G` smooth on
`X × (ℝ × ℝ)`, the derivatives along a line are directional derivatives of `G` (iteratedDeriv_comp_line), the
`e`-derivatives and the `λ`-derivatives of the `e`-derivatives at `e = 0` are values of `D^i G` and `D^j D^i G` on the
unit vectors of the parameter directions (iteratedDeriv_paramE, iteratedDeriv_paramL), and
`‖D^j (D^i G)‖ = ‖D^{i+j} G‖`; jointly smooth exponents are nested-smooth (nestedSmooth_of_contDiff). Hence
(exp_domination): if `F` is moderate on the parameter ball of radius `r` and `e^F ≤ B` there for `λ ≥ 0`, with
`e^{c ‖x‖} B` integrable for every `c`, then the `e`- and `λ`-derivatives of `e^F` (`e ∈ (-r, r)`, `λ ∈ [0, r)`) have
one integrable bound and are smooth and measurable: the hypotheses of integral_nestedSmooth_mixedCoeff and of
mixedCoeff_log_gaussIntegral_eq_connected, for the bracket of I.(3.35); so `∫ e^F` is nested-smooth at `(0, 0)` and
its mixed Taylor coefficients are the integrals of those of `e^F` (integral_exp_nestedSmooth). For the Gaussian
measure `μ_T`: `e^{c ‖y‖ + ½⟪y, T y⟫ + K - c₁ ‖x₀ + y‖²}` is `μ_T`-integrable for `c₁ > 0`
(integrable_gaussProb_exp_quadratic). -/

open MeasureTheory Metric Set
open scoped ContDiff Nat

namespace GaussianBlockSpin

section Lines

variable {X Y F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Derivatives along a line: `∂_s^j h(y₀ + s v) = D^j h(y₀ + s v)(v, …, v)`. -/
lemma iteratedDeriv_comp_line {h : Y → F} (hh : ContDiff ℝ ∞ h) (y₀ v : Y) (j : ℕ) (t : ℝ) :
    iteratedDeriv j (fun s : ℝ => h (y₀ + s • v)) t = iteratedFDeriv ℝ j h (y₀ + t • v) (fun _ => v) := by
  let L : ℝ →L[ℝ] Y := (ContinuousLinearMap.id ℝ ℝ).smulRight v
  have hfun : (fun s : ℝ => h (y₀ + s • v)) = (fun z => h (y₀ + z)) ∘ L := by
    funext s
    simp [L]
  have hsh : ContDiff ℝ j (fun z => h (y₀ + z)) := (contDiff_of_infty hh j).comp (contDiff_const.add contDiff_id)
  rw [iteratedDeriv_eq_iteratedFDeriv, hfun, L.iteratedFDeriv_comp_right hsh t le_rfl,
    ContinuousMultilinearMap.compContinuousLinearMap_apply, iteratedFDeriv_comp_add_left]
  simp [L]

/-- `‖D^j (D^i h)‖ = ‖D^{i+j} h‖`. -/
lemma norm_iteratedFDeriv_iteratedFDeriv (h : Y → F) (i j : ℕ) (z : Y) :
    ‖iteratedFDeriv ℝ j (iteratedFDeriv ℝ i h) z‖ = ‖iteratedFDeriv ℝ (i + j) h z‖ := by
  induction j generalizing i with
  | zero => simp [norm_iteratedFDeriv_zero]
  | succ j ih =>
    rw [← norm_iteratedFDeriv_fderiv]
    have hd : fderiv ℝ (iteratedFDeriv ℝ i h) =
        (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (i + 1) => Y) F) ∘ iteratedFDeriv ℝ (i + 1) h := by
      rw [iteratedFDeriv_succ_eq_comp_left]
      funext w
      simp
    rw [hd, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left, ih (i + 1), show i + (j + 1) = i + 1 + j by omega]

lemma contDiff_iteratedFDeriv_infty {h : Y → F} (hh : ContDiff ℝ ∞ h) (i : ℕ) :
    ContDiff ℝ ∞ (iteratedFDeriv ℝ i h) :=
  hh.iteratedFDeriv_right (by exact_mod_cast le_top)

lemma norm_apply_const_le {n : ℕ} (M : ContinuousMultilinearMap ℝ (fun _ : Fin n => Y) F) {v : Y} (hv : ‖v‖ ≤ 1) :
    ‖M (fun _ => v)‖ ≤ ‖M‖ := by
  refine (M.le_opNorm _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hv)

/-- The unit vectors of the two parameter directions in `X × (ℝ × ℝ)`. -/
def unitE : X × (ℝ × ℝ) := (0, (1, 0))

def unitL : X × (ℝ × ℝ) := (0, (0, 1))

omit [NormedSpace ℝ X] in
lemma norm_unitE_le : ‖(unitE : X × (ℝ × ℝ))‖ ≤ 1 := by simp [unitE, Prod.norm_def]

omit [NormedSpace ℝ X] in
lemma norm_unitL_le : ‖(unitL : X × (ℝ × ℝ))‖ ≤ 1 := by simp [unitL, Prod.norm_def]

/-- The `e`-derivatives as directional derivatives of the joint function. -/
lemma iteratedDeriv_paramE {G : X × (ℝ × ℝ) → F} (hG : ContDiff ℝ ∞ G) (x : X) (e l : ℝ) (i : ℕ) :
    iteratedDeriv i (fun e => G (x, (e, l))) e = iteratedFDeriv ℝ i G (x, (e, l)) (fun _ => unitE) := by
  have hfun : (fun e => G (x, (e, l))) = fun s : ℝ => G ((x, (0, l)) + s • unitE) := by
    funext s
    simp [unitE]
  rw [hfun, iteratedDeriv_comp_line hG]
  simp [unitE]

/-- The `λ`-derivatives of the `e`-derivatives at `e = 0`. -/
lemma iteratedDeriv_paramL {G : X × (ℝ × ℝ) → F} (hG : ContDiff ℝ ∞ G) (x : X) (l : ℝ) (i j : ℕ) :
    iteratedDeriv j (fun l => iteratedDeriv i (fun e => G (x, (e, l))) 0) l =
      iteratedFDeriv ℝ j (iteratedFDeriv ℝ i G) (x, (0, l)) (fun _ => unitL) (fun _ => unitE) := by
  have hfun : (fun l => iteratedDeriv i (fun e => G (x, (e, l))) 0) =
      fun s : ℝ => (ContinuousMultilinearMap.apply ℝ (fun _ : Fin i => X × (ℝ × ℝ)) F (fun _ => unitE))
        (iteratedFDeriv ℝ i G ((x, (0, 0)) + s • unitL)) := by
    funext s
    rw [iteratedDeriv_paramE hG]
    simp [unitL]
  have hH : ContDiff ℝ ∞ fun z => (ContinuousMultilinearMap.apply ℝ (fun _ : Fin i => X × (ℝ × ℝ)) F
      (fun _ => unitE)) (iteratedFDeriv ℝ i G z) :=
    (ContinuousLinearMap.contDiff _).comp (contDiff_iteratedFDeriv_infty hG i)
  rw [hfun, iteratedDeriv_comp_line hH]
  have hcl := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin i => X × (ℝ × ℝ)) F (fun _ => unitE)).iteratedFDeriv_comp_left
    (f := iteratedFDeriv ℝ i G) (x := (x, (0, 0)) + l • unitL)
    ((contDiff_of_infty (contDiff_iteratedFDeriv_infty hG i) j).contDiffAt) (i := j) le_rfl
  have hfc : (fun z => (ContinuousMultilinearMap.apply ℝ (fun _ : Fin i => X × (ℝ × ℝ)) F (fun _ => unitE))
      (iteratedFDeriv ℝ i G z)) = ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin i => X × (ℝ × ℝ)) F
        (fun _ => unitE)) ∘ iteratedFDeriv ℝ i G) := rfl
  rw [hfc, hcl]
  simp [unitL]

lemma contDiff_paramE {G : X × (ℝ × ℝ) → F} (hG : ContDiff ℝ ∞ G) (x : X) (l : ℝ) :
    ContDiff ℝ ∞ (fun e => G (x, (e, l))) :=
  hG.comp (contDiff_const.prodMk (contDiff_id.prodMk contDiff_const))

lemma contDiff_paramL {G : X × (ℝ × ℝ) → F} (hG : ContDiff ℝ ∞ G) (x : X) (i : ℕ) :
    ContDiff ℝ ∞ (fun l => iteratedDeriv i (fun e => G (x, (e, l))) 0) := by
  have hfun : (fun l => iteratedDeriv i (fun e => G (x, (e, l))) 0) = fun l =>
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin i => X × (ℝ × ℝ)) F (fun _ => unitE))
        (iteratedFDeriv ℝ i G (x, (0, l))) := by
    funext l
    rw [iteratedDeriv_paramE hG]
    rfl
  rw [hfun]
  exact (ContinuousLinearMap.contDiff _).comp
    ((contDiff_iteratedFDeriv_infty hG i).comp (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id)))

/-- Jointly smooth exponents are nested-smooth of every order. -/
lemma nestedSmooth_of_contDiff {G : X × (ℝ × ℝ) → ℝ} (hG : ContDiff ℝ ∞ G) (s : Set ℝ) (A B : ℕ) (x : X) :
    NestedSmooth s A B (fun e l => G (x, (e, l))) :=
  ⟨Filter.Eventually.of_forall fun l => (contDiff_of_infty (contDiff_paramE hG x l) A).contDiffAt,
    fun i _ => (contDiff_of_infty (contDiff_paramL hG x i) B).contDiffWithinAt⟩

end Lines

lemma uniqueDiffOn_Ici_inter_ball {r : ℝ} (hr : 0 < r) : UniqueDiffOn ℝ (Ici (0 : ℝ) ∩ ball 0 r) := by
  refine uniqueDiffOn_convex ((convex_Ici 0).inter (convex_ball 0 r)) ⟨r / 2, ?_⟩
  rw [interior_inter, interior_Ici, isOpen_ball.interior_eq]
  refine ⟨mem_Ioi.mpr (by positivity), ?_⟩
  rw [mem_ball_zero_iff, Real.norm_eq_abs, abs_of_pos (by positivity)]
  linarith

section Domination

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X] [OpensMeasurableSpace X]
  {ν : Measure X}

/-- **The domination hypotheses of integral_nestedSmooth_mixedCoeff for `e^F` with a moderate exponent** (`e` in
`ball 0 r`, `l` in `[0, r)`): with `F` moderate on the parameter ball of radius `r > 0`, `e^{F(x, p)} ≤ B(x)` for
`‖p‖ < r`, `p.2 ≥ 0`, and `e^{c ‖x‖} B` integrable for every `c`, there is one integrable bound for all `e`- and
`λ`-derivatives of `e^F` of order `≤ (A, B)`, and all of them are smooth and measurable. -/
theorem exp_domination {F : X × (ℝ × ℝ) → ℝ} {r : ℝ} (hr : 0 < r) (hF : Moderate r F)
    {Bd : X → ℝ} (hB : ∀ x, ∀ p : ℝ × ℝ, ‖p‖ < r → 0 ≤ p.2 → Real.exp (F (x, p)) ≤ Bd x)
    (hint : ∀ c : ℝ, Integrable (fun x => Real.exp (c * ‖x‖) * Bd x) ν) (A B : ℕ) :
    ∃ bound : X → ℝ, Integrable bound ν ∧
      (∀ x, ∀ l ∈ Ici (0 : ℝ) ∩ ball 0 r, ContDiffOn ℝ A (fun e => Real.exp (F (x, (e, l)))) (ball 0 r)) ∧
      (∀ x, ∀ l ∈ Ici (0 : ℝ) ∩ ball 0 r, ∀ i ≤ A, ∀ e ∈ ball (0 : ℝ) r,
        |iteratedDeriv i (fun e => Real.exp (F (x, (e, l)))) e| ≤ bound x) ∧
      (∀ l ∈ Ici (0 : ℝ) ∩ ball 0 r, ∀ i ≤ A, ∀ e ∈ ball (0 : ℝ) r,
        AEStronglyMeasurable (fun x => iteratedDeriv i (fun e => Real.exp (F (x, (e, l)))) e) ν) ∧
      (∀ x, ∀ i ≤ A, ContDiffOn ℝ B (fun l => iteratedDeriv i (fun e => Real.exp (F (x, (e, l)))) 0)
        (Ici 0 ∩ ball 0 r)) ∧
      (∀ x, ∀ i ≤ A, ∀ j ≤ B, ∀ l ∈ Ici (0 : ℝ) ∩ ball 0 r,
        |iteratedDerivWithin j (fun l => iteratedDeriv i (fun e => Real.exp (F (x, (e, l)))) 0) (Ici 0 ∩ ball 0 r) l|
          ≤ bound x) ∧
      (∀ i ≤ A, ∀ j ≤ B, ∀ l ∈ Ici (0 : ℝ) ∩ ball 0 r, AEStronglyMeasurable
        (fun x => iteratedDerivWithin j (fun l => iteratedDeriv i (fun e => Real.exp (F (x, (e, l)))) 0)
          (Ici 0 ∩ ball 0 r) l) ν) := by
  have hG : ContDiff ℝ ∞ (fun y => Real.exp (F y)) := Real.contDiff_exp.comp hF.1
  obtain ⟨C, c, hC, hc, hb⟩ := hF.norm_iteratedFDeriv_exp_le (A + B)
  have hu := uniqueDiffOn_Ici_inter_ball hr
  have hkey : ∀ x, ∀ n ≤ A + B, ∀ p : ℝ × ℝ, ‖p‖ < r → 0 ≤ p.2 →
      ‖iteratedFDeriv ℝ n (fun y => Real.exp (F y)) (x, p)‖ ≤ C * (Real.exp (c * ‖x‖) * Bd x) := by
    intro x n hn p hp hp2
    have h1 := hb n hn x p (mem_closedBall_zero_iff.mpr hp.le)
    have h2 := hB x p hp hp2
    calc _ ≤ C * Real.exp (c * ‖x‖) * Real.exp (F (x, p)) := h1
      _ ≤ C * Real.exp (c * ‖x‖) * Bd x := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = C * (Real.exp (c * ‖x‖) * Bd x) := by ring
  have hpair : ∀ e l : ℝ, e ∈ ball (0 : ℝ) r → l ∈ ball (0 : ℝ) r → ‖((e, l) : ℝ × ℝ)‖ < r := by
    intro e l he hl
    rw [Prod.norm_def]
    exact max_lt (mem_ball_zero_iff.mp he) (mem_ball_zero_iff.mp hl)
  have h0r : (0 : ℝ) ∈ ball (0 : ℝ) r := mem_ball_self hr
  have hE : ∀ (x : X) (e l : ℝ) (i : ℕ), iteratedDeriv i (fun e => Real.exp (F (x, (e, l)))) e =
      iteratedFDeriv ℝ i (fun y => Real.exp (F y)) (x, (e, l)) (fun _ => unitE) := fun x e l i =>
    iteratedDeriv_paramE hG x e l i
  have hL : ∀ (x : X) (i j : ℕ), ∀ l ∈ Ici (0 : ℝ) ∩ ball 0 r,
      iteratedDerivWithin j (fun l => iteratedDeriv i (fun e => Real.exp (F (x, (e, l)))) 0) (Ici 0 ∩ ball 0 r) l =
        iteratedFDeriv ℝ j (iteratedFDeriv ℝ i (fun y => Real.exp (F y))) (x, (0, l)) (fun _ => unitL)
          (fun _ => unitE) := by
    intro x i j l hl
    rw [iteratedDerivWithin_eq_iteratedDeriv hu ((contDiff_of_infty (contDiff_paramL hG x i) j).contDiffAt) hl]
    exact iteratedDeriv_paramL hG x l i j
  refine ⟨fun x => C * (Real.exp (c * ‖x‖) * Bd x), (hint c).const_mul C, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x l _
    exact (contDiff_of_infty (contDiff_paramE hG x l) A).contDiffOn
  · intro x l hl i hi e he
    rw [hE, ← Real.norm_eq_abs]
    exact (norm_apply_const_le _ norm_unitE_le).trans (hkey x i (by omega) (e, l) (hpair e l he hl.2) hl.1)
  · intro l _ i _ e _
    simp only [hE]
    exact ((ContinuousMultilinearMap.apply ℝ _ ℝ (fun _ => unitE)).continuous.comp
      (((contDiff_of_infty hG i).continuous_iteratedFDeriv').comp
        (continuous_id.prodMk continuous_const))).aestronglyMeasurable
  · intro x i _
    exact (contDiff_of_infty (contDiff_paramL hG x i) B).contDiffOn
  · intro x i hi j hj l hl
    rw [hL x i j l hl, ← Real.norm_eq_abs]
    refine (norm_apply_const_le _ norm_unitE_le).trans ((norm_apply_const_le _ norm_unitL_le).trans ?_)
    rw [norm_iteratedFDeriv_iteratedFDeriv]
    exact hkey x (i + j) (by omega) (0, l) (hpair 0 l h0r hl.2) hl.1
  · intro i _ j _ l hl
    have hfun : (fun x => iteratedDerivWithin j (fun l => iteratedDeriv i (fun e => Real.exp (F (x, (e, l)))) 0)
        (Ici 0 ∩ ball 0 r) l) = fun x => iteratedFDeriv ℝ j (iteratedFDeriv ℝ i (fun y => Real.exp (F y)))
          (x, (0, l)) (fun _ => unitL) (fun _ => unitE) := funext fun x => hL x i j l hl
    rw [hfun]
    have hc2 : Continuous (iteratedFDeriv ℝ j (iteratedFDeriv ℝ i (fun y => Real.exp (F y)))) :=
      (contDiff_of_infty (contDiff_iteratedFDeriv_infty hG i) j).continuous_iteratedFDeriv'
    exact ((ContinuousMultilinearMap.apply ℝ _ ℝ (fun _ => unitE)).continuous.comp
      ((ContinuousMultilinearMap.apply ℝ _ _ (fun _ => unitL)).continuous.comp
        (hc2.comp (continuous_id.prodMk continuous_const)))).aestronglyMeasurable

/-- **Differentiation under the integral sign for `∫ e^F` with a moderate exponent**: under the hypotheses of
exp_domination, `Z(e, l) = ∫ e^{F(x, (e, l))} dν` is nested-smooth of every order at `(0, 0)` (`l` within `[0, ∞)`)
and its mixed Taylor coefficients are the integrals of those of `e^F`. -/
theorem integral_exp_nestedSmooth {F : X × (ℝ × ℝ) → ℝ} {r : ℝ} (hr : 0 < r) (hF : Moderate r F)
    {Bd : X → ℝ} (hB : ∀ x, ∀ p : ℝ × ℝ, ‖p‖ < r → 0 ≤ p.2 → Real.exp (F (x, p)) ≤ Bd x)
    (hint : ∀ c : ℝ, Integrable (fun x => Real.exp (c * ‖x‖) * Bd x) ν) (A B : ℕ) :
    NestedSmooth (Ici 0) A B (fun e l => ∫ x, Real.exp (F (x, (e, l))) ∂ν) ∧
      ∀ i ≤ A, ∀ j ≤ B, mixedCoeff (Ici 0) i j (fun e l => ∫ x, Real.exp (F (x, (e, l))) ∂ν) =
        ∫ x, mixedCoeff (Ici 0) i j (fun e l => Real.exp (F (x, (e, l)))) ∂ν := by
  obtain ⟨bound, hb, h1, h2, h3, h4, h5, h6⟩ := exp_domination hr hF hB hint A B
  exact integral_nestedSmooth_mixedCoeff (convex_Ici 0) (mem_Ici.mpr le_rfl) hr (uniqueDiffOn_Ici_inter_ball hr)
    (G := fun x e l => Real.exp (F (x, (e, l)))) hb h1 h2 h3 h4 h5 h6

end Domination

section GaussianIntegrability

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
  [BorelSpace E]

/-- `e^{c ‖y‖ - c₁ ‖x₀ + y‖²}` is integrable (`c₁ > 0`): it is at most `e^{|c| ‖x₀‖ + c²/(2c₁)} e^{-(c₁/2) ‖x₀ + y‖²}`. -/
lemma integrable_exp_mul_norm_sub_sq (x₀ : E) {c₁ : ℝ} (hc₁ : 0 < c₁) (c : ℝ) :
    Integrable (fun y : E => Real.exp (c * ‖y‖ - c₁ * ‖x₀ + y‖ ^ 2)) := by
  set T : E →ₗ[ℝ] E := c₁ • LinearMap.id
  have hT : T.IsSymmetric := fun x y => by simp [T, inner_smul_left, inner_smul_right]
  have hpos : ∀ x, x ≠ 0 → 0 < ⟪x, T x⟫ := by
    intro x hx
    simp only [T, LinearMap.smul_apply, LinearMap.id_apply, inner_smul_right, real_inner_self_eq_norm_sq]
    have := norm_pos_iff.mpr hx
    positivity
  set K := Real.exp (|c| * ‖x₀‖ + c ^ 2 / (2 * c₁))
  have hI := ((integrable_gaussWeight hT hpos).comp_add_left x₀).const_mul K
  refine hI.mono' (by fun_prop) (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hgw : gaussWeight T (x₀ + y) = Real.exp (-(1 / 2) * (c₁ * ‖x₀ + y‖ ^ 2)) := by
    simp only [gaussWeight, T, LinearMap.smul_apply, LinearMap.id_apply, inner_smul_right, real_inner_self_eq_norm_sq]
  rw [hgw, ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have h1 : c * ‖y‖ ≤ |c| * (‖x₀ + y‖ + ‖x₀‖) := by
    have hy : ‖y‖ ≤ ‖x₀ + y‖ + ‖x₀‖ := by
      calc ‖y‖ = ‖(x₀ + y) - x₀‖ := by rw [add_sub_cancel_left]
        _ ≤ ‖x₀ + y‖ + ‖x₀‖ := norm_sub_le _ _
    calc c * ‖y‖ ≤ |c| * ‖y‖ := mul_le_mul_of_nonneg_right (le_abs_self c) (norm_nonneg y)
      _ ≤ |c| * (‖x₀ + y‖ + ‖x₀‖) := mul_le_mul_of_nonneg_left hy (abs_nonneg c)
  have h2 : |c| * ‖x₀ + y‖ ≤ c ^ 2 / (2 * c₁) + c₁ / 2 * ‖x₀ + y‖ ^ 2 := by
    have hsq : 0 ≤ c₁ / 2 * (‖x₀ + y‖ - |c| / c₁) ^ 2 := by positivity
    have hc2 : |c| ^ 2 = c ^ 2 := sq_abs c
    have : c₁ / 2 * (‖x₀ + y‖ - |c| / c₁) ^ 2 =
        c₁ / 2 * ‖x₀ + y‖ ^ 2 - |c| * ‖x₀ + y‖ + |c| ^ 2 / (2 * c₁) := by
      field_simp
      ring
    rw [this, hc2] at hsq
    linarith
  nlinarith

/-- Integrability against `μ_T` of `e^{c ‖y‖}` times `e^{½⟪y, T y⟫ + K - c₁ ‖x₀ + y‖²}`, for every `c` (`c₁ > 0`). -/
lemma integrable_gaussProb_exp_quadratic {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) (hpos : ∀ x, x ≠ 0 → 0 < ⟪x, T x⟫)
    (x₀ : E) {c₁ : ℝ} (hc₁ : 0 < c₁) (K c : ℝ) :
    Integrable (fun y => Real.exp (c * ‖y‖) * Real.exp (1 / 2 * ⟪y, T y⟫ + K - c₁ * ‖x₀ + y‖ ^ 2)) (gaussProb T) := by
  rw [integrable_gaussProb_iff hT hpos]
  refine ((integrable_exp_mul_norm_sub_sq x₀ hc₁ c).const_mul (Real.exp K)).congr
    (Filter.Eventually.of_forall fun y => ?_)
  simp only [gaussWeight]
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

end GaussianIntegrability

end GaussianBlockSpin
