import GaussianBlockSpin.LogDerivatives

/-! Differentiation under the integral sign for one real parameter within a convex set, including one-sided derivatives
at an endpoint (Mathlib's parametric-integral lemmas are for open neighbourhoods only). hasDerivWithinAt_integral_of_dominated
(one derivative), integral_iteratedDerivWithin and integral_contDiffOn_iteratedDerivWithin (iterated derivatives and
`C^N`), integral_contDiffAt_iteratedDeriv (two-sided, at `0`), and integral_nestedSmooth_mixedCoeff: for `Z(e, l) = ∫ G x e l`
with nested domination, `Z` is nested-smooth and its mixed Taylor coefficients (`e` two-sided, `l` within `s`, e.g.
`s = [0, ∞)` for `λ'` in (3.36)) are the integrals of those of `G x`. -/

open MeasureTheory Filter Metric
open scoped Topology

namespace GaussianBlockSpin

section OneParameter

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- **Differentiation under the integral sign within a convex set** (one real parameter; one-sided at an endpoint):
if `F x` is integrable at `x₀`, measurable near `x₀` in `t`, and on `t ∩ ball x₀ ε` each `F · a` has derivative
`F' x a` within `t` with `|F' x a| ≤ bound a` (integrable), then `x ↦ ∫ F x a` has derivative `∫ F' x₀ a` within `t` at
`x₀`. -/
theorem hasDerivWithinAt_integral_of_dominated {F F' : ℝ → α → ℝ} {t : Set ℝ} (ht : Convex ℝ t) {x₀ : ℝ}
    {ε : ℝ} (hε : 0 < ε) {bound : α → ℝ}
    (hF_meas : ∀ x ∈ t ∩ ball x₀ ε, AEStronglyMeasurable (F x) μ) (hF_int : Integrable (F x₀) μ)
    (hF'_meas : AEStronglyMeasurable (F' x₀) μ)
    (h_bound : ∀ᵐ a ∂μ, ∀ x ∈ t ∩ ball x₀ ε, |F' x a| ≤ bound a) (bound_integrable : Integrable bound μ)
    (h_diff : ∀ᵐ a ∂μ, ∀ x ∈ t ∩ ball x₀ ε, HasDerivWithinAt (fun y => F y a) (F' x a) t x)
    (hx₀ : x₀ ∈ t) :
    Integrable (F' x₀) μ ∧ HasDerivWithinAt (fun x => ∫ a, F x a ∂μ) (∫ a, F' x₀ a ∂μ) t x₀ := by
  set u := t ∩ ball x₀ ε with hu
  have hu_conv : Convex ℝ u := ht.inter (convex_ball x₀ ε)
  have hx₀u : x₀ ∈ u := ⟨hx₀, mem_ball_self hε⟩
  -- Lipschitz bound from the mean value inequality
  have h_lip : ∀ᵐ a ∂μ, ∀ x ∈ u, |F x a - F x₀ a| ≤ bound a * |x - x₀| := by
    filter_upwards [h_bound, h_diff] with a hb hd x hx
    have := hu_conv.norm_image_sub_le_of_norm_hasDerivWithin_le (f := fun y => F y a) (f' := fun y => F' y a)
      (fun y hy => (hd y hy).mono Set.inter_subset_left) (fun y hy => by
        rw [Real.norm_eq_abs]; exact hb y hy) hx₀u hx
    simpa [Real.norm_eq_abs] using this
  have hF'_int : Integrable (F' x₀) μ := by
    refine bound_integrable.mono' hF'_meas ?_
    filter_upwards [h_bound] with a hb
    rw [Real.norm_eq_abs]
    exact hb x₀ hx₀u
  have hF_int' : ∀ x ∈ u, Integrable (F x) μ := by
    intro x hx
    have hbx : Integrable (fun a => |F x₀ a| + bound a * |x - x₀|) μ :=
      hF_int.abs.add (bound_integrable.mul_const _)
    refine hbx.mono' (hF_meas x hx) ?_
    filter_upwards [h_lip] with a ha
    rw [Real.norm_eq_abs]
    have := ha x hx
    calc |F x a| = |F x₀ a + (F x a - F x₀ a)| := by ring_nf
      _ ≤ |F x₀ a| + |F x a - F x₀ a| := abs_add_le _ _
      _ ≤ |F x₀ a| + bound a * |x - x₀| := by linarith
  refine ⟨hF'_int, ?_⟩
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have hmem : ∀ᶠ y in 𝓝[t \ {x₀}] x₀, y ∈ u ∧ y ≠ x₀ := by
    have h1 : u ∈ 𝓝[t] x₀ := inter_mem_nhdsWithin t (ball_mem_nhds x₀ hε)
    have h2 : ∀ᶠ y in 𝓝[t \ {x₀}] x₀, y ∈ u := nhdsWithin_mono _ Set.sdiff_subset h1
    have h3 : ∀ᶠ y in 𝓝[t \ {x₀}] x₀, y ≠ x₀ := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact hy.2
    exact h2.and h3
  have hslope : ∀ᶠ y in 𝓝[t \ {x₀}] x₀, slope (fun x => ∫ a, F x a ∂μ) x₀ y =
      ∫ a, slope (fun x => F x a) x₀ y ∂μ := by
    filter_upwards [hmem] with y hy
    simp only [slope, vsub_eq_sub, smul_eq_mul]
    rw [integral_const_mul, integral_sub (hF_int' y hy.1) hF_int]
  refine Tendsto.congr' (EventuallyEq.symm hslope) ?_
  refine tendsto_integral_filter_of_dominated_convergence bound ?_ ?_ bound_integrable ?_
  · filter_upwards [hmem] with y hy
    simp only [slope, vsub_eq_sub, smul_eq_mul]
    exact ((hF_meas y hy.1).sub hF_int.aestronglyMeasurable).const_mul _
  · filter_upwards [hmem] with y hy
    filter_upwards [h_lip] with a ha
    simp only [slope, vsub_eq_sub, smul_eq_mul, Real.norm_eq_abs]
    have hne : 0 < |y - x₀| := abs_pos.mpr (sub_ne_zero.mpr hy.2)
    rw [abs_mul, abs_inv]
    calc |y - x₀|⁻¹ * |F y a - F x₀ a| ≤ |y - x₀|⁻¹ * (bound a * |y - x₀|) :=
          mul_le_mul_of_nonneg_left (ha y hy.1) (inv_nonneg.mpr hne.le)
      _ = bound a := by field_simp
  · filter_upwards [h_diff] with a ha
    exact hasDerivWithinAt_iff_tendsto_slope.mp (ha x₀ hx₀u)

/-- **Iterated derivatives under the integral sign on a convex set**: for a family `G 0, …, G N` with `G (k+1)` the
derivative of `G k` within `u` (for a.e. `a`), all dominated by an integrable `bound`, measurable, and `G N` continuous on
`u`, the `k`-th derivative of `x ↦ ∫ G 0 x a` within `u` is `∫ G k x a` on `u`, and that function is `C^N` on `u`. -/
theorem integral_iteratedDerivWithin {G : ℕ → ℝ → α → ℝ} {u : Set ℝ} (hu_conv : Convex ℝ u) (hu : UniqueDiffOn ℝ u)
    {N : ℕ} {bound : α → ℝ} (hG_meas : ∀ k ≤ N, ∀ x ∈ u, AEStronglyMeasurable (G k x) μ)
    (hG_bound : ∀ k ≤ N, ∀ᵐ a ∂μ, ∀ x ∈ u, |G k x a| ≤ bound a) (bound_integrable : Integrable bound μ)
    (hG_diff : ∀ k < N, ∀ᵐ a ∂μ, ∀ x ∈ u, HasDerivWithinAt (fun y => G k y a) (G (k + 1) x a) u x)
    (hG_cont : ∀ᵐ a ∂μ, ContinuousOn (fun x => G N x a) u) :
    (∀ k ≤ N, ∀ x ∈ u, iteratedDerivWithin k (fun y => ∫ a, G 0 y a ∂μ) u x = ∫ a, G k x a ∂μ) ∧
      ContDiffOn ℝ N (fun y => ∫ a, G 0 y a ∂μ) u := by
  have hint : ∀ k ≤ N, ∀ x ∈ u, Integrable (G k x) μ := by
    intro k hk x hx
    refine bound_integrable.mono' (hG_meas k hk x hx) ?_
    filter_upwards [hG_bound k hk] with a ha
    rw [Real.norm_eq_abs]
    exact ha x hx
  have hderiv : ∀ k < N, ∀ x ∈ u,
      HasDerivWithinAt (fun y => ∫ a, G k y a ∂μ) (∫ a, G (k + 1) x a ∂μ) u x := by
    intro k hk x hx
    refine (hasDerivWithinAt_integral_of_dominated hu_conv one_pos (F := G k) (F' := G (k + 1)) (bound := bound)
      (fun y hy => hG_meas k hk.le y hy.1) (hint k hk.le x hx) (hG_meas (k + 1) hk x hx) ?_ bound_integrable ?_ hx).2
    · filter_upwards [hG_bound (k + 1) hk] with a ha y hy
      exact ha y hy.1
    · filter_upwards [hG_diff k hk] with a ha y hy
      exact ha y hy.1
  have hiter : ∀ k ≤ N, ∀ x ∈ u, iteratedDerivWithin k (fun y => ∫ a, G 0 y a ∂μ) u x = ∫ a, G k x a ∂μ := by
    intro k
    induction k with
    | zero => intro _ x _; simp
    | succ k ih =>
      intro hk x hx
      rw [iteratedDerivWithin_succ]
      rw [derivWithin_congr (fun y hy => ih (by omega) y hy) (ih (by omega) x hx)]
      exact (hderiv k (by omega) x hx).derivWithin (hu x hx)
  refine ⟨hiter, ?_⟩
  refine contDiffOn_of_continuousOn_differentiableOn_deriv (fun m hm => ?_) (fun m hm => ?_)
  · have hm' : m ≤ N := by exact_mod_cast hm
    refine ContinuousOn.congr ?_ (fun y hy => hiter m hm' y hy)
    rcases lt_or_eq_of_le hm' with hlt | heq
    · exact fun y hy => (hderiv m hlt y hy).continuousWithinAt
    · subst heq
      refine continuousOn_of_dominated (fun y hy => hG_meas m le_rfl y hy) (fun y hy => ?_) bound_integrable hG_cont
      filter_upwards [hG_bound m le_rfl] with a ha
      rw [Real.norm_eq_abs]
      exact ha y hy
  · have hm' : m < N := by exact_mod_cast hm
    refine DifferentiableOn.congr ?_ (fun y hy => hiter m hm'.le y hy)
    exact fun y hy => (hderiv m hm' y hy).differentiableWithinAt

end OneParameter

lemma hasDerivWithinAt_iteratedDerivWithin_of_contDiffOn {f : ℝ → ℝ} {u : Set ℝ} {N k : ℕ}
    (hf : ContDiffOn ℝ N f u) (hu : UniqueDiffOn ℝ u) (hk : k < N) {y : ℝ} (hy : y ∈ u) :
    HasDerivWithinAt (iteratedDerivWithin k f u) (iteratedDerivWithin (k + 1) f u y) u y := by
  have hd := hf.differentiableOn_iteratedDerivWithin (m := k) (by exact_mod_cast hk) hu y hy
  rw [iteratedDerivWithin_succ]
  exact hd.hasDerivWithinAt

lemma iteratedDerivWithin_inter_isOpen {f : ℝ → ℝ} {s U : Set ℝ} (hU : IsOpen U) {x : ℝ} (hx : x ∈ U) (n : ℕ) :
    iteratedDerivWithin n f (s ∩ U) x = iteratedDerivWithin n f s x := by
  simp only [iteratedDerivWithin, iteratedFDerivWithin_inter_open hU hx]

section Parametric

variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}

/-- **Parametric integrals of `C^N` functions on a convex set**: if each `H x` is `C^N` on `u` (convex, unique
derivatives) with all within-derivatives of order `≤ N` bounded on `u` by an integrable `bound` and measurable in `x`,
then `l ↦ ∫ H x l` is `C^N` on `u` and its within-derivatives are the integrals of those of `H x`. -/
theorem integral_contDiffOn_iteratedDerivWithin {H : Ω → ℝ → ℝ} {u : Set ℝ} (hu_conv : Convex ℝ u)
    (hu : UniqueDiffOn ℝ u) {N : ℕ} {bound : Ω → ℝ} (hb : Integrable bound ν)
    (hsmooth : ∀ x, ContDiffOn ℝ N (H x) u)
    (hbound : ∀ x, ∀ j ≤ N, ∀ l ∈ u, |iteratedDerivWithin j (H x) u l| ≤ bound x)
    (hmeas : ∀ j ≤ N, ∀ l ∈ u, AEStronglyMeasurable (fun x => iteratedDerivWithin j (H x) u l) ν) :
    ContDiffOn ℝ N (fun l => ∫ x, H x l ∂ν) u ∧
      ∀ j ≤ N, ∀ l ∈ u, iteratedDerivWithin j (fun l => ∫ x, H x l ∂ν) u l =
        ∫ x, iteratedDerivWithin j (H x) u l ∂ν := by
  have h := integral_iteratedDerivWithin (μ := ν) (G := fun k l x => iteratedDerivWithin k (H x) u l)
    hu_conv hu (N := N) (bound := bound) (fun k hk l hl => hmeas k hk l hl)
    (fun k hk => Eventually.of_forall fun x l hl => hbound x k hk l hl) hb
    (fun k hk => Eventually.of_forall fun x l hl =>
      hasDerivWithinAt_iteratedDerivWithin_of_contDiffOn (hsmooth x) hu hk hl)
    (Eventually.of_forall fun x => (hsmooth x).continuousOn_iteratedDerivWithin le_rfl hu)
  simp only [iteratedDerivWithin_zero] at h
  exact ⟨h.2, h.1⟩

/-- The two-sided version at `0`: parametric integrals of functions `C^N` on `ball 0 ε` are `C^N` at `0`, with
`(∫ H x ·)^{(i)}(0) = ∫ (H x)^{(i)}(0)`. -/
theorem integral_contDiffAt_iteratedDeriv {H : Ω → ℝ → ℝ} {ε : ℝ} (hε : 0 < ε) {N : ℕ} {bound : Ω → ℝ}
    (hb : Integrable bound ν) (hsmooth : ∀ x, ContDiffOn ℝ N (H x) (ball 0 ε))
    (hbound : ∀ x, ∀ i ≤ N, ∀ e ∈ ball (0 : ℝ) ε, |iteratedDeriv i (H x) e| ≤ bound x)
    (hmeas : ∀ i ≤ N, ∀ e ∈ ball (0 : ℝ) ε, AEStronglyMeasurable (fun x => iteratedDeriv i (H x) e) ν) :
    ContDiffAt ℝ N (fun e => ∫ x, H x e ∂ν) 0 ∧
      ∀ i ≤ N, iteratedDeriv i (fun e => ∫ x, H x e ∂ν) 0 = ∫ x, iteratedDeriv i (H x) 0 ∂ν := by
  have hopen : IsOpen (ball (0 : ℝ) ε) := isOpen_ball
  have h0 : (0 : ℝ) ∈ ball (0 : ℝ) ε := mem_ball_self hε
  have hconv := integral_contDiffOn_iteratedDerivWithin (ν := ν) (H := H) (convex_ball 0 ε) hopen.uniqueDiffOn hb
    hsmooth
    (fun x j hj l hl => by rw [iteratedDerivWithin_of_isOpen hopen hl]; exact hbound x j hj l hl)
    (fun j hj l hl => by
      have : (fun x => iteratedDerivWithin j (H x) (ball 0 ε) l) = fun x => iteratedDeriv j (H x) l := by
        funext x
        rw [iteratedDerivWithin_of_isOpen hopen hl]
      rw [this]
      exact hmeas j hj l hl)
  refine ⟨hconv.1.contDiffAt (hopen.mem_nhds h0), fun i hi => ?_⟩
  have h1 := hconv.2 i hi 0 h0
  rw [iteratedDerivWithin_of_isOpen hopen h0] at h1
  rw [h1]
  congr 1
  funext x
  exact iteratedDerivWithin_of_isOpen hopen h0

/-- **Mixed Taylor coefficients of a parametric integral**: let `s` be convex with `0 ∈ s` and `s ∩ ball 0 ε` with
unique derivatives. Suppose that for every `x`:
* for `l ∈ s ∩ ball 0 ε`, `e ↦ G x e l` is `C^A` on `ball 0 ε`, its derivatives of order `≤ A` bounded there by
  `bound x`;
* for `i ≤ A`, `l ↦ ∂_e^i G x 0 l` is `C^B` on `s ∩ ball 0 ε`, its within-derivatives of order `≤ B` bounded there by
  `bound x`;

with `bound` integrable and all these derivatives measurable in `x`. Then `Z(e, l) = ∫ G x e l dν` is nested-smooth of
order `(A, B)` and `∂_λ^j ∂_e^i Z(0, 0) = ∫ ∂_λ^j ∂_e^i G x (0, 0) dν` for `i ≤ A`, `j ≤ B`. -/
theorem integral_nestedSmooth_mixedCoeff {s : Set ℝ} (hs_conv : Convex ℝ s) (h0 : (0 : ℝ) ∈ s) {ε : ℝ}
    (hε : 0 < ε) (hu : UniqueDiffOn ℝ (s ∩ ball 0 ε)) {A B : ℕ} {G : Ω → ℝ → ℝ → ℝ} {bound : Ω → ℝ}
    (hb : Integrable bound ν)
    (hE_smooth : ∀ x, ∀ l ∈ s ∩ ball 0 ε, ContDiffOn ℝ A (fun e => G x e l) (ball 0 ε))
    (hE_bound : ∀ x, ∀ l ∈ s ∩ ball 0 ε, ∀ i ≤ A, ∀ e ∈ ball (0 : ℝ) ε,
      |iteratedDeriv i (fun e => G x e l) e| ≤ bound x)
    (hE_meas : ∀ l ∈ s ∩ ball 0 ε, ∀ i ≤ A, ∀ e ∈ ball (0 : ℝ) ε,
      AEStronglyMeasurable (fun x => iteratedDeriv i (fun e => G x e l) e) ν)
    (hL_smooth : ∀ x, ∀ i ≤ A, ContDiffOn ℝ B (fun l => iteratedDeriv i (fun e => G x e l) 0) (s ∩ ball 0 ε))
    (hL_bound : ∀ x, ∀ i ≤ A, ∀ j ≤ B, ∀ l ∈ s ∩ ball 0 ε,
      |iteratedDerivWithin j (fun l => iteratedDeriv i (fun e => G x e l) 0) (s ∩ ball 0 ε) l| ≤ bound x)
    (hL_meas : ∀ i ≤ A, ∀ j ≤ B, ∀ l ∈ s ∩ ball 0 ε, AEStronglyMeasurable
      (fun x => iteratedDerivWithin j (fun l => iteratedDeriv i (fun e => G x e l) 0) (s ∩ ball 0 ε) l) ν) :
    NestedSmooth s A B (fun e l => ∫ x, G x e l ∂ν) ∧
      ∀ i ≤ A, ∀ j ≤ B, mixedCoeff s i j (fun e l => ∫ x, G x e l ∂ν) = ∫ x, mixedCoeff s i j (G x) ∂ν := by
  set u := s ∩ ball (0 : ℝ) ε with hudef
  have hu_conv : Convex ℝ u := hs_conv.inter (convex_ball 0 ε)
  have h0u : (0 : ℝ) ∈ u := ⟨h0, mem_ball_self hε⟩
  have hu_nhds : u ∈ 𝓝[s] (0 : ℝ) := inter_mem_nhdsWithin s (ball_mem_nhds 0 hε)
  -- the `e`-direction, for each `l ∈ u`
  have hA : ∀ l ∈ u, ContDiffAt ℝ A (fun e => ∫ x, G x e l ∂ν) 0 ∧
      ∀ i ≤ A, iteratedDeriv i (fun e => ∫ x, G x e l ∂ν) 0 = ∫ x, iteratedDeriv i (fun e => G x e l) 0 ∂ν :=
    fun l hl => integral_contDiffAt_iteratedDeriv (H := fun x e => G x e l) hε hb (fun x => hE_smooth x l hl)
      (fun x i hi e he => hE_bound x l hl i hi e he) (fun i hi e he => hE_meas l hl i hi e he)
  -- the `λ`-direction, for each `i ≤ A`
  have hB : ∀ i ≤ A, ContDiffOn ℝ B (fun l => ∫ x, iteratedDeriv i (fun e => G x e l) 0 ∂ν) u ∧
      ∀ j ≤ B, ∀ l ∈ u, iteratedDerivWithin j (fun l => ∫ x, iteratedDeriv i (fun e => G x e l) 0 ∂ν) u l =
        ∫ x, iteratedDerivWithin j (fun l => iteratedDeriv i (fun e => G x e l) 0) u l ∂ν :=
    fun i hi => integral_contDiffOn_iteratedDerivWithin (H := fun x l => iteratedDeriv i (fun e => G x e l) 0)
      hu_conv hu hb (fun x => hL_smooth x i hi) (fun x j hj l hl => hL_bound x i hi j hj l hl)
      (fun j hj l hl => hL_meas i hi j hj l hl)
  have heq : ∀ i ≤ A, Set.EqOn (fun l => iteratedDeriv i (fun e => ∫ x, G x e l ∂ν) 0)
      (fun l => ∫ x, iteratedDeriv i (fun e => G x e l) 0 ∂ν) u := fun i hi l hl => (hA l hl).2 i hi
  refine ⟨⟨?_, fun i hi => ?_⟩, fun i hi j hj => ?_⟩
  · filter_upwards [hu_nhds] with l hl
    exact (hA l hl).1
  · exact (((hB i hi).1.congr (heq i hi)).contDiffWithinAt h0u).mono_of_mem_nhdsWithin hu_nhds
  · unfold mixedCoeff
    have hopen : IsOpen (ball (0 : ℝ) ε) := isOpen_ball
    have h0b : (0 : ℝ) ∈ ball (0 : ℝ) ε := mem_ball_self hε
    rw [← iteratedDerivWithin_inter_isOpen hopen h0b, ← hudef,
      iteratedDerivWithin_congr (heq i hi) h0u, (hB i hi).2 j hj 0 h0u]
    congr 1
    funext x
    rw [hudef, iteratedDerivWithin_inter_isOpen hopen h0b]

end Parametric

end GaussianBlockSpin
