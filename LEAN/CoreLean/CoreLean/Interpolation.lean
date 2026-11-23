/-
`lem:interpolation` of BALABAN_CORE.tex: the derivative of the logarithm of a partition function
along an interpolation.

The hypotheses are those of the lemma: `μ` is a finite positive measure with `μ ≠ 0`, the
functions `f_t`, `t ∈ [0, 1]`, are measurable and bounded uniformly in `t`, and differentiable in
`t` (within `[0, 1]`) with a derivative bounded uniformly in `t`. The measurability of the
derivative is not assumed; it is derived from that of the `f_t`.
-/
import Mathlib

open MeasureTheory Set Filter Topology

namespace CoreLean

variable {α : Type*} [MeasurableSpace α]

/-- The derivative within `[0, 1]` of a family of measurable functions is measurable: it is the
pointwise limit of measurable difference quotients. -/
lemma measurable_derivWithin_family (f f' : ℝ → α → ℝ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
    (hmeas : ∀ s ∈ Icc (0 : ℝ) 1, Measurable (f s))
    (hderiv : ∀ x, HasDerivWithinAt (fun s => f s x) (f' t x) (Icc 0 1) t) :
    Measurable (f' t) := by
  -- a sequence `s_n → t` in `[0, 1] \ {t}`
  obtain ⟨s, hs_mem, hs_ne, hs_lim⟩ : ∃ s : ℕ → ℝ, (∀ n, s n ∈ Icc (0 : ℝ) 1) ∧
      (∀ n, s n ≠ t) ∧ Tendsto s atTop (𝓝 t) := by
    by_cases h1 : t < 1
    · refine ⟨fun n => t + (1 - t) / (n + 2), fun n => ⟨?_, ?_⟩, fun n => ?_, ?_⟩
      · have : 0 ≤ (1 - t) / ((n : ℝ) + 2) := div_nonneg (by linarith) (by positivity)
        linarith [ht.1]
      · have h2 : (1 - t) / ((n : ℝ) + 2) ≤ 1 - t := div_le_self (by linarith) (by linarith)
        linarith
      · have : 0 < (1 - t) / ((n : ℝ) + 2) := div_pos (by linarith) (by positivity)
        linarith
      · have h0 : Tendsto (fun n : ℕ => (1 - t) / ((n : ℝ) + 2)) atTop (𝓝 0) := by
          apply Tendsto.div_atTop tendsto_const_nhds
          exact tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
        simpa using (tendsto_const_nhds (x := t)).add h0
    · have ht1 : t = 1 := le_antisymm ht.2 (not_lt.mp h1)
      subst ht1
      refine ⟨fun n => 1 - 1 / (n + 2), fun n => ⟨?_, ?_⟩, fun n => ?_, ?_⟩
      · have : 1 / ((n : ℝ) + 2) ≤ 1 := by
          rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
        linarith
      · have : 0 ≤ 1 / ((n : ℝ) + 2) := by positivity
        linarith
      · have : 0 < 1 / ((n : ℝ) + 2) := by positivity
        linarith
      · have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 0) := by
          apply Tendsto.div_atTop tendsto_const_nhds
          exact tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
        simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub h0
  have hs_within : Tendsto s atTop (𝓝[Icc 0 1 \ {t}] t) :=
    tendsto_nhdsWithin_iff.mpr ⟨hs_lim, Eventually.of_forall fun n => ⟨hs_mem n, hs_ne n⟩⟩
  refine measurable_of_tendsto_metrizable (f := fun n x => (s n - t)⁻¹ * (f (s n) x - f t x))
    (fun n => ?_) ?_
  · exact measurable_const.mul ((hmeas _ (hs_mem n)).sub (hmeas t ht))
  · rw [tendsto_pi_nhds]
    intro x
    have hslope := (hasDerivWithinAt_iff_tendsto_slope.mp (hderiv x)).comp hs_within
    refine hslope.congr fun i => ?_
    simp only [Function.comp_apply, slope_def_field]
    ring

/-- `lem:interpolation`, `eq:interpolation`:
`log ∫ e^{f_1} dμ - log ∫ e^{f_0} dμ = ∫_0^1 ⟨∂_t f_t⟩_t dt` with
`⟨φ⟩_t = ∫ φ e^{f_t} dμ / ∫ e^{f_t} dμ`. -/
theorem interpolation (μ : Measure α) [IsFiniteMeasure μ] (hμ : μ ≠ 0)
    (f f' : ℝ → α → ℝ) (M M' : ℝ)
    (hmeas : ∀ t ∈ Icc (0 : ℝ) 1, Measurable (f t))
    (hbd : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, |f t x| ≤ M)
    (hderiv : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, HasDerivWithinAt (fun s => f s x) (f' t x) (Icc 0 1) t)
    (hbd' : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, |f' t x| ≤ M') :
    Real.log (∫ x, Real.exp (f 1 x) ∂μ) - Real.log (∫ x, Real.exp (f 0 x) ∂μ) =
      ∫ t in (0 : ℝ)..1, (∫ x, f' t x * Real.exp (f t x) ∂μ) / (∫ x, Real.exp (f t x) ∂μ) := by
  set Z : ℝ → ℝ := fun t => ∫ x, Real.exp (f t x) ∂μ with hZ
  set Z' : ℝ → ℝ := fun t => ∫ x, f' t x * Real.exp (f t x) ∂μ with hZ'
  have hmeas' : ∀ t ∈ Icc (0 : ℝ) 1, Measurable (f' t) := fun t ht =>
    measurable_derivWithin_family f f' t ht hmeas (hderiv t ht)
  have hμpos : 0 < μ.real univ := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (Measure.measure_univ_ne_zero.mpr hμ) (measure_ne_top _ _)
  -- the integrands are bounded and measurable, hence integrable
  have hint : ∀ t ∈ Icc (0 : ℝ) 1, Integrable (fun x => Real.exp (f t x)) μ := by
    intro t ht
    refine Integrable.of_bound (hmeas t ht).exp.aestronglyMeasurable (Real.exp M) ?_
    refine Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (le_of_abs_le (hbd t ht x))
  have hint' : ∀ t ∈ Icc (0 : ℝ) 1, Integrable (fun x => f' t x * Real.exp (f t x)) μ := by
    intro t ht
    refine Integrable.of_bound ((hmeas' t ht).mul (hmeas t ht).exp).aestronglyMeasurable
      (M' * Real.exp M) ?_
    refine Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul (hbd' t ht x) (Real.exp_le_exp.mpr (le_of_abs_le (hbd t ht x)))
      (Real.exp_pos _).le ((abs_nonneg _).trans (hbd' t ht x))
  -- `Z(t) ≥ e^{-M} μ(α) > 0`
  have hZpos : ∀ t ∈ Icc (0 : ℝ) 1, 0 < Z t := by
    intro t ht
    have hlow : ∫ _x, Real.exp (-M) ∂μ ≤ Z t := by
      refine integral_mono (integrable_const _) (hint t ht) fun x => ?_
      exact Real.exp_le_exp.mpr (neg_le_of_abs_le (hbd t ht x))
    rw [integral_const, smul_eq_mul] at hlow
    exact lt_of_lt_of_le (mul_pos hμpos (Real.exp_pos _)) hlow
  -- `Z` is differentiable on `(0, 1)` with the derivative `Z'`
  have hZderiv : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt Z (Z' t) t := by
    intro t ht
    have htI := Ioo_subset_Icc_self ht
    have hio : Ioo (0 : ℝ) 1 ∈ 𝓝 t := isOpen_Ioo.mem_nhds ht
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
      (F := fun s x => Real.exp (f s x)) (F' := fun s x => f' s x * Real.exp (f s x))
      (bound := fun _ => M' * Real.exp M) hio
      (mem_of_superset hio fun s hs =>
        (hmeas s (Ioo_subset_Icc_self hs)).exp.aestronglyMeasurable)
      (hint t htI) ((hmeas' t htI).mul (hmeas t htI).exp).aestronglyMeasurable
      (Eventually.of_forall fun x s hs => ?_) (integrable_const _)
      (Eventually.of_forall fun x s hs => ?_)).2
    · have hs' := Ioo_subset_Icc_self hs
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul (hbd' s hs' x) (Real.exp_le_exp.mpr (le_of_abs_le (hbd s hs' x)))
        (Real.exp_pos _).le ((abs_nonneg _).trans (hbd' s hs' x))
    · have hs' := Ioo_subset_Icc_self hs
      have hin : Icc (0 : ℝ) 1 ∈ 𝓝 s := Icc_mem_nhds hs.1 hs.2
      exact ((hderiv s hs' x).hasDerivAt hin).exp.congr_deriv (mul_comm _ _)
  -- `Z` is continuous on `[0, 1]`, by dominated convergence
  have hZcont : ContinuousOn Z (Icc 0 1) := by
    refine continuousOn_of_dominated (bound := fun _ => Real.exp M)
      (fun t ht => (hmeas t ht).exp.aestronglyMeasurable)
      (fun t ht => Eventually.of_forall fun x => ?_) (integrable_const _)
      (Eventually.of_forall fun x => ?_)
    · rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr (le_of_abs_le (hbd t ht x))
    · intro t ht
      exact Real.continuous_exp.continuousAt.comp_continuousWithinAt
        (hderiv t ht x).continuousWithinAt
  -- the logarithm of `Z`
  set g : ℝ → ℝ := fun t => Real.log (Z t) with hg
  have hgcont : ContinuousOn g (Icc 0 1) := hZcont.log fun t ht => (hZpos t ht).ne'
  have hgderiv : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt g (Z' t / Z t) t := fun t ht =>
    (hZderiv t ht).log (hZpos t (Ioo_subset_Icc_self ht)).ne'
  -- `|Z'/Z| ≤ M'`
  have hbdq : ∀ t ∈ Icc (0 : ℝ) 1, ‖Z' t / Z t‖ ≤ M' := by
    intro t ht
    have hle : ‖Z' t‖ ≤ M' * Z t := by
      have h := norm_integral_le_of_norm_le (μ := μ) (f := fun x => f' t x * Real.exp (f t x))
        (g := fun x => M' * Real.exp (f t x)) ((hint t ht).const_mul M')
        (Eventually.of_forall fun x => ?_)
      · simpa [Z', Z, integral_const_mul] using h
      · rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
        exact mul_le_mul_of_nonneg_right (hbd' t ht x) (Real.exp_pos _).le
    rw [norm_div, Real.norm_of_nonneg (hZpos t ht).le, div_le_iff₀ (hZpos t ht)]
    exact hle
  -- integrability of `Z'/Z` on `[0, 1]`
  have hInt : IntervalIntegrable (fun t => Z' t / Z t) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one]
    have hderiv_eq : EqOn (deriv g) (fun t => Z' t / Z t) (Ioo 0 1) := fun t ht =>
      (hgderiv t ht).deriv
    refine IntegrableOn.congr_fun ?_ hderiv_eq measurableSet_Ioo
    refine Measure.integrableOn_of_bounded (M := M') measure_Ioo_lt_top.ne
      (measurable_deriv g).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun t ht => ?_)
    rw [hderiv_eq ht]
    exact hbdq t (Ioo_subset_Icc_self ht)
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hgcont hgderiv
    hInt).symm

end CoreLean
