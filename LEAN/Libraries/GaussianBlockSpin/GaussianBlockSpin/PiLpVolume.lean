import Mathlib

/-! The volume of a nested `PiLp` space of Euclidean fibres is the coordinate Lebesgue measure: the map
`(ι → κ → ℝ) → PiLp 2 (ι → EuclideanSpace ℝ κ)` is volume preserving. Used to identify the configuration space of
`ℝ^d`-valued lattice fields (functions) with the inner product space of the Gaussian algebra. -/

namespace GaussianBlockSpin

open MeasureTheory Set

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Flattening `PiLp 2 (ι → EuclideanSpace ℝ κ) ≃ₗᵢ EuclideanSpace ℝ (ι × κ)`. -/
noncomputable def flattenIsometry : PiLp 2 (fun _ : ι => EuclideanSpace ℝ κ) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (ι × κ) where
  toFun f := WithLp.toLp 2 fun p => f p.1 p.2
  invFun g := WithLp.toLp 2 fun i => WithLp.toLp 2 fun k => g (i, k)
  map_add' f g := by
    ext p
    simp
  map_smul' c f := by
    ext p
    simp
  left_inv f := rfl
  right_inv g := rfl
  norm_map' f := by
    rw [EuclideanSpace.norm_eq, PiLp.norm_eq_of_L2]
    congr 1
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun k _ => sq_nonneg _)]
    rfl

/-- Currying `(ι × κ → ℝ) → (ι → κ → ℝ)` preserves the coordinate Lebesgue measures. -/
theorem measurePreserving_curry_volume :
    MeasurePreserving (MeasurableEquiv.curry ι κ ℝ) (volume : Measure (ι × κ → ℝ)) volume where
  measurable := (MeasurableEquiv.curry ι κ ℝ).measurable
  map_eq := by
    rw [volume_pi, volume_pi]
    refine (Measure.pi_eq_generateFrom (C := fun _ => pi univ '' pi univ fun _ => {s : Set ℝ | MeasurableSet s})
      (fun _ => generateFrom_pi) (fun _ => isPiSystem_pi)
      (fun _ => Measure.FiniteSpanningSetsIn.pi fun _ => (volume : Measure ℝ).toFiniteSpanningSetsIn) ?_).symm
    intro s hs
    choose t ht hts using hs
    have hpre : (MeasurableEquiv.curry ι κ ℝ) ⁻¹' pi univ s = pi univ fun p : ι × κ => t p.1 p.2 := by
      ext f
      simp only [mem_preimage, mem_pi, mem_univ, forall_const, ← hts, MeasurableEquiv.curry,
        MeasurableEquiv.coe_mk, Prod.forall]
      rfl
    rw [Measure.map_apply (MeasurableEquiv.curry ι κ ℝ).measurable
      (MeasurableSet.univ_pi fun i => hts i ▸ MeasurableSet.univ_pi fun k => ht i k (mem_univ k)), hpre, Measure.pi_pi,
      Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← hts i, Measure.pi_pi]

/-- **The coordinate Lebesgue measure of nested Euclidean fibres**: `f ↦ (i ↦ (k ↦ f i k))` from `ι → κ → ℝ` to
`PiLp 2 (ι → EuclideanSpace ℝ κ)` is volume preserving. -/
theorem measurePreserving_toPiLpEuclidean :
    MeasurePreserving (fun f : ι → κ → ℝ => (WithLp.toLp 2 fun i => WithLp.toLp 2 (f i) :
      PiLp 2 (fun _ : ι => EuclideanSpace ℝ κ))) volume volume := by
  have h := ((LinearIsometryEquiv.measurePreserving (flattenIsometry (ι := ι) (κ := κ)).symm).comp
    (PiLp.volume_preserving_toLp (ι × κ))).comp (measurePreserving_curry_volume (ι := ι) (κ := κ)).symm
  exact h

open scoped RealInnerProductSpace

omit [Fintype ι] in
/-- The box `{f | ∀ i, ‖f i‖ ≤ r}` of a field space is closed. -/
lemma isClosed_box (r : ℝ) : IsClosed {f : PiLp 2 (fun _ : ι => EuclideanSpace ℝ κ) | ∀ i, ‖f i‖ ≤ r} := by
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun i => isClosed_le
    ((PiLp.continuous_apply 2 (fun _ : ι => EuclideanSpace ℝ κ) i).norm) continuous_const

/-- The box `{f | ∀ i, ‖f i‖ ≤ r}` contains the cube of half-side `r / √(#κ)`, so its volume is at least
`(2 r / √(#κ))^{#ι #κ}`. -/
theorem volume_box_ge {r : ℝ} (hr : 0 ≤ r) :
    ENNReal.ofReal ((2 * r / Real.sqrt (Fintype.card κ)) ^ (Fintype.card ι * Fintype.card κ)) ≤  -- totalisation-audit: allow numeral denominator 2; division by √(#κ) only when #κ > 0 matters (for #κ = 0 the power has exponent 0)
      volume {f : PiLp 2 (fun _ : ι => EuclideanSpace ℝ κ) | ∀ i, ‖f i‖ ≤ r} := by
  set s := r / Real.sqrt (Fintype.card κ) with hs  -- totalisation-audit: allow numeral denominator 2; division by √(#κ) only when #κ > 0 matters (for #κ = 0 the power has exponent 0)
  have hs0 : 0 ≤ s := div_nonneg hr (Real.sqrt_nonneg _)
  have hcube : (Set.pi Set.univ fun _ : ι => Set.pi Set.univ fun _ : κ => Set.Icc (-s) s) ⊆
      (fun f : ι → κ → ℝ => (WithLp.toLp 2 fun i => WithLp.toLp 2 (f i) :
        PiLp 2 (fun _ : ι => EuclideanSpace ℝ κ))) ⁻¹' {f | ∀ i, ‖f i‖ ≤ r} := by
    intro f hf i
    have hfi : ∀ k, |f i k| ≤ s := fun k => abs_le.mpr (hf i (Set.mem_univ i) k (Set.mem_univ k))
    show ‖(WithLp.toLp 2 (f i) : EuclideanSpace ℝ κ)‖ ≤ r
    rw [EuclideanSpace.norm_eq]
    by_cases hκ : Fintype.card κ = 0
    · have : IsEmpty κ := Fintype.card_eq_zero_iff.mp hκ
      simp [hr]
    · have hκ0 : (0 : ℝ) < Fintype.card κ := by exact_mod_cast Nat.pos_of_ne_zero hκ
      calc Real.sqrt (∑ k, ‖(WithLp.toLp 2 (f i) : EuclideanSpace ℝ κ) k‖ ^ 2)
          ≤ Real.sqrt (∑ _k : κ, s ^ 2) := by
            refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun k _ => ?_)
            rw [Real.norm_eq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) (hfi k) 2
        _ = r := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hs, div_pow,
              Real.sq_sqrt hκ0.le, mul_div_cancel₀ _ hκ0.ne', Real.sqrt_sq hr]
  have hmeas := (isClosed_box (ι := ι) (κ := κ) r).measurableSet
  rw [← (measurePreserving_toPiLpEuclidean (ι := ι) (κ := κ)).measure_preimage hmeas.nullMeasurableSet]
  refine le_trans (le_of_eq ?_) (measure_mono hcube)
  rw [volume_pi_pi]
  simp_rw [volume_pi_pi, Real.volume_Icc, Finset.prod_const, Finset.card_univ]
  rw [show s - -s = 2 * s by ring, ← ENNReal.ofReal_pow (by linarith), ← ENNReal.ofReal_pow (pow_nonneg (by linarith) _),
    ← pow_mul, mul_comm (Fintype.card κ), hs, mul_div_assoc]

/-- **A Gaussian on a box**: if `⟨x, H x⟩ ≤ c ‖x‖²`, `c ≥ 0`, then
`∫_{‖x_i‖ ≤ r ∀ i} exp(-½ ⟨x, H x⟩) dx ≥ (2 r / √(#κ))^{#ι #κ} exp(-½ c #ι r²)`. -/
theorem lintegral_box_gaussian_ge {H : PiLp 2 (fun _ : ι => EuclideanSpace ℝ κ) →ₗ[ℝ]
    PiLp 2 (fun _ : ι => EuclideanSpace ℝ κ)} {c r : ℝ} (hc : 0 ≤ c) (hr : 0 ≤ r)
    (hH : ∀ x, ⟪x, H x⟫ ≤ c * ‖x‖ ^ 2) :
    ENNReal.ofReal ((2 * r / Real.sqrt (Fintype.card κ)) ^ (Fintype.card ι * Fintype.card κ) *  -- totalisation-audit: allow numeral denominator 2; division by √(#κ) only when #κ > 0 matters (for #κ = 0 the power has exponent 0)
        Real.exp (-(1 / 2) * (c * (Fintype.card ι * r ^ 2)))) ≤  -- totalisation-audit: allow numeral denominator 2; division by √(#κ) only when #κ > 0 matters (for #κ = 0 the power has exponent 0)
      ∫⁻ x, {f : PiLp 2 (fun _ : ι => EuclideanSpace ℝ κ) | ∀ i, ‖f i‖ ≤ r}.indicator 1 x *
        ENNReal.ofReal (Real.exp (-(1 / 2) * ⟪x, H x⟫)) := by  -- totalisation-audit: allow numeral denominator 2; division by √(#κ) only when #κ > 0 matters (for #κ = 0 the power has exponent 0)
  set S := {f : PiLp 2 (fun _ : ι => EuclideanSpace ℝ κ) | ∀ i, ‖f i‖ ≤ r}
  have hmeas : MeasurableSet S := (isClosed_box r).measurableSet
  have hpt : ∀ x, S.indicator (fun _ => ENNReal.ofReal (Real.exp (-(1 / 2) * (c * (Fintype.card ι * r ^ 2))))) x ≤  -- totalisation-audit: allow numeral denominator 2; division by √(#κ) only when #κ > 0 matters (for #κ = 0 the power has exponent 0)
      S.indicator 1 x * ENNReal.ofReal (Real.exp (-(1 / 2) * ⟪x, H x⟫)) := by  -- totalisation-audit: allow numeral denominator 2; division by √(#κ) only when #κ > 0 matters (for #κ = 0 the power has exponent 0)
    intro x
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, Pi.one_apply, one_mul]
      refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
      have hn : ‖x‖ ^ 2 ≤ Fintype.card ι * r ^ 2 := by
        rw [PiLp.norm_sq_eq_of_L2]
        calc ∑ i, ‖x i‖ ^ 2 ≤ ∑ _i : ι, r ^ 2 :=
              Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hx i) 2
          _ = Fintype.card ι * r ^ 2 := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      nlinarith [hH x, mul_le_mul_of_nonneg_left hn hc]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_mul]
  calc ENNReal.ofReal ((2 * r / Real.sqrt (Fintype.card κ)) ^ (Fintype.card ι * Fintype.card κ) *  -- totalisation-audit: allow numeral denominator 2; division by √(#κ) only when #κ > 0 matters (for #κ = 0 the power has exponent 0)
          Real.exp (-(1 / 2) * (c * (Fintype.card ι * r ^ 2))))  -- totalisation-audit: allow numeral denominator 2; division by √(#κ) only when #κ > 0 matters (for #κ = 0 the power has exponent 0)
      ≤ ENNReal.ofReal (Real.exp (-(1 / 2) * (c * (Fintype.card ι * r ^ 2)))) * volume S := by  -- totalisation-audit: allow numeral denominator 2; division by √(#κ) only when #κ > 0 matters (for #κ = 0 the power has exponent 0)
        rw [ENNReal.ofReal_mul (by positivity), mul_comm]
        gcongr
        exact volume_box_ge hr
    _ = ∫⁻ x, S.indicator (fun _ => ENNReal.ofReal (Real.exp (-(1 / 2) * (c * (Fintype.card ι * r ^ 2))))) x := by  -- totalisation-audit: allow numeral denominator 2; division by √(#κ) only when #κ > 0 matters (for #κ = 0 the power has exponent 0)
        rw [lintegral_indicator_const hmeas]
    _ ≤ _ := lintegral_mono hpt

end GaussianBlockSpin
