import PeterWeyl.Basic

/-!
# Convolution operators on a compact group

Let `G` be a compact topological group with its Borel σ-algebra, `μ` a finite measure on `G` and
`φ : C(G, ℂ)` a continuous kernel.  This file studies convolution
`(φ ⋆ f) x = ∫ φ (x * y⁻¹) * f y ∂μ(y)` as an operator on `L²(G, μ)`.

The operator is factored through continuous functions.  By `convolutionFun_eq_inner`, the value
`(φ ⋆ f) x` is the `L²` inner product of the kernel row `kernelRow φ x` with `f`, so it is a
continuous linear functional `kernelFunctional μ φ x` of `f`, and this functional depends
continuously on `x` in operator norm.  Hence `φ ⋆ f` is a continuous function, linear and bounded
in `f`, and the family `{φ ⋆ f | ‖f‖ ≤ r}` is equicontinuous.  The Arzelà–Ascoli theorem then shows
that convolution is a compact operator from `L²` to `C(G, ℂ)`, and so also from `L²` to `L²`.

## Main definitions

* `kernelFunctional μ φ x : Lp ℂ 2 μ →L[ℂ] ℂ`, the functional `f ↦ (φ ⋆ f) x`.
* `convolutionC μ φ : Lp ℂ 2 μ →L[ℂ] C(G, ℂ)`, convolution by `φ` with values in continuous
  functions.
* `convolutionOperator μ φ : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ`, the composite of `convolutionC μ φ` with
  `ContinuousMap.toLp`.

## Main statements

* `convolutionC_apply`: `convolutionC μ φ f` is the continuous representative of `φ ⋆ f`.
* `norm_convolutionC_le`: `‖convolutionC μ φ‖ ≤ ‖φ‖` for a probability measure.
* `equicontinuous_convolutionC`, `equicontinuous_convolutionC_of_isBounded`: convolutions of a
  bounded set of `L²` functions are equicontinuous.
* `isCompactOperator_convolutionC`, `isCompactOperator_convolutionOperator`: convolution by a
  continuous kernel is a compact operator.
* `convolutionC_rightTranslateL2`, `convolutionOperator_rightTranslateL2`: for a right invariant
  measure, convolution commutes with right translations.
* `adjoint_convolutionOperator`: the adjoint of convolution by `φ` is convolution by
  `adjointKernel φ`, for a weakly regular finite measure, such as a Haar measure.
* `isSelfAdjoint_convolutionOperator`: convolution by a kernel with `adjointKernel φ = φ` is
  self-adjoint.
* `exists_nhds_one_convolutionFun_sub_le`: a modulus of continuity for `φ ⋆ f` that is uniform over
  `G` and over the unit ball of `L²`.

## Implementation notes

The adjoint formula is first proved for continuous functions, where both inner products are
iterated integrals of a continuous function on `G × G`.  These are exchanged by
`MeasureTheory.integral_integral_swap_of_hasCompactSupport`, which needs neither σ-finiteness nor
second countability, and the formula extends to `L²` by density of continuous functions
(`ContinuousMap.toLp_denseRange`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal ComplexConjugate BoundedContinuousFunction

namespace PeterWeyl

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]

/-- Kernel rows have supremum norm at most `‖φ‖`. -/
theorem norm_kernelRow_le (φ : C(G, ℂ)) (x : G) : ‖kernelRow φ x‖ ≤ ‖φ‖ :=
  (ContinuousMap.norm_le _ (norm_nonneg φ)).2 fun y => by
    simpa using φ.norm_coe_le_norm (x * y⁻¹)

variable [MeasurableSpace G] [BorelSpace G] (μ : Measure G)

/-! ### Convolution as a map into continuous functions -/

section Finite

variable [IsFiniteMeasure μ]

/-- The continuous linear functional `f ↦ (φ ⋆ f) x = ⟪kernelRow φ x, f⟫` on `L²(G, μ)`. -/
def kernelFunctional (φ : C(G, ℂ)) (x : G) : Lp ℂ 2 μ →L[ℂ] ℂ :=
  innerSL ℂ (ContinuousMap.toLp 2 μ ℂ (kernelRow φ x))

theorem kernelFunctional_apply (φ : C(G, ℂ)) (x : G) (f : Lp ℂ 2 μ) :
    kernelFunctional μ φ x f = convolutionFun μ φ f x := by
  rw [convolutionFun_eq_inner]
  rfl

/-- The functional `f ↦ (φ ⋆ f) x` depends continuously on `x` in operator norm. -/
theorem continuous_kernelFunctional (φ : C(G, ℂ)) : Continuous (kernelFunctional μ φ) :=
  (innerSL ℂ).continuous.comp
    ((ContinuousMap.toLp (E := ℂ) 2 μ ℂ).continuous.comp (continuous_kernelRow φ))

theorem norm_kernelFunctional_le (φ : C(G, ℂ)) (x : G) :
    ‖kernelFunctional μ φ x‖ ≤ ‖(ContinuousMap.toLp (E := ℂ) 2 μ ℂ)‖ * ‖φ‖ := by
  rw [kernelFunctional, innerSL_apply_norm]
  exact ((ContinuousMap.toLp (E := ℂ) 2 μ ℂ).le_opNorm _).trans
    (mul_le_mul_of_nonneg_left (norm_kernelRow_le φ x) (norm_nonneg _))

/-- Convolution by `φ` as a continuous linear map from `L²(G, μ)` to `C(G, ℂ)`.  The function
`convolutionC μ φ f` is the continuous representative of `φ ⋆ f` (`convolutionC_apply`). -/
def convolutionC (φ : C(G, ℂ)) : Lp ℂ 2 μ →L[ℂ] C(G, ℂ) :=
  LinearMap.mkContinuous
    { toFun := fun f => ⟨fun x => kernelFunctional μ φ x f,
        (continuous_kernelFunctional μ φ).clm_apply continuous_const⟩
      map_add' := fun f f' => by ext x; simp
      map_smul' := fun c f => by ext x; simp }
    (‖(ContinuousMap.toLp (E := ℂ) 2 μ ℂ)‖ * ‖φ‖)
    fun f => (ContinuousMap.norm_le _ (by positivity)).2 fun x =>
      ((kernelFunctional μ φ x).le_opNorm f).trans
        (mul_le_mul_of_nonneg_right (norm_kernelFunctional_le μ φ x) (norm_nonneg f))

theorem convolutionC_apply_eq_kernelFunctional (φ : C(G, ℂ)) (f : Lp ℂ 2 μ) (x : G) :
    convolutionC μ φ f x = kernelFunctional μ φ x f :=
  rfl

/-- `convolutionC μ φ f` is the continuous representative of `φ ⋆ f`. -/
theorem convolutionC_apply (φ : C(G, ℂ)) (f : Lp ℂ 2 μ) (x : G) :
    convolutionC μ φ f x = convolutionFun μ φ f x :=
  kernelFunctional_apply μ φ x f

/-- On continuous functions, `convolutionC` is given by the convolution formula. -/
theorem convolutionC_toLp_apply (φ u : C(G, ℂ)) (x : G) :
    convolutionC μ φ (ContinuousMap.toLp 2 μ ℂ u) x = convolutionFun μ φ u x := by
  rw [convolutionC_apply, convolutionFun_congr_ae φ (ContinuousMap.coeFn_toLp μ u)]

/-- The operator norm of `convolutionC μ φ` is at most `‖ContinuousMap.toLp‖ * ‖φ‖`. -/
theorem norm_convolutionC_le_norm_toLp_mul (φ : C(G, ℂ)) :
    ‖convolutionC μ φ‖ ≤ ‖(ContinuousMap.toLp (E := ℂ) 2 μ ℂ)‖ * ‖φ‖ :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _

/-- The oscillation of `φ ⋆ f` between two points is controlled by the distance of the kernel
functionals. -/
theorem norm_convolutionC_apply_sub_le (φ : C(G, ℂ)) (f : Lp ℂ 2 μ) (x x' : G) :
    ‖convolutionC μ φ f x - convolutionC μ φ f x'‖ ≤
      ‖kernelFunctional μ φ x - kernelFunctional μ φ x'‖ * ‖f‖ :=
  (kernelFunctional μ φ x - kernelFunctional μ φ x').le_opNorm f

/-- Convolutions of a bounded set of `L²` functions form an equicontinuous family. -/
theorem equicontinuous_convolutionC_of_isBounded (φ : C(G, ℂ)) {s : Set (Lp ℂ 2 μ)}
    (hs : Bornology.IsBounded s) : Equicontinuous fun f : s => ⇑(convolutionC μ φ f) := by
  obtain ⟨r, hr⟩ := isBounded_iff_forall_norm_le.1 hs
  intro x₀
  refine Metric.equicontinuousAt_of_continuity_modulus
    (fun x => ‖kernelFunctional μ φ x₀ - kernelFunctional μ φ x‖ * r) ?_ _
    (Eventually.of_forall fun x f => ?_)
  · have h : Tendsto (fun x => ‖kernelFunctional μ φ x₀ - kernelFunctional μ φ x‖ * r) (𝓝 x₀)
        (𝓝 (‖kernelFunctional μ φ x₀ - kernelFunctional μ φ x₀‖ * r)) :=
      (tendsto_const_nhds.sub ((continuous_kernelFunctional μ φ).tendsto x₀)).norm.mul_const r
    simpa using h
  · rw [dist_eq_norm]
    exact (norm_convolutionC_apply_sub_le μ φ f x₀ x).trans
      (mul_le_mul_of_nonneg_left (hr f f.2) (norm_nonneg _))

/-- Convolutions of the unit ball of `L²` form an equicontinuous family, in the form consumed by
the Arzelà–Ascoli theorem. -/
theorem equicontinuous_convolutionC (φ : C(G, ℂ)) :
    Equicontinuous fun f : Metric.closedBall (0 : Lp ℂ 2 μ) 1 => convolutionFun μ φ f := by
  have hfun : (fun f : Metric.closedBall (0 : Lp ℂ 2 μ) 1 => convolutionFun μ φ f) =
      fun f : Metric.closedBall (0 : Lp ℂ 2 μ) 1 => ⇑(convolutionC μ φ f) := by
    funext f x
    exact (convolutionC_apply μ φ f x).symm
  rw [hfun]
  exact equicontinuous_convolutionC_of_isBounded μ φ Metric.isBounded_closedBall

/-- The distance of two kernel functionals is controlled by the distance of the kernel rows. -/
theorem norm_kernelFunctional_sub_le (φ : C(G, ℂ)) (x x' : G) :
    ‖kernelFunctional μ φ x' - kernelFunctional μ φ x‖ ≤
      ‖(ContinuousMap.toLp (E := ℂ) 2 μ ℂ)‖ * ‖kernelRow φ x' - kernelRow φ x‖ := by
  rw [kernelFunctional, kernelFunctional, ← map_sub, ← map_sub, innerSL_apply_norm]
  exact (ContinuousMap.toLp (E := ℂ) 2 μ ℂ).le_opNorm _

/-- A modulus of continuity for `φ ⋆ f` that is uniform over `G` and over the unit ball of `L²`:
`|(φ ⋆ f) x' - (φ ⋆ f) x| ≤ ε` whenever `x' * x⁻¹` is close to `1` and `‖f‖ ≤ 1`. -/
theorem exists_nhds_one_convolutionFun_sub_le (φ : C(G, ℂ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ U ∈ 𝓝 (1 : G), ∀ x x' : G, x' * x⁻¹ ∈ U → ∀ f : Lp ℂ 2 μ, ‖f‖ ≤ 1 →
      ‖convolutionFun μ φ f x' - convolutionFun μ φ f x‖ ≤ ε := by
  let L : C(G, C(G, ℂ)) := (ContinuousMap.mk (fun p : G × G => φ (p.1 * p.2)) (by fun_prop)).curry
  have hL1 : L 1 = φ := by
    ext z
    simp [L]
  have hL : Tendsto (fun u => ‖(ContinuousMap.toLp (E := ℂ) 2 μ ℂ)‖ * ‖L u - φ‖) (𝓝 1)
      (𝓝 (‖(ContinuousMap.toLp (E := ℂ) 2 μ ℂ)‖ * ‖L 1 - φ‖)) :=
    ((L.continuous.tendsto 1).sub_const φ).norm.const_mul _
  rw [hL1, sub_self, norm_zero, mul_zero] at hL
  refine ⟨_, hL (Iio_mem_nhds hε), fun x x' hxx' f hf => ?_⟩
  have hrow : ‖kernelRow φ x' - kernelRow φ x‖ ≤ ‖L (x' * x⁻¹) - φ‖ := by
    refine (ContinuousMap.norm_le _ (norm_nonneg _)).2 fun y => ?_
    have h := (L (x' * x⁻¹) - φ).norm_coe_le_norm (x * y⁻¹)
    simp only [ContinuousMap.sub_apply, kernelRow_apply, ← map_sub, Complex.norm_conj]
    simpa [L, mul_assoc] using h
  rw [← convolutionC_apply, ← convolutionC_apply]
  calc ‖convolutionC μ φ f x' - convolutionC μ φ f x‖
      ≤ ‖kernelFunctional μ φ x' - kernelFunctional μ φ x‖ * ‖f‖ :=
        norm_convolutionC_apply_sub_le μ φ f x' x
    _ ≤ ‖kernelFunctional μ φ x' - kernelFunctional μ φ x‖ :=
        mul_le_of_le_one_right (norm_nonneg _) hf
    _ ≤ ‖(ContinuousMap.toLp (E := ℂ) 2 μ ℂ)‖ * ‖kernelRow φ x' - kernelRow φ x‖ :=
        norm_kernelFunctional_sub_le μ φ x x'
    _ ≤ ‖(ContinuousMap.toLp (E := ℂ) 2 μ ℂ)‖ * ‖L (x' * x⁻¹) - φ‖ :=
        mul_le_mul_of_nonneg_left hrow (norm_nonneg _)
    _ ≤ ε := le_of_lt hxx'

/-- **Compactness of convolution.**  Convolution by a continuous kernel is a compact operator from
`L²(G, μ)` to `C(G, ℂ)`, by the Arzelà–Ascoli theorem. -/
theorem isCompactOperator_convolutionC (φ : C(G, ℂ)) : IsCompactOperator (convolutionC μ φ) := by
  set S := convolutionC μ φ
  let e := ContinuousMap.linearIsometryBoundedOfCompact G ℂ ℂ
  let A : Set (G →ᵇ ℂ) := e '' (S '' Metric.closedBall 0 1)
  have hA : IsCompact (closure A) := by
    refine BoundedContinuousFunction.arzela_ascoli (Metric.closedBall 0 ‖S‖)
      (isCompact_closedBall 0 ‖S‖) A ?_ ?_
    · rintro _ x ⟨_, ⟨f, hf, rfl⟩, rfl⟩
      rw [Metric.mem_closedBall, dist_zero_right,
        ContinuousMap.linearIsometryBoundedOfCompact_apply_apply]
      calc ‖S f x‖ ≤ ‖S f‖ := (S f).norm_coe_le_norm x
        _ ≤ ‖S‖ * ‖f‖ := S.le_opNorm f
        _ ≤ ‖S‖ := mul_le_of_le_one_right (norm_nonneg _) (by simpa using hf)
    · intro x₀ U hU
      filter_upwards [equicontinuous_convolutionC_of_isBounded μ φ
        (Metric.isBounded_closedBall (x := 0) (r := 1)) x₀ U hU] with x hx
      rintro ⟨_, _, ⟨f, hf, rfl⟩, rfl⟩
      exact hx ⟨f, hf⟩
  have h := (isCompactOperator_iff_image_closedBall_subset_compact
    (S : Lp ℂ 2 μ →ₗ[ℂ] C(G, ℂ)) one_pos).2
    ⟨e.symm '' closure A, hA.image e.symm.continuous, by
      rintro _ ⟨f, hf, rfl⟩
      exact ⟨e (S f), subset_closure ⟨S f, ⟨f, hf, rfl⟩, rfl⟩, e.symm_apply_apply _⟩⟩
  exact h

/-! ### Convolution as an operator on `L²` -/

/-- Convolution by `φ` as a bounded operator on `L²(G, μ)`: the composite of `convolutionC μ φ`
with the inclusion `ContinuousMap.toLp` of continuous functions. -/
def convolutionOperator (φ : C(G, ℂ)) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (ContinuousMap.toLp 2 μ ℂ).comp (convolutionC μ φ)

theorem convolutionOperator_apply (φ : C(G, ℂ)) (f : Lp ℂ 2 μ) :
    convolutionOperator μ φ f = ContinuousMap.toLp 2 μ ℂ (convolutionC μ φ f) :=
  rfl

/-- `convolutionOperator μ φ f` is represented by the convolution formula. -/
theorem coeFn_convolutionOperator (φ : C(G, ℂ)) (f : Lp ℂ 2 μ) :
    convolutionOperator μ φ f =ᵐ[μ] convolutionFun μ φ f := by
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) μ (convolutionC μ φ f)] with x hx
  rw [convolutionOperator_apply, hx, convolutionC_apply]

/-- Convolution by a continuous kernel is a compact operator on `L²(G, μ)`. -/
theorem isCompactOperator_convolutionOperator (φ : C(G, ℂ)) :
    IsCompactOperator (convolutionOperator μ φ) :=
  (isCompactOperator_convolutionC μ φ).continuous_comp (ContinuousMap.toLp 2 μ ℂ).continuous

/-! ### Right translations -/

section RightInvariant

variable [μ.IsMulRightInvariant]

/-- Convolution commutes with right translations: `φ ⋆ R_g f = R_g (φ ⋆ f)`. -/
theorem convolutionC_rightTranslateL2 (φ : C(G, ℂ)) (g : G) (f : Lp ℂ 2 μ) :
    convolutionC μ φ (rightTranslateL2 μ g f) = rightTranslate g (convolutionC μ φ f) := by
  ext x
  rw [convolutionC_apply, rightTranslate_apply, convolutionC_apply,
    convolutionFun_congr_ae φ (coeFn_rightTranslateL2 μ g f)]
  refine Eq.trans ?_ (integral_mul_right_eq_self (fun y => φ (x * g * y⁻¹) * f y) g)
  simp only [convolutionFun, mul_inv_rev, mul_assoc, mul_inv_cancel_left]

/-- Convolution commutes with right translations on `L²`. -/
theorem convolutionOperator_rightTranslateL2 (φ : C(G, ℂ)) (g : G) (f : Lp ℂ 2 μ) :
    convolutionOperator μ φ (rightTranslateL2 μ g f) =
      rightTranslateL2 μ g (convolutionOperator μ φ f) := by
  rw [convolutionOperator_apply, convolutionOperator_apply, convolutionC_rightTranslateL2,
    rightTranslateL2_toLp]

end RightInvariant

/-! ### The adjoint -/

/-- The adjoint formula on continuous functions. -/
theorem inner_convolutionOperator_adjointKernel_toLp (φ f h : C(G, ℂ)) :
    ⟪convolutionOperator μ (adjointKernel φ) (ContinuousMap.toLp 2 μ ℂ f),
        ContinuousMap.toLp 2 μ ℂ h⟫_ℂ =
      ⟪ContinuousMap.toLp 2 μ ℂ f, convolutionOperator μ φ (ContinuousMap.toLp 2 μ ℂ h)⟫_ℂ := by
  rw [convolutionOperator_apply, convolutionOperator_apply, ContinuousMap.inner_toLp,
    ContinuousMap.inner_toLp]
  simp only [convolutionC_toLp_apply, convolutionFun, adjointKernel_apply]
  have hF : Continuous (Function.uncurry fun x y : G => h x * (φ (y * x⁻¹) * conj (f y))) :=
    (h.continuous.comp continuous_fst).mul ((φ.continuous.comp
      (continuous_snd.mul continuous_fst.inv)).mul
        (Complex.continuous_conj.comp (f.continuous.comp continuous_snd)))
  calc ∫ x, h x * conj (∫ y, conj (φ (x * y⁻¹)⁻¹) * f y ∂μ) ∂μ -- totalisation-audit: allow integrands continuous on the compact group G
      = ∫ x, ∫ y, h x * (φ (y * x⁻¹) * conj (f y)) ∂μ ∂μ := by -- totalisation-audit: allow integrands continuous on the compact group G
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        dsimp only
        rw [← integral_conj, ← integral_const_mul]
        refine integral_congr_ae (ae_of_all _ fun y => ?_)
        simp
    _ = ∫ y, ∫ x, h x * (φ (y * x⁻¹) * conj (f y)) ∂μ ∂μ := -- totalisation-audit: allow integrand continuous on the compact space G × G
        integral_integral_swap_of_hasCompactSupport hF (HasCompactSupport.of_compactSpace _)
    _ = ∫ y, (∫ x, φ (y * x⁻¹) * h x ∂μ) * conj (f y) ∂μ := by -- totalisation-audit: allow integrands continuous on the compact group G
        refine integral_congr_ae (ae_of_all _ fun y => ?_)
        dsimp only
        rw [← integral_mul_const]
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        simp only
        ring

section WeaklyRegular

variable [μ.WeaklyRegular]

/-- **Adjoint of convolution.**  The adjoint of convolution by `φ` on `L²(G, μ)` is convolution by
`adjointKernel φ`, `φ* g = conj (φ g⁻¹)`. -/
theorem adjoint_convolutionOperator (φ : C(G, ℂ)) :
    ContinuousLinearMap.adjoint (convolutionOperator μ φ) =
      convolutionOperator μ (adjointKernel φ) := by
  refine ((ContinuousLinearMap.eq_adjoint_iff _ _).2 fun f h => ?_).symm
  have hd : DenseRange (ContinuousMap.toLp (E := ℂ) 2 μ ℂ) :=
    ContinuousMap.toLp_denseRange ℂ μ ℂ (by simp)
  refine hd.induction_on₂ (p := fun f h => ⟪convolutionOperator μ (adjointKernel φ) f, h⟫_ℂ =
    ⟪f, convolutionOperator μ φ h⟫_ℂ) ?_ (inner_convolutionOperator_adjointKernel_toLp μ φ) f h
  exact isClosed_eq
    (((convolutionOperator μ (adjointKernel φ)).continuous.comp continuous_fst).inner
      continuous_snd)
    (continuous_fst.inner ((convolutionOperator μ φ).continuous.comp continuous_snd))

/-- Convolution by a kernel with `adjointKernel φ = φ` is self-adjoint on `L²(G, μ)`. -/
theorem isSelfAdjoint_convolutionOperator {φ : C(G, ℂ)} (hφ : adjointKernel φ = φ) :
    IsSelfAdjoint (convolutionOperator μ φ) := by
  rw [IsSelfAdjoint, ContinuousLinearMap.star_eq_adjoint, adjoint_convolutionOperator, hφ]

end WeaklyRegular

end Finite

/-! ### Probability measures -/

section Probability

variable [IsProbabilityMeasure μ]

omit [Group G] [IsTopologicalGroup G] in
/-- For a probability measure, the inclusion of continuous functions into `L²` does not increase
norms. -/
theorem norm_toLp_le_one : ‖(ContinuousMap.toLp (E := ℂ) 2 μ ℂ)‖ ≤ 1 :=
  (ContinuousMap.toLp_norm_le μ).trans (by simp [measureUnivNNReal])

/-- For a probability measure, `‖φ ⋆ f‖∞ ≤ ‖φ‖ * ‖f‖₂`. -/
theorem norm_convolutionC_le (φ : C(G, ℂ)) : ‖convolutionC μ φ‖ ≤ ‖φ‖ :=
  (norm_convolutionC_le_norm_toLp_mul μ φ).trans
    (mul_le_of_le_one_left (norm_nonneg φ) (norm_toLp_le_one μ))

/-- For a probability measure, `|(φ ⋆ f) x| ≤ ‖φ‖ * ‖f‖₂` at every point. -/
theorem norm_convolutionC_apply_le (φ : C(G, ℂ)) (f : Lp ℂ 2 μ) (x : G) :
    ‖convolutionC μ φ f x‖ ≤ ‖φ‖ * ‖f‖ :=
  ((convolutionC μ φ f).norm_coe_le_norm x).trans (((convolutionC μ φ).le_opNorm f).trans
    (mul_le_mul_of_nonneg_right (norm_convolutionC_le μ φ) (norm_nonneg f)))

end Probability

end PeterWeyl
