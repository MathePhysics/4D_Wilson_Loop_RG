import SpectralTheorem.SpectralMeasure

/-!
# Spectral measures of a representation of `C(X)`

Let `X` be a compact Hausdorff space and `π : C(X, ℂ) → 𝓛(H)` a unital `⋆`-representation of
`C(X, ℂ)` on a complex Hilbert space `H`, i.e. a unital `⋆`-algebra homomorphism.  For `ψ ∈ H`
the map `f ↦ ⟪ψ, π(f) ψ⟫` is a positive linear functional on `C(X, ℂ)`, so by the
Riesz–Markov–Kakutani theorem there is a unique regular Borel measure `μ_ψ` on `X` with
`⟪ψ, π(f) ψ⟫ = ∫ f dμ_ψ`.  This is the construction of Reed–Simon I, §VII.2, pp. 224–225 ("the
spectral measure associated with the vector `ψ`"), where `π` is the continuous functional
calculus of a self-adjoint operator, carried out for an arbitrary representation, as in the
spectral theorem for commutative C⋆-algebras of operators (Rudin, *Functional Analysis*,
Chapter 12).

Proof sketch: the functional `f ↦ re ⟪ψ, π(f) ψ⟫` on `C(X, ℝ)` is linear; it is positive because
a real `f ≥ 0` is `g²` with `g = √f`, and `⟪ψ, π(g)† π(g) ψ⟫ = ‖π(g) ψ‖²`.  Riesz–Markov–Kakutani
(`RealRMK.rieszMeasure`) gives `μ_ψ`; the complex identity follows by splitting `f` into real and
imaginary parts.  The proofs are those of `SpectralTheorem.SpectralMeasure`, with `X` and `π` in
place of `σ(T)` and `cfcHom`.  `X` is not assumed metrizable.

Every Bochner integral in this file is of a continuous function on the compact space `X` against
a finite measure, hence of an integrable function (`integrable_repMeasure`); the lines carry the
totalisation-audit marker "continuous" for this reason.

## Main definitions and results

* `SpectralTheorem.repFunctional π ψ`: the positive linear functional `f ↦ re ⟪ψ, π(f) ψ⟫` on
  `C_c(X, ℝ) = C(X, ℝ)`.
* `SpectralTheorem.repMeasure π ψ`: the spectral measure `μ_ψ`, a finite regular Borel measure
  on `X`.
* `SpectralTheorem.integral_repMeasure`: `∫ f dμ_ψ = ⟪ψ, π(f) ψ⟫` for `f ∈ C(X, ℂ)`.
* `SpectralTheorem.integral_norm_sq_repMeasure`: `∫ |g|² dμ_ψ = ‖π(g) ψ‖²`.
* `SpectralTheorem.repMeasure_univ`: `μ_ψ(X) = ‖ψ‖²`.
* `SpectralTheorem.eq_repMeasure`: uniqueness of `μ_ψ` among regular measures.
-/

noncomputable section

open scoped InnerProductSpace ComplexConjugate CompactlySupported
open MeasureTheory

namespace SpectralTheorem

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {X : Type u} [TopologicalSpace X]
variable (π : C(X, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H))

/-- `⟪ψ, π(g)* π(g) ψ⟫ = ‖π(g) ψ‖²`, the identity behind positivity of the functional. -/
theorem inner_rep_star_mul_self (g : C(X, ℂ)) (ψ : H) :
    ⟪ψ, π (star g * g) ψ⟫_ℂ = (‖π g ψ‖ ^ 2 : ℝ) := by
  rw [map_mul, map_star, ContinuousLinearMap.star_eq_adjoint,
    mul_apply_eq_comp, ContinuousLinearMap.adjoint_inner_right,
    inner_self_eq_norm_sq_to_K]
  norm_cast

/-- For a real continuous `f`, the operator `π(f)` is self-adjoint, so `⟪ψ, π(f) ψ⟫` is real. -/
theorem inner_rep_ofRealCM (f : C(X, ℝ)) (ψ : H) :
    ⟪ψ, π (ofRealCM f) ψ⟫_ℂ = (RCLike.re ⟪ψ, π (ofRealCM f) ψ⟫_ℂ : ℂ) := by
  have hsa : IsSelfAdjoint (π (ofRealCM f)) := by
    rw [IsSelfAdjoint, ← map_star, star_ofRealCM]
  refine (RCLike.conj_eq_iff_re.mp ?_).symm
  rw [inner_conj_symm, ← ContinuousLinearMap.adjoint_inner_left,
    ← ContinuousLinearMap.star_eq_adjoint, hsa.star_eq]

/-- For a nonnegative real continuous `f`, `re ⟪ψ, π(f) ψ⟫ ≥ 0`: write `f = g²` with
`g = √f`, so that `⟪ψ, π(f) ψ⟫ = ‖π(g) ψ‖²`. -/
theorem re_inner_rep_ofRealCM_nonneg (f : C(X, ℝ)) (hf : 0 ≤ f) (ψ : H) :
    0 ≤ RCLike.re ⟪ψ, π (ofRealCM f) ψ⟫_ℂ := by
  let g : C(X, ℂ) := ofRealCM ⟨fun x => Real.sqrt (f x), by fun_prop⟩
  have hg : star g * g = ofRealCM f := by
    ext x
    simp only [g, ContinuousMap.mul_apply, ContinuousMap.star_apply, ofRealCM_apply,
      ContinuousMap.coe_mk, RCLike.star_def, Complex.conj_ofReal]
    rw [← Complex.ofReal_mul]
    congr 1
    exact Real.mul_self_sqrt (hf x)
  rw [← hg, inner_rep_star_mul_self, RCLike.re_to_complex, Complex.ofReal_re]
  positivity

/-- The real-linear functional `f ↦ re ⟪ψ, π(f) ψ⟫` on `C(X, ℝ)`. -/
def repLinear (ψ : H) : C(X, ℝ) →ₗ[ℝ] ℝ where
  toFun f := RCLike.re ⟪ψ, π (ofRealCM f) ψ⟫_ℂ
  map_add' f g := by
    rw [ofRealCM_add, map_add, add_apply, inner_add_right, map_add]
  map_smul' c f := by
    rw [ofRealCM_smul, map_smul, FunLike.coe_smul, Pi.smul_apply, inner_smul_right,
      RingHom.id_apply, smul_eq_mul, RCLike.re_to_complex, RCLike.re_to_complex,
      Complex.re_ofReal_mul]

/-- `repLinear π ψ f = re ⟪ψ, π(f) ψ⟫`. -/
theorem repLinear_apply (ψ : H) (f : C(X, ℝ)) :
    repLinear π ψ f = RCLike.re ⟪ψ, π (ofRealCM f) ψ⟫_ℂ :=
  rfl

/-- **The spectral functional** of `ψ` for `π`: `f ↦ re ⟪ψ, π(f) ψ⟫`, a positive linear
functional on `C_c(X, ℝ)`, which is `C(X, ℝ)` since `X` is compact. -/
def repFunctional (ψ : H) : C_c(X, ℝ) →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀
    { toFun := fun f => repLinear π ψ f.toContinuousMap
      map_add' := fun f g => (repLinear π ψ).map_add f.toContinuousMap g.toContinuousMap
      map_smul' := fun c f => (repLinear π ψ).map_smul c f.toContinuousMap }
    fun f hf => re_inner_rep_ofRealCM_nonneg π f.toContinuousMap (fun x => hf x) ψ

variable [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]

/-- **The spectral measure** `μ_ψ` of `ψ` for the representation `π` (Reed–Simon I, §VII.2,
p. 225, for a general representation): the regular Borel measure on `X` given by the
Riesz–Markov–Kakutani theorem for the spectral functional. -/
def repMeasure (ψ : H) : Measure X :=
  RealRMK.rieszMeasure (repFunctional π ψ)

instance (ψ : H) : (repMeasure π ψ).Regular :=
  RealRMK.regular_rieszMeasure _

instance (ψ : H) : IsFiniteMeasure (repMeasure π ψ) :=
  CompactSpace.isFiniteMeasure

/-- Continuous functions on `X` are integrable for the spectral measure. -/
theorem integrable_repMeasure {E : Type*} [NormedAddCommGroup E] (ψ : H) (f : C(X, E)) :
    Integrable f (repMeasure π ψ) :=
  f.continuous.integrable_of_hasCompactSupport
    (IsCompact.of_isClosed_subset isCompact_univ (isClosed_tsupport _) (Set.subset_univ _))

/-- `∫ f dμ_ψ = re ⟪ψ, π(f) ψ⟫` for a real continuous `f`. -/
theorem integral_repMeasure_real (ψ : H) (f : C(X, ℝ)) :
    ∫ x, f x ∂(repMeasure π ψ) = -- totalisation-audit: allow continuous
      RCLike.re ⟪ψ, π (ofRealCM f) ψ⟫_ℂ :=
  RealRMK.integral_rieszMeasure (repFunctional π ψ)
    (CompactlySupportedContinuousMap.continuousMapEquiv f)

/-- `⟪ψ, π(f) ψ⟫ = ∫ f dμ_ψ` for a real continuous `f`. -/
theorem inner_rep_ofRealCM_eq_integral (ψ : H) (f : C(X, ℝ)) :
    ⟪ψ, π (ofRealCM f) ψ⟫_ℂ =
      ((∫ x, f x ∂(repMeasure π ψ) -- totalisation-audit: allow continuous
        : ℝ) : ℂ) := by
  rw [integral_repMeasure_real, inner_rep_ofRealCM]
  rfl

/-- **The defining property of the spectral measure**: `∫ f dμ_ψ = ⟪ψ, π(f) ψ⟫` for every
continuous `f : X → ℂ` (Reed–Simon I, §VII.2, p. 224, for a general representation). -/
theorem integral_repMeasure (ψ : H) (f : C(X, ℂ)) :
    ∫ x, f x ∂(repMeasure π ψ) = -- totalisation-audit: allow continuous
      ⟪ψ, π f ψ⟫_ℂ := by
  let fr : C(X, ℝ) := ⟨fun x => (f x).re, by fun_prop⟩
  let fi : C(X, ℝ) := ⟨fun x => (f x).im, by fun_prop⟩
  have hf : f = ofRealCM fr + Complex.I • ofRealCM fi := by
    ext x
    simp only [fr, fi, ContinuousMap.add_apply, ContinuousMap.smul_apply, ofRealCM_apply,
      ContinuousMap.coe_mk, smul_eq_mul]
    rw [mul_comm]
    exact (Complex.re_add_im _).symm
  have hint := integrable_repMeasure π ψ f
  have hre : (∫ x, f x ∂(repMeasure π ψ)).re = -- totalisation-audit: allow continuous
      ∫ x, fr x ∂(repMeasure π ψ) := by -- totalisation-audit: allow continuous
    have h := integral_re (𝕜 := ℂ) hint
    rw [RCLike.re_to_complex] at h
    exact h.symm
  have him : (∫ x, f x ∂(repMeasure π ψ)).im = -- totalisation-audit: allow continuous
      ∫ x, fi x ∂(repMeasure π ψ) := by -- totalisation-audit: allow continuous
    have h := integral_im (𝕜 := ℂ) hint
    rw [RCLike.im_to_complex] at h
    exact h.symm
  conv_rhs => rw [hf, map_add, map_smul, add_apply, FunLike.coe_smul, Pi.smul_apply,
    inner_add_right, inner_smul_right, inner_rep_ofRealCM_eq_integral,
    inner_rep_ofRealCM_eq_integral]
  apply Complex.ext
  · simp [hre]
  · simp [him]

/-- `∫ |g|² dμ_ψ = ‖π(g) ψ‖²` for continuous `g : X → ℂ`. -/
theorem integral_norm_sq_repMeasure (ψ : H) (g : C(X, ℂ)) :
    ∫ x, ‖g x‖ ^ 2 ∂(repMeasure π ψ) = -- totalisation-audit: allow continuous
      ‖π g ψ‖ ^ 2 := by
  let n : C(X, ℝ) := ⟨fun x => ‖g x‖ ^ 2, by fun_prop⟩
  have hn : ofRealCM n = star g * g := by
    ext x
    simp only [n, ofRealCM_apply, ContinuousMap.coe_mk, ContinuousMap.mul_apply,
      ContinuousMap.star_apply, RCLike.star_def, Complex.conj_mul']
    push_cast
    rfl
  have h := integral_repMeasure_real π ψ n
  rw [hn, inner_rep_star_mul_self, RCLike.re_to_complex, Complex.ofReal_re] at h
  exact h

/-- **Total mass**: `μ_ψ(X) = ‖ψ‖²`. -/
theorem repMeasure_real_univ (ψ : H) :
    (repMeasure π ψ).real Set.univ = ‖ψ‖ ^ 2 := by
  have h := integral_repMeasure_real π ψ 1
  rw [ofRealCM_one, map_one, one_apply_eq_self, inner_self_eq_norm_sq] at h
  simpa using h

/-- **Total mass**: `μ_ψ(X) = ‖ψ‖²`, as an extended nonnegative real. -/
theorem repMeasure_univ (ψ : H) :
    repMeasure π ψ Set.univ = ENNReal.ofReal (‖ψ‖ ^ 2) := by
  rw [← repMeasure_real_univ π ψ, measureReal_def,
    ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- **Uniqueness of the spectral measure**: a regular measure `ν` on `X` with
`∫ f dν = re ⟪ψ, π(f) ψ⟫` for every real continuous `f` is `μ_ψ`. -/
theorem eq_repMeasure (ψ : H) (ν : Measure X) [ν.Regular]
    (h : ∀ f : C(X, ℝ),
      ∫ x, f x ∂ν = -- totalisation-audit: allow continuous
        RCLike.re ⟪ψ, π (ofRealCM f) ψ⟫_ℂ) :
    ν = repMeasure π ψ :=
  Measure.ext_of_integral_eq_on_compactlySupported fun f =>
    (h f.toContinuousMap).trans (integral_repMeasure_real π ψ f.toContinuousMap).symm

end SpectralTheorem
