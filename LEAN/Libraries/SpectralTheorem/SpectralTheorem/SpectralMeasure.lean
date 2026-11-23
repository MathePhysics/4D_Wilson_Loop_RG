import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

/-!
# Spectral measures of a bounded normal operator

Let `T` be a bounded normal operator on a complex Hilbert space `H` and `ψ ∈ H`.  The map
`f ↦ ⟪ψ, f(T) ψ⟫` on continuous functions on the spectrum `σ(T)` is a positive linear functional,
so by the Riesz–Markov–Kakutani theorem there is a unique regular Borel measure `μ_ψ` on `σ(T)`
with `⟪ψ, f(T) ψ⟫ = ∫ f dμ_ψ`.  This is Reed–Simon I, §VII.2, pp. 224–225 ("the spectral measure
associated with the vector `ψ`"), where `T` is self-adjoint and `σ(T) ⊆ ℝ`; for normal `T`,
`σ(T) ⊆ ℂ` (Reed–Simon I, Problems VII.3–5).

Here `f(T)` is mathlib's continuous functional calculus `cfcHom`, a `⋆`-algebra homomorphism
`C(σ(T), ℂ) → 𝓛(H)`, available because `H →L[ℂ] H` is a C⋆-algebra.

Every Bochner integral in this file is of a continuous function on the compact space `σ(T)` against
a finite measure, hence of an integrable function (`integrable_spectralMeasure`); the lines carry
the totalisation-audit marker "continuous" for this reason.

## Main definitions

* `SpectralTheorem.spectralFunctional T ψ`: the positive linear functional
  `f ↦ re ⟪ψ, f(T) ψ⟫` on `C_c(σ(T), ℝ) = C(σ(T), ℝ)`.
* `SpectralTheorem.spectralMeasure T ψ`: the spectral measure `μ_ψ`, a finite regular Borel measure
  on `σ(T)`.

## Main results

* `SpectralTheorem.integral_spectralMeasure`: `∫ f dμ_ψ = ⟪ψ, f(T) ψ⟫` for `f ∈ C(σ(T), ℂ)`.
* `SpectralTheorem.integral_norm_sq_spectralMeasure`: `∫ |f|² dμ_ψ = ‖f(T) ψ‖²`.
* `SpectralTheorem.spectralMeasure_univ`: `μ_ψ(σ(T)) = ‖ψ‖²`.
-/

noncomputable section

open scoped InnerProductSpace ComplexConjugate CompactlySupported
open MeasureTheory

namespace SpectralTheorem

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

section RealFunctions

variable {X : Type*} [TopologicalSpace X]

/-- A real continuous function viewed as a complex one. -/
def ofRealCM (f : C(X, ℝ)) : C(X, ℂ) :=
  ⟨fun x => (f x : ℂ), by fun_prop⟩

@[simp]
theorem ofRealCM_apply (f : C(X, ℝ)) (x : X) : ofRealCM f x = (f x : ℂ) :=
  rfl

theorem ofRealCM_add (f g : C(X, ℝ)) : ofRealCM (f + g) = ofRealCM f + ofRealCM g := by
  ext x
  simp

theorem ofRealCM_smul (c : ℝ) (f : C(X, ℝ)) : ofRealCM (c • f) = (c : ℂ) • ofRealCM f := by
  ext x
  simp

theorem star_ofRealCM (f : C(X, ℝ)) : star (ofRealCM f) = ofRealCM f := by
  ext x
  simp

theorem ofRealCM_one : ofRealCM (1 : C(X, ℝ)) = 1 := by
  ext x
  simp

end RealFunctions

variable (T : H →L[ℂ] H) [hT : IsStarNormal T]

/-- `⟪ψ, g(T)* g(T) ψ⟫ = ‖g(T) ψ‖²`, the identity behind positivity of the spectral functional. -/
theorem inner_cfcHom_star_mul_self (g : C(spectrum ℂ T, ℂ)) (ψ : H) :
    ⟪ψ, cfcHom hT (star g * g) ψ⟫_ℂ = (‖cfcHom hT g ψ‖ ^ 2 : ℝ) := by
  rw [map_mul, map_star, ContinuousLinearMap.star_eq_adjoint,
    mul_apply_eq_comp, ContinuousLinearMap.adjoint_inner_right,
    inner_self_eq_norm_sq_to_K]
  norm_cast

/-- For a real continuous `f`, the operator `f(T)` is self-adjoint, so `⟪ψ, f(T) ψ⟫` is real. -/
theorem inner_cfcHom_ofRealCM (f : C(spectrum ℂ T, ℝ)) (ψ : H) :
    ⟪ψ, cfcHom hT (ofRealCM f) ψ⟫_ℂ = (RCLike.re ⟪ψ, cfcHom hT (ofRealCM f) ψ⟫_ℂ : ℂ) := by
  have hsa : IsSelfAdjoint (cfcHom hT (ofRealCM f)) := by
    rw [IsSelfAdjoint, ← map_star, star_ofRealCM]
  refine (RCLike.conj_eq_iff_re.mp ?_).symm
  rw [inner_conj_symm, ← ContinuousLinearMap.adjoint_inner_left,
    ← ContinuousLinearMap.star_eq_adjoint, hsa.star_eq]

/-- For a nonnegative real continuous `f`, `re ⟪ψ, f(T) ψ⟫ ≥ 0`: write `f = g²` with
`g = √f`, so that `⟪ψ, f(T) ψ⟫ = ‖g(T) ψ‖²`. -/
theorem re_inner_cfcHom_ofRealCM_nonneg (f : C(spectrum ℂ T, ℝ)) (hf : 0 ≤ f) (ψ : H) :
    0 ≤ RCLike.re ⟪ψ, cfcHom hT (ofRealCM f) ψ⟫_ℂ := by
  let g : C(spectrum ℂ T, ℂ) := ofRealCM ⟨fun x => Real.sqrt (f x), by fun_prop⟩
  have hg : star g * g = ofRealCM f := by
    ext x
    simp only [g, ContinuousMap.mul_apply, ContinuousMap.star_apply, ofRealCM_apply,
      ContinuousMap.coe_mk, RCLike.star_def, Complex.conj_ofReal]
    rw [← Complex.ofReal_mul]
    congr 1
    exact Real.mul_self_sqrt (hf x)
  rw [← hg, inner_cfcHom_star_mul_self, RCLike.re_to_complex, Complex.ofReal_re]
  positivity

/-- The real-linear functional `f ↦ re ⟪ψ, f(T) ψ⟫` on `C(σ(T), ℝ)`. -/
def spectralLinear (ψ : H) : C(spectrum ℂ T, ℝ) →ₗ[ℝ] ℝ where
  toFun f := RCLike.re ⟪ψ, cfcHom hT (ofRealCM f) ψ⟫_ℂ
  map_add' f g := by
    rw [ofRealCM_add, map_add, add_apply, inner_add_right, map_add]
  map_smul' c f := by
    rw [ofRealCM_smul, map_smul, FunLike.coe_smul, Pi.smul_apply, inner_smul_right,
      RingHom.id_apply, smul_eq_mul, RCLike.re_to_complex, RCLike.re_to_complex,
      Complex.re_ofReal_mul]

theorem spectralLinear_apply (ψ : H) (f : C(spectrum ℂ T, ℝ)) :
    spectralLinear T ψ f = RCLike.re ⟪ψ, cfcHom hT (ofRealCM f) ψ⟫_ℂ :=
  rfl

/-- **The spectral functional** of `ψ`: `f ↦ re ⟪ψ, f(T) ψ⟫`, a positive linear functional on
`C_c(σ(T), ℝ)`, which is `C(σ(T), ℝ)` since `σ(T)` is compact (Reed–Simon I, p. 224). -/
def spectralFunctional (ψ : H) : C_c(spectrum ℂ T, ℝ) →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀
    { toFun := fun f => spectralLinear T ψ f.toContinuousMap
      map_add' := fun f g => (spectralLinear T ψ).map_add f.toContinuousMap g.toContinuousMap
      map_smul' := fun c f => (spectralLinear T ψ).map_smul c f.toContinuousMap }
    fun f hf => re_inner_cfcHom_ofRealCM_nonneg T f.toContinuousMap (fun x => hf x) ψ

/-- **The spectral measure** `μ_ψ` of `ψ` for the normal operator `T` (Reed–Simon I, §VII.2,
p. 225): the regular Borel measure on `σ(T)` given by the Riesz–Markov–Kakutani theorem for the
spectral functional. -/
def spectralMeasure (ψ : H) : Measure (spectrum ℂ T) :=
  RealRMK.rieszMeasure (spectralFunctional T ψ)

instance (ψ : H) : (spectralMeasure T ψ).Regular :=
  RealRMK.regular_rieszMeasure _

instance (ψ : H) : IsFiniteMeasure (spectralMeasure T ψ) :=
  CompactSpace.isFiniteMeasure

/-- Continuous functions on the spectrum are integrable for the spectral measure. -/
theorem integrable_spectralMeasure {E : Type*} [NormedAddCommGroup E] (ψ : H)
    (f : C(spectrum ℂ T, E)) : Integrable f (spectralMeasure T ψ) :=
  f.continuous.integrable_of_hasCompactSupport
    (IsCompact.of_isClosed_subset isCompact_univ (isClosed_tsupport _) (Set.subset_univ _))

/-- `∫ f dμ_ψ = re ⟪ψ, f(T) ψ⟫` for a real continuous `f`. -/
theorem integral_spectralMeasure_real (ψ : H) (f : C(spectrum ℂ T, ℝ)) :
    ∫ x, f x ∂(spectralMeasure T ψ) = -- totalisation-audit: allow continuous
      RCLike.re ⟪ψ, cfcHom hT (ofRealCM f) ψ⟫_ℂ :=
  RealRMK.integral_rieszMeasure (spectralFunctional T ψ)
    (CompactlySupportedContinuousMap.continuousMapEquiv f)

/-- `⟪ψ, f(T) ψ⟫ = ∫ f dμ_ψ` for a real continuous `f`. -/
theorem inner_cfcHom_ofRealCM_eq_integral (ψ : H) (f : C(spectrum ℂ T, ℝ)) :
    ⟪ψ, cfcHom hT (ofRealCM f) ψ⟫_ℂ =
      ((∫ x, f x ∂(spectralMeasure T ψ) -- totalisation-audit: allow continuous
        : ℝ) : ℂ) := by
  rw [integral_spectralMeasure_real, inner_cfcHom_ofRealCM]
  rfl

/-- **The defining property of the spectral measure**: `∫ f dμ_ψ = ⟪ψ, f(T) ψ⟫` for every
continuous `f : σ(T) → ℂ` (Reed–Simon I, §VII.2, p. 224). -/
theorem integral_spectralMeasure (ψ : H) (f : C(spectrum ℂ T, ℂ)) :
    ∫ x, f x ∂(spectralMeasure T ψ) = -- totalisation-audit: allow continuous
      ⟪ψ, cfcHom hT f ψ⟫_ℂ := by
  let fr : C(spectrum ℂ T, ℝ) := ⟨fun x => (f x).re, by fun_prop⟩
  let fi : C(spectrum ℂ T, ℝ) := ⟨fun x => (f x).im, by fun_prop⟩
  have hf : f = ofRealCM fr + Complex.I • ofRealCM fi := by
    ext x
    simp only [fr, fi, ContinuousMap.add_apply, ContinuousMap.smul_apply, ofRealCM_apply,
      ContinuousMap.coe_mk, smul_eq_mul]
    rw [mul_comm]
    exact (Complex.re_add_im _).symm
  have hint := integrable_spectralMeasure T ψ f
  have hre : (∫ x, f x ∂(spectralMeasure T ψ)).re = -- totalisation-audit: allow continuous
      ∫ x, fr x ∂(spectralMeasure T ψ) := by -- totalisation-audit: allow continuous
    have h := integral_re (𝕜 := ℂ) hint
    rw [RCLike.re_to_complex] at h
    exact h.symm
  have him : (∫ x, f x ∂(spectralMeasure T ψ)).im = -- totalisation-audit: allow continuous
      ∫ x, fi x ∂(spectralMeasure T ψ) := by -- totalisation-audit: allow continuous
    have h := integral_im (𝕜 := ℂ) hint
    rw [RCLike.im_to_complex] at h
    exact h.symm
  conv_rhs => rw [hf, map_add, map_smul, add_apply, FunLike.coe_smul, Pi.smul_apply,
    inner_add_right, inner_smul_right, inner_cfcHom_ofRealCM_eq_integral,
    inner_cfcHom_ofRealCM_eq_integral]
  apply Complex.ext
  · simp [hre]
  · simp [him]

/-- `∫ |g|² dμ_ψ = ‖g(T) ψ‖²` for continuous `g : σ(T) → ℂ`. -/
theorem integral_norm_sq_spectralMeasure (ψ : H) (g : C(spectrum ℂ T, ℂ)) :
    ∫ x, ‖g x‖ ^ 2 ∂(spectralMeasure T ψ) = -- totalisation-audit: allow continuous
      ‖cfcHom hT g ψ‖ ^ 2 := by
  let n : C(spectrum ℂ T, ℝ) := ⟨fun x => ‖g x‖ ^ 2, by fun_prop⟩
  have hn : ofRealCM n = star g * g := by
    ext x
    simp only [n, ofRealCM_apply, ContinuousMap.coe_mk, ContinuousMap.mul_apply,
      ContinuousMap.star_apply, RCLike.star_def, Complex.conj_mul']
    push_cast
    rfl
  have h := integral_spectralMeasure_real T ψ n
  rw [hn, inner_cfcHom_star_mul_self, RCLike.re_to_complex, Complex.ofReal_re] at h
  exact h

/-- **Total mass**: `μ_ψ(σ(T)) = ‖ψ‖²`. -/
theorem spectralMeasure_real_univ (ψ : H) :
    (spectralMeasure T ψ).real Set.univ = ‖ψ‖ ^ 2 := by
  have h := integral_spectralMeasure_real T ψ 1
  rw [ofRealCM_one, map_one, one_apply_eq_self, inner_self_eq_norm_sq] at h
  simpa using h

/-- **Total mass**: `μ_ψ(σ(T)) = ‖ψ‖²`, as an extended nonnegative real. -/
theorem spectralMeasure_univ (ψ : H) :
    spectralMeasure T ψ Set.univ = ENNReal.ofReal (‖ψ‖ ^ 2) := by
  rw [← spectralMeasure_real_univ T ψ, measureReal_def,
    ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- **Uniqueness of the spectral measure**: a regular measure `ν` on `σ(T)` with
`∫ f dν = re ⟪ψ, f(T) ψ⟫` for every real continuous `f` is `μ_ψ`. -/
theorem eq_spectralMeasure (ψ : H) (ν : Measure (spectrum ℂ T)) [ν.Regular]
    (h : ∀ f : C(spectrum ℂ T, ℝ),
      ∫ x, f x ∂ν = -- totalisation-audit: allow continuous
        RCLike.re ⟪ψ, cfcHom hT (ofRealCM f) ψ⟫_ℂ) :
    ν = spectralMeasure T ψ :=
  Measure.ext_of_integral_eq_on_compactlySupported fun f =>
    (h f.toContinuousMap).trans (integral_spectralMeasure_real T ψ f.toContinuousMap).symm

end SpectralTheorem
