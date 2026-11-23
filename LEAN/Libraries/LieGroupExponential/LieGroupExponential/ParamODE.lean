import LieGroupExponential.OmegaLemma

/-!
# A `C^n` family of solutions of a parametrised ODE near a stationary parameter

Let `F : E × P → E` be `C^n` with `F (x, 0) = 0` for all `x`.  Then the solutions of
`γ' = F (γ, p)`, `γ 0 = 0` on a fixed time interval `[-T, T]` form a family `p ↦ Γ p` which is
`C^n` at `p = 0` as a map into the Banach space of continuous curves.  This is the situation of
the exponential map of a Lie group in a chart: `F (x, ξ)` is the left-invariant vector field of
`ξ` read in the chart, and it vanishes identically for `ξ = 0`.

The proof applies mathlib's `C^n` implicit function theorem to the Picard map
`Φ (p, γ) = γ - ∫₀ᵗ F (γ s, p) ds` at `(0, 0)`, where its partial derivative in `γ` is the identity.
-/

noncomputable section

open scoped Topology
open Set Metric Filter

universe u

namespace LieGroupExponential
namespace ParamODE

open OmegaLemma MeasureTheory

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {P : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P]
variable {T : ℝ}

/-- The time interval `[-T, T]`. -/
abbrev Time (T : ℝ) : Type := Set.Icc (-T) T

/-- Extension of a curve on `[-T, T]` to the real line, frozen at the endpoints. -/
def extend (hT : 0 ≤ T) (γ : C(Time T, E)) (s : ℝ) : E :=
  γ (Set.projIcc (-T) T (by linarith) s)

omit [NormedSpace ℝ E] in
theorem continuous_extend (hT : 0 ≤ T) (γ : C(Time T, E)) : Continuous (extend hT γ) :=
  γ.continuous.comp continuous_projIcc

omit [NormedSpace ℝ E] in
theorem extend_coe (hT : 0 ≤ T) (γ : C(Time T, E)) (t : Time T) : extend hT γ t = γ t := by
  rw [extend, Set.projIcc_val]

omit [NormedSpace ℝ E] in
theorem norm_extend_le (hT : 0 ≤ T) (γ : C(Time T, E)) (s : ℝ) : ‖extend hT γ s‖ ≤ ‖γ‖ :=
  γ.norm_coe_le_norm _

/-- The primitive `t ↦ ∫₀ᵗ γ` as a linear map on the space of curves. -/
def primitiveLM (hT : 0 ≤ T) : C(Time T, E) →ₗ[ℝ] C(Time T, E) where
  toFun γ :=
    ⟨fun t => ∫ s in (0 : ℝ)..t, extend hT γ s, -- totalisation-audit: allow continuous integrand on a compact interval is interval integrable
      (intervalIntegral.continuous_primitive
        (fun a b => (continuous_extend hT γ).intervalIntegrable a b) 0).comp
        continuous_subtype_val⟩
  map_add' γ γ' := by
    ext t
    simp only [ContinuousMap.coe_mk, ContinuousMap.add_apply]
    rw [← intervalIntegral.integral_add ((continuous_extend hT γ).intervalIntegrable _ _)
      ((continuous_extend hT γ').intervalIntegrable _ _)]
    rfl
  map_smul' c γ := by
    ext t
    simp only [ContinuousMap.coe_mk, ContinuousMap.smul_apply, RingHom.id_apply]
    rw [← intervalIntegral.integral_smul]
    rfl

theorem norm_primitiveLM_le (hT : 0 ≤ T) (γ : C(Time T, E)) :
    ‖primitiveLM hT γ‖ ≤ T * ‖γ‖ := by
  rw [ContinuousMap.norm_le _ (mul_nonneg hT (norm_nonneg γ))]
  intro t
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := (t : ℝ))
    (C := ‖γ‖) (f := extend hT γ) (fun s _ => norm_extend_le hT γ s)
  have ht : |(t : ℝ) - 0| ≤ T := by
    rw [sub_zero, abs_le]
    exact ⟨t.2.1, t.2.2⟩
  calc ‖primitiveLM hT γ t‖ ≤ ‖γ‖ * |(t : ℝ) - 0| := h
    _ ≤ ‖γ‖ * T := mul_le_mul_of_nonneg_left ht (norm_nonneg γ)
    _ = T * ‖γ‖ := mul_comm _ _

/-- The primitive as a continuous linear map of norm at most `T`. -/
def primitive (hT : 0 ≤ T) : C(Time T, E) →L[ℝ] C(Time T, E) :=
  LinearMap.mkContinuous (𝕜 := ℝ) (𝕜₂ := ℝ) (E := C(Time T, E)) (F := C(Time T, E))
    (σ := RingHom.id ℝ) (primitiveLM hT) T (norm_primitiveLM_le hT)

theorem primitive_apply (hT : 0 ≤ T) (γ : C(Time T, E)) (t : Time T) :
    primitive hT γ t = ∫ s in (0 : ℝ)..t, extend hT γ s := rfl -- totalisation-audit: allow continuous integrand on a compact interval is interval integrable

/-- A parameter and a curve, paired into a curve in `E × P`. -/
def pairLM : P × C(Time T, E) →ₗ[ℝ] C(Time T, E × P) where
  toFun z := ⟨fun t => (z.2 t, z.1), z.2.continuous.prodMk continuous_const⟩
  map_add' z z' := by ext t <;> simp
  map_smul' c z := by ext t <;> simp

theorem norm_pairLM_le (z : P × C(Time T, E)) : ‖pairLM z‖ ≤ 1 * ‖z‖ := by
  rw [one_mul, ContinuousMap.norm_le _ (norm_nonneg z)]
  intro t
  exact max_le ((z.2.norm_coe_le_norm t).trans (norm_snd_le z)) (norm_fst_le z)

/-- The pairing as a continuous linear map. -/
def pair : P × C(Time T, E) →L[ℝ] C(Time T, E × P) :=
  LinearMap.mkContinuous (𝕜 := ℝ) (𝕜₂ := ℝ) (E := P × C(Time T, E)) (F := C(Time T, E × P))
    (σ := RingHom.id ℝ) pairLM 1 norm_pairLM_le

@[simp]
theorem pair_apply (z : P × C(Time T, E)) (t : Time T) : pair z t = (z.2 t, z.1) := rfl

/-- The Picard map `Φ (p, γ) = γ - ∫₀ᵗ F (γ s, p) ds`. -/
def picardMap (F : E × P → E) (hF : Continuous F) (hT : 0 ≤ T) (z : P × C(Time T, E)) :
    C(Time T, E) :=
  z.2 - primitive hT (superposition F hF (pair z))

theorem contDiff_picardMap (n : ℕ) {F : E × P → E} (hF : ContDiff ℝ n F) (hT : 0 ≤ T) :
    ContDiff ℝ n (picardMap (T := T) F hF.continuous hT) := by
  have h1 : ContDiff ℝ n (fun z : P × C(Time T, E) =>
      superposition F hF.continuous (pair z)) :=
    (contDiff_superposition n hF).comp (pair (E := E) (P := P) (T := T)).contDiff
  have h2 : ContDiff ℝ n (fun z : P × C(Time T, E) =>
      primitive hT (superposition F hF.continuous (pair z))) :=
    (primitive (E := E) hT).contDiff.comp h1
  exact contDiff_snd.sub h2

/-- If `F (·, 0)` vanishes identically, the derivative of `F` at `(x, 0)` kills the `E`
directions. -/
theorem fderiv_apply_inl_eq_zero {F : E × P → E} (hF : ContDiff ℝ 1 F)
    (hF0 : ∀ x, F (x, 0) = 0) (x v : E) : fderiv ℝ F (x, 0) (v, 0) = 0 := by -- totalisation-audit: allow the map is C^1 at this point, so fderiv is its genuine derivative
  have h1 : HasFDerivAt (fun y : E => F (y, 0))
      ((fderiv ℝ F (x, 0)).comp (ContinuousLinearMap.inl ℝ E P)) x := -- totalisation-audit: allow the map is C^1 at this point, so fderiv is its genuine derivative
    ((hF.differentiable one_ne_zero) (x, 0)).hasFDerivAt.comp x (hasFDerivAt_prodMk_left x 0)
  have h2 : HasFDerivAt (fun y : E => F (y, 0)) (0 : E →L[ℝ] E) x := by
    simp only [hF0]
    exact hasFDerivAt_const _ _
  have h := congrArg (fun L : E →L[ℝ] E => L v) (h1.unique h2)
  simpa using h

/-- The partial derivative of the Picard map in the curve direction at `(0, 0)` is the identity. -/
theorem fderiv_picardMap_comp_inr {F : E × P → E} (hF : ContDiff ℝ 1 F)
    (hF0 : ∀ x, F (x, 0) = 0) (hT : 0 ≤ T) :
    (fderiv ℝ (picardMap (T := T) F hF.continuous hT) (0, 0)) ∘L -- totalisation-audit: allow the map is C^1 at this point, so fderiv is its genuine derivative
        ContinuousLinearMap.inr ℝ P C(Time T, E) =
      ContinuousLinearMap.id ℝ C(Time T, E) := by
  have hΩ := hasFDerivAt_superposition (K := Time T) hF (pair ((0 : P), (0 : C(Time T, E))))
  have hcomp : HasFDerivAt (picardMap (T := T) F hF.continuous hT)
      (ContinuousLinearMap.snd ℝ P C(Time T, E) -
        (primitive hT) ∘L ((pointwiseApply (superposition (fderiv ℝ F) -- totalisation-audit: allow the map is C^1 at this point, so fderiv is its genuine derivative
          (hF.continuous_fderiv one_ne_zero) (pair ((0 : P), (0 : C(Time T, E)))))) ∘L pair))
      ((0 : P), (0 : C(Time T, E))) := by
    have hp : HasFDerivAt (pair (E := E) (P := P) (T := T)) pair
        ((0 : P), (0 : C(Time T, E))) :=
      (pair (E := E) (P := P) (T := T)).hasFDerivAt
    have hs : HasFDerivAt (fun z : P × C(Time T, E) => superposition F hF.continuous (pair z))
        ((pointwiseApply (superposition (fderiv ℝ F) (hF.continuous_fderiv one_ne_zero) -- totalisation-audit: allow the map is C^1 at this point, so fderiv is its genuine derivative
          (pair ((0 : P), (0 : C(Time T, E)))))) ∘L pair) ((0 : P), (0 : C(Time T, E))) :=
      hΩ.comp _ hp
    have hi : HasFDerivAt (fun z : P × C(Time T, E) =>
        primitive hT (superposition F hF.continuous (pair z)))
        ((primitive hT) ∘L ((pointwiseApply (superposition (fderiv ℝ F) -- totalisation-audit: allow the map is C^1 at this point, so fderiv is its genuine derivative
          (hF.continuous_fderiv one_ne_zero) (pair ((0 : P), (0 : C(Time T, E)))))) ∘L pair))
        ((0 : P), (0 : C(Time T, E))) :=
      (primitive (E := E) hT).hasFDerivAt.comp _ hs
    exact hasFDerivAt_snd.sub hi
  rw [hcomp.fderiv]
  ext δ t
  have hzero : pointwiseApply (superposition (fderiv ℝ F) (hF.continuous_fderiv one_ne_zero) -- totalisation-audit: allow the map is C^1 at this point, so fderiv is its genuine derivative
      (pair ((0 : P), (0 : C(Time T, E))))) (pair ((0 : P), δ)) = 0 := by
    ext s
    simp [fderiv_apply_inl_eq_zero hF hF0]
  simp [hzero]

variable [CompleteSpace E] [CompleteSpace P]

/-- A `C^n` family of solutions near the stationary parameter. -/
theorem exists_contDiffAt_solutions {n : ℕ} (hn : n ≠ 0) {F : E × P → E} (hF : ContDiff ℝ n F)
    (hF0 : ∀ x, F (x, 0) = 0) (hT : 0 ≤ T) :
    ∃ Γ : P → C(Time T, E), ContDiffAt ℝ n Γ 0 ∧ Γ 0 = 0 ∧
      ∀ᶠ p in 𝓝 (0 : P), ∀ t : Time T,
        Γ p t = ∫ s in (0 : ℝ)..t, F (extend hT (Γ p) s, p) := by -- totalisation-audit: allow continuous integrand on a compact interval is interval integrable
  have h1 : ContDiff ℝ 1 F := hF.of_le (by exact_mod_cast Nat.one_le_iff_ne_zero.2 hn)
  have hΦ : ContDiffAt ℝ n (picardMap (T := T) F hF.continuous hT)
      ((0 : P), (0 : C(Time T, E))) := (contDiff_picardMap n hF hT).contDiffAt
  have hn' : (n : WithTop ℕ∞) ≠ 0 := by exact_mod_cast hn
  have hinv : (fderiv ℝ (picardMap (T := T) F hF.continuous hT) (0, 0) ∘L -- totalisation-audit: allow the map is C^1 at this point, so fderiv is its genuine derivative
      ContinuousLinearMap.inr ℝ P C(Time T, E)).IsInvertible := by
    rw [fderiv_picardMap_comp_inr h1 hF0 hT]
    exact ⟨ContinuousLinearEquiv.refl ℝ _, rfl⟩
  have h0 : picardMap (T := T) F hF.continuous hT ((0 : P), (0 : C(Time T, E))) = 0 := by
    ext t
    simp [picardMap, primitive_apply, extend, hF0]
  refine ⟨hΦ.implicitFunction hn' hinv, hΦ.contDiffAt_implicitFunction hn' hinv,
    hΦ.implicitFunction_apply_self hn' hinv, ?_⟩
  filter_upwards [hΦ.eventually_apply_implicitFunction hn' hinv] with p hp t
  rw [h0] at hp
  have ht := congrArg (fun γ : C(Time T, E) => γ t) hp
  simp only [picardMap, ContinuousMap.sub_apply, ContinuousMap.zero_apply, sub_eq_zero] at ht
  rw [ht, primitive_apply]
  rfl

end ParamODE
end LieGroupExponential

