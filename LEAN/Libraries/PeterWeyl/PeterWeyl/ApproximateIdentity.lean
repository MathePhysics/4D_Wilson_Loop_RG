import PeterWeyl.Basic

/-!
# Approximate identities on a compact group

Let `G` be a compact topological group with a Haar measure `μ`.  This file constructs
approximate identities for the convolution `(φ ⋆ f) x = ∫ φ (x * y⁻¹) * f y ∂μ(y)` of
`PeterWeyl.Basic`: real kernels that are nonnegative, invariant under inversion, of mass one and
supported in a prescribed neighbourhood of `1`, and shows that convolution with such kernels
approximates a continuous function uniformly once the support is small enough.

The kernels are real, so that nonnegativity and mass one make sense; they are turned into complex
kernels by `complexify`.  A kernel invariant under inversion gives a kernel fixed by
`adjointKernel`, hence a self-adjoint convolution operator on `L²`.

## Main definitions

* `complexify ψ`: the complex kernel `g ↦ (ψ g : ℂ)` of a real continuous kernel `ψ`.

## Main statements

* `exists_approxKernel`: every neighbourhood `U` of `1` supports a continuous kernel
  `ψ : C(G, ℝ)` with `ψ ≥ 0`, `tsupport ψ ⊆ U`, `ψ g⁻¹ = ψ g` and `∫ ψ dμ = 1`.
* `adjointKernel_complexify`: for such a kernel, `adjointKernel (complexify ψ) = complexify ψ`.
* `exists_nhds_one_convolutionFun_approx`: for `f : C(G, ℂ)` and `ε > 0` there is a
  neighbourhood `U` of `1` such that `‖(ψ ⋆ f) x - f x‖ ≤ ε` for every `x` and every nonnegative
  kernel `ψ` of mass one supported in `U`.
* `exists_convolutionFun_approx`: the combination used for the Peter–Weyl theorem, a complex
  kernel fixed by `adjointKernel` with `‖(φ ⋆ f) x - f x‖ ≤ ε` for every `x`.

## Implementation notes

The Hausdorff property is not used.  A bump function at `1` comes from Urysohn's lemma
(`exists_continuous_one_zero_of_isCompact`) in the regular, locally compact space `G`, and is
symmetrised by adding its composition with inversion.  Its integral is positive because Haar
measure charges nonempty open sets.

Uniform continuity of `f` is used in the form `‖f (u⁻¹ * x) - f x‖ ≤ ε` for all `x` and all `u`
near `1` (`eventually_forall_norm_apply_inv_mul_sub_le`), obtained from the tube lemma
`IsCompact.eventually_forall_of_forall_eventually` rather than from a uniform structure.  The
change of variables `∫ ψ (x * y⁻¹) dμ(y) = ∫ ψ dμ` (`integral_apply_mul_inv_eq_one`) uses
invariance of `μ` under inversion (`isInvInvariant_of_compactSpace`) and left invariance; right
invariance is not needed.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ComplexConjugate

namespace PeterWeyl

section Complexify

variable {G : Type*} [TopologicalSpace G]

/-- The complexification `g ↦ (ψ g : ℂ)` of a real continuous kernel. -/
def complexify (ψ : C(G, ℝ)) : C(G, ℂ) :=
  (ContinuousMap.mk ((↑) : ℝ → ℂ) Complex.continuous_ofReal).comp ψ

@[simp]
theorem complexify_apply (ψ : C(G, ℝ)) (g : G) : complexify ψ g = (ψ g : ℂ) :=
  rfl

/-- The complexification of a real kernel invariant under inversion is fixed by `adjointKernel`,
so that convolution by it is self-adjoint. -/
theorem adjointKernel_complexify [Group G] [IsTopologicalGroup G] {ψ : C(G, ℝ)}
    (hψ : ∀ g, ψ g⁻¹ = ψ g) : adjointKernel (complexify ψ) = complexify ψ := by
  ext g
  simp [hψ]

end Complexify

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]

section Kernel

/-- A bump function at `1`: continuous, nonnegative, invariant under inversion, positive at `1`,
and with topological support in a given neighbourhood of `1`. -/
theorem exists_symmetric_bump {U : Set G} (hU : U ∈ 𝓝 (1 : G)) :
    ∃ φ : C(G, ℝ), (∀ g, 0 ≤ φ g) ∧ tsupport φ ⊆ U ∧ (∀ g, φ g⁻¹ = φ g) ∧ 0 < φ 1 := by
  obtain ⟨V, hV, hVc, hVU⟩ := exists_mem_nhds_isClosed_subset hU
  have hW : V ∩ V⁻¹ ∈ 𝓝 (1 : G) := inter_mem hV (inv_mem_nhds_one G hV)
  have hWc : IsClosed (V ∩ V⁻¹) := hVc.inter hVc.inv
  have hd : Disjoint ({1} : Set G) (interior (V ∩ V⁻¹))ᶜ :=
    disjoint_compl_right_iff_subset.2 (singleton_subset_iff.2 (mem_interior_iff_mem_nhds.2 hW))
  obtain ⟨f, hf1, hf0, -, hf01⟩ :=
    exists_continuous_one_zero_of_isCompact isCompact_singleton isOpen_interior.isClosed_compl hd
  refine ⟨⟨fun g => f g + f g⁻¹, by fun_prop⟩, fun g => add_nonneg (hf01 g).1 (hf01 g⁻¹).1,
    ?_, fun g => by simp [add_comm], ?_⟩
  · refine (closure_minimal (fun g hg => ?_) hWc).trans (inter_subset_left.trans hVU)
    by_contra hgW
    have h1 : f g = 0 := hf0 fun h => hgW (interior_subset h)
    have h2 : f g⁻¹ = 0 := hf0 fun h => hgW
      ⟨by simpa using (interior_subset h).2, by simpa using (interior_subset h).1⟩
    exact hg (by simp [h1, h2])
  · have : f 1 = 1 := hf1 (mem_singleton 1)
    simp [this]

variable [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]

/-- Every neighbourhood of `1` supports a nonnegative continuous kernel invariant under inversion
and of mass one: normalise a symmetric bump function at `1` by its integral, which is positive
because Haar measure charges nonempty open sets. -/
theorem exists_approxKernel {U : Set G} (hU : U ∈ 𝓝 (1 : G)) :
    ∃ ψ : C(G, ℝ), (∀ g, 0 ≤ ψ g) ∧ tsupport ψ ⊆ U ∧ (∀ g, ψ g⁻¹ = ψ g) ∧ ∫ g, ψ g ∂μ = 1 := by -- totalisation-audit: allow continuous integrand on a compact group, integrable
  obtain ⟨φ, hφ0, hφU, hφinv, hφ1⟩ := exists_symmetric_bump hU
  have hpos : 0 < ∫ g, φ g ∂μ := -- totalisation-audit: allow continuous integrand on a compact group, integrable
    φ.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
      (HasCompactSupport.of_compactSpace _) hφ0 hφ1.ne'
  refine ⟨(∫ g, φ g ∂μ)⁻¹ • φ, fun g => ?_, ?_, fun g => ?_, ?_⟩ -- totalisation-audit: allow the integral is positive by hpos
  · rw [ContinuousMap.smul_apply, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.2 hpos.le) (hφ0 g)
  · rw [ContinuousMap.coe_smul]
    exact (closure_mono (Function.support_const_smul_subset _ _)).trans hφU
  · rw [ContinuousMap.smul_apply, ContinuousMap.smul_apply, hφinv]
  · simp only [ContinuousMap.smul_apply, smul_eq_mul]
    rw [integral_const_mul, inv_mul_cancel₀ hpos.ne']

end Kernel

section Approximation

/-- Uniform continuity of a continuous function on a compact group with respect to left
translation: `‖f (u⁻¹ * x) - f x‖ ≤ ε` for all `x` once `u` is close to `1`. -/
theorem eventually_forall_norm_apply_inv_mul_sub_le (f : C(G, ℂ)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ u in 𝓝 (1 : G), ∀ x, ‖f (u⁻¹ * x) - f x‖ ≤ ε := by
  have hc : Continuous fun p : G × G => ‖f (p.1⁻¹ * p.2) - f p.2‖ := by fun_prop
  refine (isCompact_univ.eventually_forall_of_forall_eventually fun y _ => ?_).mono
    fun u hu x => hu x (mem_univ x)
  have h := hc.tendsto ((1 : G), y)
  simp only [inv_one, one_mul, sub_self, norm_zero] at h
  exact h.eventually (Iic_mem_nhds hε)

variable [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]

/-- A kernel of mass one keeps mass one after the change of variables `y ↦ x * y⁻¹`. -/
theorem integral_apply_mul_inv_eq_one {ψ : C(G, ℝ)} (hψ : ∫ g, ψ g ∂μ = 1) (x : G) : -- totalisation-audit: allow continuous integrand on a compact group, integrable
    ∫ y, ψ (x * y⁻¹) ∂μ = 1 := by -- totalisation-audit: allow continuous integrand on a compact group, integrable
  rw [integral_inv_eq_self (fun y => ψ (x * y)) μ, integral_mul_left_eq_self (fun y => ψ y) x, hψ]

/-- Convolution with a nonnegative kernel of mass one supported close enough to `1` approximates
a continuous function uniformly: `‖(ψ ⋆ f) x - f x‖ ≤ ε` for every `x`.  Since
`(ψ ⋆ f) x - f x = ∫ ψ (x * y⁻¹) * (f y - f x) dμ(y)` and `y = u⁻¹ * x` for `u = x * y⁻¹` in the
support of `ψ`, this is uniform continuity of `f`. -/
theorem exists_nhds_one_convolutionFun_approx (f : C(G, ℂ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ U ∈ 𝓝 (1 : G), ∀ ψ : C(G, ℝ), (∀ g, 0 ≤ ψ g) → tsupport ψ ⊆ U → ∫ g, ψ g ∂μ = 1 → -- totalisation-audit: allow continuous integrand on a compact group, integrable
      ∀ x, ‖convolutionFun μ (complexify ψ) f x - f x‖ ≤ ε := by
  refine ⟨_, eventually_forall_norm_apply_inv_mul_sub_le f hε, fun ψ hψ0 hψU hψ1 x => ?_⟩
  have hmass := integral_apply_mul_inv_eq_one μ hψ1 x
  have hcont : Continuous fun y => ψ (x * y⁻¹) := by fun_prop
  have hint : Integrable (fun y => ψ (x * y⁻¹)) μ :=
    hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hintC : Integrable (fun y => (ψ (x * y⁻¹) : ℂ)) μ :=
    (Complex.continuous_ofReal.comp hcont).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hintCf : Integrable (fun y => (ψ (x * y⁻¹) : ℂ) * f y) μ :=
    ((Complex.continuous_ofReal.comp hcont).mul f.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have heq : convolutionFun μ (complexify ψ) f x - f x =
      ∫ y, (ψ (x * y⁻¹) : ℂ) * (f y - f x) ∂μ := by -- totalisation-audit: allow continuous integrand on a compact group, integrable
    simp only [convolutionFun, complexify_apply, mul_sub]
    rw [integral_sub hintCf (hintC.mul_const _), integral_mul_const, integral_complex_ofReal,
      hmass, Complex.ofReal_one, one_mul]
  rw [heq]
  calc ‖∫ y, (ψ (x * y⁻¹) : ℂ) * (f y - f x) ∂μ‖ -- totalisation-audit: allow continuous integrand on a compact group, integrable
      ≤ ∫ y, ψ (x * y⁻¹) * ε ∂μ := by -- totalisation-audit: allow continuous integrand on a compact group, integrable
        refine norm_integral_le_of_norm_le (hint.mul_const ε) (ae_of_all _ fun y => ?_)
        rw [norm_mul, Complex.norm_of_nonneg (hψ0 _)]
        by_cases hy : ψ (x * y⁻¹) = 0
        · simp [hy]
        refine mul_le_mul_of_nonneg_left ?_ (hψ0 _)
        have hmem := hψU (subset_tsupport _ hy) x
        simpa using hmem
    _ = ε := by rw [integral_mul_const, hmass, one_mul] -- totalisation-audit: allow continuous integrand on a compact group, integrable

/-- For `f : C(G, ℂ)` and `ε > 0` there is a complex kernel `φ`, the complexification of a
nonnegative real kernel of mass one, fixed by `adjointKernel` and with `‖(φ ⋆ f) x - f x‖ ≤ ε`
for every `x`. -/
theorem exists_convolutionFun_approx (f : C(G, ℂ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : C(G, ℂ), adjointKernel φ = φ ∧ ∀ x, ‖convolutionFun μ φ f x - f x‖ ≤ ε := by
  obtain ⟨U, hU, hUapprox⟩ := exists_nhds_one_convolutionFun_approx μ f hε
  obtain ⟨ψ, hψ0, hψU, hψinv, hψ1⟩ := exists_approxKernel μ hU
  exact ⟨complexify ψ, adjointKernel_complexify hψinv, hUapprox ψ hψ0 hψU hψ1⟩

end Approximation

end PeterWeyl
