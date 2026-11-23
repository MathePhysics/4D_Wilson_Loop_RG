import TotalisationSafety
import CompactLieHeatKernel.InvariantMetric
import CompactLieHeatKernel.LeftLaplacian
import CompactLieHeatKernel.L2Semigroup
import CompactLieHeatKernel.LaplacianGeneratorBridge

/-!
# Totalisation audit for CompactLieHeatKernel

Generic proof-carrying wrappers and the shared textual regression audit live in the separate
`TotalisationSafety` library.  Since `TotalisationSafety` v0.4, this includes Mathlib's totalised
manifold derivatives `mfderiv` and `mfderivWithin`.

This module records only the HeatKernel-specific proof obligations selecting the genuine branches
of the reviewed ambient operations.  In particular, the first-order smooth-function and
conjugation derivatives are certified below.  The second-order derivative occurring in
`leftHessian` remains an explicit analytic boundary until the corresponding manifold-calculus
theorem is proved.
-/

noncomputable section

open Set
open scoped Manifold ContDiff NNReal

namespace CompactLieHeatKernel

/-- The fixed scalar denominator in `halfLeftLaplacian` is genuinely nonzero. -/
theorem totalisationGuard_halfLeftLaplacian_denominator : (2 : ℝ) ≠ 0 := by
  norm_num

/-- On the punctured right-neighbourhood used in the generator limit, the time denominator is
nonzero.  The value of the ambient total inverse at `t = 0` is therefore never observed by the
filter in `L2SelfAdjointMarkovSemigroup.HasGenerator`. -/
theorem totalisationGuard_generator_time_denominator
    {t : ℝ≥0} (ht : t ∈ Ioi 0) : (t : ℝ) ≠ 0 := by
  exact NNReal.coe_ne_zero.mpr (ne_of_gt ht)

section SmoothManifoldGuards

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G]

/-- Auxiliary certificate that the extended chart derivative is genuine.  In v0.11,
`tangentChartModelEquiv` uses the data-valued derivative of the actual chart, so this theorem is
retained as a regression and totalisation-safety witness rather than construction data. -/
theorem totalisationGuard_extChartAt_mdifferentiableAt [IsManifold I ∞ G] (x : G) :
    MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I x) x :=
  mdifferentiableAt_extChartAt (ChartedSpace.mem_chart_source x)

/-- A smooth scalar function is manifold-differentiable everywhere, so the `mfderiv`
used by `leftDifferential` is on its genuine branch whenever an explicit smoothness witness is
available. Stating the witness directly avoids adding an irrelevant `IsManifold` parameter to
this totalisation guard. -/
theorem totalisationGuard_smoothScalar_mdifferentiableAt
    {f : G → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (g : G) :
    MDifferentiableAt I 𝓘(ℝ) f g :=
  hf.mdifferentiableAt (by simp)

/-- The same first-order fact packaged through the reusable proof-carrying manifold derivative API. -/
noncomputable def totalisationSafe_smoothScalarDerivativeAt
    {f : G → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (g : G) :
    TotalisationSafety.ManifoldDerivativeAt (I := I) (I' := 𝓘(ℝ)) f g :=
  TotalisationSafety.ManifoldDerivativeAt.ofMDifferentiableAt
    (totalisationGuard_smoothScalar_mdifferentiableAt (I := I) hf g)
end SmoothManifoldGuards

section LieGroupGuards

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G]

/-- Conjugation by a fixed element is smooth; hence the `mfderiv` in `adjointDifferential` is not
using the zero fallback.  Group inversion itself is genuine total algebraic inversion. -/
theorem totalisationGuard_conjugation_mdifferentiableAt (g : G) :
    MDifferentiableAt I I (fun h : G ↦ g * h * g⁻¹) (1 : G) := by
  have hleft : ContMDiff I I ∞ (fun h : G ↦ g * h) :=
    contMDiff_mul_left
  have hright : ContMDiff I I ∞ (fun h : G ↦ h * g⁻¹) :=
    contMDiff_mul_right
  have hconj : ContMDiff I I ∞ (fun h : G ↦ g * h * g⁻¹) := by
    simpa only [Function.comp_def] using hright.comp hleft
  exact hconj.mdifferentiableAt (by simp)

/-- Conjugation's derivative packaged by the generic totalisation-safe manifold interface. -/
noncomputable def totalisationSafe_conjugationDerivativeAt (g : G) :
    TotalisationSafety.ManifoldDerivativeAt (I := I) (I' := I)
      (fun h : G ↦ g * h * g⁻¹) (1 : G) :=
  TotalisationSafety.ManifoldDerivativeAt.ofMDifferentiableAt
    (totalisationGuard_conjugation_mdifferentiableAt (I := I) g)


/-- The exact missing hypothesis required to know that the second `mfderiv` in `leftHessian` is
not Mathlib's zero fallback.  The current development deliberately leaves the theorem establishing
this property from smoothness as part of the open second-order manifold-calculus boundary. -/
def LeftHessianDifferentiabilityAt (f : G → ℝ) (g : G) : Prop :=
  MDifferentiableAt I 𝓘(ℝ, E →L[ℝ] ℝ)
    (leftDifferential (I := I) f) g

/-- Supplying the explicit boundary hypothesis selects the genuine derivative branch and packages
it using `TotalisationSafety.ManifoldDerivativeAt`. -/
noncomputable def totalisationSafe_leftHessianDerivativeAt
    {f : G → ℝ} {g : G} (h : LeftHessianDifferentiabilityAt (I := I) f g) :
    TotalisationSafety.ManifoldDerivativeAt
      (I := I) (I' := 𝓘(ℝ, E →L[ℝ] ℝ))
      (leftDifferential (I := I) f) g :=
  TotalisationSafety.ManifoldDerivativeAt.ofMDifferentiableAt h

end LieGroupGuards

end CompactLieHeatKernel
