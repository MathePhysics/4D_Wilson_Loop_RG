import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Topology.Order.Compact

/-!
# Positive heat-kernel densities

This file formalises the output expected from the missing compact-manifold heat-kernel theorem.
The central object is the density itself, rather than an opaque existence proposition.  This keeps
normalisation, symmetry, Chapman--Kolmogorov, continuity and strict positivity available to later
Yang--Mills arguments.

At positive time the density produces a genuine `ProbabilityTheory.Kernel` by taking the density
with respect to the reference probability measure.  No spectral or PDE existence theorem is
assumed here.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Manifold Topology ContDiff

namespace CompactLieHeatKernel

variable {X : Type*} [MeasurableSpace X]

/-- Measurable positive-time heat-kernel data relative to a reference probability measure.

The value at time zero is deliberately unconstrained: an honest heat kernel there is a Dirac mass,
not a density with respect to Haar measure.  Every analytic field below is therefore required only
for `t ≠ 0`.
-/
structure MeasurableHeatKernelData (μ : Measure X) [IsProbabilityMeasure μ] where
  density : ℝ≥0 → X → X → ℝ
  nonnegative : ∀ t, t ≠ 0 → ∀ x y, 0 ≤ density t x y
  strictlyPositive : ∀ t, t ≠ 0 → ∀ x y, 0 < density t x y
  measurable_density_ofReal : ∀ t, t ≠ 0 →
    Measurable (Function.uncurry fun x y ↦ ENNReal.ofReal (density t x y))
  mass_one : ∀ t, t ≠ 0 → ∀ x,
    ∫⁻ y, ENNReal.ofReal (density t x y) ∂μ = 1
  symmetric : ∀ t, t ≠ 0 → ∀ x y, density t x y = density t y x
  chapmanKolmogorov : ∀ s t, s ≠ 0 → t ≠ 0 → ∀ x z,
    ∫⁻ y, ENNReal.ofReal (density s x y) * ENNReal.ofReal (density t y z) ∂μ =
      ENNReal.ofReal (density (s + t) x z)

namespace MeasurableHeatKernelData

variable {μ : Measure X} [IsProbabilityMeasure μ]

/-- The nonnegative extended-real density used by `Measure.withDensity`.  This is reducible so
that measurability fields stated with the explicit `ENNReal.ofReal` formula elaborate without an
additional rewriting layer. -/
abbrev ennDensity (K : MeasurableHeatKernelData μ) (t : ℝ≥0) (x y : X) : ℝ≥0∞ :=
  ENNReal.ofReal (K.density t x y)

/-- Measurability of the bundled extended-real density. -/
theorem measurable_ennDensity (K : MeasurableHeatKernelData μ) (t : ℝ≥0) (ht : t ≠ 0) :
    Measurable (Function.uncurry (K.ennDensity t)) := by
  change Measurable (Function.uncurry (fun x y ↦ ENNReal.ofReal (K.density t x y)))
  exact K.measurable_density_ofReal t ht

/-- The positive-time transition kernel induced by the heat density. -/
def transitionKernel (K : MeasurableHeatKernelData μ) (t : ℝ≥0) : Kernel X X :=
  Kernel.withDensity (Kernel.const X μ) (K.ennDensity t)

/-- At a fixed starting point the transition law is exactly Haar/reference measure weighted by the
heat density. -/
theorem transitionKernel_apply (K : MeasurableHeatKernelData μ) (t : ℝ≥0) (ht : t ≠ 0) (x : X) :
    K.transitionKernel t x = μ.withDensity (K.ennDensity t x) := by
  rw [transitionKernel, Kernel.withDensity_apply (Kernel.const X μ)
    (K.measurable_ennDensity t ht) x, Kernel.const_apply]

/-- Positive-time transition kernels have total mass one. -/
theorem transitionKernel_univ (K : MeasurableHeatKernelData μ) (t : ℝ≥0) (ht : t ≠ 0)
    (x : X) : K.transitionKernel t x Set.univ = 1 := by
  rw [transitionKernel, Kernel.withDensity_apply' (Kernel.const X μ)
    (K.measurable_ennDensity t ht) x Set.univ]
  simp only [Kernel.const_apply, Measure.restrict_univ]
  simpa [ennDensity] using K.mass_one t ht x

/-- The density construction yields an actual Markov kernel at every positive time. -/
instance transitionKernel_isMarkov (K : MeasurableHeatKernelData μ) (t : ℝ≥0) [NeZero t] :
    IsMarkovKernel (K.transitionKernel t) where
  isProbabilityMeasure x := ⟨K.transitionKernel_univ t (NeZero.ne t) x⟩

end MeasurableHeatKernelData

variable [TopologicalSpace X]

/-- Continuous positive-time heat-kernel data. -/
structure ContinuousHeatKernelData (μ : Measure X) [IsProbabilityMeasure μ]
    extends MeasurableHeatKernelData μ where
  continuous_density : ∀ t, t ≠ 0 →
    Continuous (Function.uncurry (density t))

namespace ContinuousHeatKernelData

variable {μ : Measure X} [IsProbabilityMeasure μ]

/-- On a nonempty compact state space, strict positivity and continuity improve to a uniform
positive lower bound at each fixed positive time.  This is the compactness input behind the bridge
minorisation estimates used later in the Yang--Mills programme. -/
theorem exists_uniform_positive_lower_bound
    [CompactSpace X] [Nonempty X]
    (K : ContinuousHeatKernelData μ) (t : ℝ≥0) (ht : t ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ x y, c ≤ K.density t x y := by
  let f : X × X → ℝ := Function.uncurry (K.density t)
  obtain ⟨p, _hp, hpmin⟩ :=
    isCompact_univ.exists_isMinOn Set.univ_nonempty (K.continuous_density t ht).continuousOn
  refine ⟨f p, K.strictlyPositive t ht p.1 p.2, ?_⟩
  intro x y
  simpa [f] using hpmin (show (x, y) ∈ Set.univ by simp)

end ContinuousHeatKernelData

/-- Smooth positive-time heat-kernel data on a smooth manifold.

This is exactly the regularity output required in point 4.  Constructing this structure from the
Laplacian/semigroup is the remaining compact-manifold PDE theorem; once constructed, all fields are
available without further analytic interfaces.
-/
structure SmoothHeatKernelData
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [MeasurableSpace M]
    (μ : Measure M) [IsProbabilityMeasure μ]
    extends ContinuousHeatKernelData μ where
  smooth_density : ∀ t, t ≠ 0 →
    ContMDiff (I.prod I) 𝓘(ℝ) ∞ (Function.uncurry (density t))

end CompactLieHeatKernel
