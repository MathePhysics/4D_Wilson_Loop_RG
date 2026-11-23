import CompactLieHeatKernel.LeftLaplacian
import CompactLieHeatKernel.L2Semigroup
import Mathlib.Geometry.Manifold.ContMDiffMap
import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-!
# Identifying the L² generator with the group Laplacian

This file isolates the exact output required from the Friedrichs/self-adjoint-realisation step.
The analytic generator must extend `Δ_G / 2` on smooth real-valued functions.  We package this
compatibility without assuming an existence theorem.

The definition is deliberately formulated using mathlib's bundled `C^∞` maps and its actual
`LinearPMap` generator.  Thus a future construction of the Friedrichs realisation can discharge
this structure directly.
-/

noncomputable section

open MeasureTheory
open scoped Manifold ContDiff

namespace CompactLieHeatKernel

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [MeasurableSpace G]
  [BorelSpace G] [CompactSpace G] [Group G] [LieGroup I ∞ G]
  {μ : Measure G} [IsProbabilityMeasure μ]

/-- A bundled smooth real-valued function on the Lie group. -/
abbrev SmoothRealFunction := C^∞⟮I, G; ℝ⟯

/-- Forget smoothness while retaining continuity. -/
def smoothToContinuous (f : SmoothRealFunction (I := I) (G := G)) : C(G, ℝ) :=
  ⟨f, f.contMDiff.continuous⟩

/-- The `L²` class of a smooth function on a compact probability space. -/
def smoothToL2 (f : SmoothRealFunction (I := I) (G := G)) : RealL2 μ :=
  (ContinuousMap.toLp (E := ℝ) 2 μ ℝ) (smoothToContinuous f)

/-- The probabilistic sign/normalisation convention for the heat generator. -/
def halfLeftLaplacian (f : SmoothRealFunction (I := I) (G := G)) (g : G) : ℝ :=
  (2 : ℝ)⁻¹ * leftLaplacian (I := I) (f : G → ℝ) g -- totalisation-audit: allow fixed scalar denominator 2 is nonzero; see TotalisationAudit

/-- Compatibility of an unbounded self-adjoint Markov generator with `Δ_G / 2` on the smooth core.

The `laplacian_memL2` field is kept explicit because continuity/L²-integrability of the basis-free
`leftLaplacian` will become a theorem only after the remaining second-order manifold-calculus lemma
from point 2 is proved. -/
structure LaplacianGeneratorBridge (A : SelfAdjointMarkovGenerator μ) where
  laplacian_memL2 : ∀ f : SmoothRealFunction (I := I) (G := G),
    MemLp (halfLeftLaplacian (I := I) f) 2 μ
  smooth_mem_domain : ∀ f : SmoothRealFunction (I := I) (G := G),
    smoothToL2 (μ := μ) f ∈ A.generator.domain
  generator_agrees : ∀ f : SmoothRealFunction (I := I) (G := G),
    A.generator ⟨smoothToL2 (μ := μ) f, smooth_mem_domain f⟩ =
      (laplacian_memL2 f).toLp (halfLeftLaplacian (I := I) f)

namespace LaplacianGeneratorBridge

variable {A : SelfAdjointMarkovGenerator μ}

/-- The smooth `L²` vectors included by the bridge are contained in the generator domain. -/
theorem smooth_range_subset_domain (B : LaplacianGeneratorBridge (I := I) (G := G) A) :
    Set.range (fun f : SmoothRealFunction (I := I) (G := G) ↦
      smoothToL2 (I := I) (μ := μ) f) ⊆ A.generator.domain := by
  rintro _ ⟨f, rfl⟩
  exact B.smooth_mem_domain f

end LaplacianGeneratorBridge

end CompactLieHeatKernel
