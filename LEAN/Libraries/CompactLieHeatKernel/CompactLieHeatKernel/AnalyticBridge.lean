import CompactLieHeatKernel.LaplacianGeneratorBridge
import CompactLieHeatKernel.CompactManifoldTheorem
import CompactLieHeatKernel.GroupHeatKernel
import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-!
# The analytic bridge: generator, semigroup and smooth kernel

This file places points 3 and 4 in one formal object.  It deliberately does not assert an existence
theorem: current mathlib supplies densely-defined operators and their adjoints, but not the
Friedrichs/spectral-semigroup theorem plus compact-manifold heat-kernel regularity needed to build
this object from `leftLaplacian`.

Once an instance of `HeatSemigroupKernelBridge` is constructed, the analytic output needed by the
finite-lattice Yang--Mills formalisation is available as theorem-level data: a self-adjoint Markov
semigroup on L² and a smooth strictly positive transition density satisfying Chapman--Kolmogorov.
-/

noncomputable section

open MeasureTheory
open scoped Manifold ContDiff ENNReal NNReal

namespace CompactLieHeatKernel

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H}
    {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [MeasurableSpace G]
    [BorelSpace G] [CompactSpace G] [SecondCountableTopology G] [NormalSpace G] [Group G] [LieGroup I ∞ G]
    {μ : Measure G} [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [μ.WeaklyRegular]

/-- Forget the smooth/group structure and retain only measurable heat-kernel data. -/
def groupKernelMeasurableData (K : GroupHeatKernelData I G μ) : MeasurableHeatKernelData μ :=
  K.toSmoothHeatKernelData.toContinuousHeatKernelData.toMeasurableHeatKernelData

/-- Action of a heat density on an ordinary real-valued function. -/
def kernelAction (K : MeasurableHeatKernelData μ) (t : ℝ≥0) (f : G → ℝ) (x : G) : ℝ :=
  ∫ y, K.density t x y * f y ∂μ -- totalisation-audit: allow continuous compact test functions in the bridge give the intended integrable branch

/-- Compatibility between the L² semigroup and its smooth heat-kernel density.

The equality is required only on continuous functions, whose image in L² is dense on the compact
space by `ContinuousMap.toLp_denseRange`.  This is enough to identify a bounded L² operator
uniquely. -/
structure HeatSemigroupKernelBridge where
  generatorSemigroup : SelfAdjointMarkovGenerator μ
  laplacianGenerator : LaplacianGeneratorBridge (I := I) (G := G) generatorSemigroup
  kernel : GroupHeatKernelData I G μ
  represents_on_continuous : ∀ t : ℝ≥0, t ≠ 0 → ∀ f : C(G, ℝ),
    ((generatorSemigroup.semigroup.op t
        ((ContinuousMap.toLp (E := ℝ) 2 μ ℝ) f) : RealL2 μ) : G → ℝ) =ᵐ[μ]
      kernelAction (groupKernelMeasurableData kernel) t f

namespace HeatSemigroupKernelBridge

omit [SecondCountableTopology G] in
/-- Continuous functions form a dense test core for identifying each bounded time-slice of the
L² semigroup. -/
theorem continuous_toL2_denseRange (_B : HeatSemigroupKernelBridge (I := I) (G := G) (μ := μ)) :
    DenseRange (ContinuousMap.toLp (E := ℝ) 2 μ ℝ : C(G, ℝ) →L[ℝ] RealL2 μ) := by
  simpa using
    (ContinuousMap.toLp_denseRange (E := ℝ) (μ := μ) (𝕜 := ℝ) (p := (2 : ℝ≥0∞))
      (by norm_num))

omit [SecondCountableTopology G] [NormalSpace G] [μ.WeaklyRegular] in
/-- The unbounded generator occurring in the bridge has dense domain for free from its
self-adjointness. -/
theorem dense_generator_domain (B : HeatSemigroupKernelBridge (I := I) (G := G) (μ := μ)) :
    Dense (B.generatorSemigroup.generator.domain : Set (RealL2 μ)) :=
  B.generatorSemigroup.dense_generator_domain

end HeatSemigroupKernelBridge

section RegularisationConstructor

variable [T2Space G] [LocallyCompactSpace G] [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]

/-- Lie-group regularisation data: the compact-manifold smoothing datum together with the two
translation symmetries forced by a bi-invariant Laplacian. -/
structure GroupRegularisationData
    (A : SelfAdjointMarkovGenerator μ) (F : FellerLift A.semigroup)
    extends CompactManifoldRegularisationData (I := I) A.semigroup F where
  leftInvariant : ∀ t : ℝ≥0, t ≠ 0 → ∀ a x y,
    density t (a * x) (a * y) = density t x y
  rightInvariant : ∀ t : ℝ≥0, t ≠ 0 → ∀ a x y,
    density t (x * a) (y * a) = density t x y

namespace GroupRegularisationData

variable {A : SelfAdjointMarkovGenerator μ} {F : FellerLift A.semigroup}

/-- The compact-manifold theorem plus translation invariance gives the complete group heat-kernel
structure. -/
def toGroupHeatKernelData (R : GroupRegularisationData (I := I) A F) :
    GroupHeatKernelData I G μ where
  toSmoothHeatKernelData :=
    R.toCompactManifoldRegularisationData.toSmoothHeatKernelData
  leftInvariant := R.leftInvariant
  rightInvariant := R.rightInvariant

omit [FiniteDimensional ℝ E] [NormalSpace G] [μ.WeaklyRegular] in
@[simp]
theorem toGroupHeatKernelData_density (R : GroupRegularisationData (I := I) A F)
    (t : ℝ≥0) (x y : G) :
    R.toGroupHeatKernelData.density t x y = R.density t x y :=
  rfl

end GroupRegularisationData

namespace HeatSemigroupKernelBridge

/-- Construct the old generator/kernel bridge from the sharper v0.3 regularisation boundary.
The representation field is no longer independent: it follows from the Feller lift's L²
compatibility and the pointwise kernel representation. -/
def ofRegularisation
    (A : SelfAdjointMarkovGenerator μ)
    (L : LaplacianGeneratorBridge (I := I) (G := G) A)
    (F : FellerLift A.semigroup)
    (R : GroupRegularisationData (I := I) A F) :
    HeatSemigroupKernelBridge (I := I) (G := G) (μ := μ) where
  generatorSemigroup := A
  laplacianGenerator := L
  kernel := R.toGroupHeatKernelData
  represents_on_continuous := by
    intro t ht f
    rw [← F.compatible t f]
    refine (ContinuousMap.coeFn_toLp
      (p := (2 : ℝ≥0∞)) (μ := μ) (𝕜 := ℝ) (F.op t f)).trans ?_
    exact Filter.Eventually.of_forall fun x => by
      simpa [kernelAction, groupKernelMeasurableData] using R.represents t ht f x

end HeatSemigroupKernelBridge
end RegularisationConstructor

end CompactLieHeatKernel
