import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpOrder
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Self-adjoint Markov semigroups on L²

This file fixes the operator-theoretic target for the compact Lie group heat semigroup.

The heat semigroup is represented directly on the real Hilbert space `Lp ℝ 2 μ`.  We record the
properties needed later rather than introducing a merely algebraic semigroup:

* the semigroup law and identity at time zero;
* contraction in the L² norm;
* symmetry of each bounded operator, hence self-adjointness in the Hilbert-space sense;
* strong continuity;
* positivity preservation and preservation of the constant-one vector.

The infinitesimal generator is represented with mathlib's `LinearPMap`, i.e. as an honest densely
defined operator.  The generator relation is expressed by the right derivative at time zero.
This makes the precise missing theorem visible: one must construct a self-adjoint dissipative
`LinearPMap` from the group Laplacian and then prove that it generates the semigroup below.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace CompactLieHeatKernel

variable {α : Type*} [MeasurableSpace α]

/-- The real Hilbert space `L²(α, μ)`. -/
abbrev RealL2 (μ : Measure α) := MeasureTheory.Lp ℝ 2 μ

/-- The constant-one vector in `L²` for a finite measure. -/
def oneL2 (μ : Measure α) [IsFiniteMeasure μ] : RealL2 μ :=
  indicatorConstLp 2 MeasurableSet.univ (measure_ne_top μ Set.univ) (1 : ℝ)

/-- A strongly continuous symmetric Markov contraction semigroup on real `L²`.

For a bounded operator on a real Hilbert space, the displayed `symmetric` identity is exactly the
self-adjointness property.  It is stated at the inner-product level because this is the form used
throughout the heat-kernel argument and avoids coupling the basic semigroup API to the `Star`
instance on continuous linear maps.
-/
structure L2SelfAdjointMarkovSemigroup (μ : Measure α) [IsProbabilityMeasure μ] where
  /-- The time-`t` operator. -/
  op : ℝ≥0 → RealL2 μ →L[ℝ] RealL2 μ
  /-- Time zero acts as the identity. -/
  op_zero : op 0 = ContinuousLinearMap.id ℝ (RealL2 μ)
  /-- Semigroup law. -/
  op_add : ∀ s t, op (s + t) = (op s).comp (op t)
  /-- L² contraction. -/
  contractive : ∀ t f, ‖op t f‖ ≤ ‖f‖
  /-- Hilbert-space symmetry of every time slice. -/
  symmetric : ∀ t f g, inner ℝ (op t f) g = inner ℝ f (op t g)
  /-- Strong continuity in time. -/
  stronglyContinuous : ∀ f, Continuous fun t : ℝ≥0 ↦ op t f
  /-- Positivity preservation in the natural order on real `L²`. -/
  map_nonneg : ∀ t f, 0 ≤ f → 0 ≤ op t f
  /-- Markov property: the constant-one vector is fixed. -/
  map_one : ∀ t, op t (oneL2 μ) = oneL2 μ

namespace L2SelfAdjointMarkovSemigroup

variable {μ : Measure α} [IsProbabilityMeasure μ]

@[simp]
theorem op_zero_apply (S : L2SelfAdjointMarkovSemigroup μ) (f : RealL2 μ) :
    S.op 0 f = f := by
  rw [S.op_zero]
  simp

/-- Time slices commute.  This follows from the one-parameter semigroup law, not from
self-adjointness. -/
theorem op_comm (S : L2SelfAdjointMarkovSemigroup μ) (s t : ℝ≥0) :
    (S.op s).comp (S.op t) = (S.op t).comp (S.op s) := by
  rw [← S.op_add, add_comm, S.op_add]

/-- The generator relation at a vector: the right difference quotient converges strongly. -/
def HasGenerator (S : L2SelfAdjointMarkovSemigroup μ) (f Af : RealL2 μ) : Prop :=
  Tendsto
    (fun t : ℝ≥0 ↦ ((t : ℝ)⁻¹) • (S.op t f - f)) -- totalisation-audit: allow generator limit uses nhdsWithin 0 (Ioi 0), so only strictly positive times are observed
    (nhdsWithin 0 (Ioi 0)) (𝓝 Af)

end L2SelfAdjointMarkovSemigroup

/-- A self-adjoint dissipative generator together with its strongly continuous Markov semigroup.

The generator is an actual `LinearPMap`.  In the intended application it is the closure/Friedrichs
realisation of `Δ_G / 2` on a smooth core.  The sign convention is the probabilistic one:
`⟪A f, f⟫ ≤ 0` and the semigroup is `exp(t A)`.
-/
structure SelfAdjointMarkovGenerator (μ : Measure α) [IsProbabilityMeasure μ] where
  semigroup : L2SelfAdjointMarkovSemigroup μ
  generator : RealL2 μ →ₗ.[ℝ] RealL2 μ
  generator_selfAdjoint : IsSelfAdjoint generator
  generator_dissipative : ∀ f : generator.domain,
    inner ℝ (generator f) (f : RealL2 μ) ≤ 0
  generator_limit : ∀ f : generator.domain,
    semigroup.HasGenerator (f : RealL2 μ) (generator f)

namespace SelfAdjointMarkovGenerator

variable {μ : Measure α} [IsProbabilityMeasure μ]

/-- A self-adjoint unbounded generator has dense domain by mathlib's `LinearPMap` theory. -/
theorem dense_generator_domain (A : SelfAdjointMarkovGenerator μ) :
    Dense (A.generator.domain : Set (RealL2 μ)) :=
  A.generator_selfAdjoint.dense_domain

end SelfAdjointMarkovGenerator

end CompactLieHeatKernel
