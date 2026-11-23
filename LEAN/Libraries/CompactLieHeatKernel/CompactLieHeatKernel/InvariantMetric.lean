import Mathlib.Geometry.Manifold.GroupLieAlgebra
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian

/-!
# Invariant metrics on Lie groups: the left-trivialised candidate

This file starts the first analytic bridge needed for the compact-Lie-group heat-kernel
formalisation.

A subtlety in the current mathlib manifold API is essential here: `TangentSpace I g` is a
**non-reducible** type synonym of the model vector space.  Consequently, a norm or inner product on
the model space must not be recovered on a tangent space merely by unfolding definitions or by
typeclass search.

We instead use two mathematically meaningful maps.

* Left multiplication is a diffeomorphism, so its manifold derivative gives the intrinsic
  equivalence `T_1G ≃L T_gG`.
* The derivative of the actual manifold chart at the identity gives a genuine linear equivalence
  from `T_1G` to the chart model tangent space; `tangentSpaceCastModel` then exposes the underlying
  model vector space `E` explicitly.

Thus an inner product on the model vector space determines a chosen inner product on the Lie
algebra through the chosen manifold chart at the identity, and left translation transports it to
every tangent space.  The resulting pointwise form is symmetric and positive definite.  It is not
claimed to be canonical: Ad-invariance is recorded separately and is precisely the extra condition
needed for bi-invariance.
-/

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace CompactLieHeatKernel

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G]

/-- Left multiplication by a fixed group element, bundled as a smooth diffeomorphism. -/
def leftMulDiffeomorph (g : G) : G ≃ₘ⟮I, I⟯ G where
  toEquiv := Equiv.mulLeft g
  contMDiff_toFun := contMDiff_mul_left
  contMDiff_invFun := by
    simpa using (contMDiff_mul_left (I := I) (n := ∞) (G := G) (a := g⁻¹))

/-- Transport tangent spaces along an actual equality of base points.  Unlike the implementation-level
`tangentSpaceCast`, this helper carries the equality that makes the transport geometrically
legitimate. -/
def tangentSpaceEquivOfEq {x y : G} (h : x = y) :
    TangentSpace I x ≃L[ℝ] TangentSpace I y := by
  subst y
  exact ContinuousLinearEquiv.refl ℝ (TangentSpace I x)

/-- The differential of left multiplication by `g` at the identity.  The raw derivative lands in
`T_{g*1}G`; `tangentSpaceEquivOfEq` transports along the proved equality `g * 1 = g`. -/
def leftTranslationTangentEquiv (g : G) :
    GroupLieAlgebra I G ≃L[ℝ] TangentSpace I g := by
  change TangentSpace I (1 : G) ≃L[ℝ] TangentSpace I g
  let d :
      TangentSpace I (1 : G) ≃L[ℝ]
        TangentSpace I ((leftMulDiffeomorph (I := I) g) (1 : G)) :=
    (leftMulDiffeomorph (I := I) g).mfderivToContinuousLinearEquiv (by simp) (1 : G)
  have hg : ((leftMulDiffeomorph (I := I) g) (1 : G)) = g := by
    change g * (1 : G) = g
    exact mul_one g
  exact d.trans (tangentSpaceEquivOfEq (I := I) hg)

/-- The derivative of the manifold chart at `x`, followed by the explicit model-space cast.

`OpenPartialHomeomorph.MDifferentiable.mfderiv` is data-valued, so this construction does not
extract a continuous linear equivalence from the Prop-valued `ContinuousLinearMap.IsInvertible`.
The second factor is the foundational identification of the tangent space of the model space with
`E`. -/
def tangentChartModelEquiv (x : G) : TangentSpace I x ≃L[ℝ] E :=
  ((mdifferentiable_chart (I := I) x).mfderiv (ChartedSpace.mem_chart_source x)).trans
    (tangentSpaceCastModel (M := H) I ((chartAt H x) x))

/-- The chosen chart-coordinate realisation of the Lie algebra. -/
def lieAlgebraModelEquiv : GroupLieAlgebra I G ≃L[ℝ] E := by
  change TangentSpace I (1 : G) ≃L[ℝ] E
  exact tangentChartModelEquiv (I := I) (1 : G)

/-- Left translation written in the chart coordinates carrying the chosen inner product. -/
def leftTranslationModelEquiv (g : G) : E ≃L[ℝ] TangentSpace I g :=
  (lieAlgebraModelEquiv (I := I) (G := G)).symm.trans
    (leftTranslationTangentEquiv (I := I) g)

/-- Left trivialisation of the tangent bundle at a point, with values in the abstract Lie algebra. -/
def leftTrivialisation (g : G) :
    TangentSpace I g ≃L[ℝ] GroupLieAlgebra I G :=
  (leftTranslationTangentEquiv (I := I) g).symm

/-- Left trivialisation in the chosen chart coordinates on the Lie algebra. -/
def leftTrivialisationModel (g : G) : TangentSpace I g ≃L[ℝ] E :=
  (leftTranslationModelEquiv (I := I) g).symm

/-- The left-transported pointwise inner product. -/
def leftMetric (g : G) (v w : TangentSpace I g) : ℝ :=
  inner ℝ (leftTrivialisationModel (I := I) g v)
    (leftTrivialisationModel (I := I) g w)

@[simp]
theorem leftMetric_symm (g : G) (v w : TangentSpace I g) :
    leftMetric (I := I) g v w = leftMetric (I := I) g w v := by
  simpa only [leftMetric] using
    ((real_inner_comm (leftTrivialisationModel (I := I) g v)
      (leftTrivialisationModel (I := I) g w)).symm)

theorem leftMetric_pos (g : G) (v : TangentSpace I g) (hv : v ≠ 0) :
    0 < leftMetric (I := I) g v v := by
  rw [leftMetric]
  apply real_inner_self_pos.mpr
  intro h
  apply hv
  apply (leftTrivialisationModel (I := I) g).injective
  simpa using h

/-- Differential of conjugation by `g` at the identity, as an endomorphism of the abstract Lie
algebra.  The raw derivative lands in `T_{g*1*g⁻¹}G`; `tangentSpaceEquivOfEq` transports it
back to `T_1G` along the proved group equality. -/
def adjointDifferential (g : G) :
    GroupLieAlgebra I G →L[ℝ] GroupLieAlgebra I G := by
  change TangentSpace I (1 : G) →L[ℝ] TangentSpace I (1 : G)
  let c : G → G := fun h : G ↦ g * h * g⁻¹
  let d : TangentSpace I (1 : G) →L[ℝ] TangentSpace I (c (1 : G)) :=
    mfderiv I I c (1 : G) -- totalisation-audit: allow conjugation is smooth, so mfderiv is genuine; see TotalisationAudit
  have hc : c (1 : G) = (1 : G) := by
    simp [c]
  let targetCast : TangentSpace I (c (1 : G)) ≃L[ℝ] TangentSpace I (1 : G) :=
    tangentSpaceEquivOfEq (I := I) hc
  exact (targetCast : TangentSpace I (c (1 : G)) →L[ℝ] TangentSpace I (1 : G)).comp d

/-- The adjoint differential in the chosen chart coordinates carrying the inner product. -/
def adjointModelDifferential (g : G) : E →L[ℝ] E :=
  (lieAlgebraModelEquiv (I := I) (G := G) : GroupLieAlgebra I G →L[ℝ] E).comp
    ((adjointDifferential (I := I) g).comp
      ((lieAlgebraModelEquiv (I := I) (G := G)).symm : E →L[ℝ] GroupLieAlgebra I G))

/-- Ad-invariance of the chosen Lie-algebra inner product, written in the chart coordinates used to
carry the inner product. -/
def IsAdInvariantInnerProduct : Prop :=
  ∀ (g : G) (X Y : E),
    inner ℝ (adjointModelDifferential (I := I) g X)
        (adjointModelDifferential (I := I) g Y) = inner ℝ X Y

end CompactLieHeatKernel
