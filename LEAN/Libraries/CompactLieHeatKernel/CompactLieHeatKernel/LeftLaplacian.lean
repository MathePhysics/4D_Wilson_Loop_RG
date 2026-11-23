import CompactLieHeatKernel.InvariantMetric
import CompactLieHeatKernel.CanonicalContraction
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# A basis-free left-invariant second-order operator

For a smooth Lie group, let `V = T_1 G`.  In this development the chosen inner product is carried by
the model vector space `E`.  Mathlib deliberately keeps `TangentSpace` non-reducible, so all
contractions are performed in `E` after the explicit equivalence
`leftTranslationModelEquiv : E ≃L[ℝ] T_gG`.

The left differential of a scalar function at `g` is the ordinary manifold differential pulled
back along this explicit left-translation equivalence:

`d_L f(g) : E →L[ℝ] ℝ`.

Differentiate the map `g ↦ d_L f(g)` and pull back the new tangent direction once more by left
translation.  The target tangent space of the derivative is explicitly cast back to the normed
vector space `E →L[ℝ] ℝ`.  This yields a continuous bilinear form on `E`.  Contracting it with the
canonical covariant tensor gives a basis-free second-order operator.

The theorem `leftLaplacian_eq_sum_leftHessian` proves basis independence immediately.  The next
calculus lemma, not yet included, is to identify the diagonal term with the iterated left-invariant
derivative.  Once that is proved, the theorem becomes the desired formula
`Δ_G f = ∑_a X_a^2 f` in model coordinates for every orthonormal basis of `E`.
-/

noncomputable section

open Bundle
open scoped Manifold BigOperators ContDiff

namespace CompactLieHeatKernel

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G]

/-- The differential of `f` expressed in model coordinates using the left trivialisation.  The
postcomposition by `NormedSpace.fromTangentSpace` is essential: the tangent space of the scalar target is
not reducible to `ℝ` by typeclass inference. -/
def leftDifferential (f : G → ℝ) (g : G) : E →L[ℝ] ℝ := by
  let d : TangentSpace I g →L[ℝ] TangentSpace 𝓘(ℝ) (f g) :=
    mfderiv I 𝓘(ℝ) f g -- totalisation-audit: allow reviewed boundary: mfderiv is genuine only under MDifferentiableAt; smooth-function guard is recorded in TotalisationAudit
  let out : TangentSpace 𝓘(ℝ) (f g) ≃L[ℝ] ℝ :=
    NormedSpace.fromTangentSpace (f g)
  exact (out : TangentSpace 𝓘(ℝ) (f g) →L[ℝ] ℝ).comp
    (d.comp (leftTranslationModelEquiv (I := I) g : E →L[ℝ] TangentSpace I g))

/-- Directional derivative in the left-invariant direction represented by `v : E`. -/
def leftDerivativeAlong (v : E) (f : G → ℝ) (g : G) : ℝ :=
  leftDifferential (I := I) f g v

/-- The derivative of the left differential, again expressed in left-trivialised model
coordinates.  This is a continuous bilinear map on `E`. -/
def leftHessian (f : G → ℝ) (g : G) : E →L[ℝ] E →L[ℝ] ℝ := by
  let d :
      TangentSpace I g →L[ℝ]
        TangentSpace 𝓘(ℝ, E →L[ℝ] ℝ) (leftDifferential (I := I) f g) :=
    mfderiv I 𝓘(ℝ, E →L[ℝ] ℝ) -- totalisation-audit: allow reviewed boundary: non-junk branch requires the explicit leftHessian differentiability obligation in TotalisationAudit
      (leftDifferential (I := I) f) g
  let out :
      TangentSpace 𝓘(ℝ, E →L[ℝ] ℝ) (leftDifferential (I := I) f g) ≃L[ℝ]
        (E →L[ℝ] ℝ) :=
    NormedSpace.fromTangentSpace (leftDifferential (I := I) f g)
  exact (out :
      TangentSpace 𝓘(ℝ, E →L[ℝ] ℝ) (leftDifferential (I := I) f g) →L[ℝ]
        (E →L[ℝ] ℝ)).comp
    (d.comp (leftTranslationModelEquiv (I := I) g : E →L[ℝ] TangentSpace I g))

variable [FiniteDimensional ℝ E]

/-- The basis-free candidate for the left-invariant Laplacian. -/
def leftLaplacian (f : G → ℝ) (g : G) : ℝ :=
  contractDiagonal (leftHessian (I := I) f g)

/-- Formula for `leftLaplacian` in an arbitrary orthonormal basis of the model Lie algebra `E`.
This theorem is the formal basis-independence statement. -/
theorem leftLaplacian_eq_sum_leftHessian
    {ι : Type*} [Fintype ι]
    (f : G → ℝ) (g : G) (e : OrthonormalBasis ι ℝ E) :
    leftLaplacian (I := I) f g = ∑ i, leftHessian (I := I) f g (e i) (e i) := by
  exact contractDiagonal_eq_sum (leftHessian (I := I) f g) e

/-- Basis independence written directly as equality of the two coordinate sums. -/
theorem leftHessian_sum_orthonormalBasis_independent
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : G → ℝ) (g : G)
    (e : OrthonormalBasis ι ℝ E)
    (d : OrthonormalBasis κ ℝ E) :
    (∑ i, leftHessian (I := I) f g (e i) (e i)) =
      ∑ j, leftHessian (I := I) f g (d j) (d j) := by
  exact sum_diagonal_orthonormalBasis_independent (leftHessian (I := I) f g) e d

end CompactLieHeatKernel
