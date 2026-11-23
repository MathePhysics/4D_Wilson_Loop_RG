import Mathlib.Geometry.Manifold.MFDeriv.Basic

/-!
# Manifold derivatives with witnesses

Mathlib's `mfderiv` and `mfderivWithin` are total: when the relevant manifold differentiability
hypothesis fails, the returned continuous linear map is the zero map.  This file provides
proof-carrying wrappers which expose a manifold derivative only together with a `HasMFDerivAt` or
`HasMFDerivWithinAt` witness.

The wrappers do not change Mathlib's definitions.  They make the intended mathematical domain part
of the data carried by downstream code.
-/

namespace TotalisationSafety

open Set
open scoped Manifold

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']

/-- A manifold derivative at a point, bundled with the proposition that it is the derivative. -/
structure ManifoldDerivativeAt (f : M → M') (x : M) where
  derivative : TangentSpace I x →L[𝕜] TangentSpace I' (f x)
  hasMFDerivAt : HasMFDerivAt I I' f x derivative

namespace ManifoldDerivativeAt

variable {f : M → M'} {x : M}

/-- A proof-carrying derivative can be constructed from an explicit differentiability witness.
The raw `mfderiv` occurs only inside this guarded constructor. -/
noncomputable def ofMDifferentiableAt
    (h : MDifferentiableAt I I' f x) : ManifoldDerivativeAt (I := I) (I' := I') f x where
  derivative := mfderiv I I' f x -- totalisation-audit: allow guarded internally by h : MDifferentiableAt
  hasMFDerivAt := h.hasMFDerivAt

/-- The derivative carried by the wrapper is the ambient `mfderiv`, now known to be on its genuine
branch. -/
theorem derivative_eq_mfderiv
    (D : ManifoldDerivativeAt (I := I) (I' := I') f x) :
    D.derivative = mfderiv I I' f x := by -- totalisation-audit: allow equality justified by D.hasMFDerivAt
  exact D.hasMFDerivAt.mfderiv.symm

/-- A proof-carrying derivative supplies manifold differentiability. -/
theorem mdifferentiableAt
    (D : ManifoldDerivativeAt (I := I) (I' := I') f x) :
    MDifferentiableAt I I' f x :=
  D.hasMFDerivAt.mdifferentiableAt

end ManifoldDerivativeAt

/-- A manifold derivative within a set, bundled with the proposition that it is the derivative.
No uniqueness assumption is hidden: if later arguments need uniqueness of a within-set derivative,
they must supply the corresponding `UniqueMDiffWithinAt` hypothesis explicitly. -/
structure ManifoldDerivativeWithinAt (f : M → M') (s : Set M) (x : M) where
  derivative : TangentSpace I x →L[𝕜] TangentSpace I' (f x)
  hasMFDerivWithinAt : HasMFDerivWithinAt I I' f s x derivative

namespace ManifoldDerivativeWithinAt

variable {f : M → M'} {s : Set M} {x : M}

/-- Construct a proof-carrying within-set derivative from an explicit differentiability witness. -/
noncomputable def ofMDifferentiableWithinAt
    (h : MDifferentiableWithinAt I I' f s x) :
    ManifoldDerivativeWithinAt (I := I) (I' := I') f s x where
  derivative := mfderivWithin I I' f s x -- totalisation-audit: allow guarded internally by h : MDifferentiableWithinAt
  hasMFDerivWithinAt := h.hasMFDerivWithinAt

/-- A proof-carrying within-set derivative supplies manifold differentiability within the set. -/
theorem mdifferentiableWithinAt
    (D : ManifoldDerivativeWithinAt (I := I) (I' := I') f s x) :
    MDifferentiableWithinAt I I' f s x :=
  D.hasMFDerivWithinAt.mdifferentiableWithinAt

end ManifoldDerivativeWithinAt

end TotalisationSafety
