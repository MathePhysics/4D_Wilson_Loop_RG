import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Topology.Algebra.Module.LinearPMap

/-!
# Symmetric operators, relative bounds and lower bounds

Vocabulary for unbounded operators on a Hilbert space, following Reed–Simon.  Operators are
mathlib's partially defined linear maps `E →ₗ.[𝕜] E`.  The adjoint is `LinearPMap.adjoint`
(written `T†`), and self-adjointness is mathlib's `IsSelfAdjoint`, which unfolds to `T† = T`
(`LinearPMap.isSelfAdjoint_def`); this is Reed–Simon's `T = T*`.  The scalar field is any
`RCLike 𝕜`, so the complex Hilbert spaces of Reed–Simon and real Hilbert spaces are both covered.

## Main definitions

* `KatoRellich.IsSymmetric T`: `T` is densely defined and `⟪T x, y⟫ = ⟪x, T y⟫` for
  `x, y ∈ D(T)`.  Reed–Simon I, §VIII.2, p. 255, define a densely defined `T` to be symmetric if
  `T ⊆ T*`, and note that this is equivalent to the identity above.
* `KatoRellich.addScalar T z`: the operator `T + z`, with domain `D(T)`.
* `KatoRellich.IsRelBounded B A a b`: `D(A) ⊆ D(B)` and `‖B x‖ ≤ a ‖A x‖ + b ‖x‖` for
  `x ∈ D(A)`; this is (i)–(ii) of the definition of an `A`-bounded operator in Reed–Simon II,
  §X.2, p. 162, inequality (X.19a).
* `KatoRellich.IsBoundedBelow A M`: `M ‖x‖² ≤ re ⟪x, A x⟫` for `x ∈ D(A)`.

## Main results

* `KatoRellich.IsSymmetric.le_adjoint`: a symmetric operator is contained in its adjoint.
* `KatoRellich.IsSymmetric.of_isSelfAdjoint`: a self-adjoint operator is symmetric.
* `KatoRellich.IsSymmetric.add`: the sum of symmetric `A` and `B` with `D(A) ⊆ D(B)` is
  symmetric on `D(A)`.
-/

noncomputable section

open scoped InnerProductSpace ComplexConjugate

namespace KatoRellich

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- A **symmetric** operator: densely defined, with `⟪T x, y⟫ = ⟪x, T y⟫` on its domain
(Reed–Simon I, §VIII.2, p. 255). -/
structure IsSymmetric (T : E →ₗ.[𝕜] E) : Prop where
  dense_domain : Dense (T.domain : Set E)
  isFormalAdjoint : T.IsFormalAdjoint T

/-- The operator `T + z`, that is `x ↦ T x + z • x` on `D(T)`. -/
def addScalar (T : E →ₗ.[𝕜] E) (z : 𝕜) : E →ₗ.[𝕜] E where
  domain := T.domain
  toFun := T.toFun + z • T.domain.subtype

@[simp]
theorem addScalar_domain (T : E →ₗ.[𝕜] E) (z : 𝕜) : (addScalar T z).domain = T.domain :=
  rfl

theorem addScalar_apply (T : E →ₗ.[𝕜] E) (z : 𝕜) (x : (addScalar T z).domain) :
    addScalar T z x = T x + z • (x : E) :=
  rfl

/-- `B` is **`A`-bounded** with constants `a` and `b`: `D(A) ⊆ D(B)` and
`‖B x‖ ≤ a ‖A x‖ + b ‖x‖` for every `x ∈ D(A)` (Reed–Simon II, §X.2, p. 162, (X.19a)).  The
relative bound of Reed–Simon is the infimum of the admissible `a`, so "relative bound `< 1`"
means `IsRelBounded B A a b` for some `a < 1` and some `b`. -/
structure IsRelBounded (B A : E →ₗ.[𝕜] E) (a b : ℝ) : Prop where
  domain_le : A.domain ≤ B.domain
  bound : ∀ x : A.domain, ‖B ⟨x, domain_le x.2⟩‖ ≤ a * ‖A x‖ + b * ‖(x : E)‖

/-- `A` is **bounded below** by `M`: `M ‖x‖² ≤ re ⟪x, A x⟫` for every `x ∈ D(A)`.  For a
symmetric operator `⟪x, A x⟫` is real, so this is Reed–Simon's `(x, A x) ≥ M ‖x‖²`. -/
def IsBoundedBelow (A : E →ₗ.[𝕜] E) (M : ℝ) : Prop :=
  ∀ x : A.domain, M * ‖(x : E)‖ ^ 2 ≤ RCLike.re ⟪(x : E), A x⟫_𝕜

namespace IsSymmetric

variable {T : E →ₗ.[𝕜] E}

/-- A symmetric operator is contained in its adjoint. -/
theorem le_adjoint [CompleteSpace E] (hT : IsSymmetric T) : T ≤ T.adjoint :=
  LinearPMap.IsFormalAdjoint.le_adjoint hT.dense_domain hT.isFormalAdjoint

end IsSymmetric

/-- A self-adjoint operator is symmetric. -/
theorem IsSymmetric.of_isSelfAdjoint [CompleteSpace E] {T : E →ₗ.[𝕜] E}
    (hT : IsSelfAdjoint T) : IsSymmetric T := by
  have hdense := hT.dense_domain
  refine ⟨hdense, ?_⟩
  have h := LinearPMap.adjoint_isFormalAdjoint hdense
  rw [LinearPMap.isSelfAdjoint_def.mp hT] at h
  exact h

/-- The domain of `A + B` is `D(A)` when `D(A) ⊆ D(B)`. -/
theorem add_domain_of_le {A B : E →ₗ.[𝕜] E} (h : A.domain ≤ B.domain) :
    (A + B).domain = A.domain :=
  inf_eq_left.mpr h

/-- The sum of a symmetric `A` and a formally symmetric `B` with `D(A) ⊆ D(B)` is symmetric on
`D(A)`. -/
theorem IsSymmetric.add {A B : E →ₗ.[𝕜] E} (hA : IsSymmetric A) (hB : B.IsFormalAdjoint B)
    (h : A.domain ≤ B.domain) : IsSymmetric (A + B) := by
  refine ⟨?_, ?_⟩
  · rw [add_domain_of_le h]
    exact hA.dense_domain
  · intro x y
    rw [LinearPMap.add_apply, LinearPMap.add_apply, inner_add_left, inner_add_right]
    congr 1
    · exact hA.isFormalAdjoint ⟨x, x.2.1⟩ ⟨y, y.2.1⟩
    · exact hB ⟨x, x.2.2⟩ ⟨y, y.2.2⟩

/-- A symmetric operator plus a real scalar is symmetric. -/
theorem IsSymmetric.addScalar_ofReal {T : E →ₗ.[𝕜] E} (hT : IsSymmetric T) (t : ℝ) :
    IsSymmetric (addScalar T (t : 𝕜)) := by
  refine ⟨hT.dense_domain, ?_⟩
  intro x y
  rw [addScalar_apply, addScalar_apply, inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right, RCLike.conj_ofReal, hT.isFormalAdjoint x y]

end KatoRellich
