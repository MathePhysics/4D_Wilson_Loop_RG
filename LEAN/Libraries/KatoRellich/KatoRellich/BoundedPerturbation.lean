import KatoRellich.Basic

/-!
# Bounded perturbations of self-adjoint operators

For a densely defined `A` and a bounded, everywhere defined `V`, the adjoint of `A + V` on `D(A)`
is `A† + V†` on `D(A†)`.  Hence `A + V` is self-adjoint on `D(A)` whenever `A` and `V` are.

This is the special case of the Kato–Rellich theorem (Reed–Simon II, Theorem X.12, p. 162) with
relative bound `0`: a bounded `V` satisfies `‖V x‖ ≤ 0 · ‖A x‖ + ‖V‖ ‖x‖`.  Unlike the general
theorem, it needs neither complex scalars nor a lower bound, because the adjoint can be computed
directly: `x ↦ ⟪y, V x⟫` is always continuous, so `y ∈ D((A + V)†)` if and only if `y ∈ D(A†)`.

## Main results

* `KatoRellich.addBounded A V`: the operator `A + V` with domain `D(A)`.
* `KatoRellich.add_toPMap_eq_addBounded`: it agrees with mathlib's sum `A + V|_H`.
* `KatoRellich.adjoint_addBounded`: `(A + V)† = A† + V†`.
* `KatoRellich.isSelfAdjoint_addBounded`: `A + V` is self-adjoint for self-adjoint `A` and `V`.
* `KatoRellich.isRelBounded_toPMap`: a bounded `V` is `A`-bounded with constants `0` and `‖V‖`.
-/

noncomputable section

open scoped InnerProductSpace

namespace KatoRellich

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The operator `A + V` with domain `D(A)`, for a bounded, everywhere defined `V`. -/
def addBounded (A : E →ₗ.[𝕜] E) (V : E →L[𝕜] E) : E →ₗ.[𝕜] E where
  domain := A.domain
  toFun := A.toFun + (V : E →ₗ[𝕜] E).comp A.domain.subtype

@[simp]
theorem addBounded_domain (A : E →ₗ.[𝕜] E) (V : E →L[𝕜] E) :
    (addBounded A V).domain = A.domain :=
  rfl

theorem addBounded_apply (A : E →ₗ.[𝕜] E) (V : E →L[𝕜] E) (x : (addBounded A V).domain) :
    addBounded A V x = A x + V (x : E) :=
  rfl

/-- `addBounded A V` is mathlib's sum of `A` and the restriction of `V` to `H`. -/
theorem add_toPMap_eq_addBounded (A : E →ₗ.[𝕜] E) (V : E →L[𝕜] E) :
    A + (V : E →ₗ[𝕜] E).toPMap ⊤ = addBounded A V :=
  LinearPMap.ext (by simp [LinearPMap.add_domain]) (fun _ _ _ => rfl)

/-- A bounded `V` is `A`-bounded with constants `0` and `‖V‖`. -/
theorem isRelBounded_toPMap (A : E →ₗ.[𝕜] E) (V : E →L[𝕜] E) :
    IsRelBounded ((V : E →ₗ[𝕜] E).toPMap ⊤) A 0 ‖V‖ where
  domain_le := le_top
  bound x := by
    rw [zero_mul, zero_add]
    exact V.le_opNorm (x : E)

variable [CompleteSpace E]

/-- **The adjoint of a bounded perturbation**: `(A + V)† = A† + V†`, both sides on the domain
`D(A†)`. -/
theorem adjoint_addBounded {A : E →ₗ.[𝕜] E} (hA : Dense (A.domain : Set E)) (V : E →L[𝕜] E) :
    (addBounded A V).adjoint = addBounded A.adjoint (ContinuousLinearMap.adjoint V) := by
  have hdom : (addBounded A V).adjoint.domain = A.adjoint.domain := by
    ext y
    rw [LinearPMap.mem_adjoint_domain_iff, LinearPMap.mem_adjoint_domain_iff]
    have hV : Continuous fun x : A.domain => ⟪y, V (x : E)⟫_𝕜 := by fun_prop
    constructor
    · intro h
      refine (h.sub hV).congr fun x => ?_
      change ⟪y, A x + V (x : E)⟫_𝕜 - ⟪y, V (x : E)⟫_𝕜 = ⟪y, A x⟫_𝕜
      rw [inner_add_right, add_sub_cancel_right]
    · intro h
      refine (h.add hV).congr fun x => ?_
      change ⟪y, A x⟫_𝕜 + ⟪y, V (x : E)⟫_𝕜 = ⟪y, A x + V (x : E)⟫_𝕜
      rw [inner_add_right]
  refine LinearPMap.ext hdom fun y hy hy' => ?_
  change (addBounded A V).adjoint ⟨y, hy⟩ =
    A.adjoint ⟨y, hy'⟩ + ContinuousLinearMap.adjoint V y
  refine LinearPMap.adjoint_apply_eq (T := addBounded A V) hA ⟨y, hy⟩ fun x => ?_
  have h1 := LinearPMap.adjoint_isFormalAdjoint hA ⟨y, hy'⟩ x
  have h2 := ContinuousLinearMap.adjoint_inner_left V (x : E) y
  change ⟪A.adjoint ⟨y, hy'⟩ + ContinuousLinearMap.adjoint V y, (x : E)⟫_𝕜 =
    ⟪y, A x + V (x : E)⟫_𝕜
  rw [inner_add_left, inner_add_right, h2]
  exact congrArg (· + ⟪y, V (x : E)⟫_𝕜) h1

/-- **Bounded perturbations preserve self-adjointness**: if `A` is self-adjoint and `V` is a
bounded self-adjoint operator, then `A + V` is self-adjoint on `D(A)`.  This is Reed–Simon II,
Theorem X.12 (Kato–Rellich), p. 162, in the case of relative bound `0`. -/
theorem isSelfAdjoint_addBounded {A : E →ₗ.[𝕜] E} (hA : IsSelfAdjoint A) {V : E →L[𝕜] E}
    (hV : IsSelfAdjoint V) : IsSelfAdjoint (addBounded A V) := by
  rw [LinearPMap.isSelfAdjoint_def, adjoint_addBounded hA.dense_domain, hV.adjoint_eq,
    LinearPMap.isSelfAdjoint_def.mp hA]

/-- The same statement for mathlib's sum `A + V|_H`. -/
theorem isSelfAdjoint_add_toPMap {A : E →ₗ.[𝕜] E} (hA : IsSelfAdjoint A) {V : E →L[𝕜] E}
    (hV : IsSelfAdjoint V) : IsSelfAdjoint (A + (V : E →ₗ[𝕜] E).toPMap ⊤) := by
  rw [add_toPMap_eq_addBounded]
  exact isSelfAdjoint_addBounded hA hV

/-- `A - V` is self-adjoint on `D(A)` for self-adjoint `A` and bounded self-adjoint `V`.  This is
the form used for the block-diagonal operator `H_diag = A₁ - V` of the Helffer–Sjöstrand axiom in
`FiniteVolumeYM2Phi42`. -/
theorem isSelfAdjoint_addBounded_neg {A : E →ₗ.[𝕜] E} (hA : IsSelfAdjoint A) {V : E →L[𝕜] E}
    (hV : IsSelfAdjoint V) : IsSelfAdjoint (addBounded A (-V)) :=
  isSelfAdjoint_addBounded hA hV.neg

end KatoRellich
