import Mathlib

/-!
# Literature axiom: the differential of a continuous orthogonal representation

**This file contains an axiom.  It is imported temporarily from the literature because the result
is classical; it is not proved in Lean.**  The root module `LieGroupExponential` does not import
this file, so `import LieGroupExponential` stays axiom-free.  Every declaration that depends on the
axiom shows `LieGroupExponential.Literature.exists_isDifferential` under `#print axioms`.  The
ledger is `LITERATURE_AXIOMS.md` at the library root.

## Setting

A *matrix Lie group* in the sense of Hall is a closed subgroup of `GL(n)` (Definition 1.4).  Here
`G` is a subgroup of `GL (Fin n) ℝ` that is closed.  Its Lie algebra is
`matrixLieAlgebra G = {X | exp (t X) ∈ G for every real t}` (Definition 3.18).  A
`ContinuousOrthogonalAction` of `G` on a real inner product space `V` is the structure
`OrthogonalAction` of `FiniteVolumeYM2Phi42` — a map to the linear isometries of `V` which is a
group homomorphism — together with continuity into the operator-norm topology.  That is a
finite-dimensional real representation of `G` in the sense of Definition 4.1, whose image happens
to lie in the orthogonal group.

## Statement

`exists_isDifferential`: there is a real-linear map `L` from the `n × n` matrices to the operators
on `V` such that `ρ(exp X) = exp (L X)` for every `X` in the Lie algebra.

`SmoothOrthogonalAction` bundles the action with such an `L`, and
`ContinuousOrthogonalAction.toSmooth` builds one from any continuous action through the axiom.
What is then proved without the axiom:

* `iso_exp_smul`: along the one-parameter subgroup, `ρ(exp (t X)) = exp (t • L X)`;
* `hasDerivAt_iso_exp`: `L X` is the derivative at `t = 0` of `t ↦ ρ(exp (t X))`, which is Hall's
  formula for the differential and shows `L` is determined on the Lie algebra;
* `norm_exp_smul_diff_le`: `‖exp (t • L X)‖ ≤ 1`, because it is an isometry.

## Why the statement is exactly Hall's

The axiom quantifies over closed subgroups of `GL (Fin n) ℝ`, finite-dimensional real inner product
spaces `V` and continuous actions by linear isometries.  Each hypothesis is one of Hall's.

* **Closedness.**  `GL(n, ℝ)` is closed in `GL(n, ℂ)`, since a limit of real matrices is real.  So a
  closed subgroup of `GL(n, ℝ)` is a matrix Lie group in the sense of Definition 1.4.  Mathlib
  topologises `GL (Fin n) ℝ` as units, through `u ↦ (u, u⁻¹)`.  Inversion is continuous on
  invertible matrices, so this is the subspace topology from the matrices, which is the one Hall
  uses.  "Closed" and "continuous" therefore mean what they mean in the book.
* **The Lie algebra.**  Hall's `𝔤` consists of the complex `X` with `e^{tX} ∈ G` for all real `t`.
  Such an `X` is real, being the derivative at `0` of a real curve, so `𝔤 = matrixLieAlgebra G`.
  Mathlib's `NormedSpace.exp` on real matrices is the exponential series, as in Hall's
  Definition 2.2.
* **The representation.**  `V` is finite-dimensional and `ρ` is a continuous homomorphism into the
  invertible operators, which is Definition 4.1.  The case `V = 0` is excluded in the book but is
  trivially true here: both sides of `ρ(exp X) = exp (L X)` are the zero operator.
* **Linearity on all matrices.**  Hall's `π` is real-linear on `𝔤`, which is a real subspace
  (Theorem 3.20).  A linear map on a subspace extends linearly to the whole space, so asking for `L`
  on all `n × n` matrices asks for no more than the book gives.

The axiom is a single `Prop`, an existence statement, so it cannot contradict itself.

## References

B. C. Hall, *Lie Groups, Lie Algebras, and Representations: An Elementary Introduction*, 2nd ed.,
Graduate Texts in Mathematics 222, Springer, 2015, doi:10.1007/978-3-319-13467-3.  Checked
against the text on 2026-09-18; page numbers are those printed in the book:

* Definition 1.4, p. 4: a matrix Lie group is a closed subgroup of `GL(n; ℂ)`, topologised as a
  subset of `M_n(ℂ)`;
* Definition 1.18, p. 22: a Lie group homomorphism is a continuous group homomorphism;
* Definition 3.18 and Theorem 3.20, p. 56: the Lie algebra `{X : e^{tX} ∈ G for all real t}` is a
  real subspace, closed under the bracket;
* Theorem 3.28, p. 60: a Lie group homomorphism `Φ : G → H` has a unique real-linear
  `φ : 𝔤 → 𝔥` with `Φ(e^X) = e^{φ(X)}`, and `φ(X) = d/dt Φ(e^{tX})|_{t=0}`;
* Corollary 3.50, p. 72: every continuous homomorphism between matrix Lie groups is smooth;
* Definition 4.1, p. 77, and Proposition 4.4, p. 79: for a finite-dimensional real or complex
  representation `Π` there is a unique Lie algebra representation `π` with `Π(e^X) = e^{π(X)}` for
  all `X ∈ 𝔤`, computed as `π(X) = d/dt Π(e^{tX})|_{t=0}`.

The axiom is Proposition 4.4 for real representations, together with Theorem 3.20, which lets the
differential be extended from `𝔤` to all matrices.
-/

noncomputable section

open NormedSpace
open scoped RealInnerProductSpace

namespace LieGroupExponential.Literature

variable {n : ℕ}

/-- The Lie algebra of a subgroup of `GL(n, ℝ)` (Hall, Definition 3.18): the matrices whose whole
one-parameter subgroup lies in the group. -/
def matrixLieAlgebra (G : Subgroup (GL (Fin n) ℝ)) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  {X | ∀ t : ℝ, ∃ g ∈ G, ((g : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) = exp (t • X)}

theorem smul_mem_matrixLieAlgebra {G : Subgroup (GL (Fin n) ℝ)} {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : X ∈ matrixLieAlgebra G) (s : ℝ) : s • X ∈ matrixLieAlgebra G := by
  intro t
  obtain ⟨g, hg, hgX⟩ := hX (t * s)
  exact ⟨g, hg, by rw [hgX, smul_smul]⟩

/-- A continuous orthogonal action of a subgroup of `GL(n, ℝ)`: the fields of `OrthogonalAction`
together with continuity into the operator-norm topology.  This is a finite-dimensional real
representation in the sense of Hall, Definition 4.1, when `V` is finite-dimensional. -/
structure ContinuousOrthogonalAction (G : Subgroup (GL (Fin n) ℝ)) (V : Type*)
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] where
  /-- The action of a group element, as a linear isometry. -/
  iso : G → V ≃ₗᵢ[ℝ] V
  one_apply : ∀ v : V, iso 1 v = v
  mul_apply : ∀ (g h : G) (v : V), iso (g * h) v = iso g (iso h v)
  continuous_iso : Continuous fun g : G => ((iso g : V ≃ₗᵢ[ℝ] V) : V →L[ℝ] V)

namespace ContinuousOrthogonalAction

variable {G : Subgroup (GL (Fin n) ℝ)} {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- `L` is a differential of the action: it intertwines the matrix exponential on the Lie algebra
with the operator exponential (Hall, Theorem 3.28 and Proposition 4.4). -/
def IsDifferential (ρ : ContinuousOrthogonalAction G V)
    (L : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] (V →L[ℝ] V)) : Prop :=
  ∀ X ∈ matrixLieAlgebra G, ∀ g : G,
    ((g : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) = exp X →
      ((ρ.iso g : V ≃ₗᵢ[ℝ] V) : V →L[ℝ] V) = exp (L X)

end ContinuousOrthogonalAction

/-- **Literature axiom, imported temporarily because the result is classical.**

A continuous action of a closed subgroup `G` of `GL(n, ℝ)` on a finite-dimensional real inner
product space by linear isometries has a differential: a real-linear `L` with
`ρ(exp X) = exp (L X)` for every `X` in the Lie algebra of `G`.

Reference (checked against the text): B. C. Hall, *Lie Groups, Lie Algebras, and Representations*,
2nd ed., GTM 222, Springer, 2015, Proposition 4.4, p. 79 (with Theorem 3.28, p. 60), applied to the
real representation `ρ`; the extension of the differential from the Lie algebra to all matrices uses
Theorem 3.20, p. 56.  The module docstring explains why each hypothesis is Hall's. -/
axiom exists_isDifferential {n : ℕ} (G : Subgroup (GL (Fin n) ℝ))
    (hG : IsClosed (G : Set (GL (Fin n) ℝ)))
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (ρ : ContinuousOrthogonalAction G V) :
    ∃ L : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] (V →L[ℝ] V), ρ.IsDifferential L

/-- An orthogonal action with its smooth structure: a continuous orthogonal action together with a
differential intertwining the two exponentials. -/
structure SmoothOrthogonalAction (G : Subgroup (GL (Fin n) ℝ)) (V : Type*)
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] extends ContinuousOrthogonalAction G V where
  /-- The differential at the identity, extended linearly to all matrices. -/
  diff : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] (V →L[ℝ] V)
  isDifferential : toContinuousOrthogonalAction.IsDifferential diff

/-- The smooth structure of a continuous orthogonal action of a closed matrix group, chosen through
the literature axiom `exists_isDifferential`.  The differential is unique on the Lie algebra
(`SmoothOrthogonalAction.hasDerivAt_iso_exp`); off it the choice is immaterial. -/
def ContinuousOrthogonalAction.toSmooth {G : Subgroup (GL (Fin n) ℝ)}
    (hG : IsClosed (G : Set (GL (Fin n) ℝ)))
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (ρ : ContinuousOrthogonalAction G V) : SmoothOrthogonalAction G V where
  toContinuousOrthogonalAction := ρ
  diff := Classical.choose (exists_isDifferential G hG ρ) -- totalisation-audit: allow the chosen map is used only through `Classical.choose_spec`, i.e. through the intertwining property
  isDifferential := Classical.choose_spec (exists_isDifferential G hG ρ) -- totalisation-audit: allow this is the specification of the choice above

namespace SmoothOrthogonalAction

variable {G : Subgroup (GL (Fin n) ℝ)} {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Along a one-parameter subgroup the action is the exponential of a multiple of the
differential. -/
theorem iso_exp_smul (ρ : SmoothOrthogonalAction G V) {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : X ∈ matrixLieAlgebra G) (t : ℝ) (g : G)
    (hg : ((g : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) = exp (t • X)) :
    ((ρ.iso g : V ≃ₗᵢ[ℝ] V) : V →L[ℝ] V) = exp (t • ρ.diff X) := by
  rw [ρ.isDifferential (t • X) (smul_mem_matrixLieAlgebra hX t) g hg, map_smul]

/-- The operators of the action along a one-parameter subgroup have norm at most one. -/
theorem norm_exp_smul_diff_le (ρ : SmoothOrthogonalAction G V) {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : X ∈ matrixLieAlgebra G) (t : ℝ) : ‖exp (t • ρ.diff X)‖ ≤ 1 := by
  obtain ⟨g, hgG, hg⟩ := hX t
  rw [← ρ.iso_exp_smul hX t ⟨g, hgG⟩ hg]
  exact (ρ.iso ⟨g, hgG⟩).toLinearIsometry.norm_toContinuousLinearMap_le

variable [FiniteDimensional ℝ V]

/-- The differential is the derivative of the action along the one-parameter subgroup at the
identity (Hall, Theorem 3.28(3) and Proposition 4.4).  In particular it is determined on the Lie
algebra. -/
theorem hasDerivAt_iso_exp (ρ : SmoothOrthogonalAction G V) {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : X ∈ matrixLieAlgebra G) (γ : ℝ → G)
    (hγ : ∀ t, ((γ t : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) = exp (t • X)) :
    HasDerivAt (fun t => ((ρ.iso (γ t) : V ≃ₗᵢ[ℝ] V) : V →L[ℝ] V)) (ρ.diff X) 0 := by
  have hfun : (fun t => ((ρ.iso (γ t) : V ≃ₗᵢ[ℝ] V) : V →L[ℝ] V)) =
      fun t : ℝ => exp (t • ρ.diff X) :=
    funext fun t => ρ.iso_exp_smul hX t (γ t) (hγ t)
  rw [hfun]
  have h := hasDerivAt_exp_smul_const' (𝕂 := ℝ) (ρ.diff X) 0
  simpa using h

end SmoothOrthogonalAction

end LieGroupExponential.Literature
