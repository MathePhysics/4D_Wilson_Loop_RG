import KatoRellich.Basic

/-!
# Quadratic forms on a Hilbert space

Reed–Simon I, §VIII.6, pp. 276–277.  A quadratic form on a Hilbert space `H` is a sesquilinear
map `q : Q(q) × Q(q) → 𝕜` on a dense subspace `Q(q)`, the form domain; `q(·, ψ)` is conjugate
linear and `q(φ, ·)` is linear, which is also mathlib's convention for the inner product.  A
semibounded form `q(ψ, ψ) ≥ -M ‖ψ‖²` is closed if `Q(q)` is complete in the norm
`‖ψ‖₊₁ = √(q(ψ, ψ) + (M + 1) ‖ψ‖²)`.  The scalar field is any `RCLike 𝕜`.

## Main definitions

* `KatoRellich.QuadForm 𝕜 E`: a densely defined sesquilinear form
  (Reed–Simon I, §VIII.6, p. 276).
* `KatoRellich.QuadForm.IsSymmetric q`: `q(φ, ψ) = conj q(ψ, φ)` (p. 276).
* `KatoRellich.QuadForm.IsSemibounded q M`: `q(φ, φ) ≥ -M ‖φ‖²`, stated for the real part
  (p. 276).
* `KatoRellich.QuadForm.plusOneNorm q M`: the norm `‖·‖₊₁` (p. 277).
* `KatoRellich.QuadForm.IsClosed q M`: every `‖·‖₊₁`-Cauchy sequence in `Q(q)` converges in
  `‖·‖₊₁` to an element of `Q(q)` (p. 277).  This is completeness of `Q(q)` under `‖·‖₊₁`,
  stated with explicit sequences so that no auxiliary normed type appears in the statement.
* `KatoRellich.QuadForm.IsFormOf q M T`: `q` is the quadratic form of the operator `T`; see
  below.
* `KatoRellich.QuadForm.FormSpace q M hq hM`: a copy of `Q(q)` carrying the inner product
  `(φ, ψ)₊₁ = q(φ, ψ) + (M + 1) ⟪φ, ψ⟫` (p. 277), for `q` symmetric (`hq`) and semibounded with
  constant `M` (`hM`).  Its norm is `‖·‖₊₁` (`FormSpace.norm_eq`), it dominates the norm of `E`
  (`FormSpace.norm_toDomain_le`), and it is complete when `q` is closed
  (`FormSpace.completeSpace`).

## The quadratic form of an operator

Reed–Simon (p. 277, Example 2) define the quadratic form of a semibounded self-adjoint operator
`A` through the spectral theorem, which mathlib does not have for unbounded operators.  We use
the following spectral-free characterisation, `IsFormOf q M T`:

* `D(T) ⊆ Q(q)`;
* `q(φ, ψ) = ⟪φ, T ψ⟫` for `φ ∈ Q(q)` and `ψ ∈ D(T)`;
* `D(T)` is dense in `Q(q)` for `‖·‖₊₁`, i.e. `D(T)` is a form core for `q`.

These are the facts from which Reed–Simon's own proof of Theorem VIII.15 (p. 279) concludes
that `q` "is the quadratic form associated to" the operator: `(φ, A ψ) = q(φ, ψ)`, and `D(A)` is
`‖·‖₊₁`-dense in `Q(q)`.  Given the spectral theorem, this agrees with Reed–Simon's notion.  The
form `q_A` of a semibounded self-adjoint `A` is closed, has `D(A)` as a form core (Reed–Simon,
p. 278: any operator core for `A` is a form core for `q_A`, Problem 16), and satisfies
`q_A(φ, ψ) = (φ, A ψ)` for `φ ∈ Q(q_A)`, `ψ ∈ D(A)`.  Conversely, if `q` is closed and
`IsFormOf q M A` holds, then `q` and `q_A` are closed forms that agree on the common core
`D(A)`, hence they are equal.
-/

noncomputable section

open scoped InnerProductSpace ComplexConjugate

namespace KatoRellich

/-- A **quadratic form** on `E` (Reed–Simon I, §VIII.6, p. 276): a dense subspace `domain`, the
form domain `Q(q)`, and a map `form : Q(q) × Q(q) → 𝕜` that is conjugate linear in the first
argument and linear in the second. -/
structure QuadForm (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] where
  /-- The form domain `Q(q)`. -/
  domain : Submodule 𝕜 E
  /-- The form domain is dense. -/
  dense_domain : Dense (domain : Set E)
  /-- The sesquilinear form `q(φ, ψ)`, conjugate linear in `φ` and linear in `ψ`. -/
  form : domain →ₗ⋆[𝕜] domain →ₗ[𝕜] 𝕜

namespace QuadForm

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- `q` is **symmetric**: `q(φ, ψ) = conj q(ψ, φ)` (Reed–Simon I, §VIII.6, p. 276). -/
def IsSymmetric (q : QuadForm 𝕜 E) : Prop :=
  ∀ φ ψ : q.domain, q.form φ ψ = conj (q.form ψ φ)

/-- `q` is **semibounded** with constant `M`: `q(φ, φ) ≥ -M ‖φ‖²` (Reed–Simon I, §VIII.6,
p. 276).  The inequality is stated for the real part; for a symmetric form `q(φ, φ)` is real. -/
def IsSemibounded (q : QuadForm 𝕜 E) (M : ℝ) : Prop :=
  ∀ φ : q.domain, -M * ‖(φ : E)‖ ^ 2 ≤ RCLike.re (q.form φ φ)

/-- The norm `‖ψ‖₊₁ = √(q(ψ, ψ) + (M + 1) ‖ψ‖²)` on the form domain (Reed–Simon I, §VIII.6,
p. 277).  It is a norm when `q` is symmetric and semibounded with constant `M`. -/
def plusOneNorm (q : QuadForm 𝕜 E) (M : ℝ) (ψ : q.domain) : ℝ :=
  Real.sqrt (RCLike.re (q.form ψ ψ) + (M + 1) * ‖(ψ : E)‖ ^ 2)

/-- `q` is **closed** (Reed–Simon I, §VIII.6, p. 277): the form domain is complete for the norm
`‖·‖₊₁`.  Stated explicitly: every `‖·‖₊₁`-Cauchy sequence in `Q(q)` converges in `‖·‖₊₁` to an
element of `Q(q)`. -/
def IsClosed (q : QuadForm 𝕜 E) (M : ℝ) : Prop :=
  ∀ u : ℕ → q.domain,
    (∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, q.plusOneNorm M (u m - u n) < ε) →
      ∃ φ : q.domain, ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, q.plusOneNorm M (u n - φ) < ε

/-- `q` is **the quadratic form of** the operator `T`: `D(T) ⊆ Q(q)`, `q(φ, ψ) = ⟪φ, T ψ⟫` for
`φ ∈ Q(q)` and `ψ ∈ D(T)`, and `D(T)` is a form core for `q`, that is, dense in `Q(q)` for the
norm `‖·‖₊₁`.  See the module docstring for the relation with Reed–Simon's definition. -/
structure IsFormOf (q : QuadForm 𝕜 E) (M : ℝ) (T : E →ₗ.[𝕜] E) : Prop where
  /-- `D(T) ⊆ Q(q)`. -/
  domain_le : T.domain ≤ q.domain
  /-- `q(φ, ψ) = ⟪φ, T ψ⟫` for `φ ∈ Q(q)` and `ψ ∈ D(T)`. -/
  eq_inner : ∀ (φ : q.domain) (ψ : T.domain),
    q.form φ ⟨ψ, domain_le ψ.2⟩ = ⟪(φ : E), T ψ⟫_𝕜
  /-- `D(T)` is a form core: it is dense in `Q(q)` for `‖·‖₊₁`. -/
  core : ∀ ψ : q.domain, ∀ ε > 0, ∃ φ : T.domain,
    q.plusOneNorm M (ψ - ⟨φ, domain_le φ.2⟩) < ε

variable (q : QuadForm 𝕜 E) (M : ℝ)

/-- For a semibounded form, `‖ψ‖² ≤ re q(ψ, ψ) + (M + 1) ‖ψ‖²`. -/
theorem norm_sq_le (hM : q.IsSemibounded M) (ψ : q.domain) :
    ‖(ψ : E)‖ ^ 2 ≤ RCLike.re (q.form ψ ψ) + (M + 1) * ‖(ψ : E)‖ ^ 2 := by
  have := hM ψ
  nlinarith

/-- `‖ψ‖₊₁² = re q(ψ, ψ) + (M + 1) ‖ψ‖²` for a semibounded form. -/
theorem plusOneNorm_sq (hM : q.IsSemibounded M) (ψ : q.domain) :
    q.plusOneNorm M ψ ^ 2 = RCLike.re (q.form ψ ψ) + (M + 1) * ‖(ψ : E)‖ ^ 2 :=
  Real.sq_sqrt ((sq_nonneg _).trans (q.norm_sq_le M hM ψ))

/-- The Hilbert space norm is dominated by `‖·‖₊₁`: `‖ψ‖ ≤ ‖ψ‖₊₁`. -/
theorem norm_le_plusOneNorm (hM : q.IsSemibounded M) (ψ : q.domain) :
    ‖(ψ : E)‖ ≤ q.plusOneNorm M ψ :=
  Real.le_sqrt_of_sq_le (q.norm_sq_le M hM ψ)

/-! ### The Hilbert space `(Q(q), (·, ·)₊₁)` -/

/-- The form domain `Q(q)` as a separate type, to carry the inner product
`(φ, ψ)₊₁ = q(φ, ψ) + (M + 1) ⟪φ, ψ⟫` of Reed–Simon I, §VIII.6, p. 277, whose norm is
`‖·‖₊₁`.  The hypotheses that `q` is symmetric and semibounded are parameters, so that the
inner-product-space instance is unambiguous and no second norm is put on `q.domain` itself. -/
@[ext]
structure FormSpace (q : QuadForm 𝕜 E) (M : ℝ) (hq : q.IsSymmetric) (hM : q.IsSemibounded M)
    where
  /-- The underlying element of the form domain. -/
  toDomain : q.domain

namespace FormSpace

variable {q M} {hq : q.IsSymmetric} {hM : q.IsSemibounded M}

variable (q M hq hM) in
/-- The canonical equivalence with the form domain. -/
@[simps]
def equiv : FormSpace q M hq hM ≃ q.domain where
  toFun := toDomain
  invFun := fun u => ⟨u⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- Zero, transported from the form domain. -/
instance : Zero (FormSpace q M hq hM) := (equiv q M hq hM).zero
/-- Addition, transported from the form domain. -/
instance : Add (FormSpace q M hq hM) := (equiv q M hq hM).add
/-- Negation, transported from the form domain. -/
instance : Neg (FormSpace q M hq hM) := (equiv q M hq hM).Neg
/-- Subtraction, transported from the form domain. -/
instance : Sub (FormSpace q M hq hM) := (equiv q M hq hM).sub
/-- Scalar multiplication, transported from the form domain. -/
instance : SMul 𝕜 (FormSpace q M hq hM) := (equiv q M hq hM).smul 𝕜

/-- The additive group structure, transported from the form domain. -/
instance : AddCommGroup (FormSpace q M hq hM) := (equiv q M hq hM).addCommGroup

variable (q M hq hM) in
/-- The additive equivalence with the form domain. -/
def addEquiv : FormSpace q M hq hM ≃+ q.domain where
  toEquiv := equiv q M hq hM
  map_add' _ _ := rfl

/-- The module structure, transported from the form domain. -/
instance : Module 𝕜 (FormSpace q M hq hM) := (addEquiv q M hq hM).module 𝕜

/-- `toDomain` preserves zero. -/
@[simp]
theorem toDomain_zero : (0 : FormSpace q M hq hM).toDomain = 0 := rfl

/-- `toDomain` preserves addition. -/
@[simp]
theorem toDomain_add (u v : FormSpace q M hq hM) : (u + v).toDomain = u.toDomain + v.toDomain :=
  rfl

/-- `toDomain` preserves subtraction. -/
@[simp]
theorem toDomain_sub (u v : FormSpace q M hq hM) : (u - v).toDomain = u.toDomain - v.toDomain :=
  rfl

/-- `toDomain` preserves scalar multiplication. -/
@[simp]
theorem toDomain_smul (c : 𝕜) (u : FormSpace q M hq hM) : (c • u).toDomain = c • u.toDomain :=
  rfl

variable (q M hq hM) in
/-- The inner product `(φ, ψ)₊₁ = q(φ, ψ) + (M + 1) ⟪φ, ψ⟫` as an inner product space core. -/
@[instance_reducible]
def core : InnerProductSpace.Core 𝕜 (FormSpace q M hq hM) where
  inner u v := q.form u.toDomain v.toDomain +
    ((M + 1 : ℝ) : 𝕜) * ⟪(u.toDomain : E), (v.toDomain : E)⟫_𝕜
  conj_inner_symm u v := by
    rw [map_add, map_mul, RCLike.conj_ofReal, inner_conj_symm, ← hq]
  re_inner_nonneg u := by
    rw [map_add, RCLike.re_ofReal_mul, inner_self_eq_norm_sq]
    exact (sq_nonneg _).trans (q.norm_sq_le M hM u.toDomain)
  add_left u v w := by
    change q.form (u.toDomain + v.toDomain) w.toDomain +
        ((M + 1 : ℝ) : 𝕜) * ⟪((u.toDomain + v.toDomain : q.domain) : E), (w.toDomain : E)⟫_𝕜 =
      (q.form u.toDomain w.toDomain + ((M + 1 : ℝ) : 𝕜) * ⟪(u.toDomain : E), (w.toDomain : E)⟫_𝕜) +
      (q.form v.toDomain w.toDomain + ((M + 1 : ℝ) : 𝕜) * ⟪(v.toDomain : E), (w.toDomain : E)⟫_𝕜)
    rw [map_add, LinearMap.add_apply, Submodule.coe_add, inner_add_left]
    ring
  smul_left u v c := by
    change q.form (c • u.toDomain) v.toDomain +
        ((M + 1 : ℝ) : 𝕜) * ⟪((c • u.toDomain : q.domain) : E), (v.toDomain : E)⟫_𝕜 =
      conj c *
        (q.form u.toDomain v.toDomain + ((M + 1 : ℝ) : 𝕜) * ⟪(u.toDomain : E), (v.toDomain : E)⟫_𝕜)
    rw [map_smulₛₗ, LinearMap.smul_apply, Submodule.coe_smul, inner_smul_left, smul_eq_mul]
    ring
  definite u hu := by
    have hre := congrArg RCLike.re hu
    rw [map_add, RCLike.re_ofReal_mul, inner_self_eq_norm_sq, map_zero] at hre
    have h := q.norm_sq_le M hM u.toDomain
    have h0 : ‖(u.toDomain : E)‖ = 0 := by nlinarith [norm_nonneg (u.toDomain : E)]
    ext
    simpa using h0

/-- The norm on `FormSpace q M hq hM`, generated by `(·, ·)₊₁`. -/
@[instance_reducible]
instance instNormedAddCommGroup : NormedAddCommGroup (FormSpace q M hq hM) :=
  @InnerProductSpace.Core.toNormedAddCommGroup 𝕜 (FormSpace q M hq hM) _ _ _ (core q M hq hM)

/-- The inner product space structure given by `(·, ·)₊₁`. -/
@[instance_reducible]
instance instInnerProductSpace : InnerProductSpace 𝕜 (FormSpace q M hq hM) :=
  InnerProductSpace.ofCore (core q M hq hM).toCore

/-- The inner product of `FormSpace q M hq hM` is `(φ, ψ)₊₁ = q(φ, ψ) + (M + 1) ⟪φ, ψ⟫`. -/
theorem inner_def (u v : FormSpace q M hq hM) :
    ⟪u, v⟫_𝕜 = q.form u.toDomain v.toDomain +
      ((M + 1 : ℝ) : 𝕜) * ⟪(u.toDomain : E), (v.toDomain : E)⟫_𝕜 :=
  rfl

/-- `re (u, u)₊₁ = re q(u, u) + (M + 1) ‖u‖²`. -/
theorem re_inner_self (u : FormSpace q M hq hM) :
    RCLike.re ⟪u, u⟫_𝕜 =
      RCLike.re (q.form u.toDomain u.toDomain) + (M + 1) * ‖(u.toDomain : E)‖ ^ 2 := by
  rw [inner_def, map_add, RCLike.re_ofReal_mul, inner_self_eq_norm_sq]

/-- The norm of `FormSpace q M hq hM` is `‖·‖₊₁`. -/
theorem norm_eq (u : FormSpace q M hq hM) : ‖u‖ = q.plusOneNorm M u.toDomain := by
  rw [plusOneNorm, ← re_inner_self, inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]

/-- The Hilbert space norm is dominated by the norm of `FormSpace q M hq hM`. -/
theorem norm_toDomain_le (u : FormSpace q M hq hM) : ‖(u.toDomain : E)‖ ≤ ‖u‖ := by
  rw [norm_eq]
  exact q.norm_le_plusOneNorm M hM u.toDomain

/-- A closed form gives a complete space `(Q(q), (·, ·)₊₁)`. -/
theorem completeSpace (hc : q.IsClosed M) : CompleteSpace (FormSpace q M hq hM) := by
  refine UniformSpace.complete_of_cauchySeq_tendsto fun u hu => ?_
  obtain ⟨φ, hφ⟩ := hc (fun n => (u n).toDomain) fun ε hε => by
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hu ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    have h := hN m hm n hn
    rw [dist_eq_norm, norm_eq] at h
    exact h
  refine ⟨⟨φ⟩, Metric.tendsto_atTop.mpr fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := hφ ε hε
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_eq_norm, norm_eq]
  exact hN n hn

variable (q M hq hM) in
/-- The inclusion of `(Q(q), (·, ·)₊₁)` into `E`, a linear map of norm at most one. -/
def toAmbient : FormSpace q M hq hM →L[𝕜] E :=
  LinearMap.mkContinuous
    { toFun := fun u => (u.toDomain : E)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 fun u => by
      rw [one_mul]
      exact norm_toDomain_le u

/-- The inclusion `toAmbient` maps `u` to its underlying vector. -/
@[simp]
theorem toAmbient_apply (u : FormSpace q M hq hM) : toAmbient q M hq hM u = (u.toDomain : E) :=
  rfl

end FormSpace

end QuadForm

end KatoRellich
