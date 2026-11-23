import KatoRellich.Criterion
import KatoRellich.QuadraticForm

/-!
# The operator of a closed semibounded quadratic form

Reed–Simon I, §VIII.6, Theorem VIII.15, p. 278: *if `q` is a closed semibounded quadratic form,
then `q` is the quadratic form of a unique self-adjoint operator.*  "The quadratic form of `T`"
is the spectral-free notion `KatoRellich.QuadForm.IsFormOf` (see
`KatoRellich/QuadraticForm.lean` for why it agrees with Reed–Simon's definition).

Reed–Simon note (p. 276) that a semibounded form on a complex Hilbert space is automatically
symmetric: `q(φ, φ) ∈ ℝ` for all `φ` implies symmetry by polarisation.  Here `IsSemibounded`
only bounds the real part and the scalars may be real, so symmetry is an explicit hypothesis
`IsSymmetric q`.

## Construction and proof

The operator `T = QuadForm.toOperator q` is defined as in Reed–Simon's proof:
`D(T) = {ψ ∈ Q(q) : φ ↦ q(φ, ψ) is represented by a vector η}`, `T ψ = η`, so that
`q(φ, ψ) = ⟪φ, T ψ⟫` for `φ ∈ Q(q)`, `ψ ∈ D(T)`; `η` is unique because `Q(q)` is dense.  It is
built from its graph, with no choice beyond the bundled bijection graph `≃` domain.

* By the Riesz lemma on the Hilbert space `(Q(q), (·, ·)₊₁)` (complete because `q` is closed),
  every `f ∈ E` is `(T + M + 1) ψ` for some `ψ ∈ D(T)`: `Ran(T + M + 1) = E`.
* `D(T)` is dense in `E`: if `g ⊥ D(T)` and `g = (T + M + 1) ψ`, then `0 = ⟪ψ, g⟫ = ‖ψ‖₊₁²`.
* `T` is symmetric because `q` is, so the basic criterion (Reed–Simon I, Theorem VIII.3, in
  the real-shift form `KatoRellich.isSelfAdjoint_of_range_addScalar_ofReal`) shows that `T` is
  self-adjoint.  Reed–Simon instead use the Hellinger–Toeplitz theorem and the spectral theorem
  at this step (p. 279).
* `D(T)` is a form core: a vector `(·, ·)₊₁`-orthogonal to `D(T)` is orthogonal to
  `Ran(T + M + 1) = E`.
* Uniqueness, left as a problem by Reed–Simon (p. 279): a self-adjoint `S` with `D(S) ⊆ Q(q)` and
  `q(φ, ψ) = ⟪φ, S ψ⟫` satisfies `S ⊆ T`, hence `T = T† ⊆ S† = S`
  (`KatoRellich.adjoint_le_adjoint`).

## Main results

* `KatoRellich.QuadForm.toOperator`: the operator of a quadratic form, with
  `mem_toOperator_domain_iff`, `form_toOperator` and `toOperator_apply_eq`.
* `KatoRellich.QuadForm.isSelfAdjoint_toOperator`, `isFormOf_toOperator`,
  `isBoundedBelow_toOperator`: `T` is self-adjoint, `q` is its form, and `T ≥ -M`.
* `KatoRellich.QuadForm.eq_toOperator_of_isSelfAdjoint`: uniqueness without the core condition.
* `KatoRellich.QuadForm.existsUnique_isSelfAdjoint_isFormOf`: Reed–Simon I, Theorem VIII.15.
* `KatoRellich.adjoint_le_adjoint`: `S ⊆ T` with `S` densely defined implies `T† ⊆ S†`.
-/

noncomputable section

open scoped InnerProductSpace ComplexConjugate

namespace KatoRellich

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Taking adjoints reverses inclusions: if `S ⊆ T` and `S` is densely defined, then
`T† ⊆ S†`. -/
theorem adjoint_le_adjoint {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    [CompleteSpace E] {S T : E →ₗ.[𝕜] F} (h : S ≤ T) (hS : Dense (S.domain : Set E)) :
    T.adjoint ≤ S.adjoint := by
  have hT : Dense (T.domain : Set E) := hS.mono h.1
  have key : ∀ (y : T.adjoint.domain) (x : S.domain),
      ⟪T.adjoint y, (x : E)⟫_𝕜 = ⟪(y : F), S x⟫_𝕜 := by
    intro y x
    have h1 := LinearPMap.adjoint_isFormalAdjoint hT y ⟨x, h.1 x.2⟩
    have h2 : S x = T ⟨x, h.1 x.2⟩ := h.2 rfl
    rw [h2]
    exact h1
  refine ⟨fun y hy => LinearPMap.mem_adjoint_domain_of_exists y
    ⟨T.adjoint ⟨y, hy⟩, key ⟨y, hy⟩⟩, ?_⟩
  intro y y' hyy'
  exact (LinearPMap.adjoint_apply_eq hS y' fun x => by rw [key y x, hyy']).symm

namespace QuadForm

variable (q : QuadForm 𝕜 E)

/-- Vectors are determined by their inner products with the dense form domain. -/
theorem eq_of_forall_inner_eq {a b : E}
    (h : ∀ φ : q.domain, ⟪(φ : E), a⟫_𝕜 = ⟪(φ : E), b⟫_𝕜) : a = b :=
  q.dense_domain.eq_of_inner_right 𝕜 fun v hv => h ⟨v, hv⟩

/-- The graph of the operator of `q`: the pairs `(ψ, η)` with `ψ ∈ Q(q)` and
`q(φ, ψ) = ⟪φ, η⟫` for every `φ ∈ Q(q)`. -/
def reprGraph : Submodule 𝕜 (E × E) where
  carrier := {p | ∃ hp : p.1 ∈ q.domain, ∀ φ : q.domain, q.form φ ⟨p.1, hp⟩ = ⟪(φ : E), p.2⟫_𝕜}
  add_mem' := by
    rintro p p' ⟨hp, h⟩ ⟨hp', h'⟩
    refine ⟨q.domain.add_mem hp hp', fun φ => ?_⟩
    have hsum : (⟨(p + p').1, q.domain.add_mem hp hp'⟩ : q.domain) = ⟨p.1, hp⟩ + ⟨p'.1, hp'⟩ :=
      rfl
    rw [hsum, map_add, h, h', Prod.snd_add, inner_add_right]
  zero_mem' := by
    refine ⟨q.domain.zero_mem, fun φ => ?_⟩
    have h0 : (⟨(0 : E × E).1, q.domain.zero_mem⟩ : q.domain) = 0 := rfl
    rw [h0, map_zero, Prod.snd_zero, inner_zero_right]
  smul_mem' := by
    rintro c p ⟨hp, h⟩
    refine ⟨q.domain.smul_mem c hp, fun φ => ?_⟩
    have hs : (⟨(c • p).1, q.domain.smul_mem c hp⟩ : q.domain) = c • ⟨p.1, hp⟩ := rfl
    rw [hs, map_smul, h, Prod.smul_snd, inner_smul_right, smul_eq_mul]

/-- Membership in the graph of the operator of `q`. -/
theorem mem_reprGraph_iff {p : E × E} :
    p ∈ q.reprGraph ↔
      ∃ hp : p.1 ∈ q.domain, ∀ φ : q.domain, q.form φ ⟨p.1, hp⟩ = ⟪(φ : E), p.2⟫_𝕜 :=
  Iff.rfl

/-- The domain of the operator of `q`: the `ψ ∈ Q(q)` for which `φ ↦ q(φ, ψ)` is represented by
a vector, `q(φ, ψ) = ⟪φ, η⟫` for all `φ ∈ Q(q)`. -/
def reprDomain : Submodule 𝕜 E :=
  q.reprGraph.map (LinearMap.fst 𝕜 E E)

/-- Membership in the domain of the operator of `q`. -/
theorem mem_reprDomain_iff {x : E} :
    x ∈ q.reprDomain ↔
      ∃ hx : x ∈ q.domain, ∃ η : E, ∀ φ : q.domain, q.form φ ⟨x, hx⟩ = ⟪(φ : E), η⟫_𝕜 := by
  constructor
  · rintro ⟨p, ⟨hp, h⟩, rfl⟩
    exact ⟨hp, p.2, h⟩
  · rintro ⟨hx, η, h⟩
    exact ⟨(x, η), ⟨hx, h⟩, rfl⟩

/-- The projection of the graph onto the domain, `(ψ, η) ↦ ψ`, is bijective. -/
theorem bijective_reprGraph_fst :
    Function.Bijective ((LinearMap.fst 𝕜 E E).submoduleMap q.reprGraph) := by
  refine ⟨fun p p' hpp' => ?_, LinearMap.submoduleMap_surjective _ _⟩
  have h1 : (p : E × E).1 = (p' : E × E).1 := congrArg Subtype.val hpp'
  obtain ⟨hp, h⟩ := p.2
  obtain ⟨hp', h'⟩ := p'.2
  refine Subtype.ext (Prod.ext h1 (q.eq_of_forall_inner_eq fun φ => ?_))
  rw [← h, ← h']
  congr 2

/-- The graph of the operator of `q` is linearly equivalent to its domain. -/
def reprEquiv : q.reprGraph ≃ₗ[𝕜] q.reprDomain :=
  LinearEquiv.ofBijective _ q.bijective_reprGraph_fst

/-- **The operator of the form `q`** (Reed–Simon I, proof of Theorem VIII.15, p. 278):
`D(T) = {ψ ∈ Q(q) : φ ↦ q(φ, ψ) is represented by a vector η}` and `T ψ = η`, i.e.
`q(φ, ψ) = ⟪φ, T ψ⟫` for `φ ∈ Q(q)`.  The vector `η` is unique because `Q(q)` is dense. -/
def toOperator : E →ₗ.[𝕜] E where
  domain := q.reprDomain
  toFun := (LinearMap.snd 𝕜 E E).comp (q.reprGraph.subtype.comp q.reprEquiv.symm.toLinearMap)

/-- The domain of the operator of `q`. -/
@[simp]
theorem toOperator_domain : q.toOperator.domain = q.reprDomain :=
  rfl

/-- `x ∈ D(T)` iff `x ∈ Q(q)` and `φ ↦ q(φ, x)` is represented by a vector. -/
theorem mem_toOperator_domain_iff {x : E} :
    x ∈ q.toOperator.domain ↔
      ∃ hx : x ∈ q.domain, ∃ η : E, ∀ φ : q.domain, q.form φ ⟨x, hx⟩ = ⟪(φ : E), η⟫_𝕜 :=
  q.mem_reprDomain_iff

/-- The domain of the operator of `q` lies in the form domain. -/
theorem toOperator_domain_le : q.toOperator.domain ≤ q.domain := fun _ hx =>
  (q.mem_toOperator_domain_iff.mp hx).1

/-- If `x ∈ Q(q)` and `q(φ, x) = ⟪φ, η⟫` for all `φ ∈ Q(q)`, then `x ∈ D(T)`. -/
theorem mem_toOperator_domain_of_forall {x : E} (hx : x ∈ q.domain) (η : E)
    (h : ∀ φ : q.domain, q.form φ ⟨x, hx⟩ = ⟪(φ : E), η⟫_𝕜) : x ∈ q.toOperator.domain :=
  q.mem_toOperator_domain_iff.mpr ⟨hx, η, h⟩

/-- The defining identity `q(φ, ψ) = ⟪φ, T ψ⟫` for `φ ∈ Q(q)` and `ψ ∈ D(T)`. -/
theorem form_toOperator (φ : q.domain) (ψ : q.toOperator.domain) :
    q.form φ ⟨ψ, q.toOperator_domain_le ψ.2⟩ = ⟪(φ : E), q.toOperator ψ⟫_𝕜 := by
  set g := q.reprEquiv.symm ψ
  have h1 : (g : E × E).1 = ψ := congrArg Subtype.val (q.reprEquiv.apply_symm_apply ψ)
  obtain ⟨hp, h⟩ := g.2
  have hT : q.toOperator ψ = (g : E × E).2 := rfl
  rw [hT, ← h]
  congr 2
  exact h1.symm

/-- `T ψ` is the unique representing vector: if `q(φ, ψ) = ⟪φ, η⟫` for all `φ ∈ Q(q)`, then
`T ψ = η`. -/
theorem toOperator_apply_eq (ψ : q.toOperator.domain) {η : E}
    (h : ∀ φ : q.domain, q.form φ ⟨ψ, q.toOperator_domain_le ψ.2⟩ = ⟪(φ : E), η⟫_𝕜) :
    q.toOperator ψ = η :=
  q.eq_of_forall_inner_eq fun φ => by rw [← form_toOperator, h]

variable {q}

/-- The operator of a symmetric form is formally self-adjoint: `⟪T x, y⟫ = ⟪x, T y⟫`. -/
theorem toOperator_isFormalAdjoint (hq : q.IsSymmetric) :
    q.toOperator.IsFormalAdjoint q.toOperator := by
  intro x y
  have hx : ⟪(x : E), q.toOperator y⟫_𝕜 =
      q.form ⟨x, q.toOperator_domain_le x.2⟩ ⟨y, q.toOperator_domain_le y.2⟩ :=
    (q.form_toOperator ⟨x, q.toOperator_domain_le x.2⟩ y).symm
  have hy : ⟪(y : E), q.toOperator x⟫_𝕜 =
      q.form ⟨y, q.toOperator_domain_le y.2⟩ ⟨x, q.toOperator_domain_le x.2⟩ :=
    (q.form_toOperator ⟨y, q.toOperator_domain_le y.2⟩ x).symm
  rw [← inner_conj_symm, hx, hy, ← hq]

/-- The operator of a semibounded form is bounded below: `⟪ψ, T ψ⟫ ≥ -M ‖ψ‖²`. -/
theorem isBoundedBelow_toOperator {M : ℝ} (hM : q.IsSemibounded M) :
    IsBoundedBelow q.toOperator (-M) := by
  intro x
  have h := hM ⟨x, q.toOperator_domain_le x.2⟩
  rw [form_toOperator] at h
  exact h

variable {M : ℝ}

/-- `⟪φ, (T + M + 1) ψ⟫ = (φ, ψ)₊₁` for `φ ∈ Q(q)` and `ψ ∈ D(T)`. -/
theorem inner_addScalar_toOperator (hq : q.IsSymmetric) (hM : q.IsSemibounded M)
    (φ : q.domain) (ψ : q.toOperator.domain) :
    ⟪(φ : E), addScalar q.toOperator ((M + 1 : ℝ) : 𝕜) ψ⟫_𝕜 =
      ⟪(⟨φ⟩ : FormSpace q M hq hM), ⟨⟨ψ, q.toOperator_domain_le ψ.2⟩⟩⟫_𝕜 := by
  rw [FormSpace.inner_def, form_toOperator]
  change ⟪(φ : E), q.toOperator ψ + ((M + 1 : ℝ) : 𝕜) • (ψ : E)⟫_𝕜 = _
  rw [inner_add_right, inner_smul_right]

/-- Riesz representation in `(Q(q), (·, ·)₊₁)` (Reed–Simon I, proof of Theorem VIII.15): for
`f ∈ E` there is `ψ ∈ Q(q)` with `q(φ, ψ) + (M + 1) ⟪φ, ψ⟫ = ⟪φ, f⟫` for all `φ ∈ Q(q)`. -/
theorem exists_form_add_inner_eq (hq : q.IsSymmetric) (hM : q.IsSemibounded M)
    (hc : q.IsClosed M) (f : E) :
    ∃ ψ : q.domain, ∀ φ : q.domain,
      q.form φ ψ + ((M + 1 : ℝ) : 𝕜) * ⟪(φ : E), (ψ : E)⟫_𝕜 = ⟪(φ : E), f⟫_𝕜 := by
  have := FormSpace.completeSpace (hq := hq) (hM := hM) hc
  let ℓ : StrongDual 𝕜 (FormSpace q M hq hM) :=
    (innerSL 𝕜 f).comp (FormSpace.toAmbient q M hq hM)
  let w := (InnerProductSpace.toDual 𝕜 (FormSpace q M hq hM)).symm ℓ
  refine ⟨w.toDomain, fun φ => ?_⟩
  have h := InnerProductSpace.toDual_symm_apply (x := (⟨φ⟩ : FormSpace q M hq hM)) (y := ℓ)
  rw [FormSpace.inner_def] at h
  have h' := congrArg conj h
  rw [map_add, map_mul, RCLike.conj_ofReal, ← hq, inner_conj_symm] at h'
  rw [h']
  change conj ⟪f, (φ : E)⟫_𝕜 = _
  rw [inner_conj_symm]

/-- `Ran(T + M + 1) = E` for the operator `T` of a closed semibounded symmetric form. -/
theorem range_addScalar_toOperator (hq : q.IsSymmetric) (hM : q.IsSemibounded M)
    (hc : q.IsClosed M) :
    LinearMap.range (addScalar q.toOperator ((M + 1 : ℝ) : 𝕜)).toFun = ⊤ := by
  refine eq_top_iff.mpr fun f _ => ?_
  obtain ⟨ψ, hψ⟩ := exists_form_add_inner_eq hq hM hc f
  have hrep : ∀ φ : q.domain,
      q.form φ ⟨(ψ : E), ψ.2⟩ = ⟪(φ : E), f - ((M + 1 : ℝ) : 𝕜) • (ψ : E)⟫_𝕜 := by
    intro φ
    rw [inner_sub_right, inner_smul_right, ← hψ φ]
    ring
  have hmem := q.mem_toOperator_domain_of_forall ψ.2 _ hrep
  refine ⟨⟨ψ, hmem⟩, ?_⟩
  have hT := q.toOperator_apply_eq ⟨ψ, hmem⟩ hrep
  change q.toOperator ⟨ψ, hmem⟩ + ((M + 1 : ℝ) : 𝕜) • (ψ : E) = f
  rw [hT, sub_add_cancel]

/-- For `ψ ∈ D(T)`, `⟪ψ, (T + M + 1) ψ⟫ = ‖ψ‖₊₁²`, so it vanishes only for `ψ = 0`. -/
theorem eq_zero_of_inner_addScalar_toOperator_self (hq : q.IsSymmetric)
    (hM : q.IsSemibounded M) (ψ : q.toOperator.domain)
    (h : ⟪(ψ : E), addScalar q.toOperator ((M + 1 : ℝ) : 𝕜) ψ⟫_𝕜 = 0) : ψ = 0 := by
  have h' := inner_addScalar_toOperator hq hM ⟨ψ, q.toOperator_domain_le ψ.2⟩ ψ
  rw [h, eq_comm, inner_self_eq_zero] at h'
  have h0 : (ψ : E) = 0 := congrArg (fun u : FormSpace q M hq hM => (u.toDomain : E)) h'
  exact Subtype.ext h0

/-- **`D(T)` is a form core for `q`** (Reed–Simon I, proof of Theorem VIII.15): it is dense in
`Q(q)` for `‖·‖₊₁`.  If `v ∈ Q(q)` is `(·, ·)₊₁`-orthogonal to `D(T)`, then
`0 = (v, φ)₊₁ = ⟪v, (T + M + 1) φ⟫` for all `φ ∈ D(T)`, and `Ran(T + M + 1) = E` forces
`v = 0`. -/
theorem toOperator_core (hq : q.IsSymmetric) (hM : q.IsSemibounded M) (hc : q.IsClosed M)
    (ψ : q.domain) (ε : ℝ) (hε : 0 < ε) :
    ∃ φ : q.toOperator.domain, q.plusOneNorm M (ψ - ⟨φ, q.toOperator_domain_le φ.2⟩) < ε := by
  have := FormSpace.completeSpace (hq := hq) (hM := hM) hc
  let K : Submodule 𝕜 (FormSpace q M hq hM) :=
    q.toOperator.domain.comap (FormSpace.toAmbient q M hq hM).toLinearMap
  have hK : Kᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v hv
    obtain ⟨φ, hφ⟩ : (v.toDomain : E) ∈
        LinearMap.range (addScalar q.toOperator ((M + 1 : ℝ) : 𝕜)).toFun := by
      rw [range_addScalar_toOperator hq hM hc]
      trivial
    have hφK : (⟨⟨φ, q.toOperator_domain_le φ.2⟩⟩ : FormSpace q M hq hM) ∈ K := φ.2
    have h0 := (Submodule.mem_orthogonal' K v).mp hv _ hφK
    have h1 : ⟪(v.toDomain : E), (addScalar q.toOperator ((M + 1 : ℝ) : 𝕜)).toFun φ⟫_𝕜 = 0 :=
      (inner_addScalar_toOperator hq hM v.toDomain φ).trans h0
    rw [hφ, inner_self_eq_zero] at h1
    exact FormSpace.ext (Subtype.ext h1)
  have hdense : Dense (K : Set (FormSpace q M hq hM)) := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff]
    exact hK
  obtain ⟨k, hkball, hkK⟩ := Metric.dense_iff.mp hdense ⟨ψ⟩ ε hε
  refine ⟨⟨k.toDomain, hkK⟩, ?_⟩
  rw [Metric.mem_ball, dist_comm, dist_eq_norm, FormSpace.norm_eq] at hkball
  exact hkball

/-- The operator of a closed semibounded symmetric form has `q` as its quadratic form. -/
theorem isFormOf_toOperator (hq : q.IsSymmetric) (hM : q.IsSemibounded M) (hc : q.IsClosed M) :
    q.IsFormOf M q.toOperator where
  domain_le := q.toOperator_domain_le
  eq_inner := q.form_toOperator
  core ψ ε hε := toOperator_core hq hM hc ψ ε hε

section Complete

variable [CompleteSpace E]

/-- The operator of a closed semibounded symmetric form is densely defined (Reed–Simon I,
proof of Theorem VIII.15): if `g ⊥ D(T)`, write `g = (T + M + 1) ψ`; then
`0 = ⟪ψ, g⟫ = ‖ψ‖₊₁²`. -/
theorem dense_toOperator_domain (hq : q.IsSymmetric) (hM : q.IsSemibounded M)
    (hc : q.IsClosed M) : Dense (q.toOperator.domain : Set E) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    Submodule.eq_bot_iff]
  intro g hg
  obtain ⟨ψ, hψ⟩ : g ∈ LinearMap.range (addScalar q.toOperator ((M + 1 : ℝ) : 𝕜)).toFun := by
    rw [range_addScalar_toOperator hq hM hc]
    trivial
  have h0 : ⟪(ψ : E), g⟫_𝕜 = 0 := (Submodule.mem_orthogonal _ g).mp hg ψ ψ.2
  rw [← hψ] at h0
  have hψ0 : ψ = 0 := eq_zero_of_inner_addScalar_toOperator_self hq hM ψ h0
  rw [← hψ, hψ0, map_zero]

/-- The operator of a closed semibounded symmetric form is symmetric. -/
theorem isSymmetric_toOperator (hq : q.IsSymmetric) (hM : q.IsSemibounded M)
    (hc : q.IsClosed M) : KatoRellich.IsSymmetric q.toOperator :=
  ⟨dense_toOperator_domain hq hM hc, toOperator_isFormalAdjoint hq⟩

/-- **The operator of a closed semibounded symmetric form is self-adjoint** (Reed–Simon I,
Theorem VIII.15, p. 278, existence).  It is symmetric with `Ran(T + M + 1) = E`. -/
theorem isSelfAdjoint_toOperator (hq : q.IsSymmetric) (hM : q.IsSemibounded M)
    (hc : q.IsClosed M) : IsSelfAdjoint q.toOperator :=
  isSelfAdjoint_of_range_addScalar_ofReal (isSymmetric_toOperator hq hM hc) (M + 1)
    (range_addScalar_toOperator hq hM hc)

/-- **Uniqueness** (Reed–Simon I, Theorem VIII.15, p. 278): a self-adjoint `S` with
`D(S) ⊆ Q(q)` and `q(φ, ψ) = ⟪φ, S ψ⟫` for `φ ∈ Q(q)`, `ψ ∈ D(S)` is the operator of `q`.  No
form-core assumption is needed: `S ⊆ T` by the definition of `T`, hence `T = T† ⊆ S† = S`. -/
theorem eq_toOperator_of_isSelfAdjoint (hq : q.IsSymmetric) (hM : q.IsSemibounded M)
    (hc : q.IsClosed M) {S : E →ₗ.[𝕜] E} (hS : IsSelfAdjoint S) (hle : S.domain ≤ q.domain)
    (heq : ∀ (φ : q.domain) (ψ : S.domain), q.form φ ⟨ψ, hle ψ.2⟩ = ⟪(φ : E), S ψ⟫_𝕜) :
    S = q.toOperator := by
  have hST : S ≤ q.toOperator := by
    refine ⟨fun x hx =>
      q.mem_toOperator_domain_of_forall (hle hx) (S ⟨x, hx⟩) (heq · ⟨x, hx⟩), ?_⟩
    intro x y hxy
    refine (q.toOperator_apply_eq y fun φ => ?_).symm
    have hyx : (⟨y, q.toOperator_domain_le y.2⟩ : q.domain) = ⟨x, hle x.2⟩ :=
      Subtype.ext hxy.symm
    rw [hyx]
    exact heq φ x
  have hTS : q.toOperator ≤ S := by
    have h := adjoint_le_adjoint hST hS.dense_domain
    rwa [LinearPMap.isSelfAdjoint_def.mp (isSelfAdjoint_toOperator hq hM hc),
      LinearPMap.isSelfAdjoint_def.mp hS] at h
  exact le_antisymm hST hTS

/-- **Reed–Simon I, Theorem VIII.15, p. 278.**  If `q` is a closed semibounded quadratic form,
then `q` is the quadratic form of a unique self-adjoint operator.  "The quadratic form of `T`" is
the spectral-free notion `IsFormOf` (see `KatoRellich/QuadraticForm.lean`); the operator is
`QuadForm.toOperator q`, and it is bounded below by `-M` (`isBoundedBelow_toOperator`). -/
theorem existsUnique_isSelfAdjoint_isFormOf (hq : q.IsSymmetric) (hM : q.IsSemibounded M)
    (hc : q.IsClosed M) : ∃! T : E →ₗ.[𝕜] E, IsSelfAdjoint T ∧ q.IsFormOf M T :=
  ⟨q.toOperator, ⟨isSelfAdjoint_toOperator hq hM hc, isFormOf_toOperator hq hM hc⟩,
    fun _ hS => eq_toOperator_of_isSelfAdjoint hq hM hc hS.1 hS.2.domain_le hS.2.eq_inner⟩

end Complete

end QuadForm

end KatoRellich
