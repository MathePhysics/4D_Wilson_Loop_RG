import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# Von Neumann's theorem on `T† T`

**Reed–Simon II, Theorem X.25, p. 180.**  Let `A` be a closed densely defined operator and let
`D(A†A) = {ψ ∈ D(A) | A ψ ∈ D(A†)}`.  Define `A†A` on `D(A†A)` by `(A†A) ψ = A† (A ψ)`.  Then
`A†A` is self-adjoint.  Reed–Simon prove it with quadratic forms; the proof here is von Neumann's
original operator-theoretic one, which also gives the bounded inverse of `1 + A†A` used to
construct the spectral decomposition of an unbounded operator.

Proof.  Let `V (x, y) = (-y, x)` on the Hilbert space `H × H` with the `L²` inner product.  A
vector `(u, v)` is orthogonal to the graph of `T` if and only if `⟪a, u⟫ + ⟪T a, v⟫ = 0` for all
`a ∈ D(T)`, that is, if and only if `v ∈ D(T†)` and `T† v = -u`; so the orthogonal complement of
the graph of `T` is `V (graph T†)`.  If `T` is closed, its graph is a closed subspace, so
`H × H = graph T ⊕ V (graph T†)` orthogonally.  Writing `(h, 0) = (ψ, T ψ) + (-T† φ, φ)` gives
`φ = -T ψ`, hence `T ψ ∈ D(T†)` and `h = ψ + T† T ψ`: the map `1 + T†T` is onto `H`.  It is
injective because `⟪ψ, (1 + T†T) ψ⟫ = ‖ψ‖² + ‖T ψ‖²`, which also bounds its inverse `Q` by `1` in
norm and shows that `Q` is positive and that `T Q` is bounded by `1`.  Finally `T†T` is symmetric,
and if `φ ∈ D((T†T)†)` then `(1 + T†T) φ - (1 + (T†T)†) φ` is orthogonal to the range of
`1 + T†T`, which is all of `H`; so `φ ∈ D(T†T)`, and `T†T` is self-adjoint.

Everything is stated for a closed densely defined `T : E →ₗ.[𝕜] F` between two Hilbert spaces over
`𝕜 = ℝ` or `ℂ`, which is what the proof gives.

## Main definitions and results

* `SpectralTheorem.graphL2`: the graph of `T` inside `WithLp 2 (E × F)`, with
  `SpectralTheorem.mem_graphL2_orthogonal` describing its orthogonal complement by `T†`.
* `SpectralTheorem.exists_add_adjoint_apply`: for a closed densely defined `T` and every `h`
  there is `ψ ∈ D(T)` with `T ψ ∈ D(T†)` and `ψ + T† (T ψ) = h`.
* `SpectralTheorem.adjointComp T`: the operator `T† T` on `D(T†T) = {ψ ∈ D(T) | T ψ ∈ D(T†)}`,
  with `SpectralTheorem.mem_adjointComp_domain`, `SpectralTheorem.adjointComp_apply`,
  `SpectralTheorem.inner_adjointComp : ⟪(T†T) ψ, φ⟫ = ⟪T ψ, T φ⟫` and
  `SpectralTheorem.re_inner_adjointComp_self_nonneg` (positivity).
* `SpectralTheorem.vonNeumann_bijective`: `ψ ↦ ψ + (T†T) ψ` is a bijection from `D(T†T)` onto `E`.
* `SpectralTheorem.vonNeumannInverse T`: its inverse `Q : E →L[𝕜] E`, with
  `SpectralTheorem.norm_vonNeumannInverse_le_one`,
  `SpectralTheorem.isSelfAdjoint_vonNeumannInverse`,
  `SpectralTheorem.isPositive_vonNeumannInverse`, `SpectralTheorem.vonNeumannInverse_injective`,
  `SpectralTheorem.range_vonNeumannInverse` and
  `SpectralTheorem.add_adjointComp_vonNeumannInverse`.
* `SpectralTheorem.isSelfAdjoint_adjointComp`: `T†T` is self-adjoint.
* `SpectralTheorem.boundedOfCompose T`: the bounded operator `T Q : E →L[𝕜] F`, of norm at
  most `1`.
* `SpectralTheorem.hasCore_adjointCompDomain`: `D(T†T)` is a core of `T`.
-/

noncomputable section

open scoped InnerProductSpace
open WithLp

universe u v

namespace SpectralTheorem

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable {F : Type v} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-! ### The graph decomposition -/

/-- The graph of `T`, viewed inside the Hilbert space `WithLp 2 (E × F)`. -/
def graphL2 (T : E →ₗ.[𝕜] F) : Submodule 𝕜 (WithLp 2 (E × F)) :=
  T.graph.comap (WithLp.linearEquiv 2 𝕜 (E × F) : WithLp 2 (E × F) →ₗ[𝕜] E × F)

omit [CompleteSpace E] [CompleteSpace F] in
theorem mem_graphL2 {T : E →ₗ.[𝕜] F} {x : WithLp 2 (E × F)} :
    x ∈ graphL2 T ↔ ofLp x ∈ T.graph := Iff.rfl

omit [CompleteSpace E] [CompleteSpace F] in
/-- If `T` is a closed operator, its graph is a closed subspace of `WithLp 2 (E × F)`. -/
theorem isClosed_graphL2 {T : E →ₗ.[𝕜] F} (h : T.IsClosed) :
    IsClosed (graphL2 T : Set (WithLp 2 (E × F))) := by
  have hset : (graphL2 T : Set (WithLp 2 (E × F)))
      = (ofLp : WithLp 2 (E × F) → E × F) ⁻¹' (T.graph : Set (E × F)) := rfl
  rw [hset]
  exact h.preimage (WithLp.prod_continuous_ofLp 2 E F)

omit [CompleteSpace F] in
/-- The orthogonal complement of the graph of a densely defined `T` is the image of the graph of
`T†` under `(v, w) ↦ (-w, v)`. -/
theorem mem_graphL2_orthogonal {T : E →ₗ.[𝕜] F} (hT : Dense (T.domain : Set E))
    {x : WithLp 2 (E × F)} :
    x ∈ (graphL2 T)ᗮ ↔ ∃ h : (ofLp x).2 ∈ (T.adjoint).domain,
      T.adjoint ⟨(ofLp x).2, h⟩ = -(ofLp x).1 := by
  constructor
  · intro hx
    have key : ∀ a : T.domain,
        ⟪(a : E), (ofLp x).1⟫_𝕜 + ⟪(T a : F), (ofLp x).2⟫_𝕜 = 0 := by
      intro a
      have hmem : (toLp 2 ((a : E), T a) : WithLp 2 (E × F)) ∈ graphL2 T := by
        rw [mem_graphL2]
        simp
      have := (Submodule.mem_orthogonal _ _).1 hx _ hmem
      simp at this
      exact this
    have key' : ∀ a : T.domain, ⟪(ofLp x).2, (T a : F)⟫_𝕜 = ⟪-(ofLp x).1, (a : E)⟫_𝕜 := by
      intro a
      have hka := key a
      rw [inner_neg_left]
      rw [← inner_conj_symm (a : E), ← inner_conj_symm (T a : F)] at hka
      have h2 : (starRingEnd 𝕜) (⟪(ofLp x).1, (a : E)⟫_𝕜 + ⟪(ofLp x).2, (T a : F)⟫_𝕜) = 0 := by
        rw [map_add]; exact hka
      rw [map_eq_zero_iff _ (starRingEnd 𝕜).injective] at h2
      linear_combination h2
    have hmem : (ofLp x).2 ∈ (T.adjoint).domain :=
      LinearPMap.mem_adjoint_domain_of_exists _ ⟨-(ofLp x).1, fun a => (key' a).symm⟩
    exact ⟨hmem, LinearPMap.adjoint_apply_eq hT ⟨(ofLp x).2, hmem⟩ fun a => (key' a).symm⟩
  · rintro ⟨hmem, hval⟩
    rw [Submodule.mem_orthogonal]
    intro u hu
    rw [mem_graphL2, LinearPMap.mem_graph_iff] at hu
    obtain ⟨a, ha1, ha2⟩ := hu
    have hfa0 := (LinearPMap.adjoint_isFormalAdjoint hT) ⟨(ofLp x).2, hmem⟩ a
    rw [hval] at hfa0
    have hfa : ⟪(ofLp x).2, (T a : F)⟫_𝕜 = ⟪-(ofLp x).1, (a : E)⟫_𝕜 := hfa0.symm
    rw [WithLp.prod_inner_apply, ← ha1, ← ha2]
    have h3 : ⟪(T a : F), (ofLp x).2⟫_𝕜 = -⟪(a : E), (ofLp x).1⟫_𝕜 := by
      rw [← inner_conj_symm (T a : F) (ofLp x).2, hfa, inner_neg_left, map_neg, inner_conj_symm]
    rw [h3, add_neg_cancel]

/-- Von Neumann's decomposition: for a closed densely defined `T` and every `h : E` there is
`ψ ∈ D(T)` with `T ψ ∈ D(T†)` and `ψ + T† (T ψ) = h`.  This comes from writing `(h, 0)` in
`E × F = graph T ⊕ (graph T†)ᗮ`. -/
theorem exists_add_adjoint_apply {T : E →ₗ.[𝕜] F} (hT : Dense (T.domain : Set E))
    (hTc : T.IsClosed) (h : E) :
    ∃ (ψ : T.domain) (hψ : (T ψ : F) ∈ (T.adjoint).domain),
      (ψ : E) + T.adjoint ⟨T ψ, hψ⟩ = h := by
  have : CompleteSpace (graphL2 T) := (isClosed_graphL2 hTc).completeSpace_coe
  obtain ⟨y, hy, z, hz, hyz⟩ :=
    Submodule.exists_add_mem_mem_orthogonal (K := graphL2 T) (toLp 2 (h, (0 : F)))
  rw [mem_graphL2, LinearPMap.mem_graph_iff] at hy
  obtain ⟨ψ, hψ1, hψ2⟩ := hy
  rw [mem_graphL2_orthogonal hT] at hz
  obtain ⟨hmem, hval⟩ := hz
  have hsum : ((h, (0 : F)) : E × F) = ofLp y + ofLp z := by
    simpa using congrArg (ofLp (p := 2)) hyz
  have h1 : h = (ofLp y).1 + (ofLp z).1 := congrArg Prod.fst hsum
  have h2 : (0 : F) = (ofLp y).2 + (ofLp z).2 := congrArg Prod.snd hsum
  have hu2 : (ofLp y).2 = -(ofLp z).2 := eq_neg_of_add_eq_zero_left h2.symm
  have hTψ : (T ψ : F) ∈ (T.adjoint).domain := by
    rw [hψ2, hu2]
    exact neg_mem hmem
  refine ⟨ψ, hTψ, ?_⟩
  have hkey : (⟨(T ψ : F), hTψ⟩ : (T.adjoint).domain) = -⟨(ofLp z).2, hmem⟩ := by
    ext
    simp only [NegMemClass.coe_neg]
    rw [hψ2, hu2]
  rw [hkey, LinearPMap.map_neg, hval, neg_neg, h1, hψ1]

/-! ### The operator `T† T` -/

/-- The domain `D(T†T) = {ψ ∈ D(T) | T ψ ∈ D(T†)}` of `T† T`. -/
def adjointCompDomain (T : E →ₗ.[𝕜] F) : Submodule 𝕜 E where
  carrier := {x | ∃ h : x ∈ T.domain, (T ⟨x, h⟩ : F) ∈ (T.adjoint).domain}
  zero_mem' := by
    refine ⟨T.domain.zero_mem, ?_⟩
    have h0 : (⟨(0 : E), T.domain.zero_mem⟩ : T.domain) = 0 := rfl
    have h1 : (T (0 : T.domain) : F) = 0 := map_zero T.toFun
    rw [h0, h1]
    exact (T.adjoint).domain.zero_mem
  add_mem' := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    refine ⟨add_mem hx1 hy1, ?_⟩
    have hadd : (⟨x + y, add_mem hx1 hy1⟩ : T.domain) = ⟨x, hx1⟩ + ⟨y, hy1⟩ := rfl
    rw [hadd, LinearPMap.map_add]
    exact add_mem hx2 hy2
  smul_mem' := by
    rintro c x ⟨hx1, hx2⟩
    refine ⟨Submodule.smul_mem _ c hx1, ?_⟩
    have hsmul : (⟨c • x, Submodule.smul_mem _ c hx1⟩ : T.domain) = c • ⟨x, hx1⟩ := rfl
    rw [hsmul, LinearPMap.map_smul]
    exact Submodule.smul_mem _ c hx2

omit [CompleteSpace F] in
theorem mem_adjointCompDomain {T : E →ₗ.[𝕜] F} {x : E} :
    x ∈ adjointCompDomain T ↔ ∃ h : x ∈ T.domain, (T ⟨x, h⟩ : F) ∈ (T.adjoint).domain :=
  Iff.rfl

omit [CompleteSpace F] in
theorem adjointCompDomain_le {T : E →ₗ.[𝕜] F} : adjointCompDomain T ≤ T.domain :=
  fun _ hx => hx.elim fun h _ => h

/-- The operator `T† T`, on the domain `D(T†T) = {ψ ∈ D(T) | T ψ ∈ D(T†)}`.  This is
Reed–Simon's `A*A` of Theorem X.25. -/
def adjointComp (T : E →ₗ.[𝕜] F) : E →ₗ.[𝕜] E where
  domain := adjointCompDomain T
  toFun := (T.adjoint).toFun.comp
    (LinearMap.codRestrict (T.adjoint).domain
      (T.toFun.comp (Submodule.inclusion (adjointCompDomain_le (T := T))))
      fun x => (mem_adjointCompDomain.1 x.2).choose_spec)

omit [CompleteSpace F] in
@[simp]
theorem adjointComp_domain (T : E →ₗ.[𝕜] F) : (adjointComp T).domain = adjointCompDomain T :=
  rfl

omit [CompleteSpace F] in
theorem mem_adjointComp_domain {T : E →ₗ.[𝕜] F} {x : E} :
    x ∈ (adjointComp T).domain ↔ ∃ h : x ∈ T.domain, (T ⟨x, h⟩ : F) ∈ (T.adjoint).domain :=
  Iff.rfl

/-- A vector of `D(T†T)`, viewed in `D(T)`. -/
def adjointCompToDomain {T : E →ₗ.[𝕜] F} (x : (adjointComp T).domain) : T.domain :=
  ⟨(x : E), adjointCompDomain_le x.2⟩

omit [CompleteSpace F] in
@[simp]
theorem coe_adjointCompToDomain {T : E →ₗ.[𝕜] F} (x : (adjointComp T).domain) :
    (adjointCompToDomain x : E) = (x : E) := rfl

omit [CompleteSpace F] in
theorem mem_adjoint_domain_apply {T : E →ₗ.[𝕜] F} (x : (adjointComp T).domain) :
    (T (adjointCompToDomain x) : F) ∈ (T.adjoint).domain :=
  (mem_adjointComp_domain.1 x.2).choose_spec

omit [CompleteSpace F] in
/-- `(T†T) ψ = T† (T ψ)`. -/
theorem adjointComp_apply {T : E →ₗ.[𝕜] F} (x : (adjointComp T).domain) :
    adjointComp T x = T.adjoint ⟨T (adjointCompToDomain x), mem_adjoint_domain_apply x⟩ := rfl

omit [CompleteSpace F] in
/-- The fundamental identity `⟪(T†T) ψ, φ⟫ = ⟪T ψ, T φ⟫` for `ψ ∈ D(T†T)` and `φ ∈ D(T)`. -/
theorem inner_adjointComp {T : E →ₗ.[𝕜] F} (hT : Dense (T.domain : Set E))
    (x : (adjointComp T).domain) (y : T.domain) :
    ⟪(adjointComp T x : E), (y : E)⟫_𝕜 = ⟪(T (adjointCompToDomain x) : F), (T y : F)⟫_𝕜 := by
  rw [adjointComp_apply]
  exact LinearPMap.adjoint_isFormalAdjoint hT ⟨T (adjointCompToDomain x), _⟩ y

omit [CompleteSpace F] in
/-- `⟪(T†T) ψ, ψ⟫ = ‖T ψ‖²`. -/
theorem inner_adjointComp_self {T : E →ₗ.[𝕜] F} (hT : Dense (T.domain : Set E))
    (x : (adjointComp T).domain) :
    ⟪(adjointComp T x : E), (x : E)⟫_𝕜
      = ((‖(T (adjointCompToDomain x) : F)‖ ^ 2 : ℝ) : 𝕜) := by
  have e1 : ⟪(adjointComp T x : E), (x : E)⟫_𝕜
      = ⟪(T (adjointCompToDomain x) : F), (T (adjointCompToDomain x) : F)⟫_𝕜 :=
    inner_adjointComp hT x (adjointCompToDomain x)
  rw [e1, inner_self_eq_norm_sq_to_K]
  push_cast
  ring

omit [CompleteSpace F] in
/-- `T†T` is a positive operator. -/
theorem re_inner_adjointComp_self_nonneg {T : E →ₗ.[𝕜] F} (hT : Dense (T.domain : Set E))
    (x : (adjointComp T).domain) :
    0 ≤ RCLike.re ⟪(adjointComp T x : E), (x : E)⟫_𝕜 := by
  rw [inner_adjointComp_self hT, RCLike.ofReal_re]
  positivity

/-! ### Bijectivity of `1 + T†T` -/

/-- The map `ψ ↦ ψ + (T†T) ψ` on `D(T†T)`. -/
def onePlusAdjointComp (T : E →ₗ.[𝕜] F) : (adjointComp T).domain →ₗ[𝕜] E :=
  (adjointComp T).domain.subtype + (adjointComp T).toFun

omit [CompleteSpace F] in
@[simp]
theorem onePlusAdjointComp_apply {T : E →ₗ.[𝕜] F} (x : (adjointComp T).domain) :
    onePlusAdjointComp T x = (x : E) + adjointComp T x := rfl

omit [CompleteSpace F] in
/-- `⟪ψ, (1 + T†T) ψ⟫ = ‖ψ‖² + ‖T ψ‖²`. -/
theorem inner_onePlusAdjointComp {T : E →ₗ.[𝕜] F} (hT : Dense (T.domain : Set E))
    (x : (adjointComp T).domain) :
    ⟪(x : E), onePlusAdjointComp T x⟫_𝕜
      = ((‖(x : E)‖ ^ 2 + ‖(T (adjointCompToDomain x) : F)‖ ^ 2 : ℝ) : 𝕜) := by
  have h2 : ⟪(adjointComp T x : E), (x : E)⟫_𝕜
      = ⟪(T (adjointCompToDomain x) : F), (T (adjointCompToDomain x) : F)⟫_𝕜 :=
    inner_adjointComp hT x (adjointCompToDomain x)
  have h3 : ⟪(x : E), (adjointComp T x : E)⟫_𝕜
      = ((‖(T (adjointCompToDomain x) : F)‖ ^ 2 : ℝ) : 𝕜) := by
    rw [← inner_conj_symm (x : E) (adjointComp T x), h2, inner_self_eq_norm_sq_to_K,
      ← RCLike.ofReal_pow, RCLike.conj_ofReal]
  rw [onePlusAdjointComp_apply, inner_add_right, h3, inner_self_eq_norm_sq_to_K]
  push_cast
  ring

omit [CompleteSpace F] in
/-- `‖ψ‖² + ‖T ψ‖² ≤ ‖ψ‖ ‖(1 + T†T) ψ‖`, by the Cauchy–Schwarz inequality. -/
theorem norm_sq_add_norm_sq_le {T : E →ₗ.[𝕜] F} (hT : Dense (T.domain : Set E))
    (x : (adjointComp T).domain) :
    ‖(x : E)‖ ^ 2 + ‖(T (adjointCompToDomain x) : F)‖ ^ 2
      ≤ ‖(x : E)‖ * ‖onePlusAdjointComp T x‖ := by
  have h1 := norm_inner_le_norm (𝕜 := 𝕜) (x : E) (onePlusAdjointComp T x)
  rw [inner_onePlusAdjointComp hT, RCLike.norm_ofReal, abs_of_nonneg (by positivity)] at h1
  exact h1

omit [CompleteSpace F] in
/-- `1 + T†T` does not decrease the norm. -/
theorem norm_le_norm_onePlusAdjointComp {T : E →ₗ.[𝕜] F} (hT : Dense (T.domain : Set E))
    (x : (adjointComp T).domain) : ‖(x : E)‖ ≤ ‖onePlusAdjointComp T x‖ := by
  have h := norm_sq_add_norm_sq_le hT x
  nlinarith [norm_nonneg (x : E), norm_nonneg (onePlusAdjointComp T x),
    norm_nonneg (T (adjointCompToDomain x) : F),
    sq_nonneg (‖(x : E)‖ - ‖onePlusAdjointComp T x‖)]

omit [CompleteSpace F] in
/-- `‖T ψ‖ ≤ ‖(1 + T†T) ψ‖`. -/
theorem norm_apply_le_norm_onePlusAdjointComp {T : E →ₗ.[𝕜] F} (hT : Dense (T.domain : Set E))
    (x : (adjointComp T).domain) :
    ‖(T (adjointCompToDomain x) : F)‖ ≤ ‖onePlusAdjointComp T x‖ := by
  have h := norm_sq_add_norm_sq_le hT x
  nlinarith [norm_nonneg (x : E), norm_nonneg (onePlusAdjointComp T x),
    norm_nonneg (T (adjointCompToDomain x) : F),
    sq_nonneg (2 * ‖(x : E)‖ - ‖onePlusAdjointComp T x‖),
    sq_nonneg (‖(T (adjointCompToDomain x) : F)‖ - ‖onePlusAdjointComp T x‖)]

/-- **Von Neumann's theorem**, first part: for a closed densely defined `T`, the map
`ψ ↦ ψ + (T†T) ψ` is a bijection from `D(T†T)` onto `E`. -/
theorem vonNeumann_bijective {T : E →ₗ.[𝕜] F} (hT : Dense (T.domain : Set E))
    (hTc : T.IsClosed) : Function.Bijective (onePlusAdjointComp T) := by
  constructor
  · intro a b hab
    have h := norm_le_norm_onePlusAdjointComp hT (a - b)
    rw [map_sub, hab, sub_self, norm_zero] at h
    have h4 : ‖((a - b : (adjointComp T).domain) : E)‖ = 0 := le_antisymm h (norm_nonneg _)
    exact sub_eq_zero.1 (Submodule.coe_eq_zero.1 (norm_eq_zero.1 h4))
  · intro h
    obtain ⟨ψ, hψ, hsum⟩ := exists_add_adjoint_apply hT hTc h
    have hmem : (ψ : E) ∈ (adjointComp T).domain := ⟨ψ.2, hψ⟩
    exact ⟨⟨(ψ : E), hmem⟩, hsum⟩

/-! ### The bounded inverse `Q` of `1 + T†T` -/

/-- `1 + T†T` as a linear equivalence from `D(T†T)` onto `E`. -/
def vonNeumannEquiv (T : E →ₗ.[𝕜] F) (hT : Dense (T.domain : Set E)) (hTc : T.IsClosed) :
    (adjointComp T).domain ≃ₗ[𝕜] E :=
  LinearEquiv.ofBijective (onePlusAdjointComp T) (vonNeumann_bijective hT hTc)

theorem onePlusAdjointComp_symm_apply {T : E →ₗ.[𝕜] F} (hT : Dense (T.domain : Set E))
    (hTc : T.IsClosed) (h : E) :
    onePlusAdjointComp T ((vonNeumannEquiv T hT hTc).symm h) = h :=
  (vonNeumannEquiv T hT hTc).apply_symm_apply h

/-- The inverse `Q = (1 + T†T)⁻¹`, a bounded operator on `E` of norm at most `1`.
`Q` is the resolvent-like operator of von Neumann's theorem. -/
def vonNeumannInverse (T : E →ₗ.[𝕜] F) (hT : Dense (T.domain : Set E)) (hTc : T.IsClosed) :
    E →L[𝕜] E :=
  LinearMap.mkContinuous
    ((adjointComp T).domain.subtype.comp (vonNeumannEquiv T hT hTc).symm.toLinearMap) 1
    fun h => by
      have hb := norm_le_norm_onePlusAdjointComp hT ((vonNeumannEquiv T hT hTc).symm h)
      rw [onePlusAdjointComp_symm_apply] at hb
      rw [one_mul]
      exact hb

theorem vonNeumannInverse_apply {T : E →ₗ.[𝕜] F} (hT : Dense (T.domain : Set E))
    (hTc : T.IsClosed) (h : E) :
    vonNeumannInverse T hT hTc h = ((vonNeumannEquiv T hT hTc).symm h : E) := rfl

/-- `Q h` lies in `D(T†T)`. -/
theorem vonNeumannInverse_mem {T : E →ₗ.[𝕜] F} (hT : Dense (T.domain : Set E))
    (hTc : T.IsClosed) (h : E) : vonNeumannInverse T hT hTc h ∈ (adjointComp T).domain :=
  ((vonNeumannEquiv T hT hTc).symm h).2

/-- `(1 + T†T) (Q h) = h`. -/
theorem add_adjointComp_vonNeumannInverse {T : E →ₗ.[𝕜] F} (hT : Dense (T.domain : Set E))
    (hTc : T.IsClosed) (h : E) :
    vonNeumannInverse T hT hTc h
        + adjointComp T ⟨vonNeumannInverse T hT hTc h, vonNeumannInverse_mem hT hTc h⟩ = h :=
  (vonNeumannEquiv T hT hTc).apply_symm_apply h

/-- `Q ((1 + T†T) ψ) = ψ` for `ψ ∈ D(T†T)`. -/
theorem vonNeumannInverse_onePlusAdjointComp {T : E →ₗ.[𝕜] F} (hT : Dense (T.domain : Set E))
    (hTc : T.IsClosed) (x : (adjointComp T).domain) :
    vonNeumannInverse T hT hTc (onePlusAdjointComp T x) = (x : E) :=
  congrArg Subtype.val ((vonNeumannEquiv T hT hTc).symm_apply_apply x)

/-- `‖Q‖ ≤ 1`. -/
theorem norm_vonNeumannInverse_le_one {T : E →ₗ.[𝕜] F} (hT : Dense (T.domain : Set E))
    (hTc : T.IsClosed) : ‖vonNeumannInverse T hT hTc‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- `Q` is injective. -/
theorem vonNeumannInverse_injective {T : E →ₗ.[𝕜] F} (hT : Dense (T.domain : Set E))
    (hTc : T.IsClosed) : Function.Injective (vonNeumannInverse T hT hTc) := by
  intro u v huv
  exact (vonNeumannEquiv T hT hTc).symm.injective (Subtype.ext huv)

/-- The range of `Q` is exactly `D(T†T)`. -/
theorem range_vonNeumannInverse {T : E →ₗ.[𝕜] F} (hT : Dense (T.domain : Set E))
    (hTc : T.IsClosed) :
    Set.range (vonNeumannInverse T hT hTc) = ((adjointComp T).domain : Set E) := by
  ext x
  constructor
  · rintro ⟨h, rfl⟩
    exact vonNeumannInverse_mem hT hTc h
  · intro hx
    exact ⟨onePlusAdjointComp T ⟨x, hx⟩, vonNeumannInverse_onePlusAdjointComp hT hTc ⟨x, hx⟩⟩

/-- `Q` is self-adjoint. -/
theorem isSelfAdjoint_vonNeumannInverse {T : E →ₗ.[𝕜] F} (hT : Dense (T.domain : Set E))
    (hTc : T.IsClosed) : IsSelfAdjoint (vonNeumannInverse T hT hTc) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro u v
  obtain ⟨a, rfl⟩ := (vonNeumann_bijective hT hTc).surjective u
  obtain ⟨b, rfl⟩ := (vonNeumann_bijective hT hTc).surjective v
  simp only [ContinuousLinearMap.coe_coe]
  rw [vonNeumannInverse_onePlusAdjointComp, vonNeumannInverse_onePlusAdjointComp,
    onePlusAdjointComp_apply, onePlusAdjointComp_apply, inner_add_right, inner_add_left]
  congr 1
  have h1 : ⟪(adjointComp T a : E), (b : E)⟫_𝕜
      = ⟪(T (adjointCompToDomain a) : F), (T (adjointCompToDomain b) : F)⟫_𝕜 :=
    inner_adjointComp hT a (adjointCompToDomain b)
  have h2 : ⟪(adjointComp T b : E), (a : E)⟫_𝕜
      = ⟪(T (adjointCompToDomain b) : F), (T (adjointCompToDomain a) : F)⟫_𝕜 :=
    inner_adjointComp hT b (adjointCompToDomain a)
  rw [← inner_conj_symm (a : E) (adjointComp T b), h2, inner_conj_symm, ← h1]

/-- `Q` is a positive operator. -/
theorem isPositive_vonNeumannInverse {T : E →ₗ.[𝕜] F} (hT : Dense (T.domain : Set E))
    (hTc : T.IsClosed) : (vonNeumannInverse T hT hTc).IsPositive := by
  refine ⟨(ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).1
    (isSelfAdjoint_vonNeumannInverse hT hTc), fun u => ?_⟩
  obtain ⟨a, rfl⟩ := (vonNeumann_bijective hT hTc).surjective u
  rw [ContinuousLinearMap.reApplyInnerSelf_apply, vonNeumannInverse_onePlusAdjointComp,
    inner_onePlusAdjointComp hT, RCLike.ofReal_re]
  positivity

/-! ### The bounded operator `T Q` -/

/-- The bounded operator `T Q : E →L[𝕜] F`, of norm at most `1`. -/
def boundedOfCompose (T : E →ₗ.[𝕜] F) (hT : Dense (T.domain : Set E)) (hTc : T.IsClosed) :
    E →L[𝕜] F :=
  LinearMap.mkContinuous
    (T.toFun.comp ((Submodule.inclusion (adjointCompDomain_le (T := T))).comp
      (vonNeumannEquiv T hT hTc).symm.toLinearMap)) 1
    fun h => by
      have hb := norm_apply_le_norm_onePlusAdjointComp hT ((vonNeumannEquiv T hT hTc).symm h)
      rw [onePlusAdjointComp_symm_apply] at hb
      rw [one_mul]
      exact hb

/-- `T Q h = T (Q h)`. -/
theorem boundedOfCompose_apply {T : E →ₗ.[𝕜] F} (hT : Dense (T.domain : Set E))
    (hTc : T.IsClosed) (h : E) :
    boundedOfCompose T hT hTc h =
      T ⟨vonNeumannInverse T hT hTc h, adjointCompDomain_le (vonNeumannInverse_mem hT hTc h)⟩ :=
  rfl

/-- `‖T Q‖ ≤ 1`. -/
theorem norm_boundedOfCompose_le_one {T : E →ₗ.[𝕜] F} (hT : Dense (T.domain : Set E))
    (hTc : T.IsClosed) : ‖boundedOfCompose T hT hTc‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-! ### Self-adjointness of `T†T` -/

omit [CompleteSpace F] in
/-- `T†T` is symmetric. -/
theorem isFormalAdjoint_adjointComp {T : E →ₗ.[𝕜] F} (hT : Dense (T.domain : Set E)) :
    (adjointComp T).IsFormalAdjoint (adjointComp T) := by
  intro x y
  have e1 : ⟪(adjointComp T x : E), (y : E)⟫_𝕜
      = ⟪(T (adjointCompToDomain x) : F), (T (adjointCompToDomain y) : F)⟫_𝕜 :=
    inner_adjointComp hT x (adjointCompToDomain y)
  have e2 : ⟪(adjointComp T y : E), (x : E)⟫_𝕜
      = ⟪(T (adjointCompToDomain y) : F), (T (adjointCompToDomain x) : F)⟫_𝕜 :=
    inner_adjointComp hT y (adjointCompToDomain x)
  rw [e1, ← inner_conj_symm (x : E) (adjointComp T y), e2, inner_conj_symm]

/-- The domain of `T†T` is dense: it contains the range of `Q`, and a vector orthogonal to it
is orthogonal to itself. -/
theorem dense_adjointComp_domain {T : E →ₗ.[𝕜] F} (hT : Dense (T.domain : Set E))
    (hTc : T.IsClosed) : Dense ((adjointComp T).domain : Set E) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    Submodule.eq_bot_iff]
  intro x hx
  obtain ⟨a, rfl⟩ := (vonNeumann_bijective hT hTc).surjective x
  have h0 : ⟪(a : E), onePlusAdjointComp T a⟫_𝕜 = 0 :=
    (Submodule.mem_orthogonal _ _).1 hx _ a.2
  rw [inner_onePlusAdjointComp hT] at h0
  have h1 : ‖(a : E)‖ ^ 2 + ‖(T (adjointCompToDomain a) : F)‖ ^ 2 = 0 := by
    exact_mod_cast h0
  have h2 : (a : E) = 0 := by
    have h3 : ‖(a : E)‖ = 0 := by
      nlinarith [norm_nonneg (a : E), norm_nonneg (T (adjointCompToDomain a) : F)]
    exact norm_eq_zero.1 h3
  have h4 : a = 0 := Subtype.ext h2
  rw [h4, map_zero]

/-- Every vector of the domain of `(T†T)†` lies in `D(T†T)`, with the same value: this is the
heart of von Neumann's theorem.  If `φ ∈ D((T†T)†)`, solve `(1 + T†T) ψ = φ + (T†T)† φ`; then
`φ - ψ` is orthogonal to the range of `1 + T†T`, which is all of `E`. -/
theorem exists_eq_of_mem_adjoint_adjointComp {T : E →ₗ.[𝕜] F} (hT : Dense (T.domain : Set E))
    (hTc : T.IsClosed) (φ : ((adjointComp T).adjoint).domain) :
    ∃ ψ : (adjointComp T).domain, (φ : E) = (ψ : E) ∧
      (adjointComp T).adjoint φ = adjointComp T ψ := by
  have hdense := dense_adjointComp_domain hT hTc
  have hfa := LinearPMap.adjoint_isFormalAdjoint hdense
  have hsym := isFormalAdjoint_adjointComp (T := T) hT
  obtain ⟨ψ, hψ⟩ :=
    (vonNeumann_bijective hT hTc).surjective ((φ : E) + (adjointComp T).adjoint φ)
  have horth : ∀ χ : (adjointComp T).domain,
      ⟪(φ : E) - (ψ : E), onePlusAdjointComp T χ⟫_𝕜 = 0 := by
    intro χ
    have e1 : ⟪(φ : E), onePlusAdjointComp T χ⟫_𝕜
        = ⟪(φ : E) + (adjointComp T).adjoint φ, (χ : E)⟫_𝕜 := by
      rw [onePlusAdjointComp_apply, inner_add_right, inner_add_left, hfa φ χ]
    have e2 : ⟪(ψ : E), onePlusAdjointComp T χ⟫_𝕜
        = ⟪(ψ : E) + adjointComp T ψ, (χ : E)⟫_𝕜 := by
      rw [onePlusAdjointComp_apply, inner_add_right, inner_add_left, hsym ψ χ]
    rw [inner_sub_left, e1, e2, ← hψ, onePlusAdjointComp_apply]
    exact sub_self _
  obtain ⟨χ₀, hχ₀⟩ := (vonNeumann_bijective hT hTc).surjective ((φ : E) - (ψ : E))
  have h0 : ⟪(φ : E) - (ψ : E), (φ : E) - (ψ : E)⟫_𝕜 = 0 := by
    have hz := horth χ₀
    rwa [hχ₀] at hz
  have heq : (φ : E) = (ψ : E) := sub_eq_zero.1 (inner_self_eq_zero.1 h0)
  refine ⟨ψ, heq, ?_⟩
  have hval : (ψ : E) + adjointComp T ψ = (φ : E) + (adjointComp T).adjoint φ := hψ
  rw [heq] at hval
  exact (add_left_cancel hval).symm

/-- **Von Neumann's theorem** (Reed–Simon II, Theorem X.25, p. 180): for a closed densely
defined `T`, the operator `T†T` is self-adjoint on `D(T†T) = {ψ ∈ D(T) | T ψ ∈ D(T†)}`. -/
theorem isSelfAdjoint_adjointComp {T : E →ₗ.[𝕜] F} (hT : Dense (T.domain : Set E))
    (hTc : T.IsClosed) : IsSelfAdjoint (adjointComp T) := by
  rw [LinearPMap.isSelfAdjoint_def]
  have hA : adjointComp T ≤ (adjointComp T).adjoint :=
    (isFormalAdjoint_adjointComp hT).le_adjoint (dense_adjointComp_domain hT hTc)
  have hdom : (adjointComp T).domain = ((adjointComp T).adjoint).domain := by
    refine le_antisymm hA.1 fun x hx => ?_
    obtain ⟨ψ, hψ, -⟩ := exists_eq_of_mem_adjoint_adjointComp hT hTc ⟨x, hx⟩
    rw [show x = (ψ : E) from hψ]
    exact ψ.2
  exact (LinearPMap.eq_of_le_of_domain_eq hA hdom).symm

/-! ### `D(T†T)` is a core of `T` -/

/-- The closure of the graph of `T` restricted to `D(T†T)` is the graph of `T`: a vector of the
graph of `T` orthogonal to all `(χ, T χ)` with `χ ∈ D(T†T)` is orthogonal to the range of
`1 + T†T`, which is all of `E`. -/
theorem graph_domRestrict_topologicalClosure {T : E →ₗ.[𝕜] F} (hT : Dense (T.domain : Set E))
    (hTc : T.IsClosed) :
    (T.domRestrict (adjointCompDomain T)).graph.topologicalClosure = T.graph := by
  have hsub : (T.domRestrict (adjointCompDomain T)).graph.topologicalClosure ≤ T.graph :=
    Submodule.topologicalClosure_minimal _ (LinearPMap.le_graph_of_le LinearPMap.domRestrict_le) hTc
  refine le_antisymm hsub fun w hw => ?_
  have hMclosed : IsClosed
      (((T.domRestrict (adjointCompDomain T)).graph.topologicalClosure.comap
        (WithLp.linearEquiv 2 𝕜 (E × F) : WithLp 2 (E × F) →ₗ[𝕜] E × F) :
          Submodule 𝕜 (WithLp 2 (E × F))) : Set (WithLp 2 (E × F))) :=
    (Submodule.isClosed_topologicalClosure _).preimage (WithLp.prod_continuous_ofLp 2 E F)
  have : CompleteSpace
      ((T.domRestrict (adjointCompDomain T)).graph.topologicalClosure.comap
        (WithLp.linearEquiv 2 𝕜 (E × F) : WithLp 2 (E × F) →ₗ[𝕜] E × F)) :=
    hMclosed.completeSpace_coe
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.exists_add_mem_mem_orthogonal
    (K := (T.domRestrict (adjointCompDomain T)).graph.topologicalClosure.comap
      (WithLp.linearEquiv 2 𝕜 (E × F) : WithLp 2 (E × F) →ₗ[𝕜] E × F)) (toLp 2 w)
  have hsum : w = ofLp y + ofLp z := by simpa using congrArg (ofLp (p := 2)) hyz
  have hzT : ofLp z ∈ T.graph := by
    have h1 : ofLp z = w - ofLp y := by rw [hsum]; abel
    rw [h1]
    exact sub_mem hw (hsub hy)
  rw [LinearPMap.mem_graph_iff] at hzT
  obtain ⟨c, hc1, hc2⟩ := hzT
  have hperp : ∀ χ : (adjointComp T).domain, ⟪onePlusAdjointComp T χ, (c : E)⟫_𝕜 = 0 := by
    intro χ
    have hχS : ((χ : E), (T (adjointCompToDomain χ) : F))
        ∈ (T.domRestrict (adjointCompDomain T)).graph := by
      rw [LinearPMap.mem_graph_iff]
      refine ⟨⟨(χ : E), ⟨χ.2, adjointCompDomain_le χ.2⟩⟩, rfl, ?_⟩
      exact LinearPMap.domRestrict_apply rfl
    have hmemM := (T.domRestrict (adjointCompDomain T)).graph.le_topologicalClosure hχS
    have hzero := (Submodule.mem_orthogonal _ _).1 hz (toLp 2 ((χ : E),
      (T (adjointCompToDomain χ) : F))) hmemM
    rw [WithLp.prod_inner_apply] at hzero
    rw [← hc1, ← hc2] at hzero
    rw [onePlusAdjointComp_apply, inner_add_left, inner_adjointComp hT χ c]
    exact hzero
  obtain ⟨χ₀, hχ₀⟩ := (vonNeumann_bijective hT hTc).surjective (c : E)
  have hc0 : (c : E) = 0 := by
    have := hperp χ₀
    rw [hχ₀] at this
    exact inner_self_eq_zero.1 this
  have hz0 : z = 0 := by
    have h2 : ofLp z = 0 := by
      have hc : c = 0 := Subtype.ext hc0
      refine Prod.ext ?_ ?_
      · rw [← hc1, hc0]; rfl
      · rw [← hc2, hc]
        exact map_zero T.toFun
    exact (WithLp.ofLp_injective (p := 2)) h2
  have : w = ofLp y := by rw [hsum, hz0]; simp
  rw [this]
  exact hy

/-- `D(T†T)` is a core of `T` (Reed–Simon II, Theorem X.25, p. 180). -/
theorem hasCore_adjointCompDomain {T : E →ₗ.[𝕜] F} (hT : Dense (T.domain : Set E))
    (hTc : T.IsClosed) : T.HasCore (adjointCompDomain T) := by
  refine ⟨adjointCompDomain_le, ?_⟩
  have hcl : (T.domRestrict (adjointCompDomain T)).IsClosable :=
    LinearPMap.isClosable_iff_exists_closed_extension.2 ⟨T, hTc, LinearPMap.domRestrict_le⟩
  refine LinearPMap.eq_of_eq_graph ?_
  rw [← hcl.graph_closure_eq_closure_graph]
  exact graph_domRestrict_topologicalClosure hT hTc

end SpectralTheorem
