import SpectralTheorem.VonNeumann
import SpectralTheorem.NormalPMap
import SpectralTheorem.NormalSpectral
import SpectralTheorem.CommutativeSpectral

/-!
# The spectral theorem for an arbitrary unbounded normal operator

**Rudin, *Functional Analysis*, Theorem 13.33.**  Every closed densely defined normal operator
`N` on a complex Hilbert space is `∫ z dP` for a projection-valued measure `P` on `ℂ`.  Nothing
is assumed about the spectrum of `N`, which may be all of `ℂ`; the resolvent route of
`SpectralTheorem.NormalSpectral` therefore does not apply, and the proof goes through von
Neumann's theorem (`SpectralTheorem.VonNeumann`) for the bounded operators
`Q = (1 + N† N)⁻¹` and `S = N Q`, and the joint spectral theorem
(`SpectralTheorem.CommutativeSpectral`) for the star-commuting pair `(Q, S)`.

Proofs.
* **`N†† = N` for a closed densely defined `N` whose adjoint is densely defined.**  One
  inclusion is formal: `N†` is a formal adjoint of `N`, so `N ≤ N††`.  For the other, the graph
  of `N` is a closed subspace of `H ⊕₂ H`, hence equal to its double orthogonal complement, and
  the orthogonal complement of the graph of `N` is described by `N†`
  (`SpectralTheorem.mem_graphL2_orthogonal`): if `(a, b)` is orthogonal to the graph of `N` then
  `b ∈ D(N†)` and `N† b = -a`, so for `ψ ∈ D(N††)` with `η = N†† ψ` the formal adjoint identity
  gives `⟪η, b⟫ = ⟪ψ, N† b⟫ = -⟪ψ, a⟫`, that is `⟪(a, b), (ψ, η)⟫ = 0`.  Hence `(ψ, η)` lies in
  the double orthogonal complement of the graph, which is the graph.
* **Normality passes to inner products**: `‖N ψ‖ = ‖N† ψ‖` on `D(N) = D(N†)` gives
  `⟪N ψ, N φ⟫ = ⟪N† ψ, N† φ⟫` by the polarization identity, because `N (ψ + c φ) = N ψ + c N φ`.
* **`N† N = N N†`.**  Here `N N†` means `adjointComp N† = N†† N†`, which is legitimate because
  `N†† = N`.  For `x ∈ D(N) = D(N†)`, the vector `N x` lies in `D(N†)` exactly when
  `χ ↦ ⟪N x, N χ⟫` is represented by a vector of `H`, and `N† x` lies in `D(N††)` exactly when
  `χ ↦ ⟪N† x, N† χ⟫` is; these two forms coincide, so the domains agree.  On the common domain
  both values have the inner product `⟪N x, N χ⟫` against every `χ ∈ D(N)`, which is dense.
  Consequently `Q = (1 + N† N)⁻¹ = (1 + N N†)⁻¹`, since the von Neumann inverse depends only on
  the operator being inverted.
* **`N Q = Q N` on `D(N)`.**  Put `u = Q ψ`, so `u + N† (N u) = ψ`; then `N† (N u) = ψ - u`
  lies in `D(N) = D(N††)`, so `N u ∈ D(N N†)` and `(1 + N N†) (N u) = N u + N (ψ - u) = N ψ`.
  Applying `(1 + N N†)⁻¹ = Q` gives `N u = Q (N ψ)`.  As `N†` is again normal, the same holds
  for `N†`.
* **`S† = N† Q`, and `S` is normal.**  For `χ ∈ D(N†)`,
  `⟪S φ, χ⟫ = ⟪N (Q φ), χ⟫ = ⟪Q φ, N† χ⟫ = ⟪φ, Q (N† χ)⟫ = ⟪φ, N† (Q χ)⟫`, and both sides are
  continuous in `χ` while `D(N†)` is dense.  Then `S† S φ = N† (N (Q² φ)) = Q φ - Q² φ` and
  `S S† φ = N (N† (Q² φ)) = Q φ - Q² φ` by `N† N = N N†`, so `S` is normal; likewise `S Q = Q S`
  and `S† Q = Q S†`.
* **The p.v.m.**  The joint spectral theorem for the star-commuting pair `(Q, S)` gives a p.v.m.
  `P₂` on `ℂ²` with `Q = ∫ z₀ dP₂` and `S = ∫ z₁ dP₂`, carried by the joint spectrum.  Since `Q`
  is injective, `Q P₂{z₀ = 0} = ∫ z₀ 1_{z₀ = 0} dP₂ = 0` forces `P₂{z₀ = 0} = 0`, so `P₂` is
  carried by the good set `G` where `z₀ ≠ 0`, `|z₀| ≤ ‖Q‖` and `|z₁| ≤ ‖S‖`.  On all of `ℂ²`
  the bounded functions `z₀ 1_G` and `z₁ 1_G` then satisfy `z₁ 1_G = F (z₀ 1_G)` exactly, for
  the quotient coordinate `F`; so `Q φ` lies in the domain of `M = ∫ F dP₂` and
  `M (Q φ) = S φ = N (Q φ)`.  As `Ran Q = D(N† N)` is a core of `N` and `M` is closed,
  `N ≤ M`; and a normal operator has no proper normal extension, because `N ≤ M` gives
  `M† ≤ N†`, so `D(M) = D(M†) ≤ D(N†) = D(N)`.  Hence `N = M = ∫ z d(F_* P₂)`.

## Main definitions and results

* `SpectralTheorem.adjoint_le_adjoint`: the adjoint is antitone, `S ≤ T → T† ≤ S†`;
  `SpectralTheorem.le_adjoint_adjoint`: `T ≤ T††`;
  `SpectralTheorem.adjoint_adjoint`: `T†† = T` for a closed densely defined `T` with densely
  defined adjoint.
* `SpectralTheorem.inner_eq_of_norm_eq`: two linear maps into a complex inner product space with
  the same norms have the same inner products.
* `SpectralTheorem.IsNormalPMap.adjoint_adjoint`, `IsNormalPMap.adjoint`: `N†† = N` and `N†` is
  normal; `IsNormalPMap.inner_apply`: `⟪N ψ, N φ⟫ = ⟪N† ψ, N† φ⟫`.
* `SpectralTheorem.IsNormalPMap.eq_of_le`: a normal operator has no proper normal extension.
* `SpectralTheorem.IsNormalPMap.adjointComp_adjoint`: `N† N = N N†`;
  `SpectralTheorem.vonNeumannInverse_congr` and
  `SpectralTheorem.IsNormalPMap.vonNeumannInverse_adjoint_eq`: `(1 + N N†)⁻¹ = (1 + N† N)⁻¹`.
* `SpectralTheorem.IsNormalPMap.vonNeumannQ`, `IsNormalPMap.vonNeumannS`: the bounded operators
  `Q` and `S`, with `IsNormalPMap.commute_vonNeumannInverse` and
  `IsNormalPMap.commute_vonNeumannInverse_adjoint`: `N Q = Q N` and `N† Q = Q N†`.
* `SpectralTheorem.IsNormalPMap.adjoint_vonNeumannS`: `S† = N† Q`;
  `IsNormalPMap.isStarNormal_vonNeumannS`: `S` is normal;
  `IsNormalPMap.commute_vonNeumannQ_S`, `IsNormalPMap.commute_vonNeumannQ_star_S`: `Q` and `S`
  star-commute.
* `SpectralTheorem.IsNormalPMap.pairPVM`: the joint p.v.m. of `(Q, S)` on `ℂ²`, with
  `IsNormalPMap.integral_pairPVM_zero`, `IsNormalPMap.integral_pairPVM_one`,
  `IsNormalPMap.pairPVM_coordZero` and `IsNormalPMap.pairPVM_goodSet`.
* `SpectralTheorem.IsNormalPMap.normalPVM`: the p.v.m. of `N` on `ℂ`, with
  `IsNormalPMap.le_integralPMap`: `N ≤ ∫ z dP`.
* **`SpectralTheorem.IsNormalPMap.exists_pvm`**: `N = ∫ z dP` for a projection-valued measure
  `P` on `ℂ` — the spectral theorem for an arbitrary unbounded normal operator.
-/

noncomputable section

open scoped InnerProductSpace ComplexConjugate
open WithLp

universe u

namespace SpectralTheorem

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### The adjoint is antitone -/

/-- **The adjoint is antitone**: an extension has a smaller adjoint.  If `y ∈ D(T†)` then
`⟪T† y, x⟫ = ⟪y, T x⟫ = ⟪y, S x⟫` for `x ∈ D(S) ⊆ D(T)`, so `y ∈ D(S†)` and `S† y = T† y`. -/
theorem adjoint_le_adjoint {S T : H →ₗ.[ℂ] H} (hS : Dense (S.domain : Set H)) (h : S ≤ T) :
    LinearPMap.adjoint T ≤ LinearPMap.adjoint S := by
  have hT : Dense (T.domain : Set H) := hS.mono fun _ hx => h.1 hx
  have key : ∀ (y : H) (hy : y ∈ (LinearPMap.adjoint T).domain) (x : S.domain),
      ⟪(LinearPMap.adjoint T ⟨y, hy⟩ : H), (x : H)⟫_ℂ = ⟪y, (S x : H)⟫_ℂ := by
    intro y hy x
    have hx : (x : H) ∈ T.domain := h.1 x.2
    have hval : (S x : H) = T ⟨(x : H), hx⟩ := h.2 rfl
    rw [hval]
    exact LinearPMap.adjoint_isFormalAdjoint hT ⟨y, hy⟩ ⟨(x : H), hx⟩
  refine ⟨fun y hy => LinearPMap.mem_adjoint_domain_of_exists _
    ⟨LinearPMap.adjoint T ⟨y, hy⟩, key y hy⟩, ?_⟩
  intro y z hyz
  refine (LinearPMap.adjoint_apply_eq hS z fun x => ?_).symm
  rw [← hyz]
  exact key (y : H) y.2 x

/-- `T` is contained in its double adjoint, because `T†` is a formal adjoint of `T`. -/
theorem le_adjoint_adjoint {T : H →ₗ.[ℂ] H} (hT : Dense (T.domain : Set H))
    (hTd : Dense ((LinearPMap.adjoint T).domain : Set H)) :
    T ≤ LinearPMap.adjoint (LinearPMap.adjoint T) :=
  LinearPMap.IsFormalAdjoint.le_adjoint hTd (LinearPMap.adjoint_isFormalAdjoint hT)

/-! ### The double adjoint of a closed operator -/

/-- **`T†† = T`** for a closed densely defined `T` whose adjoint is densely defined.  The graph
of `T` is closed, so it equals its double orthogonal complement in `H ⊕₂ H`; the orthogonal
complement of the graph is described by `T†`, and the formal adjoint identity for `T††` says
exactly that the graph of `T††` is orthogonal to it. -/
theorem adjoint_adjoint {T : H →ₗ.[ℂ] H} (hT : Dense (T.domain : Set H))
    (hTd : Dense ((LinearPMap.adjoint T).domain : Set H)) (hTc : T.IsClosed) :
    LinearPMap.adjoint (LinearPMap.adjoint T) = T := by
  have hcomp : CompleteSpace (graphL2 T) := (isClosed_graphL2 hTc).completeSpace_coe
  have hfa := LinearPMap.adjoint_isFormalAdjoint hTd
  have hgr : ∀ (ψ : H) (hψ : ψ ∈ (LinearPMap.adjoint (LinearPMap.adjoint T)).domain),
      ∃ h : ψ ∈ T.domain,
        (T ⟨ψ, h⟩ : H) = LinearPMap.adjoint (LinearPMap.adjoint T) ⟨ψ, hψ⟩ := by
    intro ψ hψ
    set η : H := LinearPMap.adjoint (LinearPMap.adjoint T) ⟨ψ, hψ⟩ with hη
    have hmem : (toLp 2 (ψ, η) : WithLp 2 (H × H)) ∈ (graphL2 T)ᗮᗮ := by
      rw [Submodule.mem_orthogonal]
      intro u hu
      obtain ⟨hb, hval⟩ := (mem_graphL2_orthogonal hT).1 hu
      have h1 : ⟪η, (ofLp u).2⟫_ℂ = ⟪ψ, -(ofLp u).1⟫_ℂ := by
        rw [← hval, hη]
        exact hfa ⟨ψ, hψ⟩ ⟨(ofLp u).2, hb⟩
      have h2 : ⟪(ofLp u).2, η⟫_ℂ = -⟪(ofLp u).1, ψ⟫_ℂ := by
        rw [← inner_conj_symm ((ofLp u).2) η, h1, inner_neg_right, map_neg, inner_conj_symm]
      rw [WithLp.prod_inner_apply]
      exact h2.symm ▸ add_neg_cancel ⟪(ofLp u).1, ψ⟫_ℂ
    rw [Submodule.orthogonal_orthogonal] at hmem
    have hmem' : ((ψ, η) : H × H) ∈ T.graph := (mem_graphL2 (T := T)).1 hmem
    obtain ⟨z, hz1, hz2⟩ := (LinearPMap.mem_graph_iff T).1 hmem'
    have hz1' : (z : H) = ψ := hz1
    have hz2' : (T z : H) = η := hz2
    have hψT : ψ ∈ T.domain := by rw [← hz1']; exact z.2
    refine ⟨hψT, ?_⟩
    rw [← hz2']
    exact congrArg (fun w : T.domain => (T w : H)) (Subtype.ext hz1'.symm)
  refine le_antisymm ?_ (le_adjoint_adjoint hT hTd)
  refine ⟨fun ψ hψ => (hgr ψ hψ).choose, ?_⟩
  intro x y hxy
  obtain ⟨hx1, hx2⟩ := hgr (x : H) x.2
  have hy : y = ⟨(x : H), hx1⟩ := Subtype.ext hxy.symm
  rw [hy]
  exact hx2.symm

/-! ### Consequences for normal operators -/

namespace IsNormalPMap

variable {N : H →ₗ.[ℂ] H}

/-- The adjoint of a normal operator is densely defined, its domain being `D(N)`. -/
theorem adjoint_dense (hN : IsNormalPMap N) :
    Dense ((LinearPMap.adjoint N).domain : Set H) := by
  rw [hN.adjoint_domain]
  exact hN.dense_domain

/-- **`N†† = N`** for a normal operator: `N` is closed and both `N` and `N†` are densely
defined. -/
theorem adjoint_adjoint (hN : IsNormalPMap N) :
    LinearPMap.adjoint (LinearPMap.adjoint N) = N :=
  SpectralTheorem.adjoint_adjoint hN.dense_domain hN.adjoint_dense hN.isClosed

/-- **A normal operator has no proper normal extension.**  If `N ≤ M` then `M† ≤ N†`, so
`D(M) = D(M†) ≤ D(N†) = D(N)`; the reverse inclusion is `N ≤ M`, and the values agree. -/
theorem eq_of_le {M : H →ₗ.[ℂ] H} (hN : IsNormalPMap N) (hM : IsNormalPMap M) (hle : N ≤ M) :
    N = M := by
  have hdom : M.domain ≤ N.domain := by
    rw [← hM.adjoint_domain, ← hN.adjoint_domain]
    exact (adjoint_le_adjoint hN.dense_domain hle).1
  exact LinearPMap.eq_of_le_of_domain_eq hle (le_antisymm hle.1 hdom)

/-- `D(N††) = D(N)`. -/
theorem adjoint_adjoint_domain (hN : IsNormalPMap N) :
    (LinearPMap.adjoint (LinearPMap.adjoint N)).domain = N.domain :=
  congrArg LinearPMap.domain hN.adjoint_adjoint

/-! ### Normality and inner products -/

/-- `N†`, restricted to `D(N) = D(N†)`, as a linear map on `D(N)`. -/
def adjointRestrict (hN : IsNormalPMap N) : N.domain →ₗ[ℂ] H :=
  (LinearPMap.adjoint N).toFun.comp (Submodule.inclusion hN.adjoint_domain.ge)

theorem adjointRestrict_apply (hN : IsNormalPMap N) (ψ : N.domain) :
    hN.adjointRestrict ψ = LinearPMap.adjoint N ⟨(ψ : H), hN.mem_adjoint_domain ψ.2⟩ := rfl

/-- `⟪N† ψ, φ⟫ = ⟪ψ, N φ⟫` on `D(N)`. -/
theorem inner_adjointRestrict_left (hN : IsNormalPMap N) (ψ φ : N.domain) :
    ⟪hN.adjointRestrict ψ, (φ : H)⟫_ℂ = ⟪(ψ : H), (N φ : H)⟫_ℂ :=
  LinearPMap.adjoint_isFormalAdjoint hN.dense_domain
    ⟨(ψ : H), hN.mem_adjoint_domain ψ.2⟩ φ

/-- `⟪N ψ, φ⟫ = ⟪ψ, N† φ⟫` on `D(N)`, the conjugate of `inner_adjointRestrict_left`. -/
theorem inner_adjointRestrict_right (hN : IsNormalPMap N) (ψ φ : N.domain) :
    ⟪(N ψ : H), (φ : H)⟫_ℂ = ⟪(ψ : H), hN.adjointRestrict φ⟫_ℂ := by
  calc ⟪(N ψ : H), (φ : H)⟫_ℂ = conj ⟪(φ : H), (N ψ : H)⟫_ℂ := (inner_conj_symm _ _).symm
    _ = conj ⟪hN.adjointRestrict φ, (ψ : H)⟫_ℂ := by rw [hN.inner_adjointRestrict_left φ ψ]
    _ = ⟪(ψ : H), hN.adjointRestrict φ⟫_ℂ := inner_conj_symm _ _

end IsNormalPMap

omit [CompleteSpace H] in
/-- Equal vectors have equal images under a partially defined operator. -/
theorem linearPMap_apply_congr {T : H →ₗ.[ℂ] H} {x y : H} (h : x = y) (hx : x ∈ T.domain)
    (hy : y ∈ T.domain) : (T ⟨x, hx⟩ : H) = (T ⟨y, hy⟩ : H) :=
  congrArg (fun w : T.domain => (T w : H)) (Subtype.ext h)

omit [CompleteSpace H] in
/-- Two linear maps into a complex inner product space with the same norms have the same inner
products, by the polarization identity. -/
theorem inner_eq_of_norm_eq {V : Type*} [AddCommGroup V] [Module ℂ V] {f g : V →ₗ[ℂ] H}
    (h : ∀ v, ‖f v‖ = ‖g v‖) (v w : V) : ⟪f v, f w⟫_ℂ = ⟪g v, g w⟫_ℂ := by
  have e1 : ‖f v + f w‖ = ‖g v + g w‖ := by rw [← map_add, ← map_add, h]
  have e2 : ‖f v - f w‖ = ‖g v - g w‖ := by rw [← map_sub, ← map_sub, h]
  have e3 : ‖f v - (RCLike.I : ℂ) • f w‖ = ‖g v - (RCLike.I : ℂ) • g w‖ := by
    rw [← map_smul, ← map_smul, ← map_sub, ← map_sub, h]
  have e4 : ‖f v + (RCLike.I : ℂ) • f w‖ = ‖g v + (RCLike.I : ℂ) • g w‖ := by
    rw [← map_smul, ← map_smul, ← map_add, ← map_add, h]
  rw [inner_eq_sum_norm_sq_div_four, inner_eq_sum_norm_sq_div_four, e1, e2, e3, e4]

namespace IsNormalPMap

variable {N : H →ₗ.[ℂ] H}

/-- **`⟪N ψ, N φ⟫ = ⟪N† ψ, N† φ⟫`** for a normal operator, by polarization from
`‖N ψ‖ = ‖N† ψ‖`. -/
theorem inner_apply (hN : IsNormalPMap N) (ψ φ : N.domain) :
    ⟪(N ψ : H), (N φ : H)⟫_ℂ = ⟪hN.adjointRestrict ψ, hN.adjointRestrict φ⟫_ℂ :=
  inner_eq_of_norm_eq (f := N.toFun) (g := hN.adjointRestrict) hN.norm_apply ψ φ

/-! ### `N† N = N N†` -/

/-- For `x ∈ D(N)`, `N† x ∈ D(N††)` if and only if `N x ∈ D(N†)`: both say that
`χ ↦ ⟪N x, N χ⟫ = ⟪N† x, N† χ⟫` is represented by a vector. -/
theorem mem_adjoint_domain_adjointRestrict_iff (hN : IsNormalPMap N) (x : H)
    (hx : x ∈ N.domain) :
    hN.adjointRestrict ⟨x, hx⟩ ∈ (LinearPMap.adjoint (LinearPMap.adjoint N)).domain ↔
      (N ⟨x, hx⟩ : H) ∈ (LinearPMap.adjoint N).domain := by
  have hd : (LinearPMap.adjoint N).domain = N.domain := hN.adjoint_domain
  constructor
  · intro hu
    have hu' : hN.adjointRestrict ⟨x, hx⟩ ∈ N.domain := hN.adjoint_adjoint_domain.le hu
    refine LinearPMap.mem_adjoint_domain_of_exists _ ⟨N ⟨_, hu'⟩, fun χ => ?_⟩
    exact (hN.inner_adjointRestrict_right ⟨_, hu'⟩ χ).trans (hN.inner_apply ⟨x, hx⟩ χ).symm
  · intro hv
    refine LinearPMap.mem_adjoint_domain_of_exists _
      ⟨hN.adjointRestrict ⟨(N ⟨x, hx⟩ : H), hd.le hv⟩, fun χ => ?_⟩
    exact (hN.inner_adjointRestrict_left ⟨_, hd.le hv⟩ ⟨(χ : H), hd.le χ.2⟩).trans
      (hN.inner_apply ⟨x, hx⟩ ⟨(χ : H), hd.le χ.2⟩)

/-- **`N N† = N† N`** for a normal operator, as partially defined operators.  The two domains
agree by `mem_adjoint_domain_adjointRestrict_iff`, and the values agree because both have the
same inner products against the dense set `D(N)`. -/
theorem adjointComp_adjoint (hN : IsNormalPMap N) :
    adjointComp (LinearPMap.adjoint N) = adjointComp N := by
  have hd : (LinearPMap.adjoint N).domain = N.domain := hN.adjoint_domain
  have hdom : adjointCompDomain (LinearPMap.adjoint N) = adjointCompDomain N := by
    ext x
    constructor
    · rintro ⟨h, hx2⟩
      exact ⟨hd.le h, (hN.mem_adjoint_domain_adjointRestrict_iff x (hd.le h)).1 hx2⟩
    · rintro ⟨hx, hv⟩
      exact ⟨hN.mem_adjoint_domain hx,
        (hN.mem_adjoint_domain_adjointRestrict_iff x hx).2 hv⟩
  refine LinearPMap.ext hdom ?_
  intro x hf hg
  have hx : x ∈ N.domain := adjointCompDomain_le hg
  have hv : (N ⟨x, hx⟩ : H) ∈ (LinearPMap.adjoint N).domain :=
    (mem_adjointComp_domain.1 hg).choose_spec
  have hu : hN.adjointRestrict ⟨x, hx⟩ ∈ N.domain :=
    hN.adjoint_adjoint_domain.le (mem_adjointComp_domain.1 hf).choose_spec
  have hL : (adjointComp (LinearPMap.adjoint N) ⟨x, hf⟩ : H)
      = (N ⟨hN.adjointRestrict ⟨x, hx⟩, hu⟩ : H) :=
    linearPMap_apply_eq_of_eq hN.adjoint_adjoint _ hu
  refine hN.dense_domain.eq_of_inner_left ℂ fun χ hχ => ?_
  rw [hL]
  have e1 := hN.inner_adjointRestrict_right ⟨_, hu⟩ ⟨χ, hχ⟩
  have e2 := hN.inner_apply ⟨x, hx⟩ ⟨χ, hχ⟩
  have e3 := hN.inner_adjointRestrict_left ⟨(N ⟨x, hx⟩ : H), hd.le hv⟩ ⟨χ, hχ⟩
  exact e1.trans (e2.symm.trans e3.symm)

end IsNormalPMap

/-! ### The von Neumann inverse depends only on `T† T` -/

/-- `Q = (1 + T† T)⁻¹` depends only on the operator `T† T`: if `y = Q₁ h` then
`y + (T₂† T₂) y = y + (T₁† T₁) y = h`, so `Q₂ h = y`. -/
theorem vonNeumannInverse_congr {T₁ T₂ : H →ₗ.[ℂ] H} (h₁ : Dense (T₁.domain : Set H))
    (c₁ : T₁.IsClosed) (h₂ : Dense (T₂.domain : Set H)) (c₂ : T₂.IsClosed)
    (he : adjointComp T₁ = adjointComp T₂) :
    vonNeumannInverse T₁ h₁ c₁ = vonNeumannInverse T₂ h₂ c₂ := by
  refine ContinuousLinearMap.ext fun h => ?_
  have hm1 : vonNeumannInverse T₁ h₁ c₁ h ∈ (adjointComp T₁).domain :=
    vonNeumannInverse_mem h₁ c₁ h
  have hm2 : vonNeumannInverse T₁ h₁ c₁ h ∈ (adjointComp T₂).domain :=
    (congrArg LinearPMap.domain he).le hm1
  have key : (onePlusAdjointComp T₂ ⟨_, hm2⟩ : H) = h := by
    rw [onePlusAdjointComp_apply, ← linearPMap_apply_eq_of_eq he hm1 hm2]
    exact add_adjointComp_vonNeumannInverse h₁ c₁ h
  have hfin := vonNeumannInverse_onePlusAdjointComp h₂ c₂ (⟨_, hm2⟩ : (adjointComp T₂).domain)
  rw [key] at hfin
  exact hfin.symm

namespace IsNormalPMap

variable {N : H →ₗ.[ℂ] H}

/-! ### The bounded operators `Q` and `S` of a normal operator -/

/-- `Q = (1 + N† N)⁻¹`, the bounded operator of von Neumann's theorem for a normal `N`. -/
def vonNeumannQ (hN : IsNormalPMap N) : H →L[ℂ] H :=
  vonNeumannInverse N hN.dense_domain hN.isClosed

/-- `S = N Q`, a bounded operator of norm at most `1`. -/
def vonNeumannS (hN : IsNormalPMap N) : H →L[ℂ] H :=
  boundedOfCompose N hN.dense_domain hN.isClosed

theorem vonNeumannQ_mem (hN : IsNormalPMap N) (h : H) :
    hN.vonNeumannQ h ∈ (adjointComp N).domain :=
  vonNeumannInverse_mem hN.dense_domain hN.isClosed h

theorem vonNeumannQ_mem_domain (hN : IsNormalPMap N) (h : H) : hN.vonNeumannQ h ∈ N.domain :=
  adjointCompDomain_le (hN.vonNeumannQ_mem h)

/-- `S h = N (Q h)`. -/
theorem vonNeumannS_apply (hN : IsNormalPMap N) (h : H) :
    hN.vonNeumannS h = (N ⟨hN.vonNeumannQ h, hN.vonNeumannQ_mem_domain h⟩ : H) := rfl

/-- `(1 + N† N) (Q h) = h`. -/
theorem add_adjointComp_vonNeumannQ (hN : IsNormalPMap N) (h : H) :
    hN.vonNeumannQ h + (adjointComp N ⟨hN.vonNeumannQ h, hN.vonNeumannQ_mem h⟩ : H) = h :=
  add_adjointComp_vonNeumannInverse hN.dense_domain hN.isClosed h

/-- `⟪Q a, b⟫ = ⟪a, Q b⟫`. -/
theorem inner_vonNeumannQ (hN : IsNormalPMap N) (a b : H) :
    ⟪hN.vonNeumannQ a, b⟫_ℂ = ⟪a, hN.vonNeumannQ b⟫_ℂ :=
  (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1
    (isSelfAdjoint_vonNeumannInverse hN.dense_domain hN.isClosed)) a b

/-! ### The adjoint of a normal operator is normal -/

/-- **`N†` is normal when `N` is**: `D(N††) = D(N) = D(N†)` and `‖N† ψ‖ = ‖N ψ‖`. -/
theorem adjoint (hN : IsNormalPMap N) : IsNormalPMap (LinearPMap.adjoint N) where
  dense_domain := hN.adjoint_dense
  adjoint_domain := hN.adjoint_adjoint_domain.trans hN.adjoint_domain.symm
  norm_apply ψ := by
    have hψ : (ψ : H) ∈ N.domain := hN.adjoint_domain.le ψ.2
    refine (hN.norm_apply ⟨(ψ : H), hψ⟩).symm.trans (congrArg norm ?_)
    exact (linearPMap_apply_eq_of_eq hN.adjoint_adjoint _ hψ).symm

/-- `Q` is the same for `N` and for `N†`, because `N† N = N N†`. -/
theorem vonNeumannQ_adjoint (hN : IsNormalPMap N) : hN.adjoint.vonNeumannQ = hN.vonNeumannQ :=
  vonNeumannInverse_congr _ _ _ _ hN.adjointComp_adjoint

/-- **`(1 + N N†)⁻¹ = (1 + N† N)⁻¹`.** -/
theorem vonNeumannInverse_adjoint_eq (hN : IsNormalPMap N) :
    vonNeumannInverse (LinearPMap.adjoint N) hN.adjoint_dense
        (LinearPMap.adjoint_isClosed hN.dense_domain)
      = vonNeumannInverse N hN.dense_domain hN.isClosed :=
  vonNeumannInverse_congr _ _ _ _ hN.adjointComp_adjoint

/-! ### Commutation of `N` with `Q` -/

/-- **`N (Q ψ) = Q (N ψ)` for `ψ ∈ D(N)`.**  Put `u = Q ψ`, so `u + N† (N u) = ψ`; then
`N† (N u) = ψ - u ∈ D(N) = D(N††)`, so `N u ∈ D(N N†)` and
`(1 + N N†) (N u) = N u + N (ψ - u) = N ψ`.  Applying `(1 + N N†)⁻¹ = Q` gives `N u = Q (N ψ)`. -/
theorem commute_vonNeumannInverse (hN : IsNormalPMap N) {ψ : H} (hψ : ψ ∈ N.domain) :
    hN.vonNeumannS ψ = hN.vonNeumannQ (N ⟨ψ, hψ⟩) := by
  have hu : hN.vonNeumannQ ψ ∈ (adjointComp N).domain := hN.vonNeumannQ_mem ψ
  have hu1 : hN.vonNeumannQ ψ ∈ N.domain := hN.vonNeumannQ_mem_domain ψ
  have hNu : (N ⟨hN.vonNeumannQ ψ, hu1⟩ : H) ∈ (LinearPMap.adjoint N).domain :=
    (mem_adjointComp_domain.1 hu).choose_spec
  have hdiff : (LinearPMap.adjoint N ⟨(N ⟨hN.vonNeumannQ ψ, hu1⟩ : H), hNu⟩ : H)
      = ψ - hN.vonNeumannQ ψ := eq_sub_of_add_eq' (hN.add_adjointComp_vonNeumannQ ψ)
  have hψu : ψ - hN.vonNeumannQ ψ ∈ N.domain := sub_mem hψ hu1
  have hq : (LinearPMap.adjoint N ⟨(N ⟨hN.vonNeumannQ ψ, hu1⟩ : H), hNu⟩ : H) ∈ N.domain := by
    rw [hdiff]
    exact hψu
  have hmem2 : (N ⟨hN.vonNeumannQ ψ, hu1⟩ : H) ∈ (adjointComp (LinearPMap.adjoint N)).domain :=
    ⟨hNu, hN.adjoint_adjoint_domain.ge hq⟩
  have hmapsub : (N ⟨ψ - hN.vonNeumannQ ψ, hψu⟩ : H)
      = (N ⟨ψ, hψ⟩ : H) - (N ⟨hN.vonNeumannQ ψ, hu1⟩ : H) :=
    LinearPMap.map_sub N ⟨ψ, hψ⟩ ⟨hN.vonNeumannQ ψ, hu1⟩
  have hval2 : (adjointComp (LinearPMap.adjoint N)
        ⟨(N ⟨hN.vonNeumannQ ψ, hu1⟩ : H), hmem2⟩ : H)
      = (N ⟨ψ - hN.vonNeumannQ ψ, hψu⟩ : H) := by
    refine (linearPMap_apply_eq_of_eq hN.adjoint_adjoint
      (hN.adjoint_adjoint_domain.ge hq) hq).trans ?_
    exact congrArg (fun w : N.domain => (N w : H)) (Subtype.ext hdiff)
  have hsum : (onePlusAdjointComp (LinearPMap.adjoint N)
      ⟨(N ⟨hN.vonNeumannQ ψ, hu1⟩ : H), hmem2⟩ : H) = (N ⟨ψ, hψ⟩ : H) := by
    rw [onePlusAdjointComp_apply, hval2, hmapsub]
    abel
  have hfin := vonNeumannInverse_onePlusAdjointComp hN.adjoint_dense
    (LinearPMap.adjoint_isClosed hN.dense_domain)
    (⟨(N ⟨hN.vonNeumannQ ψ, hu1⟩ : H), hmem2⟩ : (adjointComp (LinearPMap.adjoint N)).domain)
  rw [hsum, hN.vonNeumannInverse_adjoint_eq] at hfin
  exact hfin.symm

/-- `N† Q h = S† h`, where `S†` is the operator `S` of the normal operator `N†`. -/
theorem vonNeumannS_adjoint_apply (hN : IsNormalPMap N) (h : H) :
    hN.adjoint.vonNeumannS h = (LinearPMap.adjoint N
      ⟨hN.vonNeumannQ h, hN.mem_adjoint_domain (hN.vonNeumannQ_mem_domain h)⟩ : H) := by
  have e : hN.adjoint.vonNeumannQ h = hN.vonNeumannQ h :=
    DFunLike.congr_fun hN.vonNeumannQ_adjoint h
  rw [hN.adjoint.vonNeumannS_apply]
  exact congrArg (fun w : (LinearPMap.adjoint N).domain => (LinearPMap.adjoint N w : H))
    (Subtype.ext e)

/-- **`N† (Q ψ) = Q (N† ψ)` for `ψ ∈ D(N†)`**, the same statement applied to the normal
operator `N†`. -/
theorem commute_vonNeumannInverse_adjoint (hN : IsNormalPMap N) {ψ : H}
    (hψ : ψ ∈ (LinearPMap.adjoint N).domain) :
    hN.adjoint.vonNeumannS ψ = hN.vonNeumannQ (LinearPMap.adjoint N ⟨ψ, hψ⟩) := by
  rw [← hN.vonNeumannQ_adjoint]
  exact hN.adjoint.commute_vonNeumannInverse hψ

/-! ### `S† = N† Q`, and `S` is normal -/

/-- **`S† = N† Q`.**  For `χ ∈ D(N†) = D(N)`,
`⟪S φ, χ⟫ = ⟪N (Q φ), χ⟫ = ⟪Q φ, N† χ⟫ = ⟪φ, Q (N† χ)⟫ = ⟪φ, N† (Q χ)⟫` by the commutation of
`N†` with `Q`; both sides are continuous in `χ` and `D(N†)` is dense. -/
theorem adjoint_vonNeumannS (hN : IsNormalPMap N) :
    ContinuousLinearMap.adjoint hN.vonNeumannS = hN.adjoint.vonNeumannS := by
  refine DFunLike.ext' (Continuous.ext_on hN.adjoint_dense
    (ContinuousLinearMap.adjoint hN.vonNeumannS).continuous
    hN.adjoint.vonNeumannS.continuous fun χ hχ => ?_)
  have hχ' : χ ∈ (LinearPMap.adjoint N).domain := hχ
  have hχN : χ ∈ N.domain := hN.adjoint_domain.le hχ'
  refine ext_inner_left ℂ fun φ => ?_
  rw [ContinuousLinearMap.adjoint_inner_right,
    hN.commute_vonNeumannInverse_adjoint hχ', ← hN.inner_vonNeumannQ]
  exact hN.inner_adjointRestrict_right ⟨hN.vonNeumannQ φ, hN.vonNeumannQ_mem_domain φ⟩
    ⟨χ, hχN⟩

/-- **`S Q = Q S`**: this is the commutation of `N` with `Q` at the vector `Q φ`. -/
theorem commute_vonNeumannQ_vonNeumannS (hN : IsNormalPMap N) (φ : H) :
    hN.vonNeumannS (hN.vonNeumannQ φ) = hN.vonNeumannQ (hN.vonNeumannS φ) :=
  hN.commute_vonNeumannInverse (hN.vonNeumannQ_mem_domain φ)

/-- **`S† Q = Q S†`**, the same statement for the normal operator `N†`. -/
theorem commute_vonNeumannQ_vonNeumannS_adjoint (hN : IsNormalPMap N) (φ : H) :
    hN.adjoint.vonNeumannS (hN.vonNeumannQ φ) = hN.vonNeumannQ (hN.adjoint.vonNeumannS φ) := by
  have h := hN.adjoint.commute_vonNeumannQ_vonNeumannS φ
  rw [hN.vonNeumannQ_adjoint] at h
  exact h

/-- **`S† S = Q - Q²`**: `S† (S φ) = N† (Q (S φ)) = N† (N (Q² φ)) = (N† N) (Q² φ)`, and
`(1 + N† N) (Q² φ) = Q φ`. -/
theorem vonNeumannS_adjoint_vonNeumannS (hN : IsNormalPMap N) (φ : H) :
    hN.adjoint.vonNeumannS (hN.vonNeumannS φ)
      = hN.vonNeumannQ φ - hN.vonNeumannQ (hN.vonNeumannQ φ) := by
  have hm : hN.vonNeumannQ (hN.vonNeumannQ φ) ∈ (adjointComp N).domain :=
    hN.vonNeumannQ_mem (hN.vonNeumannQ φ)
  have key : (adjointComp N ⟨hN.vonNeumannQ (hN.vonNeumannQ φ), hm⟩ : H)
      = hN.vonNeumannQ φ - hN.vonNeumannQ (hN.vonNeumannQ φ) :=
    eq_sub_of_add_eq' (hN.add_adjointComp_vonNeumannQ (hN.vonNeumannQ φ))
  have h1 : hN.vonNeumannQ (hN.vonNeumannS φ)
      = (N ⟨hN.vonNeumannQ (hN.vonNeumannQ φ), hN.vonNeumannQ_mem_domain _⟩ : H) :=
    (hN.commute_vonNeumannInverse (hN.vonNeumannQ_mem_domain φ)).symm
  rw [← key, hN.vonNeumannS_adjoint_apply]
  exact congrArg (fun w : (LinearPMap.adjoint N).domain => (LinearPMap.adjoint N w : H))
    (Subtype.ext h1)

/-- **`S S† = Q - Q²`**: `S (S† φ) = N (Q (S† φ)) = N (N† (Q² φ)) = (N N†) (Q² φ)`, which is
`(N† N) (Q² φ) = Q φ - Q² φ` by `adjointComp_adjoint`. -/
theorem vonNeumannS_vonNeumannS_adjoint (hN : IsNormalPMap N) (φ : H) :
    hN.vonNeumannS (hN.adjoint.vonNeumannS φ)
      = hN.vonNeumannQ φ - hN.vonNeumannQ (hN.vonNeumannQ φ) := by
  have hm : hN.vonNeumannQ (hN.vonNeumannQ φ) ∈ (adjointComp N).domain :=
    hN.vonNeumannQ_mem (hN.vonNeumannQ φ)
  have hm' : hN.vonNeumannQ (hN.vonNeumannQ φ)
      ∈ (adjointComp (LinearPMap.adjoint N)).domain :=
    (congrArg LinearPMap.domain hN.adjointComp_adjoint).ge hm
  have hr : (LinearPMap.adjoint N ⟨hN.vonNeumannQ (hN.vonNeumannQ φ),
      hN.mem_adjoint_domain (hN.vonNeumannQ_mem_domain _)⟩ : H) ∈ N.domain :=
    hN.adjoint_adjoint_domain.le (mem_adjointComp_domain.1 hm').choose_spec
  have key : (adjointComp (LinearPMap.adjoint N)
        ⟨hN.vonNeumannQ (hN.vonNeumannQ φ), hm'⟩ : H)
      = hN.vonNeumannQ φ - hN.vonNeumannQ (hN.vonNeumannQ φ) := by
    rw [linearPMap_apply_eq_of_eq hN.adjointComp_adjoint hm' hm]
    exact eq_sub_of_add_eq' (hN.add_adjointComp_vonNeumannQ (hN.vonNeumannQ φ))
  have hb : hN.vonNeumannQ (hN.adjoint.vonNeumannS φ)
      = (LinearPMap.adjoint N ⟨hN.vonNeumannQ (hN.vonNeumannQ φ),
          hN.mem_adjoint_domain (hN.vonNeumannQ_mem_domain _)⟩ : H) := by
    rw [← hN.commute_vonNeumannQ_vonNeumannS_adjoint φ, hN.vonNeumannS_adjoint_apply]
  have hstep : (N ⟨hN.vonNeumannQ (hN.adjoint.vonNeumannS φ),
        hN.vonNeumannQ_mem_domain (hN.adjoint.vonNeumannS φ)⟩ : H)
      = (N ⟨(LinearPMap.adjoint N ⟨hN.vonNeumannQ (hN.vonNeumannQ φ),
          hN.mem_adjoint_domain (hN.vonNeumannQ_mem_domain _)⟩ : H), hr⟩ : H) :=
    congrArg (fun w : N.domain => (N w : H)) (Subtype.ext hb)
  rw [← key, hN.vonNeumannS_apply]
  refine hstep.trans ?_
  exact (linearPMap_apply_eq_of_eq hN.adjoint_adjoint
    (mem_adjointComp_domain.1 hm').choose_spec hr).symm

/-- **`S` is a normal bounded operator**: `S† S = Q - Q² = S S†`. -/
theorem isStarNormal_vonNeumannS (hN : IsNormalPMap N) : IsStarNormal hN.vonNeumannS where
  star_comm_self := by
    rw [ContinuousLinearMap.star_eq_adjoint, hN.adjoint_vonNeumannS]
    show hN.adjoint.vonNeumannS * hN.vonNeumannS = hN.vonNeumannS * hN.adjoint.vonNeumannS
    refine ContinuousLinearMap.ext fun φ => ?_
    show hN.adjoint.vonNeumannS (hN.vonNeumannS φ) = hN.vonNeumannS (hN.adjoint.vonNeumannS φ)
    rw [hN.vonNeumannS_adjoint_vonNeumannS, hN.vonNeumannS_vonNeumannS_adjoint]

/-- **`Q` commutes with `S`.** -/
theorem commute_vonNeumannQ_S (hN : IsNormalPMap N) :
    Commute hN.vonNeumannQ hN.vonNeumannS := by
  show hN.vonNeumannQ * hN.vonNeumannS = hN.vonNeumannS * hN.vonNeumannQ
  refine ContinuousLinearMap.ext fun φ => ?_
  show hN.vonNeumannQ (hN.vonNeumannS φ) = hN.vonNeumannS (hN.vonNeumannQ φ)
  exact (hN.commute_vonNeumannQ_vonNeumannS φ).symm

/-- **`Q` commutes with `S†`.** -/
theorem commute_vonNeumannQ_star_S (hN : IsNormalPMap N) :
    Commute hN.vonNeumannQ (star hN.vonNeumannS) := by
  rw [ContinuousLinearMap.star_eq_adjoint, hN.adjoint_vonNeumannS]
  show hN.vonNeumannQ * hN.adjoint.vonNeumannS = hN.adjoint.vonNeumannS * hN.vonNeumannQ
  refine ContinuousLinearMap.ext fun φ => ?_
  show hN.vonNeumannQ (hN.adjoint.vonNeumannS φ) = hN.adjoint.vonNeumannS (hN.vonNeumannQ φ)
  exact (hN.commute_vonNeumannQ_vonNeumannS_adjoint φ).symm

/-! ### The joint projection-valued measure of the pair `(Q, S)` -/

/-- The star-commuting pair `(Q, S)` of bounded operators attached to a normal `N`. -/
def pairOp (hN : IsNormalPMap N) : Fin 2 → (H →L[ℂ] H) := ![hN.vonNeumannQ, hN.vonNeumannS]

theorem pairOp_cases (hN : IsNormalPMap N) (i : Fin 2) :
    hN.pairOp i = hN.vonNeumannQ ∨ hN.pairOp i = hN.vonNeumannS := by
  fin_cases i
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- `Q` and `S` commute. -/
theorem commute_pairOp (hN : IsNormalPMap N) (i j : Fin 2) :
    Commute (hN.pairOp i) (hN.pairOp j) := by
  rcases hN.pairOp_cases i with hi | hi <;> rcases hN.pairOp_cases j with hj | hj <;> rw [hi, hj]
  exacts [hN.commute_vonNeumannQ_S, hN.commute_vonNeumannQ_S.symm]

/-- `Q` and `S` star-commute: `Q` is self-adjoint and `S` is normal. -/
theorem starCommute_pairOp (hN : IsNormalPMap N) (i j : Fin 2) :
    Commute (hN.pairOp i) (star (hN.pairOp j)) := by
  have hQ : star hN.vonNeumannQ = hN.vonNeumannQ :=
    (isSelfAdjoint_vonNeumannInverse hN.dense_domain hN.isClosed).star_eq
  rcases hN.pairOp_cases i with hi | hi <;> rcases hN.pairOp_cases j with hj | hj <;> rw [hi, hj]
  · rw [hQ]
  · exact hN.commute_vonNeumannQ_star_S
  · rw [hQ]
    exact hN.commute_vonNeumannQ_S.symm
  · exact hN.isStarNormal_vonNeumannS.star_comm_self.symm

/-- The joint projection-valued measure of the pair `(Q, S)`, a p.v.m. on `ℂ²`. -/
def pairPVM (hN : IsNormalPMap N) : ProjectionValuedMeasure (Fin 2 → ℂ) H :=
  CommOperatorAlgebra.jointPVM hN.pairOp hN.commute_pairOp hN.starCommute_pairOp

/-- `∫ z₀ dP₂ = Q`. -/
theorem integral_pairPVM_zero (hN : IsNormalPMap N) :
    hN.pairPVM.integral (CommOperatorAlgebra.coordBall 0 ‖hN.vonNeumannQ‖) = hN.vonNeumannQ :=
  CommOperatorAlgebra.integral_jointPVM_coordBall hN.pairOp hN.commute_pairOp
    hN.starCommute_pairOp 0 (le_refl _)

/-- `∫ z₁ dP₂ = S`. -/
theorem integral_pairPVM_one (hN : IsNormalPMap N) :
    hN.pairPVM.integral (CommOperatorAlgebra.coordBall 1 ‖hN.vonNeumannS‖) = hN.vonNeumannS :=
  CommOperatorAlgebra.integral_jointPVM_coordBall hN.pairOp hN.commute_pairOp
    hN.starCommute_pairOp 1 (le_refl _)

theorem measurableSet_coordZero : MeasurableSet {z : Fin 2 → ℂ | z 0 = 0} := by
  have he : {z : Fin 2 → ℂ | z 0 = 0} = (fun z : Fin 2 → ℂ => z 0) ⁻¹' {(0 : ℂ)} := rfl
  rw [he]
  exact measurable_pi_apply 0 (measurableSet_singleton (0 : ℂ))

/-- **`P₂ {z₀ = 0} = 0`**: `Q P₂{z₀ = 0} = ∫ z₀ 1_{z₀ = 0} dP₂ = 0` and `Q` is injective. -/
theorem pairPVM_coordZero (hN : IsNormalPMap N) :
    hN.pairPVM {z : Fin 2 → ℂ | z 0 = 0} = 0 := by
  have hs := measurableSet_coordZero
  have e : (CommOperatorAlgebra.coordBall 0 ‖hN.vonNeumannQ‖ *
      boundedMeasurable.indicator hs : boundedMeasurable (Fin 2 → ℂ)) = 0 := by
    refine Subtype.ext (funext fun z => ?_)
    change (CommOperatorAlgebra.coordBall (0 : Fin 2) ‖hN.vonNeumannQ‖ : (Fin 2 → ℂ) → ℂ) z *
      {z : Fin 2 → ℂ | z 0 = 0}.indicator (fun _ => (1 : ℂ)) z = 0
    by_cases hz : z ∈ {z : Fin 2 → ℂ | z 0 = 0}
    · have hz0 : z 0 = 0 := hz
      rw [CommOperatorAlgebra.coordBall_apply, hz0,
        ballId_apply_of_mem (Metric.mem_closedBall_self (norm_nonneg _)), zero_mul]
    · rw [Set.indicator_of_notMem hz, mul_zero]
  have h3 : hN.pairPVM.integral (CommOperatorAlgebra.coordBall 0 ‖hN.vonNeumannQ‖) *
      hN.pairPVM.integral (boundedMeasurable.indicator hs) = 0 := by
    rw [← map_mul, e, map_zero]
  rw [hN.integral_pairPVM_zero, hN.pairPVM.integral_indicator hs] at h3
  refine ContinuousLinearMap.ext fun ψ => ?_
  rw [zero_apply]
  refine vonNeumannInverse_injective hN.dense_domain hN.isClosed ?_
  rw [map_zero]
  exact congrArg (fun A : H →L[ℂ] H => A ψ) h3

/-! ### The good set and the quotient coordinate -/

/-- The set where `z₀ ≠ 0` and the coordinates are bounded by `‖Q‖` and `‖S‖`.  It carries `P₂`,
and on it `z₁ = (z₁ / z₀) z₀`. -/
def goodSet (hN : IsNormalPMap N) : Set (Fin 2 → ℂ) :=
  {z : Fin 2 → ℂ | z 0 = 0}ᶜ ∩
    ((fun z : Fin 2 → ℂ => z 0) ⁻¹' Metric.closedBall 0 ‖hN.vonNeumannQ‖ ∩
      (fun z : Fin 2 → ℂ => z 1) ⁻¹' Metric.closedBall 0 ‖hN.vonNeumannS‖)

theorem measurableSet_goodSet (hN : IsNormalPMap N) : MeasurableSet hN.goodSet :=
  measurableSet_coordZero.compl.inter
    ((measurable_pi_apply 0 measurableSet_closedBall).inter
      (measurable_pi_apply 1 measurableSet_closedBall))

/-- **`P₂` is carried by the good set**: `{z₀ = 0}` is null and the ball condition holds on the
joint spectrum. -/
theorem pairPVM_goodSet (hN : IsNormalPMap N) : hN.pairPVM hN.goodSet = 1 := by
  have hball : MeasurableSet ((fun z : Fin 2 → ℂ => z 0) ⁻¹'
      Metric.closedBall 0 ‖hN.vonNeumannQ‖ ∩
      (fun z : Fin 2 → ℂ => z 1) ⁻¹' Metric.closedBall 0 ‖hN.vonNeumannS‖) :=
    (measurable_pi_apply 0 measurableSet_closedBall).inter
      (measurable_pi_apply 1 measurableSet_closedBall)
  have h1 : hN.pairPVM {z : Fin 2 → ℂ | z 0 = 0}ᶜ = 1 := by
    rw [hN.pairPVM.compl measurableSet_coordZero, hN.pairPVM_coordZero, sub_zero]
  have h2 : hN.pairPVM ((fun z : Fin 2 → ℂ => z 0) ⁻¹'
      Metric.closedBall 0 ‖hN.vonNeumannQ‖ ∩
      (fun z : Fin 2 → ℂ => z 1) ⁻¹' Metric.closedBall 0 ‖hN.vonNeumannS‖) = 1 := by
    refine CommOperatorAlgebra.jointPVM_apply_eq_one _ _ _ hball fun z hz => ?_
    rw [← CommOperatorAlgebra.range_jointEval] at hz
    obtain ⟨χ, rfl⟩ := hz
    exact ⟨mem_closedBall_zero_iff.2 (CommOperatorAlgebra.norm_jointEval_le _ _ _ χ 0),
      mem_closedBall_zero_iff.2 (CommOperatorAlgebra.norm_jointEval_le _ _ _ χ 1)⟩
  rw [goodSet, ← hN.pairPVM.mul_apply measurableSet_coordZero.compl hball, h1, h2, one_mul]

end IsNormalPMap

/-- The quotient of the two coordinates of `ℂ²`, `z ↦ z₁ / z₀`. -/
def quotCoord (z : Fin 2 → ℂ) : ℂ := z 1 / z 0 -- totalisation-audit: allow z 0 ≠ 0 a.e.

theorem measurable_quotCoord : Measurable quotCoord :=
  (measurable_pi_apply 1).div (measurable_pi_apply 0)

namespace IsNormalPMap

variable {N : H →ₗ.[ℂ] H}

/-- `z₀ 1_G`, a bounded Borel function whose integral against `P₂` is `Q`. -/
def goodQ (hN : IsNormalPMap N) : boundedMeasurable (Fin 2 → ℂ) :=
  CommOperatorAlgebra.coordBall 0 ‖hN.vonNeumannQ‖ *
    boundedMeasurable.indicator hN.measurableSet_goodSet

/-- `z₁ 1_G`, a bounded Borel function whose integral against `P₂` is `S`. -/
def goodS (hN : IsNormalPMap N) : boundedMeasurable (Fin 2 → ℂ) :=
  CommOperatorAlgebra.coordBall 1 ‖hN.vonNeumannS‖ *
    boundedMeasurable.indicator hN.measurableSet_goodSet

theorem integral_goodQ (hN : IsNormalPMap N) : hN.pairPVM.integral hN.goodQ = hN.vonNeumannQ := by
  rw [goodQ, map_mul, hN.pairPVM.integral_indicator hN.measurableSet_goodSet, hN.pairPVM_goodSet,
    mul_one, hN.integral_pairPVM_zero]

theorem integral_goodS (hN : IsNormalPMap N) : hN.pairPVM.integral hN.goodS = hN.vonNeumannS := by
  rw [goodS, map_mul, hN.pairPVM.integral_indicator hN.measurableSet_goodSet, hN.pairPVM_goodSet,
    mul_one, hN.integral_pairPVM_one]

/-- `z₁ 1_G = (z₁ / z₀) (z₀ 1_G)` **everywhere**: on `G` the quotient is exact because `z₀ ≠ 0`,
and off `G` both sides vanish. -/
theorem coe_goodS_eq (hN : IsNormalPMap N) (z : Fin 2 → ℂ) :
    (hN.goodS : (Fin 2 → ℂ) → ℂ) z = quotCoord z * (hN.goodQ : (Fin 2 → ℂ) → ℂ) z := by
  have hQz : (hN.goodQ : (Fin 2 → ℂ) → ℂ) z =
      (CommOperatorAlgebra.coordBall (0 : Fin 2) ‖hN.vonNeumannQ‖ : (Fin 2 → ℂ) → ℂ) z *
        hN.goodSet.indicator (fun _ => (1 : ℂ)) z := rfl
  have hSz : (hN.goodS : (Fin 2 → ℂ) → ℂ) z =
      (CommOperatorAlgebra.coordBall (1 : Fin 2) ‖hN.vonNeumannS‖ : (Fin 2 → ℂ) → ℂ) z *
        hN.goodSet.indicator (fun _ => (1 : ℂ)) z := rfl
  rw [hQz, hSz]
  by_cases hz : z ∈ hN.goodSet
  · have hz0' : z 0 ≠ 0 := hz.1
    have hz1 : z 0 ∈ Metric.closedBall (0 : ℂ) ‖hN.vonNeumannQ‖ := hz.2.1
    have hz2 : z 1 ∈ Metric.closedBall (0 : ℂ) ‖hN.vonNeumannS‖ := hz.2.2
    rw [Set.indicator_of_mem hz, CommOperatorAlgebra.coordBall_apply,
      CommOperatorAlgebra.coordBall_apply, ballId_apply_of_mem hz1, ballId_apply_of_mem hz2,
      mul_one, mul_one, quotCoord, div_mul_cancel₀ _ hz0']
  · rw [Set.indicator_of_notMem hz, mul_zero, mul_zero, mul_zero]

/-! ### The spectral theorem -/

/-- The projection-valued measure of `N` on `ℂ`: the pushforward of `P₂` along `z ↦ z₁ / z₀`. -/
def normalPVM (hN : IsNormalPMap N) : ProjectionValuedMeasure ℂ H :=
  hN.pairPVM.map quotCoord measurable_quotCoord

/-- `∫ z dP = ∫ (z₁ / z₀) dP₂`. -/
theorem integralPMap_normalPVM (hN : IsNormalPMap N) :
    hN.normalPVM.integralPMap measurable_id
      = hN.pairPVM.integralPMap measurable_quotCoord := by
  rw [normalPVM, ProjectionValuedMeasure.integralPMap_map]

/-- **`Q φ` lies in the domain of `M = ∫ (z₁ / z₀) dP₂`**, because `z₁ 1_G = (z₁/z₀) (z₀ 1_G)` is
bounded and `Q = ∫ z₀ 1_G dP₂`. -/
theorem vonNeumannQ_mem_integralPMap (hN : IsNormalPMap N) (φ : H) :
    hN.vonNeumannQ φ ∈ (hN.pairPVM.integralPMap measurable_quotCoord).domain := by
  have h := hN.pairPVM.integral_mem_integralPMap_domain measurable_quotCoord hN.goodQ hN.goodS
    hN.coe_goodS_eq φ
  rwa [hN.integral_goodQ] at h

/-- **`M (Q φ) = S φ = N (Q φ)`.** -/
theorem integralPMap_vonNeumannQ (hN : IsNormalPMap N) (φ : H) :
    hN.pairPVM.integralPMap measurable_quotCoord
        ⟨hN.vonNeumannQ φ, hN.vonNeumannQ_mem_integralPMap φ⟩ = hN.vonNeumannS φ := by
  have h := hN.pairPVM.integralPMap_integral measurable_quotCoord hN.goodQ hN.goodS
    hN.coe_goodS_eq φ
  rw [hN.integral_goodS] at h
  have hx : hN.pairPVM.integral hN.goodQ φ = hN.vonNeumannQ φ :=
    congrArg (fun A : H →L[ℂ] H => A φ) hN.integral_goodQ
  exact (linearPMap_apply_congr hx.symm _ _).trans h

/-- **`N ≤ M`**: `M` agrees with `N` on `Ran Q = D(N† N)`, a core of `N`, and `M` is closed. -/
theorem le_integralPMap (hN : IsNormalPMap N) :
    N ≤ hN.pairPVM.integralPMap measurable_quotCoord := by
  have hMc : (hN.pairPVM.integralPMap measurable_quotCoord).IsClosed :=
    hN.pairPVM.isClosed_integralPMap measurable_quotCoord
  have hres : N.domRestrict (adjointCompDomain N)
      ≤ hN.pairPVM.integralPMap measurable_quotCoord := by
    constructor
    · intro x hx
      have hx1 : x ∈ (adjointComp N).domain := hx.1
      have hxq : hN.vonNeumannQ (onePlusAdjointComp N ⟨x, hx1⟩) = x :=
        vonNeumannInverse_onePlusAdjointComp hN.dense_domain hN.isClosed ⟨x, hx1⟩
      rw [← hxq]
      exact hN.vonNeumannQ_mem_integralPMap _
    · intro a b hab
      have hx1 : (a : H) ∈ (adjointComp N).domain := a.2.1
      have hxq : hN.vonNeumannQ (onePlusAdjointComp N ⟨(a : H), hx1⟩) = (a : H) :=
        vonNeumannInverse_onePlusAdjointComp hN.dense_domain hN.isClosed ⟨(a : H), hx1⟩
      have hb : (b : H) = hN.vonNeumannQ (onePlusAdjointComp N ⟨(a : H), hx1⟩) :=
        hab.symm.trans hxq.symm
      have h1 : (hN.pairPVM.integralPMap measurable_quotCoord b : H)
          = hN.vonNeumannS (onePlusAdjointComp N ⟨(a : H), hx1⟩) :=
        (linearPMap_apply_congr hb _ _).trans (hN.integralPMap_vonNeumannQ _)
      rw [h1, hN.vonNeumannS_apply]
      exact (congrArg (fun w : N.domain => (N w : H)) (Subtype.ext hxq)).symm
  have hclb : (N.domRestrict (adjointCompDomain N)).IsClosable :=
    LinearPMap.isClosable_iff_exists_closed_extension.2 ⟨_, hMc, hres⟩
  have hgr : ((N.domRestrict (adjointCompDomain N)).closure).graph
      ≤ (hN.pairPVM.integralPMap measurable_quotCoord).graph := by
    rw [← hclb.graph_closure_eq_closure_graph]
    exact Submodule.topologicalClosure_minimal _ (LinearPMap.le_graph_of_le hres) hMc
  rw [(hasCore_adjointCompDomain hN.dense_domain hN.isClosed).closure_eq] at hgr
  exact LinearPMap.le_of_le_graph hgr

/-- **The spectral theorem for an arbitrary closed densely defined normal operator**
(Rudin, *Functional Analysis*, Theorem 13.33): `N = ∫ z dP` for a projection-valued measure `P`
on `ℂ`.  No hypothesis is made on the spectrum of `N`. -/
theorem exists_pvm (hN : IsNormalPMap N) :
    ∃ P : ProjectionValuedMeasure ℂ H, P.integralPMap measurable_id = N := by
  refine ⟨hN.normalPVM, ?_⟩
  rw [hN.integralPMap_normalPVM]
  exact (hN.eq_of_le (hN.pairPVM.isNormalPMap_integralPMap measurable_quotCoord)
    hN.le_integralPMap).symm

end IsNormalPMap

end SpectralTheorem
