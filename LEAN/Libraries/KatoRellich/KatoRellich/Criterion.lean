import KatoRellich.Basic

/-!
# The basic criterion for self-adjointness

Reed–Simon I, Theorem VIII.3 (pp. 256–257), (c) ⇒ (a): a symmetric operator `T` with
`Ran(T ± i) = H` is self-adjoint.  The proof only uses the two range conditions for a pair of
conjugate shifts, so it is stated here for an arbitrary scalar `z`: if `Ran(T + z) = H` and
`Ran(T + z̄) = H`, then `T` is self-adjoint.  With `z = i` this is Reed–Simon's statement.  With
`z` real the two conditions coincide, which gives a criterion that also works on real Hilbert
spaces: a symmetric `T` with `Ran(T + t) = H` for one real `t` is self-adjoint.

## Main results

* `KatoRellich.adjoint_domain_le_of_range`: if `T` is symmetric, `Ran(T + z̄) = H` and
  `Ran(T + z)` is dense, then `D(T†) ⊆ D(T)`.
* `KatoRellich.isSelfAdjoint_of_range_addScalar`: Reed–Simon I, Theorem VIII.3, (c) ⇒ (a), for
  the shifts `z` and `z̄`.
* `KatoRellich.isSelfAdjoint_of_range_addScalar_ofReal`: the real-shift form.
-/

noncomputable section

open scoped InnerProductSpace ComplexConjugate

namespace KatoRellich

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [CompleteSpace E]

/-- Reed–Simon I, proof of Theorem VIII.3, (c) ⇒ (a): if `T` is symmetric, `Ran(T + z̄) = H`
and `Ran(T + z)` is dense, then `D(T†) ⊆ D(T)`.

For `y ∈ D(T†)` choose `x ∈ D(T)` with `(T + z̄) x = (T† + z̄) y`.  Then `y - x` is orthogonal to
`Ran(T + z)`, hence zero. -/
theorem adjoint_domain_le_of_range {T : E →ₗ.[𝕜] E} (hT : IsSymmetric T) (z : 𝕜)
    (hz : Dense (LinearMap.range (addScalar T z).toFun : Set E))
    (hz' : LinearMap.range (addScalar T (conj z)).toFun = ⊤) :
    T.adjoint.domain ≤ T.domain := by
  intro y hy
  let y' : T.adjoint.domain := ⟨y, hy⟩
  obtain ⟨x, hx⟩ : T.adjoint y' + conj z • y ∈
      LinearMap.range (addScalar T (conj z)).toFun := by
    rw [hz']
    trivial
  have hx' : T x + conj z • (x : E) = T.adjoint y' + conj z • y := hx
  -- `y - x` is orthogonal to `Ran(T + z)`.
  have horth : ∀ w ∈ LinearMap.range (addScalar T z).toFun, ⟪y - (x : E), w⟫_𝕜 = 0 := by
    rintro _ ⟨v, rfl⟩
    have hv : (addScalar T z).toFun v = T v + z • (v : E) := rfl
    have h1 : ⟪T x + conj z • (x : E), (v : E)⟫_𝕜 =
        ⟪T.adjoint y' + conj z • y, (v : E)⟫_𝕜 := by
      rw [hx']
    rw [inner_add_left, inner_add_left, inner_smul_left, inner_smul_left, RCLike.conj_conj,
      hT.isFormalAdjoint x v,
      LinearPMap.adjoint_isFormalAdjoint hT.dense_domain y' v] at h1
    rw [hv, inner_sub_left, inner_add_right, inner_add_right, inner_smul_right,
      inner_smul_right]
    change ⟪(y' : E), T v⟫_𝕜 + z * ⟪(y' : E), (v : E)⟫_𝕜 -
      (⟪(x : E), T v⟫_𝕜 + z * ⟪(x : E), (v : E)⟫_𝕜) = 0
    rw [h1]
    ring
  -- Orthogonality to a dense subspace forces `y - x = 0`.
  have hzero : y - (x : E) = 0 := by
    have hcl : ∀ w ∈ closure (LinearMap.range (addScalar T z).toFun : Set E),
        ⟪y - (x : E), w⟫_𝕜 = 0 := by
      intro w hw
      have hcont : Continuous fun w : E => ⟪y - (x : E), w⟫_𝕜 := continuous_const.inner
        continuous_id
      exact (isClosed_singleton.preimage hcont).closure_subset_iff.mpr
        (fun w hw => horth w hw) hw
    rw [hz.closure_eq] at hcl
    exact inner_self_eq_zero.mp (hcl _ trivial)
  rw [sub_eq_zero.mp hzero]
  exact x.2

/-- **The basic criterion for self-adjointness** (Reed–Simon I, Theorem VIII.3, (c) ⇒ (a),
pp. 256–257).  A symmetric operator `T` with `Ran(T + z) = H` and `Ran(T + z̄) = H` is
self-adjoint.  Reed–Simon take `z = i`. -/
theorem isSelfAdjoint_of_range_addScalar {T : E →ₗ.[𝕜] E} (hT : IsSymmetric T) (z : 𝕜)
    (hz : LinearMap.range (addScalar T z).toFun = ⊤)
    (hz' : LinearMap.range (addScalar T (conj z)).toFun = ⊤) :
    IsSelfAdjoint T := by
  have hdense : Dense (LinearMap.range (addScalar T z).toFun : Set E) := by
    rw [hz, Submodule.top_coe]
    exact dense_univ
  have hle := adjoint_domain_le_of_range hT z hdense hz'
  rw [LinearPMap.isSelfAdjoint_def]
  exact (LinearPMap.eq_of_le_of_domain_eq hT.le_adjoint
    (le_antisymm hT.le_adjoint.1 hle)).symm

/-- The basic criterion with a real shift: a symmetric operator `T` with `Ran(T + t) = H` for
some real `t` is self-adjoint.  This form needs no complex scalars. -/
theorem isSelfAdjoint_of_range_addScalar_ofReal {T : E →ₗ.[𝕜] E} (hT : IsSymmetric T) (t : ℝ)
    (ht : LinearMap.range (addScalar T (t : 𝕜)).toFun = ⊤) :
    IsSelfAdjoint T :=
  isSelfAdjoint_of_range_addScalar hT (t : 𝕜) ht (by rw [RCLike.conj_ofReal]; exact ht)

end KatoRellich
