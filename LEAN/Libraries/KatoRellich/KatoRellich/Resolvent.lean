import KatoRellich.Basic

/-!
# Surjectivity of shifted self-adjoint operators

For a self-adjoint `A` and a scalar `z`, the operator `A + z` is onto as soon as both `A + z` and
`A + z̄` are bounded below in norm: `c ‖x‖ ≤ ‖(A + z) x‖` and `c ‖x‖ ≤ ‖(A + z̄) x‖` with
`c > 0`.  This is the step "`Ran(A + iμ) = H` since `A` is self-adjoint" in the proof of
Reed–Simon II, Theorem X.12, p. 163, and the argument is that of Reed–Simon I, proof of
Theorem VIII.3, p. 257: the range is closed because `A + z` is closed and bounded below, and it is
dense because a vector orthogonal to it solves `(A + z̄) y = 0`.

The two norm bounds are supplied for the two shifts used later:

* a real shift `t` of an operator bounded below by `M`, with `M + t > 0`:
  `(M + t) ‖x‖ ≤ ‖(A + t) x‖`, and `‖A x‖ ≤ ‖(A + t) x‖` once also `t ≥ 0` and `2M + t ≥ 0`;
* an imaginary shift `iμ` of a symmetric operator: `‖(A + iμ) x‖² = ‖A x‖² + μ² ‖x‖²`
  (Reed–Simon II, p. 162, last display).

## Main results

* `KatoRellich.isClosed_range_of_isClosed`: a closed operator bounded below in norm has closed
  range.
* `KatoRellich.isClosed_addScalar`: `A + z` is closed when `A` is.
* `KatoRellich.range_addScalar_eq_top`: `Ran(A + z) = H` for self-adjoint `A` under the two
  norm bounds.
* `KatoRellich.range_addScalar_ofReal_eq_top`: `Ran(A + t) = H` for self-adjoint `A` bounded
  below by `M` and real `t` with `M + t > 0`.
* `KatoRellich.norm_addScalar_I_sq`: `‖(A + iμ) x‖² = ‖A x‖² + μ² ‖x‖²` for symmetric `A`.
-/

noncomputable section

open scoped InnerProductSpace ComplexConjugate

namespace KatoRellich

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

section ClosedRange

variable [CompleteSpace E]

/-- A closed operator with `c ‖x‖ ≤ ‖T x‖` for some `c > 0` has closed range.  The second
projection of the (complete) graph is antilipschitz onto the range. -/
theorem isClosed_range_of_isClosed {T : E →ₗ.[𝕜] E} (hT : T.IsClosed) {c : ℝ} (hc : 0 < c)
    (hbound : ∀ x : T.domain, c * ‖(x : E)‖ ≤ ‖T x‖) :
    IsClosed (LinearMap.range T.toFun : Set E) := by
  have : CompleteSpace T.graph := hT.completeSpace_coe
  let π : T.graph →L[𝕜] E := (ContinuousLinearMap.snd 𝕜 E E).comp T.graph.subtypeL
  have hπ : ∀ g : T.graph, ‖g‖ ≤ (⟨max c⁻¹ 1, by positivity⟩ : NNReal) * ‖π g‖ := by
    rintro ⟨⟨x, y⟩, hg⟩
    obtain ⟨u, hu, hTu⟩ := (LinearPMap.mem_graph_iff T).mp hg
    simp only at hu hTu
    change ‖((x, y) : E × E)‖ ≤ max c⁻¹ 1 * ‖y‖
    rw [Prod.norm_def]
    refine max_le ?_ ?_
    · have h1 : c * ‖x‖ ≤ ‖y‖ := by rw [← hu, ← hTu]; exact hbound u
      calc ‖x‖ = c⁻¹ * (c * ‖x‖) := by field_simp
        _ ≤ c⁻¹ * ‖y‖ := by gcongr
        _ ≤ max c⁻¹ 1 * ‖y‖ := by gcongr; exact le_max_left _ _
    · calc ‖y‖ = 1 * ‖y‖ := (one_mul _).symm
        _ ≤ max c⁻¹ 1 * ‖y‖ := by gcongr; exact le_max_right _ _
  have hanti := AddMonoidHomClass.antilipschitz_of_bound π hπ
  have hrange : Set.range π = (LinearMap.range T.toFun : Set E) := by
    ext y
    constructor
    · rintro ⟨⟨⟨x, y'⟩, hg⟩, rfl⟩
      obtain ⟨u, -, hTu⟩ := (LinearPMap.mem_graph_iff T).mp hg
      exact ⟨u, hTu⟩
    · rintro ⟨u, rfl⟩
      exact ⟨⟨((u : E), T u), (LinearPMap.mem_graph_iff T).mpr ⟨u, rfl, rfl⟩⟩, rfl⟩
  rw [← hrange]
  exact hanti.isClosed_range π.uniformContinuous

/-- A closed operator with `c ‖x‖ ≤ ‖T x‖` for some `c > 0` and dense range is onto. -/
theorem range_eq_top_of_isClosed {T : E →ₗ.[𝕜] E} (hT : T.IsClosed) {c : ℝ} (hc : 0 < c)
    (hbound : ∀ x : T.domain, c * ‖(x : E)‖ ≤ ‖T x‖)
    (hdense : Dense (LinearMap.range T.toFun : Set E)) :
    LinearMap.range T.toFun = ⊤ := by
  have h := (isClosed_range_of_isClosed hT hc hbound).closure_eq
  rw [hdense.closure_eq] at h
  exact Submodule.eq_top_iff'.mpr fun y => by
    change y ∈ (LinearMap.range T.toFun : Set E)
    rw [← h]
    trivial

end ClosedRange

/-- The graph of `A + z` is the preimage of the graph of `A` under `(x, y) ↦ (x, y - z • x)`,
so `A + z` is closed when `A` is. -/
theorem isClosed_addScalar {T : E →ₗ.[𝕜] E} (hT : T.IsClosed) (z : 𝕜) :
    (addScalar T z).IsClosed := by
  have hgraph : ((addScalar T z).graph : Set (E × E)) =
      (fun p : E × E => (p.1, p.2 - z • p.1)) ⁻¹' (T.graph : Set (E × E)) := by
    ext ⟨x, y⟩
    simp only [SetLike.mem_coe, Set.mem_preimage, LinearPMap.mem_graph_iff]
    constructor
    · rintro ⟨u, hu, hTu⟩
      refine ⟨u, hu, ?_⟩
      rw [← hTu, addScalar_apply, hu, add_sub_cancel_right]
    · rintro ⟨u, hu, hTu⟩
      refine ⟨u, hu, ?_⟩
      change T u + z • (u : E) = y
      rw [hTu, hu, sub_add_cancel]
  change IsClosed ((addScalar T z).graph : Set (E × E))
  rw [hgraph]
  exact hT.preimage (by fun_prop)

section Surjective

variable [CompleteSpace E]

/-- A vector orthogonal to `Ran(T + z)` lies in `D(T†)` and solves `T† y = -z̄ y`. -/
theorem mem_adjoint_domain_of_orthogonal {T : E →ₗ.[𝕜] E} (hT : Dense (T.domain : Set E))
    (z : 𝕜) {y : E} (hy : ∀ x : T.domain, ⟪y, T x + z • (x : E)⟫_𝕜 = 0) :
    ∃ h : y ∈ T.adjoint.domain, T.adjoint ⟨y, h⟩ = -(conj z • y) := by
  have key : ∀ x : T.domain, ⟪-(conj z • y), (x : E)⟫_𝕜 = ⟪y, T x⟫_𝕜 := by
    intro x
    have h := hy x
    rw [inner_add_right, inner_smul_right] at h
    rw [inner_neg_left, inner_smul_left, RCLike.conj_conj]
    linear_combination -h
  have hmem : y ∈ T.adjoint.domain := LinearPMap.mem_adjoint_domain_of_exists y ⟨_, key⟩
  exact ⟨hmem, LinearPMap.adjoint_apply_eq hT ⟨y, hmem⟩ key⟩

/-- **`Ran(A + z) = H` for self-adjoint `A`**, provided `A + z` and `A + z̄` are both bounded
below in norm by `c > 0` (Reed–Simon I, proof of Theorem VIII.3, p. 257). -/
theorem range_addScalar_eq_top {A : E →ₗ.[𝕜] E} (hA : IsSelfAdjoint A) (z : 𝕜) {c : ℝ}
    (hc : 0 < c) (h₁ : ∀ x : A.domain, c * ‖(x : E)‖ ≤ ‖A x + z • (x : E)‖)
    (h₂ : ∀ x : A.domain, c * ‖(x : E)‖ ≤ ‖A x + conj z • (x : E)‖) :
    LinearMap.range (addScalar A z).toFun = ⊤ := by
  refine range_eq_top_of_isClosed (isClosed_addScalar hA.isClosed z) hc (fun x => h₁ x) ?_
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    Submodule.eq_bot_iff]
  intro y hy
  have horth : ∀ x : A.domain, ⟪y, A x + z • (x : E)⟫_𝕜 = 0 := by
    intro x
    rw [← inner_eq_zero_symm]
    exact (Submodule.mem_orthogonal _ y).mp hy _ ⟨x, rfl⟩
  have hadj := mem_adjoint_domain_of_orthogonal hA.dense_domain z horth
  rw [LinearPMap.isSelfAdjoint_def.mp hA] at hadj
  obtain ⟨hmem, hAy⟩ := hadj
  have h := h₂ ⟨y, hmem⟩
  change c * ‖y‖ ≤ ‖A ⟨y, hmem⟩ + conj z • y‖ at h
  rw [hAy, neg_add_cancel, norm_zero] at h
  exact norm_eq_zero.mp (le_antisymm (nonpos_of_mul_nonpos_right h hc) (norm_nonneg y))

end Surjective

/-- For `A` bounded below by `M` and real `t`: `(M + t) ‖x‖ ≤ ‖(A + t) x‖`. -/
theorem mul_norm_le_norm_add_ofReal {A : E →ₗ.[𝕜] E} {M : ℝ} (hM : IsBoundedBelow A M) (t : ℝ)
    (x : A.domain) :
    (M + t) * ‖(x : E)‖ ≤ ‖A x + (t : 𝕜) • (x : E)‖ := by
  have h1 : (M + t) * ‖(x : E)‖ ^ 2 ≤ ‖(x : E)‖ * ‖A x + (t : 𝕜) • (x : E)‖ := by
    calc (M + t) * ‖(x : E)‖ ^ 2 = M * ‖(x : E)‖ ^ 2 + t * ‖(x : E)‖ ^ 2 := by ring
      _ ≤ RCLike.re ⟪(x : E), A x⟫_𝕜 + t * ‖(x : E)‖ ^ 2 := by gcongr; exact hM x
      _ = RCLike.re ⟪(x : E), A x + (t : 𝕜) • (x : E)⟫_𝕜 := by
        rw [inner_add_right, inner_smul_right, map_add, RCLike.re_ofReal_mul,
          inner_self_eq_norm_sq]
      _ ≤ ‖(x : E)‖ * ‖A x + (t : 𝕜) • (x : E)‖ := re_inner_le_norm _ _
  rcases (norm_nonneg (x : E)).eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero]
    exact norm_nonneg _
  · nlinarith

/-- For `A` bounded below by `M` and real `t ≥ 0` with `2M + t ≥ 0`:
`‖A x‖ ≤ ‖(A + t) x‖`, since `‖(A + t) x‖² ≥ ‖A x‖² + t (2M + t) ‖x‖²`. -/
theorem norm_le_norm_add_ofReal {A : E →ₗ.[𝕜] E} {M : ℝ} (hM : IsBoundedBelow A M) {t : ℝ}
    (ht : 0 ≤ t) (hMt : 0 ≤ 2 * M + t) (x : A.domain) :
    ‖A x‖ ≤ ‖A x + (t : 𝕜) • (x : E)‖ := by
  have hre : RCLike.re ⟪A x, (t : 𝕜) • (x : E)⟫_𝕜 = t * RCLike.re ⟪(x : E), A x⟫_𝕜 := by
    rw [inner_smul_right, RCLike.re_ofReal_mul, ← inner_conj_symm, RCLike.conj_re]
  have hsq : ‖A x‖ ^ 2 ≤ ‖A x + (t : 𝕜) • (x : E)‖ ^ 2 := by
    rw [@norm_add_sq 𝕜, hre, norm_smul, RCLike.norm_ofReal, mul_pow, sq_abs]
    have := hM x
    nlinarith [sq_nonneg ‖(x : E)‖, mul_nonneg ht hMt]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

/-- **`Ran(A + t) = H`** for self-adjoint `A` bounded below by `M` and real `t` with
`M + t > 0`. -/
theorem range_addScalar_ofReal_eq_top [CompleteSpace E] {A : E →ₗ.[𝕜] E} (hA : IsSelfAdjoint A)
    {M : ℝ} (hM : IsBoundedBelow A M) {t : ℝ} (ht : 0 < M + t) :
    LinearMap.range (addScalar A (t : 𝕜)).toFun = ⊤ :=
  range_addScalar_eq_top hA (t : 𝕜) ht (mul_norm_le_norm_add_ofReal hM t)
    (by rw [RCLike.conj_ofReal]; exact mul_norm_le_norm_add_ofReal hM t)

/-- For symmetric `A`, a nonzero imaginary unit and real `μ`:
`‖(A + iμ) x‖² = ‖A x‖² + μ² ‖x‖²` (Reed–Simon II, p. 162, last display). -/
theorem norm_addScalar_I_sq {A : E →ₗ.[𝕜] E} (hA : IsSymmetric A) (hI : (RCLike.I : 𝕜) ≠ 0)
    (μ : ℝ) (x : A.domain) :
    ‖A x + ((μ : 𝕜) * RCLike.I) • (x : E)‖ ^ 2 = ‖A x‖ ^ 2 + μ ^ 2 * ‖(x : E)‖ ^ 2 := by
  have hreal : ⟪A x, (x : E)⟫_𝕜 = (RCLike.re ⟪A x, (x : E)⟫_𝕜 : 𝕜) := by
    refine (RCLike.conj_eq_iff_re.mp ?_).symm
    rw [inner_conj_symm]
    exact (hA.isFormalAdjoint x x).symm
  have hre : RCLike.re ⟪A x, ((μ : 𝕜) * RCLike.I) • (x : E)⟫_𝕜 = 0 := by
    rw [inner_smul_right, hreal]
    simp [RCLike.mul_re, RCLike.I_re]
  rw [@norm_add_sq 𝕜, hre, norm_smul, norm_mul, RCLike.norm_ofReal, RCLike.norm_I_of_ne_zero hI,
    mul_one, mul_pow, sq_abs]
  ring

/-- For symmetric `A`: `|μ| ‖x‖ ≤ ‖(A + iμ) x‖` and `‖A x‖ ≤ ‖(A + iμ) x‖`. -/
theorem norm_le_norm_addScalar_I {A : E →ₗ.[𝕜] E} (hA : IsSymmetric A)
    (hI : (RCLike.I : 𝕜) ≠ 0) (μ : ℝ) (x : A.domain) :
    |μ| * ‖(x : E)‖ ≤ ‖A x + ((μ : 𝕜) * RCLike.I) • (x : E)‖ ∧
      ‖A x‖ ≤ ‖A x + ((μ : 𝕜) * RCLike.I) • (x : E)‖ := by
  have h := norm_addScalar_I_sq hA hI μ x
  constructor
  · refine (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp ?_
    rw [h, mul_pow, sq_abs]
    nlinarith [sq_nonneg ‖A x‖]
  · refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
    rw [h]
    nlinarith [sq_nonneg μ, sq_nonneg ‖(x : E)‖]

/-- **`Ran(A + iμ) = H`** for self-adjoint `A`, a nonzero imaginary unit and real `μ ≠ 0`
(Reed–Simon II, proof of Theorem X.12, p. 163). -/
theorem range_addScalar_I_eq_top [CompleteSpace E] {A : E →ₗ.[𝕜] E} (hA : IsSelfAdjoint A)
    (hI : (RCLike.I : 𝕜) ≠ 0) {μ : ℝ} (hμ : μ ≠ 0) :
    LinearMap.range (addScalar A ((μ : 𝕜) * RCLike.I)).toFun = ⊤ := by
  have hsymm := IsSymmetric.of_isSelfAdjoint hA
  refine range_addScalar_eq_top hA _ (abs_pos.mpr hμ)
    (fun x => (norm_le_norm_addScalar_I hsymm hI μ x).1) (fun x => ?_)
  have hconj : conj ((μ : 𝕜) * RCLike.I) = ((-μ : ℝ) : 𝕜) * RCLike.I := by
    rw [map_mul, RCLike.conj_ofReal, RCLike.conj_I, RCLike.ofReal_neg, mul_neg, neg_mul]
  rw [hconj, ← abs_neg μ]
  exact (norm_le_norm_addScalar_I hsymm hI (-μ) x).1

end KatoRellich
