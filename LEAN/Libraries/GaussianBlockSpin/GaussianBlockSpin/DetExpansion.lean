import GaussianBlockSpin.GaussianIntegral

/-! The determinant expansion of a perturbed Gaussian covariance (after Bałaban, (Higgs)_{2,3} I (3.46)-(3.47)).
For a positive definite symmetric `G` with inverse `H` and a symmetric `V` with `H - V` positive definite:
`det (H - V) = det H · det (1 - G^{1/2} V G^{1/2})` and, for odd `n`,
`det (1 - G^{1/2} V G^{1/2})^{-1/2} ≥ exp Σ_{j=1}^n Tr((G V)^j) / (2j)`.
The square root is `symmFun hG Real.sqrt`, the function of a symmetric operator through an orthonormal
eigenbasis. -/

namespace GaussianBlockSpin

open scoped RealInnerProductSpace

/-- `log (1 + x) ≤ Σ_{j=1}^n (-1)^{j-1} x^j / j` for odd `n` and `x > -1` (written with `j + 1`, `j < n`). -/
theorem log_one_add_le_alternating {n : ℕ} (hn : Odd n) {x : ℝ} (hx : -1 < x) :
    Real.log (1 + x) ≤ ∑ j ∈ Finset.range n, (-1) ^ j * x ^ (j + 1) / (j + 1) := by  -- totalisation-audit: allow 1 + x > 0 from hx; divisor j + 1 >= 1
  set f : ℝ → ℝ := fun t => ∑ j ∈ Finset.range n, (-1) ^ j * t ^ (j + 1) / (j + 1) - Real.log (1 + t) with hf  -- totalisation-audit: allow f is used only at t > -1 (hderiv), where 1 + t > 0; divisor j + 1 >= 1
  have hderiv : ∀ t, -1 < t → HasDerivAt f (t ^ n / (1 + t)) t := by  -- totalisation-audit: allow 1 + t > 0 for t > -1
    intro t ht
    have h1 : HasDerivAt (fun t : ℝ => ∑ j ∈ Finset.range n, (-1) ^ j * t ^ (j + 1) / (j + 1))  -- totalisation-audit: allow divisor j + 1 >= 1
        (∑ j ∈ Finset.range n, (-1) ^ j * t ^ j) t := by
      have := HasDerivAt.fun_sum (u := Finset.range n)
        (A := fun (j : ℕ) (s : ℝ) => (-1 : ℝ) ^ j * s ^ (j + 1) / ((j : ℝ) + 1)) (fun j _ =>  -- totalisation-audit: allow divisor j + 1 >= 1
        (((hasDerivAt_pow (j + 1) t).const_mul ((-1 : ℝ) ^ j)).div_const ((j : ℝ) + 1)))
      convert this using 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Nat.add_sub_cancel]
      push_cast
      field_simp
    have h2 : HasDerivAt (fun t : ℝ => Real.log (1 + t)) (1 / (1 + t)) t := by  -- totalisation-audit: allow 1 + t > 0 for t > -1
      have := ((hasDerivAt_id t).const_add 1).log (by simp only [id]; linarith)
      simpa using this
    have hgeom : (∑ j ∈ Finset.range n, (-1 : ℝ) ^ j * t ^ j) * (1 + t) = 1 + t ^ n := by
      have := geom_sum_mul (-t) n
      simp only [neg_pow t] at this
      rw [Odd.neg_one_pow hn] at this
      linear_combination -this
    convert h1.sub h2 using 1
    have h1t : (1 + t) ≠ 0 := by linarith
    field_simp
    linear_combination -hgeom
  have hf0 : f 0 = 0 := by simp [hf]
  suffices h : 0 ≤ f x by
    simp only [hf] at h
    linarith
  rcases le_or_gt 0 x with h0 | h0
  · have hmono : MonotoneOn f (Set.Ici 0) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
      · exact fun t ht => (hderiv t (by linarith [Set.mem_Ici.mp ht])).continuousAt.continuousWithinAt
      · intro t ht
        rw [interior_Ici] at ht
        exact (hderiv t (by linarith [Set.mem_Ioi.mp ht])).differentiableAt.differentiableWithinAt
      · intro t ht
        rw [interior_Ici] at ht
        have ht0 := Set.mem_Ioi.mp ht
        rw [(hderiv t (by linarith)).deriv]
        positivity
    have := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr h0) h0
    rwa [hf0] at this
  · have hanti : AntitoneOn f (Set.Ioc (-1) 0) := by
      apply antitoneOn_of_deriv_nonpos (convex_Ioc (-1) 0)
      · exact fun t ht => (hderiv t ht.1).continuousAt.continuousWithinAt
      · intro t ht
        rw [interior_Ioc] at ht
        exact (hderiv t ht.1).differentiableAt.differentiableWithinAt
      · intro t ht
        rw [interior_Ioc] at ht
        rw [(hderiv t ht.1).deriv]
        exact div_nonpos_of_nonpos_of_nonneg ((Odd.pow_nonpos_iff hn).mpr ht.2.le) (by linarith [ht.1])
    have := hanti ⟨hx, h0.le⟩ ⟨by norm_num, le_rfl⟩ h0.le
    rwa [hf0] at this

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- `f(T) x = Σ_i f(λ_i) ⟪b_i, x⟫ b_i` for a symmetric `T` with orthonormal eigenbasis `b` and eigenvalues `λ`. -/
noncomputable def symmFun {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) (f : ℝ → ℝ) : E →ₗ[ℝ] E where
  toFun x := ∑ i, (f (hT.eigenvalues rfl i) * ⟪hT.eigenvectorBasis rfl i, x⟫) • hT.eigenvectorBasis rfl i
  map_add' x y := by simp only [inner_add_right, mul_add, add_smul, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [inner_smul_right, RingHom.id_apply, Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    ring

lemma inner_symmFun {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) (f : ℝ → ℝ) (j : Fin (Module.finrank ℝ E)) (x : E) :
    ⟪hT.eigenvectorBasis rfl j, symmFun hT f x⟫ = f (hT.eigenvalues rfl j) * ⟪hT.eigenvectorBasis rfl j, x⟫ := by
  simp only [symmFun, LinearMap.coe_mk, AddHom.coe_mk, inner_sum, inner_smul_right,
    orthonormal_iff_ite.mp (hT.eigenvectorBasis rfl).orthonormal, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

/-- Two vectors with the same coordinates in the eigenbasis are equal. -/
lemma eq_of_inner_eigenvectorBasis {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) {x y : E}
    (h : ∀ j, ⟪hT.eigenvectorBasis rfl j, x⟫ = ⟪hT.eigenvectorBasis rfl j, y⟫) : x = y := by
  apply (hT.eigenvectorBasis rfl).repr.injective
  ext j
  simp only [OrthonormalBasis.repr_apply_apply, h]

lemma symmFun_comp {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) (f g : ℝ → ℝ) :
    symmFun hT f ∘ₗ symmFun hT g = symmFun hT (fun t => f t * g t) := by
  ext x
  refine eq_of_inner_eigenvectorBasis hT fun j => ?_
  rw [LinearMap.comp_apply, inner_symmFun, inner_symmFun, inner_symmFun]
  ring

lemma symmFun_congr {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) {f g : ℝ → ℝ}
    (h : ∀ i, f (hT.eigenvalues rfl i) = g (hT.eigenvalues rfl i)) : symmFun hT f = symmFun hT g := by
  ext x
  refine eq_of_inner_eigenvectorBasis hT fun j => ?_
  rw [inner_symmFun, inner_symmFun, h]

lemma symmFun_id {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) : symmFun hT id = T := by
  ext x
  refine eq_of_inner_eigenvectorBasis hT fun j => ?_
  rw [inner_symmFun, ← hT, hT.apply_eigenvectorBasis, inner_smul_left]
  simp

lemma symmFun_one {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) : symmFun hT (fun _ => 1) = LinearMap.id := by
  ext x
  refine eq_of_inner_eigenvectorBasis hT fun j => ?_
  rw [inner_symmFun, one_mul, LinearMap.id_apply]

lemma isSymmetric_symmFun {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) (f : ℝ → ℝ) : (symmFun hT f).IsSymmetric := by
  intro x y
  simp only [symmFun, LinearMap.coe_mk, AddHom.coe_mk, sum_inner, inner_sum, inner_smul_left, inner_smul_right,
    RCLike.conj_to_real]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_comm x]
  ring

/-- For symmetric `W` with `1 - W` positive definite and odd `n`: `det (1 - W) > 0` and
`log det (1 - W) ≤ -Σ_{j=1}^n Tr(W^j) / j`. -/
theorem log_det_one_sub_le {W : E →ₗ[ℝ] E} (hW : W.IsSymmetric) (hpos : ∀ x ≠ 0, 0 < ⟪x, (1 - W) x⟫)
    {n : ℕ} (hn : Odd n) :
    0 < LinearMap.det (1 - W) ∧
      Real.log (LinearMap.det (1 - W)) ≤  -- totalisation-audit: allow det (1 - W) > 0, proved as the first conjunct
        -∑ j ∈ Finset.range n, LinearMap.trace ℝ E (W ^ (j + 1)) / (j + 1) := by  -- totalisation-audit: allow divisor j + 1 >= 1
  set b := hW.eigenvectorBasis rfl
  set ν := hW.eigenvalues rfl
  have hM : LinearMap.toMatrix b.toBasis b.toBasis W = Matrix.diagonal ν := by
    rw [hW.toMatrix_eigenvectorBasis rfl]
    simp [RCLike.ofReal_real_eq_id, ν]
  have hdet : LinearMap.det (1 - W) = ∏ i, (1 - ν i) := by
    rw [← LinearMap.det_toMatrix b.toBasis, map_sub, LinearMap.toMatrix_one, hM, ← Matrix.diagonal_one,
      Matrix.diagonal_sub, Matrix.det_diagonal]
  have htr : ∀ j : ℕ, LinearMap.trace ℝ E (W ^ j) = ∑ i, ν i ^ j := by
    intro j
    rw [LinearMap.trace_eq_matrix_trace ℝ b.toBasis, ← LinearMap.toMatrix_pow, hM, Matrix.diagonal_pow,
      Matrix.trace_diagonal]
    rfl
  have hν : ∀ i, 0 < 1 - ν i := by
    intro i
    have h := hpos (b i) (b.orthonormal.ne_zero i)
    rwa [LinearMap.sub_apply, Module.End.one_apply, hW.apply_eigenvectorBasis, inner_sub_right, inner_smul_right,
      real_inner_self_eq_norm_sq, b.orthonormal.1 i, one_pow, mul_one] at h
  refine ⟨hdet ▸ Finset.prod_pos fun i _ => hν i, ?_⟩
  rw [hdet, Real.log_prod (fun i _ => (hν i).ne')]
  have hterm : ∀ i, Real.log (1 - ν i) ≤ ∑ j ∈ Finset.range n, -(ν i ^ (j + 1) / (j + 1)) := by  -- totalisation-audit: allow 1 - nu i > 0 (hnu); divisor j + 1 >= 1
    intro i
    have h := log_one_add_le_alternating hn (x := -ν i) (by linarith [hν i])
    rw [← sub_eq_add_neg] at h
    refine h.trans (le_of_eq (Finset.sum_congr rfl fun j _ => ?_))
    rw [neg_pow (ν i), ← mul_assoc, ← pow_add, Odd.neg_one_pow ⟨j, by ring⟩]
    ring
  calc ∑ i, Real.log (1 - ν i) ≤ ∑ i, ∑ j ∈ Finset.range n, -(ν i ^ (j + 1) / (j + 1)) :=  -- totalisation-audit: allow 1 - nu i > 0 (hnu); divisor j + 1 >= 1
        Finset.sum_le_sum fun i _ => hterm i
    _ = -∑ j ∈ Finset.range n, LinearMap.trace ℝ E (W ^ (j + 1)) / (j + 1) := by  -- totalisation-audit: allow divisor j + 1 >= 1
        rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [htr, Finset.sum_div, ← Finset.sum_neg_distrib]

/-- The square root `G^{1/2}` and its inverse: `G^{1/2} G^{1/2} = G`, `G^{1/2} G^{-1/2} = G^{-1/2} G^{1/2} = 1`. -/
lemma sqrt_relations {G : E →ₗ[ℝ] E} (hG : G.IsSymmetric) (hGpos : ∀ x ≠ 0, 0 < ⟪x, G x⟫) :
    symmFun hG Real.sqrt * symmFun hG Real.sqrt = G ∧
      symmFun hG Real.sqrt * symmFun hG (fun t => (Real.sqrt t)⁻¹) = 1 ∧
        symmFun hG (fun t => (Real.sqrt t)⁻¹) * symmFun hG Real.sqrt = 1 := by
  have hl := eigenvalues_pos hG rfl hGpos
  refine ⟨?_, ?_, ?_⟩
  · rw [Module.End.mul_eq_comp, symmFun_comp]
    exact (symmFun_congr hG (g := id) fun i => Real.mul_self_sqrt (hl i).le).trans (symmFun_id hG)
  · rw [Module.End.mul_eq_comp, symmFun_comp, Module.End.one_eq_id]
    exact (symmFun_congr hG (g := fun _ => 1) fun i => mul_inv_cancel₀ (Real.sqrt_pos.mpr (hl i)).ne').trans
      (symmFun_one hG)
  · rw [Module.End.mul_eq_comp, symmFun_comp, Module.End.one_eq_id]
    exact (symmFun_congr hG (g := fun _ => 1) fun i => inv_mul_cancel₀ (Real.sqrt_pos.mpr (hl i)).ne').trans
      (symmFun_one hG)

/-- **(3.46)**: `det (H - V) = det H · det (1 - G^{1/2} V G^{1/2})` for `G` positive definite symmetric, `H G = 1`. -/
theorem det_sub_eq_det_mul_det {G H V : E →ₗ[ℝ] E} (hG : G.IsSymmetric) (hGpos : ∀ x ≠ 0, 0 < ⟪x, G x⟫)
    (hHG : H * G = 1) :
    LinearMap.det (H - V) =
      LinearMap.det H * LinearMap.det (1 - symmFun hG Real.sqrt * V * symmFun hG Real.sqrt) := by
  obtain ⟨hSS, hSSi, hSiS⟩ := sqrt_relations hG hGpos
  set S := symmFun hG Real.sqrt
  set Si := symmFun hG (fun t => (Real.sqrt t)⁻¹)
  have hH : H = Si * Si := by
    calc H = H * (G * (Si * Si)) := by
          rw [← hSS, show S * S * (Si * Si) = S * (S * Si) * Si by noncomm_ring, hSSi, mul_one, hSSi, mul_one]
      _ = Si * Si := by rw [← mul_assoc, hHG, one_mul]
  have hHV : H - V = Si * (1 - S * V * S) * Si := by
    rw [hH, mul_sub, sub_mul, mul_one, show Si * (S * V * S) * Si = (Si * S) * V * (S * Si) by noncomm_ring, hSiS,
      hSSi, one_mul, mul_one]
  rw [hHV, hH, map_mul, map_mul, map_mul]
  ring

/-- **(3.47)**: for odd `n`, `det (1 - G^{1/2} V G^{1/2})^{-1/2} ≥ exp Σ_{j=1}^n Tr((G V)^j) / (2j)` (written with
`j + 1`, `j < n`), for `G` positive definite symmetric, `H G = 1`, `V` symmetric and `H - V` positive definite. -/
theorem exp_trace_le_rpow_det {G H V : E →ₗ[ℝ] E} (hG : G.IsSymmetric) (hGpos : ∀ x ≠ 0, 0 < ⟪x, G x⟫)
    (hHG : H * G = 1) (hV : V.IsSymmetric) (hHV : ∀ x ≠ 0, 0 < ⟪x, (H - V) x⟫) {n : ℕ} (hn : Odd n) :
    Real.exp (∑ j ∈ Finset.range n, LinearMap.trace ℝ E ((G * V) ^ (j + 1)) / (2 * (j + 1))) ≤  -- totalisation-audit: allow divisor 2 (j + 1) >= 2
      LinearMap.det (1 - symmFun hG Real.sqrt * V * symmFun hG Real.sqrt) ^ (-(1 / 2 : ℝ)) := by  -- totalisation-audit: allow the base det (1 - G^{1/2} V G^{1/2}) is > 0 under the hypotheses (log_det_one_sub_le)
  obtain ⟨hSS, hSSi, hSiS⟩ := sqrt_relations hG hGpos
  have hSsymm := isSymmetric_symmFun hG Real.sqrt
  set S := symmFun hG Real.sqrt
  set Si := symmFun hG (fun t => (Real.sqrt t)⁻¹)
  set W := S * V * S
  have hH : H = Si * Si := by
    calc H = H * (G * (Si * Si)) := by
          rw [← hSS, show S * S * (Si * Si) = S * (S * Si) * Si by noncomm_ring, hSSi, mul_one, hSSi, mul_one]
      _ = Si * Si := by rw [← mul_assoc, hHG, one_mul]
  have hWsymm : W.IsSymmetric := by
    intro x y
    simp only [W, Module.End.mul_apply]
    rw [hSsymm, hV, hSsymm]
  have hWpos : ∀ x ≠ 0, 0 < ⟪x, (1 - W) x⟫ := by
    intro x hx
    have hfac : 1 - W = S * (H - V) * S := by
      rw [mul_sub, sub_mul, hH, show S * (Si * Si) * S = (S * Si) * (Si * S) by noncomm_ring, hSSi, hSiS, one_mul]
    have hSx : S x ≠ 0 := by
      intro h0
      apply hx
      have := congrArg Si h0
      rwa [map_zero, ← Module.End.mul_apply, hSiS, Module.End.one_apply] at this
    rw [hfac, Module.End.mul_apply, Module.End.mul_apply, ← hSsymm]
    exact hHV _ hSx
  obtain ⟨hdet, hlog⟩ := log_det_one_sub_le hWsymm hWpos hn
  have hconj : ∀ k : ℕ, (G * V) ^ k = S * W ^ k * Si := by
    intro k
    induction k with
    | zero => rw [pow_zero, pow_zero, mul_one, hSSi]
    | succ k ih =>
      rw [pow_succ, ih, pow_succ, ← hSS]
      simp only [W]
      rw [show S * (S * V * S) ^ k * Si * (S * S * V) = S * (S * V * S) ^ k * (Si * S) * S * V by noncomm_ring,
        hSiS, mul_one, show S * ((S * V * S) ^ k * (S * V * S)) * Si = S * (S * V * S) ^ k * S * V * (S * Si) by
          noncomm_ring, hSSi, mul_one]
  have htr : ∀ k : ℕ, LinearMap.trace ℝ E ((G * V) ^ k) = LinearMap.trace ℝ E (W ^ k) := by
    intro k
    rw [hconj, mul_assoc, LinearMap.trace_mul_comm, mul_assoc, hSiS, mul_one]
  rw [Real.rpow_def_of_pos hdet, Real.exp_le_exp]
  have hsum : ∑ j ∈ Finset.range n, LinearMap.trace ℝ E ((G * V) ^ (j + 1)) / (2 * (j + 1)) =  -- totalisation-audit: allow divisor 2 (j + 1) >= 2
      1 / 2 * ∑ j ∈ Finset.range n, LinearMap.trace ℝ E (W ^ (j + 1)) / (j + 1) := by  -- totalisation-audit: allow divisors 2 and j + 1 are positive
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [htr]
    field_simp
  rw [hsum]
  linarith

/-- `f(T) b_i = f(λ_i) b_i` on the eigenbasis. -/
lemma symmFun_eigenvectorBasis {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) (f : ℝ → ℝ) (i : Fin (Module.finrank ℝ E)) :
    symmFun hT f (hT.eigenvectorBasis rfl i) = f (hT.eigenvalues rfl i) • hT.eigenvectorBasis rfl i := by
  refine eq_of_inner_eigenvectorBasis hT fun j => ?_
  rw [inner_symmFun, inner_smul_right, orthonormal_iff_ite.mp (hT.eigenvectorBasis rfl).orthonormal]
  split_ifs with h
  · rw [h]
  · simp

/-- `det (1 + W) ≤ exp (Tr W)` for symmetric `W ≥ 0` (from `1 + w ≤ e^w` on the eigenvalues). -/
theorem det_one_add_le_exp_trace {W : E →ₗ[ℝ] E} (hW : W.IsSymmetric) (hpos : ∀ x, 0 ≤ ⟪x, W x⟫) :
    LinearMap.det (1 + W) ≤ Real.exp (LinearMap.trace ℝ E W) := by
  set b := hW.eigenvectorBasis rfl
  set ν := hW.eigenvalues rfl
  have hM : LinearMap.toMatrix b.toBasis b.toBasis W = Matrix.diagonal ν := by
    rw [hW.toMatrix_eigenvectorBasis rfl]
    simp [RCLike.ofReal_real_eq_id, ν]
  have hν : ∀ i, 0 ≤ ν i := by
    intro i
    have h := hpos (b i)
    rwa [hW.apply_eigenvectorBasis, inner_smul_right, real_inner_self_eq_norm_sq, b.orthonormal.1 i, one_pow,
      mul_one] at h
  rw [← LinearMap.det_toMatrix b.toBasis, map_add, LinearMap.toMatrix_one, hM, ← Matrix.diagonal_one,
    Matrix.diagonal_add, Matrix.det_diagonal, LinearMap.trace_eq_matrix_trace ℝ b.toBasis, hM,
    Matrix.trace_diagonal, Real.exp_sum]
  exact Finset.prod_le_prod₀ (fun i _ => by linarith [hν i]) fun i _ => by
    linarith [Real.add_one_le_exp (ν i)]

/-- **`det (H + P) ≤ det H · exp(Tr P / m)`** for symmetric `H ≥ m > 0` and symmetric `P ≥ 0`. -/
theorem det_add_le {H P : E →ₗ[ℝ] E} (hH : H.IsSymmetric) {m : ℝ} (hm : 0 < m) (hHm : ∀ x, m * ‖x‖ ^ 2 ≤ ⟪x, H x⟫)
    (hP : P.IsSymmetric) (hPpos : ∀ x, 0 ≤ ⟪x, P x⟫) :
    LinearMap.det (H + P) ≤ LinearMap.det H * Real.exp (LinearMap.trace ℝ E P / m) := by  -- totalisation-audit: allow m > 0 by hypothesis
  have hGpos : ∀ x ≠ 0, 0 < ⟪x, H x⟫ := fun x hx =>
    lt_of_lt_of_le (mul_pos hm (pow_pos (norm_pos_iff.mpr hx) 2)) (hHm x)
  obtain ⟨hSS, -, hSiS⟩ := sqrt_relations hH hGpos
  have hSSi := (sqrt_relations hH hGpos).2.1
  have hSisymm := isSymmetric_symmFun hH (fun t => (Real.sqrt t)⁻¹)
  set S := symmFun hH Real.sqrt
  set Si := symmFun hH (fun t => (Real.sqrt t)⁻¹)
  set W := Si * P * Si
  have hfac : H + P = S * (1 + W) * S := by
    rw [mul_add, add_mul, mul_one, hSS, show S * W * S = (S * Si) * P * (Si * S) by simp only [W]; noncomm_ring,
      hSSi, hSiS, one_mul, mul_one]
  have hWsymm : W.IsSymmetric := by
    intro x y
    simp only [W, Module.End.mul_apply]
    rw [hSisymm, hP, hSisymm]
  have hWpos : ∀ x, 0 ≤ ⟪x, W x⟫ := by
    intro x
    simp only [W, Module.End.mul_apply]
    rw [← hSisymm]
    exact hPpos _
  have hdetH : 0 < LinearMap.det H := det_pos_of_pos hH hGpos
  have hdet : LinearMap.det (H + P) = LinearMap.det H * LinearMap.det (1 + W) := by
    rw [hfac, map_mul, map_mul, ← hSS, map_mul]
    ring
  have htr : LinearMap.trace ℝ E W ≤ LinearMap.trace ℝ E P / m := by  -- totalisation-audit: allow m > 0 by hypothesis
    set b := hH.eigenvectorBasis rfl
    rw [LinearMap.trace_eq_sum_inner W b, LinearMap.trace_eq_sum_inner P b, Finset.sum_div]
    refine Finset.sum_le_sum fun i _ => ?_
    have hlam : m ≤ hH.eigenvalues rfl i := by
      have h := hHm (b i)
      rwa [hH.apply_eigenvectorBasis, inner_smul_right, real_inner_self_eq_norm_sq, b.orthonormal.1 i, one_pow,
        mul_one, mul_one] at h
    have hlam0 : 0 < hH.eigenvalues rfl i := lt_of_lt_of_le hm hlam
    simp only [W, Module.End.mul_apply]
    rw [← hSisymm, symmFun_eigenvectorBasis, map_smul, inner_smul_left, inner_smul_right, RCLike.conj_to_real]
    have hs : (Real.sqrt (hH.eigenvalues rfl i))⁻¹ * (Real.sqrt (hH.eigenvalues rfl i))⁻¹ =
        (hH.eigenvalues rfl i)⁻¹ := by
      rw [← mul_inv, Real.mul_self_sqrt hlam0.le]
    rw [← mul_assoc, hs, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_right (inv_anti₀ hm hlam) (hPpos _)
  rw [hdet]
  exact mul_le_mul_of_nonneg_left ((det_one_add_le_exp_trace hWsymm hWpos).trans (Real.exp_le_exp.mpr htr))
    hdetH.le

end GaussianBlockSpin
