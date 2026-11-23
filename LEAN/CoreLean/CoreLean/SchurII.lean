/-
`lem:block-interpolation` of BALABAN_CORE.tex (`8913c33305b3`): the steps on the space `𝔤^c_m`.

* `row_sum_vec`: the sums of kernels for a kernel of linear maps of a finite-dimensional space with a basis
  `e_k`, `k ∈ ι`, and coordinates `c_k`, `|c_k(Z)| ≤ α‖Z‖`, `‖e_k‖ ≤ β`: if `‖Tf‖_∞ ≤ b‖f‖_∞`, then
  `Σ_{x'} η⁴‖K(x, x')‖ ≤ |ι|²α²β²b` (the core's argument with the signs `s(x')`, through `row_sum_le`).
* `flat`, `basisS`: the flattening of the matrices into `EuclideanSpace ℂ (Fin N × Fin N)`, of the norm
  `√N|·|`; an orthonormal basis of the image of a subspace `S` gives a basis of `S` with `|c_k(Z)| ≤ √N‖Z‖`
  and `‖e_k‖ ≤ 1`, at most `N²` elements (the core's basis orthonormal for `tr Z^*Z'` has `|c_k| ≤ ‖Z‖`,
  `‖e_k‖ ≤ √N`; the products `α²β² = N` agree).
* `transpose_bound`: for a subspace closed under `X ↦ X^*` and the pairing `⟨Z, Z'⟩ = Σ_ι tr Z_ιZ'_ι`,
  `‖K^T‖ ≤ mN‖K‖`.
* `block_interpolation`: `‖1_YTf‖₂ ≤ c_I√(bb')‖f‖₂`, `c_I = 2¹²N⁶`, for `m ≤ 16`.
-/
import CoreLean.Schur
import CoreLean.OpNorm
import CoreLean.Algebra

open Finset Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean
namespace Schur

/-! ### The sums of kernels for a vector-valued kernel -/

section RowSum

variable {Y : Type*} [Fintype Y] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {ι : Type*} [Fintype ι]

/-- The sums of kernels: `Σ_{x'} w'(x')‖K(x')‖ ≤ |ι|²α²β²b`. -/
theorem row_sum_vec (w' : Y → ℝ) (hw' : ∀ y, 0 ≤ w' y) (K : Y → E →L[ℂ] E) (e : ι → E)
    (c : ι → E →ₗ[ℂ] ℂ) (α β b : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hexp : ∀ Z, Z = ∑ k, c k Z • e k) (hc : ∀ k Z, ‖c k Z‖ ≤ α * ‖Z‖) (he : ∀ k, ‖e k‖ ≤ β)
    (hT : ∀ f : Y → E, (∀ y, ‖f y‖ ≤ β) → ‖∑ y, w' y • K y (f y)‖ ≤ b * β) :
    ∑ y, w' y * ‖K y‖ ≤ (Fintype.card ι : ℝ) ^ 2 * α ^ 2 * β ^ 2 * b := by
  -- the coordinates of the images of the basis
  have h1 : ∀ k k', ∑ y, w' y * ‖c k' (K y (e k))‖ ≤ α * (b * β) := by
    intro k k'
    refine row_sum_le w' hw' (fun y => c k' (K y (e k))) _ fun f hf => ?_
    have e1 : ∑ y, (w' y : ℂ) * c k' (K y (e k)) * f y =
        c k' (∑ y, w' y • K y (f y • e k)) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [← Complex.coe_smul, map_smul, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
      ring
    rw [e1]
    refine (hc k' _).trans (mul_le_mul_of_nonneg_left (hT _ fun y => ?_) hα)
    rw [norm_smul]
    calc ‖f y‖ * ‖e k‖ ≤ 1 * β := mul_le_mul (hf y) (he k) (norm_nonneg _) zero_le_one
      _ = β := one_mul _
  -- `‖K‖ ≤ αβ Σ_{k, k'} |c_{k'}(K e_k)|`
  have h2 : ∀ y, ‖K y‖ ≤ α * β * ∑ k, ∑ k', ‖c k' (K y (e k))‖ := by
    intro y
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun Z => ?_
    have hKe : ∀ k, ‖K y (e k)‖ ≤ β * ∑ k', ‖c k' (K y (e k))‖ := fun k => by
      conv_lhs => rw [hexp (K y (e k))]
      refine (norm_sum_le _ _).trans ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun k' _ => ?_
      rw [norm_smul, mul_comm β]
      exact mul_le_mul_of_nonneg_left (he k') (norm_nonneg _)
    have eZ : K y Z = ∑ k, c k Z • K y (e k) := by
      conv_lhs => rw [hexp Z]
      rw [map_sum]
      simp only [map_smul]
    rw [eZ]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ k, ‖c k Z • K y (e k)‖ ≤ ∑ k, α * ‖Z‖ * (β * ∑ k', ‖c k' (K y (e k))‖) := by
          refine Finset.sum_le_sum fun k _ => ?_
          rw [norm_smul]
          exact mul_le_mul (hc k Z) (hKe k) (norm_nonneg _) (by positivity)
      _ = α * β * (∑ k, ∑ k', ‖c k' (K y (e k))‖) * ‖Z‖ := by
          simp only [Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun k' _ => by ring
  calc ∑ y, w' y * ‖K y‖ ≤ ∑ y, w' y * (α * β * ∑ k, ∑ k', ‖c k' (K y (e k))‖) :=
        Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (h2 y) (hw' y)
    _ = α * β * ∑ k, ∑ k', ∑ y, w' y * ‖c k' (K y (e k))‖ := by
        rw [Finset.mul_sum]
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k' _ => Finset.sum_congr rfl fun y _ => by ring
    _ ≤ α * β * ∑ _k : ι, ∑ _k' : ι, α * (b * β) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ =>
          Finset.sum_le_sum fun k' _ => h1 k k') (by positivity)
    _ = (Fintype.card ι : ℝ) ^ 2 * α ^ 2 * β ^ 2 * b := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

end RowSum

/-! ### A basis of a subspace of the matrices -/

section Matrices

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ

/-- The flattening of the matrices. -/
def flat : Mat ≃ₗ[ℂ] EuclideanSpace ℂ (Fin N × Fin N) :=
  (Matrix.ofLinearEquiv ℂ).symm.trans ((LinearEquiv.curry ℂ ℂ (Fin N) (Fin N)).symm.trans
    (EuclideanSpace.equiv (Fin N × Fin N) ℂ).symm.toLinearEquiv)

lemma flat_apply (A : Mat) (p : Fin N × Fin N) : flat A p = A p.1 p.2 := rfl

/-- `‖flat A‖ = √N|A|`. -/
lemma norm_flat (hN : 0 < N) (A : Mat) : ‖flat A‖ = Real.sqrt N * hs A := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have h1 : ‖flat A‖ ^ 2 = (Real.sqrt N * hs A) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), hs_sq, hs2_eq_sum,
      ← mul_assoc, mul_inv_cancel₀ hN', one_mul, Fintype.sum_prod_type, Finset.sum_comm]
    simp only [flat_apply, Complex.sq_norm]
  exact (pow_left_inj₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (hs_nonneg A)) two_ne_zero).1 h1

/-- The image of `S`. -/
abbrev VS (S : Submodule ℂ Mat) : Submodule ℂ (EuclideanSpace ℂ (Fin N × Fin N)) := S.map flat.toLinearMap

/-- An orthonormal basis of the image of `S`. -/
abbrev bS (S : Submodule ℂ Mat) := stdOrthonormalBasis ℂ (VS S)

/-- The basis of `S`. -/
def eS (S : Submodule ℂ Mat) (k : Fin (Module.finrank ℂ (VS S))) : Mat := flat.symm ((bS S k : VS S) : EuclideanSpace ℂ _)

lemma eS_mem (S : Submodule ℂ Mat) (k : Fin (Module.finrank ℂ (VS S))) : eS S k ∈ S := by
  obtain ⟨A, hA, hAe⟩ := Submodule.mem_map.1 (bS S k).2
  rw [eS, ← hAe]
  simpa using hA

/-- The coordinates `c_k(Z) = ⟨b_k, flat Z⟩`. -/
def cS (S : Submodule ℂ Mat) (k : Fin (Module.finrank ℂ (VS S))) : Mat →ₗ[ℂ] ℂ :=
  (innerₛₗ ℂ ((bS S k : VS S) : EuclideanSpace ℂ (Fin N × Fin N))).comp flat.toLinearMap

lemma cS_apply (S : Submodule ℂ Mat) (k : Fin (Module.finrank ℂ (VS S))) (Z : Mat) :
    cS S k Z = inner ℂ ((bS S k : VS S) : EuclideanSpace ℂ (Fin N × Fin N)) (flat Z) := rfl

set_option maxHeartbeats 1000000 in
lemma expand_S (S : Submodule ℂ Mat) {Z : Mat} (hZ : Z ∈ S) : Z = ∑ k, cS S k Z • eS S k := by
  have hz : flat Z ∈ VS S := Submodule.mem_map_of_mem hZ
  set v : VS S := ⟨flat Z, hz⟩ with hv
  have h : ∑ k, inner ℂ (bS S k) v • bS S k = v := (bS S).sum_repr' v
  have h' : ∑ k, inner ℂ ((bS S k : VS S) : EuclideanSpace ℂ (Fin N × Fin N)) (flat Z) •
      ((bS S k : VS S) : EuclideanSpace ℂ (Fin N × Fin N)) = flat Z := by
    have := congrArg Subtype.val h
    rw [Submodule.coe_sum] at this
    exact this
  have h'' := congrArg flat.symm h'
  rw [map_sum, LinearEquiv.symm_apply_apply] at h''
  conv_lhs => rw [← h'']
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul]
  rfl

lemma norm_cS_le (S : Submodule ℂ Mat) (hN : 0 < N) (k : Fin (Module.finrank ℂ (VS S))) (Z : Mat) :
    ‖cS S k Z‖ ≤ Real.sqrt N * ‖Z‖ := by
  rw [cS_apply]
  refine (norm_inner_le_norm _ _).trans ?_
  have hb : ‖((bS S k : VS S) : EuclideanSpace ℂ (Fin N × Fin N))‖ = 1 := (bS S).orthonormal.1 k
  rw [hb, one_mul, norm_flat hN]
  exact mul_le_mul_of_nonneg_left (hs_le_opNorm hN Z) (Real.sqrt_nonneg _)

lemma norm_eS_le (S : Submodule ℂ Mat) (hN : 0 < N) (k : Fin (Module.finrank ℂ (VS S))) : ‖eS S k‖ ≤ 1 := by
  refine (opNorm_le_sqrt_mul_hs _).trans ?_
  have hb : ‖((bS S k : VS S) : EuclideanSpace ℂ (Fin N × Fin N))‖ = 1 := (bS S).orthonormal.1 k
  rw [← norm_flat hN, eS, LinearEquiv.apply_symm_apply, hb]

lemma finrank_VS_le (S : Submodule ℂ Mat) : Module.finrank ℂ (VS S) ≤ N * N := by
  refine (Submodule.finrank_le _).trans (le_of_eq ?_)
  simp

/-! ### The space `𝔤^c_m` -/

variable {m : ℕ}

/-- The basis of `S^m`: `e_k` in the component `ι`. -/
def eE (S : Submodule ℂ Mat) (q : Fin m × Fin (Module.finrank ℂ (VS S))) : Fin m → S :=
  Pi.single q.1 ⟨eS S q.2, eS_mem S q.2⟩

/-- The coordinates on `S^m`. -/
def cE (S : Submodule ℂ Mat) (q : Fin m × Fin (Module.finrank ℂ (VS S))) : (Fin m → S) →ₗ[ℂ] ℂ :=
  (cS S q.2).comp (S.subtype.comp (LinearMap.proj q.1))

lemma expand_E (S : Submodule ℂ Mat) (Z : Fin m → S) : Z = ∑ q, cE S q Z • eE S q := by
  rw [Fintype.sum_prod_type]
  conv_lhs => rw [← Finset.univ_sum_single Z]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hz : (Z i : Mat) = ∑ k, cS S k (Z i) • eS S k := expand_S S (Z i).2
  have hz' : Z i = ∑ k, cS S k (Z i) • (⟨eS S k, eS_mem S k⟩ : S) := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    simp only [Submodule.coe_smul]
    exact hz
  calc Pi.single i (Z i) = LinearMap.single ℂ (fun _ : Fin m => (S : Type _)) i (Z i) := rfl
    _ = ∑ k, cS S k (Z i) • LinearMap.single ℂ (fun _ : Fin m => (S : Type _)) i
          (⟨eS S k, eS_mem S k⟩ : S) := by
        conv_lhs => rw [hz']
        rw [map_sum]
        simp only [map_smul]
    _ = ∑ k, cE S (i, k) Z • eE S (i, k) := rfl

lemma norm_cE_le (S : Submodule ℂ Mat) (hN : 0 < N) (q : Fin m × Fin (Module.finrank ℂ (VS S))) (Z : Fin m → S) :
    ‖cE S q Z‖ ≤ Real.sqrt N * ‖Z‖ := by
  refine (norm_cS_le S hN q.2 _).trans (mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _))
  show ‖((Z q.1 : S) : Mat)‖ ≤ ‖Z‖
  exact norm_le_pi_norm Z q.1

lemma norm_eE_le (S : Submodule ℂ Mat) (hN : 0 < N) (q : Fin m × Fin (Module.finrank ℂ (VS S))) : ‖eE S q‖ ≤ 1 := by
  rw [eE, Pi.norm_single]
  exact norm_eS_le S hN q.2

/-! ### The transpose -/

/-- The pairing `⟨Z, Z'⟩ = Σ_ι tr Z_ιZ'_ι` with the normalised trace. -/
def pair (S : Submodule ℂ Mat) (Z X : Fin m → S) : ℂ := ∑ ι, ntr (((Z ι : S) : Mat) * ((X ι : S) : Mat))

lemma pair_comm (S : Submodule ℂ Mat) (Z X : Fin m → S) : pair S Z X = pair S X Z := by
  unfold pair ntr
  refine Finset.sum_congr rfl fun ι _ => ?_
  rw [Matrix.trace_mul_comm]

lemma ntr_conj_self (W : Mat) : ntr (Wᴴ * W) = ((hs W ^ 2 : ℝ) : ℂ) := by
  rw [hs_sq, hs2_eq_sum]
  unfold ntr
  rw [trace_conjTranspose_mul_self]
  push_cast
  ring

/-- `‖K^T‖ ≤ mN‖K‖` for a subspace closed under `X ↦ X^*`. -/
theorem transpose_bound (S : Submodule ℂ Mat) (hN : 0 < N) (hS : ∀ A ∈ S, Aᴴ ∈ S) (K K' : (Fin m → S) →L[ℂ] (Fin m → S))
    (h : ∀ Z X, pair S Z (K' X) = pair S (K Z) X) : ‖K'‖ ≤ m * N * ‖K‖ := by
  have hsN : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt (Nat.cast_nonneg _)
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun X => ?_
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun ι => ?_
  set W : Mat := ((K' X ι : S) : Mat) with hWd
  set Z : Fin m → S := Pi.single ι ⟨Wᴴ, hS _ (K' X ι).2⟩ with hZd
  have hZn : ‖Z‖ = ‖W‖ := by
    rw [hZd, Pi.norm_single]
    exact opNorm_conjTranspose W
  -- `|W|² = ⟨Z, K^T X⟩ = ⟨KZ, X⟩`
  have hpair : pair S Z (K' X) = ((hs W ^ 2 : ℝ) : ℂ) := by
    unfold pair
    rw [Finset.sum_eq_single ι]
    · simp [hZd, hWd, ntr_conj_self]
    · intro κ _ hκ
      simp [hZd, Pi.single_eq_of_ne hκ, ntr]
    · simp
  have hbound : ‖pair S (K Z) X‖ ≤ m * (‖K‖ * ‖W‖ * ‖X‖) := by
    unfold pair
    refine (norm_sum_le _ _).trans ?_
    calc ∑ κ, ‖ntr (((K Z κ : S) : Mat) * ((X κ : S) : Mat))‖
        ≤ ∑ _κ : Fin m, ‖K‖ * ‖W‖ * ‖X‖ := by
          refine Finset.sum_le_sum fun κ _ => ?_
          refine (norm_ntr_mul_le _ _).trans ?_
          have a1 : hs ((K Z κ : S) : Mat) ≤ ‖K Z‖ := by
            refine (hs_le_opNorm hN _).trans ?_
            exact norm_le_pi_norm _ κ
          have a2 : hs ((X κ : S) : Mat) ≤ ‖X‖ := by
            refine (hs_le_opNorm hN _).trans ?_
            exact norm_le_pi_norm _ κ
          have a3 : ‖K Z‖ ≤ ‖K‖ * ‖W‖ := by rw [← hZn]; exact K.le_opNorm Z
          calc hs ((K Z κ : S) : Mat) * hs ((X κ : S) : Mat) ≤ ‖K Z‖ * ‖X‖ :=
                mul_le_mul a1 a2 (hs_nonneg _) (norm_nonneg _)
            _ ≤ ‖K‖ * ‖W‖ * ‖X‖ := mul_le_mul_of_nonneg_right a3 (norm_nonneg _)
      _ = m * (‖K‖ * ‖W‖ * ‖X‖) := by simp
  have hsq : hs W ^ 2 ≤ m * (‖K‖ * ‖W‖ * ‖X‖) := by
    have := h Z X
    rw [hpair] at this
    have e := congrArg norm this
    rw [Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)] at e
    rw [e]; exact hbound
  have hWop : ‖W‖ ≤ Real.sqrt N * hs W := opNorm_le_sqrt_mul_hs W
  have hK0 : 0 ≤ ‖K‖ := K.opNorm_nonneg
  show ‖K' X ι‖ ≤ m * N * ‖K‖ * ‖X‖
  show ‖W‖ ≤ m * N * ‖K‖ * ‖X‖
  rcases (hs_nonneg W).eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero] at hWop
    exact hWop.trans (by positivity)
  · -- `|W| ≤ m√N‖K‖‖X‖`
    have h2 : hs W ≤ m * Real.sqrt N * ‖K‖ * ‖X‖ := by
      have : hs W * hs W ≤ hs W * (m * Real.sqrt N * ‖K‖ * ‖X‖) := by
        calc hs W * hs W = hs W ^ 2 := by ring
          _ ≤ m * (‖K‖ * ‖W‖ * ‖X‖) := hsq
          _ ≤ m * (‖K‖ * (Real.sqrt N * hs W) * ‖X‖) := by gcongr
          _ = hs W * (m * Real.sqrt N * ‖K‖ * ‖X‖) := by ring
      exact le_of_mul_le_mul_left this hpos
    calc ‖W‖ ≤ Real.sqrt N * hs W := hWop
      _ ≤ Real.sqrt N * (m * Real.sqrt N * ‖K‖ * ‖X‖) := by gcongr
      _ = m * (Real.sqrt N * Real.sqrt N) * ‖K‖ * ‖X‖ := by ring
      _ = m * N * ‖K‖ * ‖X‖ := by rw [hsN]

/-! ### The bound in `L²` -/

/-- `|Z|² = Σ_ι |Z_ι|²` on `S^m`. -/
def hsF (S : Submodule ℂ Mat) (Z : Fin m → S) : ℝ := ∑ ι, hs ((Z ι : S) : Mat) ^ 2

lemma hsF_le (S : Submodule ℂ Mat) (hN : 0 < N) (Z : Fin m → S) : hsF S Z ≤ m * ‖Z‖ ^ 2 := by
  unfold hsF
  calc ∑ ι, hs ((Z ι : S) : Mat) ^ 2 ≤ ∑ _ι : Fin m, ‖Z‖ ^ 2 := by
        refine Finset.sum_le_sum fun ι _ => pow_le_pow_left₀ (hs_nonneg _) ?_ 2
        exact (hs_le_opNorm hN _).trans (norm_le_pi_norm Z ι)
    _ = m * ‖Z‖ ^ 2 := by simp

lemma norm_sq_le_hsF (S : Submodule ℂ Mat) (Z : Fin m → S) : ‖Z‖ ^ 2 ≤ N * hsF S Z := by
  have h0 : 0 ≤ hsF S Z := Finset.sum_nonneg fun ι _ => sq_nonneg _
  have h1 : ‖Z‖ ≤ Real.sqrt N * Real.sqrt (hsF S Z) := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun ι => ?_
    show ‖((Z ι : S) : Mat)‖ ≤ _
    refine (opNorm_le_sqrt_mul_hs _).trans (mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _))
    rw [← Real.sqrt_sq (hs_nonneg ((Z ι : S) : Mat))]
    exact Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun ι => hs ((Z ι : S) : Mat) ^ 2)
      (fun ι _ => sq_nonneg _) (Finset.mem_univ ι))
  calc ‖Z‖ ^ 2 ≤ (Real.sqrt N * Real.sqrt (hsF S Z)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ = N * hsF S Z := by rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), Real.sq_sqrt h0]

/-- **`lem:block-interpolation`**: for a subspace `S` of the matrices closed under `X ↦ X^*` (`𝔤^c`), forms
with `m ≤ 16` components, a kernel `K(x, x')` of linear maps of `S^m` with the transpose kernel `K'`
(`⟨Z, K'(x', x)V⟩ = ⟨K(x, x')Z, V⟩`), weights `w, w' ≥ 0` (`η⁴`), and the bounds `‖Tf‖_∞ ≤ b‖f‖_∞`,
`‖T^Tφ‖_∞ ≤ b'‖φ‖_∞`: `Σ_x w(x)|(Tf)(x)|² ≤ c_I² bb' Σ_{x'} w'(x')|f(x')|²`, `c_I = 2¹²N⁶`. -/
theorem block_interpolation (S : Submodule ℂ Mat) (hN : 0 < N) (hS : ∀ A ∈ S, Aᴴ ∈ S) (hm : m ≤ 16)
    {X Y : Type*} [Fintype X] [Fintype Y] (w : X → ℝ) (w' : Y → ℝ) (hw : ∀ x, 0 ≤ w x)
    (hw' : ∀ y, 0 ≤ w' y) (K : X → Y → (Fin m → S) →L[ℂ] (Fin m → S))
    (K' : Y → X → (Fin m → S) →L[ℂ] (Fin m → S))
    (hKK' : ∀ x y Z V, pair S Z (K' y x V) = pair S (K x y Z) V) (b b' : ℝ) (hb : 0 ≤ b) (hb' : 0 ≤ b')
    (hT : ∀ f : Y → (Fin m → S), ∀ c : ℝ, (∀ y, ‖f y‖ ≤ c) → ∀ x, ‖∑ y, w' y • K x y (f y)‖ ≤ b * c)
    (hT' : ∀ φ : X → (Fin m → S), ∀ c : ℝ, (∀ x, ‖φ x‖ ≤ c) → ∀ y, ‖∑ x, w x • K' y x (φ x)‖ ≤ b' * c)
    (f : Y → (Fin m → S)) :
    ∑ x, w x * hsF S (∑ y, w' y • K x y (f y)) ≤
      (2 ^ 12 * (N : ℝ) ^ 6) ^ 2 * b * b' * ∑ y, w' y * hsF S (f y) := by
  set d : ℕ := Fintype.card (Fin m × Fin (Module.finrank ℂ (VS S))) with hdd
  have hd : (d : ℝ) ≤ m * (N : ℝ) ^ 2 := by
    have : d ≤ m * (N * N) := by
      rw [hdd, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
      exact Nat.mul_le_mul_left _ (finrank_VS_le S)
    calc (d : ℝ) ≤ ((m * (N * N) : ℕ) : ℝ) := by exact_mod_cast this
      _ = m * (N : ℝ) ^ 2 := by push_cast; ring
  have hsN : Real.sqrt N ^ 2 = N := Real.sq_sqrt (Nat.cast_nonneg _)
  -- the sums of the kernels and of the transposes
  have rows : ∀ x, ∑ y, w' y * ‖K x y‖ ≤ (d : ℝ) ^ 2 * N * b := fun x => by
    have := row_sum_vec w' hw' (K x) (eE S) (cE S) (Real.sqrt N) 1 b (Real.sqrt_nonneg _) zero_le_one
      (expand_E S) (fun q Z => norm_cE_le S hN q Z) (fun q => norm_eE_le S hN q)
      (fun g hg => by simpa using hT g 1 hg x)
    rw [hsN, one_pow, mul_one] at this
    exact this
  have rows' : ∀ y, ∑ x, w x * ‖K' y x‖ ≤ (d : ℝ) ^ 2 * N * b' := fun y => by
    have := row_sum_vec w hw (K' y) (eE S) (cE S) (Real.sqrt N) 1 b' (Real.sqrt_nonneg _) zero_le_one
      (expand_E S) (fun q Z => norm_cE_le S hN q Z) (fun q => norm_eE_le S hN q)
      (fun g hg => by simpa using hT' g 1 hg y)
    rw [hsN, one_pow, mul_one] at this
    exact this
  have htr : ∀ x y, ‖K x y‖ ≤ m * N * ‖K' y x‖ := fun x y => by
    refine transpose_bound S hN hS (K' y x) (K x y) fun Z V => ?_
    rw [pair_comm, ← hKK' x y V Z, pair_comm]
  have cols : ∀ y, ∑ x, w x * ‖K x y‖ ≤ m * N * ((d : ℝ) ^ 2 * N * b') := fun y => by
    calc ∑ x, w x * ‖K x y‖ ≤ ∑ x, w x * (m * N * ‖K' y x‖) :=
          Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (htr x y) (hw x)
      _ = m * N * ∑ x, w x * ‖K' y x‖ := by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by ring
      _ ≤ m * N * ((d : ℝ) ^ 2 * N * b') := mul_le_mul_of_nonneg_left (rows' y) (by positivity)
  -- the test of Schur
  have hsch := schur w w' hw hw' K _ _ (by positivity) rows cols f
  -- the two norms
  have hconv : ∑ x, w x * hsF S (∑ y, w' y • K x y (f y)) ≤
      m * ∑ x, w x * ‖∑ y, w' y • K x y (f y)‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun x _ => ?_
    calc w x * hsF S (∑ y, w' y • K x y (f y)) ≤ w x * (m * ‖∑ y, w' y • K x y (f y)‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (hsF_le S hN _) (hw x)
      _ = m * (w x * ‖∑ y, w' y • K x y (f y)‖ ^ 2) := by ring
  have hconv' : ∑ y, w' y * ‖f y‖ ^ 2 ≤ N * ∑ y, w' y * hsF S (f y) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun y _ => ?_
    calc w' y * ‖f y‖ ^ 2 ≤ w' y * (N * hsF S (f y)) :=
          mul_le_mul_of_nonneg_left (norm_sq_le_hsF S (f y)) (hw' y)
      _ = N * (w' y * hsF S (f y)) := by ring
  have hF0 : 0 ≤ ∑ y, w' y * hsF S (f y) :=
    Finset.sum_nonneg fun y _ => mul_nonneg (hw' y) (Finset.sum_nonneg fun ι _ => sq_nonneg _)
  -- the constant: `m · d²Nb · mN d²Nb' · N = m²d⁴N⁴bb' ≤ m⁶N¹²bb' ≤ c_I²bb'`
  have hm' : (m : ℝ) ≤ 16 := by exact_mod_cast hm
  have hd4 : (d : ℝ) ^ 4 ≤ ((m : ℝ) * (N : ℝ) ^ 2) ^ 4 := pow_le_pow_left₀ (by positivity) hd 4
  have hm6 : (m : ℝ) ^ 6 ≤ 2 ^ 24 := by
    calc (m : ℝ) ^ 6 ≤ 16 ^ 6 := pow_le_pow_left₀ (by positivity) hm' 6
      _ = 2 ^ 24 := by norm_num
  have hconst : m * ((d : ℝ) ^ 2 * N * b * (m * N * ((d : ℝ) ^ 2 * N * b'))) * N ≤
      (2 ^ 12 * (N : ℝ) ^ 6) ^ 2 * b * b' := by
    have e1 : m * ((d : ℝ) ^ 2 * N * b * (m * N * ((d : ℝ) ^ 2 * N * b'))) * N =
        (m : ℝ) ^ 2 * (d : ℝ) ^ 4 * (N : ℝ) ^ 4 * (b * b') := by ring
    have e2 : (2 ^ 12 * (N : ℝ) ^ 6) ^ 2 * b * b' = 2 ^ 24 * (N : ℝ) ^ 12 * (b * b') := by ring
    rw [e1, e2]
    have hbb : 0 ≤ b * b' := mul_nonneg hb hb'
    calc (m : ℝ) ^ 2 * (d : ℝ) ^ 4 * (N : ℝ) ^ 4 * (b * b')
        ≤ (m : ℝ) ^ 2 * ((m : ℝ) * (N : ℝ) ^ 2) ^ 4 * (N : ℝ) ^ 4 * (b * b') := by gcongr
      _ = (m : ℝ) ^ 6 * (N : ℝ) ^ 12 * (b * b') := by ring
      _ ≤ 2 ^ 24 * (N : ℝ) ^ 12 * (b * b') := by gcongr
  calc ∑ x, w x * hsF S (∑ y, w' y • K x y (f y))
      ≤ m * ∑ x, w x * ‖∑ y, w' y • K x y (f y)‖ ^ 2 := hconv
    _ ≤ m * ((d : ℝ) ^ 2 * N * b * (m * N * ((d : ℝ) ^ 2 * N * b')) * ∑ y, w' y * ‖f y‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hsch (by positivity)
    _ ≤ m * ((d : ℝ) ^ 2 * N * b * (m * N * ((d : ℝ) ^ 2 * N * b')) * (N * ∑ y, w' y * hsF S (f y))) := by
        gcongr
    _ = m * ((d : ℝ) ^ 2 * N * b * (m * N * ((d : ℝ) ^ 2 * N * b'))) * N * ∑ y, w' y * hsF S (f y) := by
        ring
    _ ≤ (2 ^ 12 * (N : ℝ) ^ 6) ^ 2 * b * b' * ∑ y, w' y * hsF S (f y) :=
        mul_le_mul_of_nonneg_right hconst hF0

end Matrices

/-! ### The space `𝔤^c` -/

section LieC

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ

/-- `𝔤^c` is closed under `X ↦ X^*`: `(A + iB)^* = A + i(-B)`. -/
lemma lieC_star (G : GaugeGroup N) {X : Mat} (hX : X ∈ G.lieC) : Xᴴ ∈ G.lieC := by
  obtain ⟨A, hA, B, hB, rfl⟩ := hX
  refine ⟨A, hA, -B, G.neg_mem_lie hB, ?_⟩
  rw [conjTranspose_add, conjTranspose_smul, hA.1, hB.1, Complex.star_def, Complex.conj_I, smul_neg,
    neg_smul]

/-- **`lem:block-interpolation`** on `𝔤^c_m`. -/
theorem block_interpolation_lieC (G : GaugeGroup N) (hG : G.LieInput) (hN : 0 < N) {m : ℕ}
    (hm : m ≤ 16) {X Y : Type*} [Fintype X] [Fintype Y] (w : X → ℝ) (w' : Y → ℝ) (hw : ∀ x, 0 ≤ w x)
    (hw' : ∀ y, 0 ≤ w' y)
    (K : X → Y → (Fin m → GaugeGroup.lieCSubmodule hG) →L[ℂ] (Fin m → GaugeGroup.lieCSubmodule hG))
    (K' : Y → X → (Fin m → GaugeGroup.lieCSubmodule hG) →L[ℂ] (Fin m → GaugeGroup.lieCSubmodule hG))
    (hKK' : ∀ x y Z V, pair _ Z (K' y x V) = pair _ (K x y Z) V) (b b' : ℝ) (hb : 0 ≤ b) (hb' : 0 ≤ b')
    (hT : ∀ f : Y → (Fin m → GaugeGroup.lieCSubmodule hG), ∀ c : ℝ, (∀ y, ‖f y‖ ≤ c) →
      ∀ x, ‖∑ y, w' y • K x y (f y)‖ ≤ b * c)
    (hT' : ∀ φ : X → (Fin m → GaugeGroup.lieCSubmodule hG), ∀ c : ℝ, (∀ x, ‖φ x‖ ≤ c) →
      ∀ y, ‖∑ x, w x • K' y x (φ x)‖ ≤ b' * c)
    (f : Y → (Fin m → GaugeGroup.lieCSubmodule hG)) :
    ∑ x, w x * hsF _ (∑ y, w' y • K x y (f y)) ≤
      (2 ^ 12 * (N : ℝ) ^ 6) ^ 2 * b * b' * ∑ y, w' y * hsF _ (f y) :=
  block_interpolation _ hN (fun _ hA => lieC_star G hA) hm w w' hw hw' K K' hKK' b b' hb hb' hT hT' f

end LieC

end Schur
end CoreLean

end
