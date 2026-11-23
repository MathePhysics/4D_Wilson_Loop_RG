import Mathlib

/-!
# Gaussian integrals on finite-dimensional real inner product spaces

For a symmetric, positive definite linear map `T` on a finite-dimensional real inner product
space `E` (with its canonical volume),

  `∫ x, exp (-(1/2) ⟪x, T x⟫) = (2π) ^ (dim E / 2) / √(det T)`,

and, completing the square,

  `∫ x, exp (-(1/2) ⟪x, T x⟫ + ⟪T w, x⟫) = (2π) ^ (dim E / 2) / √(det T) * exp ((1/2) ⟪w, T w⟫)`.

The proof diagonalises `T` in an orthonormal eigenbasis, which preserves volume, and reduces to
a product of one-dimensional Gaussian integrals.
-/

open MeasureTheory Real
open scoped RealInnerProductSpace

namespace GaussianBlockSpin

/-- The one-dimensional Gaussian integral with variance `1 / c`. -/
lemma integral_exp_neg_half_mul_sq {c : ℝ} (hc : 0 < c) :
    ∫ t : ℝ, Real.exp (-(c / 2) * t ^ 2) = Real.sqrt (2 * π / c) := by
  rw [integral_gaussian (c / 2)]
  congr 1
  field_simp

/-- A diagonal Gaussian integral over Euclidean space is a product of one-dimensional ones. -/
lemma integral_exp_neg_half_sum_mul_sq {n : ℕ} (c : Fin n → ℝ) (hc : ∀ i, 0 < c i) :
    ∫ y : EuclideanSpace ℝ (Fin n), Real.exp (-(1 / 2) * ∑ i, c i * y i ^ 2) =
      ∏ i, Real.sqrt (2 * π / c i) := by
  have h1 : (fun y : EuclideanSpace ℝ (Fin n) => Real.exp (-(1 / 2) * ∑ i, c i * y i ^ 2)) =
      fun y => ∏ i, Real.exp (-(c i / 2) * y i ^ 2) := by
    funext y
    rw [← Real.exp_sum, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h1, ← (PiLp.volume_preserving_toLp (Fin n)).integral_comp
    (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurableEmbedding]
  rw [integral_fintype_prod_volume_eq_prod (fun i t => Real.exp (-(c i / 2) * t ^ 2))]
  exact Finset.prod_congr rfl fun i _ => integral_exp_neg_half_mul_sq (hc i)

/-- `∏ √(2π / cᵢ) = (2π) ^ (n / 2) / √(∏ cᵢ)` for positive `cᵢ`. -/
lemma prod_sqrt_two_pi_div {n : ℕ} (c : Fin n → ℝ) (hc : ∀ i, 0 < c i) :
    ∏ i, Real.sqrt (2 * π / c i) = (2 * π) ^ ((n : ℝ) / 2) / Real.sqrt (∏ i, c i) := by
  have h2π : (0 : ℝ) ≤ 2 * π := by positivity
  rw [Real.sqrt_prod _ fun i _ => (hc i).le]
  simp only [Real.sqrt_div h2π, Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  congr 1
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul h2π]
  ring_nf

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- In an orthonormal eigenbasis of a symmetric map the quadratic form is diagonal. -/
lemma inner_apply_repr_symm_eigenvectorBasis {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) {n : ℕ}
    (hn : Module.finrank ℝ E = n) (y : EuclideanSpace ℝ (Fin n)) :
    ⟪(hT.eigenvectorBasis hn).repr.symm y, T ((hT.eigenvectorBasis hn).repr.symm y)⟫ =
      ∑ i, hT.eigenvalues hn i * y i ^ 2 := by
  set b := hT.eigenvectorBasis hn
  set v := b.repr.symm y
  have hv : b.repr v = y := by simp [v]
  rw [← b.repr.inner_map_map v (T v), PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hT.eigenvectorBasis_apply_self_apply hn v i, hv, real_inner_eq_re_inner,
    RCLike.inner_apply, conj_trivial]
  simp only [RCLike.re_to_real, RCLike.ofReal_real_eq_id, id_eq]
  ring

/-- The eigenvalues of a positive definite symmetric map are positive. -/
lemma eigenvalues_pos {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) {n : ℕ}
    (hn : Module.finrank ℝ E = n) (hpos : ∀ x, x ≠ 0 → 0 < ⟪x, T x⟫) (i : Fin n) :
    0 < hT.eigenvalues hn i := by
  have h1 : ⟪hT.eigenvectorBasis hn i, hT.eigenvectorBasis hn i⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq, (hT.eigenvectorBasis hn).orthonormal.1 i]
    norm_num
  have h := hpos (hT.eigenvectorBasis hn i) ((hT.eigenvectorBasis hn).orthonormal.ne_zero i)
  rw [hT.apply_eigenvectorBasis hn i, inner_smul_right, h1] at h
  simpa using h

/-- A positive definite symmetric map has positive determinant (the product of its eigenvalues). -/
lemma det_pos_of_pos {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) (hpos : ∀ x, x ≠ 0 → 0 < ⟪x, T x⟫) :
    0 < LinearMap.det T := by
  rw [hT.det_eq_prod_eigenvalues rfl]
  exact Finset.prod_pos fun i _ => by simpa using eigenvalues_pos hT rfl hpos i

variable [MeasurableSpace E] [BorelSpace E]

/-- **Gaussian integral.** For a symmetric positive definite `T` on a finite-dimensional real
inner product space, `∫ exp (-(1/2) ⟪x, T x⟫) = (2π) ^ (dim E / 2) / √(det T)`. -/
theorem integral_exp_neg_half_inner {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric)
    (hpos : ∀ x, x ≠ 0 → 0 < ⟪x, T x⟫) :
    ∫ x : E, Real.exp (-(1 / 2) * ⟪x, T x⟫) =
      (2 * π) ^ ((Module.finrank ℝ E : ℝ) / 2) / Real.sqrt (LinearMap.det T) := by
  have hn : Module.finrank ℝ E = Module.finrank ℝ E := rfl
  rw [← (hT.eigenvectorBasis hn).measurePreserving_repr_symm.integral_comp
    (hT.eigenvectorBasis hn).repr.symm.toHomeomorph.measurableEmbedding]
  simp_rw [inner_apply_repr_symm_eigenvectorBasis hT hn]
  rw [integral_exp_neg_half_sum_mul_sq _ (eigenvalues_pos hT hn hpos),
    prod_sqrt_two_pi_div _ (eigenvalues_pos hT hn hpos), hT.det_eq_prod_eigenvalues hn]
  simp

/-- **Gaussian integral with a linear term** (completing the square). The linear term is written
as `⟪T w, x⟫`; every vector has this form by `exists_apply_eq_of_pos`. -/
theorem integral_exp_neg_half_inner_add {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric)
    (hpos : ∀ x, x ≠ 0 → 0 < ⟪x, T x⟫) (w : E) :
    ∫ x : E, Real.exp (-(1 / 2) * ⟪x, T x⟫ + ⟪T w, x⟫) =
      (2 * π) ^ ((Module.finrank ℝ E : ℝ) / 2) / Real.sqrt (LinearMap.det T) *
        Real.exp ((1 / 2) * ⟪w, T w⟫) := by
  rw [← integral_add_right_eq_self (fun x => Real.exp (-(1 / 2) * ⟪x, T x⟫ + ⟪T w, x⟫)) w]
  have key : ∀ y : E, -(1 / 2) * ⟪y + w, T (y + w)⟫ + ⟪T w, y + w⟫ =
      -(1 / 2) * ⟪y, T y⟫ + (1 / 2) * ⟪w, T w⟫ := by
    intro y
    have h1 : ⟪w, T y⟫ = ⟪T w, y⟫ := (hT w y).symm
    have h2 : ⟪y, T w⟫ = ⟪T w, y⟫ := real_inner_comm _ _
    have h3 : ⟪T w, w⟫ = ⟪w, T w⟫ := real_inner_comm _ _
    simp only [map_add, inner_add_left, inner_add_right]
    rw [h1, h2, h3]
    ring
  simp_rw [key, Real.exp_add]
  rw [integral_mul_const, integral_exp_neg_half_inner hT hpos]

omit [MeasurableSpace E] [BorelSpace E] in
/-- A positive definite map is surjective, so every linear term is of the form `⟪T w, x⟫`. -/
theorem exists_apply_eq_of_pos {T : E →ₗ[ℝ] E} (hpos : ∀ x, x ≠ 0 → 0 < ⟪x, T x⟫) (v : E) :
    ∃ w, T w = v := by
  have hinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    by_contra hne
    have := hpos x hne
    rw [hx, inner_zero_right] at this
    exact lt_irrefl _ this
  exact LinearMap.injective_iff_surjective.mp hinj v

end GaussianBlockSpin
