/-
`lem:norms` (i)–(ii) of BALABAN_CORE.tex: the inequalities between the normalised Hilbert–Schmidt
norm `|X|` and the operator norm `‖X‖` with respect to the Euclidean norm of `ℂ^N`.
-/
import CoreLean.Norms

open Matrix Complex
open scoped Matrix.Norms.L2Operator

namespace CoreLean

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ

/-- The squared Euclidean norm of the image of a vector. -/
lemma norm_sq_toLp (v : Fin N → ℂ) :
    ‖(EuclideanSpace.equiv (Fin N) ℂ).symm v‖ ^ 2 = ∑ i, Complex.normSq (v i) := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [Complex.sq_norm]

/-- The columns of `X`. -/
lemma mulVec_single_one' (X : Mat) (i : Fin N) :
    X *ᵥ Pi.single i 1 = fun j => X j i := by
  ext j
  simp

/-- `|X|² = N⁻¹ Σ_i ‖X e_i‖²`. -/
lemma hs2_eq_sum_cols (X : Mat) :
    hs2 X = (N : ℝ)⁻¹ * ∑ i, ‖(EuclideanSpace.equiv (Fin N) ℂ).symm (X *ᵥ Pi.single i 1)‖ ^ 2 := by
  rw [hs2_eq_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [norm_sq_toLp, mulVec_single_one']

/-- `|XY| ≤ ‖X‖ |Y|` (`lem:norms`(i)). -/
theorem hs_mul_le_opNorm_mul_hs (X Y : Mat) : hs (X * Y) ≤ ‖X‖ * hs Y := by
  have key : hs2 (X * Y) ≤ ‖X‖ ^ 2 * hs2 Y := by
    rw [hs2_eq_sum_cols, hs2_eq_sum_cols, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have h := Matrix.l2_opNorm_mulVec X ((EuclideanSpace.equiv (Fin N) ℂ).symm (Y *ᵥ Pi.single i 1))
    have hcol : X *ᵥ ((EuclideanSpace.equiv (Fin N) ℂ).symm (Y *ᵥ Pi.single i 1)) =
        (X * Y) *ᵥ Pi.single i 1 := by
      rw [← Matrix.mulVec_mulVec]; rfl
    rw [hcol] at h
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    rw [mul_pow] at h2
    have hN : (0 : ℝ) ≤ (N : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
    calc (N : ℝ)⁻¹ * ‖(EuclideanSpace.equiv (Fin N) ℂ).symm ((X * Y) *ᵥ Pi.single i 1)‖ ^ 2
        ≤ (N : ℝ)⁻¹ * (‖X‖ ^ 2 * ‖(EuclideanSpace.equiv (Fin N) ℂ).symm
            (Y *ᵥ Pi.single i 1)‖ ^ 2) := mul_le_mul_of_nonneg_left h2 hN
      _ = ‖X‖ ^ 2 * ((N : ℝ)⁻¹ * ‖(EuclideanSpace.equiv (Fin N) ℂ).symm
            (Y *ᵥ Pi.single i 1)‖ ^ 2) := by ring
  have := Real.sqrt_le_sqrt key
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)] at this
  exact this

lemma sum_normSq_nonneg (X : Mat) : 0 ≤ ∑ i, ∑ j, Complex.normSq (X j i) :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _

lemma hs_nonneg (X : Mat) : 0 ≤ hs X := Real.sqrt_nonneg _

/-- `|X| ≤ ‖X‖` (`lem:norms`(i)). -/
theorem hs_le_opNorm (hN : 0 < N) (X : Mat) : hs X ≤ ‖X‖ := by
  have h1 : hs (1 : Mat) = 1 := by
    unfold hs hs2 ntr
    have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    simp [Matrix.trace_one, hN']
  simpa [h1] using hs_mul_le_opNorm_mul_hs X 1

/-- `|X^*| = |X|` (`lem:norms`(i)). -/
theorem hs_conjTranspose (X : Mat) : hs Xᴴ = hs X := by
  unfold hs
  rw [hs2_eq_sum, hs2_eq_sum, Finset.sum_comm]
  simp [Matrix.conjTranspose_apply, Complex.normSq_conj]

/-- `|XY| ≤ |X| ‖Y‖` (`lem:norms`(i)). -/
theorem hs_mul_le_hs_mul_opNorm (X Y : Mat) : hs (X * Y) ≤ hs X * ‖Y‖ := by
  rw [← hs_conjTranspose, Matrix.conjTranspose_mul, mul_comm (hs X),
    ← Matrix.l2_opNorm_conjTranspose Y, ← hs_conjTranspose X]
  exact hs_mul_le_opNorm_mul_hs _ _

/-- `‖X‖ ≤ √N |X|` (`lem:norms`(i)): the operator norm is bounded by the Frobenius norm. -/
theorem opNorm_le_sqrt_mul_hs (X : Mat) : ‖X‖ ≤ Real.sqrt N * hs X := by
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (Real.sqrt_nonneg _) (hs_nonneg X))
    fun x => ?_
  -- ‖X x‖² ≤ (Σ_{ij} |X_ij|²) ‖x‖² = N |X|² ‖x‖²
  have hF : Real.sqrt N * hs X = Real.sqrt (∑ i, ∑ j, Complex.normSq (X j i)) := by
    unfold hs
    rw [hs2_eq_sum, ← Real.sqrt_mul (Nat.cast_nonneg _)]
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h; simp
    · congr 1; field_simp
  rw [hF]
  refine (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp ?_
  rw [mul_pow, Real.sq_sqrt (sum_normSq_nonneg X), EuclideanSpace.norm_sq_eq,
    EuclideanSpace.norm_sq_eq]
  have hx : ∀ i, ‖(((Matrix.toEuclideanLin (𝕜 := ℂ) (m := Fin N) (n := Fin N)).trans
      LinearMap.toContinuousLinearMap) X x) i‖ = ‖∑ j, X i j * x j‖ := by
    intro i
    simp [Matrix.mulVec, dotProduct]
  simp only [hx]
  calc ∑ i, ‖∑ j, X i j * x j‖ ^ 2 ≤ ∑ i, (∑ j, ‖X i j‖ ^ 2) * (∑ j, ‖x j‖ ^ 2) := by
        refine Finset.sum_le_sum fun i _ => ?_
        calc ‖∑ j, X i j * x j‖ ^ 2 ≤ (∑ j, ‖X i j‖ * ‖x j‖) ^ 2 := by
              gcongr
              exact (norm_sum_le _ _).trans (by simp)
          _ ≤ (∑ j, ‖X i j‖ ^ 2) * (∑ j, ‖x j‖ ^ 2) := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _ = (∑ i, ∑ j, Complex.normSq (X j i)) * ∑ j, ‖x j‖ ^ 2 := by
        rw [← Finset.sum_mul, Finset.sum_comm]
        simp [Complex.sq_norm]

/-- `|tr XY| ≤ |X| |Y|` (`lem:norms`(i)). -/
theorem norm_ntr_mul_le (X Y : Mat) : ‖ntr (X * Y)‖ ≤ hs X * hs Y := by
  -- `|Tr XY| ≤ Σ_{ij} |X_ij| |Y_ji| ≤ (Σ |X_ij|²)^{1/2} (Σ |Y_ji|²)^{1/2}`
  have hCS : ‖(X * Y).trace‖ ≤ Real.sqrt (∑ i, ∑ j, Complex.normSq (X j i)) *
      Real.sqrt (∑ i, ∑ j, Complex.normSq (Y j i)) := by
    have h1 : ‖(X * Y).trace‖ ≤ ∑ p : Fin N × Fin N, ‖X p.1 p.2‖ * ‖Y p.2 p.1‖ := by
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
      refine (norm_sum_le _ _).trans ?_
      rw [Fintype.sum_prod_type]
      exact Finset.sum_le_sum fun i _ => (norm_sum_le _ _).trans (by simp)
    have h2 := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin N × Fin N))
      (fun p => ‖X p.1 p.2‖) (fun p => ‖Y p.2 p.1‖)
    have hX : ∑ p : Fin N × Fin N, ‖X p.1 p.2‖ ^ 2 = ∑ i, ∑ j, Complex.normSq (X j i) := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]; simp [Complex.sq_norm]
    have hY : ∑ p : Fin N × Fin N, ‖Y p.2 p.1‖ ^ 2 = ∑ i, ∑ j, Complex.normSq (Y j i) := by
      rw [Fintype.sum_prod_type]; simp [Complex.sq_norm]
    rw [hX, hY] at h2
    exact h1.trans h2
  unfold hs
  rw [hs2_eq_sum, hs2_eq_sum, ntr, norm_mul, norm_inv, Complex.norm_natCast,
    Real.sqrt_mul (inv_nonneg.mpr (Nat.cast_nonneg _)),
    Real.sqrt_mul (inv_nonneg.mpr (Nat.cast_nonneg _))]
  set s := Real.sqrt (N : ℝ)⁻¹ with hs_def
  have hNN : s * s = (N : ℝ)⁻¹ := Real.mul_self_sqrt (inv_nonneg.mpr (Nat.cast_nonneg _))
  calc (N : ℝ)⁻¹ * ‖(X * Y).trace‖ ≤ (N : ℝ)⁻¹ * (Real.sqrt (∑ i, ∑ j, Complex.normSq (X j i)) *
        Real.sqrt (∑ i, ∑ j, Complex.normSq (Y j i))) :=
        mul_le_mul_of_nonneg_left hCS (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ = s * Real.sqrt (∑ i, ∑ j, Complex.normSq (X j i)) *
        (s * Real.sqrt (∑ i, ∑ j, Complex.normSq (Y j i))) := by rw [← hNN]; ring

/-- `‖XY‖ ≤ ‖X‖ ‖Y‖` (`lem:norms`(i)). -/
theorem opNorm_mul_le (X Y : Mat) : ‖X * Y‖ ≤ ‖X‖ * ‖Y‖ := Matrix.l2_opNorm_mul X Y

/-- `‖X^*‖ = ‖X‖` (`lem:norms`(i)). -/
theorem opNorm_conjTranspose (X : Mat) : ‖Xᴴ‖ = ‖X‖ := Matrix.l2_opNorm_conjTranspose X

/-- `‖UXV‖ = ‖X‖` for unitary `U`, `V` (`lem:norms`(ii)). -/
theorem opNorm_unitary_mul (U V X : Mat) (hU : U ∈ unitaryGroup (Fin N) ℂ)
    (hV : V ∈ unitaryGroup (Fin N) ℂ) : ‖U * X * V‖ = ‖X‖ := by
  rw [CStarRing.norm_mul_mem_unitary _ hV, CStarRing.norm_mem_unitary_mul _ hU]

end CoreLean
