/-
Pilot formalisation of parts of `lem:norms` of BALABAN_CORE.tex (Section 1.1,
Definition `def:group`): the normalised trace `tr X = N⁻¹ Tr X`, the normalised
Hilbert–Schmidt norm `|X| = (tr X^*X)^{1/2}`, and the identities and inequalities of
`lem:norms` (i)–(ii) which involve only these.
-/
import Mathlib

open Matrix Complex

namespace CoreLean

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ

/-- The normalised trace `tr X = N⁻¹ Tr X` (`def:group`(ii)). -/
noncomputable def ntr (X : Mat) : ℂ := (N : ℂ)⁻¹ * X.trace

/-- The square of the Hilbert–Schmidt norm, `|X|² = Re tr X^*X` (`def:group`(ii)). -/
noncomputable def hs2 (X : Mat) : ℝ := (ntr (Xᴴ * X)).re

/-- The Hilbert–Schmidt norm `|X|`. -/
noncomputable def hs (X : Mat) : ℝ := Real.sqrt (hs2 X)

/-- `Tr X^*X` is the sum of the squared moduli of the entries. -/
theorem trace_conjTranspose_mul_self (X : Mat) :
    (Xᴴ * X).trace = ∑ i, ∑ j, ((Complex.normSq (X j i) : ℝ) : ℂ) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.normSq_eq_conj_mul_self]
  simp [mul_comm]

theorem hs2_eq_sum (X : Mat) :
    hs2 X = (N : ℝ)⁻¹ * ∑ i, ∑ j, Complex.normSq (X j i) := by
  unfold hs2 ntr
  rw [trace_conjTranspose_mul_self]
  have : ((N : ℂ)⁻¹ * ∑ i, ∑ j, ((Complex.normSq (X j i) : ℝ) : ℂ)) =
      (((N : ℝ)⁻¹ * ∑ i, ∑ j, Complex.normSq (X j i) : ℝ) : ℂ) := by
    push_cast; ring
  rw [this, Complex.ofReal_re]

theorem hs2_nonneg (X : Mat) : 0 ≤ hs2 X := by
  rw [hs2_eq_sum]
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _)

theorem hs_sq (X : Mat) : hs X ^ 2 = hs2 X := Real.sq_sqrt (hs2_nonneg X)

/-- `eq:plaquette-norm`: for a unitary `U`, `1 - Re tr U = ½ |U - 1|²` (`lem:norms`(ii)). -/
theorem plaquette_norm (hN : 0 < N) (U : Mat) (hU : U ∈ unitaryGroup (Fin N) ℂ) :
    1 - (ntr U).re = (1 / 2) * hs (U - 1) ^ 2 := by
  have hUU : Uᴴ * U = 1 := by
    have := hU.1
    simpa [Matrix.star_eq_conjTranspose] using this
  have hexp : (U - 1)ᴴ * (U - 1) = 2 • (1 : Mat) - Uᴴ - U := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.mul_sub, hUU, Matrix.mul_one, Matrix.one_mul, Matrix.one_mul, two_smul]
    abel
  have htr : ((U - 1)ᴴ * (U - 1)).trace = 2 * N - star U.trace - U.trace := by
    rw [hexp, Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one,
      Matrix.trace_conjTranspose]
    simp [Fintype.card_fin, two_mul]
  simp only [hs_sq, hs2, ntr]
  rw [htr]
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  simp only [Complex.mul_re, Complex.inv_re, Complex.inv_im, Complex.natCast_re,
    Complex.natCast_im, Complex.sub_re, Complex.sub_im, Complex.mul_im, Complex.star_def,
    Complex.conj_re, Complex.conj_im, Complex.re_ofNat, Complex.im_ofNat, Complex.normSq_natCast]
  field_simp
  ring

/-- `|tr X| ≤ |X|` (`lem:norms`(i)), by the Cauchy–Schwarz inequality for the diagonal. -/
theorem norm_ntr_le_hs (hN : 0 < N) (X : Mat) : ‖ntr X‖ ≤ hs X := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  -- |Tr X|² ≤ N Σ_i |X_ii|² ≤ N Σ_{i,j} |X_ji|²
  have hdiag : ‖X.trace‖ ^ 2 ≤ N * ∑ i, Complex.normSq (X i i) := by
    have h1 : ‖X.trace‖ ≤ ∑ i, ‖X i i‖ := by
      simpa [Matrix.trace, Matrix.diag] using norm_sum_le (Finset.univ) (fun i => X i i)
    have h2 : (∑ i, ‖X i i‖) ^ 2 ≤ (Finset.univ.card : ℝ) * ∑ i, ‖X i i‖ ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    have h3 : ∑ i, ‖X i i‖ ^ 2 = ∑ i, Complex.normSq (X i i) := by
      simp [Complex.sq_norm]
    calc ‖X.trace‖ ^ 2 ≤ (∑ i, ‖X i i‖) ^ 2 := by gcongr
      _ ≤ (Finset.univ.card : ℝ) * ∑ i, ‖X i i‖ ^ 2 := h2
      _ = N * ∑ i, Complex.normSq (X i i) := by rw [h3]; simp
  have hoff : ∑ i, Complex.normSq (X i i) ≤ ∑ i, ∑ j, Complex.normSq (X j i) := by
    refine Finset.sum_le_sum fun i _ => ?_
    exact Finset.single_le_sum (f := fun j => Complex.normSq (X j i))
      (fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
  have hsq : ‖ntr X‖ ^ 2 ≤ hs X ^ 2 := by
    rw [hs_sq, hs2_eq_sum, ntr, norm_mul, norm_inv, Complex.norm_natCast, mul_pow]
    have : ((N : ℝ)⁻¹) ^ 2 * ‖X.trace‖ ^ 2 ≤ ((N : ℝ)⁻¹) ^ 2 * (N * ∑ i, ∑ j,
        Complex.normSq (X j i)) := by
      gcongr
      exact hdiag.trans (by gcongr)
    calc ((N : ℝ)⁻¹) ^ 2 * ‖X.trace‖ ^ 2 ≤ _ := this
      _ = (N : ℝ)⁻¹ * ∑ i, ∑ j, Complex.normSq (X j i) := by
        field_simp
  exact (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp hsq

/-- `|UXV| = |X|` for unitary `U`, `V` (`lem:norms`(ii)), by the cyclicity of the trace. -/
theorem hs_unitary_mul (U V X : Mat) (hU : U ∈ unitaryGroup (Fin N) ℂ)
    (hV : V ∈ unitaryGroup (Fin N) ℂ) : hs (U * X * V) = hs X := by
  have hUU : Uᴴ * U = 1 := by simpa [Matrix.star_eq_conjTranspose] using hU.1
  have hVV : V * Vᴴ = 1 := by simpa [Matrix.star_eq_conjTranspose] using hV.2
  have : (U * X * V)ᴴ * (U * X * V) = Vᴴ * (Xᴴ * X) * V := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uᴴ U, hUU, Matrix.one_mul]
  unfold hs hs2 ntr
  rw [this, Matrix.trace_mul_cycle, Matrix.mul_assoc, ← Matrix.mul_assoc V, hVV, Matrix.one_mul]

end CoreLean
