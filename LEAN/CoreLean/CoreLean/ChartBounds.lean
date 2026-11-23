/-
`lem:chart`(iii) of BALABAN_CORE.tex (`b1ff7d2601a1`): for a Hermitean matrix `X` with `‖X‖ ≤ π`,
`‖e^{iX} - 1‖ ≤ ‖X‖ ≤ (π/2)‖e^{iX} - 1‖` and `|e^{iX} - 1| ≤ |X| ≤ (π/2)|e^{iX} - 1|`.

The core's proof: with the eigenvalues `λ_k ∈ [-π, π]` of `X`, the eigenvalues of `e^{iX} - 1` are
`e^{iλ_k} - 1`, of the absolute values `2|sin(λ_k/2)|`, and `(2/π)|λ| ≤ 2|sin(λ/2)| ≤ |λ|`. Here:
Mathlib's spectral theorem `X = UDU^*` with a unitary `U` and the real diagonal `D`; then
`e^{iX} - 1 = U(e^{iD} - 1)U^*` (`exp_units_conj`, `exp_diagonal`); the operator norm of a diagonal matrix
is the supremum of its entries (`l2_opNorm_diagonal`), its Hilbert–Schmidt norm the mean square
(`hs2_eq_sum`), and both norms are invariant under the unitary conjugation (`opNorm_unitary_mul`,
`hs_unitary_mul`). The scalar bounds are `norm_exp_I_mul_ofReal_sub_one` and Jordan's inequality
`Real.mul_le_sin`.
-/
import CoreLean.OpNorm
import CoreLean.Norms

open NormedSpace Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean
namespace ChartBounds

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ

/-- The scalar bounds: `‖e^{iλ} - 1‖ ≤ |λ| ≤ (π/2)‖e^{iλ} - 1‖` for `|λ| ≤ π`. -/
lemma scalar_bounds (l : ℝ) (hl : |l| ≤ Real.pi) :
    ‖Complex.exp (Complex.I * l) - 1‖ ≤ |l| ∧
      |l| ≤ Real.pi / 2 * ‖Complex.exp (Complex.I * l) - 1‖ := by
  refine ⟨by simpa using Real.norm_exp_I_mul_ofReal_sub_one_le (x := l), ?_⟩
  rw [Complex.norm_exp_I_mul_ofReal_sub_one, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_two]
  have hpi := Real.pi_pos
  have h0 : 0 ≤ |l / 2| := abs_nonneg _
  have h1 : |l / 2| ≤ Real.pi / 2 := by rw [abs_div, abs_two]; linarith
  have hj := Real.mul_le_sin h0 h1
  have hle := abs_le.mp h1
  have hs : Real.sin |l / 2| = |Real.sin (l / 2)| := by
    rcases le_total 0 (l / 2) with h | h
    · rw [abs_of_nonneg h,
        abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi h (by linarith [hle.2]))]
    · have h' : 0 ≤ Real.sin (-(l / 2)) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [hle.1])
      rw [Real.sin_neg] at h'
      rw [abs_of_nonpos h, Real.sin_neg, abs_of_nonpos (by linarith)]
  rw [hs] at hj
  have hl2 : |l| = 2 * |l / 2| := by rw [abs_div, abs_two]; ring
  rw [hl2]
  have : 2 / Real.pi * |l / 2| * Real.pi = 2 * |l / 2| := by field_simp
  nlinarith

/-- A pointwise bound of diagonal entries gives the bound of the operator norms. -/
lemma opNorm_diagonal_le (v w : Fin N → ℂ) (c : ℝ) (hc : 0 ≤ c) (h : ∀ k, ‖v k‖ ≤ c * ‖w k‖) :
    ‖(diagonal v : Mat)‖ ≤ c * ‖(diagonal w : Mat)‖ := by
  rw [l2_opNorm_diagonal, l2_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun k => (h k).trans ?_
  exact mul_le_mul_of_nonneg_left (norm_le_pi_norm w k) hc

lemma hs2_diagonal (v : Fin N → ℂ) : hs2 (diagonal v : Mat) = (N : ℝ)⁻¹ * ∑ k, ‖v k‖ ^ 2 := by
  rw [hs2_eq_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · simp [Complex.sq_norm]
  · intro j _ hj; simp [diagonal_apply_ne _ hj]
  · simp

/-- A pointwise bound of diagonal entries gives the bound of the Hilbert–Schmidt norms. -/
lemma hs_diagonal_le (v w : Fin N → ℂ) (c : ℝ) (hc : 0 ≤ c) (h : ∀ k, ‖v k‖ ≤ c * ‖w k‖) :
    hs (diagonal v : Mat) ≤ c * hs (diagonal w : Mat) := by
  unfold hs
  conv_rhs => rw [← Real.sqrt_sq hc]
  rw [← Real.sqrt_mul (sq_nonneg c)]
  apply Real.sqrt_le_sqrt
  rw [hs2_diagonal, hs2_diagonal]
  have hsum : ∑ k, ‖v k‖ ^ 2 ≤ c ^ 2 * ∑ k, ‖w k‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun k _ => by
      have := h k; have := norm_nonneg (v k); nlinarith
  have hN : 0 ≤ (N : ℝ)⁻¹ := by positivity
  calc (N : ℝ)⁻¹ * ∑ k, ‖v k‖ ^ 2 ≤ (N : ℝ)⁻¹ * (c ^ 2 * ∑ k, ‖w k‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hsum hN
    _ = c ^ 2 * ((N : ℝ)⁻¹ * ∑ k, ‖w k‖ ^ 2) := by ring

/-- `lem:chart`(iii). -/
theorem chart_iii {X : Mat} (hX : X.IsHermitian) (hXn : ‖X‖ ≤ Real.pi) :
    ‖exp (Complex.I • X) - 1‖ ≤ ‖X‖ ∧ ‖X‖ ≤ Real.pi / 2 * ‖exp (Complex.I • X) - 1‖ ∧
      hs (exp (Complex.I • X) - 1) ≤ hs X ∧ hs X ≤ Real.pi / 2 * hs (exp (Complex.I • X) - 1) := by
  set U : Mat := (hX.eigenvectorUnitary : Mat)
  have hU : U ∈ unitaryGroup (Fin N) ℂ := hX.eigenvectorUnitary.2
  have hUs : star U ∈ unitaryGroup (Fin N) ℂ := Unitary.star_mem hU
  set l : Fin N → ℝ := hX.eigenvalues
  set d : Fin N → ℂ := fun k => (l k : ℂ)
  have hspec : X = U * diagonal d * star U := by
    have := hX.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  -- the unit `U`
  have h1 : U * star U = 1 := (Matrix.mem_unitaryGroup_iff).1 hU
  have h2 : star U * U = 1 := (Matrix.mem_unitaryGroup_iff').1 hU
  set W : Mat ˣ := ⟨U, star U, h1, h2⟩
  have hexp : exp (Complex.I • X) - 1 =
      U * diagonal (fun k => Complex.exp (Complex.I * l k) - 1) * star U := by
    have e1 : Complex.I • X = (W : Mat) * diagonal (Complex.I • d) * ((W⁻¹ : Mat ˣ) : Mat) := by
      rw [hspec]; simp only [W, Units.inv_mk, diagonal_smul, Matrix.mul_smul, Matrix.smul_mul]
    rw [e1, Matrix.exp_units_conj, Matrix.exp_diagonal]
    have e2 : (exp (Complex.I • d) : Fin N → ℂ) = fun k => Complex.exp (Complex.I * l k) := by
      funext k
      simp only [Pi.exp_def]
      rw [← Complex.exp_eq_exp_ℂ]
      simp [d]
    rw [e2]
    have e3 : diagonal (fun k => Complex.exp (Complex.I * l k) - 1) =
        diagonal (fun k => Complex.exp (Complex.I * l k)) - (1 : Mat) := by
      rw [← diagonal_one, diagonal_sub]
    rw [e3]
    simp only [W, Units.inv_mk, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h1]
  have hnormX : ‖X‖ = ‖(diagonal d : Mat)‖ := by
    rw [hspec, opNorm_unitary_mul _ _ _ hU hUs]
  have hhsX : hs X = hs (diagonal d : Mat) := by
    rw [hspec, hs_unitary_mul _ _ _ hU hUs]
  rw [hexp, opNorm_unitary_mul _ _ _ hU hUs, hs_unitary_mul _ _ _ hU hUs, hnormX, hhsX]
  have hlk : ∀ k, |l k| ≤ Real.pi := fun k => by
    have : ‖d k‖ ≤ ‖d‖ := norm_le_pi_norm d k
    rw [← l2_opNorm_diagonal (𝕜 := ℂ), ← hnormX] at this
    simpa [d] using this.trans hXn
  have hb := fun k => scalar_bounds (l k) (hlk k)
  have hdk : ∀ k, ‖d k‖ = |l k| := fun k => by simp [d]
  have up : ∀ k, ‖Complex.exp (Complex.I * l k) - 1‖ ≤ 1 * ‖d k‖ := fun k => by
    rw [one_mul, hdk]; exact (hb k).1
  have down : ∀ k, ‖d k‖ ≤ Real.pi / 2 * ‖Complex.exp (Complex.I * l k) - 1‖ := fun k => by
    rw [hdk]; exact (hb k).2
  have hpi : 0 ≤ Real.pi / 2 := by positivity
  refine ⟨?_, opNorm_diagonal_le _ _ _ hpi down, ?_, hs_diagonal_le _ _ _ hpi down⟩
  · simpa using opNorm_diagonal_le _ _ 1 zero_le_one up
  · simpa using hs_diagonal_le _ _ 1 zero_le_one up

end ChartBounds
end CoreLean

end
