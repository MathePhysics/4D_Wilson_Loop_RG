/-
The algebra of `lem:complex-gaussian` of BALABAN_CORE.tex (`9c56d4590aff`). The Euclidean space `E` is `ι → ℝ` with the
inner product `⟨x, y⟩ = Σ_ix_iy_i` (coordinates in an orthonormal basis), its complexification `ι → ℂ` with the bilinear
extension, and a linear map of `E^c` is a matrix `Q ∈ ℂ^{ι×ι}`; `Q` is symmetric if `Qᵀ = Q`, and its real part `Re Q`
(entrywise) is the map with `⟨u, (Re Q)u⟩ = Re⟨u, Qu⟩` for real `u`. The set `𝒬` of the symmetric `Q` with `Re Q`
positive definite. For `Q ∈ 𝒬` there is a real invertible `P` with `PᵀQP = diag(1 + id_k)`, `d_k ∈ ℝ` (simultaneous
diagonalisation of `Re Q` and `Im Q`); hence `Q` is invertible.
-/
import Mathlib

open Matrix Complex

noncomputable section

namespace CoreLean
namespace ComplexGauss

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The real part of a complex matrix, entrywise. -/
def reM (Q : Matrix ι ι ℂ) : Matrix ι ι ℝ := Q.map Complex.re

/-- The imaginary part of a complex matrix, entrywise. -/
def imM (Q : Matrix ι ι ℂ) : Matrix ι ι ℝ := Q.map Complex.im

/-- A real matrix as a complex one. -/
abbrev cM (P : Matrix ι ι ℝ) : Matrix ι ι ℂ := P.map (Complex.ofRealHom : ℝ →+* ℂ)

/-- A real vector as a complex one. -/
abbrev cV (x : ι → ℝ) : ι → ℂ := fun i => (x i : ℂ)

/-- `𝒬`: the symmetric complex matrices whose real part is positive definite. -/
def QSet : Set (Matrix ι ι ℂ) := {Q | Qᵀ = Q ∧ (reM Q).PosDef}

lemma re_add_im_M (Q : Matrix ι ι ℂ) : Q = cM (reM Q) + Complex.I • cM (imM Q) := by
  ext i j
  apply Complex.ext <;> simp [reM, imM, cM]

lemma reM_transpose (Q : Matrix ι ι ℂ) : reM Qᵀ = (reM Q)ᵀ := by ext; rfl

lemma imM_transpose (Q : Matrix ι ι ℂ) : imM Qᵀ = (imM Q)ᵀ := by ext; rfl

lemma isHermitian_of_symm {S : Matrix ι ι ℝ} (h : Sᵀ = S) : S.IsHermitian := by
  unfold Matrix.IsHermitian; rw [conjTranspose_eq_transpose_of_trivial]; exact h

/-- Orthogonal diagonalisation of a real symmetric matrix. -/
lemma orth_diag (A : Matrix ι ι ℝ) (hA : A.IsHermitian) :
    ∃ U : Matrix ι ι ℝ, Uᵀ * U = 1 ∧ Uᵀ * A * U = diagonal hA.eigenvalues := by
  refine ⟨(hA.eigenvectorUnitary : Matrix ι ι ℝ), ?_, ?_⟩
  · have := Unitary.coe_star_mul_self hA.eigenvectorUnitary
    rwa [Matrix.star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at this
  · have := hA.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_star_apply, Matrix.star_eq_conjTranspose,
      conjTranspose_eq_transpose_of_trivial] at this
    rw [this]
    congr 1

/-- **Simultaneous diagonalisation**: for `R` positive definite and `S` symmetric there is a real `P` with
`PᵀRP = 1` and `PᵀSP` diagonal. -/
lemma simul_diag (R S : Matrix ι ι ℝ) (hR : R.PosDef) (hS : S.IsHermitian) :
    ∃ P : Matrix ι ι ℝ, ∃ d : ι → ℝ, P.det ≠ 0 ∧ Pᵀ * R * P = 1 ∧ Pᵀ * S * P = diagonal d := by
  obtain ⟨U, hUU, hUR⟩ := orth_diag R hR.1
  set lam := hR.1.eigenvalues with hlam
  have hpos : ∀ i, 0 < lam i := hR.eigenvalues_pos
  set D : Matrix ι ι ℝ := diagonal fun i => (Real.sqrt (lam i))⁻¹ with hD
  set P1 := U * D with hP1
  have h1 : P1ᵀ * R * P1 = 1 := by
    rw [hP1, transpose_mul, hD, diagonal_transpose]
    rw [show diagonal (fun i => (Real.sqrt (lam i))⁻¹) * Uᵀ * R * (U * diagonal fun i => (Real.sqrt (lam i))⁻¹) =
      diagonal (fun i => (Real.sqrt (lam i))⁻¹) * (Uᵀ * R * U) * diagonal fun i => (Real.sqrt (lam i))⁻¹ by
        simp only [Matrix.mul_assoc]]
    rw [hUR, diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    have hx := hpos i
    have hs0 : Real.sqrt (lam i) ≠ 0 := (Real.sqrt_pos.2 hx).ne'
    have hs := Real.mul_self_sqrt hx.le
    try simp only [Pi.one_apply]
    field_simp
    nlinarith [hs, Real.sq_sqrt hx.le]
  set S1 := P1ᵀ * S * P1 with hS1
  have hgen : ∀ A : Matrix ι ι ℝ, (Aᵀ * S * A)ᵀ = Aᵀ * S * A := by
    intro A
    have hST : Sᵀ = S := by
      have := hS; unfold Matrix.IsHermitian at this; rwa [conjTranspose_eq_transpose_of_trivial] at this
    rw [transpose_mul, transpose_mul, transpose_transpose, hST, Matrix.mul_assoc]
  have hS1h : S1.IsHermitian := isHermitian_of_symm (hgen P1)
  obtain ⟨V, hVV, hVS⟩ := orth_diag S1 hS1h
  refine ⟨P1 * V, hS1h.eigenvalues, ?_, ?_, ?_⟩
  · intro h0
    have h2 : (P1 * V)ᵀ * R * (P1 * V) = 1 := by
      rw [transpose_mul, show Vᵀ * P1ᵀ * R * (P1 * V) = Vᵀ * (P1ᵀ * R * P1) * V by simp only [Matrix.mul_assoc],
        h1, Matrix.mul_one, hVV]
    have := congrArg Matrix.det h2
    rw [det_mul, det_mul, det_transpose, h0, zero_mul, zero_mul, det_one] at this
    exact zero_ne_one this
  · rw [transpose_mul, show Vᵀ * P1ᵀ * R * (P1 * V) = Vᵀ * (P1ᵀ * R * P1) * V by simp only [Matrix.mul_assoc],
      h1, Matrix.mul_one, hVV]
  · rw [transpose_mul, show Vᵀ * P1ᵀ * S * (P1 * V) = Vᵀ * (P1ᵀ * S * P1) * V by simp only [Matrix.mul_assoc]]
    exact hVS

/-- **The normal form**: for `Q ∈ 𝒬` there are a real `P`, `det P ≠ 0`, and `d ∈ ℝ^ι` with `PᵀQP = diag(1 + id)`. -/
theorem normal_form {Q : Matrix ι ι ℂ} (hQ : Q ∈ QSet) :
    ∃ P : Matrix ι ι ℝ, ∃ d : ι → ℝ, P.det ≠ 0 ∧
      (cM P)ᵀ * Q * cM P = diagonal fun i => 1 + (d i : ℂ) * Complex.I := by
  have hS : (imM Q).IsHermitian := isHermitian_of_symm (by rw [← imM_transpose, hQ.1])
  obtain ⟨P, d, hdet, h1, h2⟩ := simul_diag (reM Q) (imM Q) hQ.2 hS
  refine ⟨P, d, hdet, ?_⟩
  have hmap : ∀ A B : Matrix ι ι ℝ, cM (A * B) = cM A * cM B := fun A B => Matrix.map_mul
  have hT : (cM P)ᵀ = cM Pᵀ := Matrix.transpose_map.symm
  conv_lhs => rw [re_add_im_M Q]
  rw [hT, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, ← hmap, ← hmap, ← hmap, ← hmap, h1, h2]
  ext i j
  by_cases hij : i = j
  · subst hij; simp [cM, mul_comm]
  · simp [cM, hij]

/-- `det P ≠ 0` for a real `P` as a complex matrix. -/
lemma det_cM (P : Matrix ι ι ℝ) : (cM P).det = (P.det : ℂ) := (RingHom.map_det _ _).symm

/-- **`Q` is invertible**: `det Q ≠ 0` for `Q ∈ 𝒬`. -/
theorem det_ne_zero {Q : Matrix ι ι ℂ} (hQ : Q ∈ QSet) : Q.det ≠ 0 := by
  obtain ⟨P, d, hdet, hPQ⟩ := normal_form hQ
  have h := congrArg Matrix.det hPQ
  rw [det_mul, det_mul, det_transpose, det_cM, det_diagonal] at h
  intro h0
  rw [h0, mul_zero, zero_mul] at h
  refine (Finset.prod_ne_zero_iff.2 fun i _ => ?_) h.symm
  intro h1
  have := congrArg Complex.re h1
  simp at this

end ComplexGauss
end CoreLean

end
