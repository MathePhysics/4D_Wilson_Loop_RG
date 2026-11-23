/-
`lem:gaussian-splitting` of BALABAN_CORE.tex: completing the square in a Gaussian weight and the
integral over the inner variables.

The functions on `B = B^in ⊔ B^out` with values in `𝔤` are written in orthonormal coordinates of
the scalar product `⟨·,·⟩` of the lemma, indexed by `ι` (the inner coordinates) and `κ` (the
outer ones); `Γ` is a real symmetric matrix on `ι ⊕ κ` whose inner block is positive definite, and
`dA^in` is the Lebesgue measure of these coordinates. `C^in` is the inverse of the inner block,
extended by zero; `det(2π C^in)` is its determinant on the inner coordinates.
-/
import CoreLean.Vendor.GaussianIntegral

open Matrix MeasureTheory Complex
open scoped Real

namespace CoreLean

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- `C^in`: the inverse of the inner block of `Γ`, extended by zero. -/
noncomputable def innerInverse (Γ : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ :=
  fromBlocks (Γ.toBlocks₁₁)⁻¹ 0 0 0

/-- `lem:gaussian-splitting`, `eq:gaussian-splitting`: for `A = A^in + A^out` and
`a = C^in Γ A^out`,
`⟨A, ΓA⟩ = ⟨A^in + a, Γ(A^in + a)⟩ + ⟨A^out, (Γ - Γ C^in Γ) A^out⟩`. -/
theorem gaussian_splitting (Γ : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (hΓ : Γᵀ = Γ)
    (hP : (Γ.toBlocks₁₁).PosDef) (x : ι → ℝ) (y : κ → ℝ) :
    let A := Sum.elim x y
    let Ain := Sum.elim x (0 : κ → ℝ)
    let Aout := Sum.elim (0 : ι → ℝ) y
    let a := innerInverse Γ *ᵥ (Γ *ᵥ Aout)
    A ⬝ᵥ (Γ *ᵥ A) = (Ain + a) ⬝ᵥ (Γ *ᵥ (Ain + a)) +
      Aout ⬝ᵥ ((Γ - Γ * innerInverse Γ * Γ) *ᵥ Aout) := by
  intro A Ain Aout a
  set P := Γ.toBlocks₁₁
  set Q := Γ.toBlocks₁₂
  set R := Γ.toBlocks₂₂
  have hPs : Pᵀ = P := by
    ext i j
    have := congrFun (congrFun hΓ (Sum.inl i)) (Sum.inl j)
    simpa [P, Matrix.toBlocks₁₁] using this
  have hQ' : Γ.toBlocks₂₁ = Qᵀ := by
    ext i j
    have := congrFun (congrFun hΓ (Sum.inr i)) (Sum.inl j)
    simpa [Q, Matrix.toBlocks₁₂, Matrix.toBlocks₂₁] using this.symm
  have hΓb : Γ = fromBlocks P Q Qᵀ R := by rw [← hQ', fromBlocks_toBlocks]
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP.isUnit
  have hPPinv : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hdet
  obtain ⟨w, hw⟩ : ∃ w, w = P⁻¹ *ᵥ (Q *ᵥ y) := ⟨_, rfl⟩
  have hΓout : Γ *ᵥ Aout = Sum.elim (Q *ᵥ y) (R *ᵥ y) := by
    simp only [Aout, hΓb, fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr,
      Matrix.mulVec_zero, zero_add]
  have ha : a = Sum.elim w 0 := by
    simp only [a, hΓout, innerInverse, fromBlocks_mulVec, Sum.elim_comp_inl,
      Sum.elim_comp_inr, Matrix.zero_mulVec, add_zero, hw]
    rfl
  have hAin : Ain + a = Sum.elim (x + w) 0 := by
    rw [ha]; ext i; cases i <;> simp [Ain]
  -- the cross terms `y ⬝ᵥ Qᵀ v = v ⬝ᵥ Q y`
  have hcross : ∀ v : ι → ℝ, y ⬝ᵥ (Qᵀ *ᵥ v) = v ⬝ᵥ (Q *ᵥ y) := by
    intro v
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, dotProduct_comm]
  have hPw : P *ᵥ w = Q *ᵥ y := by rw [hw, Matrix.mulVec_mulVec, hPPinv, Matrix.one_mulVec]
  have hwPw : w ⬝ᵥ (P *ᵥ w) = w ⬝ᵥ (Q *ᵥ y) := by rw [hPw]
  have hxPw : x ⬝ᵥ (P *ᵥ w) = x ⬝ᵥ (Q *ᵥ y) := by rw [hPw]
  have hwPx : w ⬝ᵥ (P *ᵥ x) = x ⬝ᵥ (Q *ᵥ y) := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hPs, dotProduct_comm, hxPw]
  have hCΓ : Aout ⬝ᵥ ((Γ * innerInverse Γ * Γ) *ᵥ Aout) = w ⬝ᵥ (Q *ᵥ y) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    rw [show innerInverse Γ *ᵥ (Γ *ᵥ Aout) = a from rfl, ha]
    simp only [Aout, hΓb, fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr,
      Matrix.mulVec_zero, sumElim_dotProduct_sumElim, zero_dotProduct, zero_add,
      add_zero]
    exact hcross w
  have hLHS : A ⬝ᵥ (Γ *ᵥ A) = x ⬝ᵥ (P *ᵥ x) + 2 * (x ⬝ᵥ (Q *ᵥ y)) + y ⬝ᵥ (R *ᵥ y) := by
    simp only [A, hΓb, fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr,
      sumElim_dotProduct_sumElim, dotProduct_add, hcross]
    ring
  have hRHS1 : (Ain + a) ⬝ᵥ (Γ *ᵥ (Ain + a)) =
      x ⬝ᵥ (P *ᵥ x) + 2 * (x ⬝ᵥ (Q *ᵥ y)) + w ⬝ᵥ (Q *ᵥ y) := by
    rw [hAin]
    simp only [hΓb, fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr,
      sumElim_dotProduct_sumElim, Matrix.mulVec_zero, add_zero, zero_dotProduct,
      Matrix.mulVec_add, dotProduct_add, add_dotProduct, hwPw, hxPw, hwPx]
    ring
  have hRHS2 : Aout ⬝ᵥ (Γ *ᵥ Aout) = y ⬝ᵥ (R *ᵥ y) := by
    rw [hΓout]
    simp only [Aout, sumElim_dotProduct_sumElim, zero_dotProduct, zero_add]
  rw [Matrix.sub_mulVec, dotProduct_sub, hCΓ, hLHS, hRHS1, hRHS2]
  ring

/-- The quadratic form at a function supported in the inner coordinates is that of the inner
block. -/
lemma quad_inner (Γ : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (v : ι → ℝ) :
    Sum.elim v (0 : κ → ℝ) ⬝ᵥ (Γ *ᵥ Sum.elim v 0) = v ⬝ᵥ (Γ.toBlocks₁₁ *ᵥ v) := by
  conv_lhs => rw [← fromBlocks_toBlocks Γ]
  simp only [fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.mulVec_zero,
    add_zero, sumElim_dotProduct_sumElim, zero_dotProduct]

/-- The Gaussian integral of a positive definite form, `∫ e^{-½ ⟨φ, Pφ⟩} dφ = det(2πP⁻¹)^{1/2}`,
from `Balaban.integral_cexp_quadratic_form`. -/
lemma integral_exp_quadratic (P : Matrix ι ι ℝ) (hP : P.PosDef) :
    ∫ φ : ι → ℝ, Real.exp (-(1 / 2) * (φ ⬝ᵥ (P *ᵥ φ))) =
      Real.sqrt (((2 * π) • P⁻¹).det) := by
  have h := Balaban.integral_cexp_quadratic_form P hP 0
  simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero, mul_zero,
    Complex.exp_zero, mul_one] at h
  have hlhs : (fun φ : ι → ℝ => Complex.exp (-(1 / 2 : ℂ) * ((φ ⬝ᵥ P *ᵥ φ : ℝ) : ℂ))) =
      fun φ => ((Real.exp (-(1 / 2) * (φ ⬝ᵥ (P *ᵥ φ))) : ℝ) : ℂ) := by
    funext φ; push_cast; rfl
  rw [hlhs, integral_complex_ofReal] at h
  have h2π : (2 * π : ℂ) ^ ((Fintype.card ι : ℂ) / 2) =
      (((2 * π) ^ ((Fintype.card ι : ℝ) / 2) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow (by positivity)]; push_cast; rfl
  rw [h2π, ← Complex.ofReal_mul] at h
  rw [Complex.ofReal_injective h]
  have hdet : 0 < P.det := hP.det_pos
  rw [Matrix.det_smul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv',
    Real.sqrt_mul (by positivity), Real.sqrt_inv, mul_comm (Real.sqrt _)]
  congr 1
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  congr 1
  ring

/-- `lem:gaussian-splitting`, the integral over the inner variables:
`∫ exp(-½⟨A, ΓA⟩) dA^in = det(2π C^in)^{1/2} exp(-½⟨A^out, (Γ - ΓC^inΓ) A^out⟩)`. -/
theorem gaussian_splitting_integral (Γ : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (hΓ : Γᵀ = Γ)
    (hP : (Γ.toBlocks₁₁).PosDef) (y : κ → ℝ) :
    ∫ x : ι → ℝ, Real.exp (-(1 / 2) * (Sum.elim x y ⬝ᵥ (Γ *ᵥ Sum.elim x y))) =
      Real.sqrt (((2 * π) • (Γ.toBlocks₁₁)⁻¹).det) *
        Real.exp (-(1 / 2) * (Sum.elim (0 : ι → ℝ) y ⬝ᵥ
          ((Γ - Γ * innerInverse Γ * Γ) *ᵥ Sum.elim (0 : ι → ℝ) y))) := by
  set S := Sum.elim (0 : ι → ℝ) y ⬝ᵥ ((Γ - Γ * innerInverse Γ * Γ) *ᵥ Sum.elim (0 : ι → ℝ) y)
  -- `a = C^in Γ A^out` is supported in the inner coordinates: `a = (w, 0)`
  obtain ⟨w, hw⟩ : ∃ w : ι → ℝ, innerInverse Γ *ᵥ (Γ *ᵥ Sum.elim (0 : ι → ℝ) y) =
      Sum.elim w 0 := by
    refine ⟨fun i => (innerInverse Γ *ᵥ (Γ *ᵥ Sum.elim (0 : ι → ℝ) y)) (Sum.inl i), ?_⟩
    ext i
    cases i with
    | inl i => rfl
    | inr j => simp [innerInverse, Matrix.mulVec, dotProduct, Fintype.sum_sum_type]
  have hsplit : ∀ x : ι → ℝ, Sum.elim x y ⬝ᵥ (Γ *ᵥ Sum.elim x y) =
      (x + w) ⬝ᵥ (Γ.toBlocks₁₁ *ᵥ (x + w)) + S := by
    intro x
    have h := gaussian_splitting Γ hΓ hP x y
    simp only at h
    rw [h, hw]
    have : Sum.elim x (0 : κ → ℝ) + Sum.elim w 0 = Sum.elim (x + w) 0 := by
      ext i; cases i <;> simp
    rw [this, quad_inner]
  simp_rw [hsplit, mul_add, Real.exp_add]
  rw [integral_mul_const]
  rw [MeasureTheory.integral_add_right_eq_self
    (fun v : ι → ℝ => Real.exp (-(1 / 2) * (v ⬝ᵥ (Γ.toBlocks₁₁ *ᵥ v)))) w]
  rw [integral_exp_quadratic _ hP]

end CoreLean
