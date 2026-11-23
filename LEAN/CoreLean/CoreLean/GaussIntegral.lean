/-
The Gaussian integral of `lem:complex-gaussian`(i) of BALABAN_CORE.tex (`9c56d4590aff`): for `Q ∈ 𝒬` and `v ∈ E^c`,
`Z(Q, v) = ∫e^{-½⟨A, QA⟩ - ⟨A, v⟩}dA = Z(Q, 0)e^{½⟨v, Q⁻¹v⟩}`, `Z(Q, 0) ≠ 0`, and the root
`det(Q/2π)^{1/2} := Z(Q, 0)⁻¹` satisfies `(det(Q/2π)^{1/2})² = det(Q/2π)` and is positive at the real `Q`. Proof: with
`PᵀQP = diag(1 + id_k)` (`normal_form`) the substitution `A = PB` turns the integral into a product of one-dimensional
Gaussian integrals (`integral_cexp_neg_sum_mul_add`).
-/
import CoreLean.GaussAlgebra

open Matrix Complex MeasureTheory Real

noncomputable section

namespace CoreLean
namespace ComplexGauss

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `⟨A, QA⟩` for a real `A`. -/
def qf (Q : Matrix ι ι ℂ) (x : ι → ℝ) : ℂ := cV x ⬝ᵥ (Q *ᵥ cV x)

/-- `Z(Q, v) = ∫e^{-½⟨A, QA⟩ - ⟨A, v⟩}dA`. -/
def Zv (Q : Matrix ι ι ℂ) (v : ι → ℂ) : ℂ := ∫ x : ι → ℝ, cexp (-(1 / 2) * qf Q x - cV x ⬝ᵥ v)

/-- The root `det(Q/2π)^{1/2} := Z(Q, 0)⁻¹`. -/
def root (Q : Matrix ι ι ℂ) : ℂ := (Zv Q 0)⁻¹

lemma cV_mulVec (P : Matrix ι ι ℝ) (y : ι → ℝ) : cV (P *ᵥ y) = cM P *ᵥ cV y := by
  funext i
  simp [cV, cM, mulVec, dotProduct]

lemma mulVec_dot (A : Matrix ι ι ℂ) (u w : ι → ℂ) : (A *ᵥ u) ⬝ᵥ w = u ⬝ᵥ (Aᵀ *ᵥ w) := by
  rw [dotProduct_mulVec, vecMul_transpose]

lemma dot_diagonal (b u : ι → ℂ) : u ⬝ᵥ (diagonal b *ᵥ u) = ∑ i, b i * u i ^ 2 := by
  simp only [mulVec_diagonal, dotProduct]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **The linear substitution**: `∫f(PB)dB = |det P|⁻¹∫f(A)dA`. -/
lemma integral_comp_matrix (P : Matrix ι ι ℝ) (hP : P.det ≠ 0) (f : (ι → ℝ) → ℂ) :
    ∫ y, f (P *ᵥ y) = |P.det|⁻¹ • ∫ x, f x := by
  have hu : IsUnit P := (Matrix.isUnit_iff_isUnit_det P).2 (isUnit_iff_ne_zero.2 hP)
  letI : Invertible P := hu.invertible
  set e : (ι → ℝ) ≃L[ℝ] (ι → ℝ) := (Matrix.toLinearEquiv' P inferInstance).toContinuousLinearEquiv with he
  have hmap : Measure.map e.toHomeomorph.toMeasurableEquiv volume = ENNReal.ofReal |P.det⁻¹| • volume := by
    have h := Real.map_matrix_volume_pi_eq_smul_volume_pi hP
    rw [abs_inv] at h ⊢
    convert h using 2
    funext y; rfl
  have h1 := integral_map_equiv e.toHomeomorph.toMeasurableEquiv f (μ := volume)
  rw [hmap, integral_smul_measure] at h1
  have h2 : (fun y => f (e.toHomeomorph.toMeasurableEquiv y)) = fun y => f (P *ᵥ y) := by
    funext y; rfl
  rw [h2] at h1
  rw [← h1, ENNReal.toReal_ofReal (abs_nonneg _), abs_inv]

/-- The inverse in the normal form: `Q⁻¹ = P diag(1 + id)⁻¹ Pᵀ`. -/
lemma inv_normal {Q : Matrix ι ι ℂ} {P : Matrix ι ι ℝ} {d : ι → ℝ} (hdet : P.det ≠ 0)
    (hPQ : (cM P)ᵀ * Q * cM P = diagonal fun i => 1 + (d i : ℂ) * Complex.I) :
    Q⁻¹ = cM P * diagonal (fun i => (1 + (d i : ℂ) * Complex.I)⁻¹) * (cM P)ᵀ := by
  have hne : ∀ i, (1 + (d i : ℂ) * Complex.I) ≠ 0 := fun i h => by
    have := congrArg Complex.re h; simp at this
  have hdetc : IsUnit (cM P)ᵀ.det := by
    rw [det_transpose, det_cM]; exact isUnit_iff_ne_zero.2 (by exact_mod_cast hdet)
  apply Matrix.inv_eq_right_inv
  have hQP : Q * cM P = ((cM P)ᵀ)⁻¹ * diagonal fun i => 1 + (d i : ℂ) * Complex.I := by
    rw [← hPQ, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdetc, Matrix.one_mul]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hQP]
  rw [show (cM P)ᵀ⁻¹ * (diagonal fun i => 1 + (d i : ℂ) * Complex.I) *
      (diagonal fun i => (1 + (d i : ℂ) * Complex.I)⁻¹) * (cM P)ᵀ =
      (cM P)ᵀ⁻¹ * ((diagonal fun i => 1 + (d i : ℂ) * Complex.I) *
      (diagonal fun i => (1 + (d i : ℂ) * Complex.I)⁻¹)) * (cM P)ᵀ by simp only [Matrix.mul_assoc]]
  rw [diagonal_mul_diagonal]
  rw [show (fun i => (1 + (d i : ℂ) * Complex.I) * (1 + (d i : ℂ) * Complex.I)⁻¹) = fun _ => (1 : ℂ) from
    funext fun i => mul_inv_cancel₀ (hne i), diagonal_one, Matrix.mul_one, Matrix.nonsing_inv_mul _ hdetc]

/-- **The Gaussian integral in the normal form**. -/
theorem Zv_normal {Q : Matrix ι ι ℂ} {P : Matrix ι ι ℝ} {d : ι → ℝ} (hdet : P.det ≠ 0)
    (hPQ : (cM P)ᵀ * Q * cM P = diagonal fun i => 1 + (d i : ℂ) * Complex.I) (v : ι → ℂ) :
    Zv Q v = ((|P.det| : ℝ) : ℂ) * ∏ i, ((2 * π / (1 + (d i : ℂ) * Complex.I)) ^ (1 / 2 : ℂ) *
      cexp (((cM P)ᵀ *ᵥ v) i ^ 2 / (2 * (1 + (d i : ℂ) * Complex.I)))) := by
  have hne : ∀ i, (1 + (d i : ℂ) * Complex.I) ≠ 0 := fun i h => by
    have := congrArg Complex.re h; simp at this
  unfold Zv
  have hsub := integral_comp_matrix P hdet fun x => cexp (-(1 / 2) * qf Q x - cV x ⬝ᵥ v)
  have habs : (|P.det| : ℝ) ≠ 0 := abs_ne_zero.2 hdet
  have h1 : ∫ x, cexp (-(1 / 2) * qf Q x - cV x ⬝ᵥ v) =
      ((|P.det| : ℝ) : ℂ) * ∫ y, cexp (-(1 / 2) * qf Q (P *ᵥ y) - cV (P *ᵥ y) ⬝ᵥ v) := by
    rw [hsub, Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ habs, Complex.ofReal_one,
      one_mul]
  rw [h1]
  refine congrArg (fun z => ((|P.det| : ℝ) : ℂ) * z) ?_
  -- the integrand after the substitution
  have hint : ∀ y : ι → ℝ, cexp (-(1 / 2) * qf Q (P *ᵥ y) - cV (P *ᵥ y) ⬝ᵥ v) =
      cexp (-∑ i, (1 / 2 * (1 + (d i : ℂ) * Complex.I)) * (y i : ℂ) ^ 2 +
        ∑ i, (-((cM P)ᵀ *ᵥ v) i) * (y i : ℂ)) := by
    intro y
    congr 1
    unfold qf
    rw [cV_mulVec, mulVec_dot, mulVec_dot, mulVec_mulVec, mulVec_mulVec, hPQ]
    rw [dot_diagonal, Finset.mul_sum, ← Finset.sum_neg_distrib, sub_eq_add_neg]
    congr 1
    · exact Finset.sum_congr rfl fun i _ => by simp [cV]; ring
    · simp only [dotProduct, cV]
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hint)]
  rw [GaussianFourier.integral_cexp_neg_sum_mul_add (b := fun i => 1 / 2 * (1 + (d i : ℂ) * Complex.I))
    (c := fun i => -((cM P)ᵀ *ᵥ v) i) (fun i => by simp)]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hb : (π : ℂ) / (1 / 2 * (1 + (d i : ℂ) * Complex.I)) = 2 * π / (1 + (d i : ℂ) * Complex.I) := by
    field_simp
  have he : (-((cM P)ᵀ *ᵥ v) i) ^ 2 / (4 * (1 / 2 * (1 + (d i : ℂ) * Complex.I))) =
      ((cM P)ᵀ *ᵥ v) i ^ 2 / (2 * (1 + (d i : ℂ) * Complex.I)) := by
    rw [neg_sq]; congr 1; ring
  rw [hb, he]

/-- `Σ_kw_k²/(1 + id_k) = ⟨v, Q⁻¹v⟩`, `w = Pᵀv`. -/
lemma exponent_normal {Q : Matrix ι ι ℂ} {P : Matrix ι ι ℝ} {d : ι → ℝ} (hdet : P.det ≠ 0)
    (hPQ : (cM P)ᵀ * Q * cM P = diagonal fun i => 1 + (d i : ℂ) * Complex.I) (v : ι → ℂ) :
    ∑ i, ((cM P)ᵀ *ᵥ v) i ^ 2 / (2 * (1 + (d i : ℂ) * Complex.I)) = 1 / 2 * (v ⬝ᵥ (Q⁻¹ *ᵥ v)) := by
  rw [inv_normal hdet hPQ, ← mulVec_mulVec, ← mulVec_mulVec]
  rw [show v ⬝ᵥ (cM P *ᵥ (diagonal (fun i => (1 + (d i : ℂ) * Complex.I)⁻¹) *ᵥ ((cM P)ᵀ *ᵥ v))) =
      ((cM P)ᵀ *ᵥ v) ⬝ᵥ (diagonal (fun i => (1 + (d i : ℂ) * Complex.I)⁻¹) *ᵥ ((cM P)ᵀ *ᵥ v)) by
    rw [dotProduct_comm, mulVec_dot, dotProduct_comm]]
  rw [dot_diagonal, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by field_simp

/-- **`eq:complex-gaussian` before normalisation**: `Z(Q, v) = Z(Q, 0)e^{½⟨v, Q⁻¹v⟩}`. -/
theorem Zv_eq {Q : Matrix ι ι ℂ} (hQ : Q ∈ QSet) (v : ι → ℂ) :
    Zv Q v = Zv Q 0 * cexp (1 / 2 * (v ⬝ᵥ (Q⁻¹ *ᵥ v))) := by
  obtain ⟨P, d, hdet, hPQ⟩ := normal_form hQ
  rw [Zv_normal hdet hPQ v, Zv_normal hdet hPQ 0, ← exponent_normal hdet hPQ v, Complex.exp_sum]
  simp only [mulVec_zero, Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div,
    Complex.exp_zero, mul_one, Finset.prod_mul_distrib]
  ring

lemma Zv_zero_normal {Q : Matrix ι ι ℂ} {P : Matrix ι ι ℝ} {d : ι → ℝ} (hdet : P.det ≠ 0)
    (hPQ : (cM P)ᵀ * Q * cM P = diagonal fun i => 1 + (d i : ℂ) * Complex.I) :
    Zv Q 0 = ((|P.det| : ℝ) : ℂ) * ∏ i, (2 * π / (1 + (d i : ℂ) * Complex.I)) ^ (1 / 2 : ℂ) := by
  rw [Zv_normal hdet hPQ 0]
  simp

/-- `Z(Q, 0) ≠ 0`. -/
theorem Zv_zero_ne {Q : Matrix ι ι ℂ} (hQ : Q ∈ QSet) : Zv Q 0 ≠ 0 := by
  obtain ⟨P, d, hdet, hPQ⟩ := normal_form hQ
  rw [Zv_zero_normal hdet hPQ]
  refine mul_ne_zero (by exact_mod_cast abs_ne_zero.2 hdet) (Finset.prod_ne_zero_iff.2 fun i _ => ?_)
  have hne : (1 + (d i : ℂ) * Complex.I) ≠ 0 := fun h' => by
    have := congrArg Complex.re h'; simp at this
  rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
  left
  exact div_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.2 Real.pi_ne_zero)) hne

/-- **`eq:complex-gaussian`**: `det(Q/2π)^{1/2}∫e^{-½⟨A, QA⟩ - ⟨A, v⟩}dA = e^{½⟨v, Q⁻¹v⟩}`; in particular
`ν_Q(E) = 1`. -/
theorem complex_gaussian {Q : Matrix ι ι ℂ} (hQ : Q ∈ QSet) (v : ι → ℂ) :
    root Q * Zv Q v = cexp (1 / 2 * (v ⬝ᵥ (Q⁻¹ *ᵥ v))) := by
  rw [Zv_eq hQ v, root, ← mul_assoc, inv_mul_cancel₀ (Zv_zero_ne hQ), one_mul]

/-- **The square of the root** is `det(Q/2π)`. -/
theorem root_sq {Q : Matrix ι ι ℂ} (hQ : Q ∈ QSet) : root Q ^ 2 = ((2 * π : ℂ)⁻¹ • Q).det := by
  obtain ⟨P, d, hdet, hPQ⟩ := normal_form hQ
  have hne : ∀ i, (1 + (d i : ℂ) * Complex.I) ≠ 0 := fun i h => by
    have := congrArg Complex.re h; simp at this
  have hdQ := congrArg Matrix.det hPQ
  rw [det_mul, det_mul, det_transpose, det_cM, det_diagonal] at hdQ
  have hP0 : (P.det : ℂ) ≠ 0 := by exact_mod_cast hdet
  have hpi : (2 * π : ℂ) ≠ 0 := mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.2 Real.pi_ne_zero)
  have hsq : ∀ z : ℂ, (z ^ (1 / 2 : ℂ)) ^ 2 = z := fun z => by
    rw [← Complex.cpow_nat_mul]; norm_num
  have habs : ((|P.det| : ℝ) : ℂ) ^ 2 = (P.det : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow, sq_abs, Complex.ofReal_pow]
  have hZ2 : Zv Q 0 ^ 2 = (P.det : ℂ) ^ 2 * (2 * π) ^ Fintype.card ι / ∏ i, (1 + (d i : ℂ) * Complex.I) := by
    rw [Zv_zero_normal hdet hPQ, mul_pow, habs, ← Finset.prod_pow]
    simp only [hsq]
    rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, mul_div_assoc]
  have hprod : ∏ i, (1 + (d i : ℂ) * Complex.I) = (P.det : ℂ) ^ 2 * Q.det := by
    rw [← hdQ]; ring
  have hQ0 : Q.det ≠ 0 := det_ne_zero hQ
  rw [root, inv_pow, hZ2, hprod, det_smul, inv_pow]
  field_simp

/-- **The root at the real `Q`** is positive. -/
theorem root_real {R : Matrix ι ι ℝ} (hR : cM R ∈ QSet) : ∃ r : ℝ, 0 < r ∧ root (cM R) = r := by
  obtain ⟨P, d, hdet, hPQ⟩ := normal_form hR
  -- the imaginary parts vanish, so `d = 0`
  have hd : ∀ i, d i = 0 := by
    intro i
    have hc : (cM P)ᵀ * cM R * cM P = cM (Pᵀ * R * P) := by
      simp only [cM, Matrix.map_mul, Matrix.transpose_map]
    rw [hc] at hPQ
    have h := congrArg (fun M : Matrix ι ι ℂ => (M i i).im) hPQ
    simp [cM] at h
    linarith
  have hZ : Zv (cM R) 0 = ((|P.det| * Real.sqrt (2 * π) ^ Fintype.card ι : ℝ) : ℂ) := by
    rw [Zv_zero_normal hdet hPQ]
    simp only [hd, Complex.ofReal_zero, zero_mul, add_zero, div_one]
    rw [Finset.prod_const, Finset.card_univ, Complex.ofReal_mul, Complex.ofReal_pow]
    congr 2
    rw [show (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) by push_cast; ring, Real.sqrt_eq_rpow,
      Complex.ofReal_cpow (mul_pos two_pos Real.pi_pos).le]
    norm_num
  refine ⟨(|P.det| * Real.sqrt (2 * π) ^ Fintype.card ι)⁻¹, inv_pos.2 (mul_pos (abs_pos.2 hdet)
    (pow_pos (Real.sqrt_pos.2 (by positivity)) _)), ?_⟩
  rw [root, hZ, Complex.ofReal_inv]

end ComplexGauss
end CoreLean

end
