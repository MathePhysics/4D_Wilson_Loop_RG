module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Finite-dimensional Gaussian integrals with determinants

For a finite index type `ι` and a real symmetric positive definite matrix `A`:
`∫ exp(-½ φᵀAφ + J·φ) dφ = (2π)^{n/2} (det A)^{-1/2} exp(½ Jᵀ A⁻¹ J)` for complex `J`
(`Balaban.integral_cexp_quadratic_form`). The proof takes the matrix square root `S` of `A`
(`CFC.sqrt`), changes variables `ψ = Sφ` and uses Mathlib's
`GaussianFourier.integral_cexp_neg_mul_sum_add`. The vector `J` pairs with `φ` by the plain sum
`∑ i, J i * φ i`; no weights appear here (weights are handled in `Balaban.Lattice`).

Provenance: copied unchanged from `Balaban/Gaussian/Integral.lean` of
https://github.com/scottnarmstrong/balaban-lean at commit
`493e9eb97292ebf6070c1c217a09bcf1adc23857` (22 Oct 2026), Apache License 2.0
(`LICENSE-balaban-lean` in this folder).
-/

@[expose] public section

namespace Balaban

open Matrix MeasureTheory Complex
open scoped MatrixOrder Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Change of variables `ψ = S φ` for an invertible real matrix. -/
theorem integral_change_of_variable_mulVec (S : Matrix ι ι ℝ) (hS : S.det ≠ 0)
    (h : (ι → ℝ) → ℂ) (hc : Continuous h) :
    ∫ φ : ι → ℝ, h (S *ᵥ φ) = |S.det|⁻¹ • ∫ ψ : ι → ℝ, h ψ := by
  have hmap := Real.map_matrix_volume_pi_eq_smul_volume_pi hS
  have hT : Continuous (Matrix.toLin' S) := LinearMap.continuous_of_finiteDimensional _
  have h1 : ∫ ψ : ι → ℝ, h ψ ∂(Measure.map (Matrix.toLin' S) volume) =
      ∫ φ : ι → ℝ, h (Matrix.toLin' S φ) := 
    integral_map hT.aemeasurable hc.aestronglyMeasurable
  rw [hmap, integral_smul_measure] at h1
  have h2 : (ENNReal.ofReal |S.det⁻¹|).toReal = |S.det|⁻¹ := by
    rw [ENNReal.toReal_ofReal (abs_nonneg _), abs_inv]
  rw [h2] at h1
  simp only [Matrix.toLin'_apply] at h1
  rw [← h1]
  

/-- Gaussian integral in square-root form `‖S φ‖²`. -/
theorem integral_cexp_sqrt_form (S : Matrix ι ι ℝ) (hS : S.det ≠ 0) (J : ι → ℂ) :
    ∫ φ : ι → ℝ, cexp (-(1 / 2 : ℂ) * ∑ i, (((S *ᵥ φ) i : ℝ) : ℂ) ^ 2 + ∑ i, J i * (φ i : ℂ))
      = (|S.det|⁻¹ : ℝ) * ((2 * π : ℂ) ^ ((Fintype.card ι : ℂ) / 2) *
          cexp ((1 / 2 : ℂ) * ∑ k, (∑ i, ((S⁻¹ i k : ℝ) : ℂ) * J i) ^ 2)) := by
  set c : ι → ℂ := fun k => ∑ i, ((S⁻¹ i k : ℝ) : ℂ) * J i with hc
  set h : (ι → ℝ) → ℂ := fun ψ => cexp (-(1 / 2 : ℂ) * ∑ i, ((ψ i : ℝ) : ℂ) ^ 2 + ∑ i, c i * (ψ i : ℂ))
    with hh
  have hcont : Continuous h := by
    simp only [hh]; fun_prop
  have hpt : ∀ φ : ι → ℝ, cexp (-(1 / 2 : ℂ) * ∑ i, (((S *ᵥ φ) i : ℝ) : ℂ) ^ 2 + ∑ i, J i * (φ i : ℂ))
      = h (S *ᵥ φ) := by
    intro φ
    simp only [hh]
    congr 2
    have : ∑ k, c k * (((S *ᵥ φ) k : ℝ) : ℂ) = ∑ i, J i * (φ i : ℂ) := by
      set Mi : Matrix ι ι ℂ := (S⁻¹).map Complex.ofReal with hMi
      set Mc : Matrix ι ι ℂ := S.map Complex.ofReal with hMc
      have hMM : Mi * Mc = 1 := by
        have := congrArg (fun M : Matrix ι ι ℝ => M.map Complex.ofReal)
          (Matrix.nonsing_inv_mul S (isUnit_iff_ne_zero.mpr hS))
        have h2 : Mi * Mc = (S⁻¹ * S).map Complex.ofReal :=
          (Matrix.map_mul (f := Complex.ofRealHom)).symm
        rw [h2]
        simpa using this
      have e1 : ∀ k, c k = (J ᵥ* Mi) k := by
        intro k; simp [hc, hMi, Matrix.vecMul, dotProduct, mul_comm]
      have e2 : ∀ k, (((S *ᵥ φ) k : ℝ) : ℂ) = (Mc *ᵥ (fun j => (φ j : ℂ))) k := by
        intro k; simp [hMc, Matrix.mulVec, dotProduct]
      calc ∑ k, c k * (((S *ᵥ φ) k : ℝ) : ℂ)
          = (J ᵥ* Mi) ⬝ᵥ (Mc *ᵥ (fun j => (φ j : ℂ))) := by
            simp only [e1, e2, dotProduct]
        _ = J ⬝ᵥ (Mi *ᵥ (Mc *ᵥ (fun j => (φ j : ℂ)))) := (Matrix.dotProduct_mulVec J Mi _).symm
        _ = ∑ i, J i * (φ i : ℂ) := by
            rw [Matrix.mulVec_mulVec, hMM, Matrix.one_mulVec]; rfl
    exact this.symm
  simp_rw [hpt]
  rw [integral_change_of_variable_mulVec S hS h hcont]
  have := GaussianFourier.integral_cexp_neg_mul_sum_add (ι := ι) (b := (1/2 : ℂ)) (by norm_num) c
  have e : ∀ ψ : ι → ℝ, h ψ = cexp (-(1/2 : ℂ) * ∑ i, ((ψ i : ℝ) : ℂ) ^ 2 + ∑ i, c i * (ψ i : ℂ)) :=
    fun _ => rfl
  simp_rw [e]
  rw [this]
  rw [Complex.real_smul]
  have h1 : (π : ℂ) / (1 / 2) = 2 * π := by ring
  have h2 : (∑ i, c i ^ 2) / (4 * (1 / 2) : ℂ) = (1 / 2 : ℂ) * ∑ k, (∑ i, ((S⁻¹ i k : ℝ) : ℂ) * J i) ^ 2 := by
    simp only [hc]; ring
  rw [h1, h2]

/-- The bilinear form `∑ₖ (S⁻¹ᵀ J)ₖ²` equals `Jᵀ (S S)⁻¹ J`. -/
theorem sum_sq_inv (S : Matrix ι ι ℝ) (hsym : Sᵀ = S) (J : ι → ℂ) :
    ∑ k, (∑ i, ((S⁻¹ i k : ℝ) : ℂ) * J i) ^ 2 = ∑ i, ∑ j, J i * (((S * S)⁻¹ i j : ℝ) : ℂ) * J j := by
  have hMt : (S⁻¹.map Complex.ofReal)ᵀ = S⁻¹.map Complex.ofReal := by
    have : (S⁻¹)ᵀ = S⁻¹ := by rw [Matrix.transpose_nonsing_inv, hsym]
    rw [← Matrix.transpose_map, this]
  have hMM : S⁻¹.map Complex.ofReal * S⁻¹.map Complex.ofReal = ((S * S)⁻¹).map Complex.ofReal := by
    rw [Matrix.mul_inv_rev]
    exact (Matrix.map_mul (f := Complex.ofRealHom)).symm
  have e1 : ∀ k, (∑ i, ((S⁻¹ i k : ℝ) : ℂ) * J i) = (J ᵥ* S⁻¹.map Complex.ofReal) k := by
    intro k; simp [Matrix.vecMul, dotProduct, mul_comm]
  have step : ∑ k, (∑ i, ((S⁻¹ i k : ℝ) : ℂ) * J i) ^ 2 =
      (J ᵥ* S⁻¹.map Complex.ofReal) ⬝ᵥ (J ᵥ* S⁻¹.map Complex.ofReal) := by
    simp only [e1, dotProduct, sq]
  rw [step]
  have hv : J ᵥ* S⁻¹.map Complex.ofReal = S⁻¹.map Complex.ofReal *ᵥ J := by
    rw [← Matrix.vecMul_transpose, hMt]
  nth_rewrite 2 [hv]
  rw [← Matrix.dotProduct_mulVec]
  rw [Matrix.mulVec_mulVec, hMM]
  simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **Gaussian integral with determinant.** For a real symmetric positive definite `A` and complex
`J`,
`∫ exp(-½⟨φ, Aφ⟩ + ⟨J, φ⟩) dφ = (2π)^{n/2} (det A)^{-1/2} exp(½⟨J, A⁻¹ J⟩)`. -/
theorem integral_cexp_quadratic_form (A : Matrix ι ι ℝ) (hA : A.PosDef) (J : ι → ℂ) :
    ∫ φ : ι → ℝ, cexp (-(1 / 2 : ℂ) * ((φ ⬝ᵥ A *ᵥ φ : ℝ) : ℂ) + ∑ i, J i * (φ i : ℂ))
      = ((Real.sqrt A.det)⁻¹ : ℝ) * ((2 * π : ℂ) ^ ((Fintype.card ι : ℂ) / 2) *
          cexp ((1 / 2 : ℂ) * ∑ i, ∑ j, J i * ((A⁻¹ i j : ℝ) : ℂ) * J j)) := by
  have h0 : (0 : Matrix ι ι ℝ) ≤ A := Matrix.nonneg_iff_posSemidef.mpr hA.posSemidef
  obtain ⟨S, hsym, hSS⟩ : ∃ S : Matrix ι ι ℝ, Sᵀ = S ∧ S * S = A := by
    refine ⟨CFC.sqrt A, ?_, CFC.sqrt_mul_sqrt_self A h0⟩
    have := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).isHermitian
    have h : (CFC.sqrt A)ᴴ = CFC.sqrt A := this
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have hdet : S.det ^ 2 = A.det := by rw [← hSS, Matrix.det_mul, sq]
  have hdpos : 0 < A.det := hA.det_pos
  have hS : S.det ≠ 0 := by
    intro h; rw [h] at hdet; simp at hdet; linarith
  have habs : |S.det| = Real.sqrt A.det := by rw [← hdet, Real.sqrt_sq_eq_abs]
  have hq : ∀ φ : ι → ℝ, φ ⬝ᵥ A *ᵥ φ = ∑ i, ((S *ᵥ φ) i) ^ 2 := by
    intro φ
    rw [← hSS, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hsym]
    simp [dotProduct, sq]
  have := integral_cexp_sqrt_form S hS J
  simp_rw [hq]
  push_cast
  rw [this, habs, sum_sq_inv S hsym J, hSS]
  push_cast
  rfl

end Balaban
