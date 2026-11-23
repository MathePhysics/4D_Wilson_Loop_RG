/-
`lem:square-root-walks` of BALABAN_CORE.tex (`a021c13be348`), the representation of the square root in matrix form:
for a positive definite real matrix `Γ` with the spectral decomposition `Γ = U diag(γ) U^*`, the entries of
`π⁻¹∫_0^∞ x^{-1/2}(x + Γ)⁻¹ dx` are those of `Γ^{-1/2} = U diag(γ^{-1/2}) U^*` (`inv_sqrt_matrix`), from the scalar
identity `inv_sqrt_integral` in each eigenvalue: `(x + Γ)⁻¹ = U diag((x + γ)⁻¹) U^*` (`resolvent_diag`), and the
entries of `U diag(f) U^*` are `Σ_k U_{ik}f_kU_{jk}`, so that the integral passes through the finite sum.
-/
import CoreLean.SquareRootIntegral

open MeasureTheory Set Matrix

noncomputable section

namespace CoreLean
namespace SquareRootMatrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The resolvent in the eigenbasis: `(x + UDU^*)⁻¹ = U diag((x + d)⁻¹) U^*` when `x + d_k ≠ 0`. -/
lemma resolvent_diag (U : Matrix n n ℝ) (hU1 : star U * U = 1) (hU2 : U * star U = 1) (d : n → ℝ) (x : ℝ)
    (hd : ∀ k, d k + x ≠ 0) :
    (U * diagonal d * star U + x • (1 : Matrix n n ℝ))⁻¹ = U * diagonal (fun k => (d k + x)⁻¹) * star U := by
  have e : U * diagonal d * star U + x • (1 : Matrix n n ℝ) = U * diagonal (fun k => d k + x) * star U := by
    have h1 : diagonal (fun k => d k + x) = diagonal d + x • (1 : Matrix n n ℝ) := by
      ext i j
      by_cases h : i = j
      · subst h; simp
      · simp [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]
    rw [h1, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hU2]
  rw [e]
  refine Matrix.inv_eq_right_inv ?_
  calc U * diagonal (fun k => d k + x) * star U * (U * diagonal (fun k => (d k + x)⁻¹) * star U)
      = U * (diagonal (fun k => d k + x) * (star U * U) * diagonal (fun k => (d k + x)⁻¹)) * star U := by
        simp only [Matrix.mul_assoc]
    _ = U * diagonal (fun k => (d k + x) * (d k + x)⁻¹) * star U := by
        rw [hU1, Matrix.mul_one, diagonal_mul_diagonal]
    _ = 1 := by
        have : (fun k => (d k + x) * (d k + x)⁻¹) = fun _ => (1 : ℝ) := funext fun k => mul_inv_cancel₀ (hd k)
        rw [this, diagonal_one, Matrix.mul_one, hU2]

/-- The entries of `U diag(f) U^*`. -/
lemma conj_diag_apply (U : Matrix n n ℝ) (f : n → ℝ) (i j : n) :
    (U * diagonal f * star U) i j = ∑ k, U i k * f k * U j k := by
  simp [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.star_apply]

/-- **The representation of `Γ^{-1/2}`**, entrywise. -/
theorem inv_sqrt_matrix (A : Matrix n n ℝ) (hA : A.PosDef) (i j : n) :
    Real.pi⁻¹ * ∫ x in Ioi (0 : ℝ), 1 / Real.sqrt x * (A + x • (1 : Matrix n n ℝ))⁻¹ i j =
      (((hA.1.eigenvectorUnitary : Matrix n n ℝ)) * diagonal (fun k => 1 / Real.sqrt (hA.1.eigenvalues k)) *
        star ((hA.1.eigenvectorUnitary : Matrix n n ℝ))) i j := by
  set γ := hA.1.eigenvalues
  have hγ : ∀ k, 0 < γ k := hA.eigenvalues_pos
  set U : Matrix n n ℝ := (hA.1.eigenvectorUnitary : Matrix n n ℝ)
  have hU1 : star U * U = 1 := Unitary.coe_star_mul_self _
  have hU2 : U * star U = 1 := Unitary.coe_mul_star_self _
  have hAU : A = U * diagonal γ * star U := by
    have := hA.1.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply, RCLike.ofReal_real_eq_id, Function.id_comp] at this
    exact this
  -- the integrand entrywise, for `x > 0`
  have hent : ∀ x ∈ Ioi (0 : ℝ), 1 / Real.sqrt x * (A + x • (1 : Matrix n n ℝ))⁻¹ i j =
      ∑ k, U i k * U j k * (1 / (Real.sqrt x * (x + γ k))) := by
    intro x hx
    rw [mem_Ioi] at hx
    rw [hAU, resolvent_diag U hU1 hU2 γ x (fun k => by linarith [hγ k]), conj_diag_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hs : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
    have : γ k + x ≠ 0 := by linarith [hγ k]
    rw [show x + γ k = γ k + x from add_comm _ _]
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioi hent]
  -- the integrability of each term
  have hint : ∀ k, IntegrableOn (fun x : ℝ => 1 / (Real.sqrt x * (x + γ k))) (Ioi 0) := by
    intro k
    have hl := hγ k
    set F : ℝ → ℝ := fun x => 2 / Real.sqrt (γ k) * Real.arctan (Real.sqrt (x / γ k))
    have hcont : ContinuousWithinAt F (Ici 0) 0 := by
      have : Continuous F := continuous_const.mul (Real.continuous_arctan.comp (Real.continuous_sqrt.comp
        (continuous_id.div_const _)))
      exact this.continuousWithinAt
    have hlim : Filter.Tendsto F Filter.atTop (nhds (2 / Real.sqrt (γ k) * (Real.pi / 2))) :=
      (tendsto_const_nhds.mul (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds |>.comp
        (Real.tendsto_sqrt_atTop.comp (Filter.tendsto_id.atTop_div_const hl))))
    exact integrableOn_Ioi_deriv_of_nonneg hcont (fun x hx => SquareRootIntegral.hasDerivAt_F hl hx)
      (fun x hx => by rw [mem_Ioi] at hx; positivity) hlim
  rw [integral_finsetSum _ (fun k _ => (hint k).const_mul _), Finset.mul_sum, conj_diag_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_const_mul]
  have h := SquareRootIntegral.inv_sqrt_integral (hγ k)
  calc Real.pi⁻¹ * (U i k * U j k * ∫ x in Ioi (0 : ℝ), 1 / (Real.sqrt x * (x + γ k)))
      = U i k * U j k * (Real.pi⁻¹ * ∫ x in Ioi (0 : ℝ), 1 / (Real.sqrt x * (x + γ k))) := by ring
    _ = U i k * (1 / Real.sqrt (γ k)) * U j k := by rw [h]; ring

end SquareRootMatrix
end CoreLean

end
