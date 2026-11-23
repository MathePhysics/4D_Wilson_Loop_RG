import GaussianBlockSpin.FieldCoordinates
import GaussianBlockSpin.PairGaussLaws
import GaussianBlockSpin.MatrixInvSqrt

/-! Facts used to write Gaussian laws through the inverse square root:
* invSqrt_facts: under spectral bounds `0 < γ₀ ≤ Q ≤ γ₁` (`Q` symmetric), `A = invSqrt Q γ₁` is symmetric with
  `A A = Q⁻¹`, and `Q` is invertible;
* gaussPush_smul: `(s A)_* N(0,1)^{⊗ι}` is the image of `A_* N(0,1)^{⊗ι}` under `z ↦ s z`;
* inv_smul_of_ne: `(c Q)⁻¹ = c⁻¹ Q⁻¹`. -/

namespace GaussianBlockSpin

open MeasureTheory ProbabilityTheory Real Matrix
open scoped RealInnerProductSpace Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Facts about the inverse square root under spectral bounds. -/
lemma invSqrt_facts {Q : Matrix ι ι ℝ} (hQ : Qᵀ = Q) {γ₀ γ₁ : ℝ} (hγ₀ : 0 < γ₀) (hγ₀₁ : γ₀ ≤ γ₁)
    (hlo : ∀ v : ι → ℝ, γ₀ * (v ⬝ᵥ v) ≤ v ⬝ᵥ Q *ᵥ v) (hhi : ∀ v : ι → ℝ, v ⬝ᵥ Q *ᵥ v ≤ γ₁ * (v ⬝ᵥ v)) :
    (invSqrt Q γ₁)ᵀ = invSqrt Q γ₁ ∧ invSqrt Q γ₁ * invSqrt Q γ₁ = Q⁻¹ ∧ IsUnit Q.det := by
  have hγ₁ : 0 < γ₁ := hγ₀.trans_le hγ₀₁
  have hN : ‖precN Q γ₁‖ < 1 := (norm_precN_le hQ hγ₀ hγ₀₁ hlo hhi).trans_lt (by
    have := div_pos hγ₀ hγ₁; linarith)
  obtain ⟨h1, h2⟩ := invSqrt_mul_self hγ₁ hN
  exact ⟨invSqrt_transpose hQ γ₁, h1, isUnit_det_of_left_inverse h2⟩

omit [DecidableEq ι] in
/-- Scaling the matrix scales the law. -/
lemma gaussPush_smul (A : Matrix ι ι ℝ) (s : ℝ) :
    gaussPush (s • A) = (gaussPush A).map fun z => s • z := by
  unfold gaussPush
  rw [Measure.map_map (measurable_const_smul s) (measurable_mulVec A)]
  congr 1
  funext ξ
  simp [Function.comp, smul_mulVec]

/-- `(c Q)⁻¹ = c⁻¹ Q⁻¹` for invertible `Q` and `c ≠ 0`. -/
lemma inv_smul_of_ne {Q : Matrix ι ι ℝ} (hQ : IsUnit Q.det) {c : ℝ} (hc : c ≠ 0) : (c • Q)⁻¹ = c⁻¹ • Q⁻¹ := by
  refine (inv_eq_left_inv ?_)
  rw [smul_mul_smul_comm, inv_mul_cancel₀ hc, one_smul, nonsing_inv_mul _ hQ]

end GaussianBlockSpin
