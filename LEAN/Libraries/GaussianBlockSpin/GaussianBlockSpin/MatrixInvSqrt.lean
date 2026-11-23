import GaussianBlockSpin.SqrtCoefficients
import GaussianBlockSpin.PsdNorm

/-! **The inverse square root of a precision matrix as a power series**: for a symmetric `Q` with
`γ₀ |v|² ≤ vᵀ Q v ≤ γ₁ |v|²` (`0 < γ₀ ≤ γ₁`), `N = 1 - Q/γ₁` has operator norm `≤ θ = 1 - γ₀/γ₁ < 1`
(norm_precN_le), and `A = γ₁^{-1/2} Σ_n c_n N^n` (`c_n` the coefficients of `(1 - x)^{-1/2}`) satisfies `A A = Q⁻¹`
(invSqrt_mul_self), `Aᵀ = A` (invSqrt_transpose) and commutes with `Q` (invSqrt_commute). -/

namespace GaussianBlockSpin

open Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `N = 1 - Q/γ₁`. -/
noncomputable def precN (Q : Matrix ι ι ℝ) (γ₁ : ℝ) : Matrix ι ι ℝ := 1 - γ₁⁻¹ • Q

lemma inner_toEuclideanCLM_self (M : Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) :
    ⟪x, toEuclideanCLM (𝕜 := ℝ) M x⟫ = x.ofLp ⬝ᵥ M *ᵥ x.ofLp := inner_toEuclideanCLM M x x

omit [DecidableEq ι] in
lemma dotProduct_self_eq_norm_sq (x : EuclideanSpace ℝ ι) : x.ofLp ⬝ᵥ x.ofLp = ‖x‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]
  simp [dotProduct, sq]

omit [Fintype ι] in
lemma precN_transpose {Q : Matrix ι ι ℝ} (hQ : Qᵀ = Q) (γ₁ : ℝ) : (precN Q γ₁)ᵀ = precN Q γ₁ := by
  rw [precN, transpose_sub, transpose_one, transpose_smul, hQ]

/-- **`‖N‖ ≤ 1 - γ₀/γ₁`**. -/
lemma norm_precN_le {Q : Matrix ι ι ℝ} (hQ : Qᵀ = Q) {γ₀ γ₁ : ℝ} (hγ₀ : 0 < γ₀) (hγ₀₁ : γ₀ ≤ γ₁)
    (hlo : ∀ v : ι → ℝ, γ₀ * (v ⬝ᵥ v) ≤ v ⬝ᵥ Q *ᵥ v) (hhi : ∀ v : ι → ℝ, v ⬝ᵥ Q *ᵥ v ≤ γ₁ * (v ⬝ᵥ v)) :
    ‖precN Q γ₁‖ ≤ 1 - γ₀ / γ₁ := by
  have hγ₁ : 0 < γ₁ := hγ₀.trans_le hγ₀₁
  have hform : ∀ x : EuclideanSpace ℝ ι, ⟪x, toEuclideanCLM (𝕜 := ℝ) (precN Q γ₁) x⟫ =
      ‖x‖ ^ 2 - γ₁⁻¹ * (x.ofLp ⬝ᵥ Q *ᵥ x.ofLp) := fun x => by
    rw [inner_toEuclideanCLM_self, precN, sub_mulVec, dotProduct_sub, one_mulVec, smul_mulVec,
      dotProduct_smul, smul_eq_mul, dotProduct_self_eq_norm_sq]
  rw [← l2_opNorm_toEuclideanCLM]
  refine opNorm_le_of_psd _ (fun x y => ?_) (fun x => ?_) (by
      rw [sub_nonneg, div_le_one hγ₁]; exact hγ₀₁) (fun x => ?_)
  · rw [real_inner_comm, inner_toEuclideanCLM, inner_toEuclideanCLM, dotProduct_mulVec, ← mulVec_transpose,
      precN_transpose hQ, dotProduct_comm]
  · rw [hform]
    have h := hhi x.ofLp
    rw [dotProduct_self_eq_norm_sq] at h
    have : γ₁⁻¹ * (x.ofLp ⬝ᵥ Q *ᵥ x.ofLp) ≤ ‖x‖ ^ 2 := by
      rw [inv_mul_le_iff₀ hγ₁]; linarith
    linarith
  · rw [hform]
    have h := hlo x.ofLp
    rw [dotProduct_self_eq_norm_sq] at h
    have : γ₀ / γ₁ * ‖x‖ ^ 2 ≤ γ₁⁻¹ * (x.ofLp ⬝ᵥ Q *ᵥ x.ofLp) := by
      rw [div_eq_inv_mul, mul_assoc]
      exact mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hγ₁.le)
    linarith

instance : CompleteSpace (Matrix ι ι ℝ) := FiniteDimensional.complete ℝ _

/-- `Σ_n c_n N^n`; the series converges for `‖N‖ < 1` (summable_norm_sqrtCoef_smul). When it is not summable the
`tsum` is the junk value `0`. -/
noncomputable def sqrtSeries (N : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  ∑' n, sqrtCoef n • N ^ n -- totalisation-audit: allow junk 0 if the series is not summable; every theorem about it assumes ‖N‖ < 1

lemma summable_norm_sqrtCoef_smul {N : Matrix ι ι ℝ} (hN : ‖N‖ < 1) :
    Summable fun n => ‖sqrtCoef n • N ^ n‖ := by
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) (summable_norm_geometric_of_norm_lt_one hN)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sqrtCoef_nonneg n)]
  exact mul_le_of_le_one_left (norm_nonneg _) (sqrtCoef_le_one n)

/-- **`(Σ c_n N^n)² = Σ N^n`**. -/
lemma sqrtSeries_mul_self {N : Matrix ι ι ℝ} (hN : ‖N‖ < 1) : sqrtSeries N * sqrtSeries N = ∑' n, N ^ n := by
  unfold sqrtSeries
  rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm (summable_norm_sqrtCoef_smul hN)
    (summable_norm_sqrtCoef_smul hN)]
  refine tsum_congr fun n => ?_
  have h : ∀ kl ∈ Finset.HasAntidiagonal.antidiagonal n, (sqrtCoef kl.1 • N ^ kl.1) * (sqrtCoef kl.2 • N ^ kl.2) =
      (sqrtCoef kl.1 * sqrtCoef kl.2) • N ^ n := fun kl hkl => by
    rw [smul_mul_smul_comm, ← pow_add, Finset.HasAntidiagonal.mem_antidiagonal.mp hkl]
  rw [Finset.sum_congr rfl h, ← Finset.sum_smul]
  have hc := sum_antidiagonal_sqrtCoef n
  unfold sqrtConv at hc
  rw [show (∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n, sqrtCoef kl.1 * sqrtCoef kl.2) = 1 from hc, one_smul]

/-- `A = γ₁^{-1/2} Σ_n c_n N^n`, `N = 1 - Q/γ₁`. It is `Q^{-1/2}` when `γ₁ > 0` and `‖N‖ < 1` (invSqrt_mul_self;
the condition is sufficient, and for symmetric `Q` also necessary); otherwise it is possibly the junk zero matrix
(`(√γ₁)⁻¹ = 0` for `γ₁ ≤ 0`, or a non-summable series). -/
noncomputable def invSqrt (Q : Matrix ι ι ℝ) (γ₁ : ℝ) : Matrix ι ι ℝ :=
  (Real.sqrt γ₁)⁻¹ • sqrtSeries (precN Q γ₁) -- totalisation-audit: allow junk 0 for γ₁ ≤ 0 or a non-summable series (for symmetric Q exactly when ‖N‖ ≥ 1); invSqrt_mul_self and abs_invSqrt_apply_le assume γ₁ > 0 and ‖N‖ < 1

/-- **`A A = Q⁻¹`**. -/
theorem invSqrt_mul_self {Q : Matrix ι ι ℝ} {γ₁ : ℝ} (hγ₁ : 0 < γ₁) (hN : ‖precN Q γ₁‖ < 1) :
    invSqrt Q γ₁ * invSqrt Q γ₁ = Q⁻¹ ∧ (γ₁⁻¹ • ∑' n, precN Q γ₁ ^ n) * Q = 1 := by
  have hgeo := geom_series_mul_neg (precN Q γ₁) hN
  have h1N : 1 - precN Q γ₁ = γ₁⁻¹ • Q := by rw [precN]; abel
  rw [h1N, mul_smul_comm, ← smul_mul_assoc] at hgeo
  refine ⟨?_, hgeo⟩
  rw [invSqrt, smul_mul_smul_comm, sqrtSeries_mul_self hN, Matrix.inv_eq_left_inv hgeo]
  congr 1
  rw [← mul_inv, Real.mul_self_sqrt hγ₁.le]

/-- **`Aᵀ = A`** for symmetric `Q`. -/
theorem invSqrt_transpose {Q : Matrix ι ι ℝ} (hQ : Qᵀ = Q) (γ₁ : ℝ) : (invSqrt Q γ₁)ᵀ = invSqrt Q γ₁ := by
  rw [invSqrt, transpose_smul, sqrtSeries, transpose_tsum]
  congr 2
  funext n
  rw [transpose_smul, transpose_pow, precN_transpose hQ]

/-- `A` commutes with `Q`. -/
theorem invSqrt_commute {Q : Matrix ι ι ℝ} (γ₁ : ℝ) :
    Commute (invSqrt Q γ₁) Q := by
  have hQ : Q = γ₁ • (1 - precN Q γ₁) ∨ γ₁ = 0 := by
    by_cases h : γ₁ = 0
    · exact Or.inr h
    · left; rw [precN, sub_sub_cancel, smul_smul, mul_inv_cancel₀ h, one_smul]
  have hcN : Commute (sqrtSeries (precN Q γ₁)) (precN Q γ₁) := by
    unfold sqrtSeries
    refine Commute.tsum_left _ fun n => ?_
    exact (Commute.pow_left (Commute.refl (precN Q γ₁)) n).smul_left (sqrtCoef n)
  rcases hQ with hQ | hQ
  · have h := ((((Commute.one_right (sqrtSeries (precN Q γ₁))).sub_right hcN).smul_right γ₁).smul_left
      ((Real.sqrt γ₁)⁻¹ : ℝ))
    rw [← hQ] at h
    exact h
  · simp [invSqrt, hQ]

end GaussianBlockSpin
