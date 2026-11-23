import Mathlib

/-! The operator norm of a positive semidefinite symmetric operator is bounded by the bound of its quadratic form:
if `0 ≤ ⟪x, T x⟫ ≤ θ ‖x‖²`, then `‖T‖ ≤ θ` (Cauchy-Schwarz for the form `⟪u, T v⟫`). -/

namespace GaussianBlockSpin

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Cauchy-Schwarz for a symmetric positive semidefinite form. -/
lemma inner_map_sq_le (T : E →L[ℝ] E) (hsymm : ∀ x y, ⟪T x, y⟫ = ⟪x, T y⟫) (hpos : ∀ x, 0 ≤ ⟪x, T x⟫) (u v : E) :
    ⟪u, T v⟫ ^ 2 ≤ ⟪u, T u⟫ * ⟪v, T v⟫ := by
  have hq : ∀ t : ℝ, 0 ≤ ⟪v, T v⟫ * (t * t) + (2 * ⟪u, T v⟫) * t + ⟪u, T u⟫ := by
    intro t
    have h := hpos (u + t • v)
    have hvu : ⟪v, T u⟫ = ⟪u, T v⟫ := by rw [← hsymm, real_inner_comm]
    simp only [map_add, map_smul, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      RCLike.conj_to_real] at h
    rw [hvu] at h
    nlinarith
  have hd := discrim_le_zero hq
  unfold discrim at hd
  nlinarith

/-- **The norm of a positive semidefinite operator**: `0 ≤ ⟪x, T x⟫ ≤ θ ‖x‖²` gives `‖T‖ ≤ θ`. -/
theorem opNorm_le_of_psd (T : E →L[ℝ] E) (hsymm : ∀ x y, ⟪T x, y⟫ = ⟪x, T y⟫) (hpos : ∀ x, 0 ≤ ⟪x, T x⟫)
    {θ : ℝ} (hθ : 0 ≤ θ) (hle : ∀ x, ⟪x, T x⟫ ≤ θ * ‖x‖ ^ 2) : ‖T‖ ≤ θ := by
  refine ContinuousLinearMap.opNorm_le_bound _ hθ fun x => ?_
  have hcs := inner_map_sq_le T hsymm hpos (T x) x
  have h1 : ⟪T x, T x⟫ = ‖T x‖ ^ 2 := real_inner_self_eq_norm_sq _
  have h2 : ⟪T x, T (T x)⟫ ≤ θ * ‖T x‖ ^ 2 := hle (T x)
  have h3 : ⟪x, T x⟫ ≤ θ * ‖x‖ ^ 2 := hle x
  have h0 : 0 ≤ ⟪x, T x⟫ := hpos x
  have h0' : 0 ≤ ⟪T x, T (T x)⟫ := hpos (T x)
  rw [h1] at hcs
  -- `‖T x‖^4 ≤ θ² ‖T x‖² ‖x‖²`
  have h4 : (‖T x‖ ^ 2) ^ 2 ≤ (θ * ‖T x‖ ^ 2) * (θ * ‖x‖ ^ 2) :=
    hcs.trans (mul_le_mul h2 h3 h0 (by positivity))
  by_cases hTx : ‖T x‖ = 0
  · rw [hTx]; positivity
  · have hpos' : 0 < ‖T x‖ ^ 2 := by positivity
    have h5 : ‖T x‖ ^ 2 ≤ (θ * ‖x‖) ^ 2 := by
      have : ‖T x‖ ^ 2 * ‖T x‖ ^ 2 ≤ ‖T x‖ ^ 2 * (θ * ‖x‖) ^ 2 := by nlinarith
      exact le_of_mul_le_mul_left this hpos'
    by_contra hcon
    push Not at hcon
    have hθx : 0 ≤ θ * ‖x‖ := by positivity
    nlinarith

end GaussianBlockSpin
