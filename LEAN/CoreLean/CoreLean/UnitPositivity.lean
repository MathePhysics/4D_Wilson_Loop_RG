/-
`lem:unit-localised-positivity` of BALABAN_CORE.tex (`a021c13be348`), the abstract steps of its conclusion, in a
finite-dimensional complex inner product space (the functions on `S` with the Hilbert–Schmidt pairing).

* `pairing_le`: `|⟨μ, 𝒮μ⟩| ≤ ‖𝒮‖‖μ‖²` (Cauchy–Schwarz).
* `perturbed_positivity`: from `re⟨μ, Γμ⟩ ≥ (3/8)γ_f‖μ‖²` and `‖Γ(s) - Γ‖ ≤ γ_f/8`,
  `re⟨μ, Γ(s)μ⟩ ≥ ¼γ_f‖μ‖²`.
* `coercive_bijective`, `coercive_inverse_bound`: an operator with `re⟨μ, Tμ⟩ ≥ c‖μ‖²`, `c > 0`, is invertible, and its
  inverse has the norm at most `1/c`; with `c = ¼γ_f` this is the last statement of the lemma, `‖T⁻¹‖ ≤ 4γ_f⁻¹`.
-/
import Mathlib

noncomputable section

namespace CoreLean
namespace UnitPositivity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

open scoped InnerProductSpace

/-- `|⟨μ, 𝒮μ⟩| ≤ ‖𝒮‖‖μ‖²`. -/
theorem pairing_le (S : E →L[ℂ] E) (μ : E) : ‖⟪μ, S μ⟫_ℂ‖ ≤ ‖S‖ * ‖μ‖ ^ 2 := by
  calc ‖⟪μ, S μ⟫_ℂ‖ ≤ ‖μ‖ * ‖S μ‖ := norm_inner_le_norm _ _
    _ ≤ ‖μ‖ * (‖S‖ * ‖μ‖) := mul_le_mul_of_nonneg_left (S.le_opNorm μ) (norm_nonneg _)
    _ = ‖S‖ * ‖μ‖ ^ 2 := by ring

/-- **The positivity survives a perturbation of the size `γ_f/8`.** -/
theorem perturbed_positivity (T T' : E →L[ℂ] E) {γ : ℝ} (hT : ∀ μ, 3 / 8 * γ * ‖μ‖ ^ 2 ≤ (⟪μ, T μ⟫_ℂ).re)
    (hd : ‖T' - T‖ ≤ γ / 8) (μ : E) : 1 / 4 * γ * ‖μ‖ ^ 2 ≤ (⟪μ, T' μ⟫_ℂ).re := by
  have e : ⟪μ, T' μ⟫_ℂ = ⟪μ, T μ⟫_ℂ + ⟪μ, (T' - T) μ⟫_ℂ := by
    rw [← inner_add_right]; congr 1; simp
  have h1 := pairing_le (T' - T) μ
  have h2 : -(‖T' - T‖ * ‖μ‖ ^ 2) ≤ (⟪μ, (T' - T) μ⟫_ℂ).re :=
    neg_le_of_abs_le ((Complex.abs_re_le_norm _).trans h1)
  have h3 : ‖T' - T‖ * ‖μ‖ ^ 2 ≤ γ / 8 * ‖μ‖ ^ 2 := mul_le_mul_of_nonneg_right hd (sq_nonneg _)
  rw [e, Complex.add_re]
  have := hT μ
  nlinarith

/-- `c‖μ‖ ≤ ‖Tμ‖` for a coercive `T`. -/
theorem coercive_lower (T : E →L[ℂ] E) {c : ℝ} (hT : ∀ μ, c * ‖μ‖ ^ 2 ≤ (⟪μ, T μ⟫_ℂ).re) (μ : E) :
    c * ‖μ‖ ≤ ‖T μ‖ := by
  rcases eq_or_lt_of_le (norm_nonneg μ) with h | h
  · rw [← h, mul_zero]; exact norm_nonneg _
  · have h1 : c * ‖μ‖ ^ 2 ≤ ‖μ‖ * ‖T μ‖ :=
      (hT μ).trans ((Complex.re_le_norm _).trans (norm_inner_le_norm _ _))
    have h2 : c * ‖μ‖ * ‖μ‖ ≤ ‖T μ‖ * ‖μ‖ := by nlinarith
    exact le_of_mul_le_mul_right h2 h

/-- **A coercive operator on a finite-dimensional space is bijective.** -/
theorem coercive_bijective [FiniteDimensional ℂ E] (T : E →L[ℂ] E) {c : ℝ} (hc : 0 < c)
    (hT : ∀ μ, c * ‖μ‖ ^ 2 ≤ (⟪μ, T μ⟫_ℂ).re) : Function.Bijective T := by
  have hinj : Function.Injective T := by
    intro x y hxy
    have h := coercive_lower T hT (x - y)
    rw [map_sub, hxy, sub_self, norm_zero] at h
    have : ‖x - y‖ = 0 := le_antisymm (by nlinarith [norm_nonneg (x - y)]) (norm_nonneg _)
    exact sub_eq_zero.1 (norm_eq_zero.1 this)
  exact ⟨hinj, LinearMap.surjective_of_injective (f := (T : E →ₗ[ℂ] E)) hinj⟩

/-- **The bound of the inverse**: `‖μ‖ ≤ ‖Tμ‖/c`. -/
theorem coercive_inverse_bound (T : E →L[ℂ] E) {c : ℝ} (hc : 0 < c)
    (hT : ∀ μ, c * ‖μ‖ ^ 2 ≤ (⟪μ, T μ⟫_ℂ).re) (μ : E) : ‖μ‖ ≤ 1 / c * ‖T μ‖ := by
  have h := coercive_lower T hT μ
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hc]
  linarith

end UnitPositivity
end CoreLean

end
