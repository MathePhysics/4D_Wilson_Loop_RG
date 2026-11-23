/-
`prop:comparison`(ii) of BALABAN_CORE.tex (`a021c13be348`), the two steps of the proof of `eq:comparison` from
`thm:background-field`(iv).

* `integral_bound`: since `𝓗(𝔟₀) = 0`, `𝓗'(B)` is the integral over `t ∈ [0, 1]` of the derivative of `𝓗(𝔟_{tB})`
  in the direction `B`; a bound `K` of this derivative for every `t` bounds `𝓗'(B)` (the mean value inequality).
* `comparison_sum`: if every point is the first end of at most eight positive bonds of the layers and
  `Σ_x e^{-½δ₂d'(y, x)} ≤ c₁(½, δ₂)` (`eq:summation` with `α = ½`), then
  `Σ_{c' ∈ S} e^{-δ₂d'(y, c'_-)}‖B(c')‖ ≤ 8c₁(½, δ₂)e^{-½δ₂d'(y, S)}‖B‖_∞`, and with the factor `2B₆` of the two pairs
  of terms this is the last line of `eq:comparison` (`comparison_bound`).
-/
import Mathlib

open Set

noncomputable section

namespace CoreLean
namespace ComparisonArith

/-- **The integral along `tB`**: `‖f(1) - f(0)‖ ≤ K` if `‖f'(t)‖ ≤ K` on `[0, 1]`. -/
theorem integral_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f f' : ℝ → E} {K : ℝ}
    (hf : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt f (f' t) (Icc 0 1) t)
    (hK : ∀ t ∈ Ico (0 : ℝ) 1, ‖f' t‖ ≤ K) : ‖f 1 - f 0‖ ≤ K := by
  have := norm_image_sub_le_of_norm_deriv_le_segment' hf hK 1 (right_mem_Icc.2 zero_le_one)
  simpa using this

/-- **The summation over the bonds of `S`**. -/
theorem comparison_sum {ι X : Type*} [Fintype ι] [Fintype X] [DecidableEq X] (f : ι → X)
    (hfib : ∀ x, (Finset.univ.filter fun c => f c = x).card ≤ 8) (d : X → ℝ) {D δ c₁ B : ℝ} (hδ : 0 ≤ δ)
    (hD : ∀ c, D ≤ d (f c)) (hc₁ : ∑ x, Real.exp (-(1 / 2) * δ * d x) ≤ c₁) (b : ι → ℝ) (hb0 : ∀ c, 0 ≤ b c)
    (hb : ∀ c, b c ≤ B) (hB : 0 ≤ B) :
    ∑ c, Real.exp (-δ * d (f c)) * b c ≤ 8 * c₁ * Real.exp (-(1 / 2) * δ * D) * B := by
  -- each term
  have hterm : ∀ c, Real.exp (-δ * d (f c)) * b c ≤
      Real.exp (-(1 / 2) * δ * D) * B * Real.exp (-(1 / 2) * δ * d (f c)) := fun c => by
    have e : Real.exp (-δ * d (f c)) = Real.exp (-(1 / 2) * δ * d (f c)) * Real.exp (-(1 / 2) * δ * d (f c)) := by
      rw [← Real.exp_add]; congr 1; ring
    have h1 : Real.exp (-(1 / 2) * δ * d (f c)) ≤ Real.exp (-(1 / 2) * δ * D) :=
      Real.exp_le_exp.2 (by nlinarith [hD c])
    rw [e]
    calc Real.exp (-(1 / 2) * δ * d (f c)) * Real.exp (-(1 / 2) * δ * d (f c)) * b c
        ≤ Real.exp (-(1 / 2) * δ * D) * Real.exp (-(1 / 2) * δ * d (f c)) * B := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le) (hb c) (hb0 c)
          positivity
      _ = Real.exp (-(1 / 2) * δ * D) * B * Real.exp (-(1 / 2) * δ * d (f c)) := by ring
  -- the fibres
  have hfibsum : ∑ c, Real.exp (-(1 / 2) * δ * d (f c)) ≤ 8 * ∑ x, Real.exp (-(1 / 2) * δ * d x) := by
    rw [← Finset.sum_fiberwise Finset.univ f (fun c => Real.exp (-(1 / 2) * δ * d (f c))), Finset.mul_sum]
    refine Finset.sum_le_sum fun x _ => ?_
    have : ∑ c ∈ Finset.univ.filter (fun c => f c = x), Real.exp (-(1 / 2) * δ * d (f c)) =
        (Finset.univ.filter fun c => f c = x).card * Real.exp (-(1 / 2) * δ * d x) := by
      rw [Finset.sum_congr rfl (fun c hc => by rw [(Finset.mem_filter.1 hc).2]), Finset.sum_const,
        nsmul_eq_mul]
    rw [this]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hfib x) (Real.exp_pos _).le
  calc ∑ c, Real.exp (-δ * d (f c)) * b c
      ≤ ∑ c, Real.exp (-(1 / 2) * δ * D) * B * Real.exp (-(1 / 2) * δ * d (f c)) := Finset.sum_le_sum fun c _ => hterm c
    _ = Real.exp (-(1 / 2) * δ * D) * B * ∑ c, Real.exp (-(1 / 2) * δ * d (f c)) := by rw [Finset.mul_sum]
    _ ≤ Real.exp (-(1 / 2) * δ * D) * B * (8 * c₁) := by
        apply mul_le_mul_of_nonneg_left (hfibsum.trans (by linarith)) (by positivity)
    _ = 8 * c₁ * Real.exp (-(1 / 2) * δ * D) * B := by ring

/-- **The last line of `eq:comparison`**: `2B₆·8c₁ = 16B₆c₁`. -/
theorem comparison_bound {B₆ s c₁ e B : ℝ} (hB₆ : 0 ≤ B₆) (hs : s ≤ 8 * c₁ * e * B) :
    2 * B₆ * s ≤ 16 * B₆ * c₁ * e * B := by nlinarith

end ComparisonArith
end CoreLean

end
