/-
`cor:test-field`(ii) of BALABAN_CORE.tex (`a021c13be348`), in abstract form. On the functions on `𝐁₁` with the norm
`‖·‖₂` (a real inner product space `H`), with the scaled data `μ̂(c) = a_c³μ(c)`, `𝗆 = ‖μ̂‖²`, and the operators
`𝓔₀`, `𝓔̌₁` of `lem:function-field` with `‖𝓔₀‖ ≤ C₀ε`, `‖𝓔̌₁‖ ≤ C₁`, `C₀(1 + C₁)ε ≤ 1/2`: since `𝓔₁² = 0`, the averages of
the test field are `Qf = ν + 𝓔₀(I - 𝓔₁)ν`, and (`test_field_ii`)
`⟨μ̂, μ̂ + 𝓔₀(I - 𝓔̌₁)μ̂⟩ ≥ 𝗆/2`, `‖(I - 𝓔̌₁)μ̂‖ ≤ (1 + C₁)‖μ̂‖`, `‖μ̂ + 𝓔₀(I - 𝓔̌₁)μ̂‖ ≤ (3/2)‖μ̂‖`, the three bounds of
`eq:test-field`. The identity `(I + 𝓔₀ + 𝓔₁)(I - 𝓔₁) = I + 𝓔₀(I - 𝓔₁)` is `averages_of_test_field`.
-/
import Mathlib

open scoped InnerProductSpace

noncomputable section

namespace CoreLean
namespace TestField

/-- `(I + 𝓔₀ + 𝓔₁)(I - 𝓔₁) = I + 𝓔₀(I - 𝓔₁)` when `𝓔₁² = 0`. -/
theorem averages_of_test_field {R : Type*} [Ring R] (E₀ E₁ : R) (h : E₁ * E₁ = 0) :
    (1 + E₀ + E₁) * (1 - E₁) = 1 + E₀ * (1 - E₁) := by
  calc (1 + E₀ + E₁) * (1 - E₁) = 1 + E₀ * (1 - E₁) - E₁ * E₁ := by noncomm_ring
    _ = 1 + E₀ * (1 - E₁) := by rw [h, sub_zero]

/-- **`eq:test-field`** in abstract form. -/
theorem test_field_ii {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (E₀ E₁ : H →L[ℝ] H)
    {C₀ C₁ ε : ℝ} (h0 : ‖E₀‖ ≤ C₀ * ε) (h1 : ‖E₁‖ ≤ C₁) (hsmall : C₀ * (1 + C₁) * ε ≤ 1 / 2) (x : H) :
    ‖x‖ ^ 2 / 2 ≤ ⟪x, x + E₀ ((1 - E₁) x)⟫_ℝ ∧ ‖(1 - E₁) x‖ ≤ (1 + C₁) * ‖x‖ ∧
      ‖x + E₀ ((1 - E₁) x)‖ ≤ 3 / 2 * ‖x‖ := by
  have hC₁ : 0 ≤ C₁ := (norm_nonneg _).trans h1
  have hC0ε : 0 ≤ C₀ * ε := (norm_nonneg _).trans h0
  have hb1 : ‖(1 - E₁) x‖ ≤ (1 + C₁) * ‖x‖ := by
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply]
    calc ‖x - E₁ x‖ ≤ ‖x‖ + ‖E₁ x‖ := norm_sub_le _ _
      _ ≤ ‖x‖ + C₁ * ‖x‖ := add_le_add_right ((E₁.le_opNorm x).trans
          (mul_le_mul_of_nonneg_right h1 (norm_nonneg _))) _
      _ = (1 + C₁) * ‖x‖ := by ring
  have hb0 : ‖E₀ ((1 - E₁) x)‖ ≤ ‖x‖ / 2 := by
    calc ‖E₀ ((1 - E₁) x)‖ ≤ ‖E₀‖ * ‖(1 - E₁) x‖ := E₀.le_opNorm _
      _ ≤ C₀ * ε * ((1 + C₁) * ‖x‖) := mul_le_mul h0 hb1 (norm_nonneg _) hC0ε
      _ = C₀ * (1 + C₁) * ε * ‖x‖ := by ring
      _ ≤ 1 / 2 * ‖x‖ := mul_le_mul_of_nonneg_right hsmall (norm_nonneg _)
      _ = ‖x‖ / 2 := by ring
  refine ⟨?_, hb1, ?_⟩
  · rw [inner_add_right, real_inner_self_eq_norm_sq]
    have := abs_real_inner_le_norm x (E₀ ((1 - E₁) x))
    have h2 : ‖x‖ * ‖E₀ ((1 - E₁) x)‖ ≤ ‖x‖ * (‖x‖ / 2) := mul_le_mul_of_nonneg_left hb0 (norm_nonneg _)
    have h3 := neg_abs_le (⟪x, E₀ ((1 - E₁) x)⟫_ℝ)
    nlinarith
  · calc ‖x + E₀ ((1 - E₁) x)‖ ≤ ‖x‖ + ‖E₀ ((1 - E₁) x)‖ := norm_add_le _ _
      _ ≤ ‖x‖ + ‖x‖ / 2 := add_le_add_right hb0 _
      _ = 3 / 2 * ‖x‖ := by ring

end TestField
end CoreLean

end
