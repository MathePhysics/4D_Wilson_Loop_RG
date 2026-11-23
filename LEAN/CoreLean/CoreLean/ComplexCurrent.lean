/-
`lem:complex-current` of BALABAN_CORE.tex (`a021c13be348`), the inverse of the test fields at a complex
configuration, `eq:complex-test-inverse`, in abstract form. With `Q_𝐀ℱ = I + ℰ₀ + ℰ₁ + ℰ₂`, `ℰ₁² = 0`,
`‖ℰ₁‖_ψ ≤ 2C_{1b}`, `‖ℰ₀‖_ψ ≤ 2C_{0b}ε_p`, `‖ℰ₂‖_ψ ≤ C_{2b}‖𝐀‖_{∞,(-1)}`, `ε_p, ‖𝐀‖ ≤ c_cc`, and
`(2C_{0b} + C_{2b})(1 + 2C_{1b})c_cc ≤ ½`, the operator is invertible with `‖(Q_𝐀ℱ)⁻¹‖_ψ ≤ C_inv = 2(1 + 2C_{1b})`
(`complex_test_inverse`, by `test_inverse` of `CriticalCurrent.lean` with `ℰ₀ + ℰ₂` in the place of `ℰ₀`).
The constant of the columns of `ℰ₂`: `24·2L·√N·2(c''₄)⁻¹C_QC_φ·4L⁴·L ≤ C_{2b} = 400√N(c''₄)⁻¹C_QC_φL⁶`
(`constant_two`).
-/
import CoreLean.CriticalCurrent

noncomputable section

namespace CoreLean
namespace ComplexCurrent

/-- **`eq:complex-test-inverse`**. -/
theorem complex_test_inverse {R : Type*} [NormedRing R] [CompleteSpace R] [NormOneClass R] (E₀ E₁ E₂ : R)
    (hE₁ : E₁ * E₁ = 0) {C0b C1b C2b εp a c : ℝ} (h0b : 0 ≤ C0b) (h2b : 0 ≤ C2b)
    (h1 : ‖E₁‖ ≤ 2 * C1b) (h0 : ‖E₀‖ ≤ 2 * C0b * εp) (h2 : ‖E₂‖ ≤ C2b * a)
    (hεp : εp ≤ c) (ha : a ≤ c) (hsmall : (2 * C0b + C2b) * (1 + 2 * C1b) * c ≤ 1 / 2) :
    ∃ V : R, (1 + (E₀ + E₂) + E₁) * V = 1 ∧ V * (1 + (E₀ + E₂) + E₁) = 1 ∧ ‖V‖ ≤ 2 * (1 + 2 * C1b) := by
  have hX : ‖E₀ + E₂‖ ≤ (2 * C0b + C2b) * c := by
    calc ‖E₀ + E₂‖ ≤ ‖E₀‖ + ‖E₂‖ := norm_add_le _ _
      _ ≤ 2 * C0b * εp + C2b * a := add_le_add h0 h2
      _ ≤ 2 * C0b * c + C2b * c := add_le_add (mul_le_mul_of_nonneg_left hεp (by positivity))
          (mul_le_mul_of_nonneg_left ha h2b)
      _ = (2 * C0b + C2b) * c := by ring
  have := CriticalCurrent.test_inverse (E₀ + E₂) E₁ hE₁ h1 (h0 := (hX.trans_eq (by ring) :
    ‖E₀ + E₂‖ ≤ (2 * C0b + C2b) * c)) (by linarith [hsmall])
  exact this

/-- The constant `C_{2b}`. -/
theorem constant_two {N c4 CQ Cφ L : ℝ} (hN : 0 ≤ N) (hc : 0 < c4) (hQ : 0 ≤ CQ) (hφ : 0 ≤ Cφ) (hL : 0 ≤ L) :
    24 * (2 * L) * Real.sqrt N * (2 * c4⁻¹ * CQ * Cφ * (4 * L ^ 4) * L) ≤
      400 * Real.sqrt N * c4⁻¹ * CQ * Cφ * L ^ 6 := by
  have h : 0 ≤ Real.sqrt N * c4⁻¹ * CQ * Cφ * L ^ 6 := by positivity
  have e : 24 * (2 * L) * Real.sqrt N * (2 * c4⁻¹ * CQ * Cφ * (4 * L ^ 4) * L) =
      384 * (Real.sqrt N * c4⁻¹ * CQ * Cφ * L ^ 6) := by ring
  rw [e]
  nlinarith

end ComplexCurrent
end CoreLean

end
