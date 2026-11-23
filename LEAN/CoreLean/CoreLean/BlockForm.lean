/-
`prop:block-form` of BALABAN_CORE.tex (`a021c13be348`), the conclusion of its proof in abstract form. With `Δ_𝖺`
symmetric and positive semidefinite on a real inner product space (the `1`-forms with values in `𝔤`,
`thm:propagators`(i)), `G` a right inverse of it, `x = Q^*μ`, and a test field `f` with `⟨x, f⟩ ≥ 𝗆/2`
(`eq:test-field`) and `⟨f, Δ_𝖺f⟩ ≤ C_⋆𝗆` (the energy of the test field), the inequality
`0 ≤ ⟨tf - Gx, Δ_𝖺(tf - Gx)⟩` at `t = (2C_⋆)⁻¹` gives `⟨x, Gx⟩ ≥ 𝗆/(4C_⋆)`, which is `eq:block-form-lower` with
`γ_b = (4C_⋆)⁻¹` (`block_form_lower`). The arithmetic of the energy, `(6·128 + 2)C_φ²(1 + C_{1b})² + 9/4 ≤ 2¹⁰C_φ²(1 + C_{1b})²`
for `C_φ ≥ 1` (`energy_constant`), is the core's.
-/
import Mathlib

open scoped InnerProductSpace

noncomputable section

namespace CoreLean
namespace BlockForm

/-- **`eq:block-form-lower`** from the test field. -/
theorem block_form_lower {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (Δ G : H →L[ℝ] H)
    (hΔG : ∀ y, Δ (G y) = y) (hsym : ∀ u v, ⟪u, Δ v⟫_ℝ = ⟪Δ u, v⟫_ℝ) (hpos : ∀ u, 0 ≤ ⟪u, Δ u⟫_ℝ)
    (x f : H) {m C : ℝ} (hC : 0 < C) (hxf : m / 2 ≤ ⟪x, f⟫_ℝ) (hff : ⟪f, Δ f⟫_ℝ ≤ C * m) :
    m / (4 * C) ≤ ⟪x, G x⟫_ℝ := by
  set g := G x
  have hg : Δ g = x := hΔG x
  set t := 1 / (2 * C)
  have ht : 0 < t := by positivity
  have h0 := hpos (t • f - g)
  have e : ⟪t • f - g, Δ (t • f - g)⟫_ℝ = t ^ 2 * ⟪f, Δ f⟫_ℝ - 2 * t * ⟪x, f⟫_ℝ + ⟪x, g⟫_ℝ := by
    have h1 : ⟪g, Δ f⟫_ℝ = ⟪x, f⟫_ℝ := by rw [hsym, hg]
    have h2 : ⟪f, Δ g⟫_ℝ = ⟪x, f⟫_ℝ := by rw [hg, real_inner_comm]
    have h3 : ⟪g, Δ g⟫_ℝ = ⟪x, g⟫_ℝ := by rw [hg, real_inner_comm]
    simp only [map_sub, map_smul, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
      RCLike.conj_to_real, h1, h2, h3]
    ring
  rw [e] at h0
  have hm : 0 ≤ m := by
    have := hpos f
    nlinarith [hpos f]
  have h4 : t ^ 2 * ⟪f, Δ f⟫_ℝ ≤ t ^ 2 * (C * m) := mul_le_mul_of_nonneg_left hff (by positivity)
  have h5 : 2 * t * (m / 2) ≤ 2 * t * ⟪x, f⟫_ℝ := mul_le_mul_of_nonneg_left hxf (by positivity)
  have h6 : t ^ 2 * (C * m) = m / (4 * C) := by simp only [t]; field_simp; ring
  have h7 : 2 * t * (m / 2) = m / (2 * C) := by simp only [t]; field_simp
  have h8 : m / (2 * C) - m / (4 * C) = m / (4 * C) := by field_simp; ring
  linarith

/-- The energy constant: `(6·128 + 2)C_φ²(1 + C_{1b})² + 9/4 ≤ 2¹⁰C_φ²(1 + C_{1b})²` for `C_φ ≥ 1`, `C_{1b} ≥ 0`. -/
theorem energy_constant {Cφ C1 : ℝ} (hφ : 1 ≤ Cφ) (h1 : 0 ≤ C1) :
    (6 * 128 + 2) * Cφ ^ 2 * (1 + C1) ^ 2 + 9 / 4 ≤ 2 ^ 10 * Cφ ^ 2 * (1 + C1) ^ 2 := by
  have : 1 ≤ Cφ ^ 2 * (1 + C1) ^ 2 := by
    have h2 : 1 ≤ Cφ ^ 2 := by nlinarith
    have h3 : 1 ≤ (1 + C1) ^ 2 := by nlinarith
    nlinarith
  nlinarith

end BlockForm
end CoreLean

end
