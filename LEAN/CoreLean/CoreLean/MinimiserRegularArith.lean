/-
`cor:minimiser-regular` of BALABAN_CORE.tex (`a021c13be348`), the arithmetic of its proof, with `m = 2R₂M₁`,
`M ≥ LR₂M₁`, `R₂ ≥ 1`, `L ≥ 1`, `10Ma_j ≤ s ≤ 20Ma_j`, `40Mε₁ ≤ a^v₁R₂M₁`.

* `m_bound`: `m ≤ 2M/L` and `ma_j ≤ 2Ma_{j-1}` for `a_j = La_{j-1}`.
* `first_case`: `s ≥ ma_j` and `sε₁ ≤ 20Mε₁a_j ≤ 2a^v₁R₂M₁a_j`.
* `second_case_side`: `s' ≤ s + (2M/L)a_j + 2M₁La_j ≤ s + 4Ma_j ≤ (7/5)s`, `s' ≤ 24Ma_j`, and
  `10Ma_j ≥ 10LR₂M₁a_j = 5m(La_j)`.
* `second_case_condition`: `24(M/L)ε₁ ≤ 2a^v₁R₂M₁` (the second condition of `eq:minimiser-cube` at `j + 1`).
* `ratio`: `½(7/5)L^{-1-p} ≤ (7/10)L⁻² ≤ 1` for `p ≥ 1`.
-/
import Mathlib

noncomputable section

namespace CoreLean
namespace MinimiserRegularArith

/-- `m = 2R₂M₁ ≤ 2M/L`, `ma_j ≤ 2Ma_{j-1}`. -/
theorem m_bound {R₂ M₁ M L a' : ℝ} (hL : 0 < L) (ha : 0 ≤ a') (h : L * R₂ * M₁ ≤ M) :
    2 * R₂ * M₁ ≤ 2 * M / L ∧ 2 * R₂ * M₁ * (L * a') ≤ 2 * M * a' := by
  refine ⟨?_, ?_⟩
  · rw [le_div_iff₀ hL]; nlinarith
  · have : 2 * R₂ * M₁ * (L * a') = 2 * (L * R₂ * M₁) * a' := by ring
    rw [this]; nlinarith

/-- The first case. -/
theorem first_case {s M a m ε av R₂ M₁ : ℝ} (ha : 0 ≤ a) (hε : 0 ≤ ε) (hm : m ≤ M) (hM : 0 ≤ M)
    (hs1 : 10 * M * a ≤ s) (hs2 : s ≤ 20 * M * a) (hcond : 40 * M * ε ≤ av * R₂ * M₁) :
    m * a ≤ s ∧ s * ε ≤ 2 * av * R₂ * M₁ * a := by
  refine ⟨by nlinarith, ?_⟩
  have h1 : s * ε ≤ 20 * M * a * ε := mul_le_mul_of_nonneg_right hs2 hε
  nlinarith

/-- The side of `□'` in the second case. -/
theorem second_case_side {s s' M M₁ L R₂ a : ℝ} (hL : 1 ≤ L) (ha : 0 ≤ a) (hR : 1 ≤ R₂) (hM₁ : 0 ≤ M₁)
    (h : L * R₂ * M₁ ≤ M) (hs1 : 10 * M * a ≤ s) (hs2 : s ≤ 20 * M * a)
    (hs' : s' ≤ s + 2 * M / L * a + 2 * M₁ * L * a) :
    s' ≤ s + 4 * M * a ∧ s + 4 * M * a ≤ 7 / 5 * s ∧ s' ≤ 24 * M * a ∧
      10 * L * R₂ * M₁ * a = 5 * (2 * R₂ * M₁) * (L * a) := by
  have hL0 : 0 < L := by linarith
  have hM0 : 0 ≤ M := le_trans (by positivity) h
  have h1 : 2 * M / L ≤ 2 * M := div_le_self (by linarith) hL
  have h2 : M₁ * L ≤ M := by nlinarith
  have h3 : 2 * M / L * a + 2 * M₁ * L * a ≤ 4 * M * a := by
    have : 2 * M / L * a ≤ 2 * M * a := mul_le_mul_of_nonneg_right h1 ha
    have : 2 * M₁ * L * a ≤ 2 * M * a := by nlinarith
    linarith
  refine ⟨by linarith, by linarith, by linarith, by ring⟩

/-- The second condition at the index `j + 1`: `24(M/L)ε₁ ≤ 2a^v₁R₂M₁`. -/
theorem second_case_condition {M L ε av R₂ M₁ : ℝ} (hL : 1 ≤ L) (hM : 0 ≤ M) (hε : 0 ≤ ε)
    (hcond : 40 * M * ε ≤ av * R₂ * M₁) : 24 * (M / L) * ε ≤ 2 * av * R₂ * M₁ := by
  have h1 : M / L ≤ M := div_le_self hM hL
  have h2 : 24 * (M / L) * ε ≤ 24 * M * ε := by
    have := mul_le_mul_of_nonneg_right h1 hε; nlinarith
  nlinarith

/-- **The ratio of the bounds**: `½(7/5)L^{-1-p} ≤ (7/10)L⁻² ≤ 1` for `p ≥ 1`, `L ≥ 1`. -/
theorem ratio {L : ℝ} (p : ℕ) (hp : 1 ≤ p) (hL : 1 ≤ L) :
    1 / 2 * (7 / 5) * (L ^ (1 + p))⁻¹ ≤ 7 / 10 * (L ^ 2)⁻¹ ∧ 7 / 10 * (L ^ 2)⁻¹ ≤ 1 := by
  have hL0 : 0 < L := by linarith
  have h1 : L ^ 2 ≤ L ^ (1 + p) := pow_le_pow_right₀ hL (by omega)
  have h2 : (L ^ (1 + p))⁻¹ ≤ (L ^ 2)⁻¹ := inv_anti₀ (by positivity) h1
  have h3 : (L ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hL)
  refine ⟨by nlinarith, by nlinarith⟩

end MinimiserRegularArith
end CoreLean

end
