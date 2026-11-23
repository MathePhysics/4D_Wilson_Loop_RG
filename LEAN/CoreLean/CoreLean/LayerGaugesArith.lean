/-
`lem:layer-gauges` of BALABAN_CORE.tex (`a021c13be348`), the arithmetic of its proof, from `M_c ≥ LR₂M₁`,
`M ≥ L²M_c`, `R₂ ≥ 1`, `L ≥ 3`, `s_□ ≤ 20Ma_i`, `ε₁ = 2L²α`.

* `hat_side`: `ŝ = s_□ + 4M_ca_i/L ≤ 22Ma_i`, and `ŝε₁ ≤ 22Ma_iε₁ ≤ 2a^v₁R₂M₁a_i` for `2L²α ≤ a^v₁R₂M₁/(11M)`.
* `cube_distances`: `(2R₂ + 2)M₁ ≤ 4M_c/L`, `(4R₂ + 2)M₁ ≤ 6M_c/L`, and `27M_c/M₁ ≥ R₂`.
* `inner_distance`: `(4 - 6/L)M_ca_i ≥ 4M_ca_{i-1}` with `a_i = La_{i-1}`.
-/
import Mathlib

noncomputable section

namespace CoreLean
namespace LayerGaugesArith

/-- The side `ŝ` and the condition of `thm:minimiser`(iii). -/
theorem hat_side {s M Mc L a ε av R₂ M₁ : ℝ} (hL : 3 ≤ L) (ha : 0 ≤ a) (hMc : 0 ≤ Mc) (hMMc : L ^ 2 * Mc ≤ M)
    (hs : s ≤ 20 * M * a) (hε0 : 0 ≤ ε) (hM : 0 < M) (hε : ε ≤ av * R₂ * M₁ / (11 * M)) :
    s + 4 * Mc * a / L ≤ 22 * M * a ∧ 22 * M * a * ε ≤ 2 * av * R₂ * M₁ * a := by
  have hL0 : 0 < L := by linarith
  have h1 : 4 * Mc / L ≤ 2 * M := by
    rw [div_le_iff₀ hL0]
    have hL2 : 9 ≤ L ^ 2 := by nlinarith
    have h9 : 9 * Mc ≤ M := le_trans (mul_le_mul_of_nonneg_right hL2 hMc) hMMc
    have hML : M ≤ M * L := le_mul_of_one_le_right hM.le (by linarith)
    linarith
  refine ⟨?_, ?_⟩
  · have : 4 * Mc * a / L = 4 * Mc / L * a := by ring
    rw [this]
    nlinarith
  · have h2 : ε * (11 * M) ≤ av * R₂ * M₁ := (le_div_iff₀ (by positivity)).1 hε
    nlinarith

/-- The distances of the cube `□̂`. -/
theorem cube_distances {L R₂ M₁ Mc : ℝ} (hL : 0 < L) (hL1 : 1 ≤ L) (hR : 1 ≤ R₂) (hM₁ : 0 < M₁) (h : L * R₂ * M₁ ≤ Mc) :
    (2 * R₂ + 2) * M₁ ≤ 4 * Mc / L ∧ (4 * R₂ + 2) * M₁ ≤ 6 * Mc / L ∧ R₂ ≤ 27 * Mc / M₁ := by
  have hRM : 0 ≤ R₂ * M₁ := by positivity
  have e : L * R₂ * M₁ = L * (R₂ * M₁) := by ring
  refine ⟨?_, ?_, ?_⟩
  · rw [le_div_iff₀ hL]
    have h1 : (2 * R₂ + 2) * M₁ ≤ 4 * (R₂ * M₁) := by nlinarith
    have h2 : (2 * R₂ + 2) * M₁ * L ≤ 4 * (R₂ * M₁) * L := mul_le_mul_of_nonneg_right h1 hL.le
    nlinarith
  · rw [le_div_iff₀ hL]
    have h1 : (4 * R₂ + 2) * M₁ ≤ 6 * (R₂ * M₁) := by nlinarith
    have h2 : (4 * R₂ + 2) * M₁ * L ≤ 6 * (R₂ * M₁) * L := mul_le_mul_of_nonneg_right h1 hL.le
    nlinarith
  · rw [le_div_iff₀ hM₁]
    have h1 : R₂ * M₁ ≤ L * (R₂ * M₁) := le_mul_of_one_le_left hRM hL1
    have h2 : 0 ≤ Mc := le_trans (mul_nonneg hL.le hRM) (e ▸ h)
    nlinarith

/-- `(4 - 6/L)M_ca_i ≥ 4M_ca_{i-1}` for `a_i = La_{i-1}`, `L ≥ 3`. -/
theorem inner_distance {L Mc a' : ℝ} (hL : 3 ≤ L) (hMc : 0 ≤ Mc) (ha : 0 ≤ a') :
    4 * Mc * a' ≤ (4 - 6 / L) * Mc * (L * a') := by
  have hL0 : 0 < L := by linarith
  have e : (4 - 6 / L) * Mc * (L * a') = (4 * L - 6) * (Mc * a') := by field_simp
  rw [e]
  have : 4 ≤ 4 * L - 6 := by linarith
  have h0 : 0 ≤ Mc * a' := mul_nonneg hMc ha
  nlinarith

end LayerGaugesArith
end CoreLean

end
