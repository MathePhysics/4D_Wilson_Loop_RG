/-
`lem:background-admissible` of BALABAN_CORE.tex (`a021c13be348`), the arithmetic of its proof.

* `dS_bound`: from `(20 + 2R_W)M_w ≤ M/L` (`def:parameter-operators`(i)) and `M ≥ L³R₂M₁` with `R₁ + 2 ≤ L²R₂`:
  `d_S = (R_W + 10)M_wa_j + (R₁ + 2)M₁a_j ≤ 2Ma_j/L < 27Ma_{j-1}` with `a_j = La_{j-1}`.
* `units_shift`: the bounds of the index `j - 1` in the units of `j`: `B₃ε₁(a₀/a_{j-1})² ≤ L³B₃ε₁(a₀/a_j)²` and
  `B₃ε₁a_{j-1}⁻³ = L³B₃ε₁a_j⁻³`, for `a_j = La_{j-1}`, `L ≥ 1`.
-/
import Mathlib

noncomputable section

namespace CoreLean
namespace BackgroundAdmissibleArith

/-- **The distance `d_S`.** -/
theorem dS_bound {RW Mw R₁ R₂ M₁ M L a a' : ℝ} (hL : 1 ≤ L) (hMw : 0 ≤ Mw) (hRW : 0 ≤ RW) (hM₁ : 0 ≤ M₁)
    (ha' : 0 < a') (haa : a = L * a') (h1 : (20 + 2 * RW) * Mw ≤ M / L) (h2 : L ^ 3 * R₂ * M₁ ≤ M)
    (h3 : R₁ + 2 ≤ L ^ 2 * R₂) (hM : 0 < M) :
    (RW + 10) * Mw * a + (R₁ + 2) * M₁ * a ≤ 2 * M * a / L ∧ 2 * M * a / L < 27 * M * a' := by
  have hL0 : 0 < L := by linarith
  have ha : 0 ≤ a := by rw [haa]; positivity
  have hA : (RW + 10) * Mw ≤ M / L := by nlinarith
  have hB : (R₁ + 2) * M₁ ≤ M / L := by
    rw [le_div_iff₀ hL0]
    have : (R₁ + 2) * M₁ ≤ L ^ 2 * R₂ * M₁ := mul_le_mul_of_nonneg_right h3 hM₁
    nlinarith
  refine ⟨?_, ?_⟩
  · have : (RW + 10) * Mw * a + (R₁ + 2) * M₁ * a = ((RW + 10) * Mw + (R₁ + 2) * M₁) * a := by ring
    rw [this, show 2 * M * a / L = (M / L + M / L) * a by ring]
    exact mul_le_mul_of_nonneg_right (by linarith) ha
  · rw [haa, show 2 * M * (L * a') / L = 2 * M * a' by field_simp]
    nlinarith

/-- **The units of the index `j - 1`.** -/
theorem units_shift {B ε a₀ a a' L : ℝ} (hL : 1 ≤ L) (hBε : 0 ≤ B * ε) (ha' : 0 < a') (haa : a = L * a') :
    B * ε * (a₀ / a') ^ 2 ≤ L ^ 3 * (B * ε) * (a₀ / a) ^ 2 ∧ B * ε / a' ^ 3 = L ^ 3 * (B * ε) / a ^ 3 := by
  have hL0 : 0 < L := by linarith
  subst haa
  refine ⟨?_, by field_simp⟩
  have e : (a₀ / a') ^ 2 = L ^ 2 * (a₀ / (L * a')) ^ 2 := by field_simp
  rw [e]
  have hL3 : L ^ 2 ≤ L ^ 3 := by nlinarith
  have h0 : 0 ≤ B * ε * (a₀ / (L * a')) ^ 2 := by positivity
  nlinarith

end BackgroundAdmissibleArith
end CoreLean

end
