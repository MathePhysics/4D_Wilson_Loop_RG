/-
`lem:base-gauges` of BALABAN_CORE.tex (`a021c13be348`), the arithmetic of its proof, from
`(2R₂ + 1)M₁ ≤ 3M/L` (`eq:layer-condition` with `M_c ≤ M`), `R₂ ≥ 1`, `L ≥ 3`, `10Ma_i ≤ s_□ ≤ 20Ma_i`.

* `grid_side`: `(2R₂ + 2)M₁ ≤ (4/3)(2R₂ + 1)M₁ ≤ 4M/L` and `(4R₂ + 2)M₁ ≤ 6M/L < 27M/L`.
* `same_index`: `s_□̂ ≤ s_□ + 2M₁a_i ≤ 21Ma_i ≤ 2.1s_□`, and `½·2.1 = 1.05 ≤ 2`.
* `higher_index`: `½L⁻¹·24M ≤ s_□/a_i` for `s_□ ≥ 10Ma_i`, `L ≥ 3`.
* `condition`: `24Ma·ε₁ ≤ 2a^v₁R₂M₁a` for `ε₁ ≤ a^v₁R₂M₁/(12M)`.
-/
import Mathlib

noncomputable section

namespace CoreLean
namespace BaseGaugesArith

/-- The sides of the cube of the grid. -/
theorem grid_side {R₂ M₁ M L : ℝ} (hR : 1 ≤ R₂) (hM₁ : 0 ≤ M₁) (hL : 0 < L) (hM : 0 < M)
    (h : (2 * R₂ + 1) * M₁ ≤ 3 * M / L) :
    (2 * R₂ + 2) * M₁ ≤ 4 / 3 * ((2 * R₂ + 1) * M₁) ∧ 4 / 3 * ((2 * R₂ + 1) * M₁) ≤ 4 * M / L ∧
      (4 * R₂ + 2) * M₁ ≤ 6 * M / L ∧ 6 * M / L < 27 * M / L := by
  refine ⟨by nlinarith, ?_, ?_, ?_⟩
  · have : 4 / 3 * (3 * M / L) = 4 * M / L := by ring
    linarith
  · have : (4 * R₂ + 2) * M₁ = 2 * ((2 * R₂ + 1) * M₁) := by ring
    have h2 : 2 * (3 * M / L) = 6 * M / L := by ring
    linarith
  · exact div_lt_div_of_pos_right (by linarith) hL

/-- The case `j' = i`. -/
theorem same_index {s M M₁ a : ℝ} (ha : 0 ≤ a) (hs1 : 10 * M * a ≤ s) (hs2 : s ≤ 20 * M * a) (hM₁ : 2 * M₁ ≤ M) :
    s + 2 * M₁ * a ≤ 21 * M * a ∧ 21 * M * a ≤ 2.1 * s ∧ (1 / 2 : ℝ) * 2.1 ≤ 2 := by
  refine ⟨by nlinarith, by linarith, by norm_num⟩

/-- The case `j' > i`: `½L⁻¹·24M ≤ s_□/a_i`. -/
theorem higher_index {L M s a : ℝ} (hL : 3 ≤ L) (hM : 0 ≤ M) (ha : 0 < a) (hs : 10 * M * a ≤ s) :
    1 / 2 * L⁻¹ * (24 * M) ≤ s / a := by
  have hL0 : 0 < L := by linarith
  rw [le_div_iff₀ ha]
  have h1 : 1 / 2 * L⁻¹ * (24 * M) ≤ 4 * M := by
    have : L⁻¹ ≤ 1 / 3 := by rw [inv_le_comm₀ hL0 (by norm_num)]; linarith
    nlinarith
  nlinarith

/-- `24Maε₁ ≤ 2a^v₁R₂M₁a` for `ε₁ ≤ a^v₁R₂M₁/(12M)`. -/
theorem condition {M a ε av R₂ M₁ : ℝ} (hM : 0 < M) (ha : 0 ≤ a) (hε : ε ≤ av * R₂ * M₁ / (12 * M)) :
    24 * M * a * ε ≤ 2 * av * R₂ * M₁ * a := by
  have h : ε * (12 * M) ≤ av * R₂ * M₁ := (le_div_iff₀ (by positivity)).1 hε
  nlinarith

end BaseGaugesArith
end CoreLean

end
