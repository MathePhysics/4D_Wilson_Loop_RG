/-
`lem:base-setting` and `lem:cube-setting` of BALABAN_CORE.tex (`a021c13be348`), the arithmetic of their proofs.

`lem:base-setting`:
* `separation_ge`: the separation `RM/M₁ ≥ 6LR₁ ≥ R₁` for `RM ≥ 6LR₁M₁`.
* `extension_inside`: `5R₁M₁a_j < RMa_{j-1}` (`a_{j-1} = La_j`), so that the extended cube lies in `Ω_{j-1}`.
* `cube_side`: the side `M'a_j ≤ s_C + 2M₁a_j` of the smallest cube of the grid containing `C`, with
  `10M₁a_j ≤ s_C ≤ 20LM₁a_j`, gives `M' ≤ (20L + 2R₁)M₁ ≤ (20L + 3R₁)M₁` and `M' ≤ (1 + R₁/5)s_C/a_j`.
* `product_ge`: `6LR₁M₁ ≥ 4L²` for `R₁ ≥ 21L`, `M₁ ≥ 10`.
* `set_smallness`: `α + α₁ ≤ c_set` gives `(20L + 3R₁)M₁L³α ≤ c'₅` and `30NL³M₁C_reg α + α₁ ≤ c_rs`.

`lem:cube-setting`:
* `cube_scaling`: `a_n ≤ La_j` turns `a_j‖B‖ ≤ 9s`, `a_j²‖∇B‖ ≤ 18s` into `a_n‖B'‖ ≤ 9Ls`, `a_n²‖∇B'‖ ≤ 18L²s`.
* `cube_smallness`: `α + α₁ ≤ c_cube ≤ c_rs/(18L²)` gives `30NL³M_sf·0 + 18L²(α + α₁) ≤ c_rs`.
-/
import Mathlib

noncomputable section

namespace CoreLean
namespace BaseSetting

/-- The separation `RM/M₁ ≥ 6LR₁ ≥ R₁`. -/
theorem separation_ge {R M M₁ L R₁ : ℝ} (hM₁ : 0 < M₁) (hL : 1 ≤ L) (hR₁ : 0 ≤ R₁)
    (h : 6 * L * R₁ * M₁ ≤ R * M) : 6 * L * R₁ ≤ R * M / M₁ ∧ R₁ ≤ 6 * L * R₁ := by
  refine ⟨(le_div_iff₀ hM₁).2 h, ?_⟩
  nlinarith

/-- `5R₁M₁a_j < RMa_{j-1}` with `a_{j-1} = La_j`. -/
theorem extension_inside {R M M₁ L R₁ a : ℝ} (ha : 0 < a) (hM₁ : 0 < M₁) (hL : 1 ≤ L) (hR₁ : 0 < R₁)
    (h : 6 * L * R₁ * M₁ ≤ R * M) : 5 * R₁ * M₁ * a < R * M * (L * a) := by
  have h1 : 5 * R₁ * M₁ < 6 * L * R₁ * M₁ := by nlinarith [mul_pos hR₁ hM₁]
  have h2 : 6 * L * R₁ * M₁ * L ≤ R * M * L := mul_le_mul_of_nonneg_right h (by linarith)
  have h3 : 6 * L * R₁ * M₁ ≤ 6 * L * R₁ * M₁ * L := le_mul_of_one_le_right (by positivity) hL
  have : 5 * R₁ * M₁ < R * M * L := by linarith
  calc 5 * R₁ * M₁ * a < R * M * L * a := mul_lt_mul_of_pos_right this ha
    _ = R * M * (L * a) := by ring

/-- **The side of the cube**: from `M' ≤ s + 2M₁` with `10M₁ ≤ s ≤ 20LM₁` (in units of `a_j`) and `R₁ ≥ 1`,
`M' ≤ (20L + 2R₁)M₁ ≤ (20L + 3R₁)M₁` and `M' ≤ (1 + R₁/5)s`. -/
theorem cube_side {M' s M₁ L R₁ : ℝ} (hM₁ : 0 ≤ M₁) (hR₁ : 1 ≤ R₁) (hs1 : 10 * M₁ ≤ s) (hs2 : s ≤ 20 * L * M₁)
    (hM' : M' ≤ s + 2 * M₁) :
    M' ≤ (20 * L + 2 * R₁) * M₁ ∧ (20 * L + 2 * R₁) * M₁ ≤ (20 * L + 3 * R₁) * M₁ ∧ M' ≤ (1 + R₁ / 5) * s := by
  refine ⟨?_, ?_, ?_⟩
  · have : 2 * M₁ ≤ 2 * R₁ * M₁ := by nlinarith
    nlinarith
  · nlinarith
  · have : 2 * M₁ ≤ R₁ / 5 * s := by
      have : 2 * M₁ ≤ R₁ / 5 * (10 * M₁) := by nlinarith
      exact this.trans (mul_le_mul_of_nonneg_left hs1 (by positivity))
    nlinarith

/-- `6LR₁M₁ ≥ 4L²` for `R₁ ≥ 21L`, `M₁ ≥ 10`, `L ≥ 0`. -/
theorem product_ge {L R₁ M₁ : ℝ} (hL : 0 ≤ L) (hR : 21 * L ≤ R₁) (hM : 10 ≤ M₁) : 4 * L ^ 2 ≤ 6 * L * R₁ * M₁ := by
  have h1 : 6 * L * (21 * L) ≤ 6 * L * R₁ := mul_le_mul_of_nonneg_left hR (by positivity)
  have hR0 : 0 ≤ R₁ := (by positivity : (0 : ℝ) ≤ 21 * L).trans hR
  have h2 : 6 * L * R₁ * 1 ≤ 6 * L * R₁ * M₁ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  nlinarith

/-- **The smallness of `lem:base-setting`**: `α + α₁ ≤ c_set` gives the two conditions. -/
theorem set_smallness {α α₁ K₁ K₂ c₅ crs : ℝ} (hα : 0 ≤ α) (hα₁ : 0 ≤ α₁) (hK₁ : 0 < K₁) (hK₂ : 0 ≤ K₂)
    (h : α + α₁ ≤ min (c₅ / K₁) (crs / (1 + K₂))) : K₁ * α ≤ c₅ ∧ K₂ * α + α₁ ≤ crs := by
  have h1 : α + α₁ ≤ c₅ / K₁ := h.trans (min_le_left _ _)
  have h2 : α + α₁ ≤ crs / (1 + K₂) := h.trans (min_le_right _ _)
  refine ⟨?_, ?_⟩
  · have : α ≤ c₅ / K₁ := by linarith
    rwa [le_div_iff₀ hK₁, mul_comm] at this
  · have hp : 0 < 1 + K₂ := by linarith
    have : (1 + K₂) * (α + α₁) ≤ crs := by rw [mul_comm]; exact (le_div_iff₀ hp).1 h2
    nlinarith

/-- **The scaling of `lem:cube-setting`**: `a_n ≤ La_j` turns the bounds at the scale `j` into those at `n`. -/
theorem cube_scaling {an aj L nB nD s : ℝ} (hL0 : 0 ≤ L) (han0 : 0 ≤ an) (han : an ≤ L * aj) (hB : 0 ≤ nB)
    (hD : 0 ≤ nD) (h1 : aj * nB ≤ 9 * s) (h2 : aj ^ 2 * nD ≤ 18 * s) :
    an * nB ≤ 9 * L * s ∧ an ^ 2 * nD ≤ 18 * L ^ 2 * s := by
  refine ⟨?_, ?_⟩
  · calc an * nB ≤ L * aj * nB := mul_le_mul_of_nonneg_right han hB
      _ = L * (aj * nB) := by ring
      _ ≤ L * (9 * s) := mul_le_mul_of_nonneg_left h1 hL0
      _ = 9 * L * s := by ring
  · have hsq : an ^ 2 ≤ (L * aj) ^ 2 := pow_le_pow_left₀ han0 han 2
    calc an ^ 2 * nD ≤ (L * aj) ^ 2 * nD := mul_le_mul_of_nonneg_right hsq hD
      _ = L ^ 2 * (aj ^ 2 * nD) := by ring
      _ ≤ L ^ 2 * (18 * s) := mul_le_mul_of_nonneg_left h2 (sq_nonneg L)
      _ = 18 * L ^ 2 * s := by ring

/-- **The smallness of `lem:cube-setting`**: `30NL³M_sf·0 + 18L²(α + α₁) ≤ c_rs`. -/
theorem cube_smallness {N L Msf α α₁ crs csf c₃ : ℝ} (hL : 0 < L)
    (h : α + α₁ ≤ min csf (min (crs / (18 * L ^ 2)) c₃)) :
    30 * N * L ^ 3 * Msf * 0 + 18 * L ^ 2 * (α + α₁) ≤ crs := by
  have h1 : α + α₁ ≤ crs / (18 * L ^ 2) := h.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hp : 0 < 18 * L ^ 2 := by positivity
  rw [mul_zero, zero_add, mul_comm]
  exact (le_div_iff₀ hp).1 h1

end BaseSetting
end CoreLean

end
