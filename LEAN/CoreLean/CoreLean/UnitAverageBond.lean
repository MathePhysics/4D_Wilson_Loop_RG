/-
`lem:unit-average-bond`(iii) of BALABAN_CORE.tex (`a021c13be348`), from (i) and (ii), in abstract form. Let `Z` (the
space `𝔤^c`) and `F` (the forms on the bonds of `Δ_c` with the norm `‖·‖_c`) be Banach spaces, `ι : Z → F` linear with
`‖ιz‖ ≤ 2L³‖z‖` (the form `δ_c(Lq_c)⁻¹z`, by (i)), and `𝒞 : F → Z` (the remainder `C̃(·)(c)`) with the bounds of
`eq:unit-remainder` on the ball of the radius `r₀/4`:
`‖𝒞(X)‖ ≤ 4‖X‖²/r₀²` and `‖𝒞(X) - 𝒞(X')‖ ≤ 16/r₀²·max{‖X‖, ‖X'‖}‖X - X'‖`.
With `a₇ = r₀²/(192L⁶)`, `L ≥ 1`, `0 < r₀ ≤ 1` and `‖B‖ ≤ a₇`, the map `Φ(z) = 𝒞(B - ιz)` maps the ball of the radius
`a₇` into itself with the Lipschitz constant `½` (`maps_ball`, `lipschitz_ball`), so that `z = 𝒞(B - ιz)` has exactly
one solution `D̃(B)(c)` there (`unit_fixed_point`), and `‖D̃(B)(c)‖ ≤ 16‖B‖²/r₀² = C_ul‖B‖²` (`unit_fixed_bound`).
-/
import CoreLean.FixedPointBall

noncomputable section

namespace CoreLean
namespace UnitAverageBond

variable {Z F : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

section

variable {L r₀ : ℝ} (hL : 1 ≤ L) (hr₀ : 0 < r₀) (hr₁ : r₀ ≤ 1)
  (ι : Z →L[ℝ] F) (hι : ∀ z, ‖ι z‖ ≤ 2 * L ^ 3 * ‖z‖) (𝒞 : F → Z)
  (hC : ∀ X, ‖X‖ ≤ r₀ / 4 → ‖𝒞 X‖ ≤ 4 * ‖X‖ ^ 2 / r₀ ^ 2)
  (hCL : ∀ X X', ‖X‖ ≤ r₀ / 4 → ‖X'‖ ≤ r₀ / 4 → ‖𝒞 X - 𝒞 X'‖ ≤ 16 / r₀ ^ 2 * max ‖X‖ ‖X'‖ * ‖X - X'‖)
  (B : F) (hB : ‖B‖ ≤ r₀ ^ 2 / (192 * L ^ 6))
include hL hr₀ hr₁ hι hB

/-- The arguments of `𝒞` have norms at most `3L³a₇ ≤ r₀/4`. -/
lemma arg_small {z : Z} (hz : ‖z‖ ≤ r₀ ^ 2 / (192 * L ^ 6)) :
    ‖B - ι z‖ ≤ 3 * L ^ 3 * (r₀ ^ 2 / (192 * L ^ 6)) ∧ 3 * L ^ 3 * (r₀ ^ 2 / (192 * L ^ 6)) ≤ r₀ / 4 := by
  have hL3 : 1 ≤ L ^ 3 := one_le_pow₀ hL
  have ha : 0 ≤ r₀ ^ 2 / (192 * L ^ 6) := by positivity
  constructor
  · calc ‖B - ι z‖ ≤ ‖B‖ + ‖ι z‖ := norm_sub_le _ _
      _ ≤ r₀ ^ 2 / (192 * L ^ 6) + 2 * L ^ 3 * (r₀ ^ 2 / (192 * L ^ 6)) :=
          add_le_add hB ((hι z).trans (mul_le_mul_of_nonneg_left hz (by positivity)))
      _ ≤ 3 * L ^ 3 * (r₀ ^ 2 / (192 * L ^ 6)) := by nlinarith
  · have hL0 : 0 < L := by linarith
    rw [show 3 * L ^ 3 * (r₀ ^ 2 / (192 * L ^ 6)) = r₀ ^ 2 / (64 * L ^ 3) by field_simp; ring]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [mul_le_mul_of_nonneg_left hr₁ hr₀.le]

include hC in
/-- `Φ` maps the ball of the radius `a₇` into itself. -/
theorem maps_ball {z : Z} (hz : ‖z‖ ≤ r₀ ^ 2 / (192 * L ^ 6)) :
    ‖𝒞 (B - ι z)‖ ≤ r₀ ^ 2 / (192 * L ^ 6) := by
  obtain ⟨h1, h2⟩ := arg_small hL hr₀ hr₁ ι hι B hB hz
  have hL0 : 0 < L := by linarith
  set a := r₀ ^ 2 / (192 * L ^ 6)
  have ha : 0 ≤ a := by positivity
  refine (hC _ (h1.trans h2)).trans ?_
  have h3 : ‖B - ι z‖ ^ 2 ≤ (3 * L ^ 3 * a) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  calc 4 * ‖B - ι z‖ ^ 2 / r₀ ^ 2 ≤ 4 * (3 * L ^ 3 * a) ^ 2 / r₀ ^ 2 := by gcongr
    _ = 36 * L ^ 6 * a / r₀ ^ 2 * a := by ring
    _ = 36 / 192 * a := by simp only [a]; field_simp
    _ ≤ a := by nlinarith

include hCL in
/-- `Φ` has the Lipschitz constant `½` on the ball. -/
theorem lipschitz_ball {z z' : Z} (hz : ‖z‖ ≤ r₀ ^ 2 / (192 * L ^ 6)) (hz' : ‖z'‖ ≤ r₀ ^ 2 / (192 * L ^ 6)) :
    ‖𝒞 (B - ι z) - 𝒞 (B - ι z')‖ ≤ 1 / 2 * ‖z - z'‖ := by
  obtain ⟨h1, h2⟩ := arg_small hL hr₀ hr₁ ι hι B hB hz
  obtain ⟨h1', -⟩ := arg_small hL hr₀ hr₁ ι hι B hB hz'
  have hL0 : 0 < L := by linarith
  set a := r₀ ^ 2 / (192 * L ^ 6)
  have ha : 0 ≤ a := by positivity
  refine (hCL _ _ (h1.trans h2) (h1'.trans h2)).trans ?_
  have hd : ‖(B - ι z) - (B - ι z')‖ ≤ 2 * L ^ 3 * ‖z - z'‖ := by
    rw [sub_sub_sub_cancel_left, ← map_sub, norm_sub_rev z z']
    exact hι _
  have hmax : max ‖B - ι z‖ ‖B - ι z'‖ ≤ 3 * L ^ 3 * a := max_le h1 h1'
  calc 16 / r₀ ^ 2 * max ‖B - ι z‖ ‖B - ι z'‖ * ‖(B - ι z) - (B - ι z')‖
      ≤ 16 / r₀ ^ 2 * (3 * L ^ 3 * a) * (2 * L ^ 3 * ‖z - z'‖) := by gcongr
    _ = 96 * L ^ 6 * a / r₀ ^ 2 * ‖z - z'‖ := by ring
    _ = 1 / 2 * ‖z - z'‖ := by simp only [a]; field_simp; ring

include hC hCL in
/-- **(iii)**: exactly one solution `D̃(B)(c)` in the ball of the radius `a₇`. -/
theorem unit_fixed_point : ∃! z : Z, ‖z‖ ≤ r₀ ^ 2 / (192 * L ^ 6) ∧ 𝒞 (B - ι z) = z :=
  FixedPointBall.fixed_point_ball (fun z => 𝒞 (B - ι z)) (by positivity)
    (fun z hz => maps_ball hL hr₀ hr₁ ι hι 𝒞 hC B hB hz)
    (fun z z' hz hz' => lipschitz_ball hL hr₀ hr₁ ι hι 𝒞 hCL B hB hz hz')

include hC in
/-- **The bound** `‖D̃(B)(c)‖ ≤ 16‖B‖²/r₀²`. -/
theorem unit_fixed_bound {z : Z} (hz : ‖z‖ ≤ r₀ ^ 2 / (192 * L ^ 6)) (hfix : 𝒞 (B - ι z) = z) :
    ‖z‖ ≤ 16 * ‖B‖ ^ 2 / r₀ ^ 2 := by
  obtain ⟨h1, h2⟩ := arg_small hL hr₀ hr₁ ι hι B hB hz
  have hL0 : 0 < L := by linarith
  set a := r₀ ^ 2 / (192 * L ^ 6)
  set d := ‖z‖
  have hd0 : 0 ≤ d := norm_nonneg _
  have hb0 : 0 ≤ ‖B‖ := norm_nonneg _
  -- `d ≤ 4(‖B‖ + 2L³d)²/r₀²`
  have h3 : d ≤ 4 * (‖B‖ + 2 * L ^ 3 * d) ^ 2 / r₀ ^ 2 := by
    have hn : ‖B - ι z‖ ≤ ‖B‖ + 2 * L ^ 3 * d := (norm_sub_le _ _).trans (add_le_add le_rfl (hι z))
    calc d = ‖𝒞 (B - ι z)‖ := by rw [hfix]
      _ ≤ 4 * ‖B - ι z‖ ^ 2 / r₀ ^ 2 := hC _ (h1.trans h2)
      _ ≤ 4 * (‖B‖ + 2 * L ^ 3 * d) ^ 2 / r₀ ^ 2 := by gcongr
  -- `(x + y)² ≤ 2x² + 2y²` and `y = 2L³d ≤ 2L³a`
  have h4 : (‖B‖ + 2 * L ^ 3 * d) ^ 2 ≤ 2 * ‖B‖ ^ 2 + 8 * L ^ 6 * a * d := by
    have : (2 * L ^ 3 * d) ^ 2 ≤ 4 * L ^ 6 * a * d := by
      have h7 : d * d ≤ a * d := mul_le_mul_of_nonneg_right hz hd0
      have h8 : 0 ≤ 4 * L ^ 6 := by positivity
      calc (2 * L ^ 3 * d) ^ 2 = 4 * L ^ 6 * (d * d) := by ring
        _ ≤ 4 * L ^ 6 * (a * d) := mul_le_mul_of_nonneg_left h7 h8
        _ = 4 * L ^ 6 * a * d := by ring
    nlinarith [sq_nonneg (‖B‖ - 2 * L ^ 3 * d)]
  have h5 : d ≤ 8 * ‖B‖ ^ 2 / r₀ ^ 2 + 1 / 6 * d := by
    have e : 32 * L ^ 6 * a / r₀ ^ 2 = 1 / 6 := by simp only [a]; field_simp; ring
    calc d ≤ 4 * (‖B‖ + 2 * L ^ 3 * d) ^ 2 / r₀ ^ 2 := h3
      _ ≤ 4 * (2 * ‖B‖ ^ 2 + 8 * L ^ 6 * a * d) / r₀ ^ 2 := by gcongr
      _ = 8 * ‖B‖ ^ 2 / r₀ ^ 2 + 32 * L ^ 6 * a / r₀ ^ 2 * d := by ring
      _ = 8 * ‖B‖ ^ 2 / r₀ ^ 2 + 1 / 6 * d := by rw [e]
  have h6 : 0 ≤ ‖B‖ ^ 2 / r₀ ^ 2 := by positivity
  have : 8 * ‖B‖ ^ 2 / r₀ ^ 2 = 8 * (‖B‖ ^ 2 / r₀ ^ 2) := by ring
  have : 16 * ‖B‖ ^ 2 / r₀ ^ 2 = 16 * (‖B‖ ^ 2 / r₀ ^ 2) := by ring
  linarith

end

end UnitAverageBond
end CoreLean

end
