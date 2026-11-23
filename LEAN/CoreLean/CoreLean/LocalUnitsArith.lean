/-
`lem:local-units` of BALABAN_CORE.tex (`a021c13be348`), two steps of its proof.

* `cube_le_w`: (i), `c_cube = min{c_sf, c_rs/(18L²), (5120√N)⁻¹} ≤ c_w = min{c_sf, c''₄/(3L²)}`, from
  `c_rs ≤ c''₄L⁻²` (the definition of `c_rs` in `lem:regular-setting`): `c_rs/(18L²) ≤ c''₄/(18L⁴) ≤ c''₄/(3L²)`.
* `leibniz_bound`: (ii), the difference of `h²u` along a bond with the transport `T` (`‖T‖ ≤ 1` on the fields
  considered): `(h²u)(x + e)` transported minus `(h²u)(x)` is `h²(x + e)(Tu(x + e) - u(x)) + (h²(x + e) - h²(x))u(x)`,
  so its norm is at most `‖Tu(x + e) - u(x)‖ + |Δh²|‖u(x)‖` for `0 ≤ h² ≤ 1`.
-/
import Mathlib

noncomputable section

namespace CoreLean
namespace LocalUnitsArith

/-- (i): `c_cube ≤ c_w`. -/
theorem cube_le_w {csf crs c₄ L N : ℝ} (hL : 1 ≤ L) (hc₄ : 0 ≤ c₄) (hrs : crs ≤ c₄ / L ^ 2) :
    min csf (min (crs / (18 * L ^ 2)) (1 / (5120 * Real.sqrt N))) ≤ min csf (c₄ / (3 * L ^ 2)) := by
  apply min_le_min le_rfl
  refine (min_le_left _ _).trans ?_
  have hL2 : 0 < L ^ 2 := by positivity
  have h18 : 0 < 18 * L ^ 2 := by positivity
  calc crs / (18 * L ^ 2) ≤ c₄ / L ^ 2 / (18 * L ^ 2) := div_le_div_of_nonneg_right hrs h18.le
    _ = c₄ / (18 * L ^ 4) := by field_simp
    _ ≤ c₄ / (3 * L ^ 2) := by
        apply div_le_div_of_nonneg_left hc₄ (by positivity)
        have h1 : 1 ≤ L ^ 2 := by nlinarith
        have : L ^ 4 = L ^ 2 * L ^ 2 := by ring
        nlinarith

/-- (ii): the Leibniz rule for `h²u` along a bond. -/
theorem leibniz_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (T : E →L[ℝ] E) (u₁ u₀ : E)
    {h₁ h₀ : ℝ} (h₁0 : 0 ≤ h₁) (h₁1 : h₁ ≤ 1) :
    ‖T (h₁ • u₁) - h₀ • u₀‖ ≤ ‖T u₁ - u₀‖ + |h₁ - h₀| * ‖u₀‖ := by
  have e : T (h₁ • u₁) - h₀ • u₀ = h₁ • (T u₁ - u₀) + (h₁ - h₀) • u₀ := by
    rw [map_smul, smul_sub, sub_smul]; abel
  rw [e]
  calc ‖h₁ • (T u₁ - u₀) + (h₁ - h₀) • u₀‖ ≤ ‖h₁ • (T u₁ - u₀)‖ + ‖(h₁ - h₀) • u₀‖ := norm_add_le _ _
    _ = |h₁| * ‖T u₁ - u₀‖ + |h₁ - h₀| * ‖u₀‖ := by rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ ‖T u₁ - u₀‖ + |h₁ - h₀| * ‖u₀‖ := by
        rw [abs_of_nonneg h₁0]
        have := mul_le_mul_of_nonneg_right h₁1 (norm_nonneg (T u₁ - u₀))
        linarith

end LocalUnitsArith
end CoreLean

end
