/-
`prop:cube-gauge` of BALABAN_CORE.tex (`a021c13be348`), the estimates of its proof.

* `kappa_le_two`: `4s₀α'₁/a_{n+1} = 48Mα'₁/L` for `s₀ = 12Ma_{n+1}/L`, and `κ = e^{48Mα'₁/L} ≤ 2` for
  `48Mα'₁/L ≤ log 2`.
* `norm_inv_sub_one_le`: in a complete normed ring with `‖1‖ = 1`, `‖Y - 1‖ ≤ ½` gives `Y` invertible with
  `‖Y⁻¹‖ ≤ 2` and `‖Y⁻¹ - 1‖ ≤ 2‖Y - 1‖`.
* `factor_bound`: `‖γ(P^{±1} - 1)γ⁻¹‖ ≤ κ²·2‖P - 1‖ ≤ 8√Nα` for `κ ≤ 2`, `‖P - 1‖ ≤ √Nα`.
* `contour_constant`: `2·(2s₀/a₀)·8√Nα'₀(a₀/a)² · 2 = (768√N/L)Mα'₀·(a₀/a)` for `s₀ = 12Ma/L`.
* `neg_log_le`: `-log(1 - x) ≤ 2x` for `0 ≤ x ≤ ½`, hence `a_{n+1}‖X‖ ≤ 2·384√NMα'₀/L`.
* `ad_bound`: for `δ ≤ ½`, `(1 - δ)⁻¹ ≤ 1 + 2δ` and `(1 + 2δ)² ≤ e^{4δ}`.
-/
import Mathlib

noncomputable section

namespace CoreLean
namespace CubeGaugeArith

/-- `4s₀α'₁/a = 48Mα'₁/L` and `e^{48Mα'₁/L} ≤ 2`. -/
theorem kappa_le_two {M L a α : ℝ} (hL : 0 < L) (ha : 0 < a) (h : 48 * M * α / L ≤ Real.log 2) :
    4 * (12 * M * a / L) * α / a = 48 * M * α / L ∧ Real.exp (48 * M * α / L) ≤ 2 := by
  refine ⟨by field_simp; ring, ?_⟩
  calc Real.exp (48 * M * α / L) ≤ Real.exp (Real.log 2) := Real.exp_le_exp.2 h
    _ = 2 := Real.exp_log (by norm_num)

/-- **`‖Y⁻¹ - 1‖ ≤ 2‖Y - 1‖`** for `‖Y - 1‖ ≤ ½`. -/
theorem norm_inv_sub_one_le {R : Type*} [NormedRing R] [NormOneClass R] [CompleteSpace R] (Y : R)
    (hY : ‖Y - 1‖ ≤ 1 / 2) :
    IsUnit Y ∧ ‖Ring.inverse Y‖ ≤ 2 ∧ ‖Ring.inverse Y - 1‖ ≤ 2 * ‖Y - 1‖ := by
  have ht : ‖1 - Y‖ < 1 := by rw [norm_sub_rev]; linarith
  have hu : IsUnit Y := by
    have := (Units.oneSub (1 - Y) ht).isUnit
    simpa using this
  obtain ⟨u, rfl⟩ := hu
  rw [Ring.inverse_unit]
  -- `Y⁻¹ - 1 = Y⁻¹(1 - Y)`
  have e : ((u⁻¹ : Rˣ) : R) - 1 = ((u⁻¹ : Rˣ) : R) * (1 - (u : R)) := by
    rw [mul_sub, mul_one, Units.inv_mul]
  have h1 : ‖((u⁻¹ : Rˣ) : R) - 1‖ ≤ ‖((u⁻¹ : Rˣ) : R)‖ * ‖(u : R) - 1‖ := by
    rw [e]
    calc ‖((u⁻¹ : Rˣ) : R) * (1 - (u : R))‖ ≤ ‖((u⁻¹ : Rˣ) : R)‖ * ‖1 - (u : R)‖ := norm_mul_le _ _
      _ = ‖((u⁻¹ : Rˣ) : R)‖ * ‖(u : R) - 1‖ := by rw [norm_sub_rev]
  have h2 : ‖((u⁻¹ : Rˣ) : R)‖ ≤ 2 := by
    have : ‖((u⁻¹ : Rˣ) : R)‖ ≤ 1 + ‖((u⁻¹ : Rˣ) : R)‖ * ‖(u : R) - 1‖ := by
      calc ‖((u⁻¹ : Rˣ) : R)‖ = ‖1 + (((u⁻¹ : Rˣ) : R) - 1)‖ := by rw [add_sub_cancel]
        _ ≤ ‖(1 : R)‖ + ‖((u⁻¹ : Rˣ) : R) - 1‖ := norm_add_le _ _
        _ ≤ 1 + ‖((u⁻¹ : Rˣ) : R)‖ * ‖(u : R) - 1‖ := by rw [norm_one]; linarith
    have hn := norm_nonneg ((u⁻¹ : Rˣ) : R)
    nlinarith
  refine ⟨Units.isUnit u, h2, h1.trans ?_⟩
  exact mul_le_mul_of_nonneg_right h2 (norm_nonneg _)

/-- `‖γ(P' - 1)γ⁻¹‖ ≤ κ·(2‖P - 1‖)·κ ≤ 8√Nα` for `‖γ^{±1}‖ ≤ κ ≤ 2`, `‖P' - 1‖ ≤ 2‖P - 1‖`, `‖P - 1‖ ≤ √Nα`. -/
theorem factor_bound {R : Type*} [NormedRing R] (g g' Q : R) {κ q sN α : ℝ} (hκ0 : 0 ≤ κ) (hκ : κ ≤ 2)
    (hg : ‖g‖ ≤ κ) (hg' : ‖g'‖ ≤ κ) (hQ : ‖Q‖ ≤ 2 * q) (hq : q ≤ sN * α) (hq0 : 0 ≤ q) :
    ‖g * Q * g'‖ ≤ 8 * (sN * α) := by
  have h1 : ‖g * Q * g'‖ ≤ ‖g‖ * ‖Q‖ * ‖g'‖ := (norm_mul_le _ _).trans (by gcongr; exact norm_mul_le _ _)
  have h2 : ‖g‖ * ‖Q‖ * ‖g'‖ ≤ κ * (2 * q) * κ := by
    apply mul_le_mul (mul_le_mul hg hQ (norm_nonneg _) hκ0) hg' (norm_nonneg _) (by positivity)
  have h3 : κ * (2 * q) * κ ≤ 2 * (2 * q) * 2 := by
    apply mul_le_mul (mul_le_mul_of_nonneg_right hκ (by positivity)) hκ hκ0 (by positivity)
  nlinarith

/-- `2·(2s₀/a₀)·8√Nα(a₀/a)²·2 = (768√N/L)Mα(a₀/a)` for `s₀ = 12Ma/L`. -/
theorem contour_constant (sN M L a a₀ α : ℝ) (hL : L ≠ 0) (ha : a ≠ 0) (ha₀ : a₀ ≠ 0) :
    2 * (2 * (2 * (12 * M * a / L) / a₀) * (8 * sN * α * (a₀ / a) ^ 2)) = 768 * sN / L * M * α * (a₀ / a) := by
  field_simp; ring

/-- For `0 ≤ δ ≤ ½`: `(1 - δ)⁻¹ ≤ 1 + 2δ` and `(1 + 2δ)² ≤ e^{4δ}`. -/
theorem ad_bound {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1 / 2) :
    (1 - δ)⁻¹ ≤ 1 + 2 * δ ∧ (1 + 2 * δ) ^ 2 ≤ Real.exp (4 * δ) := by
  refine ⟨?_, ?_⟩
  · have hp : 0 < 1 - δ := by linarith
    rw [inv_le_iff_one_le_mul₀ hp]
    nlinarith
  · have h := Real.add_one_le_exp (2 * δ)
    have e : Real.exp (4 * δ) = Real.exp (2 * δ) ^ 2 := by rw [← Real.exp_nat_mul]; ring_nf
    rw [e]
    exact pow_le_pow_left₀ (by linarith) (by linarith) 2

/-- `-log(1 - x) ≤ 2x` for `0 ≤ x ≤ ½` (the bound of the logarithm of `lem:logarithm`(i) at `‖W - 1‖ ≤ ½`). -/
theorem neg_log_le {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1 / 2) : -Real.log (1 - x) ≤ 2 * x := by
  have hp : 0 < 1 - x := by linarith
  have h := Real.add_one_le_exp (-(2 * x))
  -- `1 - x ≥ e^{-2x}` on `[0, ½]` from `log(1 - x) ≥ -x/(1 - x) ≥ -2x`
  have hl : -(x / (1 - x)) ≤ Real.log (1 - x) := by
    have := Real.one_sub_inv_le_log_of_pos hp
    have e : 1 - (1 - x)⁻¹ = -(x / (1 - x)) := by field_simp; ring
    linarith
  have hx : x / (1 - x) ≤ 2 * x := by
    rw [div_le_iff₀ hp]; nlinarith
  linarith

end CubeGaugeArith
end CoreLean

end
