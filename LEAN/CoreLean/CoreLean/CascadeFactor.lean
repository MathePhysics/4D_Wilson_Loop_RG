/-
`lem:cascade-factor`(i) of BALABAN_CORE.tex (`a021c13be348`), the monotonicity used in its proof: for `p ≥ 0` the
function `x ↦ x(log x⁻²)^p` is increasing on `(0, e^{-p}]` (`mono_xlog`), which gives `e_i ≤ e_l` for the families
`c ĝ_l (log ĝ_l⁻²)^p` when the couplings do not increase and `γ ≤ e^{-p}`. The core argues with the derivative
`(log x⁻²)^{p-1}(log x⁻² - 2p)`; here, with `u = log x⁻¹ ≥ p` and `t = v/u ≥ 1`, from `t^p ≤ e^{p(t-1)} ≤ e^{u(t-1)}`.
-/
import Mathlib

noncomputable section

namespace CoreLean
namespace Cascade

/-- In the variable `u = log x⁻¹`: `e^{-v}(2v)^p ≤ e^{-u}(2u)^p` for `p ≤ u ≤ v`, `p ≥ 0`, `u > 0`. -/
lemma mono_u {p u v : ℝ} (hp : 0 ≤ p) (hu : 0 < u) (hpu : p ≤ u) (huv : u ≤ v) :
    Real.exp (-v) * (2 * v) ^ p ≤ Real.exp (-u) * (2 * u) ^ p := by
  have hv : 0 < v := lt_of_lt_of_le hu huv
  set t := v / u with ht
  have ht1 : 1 ≤ t := by rw [ht, le_div_iff₀ hu]; linarith
  have hvt : v = t * u := by rw [ht]; field_simp
  -- `t^p ≤ e^{p(t - 1)} ≤ e^{u(t - 1)} = e^{v - u}`
  have h1 : t ^ p ≤ Real.exp (p * (t - 1)) := by
    have h2 : t ≤ Real.exp (t - 1) := by have := Real.add_one_le_exp (t - 1); linarith
    calc t ^ p ≤ (Real.exp (t - 1)) ^ p := Real.rpow_le_rpow (by linarith) h2 hp
      _ = Real.exp (p * (t - 1)) := by rw [← Real.exp_mul]; ring_nf
  have h3 : Real.exp (p * (t - 1)) ≤ Real.exp (v - u) := by
    rw [Real.exp_le_exp, hvt]; nlinarith
  have h4 : (2 * v) ^ p = t ^ p * (2 * u) ^ p := by
    rw [hvt, show 2 * (t * u) = t * (2 * u) by ring, Real.mul_rpow (by linarith) (by linarith)]
  rw [h4]
  have h5 : 0 ≤ (2 * u) ^ p := Real.rpow_nonneg (by linarith) _
  calc Real.exp (-v) * (t ^ p * (2 * u) ^ p) = (t ^ p * Real.exp (-v)) * (2 * u) ^ p := by ring
    _ ≤ (Real.exp (v - u) * Real.exp (-v)) * (2 * u) ^ p := by
        gcongr; exact h1.trans h3
    _ = Real.exp (-u) * (2 * u) ^ p := by rw [← Real.exp_add]; ring_nf

/-- **`x(log x⁻²)^p` is increasing on `(0, e^{-p}]`**. -/
theorem mono_xlog {p x y : ℝ} (hp : 0 ≤ p) (hx : 0 < x) (hxy : x ≤ y) (hy : y ≤ Real.exp (-p)) (hy1 : y < 1) :
    x * (Real.log (x ^ 2)⁻¹) ^ p ≤ y * (Real.log (y ^ 2)⁻¹) ^ p := by
  have hy0 : 0 < y := lt_of_lt_of_le hx hxy
  set u := -Real.log y with hu
  set v := -Real.log x with hv
  have hlog : ∀ z : ℝ, 0 < z → Real.log (z ^ 2)⁻¹ = 2 * -Real.log z := fun z hz => by
    rw [Real.log_inv, Real.log_pow]; push_cast; ring
  rw [hlog x hx, hlog y hy0]
  have hu0 : 0 < u := by rw [hu, neg_pos]; exact Real.log_neg hy0 hy1
  have hpu : p ≤ u := by
    rw [hu, le_neg]; calc Real.log y ≤ Real.log (Real.exp (-p)) := Real.log_le_log hy0 hy
      _ = -p := Real.log_exp _
  have huv : u ≤ v := by rw [hu, hv, neg_le_neg_iff]; exact Real.log_le_log hx hxy
  have hxe : x = Real.exp (-v) := by rw [hv, neg_neg, Real.exp_log hx]
  have hye : y = Real.exp (-u) := by rw [hu, neg_neg, Real.exp_log hy0]
  rw [show -Real.log x = v from rfl, show -Real.log y = u from rfl]
  conv_lhs => rw [hxe]
  conv_rhs => rw [hye]
  exact mono_u hp hu0 hpu huv

end Cascade
end CoreLean

end
