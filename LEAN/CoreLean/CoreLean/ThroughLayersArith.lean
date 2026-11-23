/-
`cor:through-layers` of BALABAN_CORE.tex (`a021c13be348`), the arithmetic of its proof.

* `e_bound`: `8c_mC₀M⁸K²a_h/a_n ≤ 1` turns `𝔢_s ≤ (a_h/a_n)c_m(...) + ...` into
  `𝔢_s ≤ 2A_s + (t_s + τ_s)/(8C₀K²)` (abstract form: `x·q ≤ x/(8C₀K²)` for `q ≤ 1/(8C₀K²)`).
* `step_bound`: `2K²(11C₀A + 2C₀(2A' + T/(8C₀K²))) ≤ 30C₀K²·max{A, A'} + ½T`.
* `induction_bound`: if `T_r ≤ 30cA*_r + ½·max_{s<r}T_s` for every `r` with a nondecreasing `A*`, then
  `T_r ≤ 60cA*_r` for every `r`, whatever the number of the levels.
-/
import Mathlib

noncomputable section

namespace CoreLean
namespace ThroughLayersArith

/-- `x·q ≤ x/(8C₀K²)` for `q·8C₀K² ≤ 1`. -/
theorem e_bound {x q C K : ℝ} (hx : 0 ≤ x) (hC : 0 < C) (hK : 0 < K) (hq : 8 * C * K ^ 2 * q ≤ 1) :
    x * q ≤ x / (8 * C * K ^ 2) := by
  rw [le_div_iff₀ (by positivity)]
  have : x * (8 * C * K ^ 2 * q) ≤ x * 1 := mul_le_mul_of_nonneg_left hq hx
  nlinarith

/-- The step: `2K²(11C₀A + 2C₀(2A' + T/(8C₀K²))) ≤ 30C₀K²·max{A, A'} + ½T`. -/
theorem step_bound {K C A A' T : ℝ} (hK : 0 < K) (hC : 0 < C) (hA : 0 ≤ A) (hA' : 0 ≤ A') :
    2 * K ^ 2 * (11 * C * A + 2 * C * (2 * A' + T / (8 * C * K ^ 2))) ≤
      30 * C * K ^ 2 * max A A' + 1 / 2 * T := by
  have e : 2 * K ^ 2 * (11 * C * A + 2 * C * (2 * A' + T / (8 * C * K ^ 2))) =
      22 * C * K ^ 2 * A + 8 * C * K ^ 2 * A' + 1 / 2 * T := by
    field_simp; ring
  rw [e]
  have h1 : A ≤ max A A' := le_max_left _ _
  have h2 : A' ≤ max A A' := le_max_right _ _
  have hp : 0 ≤ C * K ^ 2 := by positivity
  nlinarith

/-- **The induction over the levels.** -/
theorem induction_bound (T A : ℕ → ℝ) {c : ℝ} (hc : 0 ≤ c) (hA0 : ∀ r, 0 ≤ A r) (hmono : Monotone A)
    (h : ∀ r, ∀ m : ℝ, 0 ≤ m → (∀ s < r, T s ≤ m) → T r ≤ 30 * c * A r + 1 / 2 * m) :
    ∀ r, T r ≤ 60 * c * A r := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    have hm : 0 ≤ 60 * c * A r := by have := hA0 r; positivity
    have hs : ∀ s < r, T s ≤ 60 * c * A r := fun s hs =>
      (ih s hs).trans (mul_le_mul_of_nonneg_left (hmono hs.le) (by positivity))
    have := h r (60 * c * A r) hm hs
    linarith

end ThroughLayersArith
end CoreLean

end
