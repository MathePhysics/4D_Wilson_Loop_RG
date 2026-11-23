/-
`lem:action-coefficient` of BALABAN_CORE.tex (`a021c13be348`), three steps of its proof in abstract form.

* (i), the upper bound: `½t²a + O(t³) ≤ ½t²b + O(t³)` for small `t > 0` gives `a ≤ b` (`second_order_le`).
* (i), the gauge directions: a symmetric bilinear form `Π` with `Π(dλ, ·) = 0` satisfies
  `Π(B - dω, B - dω) = Π(B, B)` (`polarisation_gauge`).
* (ii), the sum of the decay in one coordinate: `Σ_{n ∈ ℤ}e^{-δ(|n - p| + |n - q|)} ≤ e^{-δ|p - q|/2}Σ_{n ∈ ℤ}e^{-δ|n|/2}`
  (`decay_sum`), and `Σ_{n ∈ ℤ}e^{-c|n|} = (1 + e^{-c})/(1 - e^{-c}) = coth(c/2)` (`two_sided_geometric`); the core's
  `coth(δ₂/4)^4` is the product over the four coordinates.
-/
import Mathlib

noncomputable section

namespace CoreLean
namespace ActionCoefficient

/-- **The limit `t → 0`**: `½t²a ≤ ½t²b + Ct³` for `0 < t < δ` gives `a ≤ b`. -/
theorem second_order_le {a b C δ : ℝ} (hδ : 0 < δ) (h : ∀ t, 0 < t → t < δ → 1 / 2 * t ^ 2 * a ≤ 1 / 2 * t ^ 2 * b + C * t ^ 3) :
    a ≤ b := by
  by_contra hab
  push_neg at hab
  -- choose `t` small with `2|C|t < a - b`
  set t := min (δ / 2) ((a - b) / (2 * (|C| + 1)))
  have ht0 : 0 < t := lt_min (by linarith) (div_pos (by linarith) (by positivity))
  have htδ : t < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have ht2 : t ≤ (a - b) / (2 * (|C| + 1)) := min_le_right _ _
  have h1 := h t ht0 htδ
  have h2 : 1 / 2 * t ^ 2 * (a - b) ≤ C * t ^ 3 := by nlinarith
  have h3 : C * t ^ 3 ≤ |C| * t ^ 3 := mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
  have h4 : 2 * (|C| + 1) * t ≤ a - b := by
    rw [le_div_iff₀ (by positivity)] at ht2; linarith
  have h5 : 0 < t ^ 2 := by positivity
  nlinarith [abs_nonneg C]

/-- **The gauge directions**: `Π(B - dω, B - dω) = Π(B, B)`. -/
theorem polarisation_gauge {V : Type*} [AddCommGroup V] (P : V →+ V →+ ℝ) (hsym : ∀ u v, P u v = P v u)
    (dω B : V) (hgauge : ∀ v, P dω v = 0) : P (B - dω) (B - dω) = P B B := by
  have h1 : P B dω = 0 := by rw [hsym]; exact hgauge B
  simp only [map_sub, AddMonoidHom.sub_apply, hgauge, h1]
  ring

/-- **The decay sum in one coordinate**. -/
theorem decay_sum {δ : ℝ} (hδ : 0 < δ) (p q : ℤ)
    (hs : Summable fun n : ℤ => Real.exp (-(δ / 2 * |((n - p : ℤ) : ℝ)|))) :
    ∑' n : ℤ, Real.exp (-(δ * (|((n - p : ℤ) : ℝ)| + |((n - q : ℤ) : ℝ)|))) ≤
      Real.exp (-(δ / 2 * |((p - q : ℤ) : ℝ)|)) * ∑' n : ℤ, Real.exp (-(δ / 2 * |((n - p : ℤ) : ℝ)|)) := by
  rw [← tsum_mul_left]
  have hb : ∀ n : ℤ, Real.exp (-(δ * (|((n - p : ℤ) : ℝ)| + |((n - q : ℤ) : ℝ)|))) ≤
      Real.exp (-(δ / 2 * |((p - q : ℤ) : ℝ)|)) * Real.exp (-(δ / 2 * |((n - p : ℤ) : ℝ)|)) := by
    intro n
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    have htri : |((p - q : ℤ) : ℝ)| ≤ |((n - p : ℤ) : ℝ)| + |((n - q : ℤ) : ℝ)| := by
      push_cast
      calc |(p : ℝ) - q| = |((n : ℝ) - q) - ((n : ℝ) - p)| := by ring_nf
        _ ≤ |(n : ℝ) - q| + |(n : ℝ) - p| := abs_sub _ _
        _ = |(n : ℝ) - p| + |(n : ℝ) - q| := by ring
    have h0 : 0 ≤ |((n - q : ℤ) : ℝ)| := abs_nonneg _
    nlinarith [abs_nonneg ((n - p : ℤ) : ℝ)]
  have hs' : Summable fun n : ℤ =>
      Real.exp (-(δ / 2 * |((p - q : ℤ) : ℝ)|)) * Real.exp (-(δ / 2 * |((n - p : ℤ) : ℝ)|)) := hs.mul_left _
  exact Summable.tsum_le_tsum hb (Summable.of_nonneg_of_le (fun n => (Real.exp_pos _).le) hb hs') hs'

/-- `e^{-c|n|} = (e^{-c})^{|n|}`. -/
lemma exp_abs_nat {c : ℝ} (n : ℕ) : Real.exp (-(c * |((n : ℤ) : ℝ)|)) = Real.exp (-c) ^ n := by
  rw [← Real.exp_nat_mul]
  congr 1
  have : |((n : ℤ) : ℝ)| = (n : ℝ) := by push_cast; exact abs_of_nonneg (Nat.cast_nonneg n)
  rw [this]; ring

lemma exp_abs_neg {c : ℝ} (n : ℕ) :
    Real.exp (-(c * |((-((n : ℤ) + 1) : ℤ) : ℝ)|)) = Real.exp (-c) * Real.exp (-c) ^ n := by
  rw [← pow_succ', ← Real.exp_nat_mul]
  congr 1
  have : |((-((n : ℤ) + 1) : ℤ) : ℝ)| = ((n + 1 : ℕ) : ℝ) := by
    push_cast; rw [abs_neg]; exact abs_of_nonneg (by positivity)
  rw [this]; ring

/-- **The two-sided geometric series**: `Σ_{n ∈ ℤ}e^{-c|n|} = (1 + e^{-c})/(1 - e^{-c})`. -/
theorem two_sided_geometric {c : ℝ} (hc : 0 < c) :
    HasSum (fun n : ℤ => Real.exp (-(c * |(n : ℝ)|))) ((1 + Real.exp (-c)) / (1 - Real.exp (-c))) := by
  have hr0 : 0 ≤ Real.exp (-c) := (Real.exp_pos _).le
  have hr1 : Real.exp (-c) < 1 := by
    rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 (by linarith)
  have hgeo : HasSum (fun n : ℕ => Real.exp (-c) ^ n) (1 - Real.exp (-c))⁻¹ :=
    hasSum_geometric_of_lt_one hr0 hr1
  have h1 : HasSum (fun n : ℕ => Real.exp (-(c * |((n : ℤ) : ℝ)|))) (1 - Real.exp (-c))⁻¹ := by
    have e : (fun n : ℕ => Real.exp (-(c * |((n : ℤ) : ℝ)|))) = fun n : ℕ => Real.exp (-c) ^ n :=
      funext fun n => exp_abs_nat n
    rw [e]; exact hgeo
  have h2 : HasSum (fun n : ℕ => Real.exp (-(c * |((-((n : ℤ) + 1) : ℤ) : ℝ)|)))
      (Real.exp (-c) * (1 - Real.exp (-c))⁻¹) := by
    have e : (fun n : ℕ => Real.exp (-(c * |((-((n : ℤ) + 1) : ℤ) : ℝ)|))) =
        fun n : ℕ => Real.exp (-c) * Real.exp (-c) ^ n := funext fun n => exp_abs_neg n
    rw [e]; exact hgeo.mul_left _
  have h := HasSum.of_nat_of_neg_add_one (f := fun n : ℤ => Real.exp (-(c * |(n : ℝ)|))) h1 h2
  have hne : (1 - Real.exp (-c)) ≠ 0 := by linarith
  have e : (1 - Real.exp (-c))⁻¹ + Real.exp (-c) * (1 - Real.exp (-c))⁻¹ =
      (1 + Real.exp (-c)) / (1 - Real.exp (-c)) := by
    rw [div_eq_mul_inv]; ring
  rw [e] at h
  exact h

end ActionCoefficient
end CoreLean

end
