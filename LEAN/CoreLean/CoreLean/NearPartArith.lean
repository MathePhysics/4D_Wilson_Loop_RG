/-
`lem:near-part` of BALABAN_CORE.tex (`a021c13be348`), the self-contained steps of its proof.

* `split_identity`: the split
  `DΦ(B_Q + B_o)[δB_Q + δB_o] = DΦ(B_Q)[δB_Q] + DΦ(B_Q + B_o)[δB_o] + ∫₀¹D²Φ(B_Q + sB_o)[B_o, δB_Q] ds`
  for a twice continuously differentiable `Φ`.
* `rpow_mul_exp_neg_le`: `x^p e^{-x} ≤ p^p e^{-p}` for `x ≥ 0`, `p > 0`; hence `h^{-p}e^{-c/(64h)}` is bounded by a
  number for `h > 0` (`neg_power_exp_bounded`), which is the step "`h^{-3-β_d}e^{-c_*/(64h)}` is bounded by a number".
* `rate_steps`: `δ₆(R - 1) ≥ ½R/M` for `δ₆M ≥ 1`, `R ≥ 2`; `δR/64 ≥ c_*/(64h)` and `δℓ/8 ≥ 4c_*/h` for `δM ≥ c_*`,
  `R = M/h`, `ℓ ≥ 32R`.
-/
import Mathlib

open Set

noncomputable section

namespace CoreLean
namespace NearPartArith

/-- **The split of the derivative.** -/
theorem split_identity {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (Φ : E → ℝ) (hΦ : ContDiff ℝ 2 Φ)
    (x y u v : E) :
    fderiv ℝ Φ (x + y) (u + v) =
      fderiv ℝ Φ x u + fderiv ℝ Φ (x + y) v + ∫ s in (0 : ℝ)..1, fderiv ℝ (fderiv ℝ Φ) (x + s • y) y u := by
  have h1 : ContDiff ℝ 1 (fderiv ℝ Φ) := hΦ.fderiv_right (by norm_num)
  have hdiff : Differentiable ℝ (fderiv ℝ Φ) := h1.differentiable (by norm_num)
  have hcont : Continuous (fderiv ℝ (fderiv ℝ Φ)) := h1.continuous_fderiv (by norm_num)
  set g : ℝ → ℝ := fun s => fderiv ℝ Φ (x + s • y) u
  set g' : ℝ → ℝ := fun s => fderiv ℝ (fderiv ℝ Φ) (x + s • y) y u
  have hline : ∀ s : ℝ, HasDerivAt (fun s : ℝ => x + s • y) y s := fun s => by
    simpa using ((hasDerivAt_id s).smul_const y).const_add x
  have hg : ∀ s : ℝ, HasDerivAt g (g' s) s := fun s => by
    have hF : HasFDerivAt (fderiv ℝ Φ) (fderiv ℝ (fderiv ℝ Φ) (x + s • y)) (x + s • y) :=
      (hdiff _).hasFDerivAt
    have hc := hF.comp_hasDerivAt s (hline s)
    have := (ContinuousLinearMap.apply ℝ ℝ u).hasFDerivAt.comp_hasDerivAt s hc
    simpa [g, g', Function.comp_def] using this
  have hg'c : Continuous g' := by
    have : Continuous fun s : ℝ => x + s • y := by fun_prop
    exact ((ContinuousLinearMap.apply ℝ ℝ u).continuous.comp
      ((ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) y).continuous.comp (hcont.comp this)))
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hg s) (hg'c.intervalIntegrable 0 1)
  have hg1 : g 1 = fderiv ℝ Φ (x + y) u := by simp [g]
  have hg0 : g 0 = fderiv ℝ Φ x u := by simp [g]
  rw [hFTC, hg1, hg0, map_add]
  ring

/-- `x^p e^{-x} ≤ p^p e^{-p}` for `x ≥ 0`, `p > 0`. -/
theorem rpow_mul_exp_neg_le {x p : ℝ} (hx : 0 ≤ x) (hp : 0 < p) :
    x ^ p * Real.exp (-x) ≤ p ^ p * Real.exp (-p) := by
  rcases hx.eq_or_lt with h | h
  · subst h
    rw [Real.zero_rpow hp.ne', zero_mul]; positivity
  · -- `p log x - x ≤ p log p - p` from `log(x/p) ≤ x/p - 1`
    have hl : Real.log (x / p) ≤ x / p - 1 := Real.log_le_sub_one_of_pos (div_pos h hp)
    rw [Real.log_div h.ne' hp.ne'] at hl
    have key : p * Real.log x - x ≤ p * Real.log p - p := by
      have := mul_le_mul_of_nonneg_left hl hp.le
      rw [mul_sub, mul_sub, mul_div_cancel₀ _ hp.ne', mul_one] at this
      linarith
    rw [Real.rpow_def_of_pos h, Real.rpow_def_of_pos hp, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.2
    linarith [mul_comm (Real.log x) p, mul_comm (Real.log p) p]

/-- **`h^{-p}e^{-c/(64h)}` is bounded** for `h > 0`, `c > 0`, `p > 0`. -/
theorem neg_power_exp_bounded {c p : ℝ} (hc : 0 < c) (hp : 0 < p) :
    ∀ h : ℝ, 0 < h → (1 / h) ^ p * Real.exp (-(c / (64 * h))) ≤ (64 / c) ^ p * (p ^ p * Real.exp (-p)) := by
  intro h hh
  set x := c / (64 * h)
  have hx : 0 < x := by positivity
  have e : 1 / h = 64 / c * x := by simp only [x]; field_simp
  rw [e, Real.mul_rpow (by positivity) hx.le, mul_assoc]
  exact mul_le_mul_of_nonneg_left (rpow_mul_exp_neg_le hx.le hp) (by positivity)

/-- **The rates.** -/
theorem rate_steps {δ₆ δ M R h c ℓ : ℝ} (hM : 0 < M) (hh : 0 < h) (h6 : 1 ≤ δ₆ * M) (hR2 : 2 ≤ R)
    (hRh : R = M / h) (hδ : c ≤ δ * M) (hℓ : 32 * R ≤ ℓ) (hδ0 : 0 ≤ δ) :
    1 / 2 * R / M ≤ δ₆ * (R - 1) ∧ c / (64 * h) ≤ δ * R / 64 ∧ 4 * c / h ≤ δ * ℓ / 8 := by
  have hδR : c / h ≤ δ * R := by
    rw [hRh, div_le_iff₀ hh]
    calc c ≤ δ * M := hδ
      _ = δ * (M / h) * h := by field_simp
  refine ⟨?_, ?_, ?_⟩
  · rw [div_le_iff₀ hM]
    have h1 : 0 ≤ R - 2 := by linarith
    nlinarith
  · have : c / (64 * h) = c / h / 64 := by field_simp
    rw [this]; linarith
  · have h1 : 4 * c / h = 4 * (c / h) := by ring
    have h2 : δ * (32 * R) ≤ δ * ℓ := mul_le_mul_of_nonneg_left hℓ hδ0
    rw [h1]; nlinarith

end NearPartArith
end CoreLean

end
