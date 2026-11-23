import BakerCampbellHausdorff.ExpLog

/-!
# `log (exp Z) = Z` near `0`

For `‖Z‖ < 1/4` in a Banach algebra over `𝕂 = ℝ` or `ℂ`, `log1p 𝕂 (exp Z - 1) = Z`.  Together
with `exp_log1p` this makes `u ↦ log1p 𝕂 u` the inverse of `Z ↦ exp Z - 1` near `0`, so the
logarithm of an element close to `1` is the unique small solution of `exp W = g`.

## Main results

* `norm_exp_sub_one_lt`: `‖Z‖ < 1/4 → ‖exp Z - 1‖ < 1/3`.
* `log1p_exp_sub_one`: `‖Z‖ < 1/4 → log1p 𝕂 (exp Z - 1) = Z`.
* `exp_injOn`: `exp` is injective on the ball `‖Z‖ < 1/4`.
* `eq_log1p_of_exp_eq`: if `exp W = 1 + u` and `‖W‖ < 1/4`, then `W = log1p 𝕂 u`.

## Proof

`W = log1p 𝕂 (exp Z - 1) - Z` commutes with `Z`, so `exp W = exp (log1p 𝕂 (exp Z - 1)) exp (-Z)
= exp Z exp (-Z) = 1` by `exp_log1p`.  The bounds `‖exp Z - 1‖ < 1/3` (from `e^(1/4) < 4/3`) and
`‖log1p 𝕂 v‖ ≤ ‖v‖ / (1 - ‖v‖)` give `‖W‖ < 1/2 + 1/4 < 1`, and `eq_zero_of_exp_eq_one` gives
`W = 0`.
-/

noncomputable section

open NormedSpace

namespace BakerCampbellHausdorff

variable (𝕂 : Type*) {𝔸 : Type*} [RCLike 𝕂] [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸]
  [CompleteSpace 𝔸]

include 𝕂 in
/-- `‖exp Z - 1‖ < 1/3` for `‖Z‖ < 1/4`. -/
theorem norm_exp_sub_one_lt {Z : 𝔸} (hZ : ‖Z‖ < 1 / 4) :  -- totalisation-audit: allow literal
    ‖exp Z - 1‖ < 1 / 3 := by  -- totalisation-audit: allow literal
  have h1 := norm_exp_sub_one_le 𝕂 Z
  have h2 : Real.exp ‖Z‖ ≤ Real.exp (1 / 4) :=  -- totalisation-audit: allow literal
    Real.exp_le_exp.mpr hZ.le
  have h3 := Real.exp_bound_div_one_sub_of_interval'
    (x := 1 / 4) (by norm_num) (by norm_num)  -- totalisation-audit: allow literal
  norm_num at h3
  linarith

/-- **`log (exp Z) = Z`** for `‖Z‖ < 1/4`. -/
theorem log1p_exp_sub_one {Z : 𝔸} (hZ : ‖Z‖ < 1 / 4) :  -- totalisation-audit: allow literal
    log1p 𝕂 (exp Z - 1) = Z := by
  have hv := norm_exp_sub_one_lt 𝕂 hZ
  have hv0 := norm_nonneg (exp Z - 1)
  have hv1 : ‖exp Z - 1‖ < 1 := by linarith
  have hcomm : Commute (log1p 𝕂 (exp Z - 1)) Z :=
    ((Commute.refl Z).exp_right.sub_right (Commute.one_right Z)).log1p_right.symm
  have hexp : exp (log1p 𝕂 (exp Z - 1) + -Z) = 1 := by
    rw [exp_add_of_commute' 𝕂 hcomm.neg_right, exp_log1p 𝕂 hv1, add_sub_cancel,
      exp_mul_exp_neg 𝕂]
  have hlog : ‖log1p 𝕂 (exp Z - 1)‖ < 1 / 2 := by  -- totalisation-audit: allow literal
    refine (norm_log1p_le_div hv1).trans_lt ?_
    rw [div_lt_iff₀ (by linarith)]
    linarith
  have hnorm : ‖log1p 𝕂 (exp Z - 1) + -Z‖ < 1 := by
    calc ‖log1p 𝕂 (exp Z - 1) + -Z‖ ≤ ‖log1p 𝕂 (exp Z - 1)‖ + ‖-Z‖ := norm_add_le _ _
      _ < 1 := by rw [norm_neg]; linarith
  exact add_neg_eq_zero.mp (eq_zero_of_exp_eq_one 𝕂 hexp hnorm)

include 𝕂 in
/-- `exp` is injective on the ball of radius `1/4`. -/
theorem exp_injOn :
    Set.InjOn (exp : 𝔸 → 𝔸) (Metric.ball 0 (1 / 4)) := by  -- totalisation-audit: allow literal
  intro Z₁ h₁ Z₂ h₂ h
  rw [← log1p_exp_sub_one 𝕂 (mem_ball_zero_iff.mp h₁),
    ← log1p_exp_sub_one 𝕂 (mem_ball_zero_iff.mp h₂), h]

/-- The small logarithm is unique: `exp W = 1 + u` with `‖W‖ < 1/4` forces `W = log1p 𝕂 u`. -/
theorem eq_log1p_of_exp_eq {W u : 𝔸} (h : exp W = 1 + u)
    (hW : ‖W‖ < 1 / 4) :  -- totalisation-audit: allow literal
    W = log1p 𝕂 u := by
  rw [← log1p_exp_sub_one 𝕂 hW, h, add_sub_cancel_left]

end BakerCampbellHausdorff
