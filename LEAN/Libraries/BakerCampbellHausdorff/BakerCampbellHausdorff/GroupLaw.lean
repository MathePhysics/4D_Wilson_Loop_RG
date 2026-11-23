import BakerCampbellHausdorff.Theorem

/-!
# The local group law of the Baker–Campbell–Hausdorff function

Near `0`, `bch 𝕂` is a local group law with neutral element `0` and inverse `X ↦ -X`:
it is associative, and `bch 𝕂 (-Y) (-X) = -bch 𝕂 X Y`.  Both identities follow from uniqueness
of small logarithms (`exp_injOn`), once `bch 𝕂 X Y` is known to be small.

## Main results

* `norm_exp_mul_exp_sub_one_le_mul`: `‖exp X exp Y - 1‖ ≤ (6/5) (‖X‖ + ‖Y‖)` for
  `‖X‖ + ‖Y‖ ≤ 1/6`.
* `norm_bch_le_mul`: `‖bch 𝕂 X Y‖ ≤ (3/2) (‖X‖ + ‖Y‖)` for `‖X‖ + ‖Y‖ ≤ 1/6`.
* `norm_bch_lt`: `‖bch 𝕂 X Y‖ < 1/4` for `‖X‖ + ‖Y‖ < 1/6`.
* `bch_neg_neg`: `bch 𝕂 (-Y) (-X) = -bch 𝕂 X Y` for `‖X‖ + ‖Y‖ < 1/6`.
* `bch_assoc`: `bch 𝕂 (bch 𝕂 X Y) Z = bch 𝕂 X (bch 𝕂 Y Z)` for `‖X‖ + ‖Y‖ + ‖Z‖ < 1/10`.
-/

noncomputable section

open NormedSpace

namespace BakerCampbellHausdorff

variable {𝕂 𝔸 : Type*} [RCLike 𝕂] [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [CompleteSpace 𝔸]

theorem one_sixth_lt_log_two :
    (1 : ℝ) / 6 < Real.log 2 := by  -- totalisation-audit: allow literal; log of 2 > 0
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have h := Real.exp_bound_div_one_sub_of_interval'
    (x := 1 / 6) (by norm_num) (by norm_num)  -- totalisation-audit: allow literal
  norm_num at h
  linarith

include 𝕂 in
variable (𝕂) in
/-- `‖exp X exp Y - 1‖ ≤ (6/5) (‖X‖ + ‖Y‖)` for `‖X‖ + ‖Y‖ ≤ 1/6`. -/
theorem norm_exp_mul_exp_sub_one_le_mul {X Y : 𝔸}
    (h : ‖X‖ + ‖Y‖ ≤ 1 / 6) :  -- totalisation-audit: allow literal
    ‖exp X * exp Y - 1‖ ≤ 6 / 5 * (‖X‖ + ‖Y‖) := by  -- totalisation-audit: allow literal
  set s := ‖X‖ + ‖Y‖ with hs
  have hs0 : 0 ≤ s := by positivity
  have h1 := norm_exp_mul_exp_sub_one_le 𝕂 X Y
  have he := Real.exp_pos s
  have h2 : Real.exp s - 1 ≤ s * Real.exp s := by
    have h := Real.add_one_le_exp (-s)
    rw [Real.exp_neg] at h
    have h' : (-s + 1) * Real.exp s ≤ 1 := by
      calc (-s + 1) * Real.exp s ≤ (Real.exp s)⁻¹ * Real.exp s :=
            mul_le_mul_of_nonneg_right h he.le
        _ = 1 := inv_mul_cancel₀ he.ne'
    linarith
  have h3 : Real.exp s ≤ 6 / 5 := by  -- totalisation-audit: allow literal
    have h4 := Real.exp_bound_div_one_sub_of_interval'
      (x := 1 / 6) (by norm_num) (by norm_num)  -- totalisation-audit: allow literal
    have h5 : Real.exp s ≤ Real.exp (1 / 6) :=  -- totalisation-audit: allow literal
      Real.exp_le_exp.mpr h
    norm_num at h4
    linarith
  nlinarith

/-- `‖bch 𝕂 X Y‖ ≤ (3/2) (‖X‖ + ‖Y‖)` for `‖X‖ + ‖Y‖ ≤ 1/6`. -/
theorem norm_bch_le_mul {X Y : 𝔸} (h : ‖X‖ + ‖Y‖ ≤ 1 / 6) :  -- totalisation-audit: allow literal
    ‖bch 𝕂 X Y‖ ≤ 3 / 2 * (‖X‖ + ‖Y‖) := by  -- totalisation-audit: allow literal
  have hu := norm_exp_mul_exp_sub_one_le_mul 𝕂 h
  have hu0 := norm_nonneg (exp X * exp Y - 1)
  have hs0 : 0 ≤ ‖X‖ + ‖Y‖ := by positivity
  have hu1 : ‖exp X * exp Y - 1‖ < 1 := by linarith
  refine (norm_log1p_le_div hu1).trans ?_
  rw [div_le_iff₀ (by linarith)]
  nlinarith

/-- `‖bch 𝕂 X Y‖ < 1/4` for `‖X‖ + ‖Y‖ < 1/6`. -/
theorem norm_bch_lt {X Y : 𝔸} (h : ‖X‖ + ‖Y‖ < 1 / 6) :  -- totalisation-audit: allow literal
    ‖bch 𝕂 X Y‖ < 1 / 4 :=  -- totalisation-audit: allow literal
  (norm_bch_le_mul h.le).trans_lt (by linarith)

/-- **Inverse law**: `bch 𝕂 (-Y) (-X) = -bch 𝕂 X Y` for `‖X‖ + ‖Y‖ < 1/6`. -/
theorem bch_neg_neg {X Y : 𝔸} (h : ‖X‖ + ‖Y‖ < 1 / 6) :  -- totalisation-audit: allow literal
    bch 𝕂 (-Y) (-X) = -bch 𝕂 X Y := by
  have hZ := exp_bch (𝕂 := 𝕂) (h.trans one_sixth_lt_log_two)
  have e1 : exp (-Y) * exp (-X) * (exp X * exp Y) = 1 := by
    rw [mul_assoc, ← mul_assoc (exp (-X)), exp_neg_mul_exp 𝕂, one_mul, exp_neg_mul_exp 𝕂]
  symm
  refine eq_bch_of_exp_eq ?_ (by rw [norm_neg]; exact norm_bch_lt h)
  calc exp (-bch 𝕂 X Y) = exp (-Y) * exp (-X) * (exp X * exp Y) * exp (-bch 𝕂 X Y) := by
        rw [e1, one_mul]
    _ = exp (-Y) * exp (-X) * (exp (bch 𝕂 X Y) * exp (-bch 𝕂 X Y)) := by
        rw [hZ, mul_assoc]
    _ = exp (-Y) * exp (-X) := by rw [exp_mul_exp_neg 𝕂, mul_one]

/-- **Associativity**: `bch 𝕂 (bch 𝕂 X Y) Z = bch 𝕂 X (bch 𝕂 Y Z)` for
`‖X‖ + ‖Y‖ + ‖Z‖ < 1/10`. -/
theorem bch_assoc {X Y Z : 𝔸}
    (h : ‖X‖ + ‖Y‖ + ‖Z‖ < 1 / 10) :  -- totalisation-audit: allow literal
    bch 𝕂 (bch 𝕂 X Y) Z = bch 𝕂 X (bch 𝕂 Y Z) := by
  have hX := norm_nonneg X
  have hY := norm_nonneg Y
  have hZ := norm_nonneg Z
  have hXY : ‖X‖ + ‖Y‖ < 1 / 6 := by linarith  -- totalisation-audit: allow literal
  have hYZ : ‖Y‖ + ‖Z‖ < 1 / 6 := by linarith  -- totalisation-audit: allow literal
  have hA := norm_bch_le_mul (𝕂 := 𝕂) hXY.le
  have hB := norm_bch_le_mul (𝕂 := 𝕂) hYZ.le
  have hAZ : ‖bch 𝕂 X Y‖ + ‖Z‖ < 1 / 6 := by linarith  -- totalisation-audit: allow literal
  have hXB : ‖X‖ + ‖bch 𝕂 Y Z‖ < 1 / 6 := by linarith  -- totalisation-audit: allow literal
  have e1 : exp (bch 𝕂 (bch 𝕂 X Y) Z) = exp X * exp Y * exp Z := by
    rw [exp_bch (hAZ.trans one_sixth_lt_log_two), exp_bch (hXY.trans one_sixth_lt_log_two)]
  have e2 : exp (bch 𝕂 X (bch 𝕂 Y Z)) = exp X * exp Y * exp Z := by
    rw [exp_bch (hXB.trans one_sixth_lt_log_two), exp_bch (hYZ.trans one_sixth_lt_log_two),
      mul_assoc]
  exact exp_injOn 𝕂 (mem_ball_zero_iff.mpr (norm_bch_lt hAZ))
    (mem_ball_zero_iff.mpr (norm_bch_lt hXB)) (e1.trans e2.symm)

end BakerCampbellHausdorff
