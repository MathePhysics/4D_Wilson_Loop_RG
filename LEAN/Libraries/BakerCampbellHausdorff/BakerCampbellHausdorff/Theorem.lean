import BakerCampbellHausdorff.AnalyticLog
import BakerCampbellHausdorff.ExpMulExpSeries

/-!
# The Baker–Campbell–Hausdorff theorem in a Banach algebra

For `X, Y` in a Banach algebra `𝔸` over `𝕂 = ℝ` or `ℂ`, let

  `bch 𝕂 X Y = log (exp X exp Y) = log1p 𝕂 (exp X exp Y - 1)`.

This is the analytic form of the Baker–Campbell–Hausdorff theorem: `bch 𝕂` is analytic near `0`,
its exponential is `exp X exp Y`, it is the only small logarithm of `exp X exp Y`, and its power
series `bchSeries 𝕂 𝔸 = (logSeries 𝕂 𝔸).comp (expMulExpSeries 𝕂 𝔸)` has geometrically bounded
coefficients and begins `X + Y + ½[X, Y]`.

## Main results

* `exp_bch`: `‖X‖ + ‖Y‖ < log 2 → exp (bch 𝕂 X Y) = exp X exp Y`.
* `eq_bch_of_exp_eq`: if `exp Z = exp X exp Y` and `‖Z‖ < 1/4`, then `Z = bch 𝕂 X Y`.
* `hasFPowerSeriesAt_bch`: `bchSeries 𝕂 𝔸` is the power series of `(X, Y) ↦ bch 𝕂 X Y` at `0`.
* `exists_geometricBound_bchSeries`: `‖bchSeries 𝕂 𝔸 n‖ ≤ K Cⁿ` for some `K ≥ 0`, `C > 0`.
* `analyticAt_bch`, `analyticOnNhd_bch`: analyticity where `‖exp X exp Y - 1‖ < 1`, in
  particular on `‖X‖ + ‖Y‖ < log 2`.
* `bchSeries_one_apply`, `hasFDerivAt_bch`: the linear term is `X + Y`.
* `bchSeries_two_apply_diag`: the quadratic term is `½ [X, Y] = ½ (X Y - Y X)`.
* `bch_sub_isBigO`: `bch 𝕂 X Y = X + Y + ½ [X, Y] + O(‖(X, Y)‖³)`.
* `norm_bch_le`: `‖bch 𝕂 X Y‖ ≤ -log (2 - e^(‖X‖ + ‖Y‖))`.
* `bch_eq_add_of_commute`, `bch_zero_left`, `bch_zero_right`, `bch_neg_right`: the commuting
  case.

## Proof

`(X, Y) ↦ exp X exp Y` has the power series `expMulExpSeries 𝕂 𝔸` and value `1` at `0`, so
`HasFPowerSeriesAt.log1p_sub_one` (composition with the logarithm series) gives the power series
of `bch 𝕂`, and the radius API gives the geometric bound.  The identity `exp ∘ log = id` near `1`
(`exp_log1p`) gives `exp_bch`; `log ∘ exp = id` near `0` (`log1p_exp_sub_one`) gives uniqueness.
The low-order coefficients are read off the composition formula: `(q.comp p) 1 = q 1 (p 1)` and
`(q.comp p) 2 = q 1 (p 2) + q 2 (p 1, p 1)`.
-/

noncomputable section

open NormedSpace FormalMultilinearSeries Filter Asymptotics
open scoped Topology

namespace BakerCampbellHausdorff

/-! ### The second coefficient of a composition -/

section Comp

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- The second coefficient of `q.comp p` on the diagonal: `q₁ (p₂ (v, v)) + q₂ (p₁ v, p₁ v)`. -/
theorem comp_coeff_two_apply_diag (q : FormalMultilinearSeries 𝕜 F G)
    (p : FormalMultilinearSeries 𝕜 E F) (v : E) :
    (q.comp p) 2 (fun _ => v) = q 1 (fun _ => p 2 fun _ => v) + q 2 (fun _ => p 1 fun _ => v) := by
  have hne : Composition.single 2 two_pos ≠ Composition.ones 2 := fun h => by
    have := congrArg Composition.length h
    simp at this
  have huniv : ({Composition.single 2 two_pos, Composition.ones 2} : Finset (Composition 2)) =
      Finset.univ :=
    Finset.eq_univ_of_card _ (by rw [Finset.card_pair hne, composition_card]; rfl)
  simp only [FormalMultilinearSeries.comp, ← huniv, Finset.sum_pair hne,
    _root_.add_apply, compAlongComposition_apply]
  congr 1
  · refine q.congr (Composition.single_length _) fun i _ _ => ?_
    rw [applyComposition_single]
  · refine q.congr (Composition.ones_length _) fun i _ _ => ?_
    rw [applyComposition_ones]

end Comp

variable {𝕂 𝔸 : Type*} [RCLike 𝕂] [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [CompleteSpace 𝔸]

/-! ### Definitions -/

variable (𝕂) in
/-- The **Baker–Campbell–Hausdorff function** `bch 𝕂 X Y = log (exp X exp Y)`, defined through
the logarithm series `log1p 𝕂 u = log (1 + u)`.  It is meaningful for `‖exp X exp Y - 1‖ < 1`,
in particular for `‖X‖ + ‖Y‖ < log 2`. -/
def bch (X Y : 𝔸) : 𝔸 := log1p 𝕂 (exp X * exp Y - 1)

variable (𝕂 𝔸) in
/-- The **Baker–Campbell–Hausdorff series**: the power series of `(X, Y) ↦ bch 𝕂 X Y` at `0`,
the composition of the logarithm series with the series of `exp X exp Y`. -/
def bchSeries : FormalMultilinearSeries 𝕂 (𝔸 × 𝔸) 𝔸 :=
  (logSeries 𝕂 𝔸).comp (expMulExpSeries 𝕂 𝔸)

omit [CompleteSpace 𝔸] in
@[simp]
theorem bch_zero_zero : bch 𝕂 (0 : 𝔸) 0 = 0 := by simp [bch]

/-! ### The exponential identity and uniqueness -/

include 𝕂 in
variable (𝕂) in
theorem norm_exp_mul_exp_sub_one_lt {X Y : 𝔸}
    (h : ‖X‖ + ‖Y‖ < Real.log 2) :  -- totalisation-audit: allow log of 2 > 0
    ‖exp X * exp Y - 1‖ < 1 := by
  have h1 := norm_exp_mul_exp_sub_one_le 𝕂 X Y
  have h2 : Real.exp (‖X‖ + ‖Y‖) < 2 := by
    rwa [← Real.lt_log_iff_exp_lt (by norm_num)]
  linarith

/-- **Baker–Campbell–Hausdorff, exponential form**: `exp (bch 𝕂 X Y) = exp X exp Y` whenever
`‖exp X exp Y - 1‖ < 1`. -/
theorem exp_bch_of_norm_lt {X Y : 𝔸} (h : ‖exp X * exp Y - 1‖ < 1) :
    exp (bch 𝕂 X Y) = exp X * exp Y := by
  rw [bch, exp_log1p 𝕂 h, add_sub_cancel]

/-- **Baker–Campbell–Hausdorff, exponential form**: `exp (bch 𝕂 X Y) = exp X exp Y` for
`‖X‖ + ‖Y‖ < log 2`. -/
theorem exp_bch {X Y : 𝔸} (h : ‖X‖ + ‖Y‖ < Real.log 2) :  -- totalisation-audit: allow log of 2 > 0
    exp (bch 𝕂 X Y) = exp X * exp Y :=
  exp_bch_of_norm_lt (norm_exp_mul_exp_sub_one_lt 𝕂 h)

/-- **Uniqueness**: `bch 𝕂 X Y` is the only logarithm of `exp X exp Y` of norm `< 1/4`. -/
theorem eq_bch_of_exp_eq {X Y Z : 𝔸} (h : exp Z = exp X * exp Y)
    (hZ : ‖Z‖ < 1 / 4) :  -- totalisation-audit: allow literal
    Z = bch 𝕂 X Y :=
  eq_log1p_of_exp_eq 𝕂 (by rw [h, add_sub_cancel]) hZ

/-- `‖bch 𝕂 X Y‖ ≤ -log (2 - e^(‖X‖ + ‖Y‖))` for `‖X‖ + ‖Y‖ < log 2`. -/
theorem norm_bch_le {X Y : 𝔸}
    (h : ‖X‖ + ‖Y‖ < Real.log 2) :  -- totalisation-audit: allow log of 2 > 0
    ‖bch 𝕂 X Y‖ ≤
      -Real.log (2 - Real.exp (‖X‖ + ‖Y‖)) := by  -- totalisation-audit: allow 2 - e^s > 0 by h
  have hu := norm_exp_mul_exp_sub_one_lt 𝕂 h
  have h1 := norm_exp_mul_exp_sub_one_le 𝕂 X Y
  have h2 : Real.exp (‖X‖ + ‖Y‖) < 2 := by
    rwa [← Real.lt_log_iff_exp_lt (by norm_num)]
  refine (norm_log1p_le hu).trans ?_
  rw [neg_le_neg_iff]
  exact Real.log_le_log (by linarith) (by linarith)

/-- In the commuting case `bch 𝕂 X Y = X + Y`. -/
theorem bch_eq_add_of_commute {X Y : 𝔸} (h : Commute X Y)
    (hXY : ‖X‖ + ‖Y‖ < 1 / 4) :  -- totalisation-audit: allow literal
    bch 𝕂 X Y = X + Y :=
  (eq_bch_of_exp_eq (exp_add_of_commute' 𝕂 h) ((norm_add_le X Y).trans_lt hXY)).symm

theorem bch_zero_left {Y : 𝔸} (hY : ‖Y‖ < 1 / 4) :  -- totalisation-audit: allow literal
    bch 𝕂 0 Y = Y := by
  rw [bch_eq_add_of_commute (Commute.zero_left Y) (by simpa using hY), zero_add]

theorem bch_zero_right {X : 𝔸} (hX : ‖X‖ < 1 / 4) :  -- totalisation-audit: allow literal
    bch 𝕂 X 0 = X := by
  rw [bch_eq_add_of_commute (Commute.zero_right X) (by simpa using hX), add_zero]

theorem bch_neg_right {X : 𝔸} (hX : ‖X‖ < 1 / 8) :  -- totalisation-audit: allow literal
    bch 𝕂 X (-X) = 0 := by
  rw [bch_eq_add_of_commute (Commute.neg_right (Commute.refl X)) (by rw [norm_neg]; linarith),
    add_neg_cancel]

/-! ### The power series -/

/-- **The BCH series** is the power series of `(X, Y) ↦ bch 𝕂 X Y` at `0`. -/
theorem hasFPowerSeriesAt_bch :
    HasFPowerSeriesAt (fun v : 𝔸 × 𝔸 => bch 𝕂 v.1 v.2) (bchSeries 𝕂 𝔸) 0 :=
  (hasFPowerSeriesAt_exp_mul_exp (𝕂 := 𝕂) (𝔸 := 𝔸)).log1p_sub_one (by simp)

variable (𝕂 𝔸) in
theorem bchSeries_radius_pos : 0 < (bchSeries 𝕂 𝔸).radius :=
  (hasFPowerSeriesAt_bch (𝕂 := 𝕂) (𝔸 := 𝔸)).radius_pos

variable (𝕂 𝔸) in
/-- **Geometric bound for the BCH coefficients**: `‖bchSeries 𝕂 𝔸 n‖ ≤ K Cⁿ` for all `n`. -/
theorem exists_geometricBound_bchSeries : ∃ K C, GeometricBound (bchSeries 𝕂 𝔸) K C :=
  FormalMultilinearSeries.exists_geometricBound (bchSeries_radius_pos 𝕂 𝔸)

variable (𝕂) in
theorem analyticAt_exp_mul_exp (v : 𝔸 × 𝔸) :
    AnalyticAt 𝕂 (fun w : 𝔸 × 𝔸 => exp w.1 * exp w.2) v :=
  (AnalyticAt.comp (g := exp) (f := Prod.fst) (x := v) (exp_analytic v.1) analyticAt_fst).mul
    (AnalyticAt.comp (g := exp) (f := Prod.snd) (x := v) (exp_analytic v.2) analyticAt_snd)

/-- `bch 𝕂` is analytic wherever `‖exp X exp Y - 1‖ < 1`. -/
theorem analyticAt_bch {v : 𝔸 × 𝔸} (h : ‖exp v.1 * exp v.2 - 1‖ < 1) :
    AnalyticAt 𝕂 (fun w : 𝔸 × 𝔸 => bch 𝕂 w.1 w.2) v :=
  (analyticAt_exp_mul_exp 𝕂 v).log1p_sub_one' 𝕂 h

/-- `bch 𝕂` is analytic on `‖X‖ + ‖Y‖ < log 2`. -/
theorem analyticOnNhd_bch :
    AnalyticOnNhd 𝕂 (fun w : 𝔸 × 𝔸 => bch 𝕂 w.1 w.2)
      {v | ‖v.1‖ + ‖v.2‖ < Real.log 2} :=  -- totalisation-audit: allow log of 2 > 0
  fun _ hv => analyticAt_bch (norm_exp_mul_exp_sub_one_lt 𝕂 hv)

/-! ### Low-order terms -/

omit [CompleteSpace 𝔸] in
@[simp]
theorem bchSeries_zero_apply (v : Fin 0 → 𝔸 × 𝔸) : bchSeries 𝕂 𝔸 0 v = 0 := by
  simp [bchSeries]

omit [CompleteSpace 𝔸] in
/-- The linear term of the BCH series is `X + Y`. -/
theorem bchSeries_one_apply (v : Fin 1 → 𝔸 × 𝔸) : bchSeries 𝕂 𝔸 1 v = (v 0).1 + (v 0).2 := by
  rw [bchSeries, comp_coeff_one, logSeries_apply_eq, logCoeff_one, one_smul, pow_one,
    expMulExpSeries_one_apply]

omit [CompleteSpace 𝔸] in
/-- The quadratic term of the BCH series is `½ [X, Y] = ½ (X Y - Y X)`. -/
theorem bchSeries_two_apply_diag (v : 𝔸 × 𝔸) :
    bchSeries 𝕂 𝔸 2 (fun _ => v) = (2⁻¹ : 𝕂) • (v.1 * v.2 - v.2 * v.1) := by
  rw [bchSeries, comp_coeff_two_apply_diag, logSeries_apply_eq, logSeries_apply_eq, logCoeff_one,
    logCoeff_two, one_smul, pow_one, expMulExpSeries_two_apply_diag, expMulExpSeries_one_apply]
  simp only [sq, add_mul, mul_add]
  module

/-- The derivative of `bch 𝕂` at `0` is `(X, Y) ↦ X + Y`. -/
theorem hasFDerivAt_bch :
    HasFDerivAt (fun v : 𝔸 × 𝔸 => bch 𝕂 v.1 v.2)
      (ContinuousLinearMap.fst 𝕂 𝔸 𝔸 + ContinuousLinearMap.snd 𝕂 𝔸 𝔸) 0 := by
  have h := (hasFPowerSeriesAt_bch (𝕂 := 𝕂) (𝔸 := 𝔸)).hasFDerivAt
  convert h using 1
  refine ContinuousLinearMap.ext fun w => ?_
  rw [continuousMultilinearCurryFin1_apply, bchSeries_one_apply]
  simp

/-- **Second-order Baker–Campbell–Hausdorff formula**:
`bch 𝕂 X Y = X + Y + ½ [X, Y] + O(‖(X, Y)‖³)` as `(X, Y) → 0`. -/
theorem bch_sub_isBigO :
    (fun v : 𝔸 × 𝔸 => bch 𝕂 v.1 v.2 - (v.1 + v.2) - (2⁻¹ : 𝕂) • (v.1 * v.2 - v.2 * v.1))
      =O[𝓝 0] fun v => ‖v‖ ^ 3 := by
  have h := (hasFPowerSeriesAt_bch (𝕂 := 𝕂) (𝔸 := 𝔸)).isBigO_sub_partialSum_pow 3
  convert h using 2 with v
  simp only [zero_add, FormalMultilinearSeries.partialSum, Finset.sum_range_succ,
    Finset.range_zero, Finset.sum_empty, bchSeries_zero_apply, bchSeries_one_apply,
    bchSeries_two_apply_diag]
  abel

end BakerCampbellHausdorff
