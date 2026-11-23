import BakerCampbellHausdorff.Theorem
import BakerCampbellHausdorff.GroupLaw
import BakerCampbellHausdorff.ExpProdSeries
import Mathlib.Analysis.Analytic.Uniqueness

/-!
# Explicit, uniform constants for the BCH series

All constants here are absolute: they do not depend on `𝔸`, `𝕂`, the arguments, or (for charts)
anything but `m` and `‖L‖`.

The coefficients of the logarithm composed with a power series `P` satisfy
`‖(logSeries 𝕂 𝔸).comp P n‖ ≤ (2 M)ⁿ` whenever `‖P b‖ ≤ Mᵇ` for `b ≥ 1`: every block of a
composition has size `≥ 1`, `‖logSeries k‖ ≤ 1`, and `n` has `2ⁿ⁻¹` compositions.  For the BCH
series (`‖expMulExpSeries b‖ ≤ 2ᵇ / b!`) this gives `‖bchSeries 𝕂 𝔸 n‖ ≤ 4ⁿ`, with `K = 1` and
`C = 4` independent of `𝔸`, of the scalar field and of `X`, `Y`.  The series converges to
`bch 𝕂` on the whole ball `‖(X, Y)‖ < 1/4`, with the explicit tail bound
`‖bch 𝕂 X Y - ∑_{k < N} (bchSeries 𝕂 𝔸 k) (X, Y)‖ ≤ (4 ‖(X, Y)‖)ᴺ / (1 - 4 ‖(X, Y)‖)`.

## Main results

* `norm_logSeries_comp_le`: the composition bound.
* `norm_bchSeries_le`, `geometricBound_bchSeries`: `‖bchSeries 𝕂 𝔸 n‖ ≤ 4ⁿ`.
* `HasFPowerSeriesAt.hasFPowerSeriesOnBall_of_analyticOnNhd`: a power series of a function
  analytic on a ball inside the radius of convergence converges to it on the whole ball.
* `HasFPowerSeriesOnBall.norm_sub_partialSum_le`: tail bound from `‖p n‖ ≤ K Cⁿ`.
* `hasFPowerSeriesOnBall_bch`, `norm_bch_sub_partialSum_le`: convergence of the BCH series on
  `‖(X, Y)‖ < 1/4` with an explicit tail.
* `bchProdSeries`, `norm_bchProdSeries_le`, `geometricBound_bchProdSeries`: the explicit power
  series of `bchProd 𝕂` (`m` factors), with `‖bchProdSeries 𝕂 𝔸 m n‖ ≤ (2 m)ⁿ`.
* `hasFPowerSeriesOnBall_bchProd`, `norm_bchProd_sub_partialSum_le`: convergence on
  `‖X‖ < 1/(2m)` (sup norm) with an explicit tail.
* `bchProdSeries_one_apply`: the first-order term is `∑ᵢ Xᵢ`.
* Charts `L : E →L[𝕂] (Fin m → 𝔸)`: `norm_bchProdSeries_comp_le` (`(2 m ‖L‖)ⁿ`),
  `geometricBound_bchProdSeries_comp`, `bchProdSeries_comp_one_apply` (first-order term
  `∑ᵢ (L A)ᵢ`), `hasFDerivAt_bchProd_comp`, `bchProd_comp_sub_sum_isBigO`
  (`bchProd 𝕂 (L A) = ∑ᵢ (L A)ᵢ + O(‖A‖²)`), `norm_bchProd_comp_sub_partialSum_le`.
-/

noncomputable section

open NormedSpace FormalMultilinearSeries Filter
open scoped Topology ENNReal NNReal Nat

namespace BakerCampbellHausdorff

theorem half_lt_log_two :
    (1 : ℝ) / 2 < Real.log 2 := by  -- totalisation-audit: allow literal; log of 2 > 0
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have h := Real.exp_bound_div_one_sub_of_interval'
    (x := 1 / 2) (by norm_num) (by norm_num)  -- totalisation-audit: allow literal
  norm_num at h
  exact h

section Composition

variable {𝕂 𝔸 F : Type*} [RCLike 𝕂] [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸]
  [NormedAddCommGroup F] [NormedSpace 𝕂 F]

/-- **Composition bound.**  If `‖P b‖ ≤ Mᵇ` for all `b ≥ 1`, then
`‖(logSeries 𝕂 𝔸).comp P n‖ ≤ (2 M)ⁿ` for all `n`. -/
theorem norm_logSeries_comp_le {P : FormalMultilinearSeries 𝕂 F 𝔸} {M : ℝ} (hM : 0 ≤ M)
    (hP : ∀ b, 1 ≤ b → ‖P b‖ ≤ M ^ b) (n : ℕ) :
    ‖(logSeries 𝕂 𝔸).comp P n‖ ≤ (2 * M) ^ n := by
  have hterm : ∀ c : Composition n, ‖(logSeries 𝕂 𝔸).compAlongComposition P c‖ ≤ M ^ n := by
    intro c
    refine (compAlongComposition_norm _ P c).trans ?_
    have h1 : ‖logSeries 𝕂 𝔸 c.length‖ ≤ 1 := norm_logSeries_le_one _
    have h2 : ∏ i, ‖P (c.blocksFun i)‖ ≤ ∏ i, M ^ (c.blocksFun i) :=
      Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun i _ => hP _ (c.one_le_blocksFun i)
    rw [Finset.prod_pow_eq_pow_sum, c.sum_blocksFun] at h2
    calc ‖logSeries 𝕂 𝔸 c.length‖ * ∏ i, ‖P (c.blocksFun i)‖ ≤ 1 * M ^ n :=
          mul_le_mul h1 h2 (Finset.prod_nonneg fun _ _ => norm_nonneg _) zero_le_one
      _ = M ^ n := one_mul _
  calc ‖(logSeries 𝕂 𝔸).comp P n‖
      ≤ ∑ c : Composition n, ‖(logSeries 𝕂 𝔸).compAlongComposition P c‖ := norm_sum_le _ _
    _ ≤ ∑ _c : Composition n, M ^ n := Finset.sum_le_sum fun c _ => hterm c
    _ = (2 : ℝ) ^ (n - 1) * M ^ n := by
        rw [Finset.sum_const, Finset.card_univ, composition_card, nsmul_eq_mul]
        push_cast
        ring
    _ ≤ (2 : ℝ) ^ n * M ^ n := by
        gcongr
        · norm_num
        · omega
    _ = (2 * M) ^ n := (mul_pow _ _ _).symm

end Composition

section Ball

variable {𝕂 E F : Type*} [RCLike 𝕂] [NormedAddCommGroup E] [NormedSpace 𝕂 E]
  [NormedAddCommGroup F] [NormedSpace 𝕂 F]

/-- If `f` has power series `p` at `0` and is analytic on the ball `‖y‖ < ρ` inside the radius of
convergence of `p`, then `p` converges to `f` on the whole ball. -/
theorem _root_.HasFPowerSeriesAt.hasFPowerSeriesOnBall_of_analyticOnNhd [CompleteSpace F]
    {f : E → F} {p : FormalMultilinearSeries 𝕂 E F} (hf : HasFPowerSeriesAt f p 0) {ρ : ℝ}
    (hρ : 0 < ρ) (hρp : ENNReal.ofReal ρ ≤ p.radius)
    (han : AnalyticOnNhd 𝕂 f (Metric.ball 0 ρ)) :
    HasFPowerSeriesOnBall f p 0 (ENNReal.ofReal ρ) := by
  have hρ' : (0 : ℝ≥0∞) < ENNReal.ofReal ρ := ENNReal.ofReal_pos.mpr hρ
  have hp : HasFPowerSeriesOnBall p.sum p 0 (ENNReal.ofReal ρ) :=
    (p.hasFPowerSeriesOnBall (hρ'.trans_le hρp)).mono hρ' hρp
  refine hp.congr ?_
  rw [Metric.eball_ofReal]
  have hev : p.sum =ᶠ[𝓝 0] f := by
    filter_upwards [hf.eventually_hasSum] with y hy
    rw [zero_add] at hy
    exact hy.tsum_eq
  have hsum : AnalyticOnNhd 𝕂 p.sum (Metric.ball 0 ρ) := fun y hy =>
    hp.analyticAt_of_mem (by rwa [Metric.eball_ofReal])
  have hconn : IsPreconnected (Metric.ball (0 : E) ρ) := by
    let _ : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕂 E
    exact (convex_ball (0 : E) ρ).isPreconnected
  exact AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hsum han hconn
    (Metric.mem_ball_self hρ) hev

/-- **Explicit tail bound.**  If `p` converges to `f` on a ball and `‖p n‖ ≤ K Cⁿ`, then for
`C ‖y‖ < 1` in the ball, `‖f y - ∑_{k < N} pₖ (y, …, y)‖ ≤ K (C ‖y‖)ᴺ / (1 - C ‖y‖)`. -/
theorem _root_.HasFPowerSeriesOnBall.norm_sub_partialSum_le {f : E → F}
    {p : FormalMultilinearSeries 𝕂 E F} {r : ℝ≥0∞} (hf : HasFPowerSeriesOnBall f p 0 r)
    {K C : ℝ} (hC : 0 ≤ C) (hp : ∀ n, ‖p n‖ ≤ K * C ^ n) {y : E} (hy : y ∈ Metric.eball 0 r)
    (hCy : C * ‖y‖ < 1) (N : ℕ) :
    ‖f y - p.partialSum N y‖ ≤
      K * (C * ‖y‖) ^ N / (1 - C * ‖y‖) := by  -- totalisation-audit: allow 1 - C ‖y‖ > 0
  have h1 := (hasSum_nat_add_iff' N).mpr (hf.hasSum hy)
  rw [zero_add] at h1
  have hq0 : 0 ≤ C * ‖y‖ := mul_nonneg hC (norm_nonneg y)
  have h2 := (hasSum_geometric_of_lt_one hq0 hCy).mul_left (K * (C * ‖y‖) ^ N)
  refine h1.norm_le_of_bounded h2 fun n => ?_
  calc ‖p (n + N) fun _ => y‖ ≤ ‖p (n + N)‖ * ∏ _i : Fin (n + N), ‖y‖ := (p (n + N)).le_opNorm _
    _ = ‖p (n + N)‖ * ‖y‖ ^ (n + N) := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ ≤ K * C ^ (n + N) * ‖y‖ ^ (n + N) := by gcongr; exact hp _
    _ = K * (C * ‖y‖) ^ N * (C * ‖y‖) ^ n := by ring

end Ball

section BCH

variable {𝕂 𝔸 : Type*} [RCLike 𝕂] [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸]

theorem norm_expMulExpSeries_le_pow {n : ℕ} (hn : 1 ≤ n) :
    ‖expMulExpSeries 𝕂 𝔸 n‖ ≤ (2 : ℝ) ^ n := by
  refine (norm_expMulExpSeries_le (𝕂 := 𝕂) (𝔸 := 𝔸) hn).trans ?_
  exact div_le_self (by positivity)
    (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr n.factorial_ne_zero)

variable (𝕂 𝔸) in
/-- **Explicit BCH coefficient bound**: `‖bchSeries 𝕂 𝔸 n‖ ≤ 4ⁿ`. -/
theorem norm_bchSeries_le (n : ℕ) : ‖bchSeries 𝕂 𝔸 n‖ ≤ (4 : ℝ) ^ n := by
  have h := norm_logSeries_comp_le (𝕂 := 𝕂) (𝔸 := 𝔸) (P := expMulExpSeries 𝕂 𝔸)
    (M := 2) (by norm_num) (fun b hb => norm_expMulExpSeries_le_pow hb) n
  norm_num at h
  exact h

variable (𝕂 𝔸) in
/-- **Uniform geometric bound** `‖bchSeries 𝕂 𝔸 n‖ ≤ 1 · 4ⁿ`, with constants independent of
`𝔸`, `𝕂` and the arguments. -/
theorem geometricBound_bchSeries : GeometricBound (bchSeries 𝕂 𝔸) 1 4 :=
  ⟨zero_le_one, by norm_num, fun n => by rw [one_mul]; exact norm_bchSeries_le 𝕂 𝔸 n⟩

variable (𝕂 𝔸) in
theorem quarter_le_radius_bchSeries :
    ENNReal.ofReal (1 / 4) ≤ (bchSeries 𝕂 𝔸).radius := by  -- totalisation-audit: allow literal
  have h := (geometricBound_bchSeries 𝕂 𝔸).le_radius
    (r := Real.toNNReal (1 / 4))  -- totalisation-audit: allow literal
    (by rw [Real.coe_toNNReal _ (by norm_num)]; norm_num)  -- totalisation-audit: allow literal
  simpa [ENNReal.ofReal] using h

variable [CompleteSpace 𝔸]

/-- **The BCH series converges to `bch` on the ball `‖(X, Y)‖ < 1/4`** (sup norm on `𝔸 × 𝔸`). -/
theorem hasFPowerSeriesOnBall_bch :
    HasFPowerSeriesOnBall (fun v : 𝔸 × 𝔸 => bch 𝕂 v.1 v.2) (bchSeries 𝕂 𝔸) 0
      (ENNReal.ofReal (1 / 4)) := by  -- totalisation-audit: allow literal
  refine hasFPowerSeriesAt_bch.hasFPowerSeriesOnBall_of_analyticOnNhd (by norm_num)
    (quarter_le_radius_bchSeries 𝕂 𝔸) fun v hv => analyticAt_bch ?_
  have hv' : ‖v‖ < 1 / 4 := mem_ball_zero_iff.mp hv  -- totalisation-audit: allow literal
  have h1 : ‖v.1‖ + ‖v.2‖ < Real.log 2 := by  -- totalisation-audit: allow log of 2 > 0
    linarith [norm_fst_le v, norm_snd_le v, half_lt_log_two]
  exact norm_exp_mul_exp_sub_one_lt 𝕂 h1

/-- **Explicit tail of the BCH series**: for `‖(X, Y)‖ < 1/4`,
`‖bch 𝕂 X Y - ∑_{k < N} bchSeries 𝕂 𝔸 k (X, Y)‖ ≤ (4 ‖(X, Y)‖)ᴺ / (1 - 4 ‖(X, Y)‖)`. -/
theorem norm_bch_sub_partialSum_le {v : 𝔸 × 𝔸}
    (hv : ‖v‖ < 1 / 4) (N : ℕ) :  -- totalisation-audit: allow literal
    ‖bch 𝕂 v.1 v.2 - (bchSeries 𝕂 𝔸).partialSum N v‖ ≤
      (4 * ‖v‖) ^ N / (1 - 4 * ‖v‖) := by  -- totalisation-audit: allow 1 - 4 ‖v‖ > 0
  have h := (hasFPowerSeriesOnBall_bch (𝕂 := 𝕂) (𝔸 := 𝔸)).norm_sub_partialSum_le (K := 1)
    (C := 4) (by norm_num) (fun n => by rw [one_mul]; exact norm_bchSeries_le 𝕂 𝔸 n)
    (by rw [Metric.eball_ofReal]; exact mem_ball_zero_iff.mpr hv) (by linarith) N
  simpa using h

end BCH

section Product

variable {𝕂 𝔸 : Type*} [RCLike 𝕂] [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸]

/-- The two-factor case of `bchProd` is `bch`. -/
theorem bchProd_two (X Y : 𝔸) : bchProd 𝕂 ![X, Y] = bch 𝕂 X Y := by
  rw [bchProd, expProd_two, bch]

variable (𝕂 𝔸) in
/-- The **`m`-fold BCH series**: the explicit power series `(logSeries 𝕂 𝔸).comp (expProdSeries
𝕂 𝔸 m)` of `X ↦ log (e^X₀ ⋯ e^Xₘ₋₁)` at `0`. -/
def bchProdSeries (m : ℕ) : FormalMultilinearSeries 𝕂 (Fin m → 𝔸) 𝔸 :=
  (logSeries 𝕂 𝔸).comp (expProdSeries 𝕂 𝔸 m)

theorem norm_expProdSeries_le_pow (m : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    ‖expProdSeries 𝕂 𝔸 m n‖ ≤ (m : ℝ) ^ n := by
  refine (norm_expProdSeries_le m hn).trans ?_
  have h1 : (n !⁻¹ : ℝ) ≤ 1 :=
    inv_le_one_of_one_le₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr n.factorial_ne_zero)
  have h2 : (0 : ℝ) ≤ (m : ℝ) ^ n := by positivity
  nlinarith

variable (𝕂 𝔸) in
/-- **Explicit `m`-fold BCH coefficient bound**: `‖bchProdSeries 𝕂 𝔸 m n‖ ≤ (2 m)ⁿ`. -/
theorem norm_bchProdSeries_le (m n : ℕ) : ‖bchProdSeries 𝕂 𝔸 m n‖ ≤ (2 * (m : ℝ)) ^ n := by
  rw [bchProdSeries]
  exact norm_logSeries_comp_le (P := expProdSeries 𝕂 𝔸 m) (Nat.cast_nonneg m)
    (fun _ hb => norm_expProdSeries_le_pow m hb) n

variable (𝕂 𝔸) in
/-- **Uniform geometric bound** for `m ≥ 1` factors: `K = 1`, `C = 2 m`. -/
theorem geometricBound_bchProdSeries {m : ℕ} (hm : 1 ≤ m) :
    GeometricBound (bchProdSeries 𝕂 𝔸 m) 1 (2 * m) :=
  ⟨zero_le_one, by positivity, fun n => by rw [one_mul]; exact norm_bchProdSeries_le 𝕂 𝔸 m n⟩

theorem inv_two_mul_le_radius_bchProdSeries {m : ℕ} (hm : 1 ≤ m) :
    ENNReal.ofReal (2 * (m : ℝ))⁻¹ ≤ (bchProdSeries 𝕂 𝔸 m).radius := by
  have hm' : (0 : ℝ) < 2 * m := by positivity
  have h := (geometricBound_bchProdSeries 𝕂 𝔸 hm).le_radius (r := Real.toNNReal (2 * (m : ℝ))⁻¹)
    (by rw [Real.coe_toNNReal _ (inv_nonneg.mpr hm'.le), inv_mul_cancel₀ hm'.ne'])
  simpa [ENNReal.ofReal] using h

@[simp]
theorem bchProdSeries_zero_apply (m : ℕ) (v : Fin 0 → (Fin m → 𝔸)) :
    bchProdSeries 𝕂 𝔸 m 0 v = 0 := by
  simp [bchProdSeries]

/-- **First-order term**: `bchProdSeries 𝕂 𝔸 m 1 (X) = ∑ᵢ Xᵢ`. -/
theorem bchProdSeries_one_apply (m : ℕ) (v : Fin 1 → (Fin m → 𝔸)) :
    bchProdSeries 𝕂 𝔸 m 1 v = ∑ i, v 0 i := by
  rw [bchProdSeries, comp_coeff_one, logSeries_apply_eq, logCoeff_one, one_smul, pow_one,
    expProdSeries_one_apply]

variable [CompleteSpace 𝔸]

/-- `bchProdSeries 𝕂 𝔸 m` is the power series of `bchProd 𝕂` at `0`. -/
theorem hasFPowerSeriesAt_bchProdSeries (m : ℕ) :
    HasFPowerSeriesAt (bchProd 𝕂 : (Fin m → 𝔸) → 𝔸) (bchProdSeries 𝕂 𝔸 m) 0 :=
  (hasFPowerSeriesAt_expProd (𝕂 := 𝕂) m).log1p_sub_one expProd_zero

omit [CompleteSpace 𝔸] in
theorem sum_norm_le_card_mul_norm {m : ℕ} (X : Fin m → 𝔸) : ∑ i, ‖X i‖ ≤ m * ‖X‖ := by
  calc ∑ i, ‖X i‖ ≤ ∑ _i : Fin m, ‖X‖ := Finset.sum_le_sum fun i _ => norm_le_pi_norm X i
    _ = m * ‖X‖ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **The `m`-fold BCH series converges to `bchProd` on the ball `‖X‖ < 1/(2m)`** (sup norm). -/
theorem hasFPowerSeriesOnBall_bchProd {m : ℕ} (hm : 1 ≤ m) :
    HasFPowerSeriesOnBall (bchProd 𝕂 : (Fin m → 𝔸) → 𝔸) (bchProdSeries 𝕂 𝔸 m) 0
      (ENNReal.ofReal (2 * (m : ℝ))⁻¹) := by
  have hm' : (0 : ℝ) < 2 * m := by positivity
  refine (hasFPowerSeriesAt_bchProdSeries m).hasFPowerSeriesOnBall_of_analyticOnNhd
    (inv_pos.mpr hm') (inv_two_mul_le_radius_bchProdSeries hm) fun X hX => ?_
  have hX' : ‖X‖ < (2 * (m : ℝ))⁻¹ := mem_ball_zero_iff.mp hX
  have h1 : 2 * m * ‖X‖ < 1 := by
    have := mul_lt_mul_of_pos_left hX' hm'
    rwa [mul_inv_cancel₀ hm'.ne'] at this
  have h2 : ∑ i, ‖X i‖ < Real.log 2 := by  -- totalisation-audit: allow log of 2 > 0
    linarith [sum_norm_le_card_mul_norm X, half_lt_log_two]
  exact analyticAt_bchProd (norm_expProd_sub_one_lt 𝕂 h2)

/-- **Explicit tail of the `m`-fold series**: for `‖X‖ < 1/(2m)`,
`‖bchProd 𝕂 X - ∑_{k < N} (bchProdSeries 𝕂 𝔸 m k) (X)‖ ≤ (2 m ‖X‖)ᴺ / (1 - 2 m ‖X‖)`. -/
theorem norm_bchProd_sub_partialSum_le {m : ℕ} (hm : 1 ≤ m) {X : Fin m → 𝔸}
    (hX : 2 * m * ‖X‖ < 1) (N : ℕ) :
    ‖bchProd 𝕂 X - (bchProdSeries 𝕂 𝔸 m).partialSum N X‖ ≤
      (2 * m * ‖X‖) ^ N / (1 - 2 * m * ‖X‖) := by  -- totalisation-audit: allow 1 - 2m‖X‖ > 0
  have hm' : (0 : ℝ) < 2 * m := by positivity
  have hX' : X ∈ Metric.eball (0 : Fin m → 𝔸) (ENNReal.ofReal (2 * (m : ℝ))⁻¹) := by
    rw [Metric.eball_ofReal, mem_ball_zero_iff]
    calc ‖X‖ = (2 * (m : ℝ))⁻¹ * (2 * m * ‖X‖) := (inv_mul_cancel_left₀ hm'.ne' _).symm
      _ < (2 * (m : ℝ))⁻¹ * 1 := mul_lt_mul_of_pos_left hX (inv_pos.mpr hm')
      _ = (2 * (m : ℝ))⁻¹ := mul_one _
  have h := (hasFPowerSeriesOnBall_bchProd (𝕂 := 𝕂) (𝔸 := 𝔸) hm).norm_sub_partialSum_le (K := 1)
    (C := 2 * m) hm'.le (fun n => by rw [one_mul]; exact norm_bchProdSeries_le 𝕂 𝔸 m n) hX' hX N
  simpa using h

end Product

section Chart

variable {𝕂 𝔸 E : Type*} [RCLike 𝕂] [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [NormedAddCommGroup E]
  [NormedSpace 𝕂 E] {m : ℕ}

theorem partialSum_compContinuousLinearMap {F G : Type*} [NormedAddCommGroup F]
    [NormedSpace 𝕂 F] [NormedAddCommGroup G] [NormedSpace 𝕂 G] (p : FormalMultilinearSeries 𝕂 F G)
    (L : E →L[𝕂] F) (N : ℕ) (A : E) :
    (p.compContinuousLinearMap L).partialSum N A = p.partialSum N (L A) := by
  simp only [FormalMultilinearSeries.partialSum, compContinuousLinearMap_apply, Function.comp_def]

/-- **Chart version of the explicit bound**: `‖(bchProdSeries ∘ L) n‖ ≤ (2 m ‖L‖)ⁿ`. -/
theorem norm_bchProdSeries_comp_le (L : E →L[𝕂] (Fin m → 𝔸)) (n : ℕ) :
    ‖(bchProdSeries 𝕂 𝔸 m).compContinuousLinearMap L n‖ ≤ (2 * m * ‖L‖) ^ n := by
  calc ‖(bchProdSeries 𝕂 𝔸 m).compContinuousLinearMap L n‖
      ≤ ‖bchProdSeries 𝕂 𝔸 m n‖ * ∏ _i : Fin n, ‖L‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ (2 * (m : ℝ)) ^ n * ‖L‖ ^ n := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        gcongr
        exact norm_bchProdSeries_le 𝕂 𝔸 m n
    _ = (2 * m * ‖L‖) ^ n := (mul_pow _ _ _).symm

/-- Chart version as a `GeometricBound`, with `K = 1` and `C = 2 m (‖L‖ + 1)`. -/
theorem geometricBound_bchProdSeries_comp (hm : 1 ≤ m) (L : E →L[𝕂] (Fin m → 𝔸)) :
    GeometricBound ((bchProdSeries 𝕂 𝔸 m).compContinuousLinearMap L) 1 (2 * m * (‖L‖ + 1)) :=
  (geometricBound_bchProdSeries 𝕂 𝔸 hm).compContinuousLinearMap L

/-- **First-order term in a chart**: the order-one coefficient of `A ↦ bchProd 𝕂 (L A)` is
`A ↦ ∑ᵢ (L A)ᵢ`. -/
theorem bchProdSeries_comp_one_apply (L : E →L[𝕂] (Fin m → 𝔸)) (v : Fin 1 → E) :
    (bchProdSeries 𝕂 𝔸 m).compContinuousLinearMap L 1 v = ∑ i, L (v 0) i := by
  rw [compContinuousLinearMap_apply, bchProdSeries_one_apply]
  rfl

variable [CompleteSpace 𝔸]

theorem hasFPowerSeriesAt_bchProd_comp (L : E →L[𝕂] (Fin m → 𝔸)) :
    HasFPowerSeriesAt (fun A => bchProd 𝕂 (L A))
      ((bchProdSeries 𝕂 𝔸 m).compContinuousLinearMap L) 0 := by
  have h := hasFPowerSeriesAt_bchProdSeries (𝕂 := 𝕂) (𝔸 := 𝔸) m
  rw [← map_zero L] at h
  exact h.compContinuousLinearMap

/-- The derivative of `A ↦ bchProd 𝕂 (L A)` at `0` is `A ↦ ∑ᵢ (L A)ᵢ`. -/
theorem hasFDerivAt_bchProd_comp (L : E →L[𝕂] (Fin m → 𝔸)) :
    HasFDerivAt (fun A => bchProd 𝕂 (L A)) (∑ i, (ContinuousLinearMap.proj i).comp L) 0 := by
  have h := (hasFPowerSeriesAt_bchProd_comp (𝕂 := 𝕂) L).hasFDerivAt
  convert h using 1
  ext A
  rw [continuousMultilinearCurryFin1_apply, bchProdSeries_comp_one_apply]
  simp

/-- **Principal part**: `bchProd 𝕂 (L A) = ∑ᵢ (L A)ᵢ + O(‖A‖²)`. -/
theorem bchProd_comp_sub_sum_isBigO (L : E →L[𝕂] (Fin m → 𝔸)) :
    (fun A => bchProd 𝕂 (L A) - ∑ i, L A i) =O[𝓝 0] fun A => ‖A‖ ^ 2 := by
  have h := (hasFPowerSeriesAt_bchProd_comp (𝕂 := 𝕂) L).isBigO_sub_partialSum_pow 2
  convert h using 2 with A
  simp only [zero_add, FormalMultilinearSeries.partialSum, Finset.sum_range_succ,
    Finset.range_zero, Finset.sum_empty, bchProdSeries_comp_one_apply]
  rw [compContinuousLinearMap_apply, bchProdSeries_zero_apply, zero_add]

/-- **Explicit tail in a chart**: for `2 m ‖L A‖ < 1`,
`‖bchProd 𝕂 (L A) - ∑_{k<N} (bchProdSeries ∘ L)ₖ (A)‖ ≤ (2 m ‖L A‖)ᴺ / (1 - 2 m ‖L A‖)`. -/
theorem norm_bchProd_comp_sub_partialSum_le (hm : 1 ≤ m) (L : E →L[𝕂] (Fin m → 𝔸)) {A : E}
    (hA : 2 * m * ‖L A‖ < 1) (N : ℕ) :
    ‖bchProd 𝕂 (L A) - ((bchProdSeries 𝕂 𝔸 m).compContinuousLinearMap L).partialSum N A‖ ≤
      (2 * m * ‖L A‖) ^ N /  -- totalisation-audit: allow 1 - 2m‖L A‖ > 0
        (1 - 2 * m * ‖L A‖) := by
  rw [partialSum_compContinuousLinearMap]
  exact norm_bchProd_sub_partialSum_le hm hA N

end Chart

end BakerCampbellHausdorff
