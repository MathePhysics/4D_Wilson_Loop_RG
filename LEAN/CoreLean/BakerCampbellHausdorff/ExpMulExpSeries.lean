import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The power series of `(X, Y) ↦ exp X * exp Y`

Let `𝔸` be a normed algebra over `𝕂 = ℝ` or `ℂ`.  We write down an explicit formal multilinear
series `expMulExpSeries 𝕂 𝔸` on `𝔸 × 𝔸` whose `n`-th term, evaluated on the diagonal, is
`∑_{i ≤ n} Xⁱ Yⁿ⁻ⁱ / (i! (n-i)!)`, and show that it is the power series of
`(X, Y) ↦ exp X * exp Y` at `0`, with infinite radius of convergence.

The `n`-th coefficient is a linear combination of the monomial multilinear maps
`blockMul 𝕂 𝔸 n i : (v₁, …, vₙ) ↦ (v₁).1 ⋯ (vᵢ).1 · (vᵢ₊₁).2 ⋯ (vₙ).2`, each of norm at most `1`
(for `n > 0`).  The key analytic input is the Cauchy product formula
`(∑ Xⁱ/i!) (∑ Yʲ/j!) = ∑ₙ ∑_{i ≤ n} Xⁱ Yⁿ⁻ⁱ / (i! (n-i)!)` for absolutely convergent series in a
complete normed ring.

We do not assume `‖1‖ = 1` in `𝔸`.

## Main definitions

* `BakerCampbellHausdorff.blockMul`: the monomial multilinear map `X^i Y^(n-i)`.
* `BakerCampbellHausdorff.expMulExpSeries`: the power series of `exp X * exp Y` at `0`.

## Main results

* `BakerCampbellHausdorff.expMulExpSeries_apply_diag`: the diagonal values of the coefficients.
* `BakerCampbellHausdorff.norm_expMulExpSeries_le`: `‖expMulExpSeries 𝕂 𝔸 n‖ ≤ 2 ^ n / n !`
  for `n > 0`.
* `BakerCampbellHausdorff.expMulExpSeries_radius`: the radius of convergence is `⊤`.
* `BakerCampbellHausdorff.hasFPowerSeriesOnBall_exp_mul_exp`: `(X, Y) ↦ exp X * exp Y` has
  power series `expMulExpSeries 𝕂 𝔸` on the whole space.
* `BakerCampbellHausdorff.expMulExpSeries_zero_apply`, `expMulExpSeries_one_apply`,
  `expMulExpSeries_two_apply_diag`: the coefficients of order `0`, `1`, `2`.
-/

noncomputable section

open Nat NormedSpace

namespace BakerCampbellHausdorff

variable {𝕂 𝔸 : Type*} [RCLike 𝕂] [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸]

/-! ### The monomial multilinear maps -/

variable (𝕂 𝔸) in
/-- The monomial multilinear map `(v₁,…,vₙ) ↦ (v₁).1 ⋯ (vᵢ).1 · (vᵢ₊₁).2 ⋯ (vₙ).2` on
`𝔸 × 𝔸`. -/
def blockMul (n i : ℕ) : ContinuousMultilinearMap 𝕂 (fun _ : Fin n => 𝔸 × 𝔸) 𝔸 :=
  (ContinuousMultilinearMap.mkPiAlgebraFin 𝕂 n 𝔸).compContinuousLinearMap fun k =>
    if (k : ℕ) < i then ContinuousLinearMap.fst 𝕂 𝔸 𝔸 else ContinuousLinearMap.snd 𝕂 𝔸 𝔸

/-- `blockMul 𝕂 𝔸 n i` evaluated at `v` is the ordered product of the first components of
`v 0, …, v (i-1)` followed by the second components of the remaining vectors. -/
theorem blockMul_apply (n i : ℕ) (v : Fin n → 𝔸 × 𝔸) :
    blockMul 𝕂 𝔸 n i v = (List.ofFn fun k => if (k : ℕ) < i then (v k).1 else (v k).2).prod := by
  simp only [blockMul, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiAlgebraFin_apply]
  congr 2
  funext k
  split_ifs <;> rfl

/-- On the diagonal, `blockMul 𝕂 𝔸 n i` is the monomial `X ^ i * Y ^ (n - i)`. -/
theorem blockMul_apply_diag {n i : ℕ} (hi : i ≤ n) (v : 𝔸 × 𝔸) :
    blockMul 𝕂 𝔸 n i (fun _ => v) = v.1 ^ i * v.2 ^ (n - i) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hi
  rw [blockMul_apply, List.ofFn_add, List.prod_append]
  simp [List.prod_replicate]

/-- The first projection `𝔸 × 𝔸 →L[𝕂] 𝔸` has norm at most `1`. -/
theorem norm_fst_le_one : ‖ContinuousLinearMap.fst 𝕂 𝔸 𝔸‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by simpa using norm_fst_le x

/-- The second projection `𝔸 × 𝔸 →L[𝕂] 𝔸` has norm at most `1`. -/
theorem norm_snd_le_one : ‖ContinuousLinearMap.snd 𝕂 𝔸 𝔸‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by simpa using norm_snd_le x

/-- `blockMul 𝕂 𝔸 n i` has norm at most that of the multiplication map `mkPiAlgebraFin`. -/
theorem norm_blockMul_le_norm_mkPiAlgebraFin (n i : ℕ) :
    ‖blockMul 𝕂 𝔸 n i‖ ≤ ‖ContinuousMultilinearMap.mkPiAlgebraFin 𝕂 n 𝔸‖ := by
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  refine mul_le_of_le_one_right (norm_nonneg _) ?_
  refine Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun k _ => ?_
  split_ifs
  · exact norm_fst_le_one
  · exact norm_snd_le_one

/-- A bound on `‖blockMul 𝕂 𝔸 n i‖` valid for all `n` (including `n = 0`, where the norm is
`‖(1 : 𝔸)‖`). -/
theorem norm_blockMul_le_max (n i : ℕ) : ‖blockMul 𝕂 𝔸 n i‖ ≤ max 1 ‖(1 : 𝔸)‖ :=
  (norm_blockMul_le_norm_mkPiAlgebraFin n i).trans
    ContinuousMultilinearMap.norm_mkPiAlgebraFin_le

/-- For `n > 0`, the monomial multilinear map `blockMul 𝕂 𝔸 n i` has norm at most `1`. -/
theorem norm_blockMul_le {n : ℕ} (hn : 0 < n) (i : ℕ) : ‖blockMul 𝕂 𝔸 n i‖ ≤ 1 :=
  (norm_blockMul_le_norm_mkPiAlgebraFin n i).trans
    (ContinuousMultilinearMap.norm_mkPiAlgebraFin_le_of_pos hn)

/-! ### The series `expMulExpSeries` -/

variable (𝕂 𝔸) in
/-- The power series of `(X, Y) ↦ exp X * exp Y` at `0`: its `n`-th coefficient is
`∑_{i ≤ n} (i! (n-i)!)⁻¹ X^i Y^(n-i)` on the diagonal. -/
def expMulExpSeries : FormalMultilinearSeries 𝕂 (𝔸 × 𝔸) 𝔸 := fun n =>
  ∑ i ∈ Finset.range (n + 1), ((i ! : 𝕂)⁻¹ * ((n - i) ! : 𝕂)⁻¹) • blockMul 𝕂 𝔸 n i

/-- The coefficients of `expMulExpSeries` on the diagonal. -/
theorem expMulExpSeries_apply_diag (n : ℕ) (v : 𝔸 × 𝔸) :
    expMulExpSeries 𝕂 𝔸 n (fun _ => v) = ∑ i ∈ Finset.range (n + 1),
      ((i ! : 𝕂)⁻¹ * ((n - i) ! : 𝕂)⁻¹) • (v.1 ^ i * v.2 ^ (n - i)) := by
  simp only [expMulExpSeries, sum_apply, smul_apply]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [blockMul_apply_diag (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))]

/-- The binomial identity `∑_{i ≤ n} 1 / (i! (n-i)!) = 2 ^ n / n!`. -/
theorem sum_range_inv_factorial_mul_inv_factorial (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1),
      ((i ! : ℝ)⁻¹ * ((n - i) ! : ℝ)⁻¹) =  -- totalisation-audit: allow factorials > 0
      2 ^ n / n ! := by  -- totalisation-audit: allow n ! > 0
  have h : ∀ i ∈ Finset.range (n + 1),
      ((i ! : ℝ)⁻¹ * ((n - i) ! : ℝ)⁻¹) =  -- totalisation-audit: allow factorials > 0
        (n.choose i : ℝ) / n ! := by  -- totalisation-audit: allow n ! > 0
    intro i hi
    rw [Nat.cast_choose ℝ (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))]
    field_simp
  simp_rw [Finset.sum_congr rfl h, div_eq_mul_inv, ← Finset.sum_mul, ← Nat.cast_sum,
    Nat.sum_range_choose]
  push_cast
  rfl

/-- If every `blockMul 𝕂 𝔸 n i` has norm at most `C`, then
`‖expMulExpSeries 𝕂 𝔸 n‖ ≤ C * (2 ^ n / n!)`. -/
theorem norm_expMulExpSeries_le_of_forall {n : ℕ} {C : ℝ}
    (hC : ∀ i, ‖blockMul 𝕂 𝔸 n i‖ ≤ C) :
    ‖expMulExpSeries 𝕂 𝔸 n‖ ≤ C * (2 ^ n / n !) := by  -- totalisation-audit: allow n ! > 0
  rw [← sum_range_inv_factorial_mul_inv_factorial, Finset.mul_sum]
  refine (norm_sum_le (E := ContinuousMultilinearMap 𝕂 (fun _ : Fin n => 𝔸 × 𝔸) 𝔸) _ _).trans
    (Finset.sum_le_sum fun i _ => ?_)
  refine (norm_smul_le ((i ! : 𝕂)⁻¹ * ((n - i) ! : 𝕂)⁻¹) (blockMul 𝕂 𝔸 n i)).trans ?_
  rw [norm_mul, norm_inv, norm_inv, RCLike.norm_natCast, RCLike.norm_natCast, mul_comm C]
  exact mul_le_mul_of_nonneg_left (hC i) (by positivity)

/-- **Coefficient bound**: for `n > 0`, `‖expMulExpSeries 𝕂 𝔸 n‖ ≤ 2 ^ n / n!`. -/
theorem norm_expMulExpSeries_le {n : ℕ} (hn : 0 < n) :
    ‖expMulExpSeries 𝕂 𝔸 n‖ ≤ 2 ^ n / n ! := by  -- totalisation-audit: allow n ! > 0
  simpa using norm_expMulExpSeries_le_of_forall (fun i => norm_blockMul_le (𝕂 := 𝕂) (𝔸 := 𝔸) hn i)

/-- A coefficient bound valid for all `n`, including `n = 0`. -/
theorem norm_expMulExpSeries_le_max (n : ℕ) :
    ‖expMulExpSeries 𝕂 𝔸 n‖ ≤
      max 1 ‖(1 : 𝔸)‖ * (2 ^ n / n !) :=  -- totalisation-audit: allow n ! > 0
  norm_expMulExpSeries_le_of_forall fun i => norm_blockMul_le_max n i

/-- The series `expMulExpSeries 𝕂 𝔸` has infinite radius of convergence. -/
theorem expMulExpSeries_radius : (expMulExpSeries 𝕂 𝔸).radius = ⊤ := by
  refine (expMulExpSeries 𝕂 𝔸).radius_eq_top_of_summable_norm fun r => ?_
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    ((Real.summable_pow_div_factorial (2 * r)).mul_left (max 1 ‖(1 : 𝔸)‖))
  calc ‖expMulExpSeries 𝕂 𝔸 n‖ * (r : ℝ) ^ n
      ≤ max 1 ‖(1 : 𝔸)‖ * (2 ^ n / n !) * (r : ℝ) ^ n :=  -- totalisation-audit: allow n ! > 0
        mul_le_mul_of_nonneg_right (norm_expMulExpSeries_le_max n) (by positivity)
    _ = max 1 ‖(1 : 𝔸)‖ * ((2 * r) ^ n / n !) := by ring  -- totalisation-audit: allow n ! > 0

/-! ### `expMulExpSeries` is the power series of `exp X * exp Y` -/

/-- **Cauchy product**: `∑ₙ ∑_{i ≤ n} Xⁱ Yⁿ⁻ⁱ / (i! (n-i)!)` converges to `exp X * exp Y`. -/
theorem hasSum_exp_mul_exp [CompleteSpace 𝔸] (v : 𝔸 × 𝔸) :
    HasSum (fun n => expMulExpSeries 𝕂 𝔸 n fun _ => v) (exp v.1 * exp v.2) := by
  have h := hasSum_sum_range_mul_of_summable_norm (norm_expSeries_summable' (𝕂 := 𝕂) v.1)
    (norm_expSeries_summable' (𝕂 := 𝕂) v.2)
  rw [(exp_series_hasSum_exp' (𝕂 := 𝕂) v.1).tsum_eq,
    (exp_series_hasSum_exp' (𝕂 := 𝕂) v.2).tsum_eq] at h
  convert h using 2 with n
  rw [expMulExpSeries_apply_diag]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_mul_smul_comm]

/-- `(X, Y) ↦ exp X * exp Y` has power series `expMulExpSeries 𝕂 𝔸` at `0`, converging on the
whole space. -/
theorem hasFPowerSeriesOnBall_exp_mul_exp [CompleteSpace 𝔸] :
    HasFPowerSeriesOnBall (fun v : 𝔸 × 𝔸 => exp v.1 * exp v.2) (expMulExpSeries 𝕂 𝔸) 0 ⊤ where
  r_le := expMulExpSeries_radius.ge
  r_pos := ENNReal.zero_lt_top
  hasSum {v} _ := by
    rw [zero_add]
    exact hasSum_exp_mul_exp v

/-- `(X, Y) ↦ exp X * exp Y` has power series `expMulExpSeries 𝕂 𝔸` at `0`. -/
theorem hasFPowerSeriesAt_exp_mul_exp [CompleteSpace 𝔸] :
    HasFPowerSeriesAt (fun v : 𝔸 × 𝔸 => exp v.1 * exp v.2) (expMulExpSeries 𝕂 𝔸) 0 :=
  hasFPowerSeriesOnBall_exp_mul_exp.hasFPowerSeriesAt

/-! ### Low-order coefficients -/

/-- The constant coefficient of `expMulExpSeries` is `1`. -/
theorem expMulExpSeries_zero_apply (v : Fin 0 → 𝔸 × 𝔸) : expMulExpSeries 𝕂 𝔸 0 v = 1 := by
  simp [expMulExpSeries, blockMul_apply]

/-- The linear coefficient of `expMulExpSeries` is `(X, Y) ↦ X + Y`. -/
theorem expMulExpSeries_one_apply (v : Fin 1 → 𝔸 × 𝔸) :
    expMulExpSeries 𝕂 𝔸 1 v = (v 0).1 + (v 0).2 := by
  simp [expMulExpSeries, blockMul_apply, Finset.sum_range_succ, add_comm]

/-- The quadratic coefficient of `expMulExpSeries` on the diagonal is `X²/2 + XY + Y²/2`. -/
theorem expMulExpSeries_two_apply_diag (v : 𝔸 × 𝔸) :
    expMulExpSeries 𝕂 𝔸 2 (fun _ => v) =
      (2⁻¹ : 𝕂) • v.1 ^ 2 + v.1 * v.2 + (2⁻¹ : 𝕂) • v.2 ^ 2 := by
  simp [expMulExpSeries_apply_diag, Finset.sum_range_succ, Nat.factorial]
  abel

end BakerCampbellHausdorff
