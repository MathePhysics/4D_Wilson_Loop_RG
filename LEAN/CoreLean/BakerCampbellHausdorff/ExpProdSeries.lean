import BakerCampbellHausdorff.MulSeries
import BakerCampbellHausdorff.Product
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Normed.Algebra.Exponential

/-!
# The explicit power series of a product of exponentials

For a Banach algebra `𝔸` over `𝕂 = ℝ` or `ℂ` and `X : Fin m → 𝔸`, the ordered product
`expProd X = exp (X 0) exp (X 1) ⋯ exp (X (m - 1))` is an entire function of `X`.  We write down
its power series `expProdSeries 𝕂 𝔸 m` at `0` explicitly, by recursion on `m`, as an iterated
Cauchy product (`mulSeries`) of exponential series, and prove the multinomial coefficient bound
`‖(expProdSeries 𝕂 𝔸 m)ₙ‖ ≤ mⁿ / n!` for `n ≥ 1`.

We do not assume `‖1‖ = 1` in `𝔸`.  The space `Fin m → 𝔸` carries the sup norm.

## Main definitions

* `BakerCampbellHausdorff.finTailL`: the continuous linear map `X ↦ (X 1, …, X m)`.
* `BakerCampbellHausdorff.expProdSeries`: the power series of `expProd` at `0`.

## Main results

* `BakerCampbellHausdorff.hasFPowerSeriesOnBall_expProd`: `expProd` has power series
  `expProdSeries 𝕂 𝔸 m` on the whole space `Fin m → 𝔸`.
* `BakerCampbellHausdorff.expProdSeries_zero_apply`: the constant coefficient is `1`.
* `BakerCampbellHausdorff.norm_expProdSeries_le`: `‖(expProdSeries 𝕂 𝔸 m)ₙ‖ ≤ mⁿ / n!` for
  `n ≥ 1`.
* `BakerCampbellHausdorff.expProdSeries_one_apply`: the linear coefficient is `X ↦ ∑ᵢ Xᵢ`.

## Proof sketch

`expProdSeries 𝕂 𝔸 0` is the constant series `1`, and `expProdSeries 𝕂 𝔸 (m + 1)` is the Cauchy
product of the exponential series composed with the projection `X ↦ X 0` and of
`expProdSeries 𝕂 𝔸 m` composed with the tail map `X ↦ (X 1, …, X m)`.  Since
`expProd X = exp (X 0) * expProd (X 1, …, X m)` (`expProd_succ`), the power series statement
follows by induction from `exp_hasFPowerSeriesOnBall`,
`HasFPowerSeriesOnBall.compContinuousLinearMap` and `HasFPowerSeriesOnBall.mulSeries`.  The
projection and the tail map have norm at most `1`, and `‖(expSeries 𝕂 𝔸)ₙ‖ ≤ 1 / n!` for
`n ≥ 1`, so `norm_mulSeries_le` with `a = 1`, `b = m` gives the bound `(m + 1)ⁿ / n!` inductively.
-/

noncomputable section

open NormedSpace
open scoped Nat ENNReal

namespace BakerCampbellHausdorff

variable {𝕂 𝔸 : Type*} [RCLike 𝕂] [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸]

/-! ### Projections -/

/-- A coordinate projection `(Fin m → 𝔸) →L[𝕂] 𝔸` has norm at most `1`. -/
theorem norm_proj_le_one {m : ℕ} (i : Fin m) :
    ‖(ContinuousLinearMap.proj i : (Fin m → 𝔸) →L[𝕂] 𝔸)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun X => by
    simpa using norm_le_pi_norm X i

variable (𝕂 𝔸) in
/-- The tail map `X ↦ (X 1, …, X m)` as a continuous linear map. -/
def finTailL (m : ℕ) : (Fin (m + 1) → 𝔸) →L[𝕂] (Fin m → 𝔸) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj i.succ

@[simp]
theorem finTailL_apply (m : ℕ) (X : Fin (m + 1) → 𝔸) : finTailL 𝕂 𝔸 m X = fun i => X i.succ :=
  rfl

/-- The tail map has norm at most `1`. -/
theorem norm_finTailL_le (m : ℕ) : ‖finTailL 𝕂 𝔸 m‖ ≤ 1 :=
  ContinuousLinearMap.norm_pi_le_of_le (fun i => norm_proj_le_one i.succ) zero_le_one

/-! ### The exponential series -/

/-- The constant coefficient of the exponential series is `1`. -/
theorem expSeries_zero_apply_eq_one (v : Fin 0 → 𝔸) : expSeries 𝕂 𝔸 0 v = 1 := by
  simp [expSeries]

/-- For `n ≥ 1`, `‖(expSeries 𝕂 𝔸)ₙ‖ ≤ 1 / n!` (no factor `‖1‖`). -/
theorem norm_expSeries_le_inv_factorial {n : ℕ} (hn : 1 ≤ n) :
    ‖expSeries 𝕂 𝔸 n‖ ≤ (n !⁻¹ : ℝ) := by
  refine (norm_smul_le (n !⁻¹ : 𝕂) (ContinuousMultilinearMap.mkPiAlgebraFin 𝕂 n 𝔸)).trans ?_
  rw [norm_inv, RCLike.norm_natCast]
  exact mul_le_of_le_one_right (by positivity)
    (ContinuousMultilinearMap.norm_mkPiAlgebraFin_le_of_pos hn)

/-! ### The series `expProdSeries` -/

variable (𝕂 𝔸) in
/-- Explicit power series of `expProd` at `0`, by recursion on `m`: the constant series `1` for
`m = 0`, and the Cauchy product of `exp (X 0)` and `expProd (X 1, …, X m)` for `m + 1`. -/
def expProdSeries : (m : ℕ) → FormalMultilinearSeries 𝕂 (Fin m → 𝔸) 𝔸
  | 0 => constFormalMultilinearSeries 𝕂 (Fin 0 → 𝔸) 1
  | m + 1 => mulSeries ((expSeries 𝕂 𝔸).compContinuousLinearMap (ContinuousLinearMap.proj 0))
      ((expProdSeries m).compContinuousLinearMap (finTailL 𝕂 𝔸 m))

/-- The recursive step of `expProdSeries`: a Cauchy product of `exp (X 0)` and the tail. -/
theorem expProdSeries_succ (m : ℕ) :
    expProdSeries 𝕂 𝔸 (m + 1) =
      mulSeries ((expSeries 𝕂 𝔸).compContinuousLinearMap (ContinuousLinearMap.proj 0))
        ((expProdSeries 𝕂 𝔸 m).compContinuousLinearMap (finTailL 𝕂 𝔸 m)) :=
  rfl

/-- The constant coefficient of `expProdSeries 𝕂 𝔸 m` is `1`. -/
theorem expProdSeries_zero_apply (m : ℕ) (v : Fin 0 → (Fin m → 𝔸)) :
    expProdSeries 𝕂 𝔸 m 0 v = 1 := by
  induction m with
  | zero => simp [expProdSeries]
  | succ m ih =>
    rw [expProdSeries_succ]
    refine mulSeries_zero_apply (fun w => ?_) (fun w => ?_) v
    · exact expSeries_zero_apply_eq_one _
    · exact ih _

/-- **Power series of a product of exponentials**: `X ↦ exp (X 0) ⋯ exp (X (m - 1))` has power
series `expProdSeries 𝕂 𝔸 m` at `0`, converging on the whole space. -/
theorem hasFPowerSeriesOnBall_expProd [CompleteSpace 𝔸] (m : ℕ) :
    HasFPowerSeriesOnBall (expProd : (Fin m → 𝔸) → 𝔸) (expProdSeries 𝕂 𝔸 m) 0 ⊤ := by
  induction m with
  | zero =>
    have : (expProd : (Fin 0 → 𝔸) → 𝔸) = fun _ => 1 := funext expProd_zero_length
    rw [this]
    exact hasFPowerSeriesOnBall_const
  | succ m ih =>
    have hfun : (expProd : (Fin (m + 1) → 𝔸) → 𝔸) =
        fun Y => exp (Y 0) * expProd (finTailL 𝕂 𝔸 m Y) := funext fun Y => expProd_succ Y
    have h0 := (exp_hasFPowerSeriesOnBall (𝕂 := 𝕂) (𝔸 := 𝔸)).compContinuousLinearMap
      (u := ContinuousLinearMap.proj (R := 𝕂) (φ := fun _ : Fin (m + 1) => 𝔸) 0) (x := 0)
    have h1 := ih.compContinuousLinearMap (u := finTailL 𝕂 𝔸 m) (x := 0)
    rw [ENNReal.top_div_of_ne_top enorm_ne_top] at h0 h1
    rw [hfun, expProdSeries_succ]
    exact h0.mulSeries h1

/-- `X ↦ exp (X 0) ⋯ exp (X (m - 1))` has power series `expProdSeries 𝕂 𝔸 m` at `0`. -/
theorem hasFPowerSeriesAt_expProd [CompleteSpace 𝔸] (m : ℕ) :
    HasFPowerSeriesAt (expProd : (Fin m → 𝔸) → 𝔸) (expProdSeries 𝕂 𝔸 m) 0 :=
  (hasFPowerSeriesOnBall_expProd m).hasFPowerSeriesAt

/-- **Multinomial coefficient bound**: `‖(expProdSeries 𝕂 𝔸 m)ₙ‖ ≤ mⁿ / n!` for `n ≥ 1`. -/
theorem norm_expProdSeries_le (m : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    ‖expProdSeries 𝕂 𝔸 m n‖ ≤ (n !⁻¹ : ℝ) * (m : ℝ) ^ n := by
  induction m generalizing n with
  | zero =>
    have h : expProdSeries 𝕂 𝔸 0 n = 0 := constFormalMultilinearSeries_apply_of_nonzero (by omega)
    rw [h, ContinuousMultilinearMap.opNorm_zero]
    positivity
  | succ m ih =>
    rw [expProdSeries_succ, Nat.cast_succ, add_comm (m : ℝ)]
    refine norm_mulSeries_le (fun w => expSeries_zero_apply_eq_one _)
      (fun w => expProdSeries_zero_apply m _) (fun k hk => ?_) (fun k hk => ?_) hn
    · refine ((expSeries 𝕂 𝔸).norm_compContinuousLinearMap_le _ k).trans ?_
      rw [one_pow, mul_one]
      exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _)
        (norm_proj_le_one 0)) |>.trans (norm_expSeries_le_inv_factorial hk)
    · refine ((expProdSeries 𝕂 𝔸 m).norm_compContinuousLinearMap_le _ k).trans ?_
      exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _)
        (norm_finTailL_le m)) |>.trans (ih hk)

/-- The linear coefficient of `expProdSeries 𝕂 𝔸 m` is `X ↦ ∑ᵢ Xᵢ`. -/
theorem expProdSeries_one_apply (m : ℕ) (v : Fin 1 → (Fin m → 𝔸)) :
    expProdSeries 𝕂 𝔸 m 1 v = ∑ i, v 0 i := by
  induction m with
  | zero => simp [expProdSeries]
  | succ m ih =>
    rw [show v = fun _ => v 0 from funext fun i => congrArg v (Subsingleton.elim i 0),
      expProdSeries_succ, mulSeries_apply_diag, Finset.Nat.sum_antidiagonal_succ,
      Finset.Nat.antidiagonal_zero, Finset.sum_singleton, Fin.sum_univ_succ]
    simp only [FormalMultilinearSeries.compContinuousLinearMap_apply, Function.comp_def,
      expSeries_zero_apply_eq_one, expProdSeries_zero_apply, one_mul, mul_one]
    rw [ih, expSeries_apply_eq, add_comm]
    simp

end BakerCampbellHausdorff
