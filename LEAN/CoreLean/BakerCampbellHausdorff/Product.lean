import BakerCampbellHausdorff.AnalyticLog

/-!
# The logarithm of a product of exponentials

For `X : Fin m → 𝔸` in a Banach algebra over `𝕂 = ℝ` or `ℂ`, the ordered product
`expProd X = exp (X 0) exp (X 1) ⋯ exp (X (m - 1))` and its logarithm
`bchProd 𝕂 X = log1p 𝕂 (expProd X - 1)`: the `m`-fold Baker–Campbell–Hausdorff function, e.g. the
logarithm of a lattice holonomy `U₁ U₂ U₃ U₄` with `Uᵢ = exp (Xᵢ)`.

## Main results

* `norm_expProd_sub_one_le`: `‖expProd X - 1‖ ≤ e^(∑ ‖Xᵢ‖) - 1`.
* `exp_bchProd`: `∑ ‖Xᵢ‖ < log 2 → exp (bchProd 𝕂 X) = expProd X`.
* `eq_bchProd_of_exp_eq`: the small logarithm is unique: `exp Z = expProd X`, `‖Z‖ < 1/4` imply
  `Z = bchProd 𝕂 X`.
* `analyticAt_expProd`, `analyticAt_bchProd`: analyticity (the latter where
  `‖expProd X - 1‖ < 1`, in particular on `∑ ‖Xᵢ‖ < log 2`).
* `exists_hasFPowerSeriesAt_bchProd`: `bchProd 𝕂` has a power series `(logSeries 𝕂 𝔸).comp p` at
  `0` whose coefficients are geometrically bounded.
* `exists_hasFPowerSeriesAt_bchProd_comp`: the same after composing with a continuous linear map
  `L : E → (Fin m → 𝔸)`, e.g. a chart.
-/

noncomputable section

open NormedSpace FormalMultilinearSeries

namespace BakerCampbellHausdorff

section Algebra

variable {𝔸 : Type*} [NormedRing 𝔸]

/-- The ordered product `exp (X 0) * exp (X 1) * ⋯ * exp (X (m - 1))`. -/
def expProd {m : ℕ} (X : Fin m → 𝔸) : 𝔸 := (List.ofFn fun i => exp (X i)).prod

@[simp]
theorem expProd_zero_length (X : Fin 0 → 𝔸) : expProd X = 1 := by simp [expProd]

theorem expProd_succ {m : ℕ} (X : Fin (m + 1) → 𝔸) :
    expProd X = exp (X 0) * expProd (fun i : Fin m => X i.succ) := by
  simp [expProd, List.ofFn_succ]

@[simp]
theorem expProd_zero {m : ℕ} : expProd (0 : Fin m → 𝔸) = 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [expProd_succ]
    simp only [Pi.zero_apply, exp_zero, one_mul]
    exact ih

theorem expProd_two (X Y : 𝔸) : expProd ![X, Y] = exp X * exp Y := by
  simp [expProd, List.ofFn_succ]

/-- Peeling off the last factor: `expProd X = expProd (init X) * exp (X last)`. -/
theorem expProd_castSucc {m : ℕ} (X : Fin (m + 1) → 𝔸) :
    expProd X = expProd (fun i : Fin m => X i.castSucc) * exp (X (Fin.last m)) := by
  rw [expProd, expProd, List.ofFn_succ', List.prod_concat]

/-- `‖a b - 1‖ + 1 ≤ (‖a - 1‖ + 1) (‖b - 1‖ + 1)`. -/
theorem norm_mul_sub_one_add_one_le (a b : 𝔸) :
    ‖a * b - 1‖ + 1 ≤ (‖a - 1‖ + 1) * (‖b - 1‖ + 1) := by
  have hid : a * b - 1 = (a - 1) * (b - 1) + (a - 1) + (b - 1) := by noncomm_ring
  have h := norm_add₃_le (a := (a - 1) * (b - 1)) (b := a - 1) (c := b - 1)
  rw [← hid] at h
  nlinarith [norm_mul_le (a - 1) (b - 1)]

end Algebra

variable {𝕂 𝔸 : Type*} [RCLike 𝕂] [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [CompleteSpace 𝔸]

section Norm

variable (𝕂)
include 𝕂

/-- `‖exp X₀ ⋯ exp Xₘ₋₁ - 1‖ ≤ e^(∑ ‖Xᵢ‖) - 1`. -/
theorem norm_expProd_sub_one_le {m : ℕ} (X : Fin m → 𝔸) :
    ‖expProd X - 1‖ ≤ Real.exp (∑ i, ‖X i‖) - 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 := norm_exp_sub_one_le 𝕂 (X 0)
    have h2 := ih fun i => X i.succ
    have h3 := norm_mul_sub_one_add_one_le (exp (X 0)) (expProd fun i : Fin m => X i.succ)
    rw [expProd_succ, Fin.sum_univ_succ, Real.exp_add]
    have h4 : ‖exp (X 0) - 1‖ + 1 ≤ Real.exp ‖X 0‖ := by linarith
    have h5 : ‖(expProd fun i : Fin m => X i.succ) - 1‖ + 1 ≤
        Real.exp (∑ i : Fin m, ‖X i.succ‖) := by
      linarith
    have h6 := mul_le_mul h4 h5 (by positivity) (Real.exp_pos _).le
    linarith

end Norm

variable (𝕂) in
/-- The `m`-fold Baker–Campbell–Hausdorff function `log (exp X₀ ⋯ exp Xₘ₋₁)`. -/
def bchProd {m : ℕ} (X : Fin m → 𝔸) : 𝔸 := log1p 𝕂 (expProd X - 1)

omit [CompleteSpace 𝔸] in
@[simp]
theorem bchProd_zero {m : ℕ} : bchProd 𝕂 (0 : Fin m → 𝔸) = 0 := by simp [bchProd]

include 𝕂 in
variable (𝕂) in
theorem norm_expProd_sub_one_lt {m : ℕ} {X : Fin m → 𝔸}
    (h : ∑ i, ‖X i‖ < Real.log 2) :  -- totalisation-audit: allow log of 2 > 0
    ‖expProd X - 1‖ < 1 := by
  have h1 := norm_expProd_sub_one_le 𝕂 X
  have h2 : Real.exp (∑ i, ‖X i‖) < 2 := by
    rwa [← Real.lt_log_iff_exp_lt (by norm_num)]
  linarith

/-- **Exponential form**: `exp (log (exp X₀ ⋯ exp Xₘ₋₁)) = exp X₀ ⋯ exp Xₘ₋₁` for
`∑ ‖Xᵢ‖ < log 2`. -/
theorem exp_bchProd {m : ℕ} {X : Fin m → 𝔸}
    (h : ∑ i, ‖X i‖ < Real.log 2) :  -- totalisation-audit: allow log of 2 > 0
    exp (bchProd 𝕂 X) = expProd X := by
  rw [bchProd, exp_log1p 𝕂 (norm_expProd_sub_one_lt 𝕂 h), add_sub_cancel]

/-- **Uniqueness**: a logarithm of `exp X₀ ⋯ exp Xₘ₋₁` of norm `< 1/4` is `bchProd 𝕂 X`. -/
theorem eq_bchProd_of_exp_eq {m : ℕ} {X : Fin m → 𝔸} {Z : 𝔸} (h : exp Z = expProd X)
    (hZ : ‖Z‖ < 1 / 4) : Z = bchProd 𝕂 X :=  -- totalisation-audit: allow literal
  eq_log1p_of_exp_eq 𝕂 (by rw [h, add_sub_cancel]) hZ

variable (𝕂) in
/-- `X ↦ exp X₀ ⋯ exp Xₘ₋₁` is analytic everywhere. -/
theorem analyticAt_expProd {m : ℕ} (X : Fin m → 𝔸) :
    AnalyticAt 𝕂 (expProd : (Fin m → 𝔸) → 𝔸) X := by
  induction m with
  | zero =>
    have : (expProd : (Fin 0 → 𝔸) → 𝔸) = fun _ => 1 := funext expProd_zero_length
    rw [this]
    exact analyticAt_const
  | succ m ih =>
    let tail : (Fin (m + 1) → 𝔸) →L[𝕂] (Fin m → 𝔸) :=
      ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj i.succ
    have hfun : (expProd : (Fin (m + 1) → 𝔸) → 𝔸) =
        fun Y => exp (Y 0) * expProd (tail Y) := funext fun Y => expProd_succ Y
    rw [hfun]
    have h0 : AnalyticAt 𝕂 (fun Y : Fin (m + 1) → 𝔸 => exp (Y 0)) X :=
      AnalyticAt.comp (g := exp) (f := fun Y : Fin (m + 1) → 𝔸 => Y 0) (x := X)
        (exp_analytic (X 0))
        ((ContinuousLinearMap.proj (R := 𝕂) (φ := fun _ : Fin (m + 1) => 𝔸) 0).analyticAt X)
    have h1 : AnalyticAt 𝕂 (fun Y : Fin (m + 1) → 𝔸 => expProd (tail Y)) X :=
      (ih (tail X)).comp (tail.analyticAt X)
    exact h0.mul h1

/-- `bchProd 𝕂` is analytic wherever `‖exp X₀ ⋯ exp Xₘ₋₁ - 1‖ < 1`. -/
theorem analyticAt_bchProd {m : ℕ} {X : Fin m → 𝔸} (h : ‖expProd X - 1‖ < 1) :
    AnalyticAt 𝕂 (bchProd 𝕂 : (Fin m → 𝔸) → 𝔸) X :=
  (analyticAt_expProd 𝕂 X).log1p_sub_one' 𝕂 h

/-- `bchProd 𝕂` is analytic on `∑ ‖Xᵢ‖ < log 2`. -/
theorem analyticOnNhd_bchProd {m : ℕ} :
    AnalyticOnNhd 𝕂 (bchProd 𝕂 : (Fin m → 𝔸) → 𝔸)
      {X | ∑ i, ‖X i‖ < Real.log 2} :=  -- totalisation-audit: allow log of 2 > 0
  fun _ hX => analyticAt_bchProd (norm_expProd_sub_one_lt 𝕂 hX)

variable (𝕂) in
/-- **Power series with geometric bound**: at `0`, `bchProd 𝕂` has the power series
`(logSeries 𝕂 𝔸).comp p` for a power series `p` of `expProd`, and its coefficients satisfy
`‖(logSeries 𝕂 𝔸).comp p n‖ ≤ K Cⁿ`. -/
theorem exists_hasFPowerSeriesAt_bchProd (m : ℕ) :
    ∃ p : FormalMultilinearSeries 𝕂 (Fin m → 𝔸) 𝔸,
      HasFPowerSeriesAt (bchProd 𝕂 : (Fin m → 𝔸) → 𝔸) ((logSeries 𝕂 𝔸).comp p) 0 ∧
      ∃ K C, GeometricBound ((logSeries 𝕂 𝔸).comp p) K C := by
  obtain ⟨p, hp⟩ := analyticAt_expProd 𝕂 (0 : Fin m → 𝔸)
  exact ⟨p, hp.log1p_sub_one expProd_zero, hp.exists_geometricBound_log expProd_zero⟩

variable (𝕂) in
/-- **Charts**: for a continuous linear map `L : E → (Fin m → 𝔸)` (for instance the link
variables of a plaquette as linear functions of a chart variable), `A ↦ log (exp (L A)₀ ⋯
exp (L A)ₘ₋₁)` has a power series at `0` with geometrically bounded coefficients. -/
theorem exists_hasFPowerSeriesAt_bchProd_comp {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕂 E] {m : ℕ} (L : E →L[𝕂] (Fin m → 𝔸)) :
    ∃ p : FormalMultilinearSeries 𝕂 E 𝔸,
      HasFPowerSeriesAt (fun A => bchProd 𝕂 (L A)) p 0 ∧ ∃ K C, GeometricBound p K C := by
  obtain ⟨q, hq, K, C, hKC⟩ := exists_hasFPowerSeriesAt_bchProd 𝕂 (𝔸 := 𝔸) m
  have hq' : HasFPowerSeriesAt (bchProd 𝕂) ((logSeries 𝕂 𝔸).comp q) (L 0) := by
    rw [map_zero]
    exact hq
  exact ⟨_, hq'.compContinuousLinearMap, K, C * (‖L‖ + 1), hKC.compContinuousLinearMap L⟩

end BakerCampbellHausdorff
