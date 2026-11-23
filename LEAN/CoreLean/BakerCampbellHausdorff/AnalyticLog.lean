import BakerCampbellHausdorff.LogExp
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Analytic.Constructions

/-!
# The logarithm of an analytic function near `1`

Let `F : E → 𝔸` be analytic at `x` with `F x = 1`, where `𝔸` is a Banach algebra over
`𝕂 = ℝ` or `ℂ`.  Then `y ↦ log1p 𝕂 (F y - 1)` (the logarithm of `F y`) is analytic at `x`, with
power series `(logSeries 𝕂 𝔸).comp p` whenever `p` is a power series of `F` at `x`; its
exponential is `F y` near `x`; and its coefficients are geometrically bounded.  This is the
general form of the analytic Baker–Campbell–Hausdorff theorem (`F (X, Y) = exp X exp Y`, see
`BakerCampbellHausdorff.Theorem`); it applies equally to longer products of exponentials such as
lattice holonomies.

## Main definitions and results

* `GeometricBound p K C`: `‖p n‖ ≤ K Cⁿ` for all `n`, with `K ≥ 0` and `C > 0`.
* `FormalMultilinearSeries.exists_geometricBound`: a series with positive radius has a geometric
  bound; `GeometricBound.le_radius`, `GeometricBound.radius_pos`: conversely.
* `GeometricBound.compContinuousLinearMap`, `GeometricBound.compFormalMultilinearSeries`: the
  bound transfers through a linear chart and through a linear map on the target.
* `HasFPowerSeriesAt.log1p_sub_one`: the power series of `y ↦ log (F y)` is
  `(logSeries 𝕂 𝔸).comp p`.
* `HasFPowerSeriesAt.exists_geometricBound_log`: its coefficients are geometrically bounded.
* `AnalyticAt.log1p_sub_one`, `AnalyticOnNhd.log1p_sub_one`: analyticity.
* `ContinuousAt.eventually_exp_log1p_sub_one`: `exp (log (F y)) = F y` for `y` near `x`.
-/

noncomputable section

open NormedSpace Filter FormalMultilinearSeries
open scoped ENNReal NNReal Topology

namespace BakerCampbellHausdorff

section GeometricBound

variable {𝕂 E F : Type*} [RCLike 𝕂] [NormedAddCommGroup E] [NormedSpace 𝕂 E]
  [NormedAddCommGroup F] [NormedSpace 𝕂 F]

/-- **Geometric coefficient bound**: `‖p n‖ ≤ K Cⁿ` for every `n`. -/
structure GeometricBound (p : FormalMultilinearSeries 𝕂 E F) (K C : ℝ) : Prop where
  /-- The prefactor is nonnegative. -/
  K_nonneg : 0 ≤ K
  /-- The geometric rate is positive. -/
  C_pos : 0 < C
  /-- The bound on the multilinear coefficients. -/
  norm_le : ∀ n, ‖p n‖ ≤ K * C ^ n

/-- A formal multilinear series with positive radius of convergence has geometrically bounded
coefficients. -/
theorem _root_.FormalMultilinearSeries.exists_geometricBound {p : FormalMultilinearSeries 𝕂 E F}
    (hp : 0 < p.radius) : ∃ K C, GeometricBound p K C := by
  obtain ⟨r, hr0, hr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hp
  have hr0' : 0 < r := by exact_mod_cast hr0
  obtain ⟨K, hK, hbound⟩ := p.norm_le_div_pow_of_pos_of_lt_radius hr0' hr
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr0'
  refine ⟨K, (r : ℝ)⁻¹,  -- totalisation-audit: allow r > 0 by hrpos
    ⟨hK.le, inv_pos.mpr hrpos, fun n => ?_⟩⟩
  rw [inv_pow, ← div_eq_mul_inv]
  exact hbound n

/-- Conversely, a geometric bound with rate `C` gives radius at least `1 / C`. -/
theorem GeometricBound.le_radius {p : FormalMultilinearSeries 𝕂 E F} {K C : ℝ}
    (h : GeometricBound p K C) {r : ℝ≥0} (hr : (r : ℝ) * C ≤ 1) : (r : ℝ≥0∞) ≤ p.radius := by
  refine p.le_radius_of_bound K fun n => ?_
  have h0 : (0 : ℝ) ≤ (r : ℝ) * C := mul_nonneg r.coe_nonneg h.C_pos.le
  have h1 : ((r : ℝ) * C) ^ n ≤ 1 := pow_le_one₀ h0 hr
  calc ‖p n‖ * (r : ℝ) ^ n ≤ (K * C ^ n) * (r : ℝ) ^ n := by
        gcongr
        exact h.norm_le n
    _ = K * ((r : ℝ) * C) ^ n := by rw [mul_pow]; ring
    _ ≤ K * 1 := by gcongr; exact h.K_nonneg
    _ = K := mul_one K

theorem GeometricBound.radius_pos {p : FormalMultilinearSeries 𝕂 E F} {K C : ℝ}
    (h : GeometricBound p K C) : 0 < p.radius := by
  have hC := h.C_pos
  have hinv : (0 : ℝ) < C⁻¹ := inv_pos.mpr hC
  have hcoe : ((Real.toNNReal C⁻¹ : ℝ≥0) : ℝ) = C⁻¹ := Real.coe_toNNReal _ hinv.le
  refine lt_of_lt_of_le ?_ (h.le_radius (r := Real.toNNReal C⁻¹) (by
    rw [hcoe, inv_mul_cancel₀ hC.ne']))
  exact_mod_cast Real.toNNReal_pos.mpr hinv

/-- A geometric bound survives precomposition with a continuous linear map `L` (for instance a
chart), with rate `C (‖L‖ + 1)`. -/
theorem GeometricBound.compContinuousLinearMap {E' : Type*} [NormedAddCommGroup E']
    [NormedSpace 𝕂 E'] {p : FormalMultilinearSeries 𝕂 E F} {K C : ℝ} (h : GeometricBound p K C)
    (L : E' →L[𝕂] E) : GeometricBound (p.compContinuousLinearMap L) K (C * (‖L‖ + 1)) where
  K_nonneg := h.K_nonneg
  C_pos := mul_pos h.C_pos (by positivity)
  norm_le n := by
    have hL : ‖L‖ ≤ ‖L‖ + 1 := by linarith
    calc ‖p.compContinuousLinearMap L n‖ ≤ ‖p n‖ * ∏ _i : Fin n, ‖L‖ :=
          ContinuousMultilinearMap.norm_compContinuousLinearMap_le (p n) fun _ => L
      _ = ‖p n‖ * ‖L‖ ^ n := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ ≤ (K * C ^ n) * (‖L‖ + 1) ^ n :=
          mul_le_mul (h.norm_le n) (pow_le_pow_left₀ (norm_nonneg L) hL n) (by positivity)
            (mul_nonneg h.K_nonneg (pow_nonneg h.C_pos.le n))
      _ = K * (C * (‖L‖ + 1)) ^ n := by rw [mul_pow, mul_assoc]

/-- A geometric bound survives postcomposition with a continuous linear map `π` (for instance a
projection to coordinates), with prefactor `‖π‖ K`. -/
theorem GeometricBound.compFormalMultilinearSeries {G : Type*} [NormedAddCommGroup G]
    [NormedSpace 𝕂 G] {p : FormalMultilinearSeries 𝕂 E F} {K C : ℝ} (h : GeometricBound p K C)
    (π : F →L[𝕂] G) : GeometricBound (π.compFormalMultilinearSeries p) (‖π‖ * K) C where
  K_nonneg := mul_nonneg (norm_nonneg π) h.K_nonneg
  C_pos := h.C_pos
  norm_le n := by
    calc ‖π.compFormalMultilinearSeries p n‖ ≤ ‖π‖ * ‖p n‖ :=
          ContinuousLinearMap.norm_compContinuousMultilinearMap_le π (p n)
      _ ≤ ‖π‖ * (K * C ^ n) := mul_le_mul_of_nonneg_left (h.norm_le n) (norm_nonneg π)
      _ = ‖π‖ * K * C ^ n := (mul_assoc _ _ _).symm

end GeometricBound

variable {𝕂 𝔸 E : Type*} [RCLike 𝕂] [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [CompleteSpace 𝔸]
  [NormedAddCommGroup E] [NormedSpace 𝕂 E]

omit [CompleteSpace 𝔸] in
/-- Subtracting the constant `1` changes only the constant coefficient. -/
theorem removeZero_sub_const (p : FormalMultilinearSeries 𝕂 E 𝔸) :
    (p - constFormalMultilinearSeries 𝕂 E (1 : 𝔸)).removeZero = p.removeZero := by
  ext n : 1
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [removeZero_of_pos _ hn, removeZero_of_pos _ hn, FormalMultilinearSeries.sub_apply,
      constFormalMultilinearSeries_apply_of_nonzero hn.ne', sub_zero]

/-- **The power series of the logarithm.**  If `F` has power series `p` at `x` and `F x = 1`, then
`y ↦ log (F y) = log1p 𝕂 (F y - 1)` has power series `(logSeries 𝕂 𝔸).comp p` at `x`. -/
theorem _root_.HasFPowerSeriesAt.log1p_sub_one {F : E → 𝔸} {p : FormalMultilinearSeries 𝕂 E 𝔸}
    {x : E} (hF : HasFPowerSeriesAt F p x) (h1 : F x = 1) :
    HasFPowerSeriesAt (fun y => log1p 𝕂 (F y - 1)) ((logSeries 𝕂 𝔸).comp p) x := by
  have hsub : HasFPowerSeriesAt (fun y => F y - 1)
      (p - constFormalMultilinearSeries 𝕂 E (1 : 𝔸)) x :=
    hF.sub hasFPowerSeriesAt_const
  have hlog : HasFPowerSeriesAt (log1p 𝕂) (logSeries 𝕂 𝔸) (F x - 1) := by
    rw [h1, sub_self]
    exact hasFPowerSeriesAt_log1p
  have h := HasFPowerSeriesAt.comp (f := fun y => F y - 1) (x := x) hlog hsub
  rw [← comp_removeZero, removeZero_sub_const, comp_removeZero] at h
  exact h

/-- **Geometric bound for the logarithm series**: the coefficients of the power series of
`y ↦ log (F y)` satisfy `‖(logSeries 𝕂 𝔸).comp p n‖ ≤ K Cⁿ`. -/
theorem _root_.HasFPowerSeriesAt.exists_geometricBound_log {F : E → 𝔸}
    {p : FormalMultilinearSeries 𝕂 E 𝔸} {x : E} (hF : HasFPowerSeriesAt F p x) (h1 : F x = 1) :
    ∃ K C, GeometricBound ((logSeries 𝕂 𝔸).comp p) K C :=
  FormalMultilinearSeries.exists_geometricBound (hF.log1p_sub_one h1).radius_pos

variable (𝕂) in
/-- The logarithm of an analytic function is analytic where the function is `1`. -/
theorem _root_.AnalyticAt.log1p_sub_one {F : E → 𝔸} {x : E} (hF : AnalyticAt 𝕂 F x)
    (h1 : F x = 1) : AnalyticAt 𝕂 (fun y => log1p 𝕂 (F y - 1)) x := by
  obtain ⟨p, hp⟩ := hF
  exact (hp.log1p_sub_one h1).analyticAt

variable (𝕂) in
/-- The logarithm of an analytic function is analytic wherever `‖F y - 1‖ < 1`. -/
theorem _root_.AnalyticAt.log1p_sub_one' {F : E → 𝔸} {x : E} (hF : AnalyticAt 𝕂 F x)
    (h1 : ‖F x - 1‖ < 1) : AnalyticAt 𝕂 (fun y => log1p 𝕂 (F y - 1)) x :=
  AnalyticAt.comp (g := log1p 𝕂) (f := fun y => F y - 1) (x := x) (analyticAt_log1p h1)
    (hF.sub analyticAt_const)

variable (𝕂) in
theorem _root_.AnalyticOnNhd.log1p_sub_one {F : E → 𝔸} {s : Set E} (hF : AnalyticOnNhd 𝕂 F s)
    (h1 : ∀ y ∈ s, ‖F y - 1‖ < 1) : AnalyticOnNhd 𝕂 (fun y => log1p 𝕂 (F y - 1)) s :=
  fun y hy => (hF y hy).log1p_sub_one' 𝕂 (h1 y hy)

variable (𝕂) in
/-- `exp (log (F y)) = F y` for `y` near a point where `F = 1`. -/
theorem _root_.ContinuousAt.eventually_exp_log1p_sub_one {X : Type*} [TopologicalSpace X]
    {F : X → 𝔸} {x : X} (hF : ContinuousAt F x) (h1 : F x = 1) :
    ∀ᶠ y in 𝓝 x, exp (log1p 𝕂 (F y - 1)) = F y := by
  have hc : ContinuousAt (fun y => F y - 1) x := hF.sub continuousAt_const
  have hball : ∀ᶠ y in 𝓝 x, F y - 1 ∈ Metric.ball (0 : 𝔸) 1 :=
    hc.preimage_mem_nhds (by rw [h1, sub_self]; exact Metric.ball_mem_nhds 0 one_pos)
  filter_upwards [hball] with y hy
  rw [exp_log1p 𝕂 (mem_ball_zero_iff.mp hy), add_sub_cancel]

end BakerCampbellHausdorff
