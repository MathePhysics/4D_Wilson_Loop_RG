module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-!
# The one-dimensional lattice heat kernel

`heatKernel1 t n = q_t(n) = (1/2π) ∫_{-π}^{π} cos(nθ) e^{-2t(1-cos θ)} dθ`, the transition
probabilities of the continuous-time simple random walk on `ℤ` with jump rate `1` in each
direction.  This file proves `q_t(n) ≥ 0`, `∑ₙ q_t(n) = 1`, `q_0 = δ₀`, continuity and the
heat equation `∂_t q_t(n) = q_t(n+1) + q_t(n-1) - 2 q_t(n)`.

Provenance: copied unchanged from `Balaban/Green/Lattice/HeatKernel.lean` of
https://github.com/scottnarmstrong/balaban-lean at commit
`493e9eb97292ebf6070c1c217a09bcf1adc23857`, Apache License 2.0 (`LICENSE-balaban-lean`).
-/

@[expose] public section

noncomputable section

namespace Balaban.LatticeGreen

open MeasureTheory Real

/-- The symbol `e^{-2t(1-cos θ)}` of the heat semigroup of the one-dimensional lattice Laplacian. -/
def heatSymbol (t θ : ℝ) : ℝ := Real.exp (-(2 * t * (1 - Real.cos θ)))

/-- The one-dimensional lattice heat kernel `q_t(n)`. -/
def heatKernel1 (t : ℝ) (n : ℤ) : ℝ :=
  (2 * π)⁻¹ * ∫ θ in (-π)..π, Real.cos ((n : ℝ) * θ) * heatSymbol t θ

/-- `∫_{-π}^{π} cos(nθ) cos(θ)^k dθ`. -/
def cosPowInt (k : ℕ) (n : ℤ) : ℝ :=
  ∫ θ in (-π)..π, Real.cos ((n : ℝ) * θ) * Real.cos θ ^ k

theorem cosPowInt_zero (n : ℤ) : cosPowInt 0 n = if n = 0 then 2 * π else 0 := by
  unfold cosPowInt
  by_cases hn : n = 0
  · simp [hn]; ring
  · have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    simp only [pow_zero, mul_one, hn, ite_false]
    rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hn', integral_cos]
    have h1 : Real.sin ((n : ℝ) * π) = 0 := by
      simp
    have h2 : Real.sin ((n : ℝ) * -π) = 0 := by
      rw [mul_neg, Real.sin_neg, h1, neg_zero]
    rw [h1, h2]; simp

theorem cos_mul_cos_int (n : ℤ) (θ : ℝ) :
    Real.cos ((n : ℝ) * θ) * Real.cos θ =
      (Real.cos (((n + 1 : ℤ) : ℝ) * θ) + Real.cos (((n - 1 : ℤ) : ℝ) * θ)) / 2 := by
  push_cast
  rw [add_mul, sub_mul, one_mul, Real.cos_add, Real.cos_sub]
  ring

theorem cosPowInt_succ (k : ℕ) (n : ℤ) :
    cosPowInt (k + 1) n = (cosPowInt k (n + 1) + cosPowInt k (n - 1)) / 2 := by
  unfold cosPowInt
  have hc : ∀ m : ℤ, Continuous fun θ : ℝ => Real.cos ((m : ℝ) * θ) * Real.cos θ ^ k := by
    intro m; fun_prop
  have : ∀ θ : ℝ, Real.cos ((n : ℝ) * θ) * Real.cos θ ^ (k + 1) =
      (Real.cos (((n + 1 : ℤ) : ℝ) * θ) * Real.cos θ ^ k +
        Real.cos (((n - 1 : ℤ) : ℝ) * θ) * Real.cos θ ^ k) / 2 := by
    intro θ
    have := cos_mul_cos_int n θ
    calc Real.cos ((n : ℝ) * θ) * Real.cos θ ^ (k + 1)
        = (Real.cos ((n : ℝ) * θ) * Real.cos θ) * Real.cos θ ^ k := by ring
      _ = _ := by rw [this]; ring
  simp_rw [this]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add
    ((hc _).intervalIntegrable _ _) ((hc _).intervalIntegrable _ _)]

theorem cosPowInt_nonneg (k : ℕ) : ∀ n : ℤ, 0 ≤ cosPowInt k n := by
  induction k with
  | zero => intro n; rw [cosPowInt_zero]; split_ifs <;> positivity
  | succ k ih => intro n; rw [cosPowInt_succ]; have := ih (n + 1); have := ih (n - 1); positivity

theorem cosPowInt_eq_zero (k : ℕ) : ∀ n : ℤ, k < n.natAbs → cosPowInt k n = 0 := by
  induction k with
  | zero =>
    intro n hn
    have hn0 : n ≠ 0 := by rintro rfl; simp at hn
    simp [cosPowInt_zero, hn0]
  | succ k ih =>
    intro n hn
    rw [cosPowInt_succ, ih (n + 1) (by omega), ih (n - 1) (by omega)]; simp

theorem cosPowInt_symm (k : ℕ) (n : ℤ) : cosPowInt k (-n) = cosPowInt k n := by
  unfold cosPowInt; simp

theorem summable_cosPowInt (k : ℕ) : Summable (cosPowInt k) := by
  refine summable_of_ne_finset_zero (s := Finset.Icc (-(k : ℤ)) k) fun n hn => ?_
  apply cosPowInt_eq_zero
  simp only [Finset.mem_Icc, not_and_or, not_le] at hn
  omega

theorem tsum_cosPowInt (k : ℕ) : ∑' n, cosPowInt k n = 2 * π := by
  induction k with
  | zero =>
    rw [tsum_eq_single 0]
    · simp [cosPowInt_zero]
    · intro n hn; simp [cosPowInt_zero, hn]
  | succ k ih =>
    have e1 : ∑' n : ℤ, cosPowInt k (n + 1) = ∑' n, cosPowInt k n :=
      (Equiv.addRight (1 : ℤ)).tsum_eq (cosPowInt k)
    have e2 : ∑' n : ℤ, cosPowInt k (n - 1) = ∑' n, cosPowInt k n :=
      (Equiv.subRight (1 : ℤ)).tsum_eq (cosPowInt k)
    have s1 : Summable fun n : ℤ => cosPowInt k (n + 1) :=
      (summable_cosPowInt k).comp_injective (add_left_injective (1 : ℤ))
    have s2 : Summable fun n : ℤ => cosPowInt k (n - 1) :=
      (summable_cosPowInt k).comp_injective (sub_left_injective (b := (1 : ℤ)))
    simp_rw [cosPowInt_succ]
    rw [tsum_div_const, s1.tsum_add s2, e1, e2, ih]; ring

theorem heatSymbol_eq (t θ : ℝ) :
    heatSymbol t θ = Real.exp (-(2 * t)) * Real.exp (2 * t * Real.cos θ) := by
  unfold heatSymbol; rw [← Real.exp_add]; congr 1; ring

theorem hasSum_cosPowInt_series {t : ℝ} (ht : 0 ≤ t) (n : ℤ) :
    HasSum (fun k : ℕ => (2 * t) ^ k / (k.factorial : ℝ) * cosPowInt k n)
      (∫ θ in (-π)..π, Real.cos ((n : ℝ) * θ) * Real.exp (2 * t * Real.cos θ)) := by
  have hsum : Summable fun k : ℕ => (2 * t) ^ k / (k.factorial : ℝ) :=
    Real.summable_pow_div_factorial (2 * t)
  have hex : ∑' k : ℕ, (2 * t) ^ k / (k.factorial : ℝ) = Real.exp (2 * t) := by
    have := NormedSpace.expSeries_div_hasSum_exp (2 * t)
    rw [← Real.exp_eq_exp_ℝ] at this
    exact this.tsum_eq
  have h := intervalIntegral.hasSum_integral_of_dominated_convergence
    (μ := volume) (a := -π) (b := π)
    (F := fun (k : ℕ) (θ : ℝ) =>
      Real.cos ((n : ℝ) * θ) * ((2 * t * Real.cos θ) ^ k / (k.factorial : ℝ)))
    (f := fun θ => Real.cos ((n : ℝ) * θ) * Real.exp (2 * t * Real.cos θ))
    (fun k θ => (2 * t) ^ k / (k.factorial : ℝ))
    (fun k => by fun_prop)
    (fun k => Filter.Eventually.of_forall fun θ _ => by
      rw [norm_mul, norm_div, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_mul, mul_pow, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (k.factorial : ℝ)),
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * t)]
      have h1 := Real.abs_cos_le_one ((n : ℝ) * θ)
      have h2 : |Real.cos θ| ^ k ≤ 1 := pow_le_one₀ (abs_nonneg _) (Real.abs_cos_le_one θ)
      have h3 : (0 : ℝ) ≤ (2 * t) ^ k / (k.factorial : ℝ) := by positivity
      calc |Real.cos ((n : ℝ) * θ)| * ((2 * t) ^ k * |Real.cos θ| ^ k / (k.factorial : ℝ))
          = |Real.cos ((n : ℝ) * θ)| * ((2 * t) ^ k / (k.factorial : ℝ) * |Real.cos θ| ^ k) := by
            ring
        _ ≤ 1 * ((2 * t) ^ k / (k.factorial : ℝ) * 1) := by gcongr
        _ = _ := by ring)
    (Filter.Eventually.of_forall fun θ _ => hsum)
    (by rw [hex]; exact intervalIntegrable_const)
    (Filter.Eventually.of_forall fun θ _ => by
      have := NormedSpace.expSeries_div_hasSum_exp (2 * t * Real.cos θ)
      rw [← Real.exp_eq_exp_ℝ] at this
      exact this.mul_left _)
  convert h using 1
  funext k
  rw [cosPowInt, ← intervalIntegral.integral_const_mul]
  congr 1; funext θ
  ring

/-- The Poisson-weighted series for `q_t(n)`. -/
theorem hasSum_heatKernel1_series {t : ℝ} (ht : 0 ≤ t) (n : ℤ) :
    HasSum (fun k : ℕ => (2 * π)⁻¹ * Real.exp (-(2 * t)) * ((2 * t) ^ k / (k.factorial : ℝ)) *
      cosPowInt k n) (heatKernel1 t n) := by
  have h := (hasSum_cosPowInt_series ht n).mul_left ((2 * π)⁻¹ * Real.exp (-(2 * t)))
  have e : heatKernel1 t n =
      (2 * π)⁻¹ * Real.exp (-(2 * t)) *
        ∫ θ in (-π)..π, Real.cos ((n : ℝ) * θ) * Real.exp (2 * t * Real.cos θ) := by
    unfold heatKernel1
    have : ∀ θ : ℝ, Real.cos ((n : ℝ) * θ) * heatSymbol t θ =
        Real.exp (-(2 * t)) * (Real.cos ((n : ℝ) * θ) * Real.exp (2 * t * Real.cos θ)) :=
      fun θ => by rw [heatSymbol_eq]; ring
    simp_rw [this]
    rw [intervalIntegral.integral_const_mul]; ring
  rw [e]
  convert h using 2 with k
  ring

theorem heatKernel1_nonneg {t : ℝ} (ht : 0 ≤ t) (n : ℤ) : 0 ≤ heatKernel1 t n :=
  (hasSum_heatKernel1_series ht n).nonneg fun k => by
    have := cosPowInt_nonneg k n
    positivity

/-- The Poisson weights `e^{-2t}(2t)^k/k!/(2π)`. -/
def heatWeight (t : ℝ) (k : ℕ) : ℝ :=
  (2 * π)⁻¹ * Real.exp (-(2 * t)) * ((2 * t) ^ k / (k.factorial : ℝ))

theorem heatWeight_nonneg {t : ℝ} (ht : 0 ≤ t) (k : ℕ) : 0 ≤ heatWeight t k := by
  unfold heatWeight; positivity

theorem summable_heatWeight (t : ℝ) : Summable (heatWeight t) := by
  have := (Real.summable_pow_div_factorial (2 * t)).mul_left ((2 * π)⁻¹ * Real.exp (-(2 * t)))
  exact this

theorem hasSum_heatKernel1 {t : ℝ} (ht : 0 ≤ t) : HasSum (fun n : ℤ => heatKernel1 t n) 1 := by
  have hw0 : ∀ k, 0 ≤ heatWeight t k := heatWeight_nonneg ht
  have hsw := summable_heatWeight t
  have hf0 : ∀ p : ℕ × ℤ, 0 ≤ heatWeight t p.1 * cosPowInt p.1 p.2 := fun p =>
    mul_nonneg (hw0 _) (cosPowInt_nonneg _ _)
  have hinner : ∀ k, ∑' n, heatWeight t k * cosPowInt k n = heatWeight t k * (2 * π) := fun k => by
    rw [tsum_mul_left, tsum_cosPowInt]
  have hfs : Summable fun p : ℕ × ℤ => heatWeight t p.1 * cosPowInt p.1 p.2 := by
    rw [summable_prod_of_nonneg hf0]
    refine ⟨fun k => ?_, ?_⟩
    · exact (summable_cosPowInt k).mul_left (heatWeight t k)
    · have : (fun k : ℕ => ∑' n, heatWeight t k * cosPowInt k n) =
          fun k => heatWeight t k * (2 * π) := funext hinner
      rw [this]
      exact hsw.mul_right _
  have hq : ∀ n, heatKernel1 t n = ∑' k, heatWeight t k * cosPowInt k n := fun n =>
    ((hasSum_heatKernel1_series ht n).tsum_eq).symm
  have hfs' : Summable (Function.uncurry fun (n : ℤ) (k : ℕ) =>
      heatWeight t k * cosPowInt k n) := hfs.prod_symm
  have hsn : Summable fun n : ℤ => ∑' k, heatWeight t k * cosPowInt k n := hfs'.prod
  have hex : ∑' k : ℕ, (2 * t) ^ k / (k.factorial : ℝ) = Real.exp (2 * t) := by
    have := NormedSpace.expSeries_div_hasSum_exp (2 * t)
    rw [← Real.exp_eq_exp_ℝ] at this
    exact this.tsum_eq
  have htot : ∑' n : ℤ, ∑' k, heatWeight t k * cosPowInt k n = 1 := by
    rw [← hfs'.tsum_comm]
    simp_rw [hinner]
    rw [tsum_mul_right]
    have : ∑' k, heatWeight t k = (2 * π)⁻¹ * Real.exp (-(2 * t)) * Real.exp (2 * t) := by
      unfold heatWeight; rw [tsum_mul_left, hex]
    have h2 : Real.exp (-(2 * t)) * Real.exp (2 * t) = 1 := by
      rw [← Real.exp_add]; simp
    have hpi : (2 * π) ≠ 0 := by positivity
    rw [this]
    calc (2 * π)⁻¹ * Real.exp (-(2 * t)) * Real.exp (2 * t) * (2 * π)
        = (2 * π)⁻¹ * (2 * π) * (Real.exp (-(2 * t)) * Real.exp (2 * t)) := by ring
      _ = 1 := by rw [h2, inv_mul_cancel₀ hpi, one_mul]
  have : (fun n : ℤ => heatKernel1 t n) = fun n => ∑' k, heatWeight t k * cosPowInt k n :=
    funext hq
  rw [this]
  rw [← htot]
  exact hsn.hasSum

theorem continuous_heatSymbol : Continuous fun p : ℝ × ℝ => heatSymbol p.1 p.2 := by
  unfold heatSymbol; fun_prop

theorem continuous_heatSymbol_right (t : ℝ) : Continuous (heatSymbol t) := by
  unfold heatSymbol; fun_prop

theorem heatSymbol_pos (t θ : ℝ) : 0 < heatSymbol t θ := Real.exp_pos _

theorem heatKernel1_zero (n : ℤ) : heatKernel1 0 n = if n = 0 then 1 else 0 := by
  have : heatKernel1 0 n = (2 * π)⁻¹ * cosPowInt 0 n := by
    unfold heatKernel1 cosPowInt
    simp [heatSymbol]
  rw [this, cosPowInt_zero]
  have hpi : (2 * π) ≠ 0 := by positivity
  split_ifs
  · field_simp
  · simp

theorem heatSymbol_le_one {t : ℝ} (ht : 0 ≤ t) (θ : ℝ) : heatSymbol t θ ≤ 1 := by
  unfold heatSymbol
  rw [Real.exp_le_one_iff]
  have := Real.cos_le_one θ
  nlinarith

theorem heatSymbol_le_exp (t θ : ℝ) : heatSymbol t θ ≤ Real.exp (4 * |t|) := by
  unfold heatSymbol
  apply Real.exp_le_exp.mpr
  have h1 := Real.cos_le_one θ
  have h2 := Real.neg_one_le_cos θ
  have h3 : 0 ≤ 1 - Real.cos θ := by linarith
  have h4 : 1 - Real.cos θ ≤ 2 := by linarith
  have h5 := neg_abs_le t
  have h6 := le_abs_self t
  nlinarith [abs_nonneg t]

theorem heatKernel1_abs_le_one {t : ℝ} (ht : 0 ≤ t) (n : ℤ) : |heatKernel1 t n| ≤ 1 := by
  rw [abs_of_nonneg (heatKernel1_nonneg ht n)]
  exact le_hasSum (hasSum_heatKernel1 ht) n fun m _ => heatKernel1_nonneg ht m

theorem continuous_heatKernel1 (n : ℤ) : Continuous fun t => heatKernel1 t n := by
  unfold heatKernel1
  refine continuous_const.mul ?_
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (by unfold heatSymbol; fun_prop) _ _

theorem hasDerivAt_heatKernel1 (t : ℝ) (n : ℤ) :
    HasDerivAt (fun s => heatKernel1 s n)
      (heatKernel1 t (n + 1) + heatKernel1 t (n - 1) - 2 * heatKernel1 t n) t := by
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := -π) (b := π) (x₀ := t) (s := Metric.ball t 1)
    (F := fun (s θ : ℝ) => Real.cos ((n : ℝ) * θ) * heatSymbol s θ)
    (F' := fun (s θ : ℝ) =>
      Real.cos ((n : ℝ) * θ) * (-(2 * (1 - Real.cos θ)) * heatSymbol s θ))
    (bound := fun _ => 2 * (2 * Real.exp (4 * (|t| + 1))))
    (Metric.ball_mem_nhds t one_pos)
    (Filter.Eventually.of_forall fun s => by
      exact (by unfold heatSymbol; fun_prop : Continuous fun θ : ℝ =>
        Real.cos ((n : ℝ) * θ) * heatSymbol s θ).aestronglyMeasurable)
    ((by unfold heatSymbol; fun_prop : Continuous fun θ : ℝ =>
        Real.cos ((n : ℝ) * θ) * heatSymbol t θ).intervalIntegrable _ _)
    (by unfold heatSymbol; fun_prop : Continuous fun θ : ℝ =>
        Real.cos ((n : ℝ) * θ) * (-(2 * (1 - Real.cos θ)) * heatSymbol t θ)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun θ _ s hs => by
      have hs' : |s| ≤ |t| + 1 := by
        have := Metric.mem_ball.mp hs
        rw [Real.dist_eq] at this
        have := abs_sub_abs_le_abs_sub s t
        linarith [abs_lt.mp (Metric.mem_ball.mp hs |> fun h => by rwa [Real.dist_eq] at h)]
      rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, abs_neg]
      have h1 := Real.abs_cos_le_one ((n : ℝ) * θ)
      have h2 : |2 * (1 - Real.cos θ)| ≤ 4 := by
        rw [abs_le]; constructor <;> nlinarith [Real.cos_le_one θ, Real.neg_one_le_cos θ]
      have h3 : |heatSymbol s θ| ≤ Real.exp (4 * (|t| + 1)) := by
        rw [abs_of_pos (heatSymbol_pos _ _)]
        exact (heatSymbol_le_exp s θ).trans (Real.exp_le_exp.mpr (by linarith))
      have h4 : 0 ≤ Real.exp (4 * (|t| + 1)) := (Real.exp_pos _).le
      calc |Real.cos ((n : ℝ) * θ)| * (|2 * (1 - Real.cos θ)| * |heatSymbol s θ|)
          ≤ 1 * (4 * Real.exp (4 * (|t| + 1))) := by gcongr
        _ = 2 * (2 * Real.exp (4 * (|t| + 1))) := by ring)
    intervalIntegrable_const
    (Filter.Eventually.of_forall fun θ _ s _ => by
      have h : HasDerivAt (fun s : ℝ => -(2 * s * (1 - Real.cos θ))) (-(2 * (1 - Real.cos θ))) s := by
        have := (((hasDerivAt_id s).const_mul 2).mul_const (1 - Real.cos θ)).neg
        convert this using 1
        · funext y; simp
        · ring
      have := (h.exp).const_mul (Real.cos ((n : ℝ) * θ))
      unfold heatSymbol
      convert this using 1
      ring)
  have hk := key.2.const_mul (2 * π)⁻¹
  refine (show HasDerivAt (fun s => heatKernel1 s n) _ t from hk).congr_deriv ?_
  unfold heatKernel1
  have hc : ∀ m : ℤ, Continuous fun θ : ℝ => Real.cos ((m : ℝ) * θ) * heatSymbol t θ := by
    intro m; unfold heatSymbol; fun_prop
  have hpt : ∀ θ : ℝ, Real.cos ((n : ℝ) * θ) * (-(2 * (1 - Real.cos θ)) * heatSymbol t θ) =
      Real.cos (((n + 1 : ℤ) : ℝ) * θ) * heatSymbol t θ +
        Real.cos (((n - 1 : ℤ) : ℝ) * θ) * heatSymbol t θ -
        2 * (Real.cos ((n : ℝ) * θ) * heatSymbol t θ) := by
    intro θ
    have := cos_mul_cos_int n θ
    have e : Real.cos ((n : ℝ) * θ) * (-(2 * (1 - Real.cos θ)) * heatSymbol t θ) =
        (-2 * Real.cos ((n : ℝ) * θ) + 2 * (Real.cos ((n : ℝ) * θ) * Real.cos θ)) *
          heatSymbol t θ := by ring
    rw [e, this]; ring
  simp_rw [hpt]
  have h1 := (hc (n + 1)).intervalIntegrable (μ := volume) (-π) π
  have h2 := (hc (n - 1)).intervalIntegrable (μ := volume) (-π) π
  have h3 := ((hc n).const_mul 2).intervalIntegrable (μ := volume) (-π) π
  rw [intervalIntegral.integral_sub (h1.add h2) h3, intervalIntegral.integral_add h1 h2,
    intervalIntegral.integral_const_mul]
  ring

end Balaban.LatticeGreen
