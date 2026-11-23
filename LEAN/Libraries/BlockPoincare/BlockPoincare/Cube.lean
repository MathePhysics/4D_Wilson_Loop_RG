import BlockPoincare.Defs

/-!
# The fractional Poincaré inequality on a set of finite diameter

The first-class result of the library: on a set `A` of finite measure and diameter at most `D`,

`‖g - mean g‖²_{L²(A)} ≤ D^(2 + 2s) / μ A * [g]²_{Hˢ(A)}`,

for every `s > 0`.  In two dimensions, for a cube of side `l` (`μ A = l²`, `diam A ≤ √2 l`) the
constant is `2^(1+s) l^(2s)`, so `‖g - mean g‖_{L²(Q)} ≤ 2^((1+s)/2) l^s [g]_{Hˢ(Q)}`.

## The proof

Two elementary steps, exactly as in the manuscript's sketch, and no John-domain theory.

1. `integral_sub_mean_sq_le`: the mean minimises the `L²` distance, `∫_A (g - mean)² ≤ ∫_A (g - c)²`
   for every constant `c`.  This is the "Jensen" step, proved directly from the expansion
   `(g - c)² - (g - mean)² = 2 (mean - c) g + (c² - mean²)`.
2. Averaging that over `c = g y`, `y ∈ A`, gives
   `μ A * ∫_A (g - mean)² ≤ ∫_A ∫_A |g x - g y|²` (`mul_l2sq_sub_mean_le`).
3. `dist x y ≤ D` on `A × A` turns the right-hand side into `D^(2+2s) [g]²_{Hˢ(A)}`
   (`lintegral_sq_diff_le`).

## Conventions

`X` is a metric space (not merely pseudometric): the diameter step uses that `dist x y = 0`
forces `g x = g y`, which is where the Gagliardo integrand takes the value `0 / 0 = 0`.

## Scope

Everything here is proved.  The constant `D^(2+2s) / μ A` is explicit and depends only on the
diameter and the measure of `A`; in the cube form it is `2^(1+s) l^(2s)`, which involves the side
`l` alone.  No literature result is used or assumed.  The reverse inequality, sharpness of the
constant, and the case `s = 0` are not treated.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace BlockPoincare

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {A : Set X} {g : X → ℝ} {s D : ℝ}

/-- **The mean minimises the `L²` distance.**  For every constant `c`,
`∫_A (g - mean g)² ≤ ∫_A (g - c)²`. -/
theorem integral_sub_mean_sq_le (h0 : μ A ≠ 0) (htop : μ A ≠ ∞)
    (hg : MemLp g 2 (μ.restrict A)) (c : ℝ) :
    ∫ x in A, (g x - mean μ A g) ^ 2 ∂μ ≤ ∫ x in A, (g x - c) ^  -- totalisation-audit: allow L1 hyp
        2 ∂μ := by
  have : IsFiniteMeasure (μ.restrict A) :=
    ⟨by rwa [Measure.restrict_apply_univ, lt_top_iff_ne_top]⟩
  have hV : (μ A).toReal ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨h0,  -- totalisation-audit: allow finite
      htop⟩
  set m := mean μ A g with hm
  have hgi : Integrable g (μ.restrict A) := hg.integrable one_le_two
  have hmean : ∫ x in A, g x ∂μ = m * (μ A).toReal :=  -- totalisation-audit: allow finite, L1 hyp
      by
    rw [hm, mean]
    field_simp
  have hsq : ∀ c : ℝ, Integrable (fun x => (g x - c) ^ 2) (μ.restrict A) := fun c =>
    (hg.sub (memLp_const c)).integrable_sq
  have hdiff : ∫ x in A, ((g x - c) ^ 2 - (g x - m) ^  -- totalisation-audit: allow L1 hyp
      2) ∂μ = (m - c) ^ 2 * (μ A).toReal := by  -- totalisation-audit: allow finite
    have hfun : (fun x => (g x - c) ^ 2 - (g x - m) ^ 2)
        = fun x => 2 * (m - c) * g x + (c ^ 2 - m ^ 2) := by
      funext x; ring
    rw [hfun, integral_add ((hgi.const_mul _)) (integrable_const _), integral_const_mul,
      setIntegral_const, hmean, measureReal_def, smul_eq_mul]
    ring
  have := integral_sub (hsq c) (hsq m)
  nlinarith [mul_nonneg (sq_nonneg (m - c)) (ENNReal.toReal_nonneg (a := μ A)),
    this, hdiff]

/-- **The averaged Jensen step.**  `μ A * ∫_A (g - mean g)² ≤ ∫_A ∫_A |g x - g y|²`. -/
theorem mul_l2sq_sub_mean_le (h0 : μ A ≠ 0) (htop : μ A ≠ ∞)
    (hg : MemLp g 2 (μ.restrict A)) :
    μ A * l2sq μ A (fun x => g x - mean μ A g) ≤
      ∫⁻ x in A, ∫⁻ y in A, ENNReal.ofReal ((g x - g y) ^ 2) ∂μ ∂μ := by
  have : IsFiniteMeasure (μ.restrict A) :=
    ⟨by rwa [Measure.restrict_apply_univ, lt_top_iff_ne_top]⟩
  have hsq : ∀ c : ℝ, Integrable (fun x => (g x - c) ^ 2) (μ.restrict A) := fun c =>
    (hg.sub (memLp_const c)).integrable_sq
  have hkey : ∀ x : X, ENNReal.ofReal (∫ y in A, (g y - mean μ  -- totalisation-audit: allow L1 hyp
      A g) ^ 2 ∂μ)
      ≤ ∫⁻ y in A, ENNReal.ofReal ((g x - g y) ^ 2) ∂μ := by
    intro x
    have h1 : ∫ y in A, (g y - mean μ A g) ^ 2 ∂μ ≤ ∫ y in A,  -- totalisation-audit: allow L1 hyp
        (g x - g y) ^ 2 ∂μ := by
      refine le_trans (integral_sub_mean_sq_le h0 htop hg (g x)) (le_of_eq ?_)
      exact integral_congr_ae (.of_forall fun y => by ring)
    refine le_trans (ENNReal.ofReal_le_ofReal h1) (le_of_eq ?_)
    exact ofReal_integral_eq_lintegral_ofReal
      ((hsq (g x)).congr (.of_forall fun y => by ring)) (.of_forall fun y => sq_nonneg _)
  calc μ A * l2sq μ A (fun x => g x - mean μ A g)
      = ∫⁻ _ in A, ENNReal.ofReal (∫ y in A, (g y - mean μ A g)  -- totalisation-audit: allow L1 hyp
          ^ 2 ∂μ) ∂μ := by
        rw [setLIntegral_const, ← l2sq_toReal (hsq _), mul_comm]
    _ ≤ _ := lintegral_mono hkey

variable [MetricSpace X]

/-- **The diameter step.**  If every two points of `A` are at distance at most `D`, the double
integral of `|g x - g y|²` is bounded by `D^(2+2s)` times the Gagliardo seminorm. -/
theorem lintegral_sq_diff_le (hs : 0 < s) (hA : MeasurableSet A)
    (hD : ∀ x ∈ A, ∀ y ∈ A, dist x y ≤ D) :
    ∫⁻ x in A, ∫⁻ y in A, ENNReal.ofReal ((g x - g y) ^ 2) ∂μ ∂μ
      ≤ ENNReal.ofReal (D ^ (2 + 2 * s)) * gagliardoSq s μ A g := by
  have hq : (0 : ℝ) < 2 + 2 * s := by linarith
  have hpt : ∀ x ∈ A, ∀ y ∈ A, ENNReal.ofReal ((g x - g y) ^ 2) ≤
      ENNReal.ofReal (D ^ (2 + 2 * s)) *
        (ENNReal.ofReal ((g x - g y) ^ 2) / ENNReal.ofReal (dist x  -- totalisation-audit: allow > 0
            y ^ (2 + 2 * s))) := by
    intro x hx y hy
    rcases eq_or_ne (g x) (g y) with h | h
    · simp [h]
    have hd : 0 < dist x y := by
      rcases (dist_nonneg (x := x) (y := y)).lt_or_eq with h' | h'
      · exact h'
      · exact absurd (congrArg g (dist_eq_zero.1 h'.symm)) h
    have hDpos : 0 < D := lt_of_lt_of_le hd (hD x hx y hy)
    have hle : ENNReal.ofReal (dist x y ^ (2 + 2 * s)) ≤ ENNReal.ofReal (D ^ (2 + 2 * s)) :=
      ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow dist_nonneg (hD x hx y hy) hq.le)
    have hDne : ENNReal.ofReal (D ^ (2 + 2 * s)) ≠ 0 := by
      simp [ENNReal.ofReal_eq_zero, not_le, Real.rpow_pos_of_pos hDpos]
    calc ENNReal.ofReal ((g x - g y) ^ 2)
        = ENNReal.ofReal (D ^ (2 + 2 * s)) *
            (ENNReal.ofReal ((g x - g y) ^ 2) / ENNReal.ofReal (D  -- totalisation-audit: allow > 0
                ^ (2 + 2 * s))) :=
          (ENNReal.mul_div_cancel' (fun h => absurd h hDne)
            (fun h => absurd h ENNReal.ofReal_ne_top)).symm
      _ ≤ _ := by gcongr
  calc ∫⁻ x in A, ∫⁻ y in A, ENNReal.ofReal ((g x - g y) ^ 2) ∂μ ∂μ
      ≤ ∫⁻ x in A, ∫⁻ y in A, ENNReal.ofReal (D ^ (2 + 2 * s)) *
          (ENNReal.ofReal ((g x - g y) ^ 2) /  -- totalisation-audit: allow > 0
            ENNReal.ofReal (dist x y ^ (2 + 2 * s))) ∂μ ∂μ := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_mem hA] with x hx
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_mem hA] with y hy
        exact hpt x hx y hy
    _ = ENNReal.ofReal (D ^ (2 + 2 * s)) * gagliardoSq s μ A g := by
        rw [gagliardoSq, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        exact lintegral_congr fun x => lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- **The fractional Poincaré inequality on a set of diameter `D`**, in the form without
division. -/
theorem mul_l2sq_sub_mean_le_diam (hs : 0 < s) (hA : MeasurableSet A) (h0 : μ A ≠ 0)
    (htop : μ A ≠ ∞) (hg : MemLp g 2 (μ.restrict A)) (hD : ∀ x ∈ A, ∀ y ∈ A, dist x y ≤ D) :
    μ A * l2sq μ A (fun x => g x - mean μ A g)
      ≤ ENNReal.ofReal (D ^ (2 + 2 * s)) * gagliardoSq s μ A g :=
  le_trans (mul_l2sq_sub_mean_le h0 htop hg) (lintegral_sq_diff_le hs hA hD)

/-- **The fractional Poincaré inequality on a set of diameter `D`.** -/
theorem l2sq_sub_mean_le_diam (hs : 0 < s) (hA : MeasurableSet A) (h0 : μ A ≠ 0)
    (htop : μ A ≠ ∞) (hg : MemLp g 2 (μ.restrict A)) (hD : ∀ x ∈ A, ∀ y ∈ A, dist x y ≤ D) :
    l2sq μ A (fun x => g x - mean μ A g)
      ≤ ENNReal.ofReal (D ^ (2 + 2 * s)) / μ A * gagliardoSq s μ A  -- totalisation-audit: allow > 0
          g := by
  have key : ENNReal.ofReal (D ^ (2 + 2 * s)) / μ A * gagliardoSq  -- totalisation-audit: allow > 0
      s μ A g
      = ENNReal.ofReal (D ^ (2 + 2 * s)) * gagliardoSq s μ A g / μ  -- totalisation-audit: allow > 0
          A := by
    rw [div_eq_mul_inv, div_eq_mul_inv, mul_right_comm]
  rw [key, ENNReal.le_div_iff_mul_le (Or.inl h0) (Or.inl htop), mul_comm]
  exact mul_l2sq_sub_mean_le_diam hs hA h0 htop hg hD

end BlockPoincare
