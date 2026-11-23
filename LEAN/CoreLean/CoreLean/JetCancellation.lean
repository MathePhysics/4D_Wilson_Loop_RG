/-
`lem:jet-cancellation` of BALABAN_CORE.tex (`a021c13be348`), the analytic part of its proof, for a function
`g(ε) = D𝔚(εB)[δB]` holomorphic on a closed disc `|ε| ≤ ε₁` and bounded by `G` on its boundary, with `g(0) = 0`, and
with the Taylor coefficients `g_k` at `0` (the core's `g₁ = p₂`, `g₂ = p₃`, `g₃ = p₄`; here the coefficients of the
power series of Cauchy).
* `coeff_le`: `|g_k| ≤ Gε₁^{-k}` (Cauchy's estimate).
* `jet_tail`: `|g(ε) - g₁ε - g₂ε² - g₃ε³| ≤ 2G(|ε|/ε₁)⁴` for `|ε| ≤ ε₁/2`; for `ε₁ ≥ 2` this is `eq:jet-remainder`,
  `|g(1) - p₂ - p₃ - p₄| ≤ 2Gε₁^{-4}` (`jet_remainder`).
* `lagrange_three`: a polynomial `c₀ + c₁x + c₂x²` with values of modulus at most `Q` at `t`, `t/2`, `t/4` has
  `|c₀| ≤ 5Q`, `|c₁| ≤ 20Q/t`, `|c₂| ≤ 16Q/t²` (Lagrange's formula with the core's numbers).
* `jet_cancellation`: if moreover `|g(ε)| ≤ εA` for `0 < ε ≤ ε₀`, `ε₀ ≤ min{1, ε₁/2}`, then
  `|p₂ + p₃ + p₄| ≤ 41(A + 2Gε₀³ε₁^{-4})/ε₀²`, the core's bound with `Q̄ = A + 2Gε₀³ε₁^{-4}`.
The bounds of `g` from the hypotheses (a)-(c) of `lem:near-cancellation` are the inputs.
-/
import Mathlib

open Complex Metric Set Filter
open scoped NNReal Real

noncomputable section

namespace CoreLean
namespace Jet

variable {g : ℂ → ℂ} {R : ℝ≥0} {G : ℝ}

/-- The Taylor coefficients at `0`, from the power series of Cauchy on the circle of the radius `R`. -/
def cf (g : ℂ → ℂ) (R : ℝ≥0) (k : ℕ) : ℂ := (cauchyPowerSeries g 0 R).coeff k

/-- **Cauchy's estimate** `|g_k| ≤ GR^{-k}`. -/
theorem coeff_le (hR : 0 < R) (hd : DifferentiableOn ℂ g (closedBall 0 R))
    (hb : ∀ z ∈ sphere (0 : ℂ) R, ‖g z‖ ≤ G) (k : ℕ) : ‖cf g R k‖ ≤ G * ((R : ℝ)⁻¹) ^ k := by
  unfold cf
  rw [← FormalMultilinearSeries.norm_apply_eq_norm_coef]
  refine (norm_cauchyPowerSeries_le g 0 R k).trans ?_
  have hR' : (0 : ℝ) < R := hR
  have hcont : Continuous fun θ : ℝ => ‖g (circleMap 0 R θ)‖ :=
    ((hd.continuousOn.mono sphere_subset_closedBall).comp_continuous (continuous_circleMap 0 R)
      fun θ => circleMap_mem_sphere 0 hR'.le θ).norm
  have hint : ∫ θ : ℝ in 0..2 * π, ‖g (circleMap 0 R θ)‖ ≤ ∫ θ : ℝ in 0..2 * π, G := by
    refine intervalIntegral.integral_mono_on (by positivity) (hcont.intervalIntegrable _ _)
      intervalIntegrable_const fun θ _ => hb _ (circleMap_mem_sphere 0 hR'.le θ)
  rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hint
  rw [abs_of_pos hR']
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  calc (2 * π)⁻¹ * ∫ θ : ℝ in 0..2 * π, ‖g (circleMap 0 R θ)‖ ≤ (2 * π)⁻¹ * (2 * π * G) :=
        mul_le_mul_of_nonneg_left hint (by positivity)
    _ = G := by field_simp

/-- The power series: `g(ε) = Σ_k g_kε^k` for `|ε| < R`. -/
theorem hasSum_cf (hR : 0 < R) (hd : DifferentiableOn ℂ g (closedBall 0 R)) {ε : ℂ}
    (hε : ‖ε‖ < R) : HasSum (fun k => ε ^ k * cf g R k) (g ε) := by
  have hp := hd.hasFPowerSeriesOnBall hR
  have hmem : ε ∈ Metric.eball (0 : ℂ) R := by
    rw [Metric.mem_eball, edist_zero_right]
    exact_mod_cast hε
  have := hp.hasSum hmem
  simp only [zero_add, FormalMultilinearSeries.apply_eq_pow_smul_coeff, smul_eq_mul] at this
  exact this

theorem cf_zero (hR : 0 < R) (hd : DifferentiableOn ℂ g (closedBall 0 R)) (h0 : g 0 = 0) :
    cf g R 0 = 0 := by
  have := hasSum_cf hR hd (ε := 0) (by simpa using hR)
  rw [h0] at this
  have e : (fun k => (0 : ℂ) ^ k * cf g R k) = fun k => if k = 0 then cf g R 0 else 0 := by
    funext k; rcases k with _ | k <;> simp
  rw [e] at this
  have h2 := hasSum_ite_eq 0 (cf g R 0)
  exact (this.unique h2).symm

/-- **The tail**: `|g(ε) - g₁ε - g₂ε² - g₃ε³| ≤ 2G(|ε|/R)⁴` for `|ε| ≤ R/2`. -/
theorem jet_tail (hR : 0 < R) (hd : DifferentiableOn ℂ g (closedBall 0 R))
    (hb : ∀ z ∈ sphere (0 : ℂ) R, ‖g z‖ ≤ G) (h0 : g 0 = 0) {ε : ℂ} (hε : ‖ε‖ ≤ R / 2) :
    ‖g ε - (cf g R 1 * ε + cf g R 2 * ε ^ 2 + cf g R 3 * ε ^ 3)‖ ≤ 2 * G * (‖ε‖ / R) ^ 4 := by
  have hR' : (0 : ℝ) < R := hR
  have hεR : ‖ε‖ < R := by linarith
  have hs := hasSum_cf hR hd hεR
  have hG : 0 ≤ G := (norm_nonneg _).trans (hb (R : ℂ) (by simp [abs_of_pos hR']))
  set q := ‖ε‖ / R with hq
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q ≤ 1 / 2 := by rw [hq, div_le_iff₀ hR']; linarith
  -- the shifted series
  have hs4 := (hasSum_nat_add_iff' 4).2 hs
  have hfirst : ∑ i ∈ Finset.range 4, ε ^ i * cf g R i =
      cf g R 1 * ε + cf g R 2 * ε ^ 2 + cf g R 3 * ε ^ 3 := by
    simp [Finset.sum_range_succ, cf_zero hR hd h0]; ring
  rw [hfirst] at hs4
  -- the bound of the terms
  have hterm : ∀ k, ‖ε ^ (k + 4) * cf g R (k + 4)‖ ≤ G * q ^ 4 * q ^ k := fun k => by
    rw [norm_mul, norm_pow]
    have := coeff_le hR hd hb (k + 4)
    calc ‖ε‖ ^ (k + 4) * ‖cf g R (k + 4)‖ ≤ ‖ε‖ ^ (k + 4) * (G * ((R : ℝ)⁻¹) ^ (k + 4)) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = G * q ^ 4 * q ^ k := by rw [hq, div_eq_mul_inv]; ring
  have hgeo : HasSum (fun k : ℕ => G * q ^ 4 * q ^ k) (G * q ^ 4 * (1 - q)⁻¹) :=
    (hasSum_geometric_of_lt_one hq0 (by linarith)).mul_left _
  have hle := hs4.norm_le_of_bounded hgeo hterm
  have hinv : (1 - q)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  calc ‖g ε - (cf g R 1 * ε + cf g R 2 * ε ^ 2 + cf g R 3 * ε ^ 3)‖ ≤ G * q ^ 4 * (1 - q)⁻¹ := hle
    _ ≤ G * q ^ 4 * 2 := mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = 2 * G * q ^ 4 := by ring

/-- **`eq:jet-remainder`**: for `R ≥ 2`, `|g(1) - p₂ - p₃ - p₄| ≤ 2GR^{-4}`. -/
theorem jet_remainder (hR : 0 < R) (hR2 : 2 ≤ (R : ℝ)) (hd : DifferentiableOn ℂ g (closedBall 0 R))
    (hb : ∀ z ∈ sphere (0 : ℂ) R, ‖g z‖ ≤ G) (h0 : g 0 = 0) :
    ‖g 1 - (cf g R 1 + cf g R 2 + cf g R 3)‖ ≤ 2 * G / (R : ℝ) ^ 4 := by
  have h := jet_tail hR hd hb h0 (ε := 1) (by rw [norm_one]; linarith)
  simp only [mul_one, one_pow, norm_one] at h
  rwa [div_pow, one_pow, mul_one_div] at h

/-- **Lagrange's formula** at the points `t`, `t/2`, `t/4`. -/
theorem lagrange_three (c₀ c₁ c₂ : ℂ) {t Q : ℝ} (ht : 0 < t)
    (h1 : ‖c₀ + c₁ * t + c₂ * (t : ℂ) ^ 2‖ ≤ Q) (h2 : ‖c₀ + c₁ * ((t : ℂ) / 2) + c₂ * ((t : ℂ) / 2) ^ 2‖ ≤ Q)
    (h3 : ‖c₀ + c₁ * ((t : ℂ) / 4) + c₂ * ((t : ℂ) / 4) ^ 2‖ ≤ Q) :
    ‖c₀‖ ≤ 5 * Q ∧ ‖c₁‖ ≤ 20 * Q / t ∧ ‖c₂‖ ≤ 16 * Q / t ^ 2 := by
  set T : ℂ := (t : ℂ) with hT
  set v₁ := c₀ + c₁ * T + c₂ * T ^ 2 with hv₁
  set v₂ := c₀ + c₁ * (T / 2) + c₂ * (T / 2) ^ 2 with hv₂
  set v₃ := c₀ + c₁ * (T / 4) + c₂ * (T / 4) ^ 2 with hv₃
  have htc : T ≠ 0 := by rw [hT]; exact_mod_cast ht.ne'
  have e0 : c₀ = (1 / 3 : ℂ) * v₁ - 2 * v₂ + (8 / 3 : ℂ) * v₃ := by rw [hv₁, hv₂, hv₃]; ring
  have e1 : c₁ = ((-2 : ℂ) * v₁ + 10 * v₂ - 8 * v₃) / T := by
    rw [eq_div_iff htc, hv₁, hv₂, hv₃]; ring
  have e2 : c₂ = ((8 / 3 : ℂ) * v₁ - 8 * v₂ + (16 / 3 : ℂ) * v₃) / T ^ 2 := by
    rw [eq_div_iff (pow_ne_zero 2 htc), hv₁, hv₂, hv₃]; ring
  have hTn : ‖T‖ = t := by rw [hT, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
  refine ⟨?_, ?_, ?_⟩
  · rw [e0]
    calc ‖(1 / 3 : ℂ) * v₁ - 2 * v₂ + (8 / 3 : ℂ) * v₃‖
        ≤ ‖(1 / 3 : ℂ) * v₁‖ + ‖(2 : ℂ) * v₂‖ + ‖(8 / 3 : ℂ) * v₃‖ := by
          have := norm_sub_le ((1 / 3 : ℂ) * v₁) (2 * v₂)
          have := norm_add_le ((1 / 3 : ℂ) * v₁ - 2 * v₂) ((8 / 3 : ℂ) * v₃)
          linarith
      _ = 1 / 3 * ‖v₁‖ + 2 * ‖v₂‖ + 8 / 3 * ‖v₃‖ := by
          simp only [norm_mul]; norm_num
      _ ≤ 1 / 3 * Q + 2 * Q + 8 / 3 * Q := by gcongr
      _ = 5 * Q := by ring
  · rw [e1, norm_div, hTn]
    refine div_le_div_of_nonneg_right ?_ ht.le
    calc ‖(-2 : ℂ) * v₁ + 10 * v₂ - 8 * v₃‖ ≤ ‖(-2 : ℂ) * v₁‖ + ‖(10 : ℂ) * v₂‖ + ‖(8 : ℂ) * v₃‖ := by
          have := norm_add_le ((-2 : ℂ) * v₁) (10 * v₂)
          have := norm_sub_le ((-2 : ℂ) * v₁ + 10 * v₂) (8 * v₃)
          linarith
      _ = 2 * ‖v₁‖ + 10 * ‖v₂‖ + 8 * ‖v₃‖ := by simp only [norm_mul]; norm_num
      _ ≤ 2 * Q + 10 * Q + 8 * Q := by gcongr
      _ = 20 * Q := by ring
  · rw [e2, norm_div, norm_pow, hTn]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    calc ‖(8 / 3 : ℂ) * v₁ - 8 * v₂ + (16 / 3 : ℂ) * v₃‖
        ≤ ‖(8 / 3 : ℂ) * v₁‖ + ‖(8 : ℂ) * v₂‖ + ‖(16 / 3 : ℂ) * v₃‖ := by
          have := norm_sub_le ((8 / 3 : ℂ) * v₁) (8 * v₂)
          have := norm_add_le ((8 / 3 : ℂ) * v₁ - 8 * v₂) ((16 / 3 : ℂ) * v₃)
          linarith
      _ = 8 / 3 * ‖v₁‖ + 8 * ‖v₂‖ + 16 / 3 * ‖v₃‖ := by simp only [norm_mul]; norm_num
      _ ≤ 8 / 3 * Q + 8 * Q + 16 / 3 * Q := by gcongr
      _ = 16 * Q := by ring

/-- **`eq:jet-cancellation`**, the analytic part: with `|g(ε)| ≤ εA` for `0 < ε ≤ ε₀ ≤ min{1, R/2}`,
`|p₂ + p₃ + p₄| ≤ 41Q̄/ε₀²`, `Q̄ = A + 2Gε₀³R^{-4}`. -/
theorem jet_cancellation (hR : 0 < R) (hd : DifferentiableOn ℂ g (closedBall 0 R))
    (hb : ∀ z ∈ sphere (0 : ℂ) R, ‖g z‖ ≤ G) (h0 : g 0 = 0) {ε₀ A : ℝ} (hε₀ : 0 < ε₀) (hε₁ : ε₀ ≤ 1)
    (hε₂ : ε₀ ≤ R / 2) (hA : ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ‖g ε‖ ≤ ε * A) :
    ‖cf g R 1 + cf g R 2 + cf g R 3‖ ≤ 41 * (A + 2 * G * ε₀ ^ 3 / (R : ℝ) ^ 4) / ε₀ ^ 2 := by
  have hR' : (0 : ℝ) < R := hR
  obtain ⟨Qb, hQb⟩ : ∃ Qb, Qb = A + 2 * G * ε₀ ^ 3 / (R : ℝ) ^ 4 := ⟨_, rfl⟩
  rw [← hQb]
  have hG : 0 ≤ G := (norm_nonneg _).trans (hb (R : ℂ) (by simp [abs_of_pos hR']))
  -- `|q(ε)| ≤ Q̄` on `(0, ε₀]`
  have hq : ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ‖cf g R 1 + cf g R 2 * ε + cf g R 3 * (ε : ℂ) ^ 2‖ ≤ Qb := by
    intro ε h0' h1'
    have hεn : ‖(ε : ℂ)‖ = ε := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos h0']
    have ht := jet_tail hR hd hb h0 (ε := (ε : ℂ)) (by rw [hεn]; linarith)
    rw [hεn] at ht
    have hg := hA ε h0' h1'
    have e : (ε : ℂ) * (cf g R 1 + cf g R 2 * ε + cf g R 3 * (ε : ℂ) ^ 2) =
        g ε - (g ε - (cf g R 1 * ε + cf g R 2 * (ε : ℂ) ^ 2 + cf g R 3 * (ε : ℂ) ^ 3)) := by ring
    have hn : ε * ‖cf g R 1 + cf g R 2 * ε + cf g R 3 * (ε : ℂ) ^ 2‖ ≤ ε * A + 2 * G * (ε / R) ^ 4 := by
      have hm : ‖(ε : ℂ) * (cf g R 1 + cf g R 2 * ε + cf g R 3 * (ε : ℂ) ^ 2)‖ =
          ε * ‖cf g R 1 + cf g R 2 * ε + cf g R 3 * (ε : ℂ) ^ 2‖ := by rw [norm_mul, hεn]
      rw [← hm, e]
      exact (norm_sub_le _ _).trans (add_le_add hg ht)
    have h3 : ε ^ 3 ≤ ε₀ ^ 3 := pow_le_pow_left₀ h0'.le h1' 3
    have : ‖cf g R 1 + cf g R 2 * ε + cf g R 3 * (ε : ℂ) ^ 2‖ ≤ A + 2 * G * ε ^ 3 / (R : ℝ) ^ 4 := by
      rw [← mul_le_mul_iff_of_pos_left h0']
      calc ε * ‖cf g R 1 + cf g R 2 * ε + cf g R 3 * (ε : ℂ) ^ 2‖ ≤ ε * A + 2 * G * (ε / R) ^ 4 := hn
        _ = ε * (A + 2 * G * ε ^ 3 / (R : ℝ) ^ 4) := by field_simp
    refine this.trans ?_
    rw [hQb]
    gcongr
  have hq2 := hq (ε₀ / 2) (by linarith) (by linarith)
  have hq4 := hq (ε₀ / 4) (by linarith) (by linarith)
  push_cast at hq2 hq4
  have hL := lagrange_three (cf g R 1) (cf g R 2) (cf g R 3) hε₀ (hq ε₀ hε₀ le_rfl) hq2 hq4
  obtain ⟨l0, l1, l2⟩ := hL
  have hQ0 : 0 ≤ Qb := by
    have := (norm_nonneg _).trans (hq ε₀ hε₀ le_rfl); linarith
  have hsq : ε₀ ^ 2 ≤ ε₀ := by nlinarith
  calc ‖cf g R 1 + cf g R 2 + cf g R 3‖ ≤ ‖cf g R 1‖ + ‖cf g R 2‖ + ‖cf g R 3‖ := by
        have := norm_add_le (cf g R 1) (cf g R 2)
        have := norm_add_le (cf g R 1 + cf g R 2) (cf g R 3)
        linarith
    _ ≤ 5 * Qb + 20 * Qb / ε₀ + 16 * Qb / ε₀ ^ 2 := add_le_add (add_le_add l0 l1) l2
    _ ≤ 5 * Qb / ε₀ ^ 2 + 20 * Qb / ε₀ ^ 2 + 16 * Qb / ε₀ ^ 2 := by
        have hp : 0 < ε₀ ^ 2 := by positivity
        gcongr
        · rw [le_div_iff₀ hp]; nlinarith
    _ = 41 * Qb / ε₀ ^ 2 := by ring

end Jet
end CoreLean

end
