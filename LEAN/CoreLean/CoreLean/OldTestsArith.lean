/-
`lem:old-tests` of BALABAN_CORE.tex (`a021c13be348`), the arithmetic of its proof. Hypotheses of the lemma used:
`ϑ_n ≤ c₈ε_n`, `½ε_n ≤ ε_{n+1} ≤ 2ε_n`, `0 ≤ κ_s ≤ ¼`, `R_{n+1} ≥ 50`, `L ≥ 3`.

* `tested_cube`: `(1 + κ_s)2ϑ_n ≤ 3ϑ_n`.
* `alpha_t_le`: `α_t = 2(1 + κ_s)ε_{n+1}L⁻² ≤ (5/9)ε_n ≤ 3ε_n`.
* `alpha_d_zero`: for `n = 0`, `α_d = α_t + (9 + K₀)ϑ₀ ≤ ε₀` when `(9 + K₀)c₈ ≤ 4/9`.
  The proof in the core gives as reasons `ε₁L⁻²(1 + κ_s) ≤ ½ε₀` and `(9 + K₀)c₈ ≤ ½`; these give only
  `α_d ≤ (3/2)ε₀`, and `alpha_d_counterexample` shows that within the hypotheses of the lemma they do not give
  `α_d ≤ ε₀` (`ε₀ = 1`, `ε₁ = 2`, `L = 3`, `κ_s = ¼`, `(9 + K₀)c₈ = ½`, `ϑ₀ = c₈`: `α_d = 19/18`). Since `c₈` is
  chosen small, the condition `(9 + K₀)c₈ ≤ 4/9` repairs the step.
* `plaquette_bound`: the last display of the proof of (i) gives `f_□(V_n) ≤ ε_n` when `160C_cK₀c₈ ≤ 1`,
  `C₁₂ ≥ 160C_cK₁B₃`, the exponential at most `C₁₂⁻¹`, and `ϑ_n ≤ ε_n`.
* `first_term`: `(1 + κ_s)ε_{n+1}L⁻² ≤ ½ε_n`.
* `distance_half`, `rate_half`: `d ≥ M₂R_n - 20M_c - 2 ≥ ½M₂R_n` for `M₂ ≥ M_c ≥ 1`, `R_n ≥ 50`, and
  `e^{-½δ₂d} ≤ e^{-¼δ₂M₂R_n}`.
* `layer_distance`: `2(27 + L)M_ca_{n-1} ≤ 20M_ca_n` and `2a_{n+1} ≤ 20M_ca_n` for `L ≥ 3`, `M_c ≥ L`.
* `transports`: `2¹¹L·6ϑ_n ≤ 2¹⁴Lϑ_n < ε_n` when `2¹⁴Lc₈ < 1`.
* `new_data`, `setting_condition`: (ii), `2(1 + κ_s)ε_{n+1} ≤ 2L²(1 + κ_s)ε_n` and
  `4B₃ε' = 8B₃L²(1 + κ_s)ε̂ ≤ 10B₃L²c₈` for `ε̂ ≤ c₈`.
-/
import Mathlib

noncomputable section

namespace CoreLean
namespace OldTestsArith

/-- `(1 + κ_s)2ϑ ≤ 3ϑ`. -/
theorem tested_cube {κ ϑ : ℝ} (hκ : κ ≤ 1 / 4) (hϑ : 0 ≤ ϑ) : (1 + κ) * (2 * ϑ) ≤ 3 * ϑ := by nlinarith

/-- `α_t = 2(1 + κ_s)ε_{n+1}L⁻² ≤ (5/9)ε_n ≤ 3ε_n`. -/
theorem alpha_t_le {κ L εn εn1 : ℝ} (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1 / 4) (hL : 3 ≤ L) (hε0 : 0 ≤ εn1)
    (hε : εn1 ≤ 2 * εn) : 2 * (1 + κ) * εn1 / L ^ 2 ≤ 5 / 9 * εn ∧ 5 / 9 * εn ≤ 3 * εn := by
  have hL2 : 9 ≤ L ^ 2 := by nlinarith
  have hLp : 0 < L ^ 2 := by positivity
  have hεn : 0 ≤ εn := by linarith
  refine ⟨?_, by linarith⟩
  rw [div_le_iff₀ hLp]
  have h1 : 2 * (1 + κ) * εn1 ≤ 2 * (5 / 4) * (2 * εn) := by
    have : (1 + κ) * εn1 ≤ (5 / 4) * (2 * εn) := mul_le_mul (by linarith) hε hε0 (by norm_num)
    linarith
  have h2 : 5 / 9 * εn * 9 ≤ 5 / 9 * εn * L ^ 2 := mul_le_mul_of_nonneg_left hL2 (by positivity)
  linarith

/-- **The case `n = 0`, repaired**: `α_d = α_t + (9 + K₀)ϑ₀ ≤ ε₀` when `(9 + K₀)c₈ ≤ 4/9`. -/
theorem alpha_d_zero {κ L ε₀ ε₁ ϑ₀ c₈ K₀ : ℝ} (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1 / 4) (hL : 3 ≤ L) (hε0 : 0 ≤ ε₁)
    (hε : ε₁ ≤ 2 * ε₀) (hK : 0 ≤ 9 + K₀) (hϑ : ϑ₀ ≤ c₈ * ε₀) (hc : (9 + K₀) * c₈ ≤ 4 / 9) :
    2 * (1 + κ) * ε₁ / L ^ 2 + (9 + K₀) * ϑ₀ ≤ ε₀ := by
  have ht := (alpha_t_le hκ0 hκ hL hε0 hε).1
  have hε₀ : 0 ≤ ε₀ := by linarith
  have h2 : (9 + K₀) * ϑ₀ ≤ (9 + K₀) * (c₈ * ε₀) := mul_le_mul_of_nonneg_left hϑ hK
  have h3 : (9 + K₀) * (c₈ * ε₀) ≤ 4 / 9 * ε₀ := by
    rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hc hε₀
  linarith

/-- **The reasons stated in the core do not suffice**: within the hypotheses of the lemma, with
`ε₁L⁻²(1 + κ_s) ≤ ½ε₀` and `(9 + K₀)c₈ = ½`, `ϑ₀ = c₈ε₀`, one can have `α_d > ε₀`. -/
theorem alpha_d_counterexample :
    let κ : ℝ := 1 / 4; let L : ℝ := 3; let ε₀ : ℝ := 1; let ε₁ : ℝ := 2; let c₈ : ℝ := 1 / 2 / 9
    let K₀ : ℝ := 0; let ϑ₀ : ℝ := c₈ * ε₀
    ε₁ / L ^ 2 * (1 + κ) ≤ 1 / 2 * ε₀ ∧ (9 + K₀) * c₈ ≤ 1 / 2 ∧ ε₁ ≤ 2 * ε₀ ∧
      ε₀ < 2 * (1 + κ) * ε₁ / L ^ 2 + (9 + K₀) * ϑ₀ := by
  norm_num

/-- `(1 + κ_s)ε_{n+1}L⁻² ≤ ½ε_n`. -/
theorem first_term {κ L εn εn1 : ℝ} (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1 / 4) (hL : 3 ≤ L) (hε0 : 0 ≤ εn1)
    (hε : εn1 ≤ 2 * εn) : (1 + κ) * εn1 / L ^ 2 ≤ 1 / 2 * εn := by
  have := (alpha_t_le hκ0 hκ hL hε0 hε).1
  have hεn : 0 ≤ εn := by linarith
  have e : 2 * (1 + κ) * εn1 / L ^ 2 = 2 * ((1 + κ) * εn1 / L ^ 2) := by ring
  rw [e] at this
  linarith

/-- **The bound of the plaquettes**: `½ε + 40C_cK₀ϑ + 20C_cK₁B₃e(ε + ϑ) ≤ ε`. -/
theorem plaquette_bound {ε ϑ c₈ Cc K₀ K₁ B₃ C₁₂ e : ℝ} (hε : 0 ≤ ε) (hϑ0 : 0 ≤ ϑ) (hϑ : ϑ ≤ c₈ * ε)
    (hϑε : ϑ ≤ ε) (hCc : 0 ≤ Cc) (hK₀ : 0 ≤ K₀) (hK₁ : 0 ≤ K₁) (hB : 0 ≤ B₃) (he0 : 0 ≤ e)
    (h160 : 160 * Cc * K₀ * c₈ ≤ 1) (hC₁₂ : 160 * Cc * K₁ * B₃ ≤ C₁₂) (he : e * C₁₂ ≤ 1) :
    1 / 2 * ε + 40 * Cc * K₀ * ϑ + 20 * Cc * K₁ * B₃ * e * (ε + ϑ) ≤ ε := by
  have h2 : 40 * Cc * K₀ * ϑ ≤ 1 / 4 * ε := by
    have : 40 * Cc * K₀ * ϑ ≤ 40 * Cc * K₀ * (c₈ * ε) := mul_le_mul_of_nonneg_left hϑ (by positivity)
    nlinarith
  have h3 : 20 * Cc * K₁ * B₃ * e * (ε + ϑ) ≤ 1 / 4 * ε := by
    have hs : ε + ϑ ≤ 2 * ε := by linarith
    have h1 : 160 * Cc * K₁ * B₃ * e ≤ 1 := (mul_le_mul_of_nonneg_right hC₁₂ he0).trans (by linarith)
    have : 20 * Cc * K₁ * B₃ * e * (ε + ϑ) ≤ 20 * Cc * K₁ * B₃ * e * (2 * ε) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    nlinarith
  linarith

/-- `d ≥ M₂R_n - 20M_c - 2 ≥ ½M₂R_n`. -/
theorem distance_half {M₂ Mc R d : ℝ} (hMc : 1 ≤ Mc) (hM : Mc ≤ M₂) (hR : 50 ≤ R)
    (hd : M₂ * R - 20 * Mc - 2 ≤ d) : 1 / 2 * (M₂ * R) ≤ d := by
  have : 50 * M₂ ≤ M₂ * R := by nlinarith
  linarith

/-- `e^{-½δ₂d} ≤ e^{-¼δ₂M₂R_n}` for `d ≥ ½M₂R_n`. -/
theorem rate_half {δ d MR : ℝ} (hδ : 0 ≤ δ) (hd : 1 / 2 * MR ≤ d) :
    Real.exp (-(1 / 2) * δ * d) ≤ Real.exp (-(1 / 4) * δ * MR) :=
  Real.exp_le_exp.2 (by nlinarith)

/-- `2(27 + L)M_ca ≤ 20M_c(La)` and `2(La) ≤ 20M_ca` for `L ≥ 3`, `M_c ≥ L`, `a > 0`. -/
theorem layer_distance {L Mc a : ℝ} (hL : 3 ≤ L) (hM : L ≤ Mc) (ha : 0 ≤ a) :
    2 * (27 + L) * Mc * a ≤ 20 * Mc * (L * a) ∧ 2 * (L * a) ≤ 20 * Mc * a := by
  have hMc : 0 ≤ Mc := by linarith
  refine ⟨?_, ?_⟩
  · have : 2 * (27 + L) ≤ 20 * L := by linarith
    have := mul_le_mul_of_nonneg_right this (mul_nonneg hMc ha)
    nlinarith
  · nlinarith

/-- **The transports**: `2¹¹L·6ϑ ≤ 2¹⁴Lϑ < ε` when `2¹⁴Lc₈ < 1`, `ϑ ≤ c₈ε`, `ε > 0`. -/
theorem transports {L ϑ c₈ ε : ℝ} (hL : 0 ≤ L) (hϑ0 : 0 ≤ ϑ) (hϑ : ϑ ≤ c₈ * ε) (hε : 0 < ε)
    (hc : 2 ^ 14 * L * c₈ < 1) : 2 ^ 11 * L * (6 * ϑ) ≤ 2 ^ 14 * L * ϑ ∧ 2 ^ 14 * L * ϑ < ε := by
  refine ⟨by nlinarith, ?_⟩
  have h1 : 2 ^ 14 * L * ϑ ≤ 2 ^ 14 * L * (c₈ * ε) := mul_le_mul_of_nonneg_left hϑ (by positivity)
  have h2 : 2 ^ 14 * L * c₈ * ε < 1 * ε := mul_lt_mul_of_pos_right hc hε
  nlinarith

/-- (ii): `2(1 + κ_s)ε_{n+1} ≤ 2L²(1 + κ_s)ε_n`. -/
theorem new_data {κ L εn εn1 : ℝ} (hκ0 : 0 ≤ κ) (hL : 3 ≤ L) (hε : εn1 ≤ 2 * εn) (hεn : 0 ≤ εn) :
    2 * (1 + κ) * εn1 ≤ 2 * L ^ 2 * (1 + κ) * εn := by
  have hL2 : 9 ≤ L ^ 2 := by nlinarith
  have : εn1 ≤ L ^ 2 * εn := by nlinarith
  have h := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ 2 * (1 + κ))
  linarith

/-- (ii): `4B₃ε' = 8B₃L²(1 + κ_s)ε̂ ≤ 10B₃L²c₈` for `κ_s ≤ ¼`, `ε̂ ≤ c₈`. -/
theorem setting_condition {B₃ L κ ε c₈ : ℝ} (hB : 0 ≤ B₃) (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1 / 4) (hε0 : 0 ≤ ε)
    (hε : ε ≤ c₈) : 4 * B₃ * (2 * L ^ 2 * (1 + κ) * ε) ≤ 10 * B₃ * L ^ 2 * c₈ := by
  have hBL : 0 ≤ B₃ * L ^ 2 := by positivity
  have h1 : (1 + κ) * ε ≤ 5 / 4 * c₈ := mul_le_mul (by linarith) hε hε0 (by norm_num)
  have := mul_le_mul_of_nonneg_left h1 hBL
  nlinarith

end OldTestsArith
end CoreLean

end
