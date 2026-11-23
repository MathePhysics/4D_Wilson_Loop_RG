/-
`lem:critical-regular` of BALABAN_CORE.tex (`a021c13be348`), the arithmetic of its proof.

* `ball_distances`: from `RM₁ ≥ (L + 1)(D_lc + 5)` (the choice of `R₃`): `RM₁/L ≥ D_lc + 3`, `RM₁ ≥ D_lc + 3`, and
  `RM₁ - D_lc - 4 - L ≥ L(D_lc + 2)`, so that the ball `B̄` lies in `Ω_{t-1} ∖ Ω_{t+1}`.
* `average_plaquettes`: `L²ε₁ + C₀L⁴ε₁² ≤ 2L²ε₁` for `C₀L²ε₁ ≤ 1`.
* `ten_rho`: `10ρ ≤ B'ε₁ + ε₀/(4(1 + C_J))` from the choice of `r_lc`, the condition on `X`, and
  `B' = 10K_H(C_axL² + 2K₁) + K₁ + 1`. The proof in the core uses tacitly `8(1 + C_J)C_sL² ≥ 1` (to pass from
  `10K_He·C_sL² ≤ 1/(8(1 + C_J))` to `10K_He ≤ 1`, and likewise for `X`) and `10K_H ≥ 1` (for
  `10K_H(C_axL² + K₁) + 2K₁ ≤ B'`); these are hypotheses here, true when the constants are taken at least `1`.
* `eps_p`: `B'ε₁ + ε₀/(4(1 + C_J)) ≤ max{2B'ε₁, ε₀/(2(1 + C_J))} =: ε_p` and
  `(1 + C_J)ε_p = max{B_lcε₁, ½ε₀}` with `B_lc = 2(1 + C_J)B'`.
* `iterate_le`, `iterate_small`, `iterate_reaches`: the sequence `ε^{(0)} = ε₀`, `ε^{(l+1)} = max{Bε₁, ½ε^{(l)}}`
  satisfies `ε^{(l)} ≤ max{Bε₁, 2^{-l}ε₀}`, `ε^{(l)} ≤ max{Bε₁, ε₀} ≤ c_lc`, and reaches every `ε > 0` with
  `ε ≥ Bε₁`. The proof in the core says "each of them is at most ε₀", which fails when `B_lcε₁ > ε₀`; the bound by
  `max{B_lcε₁, ε₀} ≤ c_lc` is what the iteration needs.
-/
import Mathlib

noncomputable section

namespace CoreLean
namespace CriticalRegularArith

/-- **The ball of the proof**: the three distance inequalities from `RM₁ ≥ (L + 1)(D + 5)`. -/
theorem ball_distances {R M₁ L D : ℝ} (hL : 1 ≤ L) (hD : 0 ≤ D) (h : (L + 1) * (D + 5) ≤ R * M₁) :
    D + 3 ≤ R * M₁ / L ∧ D + 3 ≤ R * M₁ ∧ L * (D + 2) ≤ R * M₁ - D - 4 - L := by
  have hL0 : 0 < L := by linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [le_div_iff₀ hL0]; nlinarith
  · nlinarith
  · nlinarith

/-- `L²ε₁ + C₀L⁴ε₁² ≤ 2L²ε₁` for `C₀L²ε₁ ≤ 1`. -/
theorem average_plaquettes {L C₀ ε : ℝ} (hε : 0 ≤ ε) (h : C₀ * L ^ 2 * ε ≤ 1) :
    L ^ 2 * ε + C₀ * L ^ 4 * ε ^ 2 ≤ 2 * (L ^ 2 * ε) := by
  have hL : 0 ≤ L ^ 2 * ε := by positivity
  have : C₀ * L ^ 4 * ε ^ 2 = (C₀ * L ^ 2 * ε) * (L ^ 2 * ε) := by ring
  rw [this]
  nlinarith

/-- `K₁ = 6√N(2D + 1)L² = 3√N(2D + 1)·2L²`. -/
theorem K1_eq (N D L : ℝ) : 6 * Real.sqrt N * (2 * D + 1) * L ^ 2 = 3 * Real.sqrt N * (2 * D + 1) * (2 * L ^ 2) := by
  ring

/-- **The bound `10ρ ≤ B'ε₁ + ε₀/(4(1 + C_J))`**, with `ρ = K_H(κ₂ + eβ) + (C₆ + 4C₅)X²`, `κ₂ = (C_axL² + K₁)ε₁`,
`β = C_sL²ε₀ + K₁ε₁`, `X = B_bK_repβ` (here `Bb` stands for `B_bK_rep`). -/
theorem ten_rho {KH e Cax L K₁ Cs ε₀ ε₁ C₆₅ Bb X CJ : ℝ} (hKH : 0 ≤ KH) (he : 0 ≤ e) (hCs : 0 ≤ Cs)
    (hK₁ : 0 ≤ K₁) (hε₀ : 0 ≤ ε₀) (hε₁ : 0 ≤ ε₁) (hC₆₅ : 0 ≤ C₆₅) (hBb : 0 ≤ Bb) (hX0 : 0 ≤ X) (hCJ : 0 ≤ CJ)
    (hX : X = Bb * (Cs * L ^ 2 * ε₀ + K₁ * ε₁))
    (hr : 10 * KH * e * Cs * L ^ 2 ≤ 1 / (8 * (1 + CJ)))
    (hXc : 80 * (1 + CJ) * C₆₅ * Cs * L ^ 2 * Bb * X ≤ 1)
    (hconst : 1 ≤ 8 * (1 + CJ) * Cs * L ^ 2) (hKH1 : 1 ≤ 10 * KH) :
    10 * (KH * ((Cax * L ^ 2 + K₁) * ε₁ + e * (Cs * L ^ 2 * ε₀ + K₁ * ε₁)) + C₆₅ * X ^ 2) ≤
      (10 * KH * (Cax * L ^ 2 + 2 * K₁) + K₁ + 1) * ε₁ + ε₀ / (4 * (1 + CJ)) := by
  have hp : 0 < 8 * (1 + CJ) := by linarith
  set q := 8 * (1 + CJ) * Cs * L ^ 2
  -- `10K_He ≤ 1` and the first term of `eβ`
  have hr' : 10 * KH * e * Cs * L ^ 2 * (8 * (1 + CJ)) ≤ 1 := by
    rw [le_div_iff₀ hp] at hr; linarith
  have hKe : 10 * KH * e ≤ 1 := by
    have h1 : 10 * KH * e * q ≤ 1 := by simp only [q]; nlinarith
    have h0 : 0 ≤ 10 * KH * e := by positivity
    nlinarith
  have t1 : 10 * KH * e * (Cs * L ^ 2 * ε₀) ≤ ε₀ / (8 * (1 + CJ)) := by
    rw [le_div_iff₀ hp]; nlinarith
  have t2 : 10 * KH * e * (K₁ * ε₁) ≤ K₁ * ε₁ := by nlinarith [mul_nonneg hK₁ hε₁]
  -- the term `X²`
  have hXc' : 10 * C₆₅ * Bb * X ≤ 1 := by
    have h0 : 0 ≤ 10 * C₆₅ * Bb * X := by positivity
    have : 10 * C₆₅ * Bb * X * q ≤ 1 := by simp only [q]; nlinarith
    nlinarith
  have t3 : 10 * C₆₅ * X ^ 2 ≤ ε₀ / (8 * (1 + CJ)) + K₁ * ε₁ := by
    have e1 : 10 * C₆₅ * X ^ 2 = 10 * C₆₅ * Bb * X * (Cs * L ^ 2 * ε₀) + 10 * C₆₅ * Bb * X * (K₁ * ε₁) := by
      rw [hX]; ring
    have h1 : 10 * C₆₅ * Bb * X * (Cs * L ^ 2 * ε₀) ≤ ε₀ / (8 * (1 + CJ)) := by
      rw [le_div_iff₀ hp]; nlinarith
    have h2 : 10 * C₆₅ * Bb * X * (K₁ * ε₁) ≤ K₁ * ε₁ := by nlinarith [mul_nonneg hK₁ hε₁]
    linarith
  have e8 : ε₀ / (8 * (1 + CJ)) + ε₀ / (8 * (1 + CJ)) = ε₀ / (4 * (1 + CJ)) := by field_simp; ring
  have hB : 10 * KH * (Cax * L ^ 2 + K₁) * ε₁ + 2 * K₁ * ε₁ ≤ (10 * KH * (Cax * L ^ 2 + 2 * K₁) + K₁ + 1) * ε₁ := by
    have : K₁ * ε₁ ≤ 10 * KH * K₁ * ε₁ + ε₁ := by nlinarith [mul_nonneg hK₁ hε₁]
    nlinarith
  nlinarith

/-- `a + b ≤ max{2a, 2b}` in the form of `ε_p`, and `(1 + C_J)ε_p = max{B_lcε₁, ½ε₀}`. -/
theorem eps_p {B' ε₀ ε₁ CJ : ℝ} (hCJ : 0 ≤ CJ) :
    B' * ε₁ + ε₀ / (4 * (1 + CJ)) ≤ max (2 * B' * ε₁) (ε₀ / (2 * (1 + CJ))) ∧
      (1 + CJ) * max (2 * B' * ε₁) (ε₀ / (2 * (1 + CJ))) = max (2 * (1 + CJ) * B' * ε₁) (1 / 2 * ε₀) := by
  have hp : 0 < 1 + CJ := by linarith
  have e : ε₀ / (2 * (1 + CJ)) = 2 * (ε₀ / (4 * (1 + CJ))) := by field_simp; ring
  refine ⟨?_, ?_⟩
  · rw [e]
    rcases le_total (B' * ε₁) (ε₀ / (4 * (1 + CJ))) with h | h
    · exact le_max_of_le_right (by linarith)
    · exact le_max_of_le_left (by linarith)
  · rw [mul_max_of_nonneg _ _ hp.le]
    congr 1
    · ring
    · field_simp

/-- The sequence of the last statement. -/
def iter (B ε₁ ε₀ : ℝ) : ℕ → ℝ
  | 0 => ε₀
  | l + 1 => max (B * ε₁) (iter B ε₁ ε₀ l / 2)

/-- `ε^{(l)} ≤ max{Bε₁, 2^{-l}ε₀}`. -/
theorem iterate_le {B ε₁ ε₀ : ℝ} (hB : 0 ≤ B * ε₁) (hε₀ : 0 ≤ ε₀) (l : ℕ) :
    iter B ε₁ ε₀ l ≤ max (B * ε₁) (ε₀ / 2 ^ l) := by
  induction l with
  | zero => simp [iter]
  | succ l ih =>
    simp only [iter]
    refine max_le (le_max_left _ _) ?_
    rcases le_total (B * ε₁) (ε₀ / 2 ^ l) with h | h
    · rw [max_eq_right h] at ih
      exact le_max_of_le_right (by rw [pow_succ]; field_simp; field_simp at ih; linarith)
    · rw [max_eq_left h] at ih
      exact le_max_of_le_left (by linarith)

/-- `ε^{(l)} ≤ max{Bε₁, ε₀}`, hence `≤ c_lc` when `ε₀ ≤ c_lc` and `Bε₁ ≤ c_lc`. -/
theorem iterate_small {B ε₁ ε₀ c : ℝ} (hB : 0 ≤ B * ε₁) (hε₀ : 0 ≤ ε₀) (h0 : ε₀ ≤ c) (h1 : B * ε₁ ≤ c)
    (l : ℕ) : iter B ε₁ ε₀ l ≤ c := by
  have h := iterate_le hB hε₀ l
  have : ε₀ / 2 ^ l ≤ ε₀ := div_le_self hε₀ (one_le_pow₀ (by norm_num))
  exact h.trans (max_le h1 (this.trans h0))

/-- **Some `ε^{(l)}` is at most `ε`** for `ε > 0`, `ε ≥ Bε₁`. -/
theorem iterate_reaches {B ε₁ ε₀ ε : ℝ} (hB : 0 ≤ B * ε₁) (hε₀ : 0 ≤ ε₀) (hε : 0 < ε) (hBε : B * ε₁ ≤ ε) :
    ∃ l, iter B ε₁ ε₀ l ≤ ε := by
  obtain ⟨l, hl⟩ := pow_unbounded_of_one_lt (ε₀ / ε) (by norm_num : (1 : ℝ) < 2)
  refine ⟨l, (iterate_le hB hε₀ l).trans (max_le hBε ?_)⟩
  have h2 : (0 : ℝ) < 2 ^ l := by positivity
  rw [div_le_iff₀ h2]
  rw [div_lt_iff₀ hε] at hl
  linarith

/-- **The claim "each of them is at most ε₀" fails** when `Bε₁ > ε₀`: `ε^{(1)} = Bε₁ > ε₀`. -/
theorem iterate_counterexample : iter 1 1 0 1 = 1 ∧ (0 : ℝ) < 1 := by
  simp [iter]

end CriticalRegularArith
end CoreLean

end
