/-
`prop:momentum-space`(ii) of BALABAN_CORE.tex (`50787904c4ef`): the bounds of the symbols. With `n = L^k` and `a₀ = 1/n`
(the units of the last lattice):

* `uf_bound`: `|sin(p/2)/(n sin(p/(2n)))| ≤ 2/(1 + |m|)` for `p = p' + 2πm`, `-π ≤ p' ≤ π`, `|m| ≤ (n - 1)/2` (one factor of
  `u_k`; the quotient with vanishing denominator is one), and `u_bound` for the product over the four directions.
* `v_bound`: `|e^{ip} - 1| ≤ n|e^{ip/n} - 1|`, i.e. `|v_μ(p)| ≤ 1`.
* `delta_lower`: `|(e^{iap} - 1)/a|² ≥ 4π⁻²p²` for `|ap| ≤ π` (so `Δ(p) ≥ 4π⁻²|p|²`), and `delta0_bounds`:
  `4π⁻²p'² ≤ |e^{ip'} - 1|² ≤ p'²` for `|p'| ≤ π` (so `4π⁻²|p'|² ≤ Δ₀(p') ≤ |p'|²`).
-/
import Mathlib

open Real Complex

noncomputable section

namespace CoreLean
namespace MomentumSymbols

/-- `|sin(kx)| ≤ k|sin x|`. -/
lemma abs_sin_nat_mul_le (x : ℝ) : ∀ k : ℕ, |Real.sin (k * x)| ≤ k * |Real.sin x|
  | 0 => by simp
  | k + 1 => by
    have ih := abs_sin_nat_mul_le x k
    have e : Real.sin (((k + 1 : ℕ) : ℝ) * x) = Real.sin (k * x) * Real.cos x + Real.cos (k * x) * Real.sin x := by
      rw [show (((k + 1 : ℕ) : ℝ) * x) = k * x + x by push_cast; ring, Real.sin_add]
    rw [e]
    calc |Real.sin (k * x) * Real.cos x + Real.cos (k * x) * Real.sin x|
        ≤ |Real.sin (k * x)| * |Real.cos x| + |Real.cos (k * x)| * |Real.sin x| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ |Real.sin (k * x)| * 1 + 1 * |Real.sin x| := by
          gcongr
          · exact Real.abs_cos_le_one _
          · exact Real.abs_cos_le_one _
      _ ≤ k * |Real.sin x| + |Real.sin x| := by linarith
      _ = ((k + 1 : ℕ) : ℝ) * |Real.sin x| := by push_cast; ring

/-- `|e^{iθ} - 1| = 2|sin(θ/2)|`. -/
lemma norm_exp_sub_one (θ : ℝ) : ‖Complex.exp (I * θ) - 1‖ = 2 * |Real.sin (θ / 2)| := by
  rw [Complex.norm_exp_I_mul_ofReal_sub_one]; simp

/-- Jordan's inequality: `2|θ|/π ≤ |e^{iθ} - 1| ≤ |θ|` for `|θ| ≤ π`. -/
lemma chord_bounds {θ : ℝ} (hθ : |θ| ≤ π) :
    2 / π * |θ| ≤ ‖Complex.exp (I * θ) - 1‖ ∧ ‖Complex.exp (I * θ) - 1‖ ≤ |θ| := by
  rw [norm_exp_sub_one]
  refine ⟨?_, ?_⟩
  swap
  · have := Real.abs_sin_le_abs (x := θ / 2)
    rw [abs_div, abs_two] at this
    linarith
  have h1 : 0 ≤ |θ| / 2 := by positivity
  have h2 : |θ| / 2 ≤ π / 2 := by linarith
  have hs := Real.mul_le_sin h1 h2
  have hsabs : |Real.sin (θ / 2)| = |Real.sin (|θ| / 2)| := by
    rcases abs_choice θ with h | h <;> rw [h]
    rw [neg_div, Real.sin_neg, abs_neg]
  have e : |Real.sin (θ / 2)| = Real.sin (|θ| / 2) := by
    rw [hsabs]
    exact abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi h1 (by linarith))
  rw [e]
  have hπ := Real.pi_pos
  calc 2 / π * |θ| = 2 * (2 / π * (|θ| / 2)) := by ring
    _ ≤ 2 * Real.sin (|θ| / 2) := by linarith

/-- **`Δ(p) ≥ 4π⁻²|p|²`**, one direction: `|(e^{iap} - 1)/a|² ≥ 4π⁻²p²` for `a > 0`, `|ap| ≤ π`. -/
theorem delta_lower {a p : ℝ} (ha : 0 < a) (hap : |a * p| ≤ π) :
    4 / π ^ 2 * p ^ 2 ≤ (‖Complex.exp (I * ((a * p : ℝ) : ℂ)) - 1‖ / a) ^ 2 := by
  have h := (chord_bounds hap).1
  have hπ := Real.pi_pos
  have h0 : 0 ≤ 2 / π * |a * p| := by positivity
  have hsq := pow_le_pow_left₀ h0 h 2
  have e1 : (2 / π * |a * p|) ^ 2 = 4 / π ^ 2 * p ^ 2 * a ^ 2 := by
    rw [mul_pow, sq_abs, div_pow]; ring
  rw [div_pow, le_div_iff₀ (by positivity)]
  linarith

/-- **`4π⁻²|p'|² ≤ Δ₀(p') ≤ |p'|²`**, one direction: `4π⁻²p'² ≤ |e^{ip'} - 1|² ≤ p'²` for `|p'| ≤ π`. -/
theorem delta0_bounds {p : ℝ} (hp : |p| ≤ π) :
    4 / π ^ 2 * p ^ 2 ≤ ‖Complex.exp (I * p) - 1‖ ^ 2 ∧ ‖Complex.exp (I * p) - 1‖ ^ 2 ≤ p ^ 2 := by
  obtain ⟨h1, h2⟩ := chord_bounds hp
  have hπ := Real.pi_pos
  constructor
  · have h0 : 0 ≤ 2 / π * |p| := by positivity
    calc 4 / π ^ 2 * p ^ 2 = (2 / π * |p|) ^ 2 := by rw [mul_pow, sq_abs]; field_simp; ring
      _ ≤ _ := pow_le_pow_left₀ h0 h1 2
  · calc ‖Complex.exp (I * p) - 1‖ ^ 2 ≤ |p| ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
      _ = p ^ 2 := sq_abs p

/-- **`|v_μ(p)| ≤ 1`**: `|e^{ip} - 1| ≤ n|e^{ip/n} - 1|` for `n ≥ 1`. -/
theorem v_bound (n : ℕ) (hn : 1 ≤ n) (p : ℝ) :
    ‖Complex.exp (I * p) - 1‖ ≤ n * ‖Complex.exp (I * ((p / n : ℝ) : ℂ)) - 1‖ := by
  rw [norm_exp_sub_one, norm_exp_sub_one]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have e : p / 2 = (n : ℝ) * (p / n / 2) := by field_simp
  rw [e]
  have := abs_sin_nat_mul_le (p / n / 2) n
  nlinarith [abs_nonneg (Real.sin (p / n / 2))]

/-- One factor of `u_k`: `sin(p/2)/(n sin(p/(2n)))`, with the value one where the denominator vanishes. -/
def uf (n : ℕ) (p : ℝ) : ℝ := if Real.sin (p / (2 * n)) = 0 then 1 else Real.sin (p / 2) / (n * Real.sin (p / (2 * n)))

/-- **`|u_k(p' + l)| ≤ ∏_μ 2(1 + |m_μ|)⁻¹`**, one factor: for `p = p' + 2πm` with `|p'| ≤ π` and `2|m| + 1 ≤ n`,
`|sin(p/2)/(n sin(p/(2n)))| ≤ 2/(1 + |m|)`. Since `|p|/(2n) ≤ π/2`, Jordan's inequality gives `|sin(p/(2n))| ≥ |p|/(πn)`,
while `|sin(p/2)| = |sin(p'/2)|`; for `m = 0` the quotient is at most `π/2`, and otherwise `|p| ≥ π|m|`. -/
theorem uf_bound (n : ℕ) (hn : 1 ≤ n) {p' : ℝ} (hp' : |p'| ≤ π) (m : ℤ) (hm : 2 * |m| + 1 ≤ n) :
    |uf n (p' + 2 * π * m)| ≤ 2 / (1 + |(m : ℝ)|) := by
  set p := p' + 2 * π * m with hp
  have hπ := Real.pi_pos
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hmR : 2 * |(m : ℝ)| + 1 ≤ n := by
    have : ((2 * |m| + 1 : ℤ) : ℝ) ≤ ((n : ℤ) : ℝ) := by exact_mod_cast hm
    push_cast at this; exact this
  have hm0 : 0 ≤ |(m : ℝ)| := abs_nonneg _
  have hpabs : |p| ≤ π + 2 * π * |(m : ℝ)| := by
    calc |p| ≤ |p'| + |2 * π * m| := abs_add_le _ _
      _ = |p'| + 2 * π * |(m : ℝ)| := by rw [abs_mul, abs_mul, abs_two, abs_of_pos hπ]
      _ ≤ π + 2 * π * |(m : ℝ)| := by linarith
  have hq : |p| / (2 * n) ≤ π / 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hsin2 : |Real.sin (p / 2)| = |Real.sin (p' / 2)| := by
    have e : p / 2 = p' / 2 + m * π := by rw [hp]; ring
    rw [e, Real.sin_add_int_mul_pi, abs_mul]
    simp
  -- the denominator
  have hden : |p| / (π * n) ≤ |Real.sin (p / (2 * n))| := by
    have h0 : 0 ≤ |p| / (2 * n) := by positivity
    have hs := Real.mul_le_sin h0 hq
    have e : |Real.sin (p / (2 * n))| = Real.sin (|p| / (2 * n)) := by
      rcases le_total 0 p with h | h
      · rw [abs_of_nonneg h, abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by
          rw [abs_of_nonneg h] at hq; linarith))]
      · rw [abs_of_nonpos h, show p / (2 * n) = -(-p / (2 * n)) by ring, Real.sin_neg, abs_neg,
          abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by
            have : 0 ≤ -p := by linarith
            positivity) (by rw [abs_of_nonpos h] at hq; linarith))]
    rw [e]
    calc |p| / (π * n) = 2 / π * (|p| / (2 * n)) := by field_simp; try ring
      _ ≤ _ := hs
  unfold uf
  split_ifs with h0
  · -- the denominator vanishes only at `p = 0`, where `m = 0`
    rw [h0, abs_zero] at hden
    have hp0 : |p| = 0 := by
      have hpos : 0 < π * n := by positivity
      have h := hden
      rw [div_le_iff₀ hpos] at h
      exact le_antisymm (by linarith) (abs_nonneg p)
    have hm' : (m : ℝ) = 0 := by
      have hp00 : p = 0 := abs_eq_zero.1 hp0
      by_contra hne
      have h1 : 1 ≤ |(m : ℝ)| := by
        have : (1 : ℤ) ≤ |m| := Int.one_le_abs (by exact_mod_cast hne)
        exact_mod_cast this
      have : 2 * π * |(m : ℝ)| ≤ |p'| := by
        have e : 2 * π * (m : ℝ) = -p' := by rw [hp] at hp00; linarith
        have e2 : |p'| = |2 * π * (m : ℝ)| := by rw [e, abs_neg]
        rw [e2, abs_mul, abs_mul, abs_two, abs_of_pos hπ]
      nlinarith
    rw [hm', abs_zero, abs_one]; norm_num
  · rw [abs_div, abs_mul, abs_of_pos hn0, hsin2]
    have hdpos : 0 < |Real.sin (p / (2 * n))| := abs_pos.2 h0
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    by_cases hmz : (m : ℝ) = 0
    · -- `p = p'`: the quotient is at most `π/2`
      have hpp : p = p' := by rw [hp, hmz]; ring
      rw [hmz, abs_zero]
      have hsp : |Real.sin (p' / 2)| ≤ |p'| / 2 := by
        have := Real.abs_sin_le_abs (x := p' / 2); rwa [abs_div, abs_two] at this
      have hd' : |p'| / (π * n) ≤ |Real.sin (p / (2 * n))| := by rw [← hpp]; exact hden
      have : |p'| ≤ π * n * |Real.sin (p / (2 * n))| := by
        rw [div_le_iff₀ (by positivity)] at hd'; linarith
      have hπ4 : π ≤ 4 := by linarith [Real.pi_lt_d2]
      have hs0 : 0 ≤ (n : ℝ) * |Real.sin (p / (2 * n))| := by positivity
      calc |Real.sin (p' / 2)| * (1 + 0) ≤ |p'| / 2 := by linarith
        _ ≤ π * n * |Real.sin (p / (2 * n))| / 2 := by linarith
        _ ≤ 2 * (n * |Real.sin (p / (2 * n))|) := by nlinarith
    · -- `|p| ≥ π|m|`
      have h1 : 1 ≤ |(m : ℝ)| := by
        have hne : m ≠ 0 := fun h => hmz (by simp [h])
        have : (1 : ℤ) ≤ |m| := Int.one_le_abs hne
        exact_mod_cast this
      have hplow : π * |(m : ℝ)| ≤ |p| := by
        have : |2 * π * (m : ℝ)| ≤ |p| + |p'| := by
          have e : 2 * π * (m : ℝ) = p - p' := by rw [hp]; ring
          rw [e]; exact abs_sub _ _
        rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)] at this
        nlinarith
      have hd2 : π * |(m : ℝ)| / (π * n) ≤ |Real.sin (p / (2 * n))| := le_trans (by gcongr) hden
      have : |(m : ℝ)| ≤ n * |Real.sin (p / (2 * n))| := by
        rw [div_le_iff₀ (by positivity)] at hd2
        nlinarith
      have hs1 : |Real.sin (p' / 2)| ≤ 1 := Real.abs_sin_le_one _
      nlinarith [abs_nonneg (Real.sin (p' / 2))]

/-- **`|u_k(p' + l)| ≤ ∏_μ 2(1 + |m_μ|)⁻¹`**. -/
theorem u_bound (n : ℕ) (hn : 1 ≤ n) {p' : Fin 4 → ℝ} (hp' : ∀ μ, |p' μ| ≤ π) (m : Fin 4 → ℤ)
    (hm : ∀ μ, 2 * |m μ| + 1 ≤ n) :
    |∏ μ, uf n (p' μ + 2 * π * m μ)| ≤ ∏ μ, 2 / (1 + |((m μ : ℤ) : ℝ)|) := by
  rw [Finset.abs_prod]
  exact Finset.prod_le_prod₀ (fun μ _ => abs_nonneg _) fun μ _ => uf_bound n hn (hp' μ) (m μ) (hm μ)

end MomentumSymbols
end CoreLean

end
