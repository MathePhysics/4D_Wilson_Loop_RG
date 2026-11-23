/-
`lem:move-sources`(i) of BALABAN_CORE.tex (`a021c13be348`), the arithmetic of its proof for `m' = m + t > m`. With
`d' ≥ 27M_c(t - 1)` (`lem:distance`(ii)), `27δ_⋆M_c ≥ 8 log L` (`eq:layer-condition`), `ρ_{0,m'} ≤ (1 + β₀)t^{1/2}ρ_{0,m}`
(`lem:factor-field`(i)), `1 + β₀ ≤ √2` (`def:admissible`), `L ≥ 3`, and `s(y) ≤ σ2^{-(n-m')}ρ_{0,m'}`:
`e^{-½δ_⋆d'}s(y) ≤ 2L⁴σ2^{-(n-m)}ρ_{0,m}` (`source_profile`), through `e^{-½δ_⋆d'} ≤ L^{-4(t-1)}` (`decay_layers`) and
`(2L^{-4})^t(1 + β₀)t^{1/2} ≤ 2` (`profile_factor`).
-/
import Mathlib

noncomputable section

namespace CoreLean
namespace MoveSources

/-- `e^{-½δ_⋆d'} ≤ L^{-4(t-1)}`. -/
theorem decay_layers {L δ Mc d : ℝ} (hL : 1 ≤ L) (hMc : 0 < Mc) (hδ : 0 ≤ δ) (t : ℕ) (ht : 1 ≤ t)
    (hd : 27 * Mc * ((t : ℝ) - 1) ≤ d) (hcond : 8 * Real.log L ≤ 27 * δ * Mc) :
    Real.exp (-(δ * d / 2)) ≤ (L⁻¹) ^ (4 * (t - 1)) := by
  have hL0 : 0 < L := by linarith
  rw [inv_pow, ← Real.exp_log (pow_pos hL0 (4 * (t - 1))), ← Real.exp_neg, Real.log_pow]
  refine Real.exp_le_exp.2 (neg_le_neg ?_)
  have hk : ((4 * (t - 1) : ℕ) : ℝ) = 4 * ((t : ℝ) - 1) := by
    rw [Nat.cast_mul, Nat.cast_sub ht]; norm_num
  rw [hk]
  have h1t : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hk0 : 0 ≤ (t : ℝ) - 1 := by linarith
  calc 4 * ((t : ℝ) - 1) * Real.log L = ((t : ℝ) - 1) * (8 * Real.log L) / 2 := by ring
    _ ≤ ((t : ℝ) - 1) * (27 * δ * Mc) / 2 := by gcongr
    _ = δ * (27 * Mc * ((t : ℝ) - 1)) / 2 := by ring
    _ ≤ δ * d / 2 := by gcongr

/-- `(2L^{-4})^t(1 + β₀)t^{1/2} ≤ 2` for `t ≥ 1`, `L ≥ 3`, `1 + β₀ ≤ √2`. -/
theorem profile_factor {L β₀ : ℝ} (hL : 3 ≤ L) (hβ : 0 ≤ 1 + β₀) (hβ₀ : 1 + β₀ ≤ Real.sqrt 2) (t : ℕ) (ht : 1 ≤ t) :
    (2 * (L⁻¹) ^ 4) ^ t * (1 + β₀) * Real.sqrt t ≤ 2 := by
  have hL0 : 0 < L := by linarith
  set q := 2 * (L⁻¹) ^ 4
  have hq0 : 0 ≤ q := by positivity
  have hq : q ≤ 1 / 40 := by
    have : (L⁻¹) ^ 4 ≤ (1 / 3) ^ 4 := by
      apply pow_le_pow_left₀ (by positivity)
      rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hL
    simp only [q]; nlinarith
  -- `√t ≤ t ≤ 2^{t-1}` and `q^t·2^{t-1} ≤ q`
  have hsq : Real.sqrt t ≤ t := by
    have h1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have ht2 : (t : ℝ) ≤ 2 ^ (t - 1) := by
    have h := Nat.lt_two_pow_self (n := t - 1)
    have : t ≤ 2 ^ (t - 1) := by omega
    exact_mod_cast this
  have hqt : q ^ t * 2 ^ (t - 1) ≤ q := by
    have e : q ^ t = q * q ^ (t - 1) := by rw [← pow_succ']; congr 1; omega
    rw [e, mul_assoc, ← mul_pow]
    have : (q * 2) ^ (t - 1) ≤ 1 := pow_le_one₀ (by positivity) (by linarith)
    nlinarith [pow_nonneg (mul_nonneg hq0 (by norm_num : (0 : ℝ) ≤ 2)) (t - 1)]
  have hs2 : Real.sqrt 2 ≤ 2 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  calc q ^ t * (1 + β₀) * Real.sqrt t ≤ q ^ t * Real.sqrt 2 * (2 ^ (t - 1) : ℝ) := by
        have h1 : 0 ≤ q ^ t := pow_nonneg hq0 t
        have h2 : Real.sqrt t ≤ 2 ^ (t - 1) := hsq.trans ht2
        calc q ^ t * (1 + β₀) * Real.sqrt t ≤ q ^ t * Real.sqrt 2 * Real.sqrt t := by gcongr
          _ ≤ q ^ t * Real.sqrt 2 * 2 ^ (t - 1) := by gcongr
    _ = Real.sqrt 2 * (q ^ t * 2 ^ (t - 1)) := by ring
    _ ≤ 2 * (1 / 40) := by gcongr; exact hqt.trans hq
    _ ≤ 2 := by norm_num

/-- **`lem:move-sources`(i)** for `m' = m + t > m`. -/
theorem source_profile {L δ Mc d σ ρm ρm' β₀ s : ℝ} (hL : 3 ≤ L) (hMc : 0 < Mc) (hδ : 0 ≤ δ) (hσ : 0 ≤ σ)
    (hρm : 0 ≤ ρm) (hβ : 0 ≤ 1 + β₀) (hβ₀ : 1 + β₀ ≤ Real.sqrt 2) (n m t : ℕ) (ht : 1 ≤ t) (hn : m + t ≤ n)
    (hd : 27 * Mc * ((t : ℝ) - 1) ≤ d) (hcond : 8 * Real.log L ≤ 27 * δ * Mc)
    (hρ : ρm' ≤ (1 + β₀) * Real.sqrt t * ρm) (hs0 : 0 ≤ s) (hs : s ≤ σ * (1 / 2) ^ (n - (m + t)) * ρm') :
    Real.exp (-(δ * d / 2)) * s ≤ 2 * L ^ 4 * σ * (1 / 2) ^ (n - m) * ρm := by
  have hL0 : 0 < L := by linarith
  have hdec := decay_layers (by linarith) hMc hδ t ht hd hcond
  have hfac := profile_factor hL hβ hβ₀ t ht
  -- `2^{-(n-m-t)} = 2^t·2^{-(n-m)}`
  have e2 : (1 / 2 : ℝ) ^ (n - (m + t)) = 2 ^ t * (1 / 2) ^ (n - m) := by
    have h : n - m = (n - (m + t)) + t := by omega
    rw [h, pow_add]
    have h2 : (2 : ℝ) ^ t * (1 / 2) ^ t = 1 := by rw [← mul_pow]; norm_num
    calc (1 / 2 : ℝ) ^ (n - (m + t)) = (1 / 2) ^ (n - (m + t)) * ((2 : ℝ) ^ t * (1 / 2) ^ t) := by
          rw [h2, mul_one]
      _ = 2 ^ t * ((1 / 2) ^ (n - (m + t)) * (1 / 2) ^ t) := by ring
  -- `L^{-4(t-1)} = L⁴·(L^{-4})^t`
  have eL : (L⁻¹) ^ (4 * (t - 1)) = L ^ 4 * ((L⁻¹) ^ 4) ^ t := by
    rw [← pow_mul]
    have : 4 * t = 4 * (t - 1) + 4 := by omega
    rw [this, pow_add, ← mul_assoc, mul_comm (L ^ 4), mul_assoc, ← mul_pow, mul_inv_cancel₀ hL0.ne', one_pow,
      mul_one]
  have hs' : s ≤ σ * (2 ^ t * (1 / 2) ^ (n - m)) * ((1 + β₀) * Real.sqrt t * ρm) := by
    rw [← e2]
    exact hs.trans (mul_le_mul_of_nonneg_left hρ (by positivity))
  have hE0 : 0 ≤ Real.exp (-(δ * d / 2)) := (Real.exp_pos _).le
  calc Real.exp (-(δ * d / 2)) * s ≤ (L⁻¹) ^ (4 * (t - 1)) *
        (σ * (2 ^ t * (1 / 2) ^ (n - m)) * ((1 + β₀) * Real.sqrt t * ρm)) := by
        apply mul_le_mul hdec hs' hs0 (by positivity)
    _ = L ^ 4 * σ * (1 / 2) ^ (n - m) * ρm * ((2 * (L⁻¹) ^ 4) ^ t * (1 + β₀) * Real.sqrt t) := by
        rw [eL, mul_pow]; ring
    _ ≤ L ^ 4 * σ * (1 / 2) ^ (n - m) * ρm * 2 := by
        apply mul_le_mul_of_nonneg_left hfac (by positivity)
    _ = 2 * L ^ 4 * σ * (1 / 2) ^ (n - m) * ρm := by ring

/-- **The case `m' ≤ m`**: `ĝ ↦ ĝ(log ĝ^{-2})^{q₀}` is increasing for `ĝ ≤ e^{-q₀}`; with `ĝ = e^{-u}`,
`log ĝ^{-2} = 2u`, this is `e^{-u'}(2u')^{q₀} ≤ e^{-u}(2u)^{q₀}` for `q₀ ≤ u ≤ u'`, from
`(u'/u)^{q₀} = e^{q₀ log(u'/u)} ≤ e^{q₀(u' - u)/u} ≤ e^{u' - u}`. -/
theorem profile_mono {q₀ u u' : ℝ} (hq : 0 ≤ q₀) (hu : q₀ ≤ u) (hu0 : 0 < u) (huu : u ≤ u') :
    Real.exp (-u') * (2 * u') ^ q₀ ≤ Real.exp (-u) * (2 * u) ^ q₀ := by
  have hu'0 : 0 < u' := lt_of_lt_of_le hu0 huu
  have hsplit : (2 * u') ^ q₀ = (2 * u) ^ q₀ * (u' / u) ^ q₀ := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    congr 1; field_simp
  have hratio : (u' / u) ^ q₀ ≤ Real.exp (u' - u) := by
    rw [Real.rpow_def_of_pos (by positivity), mul_comm]
    refine Real.exp_le_exp.2 ?_
    have h1 : Real.log (u' / u) ≤ u' / u - 1 := Real.log_le_sub_one_of_pos (by positivity)
    have h2 : q₀ * (u' / u - 1) ≤ u' - u := by
      have e : q₀ * (u' / u - 1) = q₀ / u * (u' - u) := by field_simp
      rw [e]
      have : q₀ / u ≤ 1 := (div_le_one hu0).2 hu
      have h3 : 0 ≤ u' - u := by linarith
      nlinarith [div_nonneg hq hu0.le]
    calc q₀ * Real.log (u' / u) ≤ q₀ * (u' / u - 1) := mul_le_mul_of_nonneg_left h1 hq
      _ ≤ u' - u := h2
  have hp0 : 0 ≤ (2 * u) ^ q₀ := Real.rpow_nonneg (by positivity) q₀
  calc Real.exp (-u') * (2 * u') ^ q₀ = Real.exp (-u') * (2 * u) ^ q₀ * (u' / u) ^ q₀ := by
        rw [hsplit]; ring
    _ ≤ Real.exp (-u') * (2 * u) ^ q₀ * Real.exp (u' - u) := by gcongr
    _ = Real.exp (-u) * (2 * u) ^ q₀ := by
        rw [mul_right_comm, ← Real.exp_add]; congr 2; ring

end MoveSources
end CoreLean

end
