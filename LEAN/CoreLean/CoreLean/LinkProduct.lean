/-
`lem:link-product` of BALABAN_CORE.tex (`a021c13be348`), the arithmetic of its proof.

* *Two factors*, the comparison of the scales: for `0 < a₀ ≤ b ≤ a`, `0 ≤ d ≤ b` (`d = |z - x|_1`) and
  `0 ≤ β_b ≤ 1`, `a₀da^{-4} ≤ (ab)^{-1}(d/b)^{β_b}` (`scale_compare`), which turns the bound `6C_qκ'κ''a₀³da^{-4}` of the
  first bracket into one of the form of `eq:link-product`; the two brackets together give `10C_qκ'κ''`
  (`two_factor_constant`).
* *Several factors*: with `K_0 = κ_0` and `K_r ≤ K_{r-1}(1 + C_Πκ_r) + κ_r` whenever `K_{r-1} + κ_r ≤ 1/128` (the case of
  two factors), `κ_r ≥ 0`, `κ = Σ_{r ≤ R}κ_r ≤ 1/256` and `C_Πκ ≤ log 2`, every `K_r`, `r ≤ R`, is at most `2κ ≤ 1/128`
  (`several_factors`), through `K_r ≤ (Σ_{s ≤ r}κ_s)Π_{t ≤ r}(1 + C_Πκ_t) ≤ e^{C_Πκ}κ`.
-/
import Mathlib

open Finset

noncomputable section

namespace CoreLean
namespace LinkProduct

/-- The comparison of the scales in the first bracket. -/
theorem scale_compare {a₀ a b d β : ℝ} (ha₀ : 0 < a₀) (hb : a₀ ≤ b) (ha : b ≤ a) (hd0 : 0 ≤ d) (hd : d ≤ b)
    (hβ1 : β ≤ 1) : a₀ * d * a⁻¹ ^ 4 ≤ (a * b)⁻¹ * (d / b) ^ β := by
  have hb0 : 0 < b := lt_of_lt_of_le ha₀ hb
  have ha0 : 0 < a := lt_of_lt_of_le hb0 ha
  -- `(d/b)^β ≥ d/b`
  have hdb : d / b ≤ (d / b) ^ β := by
    rcases eq_or_lt_of_le hd0 with h | h
    · rw [← h, zero_div]; exact Real.rpow_nonneg (le_refl 0) _
    · have h1 : 0 < d / b := div_pos h hb0
      have h2 : d / b ≤ 1 := (div_le_one hb0).2 hd
      calc d / b = (d / b) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ (d / b) ^ β := Real.rpow_le_rpow_of_exponent_ge h1 h2 hβ1
  have hab : 0 < (a * b)⁻¹ := by positivity
  refine le_trans ?_ (mul_le_mul_of_nonneg_left hdb hab.le)
  -- `a₀da^{-4} ≤ d/(ab²)` since `a₀b² ≤ a³`
  have h3 : a₀ * b ^ 2 ≤ a ^ 3 := by
    have : a₀ * b ^ 2 ≤ a * a ^ 2 :=
      mul_le_mul (hb.trans ha) (pow_le_pow_left₀ hb0.le ha 2) (by positivity) ha0.le
    nlinarith
  rw [inv_pow, show (a * b)⁻¹ * (d / b) = d / (a * b ^ 2) by field_simp]
  rw [div_eq_mul_inv, show a₀ * d * (a ^ 4)⁻¹ = d * (a₀ / a ^ 4) by ring]
  refine mul_le_mul_of_nonneg_left ?_ hd0
  rw [div_le_iff₀ (by positivity)]
  calc a₀ = a₀ * b ^ 2 * (a * b ^ 2)⁻¹ * a := by field_simp
    _ ≤ a ^ 3 * (a * b ^ 2)⁻¹ * a := by gcongr
    _ = (a * b ^ 2)⁻¹ * a ^ 4 := by ring

/-- The two brackets give the constant `10C_q`. -/
theorem two_factor_constant {Cq k1 k2 X Y : ℝ} (hX : X ≤ 4 * Cq * k1 * k2) (hY : Y ≤ 6 * Cq * k1 * k2) :
    X + Y ≤ 10 * Cq * k1 * k2 := by linarith

lemma prod_le_exp {r : ℕ} {C : ℝ} (hC : 0 ≤ C) (κ : ℕ → ℝ) (hκ : ∀ s, 0 ≤ κ s) :
    ∏ t ∈ range (r + 1), (1 + C * κ t) ≤ Real.exp (C * ∑ t ∈ range (r + 1), κ t) := by
  rw [mul_sum, Real.exp_sum]
  refine Finset.prod_le_prod₀ (fun t _ => by nlinarith [hκ t]) fun t _ => ?_
  have := Real.add_one_le_exp (C * κ t)
  linarith

/-- **Several factors**. -/
theorem several_factors (κ K : ℕ → ℝ) (hκ : ∀ s, 0 ≤ κ s) {C : ℝ} (hC : 0 ≤ C) (R : ℕ)
    (hsmall : ∑ s ∈ range (R + 1), κ s ≤ 1 / 256)
    (hCκ : C * ∑ s ∈ range (R + 1), κ s ≤ Real.log 2) (hK0 : K 0 = κ 0)
    (hstep : ∀ r, 1 ≤ r → r ≤ R → K (r - 1) + κ r ≤ 1 / 128 → K r ≤ K (r - 1) * (1 + C * κ r) + κ r) :
    ∀ r ≤ R, K r ≤ 2 * ∑ s ∈ range (R + 1), κ s := by
  set κtot := ∑ s ∈ range (R + 1), κ s
  set S : ℕ → ℝ := fun r => ∑ s ∈ range (r + 1), κ s
  set P : ℕ → ℝ := fun r => ∏ t ∈ range (r + 1), (1 + C * κ t)
  have hP1 : ∀ r, 1 ≤ P r := fun r => Finset.one_le_prod₀ fun t _ => by nlinarith [hκ t]
  have hS0 : ∀ r, 0 ≤ S r := fun r => Finset.sum_nonneg fun s _ => hκ s
  have hSle : ∀ r ≤ R, S r ≤ κtot := fun r hr =>
    Finset.sum_le_sum_of_subset_of_nonneg (range_subset_range.2 (by omega)) fun s _ _ => hκ s
  have hP2 : ∀ r ≤ R, P r ≤ 2 := by
    intro r hr
    calc P r ≤ Real.exp (C * S r) := prod_le_exp hC κ hκ
      _ ≤ Real.exp (Real.log 2) := Real.exp_le_exp.2 ((mul_le_mul_of_nonneg_left (hSle r hr) hC).trans hCκ)
      _ = 2 := Real.exp_log two_pos
  -- the invariant `K_r ≤ S_r P_r`
  have hinv : ∀ r ≤ R, K r ≤ S r * P r := by
    intro r
    induction r with
    | zero =>
      intro _
      simp only [S, P, zero_add, range_one, sum_singleton, prod_singleton, hK0]
      nlinarith [hκ 0, mul_nonneg hC (hκ 0)]
    | succ r ih =>
      intro hr
      have hKr := ih (by omega)
      have hKr2 : K r ≤ 2 * S r := by
        calc K r ≤ S r * P r := hKr
          _ ≤ S r * 2 := mul_le_mul_of_nonneg_left (hP2 r (by omega)) (hS0 r)
          _ = 2 * S r := by ring
      have hcond : K (r + 1 - 1) + κ (r + 1) ≤ 1 / 128 := by
        rw [Nat.add_sub_cancel]
        have : S (r + 1) = S r + κ (r + 1) := Finset.sum_range_succ _ _
        have h2 := hSle (r + 1) hr
        linarith [hκ (r + 1)]
      have := hstep (r + 1) (by omega) hr hcond
      rw [Nat.add_sub_cancel] at this
      have eS : S (r + 1) = S r + κ (r + 1) := Finset.sum_range_succ _ _
      have eP : P (r + 1) = P r * (1 + C * κ (r + 1)) := Finset.prod_range_succ _ _
      have h1C : 0 ≤ 1 + C * κ (r + 1) := by nlinarith [hκ (r + 1)]
      calc K (r + 1) ≤ K r * (1 + C * κ (r + 1)) + κ (r + 1) := this
        _ ≤ S r * P r * (1 + C * κ (r + 1)) + κ (r + 1) := by gcongr
        _ ≤ S r * P (r + 1) + κ (r + 1) * P (r + 1) := by
            rw [eP]; nlinarith [hκ (r + 1), hP1 (r + 1), eP]
        _ = S (r + 1) * P (r + 1) := by rw [eS]; ring
  intro r hr
  calc K r ≤ S r * P r := hinv r hr
    _ ≤ S r * 2 := mul_le_mul_of_nonneg_left (hP2 r hr) (hS0 r)
    _ ≤ κtot * 2 := mul_le_mul_of_nonneg_right (hSle r hr) (by norm_num)
    _ = 2 * κtot := by ring

end LinkProduct
end CoreLean

end
