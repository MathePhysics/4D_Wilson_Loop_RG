/-
The one-dimensional profiles of `lem:bumps` of BALABAN_CORE.tex (`a021c13be348`). With `β(σ) = σ²(1 - σ)²` on `[0, 1]`
and `0` elsewhere, `β(s/n) = B_n(s)/n⁴` with `B_n(s) = s²(n - s)²` for `0 ≤ s ≤ n` (`Bq`). The core's facts, in this form:
`0 ≤ B_n ≤ n⁴/16`, first differences at most `n³/2`, second ones at most `2n²` (`β' ≤ 1/2`, `β'` 2-Lipschitz), and
`Σ_{t=0}^{n}B_n(t) = (n⁵ - n)/30 ≥ n⁵/32` for `n ≥ 2`. Then `u(s) = B_n(s)/S_n`, `v(s) = B_{n-1}(s)/S_{n-1}`,
`w(s) = v(s - 1) - v(s)`, `g(s) = (K/n)(u(s) + (n/2)w(s))` satisfy `Σ_ssg(s) = K`, `Σ_s(n - s)g(s) = 0`,
`|g| ≤ 20Kn⁻²`, `|g(s + 1) - g(s)| ≤ 124Kn⁻³` (`n ≥ 3`, `K ≥ 0`).
-/
import Mathlib

open Finset

noncomputable section

namespace CoreLean
namespace Bumps

/-- `B_n(s) = s²(n - s)²` on `[0, n]`, `0` elsewhere: `n⁴β(s/n)`. -/
def Bq (n : ℕ) (s : ℤ) : ℝ := if 0 ≤ s ∧ s ≤ n then ((s : ℝ) * ((n : ℝ) - s)) ^ 2 else 0

lemma Bq_nonneg (n : ℕ) (s : ℤ) : 0 ≤ Bq n s := by unfold Bq; split_ifs <;> positivity

lemma Bq_out {n : ℕ} {s : ℤ} (h : s < 0 ∨ (n : ℤ) < s) : Bq n s = 0 := by
  unfold Bq; rw [if_neg]; omega

lemma Bq_zero (n : ℕ) : Bq n 0 = 0 := by simp [Bq]

lemma Bq_self (n : ℕ) : Bq n n = 0 := by simp [Bq]

lemma Bq_symm (n : ℕ) (s : ℤ) : Bq n ((n : ℤ) - s) = Bq n s := by
  unfold Bq
  by_cases h : 0 ≤ s ∧ s ≤ n
  · rw [if_pos (by omega), if_pos h]; push_cast; ring
  · rw [if_neg (by omega), if_neg h]

lemma Bq_le (n : ℕ) (s : ℤ) : Bq n s ≤ (n : ℝ) ^ 4 / 16 := by
  unfold Bq
  split_ifs with h
  · have h1 : (0 : ℝ) ≤ s := by exact_mod_cast h.1
    have h2 : (s : ℝ) ≤ n := by exact_mod_cast h.2
    have h3 : (s : ℝ) * ((n : ℝ) - s) ≤ (n : ℝ) ^ 2 / 4 := by nlinarith [sq_nonneg ((s : ℝ) - n / 2)]
    have h4 : 0 ≤ (s : ℝ) * ((n : ℝ) - s) := mul_nonneg h1 (by linarith)
    calc ((s : ℝ) * ((n : ℝ) - s)) ^ 2 ≤ ((n : ℝ) ^ 2 / 4) ^ 2 := pow_le_pow_left₀ h4 h3 2
      _ = (n : ℝ) ^ 4 / 16 := by ring
  · positivity

/-- **The first differences**: `|B_n(s + 1) - B_n(s)| ≤ n³/2`. -/
lemma Bq_diff (n : ℕ) (s : ℤ) : |Bq n (s + 1) - Bq n s| ≤ (n : ℝ) ^ 3 / 2 := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rcases lt_or_ge s 0 with h0 | h0
  · rcases eq_or_lt_of_le (show s + 1 ≤ 0 by omega) with h1 | h1
    · rw [h1, Bq_zero, Bq_out (Or.inl h0)]; simp only [sub_self, abs_zero, add_zero, zero_add, sub_zero, zero_sub, mul_zero, abs_neg]; positivity
    · rw [Bq_out (Or.inl h1), Bq_out (Or.inl h0)]; simp only [sub_self, abs_zero, add_zero, zero_add, sub_zero, zero_sub, mul_zero, abs_neg]; positivity
  rcases lt_or_ge s n with hs | hs
  · -- `0 ≤ s ≤ n - 1`: with `x = n - 2s - 1`, the difference is `x(n² - x² - 1)/2`
    unfold Bq
    rw [if_pos (by omega), if_pos (by omega)]
    have h1 : (0 : ℝ) ≤ s := by exact_mod_cast h0
    have h2 : (s : ℝ) + 1 ≤ n := by exact_mod_cast (show s + 1 ≤ n by omega)
    push_cast
    set x := (n : ℝ) - 2 * s - 1 with hx
    have e : (((s : ℝ) + 1) * ((n : ℝ) - ((s : ℝ) + 1))) ^ 2 - ((s : ℝ) * ((n : ℝ) - s)) ^ 2 =
        x * ((n : ℝ) ^ 2 - x ^ 2 - 1) / 2 := by rw [hx]; ring
    rw [e, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    rw [div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2), abs_mul]
    have hx1 : |x| ≤ n := by rw [abs_le]; constructor <;> linarith
    have hx2 : 0 ≤ (n : ℝ) ^ 2 - x ^ 2 - 1 := by
      have hxa : |x| ≤ (n : ℝ) - 1 := by rw [abs_le]; constructor <;> linarith
      have : x ^ 2 ≤ ((n : ℝ) - 1) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hxa 2
      nlinarith
    rw [abs_of_nonneg hx2]
    calc |x| * ((n : ℝ) ^ 2 - x ^ 2 - 1) ≤ n * (n : ℝ) ^ 2 :=
          mul_le_mul hx1 (by nlinarith [sq_nonneg x]) hx2 hn
      _ = (n : ℝ) ^ 3 := by ring
  · rcases eq_or_lt_of_le hs with h1 | h1
    · rw [← h1, Bq_self, Bq_out (Or.inr (by omega))]; simp only [sub_self, abs_zero, add_zero, zero_add, sub_zero, zero_sub, mul_zero, abs_neg]; positivity
    · rw [Bq_out (Or.inr (by omega)), Bq_out (Or.inr h1)]; simp only [sub_self, abs_zero, add_zero, zero_add, sub_zero, zero_sub, mul_zero, abs_neg]; positivity

/-- **The second differences**: `|B_n(s + 1) - 2B_n(s) + B_n(s - 1)| ≤ 2n²` for `n ≥ 2`. -/
lemma Bq_diff2 {n : ℕ} (hn2 : 2 ≤ n) (s : ℤ) :
    |Bq n (s + 1) - 2 * Bq n s + Bq n (s - 1)| ≤ 2 * (n : ℝ) ^ 2 := by
  have hn : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  rcases lt_or_ge s 0 with h0 | h0
  · rw [Bq_out (Or.inl h0), Bq_out (Or.inl (by omega : s - 1 < 0))]
    rcases eq_or_lt_of_le (show s + 1 ≤ 0 by omega) with h1 | h1
    · rw [h1, Bq_zero]; simp only [sub_self, abs_zero, add_zero, zero_add, sub_zero, zero_sub, mul_zero, abs_neg]; positivity
    · rw [Bq_out (Or.inl h1)]; simp only [sub_self, abs_zero, add_zero, zero_add, sub_zero, zero_sub, mul_zero, abs_neg]; positivity
  rcases eq_or_lt_of_le h0 with h1 | h1
  · -- `s = 0`: the value `B_n(1) = (n - 1)²`
    rw [← h1, Bq_zero, Bq_out (Or.inl (by norm_num : (0 : ℤ) - 1 < 0))]
    unfold Bq
    rw [if_pos (by omega)]
    push_cast
    rw [mul_zero, sub_zero, add_zero, abs_of_nonneg (by positivity)]
    nlinarith
  rcases lt_or_ge s n with hs | hs
  · -- `1 ≤ s ≤ n - 1`: the second difference of the quartic is `2n² - 12s(n - s) + 2`
    unfold Bq
    rw [if_pos (by omega), if_pos (by omega), if_pos (by omega)]
    push_cast
    have e : (((s : ℝ) + 1) * ((n : ℝ) - ((s : ℝ) + 1))) ^ 2 - 2 * ((s : ℝ) * ((n : ℝ) - s)) ^ 2 +
        (((s : ℝ) - 1) * ((n : ℝ) - ((s : ℝ) - 1))) ^ 2 = 2 * (n : ℝ) ^ 2 - 12 * ((s : ℝ) * ((n : ℝ) - s)) + 2 := by
      ring
    rw [e, abs_le]
    have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast h1
    have hs2 : (s : ℝ) + 1 ≤ n := by exact_mod_cast (show s + 1 ≤ n by omega)
    have hp : (n : ℝ) - 1 ≤ (s : ℝ) * ((n : ℝ) - s) := by nlinarith
    have hq : (s : ℝ) * ((n : ℝ) - s) ≤ (n : ℝ) ^ 2 / 4 := by nlinarith [sq_nonneg ((s : ℝ) - n / 2)]
    constructor <;> nlinarith
  · rcases eq_or_lt_of_le hs with h2 | h2
    · -- `s = n`
      rw [← h2, Bq_self, Bq_out (Or.inr (by omega))]
      unfold Bq
      rw [if_pos (by omega)]
      push_cast
      rw [abs_of_nonneg (by positivity)]
      nlinarith
    · rw [Bq_out (Or.inr (by omega)), Bq_out (Or.inr h2)]
      rcases eq_or_lt_of_le (show (n : ℤ) ≤ s - 1 by omega) with h3 | h3
      · rw [← h3, Bq_self]; simp only [sub_self, abs_zero, add_zero, zero_add, sub_zero, zero_sub, mul_zero, abs_neg]; positivity
      · rw [Bq_out (Or.inr h3)]; simp only [sub_self, abs_zero, add_zero, zero_add, sub_zero, zero_sub, mul_zero, abs_neg]; positivity

/-! ### The sums -/

lemma sum_range_sq (n : ℕ) : ∑ t ∈ range (n + 1), (t : ℝ) ^ 2 = n * (n + 1) * (2 * n + 1) / 6 := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; push_cast; ring

lemma sum_range_cube (n : ℕ) : ∑ t ∈ range (n + 1), (t : ℝ) ^ 3 = ((n : ℝ) * (n + 1) / 2) ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; push_cast; ring

lemma sum_range_four (n : ℕ) :
    ∑ t ∈ range (n + 1), (t : ℝ) ^ 4 = n * (n + 1) * (2 * n + 1) * (3 * n ^ 2 + 3 * n - 1) / 30 := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; push_cast; ring

/-- `S_n = Σ_{t=0}^{n}B_n(t)`. -/
def SB (n : ℕ) : ℝ := ∑ t ∈ range (n + 1), Bq n t

/-- `S_n = (n⁵ - n)/30`, the core's `Σ_{t=0}^{m}β(t/m) = (m⁴ - 1)/(30m³)`. -/
lemma SB_eq (n : ℕ) : SB n = ((n : ℝ) ^ 5 - n) / 30 := by
  unfold SB
  have e : ∀ t ∈ range (n + 1), Bq n (t : ℤ) =
      (n : ℝ) ^ 2 * (t : ℝ) ^ 2 - 2 * n * (t : ℝ) ^ 3 + (t : ℝ) ^ 4 := fun t ht => by
    unfold Bq
    rw [if_pos (by have := mem_range.1 ht; omega)]
    push_cast; ring
  rw [sum_congr rfl e, sum_add_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum, sum_range_sq, sum_range_cube,
    sum_range_four]
  ring

lemma SB_ge {n : ℕ} (hn : 2 ≤ n) : (n : ℝ) ^ 5 / 32 ≤ SB n := by
  rw [SB_eq]
  have h : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have h4 : (16 : ℝ) ≤ (n : ℝ) ^ 4 := by nlinarith [sq_nonneg ((n : ℝ) ^ 2 - 4)]
  nlinarith

lemma SB_pos {n : ℕ} (hn : 2 ≤ n) : 0 < SB n := by
  have h0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  exact lt_of_lt_of_le (by positivity) (SB_ge hn)

/-- The sums over `[0, n]` in `ℤ` are the sums over `range (n + 1)`. -/
lemma sum_Icc_eq_range (n : ℕ) (f : ℤ → ℝ) :
    ∑ s ∈ Icc (0 : ℤ) n, f s = ∑ t ∈ range (n + 1), f t := by
  refine sum_nbij' (fun s => s.toNat) (fun t => (t : ℤ)) ?_ ?_ ?_ ?_ ?_
  · intro s hs; simp only [mem_Icc, mem_coe] at hs; simp only [mem_range, mem_coe]; omega
  · intro t ht; simp only [mem_range, mem_coe] at ht; simp only [mem_Icc, mem_coe]; omega
  · intro s hs; simp only [mem_Icc, mem_coe] at hs; simp; omega
  · intro t _; simp
  · intro s hs; simp only [mem_Icc, mem_coe] at hs; congr 1; omega

lemma sum_Bq (n : ℕ) : ∑ s ∈ Icc (0 : ℤ) n, Bq n s = SB n := by rw [sum_Icc_eq_range]; rfl

/-- The reflection `s ↦ n - s` of `[0, n]`. -/
lemma sum_reflect (n : ℕ) (f : ℤ → ℝ) : ∑ s ∈ Icc (0 : ℤ) n, f ((n : ℤ) - s) = ∑ s ∈ Icc (0 : ℤ) n, f s := by
  refine sum_nbij' (fun s => (n : ℤ) - s) (fun s => (n : ℤ) - s) ?_ ?_ ?_ ?_ ?_
  · intro s hs; simp only [mem_Icc, mem_coe] at hs ⊢; omega
  · intro s hs; simp only [mem_Icc, mem_coe] at hs ⊢; omega
  · intro s _; simp
  · intro s _; simp
  · intro s _; rfl

/-- `Σ_ssB_n(s) = (n/2)S_n` by the symmetry `B_n(s) = B_n(n - s)`. -/
lemma sum_s_Bq (n : ℕ) : ∑ s ∈ Icc (0 : ℤ) n, (s : ℝ) * Bq n s = (n : ℝ) / 2 * SB n := by
  have h := sum_reflect n fun s => (s : ℝ) * Bq n s
  simp only [Bq_symm] at h
  have h2 : ∑ s ∈ Icc (0 : ℤ) n, (((n : ℤ) - s : ℤ) : ℝ) * Bq n s + ∑ s ∈ Icc (0 : ℤ) n, (s : ℝ) * Bq n s =
      (n : ℝ) * SB n := by
    rw [← sum_add_distrib, ← sum_Bq, mul_sum]
    exact sum_congr rfl fun s _ => by push_cast; ring
  rw [h] at h2
  linarith

/-! ### `u`, `v`, `w`, `g` -/

variable (n : ℕ)

/-- `u(s) = β(s/n)/Σ_tβ(t/n)`. -/
def u (s : ℤ) : ℝ := Bq n s / SB n

/-- `v(s) = β(s/(n - 1))/Σ_tβ(t/(n - 1))`. -/
def v (s : ℤ) : ℝ := Bq (n - 1) s / SB (n - 1)

/-- `w(s) = v(s - 1) - v(s)`. -/
def w (s : ℤ) : ℝ := v n (s - 1) - v n s

/-- `g(s) = (K/n)(u(s) + (n/2)w(s))`. -/
def g (K : ℝ) (s : ℤ) : ℝ := K / n * (u n s + (n : ℝ) / 2 * w n s)

variable {n}

lemma u_out {s : ℤ} (h : s ≤ 0 ∨ (n : ℤ) ≤ s) : u n s = 0 := by
  unfold u
  rcases h with h | h
  · rcases eq_or_lt_of_le h with h | h
    · rw [h, Bq_zero, zero_div]
    · rw [Bq_out (Or.inl h), zero_div]
  · rcases eq_or_lt_of_le h with h | h
    · rw [← h, Bq_self, zero_div]
    · rw [Bq_out (Or.inr h), zero_div]

lemma v_out (hn : 1 ≤ n) {s : ℤ} (h : s ≤ 0 ∨ (n : ℤ) - 1 ≤ s) : v n s = 0 := by
  unfold v
  have hc : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
  rcases h with h | h
  · rcases eq_or_lt_of_le h with h | h
    · rw [h, Bq_zero, zero_div]
    · rw [Bq_out (Or.inl h), zero_div]
  · rcases eq_or_lt_of_le h with h | h
    · rw [← h, ← hc, Bq_self, zero_div]
    · rw [Bq_out (Or.inr (by omega)), zero_div]

lemma w_out (hn : 1 ≤ n) {s : ℤ} (h : s ≤ 0 ∨ (n : ℤ) ≤ s) : w n s = 0 := by
  unfold w
  rw [v_out hn (by omega), v_out hn (by omega), sub_zero]

lemma sum_u (hn : 2 ≤ n) : ∑ s ∈ Icc (0 : ℤ) n, u n s = 1 := by
  unfold u; rw [← sum_div, sum_Bq, div_self (SB_pos hn).ne']

lemma sum_s_u (hn : 2 ≤ n) : ∑ s ∈ Icc (0 : ℤ) n, (s : ℝ) * u n s = (n : ℝ) / 2 := by
  unfold u
  simp only [mul_div_assoc']
  rw [← sum_div, sum_s_Bq, mul_div_assoc, div_self (SB_pos hn).ne', mul_one]

/-- The sums of `v` over `[0, n]`: `Σv = 1`, and the shifted sums. -/
lemma sum_v (hn : 3 ≤ n) : ∑ s ∈ Icc (0 : ℤ) n, v n s = 1 := by
  have h1 : ∑ s ∈ Icc (0 : ℤ) n, v n s = ∑ s ∈ Icc (0 : ℤ) (n - 1 : ℕ), v n s := by
    rw [← sum_subset (s₁ := Icc (0 : ℤ) (n - 1 : ℕ)) (fun s hs => by simp only [mem_Icc] at hs ⊢; omega)
      (fun s hs hs' => v_out (by omega) (by simp only [mem_Icc] at hs hs'; omega))]
  rw [h1]
  unfold v
  rw [← sum_div, sum_Bq, div_self (SB_pos (by omega)).ne']

lemma sum_shift_v (hn : 3 ≤ n) (f : ℤ → ℝ) :
    ∑ s ∈ Icc (0 : ℤ) n, f s * v n (s - 1) = ∑ s ∈ Icc (0 : ℤ) n, f (s + 1) * v n s := by
  -- both sides are sums over the support `[1, n - 2]` of `v`
  have hL : ∑ s ∈ Icc (0 : ℤ) n, f s * v n (s - 1) = ∑ s ∈ Icc (1 : ℤ) n, f s * v n (s - 1) := by
    rw [← sum_subset (s₁ := Icc (1 : ℤ) n) (fun s hs => by simp only [mem_Icc] at hs ⊢; omega)
      (fun s hs hs' => by rw [v_out (by omega) (by simp only [mem_Icc] at hs hs'; omega), mul_zero])]
  have hR : ∑ s ∈ Icc (0 : ℤ) n, f (s + 1) * v n s = ∑ s ∈ Icc (0 : ℤ) (n - 1), f (s + 1) * v n s := by
    rw [← sum_subset (s₁ := Icc (0 : ℤ) (n - 1)) (fun s hs => by simp only [mem_Icc] at hs ⊢; omega)
      (fun s hs hs' => by rw [v_out (by omega) (by simp only [mem_Icc] at hs hs'; omega), mul_zero])]
  rw [hL, hR]
  refine sum_nbij' (fun s => s - 1) (fun s => s + 1) ?_ ?_ ?_ ?_ ?_
  · intro s hs; simp only [mem_Icc, mem_coe] at hs ⊢; omega
  · intro s hs; simp only [mem_Icc, mem_coe] at hs ⊢; omega
  · intro s _; simp
  · intro s _; simp
  · intro s _; simp

lemma sum_w (hn : 3 ≤ n) : ∑ s ∈ Icc (0 : ℤ) n, w n s = 0 := by
  unfold w
  rw [sum_sub_distrib]
  have h := sum_shift_v hn fun _ => (1 : ℝ)
  simp only [one_mul] at h
  rw [h, sub_self]

lemma sum_s_w (hn : 3 ≤ n) : ∑ s ∈ Icc (0 : ℤ) n, (s : ℝ) * w n s = 1 := by
  unfold w
  simp only [mul_sub, sum_sub_distrib]
  rw [sum_shift_v hn fun s => (s : ℝ)]
  simp only [Int.cast_add, Int.cast_one, add_mul, one_mul, sum_add_distrib]
  rw [sum_v hn]; ring

variable (K : ℝ)

/-- `Σ_ssg(s) = K`. -/
lemma sum_s_g (hn : 3 ≤ n) : ∑ s ∈ Icc (0 : ℤ) n, (s : ℝ) * g n K s = K := by
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  unfold g
  have e : ∀ s : ℤ, (s : ℝ) * (K / n * (u n s + (n : ℝ) / 2 * w n s)) =
      K / n * ((s : ℝ) * u n s) + K / 2 * ((s : ℝ) * w n s) := fun s => by field_simp
  simp only [e, sum_add_distrib, ← mul_sum, sum_s_u (by omega : 2 ≤ n), sum_s_w hn]
  field_simp; ring

/-- `Σ_s(n - s)g(s) = 0`. -/
lemma sum_ns_g (hn : 3 ≤ n) : ∑ s ∈ Icc (0 : ℤ) n, ((n : ℝ) - s) * g n K s = 0 := by
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hg : ∑ s ∈ Icc (0 : ℤ) n, g n K s = K / n := by
    unfold g
    rw [← mul_sum, sum_add_distrib, ← mul_sum, sum_u (by omega), sum_w hn]
    ring
  simp only [sub_mul, sum_sub_distrib, ← mul_sum, hg, sum_s_g K hn]
  field_simp
  ring

/-! ### The bounds -/

lemma u_le (hn : 2 ≤ n) (s : ℤ) : |u n s| ≤ 2 / n := by
  have hpos := SB_pos hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  unfold u
  rw [abs_div, abs_of_nonneg (Bq_nonneg _ _), abs_of_pos hpos, div_le_div_iff₀ hpos hn0]
  have h1 := Bq_le n s
  have h2 := SB_ge hn
  nlinarith

lemma u_diff (hn : 2 ≤ n) (s : ℤ) : |u n (s + 1) - u n s| ≤ 16 / (n : ℝ) ^ 2 := by
  have hpos := SB_pos hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  unfold u
  rw [← sub_div, abs_div, abs_of_pos hpos, div_le_div_iff₀ hpos (by positivity)]
  have h1 := Bq_diff n s
  have h2 := SB_ge hn
  nlinarith

lemma w_le (hn : 3 ≤ n) (s : ℤ) : |w n s| ≤ 36 / (n : ℝ) ^ 2 := by
  have hm : 2 ≤ n - 1 := by omega
  have hpos := SB_pos hm
  have hc : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by push_cast [show 1 ≤ n by omega]; ring
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  unfold w v
  rw [← sub_div, abs_div, abs_of_pos hpos, abs_sub_comm, div_le_div_iff₀ hpos (by positivity)]
  have h1 := Bq_diff (n - 1) (s - 1)
  rw [sub_add_cancel] at h1
  have h2 := SB_ge hm
  rw [hc] at h1 h2
  have h3 : (4 : ℝ) * (n : ℝ) ^ 2 ≤ 9 * ((n : ℝ) - 1) ^ 2 := by nlinarith
  have hm0 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  -- `|Δv| ≤ (m³/2)/(m⁵/32) = 16/m² ≤ 36/n²`
  calc |Bq (n - 1) s - Bq (n - 1) (s - 1)| * (n : ℝ) ^ 2 ≤ ((n : ℝ) - 1) ^ 3 / 2 * (n : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ ≤ 36 * (((n : ℝ) - 1) ^ 5 / 32) := by nlinarith [pow_pos hm0 3]
    _ ≤ 36 * SB (n - 1) := by linarith

lemma w_diff (hn : 3 ≤ n) (s : ℤ) : |w n (s + 1) - w n s| ≤ 216 / (n : ℝ) ^ 3 := by
  have hm : 2 ≤ n - 1 := by omega
  have hpos := SB_pos hm
  have hc : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by push_cast [show 1 ≤ n by omega]; ring
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  unfold w v
  have e : Bq (n - 1) (s + 1 - 1) / SB (n - 1) - Bq (n - 1) (s + 1) / SB (n - 1) -
      (Bq (n - 1) (s - 1) / SB (n - 1) - Bq (n - 1) s / SB (n - 1)) =
      -((Bq (n - 1) (s + 1) - 2 * Bq (n - 1) s + Bq (n - 1) (s - 1)) / SB (n - 1)) := by
    rw [add_sub_cancel_right]; ring
  rw [e, abs_neg, abs_div, abs_of_pos hpos, div_le_div_iff₀ hpos (by positivity)]
  have h1 := Bq_diff2 hm s
  have h2 := SB_ge hm
  rw [hc] at h1 h2
  have hm0 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have h3 : (8 : ℝ) * (n : ℝ) ^ 3 ≤ 27 * ((n : ℝ) - 1) ^ 3 := by nlinarith
  calc |Bq (n - 1) (s + 1) - 2 * Bq (n - 1) s + Bq (n - 1) (s - 1)| * (n : ℝ) ^ 3
      ≤ 2 * ((n : ℝ) - 1) ^ 2 * (n : ℝ) ^ 3 := mul_le_mul_of_nonneg_right h1 (by positivity)
    _ ≤ 216 * (((n : ℝ) - 1) ^ 5 / 32) := by nlinarith [pow_pos hm0 2]
    _ ≤ 216 * SB (n - 1) := by linarith

/-- `|g| ≤ 20Kn⁻²`. -/
lemma g_le (hn : 3 ≤ n) {K : ℝ} (hK : 0 ≤ K) (s : ℤ) : |g n K s| ≤ 20 * K / (n : ℝ) ^ 2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  unfold g
  rw [abs_mul, abs_of_nonneg (by positivity)]
  have h1 := u_le (by omega : 2 ≤ n) s
  have h2 := w_le hn s
  have h3 : |u n s + (n : ℝ) / 2 * w n s| ≤ 20 / n := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) / 2)]
    calc |u n s| + (n : ℝ) / 2 * |w n s| ≤ 2 / n + (n : ℝ) / 2 * (36 / (n : ℝ) ^ 2) :=
          add_le_add h1 (mul_le_mul_of_nonneg_left h2 (by positivity))
      _ = 20 / n := by field_simp; ring
  calc K / n * |u n s + (n : ℝ) / 2 * w n s| ≤ K / n * (20 / n) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = 20 * K / (n : ℝ) ^ 2 := by field_simp

/-- `|g(s + 1) - g(s)| ≤ 124Kn⁻³`. -/
lemma g_diff (hn : 3 ≤ n) {K : ℝ} (hK : 0 ≤ K) (s : ℤ) :
    |g n K (s + 1) - g n K s| ≤ 124 * K / (n : ℝ) ^ 3 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  unfold g
  rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity)]
  have h1 := u_diff (by omega : 2 ≤ n) s
  have h2 := w_diff hn s
  have h3 : |u n (s + 1) + (n : ℝ) / 2 * w n (s + 1) - (u n s + (n : ℝ) / 2 * w n s)| ≤ 124 / (n : ℝ) ^ 2 := by
    rw [show u n (s + 1) + (n : ℝ) / 2 * w n (s + 1) - (u n s + (n : ℝ) / 2 * w n s) =
      (u n (s + 1) - u n s) + (n : ℝ) / 2 * (w n (s + 1) - w n s) by ring]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) / 2)]
    calc |u n (s + 1) - u n s| + (n : ℝ) / 2 * |w n (s + 1) - w n s| ≤
          16 / (n : ℝ) ^ 2 + (n : ℝ) / 2 * (216 / (n : ℝ) ^ 3) :=
          add_le_add h1 (mul_le_mul_of_nonneg_left h2 (by positivity))
      _ = 124 / (n : ℝ) ^ 2 := by field_simp; ring
  calc K / n * |u n (s + 1) + (n : ℝ) / 2 * w n (s + 1) - (u n s + (n : ℝ) / 2 * w n s)| ≤
        K / n * (124 / (n : ℝ) ^ 2) := mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = 124 * K / (n : ℝ) ^ 3 := by field_simp

lemma g_out (hn : 1 ≤ n) {s : ℤ} (h : s ≤ 0 ∨ (n : ℤ) ≤ s) : g n K s = 0 := by
  unfold g; rw [u_out h, w_out hn h]; ring

end Bumps
end CoreLean

end
