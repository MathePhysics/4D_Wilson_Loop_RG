/-
The bump of the step "The lower bound at the trivial field" of `prop:sf-block` of BALABAN_CORE.tex (`d4ef86a9a5fd`),
in one variable, on the integers. The core uses `η(t) = cos²(πt)`; any function with the following properties serves:
`τ_h(k) = ((h + 1)² - k²)²` for `|k| ≤ h + 1` and `0` otherwise, with `c = (h + 1)²`:

* `tau_nonneg`, `tau_le`: `0 ≤ τ ≤ c²`; `tau_supp`: `τ(k) = 0` for `|k| > h` (the support lies in the block
  `|k| ≤ h`, of `2h + 1` points);
* `tau_second`: `|τ(k + 1) - 2τ(k) + τ(k - 1)| ≤ 18c` for every `k` (the function is `C^{1,1}` across `±(h + 1)`);
* `tau_sum`: `Σ_{|k| ≤ h}τ(k) ≥ (9/16)(h + 1)c²` (the points `|k| ≤ (h + 1)/2` alone).
-/
import Mathlib

open Finset

noncomputable section

namespace CoreLean
namespace SFBump

/-- The bump `τ_h(k) = ((h + 1)² - k²)²` for `|k| ≤ h + 1`, `0` otherwise. -/
def tau (h : ℕ) (k : ℤ) : ℝ := if |k| ≤ h + 1 then (((h : ℝ) + 1) ^ 2 - (k : ℝ) ^ 2) ^ 2 else 0

lemma tau_nonneg (h : ℕ) (k : ℤ) : 0 ≤ tau h k := by
  unfold tau; split_ifs <;> positivity

lemma tau_le (h : ℕ) (k : ℤ) : tau h k ≤ (((h : ℝ) + 1) ^ 2) ^ 2 := by
  unfold tau
  split_ifs with hk
  · have hk' : (k : ℝ) ^ 2 ≤ ((h : ℝ) + 1) ^ 2 := by
      have : |(k : ℝ)| ≤ (h : ℝ) + 1 := by exact_mod_cast hk
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) this 2
    have h0 : 0 ≤ ((h : ℝ) + 1) ^ 2 - (k : ℝ) ^ 2 := by linarith
    have h1 : ((h : ℝ) + 1) ^ 2 - (k : ℝ) ^ 2 ≤ ((h : ℝ) + 1) ^ 2 := by nlinarith
    exact pow_le_pow_left₀ h0 h1 2
  · positivity

lemma tau_eq_poly {h : ℕ} {k : ℤ} (hk : |k| ≤ h + 1) :
    tau h k = (((h : ℝ) + 1) ^ 2 - (k : ℝ) ^ 2) ^ 2 := by unfold tau; rw [if_pos hk]

lemma tau_out {h : ℕ} {k : ℤ} (hk : h + 1 < |k|) : tau h k = 0 := by unfold tau; rw [if_neg (by omega)]

/-- **The support**: `τ(k) = 0` for `|k| > h`. -/
lemma tau_supp {h : ℕ} {k : ℤ} (hk : (h : ℤ) < |k|) : tau h k = 0 := by
  rcases lt_or_eq_of_le (show (h : ℤ) + 1 ≤ |k| by omega) with h1 | h1
  · exact tau_out h1
  · rw [tau_eq_poly h1.symm.le]
    have : (k : ℝ) ^ 2 = ((h : ℝ) + 1) ^ 2 := by
      rw [← sq_abs, ← Int.cast_abs, ← h1]; push_cast; ring
    rw [this]; ring

/-- The polynomial second difference: `p(k + 1) - 2p(k) + p(k - 1) = 12k² - 4c + 2` for `p(k) = (c - k²)²`. -/
lemma poly_second (c k : ℝ) :
    (c - (k + 1) ^ 2) ^ 2 - 2 * (c - k ^ 2) ^ 2 + (c - (k - 1) ^ 2) ^ 2 = 12 * k ^ 2 - 4 * c + 2 := by ring

/-- **The second differences**: `|τ(k + 1) - 2τ(k) + τ(k - 1)| ≤ 18c`. -/
theorem tau_second (h : ℕ) (k : ℤ) :
    |tau h (k + 1) - 2 * tau h k + tau h (k - 1)| ≤ 18 * ((h : ℝ) + 1) ^ 2 := by
  set c : ℝ := ((h : ℝ) + 1) ^ 2
  have hc : 1 ≤ c := by
    have h1 : (1 : ℝ) ≤ (h : ℝ) + 1 := by linarith [(Nat.cast_nonneg h : (0 : ℝ) ≤ h)]
    nlinarith
  rcases le_or_gt |k| h with hk | hk
  · -- `|k| ≤ h`: all three points in the polynomial region
    have h1 : |k + 1| ≤ h + 1 := by rw [abs_le] at hk ⊢; omega
    have h2 : |k - 1| ≤ h + 1 := by rw [abs_le] at hk ⊢; omega
    rw [tau_eq_poly h1, tau_eq_poly (show |k| ≤ h + 1 by omega), tau_eq_poly h2]
    push_cast
    rw [poly_second]
    have hk2 : (k : ℝ) ^ 2 ≤ c := by
      have : |(k : ℝ)| ≤ (h : ℝ) + 1 := by
        have : |k| ≤ h + 1 := by omega
        exact_mod_cast this
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) this 2
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg (k : ℝ)]
  · rcases lt_or_eq_of_le (show (h : ℤ) + 1 ≤ |k| by omega) with hk1 | hk1
    · -- `|k| ≥ h + 2`: at most `τ(k ± 1)` with `|k ± 1| ≥ h + 1`, which vanish
      have ha : tau h k = 0 := tau_out hk1
      have e1 : |k| - 1 ≤ |k + 1| := by
        have := abs_sub_abs_le_abs_sub k (-1); simpa [sub_neg_eq_add] using this
      have e2 : |k| - 1 ≤ |k - 1| := by
        have := abs_sub_abs_le_abs_sub k 1; simpa using this
      have hb : tau h (k + 1) = 0 := tau_supp (by omega)
      have hb' : tau h (k - 1) = 0 := tau_supp (by omega)
      rw [ha, hb, hb']; simp; positivity
    · -- `|k| = h + 1`: `τ(k) = 0`, one neighbour outside, the other at `|k ∓ 1| = h`
      have ha : tau h k = 0 := tau_supp (by omega)
      rw [ha]
      rcases abs_cases k with ⟨h3, h4⟩ | ⟨h3, h4⟩
      · -- `k = h + 1`
        have hk' : k = h + 1 := by omega
        have hb : tau h (k + 1) = 0 := tau_supp (by rw [abs_of_nonneg (by omega)]; omega)
        rw [hb, tau_eq_poly (show |k - 1| ≤ h + 1 by rw [abs_of_nonneg (by omega)]; omega), hk']
        push_cast
        rw [abs_le]; constructor <;> nlinarith [(Nat.cast_nonneg h : (0 : ℝ) ≤ h)]
      · -- `k = -(h + 1)`
        have hk' : k = -(h + 1) := by omega
        have hb : tau h (k - 1) = 0 := tau_supp (by rw [abs_of_neg (by omega)]; omega)
        rw [hb, tau_eq_poly (show |k + 1| ≤ h + 1 by rw [abs_of_nonpos (by omega)]; omega), hk']
        push_cast
        rw [abs_le]; constructor <;> nlinarith [(Nat.cast_nonneg h : (0 : ℝ) ≤ h)]

/-- **The mass**: `Σ_{|k| ≤ h}τ(k) ≥ (9/16)(h + 1)c²`. -/
theorem tau_sum (h : ℕ) :
    (9 / 16) * ((h : ℝ) + 1) * (((h : ℝ) + 1) ^ 2) ^ 2 ≤ ∑ k ∈ Finset.Icc (-(h : ℤ)) h, tau h k := by
  set c : ℝ := ((h : ℝ) + 1) ^ 2
  -- the points `0 ≤ k ≤ (h + 1)/2` (at least `(h + 1)/2` of them) and their mirror images
  set T := (Finset.Icc (-(h : ℤ)) h).filter fun k => 4 * k ^ 2 ≤ ((h : ℤ) + 1) ^ 2
  have hT : ∀ k ∈ T, (9 / 16) * c ^ 2 ≤ tau h k := by
    intro k hk
    obtain ⟨hk1, hk2⟩ := mem_filter.1 hk
    rw [mem_Icc] at hk1
    rw [tau_eq_poly (show |k| ≤ h + 1 by rw [abs_le]; omega)]
    have : 4 * (k : ℝ) ^ 2 ≤ c := by simp only [c]; exact_mod_cast hk2
    have h0 : (3 / 4) * c ≤ c - (k : ℝ) ^ 2 := by linarith
    have hc : 0 ≤ (3 / 4) * c := by positivity
    calc (9 / 16) * c ^ 2 = ((3 / 4) * c) ^ 2 := by ring
      _ ≤ (c - (k : ℝ) ^ 2) ^ 2 := pow_le_pow_left₀ hc h0 2
  -- `T` contains `0, ±1, …, ±⌊(h + 1)/2⌋`, at least `h + 1` points... we only need `(h + 1)` of the mass bound
  have hcard : ((h : ℝ) + 1) ≤ (T.card : ℝ) := by
    set m := (h + 1) / 2
    have hsub : Finset.Icc (-(m : ℤ)) m ⊆ T := by
      intro k hk
      rw [mem_Icc] at hk
      refine mem_filter.2 ⟨mem_Icc.2 ⟨by omega, by omega⟩, ?_⟩
      have h1 : |k| ≤ m := by rw [abs_le]; omega
      have h2 : 2 * (m : ℤ) ≤ h + 1 := by omega
      have h3 : 2 * |k| ≤ (h : ℤ) + 1 := by omega
      have h4 : 0 ≤ 2 * |k| := by positivity
      nlinarith [sq_abs k, mul_self_le_mul_self h4 h3]
    have hc := card_le_card hsub
    rw [Int.card_Icc] at hc
    have : (h + 1 : ℤ) ≤ (m : ℤ) + 1 - -(m : ℤ) := by omega
    have : h + 1 ≤ ((m : ℤ) + 1 - -(m : ℤ)).toNat := by omega
    exact_mod_cast this.trans hc
  calc (9 / 16) * ((h : ℝ) + 1) * c ^ 2 ≤ (T.card : ℝ) * ((9 / 16) * c ^ 2) := by nlinarith [sq_nonneg c]
    _ = ∑ _k ∈ T, (9 / 16) * c ^ 2 := by rw [sum_const, nsmul_eq_mul]
    _ ≤ ∑ k ∈ T, tau h k := sum_le_sum hT
    _ ≤ ∑ k ∈ Finset.Icc (-(h : ℤ)) h, tau h k :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun k _ _ => tau_nonneg h k

end SFBump
end CoreLean

end
