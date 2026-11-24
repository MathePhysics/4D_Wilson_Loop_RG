/-
`prop:sf-vector-lower` of BALABAN_CORE.tex (`48a8b5af31cd`), the step "The cut-off minimiser": the cut-off function
in one variable on the integers, in place of the core's piecewise cubic `η`. With the bump `τ_h` of `SFBump.lean` and
its mass `m`, `G(u) = m⁻¹Σ_{k ≤ h, k + c₀ < u}τ_h(k)` rises from `0` to `1` on `[D + 1, D + 2h + 2]` (`c₀ = D + h + 1`), and
`χ₁(t) = 1 - G(|t|)`.

* `tau_first`: `|τ(k) - τ(k - 1)| ≤ 6(h + 1)³`.
* `G_succ`: `G(u + 1) - G(u) = τ(u - c₀)/m`.
* `chi1_one`, `chi1_zero`: `χ₁ = 1` for `|t| ≤ D + 1`, `χ₁ = 0` for `|t| ≥ D + 2h + 2`; `chi1_mem`: `0 ≤ χ₁ ≤ 1`.
* `chi1_first`: `|χ₁(t + 1) - χ₁(t)| ≤ 16/(9(h + 1))`; `chi1_second`: `|χ₁(t + 1) - 2χ₁(t) + χ₁(t - 1)| ≤ 32/(3(h + 1)²)`.
-/
import CoreLean.SFBump

open Finset

noncomputable section

namespace CoreLean
namespace SFBump

/-- **The first differences of the bump**: `|τ(k) - τ(k - 1)| ≤ 6(h + 1)³`. -/
theorem tau_first (h : ℕ) (k : ℤ) : |tau h k - tau h (k - 1)| ≤ 6 * ((h : ℝ) + 1) ^ 3 := by
  set c : ℝ := ((h : ℝ) + 1) ^ 2
  have hh : (0 : ℝ) ≤ h := Nat.cast_nonneg h
  by_cases hk : |k| ≤ h + 1 ∧ |k - 1| ≤ h + 1
  · obtain ⟨h1, h2⟩ := hk
    rw [tau_eq_poly h1, tau_eq_poly h2]
    have hk1 : |(k : ℝ)| ≤ (h : ℝ) + 1 := by exact_mod_cast h1
    have hk2 : |((k - 1 : ℤ) : ℝ)| ≤ (h : ℝ) + 1 := by exact_mod_cast h2
    have s1 : (k : ℝ) ^ 2 ≤ c := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hk1 2
    have s2 : ((k - 1 : ℤ) : ℝ) ^ 2 ≤ c := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hk2 2
    push_cast at s2 hk2 ⊢
    have e : (c - (k : ℝ) ^ 2) ^ 2 - (c - ((k : ℝ) - 1) ^ 2) ^ 2 =
        (1 - 2 * (k : ℝ)) * (2 * c - (k : ℝ) ^ 2 - ((k : ℝ) - 1) ^ 2) := by ring
    rw [e, abs_mul]
    have ha : |1 - 2 * (k : ℝ)| ≤ 3 * ((h : ℝ) + 1) := by
      rw [abs_le] at hk1 ⊢; constructor <;> linarith
    have hb : |2 * c - (k : ℝ) ^ 2 - ((k : ℝ) - 1) ^ 2| ≤ 2 * c := by
      rw [abs_le]; constructor <;> nlinarith [sq_nonneg (k : ℝ), sq_nonneg ((k : ℝ) - 1)]
    calc |1 - 2 * (k : ℝ)| * |2 * c - (k : ℝ) ^ 2 - ((k : ℝ) - 1) ^ 2| ≤ (3 * ((h : ℝ) + 1)) * (2 * c) :=
          mul_le_mul ha hb (abs_nonneg _) (by positivity)
      _ = 6 * ((h : ℝ) + 1) ^ 3 := by simp only [c]; ring
  · -- one of the two points lies outside `|k| ≤ h + 1`; then both values vanish
    have hz : tau h k = 0 ∧ tau h (k - 1) = 0 := by
      rcases not_and_or.1 hk with h1 | h1
      · push_neg at h1
        refine ⟨tau_out h1, tau_supp ?_⟩
        rcases abs_cases k with ⟨e1, _⟩ | ⟨e1, _⟩
        · rw [e1] at h1; rw [abs_of_nonneg (by omega)]; omega
        · rw [e1] at h1; rw [abs_of_neg (by omega)]; omega
      · push_neg at h1
        refine ⟨tau_supp ?_, tau_out h1⟩
        rcases abs_cases (k - 1) with ⟨e1, _⟩ | ⟨e1, _⟩
        · rw [e1] at h1; rw [abs_of_nonneg (by omega)]; omega
        · rw [e1] at h1; rw [lt_abs]; omega
    rw [hz.1, hz.2, sub_self, abs_zero]; positivity

/-- The mass of the bump. -/
def mass (h : ℕ) : ℝ := ∑ k ∈ Finset.Icc (-(h : ℤ)) h, tau h k

lemma mass_pos (h : ℕ) : 0 < mass h :=
  lt_of_lt_of_le (by positivity) (tau_sum h)

/-- **The rising profile** `G(u) = m⁻¹Σ_{|k| ≤ h, k + c₀ < u}τ_h(k)`, `c₀ = D + h + 1`. -/
def G (h D : ℕ) (u : ℤ) : ℝ :=
  (∑ k ∈ Finset.Icc (-(h : ℤ)) h, if k + ((D + h + 1 : ℕ) : ℤ) < u then tau h k else 0) / mass h

lemma G_succ (h D : ℕ) (u : ℤ) : G h D (u + 1) - G h D u = tau h (u - ((D + h + 1 : ℕ) : ℤ)) / mass h := by
  unfold G
  rw [← sub_div]
  congr 1
  rw [← sum_sub_distrib]
  have e : ∀ k ∈ Finset.Icc (-(h : ℤ)) h, ((if k + ((D + h + 1 : ℕ) : ℤ) < u + 1 then tau h k else 0) -
      (if k + ((D + h + 1 : ℕ) : ℤ) < u then tau h k else 0)) =
      if k = u - ((D + h + 1 : ℕ) : ℤ) then tau h k else 0 := by
    intro k _
    by_cases h1 : k = u - ((D + h + 1 : ℕ) : ℤ)
    · rw [if_pos h1, if_pos (by omega), if_neg (by omega), sub_zero]
    · rw [if_neg h1]
      by_cases h2 : k + ((D + h + 1 : ℕ) : ℤ) < u
      · rw [if_pos h2, if_pos (by omega), sub_self]
      · rw [if_neg h2, if_neg (by omega), sub_self]
  rw [sum_congr rfl e, sum_ite_eq']
  split_ifs with hm
  · rfl
  · rw [tau_supp]
    simp only [Finset.mem_Icc, not_and_or, not_le] at hm
    rw [lt_abs]; omega

lemma G_nonneg (h D : ℕ) (u : ℤ) : 0 ≤ G h D u := by
  unfold G
  exact div_nonneg (sum_nonneg fun k _ => by split_ifs <;> simp [tau_nonneg]) (mass_pos h).le

lemma G_le_one (h D : ℕ) (u : ℤ) : G h D u ≤ 1 := by
  unfold G
  rw [div_le_one (mass_pos h)]
  exact sum_le_sum fun k _ => by split_ifs <;> simp [tau_nonneg]

lemma G_low (h D : ℕ) {u : ℤ} (hu : u ≤ D + 1) : G h D u = 0 := by
  unfold G
  rw [sum_eq_zero fun k hk => by rw [if_neg (by rw [Finset.mem_Icc] at hk; push_cast; omega)], zero_div]

lemma G_high (h D : ℕ) {u : ℤ} (hu : (D + 2 * h + 2 : ℤ) ≤ u) : G h D u = 1 := by
  unfold G
  rw [sum_congr rfl fun k hk => by rw [if_pos (by rw [Finset.mem_Icc] at hk; push_cast; omega)]]
  exact div_self (mass_pos h).ne'

/-- **The cut-off in one variable**: `χ₁(t) = 1 - G(|t|)`. -/
def chi1 (h D : ℕ) (t : ℤ) : ℝ := 1 - G h D |t|

lemma chi1_mem (h D : ℕ) (t : ℤ) : 0 ≤ chi1 h D t ∧ chi1 h D t ≤ 1 := by
  unfold chi1; constructor <;> linarith [G_nonneg h D |t|, G_le_one h D |t|]

lemma chi1_one (h D : ℕ) {t : ℤ} (ht : |t| ≤ D + 1) : chi1 h D t = 1 := by
  unfold chi1; rw [G_low h D ht, sub_zero]

lemma chi1_zero (h D : ℕ) {t : ℤ} (ht : (D + 2 * h + 2 : ℤ) ≤ |t|) : chi1 h D t = 0 := by
  unfold chi1; rw [G_high h D ht, sub_self]

lemma tau_div_le (h : ℕ) (k : ℤ) : tau h k / mass h ≤ 16 / (9 * ((h : ℝ) + 1)) := by
  have hm := tau_sum h
  have hmp := mass_pos h
  have ht := tau_le h k
  rw [div_le_div_iff₀ hmp (by positivity)]
  have hc : (0 : ℝ) < (((h : ℝ) + 1) ^ 2) ^ 2 := by positivity
  unfold mass at hmp ⊢
  nlinarith

/-- **The first differences of `χ₁`.** -/
theorem chi1_first (h D : ℕ) (t : ℤ) : |chi1 h D (t + 1) - chi1 h D t| ≤ 16 / (9 * ((h : ℝ) + 1)) := by
  unfold chi1
  rcases le_or_gt 0 t with ht | ht
  · rw [abs_of_nonneg ht, abs_of_nonneg (by omega : (0 : ℤ) ≤ t + 1)]
    have := G_succ h D t
    rw [show 1 - G h D (t + 1) - (1 - G h D t) = -(G h D (t + 1) - G h D t) by ring, abs_neg, this,
      abs_of_nonneg (div_nonneg (tau_nonneg _ _) (mass_pos h).le)]
    exact tau_div_le h _
  · rw [abs_of_neg ht]
    have e : |t + 1| = -t - 1 := by rw [abs_of_nonpos (by omega)]; ring
    rw [e]
    have := G_succ h D (-t - 1)
    rw [show -t - 1 + 1 = -t by ring] at this
    rw [show 1 - G h D (-t - 1) - (1 - G h D (-t)) = G h D (-t) - G h D (-t - 1) by ring, this,
      abs_of_nonneg (div_nonneg (tau_nonneg _ _) (mass_pos h).le)]
    exact tau_div_le h _

lemma tau_diff_div_le (h : ℕ) (k : ℤ) : |tau h k - tau h (k - 1)| / mass h ≤ 32 / (3 * ((h : ℝ) + 1) ^ 2) := by
  have hm := tau_sum h
  have hmp := mass_pos h
  have ht := tau_first h k
  rw [div_le_div_iff₀ hmp (by positivity)]
  unfold mass at hmp ⊢
  have hh : (0 : ℝ) < (h : ℝ) + 1 := by positivity
  have h5 : 0 < ((h : ℝ) + 1) ^ 5 := by positivity
  nlinarith [abs_nonneg (tau h k - tau h (k - 1))]

/-- **The second differences of `χ₁`.** -/
theorem chi1_second (h D : ℕ) (t : ℤ) :
    |chi1 h D (t + 1) - 2 * chi1 h D t + chi1 h D (t - 1)| ≤ 32 / (3 * ((h : ℝ) + 1) ^ 2) := by
  have hpos : 0 ≤ 32 / (3 * ((h : ℝ) + 1) ^ 2) := by positivity
  unfold chi1
  rcases lt_trichotomy t 0 with ht | ht | ht
  · rw [abs_of_neg ht, abs_of_nonpos (by omega : t + 1 ≤ 0), abs_of_neg (by omega : t - 1 < 0)]
    have h1 := G_succ h D (-t)
    have h2 := G_succ h D (-t - 1)
    rw [show -t - 1 + 1 = -t by ring] at h2
    rw [show -(t + 1) = -t - 1 by ring, show -(t - 1) = -t + 1 by ring]
    rw [show 1 - G h D (-t - 1) - 2 * (1 - G h D (-t)) + (1 - G h D (-t + 1)) =
      -((G h D (-t + 1) - G h D (-t)) - (G h D (-t) - G h D (-t - 1))) by ring, h1, h2, abs_neg, ← sub_div,
      abs_div, abs_of_pos (mass_pos h)]
    have := tau_diff_div_le h (-t - ((D + h + 1 : ℕ) : ℤ))
    rw [show -t - ((D + h + 1 : ℕ) : ℤ) - 1 = -t - 1 - ((D + h + 1 : ℕ) : ℤ) by ring] at this
    exact this
  · subst ht
    simp only [zero_add, abs_one, abs_zero, zero_sub, abs_neg]
    rw [G_low h D (by omega), G_low h D (by omega)]
    simp only [sub_zero, mul_one]; norm_num; exact hpos
  · rw [abs_of_pos ht, abs_of_pos (by omega : 0 < t + 1), abs_of_nonneg (by omega : (0 : ℤ) ≤ t - 1)]
    have h1 := G_succ h D t
    have h2 := G_succ h D (t - 1)
    rw [show t - 1 + 1 = t by ring] at h2
    rw [show 1 - G h D (t + 1) - 2 * (1 - G h D t) + (1 - G h D (t - 1)) =
      -((G h D (t + 1) - G h D t) - (G h D t - G h D (t - 1))) by ring, h1, h2, abs_neg, ← sub_div,
      abs_div, abs_of_pos (mass_pos h)]
    have := tau_diff_div_le h (t - ((D + h + 1 : ℕ) : ℤ))
    rw [show t - ((D + h + 1 : ℕ) : ℤ) - 1 = t - 1 - ((D + h + 1 : ℕ) : ℤ) by ring] at this
    exact this

end SFBump
end CoreLean

end
