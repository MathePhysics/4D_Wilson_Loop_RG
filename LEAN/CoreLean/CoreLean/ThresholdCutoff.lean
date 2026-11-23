/-
The bound of the difference of the cut-off factors in the proof of `lem:threshold-differences`(i) of BALABAN_CORE.tex
(`a021c13be348`). For a finite set `Y` of bonds (those of `Y₀`) and a disjoint finite set `P`, cut-offs
`χ', χ''` with values in `[0, 1]` which equal one where `|A(b)| ≤ r'`, and the factors
`𝔠 = ∏_{b ∈ Y}χ_b ∏_{b ∈ P}(1 - χ_b)`:
`|𝔠'' - 𝔠'| ≤ (N_Y + 1)e^{-γr'²/4}e^{(γ/2)Σ_{b ∈ Y ∪ P}|A(b)|²}e^{-(γ/4)r'²#P}` (`cutoff_difference`), for `γ ≥ 0`
(the core's `γ₂`). The proof is the core's: `|χ'' - χ'|` and `1 - χ` are at most `1[|A(b)| > r'] ≤
e^{(γ/2)(|A(b)|² - r'²)}`, the difference of the products over `Y` is at most the sum of the differences, and the
second difference is at most the larger of the two products over `P`.
-/
import Mathlib

open Finset Real

noncomputable section

namespace CoreLean
namespace Threshold

variable {β : Type*} [DecidableEq β]

/-- `|∏ a - ∏ b| ≤ Σ|a - b|` for factors in `[0, 1]`. -/
lemma abs_prod_sub_prod_le (s : Finset β) (a b : β → ℝ) (ha0 : ∀ i, 0 ≤ a i) (ha1 : ∀ i, a i ≤ 1)
    (hb0 : ∀ i, 0 ≤ b i) (hb1 : ∀ i, b i ≤ 1) :
    |∏ i ∈ s, a i - ∏ i ∈ s, b i| ≤ ∑ i ∈ s, |a i - b i| := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [prod_insert hj, prod_insert hj, sum_insert hj]
    have hA0 : 0 ≤ ∏ i ∈ s, a i := prod_nonneg fun i _ => ha0 i
    have hB1 : ∏ i ∈ s, b i ≤ 1 := prod_le_one₀ (fun i _ => hb0 i) fun i _ => hb1 i
    have hB0 : 0 ≤ ∏ i ∈ s, b i := prod_nonneg fun i _ => hb0 i
    have hA1 : ∏ i ∈ s, a i ≤ 1 := prod_le_one₀ (fun i _ => ha0 i) fun i _ => ha1 i
    have e : a j * ∏ i ∈ s, a i - b j * ∏ i ∈ s, b i =
        (a j - b j) * ∏ i ∈ s, a i + b j * (∏ i ∈ s, a i - ∏ i ∈ s, b i) := by ring
    rw [e]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_of_nonneg hA0]
      exact mul_le_of_le_one_right (abs_nonneg _) hA1
    · rw [abs_mul, abs_of_nonneg (hb0 j)]
      exact (mul_le_of_le_one_left (abs_nonneg _) (hb1 j)).trans ih

variable (x : β → ℝ) (r γ : ℝ)

/-- `e^{(γ/2)(|A(b)|² - r'²)}`. -/
def E (b : β) : ℝ := Real.exp (γ / 2 * (x b ^ 2 - r ^ 2))

variable {x r γ}

lemma one_sub_le {χ : β → ℝ} (hχ0 : ∀ b, 0 ≤ χ b) (hone : ∀ b, x b ≤ r → χ b = 1) (hr : 0 ≤ r) (hγ : 0 ≤ γ)
    (hx : ∀ b, 0 ≤ x b) (b : β) : 1 - χ b ≤ E x r γ b := by
  by_cases h : x b ≤ r
  · rw [hone b h, sub_self]; exact (Real.exp_pos _).le
  · push_neg at h
    have : r ^ 2 ≤ x b ^ 2 := by nlinarith
    have h1 : 1 ≤ E x r γ b := Real.one_le_exp (by nlinarith)
    linarith [hχ0 b]

lemma diff_le {χ₁ χ₂ : β → ℝ} (h10 : ∀ b, 0 ≤ χ₁ b) (h11 : ∀ b, χ₁ b ≤ 1) (h20 : ∀ b, 0 ≤ χ₂ b)
    (h21 : ∀ b, χ₂ b ≤ 1) (hone1 : ∀ b, x b ≤ r → χ₁ b = 1) (hone2 : ∀ b, x b ≤ r → χ₂ b = 1) (hr : 0 ≤ r)
    (hγ : 0 ≤ γ) (b : β) : |χ₂ b - χ₁ b| ≤ E x r γ b := by
  by_cases h : x b ≤ r
  · rw [hone1 b h, hone2 b h, sub_self, abs_zero]; exact (Real.exp_pos _).le
  · push_neg at h
    have : r ^ 2 ≤ x b ^ 2 := by nlinarith
    have h1 : 1 ≤ E x r γ b := Real.one_le_exp (by nlinarith)
    have : |χ₂ b - χ₁ b| ≤ 1 := abs_sub_le_iff.2 ⟨by linarith [h21 b, h10 b], by linarith [h11 b, h20 b]⟩
    linarith

lemma prod_E (s : Finset β) :
    ∏ b ∈ s, E x r γ b = Real.exp (γ / 2 * ∑ b ∈ s, x b ^ 2 - γ / 2 * r ^ 2 * s.card) := by
  unfold E
  rw [← Real.exp_sum]
  congr 1
  simp only [mul_sub, sum_sub_distrib, ← mul_sum, sum_const, nsmul_eq_mul]
  ring

/-- **The cut-off factors** (the proof of `lem:threshold-differences`(i)): with
`𝔠 = ∏_{b ∈ Y}χ_b ∏_{b ∈ P}(1 - χ_b)`, `|𝔠'' - 𝔠'| ≤ (N_Y + 1)e^{-γr'²/4}e^{(γ/2)Σ_{Y ∪ P}|A|²}e^{-(γ/4)r'²#P}`. -/
theorem cutoff_difference (Y P : Finset β) (hYP : Disjoint Y P) {χ₁ χ₂ : β → ℝ} (h10 : ∀ b, 0 ≤ χ₁ b)
    (h11 : ∀ b, χ₁ b ≤ 1) (h20 : ∀ b, 0 ≤ χ₂ b) (h21 : ∀ b, χ₂ b ≤ 1) (hone1 : ∀ b, x b ≤ r → χ₁ b = 1)
    (hone2 : ∀ b, x b ≤ r → χ₂ b = 1) (hr : 0 ≤ r) (hγ : 0 ≤ γ) (hx : ∀ b, 0 ≤ x b) :
    |(∏ b ∈ Y, χ₂ b) * ∏ b ∈ P, (1 - χ₂ b) - (∏ b ∈ Y, χ₁ b) * ∏ b ∈ P, (1 - χ₁ b)| ≤
      (Y.card + 1) * (Real.exp (-(γ * r ^ 2 / 4)) * Real.exp (γ / 2 * ∑ b ∈ Y ∪ P, x b ^ 2) *
        Real.exp (-(γ / 4 * r ^ 2 * P.card))) := by
  set B := Real.exp (-(γ * r ^ 2 / 4)) * Real.exp (γ / 2 * ∑ b ∈ Y ∪ P, x b ^ 2) *
    Real.exp (-(γ / 4 * r ^ 2 * P.card)) with hB
  have hB' : B = Real.exp (γ / 2 * ∑ b ∈ Y ∪ P, x b ^ 2 - γ * r ^ 2 / 4 - γ / 4 * r ^ 2 * P.card) := by
    rw [hB, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hsq : ∀ s ⊆ Y ∪ P, ∑ b ∈ s, x b ^ 2 ≤ ∑ b ∈ Y ∪ P, x b ^ 2 := fun s hs =>
    sum_le_sum_of_subset_of_nonneg hs fun _ _ _ => sq_nonneg _
  have hr2 : 0 ≤ γ * r ^ 2 := by positivity
  set a₂ := ∏ b ∈ P, (1 - χ₂ b)
  set a₁ := ∏ b ∈ P, (1 - χ₁ b)
  have ha₂0 : 0 ≤ a₂ := prod_nonneg fun b _ => by linarith [h21 b]
  have ha₁0 : 0 ≤ a₁ := prod_nonneg fun b _ => by linarith [h11 b]
  have ha₂E : a₂ ≤ ∏ b ∈ P, E x r γ b :=
    prod_le_prod₀ (fun b _ => by linarith [h21 b]) fun b _ => one_sub_le h20 hone2 hr hγ hx b
  have ha₁E : a₁ ≤ ∏ b ∈ P, E x r γ b :=
    prod_le_prod₀ (fun b _ => by linarith [h11 b]) fun b _ => one_sub_le h10 hone1 hr hγ hx b
  have e : (∏ b ∈ Y, χ₂ b) * a₂ - (∏ b ∈ Y, χ₁ b) * a₁ =
      ((∏ b ∈ Y, χ₂ b) - ∏ b ∈ Y, χ₁ b) * a₂ + (∏ b ∈ Y, χ₁ b) * (a₂ - a₁) := by ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  rw [add_mul, one_mul]
  refine add_le_add ?_ ?_
  · -- the first difference: `Σ_{b ∈ Y}E(b)∏_PE ≤ N_Y·B`
    rw [abs_mul, abs_of_nonneg ha₂0]
    have h1 := abs_prod_sub_prod_le Y χ₂ χ₁ h20 h21 h10 h11
    have h2 : ∀ b ∈ Y, |χ₂ b - χ₁ b| * a₂ ≤ B := by
      intro b hb
      have hbP : b ∉ P := Finset.disjoint_left.1 hYP hb
      calc |χ₂ b - χ₁ b| * a₂ ≤ E x r γ b * ∏ b ∈ P, E x r γ b :=
            mul_le_mul (diff_le h10 h11 h20 h21 hone1 hone2 hr hγ b) ha₂E ha₂0 (Real.exp_pos _).le
        _ = ∏ b ∈ insert b P, E x r γ b := (prod_insert hbP).symm
        _ = Real.exp (γ / 2 * ∑ b ∈ insert b P, x b ^ 2 - γ / 2 * r ^ 2 * (P.card + 1)) := by
            rw [prod_E, card_insert_of_notMem hbP]; push_cast; ring_nf
        _ ≤ B := by
            rw [hB']
            refine Real.exp_le_exp.2 ?_
            have := hsq (insert b P) (insert_subset (mem_union_left _ hb) subset_union_right)
            have hP : (0 : ℝ) ≤ P.card := by positivity
            nlinarith
    calc |∏ b ∈ Y, χ₂ b - ∏ b ∈ Y, χ₁ b| * a₂ ≤ (∑ b ∈ Y, |χ₂ b - χ₁ b|) * a₂ :=
          mul_le_mul_of_nonneg_right h1 ha₂0
      _ = ∑ b ∈ Y, |χ₂ b - χ₁ b| * a₂ := sum_mul _ _ _
      _ ≤ ∑ _b ∈ Y, B := sum_le_sum h2
      _ = Y.card * B := by rw [sum_const, nsmul_eq_mul]
  · -- the second difference: zero for `P = ∅`, else at most `∏_PE ≤ B`
    rw [abs_mul, abs_of_nonneg (prod_nonneg fun b _ => h10 b)]
    have hY1 : ∏ b ∈ Y, χ₁ b ≤ 1 := prod_le_one₀ (fun b _ => h10 b) fun b _ => h11 b
    rcases P.eq_empty_or_nonempty with hP | hP
    · have : a₂ - a₁ = 0 := by simp [a₂, a₁, hP]
      rw [this, abs_zero, mul_zero]; positivity
    have hd : |a₂ - a₁| ≤ ∏ b ∈ P, E x r γ b := abs_sub_le_iff.2 ⟨by linarith, by linarith⟩
    have hcard : (1 : ℝ) ≤ P.card := by exact_mod_cast hP.card_pos
    calc (∏ b ∈ Y, χ₁ b) * |a₂ - a₁| ≤ 1 * ∏ b ∈ P, E x r γ b :=
          mul_le_mul hY1 hd (abs_nonneg _) zero_le_one
      _ = Real.exp (γ / 2 * ∑ b ∈ P, x b ^ 2 - γ / 2 * r ^ 2 * P.card) := by rw [one_mul, prod_E]
      _ ≤ B := by
          rw [hB']
          refine Real.exp_le_exp.2 ?_
          have := hsq P subset_union_right
          nlinarith

lemma one_add_sum_le_prod {ι : Type*} [DecidableEq ι] (s : Finset ι) (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i) :
    1 + ∑ i ∈ s, c i ≤ ∏ i ∈ s, (1 + c i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [sum_insert hj, prod_insert hj]
    have h0 : 0 ≤ ∑ i ∈ s, c i := sum_nonneg fun i _ => hc i
    nlinarith [hc j]

/-- `N + 1 ≤ ∏_Y(1 + c_Y)` for `N ≤ Σ_Yc_Y`, `c_Y ≥ 0` (the count `N_{Y₀} + 1 ≤ ∏_Y(1 + 2¹²M⁴(1 + d_n(Y)))` of the
proof). -/
lemma one_add_le_prod {ι : Type*} [DecidableEq ι] (s : Finset ι) (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i) {N : ℝ}
    (hN : N ≤ ∑ i ∈ s, c i) : N + 1 ≤ ∏ i ∈ s, (1 + c i) := by
  have := one_add_sum_le_prod s c hc
  linarith

end Threshold
end CoreLean

end
