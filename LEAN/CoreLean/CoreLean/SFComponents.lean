/-
`lem:sf-components` of BALABAN_CORE.tex (`aaaa938bb57d`), the step "The Poincaré inequality", on a box of `ℓ₀ × ℓ₁ × ℓ₂ × ℓ₃`
sites with values in a normed group (the core's `X_c`, `ℓ = (2n, n, n, n)`).

* `poincare1`: `Σ_{s,s' < ℓ}‖g(s) - g(s')‖² ≤ ℓ³Σ_{t+1 < ℓ}‖g(t + 1) - g(t)‖²`.
* `poincare4`: `Σ_{z,w ∈ X}‖F(z) - F(w)‖² ≤ 4(Πℓ)Σ_νℓ_ν²Σ_{bonds of direction ν}‖∂_νF‖²`, by the path which changes the
  coordinates in the order `0, 1, 2, 3` (in place of the core's count of the paths through a bond).
* `mean_le_pairs`, `mean_poincare`: with `boxMean`, the mean over the block `[0, n)⁴` of the means along the paths of
  `n` bonds in the direction `0` (the core's `Q` at the trivial configuration), `Σ_{z ∈ X}‖F(z) - QF‖² ≤ 32n²Σ_{b ⊂ X}‖∂F‖²`
  for `X = [0, 2n) × [0, n)³` (the core's constant is `160n²`).
* `local_components`: `n^{-2}Σ_D‖F‖² ≤ 64Σ_{b ⊂ X}‖∂F‖² + 2n²‖QF‖²` for a set `D ⊂ X` of `n⁴` sites (the core's `320`).
-/
import Mathlib

open Finset

noncomputable section

namespace CoreLean
namespace SFComponents

variable {E : Type*} [NormedAddCommGroup E]

/-- `‖g(s') - g(s)‖ ≤ Σ_{t+1<ℓ}‖g(t+1) - g(t)‖` for `s, s' < ℓ`. -/
lemma diff_le_tv (g : ℕ → E) {ℓ s s' : ℕ} (hs : s < ℓ) (hs' : s' < ℓ) :
    ‖g s' - g s‖ ≤ ∑ t ∈ range (ℓ - 1), ‖g (t + 1) - g t‖ := by
  wlog h : s ≤ s' generalizing s s'
  · rw [norm_sub_rev]; exact this hs' hs (by omega)
  have e : g s' - g s = ∑ t ∈ Ico s s', (g (t + 1) - g t) := by
    rw [Finset.sum_Ico_eq_sub _ h, Finset.sum_range_sub, Finset.sum_range_sub]; abel
  rw [e]
  refine (norm_sum_le _ _).trans (sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => norm_nonneg _)
  intro t ht
  rw [mem_Ico] at ht; rw [mem_range]; omega

/-- **The Poincaré inequality on an interval.** -/
lemma poincare1 (g : ℕ → E) (ℓ : ℕ) :
    ∑ s ∈ range ℓ, ∑ s' ∈ range ℓ, ‖g s - g s'‖ ^ 2 ≤
      (ℓ : ℝ) ^ 3 * ∑ t ∈ range (ℓ - 1), ‖g (t + 1) - g t‖ ^ 2 := by
  set T := ∑ t ∈ range (ℓ - 1), ‖g (t + 1) - g t‖
  have hT : T ^ 2 ≤ (ℓ : ℝ) * ∑ t ∈ range (ℓ - 1), ‖g (t + 1) - g t‖ ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := range (ℓ - 1)) (f := fun t => ‖g (t + 1) - g t‖)
    rw [card_range] at h
    refine h.trans (mul_le_mul_of_nonneg_right ?_ (sum_nonneg fun _ _ => sq_nonneg _))
    exact_mod_cast Nat.sub_le ℓ 1
  have hpt : ∀ s ∈ range ℓ, ∀ s' ∈ range ℓ, ‖g s - g s'‖ ^ 2 ≤ T ^ 2 := fun s hs s' hs' =>
    pow_le_pow_left₀ (norm_nonneg _) (diff_le_tv g (mem_range.1 hs') (mem_range.1 hs)) 2
  calc ∑ s ∈ range ℓ, ∑ s' ∈ range ℓ, ‖g s - g s'‖ ^ 2 ≤ ∑ _s ∈ range ℓ, ∑ _s' ∈ range ℓ, T ^ 2 :=
        sum_le_sum fun s hs => sum_le_sum fun s' hs' => hpt s hs s' hs'
    _ = (ℓ : ℝ) ^ 2 * T ^ 2 := by simp [sum_const, card_range]; ring
    _ ≤ (ℓ : ℝ) ^ 2 * ((ℓ : ℝ) * ∑ t ∈ range (ℓ - 1), ‖g (t + 1) - g t‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hT (by positivity)
    _ = _ := by ring

/-- `‖a + b + c + d‖² ≤ 4(‖a‖² + ‖b‖² + ‖c‖² + ‖d‖²)`. -/
lemma norm_add4_sq (a b c d : E) : ‖a + b + c + d‖ ^ 2 ≤ 4 * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2 + ‖d‖ ^ 2) := by
  have h : ‖a + b + c + d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by
    have h1 := norm_add_le (a + b + c) d
    have h2 := norm_add_le (a + b) c
    have h3 := norm_add_le a b
    linarith
  have h0 := norm_nonneg (a + b + c + d)
  have h1 := pow_le_pow_left₀ h0 h 2
  nlinarith [sq_nonneg (‖a‖ - ‖b‖), sq_nonneg (‖a‖ - ‖c‖), sq_nonneg (‖a‖ - ‖d‖), sq_nonneg (‖b‖ - ‖c‖),
    sq_nonneg (‖b‖ - ‖d‖), sq_nonneg (‖c‖ - ‖d‖)]

/-- The bonds of direction `ν` in the box, written as the four sums with the range `ℓ_ν - 1` in the place `ν`. -/
def bondSum (ℓ0 ℓ1 ℓ2 ℓ3 : ℕ) (F : ℕ → ℕ → ℕ → ℕ → E) : ℝ :=
  (ℓ0 : ℝ) ^ 2 * ∑ b ∈ range ℓ1, ∑ c ∈ range ℓ2, ∑ d ∈ range ℓ3, ∑ t ∈ range (ℓ0 - 1),
      ‖F (t + 1) b c d - F t b c d‖ ^ 2 +
    (ℓ1 : ℝ) ^ 2 * ∑ a ∈ range ℓ0, ∑ c ∈ range ℓ2, ∑ d ∈ range ℓ3, ∑ t ∈ range (ℓ1 - 1),
      ‖F a (t + 1) c d - F a t c d‖ ^ 2 +
    (ℓ2 : ℝ) ^ 2 * ∑ a ∈ range ℓ0, ∑ b ∈ range ℓ1, ∑ d ∈ range ℓ3, ∑ t ∈ range (ℓ2 - 1),
      ‖F a b (t + 1) d - F a b t d‖ ^ 2 +
    (ℓ3 : ℝ) ^ 2 * ∑ a ∈ range ℓ0, ∑ b ∈ range ℓ1, ∑ c ∈ range ℓ2, ∑ t ∈ range (ℓ3 - 1),
      ‖F a b c (t + 1) - F a b c t‖ ^ 2

lemma rearr1 (g : ℕ → ℕ → ℕ → ℕ → ℕ → ℝ) (s0 s1 s2 s3 : Finset ℕ) :
    ∑ b ∈ s1, ∑ c ∈ s2, ∑ d ∈ s3, ∑ a' ∈ s0, ∑ b' ∈ s1, g a' b c d b' =
      ∑ a' ∈ s0, ∑ c ∈ s2, ∑ d ∈ s3, ∑ b ∈ s1, ∑ b' ∈ s1, g a' b c d b' := by
  conv_lhs => arg 2; ext b; arg 2; ext c; rw [Finset.sum_comm]
  conv_lhs => arg 2; ext b; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => arg 2; ext a'; rw [Finset.sum_comm]
  conv_lhs => arg 2; ext a'; arg 2; ext c; rw [Finset.sum_comm]
lemma rearr2 (g : ℕ → ℕ → ℕ → ℕ → ℕ → ℝ) (s0 s1 s2 s3 : Finset ℕ) :
    ∑ c ∈ s2, ∑ d ∈ s3, ∑ a' ∈ s0, ∑ b' ∈ s1, ∑ c' ∈ s2, g a' b' c c' d =
      ∑ a' ∈ s0, ∑ b' ∈ s1, ∑ d ∈ s3, ∑ c ∈ s2, ∑ c' ∈ s2, g a' b' c c' d := by
  conv_lhs => arg 2; ext c; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => arg 2; ext a'; arg 2; ext c; rw [Finset.sum_comm]
  conv_lhs => arg 2; ext a'; rw [Finset.sum_comm]
  conv_lhs => arg 2; ext a'; arg 2; ext b'; rw [Finset.sum_comm]
lemma rearr3 (g : ℕ → ℕ → ℕ → ℕ → ℕ → ℝ) (s0 s1 s2 s3 : Finset ℕ) :
    ∑ d ∈ s3, ∑ a' ∈ s0, ∑ b' ∈ s1, ∑ c' ∈ s2, ∑ d' ∈ s3, g a' b' c' d d' =
      ∑ a' ∈ s0, ∑ b' ∈ s1, ∑ c' ∈ s2, ∑ d ∈ s3, ∑ d' ∈ s3, g a' b' c' d d' := by
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => arg 2; ext a'; rw [Finset.sum_comm]
  conv_lhs => arg 2; ext a'; arg 2; ext b'; rw [Finset.sum_comm]

/-- **The Poincaré inequality on a box.** -/
theorem poincare4 (ℓ0 ℓ1 ℓ2 ℓ3 : ℕ) (F : ℕ → ℕ → ℕ → ℕ → E) :
    ∑ a ∈ range ℓ0, ∑ b ∈ range ℓ1, ∑ c ∈ range ℓ2, ∑ d ∈ range ℓ3,
      ∑ a' ∈ range ℓ0, ∑ b' ∈ range ℓ1, ∑ c' ∈ range ℓ2, ∑ d' ∈ range ℓ3,
        ‖F a b c d - F a' b' c' d'‖ ^ 2 ≤
      4 * ((ℓ0 : ℝ) * ℓ1 * ℓ2 * ℓ3) * bondSum ℓ0 ℓ1 ℓ2 ℓ3 F := by
  -- the four differences along the path
  have hpt : ∀ a b c d a' b' c' d', ‖F a b c d - F a' b' c' d'‖ ^ 2 ≤
      4 * (‖F a b c d - F a' b c d‖ ^ 2 + ‖F a' b c d - F a' b' c d‖ ^ 2 + ‖F a' b' c d - F a' b' c' d‖ ^ 2 +
        ‖F a' b' c' d - F a' b' c' d'‖ ^ 2) := by
    intro a b c d a' b' c' d'
    have e : F a b c d - F a' b' c' d' = (F a b c d - F a' b c d) + (F a' b c d - F a' b' c d) +
        (F a' b' c d - F a' b' c' d) + (F a' b' c' d - F a' b' c' d') := by abel
    rw [e]; exact norm_add4_sq _ _ _ _
  set n0 := (ℓ0 : ℝ); set n1 := (ℓ1 : ℝ); set n2 := (ℓ2 : ℝ); set n3 := (ℓ3 : ℝ)
  -- the sum of each difference, by `poincare1` in its coordinate
  have h0 : ∑ a ∈ range ℓ0, ∑ b ∈ range ℓ1, ∑ c ∈ range ℓ2, ∑ d ∈ range ℓ3,
      ∑ a' ∈ range ℓ0, ∑ b' ∈ range ℓ1, ∑ c' ∈ range ℓ2, ∑ d' ∈ range ℓ3, ‖F a b c d - F a' b c d‖ ^ 2 ≤
      n1 * n2 * n3 * (n0 ^ 3 * ∑ b ∈ range ℓ1, ∑ c ∈ range ℓ2, ∑ d ∈ range ℓ3, ∑ t ∈ range (ℓ0 - 1),
        ‖F (t + 1) b c d - F t b c d‖ ^ 2) := by
    simp only [sum_const, card_range, nsmul_eq_mul]
    calc _ = n1 * n2 * n3 * ∑ b ∈ range ℓ1, ∑ c ∈ range ℓ2, ∑ d ∈ range ℓ3, ∑ a ∈ range ℓ0, ∑ a' ∈ range ℓ0,
          ‖F a b c d - F a' b c d‖ ^ 2 := by
          simp only [mul_sum]
          rw [Finset.sum_comm]
          refine sum_congr rfl fun b _ => ?_
          rw [Finset.sum_comm]
          refine sum_congr rfl fun c _ => ?_
          rw [Finset.sum_comm]
          refine sum_congr rfl fun d _ => sum_congr rfl fun a _ => sum_congr rfl fun a' _ => ?_
          ring
      _ ≤ n1 * n2 * n3 * ∑ b ∈ range ℓ1, ∑ c ∈ range ℓ2, ∑ d ∈ range ℓ3, n0 ^ 3 * ∑ t ∈ range (ℓ0 - 1),
          ‖F (t + 1) b c d - F t b c d‖ ^ 2 := by
          refine mul_le_mul_of_nonneg_left (sum_le_sum fun b _ => sum_le_sum fun c _ => sum_le_sum fun d _ =>
            poincare1 (fun s => F s b c d) ℓ0) (by positivity)
      _ = _ := by simp only [mul_sum]
  have h1 : ∑ a ∈ range ℓ0, ∑ b ∈ range ℓ1, ∑ c ∈ range ℓ2, ∑ d ∈ range ℓ3,
      ∑ a' ∈ range ℓ0, ∑ b' ∈ range ℓ1, ∑ c' ∈ range ℓ2, ∑ d' ∈ range ℓ3, ‖F a' b c d - F a' b' c d‖ ^ 2 ≤
      n0 * n2 * n3 * (n1 ^ 3 * ∑ a ∈ range ℓ0, ∑ c ∈ range ℓ2, ∑ d ∈ range ℓ3, ∑ t ∈ range (ℓ1 - 1),
        ‖F a (t + 1) c d - F a t c d‖ ^ 2) := by
    simp only [sum_const, card_range, nsmul_eq_mul, ← mul_sum]
    rw [rearr1 (fun a' b c d b' => ‖F a' b c d - F a' b' c d‖ ^ 2)]
    calc _ ≤ n0 * (n2 * (n3 * ∑ a ∈ range ℓ0, ∑ c ∈ range ℓ2, ∑ d ∈ range ℓ3, n1 ^ 3 *
          ∑ t ∈ range (ℓ1 - 1), ‖F a (t + 1) c d - F a t c d‖ ^ 2)) := by
          gcongr with a _ c _ d _
          exact poincare1 (fun s => F a s c d) ℓ1
      _ = _ := by simp only [← mul_sum]; ring
  have h2 : ∑ a ∈ range ℓ0, ∑ b ∈ range ℓ1, ∑ c ∈ range ℓ2, ∑ d ∈ range ℓ3,
      ∑ a' ∈ range ℓ0, ∑ b' ∈ range ℓ1, ∑ c' ∈ range ℓ2, ∑ d' ∈ range ℓ3, ‖F a' b' c d - F a' b' c' d‖ ^ 2 ≤
      n0 * n1 * n3 * (n2 ^ 3 * ∑ a ∈ range ℓ0, ∑ b ∈ range ℓ1, ∑ d ∈ range ℓ3, ∑ t ∈ range (ℓ2 - 1),
        ‖F a b (t + 1) d - F a b t d‖ ^ 2) := by
    simp only [sum_const, card_range, nsmul_eq_mul, ← mul_sum]
    rw [rearr2 (fun a' b' c c' d => ‖F a' b' c d - F a' b' c' d‖ ^ 2)]
    calc _ ≤ n0 * (n1 * (n3 * ∑ a ∈ range ℓ0, ∑ b ∈ range ℓ1, ∑ d ∈ range ℓ3, n2 ^ 3 *
          ∑ t ∈ range (ℓ2 - 1), ‖F a b (t + 1) d - F a b t d‖ ^ 2)) := by
          gcongr with a _ b _ d _
          exact poincare1 (fun s => F a b s d) ℓ2
      _ = _ := by simp only [← mul_sum]; ring
  have h3 : ∑ a ∈ range ℓ0, ∑ b ∈ range ℓ1, ∑ c ∈ range ℓ2, ∑ d ∈ range ℓ3,
      ∑ a' ∈ range ℓ0, ∑ b' ∈ range ℓ1, ∑ c' ∈ range ℓ2, ∑ d' ∈ range ℓ3, ‖F a' b' c' d - F a' b' c' d'‖ ^ 2 ≤
      n0 * n1 * n2 * (n3 ^ 3 * ∑ a ∈ range ℓ0, ∑ b ∈ range ℓ1, ∑ c ∈ range ℓ2, ∑ t ∈ range (ℓ3 - 1),
        ‖F a b c (t + 1) - F a b c t‖ ^ 2) := by
    simp only [sum_const, card_range, nsmul_eq_mul, ← mul_sum]
    rw [rearr3 (fun a' b' c' d d' => ‖F a' b' c' d - F a' b' c' d'‖ ^ 2)]
    calc _ ≤ n0 * (n1 * (n2 * ∑ a ∈ range ℓ0, ∑ b ∈ range ℓ1, ∑ c ∈ range ℓ2, n3 ^ 3 *
          ∑ t ∈ range (ℓ3 - 1), ‖F a b c (t + 1) - F a b c t‖ ^ 2)) := by
          gcongr with a _ b _ c _
          exact poincare1 (fun s => F a b c s) ℓ3
      _ = _ := by simp only [← mul_sum]; ring
  calc _ ≤ ∑ a ∈ range ℓ0, ∑ b ∈ range ℓ1, ∑ c ∈ range ℓ2, ∑ d ∈ range ℓ3,
        ∑ a' ∈ range ℓ0, ∑ b' ∈ range ℓ1, ∑ c' ∈ range ℓ2, ∑ d' ∈ range ℓ3,
          4 * (‖F a b c d - F a' b c d‖ ^ 2 + ‖F a' b c d - F a' b' c d‖ ^ 2 + ‖F a' b' c d - F a' b' c' d‖ ^ 2 +
            ‖F a' b' c' d - F a' b' c' d'‖ ^ 2) := by
        gcongr with a _ b _ c _ d _ a' _ b' _ c' _ d' _
        exact hpt a b c d a' b' c' d'
    _ = 4 * ((∑ a ∈ range ℓ0, ∑ b ∈ range ℓ1, ∑ c ∈ range ℓ2, ∑ d ∈ range ℓ3,
        ∑ a' ∈ range ℓ0, ∑ b' ∈ range ℓ1, ∑ c' ∈ range ℓ2, ∑ d' ∈ range ℓ3, ‖F a b c d - F a' b c d‖ ^ 2) +
        (∑ a ∈ range ℓ0, ∑ b ∈ range ℓ1, ∑ c ∈ range ℓ2, ∑ d ∈ range ℓ3,
        ∑ a' ∈ range ℓ0, ∑ b' ∈ range ℓ1, ∑ c' ∈ range ℓ2, ∑ d' ∈ range ℓ3, ‖F a' b c d - F a' b' c d‖ ^ 2) +
        (∑ a ∈ range ℓ0, ∑ b ∈ range ℓ1, ∑ c ∈ range ℓ2, ∑ d ∈ range ℓ3,
        ∑ a' ∈ range ℓ0, ∑ b' ∈ range ℓ1, ∑ c' ∈ range ℓ2, ∑ d' ∈ range ℓ3, ‖F a' b' c d - F a' b' c' d‖ ^ 2) +
        (∑ a ∈ range ℓ0, ∑ b ∈ range ℓ1, ∑ c ∈ range ℓ2, ∑ d ∈ range ℓ3,
        ∑ a' ∈ range ℓ0, ∑ b' ∈ range ℓ1, ∑ c' ∈ range ℓ2, ∑ d' ∈ range ℓ3, ‖F a' b' c' d - F a' b' c' d'‖ ^ 2)) := by
        simp only [Finset.mul_sum, Finset.sum_add_distrib, mul_add]
    _ ≤ 4 * (n1 * n2 * n3 * (n0 ^ 3 * ∑ b ∈ range ℓ1, ∑ c ∈ range ℓ2, ∑ d ∈ range ℓ3, ∑ t ∈ range (ℓ0 - 1),
          ‖F (t + 1) b c d - F t b c d‖ ^ 2) +
        n0 * n2 * n3 * (n1 ^ 3 * ∑ a ∈ range ℓ0, ∑ c ∈ range ℓ2, ∑ d ∈ range ℓ3, ∑ t ∈ range (ℓ1 - 1),
          ‖F a (t + 1) c d - F a t c d‖ ^ 2) +
        n0 * n1 * n3 * (n2 ^ 3 * ∑ a ∈ range ℓ0, ∑ b ∈ range ℓ1, ∑ d ∈ range ℓ3, ∑ t ∈ range (ℓ2 - 1),
          ‖F a b (t + 1) d - F a b t d‖ ^ 2) +
        n0 * n1 * n2 * (n3 ^ 3 * ∑ a ∈ range ℓ0, ∑ b ∈ range ℓ1, ∑ c ∈ range ℓ2, ∑ t ∈ range (ℓ3 - 1),
          ‖F a b c (t + 1) - F a b c t‖ ^ 2)) := by
        gcongr
    _ = _ := by unfold bondSum; ring

/-- `‖z - mean w‖² ≤ mean ‖z - w‖²`. -/
lemma sq_sub_mean_le [NormedSpace ℝ E] {ι : Type*} (S : Finset ι) (hS : S.Nonempty) (z : E) (w : ι → E) :
    ‖z - ((S.card : ℝ)⁻¹ • ∑ i ∈ S, w i)‖ ^ 2 ≤ (S.card : ℝ)⁻¹ * ∑ i ∈ S, ‖z - w i‖ ^ 2 := by
  have hc : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have e : z - ((S.card : ℝ)⁻¹ • ∑ i ∈ S, w i) = (S.card : ℝ)⁻¹ • ∑ i ∈ S, (z - w i) := by
    rw [sum_sub_distrib, sum_const, smul_sub, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hc.ne', one_smul]
  rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hc), mul_pow]
  have h1 : ‖∑ i ∈ S, (z - w i)‖ ^ 2 ≤ (S.card : ℝ) * ∑ i ∈ S, ‖z - w i‖ ^ 2 :=
    (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2).trans (sq_sum_le_card_mul_sum_sq)
  calc (S.card : ℝ)⁻¹ ^ 2 * ‖∑ i ∈ S, (z - w i)‖ ^ 2 ≤ (S.card : ℝ)⁻¹ ^ 2 * ((S.card : ℝ) * ∑ i ∈ S, ‖z - w i‖ ^ 2) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = _ := by field_simp

/-- `Σ_{a<n}Σ_{t<n}h(a + t) ≤ nΣ_{s<2n}h(s)` for `h ≥ 0`: each `s` is `a + t` for at most `n` pairs. -/
lemma sum_shift_le (h : ℕ → ℝ) (hh : ∀ s, 0 ≤ h s) (n : ℕ) :
    ∑ a ∈ range n, ∑ t ∈ range n, h (a + t) ≤ (n : ℝ) * ∑ s ∈ range (2 * n), h s := by
  rw [Finset.sum_comm]
  calc ∑ t ∈ range n, ∑ a ∈ range n, h (a + t) ≤ ∑ _t ∈ range n, ∑ s ∈ range (2 * n), h s := by
        refine sum_le_sum fun t ht => ?_
        have hm := Finset.sum_map (range n) (addRightEmbedding t) h
        simp only [addRightEmbedding_apply] at hm
        rw [← hm]
        refine sum_le_sum_of_subset_of_nonneg (fun s hs => ?_) fun s _ _ => hh s
        simp only [mem_map, mem_range, addRightEmbedding_apply] at hs ht ⊢
        obtain ⟨a, ha, rfl⟩ := hs; omega
    _ = _ := by simp [sum_const, card_range]

/-- The index set of the core's `Q` at the trivial configuration: the points `(a, b, c, d)` of the block `[0, n)⁴`
and the steps `t < n` along the path in the direction `0`. -/
def Iq (n : ℕ) : Finset (ℕ × ℕ × ℕ × ℕ × ℕ) := range n ×ˢ range n ×ˢ range n ×ˢ range n ×ˢ range n

lemma card_Iq (n : ℕ) : (Iq n).card = n ^ 5 := by simp [Iq, card_product]; ring

/-- `(QF)(c) = n⁻⁵Σ_{x ∈ B(c₋)}Σ_{t<n}F(x + te₀)` on the box `[0, 2n) × [0, n)³`. -/
def boxMean [NormedSpace ℝ E] (n : ℕ) (F : ℕ → ℕ → ℕ → ℕ → E) : E :=
  (((Iq n).card : ℕ) : ℝ)⁻¹ • ∑ i ∈ Iq n, F (i.1 + i.2.2.2.2) i.2.1 i.2.2.1 i.2.2.2.1

/-- **The Poincaré inequality for the mean**:
`Σ_{z ∈ X}‖F(z) - QF‖² ≤ n⁻⁴Σ_{z,w ∈ X}‖F(z) - F(w)‖²` for `X = [0, 2n) × [0, n)³`. -/
theorem mean_le_pairs [NormedSpace ℝ E] (n : ℕ) (hn : 1 ≤ n) (F : ℕ → ℕ → ℕ → ℕ → E) :
    ∑ a ∈ range (2 * n), ∑ b ∈ range n, ∑ c ∈ range n, ∑ d ∈ range n, ‖F a b c d - boxMean n F‖ ^ 2 ≤
      ((n : ℝ) ^ 4)⁻¹ * ∑ a ∈ range (2 * n), ∑ b ∈ range n, ∑ c ∈ range n, ∑ d ∈ range n,
        ∑ a' ∈ range (2 * n), ∑ b' ∈ range n, ∑ c' ∈ range n, ∑ d' ∈ range n, ‖F a b c d - F a' b' c' d'‖ ^ 2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hne : (Iq n).Nonempty := by
    rw [← card_pos, card_Iq]; positivity
  rw [mul_sum]
  refine sum_le_sum fun a _ => ?_
  rw [mul_sum]; refine sum_le_sum fun b _ => ?_
  rw [mul_sum]; refine sum_le_sum fun c _ => ?_
  rw [mul_sum]; refine sum_le_sum fun d _ => ?_
  refine (sq_sub_mean_le (Iq n) hne (F a b c d) _).trans ?_
  rw [card_Iq]
  set G : ℕ → ℕ → ℕ → ℕ → ℝ := fun a' b' c' d' => ‖F a b c d - F a' b' c' d'‖ ^ 2
  have hG : ∀ a' b' c' d', 0 ≤ G a' b' c' d' := fun _ _ _ _ => sq_nonneg _
  have e : ∑ i ∈ Iq n, ‖F a b c d - F (i.1 + i.2.2.2.2) i.2.1 i.2.2.1 i.2.2.2.1‖ ^ 2 =
      ∑ a' ∈ range n, ∑ b' ∈ range n, ∑ c' ∈ range n, ∑ d' ∈ range n, ∑ t ∈ range n, G (a' + t) b' c' d' := by
    simp only [Iq, sum_product, G]
  rw [e]
  set H : ℕ → ℝ := fun s => ∑ b' ∈ range n, ∑ c' ∈ range n, ∑ d' ∈ range n, G s b' c' d'
  have hH : ∀ s, 0 ≤ H s := fun s => sum_nonneg fun _ _ => sum_nonneg fun _ _ => sum_nonneg fun _ _ => hG _ _ _ _
  have e2 : ∀ a', ∑ b' ∈ range n, ∑ c' ∈ range n, ∑ d' ∈ range n, ∑ t ∈ range n, G (a' + t) b' c' d' =
      ∑ t ∈ range n, H (a' + t) := fun a' => by
    simp only [H]
    conv_lhs => arg 2; ext b'; arg 2; ext c'; rw [Finset.sum_comm]
    conv_lhs => arg 2; ext b'; rw [Finset.sum_comm]
    conv_lhs => rw [Finset.sum_comm]
  simp only [e2]
  have h3 := sum_shift_le H hH n
  have e3 : ∑ a' ∈ range (2 * n), ∑ b' ∈ range n, ∑ c' ∈ range n, ∑ d' ∈ range n,
      ‖F a b c d - F a' b' c' d'‖ ^ 2 = ∑ s ∈ range (2 * n), H s := rfl
  rw [e3]
  calc ((n ^ 5 : ℕ) : ℝ)⁻¹ * ∑ a' ∈ range n, ∑ t ∈ range n, H (a' + t)
      ≤ ((n ^ 5 : ℕ) : ℝ)⁻¹ * ((n : ℝ) * ∑ s ∈ range (2 * n), H s) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = _ := by push_cast; field_simp

/-- The sum of `‖∂F‖²` over the bonds of the box `ℓ₀ × ℓ₁ × ℓ₂ × ℓ₃`, without weights. -/
def bondsAll (ℓ0 ℓ1 ℓ2 ℓ3 : ℕ) (F : ℕ → ℕ → ℕ → ℕ → E) : ℝ :=
  ∑ b ∈ range ℓ1, ∑ c ∈ range ℓ2, ∑ d ∈ range ℓ3, ∑ t ∈ range (ℓ0 - 1), ‖F (t + 1) b c d - F t b c d‖ ^ 2 +
    ∑ a ∈ range ℓ0, ∑ c ∈ range ℓ2, ∑ d ∈ range ℓ3, ∑ t ∈ range (ℓ1 - 1), ‖F a (t + 1) c d - F a t c d‖ ^ 2 +
    ∑ a ∈ range ℓ0, ∑ b ∈ range ℓ1, ∑ d ∈ range ℓ3, ∑ t ∈ range (ℓ2 - 1), ‖F a b (t + 1) d - F a b t d‖ ^ 2 +
    ∑ a ∈ range ℓ0, ∑ b ∈ range ℓ1, ∑ c ∈ range ℓ2, ∑ t ∈ range (ℓ3 - 1), ‖F a b c (t + 1) - F a b c t‖ ^ 2

/-- **The Poincaré inequality for the mean**: `Σ_{z ∈ X}‖F(z) - QF‖² ≤ 32n²Σ_{b ⊂ X}‖∂F(b)‖²`,
`X = [0, 2n) × [0, n)³` (the core's `160a_j²`). -/
theorem mean_poincare [NormedSpace ℝ E] (n : ℕ) (hn : 1 ≤ n) (F : ℕ → ℕ → ℕ → ℕ → E) :
    ∑ a ∈ range (2 * n), ∑ b ∈ range n, ∑ c ∈ range n, ∑ d ∈ range n, ‖F a b c d - boxMean n F‖ ^ 2 ≤
      32 * (n : ℝ) ^ 2 * bondsAll (2 * n) n n n F := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  refine (mean_le_pairs n hn F).trans ?_
  have h4 := poincare4 (2 * n) n n n F
  have hB : bondSum (2 * n) n n n F ≤ 4 * (n : ℝ) ^ 2 * bondsAll (2 * n) n n n F := by
    unfold bondSum bondsAll
    have q1 : 0 ≤ ∑ a ∈ range (2 * n), ∑ c ∈ range n, ∑ d ∈ range n, ∑ t ∈ range (n - 1),
        ‖F a (t + 1) c d - F a t c d‖ ^ 2 := by positivity
    have q2 : 0 ≤ ∑ a ∈ range (2 * n), ∑ b ∈ range n, ∑ d ∈ range n, ∑ t ∈ range (n - 1),
        ‖F a b (t + 1) d - F a b t d‖ ^ 2 := by positivity
    have q3 : 0 ≤ ∑ a ∈ range (2 * n), ∑ b ∈ range n, ∑ c ∈ range n, ∑ t ∈ range (n - 1),
        ‖F a b c (t + 1) - F a b c t‖ ^ 2 := by positivity
    have e2 : ((2 * n : ℕ) : ℝ) ^ 2 = 4 * (n : ℝ) ^ 2 := by push_cast; ring
    rw [e2]
    have hn2 : 0 ≤ (n : ℝ) ^ 2 := by positivity
    nlinarith [mul_nonneg hn2 q1, mul_nonneg hn2 q2, mul_nonneg hn2 q3]
  calc ((n : ℝ) ^ 4)⁻¹ * _ ≤ ((n : ℝ) ^ 4)⁻¹ * (4 * (((2 * n : ℕ) : ℝ) * n * n * n) * bondSum (2 * n) n n n F) :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
    _ ≤ ((n : ℝ) ^ 4)⁻¹ * (4 * (((2 * n : ℕ) : ℝ) * n * n * n) * (4 * (n : ℝ) ^ 2 * bondsAll (2 * n) n n n F)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hB (by positivity)) (by positivity)
    _ = _ := by push_cast; field_simp; ring

/-- The box `[0, 2n) × [0, n)³` as a `Finset` of quadruples. -/
def boxQ (n : ℕ) : Finset (ℕ × ℕ × ℕ × ℕ) := range (2 * n) ×ˢ range n ×ˢ range n ×ˢ range n

/-- **The local bound** (the core's `a_j^{-2}Σ_{Δ(y)}|A_μ|² ≤ 320Σ_{b ⊂ X_c}|∂A_μ|² + 2a_j²|(QA)(c)|²`, here with `64`):
for a set `D` of `n⁴` sites of the box, `n^{-2}Σ_D‖F‖² ≤ 64Σ_{b ⊂ X}‖∂F(b)‖² + 2n²‖QF‖²`. -/
theorem local_components [NormedSpace ℝ E] (n : ℕ) (hn : 1 ≤ n) (F : ℕ → ℕ → ℕ → ℕ → E)
    (D : Finset (ℕ × ℕ × ℕ × ℕ)) (hD : D ⊆ boxQ n) (hcard : D.card = n ^ 4) :
    ((n : ℝ) ^ 2)⁻¹ * ∑ p ∈ D, ‖F p.1 p.2.1 p.2.2.1 p.2.2.2‖ ^ 2 ≤
      64 * bondsAll (2 * n) n n n F + 2 * (n : ℝ) ^ 2 * ‖boxMean n F‖ ^ 2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set m := boxMean n F
  have hpt : ∀ p ∈ D, ‖F p.1 p.2.1 p.2.2.1 p.2.2.2‖ ^ 2 ≤ 2 * ‖F p.1 p.2.1 p.2.2.1 p.2.2.2 - m‖ ^ 2 + 2 * ‖m‖ ^ 2 := by
    intro p _
    have e : F p.1 p.2.1 p.2.2.1 p.2.2.2 = (F p.1 p.2.1 p.2.2.1 p.2.2.2 - m) + m := by abel
    have h := norm_add_le (F p.1 p.2.1 p.2.2.1 p.2.2.2 - m) m
    rw [← e] at h
    have h0 := norm_nonneg (F p.1 p.2.1 p.2.2.1 p.2.2.2)
    nlinarith [sq_nonneg (‖F p.1 p.2.1 p.2.2.1 p.2.2.2 - m‖ - ‖m‖), norm_nonneg (F p.1 p.2.1 p.2.2.1 p.2.2.2 - m),
      norm_nonneg m]
  have hsub : ∑ p ∈ D, ‖F p.1 p.2.1 p.2.2.1 p.2.2.2 - m‖ ^ 2 ≤
      ∑ a ∈ range (2 * n), ∑ b ∈ range n, ∑ c ∈ range n, ∑ d ∈ range n, ‖F a b c d - m‖ ^ 2 := by
    refine (sum_le_sum_of_subset_of_nonneg hD fun _ _ _ => sq_nonneg _).trans (le_of_eq ?_)
    simp only [boxQ, sum_product]
  have hmp := mean_poincare n hn F
  have hsum : ∑ p ∈ D, ‖F p.1 p.2.1 p.2.2.1 p.2.2.2‖ ^ 2 ≤
      2 * (32 * (n : ℝ) ^ 2 * bondsAll (2 * n) n n n F) + 2 * (n : ℝ) ^ 4 * ‖m‖ ^ 2 := by
    calc ∑ p ∈ D, ‖F p.1 p.2.1 p.2.2.1 p.2.2.2‖ ^ 2
        ≤ ∑ p ∈ D, (2 * ‖F p.1 p.2.1 p.2.2.1 p.2.2.2 - m‖ ^ 2 + 2 * ‖m‖ ^ 2) := sum_le_sum hpt
      _ = 2 * ∑ p ∈ D, ‖F p.1 p.2.1 p.2.2.1 p.2.2.2 - m‖ ^ 2 + 2 * (n : ℝ) ^ 4 * ‖m‖ ^ 2 := by
          rw [sum_add_distrib, ← mul_sum, sum_const, hcard, nsmul_eq_mul]; push_cast; ring
      _ ≤ _ := by gcongr; exact hsub.trans hmp
  rw [inv_mul_le_iff₀ (by positivity)]
  nlinarith [hsum]

end SFComponents
end CoreLean

end
