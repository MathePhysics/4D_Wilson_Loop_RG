/-
The Poincaré inequality on a block, the step "A block" of the proof of `lem:sf-coercivity` of BALABAN_CORE.tex
(`542c68192a44`): on a box of `nᵈ` sites, `Σ_x ‖f(x) - m‖² ≤ n² Σ_b ‖f(b₊) - f(b₋)‖²`, with the mean `m` of `f` over the
box and the sum over the bonds with both ends in the box, for `f` with values in a real inner product space (the
matrices with the Hilbert–Schmidt norm, through `flat`). The core states the constant `2n²` (paths through the corners,
`4n · n⁵/(2n⁴)`); the proof here gives `n²` by the induction on the dimension, which suffices for `eq:sf-coercivity`.

* `diff_sq_le`: on a line, `‖g(b) - g(a)‖² ≤ n Σ_i ‖g(i + 1) - g(i)‖²` (telescoping, Cauchy–Schwarz).
* `poincare1`: the inequality in one dimension, from `diff_sq_le` and `g(a) - ḡ = n⁻¹Σ_b(g(a) - g(b))`.
* `pyth`: `Σ_t ‖h(t) - m‖² = Σ_t ‖h(t) - h̄‖² + #T‖h̄ - m‖²`.
* `sum_box_succ`, `grad_succ`: the sums over the box and the bonds of the dimension `d + 1` through the first coordinate.
* `poincare`: the inequality in every dimension: the slices `t ↦ f(a, t)` by induction, their means `F(a)` by
  `poincare1`, and `nᵈ‖F(a + 1) - F(a)‖² ≤ Σ_t ‖f(a + 1, t) - f(a, t)‖²` by Cauchy–Schwarz.
* `poincare_split`, `block_ineq`: `Σ_x ‖f(x)‖² = Σ_x ‖f(x) - m‖² + nᵈ‖m‖²`, and the inequality of the step "A block",
  `Σ_x ‖f(x)‖² ≤ n²Σ_b ‖f(b₊) - f(b₋)‖² + nᵈ‖m‖²`.
-/
import Mathlib

open Finset

noncomputable section

namespace CoreLean
namespace DiscretePoincare

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `‖Σ_{i ∈ s} v_i‖² ≤ #s Σ_{i ∈ s} ‖v_i‖²`. -/
lemma norm_sum_sq_le {ι : Type*} (s : Finset ι) (v : ι → E) : ‖∑ i ∈ s, v i‖ ^ 2 ≤ s.card * ∑ i ∈ s, ‖v i‖ ^ 2 :=
  (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le s v) 2).trans sq_sum_le_card_mul_sum_sq

/-! ### One dimension -/

/-- The squared difference across the bond `(a, a + 1)` of `{0, …, n - 1}`, `0` if it leaves the interval. -/
def bterm (n : ℕ) (G : ℕ → E) (a : ℕ) : ℝ := if a + 1 < n then ‖G (a + 1) - G a‖ ^ 2 else 0

lemma bterm_nonneg (n : ℕ) (G : ℕ → E) (a : ℕ) : 0 ≤ bterm n G a := by
  unfold bterm; split_ifs <;> positivity

/-- `‖g(b) - g(a)‖² ≤ n Σ_i ‖g(i + 1) - g(i)‖²` for `a, b < n`. -/
lemma diff_sq_le {n : ℕ} (G : ℕ → E) {a b : ℕ} (ha : a < n) (hb : b < n) :
    ‖G b - G a‖ ^ 2 ≤ n * ∑ i ∈ range n, bterm n G i := by
  wlog hab : a ≤ b generalizing a b
  · rw [← norm_neg, neg_sub]
    exact this hb ha (by omega)
  have htel : G b - G a = ∑ i ∈ Ico a b, (G (i + 1) - G i) := by
    rw [Finset.sum_Ico_eq_sub _ hab, Finset.sum_range_sub, Finset.sum_range_sub]; abel
  rw [htel]
  have hcard : ((Ico a b).card : ℝ) ≤ n := by
    have : (Ico a b).card ≤ n := by simp; omega
    exact_mod_cast this
  calc ‖∑ i ∈ Ico a b, (G (i + 1) - G i)‖ ^ 2
      ≤ (Ico a b).card * ∑ i ∈ Ico a b, ‖G (i + 1) - G i‖ ^ 2 := norm_sum_sq_le _ _
    _ ≤ n * ∑ i ∈ range n, bterm n G i := by
        refine mul_le_mul hcard ?_ (sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
        calc ∑ i ∈ Ico a b, ‖G (i + 1) - G i‖ ^ 2 = ∑ i ∈ Ico a b, bterm n G i :=
              sum_congr rfl fun i hi => by
                rw [mem_Ico] at hi
                simp only [bterm, if_pos (show i + 1 < n by omega)]
          _ ≤ ∑ i ∈ range n, bterm n G i :=
              sum_le_sum_of_subset_of_nonneg (fun i hi => by rw [mem_Ico] at hi; rw [mem_range]; omega)
                fun i _ _ => bterm_nonneg n G i

/-- **The Poincaré inequality in one dimension**: `Σ_a ‖g(a) - ḡ‖² ≤ n² Σ_i ‖g(i + 1) - g(i)‖²`. -/
lemma poincare1 {n : ℕ} (hn : 0 < n) (G : ℕ → E) :
    ∑ a ∈ range n, ‖G a - (n : ℝ)⁻¹ • ∑ b ∈ range n, G b‖ ^ 2 ≤ (n : ℝ) ^ 2 * ∑ i ∈ range n, bterm n G i := by
  set S := ∑ i ∈ range n, bterm n G i
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have key : ∀ a ∈ range n, ‖G a - (n : ℝ)⁻¹ • ∑ b ∈ range n, G b‖ ^ 2 ≤ n * S := by
    intro a ha
    have e : G a - (n : ℝ)⁻¹ • ∑ b ∈ range n, G b = (n : ℝ)⁻¹ • ∑ b ∈ range n, (G a - G b) := by
      rw [sum_sub_distrib, sum_const, card_range, smul_sub, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
        inv_mul_cancel₀ hnr.ne', one_smul]
    rw [e, norm_smul, mul_pow, norm_inv, Real.norm_natCast]
    have h1 := norm_sum_sq_le (range n) (fun b => G a - G b)
    rw [card_range] at h1
    have h2 : ∑ b ∈ range n, ‖G a - G b‖ ^ 2 ≤ n * (n * S) := by
      calc ∑ b ∈ range n, ‖G a - G b‖ ^ 2 ≤ ∑ _b ∈ range n, (n : ℝ) * S := sum_le_sum fun b hb => by
            rw [← norm_neg, neg_sub]
            exact diff_sq_le G (mem_range.1 ha) (mem_range.1 hb)
        _ = n * (n * S) := by rw [sum_const, card_range, nsmul_eq_mul]
    rw [inv_pow, inv_mul_le_iff₀ (by positivity)]
    calc ‖∑ b ∈ range n, (G a - G b)‖ ^ 2 ≤ (n : ℝ) * ∑ b ∈ range n, ‖G a - G b‖ ^ 2 := h1
      _ ≤ n * (n * (n * S)) := mul_le_mul_of_nonneg_left h2 hnr.le
      _ = n ^ 2 * (n * S) := by ring
  calc ∑ a ∈ range n, ‖G a - (n : ℝ)⁻¹ • ∑ b ∈ range n, G b‖ ^ 2 ≤ ∑ _a ∈ range n, (n : ℝ) * S :=
        sum_le_sum key
    _ = (n : ℝ) ^ 2 * S := by rw [sum_const, card_range, nsmul_eq_mul]; ring

/-! ### The mean on a finite set -/

/-- `Σ_t ‖h(t) - m‖² = Σ_t ‖h(t) - h̄‖² + #T‖h̄ - m‖²`. -/
lemma pyth {ι : Type*} (T : Finset ι) (hT : 0 < T.card) (h : ι → E) (m : E) :
    ∑ t ∈ T, ‖h t - m‖ ^ 2 =
      ∑ t ∈ T, ‖h t - (T.card : ℝ)⁻¹ • ∑ s ∈ T, h s‖ ^ 2 +
        T.card * ‖(T.card : ℝ)⁻¹ • ∑ s ∈ T, h s - m‖ ^ 2 := by
  set F := (T.card : ℝ)⁻¹ • ∑ s ∈ T, h s
  have hc : (T.card : ℝ) ≠ 0 := by exact_mod_cast hT.ne'
  have hF : ∑ t ∈ T, (h t - F) = 0 := by
    rw [sum_sub_distrib, sum_const, ← Nat.cast_smul_eq_nsmul ℝ]
    simp only [F, smul_smul, mul_inv_cancel₀ hc, one_smul, sub_self]
  have e : ∀ t, ‖h t - m‖ ^ 2 = ‖h t - F‖ ^ 2 + 2 * inner ℝ (h t - F) (F - m) + ‖F - m‖ ^ 2 := fun t => by
    rw [show h t - m = (h t - F) + (F - m) by abel]
    exact norm_add_sq_real _ _
  simp only [e, sum_add_distrib, ← mul_sum, ← sum_inner, hF, inner_zero_left, mul_zero, add_zero, sum_const,
    nsmul_eq_mul]

/-- `#T‖(Σ_t d(t))/#T‖² ≤ Σ_t ‖d(t)‖²`, the mean squared. -/
lemma mean_sq_le {ι : Type*} (T : Finset ι) (hT : 0 < T.card) (d : ι → E) :
    (T.card : ℝ) * ‖(T.card : ℝ)⁻¹ • ∑ t ∈ T, d t‖ ^ 2 ≤ ∑ t ∈ T, ‖d t‖ ^ 2 := by
  have hc : (0 : ℝ) < T.card := by exact_mod_cast hT
  have h1 := norm_sum_sq_le T d
  rw [norm_smul, mul_pow, norm_inv, Real.norm_natCast, inv_pow, ← mul_assoc]
  calc (T.card : ℝ) * ((T.card : ℝ) ^ 2)⁻¹ * ‖∑ t ∈ T, d t‖ ^ 2
      ≤ (T.card : ℝ) * ((T.card : ℝ) ^ 2)⁻¹ * (T.card * ∑ t ∈ T, ‖d t‖ ^ 2) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = ∑ t ∈ T, ‖d t‖ ^ 2 := by field_simp

/-! ### Boxes -/

/-- The box `{0, …, n - 1}ᵈ`. -/
def box (d n : ℕ) : Finset (Fin d → ℕ) := Fintype.piFinset fun _ => range n

lemma card_box (d n : ℕ) : (box d n).card = n ^ d := by
  simp [box, Fintype.card_piFinset]

/-- The mean of `f` over the box. -/
def meanB (d n : ℕ) (f : (Fin d → ℕ) → E) : E := ((box d n).card : ℝ)⁻¹ • ∑ x ∈ box d n, f x

/-- `Σ_b ‖f(b₊) - f(b₋)‖²` over the bonds with both ends in the box. -/
def grad (d n : ℕ) (f : (Fin d → ℕ) → E) : ℝ :=
  ∑ μ : Fin d, ∑ x ∈ box d n, if x μ + 1 < n then ‖f (Function.update x μ (x μ + 1)) - f x‖ ^ 2 else 0

/-- The sum over the box of the dimension `d + 1` through the first coordinate. -/
lemma sum_box_succ {M : Type*} [AddCommMonoid M] (d n : ℕ) (F : (Fin (d + 1) → ℕ) → M) :
    ∑ x ∈ box (d + 1) n, F x = ∑ a ∈ range n, ∑ t ∈ box d n, F (Fin.cons a t) := by
  rw [← Finset.sum_product' (s := range n) (t := box d n) (f := fun a t => F (Fin.cons a t))]
  refine Finset.sum_nbij' (fun x => (x 0, Fin.tail x)) (fun p => Fin.cons p.1 p.2) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    simp only [box, Fintype.mem_piFinset, mem_coe] at hx
    simp only [mem_coe, mem_product, box, Fintype.mem_piFinset]
    exact ⟨hx 0, fun i => hx i.succ⟩
  · intro p hp
    simp only [mem_coe, mem_product, box, Fintype.mem_piFinset] at hp
    simp only [mem_coe, box, Fintype.mem_piFinset]
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using hp.1
    · simpa using hp.2 j
  · intro x _; simp
  · intro p _; simp
  · intro x _; simp

/-- The bonds of the box of the dimension `d + 1`: those of the first direction and those of the slices. -/
lemma grad_succ (d n : ℕ) (f : (Fin (d + 1) → ℕ) → E) :
    grad (d + 1) n f = ∑ a ∈ range n, ∑ t ∈ box d n, (if a + 1 < n then
      ‖f (Fin.cons (a + 1) t) - f (Fin.cons a t)‖ ^ 2 else 0) +
      ∑ a ∈ range n, grad d n (fun t => f (Fin.cons a t)) := by
  unfold grad
  rw [Fin.sum_univ_succ, sum_box_succ]
  congr 1
  · refine sum_congr rfl fun a _ => sum_congr rfl fun t _ => ?_
    simp only [Fin.cons_zero, Fin.update_cons_zero]
  · rw [Finset.sum_comm (s := range n) (t := (Finset.univ : Finset (Fin d)))]
    refine sum_congr rfl fun ν _ => ?_
    rw [sum_box_succ]
    refine sum_congr rfl fun a _ => sum_congr rfl fun t _ => ?_
    simp only [Fin.cons_succ, ← Fin.cons_update]

/-- **The Poincaré inequality on a box**: `Σ_x ‖f(x) - m‖² ≤ n² Σ_b ‖f(b₊) - f(b₋)‖²`. -/
theorem poincare {n : ℕ} (hn : 0 < n) :
    ∀ d (f : (Fin d → ℕ) → E), ∑ x ∈ box d n, ‖f x - meanB d n f‖ ^ 2 ≤ (n : ℝ) ^ 2 * grad d n f
  | 0, f => by
      have hb : box 0 n = {fun i => Fin.elim0 i} := by
        ext x; simp only [box, Fintype.mem_piFinset, mem_singleton]
        exact ⟨fun _ => funext fun i => Fin.elim0 i, fun _ i => Fin.elim0 i⟩
      simp [hb, meanB, grad]
  | d + 1, f => by
      have hcd : 0 < (box d n).card := by rw [card_box]; positivity
      have hnr : (0 : ℝ) < n := by exact_mod_cast hn
      set F : ℕ → E := fun a => meanB d n (fun t => f (Fin.cons a t))
      have hF : ∀ a, F a = ((box d n).card : ℝ)⁻¹ • ∑ t ∈ box d n, f (Fin.cons a t) := fun a => rfl
      have hm : meanB (d + 1) n f = (n : ℝ)⁻¹ • ∑ a ∈ range n, F a := by
        simp only [meanB, sum_box_succ, F, ← smul_sum, smul_smul, card_box]
        congr 1
        push_cast
        rw [pow_succ, mul_inv, mul_comm]
      -- the decomposition into the slices and their means
      have hdec : ∑ x ∈ box (d + 1) n, ‖f x - meanB (d + 1) n f‖ ^ 2 =
          ∑ a ∈ range n, (∑ t ∈ box d n, ‖f (Fin.cons a t) - F a‖ ^ 2 +
            (box d n).card * ‖F a - meanB (d + 1) n f‖ ^ 2) := by
        rw [sum_box_succ]
        refine sum_congr rfl fun a _ => ?_
        rw [pyth (box d n) hcd (fun t => f (Fin.cons a t)), ← hF]
      -- the slices
      have hslice : ∀ a, ∑ t ∈ box d n, ‖f (Fin.cons a t) - F a‖ ^ 2 ≤
          (n : ℝ) ^ 2 * grad d n (fun t => f (Fin.cons a t)) := fun a => poincare hn d _
      -- the means, by `poincare1`
      have hmean := poincare1 hn F
      rw [← hm] at hmean
      -- the differences of the means
      have hdiff : ∀ a ∈ range n, ((box d n).card : ℝ) * bterm n F a ≤
          ∑ t ∈ box d n, (if a + 1 < n then ‖f (Fin.cons (a + 1) t) - f (Fin.cons a t)‖ ^ 2 else 0) := by
        intro a _
        unfold bterm
        split_ifs with ha
        · have e : F (a + 1) - F a =
              ((box d n).card : ℝ)⁻¹ • ∑ t ∈ box d n, (f (Fin.cons (a + 1) t) - f (Fin.cons a t)) := by
            rw [hF, hF, sum_sub_distrib, smul_sub]
          rw [e]
          exact mean_sq_le (box d n) hcd _
        · simp
      rw [hdec, sum_add_distrib, grad_succ, mul_add]
      have hsum2 : ∑ a ∈ range n, ((box d n).card : ℝ) * ‖F a - meanB (d + 1) n f‖ ^ 2 ≤
          (n : ℝ) ^ 2 * ∑ a ∈ range n, ∑ t ∈ box d n,
            (if a + 1 < n then ‖f (Fin.cons (a + 1) t) - f (Fin.cons a t)‖ ^ 2 else 0) := by
        rw [← mul_sum]
        calc ((box d n).card : ℝ) * ∑ a ∈ range n, ‖F a - meanB (d + 1) n f‖ ^ 2
            ≤ (box d n).card * ((n : ℝ) ^ 2 * ∑ i ∈ range n, bterm n F i) :=
              mul_le_mul_of_nonneg_left hmean (by positivity)
          _ = (n : ℝ) ^ 2 * ∑ i ∈ range n, (box d n).card * bterm n F i := by
              rw [mul_sum, mul_sum, mul_sum]; exact sum_congr rfl fun i _ => by ring
          _ ≤ (n : ℝ) ^ 2 * ∑ a ∈ range n, ∑ t ∈ box d n,
                (if a + 1 < n then ‖f (Fin.cons (a + 1) t) - f (Fin.cons a t)‖ ^ 2 else 0) :=
              mul_le_mul_of_nonneg_left (sum_le_sum hdiff) (by positivity)
      have hsum1 : ∑ a ∈ range n, ∑ t ∈ box d n, ‖f (Fin.cons a t) - F a‖ ^ 2 ≤
          (n : ℝ) ^ 2 * ∑ a ∈ range n, grad d n (fun t => f (Fin.cons a t)) := by
        rw [mul_sum]; exact sum_le_sum fun a _ => hslice a
      linarith

/-- **The split used by the core**: `Σ_x ‖f(x)‖² = Σ_x ‖f(x) - m‖² + nᵈ‖m‖²`. -/
theorem poincare_split {n : ℕ} (hn : 0 < n) (d : ℕ) (f : (Fin d → ℕ) → E) :
    ∑ x ∈ box d n, ‖f x‖ ^ 2 = ∑ x ∈ box d n, ‖f x - meanB d n f‖ ^ 2 + (n : ℝ) ^ d * ‖meanB d n f‖ ^ 2 := by
  have hc : 0 < (box d n).card := by rw [card_box]; positivity
  have h := pyth (box d n) hc f 0
  simp only [sub_zero] at h
  rw [h]
  simp only [meanB, card_box]
  push_cast
  rfl

/-- **The inequality of the step "A block"**: `Σ_x ‖f(x)‖² ≤ n²Σ_b ‖f(b₊) - f(b₋)‖² + nᵈ‖m‖²`. -/
theorem block_ineq {n : ℕ} (hn : 0 < n) (d : ℕ) (f : (Fin d → ℕ) → E) :
    ∑ x ∈ box d n, ‖f x‖ ^ 2 ≤ (n : ℝ) ^ 2 * grad d n f + (n : ℝ) ^ d * ‖meanB d n f‖ ^ 2 := by
  rw [poincare_split hn]
  linarith [poincare hn d f]

end DiscretePoincare
end CoreLean

end
