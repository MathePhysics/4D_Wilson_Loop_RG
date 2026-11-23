import Mathlib

/-! Ordered products of sums as sums over words, in a (noncommutative) ring: the expansion of products of operators
each split into pieces (for Bałaban I (3.44)-(3.47): words in the terms of `V_k`), and the sum over the words with at
least one letter from a given set (the R-terms of I L1244-L1250). -/

namespace GaussianBlockSpin

open Finset

variable {R : Type*}

/-- **Ordered products of sums are sums over words**: in a semiring (not necessarily commutative),
`(Σ_c f_0 c) (Σ_c f_1 c) ⋯ (Σ_c f_{n-1} c) = Σ_w f_0(w_0) f_1(w_1) ⋯ f_{n-1}(w_{n-1})`. -/
theorem prod_ofFn_sum [Semiring R] {ι : Type*} [Fintype ι] :
    ∀ (n : ℕ) (f : Fin n → ι → R),
      (List.ofFn fun i => ∑ c, f i c).prod = ∑ w : Fin n → ι, (List.ofFn fun i => f i (w i)).prod
  | 0, f => by simp
  | n + 1, f => by
    rw [List.ofFn_succ, List.prod_cons, prod_ofFn_sum n (fun i => f i.succ), Finset.sum_mul_sum,
      ← Fintype.sum_prod_type', ← (Fin.consEquiv fun _ : Fin (n + 1) => ι).sum_comp]
    refine Fintype.sum_congr _ _ fun p => ?_
    simp [List.ofFn_succ, Fin.consEquiv]

/-- A word product with a zero letter vanishes. -/
lemma prod_ofFn_ite_zero [Semiring R] {ι : Type*} {n : ℕ} (S : ι → Prop) [DecidablePred S]
    (f : Fin n → ι → R) (w : Fin n → ι) :
    (List.ofFn fun i => if S (w i) then 0 else f i (w i)).prod =
      if ∃ i, S (w i) then 0 else (List.ofFn fun i => f i (w i)).prod := by
  by_cases h : ∃ i, S (w i)
  · obtain ⟨i, hi⟩ := h
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨i, hi⟩)]
    exact List.prod_eq_zero (List.mem_ofFn.2 ⟨i, by simp [hi]⟩)
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h)]
    push Not at h
    congr 1
    exact List.ofFn_inj.2 (funext fun i => by simp [h i])

/-- **The words with at least one letter from `S`**: their sum is the full product minus the product of the sums
over the letters outside `S`. -/
theorem sum_words_exists [Ring R] {ι : Type*} [Fintype ι] (S : ι → Prop) [DecidablePred S] (n : ℕ)
    (f : Fin n → ι → R) :
    ∑ w ∈ univ.filter (fun w : Fin n → ι => ∃ i, S (w i)), (List.ofFn fun i => f i (w i)).prod =
      (List.ofFn fun i => ∑ c, f i c).prod - (List.ofFn fun i => ∑ c ∈ univ.filter (fun c => ¬ S c), f i c).prod := by
  have hP : (List.ofFn fun i => ∑ c ∈ univ.filter (fun c => ¬ S c), f i c).prod =
      ∑ w ∈ univ.filter (fun w : Fin n → ι => ¬ ∃ i, S (w i)), (List.ofFn fun i => f i (w i)).prod := by
    have h1 : (fun i => ∑ c ∈ univ.filter (fun c => ¬ S c), f i c) =
        fun i => ∑ c, if S c then 0 else f i c := by
      funext i
      rw [Finset.sum_filter]
      exact Finset.sum_congr rfl fun c _ => by by_cases hc : S c <;> simp [hc]
    rw [h1, prod_ofFn_sum n (fun i c => if S c then 0 else f i c), Finset.sum_filter]
    exact Finset.sum_congr rfl fun w _ => by
      rw [prod_ofFn_ite_zero S f w]
      by_cases h : ∃ i, S (w i) <;> simp [h]
  rw [hP, prod_ofFn_sum n f, ← Finset.sum_filter_add_sum_filter_not univ (fun w : Fin n → ι => ∃ i, S (w i))]
  abel

end GaussianBlockSpin
