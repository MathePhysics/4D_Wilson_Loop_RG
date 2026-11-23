import GaussianBlockSpin.PowerCountingScaleSums

/-! **Orderings of the lines** (III (2.7)): every scale assignment `j : E → [0, k)` is nondecreasing along some
ordering `σ : Fin m ≃ E` of the lines (`Tuple.sort`), so a sum over all assignments of a nonnegative function is at
most the sum over the orderings of the sums over nondecreasing tuples (sum_le_sum_orderings). -/

namespace GaussianBlockSpin

open scoped ENNReal

variable {E : Type*} [Fintype E] [DecidableEq E]

omit [DecidableEq E] in
lemma exists_ordering_monotone (j : E → ℕ) : ∃ σ : Fin (Fintype.card E) ≃ E, Monotone (j ∘ σ) := by
  set e := Fintype.equivFin E
  set f : Fin (Fintype.card E) → ℕ := j ∘ e.symm
  refine ⟨(Tuple.sort f).trans e.symm, ?_⟩
  have := Tuple.monotone_sort f
  intro a b hab
  exact this hab

/-- **Sums over scale assignments by orderings.** -/
theorem sum_le_sum_orderings (F : (E → ℕ) → ℝ≥0∞) (k : ℕ) :
    ∑ j ∈ Fintype.piFinset (fun _ : E => Finset.range k), F j ≤
      ∑ σ : Fin (Fintype.card E) ≃ E, ∑ u ∈ monoSet (Fintype.card E) (k - 1), F (fun l => u (σ.symm l)) := by
  classical
  set S := Fintype.piFinset (fun _ : E => Finset.range k) with hS
  calc ∑ j ∈ S, F j ≤ ∑ j ∈ S, ∑ σ : Fin (Fintype.card E) ≃ E, (if Monotone (j ∘ σ) then F j else 0) := by
        refine Finset.sum_le_sum fun j _ => ?_
        obtain ⟨σ, hσ⟩ := exists_ordering_monotone j
        calc F j = (if Monotone (j ∘ σ) then F j else 0) := by simp [hσ]
          _ ≤ _ := Finset.single_le_sum (f := fun σ : Fin (Fintype.card E) ≃ E => if Monotone (j ∘ σ) then F j else 0)
                (fun _ _ => bot_le) (Finset.mem_univ σ)
    _ = ∑ σ : Fin (Fintype.card E) ≃ E, ∑ j ∈ S, (if Monotone (j ∘ σ) then F j else 0) := Finset.sum_comm
    _ ≤ _ := by
        refine Finset.sum_le_sum fun σ _ => ?_
        rw [← Finset.sum_filter]
        have hinj : Set.InjOn (fun j : E → ℕ => j ∘ σ) (S.filter fun j => Monotone (j ∘ σ) : Set (E → ℕ)) := by
          intro j₁ _ j₂ _ h
          funext l
          have := congrFun h (σ.symm l)
          simpa using this
        rw [← Finset.sum_image (g := fun j : E → ℕ => j ∘ σ) (f := fun u => F (fun l => u (σ.symm l))) hinj
          |>.trans (Finset.sum_congr rfl fun j _ => by simp)]
        · refine Finset.sum_le_sum_of_subset fun u hu => ?_
          obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hu
          obtain ⟨hjS, hmono⟩ := Finset.mem_filter.mp hj
          refine mem_monoSet.mpr ⟨fun i => ?_, hmono⟩
          have := (Fintype.mem_piFinset.mp hjS) (σ i)
          simp only [Finset.mem_range] at this
          simp only [Function.comp]
          omega

/-- A canonical ordering of the lines along which the scale assignment `j` is nondecreasing (the sort of `j`). -/
noncomputable def canonOrd (j : E → ℕ) : Fin (Fintype.card E) ≃ E :=
  (Tuple.sort (j ∘ (Fintype.equivFin E).symm)).trans (Fintype.equivFin E).symm

omit [DecidableEq E] in
lemma monotone_canonOrd (j : E → ℕ) : Monotone (j ∘ canonOrd j) := by
  have := Tuple.monotone_sort (j ∘ (Fintype.equivFin E).symm)
  intro a b hab
  exact this hab

/-- **The ordering decomposition (2.7)**: a sum over scale assignments is the sum over the orderings `σ` of the sums
over the disjoint sets `J(σ)` of the assignments with canonical ordering `σ`, all nondecreasing along `σ`
(monotone_of_mem_orderClass). -/
theorem sum_eq_sum_orderClass {M : Type*} [AddCommMonoid M] (F : (E → ℕ) → M) (S : Finset (E → ℕ)) :
    ∑ j ∈ S, F j = ∑ σ : Fin (Fintype.card E) ≃ E, ∑ j ∈ S.filter (fun j => canonOrd j = σ), F j :=
  (Finset.sum_fiberwise S canonOrd F).symm

lemma monotone_of_mem_orderClass {S : Finset (E → ℕ)} {σ : Fin (Fintype.card E) ≃ E} {j : E → ℕ}
    (hj : j ∈ S.filter (fun j => canonOrd j = σ)) : Monotone (j ∘ σ) := by
  classical
  obtain ⟨-, h⟩ := Finset.mem_filter.mp hj
  rw [← h]
  exact monotone_canonOrd j

end GaussianBlockSpin
