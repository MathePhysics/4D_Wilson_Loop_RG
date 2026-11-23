/-
The polymer sum as the core's sum over sequences, `eq:polymer-sum` of BALABAN_CORE.tex (`5bbe1bc62521`):
`Ξ = 1 + Σ_{m ≥ 1}(1/m!)Σ_{(Z_1, …, Z_m)}Π_{i<j}ζ(Z_i, Z_j)Π_iz(Z_i) = Σ_SΠ_{Z ∈ S}z(Z)` over the compatible sets `S`.
A sequence with all pairs compatible has distinct entries (`Z ≁ Z`), so it is an ordering of its set of entries, and
each set of `m` polymers has `m!` orderings.
-/
import CoreLean.ClusterRecursion
import CoreLean.ClusterDobrushin

open Finset

noncomputable section

namespace CoreLean
namespace TreeGraph

open Classical

variable {Q : Type*} [Fintype Q] {inc : Q → Q → Prop}

lemma mem_pairsIn' {ι : Type*} [Fintype ι] [DecidableEq ι] {B : Finset ι} {e : Sym2 ι} :
    e ∈ pairsIn B ↔ ¬e.IsDiag ∧ ∀ x ∈ e, x ∈ B := by
  unfold pairsIn; rw [Finset.mem_filter]; simp

/-- `Π_{i<j}ζ(Z_i, Z_j)` is `1` if all pairs are compatible and `0` otherwise. -/
lemma zetaS_eq_ite (hsymm : ∀ a b, inc a b → inc b a) {n : ℕ} (Z : Fin n → Q) :
    zetaS inc Z = if (∀ i j, i ≠ j → ¬inc (Z i) (Z j)) then 1 else 0 := by
  unfold zetaS
  rw [← Finset.prod_one_add]
  split_ifs with h
  · refine Finset.prod_eq_one fun e he => ?_
    unfold fp
    rw [if_neg, add_zero]
    rintro ⟨i, j, rfl, hij⟩
    have hd := (mem_pairsIn'.1 he).1
    rw [Sym2.mk_isDiag_iff] at hd
    exact h i j hd hij
  · push_neg at h
    obtain ⟨i, j, hij, hinc⟩ := h
    refine Finset.prod_eq_zero (i := s(i, j)) (mem_pairsIn'.2 ⟨by rw [Sym2.mk_isDiag_iff]; exact hij,
      fun _ _ => Finset.mem_univ _⟩) ?_
    · unfold fp
      rw [if_pos ⟨i, j, rfl, hinc⟩]; norm_num

/-- The injective sequences with the set of entries `S`, `#S = n`, are the `n!` bijections `Fin n ≃ S`. -/
lemma card_orderings {n : ℕ} (S : Finset Q) (hS : S.card = n) :
    ((Finset.univ : Finset (Fin n → Q)).filter (fun Z => Function.Injective Z ∧ Finset.univ.image Z = S)).card =
      n.factorial := by
  have e : {Z : Fin n → Q // Z ∈ (Finset.univ : Finset (Fin n → Q)).filter
      (fun Z => Function.Injective Z ∧ Finset.univ.image Z = S)} ≃ (Fin n ↪ S) :=
    { toFun := fun Z => ⟨fun i => ⟨Z.1 i, by
          have h := (Finset.mem_filter.1 Z.2).2.2
          have hm : Z.1 i ∈ Finset.univ.image Z.1 := Finset.mem_image_of_mem _ (Finset.mem_univ i)
          rwa [h] at hm⟩,
        fun i j hij => (Finset.mem_filter.1 Z.2).2.1 (congrArg Subtype.val hij)⟩
      invFun := fun f => ⟨fun i => f i, by
          refine Finset.mem_filter.2 ⟨Finset.mem_univ _, fun i j hij => f.injective (Subtype.ext hij), ?_⟩
          apply Finset.eq_of_subset_of_card_le
          · intro x hx
            obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
            exact (f i).2
          · rw [Finset.card_image_of_injective _ (fun i j hij => f.injective (Subtype.ext hij)),
              Finset.card_univ, Fintype.card_fin, hS]⟩
      left_inv := fun Z => rfl
      right_inv := fun f => rfl }
  rw [← Fintype.card_coe, Fintype.card_congr e, Fintype.card_embedding_eq, Fintype.card_fin,
    Fintype.card_coe, hS, Nat.descFactorial_self]

/-- **The sum over sequences is `m!` times the sum over sets**:
`Σ_{Z ∈ Q^m}Π_{i<j}ζ(Z_i, Z_j)Π_iz(Z_i) = m!Σ_{S compatible, #S = m}Π_{Z ∈ S}z(Z)`. -/
lemma En_eq_sets {R : Type*} [CommRing R] (hrefl : ∀ a, inc a a) (hsymm : ∀ a b, inc a b → inc b a)
    (z : Q → R) (n : ℕ) :
    En (inc := inc) z n = (n.factorial : R) *
      ∑ S ∈ (Finset.univ : Finset (Finset Q)).filter (fun S => Cluster.Compat inc S ∧ S.card = n), ∏ q ∈ S, z q := by
  unfold En Ei
  simp only [zetaS_eq_ite hsymm]
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ) (g := fun Z : Fin n → Q =>
    Finset.univ.image Z) (fun _ _ => Finset.mem_univ _)]
  rw [Finset.mul_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun S _ => ?_
  by_cases hS : Cluster.Compat inc S ∧ S.card = n
  · rw [if_pos hS]
    -- the nonzero terms are the orderings of `S`
    have hterm : ∀ Z ∈ (Finset.univ : Finset (Fin n → Q)).filter (fun Z => Finset.univ.image Z = S),
        ((if ∀ i j, i ≠ j → ¬inc (Z i) (Z j) then (1 : ℤ) else 0 : ℤ) : R) * ∏ i, z (Z i) =
          if Function.Injective Z then ∏ q ∈ S, z q else 0 := by
      intro Z hZ
      have hZS := (Finset.mem_filter.1 hZ).2
      by_cases hinj : Function.Injective Z
      · have hc : ∀ i j, i ≠ j → ¬inc (Z i) (Z j) := fun i j hij => by
          have hi : Z i ∈ S := hZS ▸ Finset.mem_image_of_mem _ (Finset.mem_univ i)
          have hj : Z j ∈ S := hZS ▸ Finset.mem_image_of_mem _ (Finset.mem_univ j)
          exact hS.1 _ hi _ hj (fun h => hij (hinj h))
        rw [if_pos hc, if_pos hinj, Int.cast_one, one_mul, ← hZS,
          Finset.prod_image (fun i _ j _ h => hinj h)]
      · have hnc : ¬∀ i j, i ≠ j → ¬inc (Z i) (Z j) := by
          intro hc; apply hinj; intro i j hij
          by_contra hne; exact hc i j hne (hij ▸ hrefl (Z i))
        rw [if_neg hnc, if_neg hinj]; simp
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, Finset.filter_filter]
    congr 1
    have := card_orderings S hS.2
    rw [← this]
    congr 2
    ext Z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact and_comm
  · rw [if_neg hS]
    refine Finset.sum_eq_zero fun Z hZ => ?_
    have hZS := (Finset.mem_filter.1 hZ).2
    rw [if_neg, Int.cast_zero, zero_mul]
    intro hc
    have hinj : Function.Injective Z := fun i j hij => by
      by_contra hne; exact hc i j hne (hij ▸ hrefl (Z i))
    apply hS
    refine ⟨fun a ha b hb hab => ?_, ?_⟩
    · rw [← hZS] at ha hb
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 ha
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hb
      exact hc i j (fun h => hab (h ▸ rfl))
    · rw [← hZS, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]

/-- **`eq:polymer-sum`**: the polymer sum over the compatible sets is the core's sum over sequences,
`Ξ = Σ_{m ≤ #Q}(1/m!)Σ_{Z ∈ Q^m}Π_{i<j}ζΠz`. -/
theorem Xi_eq_sequences (hrefl : ∀ a, inc a a) (hsymm : ∀ a b, inc a b → inc b a) (z : Q → ℂ) :
    Cluster.Xi inc Finset.univ z = ∑ m ∈ Finset.range (Fintype.card Q + 1),
      ((m.factorial : ℂ))⁻¹ * En (inc := inc) z m := by
  unfold Cluster.Xi
  simp only [En_eq_sets hrefl hsymm]
  have hfac : ∀ m : ℕ, ((m.factorial : ℂ))⁻¹ * ((m.factorial : ℂ) *
      ∑ S ∈ (Finset.univ : Finset (Finset Q)).filter (fun S => Cluster.Compat inc S ∧ S.card = m), ∏ q ∈ S, z q) =
        ∑ S ∈ (Finset.univ : Finset (Finset Q)).filter (fun S => Cluster.Compat inc S ∧ S.card = m),
          ∏ q ∈ S, z q := fun m => by
    rw [← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero m)), one_mul]
  simp only [hfac]
  rw [Finset.powerset_univ]
  rw [← Finset.sum_fiberwise_of_maps_to (s := (Finset.univ : Finset (Finset Q)).filter (Cluster.Compat inc))
    (t := Finset.range (Fintype.card Q + 1)) (g := Finset.card) (fun S _ => by
      simp only [Finset.mem_range]; exact Nat.lt_succ_of_le (Finset.card_le_univ S))]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.filter_filter]

end TreeGraph
end CoreLean

end
