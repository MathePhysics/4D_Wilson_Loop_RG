import GaussianBlockSpin.Wick

/-! Perfect matchings of a finite set of legs as fixed-point-free involutions, and the closed form of the pairing
sum of Wick: `W(s) = Σ_{σ perfect matching of s} ∏_{i ∈ s, i < σ i} ⟪w_i, C w_{σ i}⟫` for symmetric `C`
(wickSum_eq_sum_matchings). With gaussMoment_eq_wickSum this is Isserlis' theorem as a sum over pairings. -/

open scoped RealInnerProductSpace

namespace GaussianBlockSpin

variable {m : ℕ}

/-- `σ` is a perfect matching of `s`: it fixes every leg outside `s` and is a fixed-point-free involution of `s`. -/
def IsMatching (s : Finset (Fin m)) (σ : Equiv.Perm (Fin m)) : Prop :=
  (∀ i, i ∉ s → σ i = i) ∧ ∀ i ∈ s, σ i ∈ s ∧ σ i ≠ i ∧ σ (σ i) = i

instance (s : Finset (Fin m)) (σ : Equiv.Perm (Fin m)) : Decidable (IsMatching s σ) := by
  unfold IsMatching; infer_instance

/-- The perfect matchings of `s`. -/
def matchings (s : Finset (Fin m)) : Finset (Equiv.Perm (Fin m)) :=
  Finset.univ.filter (IsMatching s)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The weight `∏_{i ∈ s, i < σ i} ⟪w_i, C w_{σ i}⟫` of a matching (each pair counted once). -/
noncomputable def matchingWeight (C : E →ₗ[ℝ] E) (w : Fin m → E) (s : Finset (Fin m)) (σ : Equiv.Perm (Fin m)) : ℝ :=
  ∏ i ∈ s.filter (fun i => i < σ i), ⟪w i, C (w (σ i))⟫

lemma isMatching_empty_iff (σ : Equiv.Perm (Fin m)) : IsMatching ∅ σ ↔ σ = 1 := by
  constructor
  · intro h
    ext i
    simp [h.1 i (Finset.notMem_empty i)]
  · rintro rfl
    exact ⟨fun _ _ => rfl, fun i hi => absurd hi (Finset.notMem_empty i)⟩

lemma matchings_empty : matchings (∅ : Finset (Fin m)) = {1} := by
  ext σ
  simp [matchings, isMatching_empty_iff]

/-- Removing the pair `{a, σ a}`: `σ * swap a (σ a)` is a perfect matching of `s \ {a, σ a}`. -/
lemma isMatching_mul_swap {s : Finset (Fin m)} {σ : Equiv.Perm (Fin m)} (hσ : IsMatching s σ) {a : Fin m}
    (ha : a ∈ s) : IsMatching ((s.erase a).erase (σ a)) (σ * Equiv.swap a (σ a)) := by
  obtain ⟨hout, hin⟩ := hσ
  obtain ⟨hja, hjne, hjj⟩ := hin a ha
  constructor
  · intro i hi
    simp only [Equiv.Perm.mul_apply]
    by_cases hia : i = a
    · subst hia; rw [Equiv.swap_apply_left, hjj]
    by_cases hij : i = σ a
    · subst hij; rw [Equiv.swap_apply_right]
    rw [Equiv.swap_apply_of_ne_of_ne hia hij]
    have : i ∉ s := by
      intro his
      exact hi (Finset.mem_erase.mpr ⟨hij, Finset.mem_erase.mpr ⟨hia, his⟩⟩)
    exact hout i this
  · intro i hi
    have hij : i ≠ σ a := (Finset.mem_erase.mp hi).1
    have hia : i ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
    have his : i ∈ s := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).2
    simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hia hij]
    obtain ⟨h1, h2, h3⟩ := hin i his
    have hσia : σ i ≠ a := by
      intro h
      apply hij
      rw [← h, h3]
    have hσij : σ i ≠ σ a := fun h => hia (σ.injective h)
    refine ⟨Finset.mem_erase.mpr ⟨hσij, Finset.mem_erase.mpr ⟨hσia, h1⟩⟩, h2, ?_⟩
    rw [Equiv.swap_apply_of_ne_of_ne hσia hσij, h3]

/-- Adding the pair `{a, j}`: if `τ` is a perfect matching of `s \ {a, j}` (`a ∈ s`, `j ∈ s \ a`), then
`τ * swap a j` is a perfect matching of `s` sending `a` to `j`. -/
lemma isMatching_mul_swap_of {s : Finset (Fin m)} {a j : Fin m} (ha : a ∈ s) (hj : j ∈ s.erase a)
    {τ : Equiv.Perm (Fin m)} (hτ : IsMatching ((s.erase a).erase j) τ) :
    IsMatching s (τ * Equiv.swap a j) ∧ (τ * Equiv.swap a j) a = j := by
  obtain ⟨hout, hin⟩ := hτ
  have hja : j ≠ a := (Finset.mem_erase.mp hj).1
  have hjs : j ∈ s := (Finset.mem_erase.mp hj).2
  have hτa : τ a = a := hout a (fun h => (Finset.mem_erase.mp (Finset.mem_erase.mp h).2).1 rfl)
  have hτj : τ j = j := hout j (fun h => (Finset.mem_erase.mp h).1 rfl)
  have hsa : (τ * Equiv.swap a j) a = j := by simp [Equiv.Perm.mul_apply, hτj]
  refine ⟨⟨fun i hi => ?_, fun i hi => ?_⟩, hsa⟩
  · have hia : i ≠ a := fun h => hi (h ▸ ha)
    have hij : i ≠ j := fun h => hi (h ▸ hjs)
    simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hia hij]
    exact hout i (fun h => hi (Finset.mem_erase.mp (Finset.mem_erase.mp h).2).2)
  · by_cases hia : i = a
    · subst hia
      refine ⟨by rw [hsa]; exact hjs, by rw [hsa]; exact hja, ?_⟩
      rw [hsa]
      simp [Equiv.Perm.mul_apply, hτa]
    by_cases hij : i = j
    · subst hij
      have hsj : (τ * Equiv.swap a i) i = a := by simp [Equiv.Perm.mul_apply, hτa]
      refine ⟨by rw [hsj]; exact ha, by rw [hsj]; exact Ne.symm hia, ?_⟩
      rw [hsj, hsa]
    have hi' : i ∈ (s.erase a).erase j :=
      Finset.mem_erase.mpr ⟨hij, Finset.mem_erase.mpr ⟨hia, hi⟩⟩
    obtain ⟨h1, h2, h3⟩ := hin i hi'
    have hτia : τ i ≠ a := fun h => (Finset.mem_erase.mp (Finset.mem_erase.mp (h ▸ h1)).2).1 rfl
    have hτij : τ i ≠ j := fun h => (Finset.mem_erase.mp (h ▸ h1)).1 rfl
    simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hia hij,
      Equiv.swap_apply_of_ne_of_ne hτia hτij]
    exact ⟨(Finset.mem_erase.mp (Finset.mem_erase.mp h1).2).2, h2, h3⟩

/-- The weight of a matching splits off the pair of the least leg `a`:
`wt(σ) = ⟪w_a, C w_{σ a}⟫ wt(σ * swap a (σ a))` on `s \ {a, σ a}`. -/
lemma matchingWeight_eq (C : E →ₗ[ℝ] E) (w : Fin m → E) {s : Finset (Fin m)} {σ : Equiv.Perm (Fin m)}
    (hσ : IsMatching s σ) {a : Fin m} (ha : a ∈ s) (hmin : ∀ i ∈ s, a ≤ i) :
    matchingWeight C w s σ = ⟪w a, C (w (σ a))⟫ *
      matchingWeight C w ((s.erase a).erase (σ a)) (σ * Equiv.swap a (σ a)) := by
  obtain ⟨hout, hin⟩ := hσ
  obtain ⟨hja, hjne, hjj⟩ := hin a ha
  set j := σ a with hj
  have haj : a < j := lt_of_le_of_ne (hmin j hja) (Ne.symm hjne)
  have hset : s.filter (fun i => i < σ i) =
      insert a (((s.erase a).erase j).filter (fun i => i < (σ * Equiv.swap a j) i)) := by
    refine Finset.ext fun i => ?_
    rw [Finset.mem_filter, Finset.mem_insert, Finset.mem_filter, Finset.mem_erase, Finset.mem_erase,
      Equiv.Perm.mul_apply]
    constructor
    · rintro ⟨his, hlt⟩
      by_cases hia : i = a
      · exact Or.inl hia
      have hij : i ≠ j := by
        rintro rfl
        rw [hjj] at hlt
        exact absurd (hlt.trans haj) (lt_irrefl _)
      exact Or.inr ⟨⟨hij, hia, his⟩, by rwa [Equiv.swap_apply_of_ne_of_ne hia hij]⟩
    · rintro (rfl | ⟨⟨hij, hia, his⟩, hlt⟩)
      · exact ⟨ha, haj⟩
      · exact ⟨his, by rwa [Equiv.swap_apply_of_ne_of_ne hia hij] at hlt⟩
  have hanot : a ∉ ((s.erase a).erase j).filter (fun i => i < (σ * Equiv.swap a j) i) := fun h => by
    rw [Finset.mem_filter, Finset.mem_erase, Finset.mem_erase] at h
    exact h.1.2.1 rfl
  unfold matchingWeight
  rw [hset, Finset.prod_insert hanot]
  congr 1
  refine Finset.prod_congr rfl fun i hi => ?_
  simp only [Finset.mem_filter, Finset.mem_erase] at hi
  rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hi.1.2.1 hi.1.1]

/-- The sum over the matchings of `s` split by the partner `j` of the least leg `a`. -/
lemma sum_matchings_eq (C : E →ₗ[ℝ] E) (w : Fin m → E) {s : Finset (Fin m)} {a : Fin m} (ha : a ∈ s)
    (hmin : ∀ i ∈ s, a ≤ i) :
    ∑ σ ∈ matchings s, matchingWeight C w s σ =
      ∑ j ∈ s.erase a, ⟪w a, C (w j)⟫ *
        ∑ τ ∈ matchings ((s.erase a).erase j), matchingWeight C w ((s.erase a).erase j) τ := by
  have hmaps : ∀ σ ∈ matchings s, σ a ∈ s.erase a := by
    intro σ hσ
    have h := ((Finset.mem_filter.mp hσ).2.2 a ha)
    exact Finset.mem_erase.mpr ⟨h.2.1, h.1⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_nbij' (fun σ => σ * Equiv.swap a j) (fun τ => τ * Equiv.swap a j) ?_ ?_ ?_ ?_ ?_
  · intro σ hσ
    simp only [Finset.mem_filter, matchings, Finset.mem_univ, true_and] at hσ ⊢
    have := isMatching_mul_swap hσ.1 ha
    rwa [hσ.2] at this
  · intro τ hτ
    simp only [Finset.mem_filter, matchings, Finset.mem_univ, true_and] at hτ ⊢
    exact isMatching_mul_swap_of ha hj hτ
  · intro σ _
    simp [mul_assoc]
  · intro τ _
    simp [mul_assoc]
  · intro σ hσ
    simp only [Finset.mem_filter, matchings, Finset.mem_univ, true_and] at hσ
    rw [matchingWeight_eq C w hσ.1 ha hmin, hσ.2]

/-- **The pairing sum is the sum over perfect matchings**: for symmetric `C`,
`W(s) = Σ_{σ perfect matching of s} ∏_{i ∈ s, i < σ i} ⟪w_i, C w_{σ i}⟫`. -/
theorem wickSum_eq_sum_matchings (C : E →ₗ[ℝ] E) (hC : ∀ x y, ⟪C x, y⟫ = ⟪x, C y⟫) (w : Fin m → E)
    (s : Finset (Fin m)) : wickSum C w s = ∑ σ ∈ matchings s, matchingWeight C w s σ := by
  induction h : s.card using Nat.strong_induction_on generalizing s with
  | _ n ih =>
    by_cases hs : s.Nonempty
    · rw [wickSum_of_nonempty C w hs, sum_matchings_eq C w (s.min'_mem hs) (fun i hi => s.min'_le i hi)]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [ih _ (h ▸ card_erase_erase_lt (s.min'_mem hs)) _ rfl, ← hC, real_inner_comm]
    · rw [Finset.not_nonempty_iff_eq_empty.mp hs, wickSum_empty, matchings_empty, Finset.sum_singleton]
      simp [matchingWeight]

/-- The inverse of a symmetric map is symmetric: `⟪C x, y⟫ = ⟪C x, T C y⟫ = ⟪T C x, C y⟫ = ⟪x, C y⟫`. -/
lemma isSymmetric_of_inverse {T C : E →ₗ[ℝ] E} (hT : T.IsSymmetric) (hTC : ∀ w, T (C w) = w) (x y : E) :
    ⟪C x, y⟫ = ⟪x, C y⟫ := by
  conv_lhs => rw [← hTC y]
  rw [← hT (C x) (C y), hTC x]

/-- **Isserlis' theorem as a sum over pairings**: for `T` symmetric positive definite and `T C = 1`,
`∫ ∏_{i ∈ s} ⟪v_i, x⟫ e^{-½⟪x, T x⟫} dx = (∫ e^{-½⟪x, T x⟫} dx) Σ_{σ perfect matching of s} ∏_{i < σ i} ⟪v_i, C v_{σ i}⟫`. -/
theorem gaussMoment_eq_sum_matchings [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {T C : E →ₗ[ℝ] E} (hT : T.IsSymmetric) (hpos : ∀ x, x ≠ 0 → 0 < ⟪x, T x⟫) (hTC : ∀ w, T (C w) = w)
    (v : Fin m → E) (s : Finset (Fin m)) :
    gaussMoment T s v = gaussMoment T (∅ : Finset (Fin m)) v * ∑ σ ∈ matchings s, matchingWeight C v s σ := by
  rw [gaussMoment_eq_wickSum hT hpos hTC v s, wickSum_eq_sum_matchings C (isSymmetric_of_inverse hT hTC) v s]

end GaussianBlockSpin
