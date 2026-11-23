import GaussianBlockSpin.TruncatedExpectations

/-! Three general facts about joint cumulants (`jointCumulant`, the first-vertex recursion from a moment function `M`
with `M ∅ = 1`), used for the cumulant expansion over independent variables (Bałaban I L1409-L1417, the lemma of
[2]):
* jointCumulant_eq_zero_of_split: if `S` splits into two nonempty parts `A`, `S \ A` whose moments factorise,
  `M(U) = M(U ∩ A) M(U \ A)` for `U ⊆ S` (independent groups of variables), then `κ(S) = 0`;
* abs_jointCumulant_le: if `|M(U)| ≤ ∏_{i ∈ U} b_i` for `U ⊆ S`, then `|κ(S)| ≤ c_{|S|} ∏_{i ∈ S} b_i` with the
  universal constants `c_n = cumBound n` (`c_1 = 1`, `c_{n+1} = 1 + Σ_{j<n} C(n, j) c_{j+1}`);
* abs_jointCumulant_sub_le: if moreover `|M(U) - M'(U)| ≤ η ∏_{i ∈ U} b_i`, then
  `|κ_M(S) - κ_{M'}(S)| ≤ c'_{|S|} η ∏_{i ∈ S} b_i` with the universal constants `c'_n = cumLip n`. -/

namespace GaussianBlockSpin

variable {n : ℕ}

/-- The case `min S ∈ A` of jointCumulant_eq_zero_of_split, by strong induction on `|S|`. -/
lemma jointCumulant_eq_zero_of_split_aux (M : Finset (Fin n) → ℝ) (hM : M ∅ = 1) (c : ℕ) :
    ∀ (S A : Finset (Fin n)), S.card = c → A ⊆ S → (S \ A).Nonempty →
      (∀ U ⊆ S, M U = M (U ∩ A) * M (U \ A)) → ∀ hS : S.Nonempty, S.min' hS ∈ A → jointCumulant M S = 0 := by
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    intro S A hc hAS hSA hfac hS hv
    set v := S.min' hS with hvdef
    have hA : A.Nonempty := ⟨v, hv⟩
    -- the sets `B ∋ v`, `B ⊊ S`, not inside `A` have vanishing cumulant
    have hzero : ∀ B ∈ (S.powerset.filter (fun B => B ≠ S)).filter (fun B => v ∈ B),
        B ∉ A.powerset.filter (fun B => v ∈ B) → jointCumulant M B = 0 := by
      intro B hB hBA
      obtain ⟨hB1, hvB⟩ := Finset.mem_filter.mp hB
      have hBS : B ⊆ S := Finset.mem_powerset.mp (Finset.mem_filter.mp hB1).1
      have hBnA : ¬ B ⊆ A := fun h => hBA (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr h, hvB⟩)
      have hBne : B.Nonempty := ⟨v, hvB⟩
      have hminB : B.min' hBne = v := by
        refine le_antisymm (B.min'_le v hvB) ?_
        exact S.min'_le _ (hBS (B.min'_mem hBne))
      refine ih B.card (hc ▸ card_lt_of_mem_proper hB1) B (B ∩ A) rfl Finset.inter_subset_left ?_ ?_ hBne ?_
      · obtain ⟨x, hxB, hxA⟩ := Finset.not_subset.mp hBnA
        exact ⟨x, Finset.mem_sdiff.mpr ⟨hxB, fun h => hxA (Finset.mem_inter.mp h).2⟩⟩
      · intro U hU
        have h1 : U ∩ (B ∩ A) = U ∩ A := by
          ext x; simp only [Finset.mem_inter]; constructor
          · rintro ⟨h1, -, h3⟩; exact ⟨h1, h3⟩
          · rintro ⟨h1, h3⟩; exact ⟨h1, hU h1, h3⟩
        have h2 : U \ (B ∩ A) = U \ A := by
          ext x; simp only [Finset.mem_sdiff, Finset.mem_inter]; constructor
          · rintro ⟨h1, h3⟩; exact ⟨h1, fun h => h3 ⟨hU h1, h⟩⟩
          · rintro ⟨h1, h3⟩; exact ⟨h1, fun h => h3 h.2⟩
        rw [h1, h2]
        exact hfac U (hU.trans hBS)
      · rw [hminB]; exact Finset.mem_inter.mpr ⟨hvB, hv⟩
    have hsub : A.powerset.filter (fun B => v ∈ B) ⊆ (S.powerset.filter (fun B => B ≠ S)).filter (fun B => v ∈ B) := by
      intro B hB
      obtain ⟨hBA, hvB⟩ := Finset.mem_filter.mp hB
      have hBA' := Finset.mem_powerset.mp hBA
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (hBA'.trans hAS), ?_⟩, hvB⟩
      rintro rfl
      obtain ⟨x, hx⟩ := hSA
      exact (Finset.mem_sdiff.mp hx).2 (hBA' (Finset.mem_sdiff.mp hx).1)
    have hsum : ∑ B ∈ (S.powerset.filter (fun B => B ≠ S)).filter (fun B => v ∈ B), jointCumulant M B * M (S \ B) =
        ∑ B ∈ A.powerset.filter (fun B => v ∈ B), jointCumulant M B * M (S \ B) := by
      refine (Finset.sum_subset hsub fun B hB hBA => ?_).symm
      rw [hzero B hB hBA, zero_mul]
    have hfacB : ∀ B ∈ A.powerset.filter (fun B => v ∈ B), M (S \ B) = M (A \ B) * M (S \ A) := by
      intro B hB
      have hBA := Finset.mem_powerset.mp (Finset.mem_filter.mp hB).1
      have h1 : (S \ B) ∩ A = A \ B := by
        ext x; simp only [Finset.mem_inter, Finset.mem_sdiff]; constructor
        · rintro ⟨⟨-, h2⟩, h3⟩; exact ⟨h3, h2⟩
        · rintro ⟨h3, h2⟩; exact ⟨⟨hAS h3, h2⟩, h3⟩
      have h2 : (S \ B) \ A = S \ A := by
        ext x; simp only [Finset.mem_sdiff]; constructor
        · rintro ⟨⟨h1, -⟩, h3⟩; exact ⟨h1, h3⟩
        · rintro ⟨h1, h3⟩; exact ⟨⟨h1, fun h => h3 (hBA h)⟩, h3⟩
      rw [hfac (S \ B) Finset.sdiff_subset, h1, h2]
    have hminA : A.min' hA = v := by
      refine le_antisymm (A.min'_le v hv) ?_
      exact S.min'_le _ (hAS (A.min'_mem hA))
    have hmomA := moment_eq_sum_jointCumulant M hM hA
    rw [hminA] at hmomA
    have hSA' : S ∩ A = A := Finset.inter_eq_right.mpr hAS
    rw [jointCumulant_of_nonempty M hS, ← hvdef, hsum, Finset.sum_congr rfl fun B hB => by rw [hfacB B hB],
      hfac S subset_rfl, hSA']
    have : ∑ B ∈ A.powerset.filter (fun B => v ∈ B), jointCumulant M B * (M (A \ B) * M (S \ A)) =
        (∑ B ∈ A.powerset.filter (fun B => v ∈ B), jointCumulant M B * M (A \ B)) * M (S \ A) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun B _ => ?_
      ring
    rw [this, ← hmomA, sub_self]

/-- **Joint cumulants of independent groups vanish**: if `A ⊆ S` and `S \ A` are both nonempty and the moments of the
subsets of `S` factorise, `M(U) = M(U ∩ A) M(U \ A)`, then `κ(S) = 0` (`M ∅ = 1`). -/
theorem jointCumulant_eq_zero_of_split (M : Finset (Fin n) → ℝ) (hM : M ∅ = 1) {S A : Finset (Fin n)} (hAS : A ⊆ S)
    (hA : A.Nonempty) (hSA : (S \ A).Nonempty) (hfac : ∀ U ⊆ S, M U = M (U ∩ A) * M (U \ A)) :
    jointCumulant M S = 0 := by
  have hS : S.Nonempty := hA.mono hAS
  by_cases hv : S.min' hS ∈ A
  · exact jointCumulant_eq_zero_of_split_aux M hM S.card S A rfl hAS hSA hfac hS hv
  · refine jointCumulant_eq_zero_of_split_aux M hM S.card S (S \ A) rfl Finset.sdiff_subset ?_ ?_ hS
      (Finset.mem_sdiff.mpr ⟨S.min'_mem hS, hv⟩)
    · rw [Finset.sdiff_sdiff_eq_self hAS]; exact hA
    · intro U hU
      have h1 : U ∩ (S \ A) = U \ A := by
        ext x; simp only [Finset.mem_inter, Finset.mem_sdiff]; constructor
        · rintro ⟨h1, -, h3⟩; exact ⟨h1, h3⟩
        · rintro ⟨h1, h3⟩; exact ⟨h1, hU h1, h3⟩
      have h2 : U \ (S \ A) = U ∩ A := by
        ext x; simp only [Finset.mem_inter, Finset.mem_sdiff]; constructor
        · rintro ⟨h1, h3⟩; exact ⟨h1, by by_contra h; exact h3 ⟨hU h1, h⟩⟩
        · rintro ⟨h1, h3⟩; exact ⟨h1, fun h => h.2 h3⟩
      rw [h1, h2, mul_comm]
      exact hfac U hU

/-- The universal constants of the a priori bound on joint cumulants: `c_0 = 0`,
`c_{n+1} = 1 + Σ_{j<n} C(n, j) c_{j+1}` (`c_1 = 1`, `c_2 = 2`, `c_3 = 6`, `c_4 = 26`). -/
noncomputable def cumBound : ℕ → ℝ
  | 0 => 0
  | n + 1 => 1 + ∑ j : Fin n, (n.choose j : ℝ) * cumBound (j + 1)
decreasing_by exact Nat.succ_lt_succ j.isLt

lemma cumBound_succ (n : ℕ) :
    cumBound (n + 1) = 1 + ∑ j ∈ Finset.range n, (n.choose j : ℝ) * cumBound (j + 1) := by
  rw [cumBound, Finset.sum_range]

lemma cumBound_nonneg (n : ℕ) : 0 ≤ cumBound n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | n
    · simp [cumBound]
    · rw [cumBound_succ]
      have : ∀ j ∈ Finset.range n, 0 ≤ (n.choose j : ℝ) * cumBound (j + 1) := fun j hj =>
        mul_nonneg (Nat.cast_nonneg _) (ih (j + 1) (by have := Finset.mem_range.mp hj; omega))
      linarith [Finset.sum_nonneg this]

/-- **A priori bound on joint cumulants**: if `|M(U)| ≤ ∏_{i ∈ U} b_i` for every `U ⊆ S` (`b ≥ 0`), then
`|κ(S)| ≤ c_{|S|} ∏_{i ∈ S} b_i`, `c = cumBound`. -/
theorem abs_jointCumulant_le (M : Finset (Fin n) → ℝ) (b : Fin n → ℝ) (hb : ∀ i, 0 ≤ b i) (S : Finset (Fin n))
    (hMb : ∀ U ⊆ S, |M U| ≤ ∏ i ∈ U, b i) :
    |jointCumulant M S| ≤ cumBound S.card * ∏ i ∈ S, b i := by
  induction hc : S.card using Nat.strong_induction_on generalizing S with
  | _ c ih =>
    subst hc
    by_cases hS : S.Nonempty
    · set v := S.min' hS with hvdef
      have hv : v ∈ S := S.min'_mem hS
      set F := (S.powerset.filter (fun B => B ≠ S)).filter (fun B => v ∈ B) with hF
      have hPS : 0 ≤ ∏ i ∈ S, b i := Finset.prod_nonneg fun i _ => hb i
      -- each term of the recursion
      have hterm : ∀ B ∈ F, |jointCumulant M B * M (S \ B)| ≤ cumBound B.card * ∏ i ∈ S, b i := by
        intro B hB
        have hB1 := (Finset.mem_filter.mp hB).1
        have hBS : B ⊆ S := Finset.mem_powerset.mp (Finset.mem_filter.mp hB1).1
        have h1 := ih B.card (card_lt_of_mem_proper hB1) B (fun U hU => hMb U (hU.trans hBS)) rfl
        have h2 := hMb (S \ B) Finset.sdiff_subset
        calc |jointCumulant M B * M (S \ B)| = |jointCumulant M B| * |M (S \ B)| := abs_mul _ _
          _ ≤ (cumBound B.card * ∏ i ∈ B, b i) * ∏ i ∈ S \ B, b i :=
              mul_le_mul h1 h2 (abs_nonneg _)
                (mul_nonneg (cumBound_nonneg _) (Finset.prod_nonneg fun i _ => hb i))
          _ = cumBound B.card * ∏ i ∈ S, b i := by
              rw [← Finset.prod_sdiff hBS]
              ring
      -- the count of the recursion
      have hcount : ∑ B ∈ F, cumBound B.card = cumBound S.card - 1 := by
        have hFeq : ∑ B ∈ F, cumBound B.card = ∑ B ∈ S.powerset.filter (fun B => v ∈ B),
            (fun j k => if k = 0 then (0 : ℝ) else cumBound j) B.card (S \ B).card := by
          rw [hF, Finset.filter_filter, Finset.sum_filter, Finset.sum_filter]
          refine Finset.sum_congr rfl fun B hB => ?_
          have hBS : B ⊆ S := Finset.mem_powerset.mp hB
          have hiff : (S \ B).card = 0 ↔ B = S := by
            rw [Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset]
            exact ⟨fun h => Finset.Subset.antisymm hBS h, fun h => h ▸ subset_rfl⟩
          by_cases hvB : v ∈ B
          · by_cases hBS' : B = S
            · simp [hBS']
            · have : (S \ B).card ≠ 0 := fun h => hBS' (hiff.mp h)
              simp [hvB, hBS', this]
          · simp [hvB]
        rw [hFeq, sum_filter_mem_powerset_card hv (fun j k => if k = 0 then (0 : ℝ) else cumBound j)]
        obtain ⟨m, hm⟩ : ∃ m, S.card = m + 1 := ⟨S.card - 1, (Nat.sub_add_cancel (Finset.card_pos.mpr hS)).symm⟩
        rw [hm, Nat.add_sub_cancel, Finset.sum_range_succ, cumBound_succ]
        simp only [Nat.choose_self, Nat.sub_self, ↓reduceIte, mul_zero, add_zero]
        rw [add_sub_cancel_left]
        refine Finset.sum_congr rfl fun j hj => ?_
        have : m - j ≠ 0 := by have := Finset.mem_range.mp hj; omega
        simp [this]
      rw [jointCumulant_of_nonempty M hS, ← hvdef, ← hF]
      calc |M S - ∑ B ∈ F, jointCumulant M B * M (S \ B)|
          ≤ |M S| + ∑ B ∈ F, |jointCumulant M B * M (S \ B)| :=
            (abs_sub _ _).trans (add_le_add le_rfl (Finset.abs_sum_le_sum_abs _ _))
        _ ≤ ∏ i ∈ S, b i + ∑ B ∈ F, cumBound B.card * ∏ i ∈ S, b i :=
            add_le_add (hMb S subset_rfl) (Finset.sum_le_sum hterm)
        _ = cumBound S.card * ∏ i ∈ S, b i := by
            rw [← Finset.sum_mul, hcount]
            ring
    · rw [Finset.not_nonempty_iff_eq_empty.mp hS]
      simpa [jointCumulant] using cumBound_nonneg 0

/-- The constants of the Lipschitz bound on joint cumulants: `c'_0 = 0`,
`c'_{n+1} = 1 + Σ_{j<n} C(n, j) (c'_{j+1} + c_{j+1})`. -/
noncomputable def cumLip : ℕ → ℝ
  | 0 => 0
  | n + 1 => 1 + ∑ j : Fin n, (n.choose j : ℝ) * (cumLip (j + 1) + cumBound (j + 1))
decreasing_by exact Nat.succ_lt_succ j.isLt

lemma cumLip_succ (n : ℕ) :
    cumLip (n + 1) = 1 + ∑ j ∈ Finset.range n, (n.choose j : ℝ) * (cumLip (j + 1) + cumBound (j + 1)) := by
  rw [cumLip, Finset.sum_range]

lemma cumLip_nonneg (n : ℕ) : 0 ≤ cumLip n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | n
    · simp [cumLip]
    · rw [cumLip_succ]
      have : ∀ j ∈ Finset.range n, 0 ≤ (n.choose j : ℝ) * (cumLip (j + 1) + cumBound (j + 1)) := fun j hj =>
        mul_nonneg (Nat.cast_nonneg _) (add_nonneg (ih (j + 1) (by have := Finset.mem_range.mp hj; omega))
          (cumBound_nonneg _))
      linarith [Finset.sum_nonneg this]

/-- **Lipschitz bound on joint cumulants**: if `|M(U)|, |M'(U)| ≤ ∏_{i ∈ U} b_i` and `|M(U) - M'(U)| ≤ η ∏_{i ∈ U} b_i`
for every `U ⊆ S`, then `|κ_M(S) - κ_{M'}(S)| ≤ c'_{|S|} η ∏_{i ∈ S} b_i`. -/
theorem abs_jointCumulant_sub_le (M M' : Finset (Fin n) → ℝ) (b : Fin n → ℝ) (hb : ∀ i, 0 ≤ b i) {η : ℝ}
    (hη : 0 ≤ η) (S : Finset (Fin n)) (hM : ∀ U ⊆ S, |M U| ≤ ∏ i ∈ U, b i) (hM' : ∀ U ⊆ S, |M' U| ≤ ∏ i ∈ U, b i)
    (hd : ∀ U ⊆ S, |M U - M' U| ≤ η * ∏ i ∈ U, b i) :
    |jointCumulant M S - jointCumulant M' S| ≤ cumLip S.card * η * ∏ i ∈ S, b i := by
  induction hc : S.card using Nat.strong_induction_on generalizing S with
  | _ c ih =>
    subst hc
    by_cases hS : S.Nonempty
    · set v := S.min' hS with hvdef
      have hv : v ∈ S := S.min'_mem hS
      set F := (S.powerset.filter (fun B => B ≠ S)).filter (fun B => v ∈ B) with hF
      have hterm : ∀ B ∈ F, |jointCumulant M B * M (S \ B) - jointCumulant M' B * M' (S \ B)| ≤
          (cumLip B.card + cumBound B.card) * η * ∏ i ∈ S, b i := by
        intro B hB
        have hB1 := (Finset.mem_filter.mp hB).1
        have hBS : B ⊆ S := Finset.mem_powerset.mp (Finset.mem_filter.mp hB1).1
        have h1 := ih B.card (card_lt_of_mem_proper hB1) B (fun U hU => hM U (hU.trans hBS))
          (fun U hU => hM' U (hU.trans hBS)) (fun U hU => hd U (hU.trans hBS)) rfl
        have h2 := abs_jointCumulant_le M' b hb B (fun U hU => hM' U (hU.trans hBS))
        have h3 := hM (S \ B) Finset.sdiff_subset
        have h4 := hd (S \ B) Finset.sdiff_subset
        have hPB : 0 ≤ ∏ i ∈ B, b i := Finset.prod_nonneg fun i _ => hb i
        have hPSB : 0 ≤ ∏ i ∈ S \ B, b i := Finset.prod_nonneg fun i _ => hb i
        have hsplit : jointCumulant M B * M (S \ B) - jointCumulant M' B * M' (S \ B) =
            (jointCumulant M B - jointCumulant M' B) * M (S \ B) +
              jointCumulant M' B * (M (S \ B) - M' (S \ B)) := by ring
        rw [hsplit, ← Finset.prod_sdiff hBS]
        calc |(jointCumulant M B - jointCumulant M' B) * M (S \ B) +
              jointCumulant M' B * (M (S \ B) - M' (S \ B))|
            ≤ |jointCumulant M B - jointCumulant M' B| * |M (S \ B)| +
                |jointCumulant M' B| * |M (S \ B) - M' (S \ B)| := by
              rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
          _ ≤ (cumLip B.card * η * ∏ i ∈ B, b i) * ∏ i ∈ S \ B, b i +
                (cumBound B.card * ∏ i ∈ B, b i) * (η * ∏ i ∈ S \ B, b i) := by
              have : 0 ≤ cumBound B.card * ∏ i ∈ B, b i := mul_nonneg (cumBound_nonneg _) hPB
              have : 0 ≤ cumLip B.card * η * ∏ i ∈ B, b i := mul_nonneg (mul_nonneg (cumLip_nonneg _) hη) hPB
              gcongr
          _ = (cumLip B.card + cumBound B.card) * η * ((∏ i ∈ S \ B, b i) * ∏ i ∈ B, b i) := by ring
      have hcount : ∑ B ∈ F, (cumLip B.card + cumBound B.card) = cumLip S.card - 1 := by
        have hFeq : ∑ B ∈ F, (cumLip B.card + cumBound B.card) = ∑ B ∈ S.powerset.filter (fun B => v ∈ B),
            (fun j k => if k = 0 then (0 : ℝ) else cumLip j + cumBound j) B.card (S \ B).card := by
          rw [hF, Finset.filter_filter, Finset.sum_filter, Finset.sum_filter]
          refine Finset.sum_congr rfl fun B hB => ?_
          have hBS : B ⊆ S := Finset.mem_powerset.mp hB
          have hiff : (S \ B).card = 0 ↔ B = S := by
            rw [Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset]
            exact ⟨fun h => Finset.Subset.antisymm hBS h, fun h => h ▸ subset_rfl⟩
          by_cases hvB : v ∈ B
          · by_cases hBS' : B = S
            · simp [hBS']
            · have : (S \ B).card ≠ 0 := fun h => hBS' (hiff.mp h)
              simp [hvB, hBS', this]
          · simp [hvB]
        rw [hFeq, sum_filter_mem_powerset_card hv (fun j k => if k = 0 then (0 : ℝ) else cumLip j + cumBound j)]
        obtain ⟨m, hm⟩ : ∃ m, S.card = m + 1 := ⟨S.card - 1, (Nat.sub_add_cancel (Finset.card_pos.mpr hS)).symm⟩
        rw [hm, Nat.add_sub_cancel, Finset.sum_range_succ, cumLip_succ]
        simp only [Nat.choose_self, Nat.sub_self, ↓reduceIte, mul_zero, add_zero]
        rw [add_sub_cancel_left]
        refine Finset.sum_congr rfl fun j hj => ?_
        have : m - j ≠ 0 := by have := Finset.mem_range.mp hj; omega
        simp [this]
      rw [jointCumulant_of_nonempty M hS, jointCumulant_of_nonempty M' hS, ← hvdef, ← hF]
      have hPS : 0 ≤ ∏ i ∈ S, b i := Finset.prod_nonneg fun i _ => hb i
      calc |M S - ∑ B ∈ F, jointCumulant M B * M (S \ B) - (M' S - ∑ B ∈ F, jointCumulant M' B * M' (S \ B))|
          = |(M S - M' S) - ∑ B ∈ F, (jointCumulant M B * M (S \ B) - jointCumulant M' B * M' (S \ B))| := by
            rw [Finset.sum_sub_distrib]; ring_nf
        _ ≤ |M S - M' S| + ∑ B ∈ F, |jointCumulant M B * M (S \ B) - jointCumulant M' B * M' (S \ B)| :=
            (abs_sub _ _).trans (add_le_add le_rfl (Finset.abs_sum_le_sum_abs _ _))
        _ ≤ η * ∏ i ∈ S, b i + ∑ B ∈ F, (cumLip B.card + cumBound B.card) * η * ∏ i ∈ S, b i :=
            add_le_add (hd S subset_rfl) (Finset.sum_le_sum hterm)
        _ = cumLip S.card * η * ∏ i ∈ S, b i := by
            rw [← Finset.sum_mul, ← Finset.sum_mul, hcount]
            ring
    · rw [Finset.not_nonempty_iff_eq_empty.mp hS]
      simpa [jointCumulant] using mul_nonneg (cumLip_nonneg 0) hη

end GaussianBlockSpin
