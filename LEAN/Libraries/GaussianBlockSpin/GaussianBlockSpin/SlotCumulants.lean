import GaussianBlockSpin.LogDerivatives
import GaussianBlockSpin.TruncatedExpectations

/-! Mixed Taylor coefficients in slot form. The `a + b` derivative slots `Fin (a + b)` are typed: slots `< a` are
`e`-slots, the others `λ`-slots, and a slot set `S` stands for `∂^S = ∂_λ^{λ(S)} ∂_e^{e(S)}` (`eCount`, `lCount`). The
two-index recursions for `exp ∘ F` become the first-slot decomposition `∂^S e^F = Σ_{B ∋ min S} ∂^B F ∂^{S \ B} e^F`
(slot_decomp_of_recursions, mixedCoeff_exp_slot), and by the uniqueness of joint cumulants the mixed Taylor
coefficients of `log Z` are the joint cumulants of the normalised mixed derivatives of `Z`
(mixedCoeff_log_eq_jointCumulant). Since `E_k = -log[…]` (I.(3.35), III (1.4)), for `α + β ≥ 1` the derivatives
`∂^{α+β} E_k / ∂e'^α ∂λ'^β` at `(0, 0)` in (3.36) and III (1.5) (which carry the factor `1/(α! β!)` there) are the
negatives of these joint cumulants; Part III describes them by connected graphs. -/

open scoped Topology

namespace GaussianBlockSpin

/-- Subsets of a disjoint union are pairs of subsets. -/
lemma sum_powerset_union_of_disjoint {α : Type*} [DecidableEq α] {U V : Finset α} (hUV : Disjoint U V)
    (f : Finset α → ℝ) :
    ∑ B ∈ (U ∪ V).powerset, f B = ∑ B₁ ∈ U.powerset, ∑ B₂ ∈ V.powerset, f (B₁ ∪ B₂) := by
  rw [← Finset.sum_product']
  refine Finset.sum_nbij' (fun B => (B ∩ U, B ∩ V)) (fun p => p.1 ∪ p.2) ?_ ?_ ?_ ?_ ?_
  · intro B _
    simp only [Finset.mem_product, Finset.mem_powerset]
    exact ⟨Finset.inter_subset_right, Finset.inter_subset_right⟩
  · intro p hp
    simp only [Finset.mem_product, Finset.mem_powerset] at hp ⊢
    exact Finset.union_subset_union hp.1 hp.2
  · intro B hB
    simp only [Finset.mem_powerset] at hB
    rw [← Finset.inter_union_distrib_left, Finset.inter_eq_left.mpr hB]
  · intro p hp
    simp only [Finset.mem_product, Finset.mem_powerset] at hp
    have h1 : Disjoint p.2 U := Finset.disjoint_of_subset_left hp.2 hUV.symm
    have h2 : Disjoint p.1 V := Finset.disjoint_of_subset_left hp.1 hUV
    ext1
    · simp only
      rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr hp.1, Finset.disjoint_iff_inter_eq_empty.mp h1,
        Finset.union_empty]
    · simp only
      rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr hp.2, Finset.disjoint_iff_inter_eq_empty.mp h2,
        Finset.empty_union]
  · intro B hB
    simp only [Finset.mem_powerset] at hB
    rw [← Finset.inter_union_distrib_left, Finset.inter_eq_left.mpr hB]

/-- The number of `e`-slots (indices `< p`) of a slot set. -/
def eCount (p : ℕ) {n : ℕ} (S : Finset (Fin n)) : ℕ := (S.filter fun i => i.val < p).card

/-- The number of `λ`-slots (indices `≥ p`) of a slot set. -/
def lCount (p : ℕ) {n : ℕ} (S : Finset (Fin n)) : ℕ := (S.filter fun i => p ≤ i.val).card

variable {n : ℕ}

lemma filter_sdiff_eq {α : Type*} [DecidableEq α] (q : α → Prop) [DecidablePred q] (S B : Finset α) :
    (S \ B).filter q = S.filter q \ B.filter q := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_sdiff]
  tauto

lemma eCount_sdiff (p : ℕ) {S B : Finset (Fin n)} (hBS : B ⊆ S) : eCount p (S \ B) = eCount p S - eCount p B := by
  unfold eCount
  rw [filter_sdiff_eq, Finset.card_sdiff_of_subset (Finset.filter_subset_filter _ hBS)]

lemma lCount_sdiff (p : ℕ) {S B : Finset (Fin n)} (hBS : B ⊆ S) : lCount p (S \ B) = lCount p S - lCount p B := by
  unfold lCount
  rw [filter_sdiff_eq, Finset.card_sdiff_of_subset (Finset.filter_subset_filter _ hBS)]

/-- **Counting typed sets through an `e`-slot**: if `v ∈ S` is an `e`-slot,
`Σ_{B ⊆ S, v ∈ B} g(e(B), λ(B)) = Σ_{i < e(S)} Σ_{j ≤ λ(S)} C(e(S) - 1, i) C(λ(S), j) g(i + 1, j)`. -/
lemma sum_filter_mem_powerset_typed (p : ℕ) {S : Finset (Fin n)} {v : Fin n} (hv : v ∈ S) (hvp : v.val < p)
    (g : ℕ → ℕ → ℝ) :
    ∑ B ∈ S.powerset.filter (fun B => v ∈ B), g (eCount p B) (lCount p B) =
      ∑ i ∈ Finset.range (eCount p S), ∑ j ∈ Finset.range (lCount p S + 1),
        ((eCount p S - 1).choose i : ℝ) * ((lCount p S).choose j : ℝ) * g (i + 1) j := by
  have hnot : ∀ B' ∈ (S.erase v).powerset, v ∉ B' := fun B' hB' h => by
    simpa using (Finset.mem_powerset.mp hB') h
  rw [filter_mem_powerset_eq_image hv, Finset.sum_image]
  swap
  · intro B1 h1 B2 h2 h
    rw [← Finset.erase_insert (hnot B1 (Finset.mem_coe.mp h1)),
      ← Finset.erase_insert (hnot B2 (Finset.mem_coe.mp h2)), h]
  have hins : ∀ B' ∈ (S.erase v).powerset, g (eCount p (insert v B')) (lCount p (insert v B')) =
      g (eCount p B' + 1) (lCount p B') := by
    intro B' hB'
    unfold eCount lCount
    rw [Finset.filter_insert, Finset.filter_insert]
    simp only [hvp, ↓reduceIte, show ¬ p ≤ v.val by omega]
    rw [Finset.card_insert_of_notMem (fun h => hnot B' hB' (Finset.mem_filter.mp h).1)]
  rw [Finset.sum_congr rfl hins]
  set E' := (S.erase v).filter fun i => i.val < p with hE'def
  set Λ := (S.erase v).filter fun i => ¬ i.val < p with hΛdef
  have hsplit : S.erase v = E' ∪ Λ := (Finset.filter_union_filter_not_eq _ _).symm
  have hdisj : Disjoint E' Λ := Finset.disjoint_filter_filter_not _ _ _
  rw [hsplit, sum_powerset_union_of_disjoint hdisj]
  have hcount : ∀ B₁ ∈ E'.powerset, ∀ B₂ ∈ Λ.powerset,
      eCount p (B₁ ∪ B₂) = B₁.card ∧ lCount p (B₁ ∪ B₂) = B₂.card := by
    intro B₁ h1 B₂ h2
    have h1' := Finset.mem_powerset.mp h1
    have h2' := Finset.mem_powerset.mp h2
    unfold eCount lCount
    rw [Finset.filter_union, Finset.filter_union]
    have e1 : B₁.filter (fun i => i.val < p) = B₁ := Finset.filter_true_of_mem fun i hi =>
      (Finset.mem_filter.mp (h1' hi)).2
    have e2 : B₂.filter (fun i => i.val < p) = ∅ := Finset.filter_false_of_mem fun i hi =>
      (Finset.mem_filter.mp (h2' hi)).2
    have l1 : B₁.filter (fun i => p ≤ i.val) = ∅ := Finset.filter_false_of_mem fun i hi => by
      have := (Finset.mem_filter.mp (h1' hi)).2
      omega
    have l2 : B₂.filter (fun i => p ≤ i.val) = B₂ := Finset.filter_true_of_mem fun i hi => by
      have := (Finset.mem_filter.mp (h2' hi)).2
      omega
    rw [e1, e2, l1, l2, Finset.union_empty, Finset.empty_union]
    exact ⟨rfl, rfl⟩
  have hE' : E'.card = eCount p S - 1 := by
    unfold eCount
    rw [hE'def, Finset.filter_erase, Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨hv, hvp⟩)]
  have hΛ : Λ.card = lCount p S := by
    unfold lCount
    rw [hΛdef, Finset.filter_erase, Finset.erase_eq_of_notMem (by simp [hvp])]
    congr 1
    ext i
    simp only [Finset.mem_filter, not_lt]
  rw [Finset.sum_congr rfl fun B₁ h1 => Finset.sum_congr rfl fun B₂ h2 => by
    rw [(hcount B₁ h1 B₂ h2).1, (hcount B₁ h1 B₂ h2).2]]
  rw [Finset.sum_powerset_apply_card (fun i => ∑ B₂ ∈ Λ.powerset, g (i + 1) B₂.card), hE']
  have hpos : eCount p S - 1 + 1 = eCount p S := Nat.sub_add_cancel (Finset.card_pos.mpr ⟨v, by
    exact Finset.mem_filter.mpr ⟨hv, hvp⟩⟩)
  rw [hpos]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_powerset_apply_card (fun j => g (i + 1) j), hΛ, nsmul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [nsmul_eq_mul]
  ring

lemma eCount_univ (a b : ℕ) : eCount a (Finset.univ : Finset (Fin (a + b))) = a := by
  unfold eCount
  have : (Finset.univ.filter fun i : Fin (a + b) => i.val < a).map Fin.valEmbedding = Finset.range a := by
    ext x
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
      Finset.mem_range]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact hi
    · intro hx
      exact ⟨⟨x, by omega⟩, hx, rfl⟩
  rw [← Finset.card_map, this, Finset.card_range]

lemma lCount_univ (a b : ℕ) : lCount a (Finset.univ : Finset (Fin (a + b))) = b := by
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin (a + b))))
    (fun i : Fin (a + b) => i.val < a)
  rw [Finset.card_univ, Fintype.card_fin] at h
  have h1 := eCount_univ a b
  unfold eCount at h1
  unfold lCount
  have : (Finset.univ.filter fun i : Fin (a + b) => a ≤ i.val) =
      Finset.univ.filter fun i : Fin (a + b) => ¬ i.val < a := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
  rw [this]
  omega

lemma eCount_mono (p : ℕ) {S T : Finset (Fin n)} (h : S ⊆ T) : eCount p S ≤ eCount p T :=
  Finset.card_le_card (Finset.filter_subset_filter _ h)

lemma lCount_mono (p : ℕ) {S T : Finset (Fin n)} (h : S ⊆ T) : lCount p S ≤ lCount p T :=
  Finset.card_le_card (Finset.filter_subset_filter _ h)

lemma eCount_eq_zero_of {p : ℕ} {S : Finset (Fin n)} (hS : ∀ i ∈ S, p ≤ i.val) : eCount p S = 0 := by
  unfold eCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro i hi
  have := hS i hi
  omega

lemma lCount_eq_card_of {p : ℕ} {S : Finset (Fin n)} (hS : ∀ i ∈ S, p ≤ i.val) : lCount p S = S.card := by
  unfold lCount
  rw [Finset.filter_true_of_mem hS]

/-- **From the two-index recursions to the first-slot decomposition**: if `z, L : ℕ → ℕ → ℝ` satisfy the `e`-step
`z(a'+1, b') = Σ_{i ≤ a'} Σ_{j ≤ b'} C(a', i) C(b', j) L(i+1, j) z(a'-i, b'-j)` (`a' + 1 ≤ a`, `b' ≤ b`) and the `λ`-step
`z(0, b'+1) = Σ_{j ≤ b'} C(b', j) L(0, j+1) z(0, b'-j)` (`b' + 1 ≤ b`), then on the `a + b` typed slots
`z(S) = Σ_{B ⊆ S, min S ∈ B} L(B) z(S \ B)` for every nonempty `S` (`z(S) = z(e(S), λ(S))`). -/
theorem slot_decomp_of_recursions (z L : ℕ → ℕ → ℝ) (a b : ℕ)
    (hE : ∀ a' b', a' + 1 ≤ a → b' ≤ b → z (a' + 1) b' = ∑ i ∈ Finset.range (a' + 1),
      ∑ j ∈ Finset.range (b' + 1), (a'.choose i : ℝ) * (b'.choose j : ℝ) * L (i + 1) j * z (a' - i) (b' - j))
    (hL : ∀ b', b' + 1 ≤ b → z 0 (b' + 1) =
      ∑ j ∈ Finset.range (b' + 1), (b'.choose j : ℝ) * L 0 (j + 1) * z 0 (b' - j))
    (S : Finset (Fin (a + b))) (h : S.Nonempty) :
    z (eCount a S) (lCount a S) = ∑ B ∈ S.powerset.filter (fun B => S.min' h ∈ B),
      L (eCount a B) (lCount a B) * z (eCount a (S \ B)) (lCount a (S \ B)) := by
  have hlS : lCount a S ≤ b := (lCount_mono a (Finset.subset_univ S)).trans (lCount_univ a b).le
  have heS : eCount a S ≤ a := (eCount_mono a (Finset.subset_univ S)).trans (eCount_univ a b).le
  set g : ℕ → ℕ → ℝ := fun i j => L i j * z (eCount a S - i) (lCount a S - j) with hg
  have hsd : ∀ B ∈ S.powerset.filter (fun B => S.min' h ∈ B),
      L (eCount a B) (lCount a B) * z (eCount a (S \ B)) (lCount a (S \ B)) = g (eCount a B) (lCount a B) := by
    intro B hB
    have hBS := Finset.mem_powerset.mp (Finset.mem_filter.mp hB).1
    rw [eCount_sdiff a hBS, lCount_sdiff a hBS]
  rw [Finset.sum_congr rfl hsd]
  by_cases hv : (S.min' h).val < a
  · rw [sum_filter_mem_powerset_typed a (S.min'_mem h) hv g]
    have hpos' : 0 < eCount a S := Finset.card_pos.mpr ⟨S.min' h, Finset.mem_filter.mpr ⟨S.min'_mem h, hv⟩⟩
    have h1 := hE (eCount a S - 1) (lCount a S) (by omega) hlS
    rw [Nat.sub_add_cancel hpos'] at h1
    rw [h1]
    refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j _ => ?_
    have hi' : i < eCount a S := Finset.mem_range.mp hi
    rw [hg]
    simp only
    rw [show eCount a S - (i + 1) = eCount a S - 1 - i by omega]
    ring
  · have hall : ∀ i ∈ S, a ≤ i.val := fun i hi => by
      have h1 : S.min' h ≤ i := S.min'_le i hi
      have h2 : (S.min' h).val ≤ i.val := h1
      omega
    have hsub : ∀ B ∈ S.powerset.filter (fun B => S.min' h ∈ B), g (eCount a B) (lCount a B) =
        (fun j k => L 0 j * z 0 k) B.card (S \ B).card := by
      intro B hB
      have hBS := Finset.mem_powerset.mp (Finset.mem_filter.mp hB).1
      have hallB : ∀ i ∈ B, a ≤ i.val := fun i hi => hall i (hBS hi)
      rw [hg]
      simp only
      rw [eCount_eq_zero_of hallB, lCount_eq_card_of hallB, eCount_eq_zero_of hall, lCount_eq_card_of hall,
        Finset.card_sdiff_of_subset hBS]
    rw [Finset.sum_congr rfl hsub, sum_filter_mem_powerset_card (S.min'_mem h) (fun j k => L 0 j * z 0 k)]
    rw [eCount_eq_zero_of hall, lCount_eq_card_of hall]
    have hc : 0 < S.card := Finset.card_pos.mpr h
    have hlS' : S.card ≤ b := by rw [← lCount_eq_card_of hall]; exact hlS
    have h1 := hL (S.card - 1) (by omega)
    rw [Nat.sub_add_cancel hc] at h1
    rw [h1]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring

variable {s : Set ℝ}

/-- **Mixed derivatives of `exp ∘ F` in slot form**: on the `a + b` typed slots,
`∂^S e^F = Σ_{B ⊆ S, min S ∈ B} ∂^B F · ∂^{S \ B} e^F` at `(0, 0)` (`∂^S = ∂^{(e(S), λ(S))}`). -/
theorem mixedCoeff_exp_slot (hs : UniqueDiffOn ℝ s) (h0 : (0 : ℝ) ∈ s) {A B : ℕ} {F : ℝ → ℝ → ℝ}
    (hF : NestedSmooth s A B F) {a b : ℕ} (ha : a ≤ A) (hb : b ≤ B) (S : Finset (Fin (a + b))) (h : S.Nonempty) :
    mixedCoeff s (eCount a S) (lCount a S) (fun e l => Real.exp (F e l)) =
      ∑ B ∈ S.powerset.filter (fun B => S.min' h ∈ B), mixedCoeff s (eCount a B) (lCount a B) F *
        mixedCoeff s (eCount a (S \ B)) (lCount a (S \ B)) (fun e l => Real.exp (F e l)) := by
  have hexp := hF.exp h0
  refine slot_decomp_of_recursions (fun i j => mixedCoeff s i j (fun e l => Real.exp (F e l)))
    (fun i j => mixedCoeff s i j F) a b (fun a' b' ha' hb' => ?_) (fun b' hb' => ?_) S h
  · exact mixedCoeff_exp_succ_left hs h0 (A := a') (B := b') (hF.mono (by omega) (by omega))
      (hexp.mono (by omega) (by omega)) le_rfl le_rfl
  · have hF0 := hF.outer 0 (Nat.zero_le A)
    simp only [iteratedDeriv_zero] at hF0
    have hF' : ContDiffWithinAt ℝ (b' + 1) (fun l => F 0 l) s 0 :=
      hF0.of_le (by exact_mod_cast (by omega : b' + 1 ≤ B))
    exact mixedCoeff_exp_succ_right hs h0 (F := F) hF'

/-- **Mixed Taylor coefficients of `log Z` are joint cumulants**: for `Z` nested-smooth of order `(A, B)` with
`Z(0, 0) > 0` and `0 < a + b`, `a ≤ A`, `b ≤ B`, the coefficient `∂_λ^b ∂_e^a log Z(0, 0)` is the joint cumulant over the
`a + b` derivative slots (slots `< a` are `e`-slots, the others `λ`-slots) of the normalised mixed derivatives
`M(S) = ∂^{(e(S), λ(S))} Z(0, 0) / Z(0, 0)`. -/
theorem mixedCoeff_log_eq_jointCumulant (hs : UniqueDiffOn ℝ s) (h0 : (0 : ℝ) ∈ s) {A B : ℕ}
    {Z : ℝ → ℝ → ℝ} (hZ : NestedSmooth s A B Z) (hpos : 0 < Z 0 0) {a b : ℕ} (ha : a ≤ A) (hb : b ≤ B)
    (hab : 0 < a + b) :
    mixedCoeff s a b (fun e l => Real.log (Z e l)) =
      jointCumulant (fun S : Finset (Fin (a + b)) => mixedCoeff s (eCount a S) (lCount a S) Z / Z 0 0)
        Finset.univ := by
  have hlog := hZ.log h0 hpos
  have hcongr : ∀ i j, mixedCoeff s i j (fun e l => Real.exp (Real.log (Z e l))) = mixedCoeff s i j Z := by
    intro i j
    refine mixedCoeff_congr h0 ?_ i j
    filter_upwards [hZ.eventually_pos hpos] with l hl
    filter_upwards [hl.2] with e he
    exact Real.exp_log he
  have hM : (fun S : Finset (Fin (a + b)) => mixedCoeff s (eCount a S) (lCount a S) Z / Z 0 0) ∅ = 1 := by
    simp only [eCount, lCount, Finset.filter_empty, Finset.card_empty]
    rw [mixedCoeff_zero_zero]
    exact div_self hpos.ne'
  have hK : ∀ S : Finset (Fin (a + b)), ∀ h : S.Nonempty,
      mixedCoeff s (eCount a S) (lCount a S) Z / Z 0 0 = ∑ B ∈ S.powerset.filter (fun B => S.min' h ∈ B),
        mixedCoeff s (eCount a B) (lCount a B) (fun e l => Real.log (Z e l)) *
          (mixedCoeff s (eCount a (S \ B)) (lCount a (S \ B)) Z / Z 0 0) := by
    intro S h
    have hd := mixedCoeff_exp_slot hs h0 hlog ha hb S h
    simp_rw [hcongr] at hd
    rw [hd, Finset.sum_div]
    refine Finset.sum_congr rfl fun B _ => ?_
    ring
  have hne : (Finset.univ : Finset (Fin (a + b))).Nonempty := Finset.univ_nonempty_iff.mpr ⟨⟨0, hab⟩⟩
  have key := eq_jointCumulant_of_decomp
    (fun S : Finset (Fin (a + b)) => mixedCoeff s (eCount a S) (lCount a S) Z / Z 0 0)
    (fun S => mixedCoeff s (eCount a S) (lCount a S) (fun e l => Real.log (Z e l))) hM hK Finset.univ hne
  simp only [eCount_univ, lCount_univ] at key
  exact key

end GaussianBlockSpin
