import GaussianBlockSpin.SlotCumulants

/-! Set partitions of derivative slots and the joint cumulants of partition sums. `partsOf S` are the partitions of a slot
set `S`; partition sums `Σ_{π partition of S} ∏_{B ∈ π} X_B` satisfy the first-slot recursion and are its only solution
(partitionSum_decomp, eq_partitionSum_of_decomp), so the normalised mixed derivatives of `e^F` (`F(0,0) = 0`) are the
partition sums of the mixed derivatives of `F` (mixedCoeff_exp_eq_partitionSum, Faà di Bruno in slot form). The joint
cumulant over slots of partition sums of block moments is the sum over partitions of the joint cumulants of the blocks
(`blockCumulant`, blocks indexed by their smallest slots; jointCumulant_partitionSum_eq), hence
jointCumulant_integral_mixedCoeff_exp. Also: locality of joint cumulants (jointCumulant_congr) and their invariance
under order-preserving relabelling (jointCumulant_map). -/

open MeasureTheory

namespace GaussianBlockSpin

variable {n : ℕ}

/-- `π` is a partition of `S`: nonempty, pairwise disjoint blocks with union `S`. -/
def IsPartOf (S : Finset (Fin n)) (π : Finset (Finset (Fin n))) : Prop :=
  (∀ B ∈ π, B.Nonempty) ∧ (∀ B ∈ π, ∀ B' ∈ π, B ≠ B' → Disjoint B B') ∧ π.biUnion id = S

instance (S : Finset (Fin n)) : DecidablePred (IsPartOf S) := fun π => by
  unfold IsPartOf; infer_instance

/-- The partitions of `S`. -/
def partsOf (S : Finset (Fin n)) : Finset (Finset (Finset (Fin n))) := S.powerset.powerset.filter (IsPartOf S)

lemma mem_partsOf {S : Finset (Fin n)} {π : Finset (Finset (Fin n))} : π ∈ partsOf S ↔ IsPartOf S π := by
  unfold partsOf
  simp only [Finset.mem_filter, Finset.mem_powerset]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨fun B hB => ?_, h⟩
    rw [← h.2.2]
    exact Finset.mem_powerset.mpr (Finset.subset_biUnion_of_mem id hB)

lemma partsOf_empty : partsOf (∅ : Finset (Fin n)) = {∅} := by
  ext π
  rw [mem_partsOf, Finset.mem_singleton]
  constructor
  · rintro ⟨hne, -, hU⟩
    rw [Finset.eq_empty_iff_forall_notMem]
    intro B hB
    obtain ⟨x, hx⟩ := hne B hB
    have : x ∈ π.biUnion id := Finset.mem_biUnion.mpr ⟨B, hB, hx⟩
    rw [hU] at this
    exact Finset.notMem_empty x this
  · rintro rfl
    exact ⟨by simp, by simp, by simp⟩

/-- Splitting a partition into a sub-collection `C` and the rest `D`. -/
lemma isPartOf_union_iff {S : Finset (Fin n)} {C D : Finset (Finset (Fin n))} :
    (IsPartOf S (C ∪ D) ∧ Disjoint C D) ↔
      (IsPartOf (C.biUnion id) C ∧ IsPartOf (S \ C.biUnion id) D ∧ C.biUnion id ⊆ S) := by
  constructor
  · rintro ⟨⟨hne, hdis, hU⟩, hCD⟩
    have hUC : C.biUnion id ⊆ S := by
      rw [← hU]
      exact Finset.biUnion_subset_biUnion_of_subset_left _ Finset.subset_union_left
    refine ⟨⟨fun B hB => hne B (Finset.mem_union_left _ hB),
      fun B hB B' hB' h => hdis B (Finset.mem_union_left _ hB) B' (Finset.mem_union_left _ hB') h, rfl⟩,
      ⟨fun B hB => hne B (Finset.mem_union_right _ hB),
      fun B hB B' hB' h => hdis B (Finset.mem_union_right _ hB) B' (Finset.mem_union_right _ hB') h, ?_⟩, hUC⟩
    ext x
    simp only [Finset.mem_biUnion, id, Finset.mem_sdiff]
    constructor
    · rintro ⟨B, hB, hx⟩
      refine ⟨?_, ?_⟩
      · rw [← hU]
        exact Finset.mem_biUnion.mpr ⟨B, Finset.mem_union_right _ hB, hx⟩
      · rintro ⟨B', hB', hx'⟩
        have hBB' : B ≠ B' := fun h => Finset.disjoint_left.mp hCD hB' (h ▸ hB)
        exact Finset.disjoint_left.mp (hdis B (Finset.mem_union_right _ hB) B' (Finset.mem_union_left _ hB') hBB')
          hx hx'
    · rintro ⟨hxS, hxC⟩
      rw [← hU] at hxS
      obtain ⟨B, hB, hx⟩ := Finset.mem_biUnion.mp hxS
      rcases Finset.mem_union.mp hB with hBC | hBD
      · exact absurd ⟨B, hBC, hx⟩ hxC
      · exact ⟨B, hBD, hx⟩
  · rintro ⟨⟨hneC, hdisC, -⟩, ⟨hneD, hdisD, hUD⟩, hUC⟩
    have hsub : ∀ B ∈ C, B ⊆ C.biUnion id := fun B hB => Finset.subset_biUnion_of_mem id hB
    have hsubD : ∀ B ∈ D, B ⊆ S \ C.biUnion id := fun B hB => by
      rw [← hUD]
      exact Finset.subset_biUnion_of_mem id hB
    have hcross : ∀ B ∈ C, ∀ B' ∈ D, Disjoint B B' := fun B hB B' hB' =>
      Finset.disjoint_of_subset_left (hsub B hB)
        (Finset.disjoint_of_subset_right (hsubD B' hB') Finset.disjoint_sdiff)
    refine ⟨⟨fun B hB => ?_, fun B hB B' hB' h => ?_, ?_⟩, ?_⟩
    · rcases Finset.mem_union.mp hB with hB | hB
      · exact hneC B hB
      · exact hneD B hB
    · rcases Finset.mem_union.mp hB with hB | hB <;> rcases Finset.mem_union.mp hB' with hB' | hB'
      · exact hdisC B hB B' hB' h
      · exact hcross B hB B' hB'
      · exact (hcross B' hB' B hB).symm
      · exact hdisD B hB B' hB' h
    · rw [Finset.union_biUnion, hUD]
      exact Finset.union_sdiff_of_subset hUC
    · rw [Finset.disjoint_left]
      intro B hBC hBD
      obtain ⟨x, hx⟩ := hneC B hBC
      exact Finset.disjoint_left.mp (hcross B hBC B hBD) hx hx

/-- **Splitting partitions along a vertex**: pairs (partition `π` of `S`, sub-collection `C ⊆ π` covering `v`) are
triples (`A ∋ v`, partition `C` of `A`, partition `D` of `S \ A`), with `D = π \ C`. -/
lemma sum_partsOf_split (S : Finset (Fin n)) (v : Fin n)
    (f : Finset (Finset (Fin n)) → Finset (Finset (Fin n)) → ℝ) :
    ∑ π ∈ partsOf S, ∑ C ∈ π.powerset.filter (fun C => v ∈ C.biUnion id), f C (π \ C) =
      ∑ A ∈ S.powerset.filter (fun A => v ∈ A), ∑ C ∈ partsOf A, ∑ D ∈ partsOf (S \ A), f C D := by
  rw [Finset.sum_sigma']
  simp_rw [← Finset.sum_product' (partsOf _) (partsOf _) f]
  rw [Finset.sum_sigma']
  refine Finset.sum_nbij' (fun x => ⟨x.2.biUnion id, (x.2, x.1 \ x.2)⟩) (fun y => ⟨y.2.1 ∪ y.2.2, y.2.1⟩)
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨π, C⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_powerset] at hx
    obtain ⟨hπ, hCπ, hv⟩ := hx
    have hsplit := isPartOf_union_iff.mp ⟨(Finset.union_sdiff_of_subset hCπ).symm ▸ mem_partsOf.mp hπ,
      Finset.disjoint_sdiff⟩
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_powerset, Finset.mem_product]
    exact ⟨⟨hsplit.2.2, hv⟩, mem_partsOf.mpr hsplit.1, mem_partsOf.mpr hsplit.2.1⟩
  · rintro ⟨A, C, D⟩ hy
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_powerset,
      Finset.mem_product] at hy
    obtain ⟨⟨hAS, hvA⟩, hC, hD⟩ := hy
    have hCA := (mem_partsOf.mp hC).2.2
    have hC' : IsPartOf (C.biUnion id) C := by rw [hCA]; exact mem_partsOf.mp hC
    have hD' : IsPartOf (S \ C.biUnion id) D := by rw [hCA]; exact mem_partsOf.mp hD
    have hU := isPartOf_union_iff.mpr ⟨hC', hD', hCA ▸ hAS⟩
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨mem_partsOf.mpr hU.1, Finset.subset_union_left, hCA ▸ hvA⟩
  · rintro ⟨π, C⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_powerset] at hx
    simp only [Finset.union_sdiff_of_subset hx.2.1]
  · rintro ⟨A, C, D⟩ hy
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_powerset,
      Finset.mem_product] at hy
    obtain ⟨⟨hAS, hvA⟩, hC, hD⟩ := hy
    have hCA := (mem_partsOf.mp hC).2.2
    have hC' : IsPartOf (C.biUnion id) C := by rw [hCA]; exact mem_partsOf.mp hC
    have hD' : IsPartOf (S \ C.biUnion id) D := by rw [hCA]; exact mem_partsOf.mp hD
    have hU := isPartOf_union_iff.mpr ⟨hC', hD', hCA ▸ hAS⟩
    simp only [hCA, Finset.union_sdiff_cancel_left hU.2]
  · rintro ⟨π, C⟩ _
    rfl

/-- **Joint cumulants of partition sums**: let `P(π)` (for collections `π` of blocks, `P(∅) = 1`; the moment
`⟨∏_{B ∈ π} X_B⟩` of the block variables) satisfy the first-block moment-cumulant relation with block cumulants `κ`:
for every partition `π` of a nonempty `T`, `P(π) = Σ_{C ⊆ π covering min T} κ(C) P(π \ C)`. Then the joint cumulant over
slots of the partition sums `M(T) = Σ_{π partition of T} P(π)` is `κ_M(S) = Σ_{π partition of S} κ(π)`. -/
theorem jointCumulant_partitionSum (P κ : Finset (Finset (Fin n)) → ℝ) (hP0 : P ∅ = 1)
    (hdec : ∀ T : Finset (Fin n), ∀ h : T.Nonempty, ∀ π ∈ partsOf T,
      P π = ∑ C ∈ π.powerset.filter (fun C => T.min' h ∈ C.biUnion id), κ C * P (π \ C))
    (S : Finset (Fin n)) (h : S.Nonempty) :
    jointCumulant (fun T => ∑ π ∈ partsOf T, P π) S = ∑ π ∈ partsOf S, κ π := by
  refine (eq_jointCumulant_of_decomp (fun T => ∑ π ∈ partsOf T, P π) (fun A => ∑ π ∈ partsOf A, κ π)
    (by simp [partsOf_empty, hP0]) (fun T hT => ?_) S h).symm
  rw [Finset.sum_congr rfl (hdec T hT), sum_partsOf_split T (T.min' hT) (fun C D => κ C * P D)]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [Finset.sum_mul_sum]

/-- **Locality**: the joint cumulant of `S` depends only on the moments of the subsets of `S`. -/
theorem jointCumulant_congr {M M' : Finset (Fin n) → ℝ} (S : Finset (Fin n)) (h : ∀ T ⊆ S, M T = M' T) :
    jointCumulant M S = jointCumulant M' S := by
  induction hc : S.card using Nat.strong_induction_on generalizing S with
  | _ c ih =>
    by_cases hS : S.Nonempty
    · rw [jointCumulant_of_nonempty M hS, jointCumulant_of_nonempty M' hS, h S subset_rfl]
      congr 1
      refine Finset.sum_congr rfl fun B hB => ?_
      have hBS : B ⊆ S := Finset.mem_powerset.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hB).1).1
      rw [ih B.card (hc ▸ card_lt_of_mem_proper (Finset.mem_filter.mp hB).1) B
        (fun T hT => h T (hT.trans hBS)) rfl, h (S \ B) Finset.sdiff_subset]
    · rw [Finset.not_nonempty_iff_eq_empty.mp hS]
      simp [jointCumulant]

/-- The smallest slot of a block (`d` for the empty block, which never occurs in a partition). -/
def bmin (d : Fin n) (B : Finset (Fin n)) : Fin n := if h : B.Nonempty then B.min' h else d

lemma bmin_of_nonempty (d : Fin n) {B : Finset (Fin n)} (h : B.Nonempty) : bmin d B = B.min' h := by
  simp [bmin, h]

lemma bmin_mem (d : Fin n) {B : Finset (Fin n)} (h : B.Nonempty) : bmin d B ∈ B := by
  rw [bmin_of_nonempty d h]
  exact B.min'_mem h

/-- The smallest slots of the blocks of a partition are distinct. -/
lemma bmin_injOn {S : Finset (Fin n)} {π : Finset (Finset (Fin n))} (hπ : IsPartOf S π) (d : Fin n) :
    Set.InjOn (bmin d) π := by
  intro B hB B' hB' h
  by_contra hne
  have h1 := bmin_mem d (hπ.1 B hB)
  have h2 := bmin_mem d (hπ.1 B' hB')
  rw [h] at h1
  exact Finset.disjoint_left.mp (hπ.2.1 B hB B' hB' hne) h1 h2

/-- A sub-collection of a partition is determined by the smallest slots of its blocks. -/
lemma image_bmin_injOn {S : Finset (Fin n)} {π : Finset (Finset (Fin n))} (hπ : IsPartOf S π) (d : Fin n) :
    Set.InjOn (fun C : Finset (Finset (Fin n)) => C.image (bmin d)) (π.powerset : Set (Finset (Finset (Fin n)))) := by
  intro C1 h1 C2 h2 h
  have h1' := Finset.mem_powerset.mp (Finset.mem_coe.mp h1)
  have h2' := Finset.mem_powerset.mp (Finset.mem_coe.mp h2)
  simp only at h
  have key : ∀ C C' : Finset (Finset (Fin n)), C ⊆ π → C' ⊆ π → C.image (bmin d) = C'.image (bmin d) → C ⊆ C' := by
    intro C C' hC hC' hCC' B hB
    have : bmin d B ∈ C'.image (bmin d) := hCC' ▸ Finset.mem_image_of_mem _ hB
    obtain ⟨B', hB', hBB'⟩ := Finset.mem_image.mp this
    rw [← bmin_injOn hπ d (hC' hB') (hC hB) hBB']
    exact hB'
  exact Finset.Subset.antisymm (key C1 C2 h1' h2' h) (key C2 C1 h2' h1' h.symm)

/-- The block moment function of a collection `C`: `R ↦ E(the blocks of C whose smallest slot is in R)`. -/
def blockMoment (E : Finset (Finset (Fin n)) → ℝ) (d : Fin n) (C : Finset (Finset (Fin n))) (R : Finset (Fin n)) :
    ℝ :=
  E (C.filter fun B => bmin d B ∈ R)

/-- **The joint cumulant of the blocks of `C`** for the block moments `E` (`E(C) = ⟨∏_{B ∈ C} X_B⟩`), the blocks indexed
by their smallest slots. -/
noncomputable def blockCumulant (E : Finset (Finset (Fin n)) → ℝ) (d : Fin n) (C : Finset (Finset (Fin n))) : ℝ :=
  jointCumulant (blockMoment E d C) (C.image (bmin d))

/-- The smallest slot of `T` is the smallest of the smallest slots of the blocks of a partition of `T`. -/
lemma min'_image_bmin {T : Finset (Fin n)} (h : T.Nonempty) {π : Finset (Finset (Fin n))} (hπ : IsPartOf T π)
    (d : Fin n) (hV : (π.image (bmin d)).Nonempty) : (π.image (bmin d)).min' hV = T.min' h := by
  have hmem : T.min' h ∈ π.biUnion id := hπ.2.2.symm ▸ T.min'_mem h
  obtain ⟨B0, hB0, hm⟩ := Finset.mem_biUnion.mp hmem
  have hB0T : B0 ⊆ T := hπ.2.2 ▸ Finset.subset_biUnion_of_mem id hB0
  have hb0 : bmin d B0 = T.min' h := by
    rw [bmin_of_nonempty d (hπ.1 B0 hB0)]
    exact le_antisymm (B0.min'_le _ hm) (T.min'_le _ (hB0T (B0.min'_mem _)))
  refine le_antisymm (hb0 ▸ (π.image (bmin d)).min'_le _ (Finset.mem_image_of_mem _ hB0)) ?_
  refine Finset.le_min' _ _ _ fun y hy => ?_
  obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hy
  have hBT : B ⊆ T := hπ.2.2 ▸ Finset.subset_biUnion_of_mem id hB
  exact T.min'_le _ (hBT (bmin_mem d (hπ.1 B hB)))

/-- **First-block moment-cumulant relation**: for block moments `E` (`E ∅ = 1`) and a partition `π` of a nonempty `T`,
`E(π) = Σ_{C ⊆ π covering min T} κ(C) E(π \ C)` with `κ = blockCumulant`. -/
theorem blockMoment_decomp (E : Finset (Finset (Fin n)) → ℝ) (hE : E ∅ = 1) (d : Fin n)
    {T : Finset (Fin n)} (h : T.Nonempty) {π : Finset (Finset (Fin n))} (hπ : π ∈ partsOf T) :
    E π = ∑ C ∈ π.powerset.filter (fun C => T.min' h ∈ C.biUnion id), blockCumulant E d C * E (π \ C) := by
  have hπ' := mem_partsOf.mp hπ
  have hinj := bmin_injOn hπ' d
  set V := π.image (bmin d) with hVdef
  have hπne : π.Nonempty := by
    obtain ⟨x, hx⟩ := h
    rw [← hπ'.2.2] at hx
    obtain ⟨B, hB, -⟩ := Finset.mem_biUnion.mp hx
    exact ⟨B, hB⟩
  have hV : V.Nonempty := hπne.image _
  have hN0 : blockMoment E d π ∅ = 1 := by
    simp [blockMoment, hE]
  have hdec := moment_eq_sum_jointCumulant (blockMoment E d π) hN0 hV
  have hNV : blockMoment E d π V = E π := by
    unfold blockMoment
    rw [Finset.filter_true_of_mem fun B hB => Finset.mem_image_of_mem _ hB]
  rw [hNV] at hdec
  rw [hdec, min'_image_bmin h hπ' d hV]
  -- reindex `R ⊆ V` by sub-collections `C ⊆ π`
  have hidx : V.powerset.filter (fun R => T.min' h ∈ R) =
      (π.powerset.filter (fun C => T.min' h ∈ C.biUnion id)).image (fun C => C.image (bmin d)) := by
    have hmem : T.min' h ∈ π.biUnion id := hπ'.2.2.symm ▸ T.min'_mem h
    obtain ⟨B0, hB0, hm⟩ := Finset.mem_biUnion.mp hmem
    have hb0 : bmin d B0 = T.min' h := by
      have hB0T : B0 ⊆ T := hπ'.2.2 ▸ Finset.subset_biUnion_of_mem id hB0
      rw [bmin_of_nonempty d (hπ'.1 B0 hB0)]
      exact le_antisymm (B0.min'_le _ hm) (T.min'_le _ (hB0T (B0.min'_mem _)))
    have hcov : ∀ C ⊆ π, (T.min' h ∈ C.biUnion id ↔ T.min' h ∈ C.image (bmin d)) := by
      intro C hC
      constructor
      · intro hc
        obtain ⟨B, hB, hmB⟩ := Finset.mem_biUnion.mp hc
        have : B = B0 := by
          by_contra hne
          exact Finset.disjoint_left.mp (hπ'.2.1 B (hC hB) B0 hB0 hne) hmB hm
        subst this
        exact hb0 ▸ Finset.mem_image_of_mem _ hB
      · intro hc
        obtain ⟨B, hB, hBm⟩ := Finset.mem_image.mp hc
        have : B = B0 := hinj (hC hB) hB0 (hBm.trans hb0.symm)
        subst this
        exact Finset.mem_biUnion.mpr ⟨B, hB, hm⟩
    ext R
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_image]
    constructor
    · rintro ⟨hRV, hTR⟩
      refine ⟨π.filter (fun B => bmin d B ∈ R), ⟨Finset.filter_subset _ _, ?_⟩, ?_⟩
      · have hR : (π.filter (fun B => bmin d B ∈ R)).image (bmin d) = R := by
          ext y
          simp only [Finset.mem_image, Finset.mem_filter]
          constructor
          · rintro ⟨B, ⟨_, hB⟩, rfl⟩
            exact hB
          · intro hy
            obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp (hRV hy)
            exact ⟨B, ⟨hB, hy⟩, rfl⟩
        rw [hcov _ (Finset.filter_subset _ _), hR]
        exact hTR
      · ext y
        simp only [Finset.mem_image, Finset.mem_filter]
        constructor
        · rintro ⟨B, ⟨_, hB⟩, rfl⟩
          exact hB
        · intro hy
          obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp (hRV hy)
          exact ⟨B, ⟨hB, hy⟩, rfl⟩
    · rintro ⟨C, ⟨hCπ, hTC⟩, rfl⟩
      exact ⟨Finset.image_subset_image hCπ, (hcov C hCπ).mp hTC⟩
  rw [hidx, Finset.sum_image]
  · refine Finset.sum_congr rfl fun C hC => ?_
    have hCπ := Finset.mem_powerset.mp (Finset.mem_filter.mp hC).1
    congr 1
    · unfold blockCumulant
      refine jointCumulant_congr _ fun R hR => ?_
      unfold blockMoment
      congr 1
      ext B
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hB, hBR⟩
        obtain ⟨B', hB', hBB'⟩ := Finset.mem_image.mp (hR hBR)
        rw [← hinj (hCπ hB') hB hBB']
        exact ⟨hB', hBB' ▸ hBR⟩
      · rintro ⟨hB, hBR⟩
        exact ⟨hCπ hB, hBR⟩
    · unfold blockMoment
      congr 1
      ext B
      simp only [Finset.mem_filter, Finset.mem_sdiff, hVdef, Finset.mem_image]
      constructor
      · rintro ⟨hB, -, hBC⟩
        exact ⟨hB, fun hBC' => hBC ⟨B, hBC', rfl⟩⟩
      · rintro ⟨hB, hBC⟩
        refine ⟨hB, ⟨B, hB, rfl⟩, ?_⟩
        rintro ⟨B', hB', hBB'⟩
        exact hBC (hinj (hCπ hB') hB hBB' ▸ hB')
  · intro C1 h1 C2 h2 heq
    exact image_bmin_injOn hπ' d (Finset.mem_coe.mpr (Finset.mem_filter.mp (Finset.mem_coe.mp h1)).1)
      (Finset.mem_coe.mpr (Finset.mem_filter.mp (Finset.mem_coe.mp h2)).1) heq

/-- **Joint cumulants of partition sums are sums of block cumulants**: for block moments `E` with `E ∅ = 1`
(`E(C) = ⟨∏_{B ∈ C} X_B⟩`), the slot moments `M(T) = Σ_{π partition of T} E(π)` (the derivatives `∂^T e^F / e^F` when
`X_B = ∂^B F`) have joint cumulants `κ_M(S) = Σ_{π partition of S} κ(X_B : B ∈ π)`. -/
theorem jointCumulant_partitionSum_eq (E : Finset (Finset (Fin n)) → ℝ) (hE : E ∅ = 1) (d : Fin n)
    (S : Finset (Fin n)) (h : S.Nonempty) :
    jointCumulant (fun T => ∑ π ∈ partsOf T, E π) S = ∑ π ∈ partsOf S, blockCumulant E d π :=
  jointCumulant_partitionSum E (blockCumulant E d) hE (fun _ hT _ hπ => blockMoment_decomp E hE d hT hπ) S h

/-- In a partition of `S`, the only sub-collection with one block that covers `v ∈ S` is the block of `v`. -/
lemma sum_filter_card_one_partsOf {S : Finset (Fin n)} {π : Finset (Finset (Fin n))} (hπ : IsPartOf S π)
    {v : Fin n} (hv : v ∈ S) (g : Finset (Finset (Fin n)) → ℝ) :
    ∃ B0 ∈ π, v ∈ B0 ∧ ∑ C ∈ π.powerset.filter (fun C => v ∈ C.biUnion id), (if C.card = 1 then g C else 0) =
      g {B0} := by
  have hmem : v ∈ π.biUnion id := hπ.2.2.symm ▸ hv
  obtain ⟨B0, hB0, hm⟩ := Finset.mem_biUnion.mp hmem
  refine ⟨B0, hB0, hm, ?_⟩
  rw [Finset.sum_eq_single_of_mem {B0}]
  · simp
  · simp only [Finset.mem_filter, Finset.mem_powerset, Finset.singleton_subset_iff]
    exact ⟨hB0, by simpa using hm⟩
  · intro C hC hne
    obtain ⟨hCπ, hvC⟩ := Finset.mem_filter.mp hC
    split_ifs with hc
    · exfalso
      obtain ⟨B, rfl⟩ := Finset.card_eq_one.mp hc
      apply hne
      have hvB : v ∈ B := by simpa using hvC
      have hBπ : B ∈ π := Finset.mem_powerset.mp hCπ (Finset.mem_singleton_self B)
      by_contra hBB0
      exact Finset.disjoint_left.mp (hπ.2.1 B hBπ B0 hB0 (fun h => hBB0 (h ▸ rfl))) hvB hm
    · rfl

/-- The only partition of a nonempty `A` with one block is `{A}`. -/
lemma sum_partsOf_card_one {A : Finset (Fin n)} (hA : A.Nonempty) (g : Finset (Finset (Fin n)) → ℝ) :
    ∑ C ∈ partsOf A, (if C.card = 1 then g C else 0) = g {A} := by
  rw [Finset.sum_eq_single_of_mem {A}]
  · simp
  · rw [mem_partsOf]
    exact ⟨by simpa using hA, by simp, by simp⟩
  · intro C hC hne
    split_ifs with hc
    · exfalso
      obtain ⟨B, rfl⟩ := Finset.card_eq_one.mp hc
      apply hne
      have := (mem_partsOf.mp hC).2.2
      simp only [Finset.singleton_biUnion, id] at this
      rw [this]
    · rfl

/-- **Partition sums satisfy the first-slot recursion**:
`Σ_{π partition of S} ∏_{B ∈ π} X_B = Σ_{A ⊆ S, v ∈ A} X_A Σ_{π partition of S \ A} ∏_{B ∈ π} X_B` for `v ∈ S`. -/
theorem partitionSum_decomp (X : Finset (Fin n) → ℝ) {S : Finset (Fin n)} {v : Fin n} (hv : v ∈ S) :
    ∑ π ∈ partsOf S, ∏ B ∈ π, X B =
      ∑ A ∈ S.powerset.filter (fun A => v ∈ A), X A * ∑ π ∈ partsOf (S \ A), ∏ B ∈ π, X B := by
  have hsplit := sum_partsOf_split S v
    (fun C D => if C.card = 1 then (∏ B ∈ C, X B) * ∏ B ∈ D, X B else 0)
  have hL : ∀ π ∈ partsOf S, ∑ C ∈ π.powerset.filter (fun C => v ∈ C.biUnion id),
      (if C.card = 1 then (∏ B ∈ C, X B) * ∏ B ∈ π \ C, X B else 0) = ∏ B ∈ π, X B := by
    intro π hπ
    obtain ⟨B0, hB0, -, hs⟩ := sum_filter_card_one_partsOf (mem_partsOf.mp hπ) hv
      (fun C => (∏ B ∈ C, X B) * ∏ B ∈ π \ C, X B)
    rw [hs, Finset.prod_singleton, Finset.sdiff_singleton_eq_erase, Finset.mul_prod_erase π X hB0]
  rw [Finset.sum_congr rfl hL] at hsplit
  rw [hsplit]
  refine Finset.sum_congr rfl fun A hA => ?_
  have hAne : A.Nonempty := ⟨v, (Finset.mem_filter.mp hA).2⟩
  rw [Finset.sum_comm]
  have hR := sum_partsOf_card_one hAne (fun C => ∑ D ∈ partsOf (S \ A), (∏ B ∈ C, X B) * ∏ B ∈ D, X B)
  rw [Finset.prod_singleton, ← Finset.mul_sum] at hR
  rw [← hR, Finset.sum_comm]
  refine Finset.sum_congr rfl fun C _ => ?_
  split_ifs <;> simp

/-- **Uniqueness**: a function `Y` with `Y ∅ = 1` satisfying the first-slot recursion
`Y(S) = Σ_{B ⊆ S, min S ∈ B} X_B Y(S \ B)` is the partition sum `Σ_{π partition of S} ∏_{B ∈ π} X_B`. -/
theorem eq_partitionSum_of_decomp (X Y : Finset (Fin n) → ℝ) (hY0 : Y ∅ = 1)
    (hY : ∀ S : Finset (Fin n), ∀ h : S.Nonempty,
      Y S = ∑ B ∈ S.powerset.filter (fun B => S.min' h ∈ B), X B * Y (S \ B))
    (S : Finset (Fin n)) : Y S = ∑ π ∈ partsOf S, ∏ B ∈ π, X B := by
  induction hc : S.card using Nat.strong_induction_on generalizing S with
  | _ c ih =>
    by_cases h : S.Nonempty
    · rw [hY S h, partitionSum_decomp X (S.min'_mem h)]
      refine Finset.sum_congr rfl fun B hB => ?_
      have hBS := Finset.mem_powerset.mp (Finset.mem_filter.mp hB).1
      have hvB := (Finset.mem_filter.mp hB).2
      rw [ih (S \ B).card (by
        rw [← hc, Finset.card_sdiff_of_subset hBS]
        have : 0 < B.card := Finset.card_pos.mpr ⟨_, hvB⟩
        have : B.card ≤ S.card := Finset.card_le_card hBS
        omega) (S \ B) rfl]
    · rw [Finset.not_nonempty_iff_eq_empty.mp h, hY0, partsOf_empty]
      simp

section Integrals

variable {s : Set ℝ}

/-- **Faà di Bruno in slot form**: the mixed derivatives of `e^F` (`F(0, 0) = 0`) are the partition sums of the mixed
derivatives of `F`: `∂^S e^F (0, 0) = Σ_{π partition of S} ∏_{B ∈ π} ∂^B F (0, 0)`. -/
theorem mixedCoeff_exp_eq_partitionSum (hs : UniqueDiffOn ℝ s) (h0 : (0 : ℝ) ∈ s) {A B : ℕ} {F : ℝ → ℝ → ℝ}
    (hF : NestedSmooth s A B F) (hF0 : F 0 0 = 0) {a b : ℕ} (ha : a ≤ A) (hb : b ≤ B) (S : Finset (Fin (a + b))) :
    mixedCoeff s (eCount a S) (lCount a S) (fun e l => Real.exp (F e l)) =
      ∑ π ∈ partsOf S, ∏ C ∈ π, mixedCoeff s (eCount a C) (lCount a C) F := by
  refine eq_partitionSum_of_decomp (fun C => mixedCoeff s (eCount a C) (lCount a C) F)
    (fun S => mixedCoeff s (eCount a S) (lCount a S) (fun e l => Real.exp (F e l))) ?_
    (fun S h => mixedCoeff_exp_slot hs h0 hF ha hb S h) S
  simp only [eCount, lCount, Finset.filter_empty, Finset.card_empty]
  rw [mixedCoeff_zero_zero, hF0, Real.exp_zero]

/-- **Joint cumulants of the integrated mixed derivatives of `e^F`**: for a probability measure `ν`, `F_x` nested-smooth
with `F_x(0, 0) = 0`, and the block variables `X_C(x) = ∂^C F_x (0, 0)` with integrable products over the blocks of every
partition of every slot set, the joint cumulant over the `a + b` slots of `M(S) = ∫ ∂^S e^{F_x} (0, 0) dν(x)` is the sum
over the partitions `π` of the slots of the joint cumulants of the blocks `(X_C)_{C ∈ π}` (`blockCumulant`). -/
theorem jointCumulant_integral_mixedCoeff_exp {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
    [IsProbabilityMeasure ν] (hs : UniqueDiffOn ℝ s) (h0 : (0 : ℝ) ∈ s) {A B : ℕ} (F : Ω → ℝ → ℝ → ℝ)
    (hF : ∀ x, NestedSmooth s A B (F x)) (hF0 : ∀ x, F x 0 0 = 0) {a b : ℕ} (ha : a ≤ A) (hb : b ≤ B)
    (hint : ∀ S : Finset (Fin (a + b)), ∀ π ∈ partsOf S,
      Integrable (fun x => ∏ C ∈ π, mixedCoeff s (eCount a C) (lCount a C) (F x)) ν)
    (d : Fin (a + b)) (hab : 0 < a + b) :
    jointCumulant (fun S : Finset (Fin (a + b)) =>
        ∫ x, mixedCoeff s (eCount a S) (lCount a S) (fun e l => Real.exp (F x e l)) ∂ν) Finset.univ =
      ∑ π ∈ partsOf Finset.univ, blockCumulant
        (fun π' => ∫ x, ∏ C ∈ π', mixedCoeff s (eCount a C) (lCount a C) (F x) ∂ν) d π := by
  have hM : (fun S : Finset (Fin (a + b)) =>
      ∫ x, mixedCoeff s (eCount a S) (lCount a S) (fun e l => Real.exp (F x e l)) ∂ν) =
      fun S => ∑ π ∈ partsOf S, ∫ x, ∏ C ∈ π, mixedCoeff s (eCount a C) (lCount a C) (F x) ∂ν := by
    funext S
    simp_rw [mixedCoeff_exp_eq_partitionSum hs h0 (hF _) (hF0 _) ha hb S]
    exact integral_finsetSum _ fun π hπ => hint S π hπ
  rw [hM]
  exact jointCumulant_partitionSum_eq _ (by simp) d Finset.univ (Finset.univ_nonempty_iff.mpr ⟨⟨0, hab⟩⟩)

end Integrals

section Relabelling

variable {r : ℕ}

lemma min'_map_orderEmbedding (f : Fin r ↪o Fin n) {S : Finset (Fin r)} (h : S.Nonempty) :
    (S.map f.toEmbedding).min' (h.map) = f (S.min' h) := by
  refine le_antisymm ((S.map f.toEmbedding).min'_le _ (Finset.mem_map_of_mem _ (S.min'_mem h))) ?_
  refine Finset.le_min' _ _ _ fun y hy => ?_
  obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hy
  exact f.monotone (S.min'_le x hx)

/-- **Joint cumulants are invariant under order-preserving relabelling of the vertices**: for an order embedding
`f : Fin r ↪o Fin n`, `κ_M(f(S)) = κ_{M ∘ f}(S)`. -/
theorem jointCumulant_map (f : Fin r ↪o Fin n) (M : Finset (Fin n) → ℝ) (hM : M ∅ = 1) (S : Finset (Fin r))
    (h : S.Nonempty) :
    jointCumulant M (S.map f.toEmbedding) = jointCumulant (fun R => M (R.map f.toEmbedding)) S := by
  refine eq_jointCumulant_of_decomp (fun R => M (R.map f.toEmbedding))
    (fun R => jointCumulant M (R.map f.toEmbedding)) (by simp [hM]) (fun S h => ?_) S h
  rw [moment_eq_sum_jointCumulant M hM h.map, min'_map_orderEmbedding f h]
  have himg : (S.map f.toEmbedding).powerset.filter (fun B => f (S.min' h) ∈ B) =
      (S.powerset.filter (fun B => S.min' h ∈ B)).map (Finset.mapEmbedding f.toEmbedding).toEmbedding := by
    ext B
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_map, Finset.mapEmbedding_apply,
      RelEmbedding.coe_toEmbedding]
    constructor
    · rintro ⟨hB, hv⟩
      refine ⟨B.preimage f f.injective.injOn, ⟨?_, ?_⟩, ?_⟩
      · intro x hx
        rw [Finset.mem_preimage] at hx
        obtain ⟨y, hy, hyx⟩ := Finset.mem_map.mp (hB hx)
        rw [← f.injective hyx]
        exact hy
      · rw [Finset.mem_preimage]
        exact hv
      · ext y
        simp only [Finset.mem_map, Finset.mem_preimage, RelEmbedding.coe_toEmbedding]
        constructor
        · rintro ⟨x, hx, rfl⟩
          exact hx
        · intro hy
          obtain ⟨x, -, rfl⟩ := Finset.mem_map.mp (hB hy)
          exact ⟨x, hy, rfl⟩
    · rintro ⟨B', ⟨hB', hv⟩, rfl⟩
      exact ⟨Finset.map_subset_map.mpr hB', Finset.mem_map_of_mem _ hv⟩
  rw [himg, Finset.sum_map]
  refine Finset.sum_congr rfl fun B _ => ?_
  simp only [Finset.mapEmbedding_apply, RelEmbedding.coe_toEmbedding]
  rw [Finset.map_sdiff]

end Relabelling

end GaussianBlockSpin
