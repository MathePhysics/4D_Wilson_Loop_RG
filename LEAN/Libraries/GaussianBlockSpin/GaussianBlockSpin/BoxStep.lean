import GaussianBlockSpin.BoxMoments

/-! The data of one decoupling step of the cumulant expansion (the box step of [2], Sect. 5, for independent
coordinates) and its exact identities.
* LocalPieces: bounded measurable local functions `h_X` (`X : P`), each depending on the coordinates `supp X`.
* Pavement: corridors `Γ`, pairwise disjoint boxes off `Γ`, and the home box of every piece (`none`: inside `Γ`;
  `some b`: inside box `b` and `Γ`).
* IsDeep: a piece is deep if every tuple of at most `t` pieces containing it has a part around it that avoids `Γ`,
  stays in its box and does not meet the rest of the tuple off `Γ` (for pieces of diameter `R` this holds at distance
  `> t R` from `Γ`).
* box_truncExp_split: in box `b`, with the corridor coordinates fixed at `x`, the truncated expectation of order
  `1 ≤ k ≤ t` of the box sum is the unconditional one of the interior pieces plus the box one of the non-deep pieces
  minus the unconditional one of the shallow pieces.
* truncExp_sub_eq_sum_boxes: unconditionally, removing the deep pieces changes the truncated expectation of order
  `1 ≤ k ≤ t` of the full sum by the sum over the boxes of the corresponding changes of the interior sums. -/

namespace GaussianBlockSpin

open MeasureTheory Function

/-- Bounded measurable local functions on `ι → ℝ`. -/
structure LocalPieces (ι P : Type*) where
  supp : P → Finset ι
  h : P → (ι → ℝ) → ℝ
  a : P → ℝ
  loc : ∀ X, DependsOn (h X) (supp X : Set ι)
  meas : ∀ X, Measurable (h X)
  bdd : ∀ X ω, |h X ω| ≤ a X

/-- Corridors, boxes and the home box of every piece. -/
structure Pavement {ι P : Type*} (L : LocalPieces ι P) (β : Type*) where
  Γ : Finset ι
  box : β → Finset ι
  disj : ∀ b b', b ≠ b' → Disjoint (box b) (box b')
  disjΓ : ∀ b, Disjoint (box b) Γ
  home : P → Option β
  homeNone : ∀ X, home X = none → L.supp X ⊆ Γ
  homeSome : ∀ X b, home X = some b → (L.supp X : Set ι) ⊆ (box b : Set ι) ∪ (Γ : Set ι)

variable {ι P β : Type*} [Fintype ι] [DecidableEq ι] [Fintype P] [DecidableEq P] [Fintype β] [DecidableEq β]
variable {L : LocalPieces ι P} (pv : Pavement L β)

/-- The pieces of box `b`. -/
def Pavement.pieces (b : β) : Finset P := Finset.univ.filter fun X => pv.home X = some b

/-- The interior pieces of box `b` (not meeting the corridors). -/
def Pavement.interior (b : β) : Finset P := (pv.pieces b).filter fun X => Disjoint (L.supp X) pv.Γ

/-- **Deep pieces**: in a box, off the corridors, and every tuple of at most `t` pieces containing the piece has a
part `C` around it whose pieces avoid `Γ` and stay in its box, and whose coordinates miss those of the other pieces off
`Γ`. -/
def Pavement.IsDeep (t : ℕ) (X : P) : Prop :=
  (∃ b, pv.home X = some b) ∧ Disjoint (L.supp X) pv.Γ ∧
    ∀ k ≤ t, ∀ g : Fin k → P, ∀ i₀, g i₀ = X → ∃ C : Finset (Fin k), i₀ ∈ C ∧
      (∀ i ∈ C, Disjoint (L.supp (g i)) pv.Γ ∧ pv.home (g i) = pv.home X) ∧
      Disjoint (C.biUnion fun i => L.supp (g i)) ((Finset.univ \ C).biUnion fun i => L.supp (g i) \ pv.Γ)

/-- The sum of the pieces of `s`. -/
def LocalPieces.sum (L : LocalPieces ι P) (s : Finset P) (ω : ι → ℝ) : ℝ := ∑ X ∈ s, L.h X ω

/-- The sum of the pieces of `s` in box `b`, the other coordinates fixed at `x`. -/
def Pavement.boxSum (b : β) (x : ι → ℝ) (s : Finset P) (y : pv.box b → ℝ) : ℝ :=
  ∑ X ∈ s, L.h X (updateFinset x (pv.box b) y)

/-- The box measure. -/
noncomputable def boxMeasure (ν₁ : ι → Measure ℝ) (s : Finset ι) : Measure (s → ℝ) := Measure.pi fun i : s => ν₁ i

variable (ν₁ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (ν₁ i)]

instance (s : Finset ι) : IsProbabilityMeasure (boxMeasure ν₁ s) := by
  unfold boxMeasure; infer_instance

omit [Fintype ι] [Fintype P] [DecidableEq P] [Fintype β] [DecidableEq β] [∀ i, IsProbabilityMeasure (ν₁ i)] in
/-- A piece of box `b` with the other coordinates fixed depends only on the box coordinates of its support. -/
lemma Pavement.dependsOn_update (b : β) (x : ι → ℝ) (X : P) :
    DependsOn (fun y : pv.box b → ℝ => L.h X (updateFinset x (pv.box b) y))
      (((L.supp X).subtype (· ∈ pv.box b) : Finset (pv.box b)) : Set (pv.box b)) := by
  intro y y' hyy
  refine L.loc X fun i hi => ?_
  by_cases hib : i ∈ pv.box b
  · simp only [updateFinset_def, hib, ↓reduceDIte]
    exact hyy ⟨i, hib⟩ (by simp [Finset.mem_subtype, Finset.mem_coe.mp hi])
  · simp [updateFinset_def, hib]

omit [Fintype ι] [Fintype P] [DecidableEq P] [Fintype β] [DecidableEq β] [∀ i, IsProbabilityMeasure (ν₁ i)] in
lemma Pavement.measurable_update (b : β) (x : ι → ℝ) (X : P) :
    Measurable (fun y : pv.box b → ℝ => L.h X (updateFinset x (pv.box b) y)) :=
  (L.meas X).comp measurable_updateFinset

omit [Fintype ι] [Fintype P] [DecidableEq P] [Fintype β] [DecidableEq β] in
/-- **Box cumulants of a tuple with a deep and a boundary piece vanish** (with the corridor coordinates fixed). -/
lemma Pavement.box_jointCumulant_deep_bd_eq_zero (t : ℕ) (b : β) (x : ι → ℝ) {k : ℕ} (hk : k ≤ t) (g : Fin k → P)
    {i₀ j : Fin k} (hi₀ : pv.IsDeep t (g i₀))
    (hj : ¬ Disjoint (L.supp (g j)) pv.Γ) :
    jointCumulant (fun T => ∫ y, ∏ i ∈ T, L.h (g i) (updateFinset x (pv.box b) y) ∂(boxMeasure ν₁ (pv.box b)))
      Finset.univ = 0 := by
  obtain ⟨-, -, hdeep⟩ := hi₀
  obtain ⟨C, hC0, hCin, hCdisj⟩ := hdeep k hk g i₀ rfl
  have hjC : j ∉ C := fun h => hj (hCin j h).1
  refine jointCumulant_local_eq_zero (fun i : pv.box b => ν₁ i)
    (fun i y => L.h (g i) (updateFinset x (pv.box b) y))
    (fun i => (L.supp (g i)).subtype (· ∈ pv.box b)) (fun i => pv.dependsOn_update b x (g i))
    (fun i => pv.measurable_update b x (g i)) (Finset.subset_univ C) ⟨i₀, hC0⟩ ⟨j, by simp [hjC]⟩ ?_
  rw [Finset.disjoint_left]
  intro z hz1 hz2
  obtain ⟨i, hi, hzi⟩ := Finset.mem_biUnion.mp hz1
  obtain ⟨i', hi', hzi'⟩ := Finset.mem_biUnion.mp hz2
  have h1 : (z : ι) ∈ C.biUnion fun i => L.supp (g i) :=
    Finset.mem_biUnion.mpr ⟨i, hi, (Finset.mem_subtype.mp hzi)⟩
  have hzΓ : (z : ι) ∉ pv.Γ := Finset.disjoint_left.mp (pv.disjΓ b) z.2
  have h2 : (z : ι) ∈ (Finset.univ \ C).biUnion fun i => L.supp (g i) \ pv.Γ :=
    Finset.mem_biUnion.mpr ⟨i', hi', Finset.mem_sdiff.mpr ⟨Finset.mem_subtype.mp hzi', hzΓ⟩⟩
  exact Finset.disjoint_left.mp hCdisj h1 h2

omit [Fintype ι] [Fintype P] [Fintype β] [DecidableEq β] [∀ i, IsProbabilityMeasure (ν₁ i)] in
lemma piFinset_inter (s u : Finset P) {k : ℕ} :
    Fintype.piFinset (fun _ : Fin k => s) ∩ Fintype.piFinset (fun _ : Fin k => u) =
      Fintype.piFinset (fun _ : Fin k => s ∩ u) := by
  ext g
  simp only [Finset.mem_inter, Fintype.mem_piFinset]
  exact ⟨fun ⟨h1, h2⟩ i => ⟨h1 i, h2 i⟩, fun h => ⟨fun i => (h i).1, fun i => (h i).2⟩⟩

omit [Fintype ι] [DecidableEq P] [Fintype β] [∀ i, IsProbabilityMeasure (ν₁ i)] in
/-- An interior piece of box `b` lies in the box. -/
lemma Pavement.supp_subset_box_of_interior {b : β} {X : P} (hX : X ∈ pv.interior b) :
    (L.supp X : Set ι) ⊆ pv.box b := by
  obtain ⟨hXp, hXΓ⟩ := Finset.mem_filter.mp hX
  have hhome : pv.home X = some b := (Finset.mem_filter.mp hXp).2
  intro i hi
  rcases pv.homeSome X b hhome hi with h | h
  · exact h
  · exact absurd (Finset.mem_coe.mp h) (Finset.disjoint_left.mp hXΓ (Finset.mem_coe.mp hi))

omit [DecidableEq P] [Fintype β] in
/-- For tuples of interior pieces the box cumulant (corridor coordinates fixed) is the unconditional one. -/
lemma Pavement.box_jointCumulant_interior (b : β) (x : ι → ℝ) {k : ℕ} (g : Fin k → P)
    (hg : ∀ i, g i ∈ pv.interior b) :
    jointCumulant (fun T => ∫ y, ∏ i ∈ T, L.h (g i) (updateFinset x (pv.box b) y) ∂(boxMeasure ν₁ (pv.box b)))
      Finset.univ =
    jointCumulant (fun T => ∫ ω, ∏ i ∈ T, L.h (g i) ω ∂(Measure.pi ν₁)) Finset.univ := by
  congr 1
  funext T
  refine integral_updateFinset_eq ν₁ (pv.box b) x (G := fun ω => ∏ i ∈ T, L.h (g i) ω) ?_
    (Finset.measurable_prod _ fun i _ => L.meas (g i))
  intro ω ω' hωω
  refine Finset.prod_congr rfl fun i _ => L.loc (g i) fun j hj => hωω j ?_
  exact pv.supp_subset_box_of_interior (hg i) hj

omit [Fintype β] in
/-- **The box identity** (the exact form of [2] (5.25)-(5.31) for independent coordinates): for `1 ≤ k ≤ t` and a set
`D` of deep pieces, in box `b` with the corridor coordinates fixed at `x`,
`⟨Ψ_b^k⟩^T_b = ⟨(Ψ^int_b)^k⟩^T + ⟨(Ψ_b - Ψ^D_b)^k⟩^T_b - ⟨(Ψ^int_b - Ψ^D_b)^k⟩^T`, the unsubscripted truncated
expectations unconditional. -/
theorem Pavement.box_truncExp_split (t : ℕ) (b : β) (x : ι → ℝ) {k : ℕ} (hk1 : 0 < k) (hkt : k ≤ t)
    (D : Finset P) (hD : ∀ X ∈ D, pv.IsDeep t X) :
    truncExp (moments (boxMeasure ν₁ (pv.box b)) (pv.boxSum b x (pv.pieces b))) k =
      truncExp (moments (Measure.pi ν₁) (L.sum (pv.interior b))) k +
        truncExp (moments (boxMeasure ν₁ (pv.box b)) (pv.boxSum b x (pv.pieces b \ D))) k -
        truncExp (moments (Measure.pi ν₁) (L.sum (pv.interior b \ D))) k := by
  set μb := boxMeasure ν₁ (pv.box b) with hμb
  set κb : (Fin k → P) → ℝ := fun g =>
    jointCumulant (fun T => ∫ y, ∏ i ∈ T, L.h (g i) (updateFinset x (pv.box b) y) ∂μb) Finset.univ with hκb
  have hbox : ∀ s : Finset P, truncExp (moments μb (pv.boxSum b x s)) k =
      ∑ g ∈ Fintype.piFinset (fun _ : Fin k => s), κb g := fun s =>
    truncExp_moments_finset_sum_eq μb s (fun X y => L.h X (updateFinset x (pv.box b) y))
      (fun X => pv.measurable_update b x X) L.a (fun X y => L.bdd X _) hk1
  have hfull : ∀ s : Finset P, s ⊆ pv.interior b → truncExp (moments (Measure.pi ν₁) (L.sum s)) k =
      ∑ g ∈ Fintype.piFinset (fun _ : Fin k => s), κb g := by
    intro s hs
    rw [show L.sum s = fun ω => ∑ X ∈ s, L.h X ω from rfl,
      truncExp_moments_finset_sum_eq (Measure.pi ν₁) s L.h L.meas L.a L.bdd hk1]
    refine Finset.sum_congr rfl fun g hg => ?_
    exact (pv.box_jointCumulant_interior ν₁ b x g fun i => hs (Fintype.mem_piFinset.mp hg i)).symm
  have hint_sub : pv.interior b ⊆ pv.pieces b := Finset.filter_subset _ _
  rw [hbox, hbox, hfull _ subset_rfl, hfull _ Finset.sdiff_subset]
  -- inclusion-exclusion over tuples
  set A := Fintype.piFinset (fun _ : Fin k => pv.interior b) with hA
  set B := Fintype.piFinset (fun _ : Fin k => pv.pieces b \ D) with hB
  have hAB : A ∩ B = Fintype.piFinset (fun _ : Fin k => pv.interior b \ D) := by
    rw [hA, hB, piFinset_inter]
    congr 1
    funext _
    ext X
    simp only [Finset.mem_inter, Finset.mem_sdiff]
    exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hint_sub h.1, h.2⟩⟩
  have hsub : A ∪ B ⊆ Fintype.piFinset (fun _ : Fin k => pv.pieces b) := by
    intro g hg
    refine Fintype.mem_piFinset.mpr fun i => ?_
    rcases Finset.mem_union.mp hg with h | h
    · exact hint_sub (Fintype.mem_piFinset.mp h i)
    · exact (Finset.mem_sdiff.mp (Fintype.mem_piFinset.mp h i)).1
  have hzero : ∀ g ∈ Fintype.piFinset (fun _ : Fin k => pv.pieces b), g ∉ A ∪ B → κb g = 0 := by
    intro g hg hgAB
    have hgA : g ∉ A := fun h => hgAB (Finset.mem_union_left _ h)
    have hgB : g ∉ B := fun h => hgAB (Finset.mem_union_right _ h)
    obtain ⟨j, hj⟩ : ∃ j, g j ∉ pv.interior b := by
      by_contra hcon
      push Not at hcon
      exact hgA (Fintype.mem_piFinset.mpr hcon)
    obtain ⟨i₀, hi₀⟩ : ∃ i₀, g i₀ ∈ D := by
      by_contra hcon
      push Not at hcon
      exact hgB (Fintype.mem_piFinset.mpr fun i =>
        Finset.mem_sdiff.mpr ⟨Fintype.mem_piFinset.mp hg i, hcon i⟩)
    have hjΓ : ¬ Disjoint (L.supp (g j)) pv.Γ := fun h =>
      hj (Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mp hg j, h⟩)
    exact pv.box_jointCumulant_deep_bd_eq_zero ν₁ t b x hkt g (hD _ hi₀) hjΓ
  rw [← Finset.sum_subset hsub hzero, ← hAB]
  have := Finset.sum_union_inter (s₁ := A) (s₂ := B) (f := κb)
  linarith

/-- **The unconditional identity** (the bookkeeping of [2] (5.30)-(5.35), exact here): for `1 ≤ k ≤ t` and a set `D` of
deep pieces, `⟨F^k⟩^T - ⟨(F - F^D)^k⟩^T = Σ_b (⟨(Ψ^int_b)^k⟩^T - ⟨(Ψ^int_b - Ψ^D_b)^k⟩^T)`: a connected tuple with a
deep piece lies in the interior of one box. -/
theorem Pavement.truncExp_sub_eq_sum_boxes (t : ℕ) {k : ℕ} (hk1 : 0 < k) (hkt : k ≤ t) (D : Finset P)
    (hD : ∀ X ∈ D, pv.IsDeep t X) :
    truncExp (moments (Measure.pi ν₁) (L.sum Finset.univ)) k -
        truncExp (moments (Measure.pi ν₁) (L.sum (Finset.univ \ D))) k =
      ∑ b, (truncExp (moments (Measure.pi ν₁) (L.sum (pv.interior b))) k -
        truncExp (moments (Measure.pi ν₁) (L.sum (pv.interior b \ D))) k) := by
  set κ : (Fin k → P) → ℝ := fun g =>
    jointCumulant (fun T => ∫ ω, ∏ i ∈ T, L.h (g i) ω ∂(Measure.pi ν₁)) Finset.univ with hκ
  have hexp : ∀ s : Finset P, truncExp (moments (Measure.pi ν₁) (L.sum s)) k =
      ∑ g ∈ Fintype.piFinset (fun _ : Fin k => s), κ g := fun s =>
    truncExp_moments_finset_sum_eq (Measure.pi ν₁) s L.h L.meas L.a L.bdd hk1
  have hpisub : ∀ s u : Finset P, u ⊆ s →
      Fintype.piFinset (fun _ : Fin k => u) ⊆ Fintype.piFinset (fun _ : Fin k => s) := fun s u hus g hg =>
    Fintype.mem_piFinset.mpr fun i => hus (Fintype.mem_piFinset.mp hg i)
  simp_rw [hexp]
  rw [← Finset.sum_sdiff (hpisub _ _ Finset.sdiff_subset), add_sub_cancel_right]
  have hbox : ∀ b, ∑ g ∈ Fintype.piFinset (fun _ : Fin k => pv.interior b), κ g -
      ∑ g ∈ Fintype.piFinset (fun _ : Fin k => pv.interior b \ D), κ g =
      ∑ g ∈ Fintype.piFinset (fun _ : Fin k => pv.interior b) \
        Fintype.piFinset (fun _ : Fin k => pv.interior b \ D), κ g := fun b => by
    rw [← Finset.sum_sdiff (hpisub _ _ Finset.sdiff_subset), add_sub_cancel_right]
  simp_rw [hbox]
  set W : β → Finset (Fin k → P) := fun b => Fintype.piFinset (fun _ : Fin k => pv.interior b) \
    Fintype.piFinset (fun _ : Fin k => pv.interior b \ D) with hW
  have i0 : Fin k := ⟨0, hk1⟩
  have hWdisj : ((Finset.univ : Finset β) : Set β).PairwiseDisjoint W := by
    intro b _ b' _ hbb'
    refine Finset.disjoint_left.mpr fun g hg hg' => hbb' ?_
    have h1 := (Finset.mem_filter.mp (Fintype.mem_piFinset.mp (Finset.mem_sdiff.mp hg).1 i0)).1
    have h2 := (Finset.mem_filter.mp (Fintype.mem_piFinset.mp (Finset.mem_sdiff.mp hg').1 i0)).1
    have e1 := (Finset.mem_filter.mp h1).2
    have e2 := (Finset.mem_filter.mp h2).2
    rw [e1] at e2
    exact Option.some_injective _ e2
  rw [← Finset.sum_biUnion hWdisj]
  refine (Finset.sum_subset (fun g hg => ?_) fun g hg hgW => ?_).symm
  · obtain ⟨b, -, hgb⟩ := Finset.mem_biUnion.mp hg
    obtain ⟨hg1, hg2⟩ := Finset.mem_sdiff.mp hgb
    refine Finset.mem_sdiff.mpr ⟨Fintype.mem_piFinset.mpr fun _ => Finset.mem_univ _, fun h => hg2 ?_⟩
    exact Fintype.mem_piFinset.mpr fun i => Finset.mem_sdiff.mpr
      ⟨Fintype.mem_piFinset.mp hg1 i, (Finset.mem_sdiff.mp (Fintype.mem_piFinset.mp h i)).2⟩
  · obtain ⟨-, hgD⟩ := Finset.mem_sdiff.mp hg
    obtain ⟨i₀, hi₀⟩ : ∃ i₀, g i₀ ∈ D := by
      by_contra hcon
      push Not at hcon
      exact hgD (Fintype.mem_piFinset.mpr fun i => Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hcon i⟩)
    obtain ⟨⟨b, hb⟩, -, hdeep⟩ := hD _ hi₀
    obtain ⟨C, hC0, hCin, hCdisj⟩ := hdeep k hkt g i₀ rfl
    by_cases hCu : C = Finset.univ
    · exfalso
      refine hgW (Finset.mem_biUnion.mpr ⟨b, Finset.mem_univ _, Finset.mem_sdiff.mpr ⟨?_, fun h => ?_⟩⟩)
      · refine Fintype.mem_piFinset.mpr fun i => ?_
        obtain ⟨h1, h2⟩ := hCin i (hCu ▸ Finset.mem_univ i)
        rw [hb] at h2
        exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2⟩, h1⟩
      · exact (Finset.mem_sdiff.mp (Fintype.mem_piFinset.mp h i₀)).2 hi₀
    · obtain ⟨j, hj⟩ : ∃ j, j ∉ C := by
        by_contra hcon
        push Not at hcon
        exact hCu (Finset.eq_univ_of_forall hcon)
      refine jointCumulant_local_eq_zero ν₁ (fun i => L.h (g i)) (fun i => L.supp (g i)) (fun i => L.loc (g i))
        (fun i => L.meas (g i)) (Finset.subset_univ C) ⟨i₀, hC0⟩ ⟨j, by simp [hj]⟩ ?_
      rw [Finset.disjoint_left]
      intro z hz1 hz2
      obtain ⟨i, hi, hzi⟩ := Finset.mem_biUnion.mp hz1
      obtain ⟨i', hi', hzi'⟩ := Finset.mem_biUnion.mp hz2
      have hzΓ : z ∉ pv.Γ := Finset.disjoint_left.mp (hCin i hi).1 hzi
      exact Finset.disjoint_left.mp hCdisj (Finset.mem_biUnion.mpr ⟨i, hi, hzi⟩)
        (Finset.mem_biUnion.mpr ⟨i', hi', Finset.mem_sdiff.mpr ⟨hzi', hzΓ⟩⟩)

end GaussianBlockSpin
