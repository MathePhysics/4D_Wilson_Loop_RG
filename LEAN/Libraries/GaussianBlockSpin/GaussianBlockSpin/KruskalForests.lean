import GaussianBlockSpin.LineConnectivity
import GaussianBlockSpin.MergeTrees

/-! **Kruskal's construction along an ordering of the lines**: processing a list of lines in order, a line is a
*tree line* if its endpoints are not yet connected by the earlier lines (treeLines). There is a forest of merge trees
whose trees are the connectivity classes of the processed lines, with disjoint vertex sets covering `V`, every tree
well formed, and whose lines are (a permutation of) the tree lines (exists_kruskal_forest). -/

namespace GaussianBlockSpin

open MergeTree

variable {V E : Type*} [DecidableEq V] [Fintype V] (ends : E → V × V)

open Classical in
/-- The tree lines of `rest`, processed after the lines `pre`. -/
noncomputable def treeLinesAux : List E → List E → List E
  | _, [] => []
  | pre, l :: rest => (if lineConn ends pre (ends l).1 (ends l).2 then [] else [l]) ++ treeLinesAux (pre ++ [l]) rest

/-- The tree lines of a list of lines (Kruskal's minimal spanning forest for the given order). -/
noncomputable def treeLines (ls : List E) : List E := treeLinesAux ends [] ls

omit [DecidableEq V] [Fintype V] in
lemma treeLinesAux_sublist : ∀ (pre rest : List E), (treeLinesAux ends pre rest).Sublist rest
  | _, [] => by simp [treeLinesAux]
  | pre, l :: rest => by
    classical
    unfold treeLinesAux
    split_ifs
    · simpa using (treeLinesAux_sublist (pre ++ [l]) rest).cons l
    · simpa using (treeLinesAux_sublist (pre ++ [l]) rest).cons_cons l

omit [DecidableEq V] [Fintype V] in
lemma treeLines_sublist (ls : List E) : (treeLines ends ls).Sublist ls := treeLinesAux_sublist ends [] ls

/-- The invariant of the construction after the lines `pre`, with tree lines `TL`. -/
def KruskalInv (pre : List E) (F : List (MergeTree V E)) (TL : List E) : Prop :=
  (∀ t ∈ F, t.WF ends) ∧ F.Pairwise (fun t t' => Disjoint t.verts t'.verts) ∧ (∀ v, ∃ t ∈ F, v ∈ t.verts) ∧
    (∀ u v, lineConn ends pre u v ↔ ∃ t ∈ F, u ∈ t.verts ∧ v ∈ t.verts) ∧ (F.flatMap lines).Perm TL

/-- The initial forest: one leaf per vertex. -/
lemma kruskalInv_nil : KruskalInv ends [] ((Finset.univ : Finset V).toList.map MergeTree.leaf) [] := by
  refine ⟨fun t ht => ?_, ?_, fun v => ?_, fun u v => ?_, ?_⟩
  · obtain ⟨v, -, rfl⟩ := List.mem_map.mp ht; trivial
  · rw [List.pairwise_map]
    refine List.Pairwise.imp (fun {a b} hab => ?_) (Finset.nodup_toList _)
    simp [verts, hab]
  · exact ⟨leaf v, List.mem_map.mpr ⟨v, Finset.mem_toList.mpr (Finset.mem_univ _), rfl⟩, by simp [verts]⟩
  · constructor
    · intro h
      have huv : u = v := by
        induction h with
        | refl => rfl
        | tail _ hxy _ => obtain ⟨l, hl, -⟩ := hxy; exact absurd hl (List.not_mem_nil)
      subst huv
      exact ⟨leaf u, List.mem_map.mpr ⟨u, Finset.mem_toList.mpr (Finset.mem_univ _), rfl⟩, by simp [verts], by
        simp [verts]⟩
    · rintro ⟨t, ht, hu, hv⟩
      obtain ⟨w, -, rfl⟩ := List.mem_map.mp ht
      simp only [verts, Finset.mem_singleton] at hu hv
      subst hu; subst hv
      exact lineConn_refl _ _
  · simp [lines]

variable {ends}

omit [Fintype V] in
/-- In a forest with pairwise disjoint trees, two trees sharing a vertex are equal. -/
lemma eq_of_mem_of_mem {F : List (MergeTree V E)} (hF : F.Pairwise (fun t t' => Disjoint t.verts t'.verts))
    {t t' : MergeTree V E} (ht : t ∈ F) (ht' : t' ∈ F) {v : V} (hv : v ∈ t.verts) (hv' : v ∈ t'.verts) : t = t' := by
  by_contra hne
  have : Std.Symm (fun t t' : MergeTree V E => Disjoint t.verts t'.verts) := ⟨fun _ _ h => h.symm⟩
  exact Finset.disjoint_left.mp (hF.forall ht ht' hne) hv hv'

omit [Fintype V] in
/-- The step without a new tree line. -/
lemma kruskalInv_step_conn {pre : List E} {F : List (MergeTree V E)} {TL : List E} (h : KruskalInv ends pre F TL)
    {l : E} (hc : lineConn ends pre (ends l).1 (ends l).2) : KruskalInv ends (pre ++ [l]) F TL := by
  obtain ⟨hwf, hdisj, hcov, hconn, hperm⟩ := h
  refine ⟨hwf, hdisj, hcov, fun u v => ?_, hperm⟩
  rw [lineConn_append_singleton, ← hconn]
  constructor
  · rintro (h | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
    · exact h
    · exact lineConn_trans (lineConn_trans h₁ hc) h₂
    · exact lineConn_trans (lineConn_trans h₁ (lineConn_symm hc)) h₂
  · exact Or.inl

omit [Fintype V] in
lemma verts_nonempty : ∀ t : MergeTree V E, t.verts.Nonempty
  | leaf v => ⟨v, by simp [verts]⟩
  | node _ t₁ _ => (verts_nonempty t₁).mono Finset.subset_union_left

omit [Fintype V] in
lemma nodup_of_pairwise_disjoint {F : List (MergeTree V E)} (hF : F.Pairwise (fun t t' => Disjoint t.verts t'.verts)) :
    F.Nodup := by
  refine hF.imp fun {t t'} h heq => ?_
  subst heq
  obtain ⟨v, hv⟩ := verts_nonempty t
  exact Finset.disjoint_left.mp h hv hv

omit [Fintype V] in
open Classical in
/-- The step with a new tree line: the trees of its endpoints merge. -/
lemma kruskalInv_step_merge {pre : List E} {F : List (MergeTree V E)} {TL : List E} (h : KruskalInv ends pre F TL)
    {l : E} (hc : ¬ lineConn ends pre (ends l).1 (ends l).2) : ∃ F', KruskalInv ends (pre ++ [l]) F' (TL ++ [l]) := by
  obtain ⟨hwf, hdisj, hcov, hconn, hperm⟩ := h
  have hsymm : Std.Symm (fun t t' : MergeTree V E => Disjoint t.verts t'.verts) := ⟨fun _ _ h => h.symm⟩
  set a := (ends l).1 with ha_def
  set b := (ends l).2 with hb_def
  obtain ⟨ta, hta, ha⟩ := hcov a
  obtain ⟨tb, htb, hb⟩ := hcov b
  have hne : ta ≠ tb := fun h => hc ((hconn a b).mpr ⟨ta, hta, ha, h ▸ hb⟩)
  have hdab : Disjoint ta.verts tb.verts := hdisj.forall hta htb hne
  set rest := F.filter (fun t => decide (a ∉ t.verts ∧ b ∉ t.verts)) with hrest
  have hmemrest : ∀ t, t ∈ rest ↔ t ∈ F ∧ a ∉ t.verts ∧ b ∉ t.verts := fun t => by
    simp [hrest, List.mem_filter]
  have hnotrest : ∀ t ∈ F, t ∉ rest → t = ta ∨ t = tb := fun t ht hnr => by
    by_cases hat : a ∈ t.verts
    · exact Or.inl (eq_of_mem_of_mem hdisj ht hta hat ha)
    · by_cases hbt : b ∈ t.verts
      · exact Or.inr (eq_of_mem_of_mem hdisj ht htb hbt hb)
      · exact absurd ((hmemrest t).mpr ⟨ht, hat, hbt⟩) hnr
  have hta_conn : ∀ u, lineConn ends pre u a → u ∈ ta.verts := fun u hu => by
    obtain ⟨t, ht, hut, hat⟩ := (hconn u a).mp hu
    rwa [eq_of_mem_of_mem hdisj ht hta hat ha] at hut
  have htb_conn : ∀ u, lineConn ends pre u b → u ∈ tb.verts := fun u hu => by
    obtain ⟨t, ht, hut, hbt⟩ := (hconn u b).mp hu
    rwa [eq_of_mem_of_mem hdisj ht htb hbt hb] at hut
  refine ⟨node l ta tb :: rest, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · exact ⟨hwf ta hta, hwf tb htb, hdab, Or.inl ⟨ha, hb⟩⟩
    · exact hwf t ((hmemrest t).mp ht).1
  · refine List.pairwise_cons.mpr ⟨fun t ht => ?_, hdisj.filter _⟩
    obtain ⟨htF, hat, hbt⟩ := (hmemrest t).mp ht
    have h1 : Disjoint ta.verts t.verts := hdisj.forall hta htF (fun h => hat (h ▸ ha))
    have h2 : Disjoint tb.verts t.verts := hdisj.forall htb htF (fun h => hbt (h ▸ hb))
    exact Finset.disjoint_union_left.mpr ⟨h1, h2⟩
  · intro v
    obtain ⟨t, ht, hv⟩ := hcov v
    by_cases htr : t ∈ rest
    · exact ⟨t, List.mem_cons_of_mem _ htr, hv⟩
    · rcases hnotrest t ht htr with rfl | rfl
      · exact ⟨node l t tb, List.mem_cons_self .., Finset.mem_union_left _ hv⟩
      · exact ⟨node l ta t, List.mem_cons_self .., Finset.mem_union_right _ hv⟩
  · intro u v
    rw [lineConn_append_singleton]
    constructor
    · rintro (h | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
      · obtain ⟨t, ht, hu, hv⟩ := (hconn u v).mp h
        by_cases htr : t ∈ rest
        · exact ⟨t, List.mem_cons_of_mem _ htr, hu, hv⟩
        · rcases hnotrest t ht htr with rfl | rfl
          · exact ⟨node l t tb, List.mem_cons_self .., Finset.mem_union_left _ hu, Finset.mem_union_left _ hv⟩
          · exact ⟨node l ta t, List.mem_cons_self .., Finset.mem_union_right _ hu, Finset.mem_union_right _ hv⟩
      · exact ⟨node l ta tb, List.mem_cons_self .., Finset.mem_union_left _ (hta_conn u h₁),
          Finset.mem_union_right _ (htb_conn v (lineConn_symm h₂))⟩
      · exact ⟨node l ta tb, List.mem_cons_self .., Finset.mem_union_right _ (htb_conn u h₁),
          Finset.mem_union_left _ (hta_conn v (lineConn_symm h₂))⟩
    · rintro ⟨t', ht', hu, hv⟩
      rcases List.mem_cons.mp ht' with rfl | ht'
      · simp only [verts, Finset.mem_union] at hu hv
        rcases hu with hu | hu <;> rcases hv with hv | hv
        · exact Or.inl ((hconn u v).mpr ⟨ta, hta, hu, hv⟩)
        · exact Or.inr (Or.inl ⟨(hconn u a).mpr ⟨ta, hta, hu, ha⟩, (hconn b v).mpr ⟨tb, htb, hb, hv⟩⟩)
        · exact Or.inr (Or.inr ⟨(hconn u b).mpr ⟨tb, htb, hu, hb⟩, (hconn a v).mpr ⟨ta, hta, ha, hv⟩⟩)
        · exact Or.inl ((hconn u v).mpr ⟨tb, htb, hu, hv⟩)
      · exact Or.inl ((hconn u v).mpr ⟨t', ((hmemrest t').mp ht').1, hu, hv⟩)
  · -- the lines
    have hnd := nodup_of_pairwise_disjoint hdisj
    have hsplit : F.Perm ([ta, tb] ++ rest) := by
      refine (List.perm_ext_iff_of_nodup hnd ?_).mpr fun t => ?_
      · refine List.Nodup.append (List.nodup_cons.mpr ⟨by simpa using hne, List.nodup_singleton _⟩)
          (hnd.filter _) ?_
        intro t ht ht'
        obtain ⟨-, hat, hbt⟩ := (hmemrest t).mp ht'
        rcases List.mem_pair.mp ht with rfl | rfl
        · exact hat ha
        · exact hbt hb
      · constructor
        · intro ht
          by_cases htr : t ∈ rest
          · exact List.mem_append_right _ htr
          · rcases hnotrest t ht htr with rfl | rfl <;> simp
        · intro ht
          rcases List.mem_append.mp ht with ht | ht
          · rcases List.mem_pair.mp ht with rfl | rfl
            · exact hta
            · exact htb
          · exact ((hmemrest t).mp ht).1
    have h1 : (F.flatMap lines).Perm (lines ta ++ lines tb ++ rest.flatMap lines) := by
      have := hsplit.flatMap_right lines
      simpa [List.flatMap_append, List.flatMap_cons, List.append_assoc] using this
    have h2 : (lines ta ++ lines tb ++ rest.flatMap lines).Perm TL := h1.symm.trans hperm
    simp only [List.flatMap_cons, lines, List.cons_append]
    exact ((h2.cons l).trans (List.perm_append_singleton l TL).symm)

omit [Fintype V] in
lemma exists_kruskalInv_append : ∀ (rest pre : List E) (F : List (MergeTree V E)) (TL : List E),
    KruskalInv ends pre F TL → ∃ F', KruskalInv ends (pre ++ rest) F' (TL ++ treeLinesAux ends pre rest)
  | [], pre, F, TL, h => ⟨F, by simpa [treeLinesAux] using h⟩
  | l :: rest, pre, F, TL, h => by
    classical
    by_cases hc : lineConn ends pre (ends l).1 (ends l).2
    · obtain ⟨F', hF'⟩ := exists_kruskalInv_append rest (pre ++ [l]) F TL (kruskalInv_step_conn h hc)
      refine ⟨F', ?_⟩
      have h1 : pre ++ l :: rest = pre ++ [l] ++ rest := by simp
      have h2 : treeLinesAux ends pre (l :: rest) = treeLinesAux ends (pre ++ [l]) rest := by
        simp [treeLinesAux, hc]
      rwa [h1, h2]
    · obtain ⟨F₁, hF₁⟩ := kruskalInv_step_merge h hc
      obtain ⟨F', hF'⟩ := exists_kruskalInv_append rest (pre ++ [l]) F₁ (TL ++ [l]) hF₁
      refine ⟨F', ?_⟩
      have h1 : pre ++ l :: rest = pre ++ [l] ++ rest := by simp
      have h2 : TL ++ treeLinesAux ends pre (l :: rest) = TL ++ [l] ++ treeLinesAux ends (pre ++ [l]) rest := by
        simp [treeLinesAux, hc]
      rwa [h1, h2]

/-- **Kruskal's forest** of a list of lines. -/
theorem exists_kruskal_forest (ls : List E) : ∃ F, KruskalInv ends ls F (treeLines ends ls) := by
  obtain ⟨F, hF⟩ := exists_kruskalInv_append ls [] _ [] (kruskalInv_nil ends)
  exact ⟨F, by simpa [treeLines] using hF⟩

/-- **The connected case**: if the lines connect all vertices, Kruskal's forest is one merge tree containing every
vertex, whose lines are the tree lines. -/
theorem exists_kruskal_tree {ls : List E} (hconn : ∀ u v, lineConn ends ls u v) (v₀ : V) :
    ∃ t : MergeTree V E, t.WF ends ∧ t.verts = Finset.univ ∧ t.lines.Perm (treeLines ends ls) := by
  obtain ⟨F, hwf, hdisj, hcov, hc, hperm⟩ := exists_kruskal_forest (ends := ends) ls
  obtain ⟨t₀, ht₀, hv₀⟩ := hcov v₀
  have hall : ∀ t ∈ F, t = t₀ := fun t ht => by
    obtain ⟨v, hv⟩ := verts_nonempty t
    obtain ⟨t', ht', hvt', hv₀t'⟩ := (hc v v₀).mp (hconn v v₀)
    have e1 : t = t' := eq_of_mem_of_mem hdisj ht ht' hv hvt'
    have e2 : t' = t₀ := eq_of_mem_of_mem hdisj ht' ht₀ hv₀t' hv₀
    rw [e1, e2]
  have hF : F = [t₀] := by
    have hnd := nodup_of_pairwise_disjoint hdisj
    have hrep : F = List.replicate F.length t₀ := List.eq_replicate_iff.mpr ⟨rfl, hall⟩
    have hlen : F.length = 1 := by
      have h1 : F.length ≤ 1 := by rw [hrep] at hnd; exact List.nodup_replicate.mp hnd
      have h2 : 0 < F.length := List.length_pos_of_mem ht₀
      omega
    rw [hrep, hlen]
    rfl
  refine ⟨t₀, hwf t₀ ht₀, ?_, ?_⟩
  · refine Finset.eq_univ_of_forall fun v => ?_
    obtain ⟨t', ht', hvt', hv₀t'⟩ := (hc v v₀).mp (hconn v v₀)
    rwa [hall t' ht'] at hvt'
  · rw [hF] at hperm
    simpa using hperm

end GaussianBlockSpin
