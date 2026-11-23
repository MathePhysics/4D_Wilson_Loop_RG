import GaussianBlockSpin.PowerCounting

/-! **Degrees of connected line sets and the power-counting hypothesis** (III (2.2), (2.7), (2.16)): the touched
vertices lineVerts, connected line sets ConnLines, and the degree
`conDeg C = d (#V(C) - 1) + Σ_{v ∈ V(C)} a_v - Σ_{l ∈ C} ω_l`. For III's graphs, `a_v = n_v - d` (`n_v` the factors
`η` at `v`, the `η^d` of the lattice sum included) and `ω_l = (d - 2) + (derivatives on l) - (vector legs of l at
(1.14), (1.15))` make `conDeg C` the degree (2.2) of a connected `C`.
* prefixSum_pcCoef_components: the lines `σ 0, …, σ i` of an ordering split into connected line sets with pairwise
  disjoint vertex sets (the components `G_i^(α)` of (2.16)), and the prefix sum of the power-counting coefficients
  is the sum of their degrees;
* prefixSum_ge_of_conDeg_ge: if every connected line set has degree at least `p₀ ≥ 0`, so has every prefix sum;
* exists_prefixSum_ge: if every connected line set has positive degree, all prefix sums of all orderings are at
  least one `p₀ > 0`, the hypothesis of power_counting. -/

namespace GaussianBlockSpin

open MergeTree

variable {V E : Type*} [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E] (ends : E → V × V)

/-- The vertices touched by a set of lines. -/
def lineVerts (P : Finset E) : Finset V := P.biUnion fun l => {(ends l).1, (ends l).2}

omit [Fintype V] [DecidableEq E] [Fintype E] in
lemma mem_lineVerts {P : Finset E} {v : V} : v ∈ lineVerts ends P ↔ ∃ l ∈ P, Incident ends l v := by
  simp only [lineVerts, Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton, Incident]
  constructor
  · rintro ⟨l, hl, h⟩; exact ⟨l, hl, h.imp Eq.symm Eq.symm⟩
  · rintro ⟨l, hl, h⟩; exact ⟨l, hl, h.imp Eq.symm Eq.symm⟩

/-- A connected set of lines: nonempty, and any two touched vertices are joined through its lines. -/
def ConnLines (C : Finset E) : Prop :=
  C.Nonempty ∧ ∀ u ∈ lineVerts ends C, ∀ v ∈ lineVerts ends C, lineConn ends C.toList u v

/-- The degree of a set of lines, `d (#V(C) - 1) + Σ_{v ∈ V(C)} a_v - Σ_{l ∈ C} ω_l` (III (2.2) for a connected
`C`, with `a_v` the vertex exponents and `ω_l` the line dimensions). -/
noncomputable def conDeg (d : ℕ) (a : V → ℝ) (ω : E → ℝ) (C : Finset E) : ℝ :=
  d * (((lineVerts ends C).card : ℝ) - 1) + ∑ v ∈ lineVerts ends C, a v - ∑ l ∈ C, ω l

variable {ends}

omit [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E] in
lemma eq_leaf_of_lines_eq_nil : ∀ {t : MergeTree V E}, t.lines = [] → ∃ u, t = leaf u
  | leaf u, _ => ⟨u, rfl⟩
  | node _ _ _, h => by simp [lines] at h

omit [Fintype V] [DecidableEq E] [Fintype E] in
/-- A well-formed merge tree has one vertex more than lines. -/
lemma length_lines_add_one {t : MergeTree V E} (ht : t.WF ends) : t.lines.length + 1 = t.verts.card := by
  induction t with
  | leaf v => simp [lines, verts]
  | node l t₁ t₂ ih₁ ih₂ =>
    obtain ⟨h₁, h₂, hd, -⟩ := ht
    simp only [lines, verts, List.length_cons, List.length_append]
    rw [Finset.card_union_of_disjoint hd, ← ih₁ h₁, ← ih₂ h₂]
    ring

omit [Fintype V] [DecidableEq E] [Fintype E] in
/-- Every vertex of a well-formed merge tree with a line is an endpoint of one of its lines. -/
lemma exists_line_incident {t : MergeTree V E} (ht : t.WF ends) (hne : t.lines ≠ []) :
    ∀ v ∈ t.verts, ∃ l ∈ t.lines, Incident ends l v := by
  induction t with
  | leaf v => simp [lines] at hne
  | node l t₁ t₂ ih₁ ih₂ =>
    obtain ⟨h₁, h₂, hd, hl⟩ := ht
    intro v hv
    simp only [verts, Finset.mem_union] at hv
    rcases hv with hv | hv
    · by_cases h1 : t₁.lines = []
      · obtain ⟨u, rfl⟩ := eq_leaf_of_lines_eq_nil h1
        simp only [verts, Finset.mem_singleton] at hv hl
        subst hv
        refine ⟨l, List.mem_cons_self .., ?_⟩
        rcases hl with ⟨a, -⟩ | ⟨a, -⟩
        · exact Or.inl a
        · exact Or.inr a
      · obtain ⟨l', hl', hinc⟩ := ih₁ h₁ h1 v hv
        exact ⟨l', by simp [lines, hl'], hinc⟩
    · by_cases h2 : t₂.lines = []
      · obtain ⟨u, rfl⟩ := eq_leaf_of_lines_eq_nil h2
        simp only [verts, Finset.mem_singleton] at hv hl
        subst hv
        refine ⟨l, List.mem_cons_self .., ?_⟩
        rcases hl with ⟨-, a⟩ | ⟨-, a⟩
        · exact Or.inr a
        · exact Or.inl a
      · obtain ⟨l', hl', hinc⟩ := ih₂ h₂ h2 v hv
        exact ⟨l', by simp [lines, hl'], hinc⟩

omit [Fintype V] [Fintype E] [DecidableEq E] in
/-- A path through the lines `ls` starting in a vertex set closed under the lines stays in it and uses only the lines
with endpoints in it. -/
lemma lineConn_filter {ls : List E} {S : Finset V} (hS : ∀ l ∈ ls, (ends l).1 ∈ S ↔ (ends l).2 ∈ S)
    {u v : V} (hu : u ∈ S) (h : lineConn ends ls u v) :
    v ∈ S ∧ lineConn ends (ls.filter fun l => (ends l).1 ∈ S) u v := by
  induction h with
  | refl => exact ⟨hu, lineConn_refl _ _⟩
  | @tail x y _ hxy ih =>
    obtain ⟨hx, hc⟩ := ih
    obtain ⟨l, hl, he⟩ := hxy
    have key := hS l hl
    rcases he with he | he
    · simp only [he] at key
      have hy : y ∈ S := key.mp hx
      exact ⟨hy, hc.tail ⟨l, List.mem_filter.mpr ⟨hl, by simp [he, hx]⟩, Or.inl he⟩⟩
    · simp only [he] at key
      have hy : y ∈ S := key.mpr hx
      exact ⟨hy, hc.tail ⟨l, List.mem_filter.mpr ⟨hl, by simp [he, hy]⟩, Or.inr he⟩⟩

omit [DecidableEq V] [Fintype V] [Fintype E] [DecidableEq E] in
lemma lineConn_congr {ls ls' : List E} (h : ∀ l, l ∈ ls ↔ l ∈ ls') {u v : V} :
    lineConn ends ls u v ↔ lineConn ends ls' u v :=
  ⟨lineConn_mono fun l hl => (h l).mp hl, lineConn_mono fun l hl => (h l).mpr hl⟩

variable (ends)

omit [DecidableEq V] [Fintype V] [Fintype E] [DecidableEq E] in
/-- The tree lines of a concatenation. -/
lemma treeLinesAux_append : ∀ (pre l₁ l₂ : List E),
    treeLinesAux ends pre (l₁ ++ l₂) = treeLinesAux ends pre l₁ ++ treeLinesAux ends (pre ++ l₁) l₂
  | pre, [], l₂ => by simp [treeLinesAux]
  | pre, l :: l₁, l₂ => by
    rw [List.cons_append]
    simp only [treeLinesAux]
    rw [treeLinesAux_append (pre ++ [l]) l₁ l₂]
    simp [List.append_assoc]

omit [Fintype V] [DecidableEq E] in
lemma mem_take_ofFn (σ : Fin (Fintype.card E) ≃ E) (i : Fin (Fintype.card E)) (l : E) :
    l ∈ (List.ofFn σ).take (i.1 + 1) ↔ σ.symm l ≤ i := by
  rw [List.mem_take_iff_getElem]
  constructor
  · rintro ⟨j, hj, rfl⟩
    simp only [List.length_ofFn] at hj
    simp only [List.getElem_ofFn, Equiv.symm_apply_apply]
    show j ≤ i.1
    omega
  · intro h
    refine ⟨(σ.symm l).1, ?_, ?_⟩
    · simp only [List.length_ofFn]; have := (σ.symm l).2; have : (σ.symm l).1 ≤ i.1 := h; omega
    · simp

omit [DecidableEq V] [Fintype V] [DecidableEq E] in
/-- A line of the prefix `σ 0, …, σ i` is a tree line of the ordering iff it is a tree line of the prefix. -/
lemma mem_treeLines_ofFn_iff (σ : Fin (Fintype.card E) ≃ E) {i i' : Fin (Fintype.card E)} (hi : i' ≤ i) :
    σ i' ∈ treeLines ends (List.ofFn σ) ↔ σ i' ∈ treeLines ends ((List.ofFn σ).take (i.1 + 1)) := by
  have hsplit := List.take_append_drop (i.1 + 1) (List.ofFn σ)
  have hmem : σ i' ∈ (List.ofFn σ).take (i.1 + 1) := (mem_take_ofFn σ i _).mpr (by simpa using hi)
  have hnd : (List.ofFn σ).Nodup := List.nodup_ofFn.mpr σ.injective
  have hdisj := List.disjoint_take_drop (m := i.1 + 1) hnd le_rfl
  conv_lhs => rw [← hsplit]
  unfold treeLines
  rw [treeLinesAux_append, List.mem_append, List.nil_append]
  constructor
  · rintro (h | h)
    · exact h
    · exact absurd ((treeLinesAux_sublist ends _ _).subset h) (fun h' => hdisj hmem h')
  · exact Or.inl

/-- The lines of `P` whose first endpoint lies in the tree `t`. -/
def linesIn (P : Finset E) (t : MergeTree V E) : Finset E := P.filter fun l => (ends l).1 ∈ t.verts

section Forest

variable {ends} {pre : List E} {F : List (MergeTree V E)}

omit [Fintype V] [Fintype E] [DecidableEq E] in
/-- Both endpoints of a processed line lie in the same tree of the forest. -/
lemma mem_tree_iff (hK : KruskalInv ends pre F (treeLines ends pre)) {t : MergeTree V E} (ht : t ∈ F) {l : E}
    (hl : l ∈ pre) : (ends l).1 ∈ t.verts ↔ (ends l).2 ∈ t.verts := by
  obtain ⟨-, hdisj, -, hconn, -⟩ := hK
  obtain ⟨t', ht', h1, h2⟩ := (hconn _ _).mp (lineConn_of_ends hl)
  constructor
  · intro h; rwa [eq_of_mem_of_mem hdisj ht ht' h h1]
  · intro h; rwa [eq_of_mem_of_mem hdisj ht ht' h h2]

omit [Fintype V] [Fintype E] [DecidableEq E] in
lemma lines_subset_pre (hK : KruskalInv ends pre F (treeLines ends pre)) {t : MergeTree V E} (ht : t ∈ F) {l : E}
    (hl : l ∈ t.lines) : l ∈ pre := by
  obtain ⟨-, -, -, -, hperm⟩ := hK
  have : l ∈ F.flatMap lines := List.mem_flatMap.mpr ⟨t, ht, hl⟩
  exact (treeLines_sublist ends pre).subset (hperm.subset this)

omit [Fintype V] [Fintype E] in
/-- A tree without processed lines is a single untouched vertex. -/
lemma linesIn_eq_empty (hK : KruskalInv ends pre F (treeLines ends pre)) {t : MergeTree V E} (ht : t ∈ F)
    (h : linesIn ends pre.toFinset t = ∅) : t.lines = [] ∧ ∀ v ∈ t.verts, v ∉ lineVerts ends pre.toFinset := by
  constructor
  · by_contra hne
    obtain ⟨l, hl⟩ := List.exists_mem_of_ne_nil _ hne
    have hmem : l ∈ linesIn ends pre.toFinset t :=
      Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr (lines_subset_pre hK ht hl), (ends_mem_verts (hK.1 t ht) l hl).1⟩
    rw [h] at hmem
    exact Finset.notMem_empty _ hmem
  · intro v hv hvP
    obtain ⟨l, hl, hinc⟩ := (mem_lineVerts ends).mp hvP
    have hlp : l ∈ pre := List.mem_toFinset.mp hl
    have h1 : (ends l).1 ∈ t.verts := by
      rcases hinc with h' | h'
      · rwa [h']
      · exact (mem_tree_iff hK ht hlp).mpr (by rwa [h'])
    have hmem : l ∈ linesIn ends pre.toFinset t := Finset.mem_filter.mpr ⟨hl, h1⟩
    rw [h] at hmem
    exact Finset.notMem_empty _ hmem

omit [Fintype V] [Fintype E] in
/-- The processed lines of a tree touch exactly its vertices. -/
lemma lineVerts_linesIn (hK : KruskalInv ends pre F (treeLines ends pre)) {t : MergeTree V E} (ht : t ∈ F)
    (hne : (linesIn ends pre.toFinset t).Nonempty) : lineVerts ends (linesIn ends pre.toFinset t) = t.verts := by
  ext v
  rw [mem_lineVerts]
  constructor
  · rintro ⟨l, hl, hinc⟩
    obtain ⟨hlP, h1⟩ := Finset.mem_filter.mp hl
    rcases hinc with h' | h'
    · rwa [← h']
    · rw [← h']; exact (mem_tree_iff hK ht (List.mem_toFinset.mp hlP)).mp h1
  · intro hv
    by_cases hlines : t.lines = []
    · obtain ⟨u, rfl⟩ := eq_leaf_of_lines_eq_nil hlines
      simp only [verts, Finset.mem_singleton] at hv
      subst hv
      obtain ⟨l, hl⟩ := hne
      refine ⟨l, hl, Or.inl ?_⟩
      have := (Finset.mem_filter.mp hl).2
      simpa [verts] using this
    · obtain ⟨l, hl, hinc⟩ := exists_line_incident (hK.1 t ht) hlines v hv
      exact ⟨l, Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr (lines_subset_pre hK ht hl),
        (ends_mem_verts (hK.1 t ht) l hl).1⟩, hinc⟩

omit [Fintype V] [Fintype E] in
/-- The processed lines of a tree form a connected line set. -/
lemma connLines_linesIn (hK : KruskalInv ends pre F (treeLines ends pre)) {t : MergeTree V E} (ht : t ∈ F)
    (hne : (linesIn ends pre.toFinset t).Nonempty) : ConnLines ends (linesIn ends pre.toFinset t) := by
  refine ⟨hne, fun u hu v hv => ?_⟩
  rw [lineVerts_linesIn hK ht hne] at hu hv
  have huv : lineConn ends pre u v := (hK.2.2.2.1 u v).mpr ⟨t, ht, hu, hv⟩
  have hS : ∀ l ∈ pre, (ends l).1 ∈ t.verts ↔ (ends l).2 ∈ t.verts := fun l hl => mem_tree_iff hK ht hl
  have h := (lineConn_filter hS hu huv).2
  refine (lineConn_congr fun l => ?_).mp h
  simp [linesIn, List.mem_filter]

omit [Fintype V] [Fintype E] [DecidableEq E] in
open Classical in
/-- Sums split along the trees of the forest. -/
lemma sum_split_trees {α : Type*} (hK : KruskalInv ends pre F (treeLines ends pre)) (S : Finset α) (φ : α → V)
    (f : α → ℝ) : ∑ x ∈ S, f x = ∑ t ∈ F.toFinset, ∑ x ∈ S.filter (fun x => φ x ∈ t.verts), f x := by
  have hone : ∀ x, ∑ t ∈ F.toFinset, (if φ x ∈ t.verts then f x else 0) = f x := by
    intro x
    obtain ⟨t₀, ht₀, hv₀⟩ := hK.2.2.1 (φ x)
    rw [Finset.sum_eq_single_of_mem t₀ (List.mem_toFinset.mpr ht₀) fun t ht hne => ?_]
    · simp [hv₀]
    · rw [ite_eq_right_iff]
      intro hv
      exact absurd (eq_of_mem_of_mem hK.2.1 (List.mem_toFinset.mp ht) ht₀ hv hv₀) hne
  calc ∑ x ∈ S, f x = ∑ x ∈ S, ∑ t ∈ F.toFinset, (if φ x ∈ t.verts then f x else 0) :=
        Finset.sum_congr rfl fun x _ => (hone x).symm
    _ = ∑ t ∈ F.toFinset, ∑ x ∈ S, (if φ x ∈ t.verts then f x else 0) := Finset.sum_comm
    _ = _ := by simp_rw [Finset.sum_filter]

omit [Fintype V] [Fintype E] [DecidableEq E] in
open Classical in
lemma length_treeLines_eq (hK : KruskalInv ends pre F (treeLines ends pre)) :
    ((treeLines ends pre).length : ℝ) = ∑ t ∈ F.toFinset, ((t.verts.card : ℝ) - 1) := by
  have hnd : F.Nodup := nodup_of_pairwise_disjoint hK.2.1
  rw [← hK.2.2.2.2.length_eq, List.length_flatMap, ← List.sum_toFinset _ hnd]
  push_cast
  refine Finset.sum_congr rfl fun t ht => ?_
  have h := length_lines_add_one (hK.1 t (List.mem_toFinset.mp ht))
  have h2 : (t.lines.length : ℝ) + 1 = t.verts.card := by exact_mod_cast h
  linarith

omit [Fintype V] [Fintype E] [DecidableEq E] in
lemma lineVerts_mono {P Q : Finset E} (h : P ⊆ Q) : lineVerts ends P ⊆ lineVerts ends Q :=
  Finset.biUnion_subset_biUnion_of_subset_left _ h

omit [Fintype V] [Fintype E] in
open Classical in
/-- **The forest identity**: for the processed lines `P`, `d #(tree lines) + Σ_{v ∈ V(P)} a_v - Σ_{l ∈ P} ω_l` is the
sum over the trees of the degrees of their processed line sets. -/
lemma sum_trees_eq (hK : KruskalInv ends pre F (treeLines ends pre)) (d : ℕ) (a : V → ℝ) (ω : E → ℝ) :
    d * ((treeLines ends pre).length : ℝ) + ∑ v ∈ lineVerts ends pre.toFinset, a v - ∑ l ∈ pre.toFinset, ω l =
      ∑ t ∈ F.toFinset, if (linesIn ends pre.toFinset t).Nonempty then
        conDeg ends d a ω (linesIn ends pre.toFinset t) else 0 := by
  rw [length_treeLines_eq hK, sum_split_trees hK (lineVerts ends pre.toFinset) id a,
    sum_split_trees hK pre.toFinset (fun l => (ends l).1) ω, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun t ht => ?_
  have htF : t ∈ F := List.mem_toFinset.mp ht
  split_ifs with hne
  · have hV := lineVerts_linesIn hK htF hne
    have hsub : t.verts ⊆ lineVerts ends pre.toFinset := by
      rw [← hV]; exact lineVerts_mono (Finset.filter_subset _ _)
    have hfilt : (lineVerts ends pre.toFinset).filter (fun v => id v ∈ t.verts) = t.verts := by
      ext v; simp only [Finset.mem_filter, id]; exact ⟨fun h => h.2, fun h => ⟨hsub h, h⟩⟩
    rw [hfilt]
    unfold conDeg
    rw [hV]
    rfl
  · have hemp : linesIn ends pre.toFinset t = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    obtain ⟨hlines, hverts⟩ := linesIn_eq_empty hK htF hemp
    have hcard : (t.verts.card : ℝ) = 1 := by
      have h := length_lines_add_one (hK.1 t htF)
      rw [hlines] at h
      simp only [List.length_nil, zero_add] at h
      exact_mod_cast h.symm
    have hfilt : (lineVerts ends pre.toFinset).filter (fun v => id v ∈ t.verts) = ∅ := by
      ext v
      simp only [Finset.mem_filter, id, Finset.notMem_empty, iff_false, not_and]
      exact fun h hv => hverts v hv h
    have hfilt2 : pre.toFinset.filter (fun l => (ends l).1 ∈ t.verts) = ∅ := hemp
    rw [hfilt, hfilt2, hcard]
    simp

end Forest

variable {ends}

omit [Fintype V] [DecidableEq V] in
lemma toFinset_take_ofFn (σ : Fin (Fintype.card E) ≃ E) (i : Fin (Fintype.card E)) :
    ((List.ofFn σ).take (i.1 + 1)).toFinset = (Finset.Iic i).image σ := by
  ext l
  rw [List.mem_toFinset, mem_take_ofFn, Finset.mem_image]
  constructor
  · intro h; exact ⟨σ.symm l, Finset.mem_Iic.mpr h, by simp⟩
  · rintro ⟨i', hi', rfl⟩; simpa using hi'

/-- **The prefix sums of the power-counting coefficients**: the tree lines, the touched vertices and the lines of the
prefix `σ 0, …, σ i`. -/
lemma prefixSum_pcCoef_eq (σ : Fin (Fintype.card E) ≃ E) (i : Fin (Fintype.card E)) (d : ℕ) (a : V → ℝ)
    (ω : E → ℝ) :
    prefixSum (pcCoef ends d a ω σ) i =
      d * ((treeLines ends ((List.ofFn σ).take (i.1 + 1))).length : ℝ) +
        ∑ v ∈ lineVerts ends ((List.ofFn σ).take (i.1 + 1)).toFinset, a v -
        ∑ l ∈ ((List.ofFn σ).take (i.1 + 1)).toFinset, ω l := by
  classical
  have hP := toFinset_take_ofFn σ i
  have hnd : (List.ofFn σ).Nodup := List.nodup_ofFn.mpr σ.injective
  have hTLsub := treeLines_sublist ends ((List.ofFn σ).take (i.1 + 1))
  have hTLnd := hTLsub.nodup (hnd.sublist (List.take_sublist _ _))
  unfold prefixSum pcCoef
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  congr 1
  · congr 1
    · -- the tree lines
      rw [← Finset.mul_sum]
      congr 1
      have h1 : ∀ i' ∈ Finset.Iic i, (if σ i' ∈ treeLines ends (List.ofFn σ) then (1 : ℝ) else 0) =
          if σ i' ∈ treeLines ends ((List.ofFn σ).take (i.1 + 1)) then 1 else 0 := fun i' hi' =>
        if_congr (mem_treeLines_ofFn_iff ends σ (Finset.mem_Iic.mp hi')) rfl rfl
      rw [Finset.sum_congr rfl h1, ← Finset.sum_image (f := fun l =>
        if l ∈ treeLines ends ((List.ofFn σ).take (i.1 + 1)) then (1 : ℝ) else 0)
        (fun x _ y _ h => σ.injective h), ← hP, Finset.sum_boole]
      have h2 : ((List.ofFn σ).take (i.1 + 1)).toFinset.filter
          (fun l => l ∈ treeLines ends ((List.ofFn σ).take (i.1 + 1))) =
          (treeLines ends ((List.ofFn σ).take (i.1 + 1))).toFinset := by
        ext l
        simp only [Finset.mem_filter, List.mem_toFinset]
        exact ⟨fun h => h.2, fun h => ⟨hTLsub.subset h, h⟩⟩
      rw [h2, List.toFinset_card_of_nodup hTLnd]
    · -- the vertices, collected where they are first touched
      simp_rw [Finset.sum_filter]
      rw [Finset.sum_comm]
      have hv : ∀ v, ∑ i' ∈ Finset.Iic i,
          (if Incident ends (σ i') v ∧ ∀ i'' < i', ¬ Incident ends (σ i'') v then a v else 0) =
          if v ∈ lineVerts ends ((List.ofFn σ).take (i.1 + 1)).toFinset then a v else 0 := by
        intro v
        split_ifs with hvP
        · obtain ⟨l, hl, hinc⟩ := (mem_lineVerts ends).mp hvP
          have hex : ∃ l, Incident ends l v := ⟨l, hinc⟩
          have hfi : firstIdx ends σ v hex ≤ i := by
            rw [hP] at hl
            obtain ⟨i', hi', rfl⟩ := Finset.mem_image.mp hl
            exact (firstIdx_le σ hex hinc).trans (Finset.mem_Iic.mp hi')
          have h3 : ∀ i' ∈ Finset.Iic i,
              (if Incident ends (σ i') v ∧ ∀ i'' < i', ¬ Incident ends (σ i'') v then a v else 0) =
              if firstIdx ends σ v hex = i' then a v else 0 := fun i' _ => by
            split_ifs with h4 h5 h5
            · rfl
            · exact absurd ((firstIdx_spec σ hex i').mpr h4) h5
            · exact absurd ((firstIdx_spec σ hex i').mp h5) h4
            · rfl
          rw [Finset.sum_congr rfl h3, Finset.sum_ite_eq]
          simp [hfi]
        · refine Finset.sum_eq_zero fun i' hi' => ?_
          rw [ite_eq_right_iff]
          rintro ⟨hinc, -⟩
          exact absurd ((mem_lineVerts ends).mpr ⟨σ i', by rw [hP]; exact Finset.mem_image_of_mem σ hi', hinc⟩) hvP
      rw [Finset.sum_congr rfl fun v _ => hv v, Finset.sum_ite_mem, Finset.univ_inter]
  · -- the lines
    rw [hP, Finset.sum_image (fun x _ y _ h => σ.injective h)]

/-- **The prefix sums are sums of degrees of components** (III (2.16)): the lines `σ 0, …, σ i` split into connected
line sets with pairwise disjoint vertex sets (the components `G_i^(α)`), and the prefix sum of the power-counting
coefficients is the sum of their degrees. -/
theorem prefixSum_pcCoef_components (σ : Fin (Fintype.card E) ≃ E) (i : Fin (Fintype.card E)) (d : ℕ)
    (a : V → ℝ) (ω : E → ℝ) :
    ∃ 𝒞 : Finset (Finset E), (∀ C ∈ 𝒞, ConnLines ends C) ∧
      (∀ C ∈ 𝒞, ∀ C' ∈ 𝒞, C ≠ C' → Disjoint (lineVerts ends C) (lineVerts ends C')) ∧
      𝒞.biUnion id = (Finset.Iic i).image σ ∧
      prefixSum (pcCoef ends d a ω σ) i = ∑ C ∈ 𝒞, conDeg ends d a ω C := by
  classical
  have hP := toFinset_take_ofFn σ i
  obtain ⟨F, hK⟩ := exists_kruskal_forest (ends := ends) ((List.ofFn σ).take (i.1 + 1))
  have hsymm : Std.Symm (fun t t' : MergeTree V E => Disjoint t.verts t'.verts) := ⟨fun _ _ h => h.symm⟩
  have hinj : Set.InjOn (linesIn ends ((List.ofFn σ).take (i.1 + 1)).toFinset)
      (F.toFinset.filter fun t => (linesIn ends ((List.ofFn σ).take (i.1 + 1)).toFinset t).Nonempty) := by
    intro t ht t' ht' h
    obtain ⟨htF, hne⟩ := Finset.mem_filter.mp ht
    obtain ⟨htF', -⟩ := Finset.mem_filter.mp ht'
    obtain ⟨l, hl⟩ := hne
    have h1 := (Finset.mem_filter.mp hl).2
    have h2 := (Finset.mem_filter.mp (h ▸ hl)).2
    exact eq_of_mem_of_mem hK.2.1 (List.mem_toFinset.mp htF) (List.mem_toFinset.mp htF') h1 h2
  refine ⟨(F.toFinset.filter fun t => (linesIn ends ((List.ofFn σ).take (i.1 + 1)).toFinset t).Nonempty).image
    (linesIn ends ((List.ofFn σ).take (i.1 + 1)).toFinset), ?_, ?_, ?_, ?_⟩
  · intro C hC
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hC
    obtain ⟨htF, hne⟩ := Finset.mem_filter.mp ht
    exact connLines_linesIn hK (List.mem_toFinset.mp htF) hne
  · intro C hC C' hC' hne
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hC
    obtain ⟨t', ht', rfl⟩ := Finset.mem_image.mp hC'
    obtain ⟨htF, hn⟩ := Finset.mem_filter.mp ht
    obtain ⟨htF', hn'⟩ := Finset.mem_filter.mp ht'
    rw [lineVerts_linesIn hK (List.mem_toFinset.mp htF) hn, lineVerts_linesIn hK (List.mem_toFinset.mp htF') hn']
    have htt : t ≠ t' := fun h => hne (h ▸ rfl)
    exact hK.2.1.forall (List.mem_toFinset.mp htF) (List.mem_toFinset.mp htF') htt
  · rw [← hP]
    ext l
    simp only [Finset.mem_biUnion, Finset.mem_image, id]
    constructor
    · rintro ⟨C, ⟨t, -, rfl⟩, hl⟩
      exact (Finset.mem_filter.mp hl).1
    · intro hl
      obtain ⟨t, htF, hv⟩ := hK.2.2.1 (ends l).1
      have hlt : l ∈ linesIn ends ((List.ofFn σ).take (i.1 + 1)).toFinset t := Finset.mem_filter.mpr ⟨hl, hv⟩
      exact ⟨_, ⟨t, Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr htF, ⟨l, hlt⟩⟩, rfl⟩, hlt⟩
  · rw [prefixSum_pcCoef_eq, sum_trees_eq hK, Finset.sum_image hinj, Finset.sum_filter]

/-- **A uniform lower bound**: if every connected line set has degree at least `p₀ ≥ 0`, so has every prefix sum of
every ordering (III's degrees of line sets are integers, so positive degrees give `p₀ = 1` for all graphs). -/
theorem prefixSum_ge_of_conDeg_ge {p₀ : ℝ} (hp₀ : 0 ≤ p₀) (d : ℕ) (a : V → ℝ) (ω : E → ℝ)
    (hge : ∀ C, ConnLines ends C → p₀ ≤ conDeg ends d a ω C) (σ : Fin (Fintype.card E) ≃ E)
    (i : Fin (Fintype.card E)) : p₀ ≤ prefixSum (pcCoef ends d a ω σ) i := by
  obtain ⟨𝒞, hconn, -, hcover, hsum⟩ := prefixSum_pcCoef_components (ends := ends) σ i d a ω
  rw [hsum]
  have h : σ i ∈ 𝒞.biUnion id := by
    rw [hcover]; exact Finset.mem_image_of_mem σ (Finset.mem_Iic.mpr le_rfl)
  obtain ⟨C, hC, -⟩ := Finset.mem_biUnion.mp h
  calc p₀ ≤ conDeg ends d a ω C := hge C (hconn C hC)
    _ ≤ ∑ C' ∈ 𝒞, conDeg ends d a ω C' :=
        Finset.single_le_sum (fun C' hC' => hp₀.trans (hge C' (hconn C' hC'))) hC

/-- **Positive degrees give the power-counting hypothesis**: if every connected line set has positive degree (the
hypothesis of III Proposition 2.1 without the exceptional graphs (2.4)), the prefix sums of the power-counting
coefficients of all orderings are bounded below by one `p₀ > 0`. -/
theorem exists_prefixSum_ge (d : ℕ) (a : V → ℝ) (ω : E → ℝ)
    (hpos : ∀ C, ConnLines ends C → 0 < conDeg ends d a ω C) :
    ∃ p₀ : ℝ, 0 < p₀ ∧ ∀ σ i, p₀ ≤ prefixSum (pcCoef ends d a ω σ) i := by
  have hpos' : ∀ σ i, 0 < prefixSum (pcCoef ends d a ω σ) i := by
    intro σ i
    obtain ⟨𝒞, hconn, -, hcover, hsum⟩ := prefixSum_pcCoef_components (ends := ends) σ i d a ω
    rw [hsum]
    have hne : 𝒞.Nonempty := by
      have h : σ i ∈ 𝒞.biUnion id := by
        rw [hcover]; exact Finset.mem_image_of_mem σ (Finset.mem_Iic.mpr le_rfl)
      obtain ⟨C, hC, -⟩ := Finset.mem_biUnion.mp h
      exact ⟨C, hC⟩
    exact Finset.sum_pos (fun C hC => hpos C (hconn C hC)) hne
  by_cases hE : Nonempty (Fin (Fintype.card E))
  · obtain ⟨i₀⟩ := hE
    obtain ⟨⟨σ₀, j₀⟩, -, hmin⟩ := Finset.exists_min_image
      (Finset.univ : Finset ((Fin (Fintype.card E) ≃ E) × Fin (Fintype.card E)))
      (fun p => prefixSum (pcCoef ends d a ω p.1) p.2) ⟨((Fintype.equivFin E).symm, i₀), Finset.mem_univ _⟩
    exact ⟨_, hpos' σ₀ j₀, fun σ i => hmin (σ, i) (Finset.mem_univ _)⟩
  · exact ⟨1, one_pos, fun σ i => absurd ⟨i⟩ hE⟩

omit [DecidableEq E] [Fintype E] in
/-- **A connected line set touches at most one vertex more than it has lines.** -/
theorem card_lineVerts_le {C : Finset E} (hC : ConnLines ends C) : (lineVerts ends C).card ≤ C.card + 1 := by
  classical
  obtain ⟨F, hK⟩ := exists_kruskal_forest (ends := ends) C.toList
  obtain ⟨l₀, hl₀⟩ := hC.1
  obtain ⟨t, htF, ht⟩ := hK.2.2.1 (ends l₀).1
  have hl₀v : (ends l₀).1 ∈ lineVerts ends C := (mem_lineVerts ends).mpr ⟨l₀, hl₀, Or.inl rfl⟩
  have hsub : lineVerts ends C ⊆ t.verts := by
    intro v hv
    obtain ⟨t', ht', h1, h2⟩ := (hK.2.2.2.1 _ _).mp (hC.2 _ hl₀v v hv)
    rwa [eq_of_mem_of_mem hK.2.1 htF ht' ht h1]
  have hlen := length_lines_add_one (hK.1 t htF)
  have htl : t.lines.length ≤ C.card := by
    have h1 : t.lines.length ≤ (F.flatMap lines).length := by
      rw [List.length_flatMap]
      exact List.le_sum_of_mem (List.mem_map_of_mem htF)
    rw [hK.2.2.2.2.length_eq] at h1
    exact h1.trans ((treeLines_sublist ends C.toList).length_le.trans (by simp))
  calc (lineVerts ends C).card ≤ t.verts.card := Finset.card_le_card hsub
    _ = t.lines.length + 1 := hlen.symm
    _ ≤ C.card + 1 := by omega

end GaussianBlockSpin
