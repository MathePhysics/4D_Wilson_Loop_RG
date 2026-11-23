import Mathlib

/-! **Spatial sums along a merge tree** (the summations over localisations in III (2.15)-(2.16)): binary merge trees
(a leaf is a vertex; a node joins two trees with disjoint vertex sets by a line), and the bound
`(∫⋯∫⁻_{verts t \ {r}} ∏_{l ∈ lines t} w_l) ≤ ∏_{l ∈ lines t} B_l` for every root `r`, whenever
`∫ w_l(y, ·) dν ≤ B_l` and `∫ w_l(·, y) dν ≤ B_l` for all `y` (lmarginal_tree_le); positions in a countable
discrete space with a measure `ν` (for a lattice of spacing `η`, `ν` = `η^d` times counting measure). -/

namespace GaussianBlockSpin

open MeasureTheory Function
open scoped ENNReal

/-- Binary merge trees: leaves are vertices, a node joins two trees by a line. -/
inductive MergeTree (V E : Type*) where
  | leaf (v : V)
  | node (l : E) (t₁ t₂ : MergeTree V E)

namespace MergeTree

variable {V E : Type*} [DecidableEq V]

/-- The vertices of a merge tree. -/
def verts : MergeTree V E → Finset V
  | leaf v => {v}
  | node _ t₁ t₂ => verts t₁ ∪ verts t₂

/-- The lines of a merge tree. -/
def lines : MergeTree V E → List E
  | leaf _ => []
  | node l t₁ t₂ => l :: (lines t₁ ++ lines t₂)

/-- Well-formed: the subtrees of every node have disjoint vertex sets and the node line joins them. -/
def WF (ends : E → V × V) : MergeTree V E → Prop
  | leaf _ => True
  | node l t₁ t₂ => WF ends t₁ ∧ WF ends t₂ ∧ Disjoint (verts t₁) (verts t₂) ∧
      (((ends l).1 ∈ verts t₁ ∧ (ends l).2 ∈ verts t₂) ∨ ((ends l).2 ∈ verts t₁ ∧ (ends l).1 ∈ verts t₂))

lemma ends_mem_verts {ends : E → V × V} : ∀ {t : MergeTree V E}, t.WF ends → ∀ l ∈ t.lines,
    (ends l).1 ∈ t.verts ∧ (ends l).2 ∈ t.verts
  | leaf _, _, l, hl => by simp [lines] at hl
  | node l' t₁ t₂, ⟨h₁, h₂, _, hl'⟩, l, hl => by
    simp only [lines, List.mem_cons, List.mem_append] at hl
    simp only [verts, Finset.mem_union]
    rcases hl with rfl | hl | hl
    · rcases hl' with ⟨a, b⟩ | ⟨a, b⟩ <;> tauto
    · obtain ⟨a, b⟩ := ends_mem_verts h₁ l hl; exact ⟨Or.inl a, Or.inl b⟩
    · obtain ⟨a, b⟩ := ends_mem_verts h₂ l hl; exact ⟨Or.inr a, Or.inr b⟩

end MergeTree

section Marginal

variable {ι X : Type*} [DecidableEq ι] [MeasurableSpace X] (ν : Measure X)

/-- A factor that does not depend on the integrated coordinates comes out of the partial integral. -/
lemma lmarginal_mul_left_of_dependsOn {s : Finset ι} {c f : (ι → X) → ℝ≥0∞} (hc : DependsOn c ((s : Set ι)ᶜ))
    (hf : Measurable f) :
    ∫⋯∫⁻_s, (fun x => c x * f x) ∂(fun _ => ν) = fun x => c x * (∫⋯∫⁻_s, f ∂(fun _ => ν)) x := by
  ext x
  have h : ∀ y : (i : s) → X, c (updateFinset x s y) = c x := fun y =>
    hc fun i hi => by simp [updateFinset_def, Finset.mem_coe.not.mp hi]
  simp only [lmarginal, h]
  exact lintegral_const_mul _ (hf.comp measurable_updateFinset)

end Marginal

open MergeTree

variable {V E X : Type*} [DecidableEq V] [Fintype V] [MeasurableSpace X] [MeasurableSingletonClass X] [Countable X]
  (ν : Measure X) [SigmaFinite ν] (ends : E → V × V) (w : E → X → X → ℝ≥0∞)

/-- The product of the line weights of a merge tree at the positions `x`. -/
noncomputable def treeWeight (t : MergeTree V E) (x : V → X) : ℝ≥0∞ :=
  (t.lines.map fun l => w l (x (ends l).1) (x (ends l).2)).prod

omit [Fintype V] [MeasurableSpace X] [MeasurableSingletonClass X] [Countable X] in
lemma dependsOn_treeWeight {t : MergeTree V E} (ht : t.WF ends) :
    DependsOn (treeWeight ends w t) (t.verts : Set V) := by
  intro x y hxy
  unfold treeWeight
  congr 1
  refine List.map_congr_left fun l hl => ?_
  obtain ⟨h1, h2⟩ := ends_mem_verts ht l hl
  rw [hxy _ (Finset.mem_coe.mpr h1), hxy _ (Finset.mem_coe.mpr h2)]

omit [DecidableEq V] [SigmaFinite ν] in
lemma measurable_of_countable_pi (f : (V → X) → ℝ≥0∞) : Measurable f := measurable_of_countable f

/-- The bound on the line weights of a tree. -/
noncomputable def treeBound (B : E → ℝ≥0∞) (t : MergeTree V E) : ℝ≥0∞ := (t.lines.map B).prod

variable {ν ends w}

/-- The node step, for a root in the first subtree. -/
lemma lmarginal_node_le {B : E → ℝ≥0∞} (hB₁ : ∀ l y, ∫⁻ x', w l y x' ∂ν ≤ B l)
    (hB₂ : ∀ l y, ∫⁻ x', w l x' y ∂ν ≤ B l) {l : E} {t₁ t₂ : MergeTree V E}
    (ih₁ : ∀ r ∈ t₁.verts, ∀ x, (∫⋯∫⁻_(t₁.verts.erase r), treeWeight ends w t₁ ∂(fun _ => ν)) x ≤ treeBound B t₁)
    (ih₂ : ∀ r ∈ t₂.verts, ∀ x, (∫⋯∫⁻_(t₂.verts.erase r), treeWeight ends w t₂ ∂(fun _ => ν)) x ≤ treeBound B t₂)
    (hwf : (node l t₁ t₂).WF ends) {r : V} (hr : r ∈ t₁.verts) (x : V → X) :
    (∫⋯∫⁻_((node l t₁ t₂).verts.erase r), treeWeight ends w (node l t₁ t₂) ∂(fun _ => ν)) x ≤
      treeBound B (node l t₁ t₂) := by
  obtain ⟨hw₁, hw₂, hdisj, hl⟩ := hwf
  have hr₂ : r ∉ t₂.verts := Finset.disjoint_left.mp hdisj hr
  -- the endpoints of the node line
  obtain ⟨u₁, u₂, hu₁, hu₂, hwl⟩ : ∃ u₁ u₂, u₁ ∈ t₁.verts ∧ u₂ ∈ t₂.verts ∧
      ((∀ y : V → X, w l (y (ends l).1) (y (ends l).2) = w l (y u₁) (y u₂)) ∧
        (∀ a, ∫⁻ x', w l a x' ∂ν ≤ B l) ∨
      (∀ y : V → X, w l (y (ends l).1) (y (ends l).2) = w l (y u₂) (y u₁)) ∧
        (∀ a, ∫⁻ x', w l x' a ∂ν ≤ B l)) := by
    rcases hl with ⟨a, b⟩ | ⟨a, b⟩
    · exact ⟨_, _, a, b, Or.inl ⟨fun y => rfl, hB₁ l⟩⟩
    · exact ⟨_, _, a, b, Or.inr ⟨fun y => rfl, hB₂ l⟩⟩
  have hu₁₂ : u₁ ≠ u₂ := fun h => Finset.disjoint_left.mp hdisj hu₁ (h ▸ hu₂)
  set F₁ := treeWeight ends w t₁ with hF₁
  set F₂ := treeWeight ends w t₂ with hF₂
  set W : (V → X) → ℝ≥0∞ := fun y => w l (y (ends l).1) (y (ends l).2) with hW
  have hsplit : treeWeight ends w (node l t₁ t₂) = fun y => (W y * F₁ y) * F₂ y := by
    funext y
    simp only [treeWeight, lines, List.map_cons, List.prod_cons, List.map_append, List.prod_append, hW, hF₁, hF₂]
    ring
  have hdep₁ := dependsOn_treeWeight ends w hw₁
  have hdep₂ := dependsOn_treeWeight ends w hw₂
  -- the coordinate sets
  set A := t₁.verts.erase r with hA
  set Bu := t₂.verts.erase u₂ with hBu
  have hverts : (node l t₁ t₂).verts.erase r = A ∪ insert u₂ Bu := by
    rw [hA, hBu, Finset.insert_erase hu₂]
    simp only [verts]
    rw [Finset.erase_union_distrib, Finset.erase_eq_of_notMem hr₂]
  have hAB : Disjoint A (insert u₂ Bu) := by
    rw [hBu, Finset.insert_erase hu₂]
    exact Finset.disjoint_of_subset_left (Finset.erase_subset _ _) hdisj
  -- step 1: the coordinates of t₂ other than u₂
  have hstep1 : ∀ y, (∫⋯∫⁻_Bu, treeWeight ends w (node l t₁ t₂) ∂(fun _ => ν)) y ≤
      W y * F₁ y * treeBound B t₂ := by
    intro y
    have hc : DependsOn (fun y => W y * F₁ y) ((Bu : Set V)ᶜ) := by
      intro a b hab
      have hWab : W a = W b := by
        rcases hwl with ⟨h, -⟩ | ⟨h, -⟩
        · rw [hW]; simp only; rw [h a, h b, hab u₁ (by simp [hBu, hu₁₂, Finset.disjoint_left.mp hdisj hu₁]), hab u₂ (by simp [hBu])]
        · rw [hW]; simp only; rw [h a, h b, hab u₁ (by simp [hBu, hu₁₂, Finset.disjoint_left.mp hdisj hu₁]), hab u₂ (by simp [hBu])]
      show W a * F₁ a = W b * F₁ b
      rw [hWab]
      congr 1
      exact hdep₁ fun i hi => hab i (fun hiB => Finset.disjoint_left.mp hdisj hi
        (Finset.mem_of_mem_erase (Finset.mem_coe.mp hiB)))
    rw [hsplit, lmarginal_mul_left_of_dependsOn ν hc (measurable_of_countable _)]
    exact mul_le_mul_of_nonneg_left (ih₂ u₂ hu₂ y) bot_le
  -- step 2: the coordinate u₂
  have hstep2 : ∀ y, (∫⋯∫⁻_(insert u₂ Bu), treeWeight ends w (node l t₁ t₂) ∂(fun _ => ν)) y ≤
      F₁ y * (treeBound B t₂ * B l) := by
    intro y
    have hu₂Bu : u₂ ∉ Bu := by simp [hBu]
    rw [lmarginal_insert _ (measurable_of_countable _) hu₂Bu]
    have hF₁u : ∀ z, F₁ (Function.update y u₂ z) = F₁ y := fun z =>
      hdep₁ fun i hi => by
        have : i ≠ u₂ := fun h => Finset.disjoint_left.mp hdisj (Finset.mem_coe.mp hi) (h ▸ hu₂)
        simp [Function.update_of_ne this]
    calc ∫⁻ z, (∫⋯∫⁻_Bu, treeWeight ends w (node l t₁ t₂) ∂(fun _ => ν)) (Function.update y u₂ z) ∂ν
        ≤ ∫⁻ z, W (Function.update y u₂ z) * F₁ y * treeBound B t₂ ∂ν := by
          refine lintegral_mono fun z => ?_
          have h := hstep1 (Function.update y u₂ z)
          rwa [hF₁u z] at h
      _ = F₁ y * treeBound B t₂ * ∫⁻ z, W (Function.update y u₂ z) ∂ν := by
          rw [← lintegral_const_mul _ (measurable_of_countable _)]
          refine lintegral_congr fun z => ?_
          ring
      _ ≤ F₁ y * treeBound B t₂ * B l := by
          refine mul_le_mul_of_nonneg_left ?_ bot_le
          rcases hwl with ⟨h, hB⟩ | ⟨h, hB⟩
          · have : ∀ z, W (Function.update y u₂ z) = w l (y u₁) z := fun z => by
              rw [hW]; simp only; rw [h, Function.update_self, Function.update_of_ne hu₁₂]
            simp_rw [this]; exact hB _
          · have : ∀ z, W (Function.update y u₂ z) = w l z (y u₁) := fun z => by
              rw [hW]; simp only; rw [h, Function.update_self, Function.update_of_ne hu₁₂]
            simp_rw [this]; exact hB _
      _ = F₁ y * (treeBound B t₂ * B l) := by ring
  -- step 3: the coordinates of t₁ other than r
  rw [hverts, lmarginal_union (fun _ => ν) _ (measurable_of_countable _) hAB]
  calc (∫⋯∫⁻_A, (∫⋯∫⁻_(insert u₂ Bu), treeWeight ends w (node l t₁ t₂) ∂(fun _ => ν)) ∂(fun _ => ν)) x
      ≤ (∫⋯∫⁻_A, (fun y => (treeBound B t₂ * B l) * F₁ y) ∂(fun _ => ν)) x := by
        refine lmarginal_mono (fun y => ?_) x
        calc _ ≤ F₁ y * (treeBound B t₂ * B l) := hstep2 y
          _ = _ := mul_comm _ _
    _ = (treeBound B t₂ * B l) * (∫⋯∫⁻_A, F₁ ∂(fun _ => ν)) x := by
        rw [lmarginal_mul_left_of_dependsOn ν (c := fun _ => treeBound B t₂ * B l) (fun _ _ _ => rfl)
          (measurable_of_countable _)]
    _ ≤ (treeBound B t₂ * B l) * treeBound B t₁ := mul_le_mul_of_nonneg_left (ih₁ r hr x) bot_le
    _ = treeBound B (node l t₁ t₂) := by
        simp only [treeBound, lines, List.map_cons, List.prod_cons, List.map_append, List.prod_append]
        ring

/-- **The spatial sum along a merge tree**: for every root `r`, integrating the positions of the other vertices of
the tree gives at most the product of the line bounds. -/
theorem lmarginal_tree_le {B : E → ℝ≥0∞} (hB₁ : ∀ l y, ∫⁻ x', w l y x' ∂ν ≤ B l)
    (hB₂ : ∀ l y, ∫⁻ x', w l x' y ∂ν ≤ B l) : ∀ (t : MergeTree V E), t.WF ends → ∀ r ∈ t.verts, ∀ x : V → X,
    (∫⋯∫⁻_(t.verts.erase r), treeWeight ends w t ∂(fun _ => ν)) x ≤ treeBound B t
  | leaf v, _, r, hr, x => by
    simp only [verts, Finset.mem_singleton] at hr
    subst hr
    simp [verts, treeWeight, treeBound, lines]
  | node l t₁ t₂, hwf, r, hr, x => by
    have ih₁ := lmarginal_tree_le hB₁ hB₂ t₁ hwf.1
    have ih₂ := lmarginal_tree_le hB₁ hB₂ t₂ hwf.2.1
    rcases Finset.mem_union.mp hr with h | h
    · exact lmarginal_node_le hB₁ hB₂ ih₁ ih₂ hwf h x
    · have hswap : treeWeight ends w (node l t₁ t₂) = treeWeight ends w (node l t₂ t₁) := by
        funext y
        simp only [treeWeight, lines, List.map_cons, List.prod_cons, List.map_append, List.prod_append]
        ring
      have hv : (node l t₁ t₂).verts = (node l t₂ t₁).verts := Finset.union_comm _ _
      have hb : treeBound B (node l t₁ t₂) = treeBound B (node l t₂ t₁) := by
        simp only [treeBound, lines, List.map_cons, List.prod_cons, List.map_append, List.prod_append]
        ring
      have hwf' : (node l t₂ t₁).WF ends := by
        obtain ⟨h₁, h₂, hd, hl⟩ := hwf
        exact ⟨h₂, h₁, hd.symm, by tauto⟩
      rw [hswap, hv, hb]
      exact lmarginal_node_le hB₁ hB₂ ih₂ ih₁ hwf' h x

end GaussianBlockSpin
