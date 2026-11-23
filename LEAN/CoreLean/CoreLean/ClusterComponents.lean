/-
The decomposition of a graph by the connected component of a vertex, for the exponential formula in the proof of
`thm:polymer-logarithm` of BALABAN_CORE.tex (`5bbe1bc62521`): for weights `f` on the pairs of a finite set `ι` and a
vertex `r`, `Σ_gΠ_{e ∈ g}f(e) = Σ_{B ∋ r}(Σ_{g₁ connected on B}Π_{g₁}f)(Σ_{g₂ on ι∖B}Π_{g₂}f)`, the sums over the graphs
(sets of pairs `{x, y}`, `x ≠ y`) with the given vertex sets. The graph `g` corresponds to its component `B` of `r`, the
edges of `g` inside `B`, and the edges of `g` outside `B`.
-/
import CoreLean.ClusterTreeGraph

open Finset

noncomputable section

namespace CoreLean
namespace TreeGraph

open Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The pairs `{x, y}`, `x ≠ y`, with both ends in `B`. -/
def pairsIn (B : Finset ι) : Finset (Sym2 ι) := Finset.univ.filter fun e => ¬e.IsDiag ∧ ∀ x ∈ e, x ∈ B

/-- The component of `r` in the graph `g`. -/
def comp (r : ι) (g : Finset (Sym2 ι)) : Finset ι :=
  Finset.univ.filter fun x => Relation.ReflTransGen (Adj id g) r x

lemma adj_id {g : Finset (Sym2 ι)} {x y : ι} : Adj id g x y ↔ s(x, y) ∈ g := by
  unfold Adj; constructor
  · rintro ⟨e, he, rfl⟩; exact he
  · intro h; exact ⟨_, h, rfl⟩

lemma mem_comp_of_adj {r : ι} {g : Finset (Sym2 ι)} {x y : ι} (hx : x ∈ comp r g) (h : s(x, y) ∈ g) :
    y ∈ comp r g := by
  simp only [comp, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  exact hx.tail (adj_id.2 h)

/-- An edge of `g` has both ends in the component of `r` or both outside. -/
lemma edge_side {r : ι} {g : Finset (Sym2 ι)} {x y : ι} (h : s(x, y) ∈ g) :
    (x ∈ comp r g ↔ y ∈ comp r g) := by
  constructor
  · intro hx; exact mem_comp_of_adj hx h
  · intro hy; exact mem_comp_of_adj hy (by rw [Sym2.eq_swap]; exact h)

/-- The graph `g ∩ pairsIn (comp r g)` connects `r` to every point of the component. -/
lemma reach_inside {r : ι} {g : Finset (Sym2 ι)} (hg : g ⊆ pairsIn Finset.univ) {x : ι}
    (hx : Relation.ReflTransGen (Adj id g) r x) :
    Relation.ReflTransGen (Adj id (g.filter fun e => e ∈ pairsIn (comp r g))) r x := by
  induction hx with
  | refl => exact Relation.ReflTransGen.refl
  | @tail a b hra hab ih =>
    refine ih.tail (adj_id.2 ?_)
    have he := adj_id.1 hab
    refine Finset.mem_filter.2 ⟨he, ?_⟩
    have hd := (Finset.mem_filter.1 (hg he)).2.1
    have ha : a ∈ comp r g := by simp only [comp, Finset.mem_filter, Finset.mem_univ, true_and]; exact hra
    simp only [pairsIn, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨hd, fun z hz => ?_⟩
    rcases Sym2.mem_iff.1 hz with rfl | rfl
    · exact ha
    · exact mem_comp_of_adj ha he

lemma rtg_mono {g g' : Finset (Sym2 ι)} (h : g ⊆ g') {x y : ι}
    (hxy : Relation.ReflTransGen (Adj id g) x y) : Relation.ReflTransGen (Adj id g') x y := by
  induction hxy with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hab ih => exact ih.tail (adj_id.2 (h (adj_id.1 hab)))

lemma adj_symm {g : Finset (Sym2 ι)} : Symmetric (Adj id g) := fun x y h =>
  adj_id.2 (by rw [Sym2.eq_swap]; exact adj_id.1 h)

lemma rtg_symm {g : Finset (Sym2 ι)} {x y : ι} (h : Relation.ReflTransGen (Adj id g) x y) :
    Relation.ReflTransGen (Adj id g) y x := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hab ih => exact Relation.ReflTransGen.head (adj_symm hab) ih

lemma pairsIn_disjoint (B : Finset ι) : Disjoint (pairsIn B) (pairsIn Bᶜ) := by
  rw [Finset.disjoint_left]
  intro e h1 h2
  simp only [pairsIn, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
  obtain ⟨x, hx⟩ : ∃ x, x ∈ e := by
    induction e using Sym2.ind with
    | h a b => exact ⟨a, Sym2.mem_mk_left a b⟩
  exact Finset.mem_compl.1 (h2.2 x hx) (h1.2 x hx)

lemma pairsIn_mono {B B' : Finset ι} (h : B ⊆ B') : pairsIn B ⊆ pairsIn B' := by
  intro e he
  simp only [pairsIn, Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
  exact ⟨he.1, fun x hx => h (he.2 x hx)⟩

/-- For `r ∈ B`, `g₁` connected on `B` and `g₂` outside `B`, the component of `r` in `g₁ ∪ g₂` is `B`. -/
lemma comp_union {r : ι} {B : Finset ι} (hr : r ∈ B) {g1 g2 : Finset (Sym2 ι)} (h1 : g1 ⊆ pairsIn B)
    (hc : Conn B id g1) (h2 : g2 ⊆ pairsIn Bᶜ) : comp r (g1 ∪ g2) = B := by
  ext x
  simp only [comp, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hx
    induction hx with
    | refl => exact hr
    | @tail a b _ hab ih =>
      have he := adj_id.1 hab
      rcases Finset.mem_union.1 he with he | he
      · exact (Finset.mem_filter.1 (h1 he)).2.2 b (Sym2.mem_mk_right a b)
      · exact absurd ih (Finset.mem_compl.1 ((Finset.mem_filter.1 (h2 he)).2.2 a (Sym2.mem_mk_left a b)))
  · intro hx
    exact rtg_mono Finset.subset_union_left (hc r hr x hx)

/-- **The decomposition by the component of `r`.** -/
theorem graph_decomp {R : Type*} [CommRing R] (r : ι) (f : Sym2 ι → R) :
    ∑ g ∈ (pairsIn (Finset.univ : Finset ι)).powerset, ∏ e ∈ g, f e =
      ∑ B ∈ (Finset.univ : Finset (Finset ι)).filter (fun B => r ∈ B),
        (∑ g1 ∈ (pairsIn B).powerset.filter (fun g1 => Conn B id g1), ∏ e ∈ g1, f e) *
          (∑ g2 ∈ (pairsIn Bᶜ).powerset, ∏ e ∈ g2, f e) := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := (pairsIn (Finset.univ : Finset ι)).powerset)
    (t := (Finset.univ : Finset (Finset ι)).filter (fun B => r ∈ B)) (g := comp r)
    (fun g _ => Finset.mem_filter.2 ⟨Finset.mem_univ _, by
      simp only [comp, Finset.mem_filter, Finset.mem_univ, true_and]; exact Relation.ReflTransGen.refl⟩)]
  refine Finset.sum_congr rfl fun B hB => ?_
  have hrB : r ∈ B := (Finset.mem_filter.1 hB).2
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  have hsplit : ∀ g ∈ (pairsIn (Finset.univ : Finset ι)).powerset.filter (fun g => comp r g = B),
      g.filter (· ∈ pairsIn B) ∪ g.filter (· ∈ pairsIn Bᶜ) = g := by
    intro g hg
    simp only [Finset.mem_filter, Finset.mem_powerset] at hg
    obtain ⟨hgU, hgB⟩ := hg
    ext e
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨he, _⟩ | ⟨he, _⟩) <;> exact he
    · intro he
      have hd := (Finset.mem_filter.1 (hgU he)).2.1
      obtain ⟨x, y, rfl⟩ : ∃ x y, e = s(x, y) := by
        induction e using Sym2.ind with
        | h a b => exact ⟨a, b, rfl⟩
      by_cases hx : x ∈ comp r g
      · left
        refine ⟨he, ?_⟩
        simp only [pairsIn, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨hd, fun z hz => ?_⟩
        rw [← hgB]
        rcases Sym2.mem_iff.1 hz with rfl | rfl
        · exact hx
        · exact (edge_side he).1 hx
      · right
        refine ⟨he, ?_⟩
        simp only [pairsIn, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨hd, fun z hz => ?_⟩
        rw [Finset.mem_compl, ← hgB]
        rcases Sym2.mem_iff.1 hz with rfl | rfl
        · exact hx
        · exact fun h => hx ((edge_side he).2 h)
  refine Finset.sum_bij' (fun g _ => (g.filter (· ∈ pairsIn B), g.filter (· ∈ pairsIn Bᶜ)))
    (fun p _ => p.1 ∪ p.2) ?_ ?_ ?_ ?_ ?_
  · -- the image lies in the product
    intro g hg
    simp only [Finset.mem_filter, Finset.mem_powerset] at hg
    obtain ⟨hgU, hgB⟩ := hg
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_powerset]
    refine ⟨⟨fun e he => (Finset.mem_filter.1 he).2, ?_⟩, fun e he => (Finset.mem_filter.1 he).2⟩
    intro x hx y hy
    rw [← hgB] at hx hy
    simp only [comp, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
    have hx' := reach_inside hgU hx
    have hy' := reach_inside hgU hy
    rw [hgB] at hx' hy'
    exact (rtg_symm hx').trans hy'
  · -- the preimage lies in the fibre
    intro p hp
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_powerset] at hp
    obtain ⟨⟨h1, hc⟩, h2⟩ := hp
    simp only [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨Finset.union_subset (h1.trans (pairsIn_mono (Finset.subset_univ _)))
      (h2.trans (pairsIn_mono (Finset.subset_univ _))), comp_union hrB h1 hc h2⟩
  · exact hsplit
  · -- the other composition
    intro p hp
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_powerset] at hp
    obtain ⟨⟨h1, _⟩, h2⟩ := hp
    have hd := pairsIn_disjoint B
    ext e <;> simp only [Finset.mem_filter, Finset.mem_union]
    · constructor
      · rintro ⟨he | he, hB⟩
        · exact he
        · exact absurd hB (Finset.disjoint_right.1 hd (h2 he))
      · intro he; exact ⟨Or.inl he, h1 he⟩
    · constructor
      · rintro ⟨he | he, hB⟩
        · exact absurd hB (Finset.disjoint_left.1 hd (h1 he))
        · exact he
      · intro he; exact ⟨Or.inr he, h2 he⟩
  · -- the weights
    intro g hg
    rw [← Finset.prod_union (Finset.disjoint_filter.2 fun e _ h1 h2 =>
      Finset.disjoint_left.1 (pairsIn_disjoint B) h1 h2), hsplit g hg]

end TreeGraph
end CoreLean

end
