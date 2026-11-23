/-
Lattice animals: the connected vertex sets of cardinality `n` containing a vertex of a graph of
degree at most `Δ` number at most `Δ ^ (2 * (n - 1))` (`Balaban.Polymer.card_animals_le`).

Provenance: `Balaban/Polymer/Animals.lean` of https://github.com/scottnarmstrong/balaban-lean at
commit `493e9eb`, Apache License 2.0 (`LICENSE-balaban-lean`), unchanged except that the module
header is replaced by plain imports.
-/
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
/-!
# Lattice animals: connected vertex sets containing a vertex

In a locally finite graph with degrees at most `Δ`, the connected vertex sets of cardinality `n`
containing a fixed vertex `x` form a finite family of cardinality at most `Δ ^ (2 * (n - 1))`:
each such set is the vertex set of a walk of length `2 * (n - 1)` starting at `x`.
-/



namespace Balaban.Polymer

open SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

open Classical in
/-- Pairs (endpoint, support) of the walks of length `L` from `x`. -/
private noncomputable def walkSupports [G.LocallyFinite] : V → ℕ → Finset (V × Finset V)
  | x, 0 => {(x, {x})}
  | x, L + 1 => (G.neighborFinset x).biUnion fun y =>
      (walkSupports y L).image fun p => (p.1, insert x p.2)

open Classical in
private theorem card_walkSupports_le [G.LocallyFinite] {Δ : ℕ} (hΔ : ∀ v, G.degree v ≤ Δ)
    (L : ℕ) : ∀ x, (walkSupports G x L).card ≤ Δ ^ L := by
  induction L with
  | zero => intro x; simp [walkSupports]
  | succ L ih =>
    intro x
    rw [walkSupports]
    calc _ ≤ ∑ y ∈ G.neighborFinset x, ((walkSupports G y L).image
            fun p => (p.1, insert x p.2)).card := Finset.card_biUnion_le
      _ ≤ ∑ _y ∈ G.neighborFinset x, Δ ^ L :=
          Finset.sum_le_sum fun y _ => (Finset.card_image_le).trans (ih y)
      _ = G.degree x * Δ ^ L := by
          rw [Finset.sum_const, smul_eq_mul, card_neighborFinset_eq_degree]
      _ ≤ Δ ^ (L + 1) := by
          rw [pow_succ, mul_comm (Δ ^ L)]
          exact Nat.mul_le_mul_right _ (hΔ x)

open Classical in
private theorem mem_walkSupports [G.LocallyFinite] {x w : V} (p : G.Walk x w) :
    (w, p.support.toFinset) ∈ walkSupports G x p.length := by
  classical
  induction p with
  | nil => simp [walkSupports]
  | @cons a b c h p ih =>
    rw [Walk.length_cons, walkSupports, Finset.mem_biUnion]
    refine ⟨b, (mem_neighborFinset _ _ _).2 h, Finset.mem_image.2 ⟨_, ih, ?_⟩⟩
    simp [Walk.support_cons]

open Classical in
/-- Insert a detour to a neighbour `u` of a vertex `a` visited by a walk. -/
private theorem exists_detour {x e a u : V} (q : G.Walk x e) (ha : a ∈ q.support)
    (h : G.Adj a u) : ∃ p : G.Walk x e, p.length = q.length + 2 ∧
      p.support.toFinset = insert u q.support.toFinset := by
  classical
  induction q with
  | @nil x' =>
    have hax : a = x' := by simpa using ha
    subst hax
    refine ⟨Walk.cons h (Walk.cons h.symm Walk.nil), by simp, ?_⟩
    ext t; simp
  | @cons x' b c hxb q ih =>
    by_cases hax : a = x'
    · subst hax
      refine ⟨Walk.cons h (Walk.cons h.symm (Walk.cons hxb q)), by simp, ?_⟩
      ext t; simp
    · have haq : a ∈ q.support := by
        have h' := ha
        simp only [Walk.support_cons, List.mem_cons] at h'
        tauto
      obtain ⟨p, hl, hs⟩ := ih haq
      refine ⟨Walk.cons hxb p, by simp [hl], ?_⟩
      ext t; simp [hs]; tauto

/-- In a connected induced subgraph with at least two vertices every vertex has a neighbour. -/
private theorem exists_adj_mem_of_connected {S : Finset V}
    (hc : (G.induce (S : Set V)).Connected) (h2 : 2 ≤ S.card) {z : V} (hz : z ∈ S) :
    ∃ z' ∈ S, G.Adj z z' := by
  classical
  obtain ⟨a, ha, hza⟩ := Finset.exists_mem_ne (Nat.lt_of_lt_of_le one_lt_two h2) z
  obtain ⟨p⟩ := hc.preconnected ⟨z, hz⟩ ⟨a, ha⟩
  cases p with
  | nil => exact absurd rfl hza
  | @cons _ v _ hadj q =>
    exact ⟨v.1, v.2, hadj⟩

open Classical in
private theorem exists_walk_of_connected [G.LocallyFinite] (n : ℕ) :
    ∀ (x : V) (S : Finset V), x ∈ S → S.card = n + 1 → (G.induce (S : Set V)).Connected →
      ∃ (w : V) (p : G.Walk x w), p.length = 2 * n ∧ p.support.toFinset = S := by
  classical
  induction n with
  | zero =>
    intro x S hx hc _
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 hc
    obtain rfl := Finset.mem_singleton.1 hx
    exact ⟨x, Walk.nil, by simp, by simp⟩
  | succ n ih =>
    intro x S hx hc hconn
    have h2 : 2 ≤ S.card := by omega
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 (by omega : 1 < S.card)
    have : Nontrivial (↥(S : Set V)) := ⟨⟨⟨a, ha⟩, ⟨b, hb⟩, fun h => hab (congrArg Subtype.val h)⟩⟩
    have : Finite (↥(S : Set V)) := inferInstance
    obtain ⟨u, hu⟩ := hconn.exists_connected_induce_compl_singleton_of_finite_nontrivial
    have huS : u.1 ∈ S := u.2
    have hcard : (S.erase u.1).card = n + 1 := by rw [Finset.card_erase_of_mem huS]; omega
    let f : (G.induce (S : Set V)).induce {u}ᶜ →g G.induce ((S.erase u.1 : Finset V) : Set V) :=
      { toFun := fun v => ⟨v.1.1, by
          have := v.2
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at this
          simp only [Finset.coe_erase, Set.mem_sdiff, Finset.mem_coe, Set.mem_singleton_iff]
          exact ⟨v.1.2, fun h => this (Subtype.ext h)⟩⟩
        map_rel' := fun {a b} h => by simpa using h }
    have hf : Function.Surjective f := by
      rintro ⟨y, hy⟩
      have hy' : y ∈ S.erase u.1 := hy
      rw [Finset.mem_erase] at hy'
      exact ⟨⟨⟨y, hy'.2⟩, fun h => hy'.1 (congrArg Subtype.val h)⟩, rfl⟩
    have hconn' : (G.induce ((S.erase u.1 : Finset V) : Set V)).Connected := hu.map f hf
    by_cases hux : u.1 = x
    · rw [hux] at huS hcard
      have hxe : x ∉ S.erase x := Finset.notMem_erase _ _
      obtain ⟨y, hyS, hxy⟩ := exists_adj_mem_of_connected G hconn h2 hx
      have hyx : y ≠ x := fun h => G.loopless.irrefl x (h ▸ hxy)
      have hyE : y ∈ S.erase x := Finset.mem_erase.2 ⟨hyx, hyS⟩
      obtain ⟨z, q, hlen, hsup⟩ := ih y (S.erase x) hyE hcard (hux ▸ hconn')
      have hzE : z ∈ S.erase x := by
        rw [← hsup]; simp
      obtain ⟨z', hz'S, hzz'⟩ :=
        exists_adj_mem_of_connected G hconn h2 (Finset.mem_of_mem_erase hzE)
      refine ⟨z', (Walk.cons hxy q).concat hzz', by simp [hlen]; omega, ?_⟩
      have hmem : ∀ t, t ∈ q.support ↔ t ∈ S.erase x := fun t => by rw [← hsup]; simp
      ext t
      simp only [Walk.support_concat, Walk.support_cons, 
        List.mem_toFinset, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, hmem,
        Finset.mem_erase]
      constructor
      · rintro ((h | h) | h)
        · exact h ▸ hx
        · exact h.2
        · exact h ▸ hz'S
      · intro h
        by_cases htx : t = x
        · exact Or.inl (Or.inl htx)
        · exact Or.inl (Or.inr ⟨htx, h⟩)
    · have hxE : x ∈ S.erase u.1 := Finset.mem_erase.2 ⟨fun h => hux h.symm, hx⟩
      obtain ⟨w, q, hlen, hsup⟩ := ih x (S.erase u.1) hxE hcard hconn'
      obtain ⟨a, haS, hua⟩ := exists_adj_mem_of_connected G hconn h2 huS
      have haE : a ∈ S.erase u.1 :=
        Finset.mem_erase.2 ⟨fun h => G.loopless.irrefl u.1 (h ▸ hua), haS⟩
      have haq : a ∈ q.support := by rw [← List.mem_toFinset, hsup]; exact haE
      obtain ⟨p, hl, hs⟩ := exists_detour G q haq hua.symm
      refine ⟨w, p, by omega, ?_⟩
      rw [hs, hsup, Finset.insert_erase huS]

theorem finite_setOf_connected_induce [G.LocallyFinite] (x : V) (n : ℕ) :
    {S : Finset V | x ∈ S ∧ S.card = n ∧ (G.induce (S : Set V)).Connected}.Finite := by
  classical
  cases n with
  | zero =>
    refine Set.Finite.subset Set.finite_empty ?_
    rintro S ⟨hx, hc, -⟩
    simp [Finset.card_eq_zero.1 hc] at hx
  | succ n =>
    refine Set.Finite.subset
      (((walkSupports G x (2 * n)).image Prod.snd).finite_toSet) ?_
    rintro S ⟨hx, hc, hconn⟩
    obtain ⟨w, p, hlen, hsup⟩ := exists_walk_of_connected G n x S hx hc hconn
    have := mem_walkSupports G p
    rw [hlen, hsup] at this
    exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨_, this, rfl⟩)

/-- The finite connected vertex sets of cardinality `n` containing `x` (lattice animals). -/
noncomputable def animals [G.LocallyFinite] (x : V) (n : ℕ) : Finset (Finset V) :=
  (finite_setOf_connected_induce G x n).toFinset

theorem mem_animals [G.LocallyFinite] {x : V} {n : ℕ} {S : Finset V} :
    S ∈ animals G x n ↔ x ∈ S ∧ S.card = n ∧ (G.induce (S : Set V)).Connected := by
  simp [animals]

theorem card_animals_le [G.LocallyFinite] {Δ : ℕ} (hΔ : ∀ v, G.degree v ≤ Δ) (x : V) (n : ℕ) :
    (animals G x n).card ≤ Δ ^ (2 * (n - 1)) := by
  classical
  cases n with
  | zero =>
    have : animals G x 0 = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun S hS => ?_
      obtain ⟨hx, hc, -⟩ := (mem_animals G).1 hS
      simp [Finset.card_eq_zero.1 hc] at hx
    simp [this]
  | succ n =>
    have hsub : animals G x (n + 1) ⊆ (walkSupports G x (2 * n)).image Prod.snd := by
      intro S hS
      obtain ⟨hx, hc, hconn⟩ := (mem_animals G).1 hS
      obtain ⟨w, p, hlen, hsup⟩ := exists_walk_of_connected G n x S hx hc hconn
      have := mem_walkSupports G p
      rw [hlen, hsup] at this
      exact Finset.mem_image.2 ⟨_, this, rfl⟩
    calc _ ≤ _ := Finset.card_le_card hsub
      _ ≤ (walkSupports G x (2 * n)).card := Finset.card_image_le
      _ ≤ Δ ^ (2 * n) := card_walkSupports_le G hΔ _ x
      _ = Δ ^ (2 * (n + 1 - 1)) := by simp

end Balaban.Polymer
