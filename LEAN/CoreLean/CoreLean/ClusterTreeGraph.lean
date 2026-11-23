/-
The tree-graph bound of `lem:cluster-bounds` of BALABAN_CORE.tex (`5bbe1bc62521`): `|ρ^T(Z_1, …, Z_m)| ≤ τ(Z_1, …, Z_m)`,
the number of the spanning trees of the graph of incompatibility, and the sign `(-1)^{m-1}ρ^T ≥ 0`.

The core proves the bound by the partition scheme of Penrose. We prove it by deletion and contraction on multigraphs,
`ρ(G) = ρ(G - e) - ρ(G/e)` and `τ(G) = τ(G - e) + τ(G/e)` for an edge `e` which is not a loop, and `ρ(G) = 0` if `G` has
a loop; here `ρ(G) = Σ_S(-1)^{#S}` over the edge sets `S` of the connected spanning subgraphs and `τ(G)` is the number of
the connected spanning edge sets with `#V - 1` edges. A multigraph is a finite set of vertices `Vs ⊆ α`, a finite set of
edge labels `Es ⊆ β`, and the ends `β → Sym2 α`; the contraction of `e = {u, v}` maps `v` to `u`.
-/
import Mathlib

open Finset

noncomputable section

namespace CoreLean
namespace TreeGraph

open Classical

variable {α β : Type*}

/-- Adjacency through the edges of `S`. -/
def Adj (ends : β → Sym2 α) (S : Finset β) (x y : α) : Prop := ∃ e ∈ S, ends e = s(x, y)

/-- The spanning subgraph with the edges `S` is connected on `Vs`. -/
def Conn (Vs : Finset α) (ends : β → Sym2 α) (S : Finset β) : Prop :=
  ∀ x ∈ Vs, ∀ y ∈ Vs, Relation.ReflTransGen (Adj ends S) x y

/-- `ρ(G) = Σ_S(-1)^{#S}` over the connected spanning edge sets. -/
def rho (Vs : Finset α) (Es : Finset β) (ends : β → Sym2 α) : ℤ :=
  ∑ S ∈ Es.powerset.filter (fun S => Conn Vs ends S), (-1) ^ S.card

/-- The number of the spanning trees: connected spanning edge sets with `#V - 1` edges. -/
def tau (Vs : Finset α) (Es : Finset β) (ends : β → Sym2 α) : ℕ :=
  (Es.powerset.filter (fun S => Conn Vs ends S ∧ S.card + 1 = Vs.card)).card

/-- The ends of the edges lie in the vertex set. -/
def WF (Vs : Finset α) (Es : Finset β) (ends : β → Sym2 α) : Prop := ∀ e ∈ Es, ∀ x ∈ ends e, x ∈ Vs

/-! ### Loops -/

lemma adj_insert_loop {ends : β → Sym2 α} {S : Finset β} {e : β} {w : α} (he : ends e = s(w, w)) :
    ∀ x y, Relation.ReflTransGen (Adj ends (insert e S)) x y ↔ Relation.ReflTransGen (Adj ends S) x y := by
  intro x y
  constructor
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hab ih =>
      obtain ⟨f, hf, hfe⟩ := hab
      rcases Finset.mem_insert.1 hf with rfl | hf
      · rw [he, Sym2.eq_iff] at hfe
        rcases hfe with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ih
      · exact ih.tail ⟨f, hf, hfe⟩
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hab ih =>
      obtain ⟨f, hf, hfe⟩ := hab
      exact ih.tail ⟨f, Finset.mem_insert_of_mem hf, hfe⟩

/-- A loop makes `ρ` vanish: `S` and `S ∪ {e}` cancel. -/
lemma rho_loop {Vs : Finset α} {Es : Finset β} {ends : β → Sym2 α} {e : β} (heE : e ∈ Es) {w : α}
    (he : ends e = s(w, w)) : rho Vs Es ends = 0 := by
  unfold rho
  rw [Finset.sum_filter, ← Finset.insert_erase heE, Finset.sum_powerset_insert (Finset.notMem_erase e Es)]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun S hS => ?_
  have heS : e ∉ S := fun h => Finset.notMem_erase e Es (Finset.mem_powerset.1 hS h)
  have hconn : Conn Vs ends (insert e S) ↔ Conn Vs ends S := by
    unfold Conn
    simp only [adj_insert_loop he]
  rw [Finset.card_insert_of_notMem heS]
  by_cases hc : Conn Vs ends S
  · rw [if_pos hc, if_pos (hconn.2 hc), pow_succ]; ring
  · rw [if_neg hc, if_neg (fun h => hc (hconn.1 h)), add_zero]

/-! ### Contraction -/

/-- The contraction of `v` to `u`. -/
def phi (u v : α) (x : α) : α := if x = v then u else x

lemma phi_eq_phi {u v w w' : α} (h : phi u v w = phi u v w') (hne : w ≠ w') : s(w, w') = s(u, v) := by
  unfold phi at h
  split_ifs at h with h1 h2 h2
  · exact absurd (h1.trans h2.symm) hne
  · subst h1; subst h; exact Sym2.eq_swap
  · subst h2; subst h; rfl
  · exact absurd h hne

lemma image_phi {Vs : Finset α} {u v : α} (hu : u ∈ Vs) (huv : u ≠ v) : Vs.image (phi u v) = Vs.erase v := by
  ext x
  simp only [Finset.mem_image, Finset.mem_erase]
  constructor
  · rintro ⟨y, hy, rfl⟩
    unfold phi
    split_ifs with h
    · exact ⟨huv, hu⟩
    · exact ⟨h, hy⟩
  · rintro ⟨hx, hxV⟩
    exact ⟨x, hxV, by simp [phi, hx]⟩

/-- **Connectivity passes through the contraction**: for `e = {u, v}` not in `S`,
`(V, S ∪ {e})` is connected iff `(V/e, S)` is. -/
lemma conn_insert_iff {Vs : Finset α} {ends : β → Sym2 α} {S : Finset β} {e : β} {u v : α}
    (he : ends e = s(u, v)) (heS : e ∉ S) :
    Conn Vs ends (insert e S) ↔ Conn (Vs.image (phi u v)) (fun f => Sym2.map (phi u v) (ends f)) S := by
  constructor
  · intro h x' hx' y' hy'
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hx'
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hy'
    have hxy := h x hx y hy
    clear hy hy'
    induction hxy with
    | refl => exact Relation.ReflTransGen.refl
    | @tail a b _ hab ih =>
      obtain ⟨f, hf, hfe⟩ := hab
      rcases Finset.mem_insert.1 hf with rfl | hf
      · rw [he, Sym2.eq_iff] at hfe
        have : phi u v a = phi u v b := by
          rcases hfe with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [phi]
        rw [← this]; exact ih
      · exact ih.tail ⟨f, hf, by simp only; rw [hfe, Sym2.map_mk]⟩
  · intro h x hx y hy
    -- every preimage of a point reachable from `φ x` is reachable from `x`
    have key : ∀ w', Relation.ReflTransGen (Adj (fun f => Sym2.map (phi u v) (ends f)) S) (phi u v x) w' →
        ∀ w, phi u v w = w' → Relation.ReflTransGen (Adj ends (insert e S)) x w := by
      have hbridge : ∀ w w', phi u v w = phi u v w' →
          Relation.ReflTransGen (Adj ends (insert e S)) w w' := by
        intro w w' hww
        by_cases hne : w = w'
        · rw [hne]
        · exact Relation.ReflTransGen.single ⟨e, Finset.mem_insert_self e S, by rw [he, phi_eq_phi hww hne]⟩
      intro w' hw'
      induction hw' with
      | refl => intro w hw; exact hbridge x w hw.symm
      | @tail a' b' _ hab ih =>
        obtain ⟨f, hf, hfe⟩ := hab
        simp only at hfe
        intro w hw
        -- the ends of `f` are preimages of `a'` and `b'`
        obtain ⟨a, b, hab'⟩ : ∃ a b, ends f = s(a, b) := by
          induction (ends f) using Sym2.ind with
          | h a b => exact ⟨a, b, rfl⟩
        have hfS : f ∈ insert e S := Finset.mem_insert_of_mem hf
        rw [hab', Sym2.map_mk, Sym2.eq_iff] at hfe
        rcases hfe with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · have hxa := ih a h1
          have hab : Relation.ReflTransGen (Adj ends (insert e S)) a b := Relation.ReflTransGen.single ⟨f, hfS, hab'⟩
          exact (hxa.trans hab).trans (hbridge b w (h2.trans hw.symm))
        · have hxb := ih b h2
          have hba : Relation.ReflTransGen (Adj ends (insert e S)) b a :=
            Relation.ReflTransGen.single ⟨f, hfS, by rw [hab', Sym2.eq_swap]⟩
          exact (hxb.trans hba).trans (hbridge a w (h1.trans hw.symm))
    exact key _ (h _ (Finset.mem_image_of_mem _ hx) _ (Finset.mem_image_of_mem _ hy)) y rfl

/-! ### Deletion and contraction -/

lemma card_image_phi {Vs : Finset α} {u v : α} (hu : u ∈ Vs) (hv : v ∈ Vs) (huv : u ≠ v) :
    (Vs.image (phi u v)).card + 1 = Vs.card := by
  rw [image_phi hu huv, Finset.card_erase_of_mem hv]
  have : 0 < Vs.card := Finset.card_pos.2 ⟨u, hu⟩
  omega

/-- `ρ(G) = ρ(G - e) - ρ(G/e)`. -/
lemma rho_dc {Vs : Finset α} {Es : Finset β} {ends : β → Sym2 α} {e : β} (heE : e ∈ Es) {u v : α}
    (he : ends e = s(u, v)) :
    rho Vs Es ends = rho Vs (Es.erase e) ends -
      rho (Vs.image (phi u v)) (Es.erase e) (fun f => Sym2.map (phi u v) (ends f)) := by
  unfold rho
  conv_lhs => rw [Finset.sum_filter, ← Finset.insert_erase heE,
    Finset.sum_powerset_insert (Finset.notMem_erase e Es)]
  rw [Finset.sum_filter, Finset.sum_filter, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun S hS => ?_
  have heS : e ∉ S := fun h => Finset.notMem_erase e Es (Finset.mem_powerset.1 hS h)
  rw [Finset.card_insert_of_notMem heS]
  by_cases hc : Conn (Vs.image (phi u v)) (fun f => Sym2.map (phi u v) (ends f)) S
  · rw [if_pos ((conn_insert_iff he heS).2 hc), if_pos hc, pow_succ]; ring
  · rw [if_neg (fun h => hc ((conn_insert_iff he heS).1 h)), if_neg hc, neg_zero]

/-- `τ(G) = τ(G - e) + τ(G/e)` for an edge `e = {u, v}`, `u ≠ v`. -/
lemma tau_dc {Vs : Finset α} {Es : Finset β} {ends : β → Sym2 α} {e : β} (heE : e ∈ Es) {u v : α}
    (he : ends e = s(u, v)) (hu : u ∈ Vs) (hv : v ∈ Vs) (huv : u ≠ v) :
    tau Vs Es ends = tau Vs (Es.erase e) ends +
      tau (Vs.image (phi u v)) (Es.erase e) (fun f => Sym2.map (phi u v) (ends f)) := by
  have hcard := card_image_phi hu hv huv
  unfold tau
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter]
  conv_lhs => rw [← Finset.insert_erase heE, Finset.sum_powerset_insert (Finset.notMem_erase e Es)]
  congr 1
  refine Finset.sum_congr rfl fun S hS => ?_
  have heS : e ∉ S := fun h => Finset.notMem_erase e Es (Finset.mem_powerset.1 hS h)
  rw [Finset.card_insert_of_notMem heS]
  have hiff : (Conn Vs ends (insert e S) ∧ S.card + 1 + 1 = Vs.card) ↔
      (Conn (Vs.image (phi u v)) (fun f => Sym2.map (phi u v) (ends f)) S ∧
        S.card + 1 = (Vs.image (phi u v)).card) := by
    rw [conn_insert_iff he heS]
    constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by omega⟩
  by_cases hc : Conn (Vs.image (phi u v)) (fun f => Sym2.map (phi u v) (ends f)) S ∧
      S.card + 1 = (Vs.image (phi u v)).card
  · rw [if_pos (hiff.2 hc), if_pos hc]
  · rw [if_neg (fun h => hc (hiff.1 h)), if_neg hc]

/-! ### The tree-graph bound -/

lemma reflTransGen_empty {ends : β → Sym2 α} {x y : α} :
    Relation.ReflTransGen (Adj ends (∅ : Finset β)) x y ↔ x = y := by
  constructor
  · intro h
    induction h with
    | refl => rfl
    | tail _ hab _ => obtain ⟨f, hf, _⟩ := hab; exact absurd hf (Finset.notMem_empty f)
  · rintro rfl; exact Relation.ReflTransGen.refl

lemma conn_empty_iff {Vs : Finset α} {ends : β → Sym2 α} : Conn Vs ends ∅ ↔ Vs.card ≤ 1 := by
  rw [Finset.card_le_one]
  unfold Conn
  simp only [reflTransGen_empty]

/-- **The tree-graph bound and the sign**: for a nonempty vertex set, `|ρ(G)| ≤ τ(G)` and `(-1)^{#V-1}ρ(G) ≥ 0`. -/
theorem tree_graph : ∀ (k : ℕ) (Vs : Finset α) (Es : Finset β) (ends : β → Sym2 α), Es.card = k → Vs.Nonempty →
    WF Vs Es ends → |rho Vs Es ends| ≤ tau Vs Es ends ∧ 0 ≤ (-1) ^ (Vs.card - 1) * rho Vs Es ends := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro Vs Es ends hk hV hWF
  by_cases hloop : ∃ e ∈ Es, (ends e).IsDiag
  · obtain ⟨e, heE, hd⟩ := hloop
    obtain ⟨w, hw⟩ : ∃ w, ends e = s(w, w) := by
      induction hz : ends e using Sym2.ind with
      | h a b =>
        rw [hz, Sym2.mk_isDiag_iff] at hd
        exact ⟨a, by rw [hd]⟩
    rw [rho_loop heE hw]
    simp
  push_neg at hloop
  rcases Es.eq_empty_or_nonempty with hE | ⟨e, heE⟩
  · -- no edges
    subst hE
    have hr : rho Vs ∅ ends = if Vs.card ≤ 1 then 1 else 0 := by
      unfold rho
      simp only [Finset.powerset_empty, Finset.filter_singleton, conn_empty_iff]
      split_ifs <;> simp
    have ht : tau Vs ∅ ends = if Vs.card ≤ 1 ∧ 1 = Vs.card then 1 else 0 := by
      unfold tau
      simp only [Finset.powerset_empty, Finset.filter_singleton, conn_empty_iff, Finset.card_empty, zero_add]
      split_ifs <;> simp
    have hpos := Finset.card_pos.2 hV
    rw [hr, ht]
    by_cases h1 : Vs.card ≤ 1
    · have h1' : Vs.card = 1 := by omega
      simp [h1, h1']
    · simp [h1]
  · -- an edge which is not a loop
    obtain ⟨u, v, he⟩ : ∃ u v, ends e = s(u, v) := by
      induction (ends e) using Sym2.ind with
      | h a b => exact ⟨a, b, rfl⟩
    have huv : u ≠ v := by
      intro h; apply hloop e heE; rw [he, h]; exact Sym2.mk_isDiag_iff.2 rfl
    have hu : u ∈ Vs := hWF e heE u (by rw [he]; exact Sym2.mem_mk_left u v)
    have hv : v ∈ Vs := hWF e heE v (by rw [he]; exact Sym2.mem_mk_right u v)
    have hk' : (Es.erase e).card < k := by
      rw [Finset.card_erase_of_mem heE, ← hk]; have := Finset.card_pos.2 ⟨e, heE⟩; omega
    have hWF1 : WF Vs (Es.erase e) ends := fun f hf => hWF f (Finset.mem_of_mem_erase hf)
    have hWF2 : WF (Vs.image (phi u v)) (Es.erase e) (fun f => Sym2.map (phi u v) (ends f)) := by
      intro f hf x hx
      rw [Sym2.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact Finset.mem_image_of_mem _ (hWF f (Finset.mem_of_mem_erase hf) y hy)
    obtain ⟨b1, s1⟩ := ih _ hk' Vs (Es.erase e) ends rfl hV hWF1
    obtain ⟨b2, s2⟩ := ih _ hk' (Vs.image (phi u v)) (Es.erase e) _ rfl (hV.image _) hWF2
    have hcard := card_image_phi hu hv huv
    rw [rho_dc heE he, tau_dc heE he hu hv huv]
    constructor
    · push_cast
      exact (abs_sub _ _).trans (add_le_add b1 b2)
    · have hn : 2 ≤ Vs.card := by
        have : Vs.card ≠ 1 := by
          intro h1
          rw [Finset.card_eq_one] at h1
          obtain ⟨a, rfl⟩ := h1
          simp at hu hv; exact huv (hu.trans hv.symm)
        have := Finset.card_pos.2 hV; omega
      have e1 : Vs.card - 1 = ((Vs.image (phi u v)).card - 1) + 1 := by omega
      rw [e1, pow_succ] at s1 ⊢
      rw [mul_sub]
      nlinarith [s1, s2]

/-! ### The Ursell function of polymers -/

variable {P : Type*}

/-- The graphs on `{1, …, m}`: the off-diagonal pairs. -/
def offdiag (m : ℕ) : Finset (Sym2 (Fin m)) := Finset.univ.filter fun e => ¬e.IsDiag

/-- The graph of incompatibility of `Z_1, …, Z_m`: the pairs `{i, j}`, `i ≠ j`, with `Z_i ≁ Z_j`. -/
def incG (inc : P → P → Prop) {m : ℕ} (Z : Fin m → P) : Finset (Sym2 (Fin m)) :=
  (offdiag m).filter fun e => ∃ i j, e = s(i, j) ∧ inc (Z i) (Z j)

/-- **The Ursell function** `ρ^T(Z_1, …, Z_m) = Σ_gΠ_{{i,j} ∈ g}(ζ(Z_i, Z_j) - 1)` over the connected graphs `g` on
`{1, …, m}`, with `ζ - 1 = -1` on the incompatible pairs and `0` otherwise (`eq:ursell`). -/
def ursell (inc : P → P → Prop) {m : ℕ} (Z : Fin m → P) : ℤ :=
  ∑ g ∈ (offdiag m).powerset.filter (fun g => Conn Finset.univ id g),
    ∏ e ∈ g, (if e ∈ incG inc Z then (-1 : ℤ) else 0)

/-- The number `τ(Z_1, …, Z_m)` of the spanning trees of the graph of incompatibility. -/
def treeCount (inc : P → P → Prop) {m : ℕ} (Z : Fin m → P) : ℕ := tau Finset.univ (incG inc Z) id

lemma ursell_eq_rho (inc : P → P → Prop) {m : ℕ} (Z : Fin m → P) :
    ursell inc Z = rho Finset.univ (incG inc Z) id := by
  unfold ursell rho
  have hsub : (incG inc Z).powerset.filter (fun g => Conn Finset.univ id g) ⊆
      (offdiag m).powerset.filter (fun g => Conn Finset.univ id g) := by
    intro g hg
    simp only [Finset.mem_filter, Finset.mem_powerset] at hg ⊢
    exact ⟨hg.1.trans (Finset.filter_subset _ _), hg.2⟩
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun g hg => ?_
    have hgG : g ⊆ incG inc Z := Finset.mem_powerset.1 (Finset.mem_filter.1 hg).1
    rw [Finset.prod_congr rfl (fun e he => if_pos (hgG he)), Finset.prod_const]
  · intro g hg hng
    simp only [Finset.mem_filter, Finset.mem_powerset] at hg hng
    have : ¬g ⊆ incG inc Z := fun h => hng ⟨h, hg.2⟩
    obtain ⟨e, he, heG⟩ := Finset.not_subset.1 this
    exact Finset.prod_eq_zero he (if_neg heG)

/-- **The tree-graph bound** (`lem:cluster-bounds`): `|ρ^T(Z_1, …, Z_m)| ≤ τ(Z_1, …, Z_m)` for `m ≥ 1`, and
`(-1)^{m-1}ρ^T ≥ 0`. -/
theorem ursell_bound (inc : P → P → Prop) {m : ℕ} (hm : 1 ≤ m) (Z : Fin m → P) :
    |ursell inc Z| ≤ treeCount inc Z ∧ 0 ≤ (-1) ^ (m - 1) * ursell inc Z := by
  have hV : (Finset.univ : Finset (Fin m)).Nonempty := ⟨⟨0, hm⟩, Finset.mem_univ _⟩
  have hWF : WF Finset.univ (incG inc Z) id := fun _ _ _ _ => Finset.mem_univ _
  have h := tree_graph _ Finset.univ (incG inc Z) id rfl hV hWF
  rw [Finset.card_univ, Fintype.card_fin] at h
  rw [ursell_eq_rho]
  exact h

end TreeGraph
end CoreLean

end
