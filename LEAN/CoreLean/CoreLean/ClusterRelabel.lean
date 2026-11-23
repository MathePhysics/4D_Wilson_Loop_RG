/-
Relabelling for the exponential formula of `thm:polymer-logarithm` of BALABAN_CORE.tex (`5bbe1bc62521`): the sums over the
connected graphs and over all graphs on the image `B` of an embedding `φ : ι' ↪ ι` are those on `ι'` with the weights
transported by `Sym2.map φ`.
-/
import CoreLean.ClusterComponents

open Finset

noncomputable section

namespace CoreLean
namespace TreeGraph

open Classical

variable {ι ι' : Type*} [Fintype ι] [Fintype ι'] [DecidableEq ι] [DecidableEq ι']

lemma map_offdiag {φ : ι' ↪ ι} {e : Sym2 ι'} (he : ¬e.IsDiag) : ¬(Sym2.map φ e).IsDiag := by
  induction e using Sym2.ind with
  | h a b =>
    rw [Sym2.map_mk, Sym2.mk_isDiag_iff]
    rw [Sym2.mk_isDiag_iff] at he
    exact fun h => he (φ.injective h)

lemma map_mem_pairsIn {φ : ι' ↪ ι} {e : Sym2 ι'} (he : e ∈ pairsIn (Finset.univ : Finset ι')) :
    Sym2.map φ e ∈ pairsIn ((Finset.univ : Finset ι').map φ) := by
  simp only [pairsIn, Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
  refine ⟨map_offdiag he.1, fun x hx => ?_⟩
  rw [Sym2.mem_map] at hx
  obtain ⟨y, -, rfl⟩ := hx
  exact Finset.mem_map_of_mem φ (Finset.mem_univ y)

/-- The embedding of the pairs. -/
def symEmb (φ : ι' ↪ ι) : Sym2 ι' ↪ Sym2 ι := ⟨Sym2.map φ, Sym2.map.injective φ.injective⟩

/-- Every pair inside the image is the image of a pair. -/
lemma pairsIn_image {φ : ι' ↪ ι} {e : Sym2 ι} (he : e ∈ pairsIn ((Finset.univ : Finset ι').map φ)) :
    ∃ e' ∈ pairsIn (Finset.univ : Finset ι'), Sym2.map φ e' = e := by
  simp only [pairsIn, Finset.mem_filter, Finset.mem_univ, true_and] at he
  obtain ⟨hd, hB⟩ := he
  induction e using Sym2.ind with
  | h a b =>
    obtain ⟨a', -, rfl⟩ := Finset.mem_map.1 (hB a (Sym2.mem_mk_left a b))
    obtain ⟨b', -, rfl⟩ := Finset.mem_map.1 (hB b (Sym2.mem_mk_right _ b))
    refine ⟨s(a', b'), ?_, rfl⟩
    simp only [pairsIn, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨fun h => hd ?_, fun _ _ => trivial⟩
    rw [Sym2.mk_isDiag_iff] at h ⊢
    rw [h]

lemma adj_map {φ : ι' ↪ ι} {g' : Finset (Sym2 ι')} {a b : ι'} :
    Adj id (g'.map (symEmb φ)) (φ a) (φ b) ↔ Adj id g' a b := by
  rw [adj_id, adj_id, Finset.mem_map]
  constructor
  · rintro ⟨e, he, hee⟩
    have : e = s(a, b) := (symEmb φ).injective (by rw [hee]; rfl)
    rw [← this]; exact he
  · intro h; exact ⟨_, h, rfl⟩

/-- Connectivity passes through the embedding. -/
lemma conn_map {φ : ι' ↪ ι} {g' : Finset (Sym2 ι')} (hg' : g' ⊆ pairsIn (Finset.univ : Finset ι')) :
    Conn ((Finset.univ : Finset ι').map φ) id (g'.map (symEmb φ)) ↔ Conn (Finset.univ : Finset ι') id g' := by
  constructor
  · intro h x _ y _
    have hxy := h (φ x) (Finset.mem_map_of_mem φ (Finset.mem_univ x)) (φ y)
      (Finset.mem_map_of_mem φ (Finset.mem_univ y))
    -- every vertex reached from `φ x` is in the image, and the steps lift
    have key : ∀ w, Relation.ReflTransGen (Adj id (g'.map (symEmb φ))) (φ x) w →
        ∀ w', φ w' = w → Relation.ReflTransGen (Adj id g') x w' := by
      intro w hw
      induction hw with
      | refl => intro w' hw'; rw [φ.injective hw']
      | @tail a b _ hab ih =>
        intro w' hw'
        obtain ⟨e, he, hee⟩ := Finset.mem_map.1 (adj_id.1 hab)
        induction e using Sym2.ind with
        | h c d =>
          have h2 : s(φ c, φ d) = s(a, b) := hee
          rw [Sym2.eq_iff] at h2
          rcases h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · rw [φ.injective hw']; exact (ih c rfl).tail (adj_id.2 he)
          · rw [φ.injective hw']; exact (ih d rfl).tail (adj_id.2 (by rw [Sym2.eq_swap]; exact he))
    exact key _ hxy y rfl
  · intro h x hx y hy
    obtain ⟨x', -, rfl⟩ := Finset.mem_map.1 hx
    obtain ⟨y', -, rfl⟩ := Finset.mem_map.1 hy
    have hxy := h x' (Finset.mem_univ _) y' (Finset.mem_univ _)
    clear hy
    induction hxy with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hab ih => exact ih.tail (adj_map.2 hab)

/-- **Relabelling of the connected graphs.** -/
lemma sum_conn_map {R : Type*} [CommRing R] (φ : ι' ↪ ι) (F : Sym2 ι → R) :
    ∑ g' ∈ (pairsIn (Finset.univ : Finset ι')).powerset.filter (fun g => Conn Finset.univ id g),
        ∏ e ∈ g', F (Sym2.map φ e) =
      ∑ g ∈ (pairsIn ((Finset.univ : Finset ι').map φ)).powerset.filter
        (fun g => Conn ((Finset.univ : Finset ι').map φ) id g), ∏ e ∈ g, F e := by
  refine Finset.sum_bij (fun g' _ => g'.map (symEmb φ)) ?_ ?_ ?_ ?_
  · intro g' hg'
    simp only [Finset.mem_filter, Finset.mem_powerset] at hg' ⊢
    refine ⟨fun e he => ?_, (conn_map (φ := φ) hg'.1).2 hg'.2⟩
    obtain ⟨e', he', rfl⟩ := Finset.mem_map.1 he
    exact map_mem_pairsIn (hg'.1 he')
  · intro a _ b _ h; exact Finset.map_injective _ h
  · intro g hg
    simp only [Finset.mem_filter, Finset.mem_powerset] at hg
    refine ⟨(pairsIn (Finset.univ : Finset ι')).filter (fun e' => Sym2.map φ e' ∈ g), ?_, ?_⟩
    · have hsub : (pairsIn (Finset.univ : Finset ι')).filter (fun e' => Sym2.map φ e' ∈ g) ⊆
          pairsIn (Finset.univ : Finset ι') := Finset.filter_subset _ _
      have hmap : ((pairsIn (Finset.univ : Finset ι')).filter (fun e' => Sym2.map φ e' ∈ g)).map (symEmb φ) = g := by
        ext e
        simp only [Finset.mem_map, Finset.mem_filter]
        constructor
        · rintro ⟨e', ⟨_, he'⟩, rfl⟩; exact he'
        · intro he
          obtain ⟨e', he', rfl⟩ := pairsIn_image (hg.1 he)
          exact ⟨e', ⟨he', he⟩, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_powerset]
      refine ⟨hsub, (conn_map (φ := φ) hsub).1 ?_⟩
      rw [hmap]; exact hg.2
    · ext e
      simp only [Finset.mem_map, Finset.mem_filter]
      constructor
      · rintro ⟨e', ⟨_, he'⟩, rfl⟩; exact he'
      · intro he
        obtain ⟨e', he', rfl⟩ := pairsIn_image (hg.1 he)
        exact ⟨e', ⟨he', he⟩, rfl⟩
  · intro g' _
    rw [Finset.prod_map]
    rfl

/-- **Relabelling of all graphs.** -/
lemma sum_all_map {R : Type*} [CommRing R] (φ : ι' ↪ ι) (F : Sym2 ι → R) :
    ∑ g' ∈ (pairsIn (Finset.univ : Finset ι')).powerset, ∏ e ∈ g', F (Sym2.map φ e) =
      ∑ g ∈ (pairsIn ((Finset.univ : Finset ι').map φ)).powerset, ∏ e ∈ g, F e := by
  refine Finset.sum_bij (fun g' _ => g'.map (symEmb φ)) ?_ ?_ ?_ ?_
  · intro g' hg'
    rw [Finset.mem_powerset] at hg' ⊢
    intro e he
    obtain ⟨e', he', rfl⟩ := Finset.mem_map.1 he
    exact map_mem_pairsIn (hg' he')
  · intro a _ b _ h; exact Finset.map_injective _ h
  · intro g hg
    rw [Finset.mem_powerset] at hg
    refine ⟨(pairsIn (Finset.univ : Finset ι')).filter (fun e' => Sym2.map φ e' ∈ g),
      Finset.mem_powerset.2 (Finset.filter_subset _ _), ?_⟩
    ext e
    simp only [Finset.mem_map, Finset.mem_filter]
    constructor
    · rintro ⟨e', ⟨_, he'⟩, rfl⟩; exact he'
    · intro he
      obtain ⟨e', he', rfl⟩ := pairsIn_image (hg he)
      exact ⟨e', ⟨he', he⟩, rfl⟩
  · intro g' _
    rw [Finset.prod_map]
    rfl

end TreeGraph
end CoreLean

end
