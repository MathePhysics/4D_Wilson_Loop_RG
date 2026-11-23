/-
Shortest paths on the fine lattice, used by the Hölder norms of `def:norms`(ii).

A shortest path from `x` to `x'` is a path (`Transports.IsPath`) ending at `x'` (`pend`) with as many bonds
as `|x - x'|₁`. Each of its points `p` lies between `x` and `x'`: `|x - p|₁ + |p - x'|₁ = |x - x'|₁`, and
in each coordinate. Consequently a shortest path between two points of a cube `|z - y|_∞ ≤ r` runs in
the cube (the core: "it runs in the cube"), if the torus is large enough.
-/
import CoreLean.Transports

open Finset

noncomputable section

namespace CoreLean

namespace Transports

variable {n : ℕ} [NeZero n]

/-- The end of a path from `s`. -/
def pend : Site n → List (Bond n) → Site n
  | s, [] => s
  | _, b :: γ => pend b.plus γ

/-- A shortest path from `x` to `x'`. -/
def IsShortest (x x' : Site n) (γ : List (Bond n)) : Prop :=
  IsPath x γ ∧ pend x γ = x' ∧ γ.length = Blocks.d1 x x'

lemma isPath_append {s : Site n} {l₁ l₂ : List (Bond n)} :
    IsPath s (l₁ ++ l₂) ↔ IsPath s l₁ ∧ IsPath (pend s l₁) l₂ := by
  induction l₁ generalizing s with
  | nil => simp [IsPath, pend]
  | cons b l ih =>
    simp only [List.cons_append, IsPath, pend]
    rw [ih]; tauto

lemma pend_append (s : Site n) (l₁ l₂ : List (Bond n)) :
    pend s (l₁ ++ l₂) = pend (pend s l₁) l₂ := by
  induction l₁ generalizing s with
  | nil => rfl
  | cons b l ih => exact ih b.plus

/-- The end of a path lies within its length of its beginning. -/
lemma d1_pend_le {s : Site n} {γ : List (Bond n)} (hγ : IsPath s γ) :
    Blocks.d1 s (pend s γ) ≤ γ.length := by
  induction γ generalizing s with
  | nil => simp [pend, d1_self]
  | cons b γ ih =>
    obtain ⟨hb, hγ'⟩ := hγ
    subst hb
    have := ih hγ'
    have h1 := d1_plus b
    have t := d1_triangle b.site b.plus (pend b.plus γ)
    simp only [pend, List.length_cons]
    omega

lemma d1_comm (x y : Site n) : Blocks.d1 x y = Blocks.d1 y x := by
  unfold Blocks.d1; congr 1; funext κ; exact Blocks.cd_sub_comm _ _

/-- The points of a shortest path lie between its ends. -/
lemma between_of_shortest {x x' : Site n} {γ : List (Bond n)} (hγ : IsShortest x x' γ) :
    ∀ b ∈ γ, (Blocks.d1 x b.site + Blocks.d1 b.site x' = Blocks.d1 x x') ∧
      (Blocks.d1 x b.plus + Blocks.d1 b.plus x' = Blocks.d1 x x') := by
  obtain ⟨hp, hend, hlen⟩ := hγ
  intro b hb
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem hb
  rw [isPath_append] at hp
  obtain ⟨hpre, hpost⟩ := hp
  obtain ⟨hbs, hpost'⟩ := hpost
  have e1 := d1_pend_le hpre
  have e2 := d1_pend_le hpost'
  rw [pend_append] at hend
  simp only [pend] at hend
  rw [hend] at e2
  rw [← hbs] at e1
  simp only [List.length_append, List.length_cons] at hlen
  have hpl := d1_plus b
  constructor
  · have t := d1_triangle x b.site x'
    have t2 := d1_triangle b.site b.plus x'
    omega
  · have t := d1_triangle x b.plus x'
    have t2 := d1_triangle x b.site b.plus
    omega

/-- Between in the `ℓ¹` distance means between in each coordinate. -/
lemma coord_between {x p x' : Site n}
    (h : Blocks.d1 x p + Blocks.d1 p x' = Blocks.d1 x x') (κ : Fin 4) :
    Blocks.cd (x κ - p κ) + Blocks.cd (p κ - x' κ) = Blocks.cd (x κ - x' κ) := by
  unfold Blocks.d1 at h
  rw [← Finset.sum_add_distrib] at h
  have hle : ∀ ι ∈ (univ : Finset (Fin 4)),
      Blocks.cd (x ι - x' ι) ≤ Blocks.cd (x ι - p ι) + Blocks.cd (p ι - x' ι) :=
    fun ι _ => Blocks.cd_sub_le _ _ _
  have := (Finset.sum_eq_sum_iff_of_le hle).mp h.symm κ (mem_univ κ)
  omega

/-- A point between two points of the cube `|z - y|_∞ ≤ r` lies in the cube, if `2(2r + a) < n`, where
`a` bounds the distance of the two points. -/
lemma cd_le_of_between {x p x' y : ZMod n} {r a : ℕ} (hx : Blocks.cd (x - y) ≤ r)
    (hx' : Blocks.cd (x' - y) ≤ r) (hxx' : Blocks.cd (x - x') ≤ a)
    (hb : Blocks.cd (x - p) + Blocks.cd (p - x') = Blocks.cd (x - x')) (hn : 2 * (2 * r + a) < n) :
    Blocks.cd (p - y) ≤ r := by
  -- integer representatives relative to `y`
  set X := (x - y).valMinAbs
  set X' := (x' - y).valMinAbs
  set δ := (p - x).valMinAbs
  have hX : X.natAbs ≤ r := hx
  have hX' : X'.natAbs ≤ r := hx'
  have hδ : δ.natAbs ≤ a := by
    have : δ.natAbs = Blocks.cd (x - p) := by rw [Blocks.cd_sub_comm]; rfl
    have h1 : Blocks.cd (x - p) ≤ Blocks.cd (x - x') := by omega
    omega
  have ex : x - y = (X : ZMod n) := (ZMod.coe_valMinAbs _).symm
  have ex' : x' - y = (X' : ZMod n) := (ZMod.coe_valMinAbs _).symm
  have ep : p - x = (δ : ZMod n) := (ZMod.coe_valMinAbs _).symm
  -- the three distances as absolute values of integers
  have hd1 : Blocks.cd (x - p) = δ.natAbs := by
    rw [← Blocks.cd_neg, neg_sub, ep]
    exact Blocks.cd_intCast_eq (by omega)
  have hd2 : Blocks.cd (p - x') = (X + δ - X').natAbs := by
    have : p - x' = ((X + δ - X' : ℤ) : ZMod n) := by
      have : p - x' = (p - x) + (x - y) - (x' - y) := by ring
      rw [this, ep, ex, ex']; push_cast; ring
    rw [this]
    exact Blocks.cd_intCast_eq (by omega)
  have hd3 : Blocks.cd (x - x') = (X - X').natAbs := by
    have : x - x' = ((X - X' : ℤ) : ZMod n) := by
      have : x - x' = (x - y) - (x' - y) := by ring
      rw [this, ex, ex']; push_cast; ring
    rw [this]
    exact Blocks.cd_intCast_eq (by omega)
  rw [hd1, hd2, hd3] at hb
  -- `X + δ` lies between `X` and `X'`
  have hP : (X + δ).natAbs ≤ r := by omega
  have : p - y = ((X + δ : ℤ) : ZMod n) := by
    have : p - y = (p - x) + (x - y) := by ring
    rw [this, ep, ex]; push_cast; ring
  rw [this]
  exact (Blocks.cd_intCast_le _).trans hP

/-- A shortest path between two points of the cube `|z - y|_∞ ≤ r` runs in the cube, if
`2(2r + |x - x'|₁) < n`. -/
theorem shortest_in_cube {x x' y : Site n} {γ : List (Bond n)} (hγ : IsShortest x x' γ) {r : ℕ}
    (hx : Blocks.dinf x y ≤ r) (hx' : Blocks.dinf x' y ≤ r)
    (hn : 2 * (2 * r + Blocks.d1 x x') < n) :
    ∀ b ∈ γ, Blocks.dinf b.site y ≤ r ∧ Blocks.dinf b.plus y ≤ r := by
  intro b hb
  obtain ⟨h1, h2⟩ := between_of_shortest hγ b hb
  have key : ∀ p, Blocks.d1 x p + Blocks.d1 p x' = Blocks.d1 x x' → Blocks.dinf p y ≤ r := by
    intro p hp
    refine Finset.sup_le fun κ _ => ?_
    exact cd_le_of_between ((Blocks.cd_le_dinf x y κ).trans hx) ((Blocks.cd_le_dinf x' y κ).trans hx')
      (Blocks.cd_le_d1 x x' κ) (coord_between hp κ)
      (lt_of_le_of_lt (by have := Blocks.cd_le_d1 x x' κ; omega) hn)
  exact ⟨key _ h1, key _ h2⟩

end Transports

end CoreLean
