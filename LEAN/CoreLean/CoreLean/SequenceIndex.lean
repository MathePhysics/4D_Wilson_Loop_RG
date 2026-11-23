/-
The concrete layer, step C2 (`CONCRETE_LAYER.md`): the finite index sets of a sequence of domains of BALABAN_CORE.tex
(`615c66b253fe`, `def:sequence`, `def:operators`), for the sequences `SeqDom` of `SequencesTorus.lean`.

* `step S j μ`: the vector `a_je_μ` of the torus.
* `IsLayerBond S q`: `q = (j, y, μ)` is a positive bond `(y, y + a_je_μ)` of a layer `Γ_j`: `j ≤ k`, `y ∈ T^{(j)}`, an
  end in `Ω_j`, no end in `Ω_{j+1}` (the paragraph after `def:sequence`).
* `LBond S`: the positive bonds of the layers, a finite type (`layerBonds_finite`), with the scale `j(c)` and the
  spacing `a_c = a_{j(c)} > 0` (`LBond.ac`, `LBond.ac_pos`); the functions on the bonds of the layers are
  `LBond S → Mat`, with the pairing `(μ, ν)_w = Σ_c a_c⁴tr μ(c)ν(c)` of `CriticalConcrete.pairF`, symmetric and
  nondegenerate (`pairLB_nondegenerate`).
* `BPt S`: the points of the determining set `𝐁` with their scales, a finite type (`detSet_finite`), with the
  spacing `a_y = a_{j(y)}` and the pairing `Σ_y a_y⁴tr μ(y)μ'(y)` of `def:operators`(iii), nondegenerate.
-/
import CoreLean.SequencesTorus
import CoreLean.CriticalConcrete

open Set

noncomputable section

namespace CoreLean
namespace SequenceIndex

open Lattices

variable (S : SeqDom)

/-- The vector `a_je_μ`. -/
def step (j : ℕ) (μ : Fin 4) : Tor (ellT S.L S.mT) :=
  fun ν => if ν = μ then ((sp S.L S.k j : ℝ) : AddCircle (ellT S.L S.mT)) else 0

/-- `(j, y, μ)` is a positive bond `(y, y + a_je_μ)` of the layer `Γ_j`. -/
def IsLayerBond (q : ℕ × Tor (ellT S.L S.mT) × Fin 4) : Prop :=
  q.1 ≤ S.k ∧ q.2.1 ∈ S.TL q.1 ∧ (q.2.1 ∈ S.Ω q.1 ∨ q.2.1 + step S q.1 q.2.2 ∈ S.Ω q.1) ∧
    q.2.1 ∉ S.Ω (q.1 + 1) ∧ q.2.1 + step S q.1 q.2.2 ∉ S.Ω (q.1 + 1)

/-- The triples `(j, y, μ)` with `j ≤ k`, `y ∈ T^{(j)}` form a finite set. -/
lemma triples_finite : {q : ℕ × Tor (ellT S.L S.mT) × Fin 4 | q.1 ≤ S.k ∧ q.2.1 ∈ S.TL q.1}.Finite := by
  have h : {q : ℕ × Tor (ellT S.L S.mT) × Fin 4 | q.1 ≤ S.k ∧ q.2.1 ∈ S.TL q.1} ⊆
      ⋃ j ∈ Finset.range (S.k + 1), ({j} : Set ℕ) ×ˢ (S.TL j ×ˢ (univ : Set (Fin 4))) := by
    rintro ⟨j, y, μ⟩ ⟨hj, hy⟩
    simp only [mem_iUnion, Finset.mem_range, mem_prod, mem_singleton_iff, mem_univ, and_true]
    exact ⟨j, by omega, rfl, hy⟩
  refine Set.Finite.subset (Set.Finite.biUnion (Finset.finite_toSet _) fun j hj => ?_) h
  have hj' : j ≤ S.k := by simp only [Finset.coe_range, mem_Iio] at hj; omega
  exact (Set.finite_singleton j).prod ((S.finite_TL hj').prod Set.finite_univ)

lemma layerBonds_finite : {q | IsLayerBond S q}.Finite :=
  (triples_finite S).subset fun _ hq => ⟨hq.1, hq.2.1⟩

/-- The positive bonds of the layers. -/
def LBond : Type _ := {q // IsLayerBond S q}

noncomputable instance : Fintype (LBond S) := (layerBonds_finite S).fintype

/-- The scale `j(c)` of a bond of the layers. -/
def LBond.scale {S : SeqDom} (c : LBond S) : ℕ := c.1.1

/-- The spacing `a_c = a_{j(c)}`. -/
def LBond.ac {S : SeqDom} (c : LBond S) : ℝ := sp S.L S.k c.1.1

lemma LBond.ac_pos {S : SeqDom} (c : LBond S) : 0 < c.ac := sp_pos S.Lpos _

/-- The pairing `(μ, ν)_w = Σ_c a_c⁴tr μ(c)ν(c)` of the functions on the bonds of the layers. -/
abbrev pairLB (N : ℕ) : LinearMap.BilinForm ℂ (LBond S → Matrix (Fin N) (Fin N) ℂ) :=
  CriticalConcrete.pairF (fun c : LBond S => c.ac)

theorem pairLB_nondegenerate (N : ℕ) : (pairLB S N).Nondegenerate :=
  ConcretePairing.wpair_nondegenerate _ fun c => by have := LBond.ac_pos c; positivity

theorem pairLB_symm (N : ℕ) (f g : LBond S → Matrix (Fin N) (Fin N) ℂ) : pairLB S N f g = pairLB S N g f :=
  ConcretePairing.wpair_symm _ f g

/-! ### The determining set -/

lemma detSet_finite : S.detSet.Finite := by
  have := triples_finite S
  refine (this.image fun q => (q.1, q.2.1)).subset ?_
  rintro ⟨j, y⟩ ⟨hj, hy⟩
  exact ⟨(j, y, 0), ⟨hj, hy.1.2⟩, rfl⟩

/-- The points of `𝐁`, with their scales. -/
def BPt : Type _ := S.detSet

noncomputable instance : Fintype (BPt S) := (detSet_finite S).fintype

/-- The spacing `a_y = a_{j(y)}` at a point of `𝐁`. -/
def BPt.ay {S : SeqDom} (y : BPt S) : ℝ := sp S.L S.k y.1.1

lemma BPt.ay_pos {S : SeqDom} (y : BPt S) : 0 < y.ay := sp_pos S.Lpos _

/-- The pairing `Σ_{y ∈ 𝐁}a_{j(y)}⁴tr μ(y)μ'(y)` of `def:operators`(iii). -/
abbrev pairB (N : ℕ) : LinearMap.BilinForm ℂ (BPt S → Matrix (Fin N) (Fin N) ℂ) :=
  CriticalConcrete.pairF (fun y : BPt S => y.ay)

theorem pairB_nondegenerate (N : ℕ) : (pairB S N).Nondegenerate :=
  ConcretePairing.wpair_nondegenerate _ fun y => by have := BPt.ay_pos y; positivity

end SequenceIndex
end CoreLean

end
