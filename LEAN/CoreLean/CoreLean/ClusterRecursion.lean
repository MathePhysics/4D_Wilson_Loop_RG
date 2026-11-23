/-
The recursion behind the exponential formula of `thm:polymer-logarithm` of BALABAN_CORE.tex (`5bbe1bc62521`). For a finite
type `Q` of polymers with a symmetric incompatibility, weights `w : Q → R`, and
`E_n = Σ_{Z ∈ Q^n}Π_{i<j}ζ(Z_i, Z_j)Π_iw(Z_i)`, `C_k = Σ_{Z ∈ Q^k}ρ^T(Z)Π_iw(Z_i)`:
`E_n = Σ_{k=1}^n C(n-1, k-1)C_kE_{n-k}` for `n ≥ 1`, by the decomposition of the graph `Π_{i<j}(1 + f_{ij})` by the
component of the first index.
-/
import CoreLean.ClusterRelabel

open Finset

noncomputable section

namespace CoreLean
namespace TreeGraph

open Classical

variable {Q : Type*} [Fintype Q] (inc : Q → Q → Prop)

/-- `f_{ij} = ζ(Z_i, Z_j) - 1`, on the pairs `{i, j}`. -/
def fp {ι : Type*} (Z : ι → Q) (e : Sym2 ι) : ℤ := if ∃ i j, e = s(i, j) ∧ inc (Z i) (Z j) then -1 else 0

/-- `Π_{i<j}ζ(Z_i, Z_j) = Σ_gΠ_{e ∈ g}f_e`. -/
def zetaS {ι : Type*} [Fintype ι] [DecidableEq ι] (Z : ι → Q) : ℤ := ∑ g ∈ (pairsIn (Finset.univ : Finset ι)).powerset, ∏ e ∈ g, fp inc Z e

/-- `ρ^T(Z) = Σ_{g connected}Π_{e ∈ g}f_e`. -/
def ursS {ι : Type*} [Fintype ι] [DecidableEq ι] (Z : ι → Q) : ℤ :=
  ∑ g ∈ (pairsIn (Finset.univ : Finset ι)).powerset.filter (fun g => Conn Finset.univ id g), ∏ e ∈ g, fp inc Z e

variable {inc}

lemma fp_map (hsymm : ∀ a b, inc a b → inc b a) {ι ι' : Type*} (φ : ι' ↪ ι) (Z : ι → Q) (e : Sym2 ι') :
    fp inc (Z ∘ φ) e = fp inc Z (Sym2.map φ e) := by
  unfold fp
  congr 1
  apply propext
  induction e using Sym2.ind with
  | h a b =>
    constructor
    · rintro ⟨i, j, hij, h⟩
      rw [Sym2.eq_iff] at hij
      refine ⟨φ i, φ j, ?_, h⟩
      rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · rw [Sym2.map_mk, Sym2.eq_swap]
    · rintro ⟨i, j, hij, h⟩
      rw [Sym2.map_mk, Sym2.eq_iff] at hij
      rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨a, b, rfl, h⟩
      · exact ⟨a, b, rfl, hsymm _ _ h⟩

/-- `ρ^T` is invariant under relabelling. -/
lemma ursS_equiv (hsymm : ∀ a b, inc a b → inc b a) {ι ι' : Type*} [Fintype ι] [Fintype ι'] [DecidableEq ι] [DecidableEq ι'] (σ : ι' ≃ ι)
    (Z : ι → Q) : ursS inc (Z ∘ σ) = ursS inc Z := by
  unfold ursS
  have h := sum_conn_map (R := ℤ) σ.toEmbedding (fp inc Z)
  have hu : (Finset.univ : Finset ι').map σ.toEmbedding = Finset.univ := by
    ext x; simp only [Finset.mem_map, Finset.mem_univ, true_and, iff_true]
    exact ⟨σ.symm x, by simp⟩
  rw [hu] at h
  rw [← h]
  refine Finset.sum_congr rfl fun g _ => Finset.prod_congr rfl fun e _ => ?_
  exact fp_map hsymm σ.toEmbedding Z e

lemma zetaS_equiv (hsymm : ∀ a b, inc a b → inc b a) {ι ι' : Type*} [Fintype ι] [Fintype ι'] [DecidableEq ι] [DecidableEq ι'] (σ : ι' ≃ ι)
    (Z : ι → Q) : zetaS inc (Z ∘ σ) = zetaS inc Z := by
  unfold zetaS
  have h := sum_all_map (R := ℤ) σ.toEmbedding (fp inc Z)
  have hu : (Finset.univ : Finset ι').map σ.toEmbedding = Finset.univ := by
    ext x; simp only [Finset.mem_map, Finset.mem_univ, true_and, iff_true]
    exact ⟨σ.symm x, by simp⟩
  rw [hu] at h
  rw [← h]
  refine Finset.sum_congr rfl fun g _ => Finset.prod_congr rfl fun e _ => ?_
  exact fp_map hsymm σ.toEmbedding Z e

/-- The sums on a subset `B` are those of the restriction. -/
lemma urs_restrict (hsymm : ∀ a b, inc a b → inc b a) {ι : Type*} [Fintype ι] [DecidableEq ι] (B : Finset ι) (Z : ι → Q) :
    ∑ g ∈ (pairsIn B).powerset.filter (fun g => Conn B id g), ∏ e ∈ g, fp inc Z e =
      ursS inc (fun x : B => Z x) := by
  unfold ursS
  have h := sum_conn_map (R := ℤ) (Function.Embedding.subtype (· ∈ B)) (fp inc Z)
  have hu : (Finset.univ : Finset B).map (Function.Embedding.subtype (· ∈ B)) = B := by
    ext x; simp
  rw [hu] at h
  rw [← h]
  refine Finset.sum_congr rfl fun g _ => Finset.prod_congr rfl fun e _ => ?_
  exact (fp_map hsymm (Function.Embedding.subtype (· ∈ B)) Z e).symm

lemma zeta_restrict (hsymm : ∀ a b, inc a b → inc b a) {ι : Type*} [Fintype ι] [DecidableEq ι] (B : Finset ι) (Z : ι → Q) :
    ∑ g ∈ (pairsIn B).powerset, ∏ e ∈ g, fp inc Z e = zetaS inc (fun x : B => Z x) := by
  unfold zetaS
  have h := sum_all_map (R := ℤ) (Function.Embedding.subtype (· ∈ B)) (fp inc Z)
  have hu : (Finset.univ : Finset B).map (Function.Embedding.subtype (· ∈ B)) = B := by
    ext x; simp
  rw [hu] at h
  rw [← h]
  refine Finset.sum_congr rfl fun g _ => Finset.prod_congr rfl fun e _ => ?_
  exact (fp_map hsymm (Function.Embedding.subtype (· ∈ B)) Z e).symm

variable {R : Type*} [CommRing R]

/-- `Σ_{Z ∈ Q^ι}Π_{i<j}ζΠw`. -/
def Ei (ι : Type*) [Fintype ι] [DecidableEq ι] (w : Q → R) : R := ∑ Z : ι → Q, (zetaS inc Z : R) * ∏ i, w (Z i)

/-- `Σ_{Z ∈ Q^ι}ρ^TΠw`. -/
def Ci (ι : Type*) [Fintype ι] [DecidableEq ι] (w : Q → R) : R := ∑ Z : ι → Q, (ursS inc Z : R) * ∏ i, w (Z i)

lemma Ei_equiv (hsymm : ∀ a b, inc a b → inc b a) {ι ι' : Type*} [Fintype ι] [Fintype ι'] [DecidableEq ι] [DecidableEq ι'] (σ : ι' ≃ ι)
    (w : Q → R) : Ei (inc := inc) ι w = Ei (inc := inc) ι' w := by
  unfold Ei
  refine Fintype.sum_equiv (σ.arrowCongr (Equiv.refl Q)).symm _ _ fun Z => ?_
  have e1 : (σ.arrowCongr (Equiv.refl Q)).symm Z = Z ∘ σ := rfl
  rw [e1, zetaS_equiv hsymm σ Z]
  congr 1
  exact (Equiv.prod_comp σ (fun i => w (Z i))).symm

lemma Ci_equiv (hsymm : ∀ a b, inc a b → inc b a) {ι ι' : Type*} [Fintype ι] [Fintype ι'] [DecidableEq ι] [DecidableEq ι'] (σ : ι' ≃ ι)
    (w : Q → R) : Ci (inc := inc) ι w = Ci (inc := inc) ι' w := by
  unfold Ci
  refine Fintype.sum_equiv (σ.arrowCongr (Equiv.refl Q)).symm _ _ fun Z => ?_
  have e1 : (σ.arrowCongr (Equiv.refl Q)).symm Z = Z ∘ σ := rfl
  rw [e1, ursS_equiv hsymm σ Z]
  congr 1
  exact (Equiv.prod_comp σ (fun i => w (Z i))).symm

/-- `E_n = Σ_{Z ∈ Q^n}Π_{i<j}ζΠw`. -/
def En (w : Q → R) (n : ℕ) : R := Ei (inc := inc) (Fin n) w

/-- `C_k = Σ_{Z ∈ Q^k}ρ^TΠw`. -/
def Ck (w : Q → R) (k : ℕ) : R := Ci (inc := inc) (Fin k) w

/-- Functions on `ι` are pairs of functions on `B` and on its complement. -/
def splitEquiv {ι : Type*} [Fintype ι] [DecidableEq ι] (B : Finset ι) : (ι → Q) ≃ (B → Q) × ((Bᶜ : Finset ι) → Q) where
  toFun Z := (fun x => Z x, fun x => Z x)
  invFun p x := if h : x ∈ B then p.1 ⟨x, h⟩ else p.2 ⟨x, Finset.mem_compl.2 h⟩
  left_inv Z := by funext x; by_cases h : x ∈ B <;> simp [h]
  right_inv p := by
    ext x
    · simp [x.2]
    · have : (x : ι) ∉ B := Finset.mem_compl.1 x.2
      simp [this]

lemma sum_split {ι : Type*} [Fintype ι] [DecidableEq ι] (B : Finset ι) (F : (B → Q) → R) (G : ((Bᶜ : Finset ι) → Q) → R) :
    ∑ Z : ι → Q, F (fun x => Z x) * G (fun x => Z x) =
      (∑ Z₁ : B → Q, F Z₁) * ∑ Z₂ : (Bᶜ : Finset ι) → Q, G Z₂ := by
  rw [Finset.sum_mul_sum, ← Fintype.sum_prod_type']
  exact Fintype.sum_equiv (splitEquiv B) _ _ fun Z => rfl

/-- The number of the sets `B ∋ r` of `k + 1` elements of `Fin n` is `C(n - 1, k)`. -/
lemma card_sets_with (n k : ℕ) (r : Fin n) :
    ((Finset.univ : Finset (Finset (Fin n))).filter (fun B => r ∈ B ∧ B.card = k + 1)).card =
      (n - 1).choose k := by
  have h : ((Finset.univ : Finset (Finset (Fin n))).filter (fun B => r ∈ B ∧ B.card = k + 1)).card =
      ((Finset.univ.erase r).powersetCard k).card := by
    refine Finset.card_bij (fun B _ => B.erase r) ?_ ?_ ?_
    · intro B hB
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hB
      rw [Finset.mem_powersetCard]
      refine ⟨Finset.erase_subset_erase r (Finset.subset_univ B), ?_⟩
      rw [Finset.card_erase_of_mem hB.1, hB.2]; rfl
    · intro B₁ h₁ B₂ h₂ he
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h₁ h₂
      rw [← Finset.insert_erase h₁.1, ← Finset.insert_erase h₂.1, he]
    · intro A hA
      rw [Finset.mem_powersetCard] at hA
      have hrA : r ∉ A := fun h => by have := hA.1 h; simp at this
      refine ⟨insert r A, ?_, Finset.erase_insert hrA⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨Finset.mem_insert_self r A, by rw [Finset.card_insert_of_notMem hrA, hA.2]⟩
  rw [h, Finset.card_powersetCard, Finset.card_erase_of_mem (Finset.mem_univ r), Finset.card_univ,
    Fintype.card_fin]

/-- **The recursion** `E_n = Σ_{k<n}C(n-1, k)C_{k+1}E_{n-1-k}` for `n ≥ 1`. -/
theorem En_rec (hsymm : ∀ a b, inc a b → inc b a) (w : Q → R) (n : ℕ) (hn : 1 ≤ n) :
    En (inc := inc) w n = ∑ k ∈ Finset.range n,
      ((n - 1).choose k : R) * Ck (inc := inc) w (k + 1) * En (inc := inc) w (n - 1 - k) := by
  set r : Fin n := ⟨0, hn⟩
  -- the decomposition of each `Π_{i<j}ζ`
  have hdec : ∀ Z : Fin n → Q, (zetaS inc Z : R) =
      ∑ B ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun B => r ∈ B),
        (ursS inc (fun x : B => Z x) : R) * (zetaS inc (fun x : (Bᶜ : Finset (Fin n)) => Z x) : R) := by
    intro Z
    have h := graph_decomp (R := R) r (fun e => (fp inc Z e : R))
    have hz : (zetaS inc Z : R) = ∑ g ∈ (pairsIn (Finset.univ : Finset (Fin n))).powerset,
        ∏ e ∈ g, (fp inc Z e : R) := by unfold zetaS; push_cast; rfl
    rw [hz, h]
    refine Finset.sum_congr (by ext; simp) fun B _ => ?_
    rw [← urs_restrict hsymm B Z, ← zeta_restrict hsymm Bᶜ Z]
    push_cast
    rfl
  -- each set `B` contributes `C_{|B|}E_{n-|B|}`
  have hB : ∀ B : Finset (Fin n), ∑ Z : Fin n → Q, (ursS inc (fun x : B => Z x) : R) *
      (zetaS inc (fun x : (Bᶜ : Finset (Fin n)) => Z x) : R) * ∏ i, w (Z i) =
        Ck (inc := inc) w B.card * En (inc := inc) w (n - B.card) := by
    intro B
    have e1 : ∀ Z : Fin n → Q, (ursS inc (fun x : B => Z x) : R) *
        (zetaS inc (fun x : (Bᶜ : Finset (Fin n)) => Z x) : R) * ∏ i, w (Z i) =
          ((ursS inc (fun x : B => Z x) : R) * ∏ x : B, w (Z x)) *
            ((zetaS inc (fun x : (Bᶜ : Finset (Fin n)) => Z x) : R) *
              ∏ x : (Bᶜ : Finset (Fin n)), w (Z x)) := by
      intro Z
      rw [Finset.prod_coe_sort B (fun i => w (Z i)), Finset.prod_coe_sort Bᶜ (fun i => w (Z i)),
        ← Finset.prod_mul_prod_compl B (fun i => w (Z i))]
      ring
    simp only [e1]
    have hs := sum_split B (fun Z₁ => (ursS inc Z₁ : R) * ∏ x, w (Z₁ x))
      (fun Z₂ => (zetaS inc Z₂ : R) * ∏ x, w (Z₂ x))
    simp only at hs
    refine hs.trans ?_
    show Ci (inc := inc) B w * Ei (inc := inc) (Bᶜ : Finset (Fin n)) w = _
    unfold Ck En
    rw [Ci_equiv hsymm (Fintype.equivFin B).symm w,
      Ei_equiv hsymm (Fintype.equivFin (Bᶜ : Finset (Fin n))).symm w]
    have h1 : Fintype.card B = B.card := Fintype.card_coe B
    have h2 : Fintype.card (Bᶜ : Finset (Fin n)) = n - B.card := by
      rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin]
    rw [h1, h2]
  unfold En Ei
  simp only [hdec, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [hB]
  -- group the sets by their cardinality
  rw [← Finset.sum_fiberwise_of_maps_to (s := (Finset.univ : Finset (Finset (Fin n))).filter (fun B => r ∈ B))
    (t := Finset.range n) (g := fun B => B.card - 1) (fun B hB => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hB
      have h1 := Finset.card_pos.2 ⟨r, hB⟩
      have h2 : B.card ≤ n := by simpa using Finset.card_le_univ B
      simp only [Finset.mem_range]; omega)]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k < n := Finset.mem_range.1 hk
  rw [Finset.sum_congr rfl (g := fun _ => Ck (inc := inc) w (k + 1) * Ei (inc := inc) (Fin (n - 1 - k)) w)
    (fun B hB => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hB
      have h1 := Finset.card_pos.2 ⟨r, hB.1⟩
      have hc : B.card = k + 1 := by omega
      rw [hc]
      have he : n - (k + 1) = n - 1 - k := by omega
      rw [he]
      rfl)]
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : (((Finset.univ : Finset (Finset (Fin n))).filter (fun B => r ∈ B)).filter
      (fun B => B.card - 1 = k)).card = (n - 1).choose k := by
    rw [Finset.filter_filter, ← card_sets_with n k r]
    congr 1
    ext B
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩; have := Finset.card_pos.2 ⟨r, h1⟩; exact ⟨h1, by omega⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩
  rw [hcard]
  unfold Ei
  ring

end TreeGraph
end CoreLean

end
