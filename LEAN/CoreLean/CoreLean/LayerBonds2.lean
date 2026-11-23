/-
`lem:layer-bonds`(ii) and (iii) of BALABAN_CORE.tex (`a021c13be348`), for the sequences of domains of
`SequencesTorus.lean`. A positive bond `c = (y, μ)` of `T^{(j)}` has the ends `y` and `y + a_je_μ` (`bend`); it is a bond
of the layer `Γ_j` if it has an end in `Ω_j` and no end in `Ω_{j+1}` (the paragraph after `def:sequence`,
`IsLayerBond`); `𝖡_c` is the set of the positive bonds of `T^{(0)}` with both ends in `B^j(c₋) ∪ B^j(c₊)` (`Bc`).
(ii) For `RM ≥ 2L` the blocks of the ends of `c` lie in `Ω_{j-1}` (`layer_bonds_ii`), so that a point of them lies in a
layer of an index `j' ≥ j - 1` and `a_j ≤ La_{j'}` (`layer_bonds_ii_scale`), which gives `‖a_jA‖_{∞,𝖡_c} ≤ L‖A‖_{∞,(-1)}`
(`layer_bonds_ii_norm`, for any function `A` on the bonds of `T^{(0)}`, weighted at the first end). (iii) A positive
bond of `T^{(0)}` whose first end lies in `Ω_j \ Ω_{j+1}` belongs to the sets `𝖡_c` of the bonds `c` of the layers of the
indices `j - 1`, `j`, `j + 1` only (`layer_bonds_iii_index`), and of at most `24` of them (`layer_bonds_iii`). The
proofs are the core's.
-/
import CoreLean.WideDomain

open Set

noncomputable section

namespace CoreLean
namespace Lattices
namespace SeqDom

variable (S : SeqDom)

/-- The end `y + a_je_μ` of the positive bond `(y, μ)` of `T^{(j)}`. -/
def bend (j : ℕ) (y : Tor (ellT S.L S.mT)) (μ : Fin 4) : Tor (ellT S.L S.mT) :=
  y + Pi.single μ ((sp S.L S.k j : ℝ) : AddCircle (ellT S.L S.mT))

/-- `(y, μ)` is a positive bond of the layer `Γ_j`: a bond of `T^{(j)}` with an end in `Ω_j` and no end in
`Ω_{j+1}`. -/
def IsLayerBond (j : ℕ) (y : Tor (ellT S.L S.mT)) (μ : Fin 4) : Prop :=
  y ∈ S.TL j ∧ (y ∈ S.Ω j ∨ S.bend j y μ ∈ S.Ω j) ∧ y ∉ S.Ω (j + 1) ∧ S.bend j y μ ∉ S.Ω (j + 1)

/-- The union `B^j(c₋) ∪ B^j(c₊)` of the blocks of the ends of `c = (y, μ)`. -/
def blocks (j : ℕ) (y : Tor (ellT S.L S.mT)) (μ : Fin 4) : Set (Tor (ellT S.L S.mT)) :=
  S.Δy (j, y) ∪ S.Δy (j, S.bend j y μ)

/-- `𝖡_c`: the positive bonds `(x, ν)` of `T^{(0)}` with both ends in `B^j(c₋) ∪ B^j(c₊)`. -/
def Bc (j : ℕ) (y : Tor (ellT S.L S.mT)) (μ : Fin 4) : Set (Tor (ellT S.L S.mT) × Fin 4) :=
  {b | b.1 ∈ S.blocks j y μ ∧ S.bend 0 b.1 b.2 ∈ S.blocks j y μ}

lemma dist_bend (j : ℕ) (y : Tor (ellT S.L S.mT)) (μ : Fin 4) : dist y (S.bend j y μ) ≤ sp S.L S.k j := by
  unfold bend
  rw [dist_self_add_right, Pi.norm_single]
  refine (norm_coe_le _).trans ?_
  rw [abs_of_pos (sp_pos S.Lpos j)]

lemma sp_mono {i j : ℕ} (h : i ≤ j) : sp S.L S.k i ≤ sp S.L S.k j := by
  unfold sp
  have hL : (1 : ℝ) ≤ S.L := by exact_mod_cast (show 1 ≤ S.L by have := S.three_le_L; omega)
  have : 0 < eta S.L S.k := by unfold eta; have := S.Lpos; positivity
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hL h) this.le

lemma mem_Δ_dist {j : ℕ} {x y : Tor (ellT S.L S.mT)} (h : x ∈ S.Δy (j, y)) : dist x y ≤ sp S.L S.k j / 2 := by
  have := ((S.mem_Δy).1 h).1
  simpa [Δ, cell, Metric.mem_closedBall] using this

lemma IsLayerBond.le_k {j : ℕ} {y : Tor (ellT S.L S.mT)} {μ : Fin 4} (h : S.IsLayerBond j y μ) : j ≤ S.k := by
  by_contra hj
  have hE := S.Ω_top j (by omega)
  rcases h.2.1 with h1 | h1 <;> rw [hE] at h1 <;> exact h1

/-- A point of the blocks of the ends of `c` is within `(3/2)a_j` of the end of `c` in `Ω_j`. -/
lemma near_end {j : ℕ} {y : Tor (ellT S.L S.mT)} {μ : Fin 4} (hc : S.IsLayerBond j y μ)
    {x : Tor (ellT S.L S.mT)} (hx : x ∈ S.blocks j y μ) :
    ∃ e ∈ S.Ω j, dist x e ≤ 3 / 2 * sp S.L S.k j := by
  have hb := S.dist_bend j y μ
  have hs := sp_pos (k := S.k) S.Lpos j
  rcases hc.2.1 with he | he
  · refine ⟨y, he, ?_⟩
    rcases hx with hx | hx
    · have := S.mem_Δ_dist hx; linarith
    · have := S.mem_Δ_dist hx
      have := dist_triangle x (S.bend j y μ) y
      rw [dist_comm (S.bend j y μ) y] at this; linarith
  · refine ⟨S.bend j y μ, he, ?_⟩
    rcases hx with hx | hx
    · have := S.mem_Δ_dist hx
      have := dist_triangle x y (S.bend j y μ); linarith
    · have := S.mem_Δ_dist hx; linarith

/-- **`lem:layer-bonds`(ii)**: for `RM ≥ 2L` the blocks of the ends of a bond `c` of `Γ_j`, and hence the bonds of
`𝖡_c`, lie in `Ω_{j-1}`. -/
theorem layer_bonds_ii (hRM : 2 * S.L ≤ S.R * S.L ^ S.mM) {j : ℕ} {y : Tor (ellT S.L S.mT)} {μ : Fin 4}
    (hc : S.IsLayerBond j y μ) {x : Tor (ellT S.L S.mT)} (hx : x ∈ S.blocks j y μ) : x ∈ S.Ω (j - 1) := by
  obtain ⟨e, he, hxe⟩ := S.near_end hc hx
  exact S.layer_bonds_i_two hRM hc.le_k he hxe

/-- **`lem:layer-bonds`(ii)**, the scales: a point of the blocks of the ends of a bond of `Γ_j` lies in a layer
`Ω_{j'} \ Ω_{j'+1}` with `j' ≥ j - 1`, and `a_j ≤ La_{j'}`. -/
theorem layer_bonds_ii_scale (hRM : 2 * S.L ≤ S.R * S.L ^ S.mM) {j : ℕ} {y : Tor (ellT S.L S.mT)} {μ : Fin 4}
    (hc : S.IsLayerBond j y μ) {x : Tor (ellT S.L S.mT)} (hx : x ∈ S.blocks j y μ) {j' : ℕ}
    (hx' : x ∉ S.Ω (j' + 1)) : j - 1 ≤ j' ∧ sp S.L S.k j ≤ S.L * sp S.L S.k j' := by
  have h1 := S.layer_bonds_ii hRM hc hx
  have hj : j - 1 ≤ j' := by
    by_contra h
    exact hx' (S.Ω_anti (by omega) h1)
  refine ⟨hj, ?_⟩
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · have := S.sp_mono (Nat.zero_le j')
    have hL : (1 : ℝ) ≤ S.L := by exact_mod_cast (show 1 ≤ S.L by have := S.three_le_L; omega)
    have := sp_pos (k := S.k) S.Lpos j'
    nlinarith
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rw [sp_succ]
    have hL : (0 : ℝ) ≤ S.L := by positivity
    exact mul_le_mul_of_nonneg_left (S.sp_mono (by omega)) hL

/-- **`lem:layer-bonds`(ii)**, the bound `‖a_jA‖_{∞,𝖡_c} ≤ L‖A‖_{∞,(-1)}`, for a function `A` on the bonds of `T^{(0)}`
with `a_{j'}|A(b)| ≤ N` whenever the first end of `b` lies in the layer `Ω_{j'} \ Ω_{j'+1}`. -/
theorem layer_bonds_ii_norm (hRM : 2 * S.L ≤ S.R * S.L ^ S.mM) {j : ℕ} {y : Tor (ellT S.L S.mT)} {μ : Fin 4}
    (hc : S.IsLayerBond j y μ) (A : Tor (ellT S.L S.mT) × Fin 4 → ℝ) {N : ℝ}
    (hA : ∀ b : Tor (ellT S.L S.mT) × Fin 4, ∀ j', b.1 ∈ S.Ω j' → b.1 ∉ S.Ω (j' + 1) → sp S.L S.k j' * |A b| ≤ N)
    {b : Tor (ellT S.L S.mT) × Fin 4} (hb : b ∈ S.Bc j y μ) : sp S.L S.k j * |A b| ≤ S.L * N := by
  obtain ⟨j', ⟨-, hj'1, hj'2⟩, -⟩ := S.layers_cover b.1
  have h := (S.layer_bonds_ii_scale hRM hc hb.1 hj'2).2
  have := hA b j' hj'1 hj'2
  calc sp S.L S.k j * |A b| ≤ S.L * sp S.L S.k j' * |A b| := mul_le_mul_of_nonneg_right h (abs_nonneg _)
    _ = S.L * (sp S.L S.k j' * |A b|) := by ring
    _ ≤ S.L * N := mul_le_mul_of_nonneg_left this (by positivity)

/-! ### (iii) -/

/-- **`lem:layer-bonds`(iii)**, the indices: if a positive bond `b` of `T^{(0)}` whose first end lies in
`Ω_j \ Ω_{j+1}` belongs to `𝖡_c` for a bond `c` of `Γ_i`, then `i ∈ {j - 1, j, j + 1}`. -/
theorem layer_bonds_iii_index (hRM : 2 * S.L ≤ S.R * S.L ^ S.mM) {j : ℕ} (hjk : j ≤ S.k)
    {b : Tor (ellT S.L S.mT) × Fin 4} (hb1 : b.1 ∈ S.Ω j) (hb2 : b.1 ∉ S.Ω (j + 1)) {i : ℕ}
    {y : Tor (ellT S.L S.mT)} {μ : Fin 4} (hc : S.IsLayerBond i y μ) (hbc : b ∈ S.Bc i y μ) :
    j - 1 ≤ i ∧ i ≤ j + 1 := by
  constructor
  · by_contra hi
    push_neg at hi
    -- both ends of `c` lie within `(3/2)a_i ≤ (3/2)a_{i+2}` of `b₋ ∈ Ω_{i+2}`, hence in `Ω_{i+1}`
    have hx : b.1 ∈ S.Ω (i + 2) := S.Ω_anti (by omega) hb1
    have hs := S.sp_mono (show i ≤ i + 2 by omega)
    have hb := S.dist_bend i y μ
    have hpos := sp_pos (k := S.k) S.Lpos i
    have hend : ∀ z, dist z b.1 ≤ 3 / 2 * sp S.L S.k i → z ∈ S.Ω (i + 1) := fun z hz =>
      S.layer_bonds_i_two hRM (by omega) hx (by linarith)
    rcases hbc.1 with h | h
    · have h1 := S.mem_Δ_dist h
      exact hc.2.2.1 (hend y (by rw [dist_comm]; linarith))
    · have h1 := S.mem_Δ_dist h
      exact hc.2.2.2 (hend _ (by rw [dist_comm]; linarith))
  · by_contra hi
    push_neg at hi
    have h1 := S.layer_bonds_ii hRM hc hbc.1
    exact hb2 (S.Ω_anti (by omega) h1)

/-- The bond `(y, μ)` of `T^{(j)}` has its end `y + a_je_μ` in `T^{(j)}`. -/
lemma bend_mem {j : ℕ} {y : Tor (ellT S.L S.mT)} (hy : y ∈ S.TL j) (μ : Fin 4) : S.bend j y μ ∈ S.TL j := by
  intro ν
  obtain ⟨r, hr⟩ := hy ν
  by_cases hν : ν = μ
  · subst hν
    refine ⟨r + 1, ?_⟩
    simp only [bend, Pi.add_apply, Pi.single_eq_same, hr, ← AddCircle.coe_add]
    congr 1; push_cast; ring
  · refine ⟨r, ?_⟩
    simp only [bend, Pi.add_apply, Pi.single_eq_of_ne hν, add_zero, hr]

open Classical in
/-- The point of `T^{(i)}` whose cell contains `x`. -/
def cellPt (i : ℕ) (x : Tor (ellT S.L S.mT)) : Tor (ellT S.L S.mT) :=
  if h : ∃ y, y ∈ S.TL i ∧ x ∈ Δ S.L S.k S.mT i y then h.choose else x

lemma cellPt_eq {i : ℕ} (hi : i ≤ S.k) {x y : Tor (ellT S.L S.mT)} (hx : x ∈ S.TL 0) (hy : y ∈ S.TL i)
    (hxy : x ∈ Δ S.L S.k S.mT i y) : S.cellPt i x = y := by
  have hex : ∃ y, y ∈ S.TL i ∧ x ∈ Δ S.L S.k S.mT i y := ⟨y, hy, hxy⟩
  obtain ⟨y₀, -, hu⟩ := S.unique_cell hi hx
  unfold cellPt
  rw [dif_pos hex]
  exact (hu _ hex.choose_spec).trans (hu y ⟨hy, hxy⟩).symm

/-- **`lem:layer-bonds`(iii)**: a positive bond `b` of `T^{(0)}` whose first end lies in `Ω_j \ Ω_{j+1}` belongs to the
sets `𝖡_c` of at most `24` bonds `c` of the layers, all of the indices `j - 1`, `j`, `j + 1`. -/
theorem layer_bonds_iii (hRM : 2 * S.L ≤ S.R * S.L ^ S.mM) {j : ℕ} (hjk : j ≤ S.k)
    {b : Tor (ellT S.L S.mT) × Fin 4} (hb0 : b.1 ∈ S.TL 0) (hb1 : b.1 ∈ S.Ω j) (hb2 : b.1 ∉ S.Ω (j + 1)) :
    ∃ F : Finset (ℕ × Tor (ellT S.L S.mT) × Fin 4), F.card ≤ 24 ∧
      ∀ i y μ, S.IsLayerBond i y μ → b ∈ S.Bc i y μ → (i, y, μ) ∈ F := by
  classical
  let sh : ℕ → Fin 4 → Tor (ellT S.L S.mT) := fun i μ => Pi.single μ ((sp S.L S.k i : ℝ) : AddCircle (ellT S.L S.mT))
  let f : Fin 3 × Fin 4 × Bool → ℕ × Tor (ellT S.L S.mT) × Fin 4 := fun q =>
    (j - 1 + q.1, if q.2.2 then S.cellPt (j - 1 + q.1) b.1 - sh (j - 1 + q.1) q.2.1
      else S.cellPt (j - 1 + q.1) b.1, q.2.1)
  refine ⟨Finset.univ.image f, (Finset.card_image_le).trans (by simp), fun i y μ hc hbc => ?_⟩
  obtain ⟨hi1, hi2⟩ := S.layer_bonds_iii_index hRM hjk hb1 hb2 hc hbc
  have hik := hc.le_k
  rw [Finset.mem_image]
  have ht : i - (j - 1) < 3 := by omega
  rcases hbc.1 with h | h
  · -- the first end lies in the block of `c₋ = y`
    refine ⟨(⟨i - (j - 1), ht⟩, μ, false), Finset.mem_univ _, ?_⟩
    have hi : j - 1 + (i - (j - 1)) = i := by omega
    simp only [f, hi, Bool.false_eq_true, if_false]
    rw [S.cellPt_eq hik hb0 hc.1 ((S.mem_Δy).1 h).1]
  · -- the first end lies in the block of `c₊ = y + a_ie_μ`
    refine ⟨(⟨i - (j - 1), ht⟩, μ, true), Finset.mem_univ _, ?_⟩
    have hi : j - 1 + (i - (j - 1)) = i := by omega
    simp only [f, hi, if_true]
    rw [S.cellPt_eq hik hb0 (S.bend_mem hc.1 μ) ((S.mem_Δy).1 h).1]
    simp [bend, sh]

end SeqDom
end Lattices
end CoreLean

end
