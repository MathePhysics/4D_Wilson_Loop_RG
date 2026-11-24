/-
`lem:sf-components` of BALABAN_CORE.tex (`aaaa938bb57d`) on the fine lattice of a sequence of domains (`a₀ = 1`): the box
`X_c` of a bond `c = (y, μ)` of `T^{(j)}` in the offsets of the blocks, and the average `Q` of the trivial configuration.

* `bx`, `phiB`: the site `y + (a - h)e_μ + Σ_i(o_i - h)e_{ν_i}` of the offsets `(a, o)`, `ν_i = μ.succAbove i`.
* `sum_box_insert`: the sum over the offsets of a block in the order `(a, b, c, d)` with `a` in the direction `μ`.
* `sum_Blk_box`, `sum_Blk_next`: the blocks of `c₋ = y` and `c₊ = y + a_je_μ` as the halves `a < n`, `n ≤ a < 2n`.
* `phiB_succ0` … `phiB_succ3`: the steps of the offsets are the fine bonds.
* `Qt`, `Qt_eq`: `(QA)(c) = n^{-5}Σ_{x ∈ B^j(y)}Σ_{t<n}A_μ(x + te_μ)` is `boxMean` of `A_μ ∘ phiB`.
* `ef_add`, `ef_ynext`, `ef_add_unit`, `mem_Blk_iff`, `mem_Xc_iff`: the fine lattice in the torus of `SequencesTorus`.
* `phiB_inj`, `phiB_mem_Xc`, `bonds_le`: the bonds of the box are fine bonds of `X_c = B^j(c₋) ∪ B^j(c₊)`.
* `cy`, `cy_facts`: the bond of the layer chosen at `y ∈ 𝐁` (`exists_layer_bond`); `block_bound`: the local bound.
* `card_boxes_le`, `boxes_sum_le`: at most `48` boxes through a fine bond (`lem:layer-bonds`(iii)); `q_sum_le`: each bond
  of the layers chosen at most twice.
* `sf_components`: **`lem:sf-components`**, `‖∇A‖² + ‖A‖_w² ≤ 2^{12}(‖∇A‖² + Σ_ca_c²|(QA)(c)|²)` (here `3073` in place of
  the core's `3841`), for `RM ≥ 2L`.
-/
import CoreLean.SFComponents
import CoreLean.SFComponentsGeom
import CoreLean.SFBlockKernel

open Finset

noncomputable section

namespace CoreLean
namespace SFBounds

open Lattices SeqDom Blocks SmallFieldBlocks SFComponents SFLocal SmallFieldDecay

variable (S : SeqDom) {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "NF" => SequenceAverages.N0 S
set_option quotPrecheck false in
local notation "jj" => (S.toDomSeq).sc

/-- The offsets `(a, b, c, d)` with `a` in the direction `μ`. -/
def bx (μ : Fin 4) (a b c d : ℕ) : Fin 4 → ℕ := Fin.insertNth μ a ![b, c, d]

lemma bx_same (μ : Fin 4) (a b c d : ℕ) : bx μ a b c d μ = a := by simp [bx]

lemma bx_succAbove (μ : Fin 4) (a b c d : ℕ) (i : Fin 3) : bx μ a b c d (μ.succAbove i) = ![b, c, d] i := by
  simp [bx]

lemma bx_self (μ : Fin 4) (o : Fin 4 → ℕ) :
    bx μ (o μ) (o (μ.succAbove 0)) (o (μ.succAbove 1)) (o (μ.succAbove 2)) = o := by
  have e : (![o (μ.succAbove 0), o (μ.succAbove 1), o (μ.succAbove 2)] : Fin 3 → ℕ) = Fin.removeNth μ o := by
    funext i; fin_cases i <;> rfl
  rw [bx, e, Fin.insertNth_self_removeNth]

/-- **The sum over the offsets of a block in the order `(a, b, c, d)`.** -/
lemma sum_box_insert {M : Type*} [AddCommMonoid M] (μ : Fin 4) (n : ℕ) (G : (Fin 4 → ℕ) → M) :
    ∑ o ∈ DiscretePoincare.box 4 n, G o =
      ∑ a ∈ range n, ∑ b ∈ range n, ∑ c ∈ range n, ∑ d ∈ range n, G (bx μ a b c d) := by
  simp only [← sum_product']
  refine Finset.sum_nbij' (fun o => (o μ, o (μ.succAbove 0), o (μ.succAbove 1), o (μ.succAbove 2)))
    (fun q => bx μ q.1 q.2.1 q.2.2.1 q.2.2.2) (fun o ho => ?_) (fun q hq => ?_) (fun o _ => bx_self μ o)
    (fun q _ => ?_) (fun o _ => by rw [bx_self])
  · simp only [DiscretePoincare.box, Fintype.mem_piFinset] at ho
    simp only [mem_product, ho, and_self]
  · simp only [mem_product] at hq
    simp only [DiscretePoincare.box, Fintype.mem_piFinset]
    intro ν
    refine Fin.succAboveCases μ ?_ (fun i => ?_) ν
    · rw [bx_same]; exact hq.1
    · rw [bx_succAbove]; fin_cases i
      · exact hq.2.1
      · exact hq.2.2.1
      · exact hq.2.2.2
  · obtain ⟨a, b, c, d⟩ := q
    simp [bx_same, bx_succAbove]

/-- The site of the offsets `(a, b, c, d)` of the box of `(y, μ)`. -/
def phiB (j : ℕ) (y : Site NF) (μ : Fin 4) (a b c d : ℕ) : Site NF := phi S.toDomSeq j y (bx μ a b c d)

/-- The block of `y` through the offsets with `a < n`. -/
lemma sum_Blk_box {M : Type*} [AddCommMonoid M] {j : ℕ} (hj : j ≤ S.k) {y : Site NF} (hy : InLat S.L j y)
    (μ : Fin 4) (g : Site NF → M) :
    ∑ x ∈ Blk S.toDomSeq j y, g x = ∑ a ∈ range (S.L ^ j), ∑ b ∈ range (S.L ^ j), ∑ c ∈ range (S.L ^ j),
      ∑ d ∈ range (S.L ^ j), g (phiB S j y μ a b c d) := by
  rw [sum_Blk (S := S.toDomSeq) j hj hy g, sum_box_insert μ]
  rfl

/-- `y + a_je_μ`, on the fine lattice. -/
def ynext (j : ℕ) (y : Site NF) (μ : Fin 4) : Site NF := y + ((S.L ^ j : ℕ) : ZMod NF) • unit NF μ

lemma phiB_next (j : ℕ) (y : Site NF) (μ : Fin 4) (a b c d : ℕ) :
    phi S.toDomSeq j (ynext S j y μ) (bx μ a b c d) = phiB S j y μ (a + S.L ^ j) b c d := by
  funext ν
  simp only [phiB, phi, ynext, unit, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  refine Fin.succAboveCases μ ?_ (fun i => ?_) ν
  · simp only [bx_same, Pi.single_eq_same, mul_one]
    push_cast; ring
  · simp only [bx_succAbove, Pi.single_eq_of_ne (Fin.succAbove_ne μ i), mul_zero, add_zero]

/-- The block of `y + a_je_μ` through the offsets with `n ≤ a < 2n`. -/
lemma sum_Blk_next {M : Type*} [AddCommMonoid M] {j : ℕ} (hj : j ≤ S.k) {y : Site NF} (μ : Fin 4)
    (hy : InLat S.L j (ynext S j y μ)) (g : Site NF → M) :
    ∑ x ∈ Blk S.toDomSeq j (ynext S j y μ), g x = ∑ a ∈ range (S.L ^ j), ∑ b ∈ range (S.L ^ j),
      ∑ c ∈ range (S.L ^ j), ∑ d ∈ range (S.L ^ j), g (phiB S j y μ (a + S.L ^ j) b c d) := by
  rw [sum_Blk (S := S.toDomSeq) j hj hy g, sum_box_insert μ]
  simp only [phiB_next]
  rfl

/-- The steps of the offsets are the fine bonds. -/
lemma phiB_succ0 (j : ℕ) (y : Site NF) (μ : Fin 4) (a b c d : ℕ) :
    phiB S j y μ (a + 1) b c d = phiB S j y μ a b c d + unit NF μ := by
  funext ν
  simp only [phiB, phi, unit, Pi.add_apply]
  refine Fin.succAboveCases μ ?_ (fun i => ?_) ν
  · simp only [bx_same, Pi.single_eq_same]; push_cast; ring
  · simp only [bx_succAbove, Pi.single_eq_of_ne (Fin.succAbove_ne μ i), add_zero]

lemma phiB_succ (j : ℕ) (y : Site NF) (μ : Fin 4) (i : Fin 3) (o : Fin 3 → ℕ) :
    phi S.toDomSeq j y (Fin.insertNth μ 0 (Function.update o i (o i + 1))) =
      phi S.toDomSeq j y (Fin.insertNth μ 0 o) + unit NF (μ.succAbove i) := by
  funext ν
  simp only [phi, unit, Pi.add_apply]
  refine Fin.succAboveCases μ ?_ (fun i' => ?_) ν
  · simp [Pi.single_eq_of_ne (Fin.succAbove_ne μ i).symm]
  · simp only [Fin.insertNth_apply_succAbove]
    by_cases h : i' = i
    · subst h; simp [Pi.single_eq_same]; push_cast; ring
    · simp [Function.update_of_ne h, Pi.single_eq_of_ne (fun e => h ((Fin.succAbove_right_inj).1 e))]

lemma phiB_add (j : ℕ) (y : Site NF) (μ : Fin 4) (a t b c d : ℕ) :
    phiB S j y μ (a + t) b c d = phiB S j y μ a b c d + ((t : ℕ) : ZMod NF) • unit NF μ := by
  funext ν
  simp only [phiB, phi, unit, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  refine Fin.succAboveCases μ ?_ (fun i => ?_) ν
  · simp only [bx_same, Pi.single_eq_same, mul_one]; push_cast; ring
  · simp only [bx_succAbove, Pi.single_eq_of_ne (Fin.succAbove_ne μ i), mul_zero, add_zero]

/-- A step of the offset `ν` is the fine bond in the direction `ν`. -/
lemma phi_update (j : ℕ) (y : Site NF) (o : Fin 4 → ℕ) (ν : Fin 4) :
    phi S.toDomSeq j y (Function.update o ν (o ν + 1)) = phi S.toDomSeq j y o + unit NF ν := by
  funext ν'
  simp only [phi, unit, Pi.add_apply]
  by_cases h : ν' = ν
  · subst h; simp [Pi.single_eq_same]; push_cast; ring
  · simp [Function.update_of_ne h, Pi.single_eq_of_ne h]

lemma bx_update1 (μ : Fin 4) (a b c d : ℕ) :
    bx μ a (b + 1) c d = Function.update (bx μ a b c d) (μ.succAbove 0) (bx μ a b c d (μ.succAbove 0) + 1) := by
  funext ν
  refine Fin.succAboveCases μ ?_ (fun i => ?_) ν
  · simp [bx_same, Function.update_of_ne (Fin.succAbove_ne μ 0).symm]
  · fin_cases i <;> simp [bx_succAbove, Function.update_apply, Fin.succAbove_right_inj]

lemma bx_update2 (μ : Fin 4) (a b c d : ℕ) :
    bx μ a b (c + 1) d = Function.update (bx μ a b c d) (μ.succAbove 1) (bx μ a b c d (μ.succAbove 1) + 1) := by
  funext ν
  refine Fin.succAboveCases μ ?_ (fun i => ?_) ν
  · simp [bx_same, Function.update_of_ne (Fin.succAbove_ne μ 1).symm]
  · fin_cases i <;> simp [bx_succAbove, Function.update_apply, Fin.succAbove_right_inj]

lemma bx_update3 (μ : Fin 4) (a b c d : ℕ) :
    bx μ a b c (d + 1) = Function.update (bx μ a b c d) (μ.succAbove 2) (bx μ a b c d (μ.succAbove 2) + 1) := by
  funext ν
  refine Fin.succAboveCases μ ?_ (fun i => ?_) ν
  · simp [bx_same, Function.update_of_ne (Fin.succAbove_ne μ 2).symm]
  · fin_cases i <;> simp [bx_succAbove, Function.update_apply, Fin.succAbove_right_inj]

lemma phiB_succ1 (j : ℕ) (y : Site NF) (μ : Fin 4) (a b c d : ℕ) :
    phiB S j y μ a (b + 1) c d = phiB S j y μ a b c d + unit NF (μ.succAbove 0) := by
  rw [phiB, bx_update1, phi_update]; rfl

lemma phiB_succ2 (j : ℕ) (y : Site NF) (μ : Fin 4) (a b c d : ℕ) :
    phiB S j y μ a b (c + 1) d = phiB S j y μ a b c d + unit NF (μ.succAbove 1) := by
  rw [phiB, bx_update2, phi_update]; rfl

lemma phiB_succ3 (j : ℕ) (y : Site NF) (μ : Fin 4) (a b c d : ℕ) :
    phiB S j y μ a b c (d + 1) = phiB S j y μ a b c d + unit NF (μ.succAbove 2) := by
  rw [phiB, bx_update3, phi_update]; rfl

/-- **The average `Q` of the trivial configuration** on the bond `(y, μ)` of `T^{(j)}`:
`n^{-5}Σ_{x ∈ B^j(y)}Σ_{t<n}A_μ(x + te_μ)`, `n = L^j`. -/
def Qt (A : Fin 4 → Site NF → Mat) (j : ℕ) (y : Site NF) (μ : Fin 4) : Mat :=
  ((((S.L ^ j : ℕ) : ℂ)) ^ 5)⁻¹ • ∑ x ∈ Blk S.toDomSeq j y, ∑ t ∈ range (S.L ^ j),
    A μ (x + ((t : ℕ) : ZMod NF) • unit NF μ)

/-- `emb((QA)(c))` is the box mean of `emb ∘ A_μ ∘ phiB`. -/
lemma Qt_eq {j : ℕ} (hj : j ≤ S.k) {y : Site NF} (hy : InLat S.L j y) (A : Fin 4 → Site NF → Mat) (μ : Fin 4) :
    emb (Qt S A j y μ) = boxMean (S.L ^ j) (fun a b c d => emb (N := N) (A μ (phiB S j y μ a b c d))) := by
  unfold Qt boxMean
  rw [card_Iq, sum_Blk_box S hj hy μ]
  simp only [Iq, sum_product, phiB_add]
  rw [show ((((S.L ^ j) ^ 5 : ℕ) : ℝ))⁻¹ = (((((S.L ^ j : ℕ) : ℝ)) ^ 5)⁻¹ : ℝ) by push_cast; ring]
  have hc : ((((S.L ^ j : ℕ) : ℂ)) ^ 5)⁻¹ = ((((((S.L ^ j : ℕ) : ℝ)) ^ 5)⁻¹ : ℝ) : ℂ) := by push_cast; ring
  rw [hc]
  show embL (((((((S.L ^ j : ℕ) : ℝ)) ^ 5)⁻¹ : ℝ) : ℂ) • _) = _
  rw [map_smul, ← Complex.coe_smul]
  congr 1
  simp only [map_sum]
  rfl

/-! ### The fine lattice and the torus -/

/-- `ef` is additive. -/
lemma ef_add (x z : Site NF) : S.ef (x + z) = S.ef x + S.ef z := by
  funext ν
  simp only [ef, Lattices.emb, Pi.add_apply]
  rw [← sub_eq_zero, sub_add_eq_sub_sub, ← AddCircle.coe_sub, ← AddCircle.coe_sub]
  have e : ((x ν + z ν).val : ℝ) * eta S.L S.k - ((x ν).val : ℝ) * eta S.L S.k - ((z ν).val : ℝ) * eta S.L S.k =
      ((((x ν + z ν).val : ℤ) - (x ν).val - (z ν).val : ℤ) : ℝ) * eta S.L S.k := by push_cast; ring
  rw [e, coe_mul_eq_zero_iff (eta_pos S.Lpos) (ellT_eq_N S.Lpos (SequenceAverages.N0_eq S)),
    ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  simp

/-- `ef(n e_μ) = (nη)e_μ`. -/
lemma ef_smul_unit (n : ℕ) (μ : Fin 4) :
    S.ef (((n : ℕ) : ZMod NF) • unit NF μ) = Pi.single μ (((n : ℝ) * eta S.L S.k : ℝ) : AddCircle (ellT S.L S.mT)) := by
  funext ν
  simp only [ef, Lattices.emb, unit, Pi.smul_apply, smul_eq_mul]
  by_cases h : ν = μ
  · subst h
    simp only [Pi.single_eq_same, mul_one]
    rw [← sub_eq_zero, ← AddCircle.coe_sub]
    have e : (((n : ZMod NF)).val : ℝ) * eta S.L S.k - (n : ℝ) * eta S.L S.k =
        (((((n : ZMod NF)).val : ℤ) - n : ℤ) : ℝ) * eta S.L S.k := by push_cast; ring
    rw [e, coe_mul_eq_zero_iff (eta_pos S.Lpos) (ellT_eq_N S.Lpos (SequenceAverages.N0_eq S)),
      ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    simp
  · simp [Pi.single_eq_of_ne h]

/-- The step `a_je_μ` on the fine lattice is the step `shj` of the torus. -/
lemma ef_ynext (j : ℕ) (y : Site NF) (μ : Fin 4) : S.ef (ynext S j y μ) = S.ef y + S.shj j μ := by
  rw [ynext, ef_add, ef_smul_unit]
  congr 1
  simp only [shj, sp]
  push_cast; ring_nf

/-- A fine bond is a bond of `T^{(0)}`. -/
lemma ef_add_unit (x : Site NF) (ν : Fin 4) : S.ef (x + unit NF ν) = S.bend 0 (S.ef x) ν := by
  have h := ef_smul_unit S 1 ν
  simp only [Nat.cast_one, one_smul, one_mul] at h
  rw [ef_add, h, bend, sp, pow_zero, one_mul]

/-- The fine points of a block are those of the cell. -/
lemma mem_Blk_iff {j : ℕ} (hj : j ≤ S.k) {y : Site NF} (hy : InLat S.L j y) (x : Site NF) :
    x ∈ Blk S.toDomSeq j y ↔ S.ef x ∈ S.Δy (j, S.ef y) := by
  rw [S.mem_Δy]
  dsimp only
  constructor
  · intro hx
    simp only [Blk, mem_filter, mem_univ, true_and] at hx
    refine ⟨?_, S.ef_mem_TL0 x⟩
    have := S.ef_mem_Δ_cen j x
    have hx' : cen S.L j x = y := hx
    rwa [hx'] at this
  · rintro ⟨hxΔ, -⟩
    simp only [Blk, mem_filter, mem_univ, true_and]
    obtain ⟨y0, -, hu⟩ := S.unique_cell hj (S.ef_mem_TL0 x)
    have e1 := hu _ ⟨S.ef_cen_mem_TL j x, S.ef_mem_Δ_cen j x⟩
    have e2 := hu _ ⟨S.ef_mem_TL_of hy, hxΔ⟩
    exact emb_injective S.Lpos (SequenceAverages.N0_eq S) (e1.trans e2.symm)

/-! ### The bonds of a box -/

lemma two_n_le {j : ℕ} (hj : j ≤ S.k) : 2 * S.L ^ j ≤ NF := by
  rw [SequenceAverages.N0_eq S]
  have : S.L ^ j ≤ S.L ^ (S.mT + S.k) := Nat.pow_le_pow_right S.Lpos (by omega)
  omega

lemma natCast_inj_lt {a a' : ℕ} (ha : a < NF) (ha' : a' < NF) (h : ((a : ℕ) : ZMod NF) = (a' : ZMod NF)) :
    a = a' := by
  rw [ZMod.natCast_eq_natCast_iff'] at h
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt ha'] at h

/-- `phiB` is injective on the box `[0, 2n) × [0, n)³`. -/
lemma phiB_inj {j : ℕ} (hj : j ≤ S.k) (y : Site NF) (μ : Fin 4) {a b c d a' b' c' d' : ℕ}
    (ha : a < 2 * S.L ^ j) (ha' : a' < 2 * S.L ^ j) (hb : b < 2 * S.L ^ j) (hb' : b' < 2 * S.L ^ j)
    (hc : c < 2 * S.L ^ j) (hc' : c' < 2 * S.L ^ j) (hd : d < 2 * S.L ^ j) (hd' : d' < 2 * S.L ^ j)
    (h : phiB S j y μ a b c d = phiB S j y μ a' b' c' d') : a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by
  have hN := two_n_le S hj
  have key : ∀ ν, (bx μ a b c d ν : ZMod NF) = (bx μ a' b' c' d' ν : ZMod NF) := fun ν => by
    have := congrFun h ν
    simp only [phiB, phi, add_right_inj] at this
    push_cast at this
    linear_combination this
  have k0 := key μ
  have k1 := key (μ.succAbove 0)
  have k2 := key (μ.succAbove 1)
  have k3 := key (μ.succAbove 2)
  simp only [bx_same, bx_succAbove] at k0 k1 k2 k3
  exact ⟨natCast_inj_lt S (by omega) (by omega) k0, natCast_inj_lt S (by omega) (by omega) k1,
    natCast_inj_lt S (by omega) (by omega) k2, natCast_inj_lt S (by omega) (by omega) k3⟩

/-- The box `X_c = B^j(c₋) ∪ B^j(c₊)` of the bond `(y, μ)` of `T^{(j)}`. -/
def Xc (j : ℕ) (y : Site NF) (μ : Fin 4) : Finset (Site NF) := Blk S.toDomSeq j y ∪ Blk S.toDomSeq j (ynext S j y μ)

lemma inLat_ynext {j : ℕ} {y : Site NF} (hy : InLat S.L j y) (μ : Fin 4) : InLat S.L j (ynext S j y μ) := by
  rw [inLat_iff S.Lpos (SequenceAverages.N0_eq S)] at hy ⊢
  have e := ef_ynext S j y μ
  simp only [ef] at e
  rw [e]
  exact S.bend_mem hy μ

lemma phiB_mem_Xc {j : ℕ} (hj : j ≤ S.k) {y : Site NF} (hy : InLat S.L j y) (μ : Fin 4) {a b c d : ℕ}
    (ha : a < 2 * S.L ^ j) (hb : b < S.L ^ j) (hc : c < S.L ^ j) (hd : d < S.L ^ j) :
    phiB S j y μ a b c d ∈ Xc S j y μ := by
  have hbox : ∀ a' : ℕ, a' < S.L ^ j → bx μ a' b c d ∈ DiscretePoincare.box 4 ((S.toDomSeq).L ^ j) := by
    intro a' ha'
    simp only [DiscretePoincare.box, Fintype.mem_piFinset, mem_range]
    intro ν
    refine Fin.succAboveCases μ ?_ (fun i => ?_) ν
    · rw [bx_same]; exact ha'
    · rw [bx_succAbove]; fin_cases i
      · exact hb
      · exact hc
      · exact hd
  rcases Nat.lt_or_ge a (S.L ^ j) with h | h
  · exact mem_union_left _ (phi_mem (S := S.toDomSeq) j hj hy (hbox a h))
  · refine mem_union_right _ ?_
    obtain ⟨a', rfl⟩ := Nat.exists_eq_add_of_le h
    rw [add_comm, ← phiB_next]
    exact phi_mem (S := S.toDomSeq) j hj (inLat_ynext S hy μ) (hbox a' (by omega))

/-- `|A_μ(x + e_ν) - A_μ(x)|²` (in the norm of `V`). -/
def gbond (A : Fin 4 → Site NF → Mat) (μ : Fin 4) (x : Site NF) (ν : Fin 4) : ℝ :=
  ‖emb (N := N) (A μ (x + unit NF ν)) - emb (A μ x)‖ ^ 2

/-- The component `A_μ` on the box of `(y, μ)`. -/
def Fbox (A : Fin 4 → Site NF → Mat) (j : ℕ) (y : Site NF) (μ : Fin 4) : ℕ → ℕ → ℕ → ℕ → VS N 1 :=
  fun a b c d => emb (A μ (phiB S j y μ a b c d))

/-- An injective family of fine bonds of `X_c` in the direction `ν`. -/
lemma fam_le {ι : Type*} (I : Finset ι) (f : ι → Site NF) (hf : Set.InjOn f I) (T : Finset (Site NF)) (ν : Fin 4)
    (hT : ∀ i ∈ I, f i ∈ T ∧ f i + unit NF ν ∈ T) (G : Site NF → ℝ) (hG : ∀ x, 0 ≤ G x) :
    ∑ i ∈ I, G (f i) ≤ ∑ x ∈ T, if x + unit NF ν ∈ T then G x else 0 := by
  rw [← sum_filter, ← sum_image hf]
  refine sum_le_sum_of_subset_of_nonneg (fun x hx => ?_) fun x _ _ => hG x
  obtain ⟨i, hi, rfl⟩ := mem_image.1 hx
  exact mem_filter.2 (hT i hi)

set_option maxHeartbeats 4000000 in
/-- **The bonds of the box are fine bonds of `X_c`.** -/
theorem bonds_le {j : ℕ} (hj : j ≤ S.k) {y : Site NF} (hy : InLat S.L j y) (A : Fin 4 → Site NF → Mat) (μ : Fin 4) :
    bondsAll (2 * S.L ^ j) (S.L ^ j) (S.L ^ j) (S.L ^ j) (Fbox S A j y μ) ≤
      ∑ x ∈ Xc S j y μ, ∑ ν, if x + unit NF ν ∈ Xc S j y μ then gbond S A μ x ν else 0 := by
  set n := S.L ^ j
  have hn : 1 ≤ n := Nat.one_le_pow _ _ S.Lpos
  have hG : ∀ ν x, 0 ≤ gbond S A μ x ν := fun _ _ => sq_nonneg _
  have hsplit : ∀ x, (∑ ν, if x + unit NF ν ∈ Xc S j y μ then gbond S A μ x ν else 0) =
      (if x + unit NF μ ∈ Xc S j y μ then gbond S A μ x μ else 0) +
      (if x + unit NF (μ.succAbove 0) ∈ Xc S j y μ then gbond S A μ x (μ.succAbove 0) else 0) +
      (if x + unit NF (μ.succAbove 1) ∈ Xc S j y μ then gbond S A μ x (μ.succAbove 1) else 0) +
      (if x + unit NF (μ.succAbove 2) ∈ Xc S j y μ then gbond S A μ x (μ.succAbove 2) else 0) := fun x => by
    rw [Fin.sum_univ_succAbove _ μ, Fin.sum_univ_three]; ring
  simp only [hsplit, sum_add_distrib]
  unfold bondsAll Fbox
  refine add_le_add (add_le_add (add_le_add ?_ ?_) ?_) ?_
  · -- the direction `μ`
    have e : ∑ b ∈ range n, ∑ c ∈ range n, ∑ d ∈ range n, ∑ t ∈ range (2 * n - 1),
        ‖emb (N := N) (A μ (phiB S j y μ (t + 1) b c d)) - emb (A μ (phiB S j y μ t b c d))‖ ^ 2 =
        ∑ q ∈ range n ×ˢ range n ×ˢ range n ×ˢ range (2 * n - 1),
          gbond S A μ (phiB S j y μ q.2.2.2 q.1 q.2.1 q.2.2.1) μ := by
      simp only [sum_product, gbond, phiB_succ0]
    rw [e]
    refine fam_le S _ _ ?_ _ μ ?_ _ (hG μ)
    · intro q hq q' hq' h
      simp only [coe_product, Set.mem_prod, mem_coe, mem_range] at hq hq'
      obtain ⟨h1, h2, h3, h4⟩ := phiB_inj S hj y μ (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) h
      exact Prod.ext h2 (Prod.ext h3 (Prod.ext h4 h1))
    · intro q hq
      simp only [mem_product, mem_range] at hq
      refine ⟨phiB_mem_Xc S hj hy μ (by omega) hq.1 hq.2.1 hq.2.2.1, ?_⟩
      rw [← phiB_succ0]; exact phiB_mem_Xc S hj hy μ (by omega) hq.1 hq.2.1 hq.2.2.1
  · have e : ∑ a ∈ range (2 * n), ∑ c ∈ range n, ∑ d ∈ range n, ∑ t ∈ range (n - 1),
        ‖emb (N := N) (A μ (phiB S j y μ a (t + 1) c d)) - emb (A μ (phiB S j y μ a t c d))‖ ^ 2 =
        ∑ q ∈ range (2 * n) ×ˢ range n ×ˢ range n ×ˢ range (n - 1),
          gbond S A μ (phiB S j y μ q.1 q.2.2.2 q.2.1 q.2.2.1) (μ.succAbove 0) := by
      simp only [sum_product, gbond, phiB_succ1]
    rw [e]
    refine fam_le S _ _ ?_ _ _ ?_ _ (hG _)
    · intro q hq q' hq' h
      simp only [coe_product, Set.mem_prod, mem_coe, mem_range] at hq hq'
      obtain ⟨h1, h2, h3, h4⟩ := phiB_inj S hj y μ (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) h
      exact Prod.ext h1 (Prod.ext h3 (Prod.ext h4 h2))
    · intro q hq
      simp only [mem_product, mem_range] at hq
      refine ⟨phiB_mem_Xc S hj hy μ hq.1 (by omega) hq.2.1 hq.2.2.1, ?_⟩
      rw [← phiB_succ1]; exact phiB_mem_Xc S hj hy μ hq.1 (by omega) hq.2.1 hq.2.2.1
  · have e : ∑ a ∈ range (2 * n), ∑ b ∈ range n, ∑ d ∈ range n, ∑ t ∈ range (n - 1),
        ‖emb (N := N) (A μ (phiB S j y μ a b (t + 1) d)) - emb (A μ (phiB S j y μ a b t d))‖ ^ 2 =
        ∑ q ∈ range (2 * n) ×ˢ range n ×ˢ range n ×ˢ range (n - 1),
          gbond S A μ (phiB S j y μ q.1 q.2.1 q.2.2.2 q.2.2.1) (μ.succAbove 1) := by
      simp only [sum_product, gbond, phiB_succ2]
    rw [e]
    refine fam_le S _ _ ?_ _ _ ?_ _ (hG _)
    · intro q hq q' hq' h
      simp only [coe_product, Set.mem_prod, mem_coe, mem_range] at hq hq'
      obtain ⟨h1, h2, h3, h4⟩ := phiB_inj S hj y μ (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) h
      exact Prod.ext h1 (Prod.ext h2 (Prod.ext h4 h3))
    · intro q hq
      simp only [mem_product, mem_range] at hq
      refine ⟨phiB_mem_Xc S hj hy μ hq.1 hq.2.1 (by omega) hq.2.2.1, ?_⟩
      rw [← phiB_succ2]; exact phiB_mem_Xc S hj hy μ hq.1 hq.2.1 (by omega) hq.2.2.1
  · have e : ∑ a ∈ range (2 * n), ∑ b ∈ range n, ∑ c ∈ range n, ∑ t ∈ range (n - 1),
        ‖emb (N := N) (A μ (phiB S j y μ a b c (t + 1))) - emb (A μ (phiB S j y μ a b c t))‖ ^ 2 =
        ∑ q ∈ range (2 * n) ×ˢ range n ×ˢ range n ×ˢ range (n - 1),
          gbond S A μ (phiB S j y μ q.1 q.2.1 q.2.2.1 q.2.2.2) (μ.succAbove 2) := by
      simp only [sum_product, gbond, phiB_succ3]
    rw [e]
    refine fam_le S _ _ ?_ _ _ ?_ _ (hG _)
    · intro q hq q' hq' h
      simp only [coe_product, Set.mem_prod, mem_coe, mem_range] at hq hq'
      obtain ⟨h1, h2, h3, h4⟩ := phiB_inj S hj y μ (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) h
      exact Prod.ext h1 (Prod.ext h2 (Prod.ext h3 h4))
    · intro q hq
      simp only [mem_product, mem_range] at hq
      refine ⟨phiB_mem_Xc S hj hy μ hq.1 hq.2.1 hq.2.2.1 (by omega), ?_⟩
      rw [← phiB_succ3]; exact phiB_mem_Xc S hj hy μ hq.1 hq.2.1 hq.2.2.1 (by omega)

/-! ### The bond chosen at a block -/

/-- `ef y ∈ Γ_j` for a point `y ∈ 𝐁` of the scale `j`. -/
lemma detB_facts {y : Site NF} (hy : y ∈ detB S.toDomSeq) :
    InLat S.L (jj y) y ∧ jj y ≤ S.k ∧ S.ef y ∈ S.TL (jj y) ∧ S.ef y ∈ S.Ω (jj y) ∧ S.ef y ∉ S.Ω (jj y + 1) := by
  have hl := (mem_detB_iff_inLat S y).1 hy
  refine ⟨hl, (S.toDomSeq).sc_le y, S.ef_mem_TL_of hl, S.ef_mem_sc y, fun h => ?_⟩
  have := ((S.toDomSeq).mem_iff y (jj y + 1)).1 (S.mem_toDomSeq_Ω.2 h)
  omega

open Classical in
/-- The bond of the layer chosen at `y ∈ 𝐁` in the direction `μ`: `(y, μ)` if it is one, else `(y - a_je_μ, μ)`. -/
def cy (y : Site NF) (μ : Fin 4) : Site NF :=
  if S.IsLayerBond (jj y) (S.ef y) μ then y else y - ((S.L ^ jj y : ℕ) : ZMod NF) • unit NF μ

lemma ef_sub_step (j : ℕ) (y : Site NF) (μ : Fin 4) :
    S.ef (y - ((S.L ^ j : ℕ) : ZMod NF) • unit NF μ) = S.ef y - S.shj j μ := by
  have h := ef_ynext S j (y - ((S.L ^ j : ℕ) : ZMod NF) • unit NF μ) μ
  rw [ynext, sub_add_cancel] at h
  rw [h]; abel

open Classical in
lemma cy_facts {y : Site NF} (hy : y ∈ detB S.toDomSeq) (μ : Fin 4) :
    S.IsLayerBond (jj y) (S.ef (cy S y μ)) μ ∧ InLat S.L (jj y) (cy S y μ) ∧
      (y = cy S y μ ∨ y = ynext S (jj y) (cy S y μ) μ) := by
  obtain ⟨hl, hk, hT, hΩ, hn⟩ := detB_facts S hy
  unfold cy
  split_ifs with h
  · exact ⟨h, hl, Or.inl rfl⟩
  · have hb := (S.exists_layer_bond hk hT hΩ hn μ).resolve_left h
    refine ⟨by rw [ef_sub_step]; exact hb, ?_, Or.inr (by rw [ynext, sub_add_cancel])⟩
    rw [inLat_iff S.Lpos (SequenceAverages.N0_eq S)]
    have := ef_sub_step S (jj y) y μ
    simp only [ef] at this
    rw [this]
    exact hb.1

/-- **The local bound at a block**: `a_j^{-2}Σ_{Δ(y)}|A_μ|² ≤ 64Σ_{b ⊂ X_c}|∂A_μ|² + 2a_j²|(QA)(c)|²` with `c` the bond chosen
at `y` in the direction `μ` (in the norm of `V`). -/
theorem block_bound {y : Site NF} (hy : y ∈ detB S.toDomSeq) (A : Fin 4 → Site NF → Mat) (μ : Fin 4) :
    (((S.L ^ jj y : ℕ) : ℝ) ^ 2)⁻¹ * ∑ x ∈ Blk S.toDomSeq (jj y) y, ‖emb (N := N) (A μ x)‖ ^ 2 ≤
      64 * bondsAll (2 * S.L ^ jj y) (S.L ^ jj y) (S.L ^ jj y) (S.L ^ jj y) (Fbox S A (jj y) (cy S y μ) μ) +
        2 * ((S.L ^ jj y : ℕ) : ℝ) ^ 2 * ‖emb (N := N) (Qt S A (jj y) (cy S y μ) μ)‖ ^ 2 := by
  obtain ⟨-, hk, -, -, -⟩ := detB_facts S hy
  obtain ⟨-, hlc, hcase⟩ := cy_facts S hy μ
  set j := jj y
  set n := S.L ^ j
  have hn : 1 ≤ n := Nat.one_le_pow _ _ S.Lpos
  rw [Qt_eq S hk hlc]
  rcases hcase with h | h
  · have hD : range n ×ˢ range n ×ˢ range n ×ˢ range n ⊆ boxQ n := by
      intro q hq; simp only [boxQ, mem_product, mem_range] at hq ⊢; omega
    have hc : (range n ×ˢ range n ×ˢ range n ×ˢ range n).card = n ^ 4 := by simp [card_product]; ring
    have hl := local_components n hn (Fbox S A j (cy S y μ) μ) _ hD hc
    have e : ∑ p ∈ range n ×ˢ range n ×ˢ range n ×ˢ range n,
        ‖Fbox S A j (cy S y μ) μ p.1 p.2.1 p.2.2.1 p.2.2.2‖ ^ 2 = ∑ x ∈ Blk S.toDomSeq j y, ‖emb (N := N) (A μ x)‖ ^ 2 := by
      conv_rhs => rw [h]
      rw [sum_Blk_box S hk hlc μ]
      simp only [sum_product, Fbox]
      rfl
    rw [e] at hl
    exact hl
  · have hD : Ico n (2 * n) ×ˢ range n ×ˢ range n ×ˢ range n ⊆ boxQ n := by
      intro q hq; simp only [boxQ, mem_product, mem_range, mem_Ico] at hq ⊢; omega
    have hc : (Ico n (2 * n) ×ˢ range n ×ˢ range n ×ˢ range n).card = n ^ 4 := by
      simp [card_product]; rw [show 2 * n - n = n by omega]; ring
    have hl := local_components n hn (Fbox S A j (cy S y μ) μ) _ hD hc
    have e : ∑ p ∈ Ico n (2 * n) ×ˢ range n ×ˢ range n ×ˢ range n,
        ‖Fbox S A j (cy S y μ) μ p.1 p.2.1 p.2.2.1 p.2.2.2‖ ^ 2 = ∑ x ∈ Blk S.toDomSeq j y, ‖emb (N := N) (A μ x)‖ ^ 2 := by
      conv_rhs => rw [h]
      rw [sum_Blk_next S hk μ (by rw [← h]; exact (detB_facts S hy).1)]
      simp only [sum_product, Fbox]
      rw [Finset.sum_Ico_eq_sum_range, show 2 * n - n = n by omega]
      refine sum_congr rfl fun a _ => ?_
      rw [add_comm n a]
    rw [e] at hl
    exact hl

/-! ### The multiplicities -/

lemma mem_Xc_iff {j : ℕ} (hj : j ≤ S.k) {c : Site NF} (hc : InLat S.L j c) (μ : Fin 4) (x : Site NF) :
    x ∈ Xc S j c μ ↔ S.ef x ∈ S.blocks j (S.ef c) μ := by
  have hb : S.bend j (S.ef c) μ = S.ef (ynext S j c μ) := by rw [ef_ynext]; rfl
  simp only [Xc, mem_union, blocks, Set.mem_union, hb]
  rw [mem_Blk_iff S hj hc, mem_Blk_iff S hj (inLat_ynext S hc μ)]

open Classical in
/-- **The boxes through a fine bond**: at most `48` points `y ∈ 𝐁` have the bond `(x, x + e_ν)` in the box of the bond
chosen at `y` in the direction `μ` (`lem:layer-bonds`(iii): at most `24` bonds `c`, each chosen at most twice). -/
lemma card_boxes_le (hRM : 2 * S.L ≤ S.R * S.L ^ S.mM) (x : Site NF) (μ ν : Fin 4) :
    ((detB S.toDomSeq).filter fun y => x ∈ Xc S (jj y) (cy S y μ) μ ∧
      x + unit NF ν ∈ Xc S (jj y) (cy S y μ) μ).card ≤ 48 := by
  have hx1 : S.ef x ∈ S.Ω (jj x) := S.ef_mem_sc x
  have hx2 : S.ef x ∉ S.Ω (jj x + 1) := fun h => by
    have := ((S.toDomSeq).mem_iff x (jj x + 1)).1 (S.mem_toDomSeq_Ω.2 h); omega
  obtain ⟨F, hF, hmem⟩ := S.layer_bonds_iii hRM ((S.toDomSeq).sc_le x) (b := (S.ef x, ν)) (S.ef_mem_TL0 x) hx1 hx2
  set Y := (detB S.toDomSeq).filter fun y => x ∈ Xc S (jj y) (cy S y μ) μ ∧ x + unit NF ν ∈ Xc S (jj y) (cy S y μ) μ
  set f : Site NF → ℕ × Tor (ellT S.L S.mT) × Fin 4 := fun y => (jj y, S.ef (cy S y μ), μ)
  have himg : Y.image f ⊆ F := by
    intro q hq
    obtain ⟨y, hy, rfl⟩ := mem_image.1 hq
    obtain ⟨hyB, hx, hx'⟩ := mem_filter.1 hy
    obtain ⟨hlb, hlc, -⟩ := cy_facts S hyB μ
    have hk := (detB_facts S hyB).2.1
    refine hmem _ _ _ hlb ⟨?_, ?_⟩
    · exact (mem_Xc_iff S hk hlc μ x).1 hx
    · show S.bend 0 (S.ef x) ν ∈ _
      rw [← ef_add_unit]; exact (mem_Xc_iff S hk hlc μ _).1 hx'
  have hfib : ∀ q ∈ Y.image f, (Y.filter fun y => f y = q).card ≤ 2 := by
    intro q hq
    obtain ⟨y0, hy0, rfl⟩ := mem_image.1 hq
    refine (card_le_card (s := Y.filter fun y => f y = f y0) (t := {cy S y0 μ, ynext S (jj y0) (cy S y0 μ) μ})
      fun y hy => ?_).trans (card_le_two)
    obtain ⟨hyY, hfy⟩ := mem_filter.1 hy
    have hyB := (mem_filter.1 hyY).1
    simp only [f, Prod.mk.injEq] at hfy
    obtain ⟨hj, hc, -⟩ := hfy
    have hcc : cy S y μ = cy S y0 μ := emb_injective S.Lpos (SequenceAverages.N0_eq S) hc
    rcases (cy_facts S hyB μ).2.2 with h | h
    · rw [h, hcc]; exact mem_insert_self _ _
    · rw [h, hcc, hj]; exact mem_insert_of_mem (mem_singleton_self _)
  calc Y.card ≤ 2 * (Y.image f).card := card_le_mul_card_image Y 2 hfib
    _ ≤ 2 * 24 := Nat.mul_le_mul_left _ ((card_le_card himg).trans hF)
    _ = 48 := by norm_num

/-- `‖∇A‖² = Σ_{μ,ν}Σ_x|A_μ(x + e_ν) - A_μ(x)|²` (in the norm of `V`). -/
def gradNorm (A : Fin 4 → Site NF → Mat) : ℝ := ∑ μ, ∑ x, ∑ ν, gbond S A μ x ν

open Classical in
/-- **The sum of the boxes**: `Σ_{y,μ}Σ_{b ⊂ X_{c(y,μ)}}|∂A_μ(b)|² ≤ 48‖∇A‖²`. -/
lemma boxes_sum_le (hRM : 2 * S.L ≤ S.R * S.L ^ S.mM) (A : Fin 4 → Site NF → Mat) :
    ∑ y ∈ detB S.toDomSeq, ∑ μ, ∑ x ∈ Xc S (jj y) (cy S y μ) μ, ∑ ν,
      (if x + unit NF ν ∈ Xc S (jj y) (cy S y μ) μ then gbond S A μ x ν else 0) ≤ 48 * gradNorm S A := by
  have hG : ∀ μ x ν, 0 ≤ gbond S A μ x ν := fun _ _ _ => sq_nonneg _
  have e1 : ∀ y μ, ∑ x ∈ Xc S (jj y) (cy S y μ) μ, ∑ ν,
      (if x + unit NF ν ∈ Xc S (jj y) (cy S y μ) μ then gbond S A μ x ν else 0) =
      ∑ x, ∑ ν, (if x ∈ Xc S (jj y) (cy S y μ) μ ∧ x + unit NF ν ∈ Xc S (jj y) (cy S y μ) μ
        then gbond S A μ x ν else 0) := by
    intro y μ
    rw [← sum_filter_add_sum_filter_not univ (fun x => x ∈ Xc S (jj y) (cy S y μ) μ)]
    rw [filter_mem_eq_inter, univ_inter]
    have h0 : ∑ x ∈ univ.filter (fun x => x ∉ Xc S (jj y) (cy S y μ) μ), ∑ ν,
        (if x ∈ Xc S (jj y) (cy S y μ) μ ∧ x + unit NF ν ∈ Xc S (jj y) (cy S y μ) μ then gbond S A μ x ν else 0) = 0 :=
      sum_eq_zero fun x hx => sum_eq_zero fun ν _ => by rw [if_neg (fun h => (mem_filter.1 hx).2 h.1)]
    rw [h0, add_zero]
    refine sum_congr rfl fun x hx => sum_congr rfl fun ν _ => ?_
    by_cases h : x + unit NF ν ∈ Xc S (jj y) (cy S y μ) μ
    · rw [if_pos h, if_pos ⟨hx, h⟩]
    · rw [if_neg h, if_neg (fun h' => h h'.2)]
  simp only [e1]
  rw [Finset.sum_comm]
  unfold gradNorm
  rw [mul_sum]
  refine sum_le_sum fun μ _ => ?_
  rw [Finset.sum_comm, mul_sum]
  refine sum_le_sum fun x _ => ?_
  rw [Finset.sum_comm, mul_sum]
  refine sum_le_sum fun ν _ => ?_
  rw [← sum_filter]
  calc ∑ y ∈ (detB S.toDomSeq).filter (fun y => x ∈ Xc S (jj y) (cy S y μ) μ ∧
        x + unit NF ν ∈ Xc S (jj y) (cy S y μ) μ), gbond S A μ x ν
      = ((detB S.toDomSeq).filter (fun y => x ∈ Xc S (jj y) (cy S y μ) μ ∧
          x + unit NF ν ∈ Xc S (jj y) (cy S y μ) μ)).card * gbond S A μ x ν := by rw [sum_const, nsmul_eq_mul]
    _ ≤ 48 * gbond S A μ x ν := by
        refine mul_le_mul_of_nonneg_right ?_ (hG μ x ν)
        exact_mod_cast card_boxes_le S hRM x μ ν

open Classical in
/-- The bonds of the layers on the fine lattice: `(j, y, μ)` with `y ∈ T^{(j)}` and `(ef y, μ)` a bond of `Γ_j`. -/
def QB : Finset (ℕ × Site NF × Fin 4) :=
  ((range (S.k + 1)) ×ˢ univ ×ˢ univ).filter fun q => InLat S.L q.1 q.2.1 ∧ S.IsLayerBond q.1 (S.ef q.2.1) q.2.2

/-- `Σ_ca_c²|(QA)(c)|²`, the constraint part of `⟨A^*, Δ^F_𝖺A⟩` (in the norm of `V`). -/
def Qnorm (A : Fin 4 → Site NF → Mat) : ℝ :=
  ∑ q ∈ QB S, ((S.L ^ q.1 : ℕ) : ℝ) ^ 2 * ‖emb (N := N) (Qt S A q.1 q.2.1 q.2.2)‖ ^ 2

/-- `‖A‖_w² = Σ_xa_{j(x)}^{-2}|A(x)|²` (in the norm of `V`). -/
def wnorm (A : Fin 4 → Site NF → Mat) : ℝ :=
  ∑ x, (((S.L ^ jj x : ℕ) : ℝ) ^ 2)⁻¹ * ∑ μ, ‖emb (N := N) (A μ x)‖ ^ 2

open Classical in
/-- **The sum of the constraint terms**: each bond of the layers is chosen at most twice. -/
lemma q_sum_le (A : Fin 4 → Site NF → Mat) :
    ∑ y ∈ detB S.toDomSeq, ∑ μ, ((S.L ^ jj y : ℕ) : ℝ) ^ 2 * ‖emb (N := N) (Qt S A (jj y) (cy S y μ) μ)‖ ^ 2 ≤
      2 * Qnorm S A := by
  set G : ℕ × Site NF × Fin 4 → ℝ := fun q => ((S.L ^ q.1 : ℕ) : ℝ) ^ 2 * ‖emb (N := N) (Qt S A q.1 q.2.1 q.2.2)‖ ^ 2
  have hG : ∀ q, 0 ≤ G q := fun q => by positivity
  set g : Site NF × Fin 4 → ℕ × Site NF × Fin 4 := fun p => (jj p.1, cy S p.1 p.2, p.2)
  have hmaps : ∀ p ∈ detB S.toDomSeq ×ˢ (univ : Finset (Fin 4)), g p ∈ QB S := by
    intro p hp
    obtain ⟨hy, -⟩ := mem_product.1 hp
    obtain ⟨hlb, hlc, -⟩ := cy_facts S hy p.2
    have hk := (detB_facts S hy).2.1
    simp only [QB, mem_filter, mem_product, mem_range, mem_univ, and_true, g]
    exact ⟨by omega, hlc, hlb⟩
  have e : ∑ y ∈ detB S.toDomSeq, ∑ μ, ((S.L ^ jj y : ℕ) : ℝ) ^ 2 * ‖emb (N := N) (Qt S A (jj y) (cy S y μ) μ)‖ ^ 2 =
      ∑ p ∈ detB S.toDomSeq ×ˢ (univ : Finset (Fin 4)), G (g p) := by rw [sum_product]
  rw [e, ← sum_fiberwise_of_maps_to hmaps, Qnorm, mul_sum]
  refine sum_le_sum fun q hq => ?_
  have hfib : ((detB S.toDomSeq ×ˢ (univ : Finset (Fin 4))).filter fun p => g p = q).card ≤ 2 := by
    refine (card_le_card (t := {(q.2.1, q.2.2), (ynext S q.1 q.2.1 q.2.2, q.2.2)}) fun p hp => ?_).trans card_le_two
    obtain ⟨hpP, hgp⟩ := mem_filter.1 hp
    obtain ⟨hy, -⟩ := mem_product.1 hpP
    rw [← hgp]
    simp only [g]
    rcases (cy_facts S hy p.2).2.2 with h | h
    · refine mem_insert.2 (Or.inl ?_)
      exact Prod.ext h rfl
    · refine mem_insert_of_mem (mem_singleton.2 ?_)
      exact Prod.ext h rfl
  calc ∑ p ∈ (detB S.toDomSeq ×ˢ (univ : Finset (Fin 4))).filter (fun p => g p = q), G (g p)
      = ((detB S.toDomSeq ×ˢ (univ : Finset (Fin 4))).filter fun p => g p = q).card * G q := by
        rw [sum_congr rfl fun p hp => by rw [(mem_filter.1 hp).2], sum_const, nsmul_eq_mul]
    _ ≤ 2 * G q := mul_le_mul_of_nonneg_right (by exact_mod_cast hfib) (hG q)

/-- **`lem:sf-components`** (fine lattice, `a₀ = 1`, in the norm of `V`): for every `1`-form `A` with values in
`M_N(ℂ)`, `‖∇A‖² + ‖A‖_w² ≤ 2^{12}(‖∇A‖² + Σ_ca_c²|(QA)(c)|²)`, `Q` the averages of the trivial configuration. -/
theorem sf_components (hRM : 2 * S.L ≤ S.R * S.L ^ S.mM) (A : Fin 4 → Site NF → Mat) :
    gradNorm S A + wnorm S A ≤ 2 ^ 12 * (gradNorm S A + Qnorm S A) := by
  -- the weighted norm block by block
  have hw : wnorm S A = ∑ y ∈ detB S.toDomSeq, ∑ μ, (((S.L ^ jj y : ℕ) : ℝ) ^ 2)⁻¹ *
      ∑ x ∈ Blk S.toDomSeq (jj y) y, ‖emb (N := N) (A μ x)‖ ^ 2 := by
    unfold wnorm
    rw [sum_blocks S.toDomSeq]
    refine sum_congr rfl fun y hy => ?_
    have hc : ∀ x ∈ Blk S.toDomSeq (jj y) y, (((S.L ^ jj x : ℕ) : ℝ) ^ 2)⁻¹ * ∑ μ, ‖emb (N := N) (A μ x)‖ ^ 2 =
        (((S.L ^ jj y : ℕ) : ℝ) ^ 2)⁻¹ * ∑ μ, ‖emb (N := N) (A μ x)‖ ^ 2 := fun x hx => by
      rw [(sc_mem_blk S.toDomSeq hy hx).1]
    rw [Finset.sum_congr rfl hc, ← mul_sum, Finset.sum_comm, mul_sum]
  have hb : wnorm S A ≤ ∑ y ∈ detB S.toDomSeq, ∑ μ,
      (64 * bondsAll (2 * S.L ^ jj y) (S.L ^ jj y) (S.L ^ jj y) (S.L ^ jj y) (Fbox S A (jj y) (cy S y μ) μ) +
        2 * ((S.L ^ jj y : ℕ) : ℝ) ^ 2 * ‖emb (N := N) (Qt S A (jj y) (cy S y μ) μ)‖ ^ 2) := by
    rw [hw]
    exact sum_le_sum fun y hy => sum_le_sum fun μ _ => block_bound S hy A μ
  have h1 : ∑ y ∈ detB S.toDomSeq, ∑ μ,
      bondsAll (2 * S.L ^ jj y) (S.L ^ jj y) (S.L ^ jj y) (S.L ^ jj y) (Fbox S A (jj y) (cy S y μ) μ) ≤
      48 * gradNorm S A := by
    refine le_trans ?_ (boxes_sum_le S hRM A)
    refine sum_le_sum fun y hy => sum_le_sum fun μ _ => ?_
    obtain ⟨-, hlc, -⟩ := cy_facts S hy μ
    exact bonds_le S (detB_facts S hy).2.1 hlc A μ
  have h2 := q_sum_le S A
  have hsplit : ∑ y ∈ detB S.toDomSeq, ∑ μ,
      (64 * bondsAll (2 * S.L ^ jj y) (S.L ^ jj y) (S.L ^ jj y) (S.L ^ jj y) (Fbox S A (jj y) (cy S y μ) μ) +
        2 * ((S.L ^ jj y : ℕ) : ℝ) ^ 2 * ‖emb (N := N) (Qt S A (jj y) (cy S y μ) μ)‖ ^ 2) =
      64 * ∑ y ∈ detB S.toDomSeq, ∑ μ,
        bondsAll (2 * S.L ^ jj y) (S.L ^ jj y) (S.L ^ jj y) (S.L ^ jj y) (Fbox S A (jj y) (cy S y μ) μ) +
      ∑ y ∈ detB S.toDomSeq, ∑ μ, 2 * ((S.L ^ jj y : ℕ) : ℝ) ^ 2 *
        ‖emb (N := N) (Qt S A (jj y) (cy S y μ) μ)‖ ^ 2 := by
    simp only [sum_add_distrib, mul_sum]
  rw [hsplit] at hb
  have hgn : 0 ≤ gradNorm S A := sum_nonneg fun _ _ => sum_nonneg fun _ _ => sum_nonneg fun _ _ => sq_nonneg _
  have hqn : 0 ≤ Qnorm S A := sum_nonneg fun _ _ => by positivity
  have h2' : ∑ y ∈ detB S.toDomSeq, ∑ μ, 2 * ((S.L ^ jj y : ℕ) : ℝ) ^ 2 *
      ‖emb (N := N) (Qt S A (jj y) (cy S y μ) μ)‖ ^ 2 ≤ 4 * Qnorm S A := by
    have : ∑ y ∈ detB S.toDomSeq, ∑ μ, 2 * ((S.L ^ jj y : ℕ) : ℝ) ^ 2 *
        ‖emb (N := N) (Qt S A (jj y) (cy S y μ) μ)‖ ^ 2 = 2 * ∑ y ∈ detB S.toDomSeq, ∑ μ,
          ((S.L ^ jj y : ℕ) : ℝ) ^ 2 * ‖emb (N := N) (Qt S A (jj y) (cy S y μ) μ)‖ ^ 2 := by
      simp only [mul_sum]; refine sum_congr rfl fun y _ => sum_congr rfl fun μ _ => by ring
    linarith
  linarith

end SFBounds
end CoreLean

end
