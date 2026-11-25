/-
`lem:sf-vector-decay` of BALABAN_CORE.tex, step (4) of "The complex field", in the fine model: the comparison of the
constraint forms at `𝐔 = e^{iX}` and at `id` (the input `hQ` of `SFVectorConj.decay_U`).

* `Bq`: the bonds with both ends in the box `X_c = B^j(c₋) ∪ B^j(c₊)` of a bond `c = (j, y, μ)` of the layers;
  `card_QB_bond`: a fine bond lies in at most `24` of them, all of the scale at least `j(x) - 1`
  (`lem:layer-bonds`(iii)); `card_Bq`: `|Bq| ≤ 8a_j⁴`.
* `region_Xc`, `ell1_le_Bq`: the region of the level `0` of the per-level framework is the box `X_c`, and its
  `ℓ¹`-sum is at most the sum over `Bq`.
* `Xc_dF`: the distance `d_F` on the box is at most `16L`.
* `Qat_one_le`, `Qat_diff_le`: `Q(id)` and `Q(e^{iX}) - Q(id)` at a bond of the layers against the box
  (`average_kernels_i`, `qseq_level_diff`); `sum_QB_Bq`, `inner_diff_le`, `expA_box`.
* `QBU_conj`, `hQ_of_QBU`: the comparison for the sesquilinear form `Σ_ca_c²⟨Q(𝐔)B(c), Q(𝐔)C(c)⟩`;
  `QBUc_conj`: the same for the bilinear form `Σ_ca_c²tr(Q(𝐔)(B^*)(c)Q(𝐔)(C)(c))`.
* Bridge (B5): `crd_ef`, `toLB`, `sum_LBond`, `Qseq_toLB` (the dictionary `LBond`/`QB`, `crd`/`baseOf`),
  `pair1V_constraintOp`, `pair1V_constraintOp_QBUc` (`⟨B^*, Q^*𝖺Q C⟩ = 𝖺a₀^{-2}QBUc(B, C)`), and
  **`constraintOp_hQ`**: the inputs `hQ`, `hQ0` of `decay_U` for `Q_𝖺 = a₀²𝖺^{-1}·constraintOp(e^{iX}, 𝖺)`.
-/
import CoreLean.SFConstraintComp

open Finset
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean
namespace SFBounds

open Lattices SeqDom Blocks SmallFieldBlocks SFBox SFBox.SeqDomBox SmallFieldDecay SmallFieldCoercivity
  SequenceOperators PartitionUnity RegularAverages AxialStraightLattice BoxGeometry

variable (S : SeqDom) {N : ℕ}

local notation "NF" => SequenceAverages.N0 S
local notation "RMS" => ((S.R * S.L ^ S.mM : ℕ) : ℝ)
set_option quotPrecheck false in
local notation "jj" => (S.toDomSeq).sc

open Classical in
/-- The bonds `(z, ν)` of the fine lattice with both ends in the box `X_c` of the bond `c = (j, y, μ)`. -/
def Bq (j : ℕ) (y : Site NF) (μ : Fin 4) : Finset (Site NF × Fin 4) :=
  (univ ×ˢ univ).filter fun b => b.1 ∈ Xc S j y μ ∧ b.1 + CoreLean.unit NF b.2 ∈ Xc S j y μ

open Classical in
/-- **The boxes of the layers through a fine bond**: at most `24` bonds `c ∈ QB` have the bond `(z, ν)` in their
box, and each has the scale at least `j(z) - 1` (`lem:layer-bonds`(iii)). -/
lemma card_QB_bond (hRM : 2 * S.L ≤ S.R * S.L ^ S.mM) (b : Site NF × Fin 4) :
    ((QB S).filter fun q => b ∈ Bq S q.1 q.2.1 q.2.2).card ≤ 24 ∧
      ∀ q ∈ QB S, b ∈ Bq S q.1 q.2.1 q.2.2 → jj b.1 ≤ q.1 + 1 := by
  obtain ⟨x, ν⟩ := b
  have hx1 : S.ef x ∈ S.Ω (jj x) := S.ef_mem_sc x
  have hx2 : S.ef x ∉ S.Ω (jj x + 1) := fun h => by
    have := ((S.toDomSeq).mem_iff x (jj x + 1)).1 (S.mem_toDomSeq_Ω.2 h); omega
  have hBc : ∀ q ∈ QB S, (x, ν) ∈ Bq S q.1 q.2.1 q.2.2 →
      S.IsLayerBond q.1 (S.ef q.2.1) q.2.2 ∧ (S.ef x, ν) ∈ S.Bc q.1 (S.ef q.2.1) q.2.2 := by
    intro q hq hb
    have hq' := hq
    simp only [QB, mem_filter, mem_product, mem_range, mem_univ, true_and] at hq'
    obtain ⟨hjk, hlat, hlb⟩ := hq'
    simp only [Bq, mem_filter, mem_product, mem_univ, true_and] at hb
    refine ⟨hlb, ?_, ?_⟩
    · exact (mem_Xc_iff S (by omega) hlat q.2.2 x).1 hb.1
    · show S.bend 0 (S.ef x) ν ∈ _
      rw [← ef_add_unit]; exact (mem_Xc_iff S (by omega) hlat q.2.2 _).1 hb.2
  refine ⟨?_, fun q hq hb => ?_⟩
  · obtain ⟨F, hF, hmem⟩ := S.layer_bonds_iii hRM ((S.toDomSeq).sc_le x) (b := (S.ef x, ν)) (S.ef_mem_TL0 x)
      hx1 hx2
    set f : ℕ × Site NF × Fin 4 → ℕ × Tor (ellT S.L S.mT) × Fin 4 := fun q => (q.1, S.ef q.2.1, q.2.2)
    have hinj : Set.InjOn f ((QB S).filter fun q => (x, ν) ∈ Bq S q.1 q.2.1 q.2.2) := by
      intro q _ q' _ hqq
      simp only [f, Prod.mk.injEq] at hqq
      obtain ⟨h1, h2, h3⟩ := hqq
      have := emb_injective S.Lpos (SequenceAverages.N0_eq S) h2
      exact Prod.ext h1 (Prod.ext this h3)
    rw [← card_image_of_injOn hinj]
    refine (card_le_card fun p hp => ?_).trans hF
    obtain ⟨q, hq, rfl⟩ := mem_image.1 hp
    obtain ⟨hqQ, hb⟩ := mem_filter.1 hq
    obtain ⟨hlb, hbc⟩ := hBc q hqQ hb
    exact hmem _ _ _ hlb hbc
  · obtain ⟨hlb, hbc⟩ := hBc q hq hb
    have hq' := hq
    simp only [QB, mem_filter, mem_product, mem_range, mem_univ, true_and] at hq'
    have h := S.layer_bonds_iii_index hRM ((S.toDomSeq).sc_le x) hx1 hx2 hlb hbc
    show jj x ≤ q.1 + 1
    omega

open Classical in
lemma card_Xc {j : ℕ} (hj : j ≤ S.k) {y : Site NF} (hy : InLat S.L j y) (μ : Fin 4) :
    (Xc S j y μ).card ≤ 2 * (S.L ^ j) ^ 4 := by
  unfold Xc
  refine (card_union_le _ _).trans ?_
  rw [card_Blk_j S hj hy, card_Blk_j S hj (inLat_ynext S hy μ)]
  omega

open Classical in
/-- `|Bq| ≤ 8a_j⁴`. -/
lemma card_Bq {j : ℕ} (hj : j ≤ S.k) {y : Site NF} (hy : InLat S.L j y) (μ : Fin 4) :
    (Bq S j y μ).card ≤ 8 * (S.L ^ j) ^ 4 := by
  have h1 : Bq S j y μ ⊆ Xc S j y μ ×ˢ univ := fun b hb => by
    simp only [Bq, mem_filter, mem_product, mem_univ, true_and] at hb
    exact mem_product.2 ⟨hb.1, mem_univ _⟩
  refine (card_le_card h1).trans ?_
  rw [card_product, card_univ, Fintype.card_fin]
  have := card_Xc S hj hy μ
  omega

/-- A site within `h_j = (a_j - 1)/2` of a site `c` of `a_jℤ⁴` in every direction lies in the block of `c`. -/
lemma add_mem_Blk {j : ℕ} (hj : j ≤ S.k) {c : Site NF} (hc : InLat S.L j c) (v : Fin 4 → ℤ)
    (hv : ∀ σ, -(half S.L j : ℤ) ≤ v σ ∧ v σ ≤ half S.L j) :
    (c + fun σ => ((v σ : ℤ) : ZMod NF)) ∈ Blk S.toDomSeq j c := by
  have hH : (2 * half S.L j + 1 : ℤ) = (S.L : ℤ) ^ j := by exact_mod_cast two_half_add_one S.L_odd j
  set o : Fin 4 → ℕ := fun σ => (v σ + half S.L j).toNat
  have ho : o ∈ DiscretePoincare.box 4 (S.L ^ j) := by
    simp only [DiscretePoincare.box, Fintype.mem_piFinset, mem_range, o]
    intro σ
    have h := hv σ
    have hLp : (0 : ℤ) < (S.L : ℤ) ^ j := pow_pos (by exact_mod_cast S.Lpos) _
    have : (v σ + half S.L j).toNat < ((S.L : ℤ) ^ j).toNat := by
      rw [Int.toNat_lt_toNat hLp]; linarith
    rwa [show ((S.L : ℤ) ^ j) = ((S.L ^ j : ℕ) : ℤ) by push_cast; rfl, Int.toNat_natCast] at this
  have hmem := phi_mem (S := S.toDomSeq) j hj hc ho
  have e : (c + fun σ => ((v σ : ℤ) : ZMod NF)) = SmallFieldBlocks.phi S.toDomSeq j c o := by
    funext σ
    have h := hv σ
    simp only [SmallFieldBlocks.phi, o, Pi.add_apply]
    rw [Int.toNat_of_nonneg (by linarith)]
    congr 1
    push_cast
    have : half S.toDomSeq.L j = half S.L j := rfl
    rw [this]; ring_nf
  rw [e]; exact hmem

/-- **The region of the level `0` is the box `X_c`**: for `(j, y, μ) ∈ QB` and `x` in the region of the level `0`
of `j` levels, `y + x ∈ X_c = B^j(y) ∪ B^j(y + a_je_μ)`. -/
lemma region_Xc {j : ℕ} {y : Site NF} {μ : Fin 4} (hq : (j, y, μ) ∈ QB S) (x : Fin 4 → ℤ)
    (hx : RelativeAverage.Rg (SequenceAverages.hS S) j μ 0 x) :
    (y + fun σ => ((x σ : ℤ) : ZMod NF)) ∈ Xc S j y μ := by
  have hq' := hq
  simp only [QB, mem_filter, mem_product, mem_range, mem_univ, true_and] at hq'
  obtain ⟨hjk, hlat, -⟩ := hq'
  set H : ℤ := ((half S.L j : ℕ) : ℤ)
  have hHz : (2 * H + 1 : ℤ) = (S.L : ℤ) ^ j := by simp only [H]; exact_mod_cast two_half_add_one S.L_odd j
  have hb : ∀ σ, -H ≤ x σ ∧ x σ ≤ (if σ = μ then (S.L : ℤ) ^ j else 0) + H := by
    intro σ
    have h := hx σ
    rw [Hw_zero, Lz_hS] at h
    simp only [or_self] at h
    exact h
  unfold Xc
  rw [mem_union]
  by_cases hxm : x μ ≤ H
  · left
    refine add_mem_Blk S (by omega) hlat x fun σ => ?_
    have h := hb σ
    by_cases hσ : σ = μ
    · subst hσ; simp only [if_true] at h; exact ⟨h.1, hxm⟩
    · simp only [hσ, if_false, zero_add] at h; exact h
  · right
    set v : Fin 4 → ℤ := x - (S.L : ℤ) ^ j • Pi.single μ 1
    have hv := add_mem_Blk S (by omega) (inLat_ynext S hlat μ) v fun σ => by
      have h := hb σ
      by_cases hσ : σ = μ
      · subst hσ
        simp only [if_true] at h
        simp only [v, Pi.sub_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
        constructor <;> linarith
      · simp only [hσ, if_false, zero_add] at h
        simp only [v, Pi.sub_apply, Pi.smul_apply, Pi.single_eq_of_ne hσ, smul_eq_mul, mul_zero, sub_zero]
        exact h
    have e : (ynext S j y μ + fun σ => ((v σ : ℤ) : ZMod NF)) = y + fun σ => ((x σ : ℤ) : ZMod NF) := by
      funext σ
      simp only [ynext, v, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, CoreLean.unit, smul_eq_mul]
      by_cases hσ : σ = μ
      · subst hσ; simp only [Pi.single_eq_same, mul_one]; push_cast; ring
      · simp only [Pi.single_eq_of_ne hσ, mul_zero, sub_zero, add_zero]
    rwa [e] at hv

/-- The sites of the box `[-h_j, a_j + h_j]⁴` are distinct on the torus. -/
lemma boxPts_inj {j : ℕ} (hj : j ≤ S.k) (y : Site NF) :
    Set.InjOn (fun x : Fin 4 → ℤ => y + fun σ => ((x σ : ℤ) : ZMod NF))
      (RelativeAverage.boxPts (SequenceAverages.hS S) j 0) := by
  intro x hx x' hx' he
  have hN := two_n_le S hj
  simp only [RelativeAverage.boxPts, Finset.mem_coe, Fintype.mem_piFinset, mem_Icc] at hx hx'
  rw [Hw_zero, Lz_hS] at hx hx'
  have hH : (2 * (half S.L j : ℤ) + 1 : ℤ) = (S.L : ℤ) ^ j := by exact_mod_cast two_half_add_one S.L_odd j
  funext σ
  have h1 := congrFun he σ
  simp only [Pi.add_apply, add_right_inj] at h1
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h1
  obtain ⟨m, hm⟩ := h1
  have a := hx σ
  have b := hx' σ
  have hNz : (2 * (S.L : ℤ) ^ j) ≤ (NF : ℤ) := by exact_mod_cast hN
  have hm0 : m = 0 := by
    by_contra hm0
    rcases lt_or_gt_of_ne hm0 with h | h
    · have : (NF : ℤ) * m ≤ -(NF : ℤ) := by nlinarith
      linarith
    · have : (NF : ℤ) * m ≥ (NF : ℤ) := by nlinarith
      linarith
  rw [hm0, mul_zero] at hm
  linarith

open Classical in
/-- **The `ℓ¹`-sum over the region of the level `0` is at most the sum over the bonds of the box `X_c`.** -/
lemma ell1_le_Bq {j : ℕ} {y : Site NF} {μ : Fin 4} (hq : (j, y, μ) ∈ QB S) (g : Fin 4 → Site NF → ℝ)
    (hg : ∀ ν z, 0 ≤ g ν z) :
    RelativeAverage.ell1 (SequenceAverages.hS S) j μ 0 (fun x ν => g ν (y + fun σ => ((x σ : ℤ) : ZMod NF))) ≤
      ∑ b ∈ Bq S j y μ, g b.2 b.1 := by
  have hq' := hq
  simp only [QB, mem_filter, mem_product, mem_range, mem_univ, true_and] at hq'
  obtain ⟨hjk, hlat, -⟩ := hq'
  set P := RelativeAverage.boxPts (SequenceAverages.hS S) j 0
  set e : (Fin 4 → ℤ) × Fin 4 → Site NF × Fin 4 := fun p => (y + fun σ => ((p.1 σ : ℤ) : ZMod NF), p.2)
  set F := (P ×ˢ (univ : Finset (Fin 4))).filter fun p => RelativeAverage.RB (SequenceAverages.hS S) j μ 0 p.1 p.2
  have h1 : RelativeAverage.ell1 (SequenceAverages.hS S) j μ 0
      (fun x ν => g ν (y + fun σ => ((x σ : ℤ) : ZMod NF))) = ∑ p ∈ F, g (e p).2 (e p).1 := by
    unfold RelativeAverage.ell1
    rw [sum_filter, sum_product]
  have hinj : Set.InjOn e F := by
    intro p hp p' hp' hpp
    simp only [e, Prod.mk.injEq] at hpp
    have hp1 := (mem_product.1 (mem_filter.1 hp).1).1
    have hp1' := (mem_product.1 (mem_filter.1 hp').1).1
    exact Prod.ext (boxPts_inj S (by omega) y hp1 hp1' hpp.1) hpp.2
  rw [h1, ← sum_image (f := fun b : Site NF × Fin 4 => g b.2 b.1) hinj]
  refine sum_le_sum_of_subset_of_nonneg (fun b hb => ?_) fun b _ _ => hg _ _
  obtain ⟨p, hp, rfl⟩ := mem_image.1 hb
  obtain ⟨-, hRB⟩ := mem_filter.1 hp
  obtain ⟨-, hR1, hR2⟩ := hRB
  simp only [Bq, mem_filter, mem_product, mem_univ, true_and, e]
  refine ⟨region_Xc S hq _ hR1, ?_⟩
  have := region_Xc S hq _ hR2
  convert this using 1
  funext σ
  simp only [Pi.add_apply, pow_zero, one_smul, CoreLean.unit]
  by_cases hσ : σ = p.2
  · subst hσ; simp; ring
  · simp [Pi.single_eq_of_ne hσ]

lemma cd_add_int_le (a : ZMod NF) (t : ℤ) : cd (a + ((t : ℤ) : ZMod NF)) ≤ cd a + t.natAbs :=
  (cd_add_le _ _).trans (Nat.add_le_add_left (cd_intCast_le t) _)

/-- The sites of the box `X_c` are within `2a_j` of both ends of `c`. -/
lemma dinf_Xc {j : ℕ} {y z : Site NF} {μ : Fin 4} (hz : z ∈ Xc S j y μ) :
    dinf z y ≤ 2 * S.L ^ j ∧ dinf z (ynext S j y μ) ≤ 2 * S.L ^ j := by
  have hh := half_le_pow S j
  have key : ∀ (c : Site NF) (s : ℤ), z ∈ Blk S.toDomSeq j c → s.natAbs ≤ S.L ^ j →
      dinf z (c + fun ν => (((if ν = μ then s else 0) : ℤ) : ZMod NF)) ≤ 2 * S.L ^ j := by
    intro c s hzc hs
    unfold dinf
    refine Finset.sup_le fun ν _ => ?_
    have hc := SmallFieldBlocks.cd_le_of_mem (S := S.toDomSeq) hzc ν
    change cd (z ν - c ν) ≤ half S.L j at hc
    have e : z ν - (c + fun ν => (((if ν = μ then s else 0) : ℤ) : ZMod NF)) ν =
        (z ν - c ν) + ((-(if ν = μ then s else 0) : ℤ) : ZMod NF) := by
      simp only [Pi.add_apply]; push_cast; ring
    rw [e]
    refine (cd_add_int_le S _ _).trans ?_
    have : (-(if ν = μ then s else 0) : ℤ).natAbs ≤ S.L ^ j := by
      split_ifs <;> simp [hs]
    omega
  have hyn : ynext S j y μ = y + fun ν => ((((if ν = μ then ((S.L ^ j : ℕ) : ℤ) else 0) : ℤ)) : ZMod NF) := by
    funext ν
    simp only [ynext, Pi.add_apply, Pi.smul_apply, CoreLean.unit, smul_eq_mul]
    by_cases h : ν = μ
    · subst h; simp
    · simp [h, Pi.single_eq_of_ne h]
  have hy0 : ∀ c : Site NF, c = c + fun ν => ((((if ν = μ then (0 : ℤ) else 0) : ℤ)) : ZMod NF) := fun c => by
    funext ν; simp
  have hyb : y = ynext S j y μ + fun ν => ((((if ν = μ then -((S.L ^ j : ℕ) : ℤ) else 0) : ℤ)) : ZMod NF) := by
    rw [hyn]; funext ν
    simp only [Pi.add_apply]
    split_ifs <;> push_cast <;> ring
  unfold Xc at hz
  rcases mem_union.1 hz with hz | hz
  · constructor
    · rw [hy0 y]; exact key y 0 hz (by simp)
    · rw [hyn]; exact key y _ hz (by simp)
  · constructor
    · rw [hyb]; exact key _ _ hz (by simp)
    · rw [hy0 (ynext S j y μ)]; exact key _ 0 hz (by simp)

/-- **The distance `d_F` on the box of a bond of a layer** is at most `16L`. -/
lemma Xc_dF (hRM : 18 * (S.L : ℝ) ≤ RMS) (hR1 : 1 ≤ S.R * S.L ^ S.mM) {j : ℕ} {y : Site NF} {μ : Fin 4}
    (hq : (j, y, μ) ∈ QB S) {z z' : Site NF} (hz : z ∈ Xc S j y μ) (hz' : z' ∈ Xc S j y μ) :
    S.dF z z' ≤ 16 * S.L := by
  have hq' := (PartitionUnity.mem_QB_iff (T := S) _).1 hq
  have hjk : j ≤ S.k := by have := hq'.1; omega
  have hL0 : (0 : ℝ) < S.L := by exact_mod_cast S.Lpos
  rcases Nat.eq_zero_or_pos j with hj0 | hj1
  · subst hj0
    have hB : ∀ c w : Site NF, w ∈ Blk S.toDomSeq 0 c → w = c := fun c w hw => by
      funext ν
      have h := SmallFieldBlocks.cd_le_of_mem (S := S.toDomSeq) hw ν
      have h0 : half S.toDomSeq.L 0 = 0 := by simp [half]
      rw [h0] at h
      have : (w ν - c ν).valMinAbs = 0 := by unfold cd at h; omega
      rw [ZMod.valMinAbs_eq_zero] at this
      exact sub_eq_zero.1 this
    have hyn : ynext S 0 y μ = y + CoreLean.unit NF μ := by simp [ynext]
    have hcase : ∀ w ∈ Xc S 0 y μ, w = y ∨ w = y + CoreLean.unit NF μ := fun w hw => by
      unfold Xc at hw
      rcases mem_union.1 hw with h | h
      · exact Or.inl (hB _ _ h)
      · exact Or.inr ((hB _ _ h).trans hyn)
    have hu := (dF_unit_le S hR1 y μ).1
    have hu' : S.dF (y + CoreLean.unit NF μ) y ≤ S.L := by rw [dF_comm]; exact hu
    rcases hcase z hz with rfl | rfl <;> rcases hcase z' hz' with rfl | rfl <;>
      first | (rw [dF_self]; positivity) | linarith
  · obtain ⟨-, hend, -, -⟩ := hq'.2.2
    have hnext : S.bend j (S.ef y) μ = S.ef (ynext S j y μ) := by rw [ef_ynext]; rfl
    have hc : ∀ w ∈ Xc S j y μ, ∀ e ∈ ({y, ynext S j y μ} : Finset (Site NF)),
        (dinf w e : ℝ) ≤ 2 * (S.L : ℝ) ^ j := by
      intro w hw e he
      have h := dinf_Xc S hw
      rcases mem_insert.1 he with rfl | he
      · have := Nat.cast_le (α := ℝ) |>.2 h.1; push_cast at this; exact this
      · rw [mem_singleton.1 he]
        have := Nat.cast_le (α := ℝ) |>.2 h.2; push_cast at this; exact this
    have h16 : (8 : ℝ) * 2 * S.L = 16 * S.L := by ring
    rcases hend with he | he
    · rw [← h16]
      exact dF_near_le S hj1 hjk (e := y) he (by norm_num) (hc z hz y (by simp)) (hc z' hz' y (by simp))
        (by linarith)
    · rw [hnext] at he
      rw [← h16]
      exact dF_near_le S hj1 hjk (e := ynext S j y μ) he (by norm_num) (hc z hz _ (by simp))
        (hc z' hz' _ (by simp)) (by linarith)

/-- `Σ_{l < j}L^{-(j-l)} ≤ 1/2` for `L ≥ 3`. -/
lemma geom_inv_le {L : ℝ} (hL : 3 ≤ L) : ∀ j : ℕ, ∑ l ∈ Finset.range j, (L ^ (j - l))⁻¹ ≤ 1 / 2
  | 0 => by simp
  | j + 1 => by
    have ih := geom_inv_le hL j
    have hL0 : 0 < L := by linarith
    have e : ∑ l ∈ Finset.range (j + 1), (L ^ (j + 1 - l))⁻¹ = L⁻¹ * (∑ l ∈ Finset.range j, (L ^ (j - l))⁻¹ + 1) := by
      rw [Finset.sum_range_succ, mul_add, Finset.mul_sum, mul_one]
      congr 1
      · refine Finset.sum_congr rfl fun l hl => ?_
        have hl' : l < j := Finset.mem_range.1 hl
        rw [show j + 1 - l = (j - l) + 1 by omega, pow_succ, mul_inv, mul_comm]
      · rw [show j + 1 - j = 1 by omega, pow_one]
    rw [e]
    have h1 : L⁻¹ ≤ 1 / 3 := by rw [inv_le_comm₀ hL0 (by norm_num)]; linarith
    have h2 : 0 ≤ ∑ l ∈ Finset.range j, (L ^ (j - l))⁻¹ := Finset.sum_nonneg fun _ _ => by positivity
    calc L⁻¹ * (∑ l ∈ Finset.range j, (L ^ (j - l))⁻¹ + 1) ≤ 1 / 3 * (1 / 2 + 1) :=
          mul_le_mul h1 (by linarith) (by linarith) (by norm_num)
      _ = 1 / 2 := by norm_num

open Classical in
/-- **The composite average at a bond of the layers**: `Q_j(U)B` evaluated at the coarse point `y/a_j` of a
bond `(j, y, μ)` (zero off `a_jℤ⁴`). -/
def Qat (U : Config N NF) (B : Fin 4 → Site NF → Matrix (Fin N) (Fin N) ℂ) (q : ℕ × Site NF × Fin 4) :
    Matrix (Fin N) (Fin N) ℂ :=
  if h : InLat S.L q.1 q.2.1 then
    MultiscaleAverages.Qcomp (SequenceAverages.hS S) S.mT S.k (fun _ => True)
      (fun W => LogM (W : Matrix (Fin N) (Fin N) ℂ)) U q.1 B q.2.2
      (LevelsBridge.baseOf (SequenceAverages.hS S) S.mT S.k (c0Of S h) q.1 q.1)
  else 0

lemma Qat_eq (U : Config N NF) (B : Fin 4 → Site NF → Matrix (Fin N) (Fin N) ℂ) {j : ℕ} {y : Site NF} {μ : Fin 4}
    (hlat : InLat S.L j y) :
    Qat S U B (j, y, μ) = MultiscaleAverages.Qcomp (SequenceAverages.hS S) S.mT S.k (fun _ => True)
      (fun W => LogM (W : Matrix (Fin N) (Fin N) ℂ)) U j B μ
      (LevelsBridge.baseOf (SequenceAverages.hS S) S.mT S.k (c0Of S hlat) j j) := by
  simp only [Qat, dif_pos hlat]

/-- `Q(id) = Qt` at the bonds of the layers (`qcomp_one_Qt`). -/
lemma Qat_one (B : Fin 4 → Site NF → Matrix (Fin N) (Fin N) ℂ) {q : ℕ × Site NF × Fin 4} (hq : q ∈ QB S) :
    Qat S RelativeAverage.oneC B q = Qt S B q.1 q.2.1 q.2.2 := by
  obtain ⟨j, y, μ⟩ := q
  have hq' := hq
  simp only [QB, mem_filter, mem_product, mem_range, mem_univ, true_and] at hq'
  obtain ⟨hjk, hlat, -⟩ := hq'
  rw [Qat_eq S _ B hlat]
  exact qcomp_one_Qt S (by omega) hlat μ B

/-- **`Q(id)` at a bond of the layers against the box**: `‖Q(id)B(c)‖ ≤ 2a_j^{-4}Σ_{b ∈ Bq}‖B(b)‖`
(`average_kernels_i` at the trivial configuration of the levels). -/
theorem Qat_one_le (B : Fin 4 → Site NF → Matrix (Fin N) (Fin N) ℂ) {j : ℕ} {y : Site NF} {μ : Fin 4}
    (hq : (j, y, μ) ∈ QB S)
    (hn : ∀ l, 4 * SequenceAverages.hS S + 4 ≤ MultiscaleAverages.nn (SequenceAverages.hS S) S.mT S.k l) :
    ‖Qat S RelativeAverage.oneC B (j, y, μ)‖ ≤
      2 * (((S.L : ℝ) ^ j) ^ 4)⁻¹ * ∑ b ∈ Bq S j y μ, ‖B b.2 b.1‖ := by
  have hq' := hq
  simp only [QB, mem_filter, mem_product, mem_range, mem_univ, true_and] at hq'
  obtain ⟨hjk, hlat, -⟩ := hq'
  set h := SequenceAverages.hS S
  have hh := one_le_hS S S.three_le_L
  obtain ⟨c, C, hc, hC, hk⟩ := RelativeAverage.average_kernels_i (N := N) h hh
  set base := LevelsBridge.baseOf h S.mT S.k (c0Of S hlat) j
  set Lc : ℂ := ((2 * h + 1 : ℕ) : ℂ)
  set Lr : ℝ := ((2 * h + 1 : ℕ) : ℝ)
  have hLr : Lr = S.L := Lr_hS S
  set D : ∀ l, Fin 4 → Site (MultiscaleAverages.nn h S.mT S.k l) → Matrix (Fin N) (Fin N) ℂ := fun l =>
    Lc ^ l • MultiscaleAverages.Qcomp h S.mT S.k (fun _ => True) (fun W => LogM (W : Matrix (Fin N) (Fin N) ℂ))
      RelativeAverage.oneC l B
  have hrec : ∀ l, l < j → ∀ ρ x, Lat (Lz h) (l + 1) x → RelativeAverage.Rg h j μ (l + 1) x →
      RelativeAverage.Rg h j μ (l + 1) (x + Lz h ^ (l + 1) • Pi.single ρ 1) →
      D (l + 1) ρ (img h (base (l + 1)) (l + 1) x) =
        Lc • RelativeAverage.Qlin (RelativeAverage.oneC (N := N)) (img h (base l) l x) ρ h (D l) := by
    intro l hl ρ x hx _ _
    have hup := LevelsBridge.up_img h S.mT S.k base l (by omega)
      (LevelsBridge.base_up h S.mT S.k (c0Of S hlat) j l hl (by omega)) x hx
    simp only [D, Pi.smul_apply, LevelsBridge.qcomp_succ_apply, LevelsBridge.mpow_oneC, hup, map_smul, smul_smul,
      pow_succ]
    ring_nf
  have hmove : ∀ l (ν : Fin 4) (z : Site (MultiscaleAverages.nn h S.mT S.k l)),
      (RelativeAverage.oneC : Config N _) ν z = AverageHolo.moveC RelativeAverage.oneC 0 ν z := fun l ν z => by
    simp [AverageHolo.moveC, RelativeAverage.oneC]
  have H := hk j μ (MultiscaleAverages.nn h S.mT S.k) hn base (fun _ => RelativeAverage.oneC)
    (fun _ => RelativeAverage.oneC) (fun _ => 0) D (fun _ => 0) (fun _ => 0) 0
    (fun _ => LevelsBridge.oneC_gauge)
    (fun l _ ν x _ _ _ => hmove l ν _)
    (fun l _ ρ x _ _ _ => ⟨fun μ' ν' z _ => by simp [LevelsBridge.plaq_oneC, hs, hs2, ntr], fun ν z _ => by simp⟩)
    (fun l _ => ⟨le_rfl, le_rfl, by simp⟩) le_rfl hc.le (by simp) hrec
  have hD0 : ∀ x ν, D 0 ν (img h (base 0) 0 x) = B ν (y + fun σ => ((x σ : ℤ) : ZMod NF)) := fun x ν => by
    simp only [D, pow_zero, one_smul, MultiscaleAverages.Qcomp_zero, LinearMap.id_apply]
    rw [show base 0 = y from baseOf_zero S hlat, img_zero]
  simp only [hD0] at H
  have hle := RelativeAverage.le_ell1 (f := fun x ν => ‖D j ν (img h (base j) j x)‖) (fun _ _ => norm_nonneg _)
    (RB_top S j μ)
  rw [img_top] at hle
  have hDj : D j μ (base j) = Lc ^ j • Qat S RelativeAverage.oneC B (j, y, μ) := by
    rw [Qat_eq S _ B hlat]; rfl
  rw [hDj, norm_smul, norm_pow] at hle
  have hLc : ‖Lc‖ = S.L := by
    rw [← hLr]; simp only [Lc, Lr, Complex.norm_natCast]
  rw [hLc] at hle
  have hBq := ell1_le_Bq S hq (fun ν z => ‖B ν z‖) (fun _ _ => norm_nonneg _)
  have hL0 : (0 : ℝ) < (S.L : ℝ) ^ j := by have := S.Lpos; positivity
  have hq3 : ((Lr ^ 3)⁻¹) ^ j = (((S.L : ℝ) ^ j) ^ 3)⁻¹ := by rw [hLr, ← inv_pow, ← pow_mul, ← pow_mul, mul_comm, inv_pow]
  rw [hq3] at H
  have key : (S.L : ℝ) ^ j * ‖Qat S RelativeAverage.oneC B (j, y, μ)‖ ≤
      2 * (((S.L : ℝ) ^ j) ^ 3)⁻¹ * ∑ b ∈ Bq S j y μ, ‖B b.2 b.1‖ :=
    hle.trans (H.trans (mul_le_mul_of_nonneg_left hBq (by positivity)))
  rw [← le_div_iff₀' hL0] at key
  refine key.trans (le_of_eq ?_)
  field_simp

/-- **`Q(𝐔) - Q(id)` at a bond of the layers against the box**: for a regular field `X` with `α₁L, K_oα₁L ≤ c`,
`‖(Q(e^{iX}) - Q(id))B(c)‖ ≤ (e^{4L³CK_oα₁L} - 1)a_j^{-4}Σ_{b ∈ Bq}‖B(b)‖` (`qseq_level_diff` at the bond itself,
`Σ_{l<j}L^{-(j-l)} ≤ 1/2`, `ell1_le_Bq`). -/
theorem Qat_diff_le (G : GaugeGroup N) (hGc : IsClosed G.mats) (hN : 1 ≤ N) :
    ∃ c Ko C : ℝ, 0 < c ∧ 0 ≤ Ko ∧ 0 ≤ C ∧
      ∀ (hRM : 2 * (S.L : ℝ) ≤ RMS)
        (hn : ∀ l, 4 * SequenceAverages.hS S + 4 ≤ MultiscaleAverages.nn (SequenceAverages.hS S) S.mT S.k l)
        {j : ℕ} {y : Site NF} {μ : Fin 4} (hq : (j, y, μ) ∈ QB S)
        {X : Fin 4 → Site NF → Matrix (Fin N) (Fin N) ℂ} {α₁ : ℝ} (hX : RegField S X α₁) (hα0 : 0 ≤ α₁)
        (hαc : α₁ * S.L ≤ c) (hKαc : Ko * (α₁ * S.L) ≤ c) (B : Fin 4 → Site NF → Matrix (Fin N) (Fin N) ℂ),
      ‖Qat S (cfgX X) B (j, y, μ) - Qat S RelativeAverage.oneC B (j, y, μ)‖ ≤
        (Real.exp (4 * (S.L : ℝ) ^ 3 * C * (Ko * (α₁ * S.L))) - 1) * (((S.L : ℝ) ^ j) ^ 4)⁻¹ *
          ∑ b ∈ Bq S j y μ, ‖B b.2 b.1‖ := by
  obtain ⟨c, Ko, C, hc, hKo, hC, hd⟩ := qseq_level_diff S G hGc hN
  refine ⟨c, Ko, C, hc, hKo, hC, ?_⟩
  intro hRM hn j y μ hq X α₁ hX hα0 hαc hKαc B
  obtain ⟨hlat, H⟩ := hd hRM hn hq hX hα0 hαc hKαc B
  set h := SequenceAverages.hS S
  set Lc : ℂ := ((2 * h + 1 : ℕ) : ℂ)
  set Lr : ℝ := ((2 * h + 1 : ℕ) : ℝ)
  have hLr : Lr = S.L := Lr_hS S
  have hL3 : (3 : ℝ) ≤ S.L := by exact_mod_cast S.three_le_L
  have hL0 : (0 : ℝ) < (S.L : ℝ) ^ j := by positivity
  set base := LevelsBridge.baseOf h S.mT S.k (c0Of S hlat) j
  set F : Fin 4 → Site (MultiscaleAverages.nn h S.mT S.k j) → Matrix (Fin N) (Fin N) ℂ :=
    Lc ^ j • (MultiscaleAverages.Qcomp h S.mT S.k (fun _ => True) (fun W => LogM (W : Matrix (Fin N) (Fin N) ℂ))
      (cfgX X) j B - MultiscaleAverages.Qcomp h S.mT S.k (fun _ => True)
        (fun W => LogM (W : Matrix (Fin N) (Fin N) ℂ)) RelativeAverage.oneC j B)
  have hle := RelativeAverage.le_ell1 (f := fun x ν => ‖F ν (img h (base j) j x)‖) (fun _ _ => norm_nonneg _)
    (RB_top S j μ)
  rw [img_top] at hle
  have hFj : F μ (base j) = Lc ^ j • (Qat S (cfgX X) B (j, y, μ) - Qat S RelativeAverage.oneC B (j, y, μ)) := by
    rw [Qat_eq S _ B hlat, Qat_eq S _ B hlat]; rfl
  rw [hFj, norm_smul, norm_pow] at hle
  have hLc : ‖Lc‖ = S.L := by
    rw [← hLr]; simp only [Lc, Lr, Complex.norm_natCast]
  rw [hLc] at hle
  -- the exponent
  have hs : ∑ l ∈ Finset.range j, 8 * Lr ^ 3 * C * (Ko * (α₁ * S.L) * (Lr ^ (j - l))⁻¹) ≤
      4 * (S.L : ℝ) ^ 3 * C * (Ko * (α₁ * S.L)) := by
    have e : ∑ l ∈ Finset.range j, 8 * Lr ^ 3 * C * (Ko * (α₁ * S.L) * (Lr ^ (j - l))⁻¹) =
        8 * Lr ^ 3 * C * (Ko * (α₁ * S.L)) * ∑ l ∈ Finset.range j, (Lr ^ (j - l))⁻¹ := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
    rw [e, hLr]
    have hg := geom_inv_le hL3 j
    have h0 : 0 ≤ 8 * (S.L : ℝ) ^ 3 * C * (Ko * (α₁ * S.L)) := by positivity
    nlinarith
  have hexp : Real.exp (∑ l ∈ Finset.range j, 8 * Lr ^ 3 * C * (Ko * (α₁ * S.L) * (Lr ^ (j - l))⁻¹)) - 1 ≤
      Real.exp (4 * (S.L : ℝ) ^ 3 * C * (Ko * (α₁ * S.L))) - 1 := by
    have := Real.exp_le_exp.2 hs; linarith
  have hexp0 : 0 ≤ Real.exp (∑ l ∈ Finset.range j, 8 * Lr ^ 3 * C * (Ko * (α₁ * S.L) * (Lr ^ (j - l))⁻¹)) - 1 := by
    have : 0 ≤ ∑ l ∈ Finset.range j, 8 * Lr ^ 3 * C * (Ko * (α₁ * S.L) * (Lr ^ (j - l))⁻¹) :=
      Finset.sum_nonneg fun _ _ => by positivity
    have := Real.add_one_le_exp (∑ l ∈ Finset.range j, 8 * Lr ^ 3 * C * (Ko * (α₁ * S.L) * (Lr ^ (j - l))⁻¹))
    linarith
  have hBq := ell1_le_Bq S hq (fun ν z => ‖B ν z‖) (fun _ _ => norm_nonneg _)
  have hq3 : ((Lr ^ 3)⁻¹) ^ j = (((S.L : ℝ) ^ j) ^ 3)⁻¹ := by
    rw [hLr, ← inv_pow, ← pow_mul, ← pow_mul, mul_comm, inv_pow]
  rw [hq3] at H
  have hsum0 : 0 ≤ ∑ b ∈ Bq S j y μ, ‖B b.2 b.1‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have key : (S.L : ℝ) ^ j * ‖Qat S (cfgX X) B (j, y, μ) - Qat S RelativeAverage.oneC B (j, y, μ)‖ ≤
      (Real.exp (4 * (S.L : ℝ) ^ 3 * C * (Ko * (α₁ * S.L))) - 1) * ((((S.L : ℝ) ^ j) ^ 3)⁻¹ *
        ∑ b ∈ Bq S j y μ, ‖B b.2 b.1‖) := by
    refine hle.trans (H.trans ?_)
    exact mul_le_mul hexp (mul_le_mul_of_nonneg_left hBq (by positivity))
      (mul_nonneg (by positivity) (RelativeAverage.ell1_nonneg fun _ _ => norm_nonneg _))
      ((le_trans hexp0 hexp))
  rw [← le_div_iff₀' hL0] at key
  refine key.trans (le_of_eq ?_)
  field_simp

open Classical in
/-- **The sum of the boxes of the layers**: `Σ_{c ∈ QB}a_j^{-2}Σ_{b ∈ Bq(c)}f(b) ≤ 24L²Σ_b a_{j(b)}^{-2}f(b)` for
`f ≥ 0` (`card_QB_bond`). -/
lemma sum_QB_Bq (hRM : 2 * S.L ≤ S.R * S.L ^ S.mM) (f : Site NF × Fin 4 → ℝ) (hf : ∀ b, 0 ≤ f b) :
    ∑ q ∈ QB S, (((S.L : ℝ) ^ q.1) ^ 2)⁻¹ * ∑ b ∈ Bq S q.1 q.2.1 q.2.2, f b ≤
      24 * (S.L : ℝ) ^ 2 * ∑ b : Site NF × Fin 4, (((S.L : ℝ) ^ jj b.1) ^ 2)⁻¹ * f b := by
  have hL1 : (1 : ℝ) ≤ S.L := by exact_mod_cast S.Lpos
  have e1 : ∑ q ∈ QB S, (((S.L : ℝ) ^ q.1) ^ 2)⁻¹ * ∑ b ∈ Bq S q.1 q.2.1 q.2.2, f b =
      ∑ b : Site NF × Fin 4, f b * ∑ q ∈ (QB S).filter (fun q => b ∈ Bq S q.1 q.2.1 q.2.2),
        (((S.L : ℝ) ^ q.1) ^ 2)⁻¹ := by
    have : ∀ q : ℕ × Site NF × Fin 4, (((S.L : ℝ) ^ q.1) ^ 2)⁻¹ * ∑ b ∈ Bq S q.1 q.2.1 q.2.2, f b =
        ∑ b : Site NF × Fin 4, if b ∈ Bq S q.1 q.2.1 q.2.2 then (((S.L : ℝ) ^ q.1) ^ 2)⁻¹ * f b else 0 := by
      intro q
      rw [Finset.mul_sum, ← Finset.sum_filter]
      congr 1
      ext b; simp
    simp only [this]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_filter, Finset.mul_sum]
    exact Finset.sum_congr rfl fun q _ => by split_ifs <;> ring
  rw [e1, Finset.mul_sum]
  refine Finset.sum_le_sum fun b _ => ?_
  obtain ⟨hcard, hsc⟩ := card_QB_bond S hRM b
  have hw : ∀ q ∈ (QB S).filter (fun q => b ∈ Bq S q.1 q.2.1 q.2.2),
      (((S.L : ℝ) ^ q.1) ^ 2)⁻¹ ≤ (S.L : ℝ) ^ 2 * (((S.L : ℝ) ^ jj b.1) ^ 2)⁻¹ := by
    intro q hq
    obtain ⟨hqQ, hb⟩ := mem_filter.1 hq
    have h := hsc q hqQ hb
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), ← div_eq_inv_mul, div_le_iff₀ (by positivity)]
    rw [← pow_mul, ← pow_mul, ← pow_add]
    exact pow_le_pow_right₀ hL1 (by omega)
  have hs := Finset.sum_le_card_nsmul _ _ _ hw
  rw [nsmul_eq_mul] at hs
  have hc : (((QB S).filter (fun q => b ∈ Bq S q.1 q.2.1 q.2.2)).card : ℝ) ≤ 24 := by exact_mod_cast hcard
  have h0 : 0 ≤ (S.L : ℝ) ^ 2 * (((S.L : ℝ) ^ jj b.1) ^ 2)⁻¹ := by positivity
  calc f b * ∑ q ∈ (QB S).filter (fun q => b ∈ Bq S q.1 q.2.1 q.2.2), (((S.L : ℝ) ^ q.1) ^ 2)⁻¹
      ≤ f b * (24 * ((S.L : ℝ) ^ 2 * (((S.L : ℝ) ^ jj b.1) ^ 2)⁻¹)) :=
        mul_le_mul_of_nonneg_left (hs.trans (mul_le_mul_of_nonneg_right hc h0)) (hf b)
    _ = 24 * (S.L : ℝ) ^ 2 * ((((S.L : ℝ) ^ jj b.1) ^ 2)⁻¹ * f b) := by ring

/-- The difference of two inner products in the norm of `V`, against the bounds of the factors. -/
lemma inner_diff_le (hN : 0 < N) {P P' Q Q' : Matrix (Fin N) (Fin N) ℂ} {xb xc ε w : ℝ} (hε : 0 ≤ ε) (hw : 0 ≤ w)
    (hxb : 0 ≤ xb) (hxc : 0 ≤ xc) (hP' : ‖P'‖ ≤ 2 * w * xb) (hdP : ‖P - P'‖ ≤ ε * w * xb)
    (hQ' : ‖Q'‖ ≤ 2 * w * xc) (hdQ : ‖Q - Q'‖ ≤ ε * w * xc) :
    ‖inner ℂ (emb (N := N) P) (emb (N := N) Q) - inner ℂ (emb (N := N) P') (emb (N := N) Q')‖ ≤
      N * (ε * (4 + ε)) * w ^ 2 * (xb * xc) := by
  have hemb : ∀ M : Matrix (Fin N) (Fin N) ℂ, ‖emb (N := N) M‖ ≤ Real.sqrt N * ‖M‖ := fun M => by
    rw [norm_emb]; exact mul_le_mul_of_nonneg_left (hs_le_opNorm hN M) (Real.sqrt_nonneg _)
  have hQ : ‖Q‖ ≤ (2 + ε) * w * xc := by
    calc ‖Q‖ = ‖Q' + (Q - Q')‖ := by rw [add_sub_cancel]
      _ ≤ ‖Q'‖ + ‖Q - Q'‖ := norm_add_le _ _
      _ ≤ 2 * w * xc + ε * w * xc := add_le_add hQ' hdQ
      _ = (2 + ε) * w * xc := by ring
  have e : inner ℂ (emb (N := N) P) (emb (N := N) Q) - inner ℂ (emb (N := N) P') (emb (N := N) Q') =
      inner ℂ (emb (N := N) (P - P')) (emb (N := N) Q) + inner ℂ (emb (N := N) P') (emb (N := N) (Q - Q')) := by
    rw [emb_sub', emb_sub', inner_sub_left, inner_sub_right]; ring
  rw [e]
  have hsN : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt (Nat.cast_nonneg _)
  have hs0 : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
  have h1 : ‖inner ℂ (emb (N := N) (P - P')) (emb (N := N) Q)‖ ≤
      (Real.sqrt N * (ε * w * xb)) * (Real.sqrt N * ((2 + ε) * w * xc)) :=
    (norm_inner_le_norm _ _).trans (mul_le_mul ((hemb _).trans (mul_le_mul_of_nonneg_left hdP hs0))
      ((hemb _).trans (mul_le_mul_of_nonneg_left hQ hs0)) (norm_nonneg _) (by positivity))
  have h2 : ‖inner ℂ (emb (N := N) P') (emb (N := N) (Q - Q'))‖ ≤
      (Real.sqrt N * (2 * w * xb)) * (Real.sqrt N * (ε * w * xc)) :=
    (norm_inner_le_norm _ _).trans (mul_le_mul ((hemb _).trans (mul_le_mul_of_nonneg_left hP' hs0))
      ((hemb _).trans (mul_le_mul_of_nonneg_left hdQ hs0)) (norm_nonneg _) (by positivity))
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ (Real.sqrt N * (ε * w * xb)) * (Real.sqrt N * ((2 + ε) * w * xc)) +
        (Real.sqrt N * (2 * w * xb)) * (Real.sqrt N * (ε * w * xc)) := add_le_add h1 h2
    _ = (Real.sqrt N * Real.sqrt N) * (ε * (4 + ε)) * w ^ 2 * (xb * xc) := by ring
    _ = _ := by rw [hsN]

lemma norm_expA (ph : Site NF → ℝ) (A : Fin 4 → Site NF → Matrix (Fin N) (Fin N) ℂ) (ν : Fin 4) (z : Site NF) :
    ‖expA S ph A ν z‖ = Real.exp (ph z) * ‖A ν z‖ := by
  simp only [expA, norm_smul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]

/-- **The weights `e^{±φ}` on the box**: `(Σ_{Bq}|e^φA|)(Σ_{Bq}|e^{-φ}A|) ≤ 3(Σ_{Bq}|A|)²` for `|φ(x) - φ(x')| ≤
δd_F(x, x')`, `16Lδ ≤ 1` (`Xc_dF`). -/
lemma expA_box (hRM : 18 * (S.L : ℝ) ≤ RMS) (hR1 : 1 ≤ S.R * S.L ^ S.mM) {j : ℕ} {y : Site NF} {μ : Fin 4}
    (hq : (j, y, μ) ∈ QB S) {δ : ℝ} (hδ : 0 ≤ δ) (hδL : 16 * S.L * δ ≤ 1) (ph : Site NF → ℝ)
    (hph : ∀ x x', |ph x - ph x'| ≤ δ * S.dF x x') (A : Fin 4 → Site NF → Matrix (Fin N) (Fin N) ℂ) :
    (∑ b ∈ Bq S j y μ, ‖expA S ph A b.2 b.1‖) * (∑ b ∈ Bq S j y μ, ‖expA S (fun x => -ph x) A b.2 b.1‖) ≤
      3 * (∑ b ∈ Bq S j y μ, ‖A b.2 b.1‖) ^ 2 := by
  have hw : ∀ b ∈ Bq S j y μ, ∀ b' ∈ Bq S j y μ, Real.exp (ph b.1) * Real.exp (-ph b'.1) ≤ 3 := by
    intro b hb b' hb'
    simp only [Bq, mem_filter, mem_product, mem_univ, true_and] at hb hb'
    have hd := Xc_dF S hRM hR1 hq hb.1 hb'.1
    have h1 : ph b.1 - ph b'.1 ≤ 1 := by
      have := (le_abs_self _).trans (hph b.1 b'.1)
      have h2 : δ * S.dF b.1 b'.1 ≤ δ * (16 * S.L) := mul_le_mul_of_nonneg_left hd hδ
      linarith
    rw [← Real.exp_add]
    calc Real.exp (ph b.1 + -ph b'.1) ≤ Real.exp 1 := Real.exp_le_exp.2 (by linarith)
      _ ≤ 3 := (Real.exp_one_lt_d9.trans (by norm_num)).le
  simp only [norm_expA]
  rw [Finset.sum_mul_sum, sq, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun b hb => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun b' hb' => ?_
  have h := hw b hb b' hb'
  have h0 : 0 ≤ ‖A b.2 b.1‖ * ‖A b'.2 b'.1‖ := by positivity
  calc Real.exp (ph b.1) * ‖A b.2 b.1‖ * (Real.exp (-ph b'.1) * ‖A b'.2 b'.1‖)
      = (Real.exp (ph b.1) * Real.exp (-ph b'.1)) * (‖A b.2 b.1‖ * ‖A b'.2 b'.1‖) := by ring
    _ ≤ 3 * (‖A b.2 b.1‖ * ‖A b'.2 b'.1‖) := mul_le_mul_of_nonneg_right h h0

/-- **The constraint form at `𝐔`**: `Σ_{c ∈ QB}a_c²⟨(Q(𝐔)B)(c), (Q(𝐔)C)(c)⟩` (in the norm of `V`). -/
def QBU (U : Config N NF) (B C : Fin 4 → Site NF → Matrix (Fin N) (Fin N) ℂ) : ℂ :=
  ∑ q ∈ QB S, (((S.L ^ q.1 : ℕ) : ℝ) ^ 2 : ℂ) * inner ℂ (emb (N := N) (Qat S U B q)) (emb (N := N) (Qat S U C q))

lemma QBU_one (B C : Fin 4 → Site NF → Matrix (Fin N) (Fin N) ℂ) :
    QBU S RelativeAverage.oneC B C = QB2 S B C := by
  unfold QBU QB2
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [Qat_one S B hq, Qat_one S C hq]

/-- `‖A‖² ≤ |A|²_V` (the operator norm against the norm of `V`). -/
lemma opNorm_sq_le_emb (A : Matrix (Fin N) (Fin N) ℂ) : ‖A‖ ^ 2 ≤ ‖emb (N := N) A‖ ^ 2 := by
  have h := opNorm_le_sqrt_mul_hs A
  rw [← norm_emb] at h
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

/-- **The comparison of the constraint forms at `𝐔 = e^{iX}`** (`lem:sf-vector-decay`, "The complex field", step
(4), in the fine model): for a regular field `X` with `α₁L, K_oα₁L ≤ c` and a weight `φ` with
`|φ(x) - φ(x')| ≤ δd_F(x, x')`, `16Lδ ≤ 1`,
`|Re Σ_ca_c²⟨Q(𝐔)(e^φA)(c), Q(𝐔)(e^{-φ}A)(c)⟩ - Σ_ca_c²|(QA)(c)|²| ≤ (96L³δ + 576L²Nε̄(4 + ε̄))‖A‖_w²`,
`ε̄ = e^{4L³CK_oα₁L} - 1` (`Q_conj` at `id`; `Qat_one_le`, `Qat_diff_le`, `expA_box`, `sum_QB_Bq`). -/
theorem QBU_conj (G : GaugeGroup N) (hGc : IsClosed G.mats) (hN : 1 ≤ N) :
    ∃ c Ko C : ℝ, 0 < c ∧ 0 ≤ Ko ∧ 0 ≤ C ∧
      ∀ (hRM : 18 * (S.L : ℝ) ≤ RMS) (hR1 : 1 ≤ S.R * S.L ^ S.mM)
        (hn : ∀ l, 4 * SequenceAverages.hS S + 4 ≤ MultiscaleAverages.nn (SequenceAverages.hS S) S.mT S.k l)
        {X : Fin 4 → Site NF → Matrix (Fin N) (Fin N) ℂ} {α₁ : ℝ} (hX : RegField S X α₁) (hα0 : 0 ≤ α₁)
        (hαc : α₁ * S.L ≤ c) (hKαc : Ko * (α₁ * S.L) ≤ c) {δ : ℝ} (hδ : 0 ≤ δ) (hδL : 16 * S.L * δ ≤ 1)
        (ph : Site NF → ℝ) (hph : ∀ x x', |ph x - ph x'| ≤ δ * S.dF x x')
        (A : Fin 4 → Site NF → Matrix (Fin N) (Fin N) ℂ),
      |(QBU S (cfgX X) (expA S ph A) (expA S (fun x => -ph x) A)).re - Qnorm S A| ≤
        (96 * (S.L : ℝ) ^ 3 * δ + 576 * (S.L : ℝ) ^ 2 * N *
          ((Real.exp (4 * (S.L : ℝ) ^ 3 * C * (Ko * (α₁ * S.L))) - 1) *
            (4 + (Real.exp (4 * (S.L : ℝ) ^ 3 * C * (Ko * (α₁ * S.L))) - 1)))) * wnorm S A := by
  obtain ⟨c, Ko, C, hc, hKo, hC, hd⟩ := Qat_diff_le S G hGc hN
  refine ⟨c, Ko, C, hc, hKo, hC, ?_⟩
  intro hRM hR1 hn X α₁ hX hα0 hαc hKαc δ hδ hδL ph hph A
  set ε := Real.exp (4 * (S.L : ℝ) ^ 3 * C * (Ko * (α₁ * S.L))) - 1 with hεdef
  have hε : 0 ≤ ε := by
    have h0 : 0 ≤ 4 * (S.L : ℝ) ^ 3 * C * (Ko * (α₁ * S.L)) := by positivity
    have := Real.add_one_le_exp (4 * (S.L : ℝ) ^ 3 * C * (Ko * (α₁ * S.L)))
    simp only [hεdef]; linarith
  have hN0 : 0 < N := by omega
  have hL0 : (0 : ℝ) < S.L := by exact_mod_cast S.Lpos
  have hRM2 : 2 * (S.L : ℝ) ≤ RMS := by linarith
  have hRMn : 2 * S.L ≤ S.R * S.L ^ S.mM := by exact_mod_cast hRM2
  set B := expA S ph A
  set C' := expA S (fun x => -ph x) A
  set K : ℝ := (N : ℝ) * (ε * (4 + ε))
  have hK : 0 ≤ K := by positivity
  -- the bound of one bond of the layers
  have hbond : ∀ q ∈ QB S, ‖(((S.L ^ q.1 : ℕ) : ℝ) ^ 2 : ℂ) *
      (inner ℂ (emb (N := N) (Qat S (cfgX X) B q)) (emb (N := N) (Qat S (cfgX X) C' q)) -
        inner ℂ (emb (N := N) (Qat S RelativeAverage.oneC B q)) (emb (N := N) (Qat S RelativeAverage.oneC C' q)))‖ ≤
      24 * K * ((((S.L : ℝ) ^ q.1) ^ 2)⁻¹ * ∑ b ∈ Bq S q.1 q.2.1 q.2.2, ‖emb (N := N) (A b.2 b.1)‖ ^ 2) := by
    rintro ⟨j, y, μ⟩ hq
    have hq' := hq
    simp only [QB, mem_filter, mem_product, mem_range, mem_univ, true_and] at hq'
    obtain ⟨hjk, hlat, -⟩ := hq'
    set w : ℝ := (((S.L : ℝ) ^ j) ^ 4)⁻¹
    set xb := ∑ b ∈ Bq S j y μ, ‖B b.2 b.1‖
    set xc := ∑ b ∈ Bq S j y μ, ‖C' b.2 b.1‖
    set xa := ∑ b ∈ Bq S j y μ, ‖A b.2 b.1‖
    set ya := ∑ b ∈ Bq S j y μ, ‖emb (N := N) (A b.2 b.1)‖ ^ 2
    have hpj : (0 : ℝ) < (S.L : ℝ) ^ j := by positivity
    have h1 := inner_diff_le hN0 hε (by positivity : 0 ≤ w) (Finset.sum_nonneg fun _ _ => norm_nonneg _)
      (Finset.sum_nonneg fun _ _ => norm_nonneg _) (Qat_one_le S B hq hn)
      (hd hRM2 hn hq hX hα0 hαc hKαc B) (Qat_one_le S C' hq hn) (hd hRM2 hn hq hX hα0 hαc hKαc C')
    have h2 : xb * xc ≤ 3 * xa ^ 2 := expA_box S hRM hR1 hq hδ hδL ph hph A
    have h3 : xa ^ 2 ≤ 8 * ((S.L : ℝ) ^ j) ^ 4 * ya := by
      have hcs := sq_sum_le_card_mul_sum_sq (s := Bq S j y μ) (f := fun b => ‖A b.2 b.1‖)
      have hc : ((Bq S j y μ).card : ℝ) ≤ 8 * ((S.L : ℝ) ^ j) ^ 4 := by
        have := card_Bq S (by omega) hlat μ; exact_mod_cast this
      have hs : ∑ b ∈ Bq S j y μ, ‖A b.2 b.1‖ ^ 2 ≤ ya :=
        Finset.sum_le_sum fun b _ => opNorm_sq_le_emb _
      calc xa ^ 2 ≤ (Bq S j y μ).card * ∑ b ∈ Bq S j y μ, ‖A b.2 b.1‖ ^ 2 := hcs
        _ ≤ 8 * ((S.L : ℝ) ^ j) ^ 4 * ya :=
          mul_le_mul hc hs (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
    have hnc : ‖((((S.L ^ j : ℕ) : ℝ) : ℂ)) ^ 2‖ = ((S.L : ℝ) ^ j) ^ 2 := by
      rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg (by positivity)]; push_cast; ring
    dsimp only
    rw [norm_mul, hnc]
    have hya : 0 ≤ ya := Finset.sum_nonneg fun _ _ => sq_nonneg _
    calc ((S.L : ℝ) ^ j) ^ 2 * ‖_‖ ≤ ((S.L : ℝ) ^ j) ^ 2 * (K * w ^ 2 * (xb * xc)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ ((S.L : ℝ) ^ j) ^ 2 * (K * w ^ 2 * (3 * (8 * ((S.L : ℝ) ^ j) ^ 4 * ya))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (h2.trans ?_) (by positivity)) (by positivity)
          exact mul_le_mul_of_nonneg_left h3 (by norm_num)
      _ = 24 * K * ((((S.L : ℝ) ^ j) ^ 2)⁻¹ * ya) := by
          simp only [w]; field_simp; ring
  -- the sum over the bonds of the layers
  have hdiff : ‖QBU S (cfgX X) B C' - QB2 S B C'‖ ≤ 576 * (S.L : ℝ) ^ 2 * K * wnorm S A := by
    rw [← QBU_one S B C']
    unfold QBU
    rw [← Finset.sum_sub_distrib]
    simp only [← mul_sub]
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hbond).trans ?_)
    rw [← Finset.mul_sum]
    have hs := sum_QB_Bq S hRMn (fun b => ‖emb (N := N) (A b.2 b.1)‖ ^ 2) fun _ => sq_nonneg _
    have hw : ∑ b : Site NF × Fin 4, (((S.L : ℝ) ^ jj b.1) ^ 2)⁻¹ * ‖emb (N := N) (A b.2 b.1)‖ ^ 2 = wnorm S A := by
      unfold wnorm
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.mul_sum]; push_cast; rfl
    rw [hw] at hs
    calc 24 * K * ∑ q ∈ QB S, (((S.L : ℝ) ^ q.1) ^ 2)⁻¹ * ∑ b ∈ Bq S q.1 q.2.1 q.2.2, ‖emb (N := N) (A b.2 b.1)‖ ^ 2
        ≤ 24 * K * (24 * (S.L : ℝ) ^ 2 * wnorm S A) := mul_le_mul_of_nonneg_left hs (by positivity)
      _ = 576 * (S.L : ℝ) ^ 2 * K * wnorm S A := by ring
  have hQ0 := Q_conj S hRM hδ hδL ph hph A
  have hre : |(QBU S (cfgX X) B C').re - (QB2 S B C').re| ≤ 576 * (S.L : ℝ) ^ 2 * K * wnorm S A := by
    rw [← Complex.sub_re]; exact (Complex.abs_re_le_norm _).trans hdiff
  calc |(QBU S (cfgX X) B C').re - Qnorm S A|
      ≤ |(QBU S (cfgX X) B C').re - (QB2 S B C').re| + |(QB2 S B C').re - Qnorm S A| := abs_sub_le _ _ _
    _ ≤ 576 * (S.L : ℝ) ^ 2 * K * wnorm S A + 96 * (S.L : ℝ) ^ 3 * δ * wnorm S A := add_le_add hre hQ0
    _ = _ := by simp only [K]; ring

/-- **The input `hQ` of `decay_U`**: for an operator `Q_𝖺` on `1`-forms whose sesquilinear form is the constraint form
at `𝐔` (`⟨B^*, Q_𝖺C⟩ = QBU(B, C)`), both comparisons of `decay_U` hold with
`ε_Q = 96L³δ + 576L²Nε̄(4 + ε̄)`, `ε̄ = e^{4L³CK_oα₁L} - 1` (`QBU_conj`, at `φ` and at `φ = 0`). -/
theorem hQ_of_QBU (G : GaugeGroup N) (hGc : IsClosed G.mats) (hN : 1 ≤ N) :
    ∃ c Ko C : ℝ, 0 < c ∧ 0 ≤ Ko ∧ 0 ≤ C ∧
      ∀ (hRM : 18 * (S.L : ℝ) ≤ RMS) (hR1 : 1 ≤ S.R * S.L ^ S.mM)
        (hn : ∀ l, 4 * SequenceAverages.hS S + 4 ≤ MultiscaleAverages.nn (SequenceAverages.hS S) S.mT S.k l)
        {X : Fin 4 → Site NF → Matrix (Fin N) (Fin N) ℂ} {α₁ : ℝ} (hX : RegField S X α₁) (hα0 : 0 ≤ α₁)
        (hαc : α₁ * S.L ≤ c) (hKαc : Ko * (α₁ * S.L) ≤ c) {δ : ℝ} (hδ : 0 ≤ δ) (hδL : 16 * S.L * δ ≤ 1)
        (ph : Site NF → ℝ) (hph : ∀ x x', |ph x - ph x'| ≤ δ * S.dF x x')
        (QOp : Module.End ℂ (Fin 4 → Site NF → Matrix (Fin N) (Fin N) ℂ))
        (hQOp : ∀ B C, pair1V S B (QOp C) = QBU S (cfgX X) B C),
      (∀ A, |(pair1V S (expA S ph A) (QOp (expA S (fun x => -ph x) A))).re - Qnorm S A| ≤
        (96 * (S.L : ℝ) ^ 3 * δ + 576 * (S.L : ℝ) ^ 2 * N *
          ((Real.exp (4 * (S.L : ℝ) ^ 3 * C * (Ko * (α₁ * S.L))) - 1) *
            (4 + (Real.exp (4 * (S.L : ℝ) ^ 3 * C * (Ko * (α₁ * S.L))) - 1)))) * (gradNorm S A + wnorm S A)) ∧
      (∀ A, |(pair1V S A (QOp A)).re - Qnorm S A| ≤
        (96 * (S.L : ℝ) ^ 3 * δ + 576 * (S.L : ℝ) ^ 2 * N *
          ((Real.exp (4 * (S.L : ℝ) ^ 3 * C * (Ko * (α₁ * S.L))) - 1) *
            (4 + (Real.exp (4 * (S.L : ℝ) ^ 3 * C * (Ko * (α₁ * S.L))) - 1)))) * (gradNorm S A + wnorm S A)) := by
  obtain ⟨c, Ko, C, hc, hKo, hC, hd⟩ := QBU_conj S G hGc hN
  refine ⟨c, Ko, C, hc, hKo, hC, ?_⟩
  intro hRM hR1 hn X α₁ hX hα0 hαc hKαc δ hδ hδL ph hph QOp hQOp
  set ε := Real.exp (4 * (S.L : ℝ) ^ 3 * C * (Ko * (α₁ * S.L))) - 1 with hεdef
  have hε : 0 ≤ ε := by
    have h0 : 0 ≤ 4 * (S.L : ℝ) ^ 3 * C * (Ko * (α₁ * S.L)) := by positivity
    have := Real.add_one_le_exp (4 * (S.L : ℝ) ^ 3 * C * (Ko * (α₁ * S.L)))
    simp only [hεdef]; linarith
  have hE0 : 0 ≤ 576 * (S.L : ℝ) ^ 2 * N * (ε * (4 + ε)) := by positivity
  have hEd : 0 ≤ 96 * (S.L : ℝ) ^ 3 * δ := by positivity
  have hext : ∀ A : Fin 4 → Site NF → Matrix (Fin N) (Fin N) ℂ, wnorm S A ≤ gradNorm S A + wnorm S A := fun A => by
    have := gradNorm_nonneg' S A; linarith
  refine ⟨fun A => ?_, fun A => ?_⟩
  · rw [hQOp]
    exact (hd hRM hR1 hn hX hα0 hαc hKαc hδ hδL ph hph A).trans
      (mul_le_mul_of_nonneg_left (hext A) (by positivity))
  · have h0 := hd hRM hR1 hn hX hα0 hαc hKαc le_rfl (by simp) (fun _ => 0) (fun x x' => by simp) A
    simp only [neg_zero, expA_zero] at h0
    rw [hQOp]
    refine h0.trans ?_
    simp only [mul_zero, zero_add]
    calc 576 * (S.L : ℝ) ^ 2 * N * (ε * (4 + ε)) * wnorm S A
        ≤ 576 * (S.L : ℝ) ^ 2 * N * (ε * (4 + ε)) * (gradNorm S A + wnorm S A) :=
          mul_le_mul_of_nonneg_left (hext A) hE0
      _ ≤ (96 * (S.L : ℝ) ^ 3 * δ + 576 * (S.L : ℝ) ^ 2 * N * (ε * (4 + ε))) * (gradNorm S A + wnorm S A) :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hEd)
            (add_nonneg (gradNorm_nonneg' S A) (wnorm_nonneg' S A))

/-! ### The bilinear constraint form `⟨B^*, Q^*Q C⟩` at `𝐔`

At a complex configuration the transpose of `Q(𝐔)` for the bilinear pairing gives the form
`Σ_ca_c²tr(Q(𝐔)(B^*)(c)·Q(𝐔)(C)(c))`, with `B^*` the sitewise adjoint; at `id`, `Q(B^*) = Q(B)^*`. -/

open Matrix

/-- The sitewise adjoint `B^*` of a `1`-form. -/
def Bstar (B : Fin 4 → Site NF → Matrix (Fin N) (Fin N) ℂ) : Fin 4 → Site NF → Matrix (Fin N) (Fin N) ℂ :=
  fun μ x => (B μ x)ᴴ

lemma Qt_Bstar (B : Fin 4 → Site NF → Matrix (Fin N) (Fin N) ℂ) (j : ℕ) (y : Site NF) (μ : Fin 4) :
    Qt S (Bstar S B) j y μ = (Qt S B j y μ)ᴴ := by
  unfold Qt Bstar
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sum]
  simp only [Matrix.conjTranspose_sum, star_inv₀, star_pow, Complex.star_def, Complex.conj_natCast]

/-- **The bilinear constraint form at `𝐔`**: `Σ_{c ∈ QB}a_c²tr(Q(𝐔)(B^*)(c)·Q(𝐔)(C)(c))`, written in the norm of `V`
as `a_c²⟨Q(𝐔)(B^*)(c)^*, Q(𝐔)(C)(c)⟩`. -/
def QBUc (U : Config N NF) (B C : Fin 4 → Site NF → Matrix (Fin N) (Fin N) ℂ) : ℂ :=
  ∑ q ∈ QB S, (((S.L ^ q.1 : ℕ) : ℝ) ^ 2 : ℂ) *
    inner ℂ (emb (N := N) (Qat S U (Bstar S B) q)ᴴ) (emb (N := N) (Qat S U C q))

lemma QBUc_one (B C : Fin 4 → Site NF → Matrix (Fin N) (Fin N) ℂ) :
    QBUc S RelativeAverage.oneC B C = QB2 S B C := by
  unfold QBUc QB2
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [Qat_one S _ hq, Qat_one S C hq, Qt_Bstar, Matrix.conjTranspose_conjTranspose]

lemma norm_Bstar (B : Fin 4 → Site NF → Matrix (Fin N) (Fin N) ℂ) (ν : Fin 4) (z : Site NF) :
    ‖Bstar S B ν z‖ = ‖B ν z‖ := opNorm_conjTranspose _

/-- **The comparison of the bilinear constraint forms at `𝐔 = e^{iX}`**: as `QBU_conj`, for
`Σ_ca_c²tr(Q(𝐔)(B^*)(c)Q(𝐔)(C)(c))` (`Q(id)(B^*) = Q(id)(B)^*`, `‖M^*‖ = ‖M‖`). -/
theorem QBUc_conj (G : GaugeGroup N) (hGc : IsClosed G.mats) (hN : 1 ≤ N) :
    ∃ c Ko C : ℝ, 0 < c ∧ 0 ≤ Ko ∧ 0 ≤ C ∧
      ∀ (hRM : 18 * (S.L : ℝ) ≤ RMS) (hR1 : 1 ≤ S.R * S.L ^ S.mM)
        (hn : ∀ l, 4 * SequenceAverages.hS S + 4 ≤ MultiscaleAverages.nn (SequenceAverages.hS S) S.mT S.k l)
        {X : Fin 4 → Site NF → Matrix (Fin N) (Fin N) ℂ} {α₁ : ℝ} (hX : RegField S X α₁) (hα0 : 0 ≤ α₁)
        (hαc : α₁ * S.L ≤ c) (hKαc : Ko * (α₁ * S.L) ≤ c) {δ : ℝ} (hδ : 0 ≤ δ) (hδL : 16 * S.L * δ ≤ 1)
        (ph : Site NF → ℝ) (hph : ∀ x x', |ph x - ph x'| ≤ δ * S.dF x x')
        (A : Fin 4 → Site NF → Matrix (Fin N) (Fin N) ℂ),
      |(QBUc S (cfgX X) (expA S ph A) (expA S (fun x => -ph x) A)).re - Qnorm S A| ≤
        (96 * (S.L : ℝ) ^ 3 * δ + 576 * (S.L : ℝ) ^ 2 * N *
          ((Real.exp (4 * (S.L : ℝ) ^ 3 * C * (Ko * (α₁ * S.L))) - 1) *
            (4 + (Real.exp (4 * (S.L : ℝ) ^ 3 * C * (Ko * (α₁ * S.L))) - 1)))) * wnorm S A := by
  obtain ⟨c, Ko, C, hc, hKo, hC, hd⟩ := Qat_diff_le S G hGc hN
  refine ⟨c, Ko, C, hc, hKo, hC, ?_⟩
  intro hRM hR1 hn X α₁ hX hα0 hαc hKαc δ hδ hδL ph hph A
  set ε := Real.exp (4 * (S.L : ℝ) ^ 3 * C * (Ko * (α₁ * S.L))) - 1 with hεdef
  have hε : 0 ≤ ε := by
    have h0 : 0 ≤ 4 * (S.L : ℝ) ^ 3 * C * (Ko * (α₁ * S.L)) := by positivity
    have := Real.add_one_le_exp (4 * (S.L : ℝ) ^ 3 * C * (Ko * (α₁ * S.L)))
    simp only [hεdef]; linarith
  have hN0 : 0 < N := by omega
  have hL0 : (0 : ℝ) < S.L := by exact_mod_cast S.Lpos
  have hRM2 : 2 * (S.L : ℝ) ≤ RMS := by linarith
  have hRMn : 2 * S.L ≤ S.R * S.L ^ S.mM := by exact_mod_cast hRM2
  set B := expA S ph A
  set C' := expA S (fun x => -ph x) A
  set K : ℝ := (N : ℝ) * (ε * (4 + ε))
  have hK : 0 ≤ K := by positivity
  have hbond : ∀ q ∈ QB S, ‖(((S.L ^ q.1 : ℕ) : ℝ) ^ 2 : ℂ) *
      (inner ℂ (emb (N := N) (Qat S (cfgX X) (Bstar S B) q)ᴴ) (emb (N := N) (Qat S (cfgX X) C' q)) -
        inner ℂ (emb (N := N) (Qat S RelativeAverage.oneC (Bstar S B) q)ᴴ)
          (emb (N := N) (Qat S RelativeAverage.oneC C' q)))‖ ≤
      24 * K * ((((S.L : ℝ) ^ q.1) ^ 2)⁻¹ * ∑ b ∈ Bq S q.1 q.2.1 q.2.2, ‖emb (N := N) (A b.2 b.1)‖ ^ 2) := by
    rintro ⟨j, y, μ⟩ hq
    have hq' := hq
    simp only [QB, mem_filter, mem_product, mem_range, mem_univ, true_and] at hq'
    obtain ⟨hjk, hlat, -⟩ := hq'
    set w : ℝ := (((S.L : ℝ) ^ j) ^ 4)⁻¹
    set xb := ∑ b ∈ Bq S j y μ, ‖B b.2 b.1‖
    set xc := ∑ b ∈ Bq S j y μ, ‖C' b.2 b.1‖
    set xa := ∑ b ∈ Bq S j y μ, ‖A b.2 b.1‖
    set ya := ∑ b ∈ Bq S j y μ, ‖emb (N := N) (A b.2 b.1)‖ ^ 2
    have hpj : (0 : ℝ) < (S.L : ℝ) ^ j := by positivity
    have hsB : ∑ b ∈ Bq S j y μ, ‖Bstar S B b.2 b.1‖ = xb :=
      Finset.sum_congr rfl fun b _ => norm_Bstar S B _ _
    have hP' : ‖(Qat S RelativeAverage.oneC (Bstar S B) (j, y, μ))ᴴ‖ ≤ 2 * w * xb := by
      rw [opNorm_conjTranspose, ← hsB]; exact Qat_one_le S _ hq hn
    have hdP : ‖(Qat S (cfgX X) (Bstar S B) (j, y, μ))ᴴ - (Qat S RelativeAverage.oneC (Bstar S B) (j, y, μ))ᴴ‖ ≤
        ε * w * xb := by
      rw [← Matrix.conjTranspose_sub, opNorm_conjTranspose, ← hsB]
      exact hd hRM2 hn hq hX hα0 hαc hKαc _
    have h1 := inner_diff_le hN0 hε (by positivity : 0 ≤ w) (Finset.sum_nonneg fun _ _ => norm_nonneg _)
      (Finset.sum_nonneg fun _ _ => norm_nonneg _) hP' hdP (Qat_one_le S C' hq hn)
      (hd hRM2 hn hq hX hα0 hαc hKαc C')
    have h2 : xb * xc ≤ 3 * xa ^ 2 := expA_box S hRM hR1 hq hδ hδL ph hph A
    have h3 : xa ^ 2 ≤ 8 * ((S.L : ℝ) ^ j) ^ 4 * ya := by
      have hcs := sq_sum_le_card_mul_sum_sq (s := Bq S j y μ) (f := fun b => ‖A b.2 b.1‖)
      have hc : ((Bq S j y μ).card : ℝ) ≤ 8 * ((S.L : ℝ) ^ j) ^ 4 := by
        have := card_Bq S (by omega) hlat μ; exact_mod_cast this
      have hs : ∑ b ∈ Bq S j y μ, ‖A b.2 b.1‖ ^ 2 ≤ ya :=
        Finset.sum_le_sum fun b _ => opNorm_sq_le_emb _
      calc xa ^ 2 ≤ (Bq S j y μ).card * ∑ b ∈ Bq S j y μ, ‖A b.2 b.1‖ ^ 2 := hcs
        _ ≤ 8 * ((S.L : ℝ) ^ j) ^ 4 * ya :=
          mul_le_mul hc hs (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
    have hnc : ‖((((S.L ^ j : ℕ) : ℝ) : ℂ)) ^ 2‖ = ((S.L : ℝ) ^ j) ^ 2 := by
      rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg (by positivity)]; push_cast; ring
    dsimp only
    rw [norm_mul, hnc]
    have hya : 0 ≤ ya := Finset.sum_nonneg fun _ _ => sq_nonneg _
    calc ((S.L : ℝ) ^ j) ^ 2 * ‖_‖ ≤ ((S.L : ℝ) ^ j) ^ 2 * (K * w ^ 2 * (xb * xc)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ ((S.L : ℝ) ^ j) ^ 2 * (K * w ^ 2 * (3 * (8 * ((S.L : ℝ) ^ j) ^ 4 * ya))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (h2.trans ?_) (by positivity)) (by positivity)
          exact mul_le_mul_of_nonneg_left h3 (by norm_num)
      _ = 24 * K * ((((S.L : ℝ) ^ j) ^ 2)⁻¹ * ya) := by
          simp only [w]; field_simp; ring
  have hdiff : ‖QBUc S (cfgX X) B C' - QB2 S B C'‖ ≤ 576 * (S.L : ℝ) ^ 2 * K * wnorm S A := by
    rw [← QBUc_one S B C']
    unfold QBUc
    rw [← Finset.sum_sub_distrib]
    simp only [← mul_sub]
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hbond).trans ?_)
    rw [← Finset.mul_sum]
    have hs := sum_QB_Bq S hRMn (fun b => ‖emb (N := N) (A b.2 b.1)‖ ^ 2) fun _ => sq_nonneg _
    have hw : ∑ b : Site NF × Fin 4, (((S.L : ℝ) ^ jj b.1) ^ 2)⁻¹ * ‖emb (N := N) (A b.2 b.1)‖ ^ 2 = wnorm S A := by
      unfold wnorm
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.mul_sum]; push_cast; rfl
    rw [hw] at hs
    calc 24 * K * ∑ q ∈ QB S, (((S.L : ℝ) ^ q.1) ^ 2)⁻¹ * ∑ b ∈ Bq S q.1 q.2.1 q.2.2, ‖emb (N := N) (A b.2 b.1)‖ ^ 2
        ≤ 24 * K * (24 * (S.L : ℝ) ^ 2 * wnorm S A) := mul_le_mul_of_nonneg_left hs (by positivity)
      _ = 576 * (S.L : ℝ) ^ 2 * K * wnorm S A := by ring
  have hQ0 := Q_conj S hRM hδ hδL ph hph A
  have hre : |(QBUc S (cfgX X) B C').re - (QB2 S B C').re| ≤ 576 * (S.L : ℝ) ^ 2 * K * wnorm S A := by
    rw [← Complex.sub_re]; exact (Complex.abs_re_le_norm _).trans hdiff
  calc |(QBUc S (cfgX X) B C').re - Qnorm S A|
      ≤ |(QBUc S (cfgX X) B C').re - (QB2 S B C').re| + |(QB2 S B C').re - Qnorm S A| := abs_sub_le _ _ _
    _ ≤ 576 * (S.L : ℝ) ^ 2 * K * wnorm S A + 96 * (S.L : ℝ) ^ 3 * δ * wnorm S A := add_le_add hre hQ0
    _ = _ := by simp only [K]; ring

/-! ### The dictionary with the concrete operators (bridge (B5))

The bonds of the layers `LBond` of `SequenceIndex` are the triples `(j, ef y, μ)`, `(j, y, μ) ∈ QB`, and the coarse
point `crd j (ef y)` is the base point `baseOf c₀ j j` of the chain. -/

lemma NF_eq_mul {j : ℕ} (hj : j ≤ S.k) :
    NF = S.L ^ j * MultiscaleAverages.nn (SequenceAverages.hS S) S.mT S.k j := by
  simp only [SequenceAverages.N0, MultiscaleAverages.nn, Nat.sub_zero, ← SequenceAverages.L_eq S]
  rw [show S.mT + S.k = j + (S.mT + (S.k - j)) by omega, pow_add]; ring

/-- **The coarse point of a bond of the layers**: `crd j (ef y) = baseOf c₀ j j` for `y ∈ a_jℤ⁴`. -/
lemma crd_ef {j : ℕ} (hj : j ≤ S.k) {y : Site NF} (hlat : InLat S.L j y) :
    SequenceAverages.crd S j (S.ef y) =
      LevelsBridge.baseOf (SequenceAverages.hS S) S.mT S.k (c0Of S hlat) j j := by
  have hinj := emb_injective (N := SequenceAverages.N0 S) (L := S.L) (k := S.k) (m := S.mT) S.Lpos
    (SequenceAverages.N0_eq S)
  set n := MultiscaleAverages.nn (SequenceAverages.hS S) S.mT S.k j
  have hn0 : (0 : ℤ) < n := by have : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n); exact_mod_cast this
  have hNF : (NF : ℤ) = (S.L : ℤ) ^ j * n := by rw [NF_eq_mul S hj]; push_cast; ring
  have hLj : (0 : ℤ) < (S.L : ℤ) ^ j := pow_pos (by exact_mod_cast S.Lpos) _
  funext σ
  simp only [SequenceAverages.crd, SeqDom.ef, Function.leftInverse_invFun hinj y, LevelsBridge.baseOf, Nat.sub_self,
    pow_zero, one_mul]
  set r := c0Of S hlat σ
  have hy : y σ = (((S.L ^ j : ℕ) * r : ℤ) : ZMod NF) := (hlat σ).choose_spec
  have hv : (((y σ).val : ℕ) : ℤ) = (S.L : ℤ) ^ j * (r % n) := by
    rw [hy, ZMod.val_intCast, hNF]
    push_cast
    exact Int.mul_emod_mul_of_pos _ _ hLj
  have hr0 : 0 ≤ r % (n : ℤ) := Int.emod_nonneg _ hn0.ne'
  have hv' : (y σ).val = S.L ^ j * (r % n).toNat := by
    have : (((y σ).val : ℕ) : ℤ) = ((S.L ^ j * (r % n).toNat : ℕ) : ℤ) := by
      rw [hv]; push_cast; rw [Int.toNat_of_nonneg hr0]
    exact_mod_cast this
  rw [hv', Nat.mul_div_cancel_left _ (pow_pos S.Lpos _)]
  have e : (((r % n).toNat : ℕ) : ZMod n) = (((r % n).toNat : ℤ) : ZMod n) := by push_cast; rfl
  rw [e, Int.toNat_of_nonneg hr0, ZMod.intCast_mod]

lemma T_zero_of_mem {j : ℕ} {t : Tor (ellT S.L S.mT)} (ht : t ∈ S.TL j) : t ∈ S.TL 0 := by
  induction j with
  | zero => exact ht
  | succ j ih => exact ih (T_subset (L := S.L) (k := S.k) (m := S.mT) j ht)

lemma bend_eq_step (j : ℕ) (t : Tor (ellT S.L S.mT)) (μ : Fin 4) : S.bend j t μ = t + SequenceIndex.step S j μ := by
  funext ν
  simp only [SeqDom.bend, SequenceIndex.step, Pi.add_apply, Pi.single_apply]

/-- The bond of `LBond` of a bond `(j, y, μ) ∈ QB`. -/
def toLB (q : ℕ × Site NF × Fin 4) (hq : q ∈ QB S) : SequenceIndex.LBond S :=
  ⟨(q.1, S.ef q.2.1, q.2.2), by
    have hq' := hq
    simp only [QB, mem_filter, mem_product, mem_range, mem_univ, true_and] at hq'
    obtain ⟨hjk, -, hlb, hend, hn1, hn2⟩ := hq'
    rw [bend_eq_step] at hend hn2
    exact ⟨by omega, hlb, hend, hn1, hn2⟩⟩

/-- **The sum over `LBond` as the sum over `QB`.** -/
lemma sum_LBond {M : Type*} [AddCommMonoid M] (F : SequenceIndex.LBond S → M) :
    ∑ c : SequenceIndex.LBond S, F c = ∑ q ∈ QB S, if hq : q ∈ QB S then F (toLB S q hq) else 0 := by
  have hinj := emb_injective (N := SequenceAverages.N0 S) (L := S.L) (k := S.k) (m := S.mT) S.Lpos
    (SequenceAverages.N0_eq S)
  symm
  refine Finset.sum_bij (fun q hq => toLB S q hq) (fun _ _ => mem_univ _) (fun q hq q' hq' h => ?_)
    (fun c _ => ?_) (fun q hq => by simp only [dif_pos hq])
  · have h' := congrArg Subtype.val h
    simp only [toLB, Prod.mk.injEq] at h'
    obtain ⟨h1, h2, h3⟩ := h'
    exact Prod.ext h1 (Prod.ext (hinj h2) h3)
  · obtain ⟨⟨j, t, μ⟩, hc⟩ := c
    obtain ⟨hjk, ht, hend, hn1, hn2⟩ := hc
    obtain ⟨y, rfl⟩ : t ∈ Set.range (Lattices.emb (N := SequenceAverages.N0 S) S.L S.k S.mT) := by
      rw [range_emb S.Lpos (SequenceAverages.N0_eq S)]; exact T_zero_of_mem S ht
    have hlat : InLat S.L j y := (inLat_iff S.Lpos (SequenceAverages.N0_eq S) y).2 ht
    have hq : (j, y, μ) ∈ QB S := by
      simp only [QB, mem_filter, mem_product, mem_range, mem_univ, true_and]
      refine ⟨⟨Nat.lt_succ_of_le hjk, trivial⟩, hlat, ht, ?_, hn1, ?_⟩ <;> rw [bend_eq_step] <;> assumption
    exact ⟨(j, y, μ), hq, rfl⟩

/-- `(QA)(c)` of `SequenceAverages` at the bond of `LBond` of `(j, y, μ) ∈ QB` is `Qat`. -/
lemma Qseq_toLB (U : Config N NF) (A : Fin 4 → Site NF → Matrix (Fin N) (Fin N) ℂ) {q : ℕ × Site NF × Fin 4}
    (hq : q ∈ QB S) :
    SequenceAverages.Qseq S (fun _ => True) (fun W => LogM (W : Matrix (Fin N) (Fin N) ℂ)) U A (toLB S q hq) =
      Qat S U A q := by
  obtain ⟨j, y, μ⟩ := q
  have hq' := hq
  simp only [QB, mem_filter, mem_product, mem_range, mem_univ, true_and] at hq'
  obtain ⟨hjk, hlat, -⟩ := hq'
  rw [SequenceAverages.Qseq_apply, Qat_eq S U A hlat]
  simp only [toLB]
  rw [crd_ef S (by omega) hlat]
  rfl

/-- `⟨B^*, F⟩ = Na^{-4}⟨B^*, F⟩_a`: the sesquilinear pairing of the fine model against the bilinear pairing of
`ConcretePairing` at the adjoint form. -/
lemma pair1V_pairForm1 [NeZero N] {a : ℂ} (ha : a ≠ 0) (B F : Fin 4 → Site NF → Matrix (Fin N) (Fin N) ℂ) :
    pair1V S B F = (N : ℂ) * (a ^ 4)⁻¹ * ConcretePairing.pairForm1 a (Bstar S B) F := by
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  rw [pair1V_tr, ConcretePairing.pairForm1_apply', Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [ConcretePairing.wpair_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [Bstar, ntr]
  field_simp

/-- **The form of the concrete constraint operator** (bridge (B5)): for every configuration `U` and `𝖺`,
`⟨B^*, Q^*𝖺Q C⟩ = 𝖺a₀^{-2}Σ_{c ∈ LBond}L^{2j(c)}tr((QB^*)(c)(QC)(c))` (`QseqStar_spec`, `a_c = L^{j(c)}a₀`). -/
theorem pair1V_constraintOp [NeZero N] (inN : (Matrix (Fin N) (Fin N) ℂ)ˣ → Prop)
    (log : (Matrix (Fin N) (Fin N) ℂ)ˣ → Matrix (Fin N) (Fin N) ℂ)
    (U : Config N NF) (aa : ℂ) (B C : Fin 4 → Site NF → Matrix (Fin N) (Fin N) ℂ) :
    pair1V S B (SequenceAverages.constraintOp S inN log U aa C) =
      aa * ((((SequenceAverages.a0 S : ℝ) : ℂ)) ^ 2)⁻¹ * ∑ c : SequenceIndex.LBond S,
        ((((S.L ^ c.1.1 : ℕ) : ℝ) ^ 2 : ℝ) : ℂ) *
          (SequenceAverages.Qseq S inN log U (Bstar S B) c * SequenceAverages.Qseq S inN log U C c).trace := by
  have ha : (((SequenceAverages.a0 S : ℝ) : ℂ)) ≠ 0 := by exact_mod_cast (SequenceAverages.a0_pos S).ne'
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  rw [pair1V_pairForm1 S ha, ConcretePairing.pairForm1_symm]
  simp only [SequenceAverages.constraintOp, LinearMap.comp_apply]
  rw [SequenceAverages.QseqStar_spec]
  simp only [SequenceIndex.pairLB, CriticalConcrete.pairF, ConcretePairing.wpair_apply, ConcretePairing.mulW,
    LinearMap.coe_mk, AddHom.coe_mk, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hac : (c.ac : ℝ) = (S.L : ℝ) ^ c.1.1 * SequenceAverages.a0 S := rfl
  have hac' : ((c.ac : ℝ) : ℂ) = ((S.L : ℝ) : ℂ) ^ c.1.1 * ((SequenceAverages.a0 S : ℝ) : ℂ) := by
    rw [hac]; push_cast; ring
  simp only [ntr]
  rw [smul_mul_assoc, Matrix.trace_smul, Matrix.trace_mul_comm (SequenceAverages.Qseq S inN log U C c), smul_eq_mul]
  push_cast
  rw [hac']
  field_simp
  simp only [Complex.ofReal_natCast]
  ring

/-- **The concrete constraint form is `QBUc`**: for `inN = True`, `log = LogM`,
`⟨B^*, Q^*𝖺Q C⟩ = 𝖺a₀^{-2}QBUc(U)(B, C)`. -/
theorem pair1V_constraintOp_QBUc [NeZero N] (U : Config N NF) (aa : ℂ)
    (B C : Fin 4 → Site NF → Matrix (Fin N) (Fin N) ℂ) :
    pair1V S B (SequenceAverages.constraintOp S (fun _ => True) (fun W => LogM (W : Matrix (Fin N) (Fin N) ℂ))
      U aa C) = aa * ((((SequenceAverages.a0 S : ℝ) : ℂ)) ^ 2)⁻¹ * QBUc S U B C := by
  rw [pair1V_constraintOp, sum_LBond]
  congr 1
  unfold QBUc
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [dif_pos hq, Qseq_toLB S U _ hq, Qseq_toLB S U _ hq, inner_emb, Matrix.conjTranspose_conjTranspose]
  simp only [toLB]
  push_cast
  ring

lemma pair1V_smul_right (κ : ℂ) (B F : Fin 4 → Site NF → Matrix (Fin N) (Fin N) ℂ) :
    pair1V S B (κ • F) = κ * pair1V S B F := by
  unfold pair1V
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [Pi.smul_apply, emb_smul', inner_smul_right]

/-- **The input `hQ` of `decay_U` for the concrete constraint operator** (`lem:sf-vector-decay`, (C4), with the
bridge (B5)): for `𝖺 ≠ 0` and `Q_𝖺 = a₀²𝖺^{-1}Q(𝐔)^*𝖺Q(𝐔)` at `𝐔 = e^{iX}` (`SequenceAverages.constraintOp`),
`|Re⟨(e^φA)^*, Q_𝖺(e^{-φ}A)⟩ - Σ_ca_c²|(QA)(c)|²| ≤ ε_Q(‖∇A‖² + ‖A‖_w²)` and the same at `φ = 0`, with
`ε_Q = 96L³δ + 576L²Nε̄(4 + ε̄)`, `ε̄ = e^{4L³CK_oα₁L} - 1` (`pair1V_constraintOp_QBUc`, `QBUc_conj`). -/
theorem constraintOp_hQ [NeZero N] (G : GaugeGroup N) (hGc : IsClosed G.mats) (hN : 1 ≤ N) :
    ∃ c Ko C : ℝ, 0 < c ∧ 0 ≤ Ko ∧ 0 ≤ C ∧
      ∀ (hRM : 18 * (S.L : ℝ) ≤ RMS) (hR1 : 1 ≤ S.R * S.L ^ S.mM)
        (hn : ∀ l, 4 * SequenceAverages.hS S + 4 ≤ MultiscaleAverages.nn (SequenceAverages.hS S) S.mT S.k l)
        {X : Fin 4 → Site NF → Matrix (Fin N) (Fin N) ℂ} {α₁ : ℝ} (hX : RegField S X α₁) (hα0 : 0 ≤ α₁)
        (hαc : α₁ * S.L ≤ c) (hKαc : Ko * (α₁ * S.L) ≤ c) {δ : ℝ} (hδ : 0 ≤ δ) (hδL : 16 * S.L * δ ≤ 1)
        (ph : Site NF → ℝ) (hph : ∀ x x', |ph x - ph x'| ≤ δ * S.dF x x') {aa : ℂ} (haa : aa ≠ 0),
      (∀ A, |(pair1V S (expA S ph A) (((((SequenceAverages.a0 S : ℝ) : ℂ)) ^ 2 * aa⁻¹) •
          SequenceAverages.constraintOp S (fun _ => True) (fun W => LogM (W : Matrix (Fin N) (Fin N) ℂ))
            (cfgX X) aa (expA S (fun x => -ph x) A))).re - Qnorm S A| ≤
        (96 * (S.L : ℝ) ^ 3 * δ + 576 * (S.L : ℝ) ^ 2 * N *
          ((Real.exp (4 * (S.L : ℝ) ^ 3 * C * (Ko * (α₁ * S.L))) - 1) *
            (4 + (Real.exp (4 * (S.L : ℝ) ^ 3 * C * (Ko * (α₁ * S.L))) - 1)))) * (gradNorm S A + wnorm S A)) ∧
      (∀ A, |(pair1V S A (((((SequenceAverages.a0 S : ℝ) : ℂ)) ^ 2 * aa⁻¹) •
          SequenceAverages.constraintOp S (fun _ => True) (fun W => LogM (W : Matrix (Fin N) (Fin N) ℂ))
            (cfgX X) aa A)).re - Qnorm S A| ≤
        (96 * (S.L : ℝ) ^ 3 * δ + 576 * (S.L : ℝ) ^ 2 * N *
          ((Real.exp (4 * (S.L : ℝ) ^ 3 * C * (Ko * (α₁ * S.L))) - 1) *
            (4 + (Real.exp (4 * (S.L : ℝ) ^ 3 * C * (Ko * (α₁ * S.L))) - 1)))) * (gradNorm S A + wnorm S A)) := by
  obtain ⟨c, Ko, C, hc, hKo, hC, hd⟩ := QBUc_conj S G hGc hN
  refine ⟨c, Ko, C, hc, hKo, hC, ?_⟩
  intro hRM hR1 hn X α₁ hX hα0 hαc hKαc δ hδ hδL ph hph aa haa
  have ha : (((SequenceAverages.a0 S : ℝ) : ℂ)) ≠ 0 := by exact_mod_cast (SequenceAverages.a0_pos S).ne'
  have hform : ∀ B C' : Fin 4 → Site NF → Matrix (Fin N) (Fin N) ℂ,
      pair1V S B (((((SequenceAverages.a0 S : ℝ) : ℂ)) ^ 2 * aa⁻¹) •
        SequenceAverages.constraintOp S (fun _ => True) (fun W => LogM (W : Matrix (Fin N) (Fin N) ℂ))
          (cfgX X) aa C') = QBUc S (cfgX X) B C' := by
    intro B C'
    rw [pair1V_smul_right, pair1V_constraintOp_QBUc]
    field_simp
  set ε := Real.exp (4 * (S.L : ℝ) ^ 3 * C * (Ko * (α₁ * S.L))) - 1 with hεdef
  have hε : 0 ≤ ε := by
    have h0 : 0 ≤ 4 * (S.L : ℝ) ^ 3 * C * (Ko * (α₁ * S.L)) := by positivity
    have := Real.add_one_le_exp (4 * (S.L : ℝ) ^ 3 * C * (Ko * (α₁ * S.L)))
    simp only [hεdef]; linarith
  have hE0 : 0 ≤ 576 * (S.L : ℝ) ^ 2 * N * (ε * (4 + ε)) := by positivity
  have hEd : 0 ≤ 96 * (S.L : ℝ) ^ 3 * δ := by positivity
  have hext : ∀ A : Fin 4 → Site NF → Matrix (Fin N) (Fin N) ℂ, wnorm S A ≤ gradNorm S A + wnorm S A := fun A => by
    have := gradNorm_nonneg' S A; linarith
  refine ⟨fun A => ?_, fun A => ?_⟩
  · rw [hform]
    exact (hd hRM hR1 hn hX hα0 hαc hKαc hδ hδL ph hph A).trans
      (mul_le_mul_of_nonneg_left (hext A) (by positivity))
  · have h0 := hd hRM hR1 hn hX hα0 hαc hKαc le_rfl (by simp) (fun _ => 0) (fun x x' => by simp) A
    simp only [neg_zero, expA_zero] at h0
    rw [hform]
    refine h0.trans ?_
    simp only [mul_zero, zero_add]
    calc 576 * (S.L : ℝ) ^ 2 * N * (ε * (4 + ε)) * wnorm S A
        ≤ 576 * (S.L : ℝ) ^ 2 * N * (ε * (4 + ε)) * (gradNorm S A + wnorm S A) :=
          mul_le_mul_of_nonneg_left (hext A) hE0
      _ ≤ (96 * (S.L : ℝ) ^ 3 * δ + 576 * (S.L : ℝ) ^ 2 * N * (ε * (4 + ε))) * (gradNorm S A + wnorm S A) :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hEd)
            (add_nonneg (gradNorm_nonneg' S A) (wnorm_nonneg' S A))

end SFBounds
end CoreLean

end
