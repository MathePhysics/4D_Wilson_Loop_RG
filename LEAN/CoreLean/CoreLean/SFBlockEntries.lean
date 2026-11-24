/-
`prop:sf-block` of BALABAN_CORE.tex (`4252790331fd`), the steps "The scaled operator" and "The entries", on the fine
lattice of a sequence of domains (`a₀ = 1`).

* `chain2`: `Σ_{y''}e^{-δd(y, y'') - δ'd(y'', y')} ≤ c₁(½, δ_m)e^{-½δ_m d(y, y')}`, `δ_m = min{δ, δ'}`
  (`eq:chain-summation` with `n = 2`).
* `QpStar`: the transpose of the averages, `(Q'^*μ)(x) = Ad_{W(y, x)}⁻¹μ(y)` for `x ∈ Δ(y)` (the remark after
  `lem:block-average-transports`); `lamZ y' Z = Q'^*(Z1_{y'})`, supported in `Δ(y')`, `|lamZ| ≤ 2√N|Z|`.
* `Gp2_lamZ`: `|(G'²λ_Z)(x)| ≤ 2√NC_v²L⁴c₁(½, (7/8)δ)a_y²a_{y'}²e^{-(7/16)δd(y, y')}|Z|` for `x ∈ Δ(y)`, by the bound (iv)
  of `G'` twice, `G'λ = Σ_{y''}G'(1_{Δ(y'')}G'λ)`, `eq:sf-scale-shift` and `chain2`.
-/
import CoreLean.SFScalar

open Finset Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean
namespace SFBounds

open Lattices SeqDom Blocks SmallFieldBlocks SFBox SFBox.SeqDomBox SFLocal LocalLaplacian InteriorSchauder
  SmallFieldDecay SmallFieldCoercivity SequenceOperators CompressedInverse

variable (S : SeqDom) {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ
local notation "NF" => SequenceAverages.N0 S
local notation "RMS" => ((S.R * S.L ^ S.mM : ℕ) : ℝ)
set_option quotPrecheck false in
local notation "jj" => (S.toDomSeq).sc

/-- **`eq:chain-summation` with `n = 2`** over the fine determining set. -/
theorem chain2 {δ δ' : ℝ} (hδ : 0 < δ) (hδ' : 0 < δ') (hRM : (S.toContSeq).r1 (1 / 2) (min δ δ') ≤ RMS)
    {y y' : Site NF} (hy : y ∈ detB S.toDomSeq) :
    ∑ y'' ∈ detB S.toDomSeq, Real.exp (-(δ * S.dF y y'')) * Real.exp (-(δ' * S.dF y'' y')) ≤
      (S.toContSeq).c1 (1 / 2) (min δ δ') * Real.exp (-(1 / 2 * min δ δ' * S.dF y y')) := by
  set m := min δ δ'
  have hm : 0 < m := lt_min hδ hδ'
  have hsum := S.summation_fine (α := 1 / 2) (by norm_num) hm hRM hy
  have hterm : ∀ y'' ∈ detB S.toDomSeq, Real.exp (-(δ * S.dF y y'')) * Real.exp (-(δ' * S.dF y'' y')) ≤
      Real.exp (-(1 / 2 * m * S.dF y y')) * Real.exp (-(1 / 2 * m * S.dF y y'')) := by
    intro y'' _
    rw [← Real.exp_add, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have ht := S.dF_triangle y y'' y'
    have h1 := S.dF_nonneg y y''
    have h2 := S.dF_nonneg y'' y'
    have hmδ : m ≤ δ := min_le_left _ _
    have hmδ' : m ≤ δ' := min_le_right _ _
    nlinarith [mul_le_mul_of_nonneg_right hmδ h1, mul_le_mul_of_nonneg_right hmδ' h2]
  calc _ ≤ ∑ y'' ∈ detB S.toDomSeq, Real.exp (-(1 / 2 * m * S.dF y y')) * Real.exp (-(1 / 2 * m * S.dF y y'')) :=
        sum_le_sum hterm
    _ = Real.exp (-(1 / 2 * m * S.dF y y')) * ∑ y'' ∈ detB S.toDomSeq, Real.exp (-(1 / 2 * m * S.dF y y'')) := by
        rw [mul_sum]
    _ ≤ Real.exp (-(1 / 2 * m * S.dF y y')) * (S.toContSeq).c1 (1 / 2) m := by gcongr
    _ = _ := by ring

/-- The transpose of the averages: `(Q'^*μ)(x) = Ad_{W(y(x), x)}⁻¹μ(y(x))`. -/
def QpStar (W : Site NF → Site NF → GLN) (μ : Site NF → Mat) : Site NF → Mat :=
  fun x => Ad (W (bc S.toDomSeq x) x)⁻¹ (μ (bc S.toDomSeq x))

/-- `λ_Z = Q'^*(Z1_{y'})`. -/
def lamZ (W : Site NF → Site NF → GLN) (y' : Site NF) (Z : Mat) : Site NF → Mat :=
  QpStar S W fun y => if y = y' then Z else 0

lemma lamZ_supp (W : Site NF → Site NF → GLN) {y' : Site NF} (hy' : y' ∈ detB S.toDomSeq) (Z : Mat) :
    ∀ x', x' ∉ Blk S.toDomSeq (jj y') y' → lamZ S W y' Z x' = 0 := by
  intro x' hx'
  simp only [lamZ, QpStar]
  rw [if_neg]
  · simp [Ad]
  · intro h
    apply hx'
    rw [← h]
    exact mem_blk_bc S x'

lemma lamZ_bound [NeZero N] {W : Site NF → Site NF → GLN} (hW : WBound S W) {y' : Site NF}
    (hy' : y' ∈ detB S.toDomSeq) (Z : Mat) (x' : Site NF) :
    hs (lamZ S W y' Z x') ≤ 2 * Real.sqrt N * hs Z := by
  by_cases h : bc S.toDomSeq x' = y'
  · simp only [lamZ, QpStar, h, if_true]
    have hx : x' ∈ Blk S.toDomSeq (jj y') y' := by rw [← h]; exact mem_blk_bc S x'
    exact (hW y' hy' x' hx Z).2
  · rw [lamZ_supp S W hy' Z x' (fun hm => h ((sc_mem_blk S.toDomSeq hy' hm).2))]
    simp [hs, hs2, ntr]; positivity

/-- The restriction of a `0`-form to a block. -/
def onBlk (y : Site NF) (v : Site NF → Mat) : Site NF → Mat :=
  fun x => if x ∈ Blk S.toDomSeq (jj y) y then v x else 0

lemma sum_onBlk (v : Site NF → Mat) : ∑ y ∈ detB S.toDomSeq, onBlk S y v = v := by
  funext x
  rw [Finset.sum_apply]
  simp only [onBlk]
  rw [Finset.sum_eq_single (bc S.toDomSeq x)]
  · rw [if_pos (mem_blk_bc S x)]
  · intro y hy hne
    rw [if_neg]
    intro hx
    exact hne (sc_mem_blk S.toDomSeq hy hx).2.symm
  · intro h; exact absurd (bc_mem_detB S x) h

/-- The number `C_{G'²} = 2√NC_v²L⁴c₁(½, ¾δ)`. -/
def CG2 (S : SeqDom) (N : ℕ) (δ : ℝ) : ℝ :=
  2 * Real.sqrt N * Cv S δ (Csc S N) (4 * N * (S.L : ℝ) ^ 4) ^ 2 * (S.L : ℝ) ^ (4 : ℝ) *
    (S.toContSeq).c1 (1 / 2) (3 / 4 * δ)

namespace ScalarHyp

variable {S} {X : Fin 4 → Site (SequenceAverages.N0 S) → Matrix (Fin N) (Fin N) ℂ} {α₁ : ℝ}
  {W : Site (SequenceAverages.N0 S) → Site (SequenceAverages.N0 S) → (Matrix (Fin N) (Fin N) ℂ)ˣ} {η : ℝ}
  {ΩD : Set (Site (SequenceAverages.N0 S))} {δ : ℝ}
  (H : ScalarHyp S X α₁ W η ΩD δ)
include H

lemma Cv_nonneg : 0 ≤ Cv S δ (Csc S N) (4 * N * (S.L : ℝ) ^ 4) := by
  have := H.hδ0
  have hc1 : 0 ≤ (S.toContSeq).c1 (1 / 2) δ := by unfold Summation.ContSeq.c1; positivity
  unfold Cv C2 CTh CF Ksf Csc; positivity

/-- **`|(G'²λ_Z)(x)| ≤ C_{G'²}a_y²a_{y'}²e^{-(3/8)δd(y, y')}|Z|`** for `x ∈ Δ(y)`. -/
theorem Gp2_lamZ [NeZero N] (hRMc : (S.toContSeq).r1 (1 / 2) (3 / 4 * δ) ≤ RMS) {y y' x : Site NF}
    (hy : y ∈ detB S.toDomSeq) (hy' : y' ∈ detB S.toDomSeq) (hx : x ∈ Blk S.toDomSeq (jj y) y) (Z : Mat) :
    hs (Gp' S.toDomSeq (cfgX X) W ΩD (Gp' S.toDomSeq (cfgX X) W ΩD (lamZ S W y' Z)) x) ≤
      CG2 S N δ * (S.L : ℝ) ^ (2 * jj y) * (S.L : ℝ) ^ (2 * jj y') * Real.exp (-(3 / 8 * δ * S.dF y y')) * hs Z := by
  set G := Gp' S.toDomSeq (cfgX X) W ΩD
  set v := G (lamZ S W y' Z)
  have hL : (3 : ℝ) ≤ S.L := by exact_mod_cast S.three_le_L
  have hδ := H.hδ0
  have hCv := H.Cv_nonneg
  have hZ := hs_nonneg (N := N) Z
  set Cv' := Cv S δ (Csc S N) (4 * N * (S.L : ℝ) ^ 4)
  -- the first application
  have hv : ∀ y'' ∈ detB S.toDomSeq, ∀ x'', hs (onBlk S y'' v x'') ≤
      Cv' * Real.exp (-(7 / 8 * δ * S.dF y'' y')) * ((S.L : ℝ) ^ (2 * jj y'') * (2 * Real.sqrt N * hs Z)) := by
    intro y'' hy'' x''
    simp only [onBlk]
    split_ifs with hx''
    · exact H.values hy'' hy' hx'' (by positivity) (lamZ_supp S W hy' Z) (lamZ_bound S H.hW hy' Z)
    · simp [hs, hs2, ntr]; positivity
  -- the second application, block by block
  have hsplit : G v = ∑ y'' ∈ detB S.toDomSeq, G (onBlk S y'' v) := by
    rw [← map_sum, sum_onBlk]
  have hterm : ∀ y'' ∈ detB S.toDomSeq, hs (G (onBlk S y'' v) x) ≤
      Cv' * Real.exp (-(7 / 8 * δ * S.dF y y'')) * ((S.L : ℝ) ^ (2 * jj y) *
        (Cv' * Real.exp (-(7 / 8 * δ * S.dF y'' y')) * ((S.L : ℝ) ^ (2 * jj y'') * (2 * Real.sqrt N * hs Z)))) := by
    intro y'' hy''
    have := H.values hy hy'' hx (Λ := Cv' * Real.exp (-(7 / 8 * δ * S.dF y'' y')) *
      ((S.L : ℝ) ^ (2 * jj y'') * (2 * Real.sqrt N * hs Z))) (by positivity)
      (fun x'' hx'' => by simp only [onBlk]; rw [if_neg hx''])
      (hv y'' hy'')
    exact this.trans (le_of_eq (by ring))
  have hsum : hs (G v x) ≤ ∑ y'' ∈ detB S.toDomSeq, Cv' * Real.exp (-(7 / 8 * δ * S.dF y y'')) *
      ((S.L : ℝ) ^ (2 * jj y) * (Cv' * Real.exp (-(7 / 8 * δ * S.dF y'' y')) *
        ((S.L : ℝ) ^ (2 * jj y'') * (2 * Real.sqrt N * hs Z)))) := by
    rw [hsplit, Finset.sum_apply]
    exact (RegularAverages.hs_sum_le _ _).trans (sum_le_sum hterm)
  -- the scale shift `a_{y''}² ≤ L⁴e^{δd(y', y'')/8}a_{y'}²`
  have hsh : ∀ y'', (S.L : ℝ) ^ (2 * jj y'') ≤
      (S.L : ℝ) ^ (4 : ℝ) * Real.exp (δ / 8 * S.dF y'' y') * (S.L : ℝ) ^ (2 * jj y') := by
    intro y''
    have h := S.scale_shift hδ H.hRMs (σ := ((2 : ℕ) : ℝ)) (by norm_num) y' y''
    rw [Real.rpow_natCast, Real.rpow_natCast, ← pow_mul, ← pow_mul, mul_comm (jj y'') 2, mul_comm (jj y') 2,
      S.dF_comm y' y''] at h
    exact h
  have hchain := chain2 S (δ := 7 / 8 * δ) (δ' := 3 / 4 * δ) (by positivity) (by positivity)
    (by rw [show min (7 / 8 * δ) (3 / 4 * δ) = 3 / 4 * δ from min_eq_right (by linarith)]; exact hRMc) hy (y' := y')
  rw [show min (7 / 8 * δ) (3 / 4 * δ) = 3 / 4 * δ from min_eq_right (by linarith)] at hchain
  have hterm2 : ∀ y'' ∈ detB S.toDomSeq, Cv' * Real.exp (-(7 / 8 * δ * S.dF y y'')) *
      ((S.L : ℝ) ^ (2 * jj y) * (Cv' * Real.exp (-(7 / 8 * δ * S.dF y'' y')) *
        ((S.L : ℝ) ^ (2 * jj y'') * (2 * Real.sqrt N * hs Z)))) ≤
      2 * Real.sqrt N * Cv' ^ 2 * (S.L : ℝ) ^ (4 : ℝ) * (S.L : ℝ) ^ (2 * jj y) * (S.L : ℝ) ^ (2 * jj y') * hs Z *
        (Real.exp (-(7 / 8 * δ * S.dF y y'')) * Real.exp (-(3 / 4 * δ * S.dF y'' y'))) := by
    intro y'' _
    have h1 := hsh y''
    have hexp : Real.exp (-(7 / 8 * δ * S.dF y'' y')) * Real.exp (δ / 8 * S.dF y'' y') =
        Real.exp (-(3 / 4 * δ * S.dF y'' y')) := by rw [← Real.exp_add]; ring_nf
    calc Cv' * Real.exp (-(7 / 8 * δ * S.dF y y'')) * ((S.L : ℝ) ^ (2 * jj y) *
          (Cv' * Real.exp (-(7 / 8 * δ * S.dF y'' y')) * ((S.L : ℝ) ^ (2 * jj y'') * (2 * Real.sqrt N * hs Z))))
        ≤ Cv' * Real.exp (-(7 / 8 * δ * S.dF y y'')) * ((S.L : ℝ) ^ (2 * jj y) *
          (Cv' * Real.exp (-(7 / 8 * δ * S.dF y'' y')) * (((S.L : ℝ) ^ (4 : ℝ) * Real.exp (δ / 8 * S.dF y'' y') *
            (S.L : ℝ) ^ (2 * jj y')) * (2 * Real.sqrt N * hs Z)))) := by gcongr
      _ = 2 * Real.sqrt N * Cv' ^ 2 * (S.L : ℝ) ^ (4 : ℝ) * (S.L : ℝ) ^ (2 * jj y) * (S.L : ℝ) ^ (2 * jj y') * hs Z *
          (Real.exp (-(7 / 8 * δ * S.dF y y'')) * (Real.exp (-(7 / 8 * δ * S.dF y'' y')) *
            Real.exp (δ / 8 * S.dF y'' y'))) := by ring
      _ = _ := by rw [hexp]
  refine hsum.trans ((sum_le_sum hterm2).trans ?_)
  rw [← mul_sum]
  have hK : 0 ≤ 2 * Real.sqrt N * Cv' ^ 2 * (S.L : ℝ) ^ (4 : ℝ) * (S.L : ℝ) ^ (2 * jj y) *
      (S.L : ℝ) ^ (2 * jj y') * hs Z := by positivity
  calc _ ≤ 2 * Real.sqrt N * Cv' ^ 2 * (S.L : ℝ) ^ (4 : ℝ) * (S.L : ℝ) ^ (2 * jj y) * (S.L : ℝ) ^ (2 * jj y') *
        hs Z * ((S.toContSeq).c1 (1 / 2) (3 / 4 * δ) * Real.exp (-(1 / 2 * (3 / 4 * δ) * S.dF y y'))) :=
        mul_le_mul_of_nonneg_left hchain hK
    _ = _ := by
        rw [show 1 / 2 * (3 / 4 * δ) * S.dF y y' = 3 / 8 * δ * S.dF y y' by ring]
        unfold CG2; ring

end ScalarHyp

/-- The average of a form bounded by `M` on the block is bounded by `2√NM`. -/
lemma avgW_le [NeZero N] {W : Site NF → Site NF → GLN} (hW : WBound S W) {y : Site NF}
    (hy : y ∈ detB S.toDomSeq) {v : Site NF → Mat} {M : ℝ} (hv : ∀ x ∈ Blk S.toDomSeq (jj y) y, hs (v x) ≤ M) :
    hs (avgW S.toDomSeq W y v) ≤ 2 * Real.sqrt N * M := by
  have hL : (0 : ℝ) < S.L := by exact_mod_cast S.Lpos
  rw [avgW_blk S.toDomSeq W hy v, RegularAverages.hs_smul]
  simp only [toDomSeq_L]
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hsum : hs (∑ x ∈ Blk S.toDomSeq (jj y) y, Ad (W y x) (v x)) ≤
      ∑ _x ∈ Blk S.toDomSeq (jj y) y, 2 * Real.sqrt N * M :=
    (RegularAverages.hs_sum_le _ _).trans (sum_le_sum fun x hx =>
      ((hW y hy x hx) (v x)).1.trans (mul_le_mul_of_nonneg_left (hv x hx) (by positivity)))
  rw [sum_const, nsmul_eq_mul, card_Blk S hy] at hsum
  calc ((S.L : ℝ) ^ (4 * jj y))⁻¹ * hs (∑ x ∈ Blk S.toDomSeq (jj y) y, Ad (W y x) (v x))
      ≤ ((S.L : ℝ) ^ (4 * jj y))⁻¹ * ((S.L : ℝ) ^ (4 * jj y) * (2 * Real.sqrt N * M)) := by gcongr
    _ = 2 * Real.sqrt N * M := by field_simp

/-- The entries of the scaled operator, `T̂[y, y']Z = a_{y'}⁻⁴(Q'G'²λ_Z)(y)`. -/
def That (X : Fin 4 → Site NF → Mat) (W : Site NF → Site NF → GLN) (ΩD : Set (Site NF)) (y y' : Site NF)
    (Z : Mat) : Mat :=
  ((((S.L : ℝ) ^ (4 * jj y')) : ℝ) : ℂ)⁻¹ • avgW S.toDomSeq W y
    (Gp' S.toDomSeq (cfgX X) W ΩD (Gp' S.toDomSeq (cfgX X) W ΩD (lamZ S W y' Z)))

/-- The number `κ = 2√NC_{G'²}L⁴` of `eq:sf-block-entries`. -/
def kappaB (S : SeqDom) (N : ℕ) (δ : ℝ) : ℝ := 2 * Real.sqrt N * CG2 S N δ * (S.L : ℝ) ^ (4 : ℝ)

namespace ScalarHyp

variable {S} {X : Fin 4 → Site (SequenceAverages.N0 S) → Matrix (Fin N) (Fin N) ℂ} {α₁ : ℝ}
  {W : Site (SequenceAverages.N0 S) → Site (SequenceAverages.N0 S) → (Matrix (Fin N) (Fin N) ℂ)ˣ} {η : ℝ}
  {ΩD : Set (Site (SequenceAverages.N0 S))} {δ : ℝ}
  (H : ScalarHyp S X α₁ W η ΩD δ)
include H

/-- **`eq:sf-block-entries`**: `|T̂[y, y']Z| ≤ κe^{-δ_T d(y, y')}|Z|`, `δ_T = δ/4`. -/
theorem That_bound [NeZero N] (hRMc : (S.toContSeq).r1 (1 / 2) (3 / 4 * δ) ≤ RMS) {y y' : Site NF}
    (hy : y ∈ detB S.toDomSeq) (hy' : y' ∈ detB S.toDomSeq) (Z : Mat) :
    hs (That S X W ΩD y y' Z) ≤ kappaB S N δ * Real.exp (-(1 / 4 * δ * S.dF y y')) * hs Z := by
  have hL : (3 : ℝ) ≤ S.L := by exact_mod_cast S.three_le_L
  have hL0 : (0 : ℝ) < S.L := by linarith
  have hδ := H.hδ0
  have hZ := hs_nonneg (N := N) Z
  have hc1 : 0 ≤ (S.toContSeq).c1 (1 / 2) (3 / 4 * δ) := by unfold Summation.ContSeq.c1; positivity
  have hCG : 0 ≤ CG2 S N δ := by unfold CG2; have := H.Cv_nonneg; positivity
  have havg := avgW_le S H.hW hy (v := Gp' S.toDomSeq (cfgX X) W ΩD (Gp' S.toDomSeq (cfgX X) W ΩD (lamZ S W y' Z)))
    (fun x hx => H.Gp2_lamZ hRMc hy hy' hx Z)
  simp only [That]
  rw [RegularAverages.hs_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  -- `(a_y/a_{y'})² ≤ L⁴e^{δd/8}`
  have hsh := S.scale_shift hδ H.hRMs (σ := ((2 : ℕ) : ℝ)) (by norm_num) y' y
  rw [Real.rpow_natCast, Real.rpow_natCast, ← pow_mul, ← pow_mul, mul_comm (jj y) 2, mul_comm (jj y') 2,
    S.dF_comm y' y] at hsh
  have e4 : (S.L : ℝ) ^ (4 * jj y') = (S.L : ℝ) ^ (2 * jj y') * (S.L : ℝ) ^ (2 * jj y') := by
    rw [← pow_add]; ring_nf
  have hp : (0 : ℝ) < (S.L : ℝ) ^ (2 * jj y') := by positivity
  have hexp : Real.exp (δ / 8 * S.dF y y') * Real.exp (-(3 / 8 * δ * S.dF y y')) =
      Real.exp (-(1 / 4 * δ * S.dF y y')) := by rw [← Real.exp_add]; ring_nf
  calc ((S.L : ℝ) ^ (4 * jj y'))⁻¹ * hs (avgW S.toDomSeq W y
        (Gp' S.toDomSeq (cfgX X) W ΩD (Gp' S.toDomSeq (cfgX X) W ΩD (lamZ S W y' Z))))
      ≤ ((S.L : ℝ) ^ (4 * jj y'))⁻¹ * (2 * Real.sqrt N * (CG2 S N δ * (S.L : ℝ) ^ (2 * jj y) *
          (S.L : ℝ) ^ (2 * jj y') * Real.exp (-(3 / 8 * δ * S.dF y y')) * hs Z)) := by gcongr
    _ = 2 * Real.sqrt N * CG2 S N δ * ((S.L : ℝ) ^ (2 * jj y) / (S.L : ℝ) ^ (2 * jj y')) *
          Real.exp (-(3 / 8 * δ * S.dF y y')) * hs Z := by
        rw [e4]; field_simp
    _ ≤ 2 * Real.sqrt N * CG2 S N δ * ((S.L : ℝ) ^ (4 : ℝ) * Real.exp (δ / 8 * S.dF y y')) *
          Real.exp (-(3 / 8 * δ * S.dF y y')) * hs Z := by
        gcongr
        rw [div_le_iff₀ hp]; exact hsh
    _ = _ := by rw [← hexp]; unfold kappaB; ring

end ScalarHyp

end SFBounds
end CoreLean

end
