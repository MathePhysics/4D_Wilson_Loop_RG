/-
`prop:sf-bounds` of BALABAN_CORE.tex (`4252790331fd`), the step "The weighted bound", second part: the norms of `u` on
the blocks and the term `eq:sf-far-term`, on the fine lattice (`a₀ = 1`).

* `sc_of_mem_blk`, `card_Blk`: the sites of a block `Δ(y)` have the scale `j(y)`, and the block has `a_{j(y)}⁴` sites.
* `block_L2_le`: for a weight `φ` which is `δ`-Lipschitz in `d`, `‖u‖²_{2,Δ(y'')} ≤ a_{y''}²e^{4δ}e^{-2φ(y'')}‖e^φu‖_w²`;
  `block_L1_le`: `Σ_{x' ∈ Δ(y'')}|u(x')| ≤ a_{y''}²‖u‖_{2,Δ(y'')}` (Cauchy–Schwarz).
* `far_sum` (`eq:sf-far-term`): `Σ_{x'}a_{j(x')}⁻⁴e^{-2δd(z, x')}|u(x')| ≤ e^{7δ}L⁴c₁(½, δ)a_{j(z)}⁻¹e^{-φ(z)}‖e^φu‖_w` for
  `RM ≥ max{r₁(½, δ), 32δ⁻¹ log L}`; with the hypothesis on `𝓕` of `prop:sf-bounds` this is
  `|(𝓕u)(z)| ≤ C_𝓕a_{j(z)}⁻³e^{-φ(z)}M₀`.
-/
import CoreLean.SFBoundsSetup

open Finset Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean
namespace SFBounds

open Lattices SeqDom Blocks SmallFieldBlocks SFBox

variable (S : SeqDom) {N m : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "NF" => SequenceAverages.N0 S
local notation "RMS" => ((S.R * S.L ^ S.mM : ℕ) : ℝ)
set_option quotPrecheck false in
local notation "jj" => (S.toDomSeq).sc

/-- The sites of a block `Δ(y)`, `y ∈ 𝐁`, have the scale `j(y)`. -/
lemma sc_of_mem_blk {y x : Site NF} (hy : y ∈ detB S.toDomSeq) (hx : x ∈ Blk S.toDomSeq (jj y) y) :
    jj x = jj y := by
  obtain ⟨x0, -, rfl⟩ := Finset.mem_image.1 hy
  have hcen : cen S.L (jj (bc S.toDomSeq x0)) x = bc S.toDomSeq x0 := (Finset.mem_filter.1 hx).2
  have h := (fiber_eq S.toDomSeq x0 x).2 hcen
  rw [← sc_bc S.toDomSeq x, h]

/-- A site lies in the block of `bc x`. -/
lemma mem_blk_bc (x : Site NF) : x ∈ Blk S.toDomSeq (jj (bc S.toDomSeq x)) (bc S.toDomSeq x) := by
  refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
  rw [sc_bc]; rfl

lemma bc_mem_detB (x : Site NF) : bc S.toDomSeq x ∈ detB S.toDomSeq := Finset.mem_image_of_mem _ (Finset.mem_univ x)

/-- **A block `Δ(y)` has `a_{j(y)}⁴` sites.** -/
lemma card_Blk {y : Site NF} (hy : y ∈ detB S.toDomSeq) :
    ((Blk S.toDomSeq (jj y) y).card : ℝ) = (S.L : ℝ) ^ (4 * jj y) := by
  have h := SmallFieldBlocks.sum_Blk (S := S.toDomSeq) (jj y) ((S.toDomSeq).sc_le y) ((S.mem_detB_iff_inLat y).1 hy) (fun _ => (1 : ℕ))
  simp only [sum_const, smul_eq_mul, mul_one, DiscretePoincare.card_box] at h
  rw [h]; push_cast; rw [← pow_mul, mul_comm]; rfl

/-- **The norm of `u` on a block**: `Σ_{x' ∈ Δ(y)}|u(x')|² ≤ a_y²e^{4δ}e^{-2φ(y)}‖e^φu‖_w²`. -/
theorem block_L2_le {δ : ℝ} (hδ : 0 ≤ δ) {ph : Site NF → ℝ} (hph : ∀ x x', |ph x - ph x'| ≤ δ * S.dF x x')
    (u : Fin m → Site NF → Mat) {y : Site NF} (hy : y ∈ detB S.toDomSeq) :
    ∑ x ∈ Blk S.toDomSeq (jj y) y, nsq (fun k => u k x) ≤
      (S.L : ℝ) ^ (2 * jj y) * Real.exp (4 * δ) * Real.exp (-2 * ph y) * wN S (eF S ph u) := by
  have hL : (0 : ℝ) < S.L := by exact_mod_cast S.Lpos
  have hterm : ∀ x ∈ Blk S.toDomSeq (jj y) y, nsq (fun k => u k x) ≤
      (S.L : ℝ) ^ (2 * jj y) * Real.exp (4 * δ) * Real.exp (-2 * ph y) *
        (((S.L : ℝ) ^ (2 * jj x))⁻¹ * nsq fun k => eF S ph u k x) := by
    intro x hx
    have hsc := sc_of_mem_blk S hy hx
    have hd : S.dF y x ≤ 2 := ENNReal.toReal_le_of_le_ofReal (by norm_num) (S.wdist_block_le hy hx)
    rw [nsq_eF, hsc]
    have hp : (S.L : ℝ) ^ (2 * jj y) ≠ 0 := pow_ne_zero _ hL.ne'
    have e : (S.L : ℝ) ^ (2 * jj y) * Real.exp (4 * δ) * Real.exp (-2 * ph y) *
        (((S.L : ℝ) ^ (2 * jj y))⁻¹ * (Real.exp (2 * ph x) * nsq fun k => u k x)) =
        Real.exp (4 * δ - 2 * ph y + 2 * ph x) * nsq fun k => u k x := by
      have ee : Real.exp (4 * δ - 2 * ph y + 2 * ph x) =
          Real.exp (4 * δ) * Real.exp (-2 * ph y) * Real.exp (2 * ph x) := by
        rw [← Real.exp_add, ← Real.exp_add]; ring_nf
      rw [ee, show (S.L : ℝ) ^ (2 * jj y) * Real.exp (4 * δ) * Real.exp (-2 * ph y) *
          (((S.L : ℝ) ^ (2 * jj y))⁻¹ * (Real.exp (2 * ph x) * nsq fun k => u k x)) =
          ((S.L : ℝ) ^ (2 * jj y) * ((S.L : ℝ) ^ (2 * jj y))⁻¹) * Real.exp (4 * δ) * Real.exp (-2 * ph y) *
            Real.exp (2 * ph x) * nsq fun k => u k x by ring, mul_inv_cancel₀ hp, one_mul]
    rw [e]
    have h1 : 0 ≤ 4 * δ - 2 * ph y + 2 * ph x := by
      have := (abs_le.1 (hph x y)).1
      rw [S.dF_comm] at this
      nlinarith
    have h2 := nsq_nonneg fun k => u k x
    calc nsq (fun k => u k x) = 1 * nsq (fun k => u k x) := (one_mul _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right (Real.one_le_exp h1) h2
  refine (sum_le_sum hterm).trans ?_
  rw [← mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun x _ _ => mul_nonneg (by positivity) (nsq_nonneg _)

/-- **Cauchy–Schwarz on a block**: `Σ_{x' ∈ Δ(y)}|u(x')| ≤ a_y²(Σ_{x' ∈ Δ(y)}|u(x')|²)^{1/2}`. -/
theorem block_L1_le (u : Fin m → Site NF → Mat) {y : Site NF} (hy : y ∈ detB S.toDomSeq) :
    ∑ x ∈ Blk S.toDomSeq (jj y) y, Real.sqrt (nsq fun k => u k x) ≤
      (S.L : ℝ) ^ (2 * jj y) * Real.sqrt (∑ x ∈ Blk S.toDomSeq (jj y) y, nsq fun k => u k x) := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Blk S.toDomSeq (jj y) y) (fun _ => (1 : ℝ))
    (fun x => Real.sqrt (nsq fun k => u k x))
  simp only [one_mul, one_pow, sum_const, nsmul_eq_mul, mul_one] at hcs
  have hsq : ∀ x ∈ Blk S.toDomSeq (jj y) y, Real.sqrt (nsq fun k => u k x) ^ 2 = nsq fun k => u k x :=
    fun x _ => Real.sq_sqrt (nsq_nonneg _)
  rw [sum_congr rfl hsq, card_Blk S hy] at hcs
  have hS : 0 ≤ ∑ x ∈ Blk S.toDomSeq (jj y) y, nsq fun k => u k x := sum_nonneg fun _ _ => nsq_nonneg _
  have e : (S.L : ℝ) ^ (2 * jj y) * Real.sqrt (∑ x ∈ Blk S.toDomSeq (jj y) y, nsq fun k => u k x) =
      Real.sqrt ((S.L : ℝ) ^ (4 * jj y) * ∑ x ∈ Blk S.toDomSeq (jj y) y, nsq fun k => u k x) := by
    rw [Real.sqrt_mul (by positivity), show (S.L : ℝ) ^ (4 * jj y) = ((S.L : ℝ) ^ (2 * jj y)) ^ 2 by
      rw [← pow_mul]; ring_nf, Real.sqrt_sq (by positivity)]
  rw [e]
  exact Real.le_sqrt_of_sq_le hcs

/-- **`eq:sf-far-term`**: `Σ_{x'}a_{j(x')}⁻⁴e^{-2δd(z, x')}|u(x')| ≤ e^{7δ}L⁴c₁(½, δ)a_{j(z)}⁻¹e^{-φ(z)}‖e^φu‖_w`. -/
theorem far_sum {δ : ℝ} (hδ : 0 < δ) (hRM1 : (S.toContSeq).r1 (1 / 2) δ ≤ RMS)
    (hRM2 : 32 * Real.log S.L / δ ≤ RMS) {ph : Site NF → ℝ} (hph : ∀ x x', |ph x - ph x'| ≤ δ * S.dF x x')
    (u : Fin m → Site NF → Mat) (z : Site NF) :
    ∑ x', ((S.L : ℝ) ^ (4 * jj x'))⁻¹ * Real.exp (-(2 * δ * S.dF z x')) * Real.sqrt (nsq fun k => u k x') ≤
      Real.exp (7 * δ) * (S.L : ℝ) ^ (4 : ℝ) * (S.toContSeq).c1 (1 / 2) δ * ((S.L : ℝ) ^ jj z)⁻¹ *
        Real.exp (-ph z) * Real.sqrt (wN S (eF S ph u)) := by
  have hL : (0 : ℝ) < S.L := by exact_mod_cast S.Lpos
  set M := Real.sqrt (wN S (eF S ph u))
  have hM : 0 ≤ M := Real.sqrt_nonneg _
  rw [sum_blocks S.toDomSeq]
  -- the bound of the terms of one block
  have hblock : ∀ y ∈ detB S.toDomSeq,
      ∑ x' ∈ Blk S.toDomSeq (jj y) y, ((S.L : ℝ) ^ (4 * jj x'))⁻¹ * Real.exp (-(2 * δ * S.dF z x')) *
        Real.sqrt (nsq fun k => u k x') ≤
      Real.exp (6 * δ) * ((S.L : ℝ) ^ jj y)⁻¹ * Real.exp (-(δ * S.dF z y)) * Real.exp (-ph z) * M := by
    intro y hy
    have hd2 : ∀ x' ∈ Blk S.toDomSeq (jj y) y, Real.exp (-(2 * δ * S.dF z x')) ≤
        Real.exp (4 * δ) * Real.exp (-(2 * δ * S.dF z y)) := by
      intro x' hx'
      have hd : S.dF y x' ≤ 2 := ENNReal.toReal_le_of_le_ofReal (by norm_num) (S.wdist_block_le hy hx')
      have ht := S.dF_triangle z x' y
      rw [S.dF_comm x' y] at ht
      rw [← Real.exp_add]
      exact Real.exp_le_exp.2 (by nlinarith)
    have h1 : ∑ x' ∈ Blk S.toDomSeq (jj y) y, ((S.L : ℝ) ^ (4 * jj x'))⁻¹ * Real.exp (-(2 * δ * S.dF z x')) *
        Real.sqrt (nsq fun k => u k x') ≤ ((S.L : ℝ) ^ (4 * jj y))⁻¹ * (Real.exp (4 * δ) *
          Real.exp (-(2 * δ * S.dF z y))) * ∑ x' ∈ Blk S.toDomSeq (jj y) y, Real.sqrt (nsq fun k => u k x') := by
      rw [mul_sum]
      refine sum_le_sum fun x' hx' => ?_
      rw [sc_of_mem_blk S hy hx']
      gcongr
      exact hd2 x' hx'
    have h2 := block_L1_le S u hy
    have h3 := block_L2_le S hδ.le hph u hy
    have h3' : Real.sqrt (∑ x ∈ Blk S.toDomSeq (jj y) y, nsq fun k => u k x) ≤
        (S.L : ℝ) ^ jj y * Real.exp (2 * δ) * Real.exp (-ph y) * M := by
      calc Real.sqrt (∑ x ∈ Blk S.toDomSeq (jj y) y, nsq fun k => u k x)
          ≤ Real.sqrt ((S.L : ℝ) ^ (2 * jj y) * Real.exp (4 * δ) * Real.exp (-2 * ph y) * wN S (eF S ph u)) :=
            Real.sqrt_le_sqrt h3
        _ = (S.L : ℝ) ^ jj y * Real.exp (2 * δ) * Real.exp (-ph y) * M := by
            have e : (S.L : ℝ) ^ (2 * jj y) * Real.exp (4 * δ) * Real.exp (-2 * ph y) =
                ((S.L : ℝ) ^ jj y * Real.exp (2 * δ) * Real.exp (-ph y)) ^ 2 := by
              rw [mul_pow, mul_pow, ← Real.exp_nat_mul, ← Real.exp_nat_mul, pow_mul']; push_cast; ring_nf
            rw [e, Real.sqrt_mul (pow_two_nonneg _), Real.sqrt_sq (by positivity)]
    have hphy : -ph y ≤ δ * S.dF z y - ph z := by
      have := (abs_le.1 (hph z y)).2; linarith
    have h4 : Real.exp (-ph y) ≤ Real.exp (δ * S.dF z y) * Real.exp (-ph z) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by linarith)
    calc _ ≤ ((S.L : ℝ) ^ (4 * jj y))⁻¹ * (Real.exp (4 * δ) * Real.exp (-(2 * δ * S.dF z y))) *
          ((S.L : ℝ) ^ (2 * jj y) * ((S.L : ℝ) ^ jj y * Real.exp (2 * δ) *
            (Real.exp (δ * S.dF z y) * Real.exp (-ph z)) * M)) := by
          refine h1.trans (mul_le_mul_of_nonneg_left (h2.trans (mul_le_mul_of_nonneg_left
            (h3'.trans ?_) (by positivity))) (by positivity))
          gcongr
      _ = Real.exp (6 * δ) * ((S.L : ℝ) ^ jj y)⁻¹ * Real.exp (-(δ * S.dF z y)) * Real.exp (-ph z) * M := by
          have e1 : (S.L : ℝ) ^ (4 * jj y) = ((S.L : ℝ) ^ jj y) ^ 4 := by rw [← pow_mul, mul_comm]
          have e2 : (S.L : ℝ) ^ (2 * jj y) = ((S.L : ℝ) ^ jj y) ^ 2 := by rw [← pow_mul, mul_comm]
          have hp : (S.L : ℝ) ^ jj y ≠ 0 := pow_ne_zero _ hL.ne'
          rw [e1, e2]
          have ex : Real.exp (4 * δ) * Real.exp (-(2 * δ * S.dF z y)) * Real.exp (2 * δ) *
              Real.exp (δ * S.dF z y) = Real.exp (6 * δ) * Real.exp (-(δ * S.dF z y)) := by
            rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; ring_nf
          have ep : ((S.L : ℝ) ^ jj y) ^ 3 * (((S.L : ℝ) ^ jj y) ^ 4)⁻¹ = ((S.L : ℝ) ^ jj y)⁻¹ := by
            rw [pow_succ _ 3, mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 3 hp), one_mul]
          calc (((S.L : ℝ) ^ jj y) ^ 4)⁻¹ * (Real.exp (4 * δ) * Real.exp (-(2 * δ * S.dF z y))) *
                (((S.L : ℝ) ^ jj y) ^ 2 * ((S.L : ℝ) ^ jj y * Real.exp (2 * δ) *
                  (Real.exp (δ * S.dF z y) * Real.exp (-ph z)) * M))
              = (((S.L : ℝ) ^ jj y) ^ 3 * (((S.L : ℝ) ^ jj y) ^ 4)⁻¹) *
                  (Real.exp (4 * δ) * Real.exp (-(2 * δ * S.dF z y)) * Real.exp (2 * δ) *
                    Real.exp (δ * S.dF z y)) * Real.exp (-ph z) * M := by ring
            _ = _ := by rw [ep, ex]; ring
  refine (sum_le_sum hblock).trans ?_
  -- the scale shift and the summation
  set yz := bc S.toDomSeq z
  have hyz : yz ∈ detB S.toDomSeq := bc_mem_detB S z
  have hdz : S.dF yz z ≤ 2 :=
    ENNReal.toReal_le_of_le_ofReal (by norm_num) (S.wdist_block_le hyz (mem_blk_bc S z))
  have hterm : ∀ y ∈ detB S.toDomSeq, Real.exp (6 * δ) * ((S.L : ℝ) ^ jj y)⁻¹ * Real.exp (-(δ * S.dF z y)) *
      Real.exp (-ph z) * M ≤ Real.exp (7 * δ) * (S.L : ℝ) ^ (4 : ℝ) * ((S.L : ℝ) ^ jj z)⁻¹ *
        Real.exp (-ph z) * M * Real.exp (-(1 / 2 * δ * S.dF yz y)) := by
    intro y _
    have hsh := S.scale_shift hδ hRM2 (show |(-1 : ℝ)| ≤ 4 by norm_num) z y
    simp only [Real.rpow_neg_one] at hsh
    have ht := S.dF_triangle yz z y
    have hexp : Real.exp (-(δ * S.dF z y)) * Real.exp (δ / 8 * S.dF z y) ≤
        Real.exp δ * Real.exp (-(1 / 2 * δ * S.dF yz y)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have h0 := S.dF_nonneg z y
      nlinarith
    calc Real.exp (6 * δ) * ((S.L : ℝ) ^ jj y)⁻¹ * Real.exp (-(δ * S.dF z y)) * Real.exp (-ph z) * M
        ≤ Real.exp (6 * δ) * ((S.L : ℝ) ^ (4 : ℝ) * Real.exp (δ / 8 * S.dF z y) * ((S.L : ℝ) ^ jj z)⁻¹) *
            Real.exp (-(δ * S.dF z y)) * Real.exp (-ph z) * M := by gcongr
      _ = Real.exp (6 * δ) * (S.L : ℝ) ^ (4 : ℝ) * ((S.L : ℝ) ^ jj z)⁻¹ * Real.exp (-ph z) * M *
            (Real.exp (-(δ * S.dF z y)) * Real.exp (δ / 8 * S.dF z y)) := by ring
      _ ≤ Real.exp (6 * δ) * (S.L : ℝ) ^ (4 : ℝ) * ((S.L : ℝ) ^ jj z)⁻¹ * Real.exp (-ph z) * M *
            (Real.exp δ * Real.exp (-(1 / 2 * δ * S.dF yz y))) := by gcongr
      _ = _ := by rw [show 7 * δ = 6 * δ + δ by ring, Real.exp_add]; ring
  refine (sum_le_sum hterm).trans ?_
  rw [← mul_sum]
  have hsum := S.summation_fine (α := 1 / 2) (by norm_num) hδ hRM1 hyz
  calc Real.exp (7 * δ) * (S.L : ℝ) ^ (4 : ℝ) * ((S.L : ℝ) ^ jj z)⁻¹ * Real.exp (-ph z) * M *
        ∑ y ∈ detB S.toDomSeq, Real.exp (-(1 / 2 * δ * S.dF yz y))
      ≤ Real.exp (7 * δ) * (S.L : ℝ) ^ (4 : ℝ) * ((S.L : ℝ) ^ jj z)⁻¹ * Real.exp (-ph z) * M *
          (S.toContSeq).c1 (1 / 2) δ := by gcongr
    _ = _ := by ring

end SFBounds
end CoreLean

end
