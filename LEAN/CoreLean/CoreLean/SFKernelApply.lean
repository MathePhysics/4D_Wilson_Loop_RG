/-
Block kernel bounds applied to forms with block bounds (the function form of `KB_comp`), for operators and for operators
composed with `D^*_𝐔`, on the fine lattice (`a₀ = 1`); BALABAN_CORE.tex (`d4ef86a9a5fd`), `prop:sf-block`.

* `BlkBd v C ρ p q y'`: `|v(z)| ≤ Ca_{y''}^pa_{y'}^qe^{-ρd(y'', y')}Λ` for `z ∈ Δ(y'')` (with the factor `Λ` in `C`).
* `KB_apply`: `B` with `KB (C_B, ρ_B, p_B, 0)` and `v` with `BlkBd (C, ρ, p, q)` give
  `|(Bv)(x)| ≤ CC_BL⁴c₁(½, m)a_y^{p_B}a_{y'}^{p+q}e^{-(m/2)d(y, y')}` for `x ∈ Δ(y)`.
* `KBS B U C ρ p`: the bound `|(BD^*_𝐔λ)(x)| ≤ Ca_y^pe^{-ρd(y, y')}Λ` for families `λ` supported in `Δ(y')`;
  `KB_apply_star`: the same composition for `BD^*_𝐔g` with `g` of block bounds.
* `ScalarHyp.KB_Gp'`, `ScalarHyp.KBS_Gp'`: `G'` satisfies `KB (C_v, (7/8)δ, 2, 0)` and `KBS (C_v, (7/8)δ, 1)`.
-/
import CoreLean.SFKernelComp

open Finset Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean
namespace SFBounds

open Lattices SeqDom Blocks SmallFieldBlocks SFBox SFBox.SeqDomBox SmallFieldDecay SequenceOperators

variable (S : SeqDom) {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "NF" => SequenceAverages.N0 S
local notation "RMS" => ((S.R * S.L ^ S.mM : ℕ) : ℝ)
set_option quotPrecheck false in
local notation "jj" => (S.toDomSeq).sc

/-- Block bounds of a form relative to a source block `Δ(y')`. -/
def BlkBd (v : Site NF → Mat) (C ρ : ℝ) (p q : ℕ) (y' : Site NF) : Prop :=
  ∀ y'' ∈ detB S.toDomSeq, ∀ z ∈ Blk S.toDomSeq ((S.toDomSeq).sc y'') y'',
    hs (v z) ≤ C * (S.L : ℝ) ^ (p * (S.toDomSeq).sc y'') * (S.L : ℝ) ^ (q * (S.toDomSeq).sc y') *
      Real.exp (-(ρ * S.dF y'' y'))

/-- The common summation: `Σ_{y''}e^{-ρ_Bd(y, y'')}a_{y''}^pa_{y'}^qe^{-ρd(y'', y')} ≤ L⁴c₁a_{y'}^{p+q}e^{-(m/2)d}`. -/
lemma blk_sum {ρ ρB δ m : ℝ} {p q : ℕ} (hp : p ≤ 4) (hδ : 0 < δ) (hm : 0 < m) (hmB : m ≤ ρB) (hmA : m + δ / 8 ≤ ρ)
    (hRMs : 32 * Real.log S.L / δ ≤ RMS) (hRMc : (S.toContSeq).r1 (1 / 2) m ≤ RMS) {y y' : Site NF}
    (hy : y ∈ detB S.toDomSeq) :
    ∑ y'' ∈ detB S.toDomSeq, Real.exp (-(ρB * S.dF y y'')) * ((S.L : ℝ) ^ (p * jj y'') * (S.L : ℝ) ^ (q * jj y') *
        Real.exp (-(ρ * S.dF y'' y'))) ≤
      (S.L : ℝ) ^ (4 : ℝ) * (S.toContSeq).c1 (1 / 2) m * (S.L : ℝ) ^ ((p + q) * jj y') *
        Real.exp (-(m / 2 * S.dF y y')) := by
  have hL : (0 : ℝ) < S.L := by exact_mod_cast S.Lpos
  have hsh : ∀ y'', (S.L : ℝ) ^ (p * jj y'') ≤
      (S.L : ℝ) ^ (4 : ℝ) * Real.exp (δ / 8 * S.dF y'' y') * (S.L : ℝ) ^ (p * jj y') := by
    intro y''
    have h := S.scale_shift hδ hRMs (σ := ((p : ℕ) : ℝ)) (by rw [abs_of_nonneg (by positivity)]; exact_mod_cast hp)
      y' y''
    rw [Real.rpow_natCast, Real.rpow_natCast, ← pow_mul, ← pow_mul, mul_comm (jj y'') p, mul_comm (jj y') p,
      S.dF_comm y' y''] at h
    exact h
  have hchain := chain2 S (δ := ρB) (δ' := m) (by linarith) hm (by rw [min_eq_right hmB]; exact hRMc) hy (y' := y')
  rw [min_eq_right hmB] at hchain
  have epow : (S.L : ℝ) ^ ((p + q) * jj y') = (S.L : ℝ) ^ (p * jj y') * (S.L : ℝ) ^ (q * jj y') := by
    rw [← pow_add]; ring_nf
  have hterm : ∀ y'' ∈ detB S.toDomSeq, Real.exp (-(ρB * S.dF y y'')) * ((S.L : ℝ) ^ (p * jj y'') *
      (S.L : ℝ) ^ (q * jj y') * Real.exp (-(ρ * S.dF y'' y'))) ≤
      (S.L : ℝ) ^ (4 : ℝ) * (S.L : ℝ) ^ ((p + q) * jj y') *
        (Real.exp (-(ρB * S.dF y y'')) * Real.exp (-(m * S.dF y'' y'))) := by
    intro y'' _
    have hd := S.dF_nonneg y'' y'
    have hexp : Real.exp (-(ρ * S.dF y'' y')) * Real.exp (δ / 8 * S.dF y'' y') ≤ Real.exp (-(m * S.dF y'' y')) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by nlinarith)
    rw [epow]
    calc Real.exp (-(ρB * S.dF y y'')) * ((S.L : ℝ) ^ (p * jj y'') * (S.L : ℝ) ^ (q * jj y') *
          Real.exp (-(ρ * S.dF y'' y')))
        ≤ Real.exp (-(ρB * S.dF y y'')) * (((S.L : ℝ) ^ (4 : ℝ) * Real.exp (δ / 8 * S.dF y'' y') *
          (S.L : ℝ) ^ (p * jj y')) * (S.L : ℝ) ^ (q * jj y') * Real.exp (-(ρ * S.dF y'' y'))) := by gcongr; exact hsh y''
      _ = (S.L : ℝ) ^ (4 : ℝ) * ((S.L : ℝ) ^ (p * jj y') * (S.L : ℝ) ^ (q * jj y')) *
          (Real.exp (-(ρB * S.dF y y'')) * (Real.exp (-(ρ * S.dF y'' y')) * Real.exp (δ / 8 * S.dF y'' y'))) := by ring
      _ ≤ _ := by gcongr
  refine (sum_le_sum hterm).trans ?_
  rw [← mul_sum]
  calc _ ≤ (S.L : ℝ) ^ (4 : ℝ) * (S.L : ℝ) ^ ((p + q) * jj y') *
        ((S.toContSeq).c1 (1 / 2) m * Real.exp (-(1 / 2 * m * S.dF y y'))) :=
        mul_le_mul_of_nonneg_left hchain (by positivity)
    _ = _ := by rw [show 1 / 2 * m * S.dF y y' = m / 2 * S.dF y y' by ring]; ring

/-- **A block kernel bound applied to a form with block bounds.** -/
theorem KB_apply {B : Module.End ℂ (Site NF → Mat)} {CB ρB C ρ δ m : ℝ} {pB p q : ℕ} (hB : KB S B CB ρB pB 0)
    (hCB : 0 ≤ CB) (hC : 0 ≤ C) {v : Site NF → Mat} {y' : Site NF} (hv : BlkBd S v C ρ p q y') (hp : p ≤ 4)
    (hδ : 0 < δ) (hm : 0 < m) (hmB : m ≤ ρB) (hmA : m + δ / 8 ≤ ρ)
    (hRMs : 32 * Real.log S.L / δ ≤ RMS) (hRMc : (S.toContSeq).r1 (1 / 2) m ≤ RMS)
    {y x : Site NF} (hy : y ∈ detB S.toDomSeq) (hx : x ∈ Blk S.toDomSeq (jj y) y) :
    hs (B v x) ≤ C * CB * (S.L : ℝ) ^ (4 : ℝ) * (S.toContSeq).c1 (1 / 2) m * (S.L : ℝ) ^ (pB * jj y) *
      (S.L : ℝ) ^ ((p + q) * jj y') * Real.exp (-(m / 2 * S.dF y y')) := by
  have hL : (0 : ℝ) < S.L := by exact_mod_cast S.Lpos
  set E := fun y'' => C * (S.L : ℝ) ^ (p * jj y'') * (S.L : ℝ) ^ (q * jj y') * Real.exp (-(ρ * S.dF y'' y'))
  have hblk : ∀ y'' ∈ detB S.toDomSeq, ∀ x'', hs (onBlk S y'' v x'') ≤ E y'' := by
    intro y'' hy'' x''
    simp only [onBlk]
    split_ifs with hx''
    · exact hv y'' hy'' x'' hx''
    · simp [hs, hs2, ntr]; simp only [E]; positivity
  have hterm : ∀ y'' ∈ detB S.toDomSeq, hs (B (onBlk S y'' v) x) ≤
      CB * (S.L : ℝ) ^ (pB * jj y) * Real.exp (-(ρB * S.dF y y'')) * E y'' := by
    intro y'' hy''
    have := hB y hy y'' hy'' (onBlk S y'' v) (E y'') (by simp only [E]; positivity)
      (fun x'' hx'' => by simp only [onBlk]; rw [if_neg hx'']) (hblk y'' hy'') x hx
    simpa only [zero_mul, pow_zero, mul_one] using this
  have hsplit : B v = ∑ y'' ∈ detB S.toDomSeq, B (onBlk S y'' v) := by rw [← map_sum, sum_onBlk]
  have hsum : hs (B v x) ≤ ∑ y'' ∈ detB S.toDomSeq, CB * (S.L : ℝ) ^ (pB * jj y) *
      Real.exp (-(ρB * S.dF y y'')) * E y'' := by
    rw [hsplit, Finset.sum_apply]
    exact (RegularAverages.hs_sum_le _ _).trans (sum_le_sum hterm)
  have hs2 := blk_sum S (ρ := ρ) (ρB := ρB) (p := p) (q := q) hp hδ hm hmB hmA hRMs hRMc hy (y' := y')
  refine hsum.trans ?_
  have e : ∑ y'' ∈ detB S.toDomSeq, CB * (S.L : ℝ) ^ (pB * jj y) * Real.exp (-(ρB * S.dF y y'')) * E y'' =
      C * CB * (S.L : ℝ) ^ (pB * jj y) * ∑ y'' ∈ detB S.toDomSeq, Real.exp (-(ρB * S.dF y y'')) *
        ((S.L : ℝ) ^ (p * jj y'') * (S.L : ℝ) ^ (q * jj y') * Real.exp (-(ρ * S.dF y'' y'))) := by
    rw [mul_sum]; refine sum_congr rfl fun y'' _ => ?_; simp only [E]; ring
  rw [e]
  calc C * CB * (S.L : ℝ) ^ (pB * jj y) * ∑ y'' ∈ detB S.toDomSeq, Real.exp (-(ρB * S.dF y y'')) *
        ((S.L : ℝ) ^ (p * jj y'') * (S.L : ℝ) ^ (q * jj y') * Real.exp (-(ρ * S.dF y'' y')))
      ≤ C * CB * (S.L : ℝ) ^ (pB * jj y) * ((S.L : ℝ) ^ (4 : ℝ) * (S.toContSeq).c1 (1 / 2) m *
          (S.L : ℝ) ^ ((p + q) * jj y') * Real.exp (-(m / 2 * S.dF y y'))) :=
        mul_le_mul_of_nonneg_left hs2 (by positivity)
    _ = _ := by ring

/-- **The bound of `BD^*_𝐔`** on families supported in a block. -/
def KBS (B : Module.End ℂ (Site NF → Mat)) (U : Config N NF) (C ρ : ℝ) (p : ℕ) : Prop :=
  ∀ y ∈ detB S.toDomSeq, ∀ y' ∈ detB S.toDomSeq, ∀ (lam : Fin 4 → Site NF → Mat) (Λ : ℝ), 0 ≤ Λ →
    (∀ μ x', x' ∉ Blk S.toDomSeq ((S.toDomSeq).sc y') y' → lam μ x' = 0) → (∀ μ x', hs (lam μ x') ≤ Λ) →
    ∀ x ∈ Blk S.toDomSeq ((S.toDomSeq).sc y) y,
      hs (B (Ds1L a1 U lam) x) ≤ C * (S.L : ℝ) ^ (p * (S.toDomSeq).sc y) * Real.exp (-(ρ * S.dF y y')) * Λ

/-- **`BD^*_𝐔` applied to a family with block bounds.** -/
theorem KB_apply_star {B : Module.End ℂ (Site NF → Mat)} {U : Config N NF} {CB ρB C ρ δ m : ℝ} {pB p q : ℕ}
    (hB : KBS S B U CB ρB pB) (hCB : 0 ≤ CB) (hC : 0 ≤ C) {g : Fin 4 → Site NF → Mat} {y' : Site NF}
    (hg : ∀ μ, BlkBd S (g μ) C ρ p q y') (hp : p ≤ 4)
    (hδ : 0 < δ) (hm : 0 < m) (hmB : m ≤ ρB) (hmA : m + δ / 8 ≤ ρ)
    (hRMs : 32 * Real.log S.L / δ ≤ RMS) (hRMc : (S.toContSeq).r1 (1 / 2) m ≤ RMS)
    {y x : Site NF} (hy : y ∈ detB S.toDomSeq) (hx : x ∈ Blk S.toDomSeq (jj y) y) :
    hs (B (Ds1L a1 U g) x) ≤ C * CB * (S.L : ℝ) ^ (4 : ℝ) * (S.toContSeq).c1 (1 / 2) m * (S.L : ℝ) ^ (pB * jj y) *
      (S.L : ℝ) ^ ((p + q) * jj y') * Real.exp (-(m / 2 * S.dF y y')) := by
  have hL : (0 : ℝ) < S.L := by exact_mod_cast S.Lpos
  set E := fun y'' => C * (S.L : ℝ) ^ (p * jj y'') * (S.L : ℝ) ^ (q * jj y') * Real.exp (-(ρ * S.dF y'' y'))
  set gb : Site NF → Fin 4 → Site NF → Mat := fun y'' μ => onBlk S y'' (g μ)
  have hterm : ∀ y'' ∈ detB S.toDomSeq, hs (B (Ds1L a1 U (gb y'')) x) ≤
      CB * (S.L : ℝ) ^ (pB * jj y) * Real.exp (-(ρB * S.dF y y'')) * E y'' := by
    intro y'' hy''
    refine hB y hy y'' hy'' (gb y'') (E y'') (by simp only [E]; positivity)
      (fun μ x'' hx'' => by simp only [gb, onBlk]; rw [if_neg hx'']) (fun μ x'' => ?_) x hx
    simp only [gb, onBlk]
    split_ifs with hx''
    · exact hg μ y'' hy'' x'' hx''
    · simp [hs, hs2, ntr]; simp only [E]; positivity
  have hsplit : Ds1L a1 U g = ∑ y'' ∈ detB S.toDomSeq, Ds1L a1 U (gb y'') := by
    rw [← map_sum]; congr 1; funext μ x; rw [Finset.sum_apply, Finset.sum_apply]
    have := congrFun (sum_onBlk S (g μ)) x; rw [Finset.sum_apply] at this; exact this.symm
  have hsum : hs (B (Ds1L a1 U g) x) ≤ ∑ y'' ∈ detB S.toDomSeq, CB * (S.L : ℝ) ^ (pB * jj y) *
      Real.exp (-(ρB * S.dF y y'')) * E y'' := by
    rw [hsplit, map_sum, Finset.sum_apply]
    exact (RegularAverages.hs_sum_le _ _).trans (sum_le_sum hterm)
  have hs2 := blk_sum S (ρ := ρ) (ρB := ρB) (p := p) (q := q) hp hδ hm hmB hmA hRMs hRMc hy (y' := y')
  refine hsum.trans ?_
  have e : ∑ y'' ∈ detB S.toDomSeq, CB * (S.L : ℝ) ^ (pB * jj y) * Real.exp (-(ρB * S.dF y y'')) * E y'' =
      C * CB * (S.L : ℝ) ^ (pB * jj y) * ∑ y'' ∈ detB S.toDomSeq, Real.exp (-(ρB * S.dF y y'')) *
        ((S.L : ℝ) ^ (p * jj y'') * (S.L : ℝ) ^ (q * jj y') * Real.exp (-(ρ * S.dF y'' y'))) := by
    rw [mul_sum]; refine sum_congr rfl fun y'' _ => ?_; simp only [E]; ring
  rw [e]
  calc _ ≤ C * CB * (S.L : ℝ) ^ (pB * jj y) * ((S.L : ℝ) ^ (4 : ℝ) * (S.toContSeq).c1 (1 / 2) m *
          (S.L : ℝ) ^ ((p + q) * jj y') * Real.exp (-(m / 2 * S.dF y y'))) :=
        mul_le_mul_of_nonneg_left hs2 (by positivity)
    _ = _ := by ring

namespace ScalarHyp

variable {S} {X : Fin 4 → Site (SequenceAverages.N0 S) → Matrix (Fin N) (Fin N) ℂ} {α₁ : ℝ}
  {W : Site (SequenceAverages.N0 S) → Site (SequenceAverages.N0 S) → (Matrix (Fin N) (Fin N) ℂ)ˣ} {η : ℝ}
  {ΩD : Set (Site (SequenceAverages.N0 S))} {δ : ℝ}
  (H : ScalarHyp S X α₁ W η ΩD δ)
include H

/-- `G'` satisfies the block kernel bound `KB (C_v, (7/8)δ, 2, 0)`. -/
theorem KB_Gp' [NeZero N] :
    KB S (Gp' S.toDomSeq (cfgX X) W ΩD) (Cv S δ (Csc S N) (4 * N * (S.L : ℝ) ^ 4)) (7 / 8 * δ) 2 0 := by
  intro y hy y' hy' lam Λ hΛ hsupp hbd x hx
  have := H.values hy hy' hx hΛ hsupp hbd
  simp only [zero_mul, pow_zero, mul_one]
  linarith

/-- `G'D^*_𝐔` satisfies `KBS (C_v, (7/8)δ, 1)`. -/
theorem KBS_Gp' [NeZero N] :
    KBS S (Gp' S.toDomSeq (cfgX X) W ΩD) (cfgX X) (Cv S δ (Csc S N) (4 * N * (S.L : ℝ) ^ 4)) (7 / 8 * δ) 1 := by
  intro y hy y' hy' lam Λ hΛ hsupp hbd x hx
  have := H.Dstar_values hy hy' hx hΛ hsupp hbd
  simp only [one_mul]
  linarith

end ScalarHyp

end SFBounds
end CoreLean

end
