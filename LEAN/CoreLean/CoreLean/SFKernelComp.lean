/-
Block kernel bounds and their composition on the fine lattice of a sequence of domains (`a₀ = 1`), the computation of
the steps "The entries" and "The projection" of `prop:sf-block` of BALABAN_CORE.tex (`d4ef86a9a5fd`) in one form.

* `KB A C ρ p q`: for `y, y' ∈ 𝐁`, `x ∈ Δ(y)` and `λ` supported in `Δ(y')` with `|λ| ≤ Λ`,
  `|(Aλ)(x)| ≤ Ca_y^pa_{y'}^qe^{-ρd(y, y')}Λ`.
* `KB_comp`: if `A` satisfies `KB` with `(C_A, ρ_A, p_A, q_A)`, `p_A ≤ 4`, and `B` with `(C_B, ρ_B, p_B, 0)`, then for
  `0 < m ≤ ρ_B`, `m + δ/8 ≤ ρ_A` and `RM ≥ max{32δ⁻¹log L, r₁(½, m)}`, `BA` satisfies `KB` with
  `(C_AC_BL⁴c₁(½, m), m/2, p_B, p_A + q_A)` (the decomposition `Aλ = Σ_{y''}1_{Δ(y'')}Aλ`, `eq:sf-scale-shift`, and
  `eq:chain-summation`).
* `KB_add`, `KB_mono`: sums and weakenings.
-/
import CoreLean.SFResolvent

open Finset Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean
namespace SFBounds

open Lattices SeqDom Blocks SmallFieldBlocks SFBox SFBox.SeqDomBox SmallFieldDecay

variable (S : SeqDom) {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "NF" => SequenceAverages.N0 S
local notation "RMS" => ((S.R * S.L ^ S.mM : ℕ) : ℝ)
set_option quotPrecheck false in
local notation "jj" => (S.toDomSeq).sc

/-- **The block kernel bound.** -/
def KB (A : Module.End ℂ (Site NF → Mat)) (C ρ : ℝ) (p q : ℕ) : Prop :=
  ∀ y ∈ detB S.toDomSeq, ∀ y' ∈ detB S.toDomSeq, ∀ (lam : Site NF → Mat) (Λ : ℝ), 0 ≤ Λ →
    (∀ x', x' ∉ Blk S.toDomSeq ((S.toDomSeq).sc y') y' → lam x' = 0) → (∀ x', hs (lam x') ≤ Λ) →
    ∀ x ∈ Blk S.toDomSeq ((S.toDomSeq).sc y) y,
      hs (A lam x) ≤ C * (S.L : ℝ) ^ (p * (S.toDomSeq).sc y) * (S.L : ℝ) ^ (q * (S.toDomSeq).sc y') *
        Real.exp (-(ρ * S.dF y y')) * Λ

/-- **The composition of block kernel bounds.** -/
theorem KB_comp {A B : Module.End ℂ (Site NF → Mat)} {CA ρA CB ρB δ m : ℝ} {pA qA pB : ℕ}
    (hA : KB S A CA ρA pA qA) (hB : KB S B CB ρB pB 0) (hCA : 0 ≤ CA) (hCB : 0 ≤ CB) (hpA : pA ≤ 4)
    (hδ : 0 < δ) (hm : 0 < m) (hmB : m ≤ ρB) (hmA : m + δ / 8 ≤ ρA)
    (hRMs : 32 * Real.log S.L / δ ≤ RMS) (hRMc : (S.toContSeq).r1 (1 / 2) m ≤ RMS) :
    KB S (B * A) (CA * CB * (S.L : ℝ) ^ (4 : ℝ) * (S.toContSeq).c1 (1 / 2) m) (m / 2) pB (pA + qA) := by
  intro y hy y' hy' lam Λ hΛ hsupp hbd x hx
  have hL : (0 : ℝ) < S.L := by exact_mod_cast S.Lpos
  set v := A lam
  -- the bound of `Aλ` on each block
  have hv : ∀ y'' ∈ detB S.toDomSeq, ∀ x'', hs (onBlk S y'' v x'') ≤
      CA * (S.L : ℝ) ^ (pA * jj y'') * (S.L : ℝ) ^ (qA * jj y') * Real.exp (-(ρA * S.dF y'' y')) * Λ := by
    intro y'' hy'' x''
    simp only [onBlk]
    split_ifs with hx''
    · exact hA y'' hy'' y' hy' lam Λ hΛ hsupp hbd x'' hx''
    · simp [hs, hs2, ntr]; positivity
  have hsplit : B v = ∑ y'' ∈ detB S.toDomSeq, B (onBlk S y'' v) := by rw [← map_sum, sum_onBlk]
  set E := fun y'' => CA * (S.L : ℝ) ^ (pA * jj y'') * (S.L : ℝ) ^ (qA * jj y') * Real.exp (-(ρA * S.dF y'' y')) * Λ
  have hterm : ∀ y'' ∈ detB S.toDomSeq, hs (B (onBlk S y'' v) x) ≤
      CB * (S.L : ℝ) ^ (pB * jj y) * Real.exp (-(ρB * S.dF y y'')) * E y'' := by
    intro y'' hy''
    have := hB y hy y'' hy'' (onBlk S y'' v) (E y'') (by simp only [E]; positivity)
      (fun x'' hx'' => by simp only [onBlk]; rw [if_neg hx'']) (hv y'' hy'') x hx
    simpa only [zero_mul, pow_zero, mul_one] using this
  -- the scale shift `a_{y''}^{p_A} ≤ L⁴e^{δd(y'', y')/8}a_{y'}^{p_A}`
  have hsh : ∀ y'', (S.L : ℝ) ^ (pA * jj y'') ≤
      (S.L : ℝ) ^ (4 : ℝ) * Real.exp (δ / 8 * S.dF y'' y') * (S.L : ℝ) ^ (pA * jj y') := by
    intro y''
    have h := S.scale_shift hδ hRMs (σ := ((pA : ℕ) : ℝ)) (by rw [abs_of_nonneg (by positivity)]; exact_mod_cast hpA)
      y' y''
    rw [Real.rpow_natCast, Real.rpow_natCast, ← pow_mul, ← pow_mul, mul_comm (jj y'') pA, mul_comm (jj y') pA,
      S.dF_comm y' y''] at h
    exact h
  have hchain := chain2 S (δ := ρB) (δ' := m) (by linarith) hm
    (by rw [min_eq_right hmB]; exact hRMc) hy (y' := y')
  rw [min_eq_right hmB] at hchain
  have hterm2 : ∀ y'' ∈ detB S.toDomSeq,
      CB * (S.L : ℝ) ^ (pB * jj y) * Real.exp (-(ρB * S.dF y y'')) * E y'' ≤
      CA * CB * (S.L : ℝ) ^ (4 : ℝ) * (S.L : ℝ) ^ (pB * jj y) * (S.L : ℝ) ^ ((pA + qA) * jj y') * Λ *
        (Real.exp (-(ρB * S.dF y y'')) * Real.exp (-(m * S.dF y'' y'))) := by
    intro y'' _
    simp only [E]
    have h1 := hsh y''
    have hd := S.dF_nonneg y'' y'
    have hexp : Real.exp (-(ρA * S.dF y'' y')) * Real.exp (δ / 8 * S.dF y'' y') ≤ Real.exp (-(m * S.dF y'' y')) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by nlinarith)
    have epow : (S.L : ℝ) ^ ((pA + qA) * jj y') = (S.L : ℝ) ^ (pA * jj y') * (S.L : ℝ) ^ (qA * jj y') := by
      rw [← pow_add]; ring_nf
    rw [epow]
    calc CB * (S.L : ℝ) ^ (pB * jj y) * Real.exp (-(ρB * S.dF y y'')) *
          (CA * (S.L : ℝ) ^ (pA * jj y'') * (S.L : ℝ) ^ (qA * jj y') * Real.exp (-(ρA * S.dF y'' y')) * Λ)
        ≤ CB * (S.L : ℝ) ^ (pB * jj y) * Real.exp (-(ρB * S.dF y y'')) *
          (CA * ((S.L : ℝ) ^ (4 : ℝ) * Real.exp (δ / 8 * S.dF y'' y') * (S.L : ℝ) ^ (pA * jj y')) *
            (S.L : ℝ) ^ (qA * jj y') * Real.exp (-(ρA * S.dF y'' y')) * Λ) := by gcongr
      _ = CA * CB * (S.L : ℝ) ^ (4 : ℝ) * (S.L : ℝ) ^ (pB * jj y) *
            ((S.L : ℝ) ^ (pA * jj y') * (S.L : ℝ) ^ (qA * jj y')) * Λ *
            (Real.exp (-(ρB * S.dF y y'')) * (Real.exp (-(ρA * S.dF y'' y')) * Real.exp (δ / 8 * S.dF y'' y'))) := by
          ring
      _ ≤ _ := by gcongr
  have hsum : hs (B v x) ≤ ∑ y'' ∈ detB S.toDomSeq,
      CB * (S.L : ℝ) ^ (pB * jj y) * Real.exp (-(ρB * S.dF y y'')) * E y'' := by
    rw [hsplit, Finset.sum_apply]
    exact (RegularAverages.hs_sum_le _ _).trans (sum_le_sum hterm)
  have hK : 0 ≤ CA * CB * (S.L : ℝ) ^ (4 : ℝ) * (S.L : ℝ) ^ (pB * jj y) * (S.L : ℝ) ^ ((pA + qA) * jj y') * Λ := by
    positivity
  show hs (B v x) ≤ _
  refine hsum.trans ((sum_le_sum hterm2).trans ?_)
  rw [← mul_sum]
  calc _ ≤ CA * CB * (S.L : ℝ) ^ (4 : ℝ) * (S.L : ℝ) ^ (pB * jj y) * (S.L : ℝ) ^ ((pA + qA) * jj y') * Λ *
        ((S.toContSeq).c1 (1 / 2) m * Real.exp (-(1 / 2 * m * S.dF y y'))) := mul_le_mul_of_nonneg_left hchain hK
    _ = _ := by
        rw [show 1 / 2 * m * S.dF y y' = m / 2 * S.dF y y' by ring]; ring

/-- Sums of block kernel bounds. -/
theorem KB_add {A B : Module.End ℂ (Site NF → Mat)} {CA CB ρ : ℝ} {p q : ℕ} (hA : KB S A CA ρ p q)
    (hB : KB S B CB ρ p q) : KB S (A + B) (CA + CB) ρ p q := by
  intro y hy y' hy' lam Λ hΛ hsupp hbd x hx
  have h1 := hA y hy y' hy' lam Λ hΛ hsupp hbd x hx
  have h2 := hB y hy y' hy' lam Λ hΛ hsupp hbd x hx
  rw [LinearMap.add_apply, Pi.add_apply]
  refine (hs_add_le _ _).trans ?_
  linarith

/-- Weakening of the rate and the constant. -/
theorem KB_mono {A : Module.End ℂ (Site NF → Mat)} {C C' ρ ρ' : ℝ} {p q : ℕ} (hA : KB S A C ρ p q)
    (hC0 : 0 ≤ C) (hC : C ≤ C') (hρ : ρ' ≤ ρ) : KB S A C' ρ' p q := by
  intro y hy y' hy' lam Λ hΛ hsupp hbd x hx
  refine (hA y hy y' hy' lam Λ hΛ hsupp hbd x hx).trans ?_
  have hd := S.dF_nonneg y y'
  have he : Real.exp (-(ρ * S.dF y y')) ≤ Real.exp (-(ρ' * S.dF y y')) := Real.exp_le_exp.2 (by nlinarith)
  have hL : (0 : ℝ) < S.L := by exact_mod_cast S.Lpos
  have hC' : 0 ≤ C' := hC0.trans hC
  gcongr

end SFBounds
end CoreLean

end
