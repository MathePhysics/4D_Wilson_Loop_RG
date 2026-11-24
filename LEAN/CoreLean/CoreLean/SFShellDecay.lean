/-
`prop:sf-vector-lower` of BALABAN_CORE.tex (`3373af8b246f`), the step "The cut-off minimiser", the distance of a
sequence whose scales are at most `m` (the comparison sequences of `SFComparison.lean`, `m = i + 1`): the weight of
`def:distance` is at least `a_m⁻¹` everywhere, so that `d(x, x') ≥ a_m⁻¹|x - x'|₁ ≥ |x - x'|_∞/L^m` in the units of the
fine lattice.

* `wdist_ge_scaled`: `a_m⁻¹|z - z'|₁ ≤ d(z, z')` when every scale is at most `m`.
* `dF_ge_dinf`: for a sequence with `Ω_{m+1} = ∅`, `dinf(x, x')/L^m ≤ d(x, x')` on the fine lattice.
-/
import CoreLean.SFCutoff

open Finset Set MeasureTheory
open scoped ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean

variable {p : ℝ}

/-- **The weighted distance of a sequence whose scales are at most `m`**: `a_m⁻¹|z - z'|₁ ≤ d(z, z')`. -/
theorem wdist_ge_scaled (D : DomainData p) (m : ℕ) (hm : ∀ z, D.scale z ≤ m) (z z' : Tor p) :
    ENNReal.ofReal ((D.a m)⁻¹ * dist1 z z') ≤ wdist D z z' := by
  refine le_iInf fun P => ?_
  have h1 := ofReal_sum_abs_sub_le P.lip P.T_nonneg
  have h2 : dist1 z z' ≤ ∑ ν, |P.γ P.T ν - P.γ 0 ν| := by
    calc dist1 z z' = dist1 (projT p (P.γ 0)) (projT p (P.γ P.T)) := by rw [P.start, P.stop]
      _ ≤ ∑ ν, |P.γ 0 ν - P.γ P.T ν| := dist1_projT_le _ _
      _ = ∑ ν, |P.γ P.T ν - P.γ 0 ν| := Finset.sum_congr rfl fun ν _ => abs_sub_comm _ _
  have hc : 0 ≤ (D.a m)⁻¹ := inv_nonneg.2 (D.a_pos' m).le
  rw [ENNReal.ofReal_mul hc]
  refine (mul_le_mul' le_rfl ((ENNReal.ofReal_le_ofReal h2).trans h1)).trans ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun t => ?_
  unfold wIntegrand
  refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
  unfold DomainData.weight
  exact inv_anti₀ (D.a_pos' _) (D.a_mono _ _ (hm _))

namespace Lattices
namespace SeqDom

variable (S : SeqDom)

local notation "NF" => SequenceAverages.N0 S

lemma norm_le_dist1 (z z' : Tor (ellT S.L S.mT)) : ‖z - z'‖ ≤ dist1 z z' := by
  refine (pi_norm_le_iff_of_nonneg (dist1_nonneg _ _)).2 fun ν => ?_
  exact single_le_sum (f := fun ν => ‖z ν - z' ν‖) (fun _ _ => norm_nonneg _) (mem_univ ν)

/-- **The weighted distance of a sequence with `Ω_{m+1} = ∅`** on the fine lattice: `dinf(x, x')/L^m ≤ d(x, x')`. -/
theorem dF_ge_dinf {m : ℕ} (hm : S.Ω (m + 1) = ∅) (x x' : Site NF) :
    (Blocks.dinf x x' : ℝ) / (S.L : ℝ) ^ m ≤ S.dF x x' := by
  have hL : 0 < S.L := S.Lpos
  have hscale : ∀ z, (S.toContSeq).D.scale z ≤ m := fun z => by
    by_contra h
    have h1 := ((S.toContSeq).D.mem_scale z).1
    have h2 := (S.toContSeq).D.Ω_anti (show m + 1 ≤ (S.toContSeq).D.scale z by omega) h1
    rw [D_Ω, hm] at h2
    exact h2
  have h := wdist_ge_scaled (S.toContSeq).D m hscale (S.ef x) (S.ef x')
  have hne := wdist_ne_top (S.toContSeq).D (S.ef x) (S.ef x')
  have hle : (sp S.L S.k m)⁻¹ * dist1 (S.ef x) (S.ef x') ≤ S.dF x x' := by
    unfold dF
    rw [← D_a, ← ENNReal.ofReal_le_iff_le_toReal hne]
    exact h
  have hd : ‖S.ef x - S.ef x'‖ = Blocks.dinf x x' * eta S.L S.k :=
    norm_emb_sub hL (SequenceAverages.N0_eq S) x x'
  have h3 := norm_le_dist1 S (S.ef x) (S.ef x')
  rw [hd] at h3
  have he : 0 < eta S.L S.k := eta_pos hL
  have hsp : sp S.L S.k m = (S.L : ℝ) ^ m * eta S.L S.k := rfl
  calc (Blocks.dinf x x' : ℝ) / (S.L : ℝ) ^ m = (sp S.L S.k m)⁻¹ * (Blocks.dinf x x' * eta S.L S.k) := by
        rw [hsp]; field_simp
    _ ≤ (sp S.L S.k m)⁻¹ * dist1 (S.ef x) (S.ef x') :=
        mul_le_mul_of_nonneg_left h3 (inv_nonneg.2 (by rw [hsp]; positivity))
    _ ≤ S.dF x x' := hle

end SeqDom
end Lattices
namespace SFBounds

open Lattices SeqDom Blocks SmallFieldBlocks SFLocal SmallFieldDecay SmallFieldCoercivity
  SequenceOperators CompressedInverse ConcretePairing SFBox SFBox.SeqDomBox

/-- **The test of Schur for a scalar kernel**: `u ≤ Kv`, `Σ_yK(x, y) ≤ A`, `Σ_xK(x, y) ≤ B` give
`Σu² ≤ ABΣv²`. -/
theorem schur_scalar {ι : Type*} [Fintype ι] (u v : ι → ℝ) (K : ι → ι → ℝ) (hK : ∀ x y, 0 ≤ K x y)
    (hu0 : ∀ x, 0 ≤ u x) (hu : ∀ x, u x ≤ ∑ y, K x y * v y) (A B : ℝ) (hA0 : 0 ≤ A)
    (hA : ∀ x, ∑ y, K x y ≤ A) (hB : ∀ y, ∑ x, K x y ≤ B) :
    ∑ x, u x ^ 2 ≤ A * B * ∑ y, v y ^ 2 := by
  have row : ∀ x, u x ^ 2 ≤ A * ∑ y, K x y * v y ^ 2 := fun x => by
    have h2 : (∑ y, K x y * v y) ^ 2 ≤ (∑ y, K x y) * ∑ y, K x y * v y ^ 2 :=
      Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun y _ => hK x y)
        (fun y _ => mul_nonneg (hK x y) (sq_nonneg _)) (fun y _ => le_of_eq (by ring))
    have h3 : 0 ≤ ∑ y, K x y * v y ^ 2 := Finset.sum_nonneg fun y _ => mul_nonneg (hK x y) (sq_nonneg _)
    calc u x ^ 2 ≤ (∑ y, K x y * v y) ^ 2 := pow_le_pow_left₀ (hu0 x) (hu x) 2
      _ ≤ (∑ y, K x y) * ∑ y, K x y * v y ^ 2 := h2
      _ ≤ A * ∑ y, K x y * v y ^ 2 := mul_le_mul_of_nonneg_right (hA x) h3
  calc ∑ x, u x ^ 2 ≤ ∑ x, A * ∑ y, K x y * v y ^ 2 := Finset.sum_le_sum fun x _ => row x
    _ = A * ∑ y, v y ^ 2 * ∑ x, K x y := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        congr 1
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun x _ => by ring
    _ ≤ A * ∑ y, v y ^ 2 * B := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y _ => ?_) hA0
        exact mul_le_mul_of_nonneg_left (hB y) (sq_nonneg _)
    _ = A * B * ∑ y, v y ^ 2 := by rw [← Finset.sum_mul]; ring

variable (S : SeqDom) {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "NF" => SequenceAverages.N0 S
local notation "RMS" => ((S.R * S.L ^ S.mM : ℕ) : ℝ)
set_option quotPrecheck false in
local notation "jj" => (S.toDomSeq).sc

lemma dF_bc_le (x : Site NF) : S.dF x (bc S.toDomSeq x) ≤ 2 := by
  rw [dF_comm]
  exact ENNReal.toReal_le_of_le_ofReal (by norm_num) (S.wdist_block_le (bc_mem_detB S x) (mem_blk_bc S x))

/-- The sum of a kernel of the block centres over the fine lattice: `Σ_{x'}a_{y(x')}^{-4}F(y(x')) = Σ_{y' ∈ 𝐁}F(y')`. -/
lemma sum_fine_bc (F : Site NF → ℝ) :
    ∑ x', ((S.L : ℝ) ^ (4 * jj (bc S.toDomSeq x')))⁻¹ * F (bc S.toDomSeq x') = ∑ y' ∈ detB S.toDomSeq, F y' := by
  rw [sum_blocks S.toDomSeq]
  refine sum_congr rfl fun y' hy' => ?_
  have e : ∀ x' ∈ Blk S.toDomSeq (jj y') y', ((S.L : ℝ) ^ (4 * jj (bc S.toDomSeq x')))⁻¹ * F (bc S.toDomSeq x') =
      ((S.L : ℝ) ^ (4 * jj y'))⁻¹ * F y' := fun x' hx' => by
    rw [(sc_mem_blk S.toDomSeq hy' hx').2]
  rw [sum_congr rfl e, sum_const, nsmul_eq_mul, card_Blk S hy']
  have : (0 : ℝ) < (S.L : ℝ) ^ (4 * jj y') := by have := S.Lpos; positivity
  field_simp

variable {S}

/-- **(I1) The weighted bound of `P`** at the trivial configuration for a sequence with the scales `i` and `i + 1`
only: `Σ_xe^{2φ(x)}|(Pf)(x)|² ≤ (C_Pe^{4κ})²c₁ · L⁴c₁ · Σ_xe^{2φ(x)}|f(x)|²` for `φ` with the Lipschitz constant
`κ ≤ θ/2` in the weighted distance, `θ = (7/32)θ_B` the rate of the kernel of `P`. -/
theorem P_weighted [NeZero N] {δ : ℝ} (H : ScalarHyp (N := N) S (X0 S) 0 (W1 S) 0 Set.univ δ)
    (hRMb : (S.toContSeq).r1 (1 / 2) (1 / 32 * δ) ≤ RMS) (hRMs4 : 32 * Real.log S.L / (1 / 4 * δ) ≤ RMS)
    (hsmallT : CTd S N δ 0 0 * (S.toContSeq).c1 (1 / 2) (1 / 32 * δ) ≤ gammaB N / 4)
    (hRMθs : 32 * Real.log S.L / (thetaB S N δ / 2) ≤ RMS)
    (hRMθc : (S.toContSeq).r1 (1 / 2) (7 / 16 * thetaB S N δ) ≤ RMS)
    (hRMsum : (S.toContSeq).r1 (1 / 2) (7 / 32 * thetaB S N δ) ≤ RMS)
    {i : ℕ} (hsc : ∀ x, i ≤ jj x ∧ jj x ≤ i + 1)
    (ph : Site NF → ℝ) {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1 / 2 * (7 / 32 * thetaB S N δ))
    (hph : ∀ x x', |ph x - ph x'| ≤ κ * S.dF x x') (f : Site NF → Mat) :
    ∑ x, Real.exp (2 * ph x) * hs2 (Pop S (X0 S) (W1 S) Set.univ f x) ≤
      (CPk S N δ * Real.exp (4 * κ)) ^ 2 * ((S.toContSeq).c1 (1 / 2) (7 / 32 * thetaB S N δ) *
        ((S.L : ℝ) ^ 4 * (S.toContSeq).c1 (1 / 2) (7 / 32 * thetaB S N δ))) *
        ∑ x, Real.exp (2 * ph x) * hs2 (f x) := by
  set θ := 7 / 32 * thetaB S N δ
  have hθ : 0 < θ := by have := H.thetaB_pos (N := N); positivity
  have hL : (0 : ℝ) < S.L := by exact_mod_cast S.Lpos
  have hCP : 0 ≤ CPk S N δ := by
    have h1 : 0 ≤ (S.toContSeq).c1 (1 / 2) (thetaB S N δ) := by unfold Summation.ContSeq.c1; positivity
    have h2 : 0 ≤ (S.toContSeq).c1 (1 / 2) (7 / 16 * thetaB S N δ) := by unfold Summation.ContSeq.c1; positivity
    unfold CPk gammaB; positivity
  set c1 := (S.toContSeq).c1 (1 / 2) θ
  have hc1 : 0 ≤ c1 := by unfold c1 Summation.ContSeq.c1; positivity
  -- the kernel
  set K : Site NF → Site NF → ℝ := fun x x' => ((S.L : ℝ) ^ (4 * jj (bc S.toDomSeq x')))⁻¹ *
    Real.exp (-(1 / 2 * θ * S.dF (bc S.toDomSeq x) (bc S.toDomSeq x')))
  have hK : ∀ x x', 0 ≤ K x x' := fun x x' => by positivity
  -- the pointwise bound with the weight
  have hpt : ∀ x, Real.exp (ph x) * hs (Pop S (X0 S) (W1 S) Set.univ f x) ≤
      ∑ x', (CPk S N δ * Real.exp (4 * κ) * K x x') * (Real.exp (ph x') * hs (f x')) := by
    intro x
    have hP := H.P_bound hRMb hRMs4 hsmallT hRMθs hRMθc f x
    calc Real.exp (ph x) * hs (Pop S (X0 S) (W1 S) Set.univ f x)
        ≤ Real.exp (ph x) * (CPk S N δ * ∑ x', ((S.L : ℝ) ^ (4 * jj (bc S.toDomSeq x')))⁻¹ *
          Real.exp (-(θ * S.dF (bc S.toDomSeq x) (bc S.toDomSeq x'))) * hs (f x')) :=
          mul_le_mul_of_nonneg_left hP (Real.exp_pos _).le
      _ ≤ _ := by
          rw [mul_sum, mul_sum]
          refine sum_le_sum fun x' _ => ?_
          have hd : ph x - ph x' ≤ κ * (4 + S.dF (bc S.toDomSeq x) (bc S.toDomSeq x')) := by
            have h1 := (abs_le.1 (hph x x')).2
            have h2 := S.dF_triangle x (bc S.toDomSeq x) x'
            have h3 := S.dF_triangle (bc S.toDomSeq x) (bc S.toDomSeq x') x'
            have h4 := dF_bc_le S x
            have h5 := dF_bc_le S x'
            rw [dF_comm] at h5
            nlinarith
          have hdF : 0 ≤ S.dF (bc S.toDomSeq x) (bc S.toDomSeq x') := ENNReal.toReal_nonneg
          have hexp : Real.exp (ph x) * Real.exp (-(θ * S.dF (bc S.toDomSeq x) (bc S.toDomSeq x'))) ≤
              Real.exp (4 * κ) * Real.exp (-(1 / 2 * θ * S.dF (bc S.toDomSeq x) (bc S.toDomSeq x'))) *
                Real.exp (ph x') := by
            rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
            refine Real.exp_le_exp.2 ?_
            nlinarith
          have hf0 := hs_nonneg (f x')
          have ha : 0 ≤ ((S.L : ℝ) ^ (4 * jj (bc S.toDomSeq x')))⁻¹ := by positivity
          calc Real.exp (ph x) * (CPk S N δ * (((S.L : ℝ) ^ (4 * jj (bc S.toDomSeq x')))⁻¹ *
                Real.exp (-(θ * S.dF (bc S.toDomSeq x) (bc S.toDomSeq x'))) * hs (f x')))
              = CPk S N δ * ((S.L : ℝ) ^ (4 * jj (bc S.toDomSeq x')))⁻¹ * hs (f x') *
                (Real.exp (ph x) * Real.exp (-(θ * S.dF (bc S.toDomSeq x) (bc S.toDomSeq x')))) := by ring
            _ ≤ CPk S N δ * ((S.L : ℝ) ^ (4 * jj (bc S.toDomSeq x')))⁻¹ * hs (f x') *
                (Real.exp (4 * κ) * Real.exp (-(1 / 2 * θ * S.dF (bc S.toDomSeq x) (bc S.toDomSeq x'))) *
                  Real.exp (ph x')) := mul_le_mul_of_nonneg_left hexp (by positivity)
            _ = _ := by simp only [K]; ring
  -- the sums of the kernel
  have hrow : ∀ x, ∑ x', K x x' ≤ c1 := fun x => by
    have := sum_fine_bc S (fun y' => Real.exp (-(1 / 2 * θ * S.dF (bc S.toDomSeq x) y')))
    simp only [K]
    rw [this]
    exact summation_fine S (by norm_num) hθ hRMsum (bc_mem_detB S x)
  have hcol : ∀ x', ∑ x, K x x' ≤ (S.L : ℝ) ^ 4 * c1 := fun x' => by
    set y' := bc S.toDomSeq x'
    have hratio : ∀ x, ((S.L : ℝ) ^ (4 * jj y'))⁻¹ ≤ (S.L : ℝ) ^ 4 * ((S.L : ℝ) ^ (4 * jj (bc S.toDomSeq x)))⁻¹ := by
      intro x
      have h1 := hsc (bc S.toDomSeq x)
      have h2 := hsc x'
      rw [sc_bc] at h1
      rw [show jj y' = jj x' from sc_bc _ x']
      have hL1 : (1 : ℝ) ≤ S.L := by exact_mod_cast S.Lpos
      rw [show jj (bc S.toDomSeq x) = jj x from sc_bc _ x]
      rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), ← div_eq_inv_mul, div_le_iff₀ (by positivity)]
      rw [← pow_add]
      exact pow_le_pow_right₀ hL1 (by omega)
    calc ∑ x, K x x' ≤ ∑ x, (S.L : ℝ) ^ 4 * (((S.L : ℝ) ^ (4 * jj (bc S.toDomSeq x)))⁻¹ *
          Real.exp (-(1 / 2 * θ * S.dF y' (bc S.toDomSeq x)))) := by
          refine sum_le_sum fun x _ => ?_
          simp only [K]
          rw [dF_comm]
          have := hratio x
          have he : 0 ≤ Real.exp (-(1 / 2 * θ * S.dF y' (bc S.toDomSeq x))) := (Real.exp_pos _).le
          nlinarith
      _ = (S.L : ℝ) ^ 4 * ∑ y ∈ detB S.toDomSeq, Real.exp (-(1 / 2 * θ * S.dF y' y)) := by
          rw [← mul_sum, sum_fine_bc S (fun y => Real.exp (-(1 / 2 * θ * S.dF y' y)))]
      _ ≤ (S.L : ℝ) ^ 4 * c1 :=
          mul_le_mul_of_nonneg_left (summation_fine S (by norm_num) hθ hRMsum (bc_mem_detB S x')) (by positivity)
  -- Schur
  have hS := schur_scalar (fun x => Real.exp (ph x) * hs (Pop S (X0 S) (W1 S) Set.univ f x))
    (fun x' => Real.exp (ph x') * hs (f x')) (fun x x' => CPk S N δ * Real.exp (4 * κ) * K x x')
    (fun x x' => by have := hK x x'; positivity) (fun x => by have := hs_nonneg (Pop S (X0 S) (W1 S) Set.univ f x); positivity)
    hpt (CPk S N δ * Real.exp (4 * κ) * c1) (CPk S N δ * Real.exp (4 * κ) * ((S.L : ℝ) ^ 4 * c1)) (by positivity)
    (fun x => by rw [← mul_sum]; exact mul_le_mul_of_nonneg_left (hrow x) (by positivity))
    (fun x' => by rw [← mul_sum]; exact mul_le_mul_of_nonneg_left (hcol x') (by positivity))
  have e1 : ∀ x, (Real.exp (ph x) * hs (Pop S (X0 S) (W1 S) Set.univ f x)) ^ 2 =
      Real.exp (2 * ph x) * hs2 (Pop S (X0 S) (W1 S) Set.univ f x) := fun x => by
    rw [mul_pow, ← Real.exp_nat_mul, hs_sq]; norm_num
  have e2 : ∀ x, (Real.exp (ph x) * hs (f x)) ^ 2 = Real.exp (2 * ph x) * hs2 (f x) := fun x => by
    rw [mul_pow, ← Real.exp_nat_mul, hs_sq]; norm_num
  simp only [e1, e2] at hS
  refine hS.trans (le_of_eq ?_)
  ring

end SFBounds

namespace SFBounds

open Lattices SeqDom Blocks SmallFieldBlocks SFLocal SmallFieldDecay SmallFieldCoercivity
  SequenceOperators CompressedInverse ConcretePairing SFBox SFBox.SeqDomBox

variable (S : SeqDom) {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "NF" => SequenceAverages.N0 S

lemma expCfg_zero : S.expCfg (N := N) 0 = cfgX (X0 S) := by
  funext μ x
  simp [expCfg, cfgX, X0]

variable {S}

/-- **(I2) The weighted bound of the minimiser** (eq:sf-decay at the trivial configuration):
`‖e^φλ‖_w + ‖∂(e^φλ)‖₂ ≤ 12‖e^φRf‖_{w⁻¹}` for `λ = G'Rf` and `φ` with the Lipschitz constant `κ ≤ 1/(128L)` in the
weighted distance. -/
theorem minim_weighted [NeZero N] (hRM : 1 ≤ S.R * S.L ^ S.mM) (ph : Site NF → ℝ) {κ : ℝ} (hκ0 : 0 ≤ κ)
    (hκ : κ ≤ 1 / (128 * S.L)) (hph : ∀ x x', |ph x - ph x'| ≤ κ * S.dF x x') (f : Site NF → Mat) :
    Real.sqrt (wnormM S.toDomSeq (expS ph (minim S f))) + Real.sqrt (dsqM (expS ph (minim S f))) ≤
      12 * Real.sqrt (fwinv S.toDomSeq ph (f - Pop S (X0 S) (W1 S) Set.univ f)) := by
  have hN : (1 : ℝ) ≤ Real.sqrt N := by
    rw [Real.one_le_sqrt]; exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have h := S.sf_decay_seq hRM 0 (W1 S) Set.univ ph κ 0 0 hκ0 hκ le_rfl (by norm_num) le_rfl hph
    (fun j x μ _ _ => by simp only [Pi.zero_apply, zero_mul]; exact le_of_eq norm_zero) (fun y _ x _ Z => by simp [Ad, hs, hs2, ntr])
    (fun y _ x _ Z => by
      have e : Ad (W1 S y x) Z = Z := by simp [Ad]
      rw [e]; have := hs_nonneg Z; nlinarith)
    (by norm_num) (f - Pop S (X0 S) (W1 S) Set.univ f) 0
  rw [map_zero, add_zero, expCfg_zero] at h
  have hg : gnorm (N := N) ph (0 : Form1 N NF) = 0 := by simp [gnorm, hs2, ntr]
  rw [hg, Real.sqrt_zero, mul_zero, add_zero] at h
  exact h

end SFBounds

namespace SFBounds

open Lattices SeqDom Blocks SmallFieldBlocks SFLocal SmallFieldDecay SmallFieldCoercivity
  SequenceOperators CompressedInverse ConcretePairing SFBox SFBox.SeqDomBox

variable {S : SeqDom} {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "NF" => SequenceAverages.N0 S
set_option quotPrecheck false in
local notation "jj" => (S.toDomSeq).sc

/-- **(S1) The tail of a weighted sum**: where `φ ≥ Φ`, `Σ_{x ∈ Z}|u|² ≤ e^{-2Φ}Σ_xe^{2φ}|u|²`. -/
lemma weight_tail (u : Site NF → Mat) (ph : Site NF → ℝ) (Z : Finset (Site NF)) {Φ : ℝ}
    (hZ : ∀ x ∈ Z, Φ ≤ ph x) :
    ∑ x ∈ Z, hs2 (u x) ≤ Real.exp (-(2 * Φ)) * ∑ x, Real.exp (2 * ph x) * hs2 (u x) := by
  rw [mul_sum]
  refine (sum_le_sum fun x hx => ?_).trans (sum_le_sum_of_subset_of_nonneg (subset_univ Z) fun x _ _ => ?_)
  · have h1 : 1 ≤ Real.exp (-(2 * Φ)) * Real.exp (2 * ph x) := by
      rw [← Real.exp_add]; exact Real.one_le_exp (by linarith [hZ x hx])
    have := hs2_nonneg (u x)
    nlinarith
  · have := hs2_nonneg (u x); positivity

/-- **(S2)** For a sequence with the scales at most `m`: `‖e^φg‖²_{w⁻¹} ≤ L^{2m}Σ_xe^{2φ}|g|²`. -/
lemma fwinv_le {m : ℕ} (hsc : ∀ x, jj x ≤ m) (ph : Site NF → ℝ) (g : Site NF → Mat) :
    fwinv S.toDomSeq ph g ≤ (S.L : ℝ) ^ (2 * m) * ∑ x, Real.exp (2 * ph x) * hs2 (g x) := by
  unfold fwinv
  rw [mul_sum]
  refine sum_le_sum fun x _ => ?_
  have hL1 : (1 : ℝ) ≤ S.L := by exact_mod_cast S.Lpos
  have h1 : (S.L : ℝ) ^ (2 * jj x) ≤ (S.L : ℝ) ^ (2 * m) := pow_le_pow_right₀ hL1 (by have := hsc x; omega)
  have := hs2_nonneg (g x)
  have : 0 ≤ Real.exp (2 * ph x) := (Real.exp_pos _).le
  show (S.toDomSeq.L : ℝ) ^ (2 * jj x) * Real.exp (2 * ph x) * hs2 (g x) ≤ _
  rw [toDomSeq_L]
  have h2 : 0 ≤ Real.exp (2 * ph x) * hs2 (g x) := by positivity
  calc (S.L : ℝ) ^ (2 * jj x) * Real.exp (2 * ph x) * hs2 (g x)
      = (S.L : ℝ) ^ (2 * jj x) * (Real.exp (2 * ph x) * hs2 (g x)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right h1 h2

/-- **(S3)** `Σe^{2φ}|f - g|² ≤ 2Σe^{2φ}|f|² + 2Σe^{2φ}|g|²`. -/
lemma weighted_sub_le (ph : Site NF → ℝ) (f g : Site NF → Mat) :
    ∑ x, Real.exp (2 * ph x) * hs2 ((f - g) x) ≤
      2 * ∑ x, Real.exp (2 * ph x) * hs2 (f x) + 2 * ∑ x, Real.exp (2 * ph x) * hs2 (g x) := by
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun x _ => ?_
  have h : hs2 ((f - g) x) ≤ 2 * hs2 (f x) + 2 * hs2 (g x) := by
    rw [← hs_sq, ← hs_sq, ← hs_sq, Pi.sub_apply, sub_eq_add_neg]
    have h1 := hs_add_le (f x) (-g x)
    have h2 : hs (-g x) = hs (g x) := by
      have : hs2 (-g x) = hs2 (g x) := by
        rw [show -g x = (-1 : ℂ) • g x by simp, RegularAverages.hs2_smul]; simp
      unfold hs; rw [this]
    rw [h2] at h1
    have := hs_nonneg (f x + -g x); have := hs_nonneg (f x); have := hs_nonneg (g x)
    nlinarith [sq_nonneg (hs (f x) - hs (g x))]
  have := (Real.exp_pos (2 * ph x)).le
  nlinarith

/-- **(S4)** For a sequence with the scales at most `m`: `Σ_xe^{2φ}|λ|² ≤ L^{2m}‖e^φλ‖_w²`. -/
lemma weighted_le_wnorm {m : ℕ} (hsc : ∀ x, jj x ≤ m) (ph : Site NF → ℝ) (lam : Site NF → Mat) :
    ∑ x, Real.exp (2 * ph x) * hs2 (lam x) ≤ (S.L : ℝ) ^ (2 * m) * wnormM S.toDomSeq (expS ph lam) := by
  unfold wnormM expS
  rw [mul_sum]
  refine sum_le_sum fun x _ => ?_
  have hL1 : (1 : ℝ) ≤ S.L := by exact_mod_cast S.Lpos
  have hLp : (0 : ℝ) < (S.L : ℝ) ^ (2 * jj x) := by positivity
  rw [RegularAverages.hs2_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), sq,
    ← Real.exp_add, show ph x + ph x = 2 * ph x by ring]
  show _ ≤ (S.L : ℝ) ^ (2 * m) * (((S.toDomSeq.L : ℝ) ^ (2 * jj x))⁻¹ * (Real.exp (2 * ph x) * hs2 (lam x)))
  rw [toDomSeq_L]
  have h1 : (S.L : ℝ) ^ (2 * jj x) ≤ (S.L : ℝ) ^ (2 * m) := pow_le_pow_right₀ hL1 (by have := hsc x; omega)
  have h0 : 0 ≤ Real.exp (2 * ph x) * hs2 (lam x) := by have := hs2_nonneg (lam x); positivity
  rw [← mul_assoc]
  refine le_mul_of_one_le_left h0 ?_
  rw [← div_eq_mul_inv, one_le_div hLp]; exact h1

end SFBounds

namespace SFBounds

open Lattices SeqDom Blocks SmallFieldBlocks SFLocal SmallFieldDecay SmallFieldCoercivity
  SequenceOperators CompressedInverse ConcretePairing SFBox SFBox.SeqDomBox

variable {S : SeqDom} {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "NF" => SequenceAverages.N0 S

/-- **A multiplier which vanishes where `φ < Φ`**: `Σ|m u|² ≤ g²e^{-2Φ}Σe^{2φ}|u|²` for `|m| ≤ g`. -/
lemma mult_tail (m : Site NF → ℝ) (u : Site NF → Mat) (ph : Site NF → ℝ) {g Φ : ℝ}
    (hm : ∀ x, |m x| ≤ g) (hΦ : ∀ x, m x ≠ 0 → Φ ≤ ph x) :
    ∑ x, hs2 ((m x : ℂ) • u x) ≤ g ^ 2 * (Real.exp (-(2 * Φ)) * ∑ x, Real.exp (2 * ph x) * hs2 (u x)) := by
  rw [mul_sum, mul_sum]
  refine sum_le_sum fun x _ => ?_
  rw [RegularAverages.hs2_smul, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hu := hs2_nonneg (u x)
  by_cases h : m x = 0
  · rw [h]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul]; positivity
  · have h1 : 1 ≤ Real.exp (-(2 * Φ)) * Real.exp (2 * ph x) := by
      rw [← Real.exp_add]; exact Real.one_le_exp (by linarith [hΦ x h])
    have h2 : m x ^ 2 ≤ g ^ 2 := by
      have := hm x
      have h0 : 0 ≤ g := (abs_nonneg _).trans this
      exact sq_le_sq' (by linarith [neg_abs_le (m x)]) ((le_abs_self _).trans this)
    have hg : 0 ≤ g ^ 2 := sq_nonneg _
    calc m x ^ 2 * hs2 (u x) ≤ g ^ 2 * hs2 (u x) := mul_le_mul_of_nonneg_right h2 hu
      _ ≤ g ^ 2 * (Real.exp (-(2 * Φ)) * (Real.exp (2 * ph x) * hs2 (u x))) := by
          refine mul_le_mul_of_nonneg_left ?_ hg
          rw [← mul_assoc]; exact le_mul_of_one_le_left hu h1

/-- **(A1)** `Σ|(1 - χ)u|² ≤ e^{-2Φ}Σe^{2φ}|u|²` for `0 ≤ χ ≤ 1` and `φ ≥ Φ` where `χ ≠ 1`. -/
lemma A1_bound (χ : Site NF → ℝ) (u : Site NF → Mat) (ph : Site NF → ℝ) {Φ : ℝ}
    (hχ : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) (hΦ : ∀ x, χ x ≠ 1 → Φ ≤ ph x) :
    ∑ x, hs2 (((1 - χ x : ℝ) : ℂ) • u x) ≤ Real.exp (-(2 * Φ)) * ∑ x, Real.exp (2 * ph x) * hs2 (u x) := by
  have h := mult_tail (fun x => 1 - χ x) u ph (g := 1) (Φ := Φ)
    (fun x => by have := hχ x; rw [abs_le]; constructor <;> linarith)
    (fun x hx => hΦ x (fun h => hx (by simp only [h, sub_self])))
  simpa using h

end SFBounds

namespace SFBounds

open Lattices SeqDom Blocks SmallFieldBlocks SFLocal SmallFieldDecay SmallFieldCoercivity
  SequenceOperators CompressedInverse ConcretePairing SFBox SFBox.SeqDomBox

variable {S : SeqDom} {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "NF" => SequenceAverages.N0 S

lemma hs2_add_le (X Y : Mat) : hs2 (X + Y) ≤ 2 * hs2 X + 2 * hs2 Y := by
  rw [← hs_sq, ← hs_sq, ← hs_sq]
  have h1 := hs_add_le X Y
  have := hs_nonneg (X + Y); have := hs_nonneg X; have := hs_nonneg Y
  nlinarith [sq_nonneg (hs X - hs Y)]

/-- **The difference of `λ` with the weight**: `e^{2a}|q - p|² ≤ 2|e^bq - e^ap|² + 8ε²e^{2b}|q|²` for `|a - b| ≤ ε ≤ 1`. -/
lemma weighted_diff (a b ε : ℝ) (hab : |a - b| ≤ ε) (hε : ε ≤ 1) (p q : Mat) :
    Real.exp (2 * a) * hs2 (q - p) ≤
      2 * hs2 (((Real.exp b : ℝ) : ℂ) • q - ((Real.exp a : ℝ) : ℂ) • p) + 8 * ε ^ 2 * (Real.exp (2 * b) * hs2 q) := by
  have e1 : ((Real.exp a : ℝ) : ℂ) • (q - p) = (((Real.exp b : ℝ) : ℂ) • q - ((Real.exp a : ℝ) : ℂ) • p) +
      ((Real.exp a - Real.exp b : ℝ) : ℂ) • q := by push_cast; module
  have h1 := hs2_add_le (((Real.exp b : ℝ) : ℂ) • q - ((Real.exp a : ℝ) : ℂ) • p) (((Real.exp a - Real.exp b : ℝ) : ℂ) • q)
  rw [← e1] at h1
  rw [RegularAverages.hs2_smul, RegularAverages.hs2_smul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, sq_abs, sq_abs] at h1
  have h2 : |Real.exp a - Real.exp b| ≤ 2 * ε * Real.exp b := by
    have e2 : Real.exp a - Real.exp b = Real.exp b * (Real.exp (a - b) - 1) := by
      rw [mul_sub, ← Real.exp_add]; ring_nf
    rw [e2, abs_mul, abs_of_pos (Real.exp_pos b)]
    have := Real.abs_exp_sub_one_le (hab.trans hε)
    have := Real.exp_pos b
    nlinarith
  have h3 : (Real.exp a - Real.exp b) ^ 2 ≤ 4 * ε ^ 2 * Real.exp (2 * b) := by
    have h4 : (Real.exp a - Real.exp b) ^ 2 ≤ (2 * ε * Real.exp b) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h2 2
    have e3 : (2 * ε * Real.exp b) ^ 2 = 4 * ε ^ 2 * Real.exp (2 * b) := by
      rw [mul_pow, mul_pow, ← Real.exp_nat_mul]; norm_num
    linarith
  have hq := hs2_nonneg q
  have e4 : Real.exp a ^ 2 = Real.exp (2 * a) := by rw [← Real.exp_nat_mul]; norm_num
  rw [e4] at h1
  nlinarith

/-- **(A3), one direction and sign**: for `|φ(x') - φ(x)| ≤ ε ≤ 1` at the bonds, `x' = x ± e_ν`,
`Σ_xe^{2φ(x)}|λ(x') - λ(x)|² ≤ 2Σ_x|(e^φλ)(x') - (e^φλ)(x)|² + 8ε²Σ_xe^{2φ}|λ|²`. -/
lemma weighted_diff_sum (lam : Site NF → Mat) (ph : Site NF → ℝ) (s : Site NF) {ε : ℝ} (hε : ε ≤ 1)
    (hph : ∀ x, |ph x - ph (x + s)| ≤ ε) :
    ∑ x, Real.exp (2 * ph x) * hs2 (lam (x + s) - lam x) ≤
      2 * ∑ x, hs2 (expS ph lam (x + s) - expS ph lam x) + 8 * ε ^ 2 * ∑ x, Real.exp (2 * ph x) * hs2 (lam x) := by
  have h := fun x => weighted_diff (ph x) (ph (x + s)) ε (hph x) hε (lam x) (lam (x + s))
  have hshift : ∑ x, Real.exp (2 * ph (x + s)) * hs2 (lam (x + s)) = ∑ x, Real.exp (2 * ph x) * hs2 (lam x) :=
    Fintype.sum_equiv (Equiv.addRight s) _ _ fun _ => rfl
  calc ∑ x, Real.exp (2 * ph x) * hs2 (lam (x + s) - lam x)
      ≤ ∑ x, (2 * hs2 (expS ph lam (x + s) - expS ph lam x) +
          8 * ε ^ 2 * (Real.exp (2 * ph (x + s)) * hs2 (lam (x + s)))) := sum_le_sum fun x _ => h x
    _ = _ := by rw [sum_add_distrib, ← mul_sum, ← mul_sum, hshift]

end SFBounds

namespace SFBounds

open Lattices SeqDom Blocks SmallFieldBlocks SFLocal SmallFieldDecay SmallFieldCoercivity
  SequenceOperators CompressedInverse ConcretePairing SFBox SFBox.SeqDomBox

variable {S : SeqDom} {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "NF" => SequenceAverages.N0 S

lemma hs2_sub_comm (X Y : Mat) : hs2 (X - Y) = hs2 (Y - X) := by
  rw [show X - Y = (-1 : ℂ) • (Y - X) by simp, RegularAverages.hs2_smul]; simp

lemma hs2_sum4_le (v : Fin 4 → Mat) : hs2 (∑ ν, v ν) ≤ 4 * ∑ ν, hs2 (v ν) := by
  rw [← hs_sq]
  have h1 : hs (∑ ν, v ν) ≤ ∑ ν, hs (v ν) := by
    rw [Fin.sum_univ_four, Fin.sum_univ_four]
    calc hs (v 0 + v 1 + v 2 + v 3) ≤ hs (v 0 + v 1 + v 2) + hs (v 3) := hs_add_le _ _
      _ ≤ hs (v 0 + v 1) + hs (v 2) + hs (v 3) := by linarith [hs_add_le (v 0 + v 1) (v 2)]
      _ ≤ hs (v 0) + hs (v 1) + hs (v 2) + hs (v 3) := by linarith [hs_add_le (v 0) (v 1)]
  have h2 := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Fin 4))) (f := fun ν => hs (v ν))
  simp only [card_univ, Fintype.card_fin, hs_sq] at h2
  have h0 := hs_nonneg (∑ ν, v ν)
  calc hs (∑ ν, v ν) ^ 2 ≤ (∑ ν, hs (v ν)) ^ 2 := pow_le_pow_left₀ h0 h1 2
    _ ≤ _ := by exact_mod_cast h2

/-- **(A3)** The terms of the derivatives of the cut-off. -/
theorem A3_bound (χ : Site NF → ℝ) (lam : Site NF → Mat) (ph : Site NF → ℝ) {g1 Φ ε : ℝ}
    (hg1 : ∀ x ν, |χ (x + unit NF ν) - χ x| ≤ g1 ∧ |χ (x - unit NF ν) - χ x| ≤ g1)
    (hΦ : ∀ x ν, (χ (x + unit NF ν) - χ x ≠ 0 ∨ χ (x - unit NF ν) - χ x ≠ 0) → Φ ≤ ph x)
    (hε : ε ≤ 1) (hph : ∀ x ν, |ph x - ph (x + unit NF ν)| ≤ ε ∧ |ph x - ph (x + -unit NF ν)| ≤ ε) :
    ∑ x, hs2 (∑ ν, (((χ (x + unit NF ν) - χ x : ℝ) : ℂ) • (lam (x + unit NF ν) - lam x) +
        ((χ (x - unit NF ν) - χ x : ℝ) : ℂ) • (lam (x - unit NF ν) - lam x))) ≤
      g1 ^ 2 * (Real.exp (-(2 * Φ)) * (128 * dsqM (expS ph lam) +
        512 * ε ^ 2 * ∑ x, Real.exp (2 * ph x) * hs2 (lam x))) := by
  set W := ∑ x, Real.exp (2 * ph x) * hs2 (lam x)
  set D := dsqM (expS ph lam)
  -- the pointwise splitting
  have hpt : ∀ x, hs2 (∑ ν, (((χ (x + unit NF ν) - χ x : ℝ) : ℂ) • (lam (x + unit NF ν) - lam x) +
      ((χ (x - unit NF ν) - χ x : ℝ) : ℂ) • (lam (x - unit NF ν) - lam x))) ≤
      8 * ∑ ν, (hs2 (((χ (x + unit NF ν) - χ x : ℝ) : ℂ) • (lam (x + unit NF ν) - lam x)) +
        hs2 (((χ (x - unit NF ν) - χ x : ℝ) : ℂ) • (lam (x - unit NF ν) - lam x))) := fun x => by
    refine (hs2_sum4_le _).trans ?_
    rw [mul_sum, mul_sum]
    refine sum_le_sum fun ν _ => ?_
    have := hs2_add_le (((χ (x + unit NF ν) - χ x : ℝ) : ℂ) • (lam (x + unit NF ν) - lam x))
      (((χ (x - unit NF ν) - χ x : ℝ) : ℂ) • (lam (x - unit NF ν) - lam x))
    linarith
  -- one direction and sign
  have hD : ∀ ν, ∑ x, hs2 (expS ph lam (x + unit NF ν) - expS ph lam x) ≤ D := fun ν => by
    unfold D dsqM
    rw [sum_comm]
    exact single_le_sum (f := fun μ => ∑ x, hs2 (expS ph lam (x + unit NF μ) - expS ph lam x))
      (fun μ _ => sum_nonneg fun x _ => hs2_nonneg _) (mem_univ ν)
  have hDm : ∀ ν, ∑ x, hs2 (expS ph lam (x + -unit NF ν) - expS ph lam x) ≤ D := fun ν => by
    have e : ∑ x, hs2 (expS ph lam (x + -unit NF ν) - expS ph lam x) =
        ∑ x, hs2 (expS ph lam (x + unit NF ν) - expS ph lam x) := by
      rw [← sum_shift_site S (fun x => hs2 (expS ph lam (x + -unit NF ν) - expS ph lam x)) (unit NF ν)]
      refine sum_congr rfl fun x _ => ?_
      simp only [add_neg_cancel_right]
      exact hs2_sub_comm _ _
    rw [e]; exact hD ν
  have hplus : ∀ ν, ∑ x, hs2 (((χ (x + unit NF ν) - χ x : ℝ) : ℂ) • (lam (x + unit NF ν) - lam x)) ≤
      g1 ^ 2 * (Real.exp (-(2 * Φ)) * (2 * D + 8 * ε ^ 2 * W)) := fun ν => by
    have h1 := mult_tail (fun x => χ (x + unit NF ν) - χ x) (fun x => lam (x + unit NF ν) - lam x) ph
      (g := g1) (Φ := Φ) (fun x => (hg1 x ν).1) (fun x hx => hΦ x ν (Or.inl hx))
    have h2 := weighted_diff_sum lam ph (unit NF ν) hε (fun x => (hph x ν).1)
    have hg : 0 ≤ g1 ^ 2 * Real.exp (-(2 * Φ)) := by positivity
    calc _ ≤ g1 ^ 2 * (Real.exp (-(2 * Φ)) * ∑ x, Real.exp (2 * ph x) * hs2 (lam (x + unit NF ν) - lam x)) := h1
      _ ≤ g1 ^ 2 * (Real.exp (-(2 * Φ)) * (2 * D + 8 * ε ^ 2 * W)) := by
          rw [← mul_assoc, ← mul_assoc]
          refine mul_le_mul_of_nonneg_left (h2.trans ?_) hg
          linarith [hD ν]
  have hminus : ∀ ν, ∑ x, hs2 (((χ (x - unit NF ν) - χ x : ℝ) : ℂ) • (lam (x - unit NF ν) - lam x)) ≤
      g1 ^ 2 * (Real.exp (-(2 * Φ)) * (2 * D + 8 * ε ^ 2 * W)) := fun ν => by
    have h1 := mult_tail (fun x => χ (x - unit NF ν) - χ x) (fun x => lam (x - unit NF ν) - lam x) ph
      (g := g1) (Φ := Φ) (fun x => (hg1 x ν).2) (fun x hx => hΦ x ν (Or.inr hx))
    have h2 := weighted_diff_sum lam ph (-unit NF ν) hε (fun x => (hph x ν).2)
    simp only [← sub_eq_add_neg] at h2
    have hg : 0 ≤ g1 ^ 2 * Real.exp (-(2 * Φ)) := by positivity
    have hDm' := hDm ν
    simp only [← sub_eq_add_neg] at hDm'
    calc _ ≤ g1 ^ 2 * (Real.exp (-(2 * Φ)) * ∑ x, Real.exp (2 * ph x) * hs2 (lam (x - unit NF ν) - lam x)) := h1
      _ ≤ g1 ^ 2 * (Real.exp (-(2 * Φ)) * (2 * D + 8 * ε ^ 2 * W)) := by
          rw [← mul_assoc, ← mul_assoc]
          refine mul_le_mul_of_nonneg_left (h2.trans ?_) hg
          linarith
  calc _ ≤ ∑ x, 8 * ∑ ν, (hs2 (((χ (x + unit NF ν) - χ x : ℝ) : ℂ) • (lam (x + unit NF ν) - lam x)) +
        hs2 (((χ (x - unit NF ν) - χ x : ℝ) : ℂ) • (lam (x - unit NF ν) - lam x))) := sum_le_sum fun x _ => hpt x
    _ = 8 * ∑ ν, (∑ x, hs2 (((χ (x + unit NF ν) - χ x : ℝ) : ℂ) • (lam (x + unit NF ν) - lam x)) +
        ∑ x, hs2 (((χ (x - unit NF ν) - χ x : ℝ) : ℂ) • (lam (x - unit NF ν) - lam x))) := by
        rw [← mul_sum, sum_comm]; simp only [sum_add_distrib]
    _ ≤ 8 * ∑ _ν : Fin 4, (2 * (g1 ^ 2 * (Real.exp (-(2 * Φ)) * (2 * D + 8 * ε ^ 2 * W)))) := by
        refine mul_le_mul_of_nonneg_left (sum_le_sum fun ν _ => ?_) (by norm_num)
        linarith [hplus ν, hminus ν]
    _ = _ := by simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

end SFBounds

namespace SFBounds

open Lattices SeqDom Blocks SmallFieldBlocks SFLocal SmallFieldDecay SmallFieldCoercivity
  SequenceOperators CompressedInverse ConcretePairing SFBox SFBox.SeqDomBox

variable (S : SeqDom) {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "NF" => SequenceAverages.N0 S
set_option quotPrecheck false in
local notation "jj" => (S.toDomSeq).sc

/-- The constant of the Laplacian of `b_y`. -/
def Cbump : ℝ := 4608 * (16 / 9) ^ 4

/-- **`|Δb_y| ≤ C_b a_y^{-2}`.** -/
theorem lapR_bfun_le {y : Site NF} (hy : y ∈ detB S.toDomSeq) (x : Site NF) :
    |lapR S (bfun S y) x| ≤ Cbump * ((S.L : ℝ) ^ (2 * jj y))⁻¹ := by
  set h := half S.L (jj y)
  have hn : ((S.L : ℝ) ^ jj y) = 2 * h + 1 := by exact_mod_cast (two_half_add_one S.L_odd (jj y)).symm
  have hh : (0 : ℝ) < (h : ℝ) + 1 := by positivity
  set Z := ∑ x' ∈ Blk S.toDomSeq (jj y) y, zeta S y x'
  have hZ : ((9 / 16) * ((h : ℝ) + 1)) ^ 4 ≤ Z := zeta_mass S hy
  have hZ0 : 0 < Z := zeta_sum_pos S hy
  -- the normalisation `κ = a⁴/Σζ ≤ 16(16/9)⁴`
  set κ := (S.L : ℝ) ^ (4 * jj y) / Z
  have hκ : κ ≤ 16 * (16 / 9) ^ 4 := by
    have h4 : (S.L : ℝ) ^ (4 * jj y) = (2 * h + 1) ^ 4 := by rw [pow_mul', hn]
    have h5 : ((2 : ℝ) * h + 1) ^ 4 ≤ 16 * ((h : ℝ) + 1) ^ 4 := by
      have : (2 : ℝ) * h + 1 ≤ 2 * ((h : ℝ) + 1) := by linarith
      calc ((2 : ℝ) * h + 1) ^ 4 ≤ (2 * ((h : ℝ) + 1)) ^ 4 := pow_le_pow_left₀ (by positivity) this 4
        _ = 16 * ((h : ℝ) + 1) ^ 4 := by ring
    rw [div_le_iff₀ hZ0, h4]
    calc ((2 : ℝ) * h + 1) ^ 4 ≤ 16 * ((h : ℝ) + 1) ^ 4 := h5
      _ = 16 * (16 / 9) ^ 4 * (((9 / 16) * ((h : ℝ) + 1)) ^ 4) := by ring
      _ ≤ 16 * (16 / 9) ^ 4 * Z := mul_le_mul_of_nonneg_left hZ (by positivity)
  have hκ0 : 0 ≤ κ := by positivity
  -- the Laplacian
  have e : lapR S (bfun S y) x = -κ * ∑ ν, (zeta S y (x + unit NF ν) - 2 * zeta S y x + zeta S y (x - unit NF ν)) := by
    simp only [lapR, bfun, mul_sum]
    refine sum_congr rfl fun ν _ => ?_
    simp only [κ, Z]; ring
  have hsec : ∀ ν, |zeta S y (x + unit NF ν) - 2 * zeta S y x + zeta S y (x - unit NF ν)| ≤ 18 / cB h :=
    fun ν => zeta_second S hy x ν
  have hsum : |∑ ν, (zeta S y (x + unit NF ν) - 2 * zeta S y x + zeta S y (x - unit NF ν))| ≤ 4 * (18 / cB h) := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ ν, |zeta S y (x + unit NF ν) - 2 * zeta S y x + zeta S y (x - unit NF ν)| ≤ ∑ _ν : Fin 4, 18 / cB h :=
          sum_le_sum fun ν _ => hsec ν
      _ = 4 * (18 / cB h) := by simp
  have hcB : 18 / cB h ≤ 72 * ((S.L : ℝ) ^ (2 * jj y))⁻¹ := by
    have h2 : (S.L : ℝ) ^ (2 * jj y) = (2 * h + 1) ^ 2 := by rw [pow_mul', hn]
    rw [h2, cB, div_le_iff₀ (by positivity)]
    have hp : (0 : ℝ) < (2 * (h : ℝ) + 1) ^ 2 := by positivity
    field_simp
    nlinarith
  rw [e, abs_mul, abs_neg, abs_of_nonneg hκ0]
  calc κ * |∑ ν, (zeta S y (x + unit NF ν) - 2 * zeta S y x + zeta S y (x - unit NF ν))|
      ≤ (16 * (16 / 9) ^ 4) * (4 * (72 * ((S.L : ℝ) ^ (2 * jj y))⁻¹)) := by
        refine mul_le_mul hκ (hsum.trans ?_) (abs_nonneg _) (by positivity)
        linarith
    _ = Cbump * ((S.L : ℝ) ^ (2 * jj y))⁻¹ := by unfold Cbump; ring

end SFBounds

namespace SFBounds

open Lattices SeqDom Blocks SmallFieldBlocks SFLocal SmallFieldDecay SmallFieldCoercivity
  SequenceOperators CompressedInverse ConcretePairing SFBox SFBox.SeqDomBox

variable (S : SeqDom) {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "NF" => SequenceAverages.N0 S
set_option quotPrecheck false in
local notation "jj" => (S.toDomSeq).sc


lemma hs_sum_le {ι : Type*} (s : Finset ι) (v : ι → Mat) : hs (∑ i ∈ s, v i) ≤ ∑ i ∈ s, hs (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hs, hs2, ntr]
  | insert a s ha ih => rw [sum_insert ha, sum_insert ha]; exact (hs_add_le _ _).trans (by linarith)

lemma hs2_sum_le_card {ι : Type*} (s : Finset ι) (v : ι → Mat) :
    hs2 (∑ i ∈ s, v i) ≤ s.card * ∑ i ∈ s, hs2 (v i) := by
  rw [← hs_sq]
  have h2 := sq_sum_le_card_mul_sum_sq (s := s) (f := fun i => hs (v i))
  simp only [hs_sq] at h2
  exact (pow_le_pow_left₀ (hs_nonneg _) (hs_sum_le s v) 2).trans h2

/-- The nine sites `x`, `x ± e_ν`. -/
def nb9 (x : Site NF) : Finset (Site NF) :=
  insert x (Finset.univ.image (fun ν => x + unit NF ν) ∪ Finset.univ.image (fun ν => x - unit NF ν))

lemma card_nb9 (x : Site NF) : (nb9 S x).card ≤ 9 := by
  unfold nb9
  refine (Finset.card_insert_le _ _).trans ?_
  have h1 := Finset.card_union_le (Finset.univ.image (fun ν => x + unit NF ν)) (Finset.univ.image (fun ν => x - unit NF ν))
  have h2 : (Finset.univ.image (fun ν => x + unit NF ν)).card ≤ 4 := (Finset.card_image_le).trans (by simp)
  have h3 : (Finset.univ.image (fun ν => x - unit NF ν)).card ≤ 4 := (Finset.card_image_le).trans (by simp)
  omega

/-- **The support of `Δb_y`**: it vanishes at `x` unless one of the nine sites `x`, `x ± e_ν` lies in `Δ(y)`. -/
lemma lapR_bfun_supp {y : Site NF} (hy : y ∈ detB S.toDomSeq) {x : Site NF}
    (hx : ∀ z ∈ nb9 S x, z ∉ Blk S.toDomSeq (jj y) y) : lapR S (bfun S y) x = 0 := by
  have h0 : bfun S y x = 0 := bfun_supp S hy (hx x (mem_insert_self _ _))
  have hp : ∀ ν, bfun S y (x + unit NF ν) = 0 := fun ν =>
    bfun_supp S hy (hx _ (mem_insert_of_mem (mem_union_left _ (mem_image_of_mem _ (mem_univ ν)))))
  have hm : ∀ ν, bfun S y (x - unit NF ν) = 0 := fun ν =>
    bfun_supp S hy (hx _ (mem_insert_of_mem (mem_union_right _ (mem_image_of_mem _ (mem_univ ν)))))
  simp [lapR, h0, hp, hm]

/-- **At most nine `Δb_y` do not vanish at a site.** -/
lemma card_lap_nonzero (x : Site NF) :
    ((detB S.toDomSeq).filter fun y => lapR S (bfun S y) x ≠ 0).card ≤ 9 := by
  classical
  have hsub : (detB S.toDomSeq).filter (fun y => lapR S (bfun S y) x ≠ 0) ⊆ (nb9 S x).image (bc S.toDomSeq) := by
    intro y hy
    obtain ⟨hyB, hne⟩ := mem_filter.1 hy
    by_contra hnot
    apply hne
    refine lapR_bfun_supp S hyB fun z hz hzy => hnot ?_
    exact Finset.mem_image.2 ⟨z, hz, (sc_mem_blk S.toDomSeq hyB hzy).2⟩
  exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (card_nb9 S x))

/-- **The sites where `Δb_y` does not vanish**: at most `9a_y⁴` of them. -/
lemma card_lap_supp {y : Site NF} (hy : y ∈ detB S.toDomSeq) :
    ((univ : Finset (Site NF)).filter fun x => lapR S (bfun S y) x ≠ 0).card ≤ 9 * (S.L : ℝ) ^ (4 * jj y) := by
  classical
  set B := Blk S.toDomSeq (jj y) y
  set U : Finset (Site NF) := B ∪ (Finset.univ.biUnion fun ν => B.image (fun z => z - unit NF ν)) ∪
    (Finset.univ.biUnion fun ν => B.image (fun z => z + unit NF ν))
  have hsub : (univ : Finset (Site NF)).filter (fun x => lapR S (bfun S y) x ≠ 0) ⊆ U := by
    intro x hx
    obtain ⟨-, hne⟩ := mem_filter.1 hx
    by_contra hnot
    apply hne
    refine lapR_bfun_supp S hy fun z hz hzB => hnot ?_
    simp only [nb9, Finset.mem_insert, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at hz
    rcases hz with rfl | ⟨ν, rfl⟩ | ⟨ν, rfl⟩
    · exact mem_union_left _ (mem_union_left _ hzB)
    · exact mem_union_left _ (mem_union_right _ (Finset.mem_biUnion.2 ⟨ν, mem_univ _, Finset.mem_image.2 ⟨_, hzB, by abel⟩⟩))
    · exact mem_union_right _ (Finset.mem_biUnion.2 ⟨ν, mem_univ _, Finset.mem_image.2 ⟨_, hzB, by abel⟩⟩)
  have hB : (B.card : ℝ) = (S.L : ℝ) ^ (4 * jj y) := card_Blk S hy
  have hU : (U.card : ℝ) ≤ 9 * B.card := by
    have h1 : U.card ≤ B.card + 4 * B.card + 4 * B.card := by
      refine (Finset.card_union_le _ _).trans (add_le_add ((Finset.card_union_le _ _).trans (add_le_add le_rfl ?_)) ?_)
      · refine Finset.card_biUnion_le.trans ?_
        calc ∑ ν : Fin 4, (B.image (fun z => z - unit NF ν)).card ≤ ∑ _ν : Fin 4, B.card :=
              sum_le_sum fun ν _ => Finset.card_image_le
          _ = 4 * B.card := by simp
      · refine Finset.card_biUnion_le.trans ?_
        calc ∑ ν : Fin 4, (B.image (fun z => z + unit NF ν)).card ≤ ∑ _ν : Fin 4, B.card :=
              sum_le_sum fun ν _ => Finset.card_image_le
          _ = 4 * B.card := by simp
    have : (U.card : ℝ) ≤ B.card + 4 * B.card + 4 * B.card := by exact_mod_cast h1
    linarith
  calc (((univ : Finset (Site NF)).filter fun x => lapR S (bfun S y) x ≠ 0).card : ℝ) ≤ U.card := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ 9 * B.card := hU
    _ = 9 * (S.L : ℝ) ^ (4 * jj y) := by rw [hB]

/-- `Σ_x|Δb_y(x)|² ≤ 9C_b²`. -/
lemma sum_lap_sq {y : Site NF} (hy : y ∈ detB S.toDomSeq) :
    ∑ x, lapR S (bfun S y) x ^ 2 ≤ 9 * Cbump ^ 2 := by
  classical
  have hL : (0 : ℝ) < (S.L : ℝ) ^ (4 * jj y) := by have := S.Lpos; positivity
  have hpt : ∀ x, lapR S (bfun S y) x ^ 2 ≤ Cbump ^ 2 * ((S.L : ℝ) ^ (4 * jj y))⁻¹ := fun x => by
    have h := lapR_bfun_le S hy x
    have hC : 0 ≤ Cbump * ((S.L : ℝ) ^ (2 * jj y))⁻¹ := by unfold Cbump; positivity
    have := (sq_le_sq' (by linarith [neg_abs_le (lapR S (bfun S y) x)]) ((le_abs_self _).trans h))
    calc lapR S (bfun S y) x ^ 2 ≤ (Cbump * ((S.L : ℝ) ^ (2 * jj y))⁻¹) ^ 2 := this
      _ = Cbump ^ 2 * ((S.L : ℝ) ^ (4 * jj y))⁻¹ := by
          rw [mul_pow, inv_pow, ← pow_mul]; ring_nf
  rw [← sum_filter_ne_zero]
  have hne : ∀ x, lapR S (bfun S y) x ^ 2 ≠ 0 → lapR S (bfun S y) x ≠ 0 := fun x h h0 => h (by rw [h0]; ring)
  calc ∑ x ∈ (univ : Finset (Site NF)).filter (fun x => lapR S (bfun S y) x ^ 2 ≠ 0), lapR S (bfun S y) x ^ 2
      ≤ ∑ x ∈ (univ : Finset (Site NF)).filter (fun x => lapR S (bfun S y) x ≠ 0), lapR S (bfun S y) x ^ 2 :=
        sum_le_sum_of_subset_of_nonneg (fun x hx => by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢; exact hne x hx) (fun x _ _ => sq_nonneg _)
    _ ≤ ∑ x ∈ (univ : Finset (Site NF)).filter (fun x => lapR S (bfun S y) x ≠ 0),
          Cbump ^ 2 * ((S.L : ℝ) ^ (4 * jj y))⁻¹ := sum_le_sum fun x _ => hpt x
    _ ≤ 9 * (S.L : ℝ) ^ (4 * jj y) * (Cbump ^ 2 * ((S.L : ℝ) ^ (4 * jj y))⁻¹) := by
        rw [sum_const, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (card_lap_supp S hy) (by unfold Cbump; positivity)
    _ = 9 * Cbump ^ 2 * ((S.L : ℝ) ^ (4 * jj y) * ((S.L : ℝ) ^ (4 * jj y))⁻¹) := by ring
    _ = 9 * Cbump ^ 2 := by rw [mul_inv_cancel₀ hL.ne', mul_one]

end SFBounds

namespace SFBounds

open Lattices SeqDom Blocks SmallFieldBlocks SFLocal SmallFieldDecay SmallFieldCoercivity
  SequenceOperators CompressedInverse ConcretePairing SFBox SFBox.SeqDomBox

variable (S : SeqDom) {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "NF" => SequenceAverages.N0 S
set_option quotPrecheck false in
local notation "jj" => (S.toDomSeq).sc

/-- **`|Q'g(y)|² ≤ a_y^{-4}Σ_{Δ(y)}|g|²`.** -/
lemma hs2_avgW_le {y : Site NF} (hy : y ∈ detB S.toDomSeq) (g : Site NF → Mat) :
    hs2 (avgW S.toDomSeq (W1 S) y g) ≤
      ((S.L : ℝ) ^ (4 * jj y))⁻¹ * ∑ x ∈ Blk S.toDomSeq (jj y) y, hs2 (g x) := by
  have hL : (0 : ℝ) < (S.L : ℝ) ^ (4 * jj y) := by have := S.Lpos; positivity
  rw [avgW_triv_eq S S.toDomSeq hy, RegularAverages.hs2_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs]
  simp only [toDomSeq_L]
  rw [abs_of_pos hL]
  have h := hs2_sum_le_card (Blk S.toDomSeq (jj y) y) g
  rw [show ((Blk S.toDomSeq (jj y) y).card : ℝ) = (S.L : ℝ) ^ (4 * jj y) from card_Blk S hy] at h
  calc ((S.L : ℝ) ^ (4 * jj y))⁻¹ ^ 2 * hs2 (∑ x ∈ Blk S.toDomSeq (jj y) y, g x)
      ≤ ((S.L : ℝ) ^ (4 * jj y))⁻¹ ^ 2 * ((S.L : ℝ) ^ (4 * jj y) * ∑ x ∈ Blk S.toDomSeq (jj y) y, hs2 (g x)) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by field_simp

/-- **(A4) The corrections**: `Σ_x|Σ_y(Δb_y)(x)(Q'g)(y)|² ≤ 81C_b²L^{-4i}Σ_{x ∈ Z}|g|²` for a set `Z` which contains
the blocks with `Q'g ≠ 0`, in a sequence whose scales are at least `i`. -/
theorem A4_bound (g : Site NF → Mat) (Z : Finset (Site NF))
    (hZ : ∀ y ∈ detB S.toDomSeq, avgW S.toDomSeq (W1 S) y g ≠ 0 → ∀ x ∈ Blk S.toDomSeq (jj y) y, x ∈ Z)
    {i : ℕ} (hsc : ∀ x, i ≤ jj x) :
    ∑ x, hs2 (∑ y ∈ detB S.toDomSeq, (lapR S (bfun S y) x : ℂ) • avgW S.toDomSeq (W1 S) y g) ≤
      81 * Cbump ^ 2 * ((S.L : ℝ) ^ (4 * i))⁻¹ * ∑ x ∈ Z, hs2 (g x) := by
  classical
  have hL1 : (1 : ℝ) ≤ S.L := by exact_mod_cast S.Lpos
  set c : Site NF → Mat := fun y => avgW S.toDomSeq (W1 S) y g
  -- at a site, at most nine terms
  have hpt : ∀ x, hs2 (∑ y ∈ detB S.toDomSeq, (lapR S (bfun S y) x : ℂ) • c y) ≤
      9 * ∑ y ∈ detB S.toDomSeq, lapR S (bfun S y) x ^ 2 * hs2 (c y) := by
    intro x
    set T := (detB S.toDomSeq).filter fun y => lapR S (bfun S y) x ≠ 0
    have e : ∑ y ∈ detB S.toDomSeq, (lapR S (bfun S y) x : ℂ) • c y = ∑ y ∈ T, (lapR S (bfun S y) x : ℂ) • c y := by
      rw [sum_filter]
      refine sum_congr rfl fun y _ => ?_
      split_ifs with h
      · rfl
      · push_neg at h; rw [h, Complex.ofReal_zero, zero_smul]
    rw [e]
    refine (hs2_sum_le_card T _).trans ?_
    have hT : (T.card : ℝ) ≤ 9 := by exact_mod_cast card_lap_nonzero S x
    have hterm : ∀ y, hs2 ((lapR S (bfun S y) x : ℂ) • c y) = lapR S (bfun S y) x ^ 2 * hs2 (c y) := fun y => by
      rw [RegularAverages.hs2_smul, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    simp only [hterm]
    have hsub : ∑ y ∈ T, lapR S (bfun S y) x ^ 2 * hs2 (c y) ≤
        ∑ y ∈ detB S.toDomSeq, lapR S (bfun S y) x ^ 2 * hs2 (c y) :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun y _ _ => mul_nonneg (sq_nonneg _) (hs2_nonneg _)
    have h0 : 0 ≤ ∑ y ∈ T, lapR S (bfun S y) x ^ 2 * hs2 (c y) :=
      sum_nonneg fun y _ => mul_nonneg (sq_nonneg _) (hs2_nonneg _)
    nlinarith
  -- the averages
  have hc : ∀ y ∈ detB S.toDomSeq, hs2 (c y) ≤ ((S.L : ℝ) ^ (4 * i))⁻¹ *
      (if c y ≠ 0 then ∑ x ∈ Blk S.toDomSeq (jj y) y, hs2 (g x) else 0) := by
    intro y hy
    split_ifs with h
    · refine (hs2_avgW_le S hy g).trans (mul_le_mul_of_nonneg_right ?_ (sum_nonneg fun x _ => hs2_nonneg _))
      exact inv_anti₀ (by positivity) (pow_le_pow_right₀ hL1 (by have := hsc y; omega))
    · push_neg at h; rw [h]; simp [hs2, ntr]
  -- the blocks with `c ≠ 0` lie in `Z`
  have hZsum : ∑ y ∈ detB S.toDomSeq, (if c y ≠ 0 then ∑ x ∈ Blk S.toDomSeq (jj y) y, hs2 (g x) else 0) ≤
      ∑ x ∈ Z, hs2 (g x) := by
    have e : ∑ x ∈ Z, hs2 (g x) = ∑ y ∈ detB S.toDomSeq, ∑ x ∈ Blk S.toDomSeq (jj y) y,
        (if x ∈ Z then hs2 (g x) else 0) := by
      rw [← sum_blocks S.toDomSeq (fun x => if x ∈ Z then hs2 (g x) else 0), sum_ite_mem, Finset.univ_inter]
    rw [e]
    refine sum_le_sum fun y hy => ?_
    split_ifs with h
    · exact le_of_eq (sum_congr rfl fun x hx => by rw [if_pos (hZ y hy h x hx)])
    · exact sum_nonneg fun x _ => by split_ifs <;> simp [hs2_nonneg]
  calc ∑ x, hs2 (∑ y ∈ detB S.toDomSeq, (lapR S (bfun S y) x : ℂ) • c y)
      ≤ ∑ x, 9 * ∑ y ∈ detB S.toDomSeq, lapR S (bfun S y) x ^ 2 * hs2 (c y) := sum_le_sum fun x _ => hpt x
    _ = 9 * ∑ y ∈ detB S.toDomSeq, hs2 (c y) * ∑ x, lapR S (bfun S y) x ^ 2 := by
        rw [← mul_sum, sum_comm]
        congr 1
        refine sum_congr rfl fun y _ => ?_
        rw [mul_sum]; exact sum_congr rfl fun x _ => by ring
    _ ≤ 9 * ∑ y ∈ detB S.toDomSeq, (((S.L : ℝ) ^ (4 * i))⁻¹ *
          (if c y ≠ 0 then ∑ x ∈ Blk S.toDomSeq (jj y) y, hs2 (g x) else 0)) * (9 * Cbump ^ 2) := by
        refine mul_le_mul_of_nonneg_left (sum_le_sum fun y hy => ?_) (by norm_num)
        exact mul_le_mul (hc y hy) (sum_lap_sq S hy) (sum_nonneg fun x _ => sq_nonneg _)
          (by have := hc y hy; have := hs2_nonneg (c y); linarith)
    _ = 81 * Cbump ^ 2 * ((S.L : ℝ) ^ (4 * i))⁻¹ *
          ∑ y ∈ detB S.toDomSeq, (if c y ≠ 0 then ∑ x ∈ Blk S.toDomSeq (jj y) y, hs2 (g x) else 0) := by
        rw [← sum_mul, ← mul_sum]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hZsum (by unfold Cbump; positivity)

end SFBounds

namespace SFBounds

open Lattices SeqDom Blocks SmallFieldBlocks SFLocal SmallFieldDecay SmallFieldCoercivity
  SequenceOperators CompressedInverse ConcretePairing SFBox SFBox.SeqDomBox

variable {S : SeqDom} {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "NF" => SequenceAverages.N0 S

/-- **The scales of the comparison sequence** are `i` and `i + 1`. -/
lemma twoLayer_sc {i : ℕ} (hi : i + 1 ≤ S.k) (Λ : Set (Tor (ellT S.L S.mT))) (hΛ : IsCubes S (i + 1) Λ)
    (x : Site NF) : i ≤ ((twoLayer S i hi Λ hΛ).toDomSeq).sc x ∧ ((twoLayer S i hi Λ hΛ).toDomSeq).sc x ≤ i + 1 := by
  constructor
  · refine (((twoLayer S i hi Λ hΛ).toDomSeq).mem_iff x i).1 ?_
    show (twoLayer S i hi Λ hΛ).ef x ∈ (twoLayer S i hi Λ hΛ).Ω i
    rw [twoLayer_low le_rfl]; trivial
  · by_contra h
    have h2 := (((twoLayer S i hi Λ hΛ).toDomSeq).mem_iff x (i + 2)).2 (by omega)
    change (twoLayer S i hi Λ hΛ).ef x ∈ (twoLayer S i hi Λ hΛ).Ω (i + 2) at h2
    rw [twoLayer_high le_rfl] at h2
    exact h2

lemma hs2_four_le (a b c d : Mat) : hs2 (-a - b + c + d) ≤ 8 * (hs2 a + hs2 b + hs2 c + hs2 d) := by
  have h1 := hs2_add_le (-a - b + c) d
  have h2 := hs2_add_le (-a - b) c
  have h3 := hs2_add_le (-a) (-b)
  have e1 : hs2 (-a) = hs2 a := by rw [show -a = (-1 : ℂ) • a by simp, RegularAverages.hs2_smul]; simp
  have e2 : hs2 (-b) = hs2 b := by rw [show -b = (-1 : ℂ) • b by simp, RegularAverages.hs2_smul]; simp
  rw [← sub_eq_add_neg] at h3
  rw [e1, e2] at h3
  have := hs2_nonneg a; have := hs2_nonneg b; have := hs2_nonneg c; have := hs2_nonneg d
  linarith

end SFBounds

namespace SFBounds

open Lattices SeqDom Blocks SmallFieldBlocks SFLocal SmallFieldDecay SmallFieldCoercivity
  SequenceOperators CompressedInverse ConcretePairing SFBox SFBox.SeqDomBox

variable (T : SeqDom) {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "NT" => SequenceAverages.N0 T
local notation "RMT" => ((T.R * T.L ^ T.mM : ℕ) : ℝ)
set_option quotPrecheck false in
local notation "jt" => (T.toDomSeq).sc

/-- **The decomposition of `Δ(λ - λ̃)`** for a sequence and its own minimiser and correction. -/
theorem lap_diff_gen [NeZero N] (f : Site NT → Mat) (χ : Site NT → ℝ) (hfχ : ∀ x, χ x ≠ 1 → f x = 0)
    (x : Site NT) :
    Ds1L a1 (cfgX (X0 T)) (D0L a1 (cfgX (X0 T)) (minim T f - corr T (fun x => (χ x : ℂ) • minim T f x))) x =
      -(((1 - χ x : ℝ) : ℂ) • Pop T (X0 T) (W1 T) Set.univ f x) - (lapR T χ x : ℂ) • minim T f x +
      ∑ ν, (((χ (x + unit NT ν) - χ x : ℝ) : ℂ) • (minim T f (x + unit NT ν) - minim T f x) +
        ((χ (x - unit NT ν) - χ x : ℝ) : ℂ) • (minim T f (x - unit NT ν) - minim T f x)) +
      ∑ y ∈ detB T.toDomSeq, (lapR T (bfun T y) x : ℂ) •
        avgW T.toDomSeq (W1 T) y (fun x => (χ x : ℂ) • minim T f x) := by
  set lam := minim T f
  set g : Site NT → Mat := fun x => (χ x : ℂ) • lam x
  have e1 : lam - corr T g = (fun x => ((1 - χ x : ℝ) : ℂ) • lam x) +
      (fun x => ∑ y ∈ detB T.toDomSeq, ((bfun T y x : ℝ) : ℂ) • avgW T.toDomSeq (W1 T) y g) := by
    funext x
    simp only [Pi.sub_apply, corr, Pi.add_apply, g]
    push_cast
    rw [sub_smul, one_smul]; abel
  rw [e1, map_add, map_add, Pi.add_apply, lap_mul T (fun x => 1 - χ x) lam x, lap_sum T]
  simp only [lap_const T]
  rw [minim_lap]
  have hfx : ((1 - χ x : ℝ) : ℂ) • f x = 0 := by
    by_cases h : χ x = 1
    · rw [h, sub_self, Complex.ofReal_zero, zero_smul]
    · rw [hfχ x h, smul_zero]
  have hlapR : lapR T (fun x => 1 - χ x) x = -lapR T χ x := by
    simp only [lapR, ← sum_neg_distrib]; refine sum_congr rfl fun ν _ => ?_; ring
  rw [Pi.sub_apply, smul_sub, hfx, zero_sub, hlapR]
  have hd : ∀ ν, (((1 - χ (x + unit NT ν)) - (1 - χ x) : ℝ) : ℂ) = -((χ (x + unit NT ν) - χ x : ℝ) : ℂ) ∧
      (((1 - χ (x - unit NT ν)) - (1 - χ x) : ℝ) : ℂ) = -((χ (x - unit NT ν) - χ x : ℝ) : ℂ) := fun ν => by
    constructor <;> push_cast <;> ring
  simp only [fun ν => (hd ν).1, fun ν => (hd ν).2, neg_smul, ← neg_add, sum_neg_distrib]
  push_cast
  module

end SFBounds

namespace SFBounds

open Lattices SeqDom Blocks SmallFieldBlocks SFLocal SmallFieldDecay SmallFieldCoercivity
  SequenceOperators CompressedInverse ConcretePairing SFBox SFBox.SeqDomBox

variable {T : SeqDom} {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "NT" => SequenceAverages.N0 T
local notation "RMT" => ((T.R * T.L ^ T.mM : ℕ) : ℝ)
set_option quotPrecheck false in
local notation "jt" => (T.toDomSeq).sc

/-- The constant of `P_weighted`. -/
def CIone (T : SeqDom) (N : ℕ) (δ κ : ℝ) : ℝ :=
  (CPk T N δ * Real.exp (4 * κ)) ^ 2 * ((T.toContSeq).c1 (1 / 2) (7 / 32 * thetaB T N δ) *
    ((T.L : ℝ) ^ 4 * (T.toContSeq).c1 (1 / 2) (7 / 32 * thetaB T N δ)))

/-- **eq:sf-cut-off, the bound on the shell**: for a sequence with the scales `i` and `i + 1`, its minimiser `λ`
and the correction `λ̃` of a cut-off `χ`, and a weight `φ ≥ Φ` on the shell,
`‖Δ(λ - λ̃)‖² ≤ 8e^{-2Φ}KΣe^{2φ}|f|²`. -/
theorem cutoff_bound_gen [NeZero N] {δ : ℝ} (H : ScalarHyp (N := N) T (X0 T) 0 (W1 T) 0 Set.univ δ)
    (hRMb : (T.toContSeq).r1 (1 / 2) (1 / 32 * δ) ≤ RMT) (hRMs4 : 32 * Real.log T.L / (1 / 4 * δ) ≤ RMT)
    (hsmallT : CTd T N δ 0 0 * (T.toContSeq).c1 (1 / 2) (1 / 32 * δ) ≤ gammaB N / 4)
    (hRMθs : 32 * Real.log T.L / (thetaB T N δ / 2) ≤ RMT)
    (hRMθc : (T.toContSeq).r1 (1 / 2) (7 / 16 * thetaB T N δ) ≤ RMT)
    (hRMsum : (T.toContSeq).r1 (1 / 2) (7 / 32 * thetaB T N δ) ≤ RMT) (hRM1 : 1 ≤ T.R * T.L ^ T.mM)
    {i : ℕ} (hsc : ∀ x, i ≤ jt x ∧ jt x ≤ i + 1)
    (f : Site NT → Mat) (χ ph : Site NT → ℝ) {g1 g2 ε κ Φ : ℝ} (hκ0 : 0 ≤ κ)
    (hκθ : κ ≤ 1 / 2 * (7 / 32 * thetaB T N δ)) (hκL : κ ≤ 1 / (128 * T.L))
    (hph : ∀ x x', |ph x - ph x'| ≤ κ * T.dF x x') (hε : ε ≤ 1)
    (hphb : ∀ x ν, |ph x - ph (x + unit NT ν)| ≤ ε ∧ |ph x - ph (x + -unit NT ν)| ≤ ε)
    (hχ : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1)
    (hg1 : ∀ x ν, |χ (x + unit NT ν) - χ x| ≤ g1 ∧ |χ (x - unit NT ν) - χ x| ≤ g1)
    (hg2 : ∀ x, |lapR T χ x| ≤ g2)
    (hΦ1 : ∀ x, χ x ≠ 1 → Φ ≤ ph x) (hΦ2 : ∀ x, lapR T χ x ≠ 0 → Φ ≤ ph x)
    (hΦ3 : ∀ x ν, (χ (x + unit NT ν) - χ x ≠ 0 ∨ χ (x - unit NT ν) - χ x ≠ 0) → Φ ≤ ph x)
    (Z : Finset (Site NT))
    (hZ : ∀ y ∈ detB T.toDomSeq, avgW T.toDomSeq (W1 T) y (fun x => (χ x : ℂ) • minim T f x) ≠ 0 →
      ∀ x ∈ Blk T.toDomSeq (jt y) y, x ∈ Z)
    (hΦZ : ∀ x ∈ Z, Φ ≤ ph x) (hfχ : ∀ x, χ x ≠ 1 → f x = 0) :
    ∑ x, hs2 (Ds1L a1 (cfgX (X0 T)) (D0L a1 (cfgX (X0 T))
      (minim T f - corr T (fun x => (χ x : ℂ) • minim T f x))) x) ≤
      8 * Real.exp (-(2 * Φ)) * (CIone T N δ κ +
        (g2 ^ 2 + 512 * g1 ^ 2 * ε ^ 2 + 81 * Cbump ^ 2 * ((T.L : ℝ) ^ (4 * i))⁻¹) * (T.L : ℝ) ^ (2 * (i + 1)) *
          (288 * (T.L : ℝ) ^ (2 * (i + 1)) * (1 + CIone T N δ κ)) +
        128 * g1 ^ 2 * (288 * (T.L : ℝ) ^ (2 * (i + 1)) * (1 + CIone T N δ κ))) *
        ∑ x, Real.exp (2 * ph x) * hs2 (f x) := by
  set lam := minim T f
  set P := Pop T (X0 T) (W1 T) Set.univ f
  set m := i + 1
  set CI := CIone T N δ κ
  set Wf := ∑ x, Real.exp (2 * ph x) * hs2 (f x)
  set WP := ∑ x, Real.exp (2 * ph x) * hs2 (P x)
  set Wl := ∑ x, Real.exp (2 * ph x) * hs2 (lam x)
  set Lm := (T.L : ℝ) ^ (2 * m)
  set E := 288 * Lm * (1 + CI)
  have hWf : 0 ≤ Wf := sum_nonneg fun x _ => by have := hs2_nonneg (f x); positivity
  have hc1 : 0 ≤ (T.toContSeq).c1 (1 / 2) (7 / 32 * thetaB T N δ) := by
    unfold Summation.ContSeq.c1; positivity
  have hCI : 0 ≤ CI := by
    show 0 ≤ CIone T N δ κ
    unfold CIone
    positivity
  have hLm : 0 ≤ Lm := by positivity
  -- (I1)
  have hWP : WP ≤ CI * Wf := P_weighted H hRMb hRMs4 hsmallT hRMθs hRMθc hRMsum hsc ph hκ0 hκθ hph f
  -- (I2)
  have hup : ∀ x, jt x ≤ m := fun x => (hsc x).2
  have hfw : fwinv T.toDomSeq ph (f - P) ≤ Lm * (2 * (1 + CI) * Wf) := by
    refine (fwinv_le hup ph (f - P)).trans (mul_le_mul_of_nonneg_left ?_ hLm)
    have := weighted_sub_le ph f P
    nlinarith
  have hdec := minim_weighted hRM1 ph hκ0 hκL hph f
  set wn := wnormM T.toDomSeq (expS ph lam)
  set D := dsqM (expS ph lam)
  have hwn0 : 0 ≤ wn := sum_nonneg fun x _ => by have := hs2_nonneg (expS ph lam x); positivity
  have hD0 : 0 ≤ D := sum_nonneg fun x _ => sum_nonneg fun μ _ => hs2_nonneg _
  have hfw0 : 0 ≤ fwinv T.toDomSeq ph (f - P) := sum_nonneg fun x _ => by
    have := hs2_nonneg ((f - P) x); positivity
  have hsq : ∀ a : ℝ, 0 ≤ a → Real.sqrt a ≤ 12 * Real.sqrt (fwinv T.toDomSeq ph (f - P)) → a ≤ E * Wf := by
    intro a ha h
    have h1 : a ≤ 144 * fwinv T.toDomSeq ph (f - P) := by
      have h2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
      rw [Real.sq_sqrt ha, mul_pow, Real.sq_sqrt hfw0] at h2; linarith
    calc a ≤ 144 * fwinv T.toDomSeq ph (f - P) := h1
      _ ≤ 144 * (Lm * (2 * (1 + CI) * Wf)) := by linarith
      _ = E * Wf := by unfold E; ring
  have hwn : wn ≤ E * Wf := hsq wn hwn0 (by linarith [Real.sqrt_nonneg D])
  have hD : D ≤ E * Wf := hsq D hD0 (by linarith [Real.sqrt_nonneg wn])
  have hWl : Wl ≤ Lm * (E * Wf) := (weighted_le_wnorm hup ph lam).trans (mul_le_mul_of_nonneg_left hwn hLm)
  -- the four terms
  have hsplit : ∑ x, hs2 (Ds1L a1 (cfgX (X0 T)) (D0L a1 (cfgX (X0 T))
      (minim T f - corr T (fun x => (χ x : ℂ) • minim T f x))) x) ≤
      8 * (∑ x, hs2 (((1 - χ x : ℝ) : ℂ) • P x) + ∑ x, hs2 ((lapR T χ x : ℂ) • lam x) +
        ∑ x, hs2 (∑ ν, (((χ (x + unit NT ν) - χ x : ℝ) : ℂ) • (lam (x + unit NT ν) - lam x) +
          ((χ (x - unit NT ν) - χ x : ℝ) : ℂ) • (lam (x - unit NT ν) - lam x))) +
        ∑ x, hs2 (∑ y ∈ detB T.toDomSeq, (lapR T (bfun T y) x : ℂ) •
          avgW T.toDomSeq (W1 T) y (fun x => (χ x : ℂ) • lam x))) := by
    simp only [mul_add, ← sum_add_distrib, mul_sum]
    refine sum_le_sum fun x _ => ?_
    rw [lap_diff_gen T f χ hfχ x]
    have := hs2_four_le (((1 - χ x : ℝ) : ℂ) • P x) ((lapR T χ x : ℂ) • lam x)
      (∑ ν, (((χ (x + unit NT ν) - χ x : ℝ) : ℂ) • (lam (x + unit NT ν) - lam x) +
        ((χ (x - unit NT ν) - χ x : ℝ) : ℂ) • (lam (x - unit NT ν) - lam x)))
      (∑ y ∈ detB T.toDomSeq, (lapR T (bfun T y) x : ℂ) • avgW T.toDomSeq (W1 T) y (fun x => (χ x : ℂ) • lam x))
    linarith
  have hA1 := A1_bound χ P ph hχ hΦ1
  have hA2 := mult_tail (lapR T χ) lam ph hg2 hΦ2
  have hA3 := A3_bound χ lam ph hg1 hΦ3 hε hphb
  have hA4 := A4_bound T (fun x => (χ x : ℂ) • lam x) Z hZ (fun x => (hsc x).1)
  have hZl : ∑ x ∈ Z, hs2 ((χ x : ℂ) • lam x) ≤ Real.exp (-(2 * Φ)) * Wl := by
    refine le_trans (sum_le_sum fun x _ => ?_) (weight_tail lam ph Z hΦZ)
    rw [RegularAverages.hs2_smul, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have h1 : χ x ^ 2 ≤ 1 := by have := hχ x; nlinarith
    exact mul_le_of_le_one_left (hs2_nonneg _) h1
  have he : 0 ≤ Real.exp (-(2 * Φ)) := (Real.exp_pos _).le
  have hCb : 0 ≤ 81 * Cbump ^ 2 * ((T.L : ℝ) ^ (4 * i))⁻¹ := by unfold Cbump; positivity
  -- assembly
  have h1 : ∑ x, hs2 (((1 - χ x : ℝ) : ℂ) • P x) ≤ Real.exp (-(2 * Φ)) * (CI * Wf) :=
    hA1.trans (mul_le_mul_of_nonneg_left hWP he)
  have h2 : ∑ x, hs2 ((lapR T χ x : ℂ) • lam x) ≤ g2 ^ 2 * (Real.exp (-(2 * Φ)) * (Lm * (E * Wf))) :=
    hA2.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hWl he) (sq_nonneg _))
  have h3 : ∑ x, hs2 (∑ ν, (((χ (x + unit NT ν) - χ x : ℝ) : ℂ) • (lam (x + unit NT ν) - lam x) +
      ((χ (x - unit NT ν) - χ x : ℝ) : ℂ) • (lam (x - unit NT ν) - lam x))) ≤
      g1 ^ 2 * (Real.exp (-(2 * Φ)) * (128 * (E * Wf) + 512 * ε ^ 2 * (Lm * (E * Wf)))) := by
    refine hA3.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ he) (sq_nonneg _))
    have : 0 ≤ 512 * ε ^ 2 := by positivity
    exact add_le_add (by linarith [hD]) (mul_le_mul_of_nonneg_left hWl this)
  have h4 : ∑ x, hs2 (∑ y ∈ detB T.toDomSeq, (lapR T (bfun T y) x : ℂ) •
      avgW T.toDomSeq (W1 T) y (fun x => (χ x : ℂ) • lam x)) ≤
      81 * Cbump ^ 2 * ((T.L : ℝ) ^ (4 * i))⁻¹ * (Real.exp (-(2 * Φ)) * (Lm * (E * Wf))) :=
    hA4.trans (mul_le_mul_of_nonneg_left (hZl.trans (mul_le_mul_of_nonneg_left hWl he)) hCb)
  refine hsplit.trans ?_
  calc 8 * (∑ x, hs2 (((1 - χ x : ℝ) : ℂ) • P x) + ∑ x, hs2 ((lapR T χ x : ℂ) • lam x) +
        ∑ x, hs2 (∑ ν, (((χ (x + unit NT ν) - χ x : ℝ) : ℂ) • (lam (x + unit NT ν) - lam x) +
          ((χ (x - unit NT ν) - χ x : ℝ) : ℂ) • (lam (x - unit NT ν) - lam x))) +
        ∑ x, hs2 (∑ y ∈ detB T.toDomSeq, (lapR T (bfun T y) x : ℂ) •
          avgW T.toDomSeq (W1 T) y (fun x => (χ x : ℂ) • lam x)))
      ≤ 8 * (Real.exp (-(2 * Φ)) * (CI * Wf) + g2 ^ 2 * (Real.exp (-(2 * Φ)) * (Lm * (E * Wf))) +
          g1 ^ 2 * (Real.exp (-(2 * Φ)) * (128 * (E * Wf) + 512 * ε ^ 2 * (Lm * (E * Wf)))) +
          81 * Cbump ^ 2 * ((T.L : ℝ) ^ (4 * i))⁻¹ * (Real.exp (-(2 * Φ)) * (Lm * (E * Wf)))) := by
        linarith [h1, h2, h3, h4]
    _ = _ := by ring

end SFBounds

end CoreLean

end
