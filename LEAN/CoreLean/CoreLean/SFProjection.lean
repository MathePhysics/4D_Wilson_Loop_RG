/-
`prop:sf-block` of BALABAN_CORE.tex (`aaaa938bb57d`), the step "The projection": the kernel of
`P = G'Q'^*T⁻¹Q'G'` on the fine lattice of a sequence of domains (`a₀ = 1`).

* `chainP`: the double sum `Σ_{y₁, y₂}a_y²e^{-ρd(y, y₁)}a_{y₁}^{-4}e^{-θd(y₁, y₂)}a_{y₂}^{-4}a_{y'}²e^{-ρd(y₂, y')}
  ≤ L^{12}c₁(½, θ)c₁(½, 7θ/16)a_{y'}^{-4}e^{-(7/32)θd(y, y')}` (the core's three quotients and `eq:chain-summation`).
* `inv_bound`: a kernel whose equation `Tu = δ_{c'}w` has solutions with `‖u(c)‖ ≤ k(c, c')‖w‖` has
  `‖(T⁻¹ν)(c)‖ ≤ Σ_{c'}k(c, c')‖ν(c')‖`.
* `ntr_Ad`, `avg_pair`: `Σ_y a_y⁴tr(A(y)(Q'g)(y)) = ⟨Q'^*A, g⟩` for any transports `W`.
* `ScalarHyp.QG_trace`: `a_y⁴tr(Z(Q'G'f)(y)) = ⟨G'λ_Z, f⟩` (the symmetry of `G'`); `ScalarHyp.QG_bound`: the kernel of
  `Q'G'`, `|(Q'G'f)(y)| ≤ a_y^{-4}Σ_{x'}2√NC_va_{x'}²e^{-(7/8)δd(y(x'), y)}|f(x')|` (the core's `k₂`).
* `avgL`, `QpL`, `blkL`, `unblkL`, `Tinv`, `Pop`: `P = G'Q'^*T⁻¹Q'G'` as a linear map, `T⁻¹ν = a^{-4}T̂⁻¹ν`
  (`T̂⁻¹` from `ScalarHyp.block_inverse`, `0` where `T̂` is not invertible); `gammaB`, `thetaB`: `γ` and the rate of `T̂⁻¹`.
* `ScalarHyp.P_bound`: `|(Pf)(x)| ≤ C_PΣ_{x'}a_{y(x')}^{-4}e^{-(7/32)θ_Bd(y(x), y(x'))}|f(x')|`.
* `ScalarHyp.QGs_bound`: the kernel of `Q'G'D^*_𝐔`, through `⟨D_𝐔λ, h⟩ = ⟨λ, D^*_𝐔h⟩` (`D0L_transpose`).
* `ScalarHyp.Pgen`: the common bound; `gradP_bound`, `PDs_bound`, `gradPDs_bound`: the kernels of `∇P`, `P∇^*`, `∇P∇^*`
  with the factors `a_{y(x)}^{-1}`, `a_{y(x')}^{-1}`, `a_{y(x)}^{-1}a_{y(x')}^{-1}` (the core moves `a_{y(x')}^{-1}` to
  `a_{y(x)}^{-1}` with `eq:sf-scale-shift`; here it stays on the side where it arises).
-/
import CoreLean.SFBlockKernel

open Finset Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean
namespace SFBounds

open Lattices SeqDom Blocks SmallFieldBlocks SFBox SFBox.SeqDomBox SmallFieldDecay SmallFieldCoercivity
  SequenceOperators CompressedInverse SFLocal ConcretePairing

variable (S : SeqDom) {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ
local notation "NF" => SequenceAverages.N0 S
local notation "RMS" => ((S.R * S.L ^ S.mM : ℕ) : ℝ)
set_option quotPrecheck false in
local notation "jj" => (S.toDomSeq).sc

/-- `a_{x'}^{-4} ≤ L⁴e^{(δ/8)d(x, x')}a_x^{-4}`. -/
lemma inv_shift {δ : ℝ} (hδ : 0 < δ) (hRM : 32 * Real.log S.L / δ ≤ RMS) (x x' : Site NF) :
    ((S.L : ℝ) ^ (4 * jj x'))⁻¹ ≤ (S.L : ℝ) ^ (4 : ℝ) * Real.exp (δ / 8 * S.dF x x') * ((S.L : ℝ) ^ (4 * jj x))⁻¹ := by
  have hL : (0 : ℝ) < S.L := by exact_mod_cast S.Lpos
  have h := S.scale_shift hδ hRM (σ := -4) (by norm_num) x x'
  have e : ∀ z : Site NF, ((S.L : ℝ) ^ jj z) ^ (-4 : ℝ) = ((S.L : ℝ) ^ (4 * jj z))⁻¹ := fun z => by
    rw [Real.rpow_neg (by positivity), show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, ← pow_mul,
      mul_comm]
  rwa [e, e] at h

/-- `a_{x'}² ≤ L⁴e^{(δ/8)d(x, x')}a_x²`. -/
lemma sq_shift {δ : ℝ} (hδ : 0 < δ) (hRM : 32 * Real.log S.L / δ ≤ RMS) (x x' : Site NF) :
    (S.L : ℝ) ^ (2 * jj x') ≤ (S.L : ℝ) ^ (4 : ℝ) * Real.exp (δ / 8 * S.dF x x') * (S.L : ℝ) ^ (2 * jj x) := by
  have h := S.scale_shift hδ hRM (σ := ((2 : ℕ) : ℝ)) (by norm_num) x x'
  rwa [Real.rpow_natCast, Real.rpow_natCast, ← pow_mul, ← pow_mul, mul_comm (jj x') 2, mul_comm (jj x) 2] at h

/-- **The double sum of the kernel of `P`.** -/
lemma chainP {ρ θ : ℝ} (hθ : 0 < θ) (hρ : 9 / 8 * θ ≤ ρ)
    (hRMs : 32 * Real.log S.L / (θ / 2) ≤ RMS) (hRMc : (S.toContSeq).r1 (1 / 2) (7 / 16 * θ) ≤ RMS)
    {y y' : Site NF} (hy : y ∈ detB S.toDomSeq) :
    ∑ c ∈ detB S.toDomSeq, ∑ c' ∈ detB S.toDomSeq,
      (S.L : ℝ) ^ (2 * jj y) * Real.exp (-(ρ * S.dF y c)) * ((S.L : ℝ) ^ (4 * jj c))⁻¹ *
        (Real.exp (-(θ * S.dF c c')) * ((S.L : ℝ) ^ (4 * jj c'))⁻¹ * (S.L : ℝ) ^ (2 * jj y') *
          Real.exp (-(ρ * S.dF c' y'))) ≤
      (S.L : ℝ) ^ (12 : ℝ) * (S.toContSeq).c1 (1 / 2) θ * (S.toContSeq).c1 (1 / 2) (7 / 16 * θ) *
        ((S.L : ℝ) ^ (4 * jj y'))⁻¹ * Real.exp (-(7 / 32 * θ * S.dF y y')) := by
  have hL : (0 : ℝ) < S.L := by exact_mod_cast S.Lpos
  have hRMs1 : 32 * Real.log S.L / θ ≤ RMS := by
    have hlog : 0 ≤ Real.log S.L := Real.log_nonneg (by exact_mod_cast (show 1 ≤ S.L by have := S.three_le_L; omega))
    refine le_trans ?_ hRMs
    rw [div_le_div_iff₀ hθ (by positivity)]; nlinarith
  have hRMc1 : (S.toContSeq).r1 (1 / 2) θ ≤ RMS := (r1_anti S (by positivity) (by linarith)).trans hRMc
  have hc1 : 0 ≤ (S.toContSeq).c1 (1 / 2) θ := by unfold Summation.ContSeq.c1; positivity
  -- the inner sum
  have hA : ∀ c ∈ detB S.toDomSeq, ∑ c' ∈ detB S.toDomSeq, Real.exp (-(θ * S.dF c c')) *
      ((S.L : ℝ) ^ (4 * jj c'))⁻¹ * (S.L : ℝ) ^ (2 * jj y') * Real.exp (-(ρ * S.dF c' y')) ≤
      (S.L : ℝ) ^ (4 : ℝ) * (S.toContSeq).c1 (1 / 2) θ * ((S.L : ℝ) ^ (4 * jj y'))⁻¹ * (S.L : ℝ) ^ (2 * jj y') *
        Real.exp (-(θ / 2 * S.dF c y')) := by
    intro c hc
    have hch := chain2 S (δ := θ) (δ' := ρ - θ / 8) hθ (by linarith)
      (by rw [min_eq_left (by linarith)]; exact hRMc1) hc (y' := y')
    rw [min_eq_left (by linarith)] at hch
    calc _ ≤ ∑ c' ∈ detB S.toDomSeq, (S.L : ℝ) ^ (4 : ℝ) * ((S.L : ℝ) ^ (4 * jj y'))⁻¹ * (S.L : ℝ) ^ (2 * jj y') *
          (Real.exp (-(θ * S.dF c c')) * Real.exp (-((ρ - θ / 8) * S.dF c' y'))) := by
          refine sum_le_sum fun c' _ => ?_
          have hsh := inv_shift S hθ hRMs1 y' c'
          have hd := S.dF_nonneg c' y'
          have he : Real.exp (-(ρ * S.dF c' y')) * Real.exp (θ / 8 * S.dF y' c') =
              Real.exp (-((ρ - θ / 8) * S.dF c' y')) := by
            rw [← Real.exp_add, S.dF_comm y' c']; congr 1; ring
          calc Real.exp (-(θ * S.dF c c')) * ((S.L : ℝ) ^ (4 * jj c'))⁻¹ * (S.L : ℝ) ^ (2 * jj y') *
                Real.exp (-(ρ * S.dF c' y'))
              ≤ Real.exp (-(θ * S.dF c c')) * ((S.L : ℝ) ^ (4 : ℝ) * Real.exp (θ / 8 * S.dF y' c') *
                ((S.L : ℝ) ^ (4 * jj y'))⁻¹) * (S.L : ℝ) ^ (2 * jj y') * Real.exp (-(ρ * S.dF c' y')) := by
                gcongr
            _ = _ := by rw [← he]; ring
      _ = (S.L : ℝ) ^ (4 : ℝ) * ((S.L : ℝ) ^ (4 * jj y'))⁻¹ * (S.L : ℝ) ^ (2 * jj y') *
          ∑ c' ∈ detB S.toDomSeq, Real.exp (-(θ * S.dF c c')) * Real.exp (-((ρ - θ / 8) * S.dF c' y')) := by
          rw [mul_sum]
      _ ≤ (S.L : ℝ) ^ (4 : ℝ) * ((S.L : ℝ) ^ (4 * jj y'))⁻¹ * (S.L : ℝ) ^ (2 * jj y') *
          ((S.toContSeq).c1 (1 / 2) θ * Real.exp (-(1 / 2 * θ * S.dF c y'))) :=
          mul_le_mul_of_nonneg_left hch (by positivity)
      _ = _ := by rw [show 1 / 2 * θ * S.dF c y' = θ / 2 * S.dF c y' by ring]; ring
  -- the outer sum
  have hch := chain2 S (δ := ρ - θ / 16) (δ' := 7 / 16 * θ) (by linarith) (by positivity)
    (by rw [min_eq_right (by linarith)]; exact hRMc) hy (y' := y')
  rw [min_eq_right (by linarith)] at hch
  calc _ ≤ ∑ c ∈ detB S.toDomSeq, (S.L : ℝ) ^ (2 * jj y) * Real.exp (-(ρ * S.dF y c)) * ((S.L : ℝ) ^ (4 * jj c))⁻¹ *
        ((S.L : ℝ) ^ (4 : ℝ) * (S.toContSeq).c1 (1 / 2) θ * ((S.L : ℝ) ^ (4 * jj y'))⁻¹ * (S.L : ℝ) ^ (2 * jj y') *
          Real.exp (-(θ / 2 * S.dF c y'))) := by
        refine sum_le_sum fun c hc => ?_
        rw [← mul_sum]
        exact mul_le_mul_of_nonneg_left (le_of_eq_of_le (sum_congr rfl fun c' _ => by ring) (hA c hc))
          (by positivity)
    _ ≤ ∑ c ∈ detB S.toDomSeq, (S.L : ℝ) ^ (12 : ℝ) * (S.toContSeq).c1 (1 / 2) θ * ((S.L : ℝ) ^ (4 * jj y'))⁻¹ *
        (Real.exp (-((ρ - θ / 16) * S.dF y c)) * Real.exp (-(7 / 16 * θ * S.dF c y'))) := by
        refine sum_le_sum fun c _ => ?_
        have h1 := sq_shift S (δ := θ / 2) (by positivity) hRMs c y
        have h2 := sq_shift S (δ := θ / 2) (by positivity) hRMs c y'
        have hd1 := S.dF_nonneg y c
        have hd2 := S.dF_nonneg c y'
        have hc4 : (0 : ℝ) < (S.L : ℝ) ^ (4 * jj c) := by positivity
        have e2 : (S.L : ℝ) ^ (2 * jj c) * (S.L : ℝ) ^ (2 * jj c) * ((S.L : ℝ) ^ (4 * jj c))⁻¹ = 1 := by
          rw [← pow_add, show 2 * jj c + 2 * jj c = 4 * jj c by ring, mul_inv_cancel₀ hc4.ne']
        have e12 : (S.L : ℝ) ^ (12 : ℝ) = (S.L : ℝ) ^ (4 : ℝ) * (S.L : ℝ) ^ (4 : ℝ) * (S.L : ℝ) ^ (4 : ℝ) := by
          rw [← Real.rpow_add hL, ← Real.rpow_add hL]; norm_num
        have hE : Real.exp (-(ρ * S.dF y c)) * Real.exp (-(θ / 2 * S.dF c y')) *
            (Real.exp (θ / 2 / 8 * S.dF c y) * Real.exp (θ / 2 / 8 * S.dF c y')) =
            Real.exp (-((ρ - θ / 16) * S.dF y c)) * Real.exp (-(7 / 16 * θ * S.dF c y')) := by
          rw [S.dF_comm c y]; simp only [← Real.exp_add]; congr 1; ring
        have hP : 0 ≤ (S.L : ℝ) ^ (4 : ℝ) * (S.toContSeq).c1 (1 / 2) θ * ((S.L : ℝ) ^ (4 * jj y'))⁻¹ *
            Real.exp (-(ρ * S.dF y c)) * Real.exp (-(θ / 2 * S.dF c y')) * ((S.L : ℝ) ^ (4 * jj c))⁻¹ := by positivity
        calc (S.L : ℝ) ^ (2 * jj y) * Real.exp (-(ρ * S.dF y c)) * ((S.L : ℝ) ^ (4 * jj c))⁻¹ *
              ((S.L : ℝ) ^ (4 : ℝ) * (S.toContSeq).c1 (1 / 2) θ * ((S.L : ℝ) ^ (4 * jj y'))⁻¹ *
                (S.L : ℝ) ^ (2 * jj y') * Real.exp (-(θ / 2 * S.dF c y')))
            = ((S.L : ℝ) ^ (4 : ℝ) * (S.toContSeq).c1 (1 / 2) θ * ((S.L : ℝ) ^ (4 * jj y'))⁻¹ *
                Real.exp (-(ρ * S.dF y c)) * Real.exp (-(θ / 2 * S.dF c y')) * ((S.L : ℝ) ^ (4 * jj c))⁻¹) *
              ((S.L : ℝ) ^ (2 * jj y) * (S.L : ℝ) ^ (2 * jj y')) := by ring
          _ ≤ ((S.L : ℝ) ^ (4 : ℝ) * (S.toContSeq).c1 (1 / 2) θ * ((S.L : ℝ) ^ (4 * jj y'))⁻¹ *
                Real.exp (-(ρ * S.dF y c)) * Real.exp (-(θ / 2 * S.dF c y')) * ((S.L : ℝ) ^ (4 * jj c))⁻¹) *
              (((S.L : ℝ) ^ (4 : ℝ) * Real.exp (θ / 2 / 8 * S.dF c y) * (S.L : ℝ) ^ (2 * jj c)) *
                ((S.L : ℝ) ^ (4 : ℝ) * Real.exp (θ / 2 / 8 * S.dF c y') * (S.L : ℝ) ^ (2 * jj c))) :=
              mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (by positivity) (by positivity)) hP
          _ = (S.L : ℝ) ^ (4 : ℝ) * (S.L : ℝ) ^ (4 : ℝ) * (S.L : ℝ) ^ (4 : ℝ) * (S.toContSeq).c1 (1 / 2) θ *
                ((S.L : ℝ) ^ (4 * jj y'))⁻¹ *
              (Real.exp (-(ρ * S.dF y c)) * Real.exp (-(θ / 2 * S.dF c y')) *
                (Real.exp (θ / 2 / 8 * S.dF c y) * Real.exp (θ / 2 / 8 * S.dF c y'))) *
              ((S.L : ℝ) ^ (2 * jj c) * (S.L : ℝ) ^ (2 * jj c) * ((S.L : ℝ) ^ (4 * jj c))⁻¹) := by ring
          _ = _ := by rw [hE, e2, e12]; ring
    _ = (S.L : ℝ) ^ (12 : ℝ) * (S.toContSeq).c1 (1 / 2) θ * ((S.L : ℝ) ^ (4 * jj y'))⁻¹ *
        ∑ c ∈ detB S.toDomSeq, Real.exp (-((ρ - θ / 16) * S.dF y c)) * Real.exp (-(7 / 16 * θ * S.dF c y')) := by
        rw [mul_sum]
    _ ≤ (S.L : ℝ) ^ (12 : ℝ) * (S.toContSeq).c1 (1 / 2) θ * ((S.L : ℝ) ^ (4 * jj y'))⁻¹ *
        ((S.toContSeq).c1 (1 / 2) (7 / 16 * θ) * Real.exp (-(1 / 2 * (7 / 16 * θ) * S.dF y y'))) :=
        mul_le_mul_of_nonneg_left hch (by positivity)
    _ = _ := by rw [show 1 / 2 * (7 / 16 * θ) * S.dF y y' = 7 / 32 * θ * S.dF y y' by ring]; ring

/-- **The inverse by linearity**: the solutions of `Tu = δ_{c'}w` bound `T⁻¹`. -/
lemma inv_bound {ι V : Type*} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (K : ι → ι → (V →L[ℂ] V)) (hb : Function.Bijective (kerLin K)) (k : ι → ι → ℝ)
    (h : ∀ (c c' : ι) (u : L2 ι V) (w : V), kerApply K u = CoreLean.single c' w → ‖u.ofLp c‖ ≤ k c c' * ‖w‖)
    (u : L2 ι V) (c : ι) : ‖u.ofLp c‖ ≤ ∑ c', k c c' * ‖(kerApply K u).ofLp c'‖ := by
  set ν := kerApply K u
  choose v hv using fun c' => hb.2 (CoreLean.single c' (ν.ofLp c'))
  have hsum : kerLin K (∑ c', v c') = kerLin K u := by
    rw [map_sum]
    simp only [hv]
    ext c''
    simp only [CoreLean.single, WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_toLp, Pi.single_apply]
    rw [Finset.sum_ite_eq]; simp; rfl
  have hu : u = ∑ c', v c' := (hb.1 hsum).symm
  rw [hu, WithLp.ofLp_sum, Finset.sum_apply]
  refine (norm_sum_le _ _).trans (sum_le_sum fun c' _ => h c c' (v c') _ (hv c'))

/-- `tr(A Ad_W B) = tr(Ad_{W⁻¹}A B)`. -/
lemma ntr_Ad (W : GLN) (A B : Mat) : ntr (A * Ad W B) = ntr (Ad W⁻¹ A * B) := by
  simp only [Ad, inv_inv, ntr]
  congr 1
  rw [show A * ((W : Mat) * B * ((W⁻¹ : GLN) : Mat)) = (A * (W : Mat) * B) * ((W⁻¹ : GLN) : Mat) by
    simp only [Matrix.mul_assoc], Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

/-- **`Q'` is the transpose of `Q'^*`**: `Σ_y a_y⁴tr(A(y)(Q'g)(y)) = ⟨Q'^*A, g⟩`. -/
lemma avg_pair (W : Site NF → Site NF → GLN) (A g : Site NF → Mat) :
    ∑ y ∈ detB S.toDomSeq, (((S.L : ℝ) ^ (4 * jj y) : ℝ) : ℂ) * ntr (A y * avgW S.toDomSeq W y g) =
      P0 (QpStar S W A) g := by
  have hL : (0 : ℝ) < S.L := by exact_mod_cast S.Lpos
  simp only [P0, pairForm0, ConcretePairing.wpair_apply, a1, Complex.ofReal_one, one_pow, one_mul, QpStar]
  rw [sum_blocks S.toDomSeq]
  refine sum_congr rfl fun y hy => ?_
  rw [avgW_blk S.toDomSeq W hy g]
  simp only [toDomSeq_L]
  have hc : (((S.L : ℝ) ^ (4 * jj y) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (pow_pos hL _).ne'
  rw [mul_smul_comm, ntr_smul, ← mul_assoc, mul_inv_cancel₀ hc, one_mul, mul_sum, ntr_sum]
  refine sum_congr rfl fun x hx => ?_
  rw [(sc_mem_blk S.toDomSeq hy hx).2, ntr_Ad]

namespace ScalarHyp

variable {S} {X : Fin 4 → Site (SequenceAverages.N0 S) → Matrix (Fin N) (Fin N) ℂ} {α₁ : ℝ}
  {W : Site (SequenceAverages.N0 S) → Site (SequenceAverages.N0 S) → (Matrix (Fin N) (Fin N) ℂ)ˣ} {η : ℝ}
  {ΩD : Set (Site (SequenceAverages.N0 S))} {δ : ℝ}
  (H : ScalarHyp S X α₁ W η ΩD δ)
include H

/-- `a_y⁴tr(Z(Q'G'f)(y)) = ⟨G'λ_Z, f⟩`. -/
lemma QG_trace [NeZero N] {y : Site NF} (hy : y ∈ detB S.toDomSeq) (Z : Mat) (f : Site NF → Mat) :
    (((S.L : ℝ) ^ (4 * jj y) : ℝ) : ℂ) * ntr (Z * avgW S.toDomSeq W y (Gp' S.toDomSeq (cfgX X) W ΩD f)) =
      P0 (Gp' S.toDomSeq (cfgX X) W ΩD (lamZ S W y Z)) f := by
  rw [Gp'_symm S.toDomSeq _ _ _ H.hK, lamZ, ← avg_pair S W]
  rw [Finset.sum_eq_single y (fun y' _ hne => by rw [if_neg hne]; simp [ntr]) (fun h => absurd hy h), if_pos rfl]

/-- **The kernel of `Q'G'`**: `|(Q'G'f)(y)| ≤ a_y^{-4}Σ_{x'}2√NC_va_{x'}²e^{-(7/8)δd(y(x'), y)}|f(x')|`. -/
theorem QG_bound [NeZero N] {y : Site NF} (hy : y ∈ detB S.toDomSeq) (f : Site NF → Mat) :
    hs (avgW S.toDomSeq W y (Gp' S.toDomSeq (cfgX X) W ΩD f)) ≤
      ((S.L : ℝ) ^ (4 * jj y))⁻¹ * ∑ x', 2 * Real.sqrt N * Cv S δ (Csc S N) (4 * N * (S.L : ℝ) ^ 4) *
        (S.L : ℝ) ^ (2 * jj (bc S.toDomSeq x')) * Real.exp (-(7 / 8 * δ * S.dF (bc S.toDomSeq x') y)) *
          hs (f x') := by
  have hL : (0 : ℝ) < S.L := by exact_mod_cast S.Lpos
  have hCv := H.Cv_nn
  set M := avgW S.toDomSeq W y (Gp' S.toDomSeq (cfgX X) W ΩD f)
  set R := ∑ x', 2 * Real.sqrt N * Cv S δ (Csc S N) (4 * N * (S.L : ℝ) ^ 4) *
    (S.L : ℝ) ^ (2 * jj (bc S.toDomSeq x')) * Real.exp (-(7 / 8 * δ * S.dF (bc S.toDomSeq x') y)) * hs (f x')
  have hR : 0 ≤ R := sum_nonneg fun x' _ => by have := hs_nonneg (N := N) (f x'); positivity
  have ha : (0 : ℝ) < (S.L : ℝ) ^ (4 * jj y) := by positivity
  -- `a_y⁴|M|² ≤ |M|R`
  have key : (S.L : ℝ) ^ (4 * jj y) * hs M ^ 2 ≤ hs M * R := by
    have htr := H.QG_trace hy Mᴴ f
    have hre : (S.L : ℝ) ^ (4 * jj y) * hs M ^ 2 =
        RCLike.re ((((S.L : ℝ) ^ (4 * jj y) : ℝ) : ℂ) * ntr (Mᴴ * M)) := by
      rw [RCLike.re_to_complex, Complex.re_ofReal_mul, hs_sq]; rfl
    rw [hre, htr]
    refine (RCLike.re_le_norm _).trans ((P0_abs_le S _ _).trans ?_)
    rw [mul_sum]
    refine sum_le_sum fun x' _ => ?_
    have hG := H.KB_Gp' (bc S.toDomSeq x') (bc_mem_detB S x') y hy (lamZ S W y Mᴴ)
      (2 * Real.sqrt N * hs Mᴴ) (by have := hs_nonneg (N := N) Mᴴ; positivity) (lamZ_supp S W hy _) (lamZ_bound S H.hW hy _) x' (mem_blk_bc S x')
    rw [hs_conjTranspose] at hG
    simp only [zero_mul, pow_zero, mul_one] at hG
    have hf := hs_nonneg (N := N) (f x')
    calc hs (Gp' S.toDomSeq (cfgX X) W ΩD (lamZ S W y Mᴴ) x') * hs (f x')
        ≤ Cv S δ (Csc S N) (4 * N * (S.L : ℝ) ^ 4) * (S.L : ℝ) ^ (2 * jj (bc S.toDomSeq x')) *
            Real.exp (-(7 / 8 * δ * S.dF (bc S.toDomSeq x') y)) * (2 * Real.sqrt N * hs M) * hs (f x') :=
          mul_le_mul_of_nonneg_right hG hf
      _ = _ := by ring
  rcases (hs_nonneg (N := N) M).eq_or_lt with h0 | hpos
  · rw [← h0]; exact mul_nonneg (inv_nonneg.2 ha.le) hR
  · rw [le_inv_mul_iff₀ ha]
    nlinarith

end ScalarHyp

/-- `Q'^*` of a family on `𝐁_D` extended by zero is the sum of the `λ_Z`. -/
lemma sum_lamZ (W : Site NF → Site NF → GLN) {ΩD : Set (Site NF)} (a : BD S ΩD → Mat) :
    ∑ c : BD S ΩD, lamZ S W c.1 (a c) = QpStar S W (extBD S a) := by
  funext x
  rw [Finset.sum_apply]
  simp only [lamZ, QpStar, extBD]
  by_cases h : bc S.toDomSeq x ∈ BD S ΩD
  · rw [dif_pos h, Fintype.sum_eq_single ⟨bc S.toDomSeq x, h⟩]
    · simp
    · intro c hc
      rw [if_neg (fun he => hc (Subtype.ext he.symm))]; simp [Ad]
  · rw [dif_neg h]
    rw [show Ad (W (bc S.toDomSeq x) x)⁻¹ (0 : Mat) = 0 by simp [Ad]]
    refine sum_eq_zero fun c _ => ?_
    rw [if_neg (fun he => h (by rw [he]; exact c.2))]; simp [Ad]

/-- A sum over `𝐁_D` of a nonnegative function is at most the sum over `𝐁`. -/
lemma sum_BD_le_detB {ΩD : Set (Site NF)} (F : Site NF → ℝ) (hF : ∀ y, 0 ≤ F y) :
    ∑ c : BD S ΩD, F c.1 ≤ ∑ y ∈ detB S.toDomSeq, F y := by
  rw [Finset.sum_coe_sort (BD S ΩD) F]
  exact sum_le_sum_of_subset_of_nonneg (BD_sub S ΩD) fun y _ _ => hF y

/-- `Q'` as a linear map. -/
def avgL (W : Site NF → Site NF → GLN) : (Site NF → Mat) →ₗ[ℂ] (Site NF → Mat) where
  toFun v y := avgW S.toDomSeq W y v
  map_add' v w := by funext y; exact avgW_add S W y v w
  map_smul' a v := by funext y; exact avgW_smul S W y a v

/-- `Q'^*` as a linear map. -/
def QpL (W : Site NF → Site NF → GLN) : (Site NF → Mat) →ₗ[ℂ] (Site NF → Mat) where
  toFun := QpStar S W
  map_add' μ ν := by funext x; simp only [QpStar, Pi.add_apply]; exact Ad_add _ _ _
  map_smul' a μ := by funext x; simp only [QpStar, Pi.smul_apply, RingHom.id_apply]; exact Ad_smul _ _ _

/-- The restriction to `𝐁_D`, with values in `V`. -/
def blkL (ΩD : Set (Site NF)) : (Site NF → Mat) →ₗ[ℂ] L2 (BD S ΩD) (VS N 1) where
  toFun v := WithLp.toLp 2 fun c => emb (v c.1)
  map_add' v w := by ext c p; rfl
  map_smul' a v := by ext c p; rfl

/-- The extension by zero of `a_c^{-4}u(c)`: the passage from `T̂⁻¹` to `T⁻¹`. -/
def unblkL (ΩD : Set (Site NF)) : L2 (BD S ΩD) (VS N 1) →ₗ[ℂ] (Site NF → Mat) where
  toFun u := extBD S fun c => ((((S.L : ℝ) ^ (4 * jj c.1)) : ℝ) : ℂ)⁻¹ • proj (u.ofLp c)
  map_add' u v := by
    funext x; simp only [extBD, Pi.add_apply]; split_ifs
    · rw [← smul_add]; congr 1
    · simp
  map_smul' a u := by
    funext x; simp only [extBD, Pi.smul_apply, RingHom.id_apply]; split_ifs
    · rw [smul_comm]; congr 1
    · simp

open scoped Classical in
/-- `T̂⁻¹`, where `T̂` is invertible. -/
def Tinv (X : Fin 4 → Site NF → Mat) (W : Site NF → Site NF → GLN) (ΩD : Set (Site NF)) :
    L2 (BD S ΩD) (VS N 1) →ₗ[ℂ] L2 (BD S ΩD) (VS N 1) :=
  if h : Function.Bijective (kerLin (kerT S (Subtype.val : BD S ΩD → Site NF) X W ΩD)) then
    (LinearEquiv.ofBijective _ h).symm.toLinearMap
  else 0

lemma kerApply_Tinv (X : Fin 4 → Site NF → Mat) (W : Site NF → Site NF → GLN) (ΩD : Set (Site NF))
    (h : Function.Bijective (kerLin (kerT S (Subtype.val : BD S ΩD → Site NF) X W ΩD))) (ν : L2 (BD S ΩD) (VS N 1)) :
    kerApply (kerT S (Subtype.val : BD S ΩD → Site NF) X W ΩD) (Tinv S X W ΩD ν) = ν := by
  classical
  unfold Tinv
  rw [dif_pos h]
  exact (LinearEquiv.ofBijective _ h).apply_symm_apply ν

/-- **The projection** `P = G'Q'^*T⁻¹Q'G'`. -/
def Pop (X : Fin 4 → Site NF → Mat) (W : Site NF → Site NF → GLN) (ΩD : Set (Site NF)) :
    Module.End ℂ (Site NF → Mat) :=
  Gp' S.toDomSeq (cfgX X) W ΩD ∘ₗ QpL S W ∘ₗ unblkL S ΩD ∘ₗ Tinv S X W ΩD ∘ₗ blkL S ΩD ∘ₗ avgL S W ∘ₗ
    Gp' S.toDomSeq (cfgX X) W ΩD

/-- `γ_B = c_lo²`. -/
def gammaB (N : ℕ) : ℝ := ((9 / 32) ^ 4 / (864 + 4 * N)) ^ 2

/-- The rate `θ_B` of `T̂⁻¹`. -/
def thetaB (S : SeqDom) (N : ℕ) (δ : ℝ) : ℝ :=
  min (1 / 64 * δ) (min (1 / 4 * δ / 2) (gammaB N * (1 / 4 * δ) /
    (6 * (kappaB S N δ + 1) * ((S.toContSeq).c1 (1 / 2) (1 / 8 * δ) + 1))))

/-- The constant of the kernel of `P`. -/
def CPk (S : SeqDom) (N : ℕ) (δ : ℝ) : ℝ :=
  (2 * Real.sqrt N * Cv S δ (Csc S N) (4 * N * (S.L : ℝ) ^ 4)) ^ 2 * (2 / gammaB N) * (S.L : ℝ) ^ (12 : ℝ) *
    (S.toContSeq).c1 (1 / 2) (thetaB S N δ) * (S.toContSeq).c1 (1 / 2) (7 / 16 * thetaB S N δ)

namespace ScalarHyp

variable {S} {X : Fin 4 → Site (SequenceAverages.N0 S) → Matrix (Fin N) (Fin N) ℂ} {α₁ : ℝ}
  {W : Site (SequenceAverages.N0 S) → Site (SequenceAverages.N0 S) → (Matrix (Fin N) (Fin N) ℂ)ˣ} {η : ℝ}
  {ΩD : Set (Site (SequenceAverages.N0 S))} {δ : ℝ}
  (H : ScalarHyp S X α₁ W η ΩD δ)
include H

lemma thetaB_pos [NeZero N] : 0 < thetaB S N δ := by
  have hδ := H.hδ0
  have hκ : 0 ≤ kappaB S N δ := by
    have := H.Cv_nn
    have hc1 : 0 ≤ (S.toContSeq).c1 (1 / 2) (3 / 4 * δ) := by unfold Summation.ContSeq.c1; positivity
    unfold kappaB CG2; positivity
  have hc1 : 0 ≤ (S.toContSeq).c1 (1 / 2) (1 / 8 * δ) := by unfold Summation.ContSeq.c1; positivity
  unfold thetaB gammaB
  exact lt_min (by positivity) (lt_min (by positivity) (by positivity))

/-- **The kernel of `P`** (`prop:sf-block`, the last part, for `P`): for `x ∈ Δ(y)`,
`|(Pf)(x)| ≤ C_PΣ_{x'}a_{y(x')}^{-4}e^{-(7/32)θ_Bd(y(x), y(x'))}|f(x')|`. -/
theorem P_bound [NeZero N]
    (hRMb : (S.toContSeq).r1 (1 / 2) (1 / 32 * δ) ≤ RMS) (hRMs4 : 32 * Real.log S.L / (1 / 4 * δ) ≤ RMS)
    (hsmallT : CTd S N δ α₁ η * (S.toContSeq).c1 (1 / 2) (1 / 32 * δ) ≤ gammaB N / 4)
    (hRMθs : 32 * Real.log S.L / (thetaB S N δ / 2) ≤ RMS)
    (hRMθc : (S.toContSeq).r1 (1 / 2) (7 / 16 * thetaB S N δ) ≤ RMS) (f : Site NF → Mat) (x : Site NF) :
    hs (Pop S X W ΩD f x) ≤ CPk S N δ * ∑ x', ((S.L : ℝ) ^ (4 * jj (bc S.toDomSeq x')))⁻¹ *
      Real.exp (-(7 / 32 * thetaB S N δ * S.dF (bc S.toDomSeq x) (bc S.toDomSeq x'))) * hs (f x') := by
  have hL : (0 : ℝ) < S.L := by exact_mod_cast S.Lpos
  have hδ := H.hδ0
  have hCv := H.Cv_nn
  have hθ := H.thetaB_pos (N := N)
  have hθle : thetaB S N δ ≤ 1 / 64 * δ := min_le_left _ _
  have hγ : 0 < gammaB N := by unfold gammaB; positivity
  have hN : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N))
  obtain ⟨hb, hsol⟩ := H.block_inverse hRMb hRMs4 hsmallT
  set G := Gp' S.toDomSeq (cfgX X) W ΩD
  set g : Site NF → Mat := avgL S W (G f)
  set u := Tinv S X W ΩD (blkL S ΩD g)
  set Zc : BD S ΩD → Mat := fun c => ((((S.L : ℝ) ^ (4 * jj c.1)) : ℝ) : ℂ)⁻¹ • proj (u.ofLp c)
  set CV := Cv S δ (Csc S N) (4 * N * (S.L : ℝ) ^ 4)
  set y := bc S.toDomSeq x
  have hy : y ∈ detB S.toDomSeq := bc_mem_detB S x
  -- `Pf = Σ_c G'λ_{Z_c}`
  have hP : Pop S X W ΩD f = ∑ c : BD S ΩD, G (lamZ S W c.1 (Zc c)) := by
    rw [← map_sum, sum_lamZ]; rfl
  -- the bound of `T̂⁻¹`
  have hu : ∀ c : BD S ΩD, hs (proj (u.ofLp c)) ≤
      ∑ c' : BD S ΩD, 2 / gammaB N * Real.exp (-(thetaB S N δ * S.dF c.1 c'.1)) * hs (g c'.1) := by
    intro c
    have h1 := inv_bound _ hb _ hsol u c
    rw [kerApply_Tinv S X W ΩD hb] at h1
    rw [norm_eq_proj] at h1
    have h2 : ∀ c' : BD S ΩD, ‖(blkL S ΩD g).ofLp c'‖ = Real.sqrt N * hs (g c'.1) := fun c' => by
      rw [show (blkL S ΩD g).ofLp c' = emb (g c'.1) from rfl, norm_emb]
    simp only [h2] at h1
    rw [← mul_le_mul_iff_of_pos_left hN, mul_sum]
    refine h1.trans (le_of_eq (sum_congr rfl fun c' _ => ?_))
    unfold thetaB gammaB; ring_nf
  -- the bound of `Q'G'`
  have hg : ∀ c' : BD S ΩD, hs (g c'.1) ≤ ((S.L : ℝ) ^ (4 * jj c'.1))⁻¹ * ∑ x', 2 * Real.sqrt N * CV *
      (S.L : ℝ) ^ (2 * jj (bc S.toDomSeq x')) * Real.exp (-(7 / 8 * δ * S.dF (bc S.toDomSeq x') c'.1)) * hs (f x') :=
    fun c' => H.QG_bound ((BD_sub S ΩD) c'.2) f
  -- the bound of `G'Q'^*`
  have hG : ∀ c : BD S ΩD, hs (G (lamZ S W c.1 (Zc c)) x) ≤
      2 * Real.sqrt N * CV * (S.L : ℝ) ^ (2 * jj y) * Real.exp (-(7 / 8 * δ * S.dF y c.1)) *
        (((S.L : ℝ) ^ (4 * jj c.1))⁻¹ * hs (proj (u.ofLp c))) := by
    intro c
    have hc := (BD_sub S ΩD) c.2
    have hZ : hs (Zc c) = ((S.L : ℝ) ^ (4 * jj c.1))⁻¹ * hs (proj (u.ofLp c)) := by
      simp only [Zc]
      rw [RegularAverages.hs_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have h := H.KB_Gp' y hy c.1 hc (lamZ S W c.1 (Zc c)) (2 * Real.sqrt N * hs (Zc c))
      (by have := hs_nonneg (N := N) (Zc c); positivity) (lamZ_supp S W hc _) (lamZ_bound S H.hW hc _) x (mem_blk_bc S x)
    simp only [zero_mul, pow_zero, mul_one] at h
    rw [hZ] at h
    linarith
  -- the integrand of `chainP`
  set ρ : ℝ := 7 / 8 * δ
  set E : Site NF → Site NF → Site NF → ℝ := fun y' c c' =>
    (S.L : ℝ) ^ (2 * jj y) * Real.exp (-(ρ * S.dF y c)) * ((S.L : ℝ) ^ (4 * jj c))⁻¹ *
      (Real.exp (-(thetaB S N δ * S.dF c c')) * ((S.L : ℝ) ^ (4 * jj c'))⁻¹ * (S.L : ℝ) ^ (2 * jj y') *
        Real.exp (-(ρ * S.dF c' y')))
  have hE0 : ∀ y' c c', 0 ≤ E y' c c' := fun y' c c' => by positivity
  set K := (2 * Real.sqrt N * CV) ^ 2 * (2 / gammaB N)
  have hK0 : 0 ≤ K := by positivity
  -- the three bounds composed
  have hstep : hs (Pop S X W ΩD f x) ≤
      ∑ c : BD S ΩD, ∑ c' : BD S ΩD, ∑ x', K * E (bc S.toDomSeq x') c.1 c'.1 * hs (f x') := by
    rw [hP, Finset.sum_apply]
    refine (RegularAverages.hs_sum_le _ _).trans (sum_le_sum fun c _ => (hG c).trans ?_)
    have hA0 : 0 ≤ 2 * Real.sqrt N * CV * (S.L : ℝ) ^ (2 * jj y) * Real.exp (-(7 / 8 * δ * S.dF y c.1)) *
        ((S.L : ℝ) ^ (4 * jj c.1))⁻¹ := by positivity
    calc 2 * Real.sqrt N * CV * (S.L : ℝ) ^ (2 * jj y) * Real.exp (-(7 / 8 * δ * S.dF y c.1)) *
          (((S.L : ℝ) ^ (4 * jj c.1))⁻¹ * hs (proj (u.ofLp c)))
        = 2 * Real.sqrt N * CV * (S.L : ℝ) ^ (2 * jj y) * Real.exp (-(7 / 8 * δ * S.dF y c.1)) *
          ((S.L : ℝ) ^ (4 * jj c.1))⁻¹ * hs (proj (u.ofLp c)) := by ring
      _ ≤ 2 * Real.sqrt N * CV * (S.L : ℝ) ^ (2 * jj y) * Real.exp (-(7 / 8 * δ * S.dF y c.1)) *
          ((S.L : ℝ) ^ (4 * jj c.1))⁻¹ * ∑ c' : BD S ΩD, 2 / gammaB N *
            Real.exp (-(thetaB S N δ * S.dF c.1 c'.1)) * (((S.L : ℝ) ^ (4 * jj c'.1))⁻¹ * ∑ x', 2 * Real.sqrt N * CV *
              (S.L : ℝ) ^ (2 * jj (bc S.toDomSeq x')) * Real.exp (-(7 / 8 * δ * S.dF (bc S.toDomSeq x') c'.1)) *
                hs (f x')) := by
          refine mul_le_mul_of_nonneg_left ((hu c).trans (sum_le_sum fun c' _ => ?_)) hA0
          exact mul_le_mul_of_nonneg_left (hg c') (by positivity)
      _ = _ := by
          rw [mul_sum]
          refine sum_congr rfl fun c' _ => ?_
          rw [mul_sum, mul_sum, mul_sum]
          refine sum_congr rfl fun x' _ => ?_
          simp only [E, K, ρ]
          rw [S.dF_comm (bc S.toDomSeq x') c'.1]
          ring
  -- the order of the sums
  have hswap : ∑ c : BD S ΩD, ∑ c' : BD S ΩD, ∑ x', K * E (bc S.toDomSeq x') c.1 c'.1 * hs (f x') =
      ∑ x', K * hs (f x') * ∑ c : BD S ΩD, ∑ c' : BD S ΩD, E (bc S.toDomSeq x') c.1 c'.1 := by
    rw [sum_congr rfl fun c _ => Finset.sum_comm, Finset.sum_comm]
    refine sum_congr rfl fun x' _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun c _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun c' _ => ?_
    ring
  -- the double sum
  have hsum : ∀ x', ∑ c : BD S ΩD, ∑ c' : BD S ΩD, E (bc S.toDomSeq x') c.1 c'.1 ≤
      (S.L : ℝ) ^ (12 : ℝ) * (S.toContSeq).c1 (1 / 2) (thetaB S N δ) *
        (S.toContSeq).c1 (1 / 2) (7 / 16 * thetaB S N δ) * ((S.L : ℝ) ^ (4 * jj (bc S.toDomSeq x')))⁻¹ *
          Real.exp (-(7 / 32 * thetaB S N δ * S.dF y (bc S.toDomSeq x'))) := by
    intro x'
    refine le_trans ?_ (chainP S hθ (show 9 / 8 * thetaB S N δ ≤ 7 / 8 * δ by linarith) hRMθs hRMθc hy
      (y' := bc S.toDomSeq x'))
    refine (sum_le_sum fun c _ => sum_BD_le_detB S (fun c' => E (bc S.toDomSeq x') c.1 c')
      fun c' => hE0 _ _ _).trans ?_
    exact sum_BD_le_detB S (fun c => ∑ c' ∈ detB S.toDomSeq, E (bc S.toDomSeq x') c c')
      fun c => sum_nonneg fun c' _ => hE0 _ _ _
  rw [hswap] at hstep
  refine hstep.trans ?_
  rw [mul_sum]
  refine sum_le_sum fun x' _ => ?_
  have hf := hs_nonneg (N := N) (f x')
  calc K * hs (f x') * ∑ c : BD S ΩD, ∑ c' : BD S ΩD, E (bc S.toDomSeq x') c.1 c'.1
      ≤ K * hs (f x') * ((S.L : ℝ) ^ (12 : ℝ) * (S.toContSeq).c1 (1 / 2) (thetaB S N δ) *
        (S.toContSeq).c1 (1 / 2) (7 / 16 * thetaB S N δ) * ((S.L : ℝ) ^ (4 * jj (bc S.toDomSeq x')))⁻¹ *
          Real.exp (-(7 / 32 * thetaB S N δ * S.dF y (bc S.toDomSeq x')))) :=
        mul_le_mul_of_nonneg_left (hsum x') (by positivity)
    _ = _ := by simp only [CPk, K, CV]; ring

end ScalarHyp

/-- `|⟨A, B⟩| ≤ Σ_xΣ_ν|A_ν(x)||B_ν(x)|` for the pairing of `1`-forms. -/
lemma pair1_abs_le (A B : Fin 4 → Site NF → Mat) :
    ‖pairForm1 a1 A B‖ ≤ ∑ x, ∑ ν : Fin 4, hs (A ν x) * hs (B ν x) := by
  rw [pairForm1_apply']
  simp only [ConcretePairing.wpair_apply, a1, Complex.ofReal_one, one_pow, one_mul]
  rw [Finset.sum_comm]
  exact (norm_sum_le _ _).trans (sum_le_sum fun x _ => (norm_sum_le _ _).trans
    (sum_le_sum fun ν _ => norm_ntr_mul_le _ _))

/-- The component `ν` of `D_𝐔` as a linear map. -/
def DfwL (U : Config N NF) (ν : Fin 4) : Module.End ℂ (Site NF → Mat) := LinearMap.proj ν ∘ₗ D0L a1 U

lemma DfwL_apply (U : Config N NF) (ν : Fin 4) (f : Site NF → Mat) (x : Site NF) :
    DfwL S U ν f x = Dfw 1 U ν f x := by
  simp only [DfwL, LinearMap.coe_comp, Function.comp_apply, LinearMap.proj_apply, D0L_apply, D0, a1,
    Complex.ofReal_one]

namespace ScalarHyp

variable {S} {X : Fin 4 → Site (SequenceAverages.N0 S) → Matrix (Fin N) (Fin N) ℂ} {α₁ : ℝ}
  {W : Site (SequenceAverages.N0 S) → Site (SequenceAverages.N0 S) → (Matrix (Fin N) (Fin N) ℂ)ˣ} {η : ℝ}
  {ΩD : Set (Site (SequenceAverages.N0 S))} {δ : ℝ}
  (H : ScalarHyp S X α₁ W η ΩD δ)
include H

lemma Cg_nn' [NeZero N] : 0 ≤ Cg S δ (Csc S N) (4 * N * (S.L : ℝ) ^ 4) α₁ := by
  have := H.hδ0; have := H.hα0
  have hc1 : 0 ≤ (S.toContSeq).c1 (1 / 2) δ := by unfold Summation.ContSeq.c1; positivity
  unfold Cg Cd C2 CTh CF Ksf Ksfb Csc
  have := KH_ge (1 / 2) (by norm_num); have := KD_ge (1 / 2) (by norm_num) (by norm_num)
  positivity

/-- **The kernel of `Q'G'D^*_𝐔`**: `|(Q'G'D^*h)(y)| ≤ a_y^{-4}Σ_{x'}2√NC_ga_{x'}e^{-(7/8)δd(y(x'), y)}Σ_ν|h_ν(x')|`,
by the symmetry of `G'` and `⟨D_𝐔λ, h⟩ = ⟨λ, D^*_𝐔h⟩`. -/
theorem QGs_bound [NeZero N] {y : Site NF} (hy : y ∈ detB S.toDomSeq) (h : Fin 4 → Site NF → Mat) :
    hs (avgW S.toDomSeq W y (Gp' S.toDomSeq (cfgX X) W ΩD (Ds1L a1 (cfgX X) h))) ≤
      ((S.L : ℝ) ^ (4 * jj y))⁻¹ * ∑ x', 2 * Real.sqrt N * Cg S δ (Csc S N) (4 * N * (S.L : ℝ) ^ 4) α₁ *
        (S.L : ℝ) ^ jj (bc S.toDomSeq x') * Real.exp (-(7 / 8 * δ * S.dF (bc S.toDomSeq x') y)) *
          ∑ ν : Fin 4, hs (h ν x') := by
  have hL : (0 : ℝ) < S.L := by exact_mod_cast S.Lpos
  have hCg := H.Cg_nn'
  set M := avgW S.toDomSeq W y (Gp' S.toDomSeq (cfgX X) W ΩD (Ds1L a1 (cfgX X) h))
  set R := ∑ x', 2 * Real.sqrt N * Cg S δ (Csc S N) (4 * N * (S.L : ℝ) ^ 4) α₁ *
    (S.L : ℝ) ^ jj (bc S.toDomSeq x') * Real.exp (-(7 / 8 * δ * S.dF (bc S.toDomSeq x') y)) *
      ∑ ν : Fin 4, hs (h ν x')
  have hR : 0 ≤ R := sum_nonneg fun x' _ => by
    have := sum_nonneg fun ν (_ : ν ∈ univ) => hs_nonneg (N := N) (h ν x'); positivity
  have ha : (0 : ℝ) < (S.L : ℝ) ^ (4 * jj y) := by positivity
  have key : (S.L : ℝ) ^ (4 * jj y) * hs M ^ 2 ≤ hs M * R := by
    have htr := H.QG_trace hy Mᴴ (Ds1L a1 (cfgX X) h)
    have hre : (S.L : ℝ) ^ (4 * jj y) * hs M ^ 2 =
        RCLike.re ((((S.L : ℝ) ^ (4 * jj y) : ℝ) : ℂ) * ntr (Mᴴ * M)) := by
      rw [RCLike.re_to_complex, Complex.re_ofReal_mul, hs_sq]; rfl
    rw [hre, htr, show P0 (Gp' S.toDomSeq (cfgX X) W ΩD (lamZ S W y Mᴴ)) (Ds1L a1 (cfgX X) h) =
      pairForm1 a1 (D0L a1 (cfgX X) (Gp' S.toDomSeq (cfgX X) W ΩD (lamZ S W y Mᴴ))) h from
        (D0L_transpose a1 _ _ _).symm]
    refine (RCLike.re_le_norm _).trans ((pair1_abs_le S _ _).trans ?_)
    rw [mul_sum]
    refine sum_le_sum fun x' _ => ?_
    refine (sum_le_sum fun ν _ => ?_).trans (le_of_eq (show ∑ ν : Fin 4,
      Cg S δ (Csc S N) (4 * N * (S.L : ℝ) ^ 4) α₁ * Real.exp (-(7 / 8 * δ * S.dF (bc S.toDomSeq x') y)) *
        ((S.L : ℝ) ^ jj (bc S.toDomSeq x') * (2 * Real.sqrt N * hs M)) * hs (h ν x') = _ by rw [← mul_sum]; ring))
    have hG := H.gradient (bc_mem_detB S x') hy (mem_blk_bc S x') (lam := lamZ S W y Mᴴ)
      (Λ := 2 * Real.sqrt N * hs Mᴴ) (by have := hs_nonneg (N := N) Mᴴ; positivity) (lamZ_supp S W hy _)
      (lamZ_bound S H.hW hy _) ν
    rw [hs_conjTranspose] at hG
    have hD : D0L a1 (cfgX X) (Gp' S.toDomSeq (cfgX X) W ΩD (lamZ S W y Mᴴ)) ν x' =
        Dfw 1 (cfgX X) ν (Gp' S.toDomSeq (cfgX X) W ΩD (lamZ S W y Mᴴ)) x' := by
      simp only [D0L_apply, D0, a1, Complex.ofReal_one]
    rw [hD]
    exact mul_le_mul_of_nonneg_right hG (hs_nonneg _)
  rcases (hs_nonneg (N := N) M).eq_or_lt with h0 | hpos
  · rw [← h0]; exact mul_nonneg (inv_nonneg.2 ha.le) hR
  · rw [le_inv_mul_iff₀ ha]
    nlinarith

/-- **The general kernel bound** behind `P`, `∇P`, `P∇^*`, `∇P∇^*`: a left operator bounded on the `λ_Z` like `G'`,
composed with `Q'^*T⁻¹`, applied to data `g` bounded on `𝐁_D` like `Q'G'f`. -/
theorem Pgen [NeZero N]
    (hRMb : (S.toContSeq).r1 (1 / 2) (1 / 32 * δ) ≤ RMS) (hRMs4 : 32 * Real.log S.L / (1 / 4 * δ) ≤ RMS)
    (hsmallT : CTd S N δ α₁ η * (S.toContSeq).c1 (1 / 2) (1 / 32 * δ) ≤ gammaB N / 4)
    (hRMθs : 32 * Real.log S.L / (thetaB S N δ / 2) ≤ RMS)
    (hRMθc : (S.toContSeq).r1 (1 / 2) (7 / 16 * thetaB S N δ) ≤ RMS)
    (Lop : Module.End ℂ (Site NF → Mat)) {y x : Site NF} (hy : y ∈ detB S.toDomSeq) {A0 εL : ℝ}
    (hA0 : 0 ≤ A0) (hεL : 0 ≤ εL)
    (hLop : ∀ (c : BD S ΩD) (Z : Mat), hs (Lop (lamZ S W c.1 Z) x) ≤
      A0 * εL * (S.L : ℝ) ^ (2 * jj y) * Real.exp (-(7 / 8 * δ * S.dF y c.1)) * hs Z)
    (g : Site NF → Mat) (w εR : Site NF → ℝ) (hw : ∀ x', 0 ≤ w x') (hεR : ∀ x', 0 ≤ εR x') {B0 : ℝ} (hB0 : 0 ≤ B0)
    (hg : ∀ c : BD S ΩD, hs (g c.1) ≤ ((S.L : ℝ) ^ (4 * jj c.1))⁻¹ * ∑ x', B0 * εR x' *
      (S.L : ℝ) ^ (2 * jj (bc S.toDomSeq x')) * Real.exp (-(7 / 8 * δ * S.dF (bc S.toDomSeq x') c.1)) * w x') :
    hs (Lop (QpL S W (unblkL S ΩD (Tinv S X W ΩD (blkL S ΩD g)))) x) ≤
      A0 * B0 * (2 / gammaB N) * (S.L : ℝ) ^ (12 : ℝ) * (S.toContSeq).c1 (1 / 2) (thetaB S N δ) *
        (S.toContSeq).c1 (1 / 2) (7 / 16 * thetaB S N δ) * εL * ∑ x', εR x' *
          ((S.L : ℝ) ^ (4 * jj (bc S.toDomSeq x')))⁻¹ *
            Real.exp (-(7 / 32 * thetaB S N δ * S.dF y (bc S.toDomSeq x'))) * w x' := by
  have hL : (0 : ℝ) < S.L := by exact_mod_cast S.Lpos
  have hδ := H.hδ0
  have hθ := H.thetaB_pos (N := N)
  have hθle : thetaB S N δ ≤ 1 / 64 * δ := min_le_left _ _
  have hγ : 0 < gammaB N := by unfold gammaB; positivity
  have hN : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N))
  have hc1 : 0 ≤ (S.toContSeq).c1 (1 / 2) (thetaB S N δ) := by unfold Summation.ContSeq.c1; positivity
  have hc2 : 0 ≤ (S.toContSeq).c1 (1 / 2) (7 / 16 * thetaB S N δ) := by unfold Summation.ContSeq.c1; positivity
  obtain ⟨hb, hsol⟩ := H.block_inverse hRMb hRMs4 hsmallT
  set u := Tinv S X W ΩD (blkL S ΩD g)
  set Zc : BD S ΩD → Mat := fun c => ((((S.L : ℝ) ^ (4 * jj c.1)) : ℝ) : ℂ)⁻¹ • proj (u.ofLp c)
  have hP : Lop (QpL S W (unblkL S ΩD u)) = ∑ c : BD S ΩD, Lop (lamZ S W c.1 (Zc c)) := by
    rw [← map_sum, sum_lamZ]; rfl
  have hu : ∀ c : BD S ΩD, hs (proj (u.ofLp c)) ≤
      ∑ c' : BD S ΩD, 2 / gammaB N * Real.exp (-(thetaB S N δ * S.dF c.1 c'.1)) * hs (g c'.1) := by
    intro c
    have h1 := inv_bound _ hb _ hsol u c
    rw [kerApply_Tinv S X W ΩD hb] at h1
    rw [norm_eq_proj] at h1
    have h2 : ∀ c' : BD S ΩD, ‖(blkL S ΩD g).ofLp c'‖ = Real.sqrt N * hs (g c'.1) := fun c' => by
      rw [show (blkL S ΩD g).ofLp c' = emb (g c'.1) from rfl, norm_emb]
    simp only [h2] at h1
    rw [← mul_le_mul_iff_of_pos_left hN, mul_sum]
    refine h1.trans (le_of_eq (sum_congr rfl fun c' _ => ?_))
    unfold thetaB gammaB; ring_nf
  have hG : ∀ c : BD S ΩD, hs (Lop (lamZ S W c.1 (Zc c)) x) ≤
      A0 * εL * (S.L : ℝ) ^ (2 * jj y) * Real.exp (-(7 / 8 * δ * S.dF y c.1)) *
        (((S.L : ℝ) ^ (4 * jj c.1))⁻¹ * hs (proj (u.ofLp c))) := by
    intro c
    have hZ : hs (Zc c) = ((S.L : ℝ) ^ (4 * jj c.1))⁻¹ * hs (proj (u.ofLp c)) := by
      simp only [Zc]
      rw [RegularAverages.hs_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [← hZ]; exact hLop c (Zc c)
  set ρ : ℝ := 7 / 8 * δ
  set E : Site NF → Site NF → Site NF → ℝ := fun y' c c' =>
    (S.L : ℝ) ^ (2 * jj y) * Real.exp (-(ρ * S.dF y c)) * ((S.L : ℝ) ^ (4 * jj c))⁻¹ *
      (Real.exp (-(thetaB S N δ * S.dF c c')) * ((S.L : ℝ) ^ (4 * jj c'))⁻¹ * (S.L : ℝ) ^ (2 * jj y') *
        Real.exp (-(ρ * S.dF c' y')))
  have hE0 : ∀ y' c c', 0 ≤ E y' c c' := fun y' c c' => by positivity
  set K := A0 * εL * (2 / gammaB N) * B0
  have hK0 : 0 ≤ K := by positivity
  have hstep : hs (Lop (QpL S W (unblkL S ΩD u)) x) ≤
      ∑ c : BD S ΩD, ∑ c' : BD S ΩD, ∑ x', K * E (bc S.toDomSeq x') c.1 c'.1 * (εR x' * w x') := by
    rw [hP, Finset.sum_apply]
    refine (RegularAverages.hs_sum_le _ _).trans (sum_le_sum fun c _ => (hG c).trans ?_)
    have hA0' : 0 ≤ A0 * εL * (S.L : ℝ) ^ (2 * jj y) * Real.exp (-(7 / 8 * δ * S.dF y c.1)) *
        ((S.L : ℝ) ^ (4 * jj c.1))⁻¹ := by positivity
    calc A0 * εL * (S.L : ℝ) ^ (2 * jj y) * Real.exp (-(7 / 8 * δ * S.dF y c.1)) *
          (((S.L : ℝ) ^ (4 * jj c.1))⁻¹ * hs (proj (u.ofLp c)))
        = A0 * εL * (S.L : ℝ) ^ (2 * jj y) * Real.exp (-(7 / 8 * δ * S.dF y c.1)) *
          ((S.L : ℝ) ^ (4 * jj c.1))⁻¹ * hs (proj (u.ofLp c)) := by ring
      _ ≤ A0 * εL * (S.L : ℝ) ^ (2 * jj y) * Real.exp (-(7 / 8 * δ * S.dF y c.1)) *
          ((S.L : ℝ) ^ (4 * jj c.1))⁻¹ * ∑ c' : BD S ΩD, 2 / gammaB N *
            Real.exp (-(thetaB S N δ * S.dF c.1 c'.1)) * (((S.L : ℝ) ^ (4 * jj c'.1))⁻¹ * ∑ x', B0 * εR x' *
              (S.L : ℝ) ^ (2 * jj (bc S.toDomSeq x')) * Real.exp (-(7 / 8 * δ * S.dF (bc S.toDomSeq x') c'.1)) *
                w x') := by
          refine mul_le_mul_of_nonneg_left ((hu c).trans (sum_le_sum fun c' _ => ?_)) hA0'
          exact mul_le_mul_of_nonneg_left (hg c') (by positivity)
      _ = _ := by
          rw [mul_sum]
          refine sum_congr rfl fun c' _ => ?_
          rw [mul_sum, mul_sum, mul_sum]
          refine sum_congr rfl fun x' _ => ?_
          simp only [E, K, ρ]
          rw [S.dF_comm (bc S.toDomSeq x') c'.1]
          ring
  have hswap : ∑ c : BD S ΩD, ∑ c' : BD S ΩD, ∑ x', K * E (bc S.toDomSeq x') c.1 c'.1 * (εR x' * w x') =
      ∑ x', K * (εR x' * w x') * ∑ c : BD S ΩD, ∑ c' : BD S ΩD, E (bc S.toDomSeq x') c.1 c'.1 := by
    rw [sum_congr rfl fun c _ => Finset.sum_comm, Finset.sum_comm]
    refine sum_congr rfl fun x' _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun c _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun c' _ => ?_
    ring
  have hsum : ∀ x', ∑ c : BD S ΩD, ∑ c' : BD S ΩD, E (bc S.toDomSeq x') c.1 c'.1 ≤
      (S.L : ℝ) ^ (12 : ℝ) * (S.toContSeq).c1 (1 / 2) (thetaB S N δ) *
        (S.toContSeq).c1 (1 / 2) (7 / 16 * thetaB S N δ) * ((S.L : ℝ) ^ (4 * jj (bc S.toDomSeq x')))⁻¹ *
          Real.exp (-(7 / 32 * thetaB S N δ * S.dF y (bc S.toDomSeq x'))) := by
    intro x'
    refine le_trans ?_ (chainP S hθ (show 9 / 8 * thetaB S N δ ≤ 7 / 8 * δ by linarith) hRMθs hRMθc hy
      (y' := bc S.toDomSeq x'))
    refine (sum_le_sum fun c _ => sum_BD_le_detB S (fun c' => E (bc S.toDomSeq x') c.1 c')
      fun c' => hE0 _ _ _).trans ?_
    exact sum_BD_le_detB S (fun c => ∑ c' ∈ detB S.toDomSeq, E (bc S.toDomSeq x') c c')
      fun c => sum_nonneg fun c' _ => hE0 _ _ _
  rw [hswap] at hstep
  refine hstep.trans ?_
  rw [mul_sum]
  refine sum_le_sum fun x' _ => ?_
  have hwx := hw x'
  have hεx := hεR x'
  calc K * (εR x' * w x') * ∑ c : BD S ΩD, ∑ c' : BD S ΩD, E (bc S.toDomSeq x') c.1 c'.1
      ≤ K * (εR x' * w x') * ((S.L : ℝ) ^ (12 : ℝ) * (S.toContSeq).c1 (1 / 2) (thetaB S N δ) *
        (S.toContSeq).c1 (1 / 2) (7 / 16 * thetaB S N δ) * ((S.L : ℝ) ^ (4 * jj (bc S.toDomSeq x')))⁻¹ *
          Real.exp (-(7 / 32 * thetaB S N δ * S.dF y (bc S.toDomSeq x')))) :=
        mul_le_mul_of_nonneg_left (hsum x') (by positivity)
    _ = _ := by simp only [K]; ring

/-- The constant of the kernels of `∇P`, `P∇^*`, `∇P∇^*`. -/
def CPg (S : SeqDom) (N : ℕ) (δ α₁ : ℝ) : ℝ :=
  (2 * Real.sqrt N * (Cv S δ (Csc S N) (4 * N * (S.L : ℝ) ^ 4) + Cg S δ (Csc S N) (4 * N * (S.L : ℝ) ^ 4) α₁)) ^ 2 *
    (2 / gammaB N) * (S.L : ℝ) ^ (12 : ℝ) * (S.toContSeq).c1 (1 / 2) (thetaB S N δ) *
      (S.toContSeq).c1 (1 / 2) (7 / 16 * thetaB S N δ)

end ScalarHyp

namespace ScalarHyp

variable {S} {X : Fin 4 → Site (SequenceAverages.N0 S) → Matrix (Fin N) (Fin N) ℂ} {α₁ : ℝ}
  {W : Site (SequenceAverages.N0 S) → Site (SequenceAverages.N0 S) → (Matrix (Fin N) (Fin N) ℂ)ˣ} {η : ℝ}
  {ΩD : Set (Site (SequenceAverages.N0 S))} {δ : ℝ}
  (H : ScalarHyp S X α₁ W η ΩD δ)
include H

/-- The left factor `G'`: `|(G'λ_Z)(x)| ≤ 2√NC_va_y²e^{-(7/8)δd(y, c)}|Z|`. -/
lemma left_G [NeZero N] (x : Site NF) (c : BD S ΩD) (Z : Mat) :
    hs (Gp' S.toDomSeq (cfgX X) W ΩD (lamZ S W c.1 Z) x) ≤
      2 * Real.sqrt N * Cv S δ (Csc S N) (4 * N * (S.L : ℝ) ^ 4) * 1 * (S.L : ℝ) ^ (2 * jj (bc S.toDomSeq x)) *
        Real.exp (-(7 / 8 * δ * S.dF (bc S.toDomSeq x) c.1)) * hs Z := by
  have hc := (BD_sub S ΩD) c.2
  have h := H.KB_Gp' (bc S.toDomSeq x) (bc_mem_detB S x) c.1 hc (lamZ S W c.1 Z) (2 * Real.sqrt N * hs Z)
    (by have := hs_nonneg (N := N) Z; positivity) (lamZ_supp S W hc _) (lamZ_bound S H.hW hc _) x (mem_blk_bc S x)
  simp only [zero_mul, pow_zero, mul_one] at h
  linarith

/-- The left factor `D_{𝐔,ν}G'`: `|(D_νG'λ_Z)(x)| ≤ 2√NC_ga_y^{-1}a_y²e^{-(7/8)δd(y, c)}|Z|`. -/
lemma left_DG [NeZero N] (ν : Fin 4) (x : Site NF) (c : BD S ΩD) (Z : Mat) :
    hs ((DfwL S (cfgX X) ν ∘ₗ Gp' S.toDomSeq (cfgX X) W ΩD) (lamZ S W c.1 Z) x) ≤
      2 * Real.sqrt N * Cg S δ (Csc S N) (4 * N * (S.L : ℝ) ^ 4) α₁ * ((S.L : ℝ) ^ jj (bc S.toDomSeq x))⁻¹ *
        (S.L : ℝ) ^ (2 * jj (bc S.toDomSeq x)) * Real.exp (-(7 / 8 * δ * S.dF (bc S.toDomSeq x) c.1)) * hs Z := by
  have hL : (0 : ℝ) < S.L := by exact_mod_cast S.Lpos
  have hc := (BD_sub S ΩD) c.2
  rw [LinearMap.comp_apply, DfwL_apply]
  have h := H.gradient (bc_mem_detB S x) hc (mem_blk_bc S x) (lam := lamZ S W c.1 Z) (Λ := 2 * Real.sqrt N * hs Z)
    (by have := hs_nonneg (N := N) Z; positivity) (lamZ_supp S W hc _) (lamZ_bound S H.hW hc _) ν
  have e : ((S.L : ℝ) ^ jj (bc S.toDomSeq x))⁻¹ * (S.L : ℝ) ^ (2 * jj (bc S.toDomSeq x)) =
      (S.L : ℝ) ^ jj (bc S.toDomSeq x) := by
    rw [two_mul, pow_add, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
  calc _ ≤ _ := h
    _ = 2 * Real.sqrt N * Cg S δ (Csc S N) (4 * N * (S.L : ℝ) ^ 4) α₁ *
        (((S.L : ℝ) ^ jj (bc S.toDomSeq x))⁻¹ * (S.L : ℝ) ^ (2 * jj (bc S.toDomSeq x))) *
        Real.exp (-(7 / 8 * δ * S.dF (bc S.toDomSeq x) c.1)) * hs Z := by rw [e]; ring
    _ = _ := by ring

/-- The right data `Q'G'D^*h` in the form of `Pgen`. -/
lemma right_QGs [NeZero N] (h : Fin 4 → Site NF → Mat) (c : BD S ΩD) :
    hs (avgL S W (Gp' S.toDomSeq (cfgX X) W ΩD (Ds1L a1 (cfgX X) h)) c.1) ≤
      ((S.L : ℝ) ^ (4 * jj c.1))⁻¹ * ∑ x', 2 * Real.sqrt N * Cg S δ (Csc S N) (4 * N * (S.L : ℝ) ^ 4) α₁ *
        ((S.L : ℝ) ^ jj (bc S.toDomSeq x'))⁻¹ * (S.L : ℝ) ^ (2 * jj (bc S.toDomSeq x')) *
          Real.exp (-(7 / 8 * δ * S.dF (bc S.toDomSeq x') c.1)) * ∑ ν : Fin 4, hs (h ν x') := by
  have hL : (0 : ℝ) < S.L := by exact_mod_cast S.Lpos
  refine (H.QGs_bound ((BD_sub S ΩD) c.2) h).trans (le_of_eq ?_)
  congr 1
  refine sum_congr rfl fun x' _ => ?_
  have e : ((S.L : ℝ) ^ jj (bc S.toDomSeq x'))⁻¹ * (S.L : ℝ) ^ (2 * jj (bc S.toDomSeq x')) =
      (S.L : ℝ) ^ jj (bc S.toDomSeq x') := by
    rw [two_mul, pow_add, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
  rw [mul_assoc (2 * Real.sqrt N * _) _ ((S.L : ℝ) ^ (2 * jj (bc S.toDomSeq x'))), e]

lemma right_QG [NeZero N] (f : Site NF → Mat) (c : BD S ΩD) :
    hs (avgL S W (Gp' S.toDomSeq (cfgX X) W ΩD f) c.1) ≤
      ((S.L : ℝ) ^ (4 * jj c.1))⁻¹ * ∑ x', 2 * Real.sqrt N * Cv S δ (Csc S N) (4 * N * (S.L : ℝ) ^ 4) * 1 *
        (S.L : ℝ) ^ (2 * jj (bc S.toDomSeq x')) * Real.exp (-(7 / 8 * δ * S.dF (bc S.toDomSeq x') c.1)) * hs (f x') := by
  simp only [mul_one]; exact H.QG_bound ((BD_sub S ΩD) c.2) f

lemma AB_le [NeZero N] {A B : ℝ} (hA : A = 2 * Real.sqrt N * Cv S δ (Csc S N) (4 * N * (S.L : ℝ) ^ 4) ∨
      A = 2 * Real.sqrt N * Cg S δ (Csc S N) (4 * N * (S.L : ℝ) ^ 4) α₁)
    (hB : B = 2 * Real.sqrt N * Cv S δ (Csc S N) (4 * N * (S.L : ℝ) ^ 4) ∨
      B = 2 * Real.sqrt N * Cg S δ (Csc S N) (4 * N * (S.L : ℝ) ^ 4) α₁) :
    A * B ≤ (2 * Real.sqrt N * (Cv S δ (Csc S N) (4 * N * (S.L : ℝ) ^ 4) +
      Cg S δ (Csc S N) (4 * N * (S.L : ℝ) ^ 4) α₁)) ^ 2 := by
  have hv := H.Cv_nn; have hg := H.Cg_nn'
  have hN := Real.sqrt_nonneg (N : ℝ)
  have hA0 : 0 ≤ A ∧ A ≤ 2 * Real.sqrt N * (Cv S δ (Csc S N) (4 * N * (S.L : ℝ) ^ 4) +
      Cg S δ (Csc S N) (4 * N * (S.L : ℝ) ^ 4) α₁) := by
    rcases hA with rfl | rfl <;> constructor <;> nlinarith
  have hB0 : 0 ≤ B ∧ B ≤ 2 * Real.sqrt N * (Cv S δ (Csc S N) (4 * N * (S.L : ℝ) ^ 4) +
      Cg S δ (Csc S N) (4 * N * (S.L : ℝ) ^ 4) α₁) := by
    rcases hB with rfl | rfl <;> constructor <;> nlinarith
  rw [sq]; exact mul_le_mul hA0.2 hB0.2 hB0.1 (hA0.1.trans hA0.2)

/-- **The kernel of `∇P`**: `|(D_νPf)(x)| ≤ C_Pa_y^{-1}Σ_{x'}a_{y(x')}^{-4}e^{-(7/32)θ_Bd(y, y(x'))}|f(x')|`, `y = y(x)`. -/
theorem gradP_bound [NeZero N]
    (hRMb : (S.toContSeq).r1 (1 / 2) (1 / 32 * δ) ≤ RMS) (hRMs4 : 32 * Real.log S.L / (1 / 4 * δ) ≤ RMS)
    (hsmallT : CTd S N δ α₁ η * (S.toContSeq).c1 (1 / 2) (1 / 32 * δ) ≤ gammaB N / 4)
    (hRMθs : 32 * Real.log S.L / (thetaB S N δ / 2) ≤ RMS)
    (hRMθc : (S.toContSeq).r1 (1 / 2) (7 / 16 * thetaB S N δ) ≤ RMS) (ν : Fin 4) (f : Site NF → Mat) (x : Site NF) :
    hs (Dfw 1 (cfgX X) ν (Pop S X W ΩD f) x) ≤ CPg S N δ α₁ * ((S.L : ℝ) ^ jj (bc S.toDomSeq x))⁻¹ *
      ∑ x', ((S.L : ℝ) ^ (4 * jj (bc S.toDomSeq x')))⁻¹ *
        Real.exp (-(7 / 32 * thetaB S N δ * S.dF (bc S.toDomSeq x) (bc S.toDomSeq x'))) * hs (f x') := by
  have hL : (0 : ℝ) < S.L := by exact_mod_cast S.Lpos
  have hγ : 0 < gammaB N := by unfold gammaB; positivity
  have hθ := H.thetaB_pos (N := N)
  have hc1 : 0 ≤ (S.toContSeq).c1 (1 / 2) (thetaB S N δ) := by unfold Summation.ContSeq.c1; positivity
  have hc2 : 0 ≤ (S.toContSeq).c1 (1 / 2) (7 / 16 * thetaB S N δ) := by unfold Summation.ContSeq.c1; positivity
  have hv := H.Cv_nn; have hg := H.Cg_nn'
  have e : Dfw 1 (cfgX X) ν (Pop S X W ΩD f) x = (DfwL S (cfgX X) ν ∘ₗ Gp' S.toDomSeq (cfgX X) W ΩD)
      (QpL S W (unblkL S ΩD (Tinv S X W ΩD (blkL S ΩD (avgL S W (Gp' S.toDomSeq (cfgX X) W ΩD f)))))) x := by
    rw [LinearMap.comp_apply, DfwL_apply]; rfl
  rw [e]
  have h := H.Pgen hRMb hRMs4 hsmallT hRMθs hRMθc _ (bc_mem_detB S x) (by positivity) (by positivity)
    (H.left_DG ν x) _ (fun x' => hs (f x')) (fun _ => 1) (fun x' => hs_nonneg _) (fun _ => zero_le_one)
    (by positivity) (H.right_QG f)
  simp only [one_mul] at h
  refine h.trans ?_
  have hS : 0 ≤ ∑ x', ((S.L : ℝ) ^ (4 * jj (bc S.toDomSeq x')))⁻¹ *
      Real.exp (-(7 / 32 * thetaB S N δ * S.dF (bc S.toDomSeq x) (bc S.toDomSeq x'))) * hs (f x') :=
    sum_nonneg fun x' _ => by have := hs_nonneg (N := N) (f x'); positivity
  have hAB := H.AB_le (Or.inr rfl) (Or.inl rfl)
  calc _ = (2 * Real.sqrt N * Cg S δ (Csc S N) (4 * N * (S.L : ℝ) ^ 4) α₁ *
        (2 * Real.sqrt N * Cv S δ (Csc S N) (4 * N * (S.L : ℝ) ^ 4))) *
        ((2 / gammaB N) * (S.L : ℝ) ^ (12 : ℝ) * (S.toContSeq).c1 (1 / 2) (thetaB S N δ) *
          (S.toContSeq).c1 (1 / 2) (7 / 16 * thetaB S N δ) * ((S.L : ℝ) ^ jj (bc S.toDomSeq x))⁻¹ *
          ∑ x', ((S.L : ℝ) ^ (4 * jj (bc S.toDomSeq x')))⁻¹ *
            Real.exp (-(7 / 32 * thetaB S N δ * S.dF (bc S.toDomSeq x) (bc S.toDomSeq x'))) * hs (f x')) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hAB (by positivity)
    _ = _ := by unfold CPg; ring

/-- **The kernel of `P∇^*`**: `|(PD^*_𝐔h)(x)| ≤ C_PΣ_{x'}a_{y(x')}^{-1}a_{y(x')}^{-4}e^{-(7/32)θ_Bd}Σ_ν|h_ν(x')|`. -/
theorem PDs_bound [NeZero N]
    (hRMb : (S.toContSeq).r1 (1 / 2) (1 / 32 * δ) ≤ RMS) (hRMs4 : 32 * Real.log S.L / (1 / 4 * δ) ≤ RMS)
    (hsmallT : CTd S N δ α₁ η * (S.toContSeq).c1 (1 / 2) (1 / 32 * δ) ≤ gammaB N / 4)
    (hRMθs : 32 * Real.log S.L / (thetaB S N δ / 2) ≤ RMS)
    (hRMθc : (S.toContSeq).r1 (1 / 2) (7 / 16 * thetaB S N δ) ≤ RMS) (h : Fin 4 → Site NF → Mat) (x : Site NF) :
    hs (Pop S X W ΩD (Ds1L a1 (cfgX X) h) x) ≤ CPg S N δ α₁ *
      ∑ x', ((S.L : ℝ) ^ jj (bc S.toDomSeq x'))⁻¹ * ((S.L : ℝ) ^ (4 * jj (bc S.toDomSeq x')))⁻¹ *
        Real.exp (-(7 / 32 * thetaB S N δ * S.dF (bc S.toDomSeq x) (bc S.toDomSeq x'))) *
          ∑ ν : Fin 4, hs (h ν x') := by
  have hL : (0 : ℝ) < S.L := by exact_mod_cast S.Lpos
  have hγ : 0 < gammaB N := by unfold gammaB; positivity
  have hθ := H.thetaB_pos (N := N)
  have hc1 : 0 ≤ (S.toContSeq).c1 (1 / 2) (thetaB S N δ) := by unfold Summation.ContSeq.c1; positivity
  have hc2 : 0 ≤ (S.toContSeq).c1 (1 / 2) (7 / 16 * thetaB S N δ) := by unfold Summation.ContSeq.c1; positivity
  have hv := H.Cv_nn; have hg := H.Cg_nn'
  have hw : ∀ x', 0 ≤ ∑ ν : Fin 4, hs (h ν x') := fun x' => sum_nonneg fun ν _ => hs_nonneg _
  have hP := H.Pgen hRMb hRMs4 hsmallT hRMθs hRMθc (Gp' S.toDomSeq (cfgX X) W ΩD) (bc_mem_detB S x)
    (by positivity) zero_le_one (H.left_G x) _ (fun x' => ∑ ν : Fin 4, hs (h ν x'))
    (fun x' => ((S.L : ℝ) ^ jj (bc S.toDomSeq x'))⁻¹) hw (fun x' => by positivity) (by positivity)
    (H.right_QGs h)
  refine hP.trans ?_
  have hS : 0 ≤ ∑ x', ((S.L : ℝ) ^ jj (bc S.toDomSeq x'))⁻¹ * ((S.L : ℝ) ^ (4 * jj (bc S.toDomSeq x')))⁻¹ *
      Real.exp (-(7 / 32 * thetaB S N δ * S.dF (bc S.toDomSeq x) (bc S.toDomSeq x'))) * ∑ ν : Fin 4, hs (h ν x') :=
    sum_nonneg fun x' _ => by have := hw x'; positivity
  have hAB := H.AB_le (Or.inl rfl) (Or.inr rfl)
  calc _ = (2 * Real.sqrt N * Cv S δ (Csc S N) (4 * N * (S.L : ℝ) ^ 4) *
        (2 * Real.sqrt N * Cg S δ (Csc S N) (4 * N * (S.L : ℝ) ^ 4) α₁)) *
        ((2 / gammaB N) * (S.L : ℝ) ^ (12 : ℝ) * (S.toContSeq).c1 (1 / 2) (thetaB S N δ) *
          (S.toContSeq).c1 (1 / 2) (7 / 16 * thetaB S N δ) *
          ∑ x', ((S.L : ℝ) ^ jj (bc S.toDomSeq x'))⁻¹ * ((S.L : ℝ) ^ (4 * jj (bc S.toDomSeq x')))⁻¹ *
            Real.exp (-(7 / 32 * thetaB S N δ * S.dF (bc S.toDomSeq x) (bc S.toDomSeq x'))) *
              ∑ ν : Fin 4, hs (h ν x')) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hAB (by positivity)
    _ = _ := by unfold CPg; ring

/-- **The kernel of `∇P∇^*`**: `|(D_νPD^*_𝐔h)(x)| ≤ C_Pa_y^{-1}Σ_{x'}a_{y(x')}^{-1}a_{y(x')}^{-4}e^{-(7/32)θ_Bd}Σ_μ|h_μ(x')|`. -/
theorem gradPDs_bound [NeZero N]
    (hRMb : (S.toContSeq).r1 (1 / 2) (1 / 32 * δ) ≤ RMS) (hRMs4 : 32 * Real.log S.L / (1 / 4 * δ) ≤ RMS)
    (hsmallT : CTd S N δ α₁ η * (S.toContSeq).c1 (1 / 2) (1 / 32 * δ) ≤ gammaB N / 4)
    (hRMθs : 32 * Real.log S.L / (thetaB S N δ / 2) ≤ RMS)
    (hRMθc : (S.toContSeq).r1 (1 / 2) (7 / 16 * thetaB S N δ) ≤ RMS) (ν : Fin 4) (h : Fin 4 → Site NF → Mat)
    (x : Site NF) :
    hs (Dfw 1 (cfgX X) ν (Pop S X W ΩD (Ds1L a1 (cfgX X) h)) x) ≤ CPg S N δ α₁ *
      ((S.L : ℝ) ^ jj (bc S.toDomSeq x))⁻¹ *
      ∑ x', ((S.L : ℝ) ^ jj (bc S.toDomSeq x'))⁻¹ * ((S.L : ℝ) ^ (4 * jj (bc S.toDomSeq x')))⁻¹ *
        Real.exp (-(7 / 32 * thetaB S N δ * S.dF (bc S.toDomSeq x) (bc S.toDomSeq x'))) *
          ∑ μ : Fin 4, hs (h μ x') := by
  have hL : (0 : ℝ) < S.L := by exact_mod_cast S.Lpos
  have hγ : 0 < gammaB N := by unfold gammaB; positivity
  have hθ := H.thetaB_pos (N := N)
  have hc1 : 0 ≤ (S.toContSeq).c1 (1 / 2) (thetaB S N δ) := by unfold Summation.ContSeq.c1; positivity
  have hc2 : 0 ≤ (S.toContSeq).c1 (1 / 2) (7 / 16 * thetaB S N δ) := by unfold Summation.ContSeq.c1; positivity
  have hv := H.Cv_nn; have hg := H.Cg_nn'
  have hw : ∀ x', 0 ≤ ∑ μ : Fin 4, hs (h μ x') := fun x' => sum_nonneg fun μ _ => hs_nonneg _
  have e : Dfw 1 (cfgX X) ν (Pop S X W ΩD (Ds1L a1 (cfgX X) h)) x =
      (DfwL S (cfgX X) ν ∘ₗ Gp' S.toDomSeq (cfgX X) W ΩD) (QpL S W (unblkL S ΩD (Tinv S X W ΩD (blkL S ΩD
        (avgL S W (Gp' S.toDomSeq (cfgX X) W ΩD (Ds1L a1 (cfgX X) h))))))) x := by
    rw [LinearMap.comp_apply, DfwL_apply]; rfl
  rw [e]
  have hP := H.Pgen hRMb hRMs4 hsmallT hRMθs hRMθc _ (bc_mem_detB S x) (by positivity) (by positivity)
    (H.left_DG ν x) _ (fun x' => ∑ μ : Fin 4, hs (h μ x'))
    (fun x' => ((S.L : ℝ) ^ jj (bc S.toDomSeq x'))⁻¹) hw (fun x' => by positivity) (by positivity)
    (H.right_QGs h)
  refine hP.trans ?_
  have hS : 0 ≤ ∑ x', ((S.L : ℝ) ^ jj (bc S.toDomSeq x'))⁻¹ * ((S.L : ℝ) ^ (4 * jj (bc S.toDomSeq x')))⁻¹ *
      Real.exp (-(7 / 32 * thetaB S N δ * S.dF (bc S.toDomSeq x) (bc S.toDomSeq x'))) * ∑ μ : Fin 4, hs (h μ x') :=
    sum_nonneg fun x' _ => by have := hw x'; positivity
  have hAB := H.AB_le (Or.inr rfl) (Or.inr rfl)
  calc _ = (2 * Real.sqrt N * Cg S δ (Csc S N) (4 * N * (S.L : ℝ) ^ 4) α₁ *
        (2 * Real.sqrt N * Cg S δ (Csc S N) (4 * N * (S.L : ℝ) ^ 4) α₁)) *
        ((2 / gammaB N) * (S.L : ℝ) ^ (12 : ℝ) * (S.toContSeq).c1 (1 / 2) (thetaB S N δ) *
          (S.toContSeq).c1 (1 / 2) (7 / 16 * thetaB S N δ) * ((S.L : ℝ) ^ jj (bc S.toDomSeq x))⁻¹ *
          ∑ x', ((S.L : ℝ) ^ jj (bc S.toDomSeq x'))⁻¹ * ((S.L : ℝ) ^ (4 * jj (bc S.toDomSeq x')))⁻¹ *
            Real.exp (-(7 / 32 * thetaB S N δ * S.dF (bc S.toDomSeq x) (bc S.toDomSeq x'))) *
              ∑ μ : Fin 4, hs (h μ x')) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hAB (by positivity)
    _ = _ := by unfold CPg; ring

end ScalarHyp

end SFBounds
end CoreLean

end
