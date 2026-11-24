/-
`lem:sf-vector-decay` of BALABAN_CORE.tex (`ff7468ef0e33`), step (3) of "The complex field": the kernel of
`P(𝐔) - P(id)` on the fine lattice (`a₀ = 1`), by the resolvent identities of `SFDiff` and `SFBlockDiff` in place of
the lemma of Schwarz.

* `ScalarHyp.PgenR`: `Pgen` with a general outer rate `ρ ≥ (9/8)θ_B` (for the differences, whose rates are smaller
  than `(7/8)δ`).
-/
import CoreLean.SFVectorDecay

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

namespace ScalarHyp

variable {S} {X : Fin 4 → Site (SequenceAverages.N0 S) → Matrix (Fin N) (Fin N) ℂ} {α₁ : ℝ}
  {W : Site (SequenceAverages.N0 S) → Site (SequenceAverages.N0 S) → (Matrix (Fin N) (Fin N) ℂ)ˣ} {η : ℝ}
  {ΩD : Set (Site (SequenceAverages.N0 S))} {δ : ℝ}
  (H : ScalarHyp S X α₁ W η ΩD δ)
include H

/-- **The general kernel bound with a general rate `ρ ≥ (9/8)θ_B`** (as `Pgen`, whose rate is `(7/8)δ`) behind `P`, `∇P`, `P∇^*`, `∇P∇^*`: a left operator bounded on the `λ_Z` like `G'`,
composed with `Q'^*T⁻¹`, applied to data `g` bounded on `𝐁_D` like `Q'G'f`. -/
theorem PgenR [NeZero N]
    (hRMb : (S.toContSeq).r1 (1 / 2) (1 / 32 * δ) ≤ RMS) (hRMs4 : 32 * Real.log S.L / (1 / 4 * δ) ≤ RMS)
    (hsmallT : CTd S N δ α₁ η * (S.toContSeq).c1 (1 / 2) (1 / 32 * δ) ≤ gammaB N / 4)
    (hRMθs : 32 * Real.log S.L / (thetaB S N δ / 2) ≤ RMS)
    (hRMθc : (S.toContSeq).r1 (1 / 2) (7 / 16 * thetaB S N δ) ≤ RMS)
    {ρ : ℝ} (hρ : 9 / 8 * thetaB S N δ ≤ ρ)
    (Lop : Module.End ℂ (Site NF → Mat)) {y x : Site NF} (hy : y ∈ detB S.toDomSeq) {A0 εL : ℝ}
    (hA0 : 0 ≤ A0) (hεL : 0 ≤ εL)
    (hLop : ∀ (c : BD S ΩD) (Z : Mat), hs (Lop (lamZ S W c.1 Z) x) ≤
      A0 * εL * (S.L : ℝ) ^ (2 * jj y) * Real.exp (-(ρ * S.dF y c.1)) * hs Z)
    (g : Site NF → Mat) (w εR : Site NF → ℝ) (hw : ∀ x', 0 ≤ w x') (hεR : ∀ x', 0 ≤ εR x') {B0 : ℝ} (hB0 : 0 ≤ B0)
    (hg : ∀ c : BD S ΩD, hs (g c.1) ≤ ((S.L : ℝ) ^ (4 * jj c.1))⁻¹ * ∑ x', B0 * εR x' *
      (S.L : ℝ) ^ (2 * jj (bc S.toDomSeq x')) * Real.exp (-(ρ * S.dF (bc S.toDomSeq x') c.1)) * w x') :
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
      A0 * εL * (S.L : ℝ) ^ (2 * jj y) * Real.exp (-(ρ * S.dF y c.1)) *
        (((S.L : ℝ) ^ (4 * jj c.1))⁻¹ * hs (proj (u.ofLp c))) := by
    intro c
    have hZ : hs (Zc c) = ((S.L : ℝ) ^ (4 * jj c.1))⁻¹ * hs (proj (u.ofLp c)) := by
      simp only [Zc]
      rw [RegularAverages.hs_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [← hZ]; exact hLop c (Zc c)
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
    have hA0' : 0 ≤ A0 * εL * (S.L : ℝ) ^ (2 * jj y) * Real.exp (-(ρ * S.dF y c.1)) *
        ((S.L : ℝ) ^ (4 * jj c.1))⁻¹ := by positivity
    calc A0 * εL * (S.L : ℝ) ^ (2 * jj y) * Real.exp (-(ρ * S.dF y c.1)) *
          (((S.L : ℝ) ^ (4 * jj c.1))⁻¹ * hs (proj (u.ofLp c)))
        = A0 * εL * (S.L : ℝ) ^ (2 * jj y) * Real.exp (-(ρ * S.dF y c.1)) *
          ((S.L : ℝ) ^ (4 * jj c.1))⁻¹ * hs (proj (u.ofLp c)) := by ring
      _ ≤ A0 * εL * (S.L : ℝ) ^ (2 * jj y) * Real.exp (-(ρ * S.dF y c.1)) *
          ((S.L : ℝ) ^ (4 * jj c.1))⁻¹ * ∑ c' : BD S ΩD, 2 / gammaB N *
            Real.exp (-(thetaB S N δ * S.dF c.1 c'.1)) * (((S.L : ℝ) ^ (4 * jj c'.1))⁻¹ * ∑ x', B0 * εR x' *
              (S.L : ℝ) ^ (2 * jj (bc S.toDomSeq x')) * Real.exp (-(ρ * S.dF (bc S.toDomSeq x') c'.1)) *
                w x') := by
          refine mul_le_mul_of_nonneg_left ((hu c).trans (sum_le_sum fun c' _ => ?_)) hA0'
          exact mul_le_mul_of_nonneg_left (hg c') (by positivity)
      _ = _ := by
          rw [mul_sum]
          refine sum_congr rfl fun c' _ => ?_
          rw [mul_sum, mul_sum, mul_sum]
          refine sum_congr rfl fun x' _ => ?_
          simp only [E, K]
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
    refine le_trans ?_ (chainP S hθ hρ hRMθs hRMθc hy
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


/-- The constant of the first term of `P(𝐔) - P(id)`. -/
def CPdA (S : SeqDom) (N : ℕ) (δ α₁ η : ℝ) : ℝ :=
  2 * Real.sqrt N * CD S N δ α₁ η * (2 * Real.sqrt N * Cv S δ (Csc S N) (4 * N * (S.L : ℝ) ^ 4)) * (2 / gammaB N) *
    (S.L : ℝ) ^ (12 : ℝ) * (S.toContSeq).c1 (1 / 2) (thetaB S N δ) * (S.toContSeq).c1 (1 / 2) (7 / 16 * thetaB S N δ)

/-- **The first term of `P(𝐔) - P(id)`**: `(G'_𝐔 - G'_id)Q'^*T_𝐔⁻¹Q'G'_𝐔` has the kernel
`C_{PdA}a_{y(x')}^{-4}e^{-(7/32)θ_Bd}` (`diff_KB` at the rate `δ/4` and `PgenR`). -/
theorem PdiffA [NeZero N]
    (hRMb : (S.toContSeq).r1 (1 / 2) (1 / 32 * δ) ≤ RMS) (hRMs4 : 32 * Real.log S.L / (1 / 4 * δ) ≤ RMS)
    (hsmallT : CTd S N δ α₁ η * (S.toContSeq).c1 (1 / 2) (1 / 32 * δ) ≤ gammaB N / 4)
    (hRMθs : 32 * Real.log S.L / (thetaB S N δ / 2) ≤ RMS)
    (hRMθc : (S.toContSeq).r1 (1 / 2) (7 / 16 * thetaB S N δ) ≤ RMS)
    (hRMc : (S.toContSeq).r1 (1 / 2) (3 / 4 * δ) ≤ RMS) (f : Site NF → Mat) (x : Site NF) :
    hs ((Gp' S.toDomSeq (cfgX X) W ΩD - Gp' S.toDomSeq (cfgX (X0 S)) (W1 S) ΩD : Module.End ℂ (Site NF → Mat))
        (QpL S W (unblkL S ΩD (Tinv S X W ΩD (blkL S ΩD (avgL S W (Gp' S.toDomSeq (cfgX X) W ΩD f)))))) x) ≤
      CPdA S N δ α₁ η * ∑ x', ((S.L : ℝ) ^ (4 * jj (bc S.toDomSeq x')))⁻¹ *
        Real.exp (-(7 / 32 * thetaB S N δ * S.dF (bc S.toDomSeq x) (bc S.toDomSeq x'))) * hs (f x') := by
  have hδ := H.hδ0
  have hθ := H.thetaB_pos (N := N)
  have hθle : thetaB S N δ ≤ 1 / 64 * δ := min_le_left _ _
  have hCv := H.Cv_nn
  have hCD := H.CD_nn
  have hN : (0 : ℝ) ≤ Real.sqrt N := Real.sqrt_nonneg _
  set y := bc S.toDomSeq x
  have hy : y ∈ detB S.toDomSeq := bc_mem_detB S x
  have hLop : ∀ (c : BD S ΩD) (Z : Mat),
      hs ((Gp' S.toDomSeq (cfgX X) W ΩD - Gp' S.toDomSeq (cfgX (X0 S)) (W1 S) ΩD : Module.End ℂ (Site NF → Mat)) (lamZ S W c.1 Z) x) ≤
        (2 * Real.sqrt N * CD S N δ α₁ η) * 1 * (S.L : ℝ) ^ (2 * jj y) * Real.exp (-(1 / 4 * δ * S.dF y c.1)) * hs Z := by
    intro c Z
    have hc := (BD_sub S ΩD) c.2
    have h := H.diff_KB hRMc y hy c.1 hc (lamZ S W c.1 Z) (2 * Real.sqrt N * hs Z)
      (by have := hs_nonneg (N := N) Z; positivity) (lamZ_supp S W hc _) (lamZ_bound S H.hW hc _) x (mem_blk_bc S x)
    simp only [zero_mul, pow_zero, mul_one] at h
    refine h.trans (le_of_eq ?_)
    ring
  have hg : ∀ c : BD S ΩD, hs (avgL S W (Gp' S.toDomSeq (cfgX X) W ΩD f) c.1) ≤
      ((S.L : ℝ) ^ (4 * jj c.1))⁻¹ * ∑ x', (2 * Real.sqrt N * Cv S δ (Csc S N) (4 * N * (S.L : ℝ) ^ 4)) * 1 *
        (S.L : ℝ) ^ (2 * jj (bc S.toDomSeq x')) * Real.exp (-(1 / 4 * δ * S.dF (bc S.toDomSeq x') c.1)) *
          hs (f x') := by
    intro c
    refine (H.QG_bound ((BD_sub S ΩD) c.2) f).trans ?_
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x' _ => ?_) (by positivity)
    have he : Real.exp (-(7 / 8 * δ * S.dF (bc S.toDomSeq x') c.1)) ≤
        Real.exp (-(1 / 4 * δ * S.dF (bc S.toDomSeq x') c.1)) := by
      apply Real.exp_le_exp.2
      have := S.dF_nonneg (bc S.toDomSeq x') c.1
      nlinarith
    have := hs_nonneg (f x')
    have h0 : 0 ≤ 2 * Real.sqrt N * Cv S δ (Csc S N) (4 * N * (S.L : ℝ) ^ 4) * (S.L : ℝ) ^ (2 * jj (bc S.toDomSeq x')) :=
      by positivity
    calc 2 * Real.sqrt N * Cv S δ (Csc S N) (4 * N * (S.L : ℝ) ^ 4) * (S.L : ℝ) ^ (2 * jj (bc S.toDomSeq x')) *
          Real.exp (-(7 / 8 * δ * S.dF (bc S.toDomSeq x') c.1)) * hs (f x')
        ≤ 2 * Real.sqrt N * Cv S δ (Csc S N) (4 * N * (S.L : ℝ) ^ 4) * (S.L : ℝ) ^ (2 * jj (bc S.toDomSeq x')) *
          Real.exp (-(1 / 4 * δ * S.dF (bc S.toDomSeq x') c.1)) * hs (f x') := by gcongr
      _ = _ := by ring
  have h := H.PgenR hRMb hRMs4 hsmallT hRMθs hRMθc (ρ := 1 / 4 * δ) (by linarith)
    (Gp' S.toDomSeq (cfgX X) W ΩD - Gp' S.toDomSeq (cfgX (X0 S)) (W1 S) ΩD) hy (by positivity) (by norm_num) hLop
    (avgL S W (Gp' S.toDomSeq (cfgX X) W ΩD f)) (fun x' => hs (f x')) (fun _ => 1) (fun x' => hs_nonneg _)
    (fun _ => zero_le_one) (by positivity) hg
  refine h.trans (le_of_eq ?_)
  unfold CPdA
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x' _ => ?_
  ring

omit H in
/-- The trace identity of the averages: `a_y⁴tr(Z(Q'_Wg)(y)) = ⟨λ_Z, g⟩`. -/
lemma trace_avg (W' : Site NF → Site NF → GLN) {y : Site NF} (hy : y ∈ detB S.toDomSeq) (Z : Mat) (g : Site NF → Mat) :
    (((S.L : ℝ) ^ (4 * jj y) : ℝ) : ℂ) * ntr (Z * avgW S.toDomSeq W' y g) = P0 (lamZ S W' y Z) g := by
  rw [lamZ, ← avg_pair S W']
  rw [Finset.sum_eq_single y (fun y' _ hne => by rw [if_neg hne]; simp [ntr]) (fun h => absurd hy h), if_pos rfl]

omit H in
/-- **The kernel of `Q'_W` applied to `Bf`** from a kernel bound of `B` on the `λ_Z`: if
`|(Bλ)(x')| ≤ C a_{y(x')}²e^{-ρd(y(x'), y)}|Z|` for the `λ = Λ_y(Z)` of a family `Λ`, and
`a_y⁴tr(Z(Q'_WBf)(y)) = ⟨Bλ, f⟩`, then `|(Q'_WBf)(y)| ≤ a_y^{-4}Σ_{x'}Ca_{y(x')}²e^{-ρd}|f(x')|`. -/
lemma QG_gen {y : Site NF} (v : Mat) (F : Mat → Site NF → Mat) (f : Site NF → Mat) {C ρ : ℝ} (hC : 0 ≤ C)
    (htr : ∀ Z, (((S.L : ℝ) ^ (4 * jj y) : ℝ) : ℂ) * ntr (Z * v) = P0 (F Z) f)
    (hF : ∀ Z x', hs (F Z x') ≤ C * (S.L : ℝ) ^ (2 * jj (bc S.toDomSeq x')) *
      Real.exp (-(ρ * S.dF (bc S.toDomSeq x') y)) * hs Z) :
    hs v ≤ ((S.L : ℝ) ^ (4 * jj y))⁻¹ * ∑ x', C * (S.L : ℝ) ^ (2 * jj (bc S.toDomSeq x')) *
      Real.exp (-(ρ * S.dF (bc S.toDomSeq x') y)) * hs (f x') := by
  have hL : (0 : ℝ) < S.L := by exact_mod_cast S.Lpos
  set R := ∑ x', C * (S.L : ℝ) ^ (2 * jj (bc S.toDomSeq x')) * Real.exp (-(ρ * S.dF (bc S.toDomSeq x') y)) * hs (f x')
  have hR : 0 ≤ R := Finset.sum_nonneg fun x' _ => by have := hs_nonneg (N := N) (f x'); positivity
  have ha : (0 : ℝ) < (S.L : ℝ) ^ (4 * jj y) := by positivity
  have key : (S.L : ℝ) ^ (4 * jj y) * hs v ^ 2 ≤ hs v * R := by
    have h := htr vᴴ
    have hre : (S.L : ℝ) ^ (4 * jj y) * hs v ^ 2 = RCLike.re ((((S.L : ℝ) ^ (4 * jj y) : ℝ) : ℂ) * ntr (vᴴ * v)) := by
      rw [RCLike.re_to_complex, Complex.re_ofReal_mul, hs_sq]; rfl
    rw [hre, h]
    refine (RCLike.re_le_norm _).trans ((P0_abs_le S _ _).trans ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun x' _ => ?_
    have hf := hs_nonneg (N := N) (f x')
    have h2 := hF vᴴ x'
    rw [hs_conjTranspose] at h2
    calc hs (F vᴴ x') * hs (f x') ≤ C * (S.L : ℝ) ^ (2 * jj (bc S.toDomSeq x')) *
          Real.exp (-(ρ * S.dF (bc S.toDomSeq x') y)) * hs v * hs (f x') := mul_le_mul_of_nonneg_right h2 hf
      _ = _ := by ring
  rcases (hs_nonneg (N := N) v).eq_or_lt with h0 | hpos
  · rw [← h0]; exact mul_nonneg (inv_nonneg.2 ha.le) hR
  · rw [le_inv_mul_iff₀ ha]
    nlinarith

/-- **The data of the second term**: `|(Q'_W(G'_𝐔 - G'_id)f)(y)| ≤ a_y^{-4}Σ_{x'}2√NC_Da_{y(x')}²e^{-(δ/4)d}|f(x')|`. -/
lemma QG_diff [NeZero N] (hRMc : (S.toContSeq).r1 (1 / 2) (3 / 4 * δ) ≤ RMS) {y : Site NF}
    (hy : y ∈ detB S.toDomSeq) (f : Site NF → Mat) :
    hs (avgW S.toDomSeq W y ((Gp' S.toDomSeq (cfgX X) W ΩD - Gp' S.toDomSeq (cfgX (X0 S)) (W1 S) ΩD :
      Module.End ℂ (Site NF → Mat)) f)) ≤
      ((S.L : ℝ) ^ (4 * jj y))⁻¹ * ∑ x', (2 * Real.sqrt N * CD S N δ α₁ η) * (S.L : ℝ) ^ (2 * jj (bc S.toDomSeq x')) *
        Real.exp (-(1 / 4 * δ * S.dF (bc S.toDomSeq x') y)) * hs (f x') := by
  have hCD := H.CD_nn
  refine QG_gen _ (fun Z => (Gp' S.toDomSeq (cfgX X) W ΩD - Gp' S.toDomSeq (cfgX (X0 S)) (W1 S) ΩD :
    Module.End ℂ (Site NF → Mat)) (lamZ S W y Z)) f (by positivity) (fun Z => ?_) (fun Z x' => ?_)
  · rw [trace_avg W hy, LinearMap.sub_apply, LinearMap.sub_apply, map_sub, map_sub, LinearMap.sub_apply]
    rw [← Gp'_symm S.toDomSeq _ _ _ H.hK, ← Gp'_symm S.toDomSeq _ _ _ (hK_triv S ΩD)]
  · have h := H.diff_KB hRMc (bc S.toDomSeq x') (bc_mem_detB S x') y hy (lamZ S W y Z) (2 * Real.sqrt N * hs Z)
      (by have := hs_nonneg (N := N) Z; positivity) (lamZ_supp S W hy _) (lamZ_bound S H.hW hy _) x' (mem_blk_bc S x')
    simp only [zero_mul, pow_zero, mul_one] at h
    refine h.trans (le_of_eq ?_)
    ring

/-- **The data of the third term**: `|((Q'_W - Q'_id)G'_idf)(y)| ≤ a_y^{-4}Σ_{x'}2√NηC_va_{y(x')}²e^{-(7/8)δd}|f(x')|`. -/
lemma QG_avgdiff [NeZero N] {y : Site NF} (hy : y ∈ detB S.toDomSeq) (f : Site NF → Mat) :
    hs (avgW S.toDomSeq W y (Gp' S.toDomSeq (cfgX (X0 S)) (W1 S) ΩD f) -
        avgW S.toDomSeq (W1 S) y (Gp' S.toDomSeq (cfgX (X0 S)) (W1 S) ΩD f)) ≤
      ((S.L : ℝ) ^ (4 * jj y))⁻¹ * ∑ x', (2 * Real.sqrt N * η * Cv S δ (Csc S N) (4 * N * (S.L : ℝ) ^ 4)) *
        (S.L : ℝ) ^ (2 * jj (bc S.toDomSeq x')) * Real.exp (-(7 / 8 * δ * S.dF (bc S.toDomSeq x') y)) * hs (f x') := by
  have H0 := H.triv (N := N)
  have hCv := H.Cv_nn
  have hη := H.hη
  refine QG_gen _ (fun Z => Gp' S.toDomSeq (cfgX (X0 S)) (W1 S) ΩD (lamZ S W y Z - lamZ S (W1 S) y Z)) f
    (by positivity) (fun Z => ?_) (fun Z x' => ?_)
  · rw [Matrix.mul_sub, ntr_sub, mul_sub, trace_avg W hy, trace_avg (W1 S) hy, ← Gp'_symm S.toDomSeq _ _ _ (hK_triv S ΩD),
      ← Gp'_symm S.toDomSeq _ _ _ (hK_triv S ΩD), map_sub, LinearMap.map_sub₂]
  · have hd := lamZ_diff S hη H.hW1 H.hW hy Z
    have hsupp : ∀ x'', x'' ∉ Blk S.toDomSeq (jj y) y → (lamZ S W y Z - lamZ S (W1 S) y Z) x'' = 0 := fun x'' hx'' => by
      rw [Pi.sub_apply, lamZ_supp S W hy Z x'' hx'', lamZ_supp S (W1 S) hy Z x'' hx'', sub_zero]
    have h := H0.KB_Gp' (bc S.toDomSeq x') (bc_mem_detB S x') y hy (lamZ S W y Z - lamZ S (W1 S) y Z)
      (2 * Real.sqrt N * η * hs Z) (by have := hs_nonneg (N := N) Z; positivity) hsupp hd x' (mem_blk_bc S x')
    simp only [zero_mul, pow_zero, mul_one] at h
    refine h.trans (le_of_eq ?_)
    ring

omit H in
lemma exp_rate_le {a b d : ℝ} (hab : b ≤ a) (hd : 0 ≤ d) : Real.exp (-(a * d)) ≤ Real.exp (-(b * d)) :=
  Real.exp_le_exp.2 (by nlinarith)

/-- The left factor `G'_id` on the `λ_Z` of `W` (the kernel bound of `G'` at the trivial configuration, at the rate
`δ/4`). -/
lemma hLop_G0 [NeZero N] {x : Site NF} (c : BD S ΩD) (Z : Mat) :
    hs (Gp' S.toDomSeq (cfgX (X0 S)) (W1 S) ΩD (lamZ S W c.1 Z) x) ≤
      (2 * Real.sqrt N * Cv S δ (Csc S N) (4 * N * (S.L : ℝ) ^ 4)) * 1 * (S.L : ℝ) ^ (2 * jj (bc S.toDomSeq x)) *
        Real.exp (-(1 / 4 * δ * S.dF (bc S.toDomSeq x) c.1)) * hs Z := by
  have H0 := H.triv (N := N)
  have hc := (BD_sub S ΩD) c.2
  have hδ := H.hδ0
  have h := H0.KB_Gp' (bc S.toDomSeq x) (bc_mem_detB S x) c.1 hc (lamZ S W c.1 Z) (2 * Real.sqrt N * hs Z)
    (by have := hs_nonneg (N := N) Z; positivity) (lamZ_supp S W hc _) (lamZ_bound S H.hW hc _) x (mem_blk_bc S x)
  simp only [zero_mul, pow_zero, mul_one] at h
  refine h.trans ?_
  have he := exp_rate_le (show 1 / 4 * δ ≤ 7 / 8 * δ by linarith) (S.dF_nonneg (bc S.toDomSeq x) c.1)
  have hCv := H.Cv_nn
  have h0 : 0 ≤ Cv S δ (Csc S N) (4 * N * (S.L : ℝ) ^ 4) * (S.L : ℝ) ^ (2 * jj (bc S.toDomSeq x)) *
      (2 * Real.sqrt N * hs Z) := by have := hs_nonneg (N := N) Z; positivity
  calc Cv S δ (Csc S N) (4 * N * (S.L : ℝ) ^ 4) * (S.L : ℝ) ^ (2 * jj (bc S.toDomSeq x)) *
        Real.exp (-(7 / 8 * δ * S.dF (bc S.toDomSeq x) c.1)) * (2 * Real.sqrt N * hs Z)
      = Cv S δ (Csc S N) (4 * N * (S.L : ℝ) ^ 4) * (S.L : ℝ) ^ (2 * jj (bc S.toDomSeq x)) * (2 * Real.sqrt N * hs Z) *
          Real.exp (-(7 / 8 * δ * S.dF (bc S.toDomSeq x) c.1)) := by ring
    _ ≤ Cv S δ (Csc S N) (4 * N * (S.L : ℝ) ^ 4) * (S.L : ℝ) ^ (2 * jj (bc S.toDomSeq x)) * (2 * Real.sqrt N * hs Z) *
          Real.exp (-(1 / 4 * δ * S.dF (bc S.toDomSeq x) c.1)) := mul_le_mul_of_nonneg_left he h0
    _ = _ := by ring

/-- The constants of the second and third terms of `P(𝐔) - P(id)`. -/
def CPdB1 (S : SeqDom) (N : ℕ) (δ α₁ η : ℝ) : ℝ :=
  2 * Real.sqrt N * Cv S δ (Csc S N) (4 * N * (S.L : ℝ) ^ 4) * (2 * Real.sqrt N * CD S N δ α₁ η) * (2 / gammaB N) *
    (S.L : ℝ) ^ (12 : ℝ) * (S.toContSeq).c1 (1 / 2) (thetaB S N δ) * (S.toContSeq).c1 (1 / 2) (7 / 16 * thetaB S N δ)

def CPdB2 (S : SeqDom) (N : ℕ) (δ η : ℝ) : ℝ :=
  2 * Real.sqrt N * Cv S δ (Csc S N) (4 * N * (S.L : ℝ) ^ 4) *
    (2 * Real.sqrt N * η * Cv S δ (Csc S N) (4 * N * (S.L : ℝ) ^ 4)) * (2 / gammaB N) *
    (S.L : ℝ) ^ (12 : ℝ) * (S.toContSeq).c1 (1 / 2) (thetaB S N δ) * (S.toContSeq).c1 (1 / 2) (7 / 16 * thetaB S N δ)

/-- **The second term of `P(𝐔) - P(id)`**: `G'_idQ'^*T_𝐔⁻¹Q'(G'_𝐔 - G'_id)`. -/
theorem PdiffB1 [NeZero N]
    (hRMb : (S.toContSeq).r1 (1 / 2) (1 / 32 * δ) ≤ RMS) (hRMs4 : 32 * Real.log S.L / (1 / 4 * δ) ≤ RMS)
    (hsmallT : CTd S N δ α₁ η * (S.toContSeq).c1 (1 / 2) (1 / 32 * δ) ≤ gammaB N / 4)
    (hRMθs : 32 * Real.log S.L / (thetaB S N δ / 2) ≤ RMS)
    (hRMθc : (S.toContSeq).r1 (1 / 2) (7 / 16 * thetaB S N δ) ≤ RMS)
    (hRMc : (S.toContSeq).r1 (1 / 2) (3 / 4 * δ) ≤ RMS) (f : Site NF → Mat) (x : Site NF) :
    hs (Gp' S.toDomSeq (cfgX (X0 S)) (W1 S) ΩD (QpL S W (unblkL S ΩD (Tinv S X W ΩD (blkL S ΩD (avgL S W
        ((Gp' S.toDomSeq (cfgX X) W ΩD - Gp' S.toDomSeq (cfgX (X0 S)) (W1 S) ΩD : Module.End ℂ (Site NF → Mat)) f)))))) x) ≤
      CPdB1 S N δ α₁ η * ∑ x', ((S.L : ℝ) ^ (4 * jj (bc S.toDomSeq x')))⁻¹ *
        Real.exp (-(7 / 32 * thetaB S N δ * S.dF (bc S.toDomSeq x) (bc S.toDomSeq x'))) * hs (f x') := by
  have hδ := H.hδ0
  have hθ := H.thetaB_pos (N := N)
  have hθle : thetaB S N δ ≤ 1 / 64 * δ := min_le_left _ _
  have hCv := H.Cv_nn
  have hCD := H.CD_nn
  set g : Site NF → Mat := avgL S W
    ((Gp' S.toDomSeq (cfgX X) W ΩD - Gp' S.toDomSeq (cfgX (X0 S)) (W1 S) ΩD : Module.End ℂ (Site NF → Mat)) f)
  have hg : ∀ c : BD S ΩD, hs (g c.1) ≤ ((S.L : ℝ) ^ (4 * jj c.1))⁻¹ * ∑ x', (2 * Real.sqrt N * CD S N δ α₁ η) * 1 *
      (S.L : ℝ) ^ (2 * jj (bc S.toDomSeq x')) * Real.exp (-(1 / 4 * δ * S.dF (bc S.toDomSeq x') c.1)) * hs (f x') := by
    intro c
    refine (H.QG_diff hRMc ((BD_sub S ΩD) c.2) f).trans (le_of_eq ?_)
    congr 1
    exact Finset.sum_congr rfl fun x' _ => by ring
  have h := H.PgenR hRMb hRMs4 hsmallT hRMθs hRMθc (ρ := 1 / 4 * δ) (by linarith)
    (Gp' S.toDomSeq (cfgX (X0 S)) (W1 S) ΩD) (bc_mem_detB S x) (by positivity) (by norm_num) (fun c Z => H.hLop_G0 c Z)
    g (fun x' => hs (f x')) (fun _ => 1) (fun x' => hs_nonneg _) (fun _ => zero_le_one) (by positivity) hg
  refine h.trans (le_of_eq ?_)
  unfold CPdB1
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x' _ => ?_
  ring

/-- **The third term of `P(𝐔) - P(id)`**: `G'_idQ'^*T_𝐔⁻¹(Q'_W - Q'_id)G'_id`. -/
theorem PdiffB2 [NeZero N]
    (hRMb : (S.toContSeq).r1 (1 / 2) (1 / 32 * δ) ≤ RMS) (hRMs4 : 32 * Real.log S.L / (1 / 4 * δ) ≤ RMS)
    (hsmallT : CTd S N δ α₁ η * (S.toContSeq).c1 (1 / 2) (1 / 32 * δ) ≤ gammaB N / 4)
    (hRMθs : 32 * Real.log S.L / (thetaB S N δ / 2) ≤ RMS)
    (hRMθc : (S.toContSeq).r1 (1 / 2) (7 / 16 * thetaB S N δ) ≤ RMS) (f : Site NF → Mat) (x : Site NF) :
    hs (Gp' S.toDomSeq (cfgX (X0 S)) (W1 S) ΩD (QpL S W (unblkL S ΩD (Tinv S X W ΩD (blkL S ΩD
        (avgL S W (Gp' S.toDomSeq (cfgX (X0 S)) (W1 S) ΩD f) - avgL S (W1 S) (Gp' S.toDomSeq (cfgX (X0 S)) (W1 S) ΩD f)))))) x) ≤
      CPdB2 S N δ η * ∑ x', ((S.L : ℝ) ^ (4 * jj (bc S.toDomSeq x')))⁻¹ *
        Real.exp (-(7 / 32 * thetaB S N δ * S.dF (bc S.toDomSeq x) (bc S.toDomSeq x'))) * hs (f x') := by
  have hδ := H.hδ0
  have hθ := H.thetaB_pos (N := N)
  have hθle : thetaB S N δ ≤ 1 / 64 * δ := min_le_left _ _
  have hCv := H.Cv_nn
  have hη := H.hη
  have hg : ∀ c : BD S ΩD, hs ((avgL S W (Gp' S.toDomSeq (cfgX (X0 S)) (W1 S) ΩD f) -
      avgL S (W1 S) (Gp' S.toDomSeq (cfgX (X0 S)) (W1 S) ΩD f)) c.1) ≤
      ((S.L : ℝ) ^ (4 * jj c.1))⁻¹ * ∑ x', (2 * Real.sqrt N * η * Cv S δ (Csc S N) (4 * N * (S.L : ℝ) ^ 4)) * 1 *
        (S.L : ℝ) ^ (2 * jj (bc S.toDomSeq x')) * Real.exp (-(1 / 4 * δ * S.dF (bc S.toDomSeq x') c.1)) * hs (f x') := by
    intro c
    refine (H.QG_avgdiff ((BD_sub S ΩD) c.2) f).trans ?_
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x' _ => ?_) (by positivity)
    have he := exp_rate_le (show 1 / 4 * δ ≤ 7 / 8 * δ by linarith) (S.dF_nonneg (bc S.toDomSeq x') c.1)
    have h0 : 0 ≤ 2 * Real.sqrt N * η * Cv S δ (Csc S N) (4 * N * (S.L : ℝ) ^ 4) *
        (S.L : ℝ) ^ (2 * jj (bc S.toDomSeq x')) * hs (f x') := by have := hs_nonneg (f x'); positivity
    calc 2 * Real.sqrt N * η * Cv S δ (Csc S N) (4 * N * (S.L : ℝ) ^ 4) * (S.L : ℝ) ^ (2 * jj (bc S.toDomSeq x')) *
          Real.exp (-(7 / 8 * δ * S.dF (bc S.toDomSeq x') c.1)) * hs (f x')
        = 2 * Real.sqrt N * η * Cv S δ (Csc S N) (4 * N * (S.L : ℝ) ^ 4) * (S.L : ℝ) ^ (2 * jj (bc S.toDomSeq x')) *
          hs (f x') * Real.exp (-(7 / 8 * δ * S.dF (bc S.toDomSeq x') c.1)) := by ring
      _ ≤ 2 * Real.sqrt N * η * Cv S δ (Csc S N) (4 * N * (S.L : ℝ) ^ 4) * (S.L : ℝ) ^ (2 * jj (bc S.toDomSeq x')) *
          hs (f x') * Real.exp (-(1 / 4 * δ * S.dF (bc S.toDomSeq x') c.1)) := mul_le_mul_of_nonneg_left he h0
      _ = _ := by ring
  have h := H.PgenR hRMb hRMs4 hsmallT hRMθs hRMθc (ρ := 1 / 4 * δ) (by linarith)
    (Gp' S.toDomSeq (cfgX (X0 S)) (W1 S) ΩD) (bc_mem_detB S x) (by positivity) (by norm_num) (fun c Z => H.hLop_G0 c Z)
    _ (fun x' => hs (f x')) (fun _ => 1) (fun x' => hs_nonneg _) (fun _ => zero_le_one) (by positivity) hg
  refine h.trans (le_of_eq ?_)
  unfold CPdB2
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x' _ => ?_
  ring


/-- **The kernel bound of `L(Q'^*_W - Q'^*_id)T⁻¹g`** (as `PgenR`, with the difference of the transposed averages; for the
fourth term of `P(𝐔) - P(id)`). As `PgenR`: `P`, `∇P`, `P∇^*`, `∇P∇^*`: a left operator bounded on the `λ_Z` like `G'`,
composed with `Q'^*T⁻¹`, applied to data `g` bounded on `𝐁_D` like `Q'G'f`. -/
theorem PgenD [NeZero N]
    (hRMb : (S.toContSeq).r1 (1 / 2) (1 / 32 * δ) ≤ RMS) (hRMs4 : 32 * Real.log S.L / (1 / 4 * δ) ≤ RMS)
    (hsmallT : CTd S N δ α₁ η * (S.toContSeq).c1 (1 / 2) (1 / 32 * δ) ≤ gammaB N / 4)
    (hRMθs : 32 * Real.log S.L / (thetaB S N δ / 2) ≤ RMS)
    (hRMθc : (S.toContSeq).r1 (1 / 2) (7 / 16 * thetaB S N δ) ≤ RMS)
    {ρ : ℝ} (hρ : 9 / 8 * thetaB S N δ ≤ ρ)
    (Lop : Module.End ℂ (Site NF → Mat)) {y x : Site NF} (hy : y ∈ detB S.toDomSeq) {A0 εL : ℝ}
    (hA0 : 0 ≤ A0) (hεL : 0 ≤ εL)
    (hLop : ∀ (c : BD S ΩD) (Z : Mat), hs (Lop (lamZ S W c.1 Z - lamZ S (W1 S) c.1 Z) x) ≤
      A0 * εL * (S.L : ℝ) ^ (2 * jj y) * Real.exp (-(ρ * S.dF y c.1)) * hs Z)
    (g : Site NF → Mat) (w εR : Site NF → ℝ) (hw : ∀ x', 0 ≤ w x') (hεR : ∀ x', 0 ≤ εR x') {B0 : ℝ} (hB0 : 0 ≤ B0)
    (hg : ∀ c : BD S ΩD, hs (g c.1) ≤ ((S.L : ℝ) ^ (4 * jj c.1))⁻¹ * ∑ x', B0 * εR x' *
      (S.L : ℝ) ^ (2 * jj (bc S.toDomSeq x')) * Real.exp (-(ρ * S.dF (bc S.toDomSeq x') c.1)) * w x') :
    hs (Lop (QpL S W (unblkL S ΩD (Tinv S X W ΩD (blkL S ΩD g))) -
      QpL S (W1 S) (unblkL S ΩD (Tinv S X W ΩD (blkL S ΩD g)))) x) ≤
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
  have hP : Lop (QpL S W (unblkL S ΩD u) - QpL S (W1 S) (unblkL S ΩD u)) =
      ∑ c : BD S ΩD, Lop (lamZ S W c.1 (Zc c) - lamZ S (W1 S) c.1 (Zc c)) := by
    rw [← map_sum, Finset.sum_sub_distrib, sum_lamZ, sum_lamZ]; rfl
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
  have hG : ∀ c : BD S ΩD, hs (Lop (lamZ S W c.1 (Zc c) - lamZ S (W1 S) c.1 (Zc c)) x) ≤
      A0 * εL * (S.L : ℝ) ^ (2 * jj y) * Real.exp (-(ρ * S.dF y c.1)) *
        (((S.L : ℝ) ^ (4 * jj c.1))⁻¹ * hs (proj (u.ofLp c))) := by
    intro c
    have hZ : hs (Zc c) = ((S.L : ℝ) ^ (4 * jj c.1))⁻¹ * hs (proj (u.ofLp c)) := by
      simp only [Zc]
      rw [RegularAverages.hs_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [← hZ]; exact hLop c (Zc c)
  set E : Site NF → Site NF → Site NF → ℝ := fun y' c c' =>
    (S.L : ℝ) ^ (2 * jj y) * Real.exp (-(ρ * S.dF y c)) * ((S.L : ℝ) ^ (4 * jj c))⁻¹ *
      (Real.exp (-(thetaB S N δ * S.dF c c')) * ((S.L : ℝ) ^ (4 * jj c'))⁻¹ * (S.L : ℝ) ^ (2 * jj y') *
        Real.exp (-(ρ * S.dF c' y')))
  have hE0 : ∀ y' c c', 0 ≤ E y' c c' := fun y' c c' => by positivity
  set K := A0 * εL * (2 / gammaB N) * B0
  have hK0 : 0 ≤ K := by positivity
  have hstep : hs (Lop (QpL S W (unblkL S ΩD u) - QpL S (W1 S) (unblkL S ΩD u)) x) ≤
      ∑ c : BD S ΩD, ∑ c' : BD S ΩD, ∑ x', K * E (bc S.toDomSeq x') c.1 c'.1 * (εR x' * w x') := by
    rw [hP, Finset.sum_apply]
    refine (RegularAverages.hs_sum_le _ _).trans (sum_le_sum fun c _ => (hG c).trans ?_)
    have hA0' : 0 ≤ A0 * εL * (S.L : ℝ) ^ (2 * jj y) * Real.exp (-(ρ * S.dF y c.1)) *
        ((S.L : ℝ) ^ (4 * jj c.1))⁻¹ := by positivity
    calc A0 * εL * (S.L : ℝ) ^ (2 * jj y) * Real.exp (-(ρ * S.dF y c.1)) *
          (((S.L : ℝ) ^ (4 * jj c.1))⁻¹ * hs (proj (u.ofLp c)))
        = A0 * εL * (S.L : ℝ) ^ (2 * jj y) * Real.exp (-(ρ * S.dF y c.1)) *
          ((S.L : ℝ) ^ (4 * jj c.1))⁻¹ * hs (proj (u.ofLp c)) := by ring
      _ ≤ A0 * εL * (S.L : ℝ) ^ (2 * jj y) * Real.exp (-(ρ * S.dF y c.1)) *
          ((S.L : ℝ) ^ (4 * jj c.1))⁻¹ * ∑ c' : BD S ΩD, 2 / gammaB N *
            Real.exp (-(thetaB S N δ * S.dF c.1 c'.1)) * (((S.L : ℝ) ^ (4 * jj c'.1))⁻¹ * ∑ x', B0 * εR x' *
              (S.L : ℝ) ^ (2 * jj (bc S.toDomSeq x')) * Real.exp (-(ρ * S.dF (bc S.toDomSeq x') c'.1)) *
                w x') := by
          refine mul_le_mul_of_nonneg_left ((hu c).trans (sum_le_sum fun c' _ => ?_)) hA0'
          exact mul_le_mul_of_nonneg_left (hg c') (by positivity)
      _ = _ := by
          rw [mul_sum]
          refine sum_congr rfl fun c' _ => ?_
          rw [mul_sum, mul_sum, mul_sum]
          refine sum_congr rfl fun x' _ => ?_
          simp only [E, K]
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
    refine le_trans ?_ (chainP S hθ hρ hRMθs hRMθc hy
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

/-- The constant of the fourth term of `P(𝐔) - P(id)`. -/
def CPdB3 (S : SeqDom) (N : ℕ) (δ η : ℝ) : ℝ :=
  2 * Real.sqrt N * η * Cv S δ (Csc S N) (4 * N * (S.L : ℝ) ^ 4) *
    (2 * Real.sqrt N * Cv S δ (Csc S N) (4 * N * (S.L : ℝ) ^ 4)) * (2 / gammaB N) *
    (S.L : ℝ) ^ (12 : ℝ) * (S.toContSeq).c1 (1 / 2) (thetaB S N δ) * (S.toContSeq).c1 (1 / 2) (7 / 16 * thetaB S N δ)

/-- **The fourth term of `P(𝐔) - P(id)`**: `G'_id(Q'^*_W - Q'^*_id)T_𝐔⁻¹Q'_idG'_id`. -/
theorem PdiffB3 [NeZero N]
    (hRMb : (S.toContSeq).r1 (1 / 2) (1 / 32 * δ) ≤ RMS) (hRMs4 : 32 * Real.log S.L / (1 / 4 * δ) ≤ RMS)
    (hsmallT : CTd S N δ α₁ η * (S.toContSeq).c1 (1 / 2) (1 / 32 * δ) ≤ gammaB N / 4)
    (hRMθs : 32 * Real.log S.L / (thetaB S N δ / 2) ≤ RMS)
    (hRMθc : (S.toContSeq).r1 (1 / 2) (7 / 16 * thetaB S N δ) ≤ RMS) (f : Site NF → Mat) (x : Site NF) :
    hs (Gp' S.toDomSeq (cfgX (X0 S)) (W1 S) ΩD
        (QpL S W (unblkL S ΩD (Tinv S X W ΩD (blkL S ΩD (avgL S (W1 S) (Gp' S.toDomSeq (cfgX (X0 S)) (W1 S) ΩD f))))) -
          QpL S (W1 S) (unblkL S ΩD (Tinv S X W ΩD (blkL S ΩD (avgL S (W1 S) (Gp' S.toDomSeq (cfgX (X0 S)) (W1 S) ΩD f)))))) x) ≤
      CPdB3 S N δ η * ∑ x', ((S.L : ℝ) ^ (4 * jj (bc S.toDomSeq x')))⁻¹ *
        Real.exp (-(7 / 32 * thetaB S N δ * S.dF (bc S.toDomSeq x) (bc S.toDomSeq x'))) * hs (f x') := by
  have H0 := H.triv (N := N)
  have hδ := H.hδ0
  have hθ := H.thetaB_pos (N := N)
  have hθle : thetaB S N δ ≤ 1 / 64 * δ := min_le_left _ _
  have hCv := H.Cv_nn
  have hη := H.hη
  have hLop : ∀ (c : BD S ΩD) (Z : Mat),
      hs (Gp' S.toDomSeq (cfgX (X0 S)) (W1 S) ΩD (lamZ S W c.1 Z - lamZ S (W1 S) c.1 Z) x) ≤
        (2 * Real.sqrt N * η * Cv S δ (Csc S N) (4 * N * (S.L : ℝ) ^ 4)) * 1 * (S.L : ℝ) ^ (2 * jj (bc S.toDomSeq x)) *
          Real.exp (-(7 / 8 * δ * S.dF (bc S.toDomSeq x) c.1)) * hs Z := by
    intro c Z
    have hc := (BD_sub S ΩD) c.2
    have hd := lamZ_diff S hη H.hW1 H.hW hc Z
    have hsupp : ∀ x'', x'' ∉ Blk S.toDomSeq (jj c.1) c.1 → (lamZ S W c.1 Z - lamZ S (W1 S) c.1 Z) x'' = 0 :=
      fun x'' hx'' => by rw [Pi.sub_apply, lamZ_supp S W hc Z x'' hx'', lamZ_supp S (W1 S) hc Z x'' hx'', sub_zero]
    have h := H0.KB_Gp' (bc S.toDomSeq x) (bc_mem_detB S x) c.1 hc (lamZ S W c.1 Z - lamZ S (W1 S) c.1 Z)
      (2 * Real.sqrt N * η * hs Z) (by have := hs_nonneg (N := N) Z; positivity) hsupp hd x (mem_blk_bc S x)
    simp only [zero_mul, pow_zero, mul_one] at h
    refine h.trans (le_of_eq ?_)
    ring
  set g : Site NF → Mat := avgL S (W1 S) (Gp' S.toDomSeq (cfgX (X0 S)) (W1 S) ΩD f)
  have hg : ∀ c : BD S ΩD, hs (g c.1) ≤ ((S.L : ℝ) ^ (4 * jj c.1))⁻¹ * ∑ x',
      (2 * Real.sqrt N * Cv S δ (Csc S N) (4 * N * (S.L : ℝ) ^ 4)) * 1 * (S.L : ℝ) ^ (2 * jj (bc S.toDomSeq x')) *
        Real.exp (-(7 / 8 * δ * S.dF (bc S.toDomSeq x') c.1)) * hs (f x') := by
    intro c
    refine (H0.QG_bound ((BD_sub S ΩD) c.2) f).trans (le_of_eq ?_)
    congr 1
    exact Finset.sum_congr rfl fun x' _ => by ring
  have h := H.PgenD hRMb hRMs4 hsmallT hRMθs hRMθc (ρ := 7 / 8 * δ) (by linarith)
    (Gp' S.toDomSeq (cfgX (X0 S)) (W1 S) ΩD) (bc_mem_detB S x) (by positivity) (by norm_num) hLop
    g (fun x' => hs (f x')) (fun _ => 1) (fun x' => hs_nonneg _) (fun _ => zero_le_one) (by positivity) hg
  refine h.trans (le_of_eq ?_)
  unfold CPdB3
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x' _ => ?_
  ring

/-- The norm of a difference of the block operators: `|(K_id - K_𝐔)(c, c')v| ≤ C_Te^{-(δ/32)d(c, c')}|v|`. -/
lemma kerT_diff_le [NeZero N] (hRMa : (S.toContSeq).r1 (1 / 2) (1 / 8 * δ) ≤ RMS)
    (hRMs4 : 32 * Real.log S.L / (1 / 4 * δ) ≤ RMS) (c c' : BD S ΩD) (v : VS N 1) :
    ‖kerT S (Subtype.val : BD S ΩD → Site NF) (X0 S) (W1 S) ΩD c c' v -
        kerT S (Subtype.val : BD S ΩD → Site NF) X W ΩD c c' v‖ ≤
      CTd S N δ α₁ η * Real.exp (-(1 / 32 * δ * S.dF c.1 c'.1)) * ‖v‖ := by
  rw [kerT_apply, kerT_apply, ← emb_sub', norm_emb, norm_eq_proj v, SupportCont.hs_sub_comm]
  have h := H.That_diff hRMa hRMs4 ((BD_sub S ΩD) c.2) ((BD_sub S ΩD) c'.2) (proj v)
  have hN := Real.sqrt_nonneg (N : ℝ)
  calc Real.sqrt N * hs (That S X W ΩD c.1 c'.1 (proj v) - That S (X0 S) (W1 S) ΩD c.1 c'.1 (proj v))
      ≤ Real.sqrt N * (CTd S N δ α₁ η * Real.exp (-(1 / 32 * δ * S.dF c.1 c'.1)) * hs (proj v)) :=
        mul_le_mul_of_nonneg_left h hN
    _ = _ := by ring

/-- The constant of the fifth term of `P(𝐔) - P(id)`. -/
def CPdB4 (S : SeqDom) (N : ℕ) (δ α₁ η : ℝ) : ℝ :=
  2 * Real.sqrt N * Cv S δ (Csc S N) (4 * N * (S.L : ℝ) ^ 4) * (2 / gammaB N) ^ 2 * CTd S N δ α₁ η *
    ((S.toContSeq).c1 (1 / 2) (thetaB S N δ) * (S.toContSeq).c1 (1 / 2) (thetaB S N δ / 2)) *
    (2 * Real.sqrt N * Cv S δ (Csc S N) (4 * N * (S.L : ℝ) ^ 4)) *
    ((S.L : ℝ) ^ (12 : ℝ) * (S.toContSeq).c1 (1 / 2) (thetaB S N δ / 4) *
      (S.toContSeq).c1 (1 / 2) (7 / 16 * (thetaB S N δ / 4)))

/-- The middle chain `T_𝐔⁻¹(T̂_id - T̂_𝐔)T_id⁻¹`: `Σ_{c₁, c₂}e^{-θd(c, c₁)}e^{-(δ/32)d(c₁, c₂)}e^{-θd(c₂, c₃)} ≤
c₁(½, θ)c₁(½, θ/2)e^{-(θ/4)d(c, c₃)}`. -/
lemma chain_mid [NeZero N] (hRMq : (S.toContSeq).r1 (1 / 2) (thetaB S N δ) ≤ RMS)
    (hRMq2 : (S.toContSeq).r1 (1 / 2) (thetaB S N δ / 2) ≤ RMS) (c c3 : BD S ΩD) :
    ∑ c1 : BD S ΩD, ∑ c2 : BD S ΩD, Real.exp (-(thetaB S N δ * S.dF c.1 c1.1)) *
        Real.exp (-(1 / 32 * δ * S.dF c1.1 c2.1)) * Real.exp (-(thetaB S N δ * S.dF c2.1 c3.1)) ≤
      (S.toContSeq).c1 (1 / 2) (thetaB S N δ) * (S.toContSeq).c1 (1 / 2) (thetaB S N δ / 2) *
        Real.exp (-(thetaB S N δ / 4 * S.dF c.1 c3.1)) := by
  have hδ := H.hδ0
  have hθ := H.thetaB_pos (N := N)
  have hθle : thetaB S N δ ≤ 1 / 64 * δ := min_le_left _ _
  have hc := (BD_sub S ΩD) c.2
  set θ := thetaB S N δ
  have hmin1 : min θ (1 / 32 * δ) = θ := min_eq_left (by linarith)
  have hmin2 : min (θ / 2) θ = θ / 2 := min_eq_left (by linarith)
  -- the inner sum over `c₁`
  have h1 : ∀ c2 : BD S ΩD, ∑ c1 : BD S ΩD, Real.exp (-(θ * S.dF c.1 c1.1)) * Real.exp (-(1 / 32 * δ * S.dF c1.1 c2.1)) ≤
      (S.toContSeq).c1 (1 / 2) θ * Real.exp (-(1 / 2 * θ * S.dF c.1 c2.1)) := by
    intro c2
    refine (sum_BD_le_detB S (fun c1 => Real.exp (-(θ * S.dF c.1 c1)) * Real.exp (-(1 / 32 * δ * S.dF c1 c2.1)))
      fun _ => by positivity).trans ?_
    have := chain2 S hθ (show (0 : ℝ) < 1 / 32 * δ by positivity) (by rw [hmin1]; exact hRMq) (y' := c2.1) hc
    rwa [hmin1] at this
  calc ∑ c1 : BD S ΩD, ∑ c2 : BD S ΩD, Real.exp (-(θ * S.dF c.1 c1.1)) *
        Real.exp (-(1 / 32 * δ * S.dF c1.1 c2.1)) * Real.exp (-(θ * S.dF c2.1 c3.1))
      = ∑ c2 : BD S ΩD, (∑ c1 : BD S ΩD, Real.exp (-(θ * S.dF c.1 c1.1)) *
          Real.exp (-(1 / 32 * δ * S.dF c1.1 c2.1))) * Real.exp (-(θ * S.dF c2.1 c3.1)) := by
        rw [Finset.sum_comm]; simp only [Finset.sum_mul]
    _ ≤ ∑ c2 : BD S ΩD, (S.toContSeq).c1 (1 / 2) θ * Real.exp (-(1 / 2 * θ * S.dF c.1 c2.1)) *
          Real.exp (-(θ * S.dF c2.1 c3.1)) :=
        Finset.sum_le_sum fun c2 _ => mul_le_mul_of_nonneg_right (h1 c2) (Real.exp_pos _).le
    _ = (S.toContSeq).c1 (1 / 2) θ * ∑ c2 : BD S ΩD, Real.exp (-(θ / 2 * S.dF c.1 c2.1)) *
          Real.exp (-(θ * S.dF c2.1 c3.1)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun c2 _ => ?_
        rw [show 1 / 2 * θ = θ / 2 by ring]; ring
    _ ≤ (S.toContSeq).c1 (1 / 2) θ * ((S.toContSeq).c1 (1 / 2) (θ / 2) * Real.exp (-(1 / 2 * (θ / 2) * S.dF c.1 c3.1))) := by
        have hc1 : 0 ≤ (S.toContSeq).c1 (1 / 2) θ := by unfold Summation.ContSeq.c1; positivity
        refine mul_le_mul_of_nonneg_left ?_ hc1
        refine (sum_BD_le_detB S (fun c2 => Real.exp (-(θ / 2 * S.dF c.1 c2)) * Real.exp (-(θ * S.dF c2 c3.1)))
          fun _ => by positivity).trans ?_
        have := chain2 S (show (0 : ℝ) < θ / 2 by positivity) hθ (by rw [hmin2]; exact hRMq2) (y' := c3.1) hc
        rwa [hmin2] at this
    _ = _ := by rw [show 1 / 2 * (θ / 2) = θ / 4 by ring]; ring

/-- **The difference of the block inverses**: `T_𝐔⁻¹ν - T_id⁻¹ν = T_𝐔⁻¹(T_id - T_𝐔)T_id⁻¹ν`, so that
`|(T_𝐔⁻¹ν - T_id⁻¹ν)(c)| ≤ (2/γ)²C_TΣ_{c₃}(Σ_{c₁, c₂}e^{-θd(c, c₁)}e^{-(δ/32)d(c₁, c₂)}e^{-θd(c₂, c₃)})|ν(c₃)|`. -/
lemma Tinv_diff_le [NeZero N]
    (hRMb : (S.toContSeq).r1 (1 / 2) (1 / 32 * δ) ≤ RMS) (hRMs4 : 32 * Real.log S.L / (1 / 4 * δ) ≤ RMS)
    (hsmallT : CTd S N δ α₁ η * (S.toContSeq).c1 (1 / 2) (1 / 32 * δ) ≤ gammaB N / 4)
    (hsmallT0 : CTd S N δ 0 0 * (S.toContSeq).c1 (1 / 2) (1 / 32 * δ) ≤ gammaB N / 4)
    (hRMa : (S.toContSeq).r1 (1 / 2) (1 / 8 * δ) ≤ RMS) (ν : L2 (BD S ΩD) (VS N 1)) (c : BD S ΩD) :
    ‖(Tinv S X W ΩD ν - Tinv S (X0 S) (W1 S) ΩD ν).ofLp c‖ ≤
      (2 / gammaB N) ^ 2 * CTd S N δ α₁ η * ∑ c3 : BD S ΩD, (∑ c1 : BD S ΩD, ∑ c2 : BD S ΩD,
        Real.exp (-(thetaB S N δ * S.dF c.1 c1.1)) * Real.exp (-(1 / 32 * δ * S.dF c1.1 c2.1)) *
          Real.exp (-(thetaB S N δ * S.dF c2.1 c3.1))) * ‖ν.ofLp c3‖ := by
  have H0 := H.triv (N := N)
  obtain ⟨hbU, hsolU⟩ := H.block_inverse hRMb hRMs4 hsmallT
  obtain ⟨hb0, hsol0⟩ := H0.block_inverse hRMb hRMs4 hsmallT0
  set KU := kerT S (Subtype.val : BD S ΩD → Site NF) X W ΩD
  set K0 := kerT S (Subtype.val : BD S ΩD → Site NF) (X0 S) (W1 S) ΩD
  set uU := Tinv S X W ΩD ν
  set u0 := Tinv S (X0 S) (W1 S) ΩD ν
  have hU : kerApply KU uU = ν := kerApply_Tinv S X W ΩD hbU ν
  have h0 : kerApply K0 u0 = ν := kerApply_Tinv S (X0 S) (W1 S) ΩD hb0 ν
  set θ := thetaB S N δ
  set k0 := 2 / gammaB N
  have hγ : 0 < gammaB N := by unfold gammaB; positivity
  have hk0 : 0 ≤ k0 := by positivity
  have hCT := H.CTd_nn
  have hinvU : ∀ (v : L2 (BD S ΩD) (VS N 1)) (c : BD S ΩD),
      ‖v.ofLp c‖ ≤ ∑ c' : BD S ΩD, k0 * Real.exp (-(θ * S.dF c.1 c'.1)) * ‖(kerApply KU v).ofLp c'‖ := by
    intro v c
    refine (inv_bound _ hbU _ hsolU v c).trans (le_of_eq (Finset.sum_congr rfl fun c' _ => ?_))
    simp only [k0, θ]; unfold thetaB gammaB; ring_nf
  have hinv0 : ∀ (v : L2 (BD S ΩD) (VS N 1)) (c : BD S ΩD),
      ‖v.ofLp c‖ ≤ ∑ c' : BD S ΩD, k0 * Real.exp (-(θ * S.dF c.1 c'.1)) * ‖(kerApply K0 v).ofLp c'‖ := by
    intro v c
    refine (inv_bound _ hb0 _ hsol0 v c).trans (le_of_eq (Finset.sum_congr rfl fun c' _ => ?_))
    simp only [k0, θ]; unfold thetaB gammaB; ring_nf
  -- the resolvent identity at the level of the kernels
  have hres : ∀ c1 : BD S ΩD, (kerApply KU (uU - u0)).ofLp c1 = ∑ c2 : BD S ΩD, (K0 c1 c2 (u0.ofLp c2) - KU c1 c2 (u0.ofLp c2)) := by
    intro c1
    have e1 : kerApply KU (uU - u0) = kerApply KU uU - kerApply KU u0 := (kerLin KU).map_sub uU u0
    rw [e1, hU, ← h0, WithLp.ofLp_sub, Pi.sub_apply, kerApply_apply, kerApply_apply, Finset.sum_sub_distrib]
  have hmid : ∀ c1 : BD S ΩD, ‖(kerApply KU (uU - u0)).ofLp c1‖ ≤
      ∑ c2 : BD S ΩD, CTd S N δ α₁ η * Real.exp (-(1 / 32 * δ * S.dF c1.1 c2.1)) * ‖u0.ofLp c2‖ := by
    intro c1
    rw [hres]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun c2 _ => H.kerT_diff_le hRMa hRMs4 c1 c2 _)
  have hu0 : ∀ c2 : BD S ΩD, ‖u0.ofLp c2‖ ≤ ∑ c3 : BD S ΩD, k0 * Real.exp (-(θ * S.dF c2.1 c3.1)) * ‖ν.ofLp c3‖ := by
    intro c2
    have := hinv0 u0 c2
    rwa [h0] at this
  -- combine
  have hD := hinvU (uU - u0) c
  calc ‖(uU - u0).ofLp c‖
      ≤ ∑ c1 : BD S ΩD, k0 * Real.exp (-(θ * S.dF c.1 c1.1)) * ‖(kerApply KU (uU - u0)).ofLp c1‖ := hD
    _ ≤ ∑ c1 : BD S ΩD, k0 * Real.exp (-(θ * S.dF c.1 c1.1)) * ∑ c2 : BD S ΩD, CTd S N δ α₁ η *
          Real.exp (-(1 / 32 * δ * S.dF c1.1 c2.1)) * ∑ c3 : BD S ΩD, k0 * Real.exp (-(θ * S.dF c2.1 c3.1)) *
            ‖ν.ofLp c3‖ := by
        refine Finset.sum_le_sum fun c1 _ => mul_le_mul_of_nonneg_left ((hmid c1).trans ?_) (by positivity)
        exact Finset.sum_le_sum fun c2 _ => mul_le_mul_of_nonneg_left (hu0 c2) (by positivity)
    _ = k0 ^ 2 * CTd S N δ α₁ η * ∑ c3 : BD S ΩD, (∑ c1 : BD S ΩD, ∑ c2 : BD S ΩD,
          Real.exp (-(θ * S.dF c.1 c1.1)) * Real.exp (-(1 / 32 * δ * S.dF c1.1 c2.1)) *
            Real.exp (-(θ * S.dF c2.1 c3.1))) * ‖ν.ofLp c3‖ := by
        have e1 : ∑ c1 : BD S ΩD, k0 * Real.exp (-(θ * S.dF c.1 c1.1)) * ∑ c2 : BD S ΩD, CTd S N δ α₁ η *
            Real.exp (-(1 / 32 * δ * S.dF c1.1 c2.1)) * ∑ c3 : BD S ΩD, k0 * Real.exp (-(θ * S.dF c2.1 c3.1)) *
              ‖ν.ofLp c3‖ = ∑ c1 : BD S ΩD, ∑ c2 : BD S ΩD, ∑ c3 : BD S ΩD, k0 ^ 2 * CTd S N δ α₁ η *
                (Real.exp (-(θ * S.dF c.1 c1.1)) * Real.exp (-(1 / 32 * δ * S.dF c1.1 c2.1)) *
                  Real.exp (-(θ * S.dF c2.1 c3.1))) * ‖ν.ofLp c3‖ := by
          refine Finset.sum_congr rfl fun c1 _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun c2 _ => ?_
          rw [Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun c3 _ => by ring
        rw [e1, Finset.sum_congr rfl fun c1 _ => Finset.sum_comm, Finset.sum_comm, Finset.mul_sum]
        refine Finset.sum_congr rfl fun c3 _ => ?_
        rw [Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun c1 _ => ?_
        rw [Finset.sum_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun c2 _ => by ring

/-- **The fifth term of `P(𝐔) - P(id)`**: `G'_idQ'^*_id(T_𝐔⁻¹ - T_id⁻¹)Q'_idG'_id` has the kernel
`C_{PdB4}a_{y(x')}^{-4}e^{-(7/32)(θ_B/4)d}` (the resolvent identity of the block inverses, `chain_mid`, `chainP` at the rate
`θ_B/4`). -/
theorem PdiffB4 [NeZero N]
    (hRMb : (S.toContSeq).r1 (1 / 2) (1 / 32 * δ) ≤ RMS) (hRMs4 : 32 * Real.log S.L / (1 / 4 * δ) ≤ RMS)
    (hsmallT : CTd S N δ α₁ η * (S.toContSeq).c1 (1 / 2) (1 / 32 * δ) ≤ gammaB N / 4)
    (hsmallT0 : CTd S N δ 0 0 * (S.toContSeq).c1 (1 / 2) (1 / 32 * δ) ≤ gammaB N / 4)
    (hRMa : (S.toContSeq).r1 (1 / 2) (1 / 8 * δ) ≤ RMS)
    (hRMq : (S.toContSeq).r1 (1 / 2) (thetaB S N δ) ≤ RMS)
    (hRMq2 : (S.toContSeq).r1 (1 / 2) (thetaB S N δ / 2) ≤ RMS)
    (hRMs8 : 32 * Real.log S.L / (thetaB S N δ / 4 / 2) ≤ RMS)
    (hRMc8 : (S.toContSeq).r1 (1 / 2) (7 / 16 * (thetaB S N δ / 4)) ≤ RMS) (f : Site NF → Mat) (x : Site NF) :
    hs (Gp' S.toDomSeq (cfgX (X0 S)) (W1 S) ΩD (QpL S (W1 S) (unblkL S ΩD
        (Tinv S X W ΩD (blkL S ΩD (avgL S (W1 S) (Gp' S.toDomSeq (cfgX (X0 S)) (W1 S) ΩD f))) -
          Tinv S (X0 S) (W1 S) ΩD (blkL S ΩD (avgL S (W1 S) (Gp' S.toDomSeq (cfgX (X0 S)) (W1 S) ΩD f)))))) x) ≤
      CPdB4 S N δ α₁ η * ∑ x', ((S.L : ℝ) ^ (4 * jj (bc S.toDomSeq x')))⁻¹ *
        Real.exp (-(7 / 32 * (thetaB S N δ / 4) * S.dF (bc S.toDomSeq x) (bc S.toDomSeq x'))) * hs (f x') := by
  have H0 := H.triv (N := N)
  have hL : (0 : ℝ) < S.L := by exact_mod_cast S.Lpos
  have hδ := H.hδ0
  have hθ := H.thetaB_pos (N := N)
  have hθle : thetaB S N δ ≤ 1 / 64 * δ := min_le_left _ _
  have hCv := H.Cv_nn
  have hCT := H.CTd_nn
  have hγ : 0 < gammaB N := by unfold gammaB; positivity
  have hN : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N))
  set θ := thetaB S N δ
  set ρ : ℝ := 7 / 8 * δ
  set Cvv := Cv S δ (Csc S N) (4 * N * (S.L : ℝ) ^ 4)
  set k0 := 2 / gammaB N
  set CT := CTd S N δ α₁ η
  set cc := (S.toContSeq).c1 (1 / 2) θ * (S.toContSeq).c1 (1 / 2) (θ / 2)
  have hcc : 0 ≤ cc := by
    have h1 : 0 ≤ (S.toContSeq).c1 (1 / 2) θ := by unfold Summation.ContSeq.c1; positivity
    have h2 : 0 ≤ (S.toContSeq).c1 (1 / 2) (θ / 2) := by unfold Summation.ContSeq.c1; positivity
    positivity
  set g := avgL S (W1 S) (Gp' S.toDomSeq (cfgX (X0 S)) (W1 S) ΩD f)
  set ν := blkL S ΩD g
  set d := Tinv S X W ΩD ν - Tinv S (X0 S) (W1 S) ΩD ν
  set y := bc S.toDomSeq x
  have hy : y ∈ detB S.toDomSeq := bc_mem_detB S x
  set Zc : BD S ΩD → Mat := fun c => ((((S.L : ℝ) ^ (4 * jj c.1)) : ℝ) : ℂ)⁻¹ • proj (d.ofLp c)
  set F : Site NF → ℝ := fun x' => hs (f x')
  set Q : Site NF → ℝ := fun c3 => ((S.L : ℝ) ^ (4 * jj c3))⁻¹ * ∑ x', 2 * Real.sqrt N * Cvv *
    (S.L : ℝ) ^ (2 * jj (bc S.toDomSeq x')) * Real.exp (-(ρ * S.dF (bc S.toDomSeq x') c3)) * F x'
  have hQ0 : ∀ c3, 0 ≤ Q c3 := fun c3 => mul_nonneg (by positivity)
    (Finset.sum_nonneg fun x' _ => by have := hs_nonneg (N := N) (f x'); positivity)
  -- the outer factor
  have hsum : Gp' S.toDomSeq (cfgX (X0 S)) (W1 S) ΩD (QpL S (W1 S) (unblkL S ΩD d)) =
      ∑ c : BD S ΩD, Gp' S.toDomSeq (cfgX (X0 S)) (W1 S) ΩD (lamZ S (W1 S) c.1 (Zc c)) := by
    rw [← map_sum, sum_lamZ]; rfl
  have hG : ∀ c : BD S ΩD, hs (Gp' S.toDomSeq (cfgX (X0 S)) (W1 S) ΩD (lamZ S (W1 S) c.1 (Zc c)) x) ≤
      2 * Cvv * (S.L : ℝ) ^ (2 * jj y) * Real.exp (-(ρ * S.dF y c.1)) * ((S.L : ℝ) ^ (4 * jj c.1))⁻¹ * ‖d.ofLp c‖ := by
    intro c
    have hc := (BD_sub S ΩD) c.2
    have hZ : hs (Zc c) = ((S.L : ℝ) ^ (4 * jj c.1))⁻¹ * hs (proj (d.ofLp c)) := by
      simp only [Zc]
      rw [RegularAverages.hs_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have h := H0.KB_Gp' y hy c.1 hc (lamZ S (W1 S) c.1 (Zc c)) (2 * Real.sqrt N * hs (Zc c))
      (by have := hs_nonneg (N := N) (Zc c); positivity) (lamZ_supp S (W1 S) hc _) (lamZ_bound S (wbound_triv S) hc _)
      x (mem_blk_bc S x)
    simp only [zero_mul, pow_zero, mul_one] at h
    rw [hZ] at h
    refine h.trans (le_of_eq ?_)
    rw [norm_eq_proj (d.ofLp c)]
    ring
  -- the block function `d`
  have hd : ∀ c : BD S ΩD, ‖d.ofLp c‖ ≤ k0 ^ 2 * CT * cc * Real.sqrt N *
      ∑ c3 : BD S ΩD, Real.exp (-(θ / 4 * S.dF c.1 c3.1)) * Q c3.1 := by
    intro c
    refine (H.Tinv_diff_le hRMb hRMs4 hsmallT hsmallT0 hRMa ν c).trans ?_
    have hν : ∀ c3 : BD S ΩD, ‖ν.ofLp c3‖ ≤ Real.sqrt N * Q c3.1 := by
      intro c3
      have e : ‖ν.ofLp c3‖ = Real.sqrt N * hs (g c3.1) := by
        rw [show ν.ofLp c3 = emb (g c3.1) from rfl, norm_emb]
      rw [e]
      exact mul_le_mul_of_nonneg_left (H0.QG_bound ((BD_sub S ΩD) c3.2) f) hN.le
    have hM := H.chain_mid hRMq hRMq2 c
    calc k0 ^ 2 * CT * ∑ c3 : BD S ΩD, (∑ c1 : BD S ΩD, ∑ c2 : BD S ΩD, Real.exp (-(θ * S.dF c.1 c1.1)) *
          Real.exp (-(1 / 32 * δ * S.dF c1.1 c2.1)) * Real.exp (-(θ * S.dF c2.1 c3.1))) * ‖ν.ofLp c3‖
        ≤ k0 ^ 2 * CT * ∑ c3 : BD S ΩD, (cc * Real.exp (-(θ / 4 * S.dF c.1 c3.1))) * (Real.sqrt N * Q c3.1) := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun c3 _ => ?_) (by positivity)
          exact mul_le_mul (hM c3) (hν c3) (norm_nonneg _) (by positivity)
      _ = _ := by
          rw [Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun c3 _ => by ring
  -- the chain sum
  set E : Site NF → Site NF → Site NF → ℝ := fun y' c c3 =>
    (S.L : ℝ) ^ (2 * jj y) * Real.exp (-(ρ * S.dF y c)) * ((S.L : ℝ) ^ (4 * jj c))⁻¹ *
      (Real.exp (-(θ / 4 * S.dF c c3)) * ((S.L : ℝ) ^ (4 * jj c3))⁻¹ * (S.L : ℝ) ^ (2 * jj y') *
        Real.exp (-(ρ * S.dF c3 y')))
  have hE0 : ∀ y' c c3, 0 ≤ E y' c c3 := fun y' c c3 => by positivity
  have hchain : ∀ x', ∑ c : BD S ΩD, ∑ c3 : BD S ΩD, E (bc S.toDomSeq x') c.1 c3.1 ≤
      (S.L : ℝ) ^ (12 : ℝ) * (S.toContSeq).c1 (1 / 2) (θ / 4) * (S.toContSeq).c1 (1 / 2) (7 / 16 * (θ / 4)) *
        ((S.L : ℝ) ^ (4 * jj (bc S.toDomSeq x')))⁻¹ * Real.exp (-(7 / 32 * (θ / 4) * S.dF y (bc S.toDomSeq x'))) := by
    intro x'
    refine le_trans ?_ (chainP S (show 0 < θ / 4 by positivity) (show 9 / 8 * (θ / 4) ≤ ρ by simp only [ρ]; linarith)
      hRMs8 hRMc8 hy (y' := bc S.toDomSeq x'))
    refine (Finset.sum_le_sum fun c _ => sum_BD_le_detB S (fun c3 => E (bc S.toDomSeq x') c.1 c3)
      fun c3 => hE0 _ _ _).trans ?_
    exact sum_BD_le_detB S (fun c => ∑ c3 ∈ detB S.toDomSeq, E (bc S.toDomSeq x') c c3)
      fun c => Finset.sum_nonneg fun c3 _ => hE0 _ _ _
  -- assemble
  set K := 2 * Cvv * (k0 ^ 2 * CT * cc * Real.sqrt N) * (2 * Real.sqrt N * Cvv)
  have hK : 0 ≤ K := by positivity
  have hstep : hs (Gp' S.toDomSeq (cfgX (X0 S)) (W1 S) ΩD (QpL S (W1 S) (unblkL S ΩD d)) x) ≤
      ∑ c : BD S ΩD, ∑ c3 : BD S ΩD, ∑ x', K * E (bc S.toDomSeq x') c.1 c3.1 * F x' := by
    rw [hsum, Finset.sum_apply]
    refine (RegularAverages.hs_sum_le _ _).trans (Finset.sum_le_sum fun c _ => (hG c).trans ?_)
    have hA : 0 ≤ 2 * Cvv * (S.L : ℝ) ^ (2 * jj y) * Real.exp (-(ρ * S.dF y c.1)) * ((S.L : ℝ) ^ (4 * jj c.1))⁻¹ := by
      positivity
    refine (mul_le_mul_of_nonneg_left (hd c) hA).trans (le_of_eq ?_)
    simp only [Q, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c3 _ => Finset.sum_congr rfl fun x' _ => ?_
    simp only [E, K, F]
    rw [S.dF_comm (bc S.toDomSeq x') c3.1]
    ring
  have hswap : ∑ c : BD S ΩD, ∑ c3 : BD S ΩD, ∑ x', K * E (bc S.toDomSeq x') c.1 c3.1 * F x' =
      ∑ x', K * F x' * ∑ c : BD S ΩD, ∑ c3 : BD S ΩD, E (bc S.toDomSeq x') c.1 c3.1 := by
    rw [Finset.sum_congr rfl fun c _ => Finset.sum_comm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun x' _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun c3 _ => by ring
  refine (hstep.trans (le_of_eq hswap)).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun x' _ => ?_
  have hF0 : 0 ≤ F x' := hs_nonneg _
  calc K * F x' * ∑ c : BD S ΩD, ∑ c3 : BD S ΩD, E (bc S.toDomSeq x') c.1 c3.1
      ≤ K * F x' * ((S.L : ℝ) ^ (12 : ℝ) * (S.toContSeq).c1 (1 / 2) (θ / 4) *
        (S.toContSeq).c1 (1 / 2) (7 / 16 * (θ / 4)) * ((S.L : ℝ) ^ (4 * jj (bc S.toDomSeq x')))⁻¹ *
          Real.exp (-(7 / 32 * (θ / 4) * S.dF y (bc S.toDomSeq x')))) :=
        mul_le_mul_of_nonneg_left (hchain x') (by positivity)
    _ = _ := by simp only [K, F]; unfold CPdB4; ring

/-- The constant of the kernel of `P(𝐔) - P(id)`. -/
def CPd (S : SeqDom) (N : ℕ) (δ α₁ η : ℝ) : ℝ :=
  CPdA S N δ α₁ η + CPdB1 S N δ α₁ η + CPdB2 S N δ η + CPdB3 S N δ η + CPdB4 S N δ α₁ η

/-- The telescoping of `P(𝐔) - P(id)` into the five terms `A`, `B₁`, `B₂`, `B₃`, `B₄`. -/
lemma Pop_sub_eq (f : Site NF → Mat) :
    (Pop S X W ΩD - Pop S (X0 S) (W1 S) ΩD : Module.End ℂ (Site NF → Mat)) f =
      (Gp' S.toDomSeq (cfgX X) W ΩD - Gp' S.toDomSeq (cfgX (X0 S)) (W1 S) ΩD : Module.End ℂ (Site NF → Mat))
          (QpL S W (unblkL S ΩD (Tinv S X W ΩD (blkL S ΩD (avgL S W (Gp' S.toDomSeq (cfgX X) W ΩD f)))))) +
        Gp' S.toDomSeq (cfgX (X0 S)) (W1 S) ΩD (QpL S W (unblkL S ΩD (Tinv S X W ΩD (blkL S ΩD (avgL S W
          ((Gp' S.toDomSeq (cfgX X) W ΩD - Gp' S.toDomSeq (cfgX (X0 S)) (W1 S) ΩD : Module.End ℂ (Site NF → Mat))
            f)))))) +
        Gp' S.toDomSeq (cfgX (X0 S)) (W1 S) ΩD (QpL S W (unblkL S ΩD (Tinv S X W ΩD (blkL S ΩD
          (avgL S W (Gp' S.toDomSeq (cfgX (X0 S)) (W1 S) ΩD f) -
            avgL S (W1 S) (Gp' S.toDomSeq (cfgX (X0 S)) (W1 S) ΩD f)))))) +
        Gp' S.toDomSeq (cfgX (X0 S)) (W1 S) ΩD
          (QpL S W (unblkL S ΩD (Tinv S X W ΩD (blkL S ΩD (avgL S (W1 S) (Gp' S.toDomSeq (cfgX (X0 S)) (W1 S) ΩD f))))) -
            QpL S (W1 S) (unblkL S ΩD (Tinv S X W ΩD (blkL S ΩD (avgL S (W1 S)
              (Gp' S.toDomSeq (cfgX (X0 S)) (W1 S) ΩD f)))))) +
        Gp' S.toDomSeq (cfgX (X0 S)) (W1 S) ΩD (QpL S (W1 S) (unblkL S ΩD
          (Tinv S X W ΩD (blkL S ΩD (avgL S (W1 S) (Gp' S.toDomSeq (cfgX (X0 S)) (W1 S) ΩD f))) -
            Tinv S (X0 S) (W1 S) ΩD (blkL S ΩD (avgL S (W1 S) (Gp' S.toDomSeq (cfgX (X0 S)) (W1 S) ΩD f)))))) := by
  simp only [Pop, LinearMap.sub_apply, LinearMap.comp_apply, map_sub]
  abel

/-- **The kernel of `P(𝐔) - P(id)`**: `|(P(𝐔) - P(id))f(x)| ≤ C_{Pd}Σ_{x'}a_{y(x')}^{-4}e^{-(7/32)(θ_B/4)d(y(x), y(x'))}|f(x')|`,
the sum of the five terms at the slowest of their rates. -/
theorem Pdiff [NeZero N]
    (hRMb : (S.toContSeq).r1 (1 / 2) (1 / 32 * δ) ≤ RMS) (hRMs4 : 32 * Real.log S.L / (1 / 4 * δ) ≤ RMS)
    (hsmallT : CTd S N δ α₁ η * (S.toContSeq).c1 (1 / 2) (1 / 32 * δ) ≤ gammaB N / 4)
    (hsmallT0 : CTd S N δ 0 0 * (S.toContSeq).c1 (1 / 2) (1 / 32 * δ) ≤ gammaB N / 4)
    (hRMθs : 32 * Real.log S.L / (thetaB S N δ / 2) ≤ RMS)
    (hRMθc : (S.toContSeq).r1 (1 / 2) (7 / 16 * thetaB S N δ) ≤ RMS)
    (hRMc : (S.toContSeq).r1 (1 / 2) (3 / 4 * δ) ≤ RMS)
    (hRMa : (S.toContSeq).r1 (1 / 2) (1 / 8 * δ) ≤ RMS)
    (hRMq : (S.toContSeq).r1 (1 / 2) (thetaB S N δ) ≤ RMS)
    (hRMq2 : (S.toContSeq).r1 (1 / 2) (thetaB S N δ / 2) ≤ RMS)
    (hRMs8 : 32 * Real.log S.L / (thetaB S N δ / 4 / 2) ≤ RMS)
    (hRMc8 : (S.toContSeq).r1 (1 / 2) (7 / 16 * (thetaB S N δ / 4)) ≤ RMS) (f : Site NF → Mat) (x : Site NF) :
    hs ((Pop S X W ΩD - Pop S (X0 S) (W1 S) ΩD : Module.End ℂ (Site NF → Mat)) f x) ≤
      CPd S N δ α₁ η * ∑ x', ((S.L : ℝ) ^ (4 * jj (bc S.toDomSeq x')))⁻¹ *
        Real.exp (-(7 / 32 * (thetaB S N δ / 4) * S.dF (bc S.toDomSeq x) (bc S.toDomSeq x'))) * hs (f x') := by
  have hθ := H.thetaB_pos (N := N)
  set θ := thetaB S N δ
  set E : ℝ → ℝ := fun r => ∑ x', ((S.L : ℝ) ^ (4 * jj (bc S.toDomSeq x')))⁻¹ *
    Real.exp (-(r * S.dF (bc S.toDomSeq x) (bc S.toDomSeq x'))) * hs (f x')
  have hmono : E (7 / 32 * θ) ≤ E (7 / 32 * (θ / 4)) := by
    refine Finset.sum_le_sum fun x' _ => ?_
    have hd := S.dF_nonneg (bc S.toDomSeq x) (bc S.toDomSeq x')
    have h1 : Real.exp (-(7 / 32 * θ * S.dF (bc S.toDomSeq x) (bc S.toDomSeq x'))) ≤
        Real.exp (-(7 / 32 * (θ / 4) * S.dF (bc S.toDomSeq x) (bc S.toDomSeq x'))) :=
      Real.exp_le_exp.2 (by nlinarith)
    have := hs_nonneg (N := N) (f x')
    gcongr
  have hE0 : 0 ≤ E (7 / 32 * θ) :=
    Finset.sum_nonneg fun x' _ => by have := hs_nonneg (N := N) (f x'); positivity
  have hA := H.PdiffA hRMb hRMs4 hsmallT hRMθs hRMθc hRMc f x
  have hB1 := H.PdiffB1 hRMb hRMs4 hsmallT hRMθs hRMθc hRMc f x
  have hB2 := H.PdiffB2 hRMb hRMs4 hsmallT hRMθs hRMθc f x
  have hB3 := H.PdiffB3 hRMb hRMs4 hsmallT hRMθs hRMθc f x
  have hB4 := H.PdiffB4 hRMb hRMs4 hsmallT hsmallT0 hRMa hRMq hRMq2 hRMs8 hRMc8 f x
  have hc1 : ∀ r, 0 ≤ (S.toContSeq).c1 (1 / 2) r := fun r => by unfold Summation.ContSeq.c1; positivity
  have hL : (0 : ℝ) ≤ S.L := by positivity
  have hγ : 0 ≤ 2 / gammaB N := by unfold gammaB; positivity
  have hCv := H.Cv_nn
  have hCD := H.CD_nn
  have hCT := H.CTd_nn
  have hη := H.hη
  have hsq := Real.sqrt_nonneg (N : ℝ)
  have hrp := Real.rpow_nonneg hL (12 : ℝ)
  have cA : 0 ≤ CPdA S N δ α₁ η := by unfold CPdA; exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hCD) (mul_nonneg (by positivity) hCv)) hγ) hrp) (hc1 (thetaB S N δ))) (hc1 (7 / 16 * thetaB S N δ))
  have cB1 : 0 ≤ CPdB1 S N δ α₁ η := by unfold CPdB1; exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hCv) (mul_nonneg (by positivity) hCD)) hγ) hrp) (hc1 (thetaB S N δ))) (hc1 (7 / 16 * thetaB S N δ))
  have cB2 : 0 ≤ CPdB2 S N δ η := by unfold CPdB2; exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hCv) (mul_nonneg (mul_nonneg (by positivity) hη) hCv)) hγ) hrp) (hc1 (thetaB S N δ))) (hc1 (7 / 16 * thetaB S N δ))
  have cB3 : 0 ≤ CPdB3 S N δ η := by unfold CPdB3; exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hη) hCv) (mul_nonneg (by positivity) hCv)) hγ) hrp) (hc1 (thetaB S N δ))) (hc1 (7 / 16 * thetaB S N δ))
  rw [H.Pop_sub_eq]
  have h5 : ∀ a b c d e : Mat, hs (a + b + c + d + e) ≤ hs a + hs b + hs c + hs d + hs e := fun a b c d e => by
    have := hs_add_le (N := N) (a + b + c + d) e
    have := hs_add_le (N := N) (a + b + c) d
    have := hs_add_le (N := N) (a + b) c
    have := hs_add_le (N := N) a b
    linarith
  set E1 := E (7 / 32 * θ)
  set E2 := E (7 / 32 * (θ / 4))
  have hsum : CPdA S N δ α₁ η * E1 + CPdB1 S N δ α₁ η * E1 + CPdB2 S N δ η * E1 + CPdB3 S N δ η * E1 +
      CPdB4 S N δ α₁ η * E2 ≤ CPd S N δ α₁ η * E2 := by
    have eA := mul_le_mul_of_nonneg_left hmono cA
    have eB1 := mul_le_mul_of_nonneg_left hmono cB1
    have eB2 := mul_le_mul_of_nonneg_left hmono cB2
    have eB3 := mul_le_mul_of_nonneg_left hmono cB3
    unfold CPd
    linarith
  simp only [Pi.add_apply]
  exact (h5 _ _ _ _ _).trans ((add_le_add (add_le_add (add_le_add (add_le_add hA hB1) hB2) hB3) hB4).trans hsum)

end ScalarHyp

end SFBounds
end CoreLean

end
