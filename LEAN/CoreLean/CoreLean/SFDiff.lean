/-
`prop:sf-block` of BALABAN_CORE.tex (`d4ef86a9a5fd`), the comparison with the trivial field on the fine lattice
(`a₀ = 1`): `G'_𝐔 - G'_id = G'_𝐔(Δ'_id - Δ'_𝐔)G'_id` with `(Δ'_id - Δ'_𝐔)f = D^*_𝐔g - r + (Q'^*𝖺Q'_id - Q'^*𝖺Q'_W)f`
(`cinv_sub`, `DeltaS_eq`, `lap_diff`), and the bounds (iv) of `G'` at both configurations give

`|((G'_𝐔 - G'_id)λ)(x)| ≤ C_Da_y²e^{-(δ/4)d(y, y')}Λ`, `C_D = O(α₁ + η)` (`diff_KB`),

which replaces the lemma of Schwarz in the core's proof (the smallness is linear in `α₁` and in the bound `η` of the
transports, with no holomorphy in the field).

* `ncon_diff`: `|(Q'^*𝖺Q'_id f - Q'^*𝖺Q'_Wf)(z)| ≤ (1 + 4N)ηa_{j(z)}⁻²max_{Δ(y(z))}|f|`.
* `diff_KB`: the block kernel bound of the difference.
-/
import CoreLean.SFDiffPre

open Finset Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean
namespace SFBounds

open Lattices SeqDom Blocks SmallFieldBlocks SFBox SFBox.SeqDomBox SmallFieldDecay SmallFieldCoercivity
  SequenceOperators CompressedInverse SFLocal

variable (S : SeqDom) {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ
local notation "NF" => SequenceAverages.N0 S
local notation "RMS" => ((S.R * S.L ^ S.mM : ℕ) : ℝ)
set_option quotPrecheck false in
local notation "jj" => (S.toDomSeq).sc

/-- **The difference of the constraint operators.** -/
lemma ncon_diff [NeZero N] {W : Site NF → Site NF → GLN} {η : ℝ} (hη : 0 ≤ η)
    (hW1 : ∀ y ∈ detB S.toDomSeq, ∀ x ∈ Blk S.toDomSeq ((S.toDomSeq).sc y) y, ∀ Z : Mat,
      hs (Ad (W y x) Z - Z) ≤ η * hs Z) (hW : WBound S W) (f : Site NF → Mat) (z : Site NF) {M : ℝ}
    (hM : ∀ x' ∈ Blk S.toDomSeq (jj (bc S.toDomSeq z)) (bc S.toDomSeq z), hs (f x') ≤ M) :
    hs (Ncon S.toDomSeq (W1 S) f z - Ncon S.toDomSeq W f z) ≤ (1 + 4 * N) * η * ((S.L : ℝ) ^ (2 * jj z))⁻¹ * M := by
  set y := bc S.toDomSeq z
  have hy : y ∈ detB S.toDomSeq := bc_mem_detB S z
  have hzb : z ∈ Blk S.toDomSeq (jj y) y := mem_blk_bc S z
  have hsc : jj y = jj z := sc_bc _ z
  have hL : (0 : ℝ) < S.L := by exact_mod_cast S.Lpos
  have hL1 : 1 ≤ S.L := by have := S.three_le_L; omega
  have hM0 : 0 ≤ M := (hs_nonneg _).trans (hM z hzb)
  obtain ⟨ha1, ha2⟩ := aseq_mem S.L hL1 (jj z)
  set c : ℝ := aseq 1 S.L (jj z) * ((S.L : ℝ) ^ (2 * jj z))⁻¹
  have hc0 : 0 ≤ c := by have := aseq_pos (aa := 1) one_pos S.L (jj z); positivity
  have hc1 : c ≤ ((S.L : ℝ) ^ (2 * jj z))⁻¹ := by
    calc c ≤ 1 * ((S.L : ℝ) ^ (2 * jj z))⁻¹ := by simp only [c]; gcongr
      _ = _ := one_mul _
  have e : Ncon S.toDomSeq (W1 S) f z - Ncon S.toDomSeq W f z =
      ((c : ℝ) : ℂ) • ((avgW S.toDomSeq (W1 S) y f - avgW S.toDomSeq W y f) +
        (avgW S.toDomSeq W y f - Ad (W y z)⁻¹ (avgW S.toDomSeq W y f))) := by
    simp only [Ncon, c]
    rw [← smul_sub]
    congr 1
    simp only [W1, inv_one, Ad, Units.val_one, one_mul, mul_one]
    abel
  rw [e, RegularAverages.hs_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc0]
  -- the two differences
  have h1 : hs (avgW S.toDomSeq (W1 S) y f - avgW S.toDomSeq W y f) ≤ η * M := by
    rw [avgW_blk S.toDomSeq _ hy, avgW_blk S.toDomSeq _ hy, ← smul_sub, ← sum_sub_distrib, RegularAverages.hs_smul]
    simp only [toDomSeq_L, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (pow_pos hL _)]
    have hs1 : hs (∑ x ∈ Blk S.toDomSeq (jj y) y, (Ad (W1 S y x) (f x) - Ad (W y x) (f x))) ≤
        ∑ _x ∈ Blk S.toDomSeq (jj y) y, η * M := by
      refine (RegularAverages.hs_sum_le _ _).trans (sum_le_sum fun x hx => ?_)
      rw [show Ad (W1 S y x) (f x) - Ad (W y x) (f x) = -(Ad (W y x) (f x) - f x) by simp [Ad], SupportCont.hs_neg]
      exact (hW1 y hy x hx (f x)).trans (mul_le_mul_of_nonneg_left (hM x hx) hη)
    rw [sum_const, nsmul_eq_mul, card_Blk S hy] at hs1
    calc ((S.L : ℝ) ^ (4 * jj y))⁻¹ * hs (∑ x ∈ Blk S.toDomSeq (jj y) y, (Ad (W1 S y x) (f x) - Ad (W y x) (f x)))
        ≤ ((S.L : ℝ) ^ (4 * jj y))⁻¹ * ((S.L : ℝ) ^ (4 * jj y) * (η * M)) := by gcongr
      _ = η * M := by field_simp
  have h2 : hs (avgW S.toDomSeq W y f - Ad (W y z)⁻¹ (avgW S.toDomSeq W y f)) ≤ 4 * N * η * M := by
    set A := avgW S.toDomSeq W y f
    have hA := avgW_le S hW hy hM
    have e2 : A - Ad (W y z)⁻¹ A = Ad (W y z)⁻¹ (Ad (W y z) A - A) := by rw [Ad_sub, Ad_inv_Ad]
    rw [e2]
    have h3 := (hW y hy z hzb (Ad (W y z) A - A)).2
    have h4 := hW1 y hy z hzb A
    have hN : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt (Nat.cast_nonneg _)
    have hsN : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
    calc hs (Ad (W y z)⁻¹ (Ad (W y z) A - A)) ≤ 2 * Real.sqrt N * hs (Ad (W y z) A - A) := h3
      _ ≤ 2 * Real.sqrt N * (η * (2 * Real.sqrt N * M)) := by gcongr; exact h4.trans (by gcongr)
      _ = 4 * (Real.sqrt N * Real.sqrt N) * η * M := by ring
      _ = 4 * N * η * M := by rw [hN]
  calc c * hs ((avgW S.toDomSeq (W1 S) y f - avgW S.toDomSeq W y f) +
        (avgW S.toDomSeq W y f - Ad (W y z)⁻¹ (avgW S.toDomSeq W y f)))
      ≤ ((S.L : ℝ) ^ (2 * jj z))⁻¹ * (η * M + 4 * N * η * M) := by
        exact mul_le_mul hc1 ((hs_add_le _ _).trans (add_le_add h1 h2)) (hs_nonneg _) (by positivity)
    _ = _ := by ring

/-- The constant `C_D` of the difference. -/
def CD (S : SeqDom) (N : ℕ) (δ α₁ η : ℝ) : ℝ :=
  Cv S δ (Csc S N) (4 * N * (S.L : ℝ) ^ 4) * (S.L : ℝ) ^ (4 : ℝ) * (S.toContSeq).c1 (1 / 2) (3 / 4 * δ) *
    (18 * α₁ * (S.L : ℝ) ^ 3 * Cv S δ (Csc S N) (4 * N * (S.L : ℝ) ^ 4) * (S.L : ℝ) ^ (4 : ℝ) +
      ((1 + 4 * N) * η * Cv S δ (Csc S N) (4 * N * (S.L : ℝ) ^ 4) +
        144 * α₁ * (S.L : ℝ) ^ 2 * Cg S δ (Csc S N) (4 * N * (S.L : ℝ) ^ 4) 0))

namespace ScalarHyp

variable {S} {X : Fin 4 → Site (SequenceAverages.N0 S) → Matrix (Fin N) (Fin N) ℂ} {α₁ : ℝ}
  {W : Site (SequenceAverages.N0 S) → Site (SequenceAverages.N0 S) → (Matrix (Fin N) (Fin N) ℂ)ˣ} {η : ℝ}
  {ΩD : Set (Site (SequenceAverages.N0 S))} {δ : ℝ}
  (H : ScalarHyp S X α₁ W η ΩD δ)
include H

lemma exp_near {a b : ℝ} (hab : b ≤ a + (S.L + 4)) :
    Real.exp (-(7 / 8 * δ * a)) ≤ 3 * Real.exp (-(7 / 8 * δ * b)) := by
  have hδ := H.hδ0
  have hδL := H.hδ
  have hL : (3 : ℝ) ≤ S.L := by exact_mod_cast S.three_le_L
  have h1 : 7 / 8 * δ * (S.L + 4) ≤ 1 := by
    have : δ * (S.L + 4) ≤ 1 / (128 * S.L) * (S.L + 4) := mul_le_mul_of_nonneg_right hδL (by linarith)
    have e : 1 / (128 * (S.L : ℝ)) * (S.L + 4) ≤ 1 := by
      rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]; linarith
    nlinarith
  calc Real.exp (-(7 / 8 * δ * a)) ≤ Real.exp (-(7 / 8 * δ * b) + 1) := Real.exp_le_exp.2 (by nlinarith)
    _ = Real.exp (-(7 / 8 * δ * b)) * Real.exp 1 := Real.exp_add _ _
    _ ≤ Real.exp (-(7 / 8 * δ * b)) * 3 := by
        gcongr; have := Real.exp_one_lt_d9; linarith
    _ = _ := by ring

lemma Cv_nn [NeZero N] : 0 ≤ Cv S δ (Csc S N) (4 * N * (S.L : ℝ) ^ 4) := H.Cv_nonneg

lemma Cg_nn [NeZero N] : 0 ≤ Cg S δ (Csc S N) (4 * N * (S.L : ℝ) ^ 4) 0 := by
  have := H.hδ0
  have hc1 : 0 ≤ (S.toContSeq).c1 (1 / 2) δ := by unfold Summation.ContSeq.c1; positivity
  unfold Cg Cd C2 CTh CF Ksf Ksfb Csc
  have := KH_ge (1 / 2) (by norm_num); have := KD_ge (1 / 2) (by norm_num) (by norm_num)
  positivity

/-- **The block kernel bound of `G'_𝐔 - G'_id`.** -/
theorem diff_KB [NeZero N] (hRMc : (S.toContSeq).r1 (1 / 2) (3 / 4 * δ) ≤ RMS) :
    KB S (Gp' S.toDomSeq (cfgX X) W ΩD - Gp' S.toDomSeq (cfgX (X0 S)) (W1 S) ΩD) (CD S N δ α₁ η) (1 / 4 * δ) 2 0 := by
  intro y hy y' hy' lam Λ hΛ hsupp hbd x hx
  have H0 := H.triv (N := N)
  have hL : (3 : ℝ) ≤ S.L := by exact_mod_cast S.three_le_L
  have hL0 : (0 : ℝ) < S.L := by linarith
  have hRM1 := hRM1_of S H.hRM8
  have hδ := H.hδ0
  have hα0 := H.hα0
  have hCv := H.Cv_nn
  have hCg := H.Cg_nn
  set Cv' := Cv S δ (Csc S N) (4 * N * (S.L : ℝ) ^ 4)
  set Cg0 := Cg S δ (Csc S N) (4 * N * (S.L : ℝ) ^ 4) 0
  set U := cfgX (N := N) X
  set GU := Gp' S.toDomSeq U W ΩD
  set G0 := Gp' S.toDomSeq (cfgX (N := N) (X0 S)) (W1 S) ΩD
  set f := G0 lam
  -- the resolvent identity and the divergence form
  have hres : GU lam - G0 lam = GU (((DeltaS S.toDomSeq (cfgX (X0 S)) (W1 S) - DeltaS S.toDomSeq U W : Module.End ℂ (Site NF → Mat)) f)) :=
    cinv_sub (piD_idem ΩD) H.hK H0.hK lam
  have hLap : ∀ (V : Config N NF) (v : Site NF → Mat) z, Ds1 a1 V (D0L a1 V v) z = Lap 1 V v z := fun _ _ _ => rfl
  have hT : ((DeltaS S.toDomSeq (cfgX (X0 S)) (W1 S) - DeltaS S.toDomSeq U W : Module.End ℂ (Site NF → Mat)) f) =
      Ds1L a1 U (gdiv S U f) +
        fun z => (Ncon S.toDomSeq (W1 S) f z - Ncon S.toDomSeq W f z) - rdiv S U f z := by
    funext z
    have hl := lap_diff S X f z
    simp only [LinearMap.sub_apply, DeltaS_eq, Pi.add_apply, Pi.sub_apply, Ds1L_apply, hLap]
    rw [show Ds1 a1 U (gdiv S U f) z = Ds1 1 U (gdiv S U f) z from rfl,
      show Lap 1 U f z = Lap 1 (cfgX (X0 S)) f z + (-Ds1 1 U (gdiv S U f) z + rdiv S U f z) by rw [← hl]; abel]
    abel
  -- the block bounds of the sources
  have hX32 : ∀ μ w, ‖X μ w‖ ≤ 1 / 32 := fun μ w => by
    have h := (X_bond_le S H.hX hα0 hRM1 w μ).1
    have hp : ((S.L : ℝ) ^ jj w)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith))
    have hα := H.hα
    have : α₁ * S.L ≤ 1 / 32 := by nlinarith
    calc ‖X μ w‖ ≤ α₁ * S.L * ((S.L : ℝ) ^ jj w)⁻¹ := h
      _ ≤ α₁ * S.L * 1 := by gcongr
      _ ≤ 1 / 32 := by linarith
  have hfv : ∀ w, hs (f w) ≤ Cv' * Real.exp (-(7 / 8 * δ * S.dF (bc S.toDomSeq w) y')) *
      ((S.L : ℝ) ^ (2 * jj (bc S.toDomSeq w)) * Λ) :=
    fun w => H0.values (bc_mem_detB S w) hy' (mem_blk_bc S w) hΛ hsupp hbd
  have hg : ∀ μ, BlkBd S (gdiv S U f μ) (18 * α₁ * (S.L : ℝ) ^ 3 * Cv' * Λ) (7 / 8 * δ) 1 0 y' := by
    intro μ y'' hy'' z hz
    have hsz := sc_of_mem_blk S hy'' hz
    have hXz := (X_bond_le S H.hX hα0 hRM1 z μ).1
    rw [hsz] at hXz
    have h1 := gdiv_bound S f μ z (hX32 μ z)
    obtain ⟨hs1, -, -, -⟩ := nbr_scale S hRM1 z μ
    have hd := nbr_dist S hRM1 hy'' hz (z + unit _ μ) (dF_unit_le S hRM1 z μ).1
    have hsc3 : jj (bc S.toDomSeq (z + unit _ μ)) = jj (z + unit _ μ) := sc_bc _ _
    have ht := S.dF_triangle y'' (bc S.toDomSeq (z + unit _ μ)) y'
    have he := H.exp_near (a := S.dF (bc S.toDomSeq (z + unit _ μ)) y') (b := S.dF y'' y') (by linarith)
    have hp : (S.L : ℝ) ^ (2 * jj (bc S.toDomSeq (z + unit _ μ))) ≤ (S.L : ℝ) ^ 2 * (S.L : ℝ) ^ (2 * jj y'') := by
      rw [hsc3, ← pow_add]; exact pow_le_pow_right₀ (by linarith) (by omega)
    have hfz := hfv (z + unit _ μ)
    have hfz' : hs (f (z + unit _ μ)) ≤ Cv' * (3 * Real.exp (-(7 / 8 * δ * S.dF y'' y'))) *
        ((S.L : ℝ) ^ 2 * (S.L : ℝ) ^ (2 * jj y'') * Λ) :=
      hfz.trans (by gcongr)
    have epow : (S.L : ℝ) ^ (2 * jj y'') = (S.L : ℝ) ^ jj y'' * (S.L : ℝ) ^ jj y'' := by rw [← pow_add]; ring_nf
    have hq : (S.L : ℝ) ^ jj y'' ≠ 0 := by positivity
    calc hs (gdiv S U f μ z) ≤ 6 * ‖X μ z‖ * hs (f (z + unit _ μ)) := h1
      _ ≤ 6 * (α₁ * S.L * ((S.L : ℝ) ^ jj y'')⁻¹) * (Cv' * (3 * Real.exp (-(7 / 8 * δ * S.dF y'' y'))) *
          ((S.L : ℝ) ^ 2 * (S.L : ℝ) ^ (2 * jj y'') * Λ)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hXz (by norm_num)) hfz' (hs_nonneg _) (by positivity)
      _ = 18 * α₁ * (S.L : ℝ) ^ 3 * Cv' * Λ * (S.L : ℝ) ^ (1 * jj y'') * (S.L : ℝ) ^ (0 * jj y') *
          Real.exp (-(7 / 8 * δ * S.dF y'' y')) := by
        rw [epow, one_mul, zero_mul, pow_zero]; field_simp; ring
  have hv : BlkBd S (fun z => (Ncon S.toDomSeq (W1 S) f z - Ncon S.toDomSeq W f z) - rdiv S U f z)
      ((1 + 4 * N) * η * Cv' * Λ + 144 * α₁ * (S.L : ℝ) ^ 2 * Cg0 * Λ) (7 / 8 * δ) 0 0 y' := by
    intro y'' hy'' z hz
    obtain ⟨hsz, hbz⟩ := sc_mem_blk S.toDomSeq hy'' hz
    -- the constraint term
    have hM : ∀ x' ∈ Blk S.toDomSeq (jj (bc S.toDomSeq z)) (bc S.toDomSeq z),
        hs (f x') ≤ Cv' * Real.exp (-(7 / 8 * δ * S.dF y'' y')) * ((S.L : ℝ) ^ (2 * jj y'') * Λ) := by
      intro x' hx'
      rw [hbz] at hx'
      have := H0.values hy'' hy' hx' hΛ hsupp hbd
      exact this
    have hn := ncon_diff S H.hη H.hW1 H.hW f z hM
    rw [hsz] at hn
    have hn' : hs (Ncon S.toDomSeq (W1 S) f z - Ncon S.toDomSeq W f z) ≤
        (1 + 4 * N) * η * Cv' * Λ * Real.exp (-(7 / 8 * δ * S.dF y'' y')) := by
      refine hn.trans (le_of_eq ?_)
      have hq : (S.L : ℝ) ^ (2 * jj y'') ≠ 0 := by positivity
      field_simp
    -- the remainder
    have hr := rdiv_bound S f z (fun μ => hX32 μ _)
    have hrμ : ∀ μ, 12 * ‖X μ (z - unit _ μ)‖ * hs (f z - f (z - unit _ μ)) ≤
        36 * α₁ * (S.L : ℝ) ^ 2 * Cg0 * Λ * Real.exp (-(7 / 8 * δ * S.dF y'' y')) := by
      intro μ
      have hXz := (X_bond_le S H.hX hα0 hRM1 (z - unit _ μ) μ).2
      rw [sub_add_cancel, hsz] at hXz
      set w := z - unit _ μ
      have hgr := H0.gradient (bc_mem_detB S w) hy' (mem_blk_bc S w) hΛ hsupp hbd μ
      have hdf : Dfw 1 (cfgX (X0 S)) μ f w = f z - f w := by
        simp [Dfw, cfgX, X0, Ad, w]
      rw [hdf] at hgr
      obtain ⟨-, -, -, hs4⟩ := nbr_scale S hRM1 z μ
      have hsc4 : jj (bc S.toDomSeq w) = jj w := sc_bc _ _
      have hd := nbr_dist S hRM1 hy'' hz w (dF_unit_le S hRM1 z μ).2
      have ht := S.dF_triangle y'' (bc S.toDomSeq w) y'
      have he := H.exp_near (a := S.dF (bc S.toDomSeq w) y') (b := S.dF y'' y') (by linarith)
      obtain ⟨-, -, hs3, -⟩ := nbr_scale S hRM1 z μ
      have hp : (S.L : ℝ) ^ jj (bc S.toDomSeq w) ≤ S.L * (S.L : ℝ) ^ jj y'' := by
        rw [hsc4, ← pow_succ']; rw [← hsz]; exact pow_le_pow_right₀ (by linarith) (by omega)
      have hgr' : hs (f z - f w) ≤ Cg0 * (3 * Real.exp (-(7 / 8 * δ * S.dF y'' y'))) *
          (S.L * (S.L : ℝ) ^ jj y'' * Λ) := hgr.trans (by gcongr)
      have hq : (S.L : ℝ) ^ jj y'' ≠ 0 := by positivity
      calc 12 * ‖X μ w‖ * hs (f z - f w) ≤ 12 * (α₁ * S.L * ((S.L : ℝ) ^ jj y'')⁻¹) *
            (Cg0 * (3 * Real.exp (-(7 / 8 * δ * S.dF y'' y'))) * (S.L * (S.L : ℝ) ^ jj y'' * Λ)) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hXz (by norm_num)) hgr' (hs_nonneg _) (by positivity)
        _ = 36 * α₁ * (S.L : ℝ) ^ 2 * Cg0 * Λ * Real.exp (-(7 / 8 * δ * S.dF y'' y')) := by field_simp; ring
    have hr' : hs (rdiv S U f z) ≤ 144 * α₁ * (S.L : ℝ) ^ 2 * Cg0 * Λ * Real.exp (-(7 / 8 * δ * S.dF y'' y')) := by
      refine hr.trans ((sum_le_sum fun μ _ => hrμ μ).trans (le_of_eq ?_))
      simp; ring
    simp only [zero_mul, pow_zero, mul_one]
    calc hs ((Ncon S.toDomSeq (W1 S) f z - Ncon S.toDomSeq W f z) - rdiv S U f z)
        ≤ hs (Ncon S.toDomSeq (W1 S) f z - Ncon S.toDomSeq W f z) + hs (rdiv S U f z) :=
          RegularAverages.hs_sub_le' _ _
      _ ≤ _ := by linarith
  -- the two applications of `G'_𝐔`
  have hgC : 0 ≤ 18 * α₁ * (S.L : ℝ) ^ 3 * Cv' * Λ :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hα0) (by positivity)) hCv) hΛ
  have hvC : 0 ≤ (1 + 4 * N) * η * Cv' * Λ + 144 * α₁ * (S.L : ℝ) ^ 2 * Cg0 * Λ :=
    add_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) H.hη) hCv) hΛ)
      (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hα0) (by positivity)) hCg) hΛ)
  have hA := KB_apply_star S H.KBS_Gp' hCv hgC hg (by norm_num) hδ (by positivity) (by linarith)
    (by linarith) H.hRMs hRMc hy hx (m := 3 / 4 * δ)
  have hB := KB_apply S H.KB_Gp' hCv hvC hv (by norm_num) hδ (by positivity) (by linarith)
    (by linarith) H.hRMs hRMc hy hx (m := 3 / 4 * δ)
  -- the scale shift `a_{y'} ≤ L⁴e^{δd/8}a_y`
  have hsh := S.scale_shift hδ H.hRMs (σ := ((1 : ℕ) : ℝ)) (by norm_num) y y'
  rw [Real.rpow_natCast, Real.rpow_natCast, pow_one, pow_one] at hsh
  have hc1 : 0 ≤ (S.toContSeq).c1 (1 / 2) (3 / 4 * δ) := by unfold Summation.ContSeq.c1; positivity
  show hs ((GU - G0) lam x) ≤ _
  rw [LinearMap.sub_apply, hres, hT, map_add, Pi.add_apply]
  refine (hs_add_le _ _).trans ?_
  have hexp : Real.exp (δ / 8 * S.dF y y') * Real.exp (-(3 / 4 * δ / 2 * S.dF y y')) =
      Real.exp (-(1 / 4 * δ * S.dF y y')) := by rw [← Real.exp_add]; ring_nf
  have hexp' : Real.exp (-(3 / 4 * δ / 2 * S.dF y y')) ≤ Real.exp (-(1 / 4 * δ * S.dF y y')) :=
    Real.exp_le_exp.2 (by have := S.dF_nonneg y y'; nlinarith)
  have hA' : hs (GU (Ds1L a1 U (gdiv S U f)) x) ≤ 18 * α₁ * (S.L : ℝ) ^ 3 * Cv' * Λ * Cv' * (S.L : ℝ) ^ (4 : ℝ) *
      (S.toContSeq).c1 (1 / 2) (3 / 4 * δ) * (S.L : ℝ) ^ (2 * jj y) * (S.L : ℝ) ^ (4 : ℝ) *
        Real.exp (-(1 / 4 * δ * S.dF y y')) := by
    refine hA.trans ?_
    simp only [add_zero, one_mul]
    rw [← hexp, show 2 * jj y = jj y + jj y by ring, pow_add]
    have : (S.L : ℝ) ^ jj y' ≤ (S.L : ℝ) ^ (4 : ℝ) * Real.exp (δ / 8 * S.dF y y') * (S.L : ℝ) ^ jj y := hsh
    calc 18 * α₁ * (S.L : ℝ) ^ 3 * Cv' * Λ * Cv' * (S.L : ℝ) ^ (4 : ℝ) * (S.toContSeq).c1 (1 / 2) (3 / 4 * δ) *
          (S.L : ℝ) ^ jj y * (S.L : ℝ) ^ jj y' * Real.exp (-(3 / 4 * δ / 2 * S.dF y y'))
        ≤ 18 * α₁ * (S.L : ℝ) ^ 3 * Cv' * Λ * Cv' * (S.L : ℝ) ^ (4 : ℝ) * (S.toContSeq).c1 (1 / 2) (3 / 4 * δ) *
          (S.L : ℝ) ^ jj y * ((S.L : ℝ) ^ (4 : ℝ) * Real.exp (δ / 8 * S.dF y y') * (S.L : ℝ) ^ jj y) *
          Real.exp (-(3 / 4 * δ / 2 * S.dF y y')) := by gcongr
      _ = _ := by ring
  have hB' : hs (GU (fun z => (Ncon S.toDomSeq (W1 S) f z - Ncon S.toDomSeq W f z) - rdiv S U f z) x) ≤
      ((1 + 4 * N) * η * Cv' * Λ + 144 * α₁ * (S.L : ℝ) ^ 2 * Cg0 * Λ) * Cv' * (S.L : ℝ) ^ (4 : ℝ) *
        (S.toContSeq).c1 (1 / 2) (3 / 4 * δ) * (S.L : ℝ) ^ (2 * jj y) * Real.exp (-(1 / 4 * δ * S.dF y y')) := by
    refine hB.trans ?_
    simp only [add_zero, zero_mul, pow_zero, mul_one]
    gcongr
  calc _ ≤ _ := add_le_add hA' hB'
    _ = _ := by unfold CD; simp only [zero_mul, pow_zero, mul_one]; ring

end ScalarHyp

end SFBounds
end CoreLean

end
