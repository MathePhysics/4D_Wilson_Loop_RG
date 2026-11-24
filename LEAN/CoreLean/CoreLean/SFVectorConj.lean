/-
`lem:sf-vector-decay` of BALABAN_CORE.tex (`bb3c43c53e37`), eq:sf-vector-conjugated on the torus, assembled from the
steps of "The trivial configuration" and "The complex field" on the fine lattice (`a₀ = 1`), with the comparison of
the constraint terms (step (4)) as the named input `hQ`.

* `inner_vL_herm`, `pairP_triv_eq`: `Re⟨A^*, ∂P(id)∂^*A⟩ = N‖P(id)∂^*A‖²`.
* `formU`: the form of `Δ_𝖺(𝐔) = D^*_𝐔D_𝐔 + D_𝐔D^*_𝐔 + Δ'(𝐔) - D_𝐔P(𝐔)D^*_𝐔 + Q^*𝖺Q` with a given constraint form.
* `conj_U`: `Re⟨(e^φA)^*, Δ_𝖺(𝐔)(e^{-φ}A)⟩ ≥ ((2^{13}C_loc)⁻¹ - E)N(A)²`, `E` the sum of the errors of the steps.
-/
import CoreLean.SFHessComp

open Finset Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean
namespace SFBounds

open Lattices SeqDom Blocks SmallFieldBlocks SFBox SFBox.SeqDomBox SmallFieldDecay SmallFieldCoercivity
  SequenceOperators CompressedInverse SFLocal ConcretePairing PartitionUnity

variable (S : SeqDom) {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ
local notation "NF" => SequenceAverages.N0 S
local notation "RMS" => ((S.R * S.L ^ S.mM : ℕ) : ℝ)
set_option quotPrecheck false in
local notation "jj" => (S.toDomSeq).sc

lemma inner_vL_herm [NeZero N] (f g : Site NF → Mat) : inner ℂ (vL S f) (vL S g) = N * herm S f g := by
  rw [inner_vL, herm_eq, mul_sum]
  refine sum_congr rfl fun x _ => ?_
  rw [inner_emb, ntr, ← mul_assoc, mul_inv_cancel₀ (Nat.cast_ne_zero.2 (NeZero.ne N)), one_mul]

/-- **The projection term at the trivial configuration**: `Re⟨A^*, ∂P(id)∂^*A⟩ = N‖P(id)∂^*A‖²` (`P(id)` is
self-adjoint and idempotent). -/
lemma pairP_triv_eq [NeZero N] (ΩD : Set (Site NF)) (A : Fin 4 → Site NF → Mat) :
    (pairP S (X0 S) (W1 S) ΩD A A).re =
      N * ∑ x, hs2 (Pop S (X0 S) (W1 S) ΩD (Ds1L a1 (cfgX (X0 S)) A) x) := by
  have hb := hb_triv (N := N) (S := S) ΩD
  set f := Ds1L a1 (cfgX (X0 S)) A
  set P := Pop S (X0 S) (W1 S) ΩD
  have e : pairP S (X0 S) (W1 S) ΩD A A = inner ℂ (vL S (P f)) (vL S (P f)) := by
    unfold pairP pair1V
    rw [pair_Ds_triv, inner_vL_herm, inner_vL_herm, ← Pop_idem S _ _ ΩD hb f]
    rw [← Pop_herm_triv S ΩD hb, Pop_idem S _ _ ΩD hb]
  rw [e, ← vL_norm_sq']
  exact @inner_self_eq_norm_sq ℂ _ _ _ _ (vL S (P f))

/-- The form of `Δ_𝖺(𝐔)` on the torus, with the constraint form `QU`. -/
def formU {G : GaugeGroup N} (hG : G.LieInput) [NeZero N] (X : Fin 4 → Site NF → Mat) (W : Site NF → Site NF → GLN)
    (QU : (Fin 4 → Site NF → Mat) → (Fin 4 → Site NF → Mat) → ℂ) (B C : Fin 4 → Site NF → Mat) : ℂ :=
  pair1V S B (Ds2 a1 (cfgX X) (D1 a1 (cfgX X) C)) + pair1V S B (D0L a1 (cfgX X) (Ds1L a1 (cfgX X) C)) +
    pair1V S B (hessOp' a1 hG (cfgX X) C) - pairP S X W Set.univ B C + QU B C

lemma CPvU_nn [NeZero N] {δ α₁ : ℝ} (hδ : 0 < δ) (hθ : 0 < thetaB S N δ) (hCv : 0 ≤ Cv S δ (Csc S N) (4 * N * (S.L : ℝ) ^ 4))
    (hCg : 0 ≤ Cg S δ (Csc S N) (4 * N * (S.L : ℝ) ^ 4) α₁) : 0 ≤ CPvU S N δ α₁ := by
  have hc1 : ∀ r, 0 ≤ (S.toContSeq).c1 (1 / 2) r := fun r => by unfold Summation.ContSeq.c1; positivity
  have hγ : 0 ≤ 2 / gammaB N := by unfold gammaB; positivity
  have hL : (0 : ℝ) ≤ S.L := by positivity
  have hrp := Real.rpow_nonneg hL (12 : ℝ)
  have hCPg : 0 ≤ ScalarHyp.CPg S N δ α₁ := by
    unfold ScalarHyp.CPg
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) hγ) hrp) (hc1 _)) (hc1 _)
  unfold CPvU
  refine mul_nonneg (mul_nonneg hCPg ?_) ?_
  · have : 0 ≤ 4 / (7 / 32 * thetaB S N δ) := by positivity
    positivity
  · have := hc1 (7 / 32 * thetaB S N δ); have := hc1 (7 / 32 * thetaB S N δ / 2); positivity

/-- The sum of the errors of the steps of eq:sf-vector-conjugated. -/
def Econj (S : SeqDom) (N : ℕ) (δ0 α₁ η δ εQ : ℝ) : ℝ :=
  16 * (S.L : ℝ) ^ 2 * δ ^ 2 + (288 * (α₁ * S.L) + 1728 * (α₁ * S.L) ^ 2) +
    2903040 * (N : ℝ) ^ 2 * α₁ * (S.L : ℝ) ^ 6 + Kcomp S N δ0 α₁ η + 4 * CPvU S N δ0 α₁ * δ + εQ

namespace ScalarHyp

variable {S} {X : Fin 4 → Site (SequenceAverages.N0 S) → Matrix (Fin N) (Fin N) ℂ} {α₁ : ℝ}
  {W : Site (SequenceAverages.N0 S) → Site (SequenceAverages.N0 S) → (Matrix (Fin N) (Fin N) ℂ)ˣ} {η : ℝ}
  {δ0 : ℝ}

/-- **eq:sf-vector-conjugated on the torus** (`lem:sf-vector-decay`, the steps "The trivial configuration" and
"The complex field"), with the comparison of the constraint terms as the input `hQ`:
`Re⟨(e^φA)^*, Δ_𝖺(𝐔)(e^{-φ}A)⟩ ≥ ((2^{13}C_loc)⁻¹ - E)N(A)²`. -/
theorem conj_U [NeZero N] {G : GaugeGroup N} (hG : G.LieInput) (H : ScalarHyp S X α₁ W η Set.univ δ0)
    (hα512 : α₁ ≤ 1 / 512) (hM : 12 ≤ S.L ^ S.mM) (hR : 12 * S.L ≤ S.R)
    (hRMb : (S.toContSeq).r1 (1 / 2) (1 / 32 * δ0) ≤ RMS) (hRMs4 : 32 * Real.log S.L / (1 / 4 * δ0) ≤ RMS)
    (hsmallT : CTd S N δ0 α₁ η * (S.toContSeq).c1 (1 / 2) (1 / 32 * δ0) ≤ gammaB N / 4)
    (hsmallT0 : CTd S N δ0 0 0 * (S.toContSeq).c1 (1 / 2) (1 / 32 * δ0) ≤ gammaB N / 4)
    (hRMθs : 32 * Real.log S.L / (thetaB S N δ0 / 2) ≤ RMS)
    (hRMθc : (S.toContSeq).r1 (1 / 2) (7 / 16 * thetaB S N δ0) ≤ RMS)
    (hRMc : (S.toContSeq).r1 (1 / 2) (3 / 4 * δ0) ≤ RMS)
    (hRMa : (S.toContSeq).r1 (1 / 2) (1 / 8 * δ0) ≤ RMS)
    (hRMq : (S.toContSeq).r1 (1 / 2) (thetaB S N δ0) ≤ RMS)
    (hRMq2 : (S.toContSeq).r1 (1 / 2) (thetaB S N δ0 / 2) ≤ RMS)
    (hRMs8 : 32 * Real.log S.L / (thetaB S N δ0 / 4 / 2) ≤ RMS)
    (hRMc8 : (S.toContSeq).r1 (1 / 2) (7 / 16 * (thetaB S N δ0 / 4)) ≤ RMS)
    (hRMd2 : (S.toContSeq).r1 (1 / 2) (7 / 16 * (thetaB S N δ0 / 4) / 2) ≤ RMS)
    (hRMds : 32 * Real.log S.L / (2 * (7 / 16 * (thetaB S N δ0 / 4))) ≤ RMS)
    (hRMp2 : (S.toContSeq).r1 (1 / 2) (7 / 16 * thetaB S N δ0 / 2) ≤ RMS)
    (hRMps : 32 * Real.log S.L / (2 * (7 / 16 * thetaB S N δ0)) ≤ RMS)
    (hRMsum : (S.toContSeq).r1 (1 / 2) (7 / 32 * thetaB S N δ0) ≤ RMS)
    (hRMsum2 : (S.toContSeq).r1 (1 / 2) (7 / 32 * thetaB S N δ0 / 2) ≤ RMS)
    (hRMss : 32 * Real.log S.L / (2 * (7 / 32 * thetaB S N δ0)) ≤ RMS)
    (hR1 : 1 ≤ S.R) (hRM2 : 2 * (S.L : ℝ) ≤ RMS) (hRMn : 2 * S.L ≤ S.R * S.L ^ S.mM)
    (hcutS : 8 * Real.exp (-(2 * (kap0 S N δ0 * (((S.L ^ S.mM : ℕ) : ℝ) / S.L)))) *
      Kbar S.L (kap0 S N δ0) (CIone S N δ0 (kap0 S N δ0)) Cbump ≤ 1 / 16)
    {ε : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1) (hΘ : ThetaIMS S N δ0 (Cloc S.L) ε ≤ 1 / 2)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδθ : δ ≤ 1 / 4 * (7 / 32 * thetaB S N δ0)) (hδL : 16 * S.L * δ ≤ 1)
    (ph : Site NF → ℝ) (hph : ∀ x x', |ph x - ph x'| ≤ δ * S.dF x x')
    (QU : (Fin 4 → Site NF → Mat) → (Fin 4 → Site NF → Mat) → ℂ) {εQ : ℝ} (A : Fin 4 → Site NF → Mat)
    (hQ : |(QU (expA S ph A) (expA S (fun x => -ph x) A)).re - Qnorm S A| ≤ εQ * (gradNorm S A + wnorm S A)) :
    ((2 ^ 13 * Cloc S.L)⁻¹ - Econj S N δ0 α₁ η δ εQ) * (gradNorm S A + wnorm S A) ≤
      (formU S hG X W QU (expA S ph A) (expA S (fun x => -ph x) A)).re := by
  have hL1 : (1 : ℝ) ≤ S.L := by exact_mod_cast S.Lpos
  have hL0 : (0 : ℝ) ≤ S.L := by linarith
  have hRML : (S.L : ℝ) < RMS := by
    have h8 := H.hRM8
    have h2 : (S.L : ℝ) ≤ (S.L : ℝ) ^ 2 := le_self_pow₀ hL1 (by norm_num)
    linarith
  have hRM1 : 1 ≤ S.R * S.L ^ S.mM := Nat.one_le_iff_ne_zero.2 (by have := S.one_le_R; have := S.Lpos; positivity)
  have hα0 := H.hα0
  have hα32 : α₁ ≤ 1 / 32 := by linarith
  have hδL' : δ * S.L ≤ 1 := by linarith [mul_nonneg hδ hL0]
  set B := expA S ph A
  set C := expA S (fun x => -ph x) A
  set Gn := gradNorm S A
  set Wn := wnorm S A
  set Pn := (N : ℝ) * ∑ x, hs2 (Pop S (X0 S) (W1 S) Set.univ (Ds1L a1 (cfgX (X0 S)) A) x)
  have hG0 := gradNorm_nonneg' S A
  have hW0 := wnorm_nonneg' S A
  have hlap := lap_comp S hRML H.hX hα0 hα32 hδ hδL ph hph A
  have hgr := grad_conj S hRM1 hδ hδL' ph hph A
  have hhs := hess_comp S hG hRML H.hX hα0 hα512 hδ hδL ph hph A
  have hPc := H.P_conjU hRMb hRMs4 hsmallT hRMθs hRMθc hRMsum hRMsum2 hRMss hδ hδθ ph hph A
  have hPm := H.Pcomp hRMb hRMs4 hsmallT hsmallT0 hRMθs hRMθc hRMc hRMa hRMq hRMq2 hRMs8 hRMc8 hRMd2 hRMds
    hRMp2 hRMps A
  have hP0 := pairP_triv_eq S Set.univ A
  have hu := sum_u_sq_le S A
  have hvl := vector_lower_torus S hM hR H.triv hRMb hRMs4 hsmallT0 hRMθs hRMθc hRMsum hRMsum2 hRMss hR1 hRM2 hRMn
    hcutS hε0 hε hΘ A
  have hsc := sf_components S hRMn A
  have hCv := H.Cv_nn
  have hCg := H.Cg_nn'
  have hCPv := CPvU_nn S H.hδ0 (H.thetaB_pos (N := N)) hCv hCg
  have hCl : 0 < Cloc S.L := by unfold Cloc SFOneLayer.Col; positivity
  -- the form of `Δ_𝖺(id)` and its lower bound
  have hfA : formA S A = Gn + Qnorm S A - Pn := by unfold formA formF; rfl
  have hfa : (Gn + Wn) * (2 ^ 13 * Cloc S.L)⁻¹ ≤ formA S A := by
    rw [← div_eq_mul_inv, div_le_iff₀ (by positivity)]
    have : formF S A ≤ 2 * Cloc S.L * formA S A := hvl
    have hF : formF S A = gradNorm S A + Qnorm S A := rfl
    linarith
  -- the terms
  have hhs' : -(2903040 * (N : ℝ) ^ 2 * α₁ * (S.L : ℝ) ^ 6 * Wn) ≤
      (pair1V S B (hessOp' a1 hG (cfgX X) C)).re := by
    have := Complex.abs_re_le_norm (pair1V S B (hessOp' a1 hG (cfgX X) C))
    have := neg_abs_le (pair1V S B (hessOp' a1 hG (cfgX X) C)).re
    linarith
  have hPU : (pairP S X W Set.univ B C).re ≤ Pn + Kcomp S N δ0 α₁ η * (Gn + Wn) + 4 * CPvU S N δ0 α₁ * δ * Wn := by
    have h1 := (abs_le.1 hPc).2
    have h2 := (abs_le.1 hPm).2
    have h3 : (N : ℝ) * CPvU S N δ0 α₁ * δ * ∑ x, (((S.L : ℝ) ^ jj x)⁻¹ * ∑ ν, hs (A ν x)) ^ 2 ≤
        4 * CPvU S N δ0 α₁ * δ * Wn := by
      have h0 : 0 ≤ CPvU S N δ0 α₁ * δ := mul_nonneg hCPv hδ
      have := mul_le_mul_of_nonneg_left hu h0
      linarith
    rw [hP0] at h2
    linarith
  have hQ' := (abs_le.1 hQ).1
  have hlap' := (abs_le.1 hlap).1
  -- the sum
  have hre : (formU S hG X W QU B C).re =
      (pair1V S B (Ds2 a1 (cfgX X) (D1 a1 (cfgX X) C)) + pair1V S B (D0L a1 (cfgX X) (Ds1L a1 (cfgX X) C))).re +
        (pair1V S B (hessOp' a1 hG (cfgX X) C)).re - (pairP S X W Set.univ B C).re + (QU B C).re := by
    unfold formU
    simp only [Complex.add_re, Complex.sub_re]
  rw [hre]
  have hK1 : 0 ≤ 2903040 * (N : ℝ) ^ 2 * α₁ * (S.L : ℝ) ^ 6 := by positivity
  have hK2 : 0 ≤ 4 * CPvU S N δ0 α₁ * δ := by positivity
  have hK3 : 0 ≤ 16 * (S.L : ℝ) ^ 2 * δ ^ 2 := by positivity
  have e1 : 2903040 * (N : ℝ) ^ 2 * α₁ * (S.L : ℝ) ^ 6 * Wn ≤ 2903040 * (N : ℝ) ^ 2 * α₁ * (S.L : ℝ) ^ 6 * (Gn + Wn) :=
    mul_le_mul_of_nonneg_left (by linarith) hK1
  have e2 : 4 * CPvU S N δ0 α₁ * δ * Wn ≤ 4 * CPvU S N δ0 α₁ * δ * (Gn + Wn) :=
    mul_le_mul_of_nonneg_left (by linarith) hK2
  have e3 : 16 * (S.L : ℝ) ^ 2 * δ ^ 2 * Wn ≤ 16 * (S.L : ℝ) ^ 2 * δ ^ 2 * (Gn + Wn) :=
    mul_le_mul_of_nonneg_left (by linarith) hK3
  have key : ((2 ^ 13 * Cloc S.L)⁻¹ - Econj S N δ0 α₁ η δ εQ) * (Gn + Wn) =
      (Gn + Wn) * (2 ^ 13 * Cloc S.L)⁻¹ - (16 * (S.L : ℝ) ^ 2 * δ ^ 2 * (Gn + Wn) +
        (288 * (α₁ * S.L) + 1728 * (α₁ * S.L) ^ 2) * (Gn + Wn) +
        2903040 * (N : ℝ) ^ 2 * α₁ * (S.L : ℝ) ^ 6 * (Gn + Wn) + Kcomp S N δ0 α₁ η * (Gn + Wn) +
        4 * CPvU S N δ0 α₁ * δ * (Gn + Wn) + εQ * (Gn + Wn)) := by
    unfold Econj; ring
  rw [key]
  linarith

end ScalarHyp

/-! ### The operator and the decay -/

/-- **The operator of the fine model**: `T(𝐔) = Δ(𝐔) + D_𝐔(1 - P(𝐔))D^*_𝐔 + Q_op`, with `Δ(𝐔) = D^*_𝐔D_𝐔 + Δ'(𝐔)`
(`hessLin`) and a given constraint operator `Q_op` (the shape of `DeltaA` with `R = 1 - P`). -/
def TU {G : GaugeGroup N} (hG : G.LieInput) [NeZero N] (X : Fin 4 → Site NF → Mat) (W : Site NF → Site NF → GLN)
    (QOp : Module.End ℂ (Fin 4 → Site NF → Mat)) : Module.End ℂ (Fin 4 → Site NF → Mat) :=
  hessLin a1 hG (by simp [a1]) (cfgX X) +
    D0L a1 (cfgX X) ∘ₗ (1 - Pop S X W Set.univ) ∘ₗ Ds1L a1 (cfgX X) + QOp

lemma pair1V_sub (B J D : Fin 4 → Site NF → Mat) : pair1V S B (J - D) = pair1V S B J - pair1V S B D := by
  unfold pair1V
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Pi.sub_apply, Pi.sub_apply, emb_sub', inner_sub_right]

/-- The form of `T(𝐔)` is `formU`. -/
lemma pair_TU {G : GaugeGroup N} (hG : G.LieInput) [NeZero N] (X : Fin 4 → Site NF → Mat)
    (W : Site NF → Site NF → GLN) (QOp : Module.End ℂ (Fin 4 → Site NF → Mat)) (B C : Fin 4 → Site NF → Mat) :
    pair1V S B (TU S hG X W QOp C) = formU S hG X W (fun B C => pair1V S B (QOp C)) B C := by
  have hP : pairP S X W Set.univ B C = pair1V S B (D0L a1 (cfgX X) (Pop S X W Set.univ (Ds1L a1 (cfgX X) C))) := by
    unfold pairP
    congr 1
  unfold TU formU
  rw [hP]
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply, Module.End.one_apply, map_sub]
  rw [pair1V_add, pair1V_add, pair1V_sub]
  have hh : hessLin a1 hG (by simp [a1]) (cfgX X) C = Ds2 a1 (cfgX X) (D1 a1 (cfgX X) C) + hessOp' a1 hG (cfgX X) C := rfl
  rw [hh, pair1V_add]
  ring

namespace ScalarHyp

variable {S} {X : Fin 4 → Site (SequenceAverages.N0 S) → Matrix (Fin N) (Fin N) ℂ} {α₁ : ℝ}
  {W : Site (SequenceAverages.N0 S) → Site (SequenceAverages.N0 S) → (Matrix (Fin N) (Fin N) ℂ)ˣ} {η : ℝ}
  {δ0 : ℝ}

/-- **eq:sf-vector-decay on the torus** (`lem:sf-vector-decay`, "Conclusion", in the fine model), with the
comparison of the constraint terms as the input `hQ`: `T(𝐔)` is bijective, and for `u = e^φT(𝐔)⁻¹(J + D^*_𝐔K)`,
`N(u) ≤ c⁻¹(‖e^φJ‖_{w⁻¹} + 3L‖e^φK‖)`, `c = (2^{13}C_loc)⁻¹ - E`. -/
theorem decay_U [NeZero N] {G : GaugeGroup N} (hG : G.LieInput) (H : ScalarHyp S X α₁ W η Set.univ δ0)
    (hα512 : α₁ ≤ 1 / 512) (hM : 12 ≤ S.L ^ S.mM) (hR : 12 * S.L ≤ S.R)
    (hRMb : (S.toContSeq).r1 (1 / 2) (1 / 32 * δ0) ≤ RMS) (hRMs4 : 32 * Real.log S.L / (1 / 4 * δ0) ≤ RMS)
    (hsmallT : CTd S N δ0 α₁ η * (S.toContSeq).c1 (1 / 2) (1 / 32 * δ0) ≤ gammaB N / 4)
    (hsmallT0 : CTd S N δ0 0 0 * (S.toContSeq).c1 (1 / 2) (1 / 32 * δ0) ≤ gammaB N / 4)
    (hRMθs : 32 * Real.log S.L / (thetaB S N δ0 / 2) ≤ RMS)
    (hRMθc : (S.toContSeq).r1 (1 / 2) (7 / 16 * thetaB S N δ0) ≤ RMS)
    (hRMc : (S.toContSeq).r1 (1 / 2) (3 / 4 * δ0) ≤ RMS)
    (hRMa : (S.toContSeq).r1 (1 / 2) (1 / 8 * δ0) ≤ RMS)
    (hRMq : (S.toContSeq).r1 (1 / 2) (thetaB S N δ0) ≤ RMS)
    (hRMq2 : (S.toContSeq).r1 (1 / 2) (thetaB S N δ0 / 2) ≤ RMS)
    (hRMs8 : 32 * Real.log S.L / (thetaB S N δ0 / 4 / 2) ≤ RMS)
    (hRMc8 : (S.toContSeq).r1 (1 / 2) (7 / 16 * (thetaB S N δ0 / 4)) ≤ RMS)
    (hRMd2 : (S.toContSeq).r1 (1 / 2) (7 / 16 * (thetaB S N δ0 / 4) / 2) ≤ RMS)
    (hRMds : 32 * Real.log S.L / (2 * (7 / 16 * (thetaB S N δ0 / 4))) ≤ RMS)
    (hRMp2 : (S.toContSeq).r1 (1 / 2) (7 / 16 * thetaB S N δ0 / 2) ≤ RMS)
    (hRMps : 32 * Real.log S.L / (2 * (7 / 16 * thetaB S N δ0)) ≤ RMS)
    (hRMsum : (S.toContSeq).r1 (1 / 2) (7 / 32 * thetaB S N δ0) ≤ RMS)
    (hRMsum2 : (S.toContSeq).r1 (1 / 2) (7 / 32 * thetaB S N δ0 / 2) ≤ RMS)
    (hRMss : 32 * Real.log S.L / (2 * (7 / 32 * thetaB S N δ0)) ≤ RMS)
    (hR1 : 1 ≤ S.R) (hRM2 : 2 * (S.L : ℝ) ≤ RMS) (hRMn : 2 * S.L ≤ S.R * S.L ^ S.mM)
    (hcutS : 8 * Real.exp (-(2 * (kap0 S N δ0 * (((S.L ^ S.mM : ℕ) : ℝ) / S.L)))) *
      Kbar S.L (kap0 S N δ0) (CIone S N δ0 (kap0 S N δ0)) Cbump ≤ 1 / 16)
    {ε : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1) (hΘ : ThetaIMS S N δ0 (Cloc S.L) ε ≤ 1 / 2)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδθ : δ ≤ 1 / 4 * (7 / 32 * thetaB S N δ0)) (hδL : 16 * S.L * δ ≤ 1)
    (ph : Site NF → ℝ) (hph : ∀ x x', |ph x - ph x'| ≤ δ * S.dF x x')
    (QOp : Module.End ℂ (Fin 4 → Site NF → Mat)) {εQ : ℝ}
    (hQ : ∀ A, |(pair1V S (expA S ph A) (QOp (expA S (fun x => -ph x) A))).re - Qnorm S A| ≤
      εQ * (gradNorm S A + wnorm S A))
    (hQ0 : ∀ A, |(pair1V S A (QOp A)).re - Qnorm S A| ≤ εQ * (gradNorm S A + wnorm S A))
    (hc : 0 < (2 ^ 13 * Cloc S.L)⁻¹ - Econj S N δ0 α₁ η δ εQ)
    (hc0 : 0 < (2 ^ 13 * Cloc S.L)⁻¹ - Econj S N δ0 α₁ η 0 εQ)
    (J : Fin 4 → Site NF → Mat) (K : Fin 4 → Fin 4 → Site NF → Mat) :
    Function.Bijective (TU S hG X W QOp) ∧
      ∀ v, TU S hG X W QOp v = J + DsU S X K →
        √(gradNorm S (expA S ph v) + wnorm S (expA S ph v)) ≤
          ((2 ^ 13 * Cloc S.L)⁻¹ - Econj S N δ0 α₁ η δ εQ)⁻¹ *
            (√(wInv S (expA S ph J)) + 3 * S.L * √(Knorm S ph K)) := by
  have hRML : (S.L : ℝ) < RMS := by
    have hL1 : (1 : ℝ) ≤ S.L := by exact_mod_cast S.Lpos
    have h8 := H.hRM8
    have h2 : (S.L : ℝ) ≤ (S.L : ℝ) ^ 2 := le_self_pow₀ hL1 (by norm_num)
    linarith
  have hα32 : α₁ ≤ 1 / 32 := by linarith
  have hθ := H.thetaB_pos (N := N)
  refine ⟨?_, fun v hv => ?_⟩
  · -- the conjugated form at `φ = 0` is coercive
    refine bij_of_coercive S (TU S hG X W QOp) hc0 fun A => ?_
    have h := H.conj_U hG hα512 hM hR hRMb hRMs4 hsmallT hsmallT0 hRMθs hRMθc hRMc hRMa hRMq hRMq2 hRMs8 hRMc8
      hRMd2 hRMds hRMp2 hRMps hRMsum hRMsum2 hRMss hR1 hRM2 hRMn hcutS hε0 hε hΘ le_rfl (by positivity) (by simp)
      (fun _ => 0) (fun _ _ => by simp) (fun B C => pair1V S B (QOp C)) A
      (by simp only [neg_zero, expA_zero]; exact hQ0 A)
    simp only [neg_zero, expA_zero] at h
    rw [pair_TU]
    exact h
  · -- `v = e^{-φ}u` with `u = e^φv`
    set u := expA S ph v
    have hvu : expA S (fun x => -ph x) u = v := by
      funext μ x
      simp only [u, expA, smul_smul, ← Complex.ofReal_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero,
        Complex.ofReal_one, one_smul]
    have h := H.conj_U hG hα512 hM hR hRMb hRMs4 hsmallT hsmallT0 hRMθs hRMθc hRMc hRMa hRMq hRMq2 hRMs8 hRMc8
      hRMd2 hRMds hRMp2 hRMps hRMsum hRMsum2 hRMss hR1 hRM2 hRMn hcutS hε0 hε hΘ hδ hδθ hδL ph hph
      (fun B C => pair1V S B (QOp C)) u (hQ u)
    rw [← pair_TU, hvu, hv] at h
    exact decay_of_conj S hRML H.hX H.hα0 hα32 hδ hδL ph hph hc u J K h

end ScalarHyp

end SFBounds
end CoreLean

end
