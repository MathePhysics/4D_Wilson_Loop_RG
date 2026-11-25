/-
`lem:sf-vector-decay` of BALABAN_CORE.tex for a compression: the conclusion of `decay_U` for the compressed inverse
`cinv π₁ T(𝐔)` with an idempotent `π₁` which commutes with the weights `e^φ` and is symmetric for `⟨B^*, C⟩` (the
projection onto the forms with values in `𝔤^c` of the concrete layer): the compressed kernel is invertible, and the
compressed solutions satisfy eq:sf-vector-decay with the same constant (the conjugated form at `u ∈ ran π₁` sees only
`π₁T`).
-/
import CoreLean.SFVectorConj

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

namespace ScalarHyp

variable {S} {X : Fin 4 → Site (SequenceAverages.N0 S) → Matrix (Fin N) (Fin N) ℂ} {α₁ : ℝ}
  {W : Site (SequenceAverages.N0 S) → Site (SequenceAverages.N0 S) → (Matrix (Fin N) (Fin N) ℂ)ˣ} {η : ℝ}
  {δ0 : ℝ}

/-- **eq:sf-vector-decay for the compressed inverse**: `ckern π₁ T(𝐔)` is invertible, and every `v ∈ ran π₁` with
`π₁T(𝐔)v = π₁(J + D^*_𝐔K)` satisfies the bound of `decay_U`. -/
theorem decay_U_comp [NeZero N] {G : GaugeGroup N} (hG : G.LieInput) (H : ScalarHyp S X α₁ W η Set.univ δ0)
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
    (π₁ : Module.End ℂ (Fin 4 → Site NF → Mat)) (hπ : ∀ A, π₁ (π₁ A) = π₁ A)
    (hπe : ∀ (ψ : Site NF → ℝ) A, π₁ (expA S ψ A) = expA S ψ (π₁ A))
    (hπs : ∀ B C, pair1V S (π₁ B) C = pair1V S B (π₁ C))
    (J : Fin 4 → Site NF → Mat) (K : Fin 4 → Fin 4 → Site NF → Mat) :
    IsUnit (ckern π₁ (TU S hG X W QOp)) ∧
      ∀ v, π₁ v = v → π₁ (TU S hG X W QOp v) = π₁ (J + DsU S X K) →
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
  -- the coercivity at `φ = 0`
  have hcoer0 : ∀ A, ((2 ^ 13 * Cloc S.L)⁻¹ - Econj S N δ0 α₁ η 0 εQ) * (gradNorm S A + wnorm S A) ≤
      (pair1V S A (TU S hG X W QOp A)).re := fun A => by
    have h := H.conj_U hG hα512 hM hR hRMb hRMs4 hsmallT hsmallT0 hRMθs hRMθc hRMc hRMa hRMq hRMq2 hRMs8 hRMc8
      hRMd2 hRMds hRMp2 hRMps hRMsum hRMsum2 hRMss hR1 hRM2 hRMn hcutS hε0 hε hΘ le_rfl (by positivity) (by simp)
      (fun _ => 0) (fun _ _ => by simp) (fun B C => pair1V S B (QOp C)) A
      (by simp only [neg_zero, expA_zero]; exact hQ0 A)
    simp only [neg_zero, expA_zero] at h
    rw [pair_TU]
    exact h
  refine ⟨?_, fun v hvπ hv => ?_⟩
  · -- the compressed kernel is injective
    set T := TU S hG X W QOp
    have hinj : Function.Injective (ckern π₁ T) := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro A hA
      rw [ckern_apply] at hA
      have h1 : π₁ (T (π₁ A)) = 0 := by
        have := congrArg π₁ hA
        rwa [map_add, map_sub, hπ, hπ, sub_self, add_zero, map_zero] at this
      have h2 : A = π₁ A := by
        rw [h1, zero_add, sub_eq_zero] at hA; exact hA
      have h3 := hcoer0 A
      have h4 : pair1V S A (T A) = 0 := by
        rw [h2, hπs, h1]
        unfold pair1V; simp only [Pi.zero_apply]
        have : ∀ Z : Mat, emb (N := N) Z = embL Z := fun Z => rfl
        simp [this]
      rw [h4, Complex.zero_re] at h3
      have hg := gradNorm_nonneg' S A
      have hw := wnorm_nonneg' S A
      have h5 : gradNorm S A + wnorm S A ≤ 0 :=
        (mul_le_mul_iff_of_pos_left hc0).1 (by rw [mul_zero]; exact h3)
      have hw0 : wnorm S A = 0 := by linarith
      exact eq_zero_of_wnorm S A hw0
    exact (Module.End.isUnit_iff _).2 ⟨hinj, LinearMap.injective_iff_surjective.1 hinj⟩
  · set u := expA S ph v
    have hvu : expA S (fun x => -ph x) u = v := by
      funext μ x
      simp only [u, expA, smul_smul, ← Complex.ofReal_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero,
        Complex.ofReal_one, one_smul]
    have huπ : π₁ u = u := by simp only [u]; rw [hπe, hvπ]
    have heu : π₁ (expA S ph u) = expA S ph u := by rw [hπe, huπ]
    have h := H.conj_U hG hα512 hM hR hRMb hRMs4 hsmallT hsmallT0 hRMθs hRMθc hRMc hRMa hRMq hRMq2 hRMs8 hRMc8
      hRMd2 hRMds hRMp2 hRMps hRMsum hRMsum2 hRMss hR1 hRM2 hRMn hcutS hε0 hε hΘ hδ hδθ hδL ph hph
      (fun B C => pair1V S B (QOp C)) u (hQ u)
    rw [← pair_TU, hvu] at h
    have hpair : pair1V S (expA S ph u) (TU S hG X W QOp v) = pair1V S (expA S ph u) (J + DsU S X K) := by
      rw [← heu, hπs, hv, ← hπs, heu]
    rw [hpair] at h
    exact decay_of_conj S hRML H.hX H.hα0 hα32 hδ hδL ph hph hc u J K h

end ScalarHyp

end SFBounds
end CoreLean

end
