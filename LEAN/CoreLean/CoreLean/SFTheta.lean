/-
`prop:sf-bounds` of BALABAN_CORE.tex (`4252790331fd`): the hypotheses of `lem:sf-local` on the box about a site `z` of
a scale `j ≥ 2` together with the bound of its number `Θ` (the step "Values in the layers `j ≥ 2`"), in the form in
which the later steps (first differences, Hölder moduli, second differences) use them, on the fine lattice (`a₀ = 1`).

* `theta_at`: there are bounds `Fb`, `Gb` of the data on `Q_{8+2L}` such that `SFHyp` holds on the box about `z` with
  `√N a²Fb`, `√N aGb`, and `Θ ≤ √N C_Θ a⁻¹e^{-φ(z)}M₀`.
-/
import CoreLean.SFValues

open Finset Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean
namespace SFBounds

open Lattices SeqDom Blocks SmallFieldBlocks SFBox SFBox.SeqDomBox SFLocal LocalLaplacian InteriorSchauder

variable (S : SeqDom) {N m : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "NF" => SequenceAverages.N0 S
local notation "RMS" => ((S.R * S.L ^ S.mM : ℕ) : ℝ)
set_option quotPrecheck false in
local notation "jj" => (S.toDomSeq).sc

namespace SFBHyp

variable {S} {X : Fin 4 → Site (SequenceAverages.N0 S) → Matrix (Fin N) (Fin N) ℂ} {α₁ : ℝ}
  {ΩD : Set (Site (SequenceAverages.N0 S))} {δ₁ Cs CN : ℝ}
  {u f : Fin m → Site (SequenceAverages.N0 S) → Matrix (Fin N) (Fin N) ℂ}
  {g : Fin m → Fin 4 → Site (SequenceAverages.N0 S) → Matrix (Fin N) (Fin N) ℂ}
  {Zu Nu Fu : Fin m → Site (SequenceAverages.N0 S) → Matrix (Fin N) (Fin N) ℂ}
  {Zc : Site (SequenceAverages.N0 S) → (Fin 4 → ℤ) → (VS N m →L[ℝ] VS N m)} {y' : Site (SequenceAverages.N0 S)}
  {F G : ℝ}
  (H : SFBHyp S X α₁ ΩD δ₁ Cs CN u f g Zu Nu Fu Zc y' F G)
include H

/-- **The hypotheses of `lem:sf-local` about `z` and the bound of `Θ`.** -/
theorem theta_at [NeZero N] {z : Site NF} (hj : 2 ≤ jj z) :
    ∃ Fb Gb : ℝ, SFHyp ((S.L : ℝ) ^ jj z)⁻¹ (xbar z) (Atil ((S.L : ℝ) ^ jj z) X) S.L α₁
        (sfData S (jj z) u f g Nu Fu Zc) CN
        (Real.sqrt N * ((S.L : ℝ) ^ jj z) ^ 2 * Fb) (Real.sqrt N * (S.L : ℝ) ^ jj z * Gb) ∧
      Th ((S.L : ℝ) ^ jj z)⁻¹ (xbar z) S.L (sfData S (jj z) u f g Nu Fu Zc)
        (Real.sqrt N * ((S.L : ℝ) ^ jj z) ^ 2 * Fb) (Real.sqrt N * (S.L : ℝ) ^ jj z * Gb) ≤
        Real.sqrt N * (CTh S δ₁ Cs * ((S.L : ℝ) ^ jj z)⁻¹ * Real.exp (-phiY S δ₁ y' z) * M0 S Cs y' F G) := by
  have hL := H.L3
  have hL0 : (0 : ℝ) < S.L := by linarith
  have hM := H.wN_le_M0
  have hM0 := H.M0_nonneg
  set c : ℝ := (S.L : ℝ) ^ jj z with hc_def
  have hc : 0 < c := by positivity
  set E := Real.exp (-phiY S δ₁ y' z)
  have hE : 0 < E := Real.exp_pos _
  have hCF : 0 ≤ CF S δ₁ := by unfold CF; have := H.c1_nonneg; positivity
  have hCs := H.hCs
  set Fb : ℝ := ((S.L : ℝ) ^ 6 + Cs * CF S δ₁ * (S.L : ℝ) ^ 3) * Real.exp S.L * c⁻¹ ^ 3 * E * M0 S Cs y' F G
  set Gb : ℝ := (S.L : ℝ) ^ 4 * Real.exp S.L * c⁻¹ ^ 2 * E * M0 S Cs y' F G
  have hFb : ∀ w, InQr c⁻¹ (xbar z) (8 + 2 * S.L) w →
      Real.sqrt (nsq fun k => f k (castS w) + Fu k (castS w)) ≤ Fb := by
    intro w hw
    refine (nsq_add_le _ _).trans ?_
    have hB1 : Real.sqrt (nsq fun k => f k (castS w)) ≤
        (S.L : ℝ) ^ 6 * Real.exp S.L * c⁻¹ ^ 3 * E * M0 S Cs y' F G := by
      by_cases hsrc : (dinf (castS w) y' : ℝ) < (S.L : ℝ) ^ jj y'
      · obtain ⟨hjj, hphi⟩ := H.source_near hj hw hsrc
        have hfF : Real.sqrt (nsq fun k => f k (castS w)) ≤ F := by
          rw [Real.sqrt_le_left H.hF]; exact H.hfb _
        have h3 : c ^ 3 ≤ (S.L : ℝ) ^ 6 * (S.L : ℝ) ^ (3 * jj y') := by
          rw [hc_def, ← pow_mul, mul_comm]; exact H.pow_le_of_le hjj 3
        have hEL : 1 ≤ Real.exp S.L * E := by
          rw [← Real.exp_add]; exact Real.one_le_exp (by unfold phiY at hphi ⊢; linarith)
        have hFM := H.F_le_M0
        have hFc : F ≤ (S.L : ℝ) ^ 6 * c⁻¹ ^ 3 * ((S.L : ℝ) ^ (3 * jj y') * F) := by
          rw [show (S.L : ℝ) ^ 6 * c⁻¹ ^ 3 * ((S.L : ℝ) ^ (3 * jj y') * F) =
            ((S.L : ℝ) ^ 6 * (S.L : ℝ) ^ (3 * jj y')) * F / c ^ 3 by field_simp]
          rw [le_div_iff₀ (by positivity)]
          have := H.hF
          nlinarith
        calc Real.sqrt (nsq fun k => f k (castS w)) ≤ F := hfF
          _ ≤ (S.L : ℝ) ^ 6 * c⁻¹ ^ 3 * ((S.L : ℝ) ^ (3 * jj y') * F) := hFc
          _ ≤ (S.L : ℝ) ^ 6 * c⁻¹ ^ 3 * M0 S Cs y' F G := by gcongr
          _ ≤ (S.L : ℝ) ^ 6 * c⁻¹ ^ 3 * M0 S Cs y' F G * (Real.exp S.L * E) :=
              le_mul_of_one_le_right (by positivity) hEL
          _ = _ := by ring
      · push_neg at hsrc
        have : (nsq fun k => f k (castS w)) = 0 :=
          Finset.sum_eq_zero fun k _ => by show hs2 (f k (castS w)) = 0; rw [H.hfs k _ hsrc]; simp [hs2, ntr]
        rw [this, Real.sqrt_zero]; positivity
    have hB2 : Real.sqrt (nsq fun k => Fu k (castS w)) ≤
        Cs * CF S δ₁ * (S.L : ℝ) ^ 3 * Real.exp S.L * c⁻¹ ^ 3 * E * M0 S Cs y' F G := by
      have h1 := H.hFu (castS w)
      have h2 := far_sum S H.hδ0 H.hRM1 H.hRMs H.phi_lip' u (castS w)
      have hge := H.sc_box_ge (by linarith) hw
      have h3 : ((S.L : ℝ) ^ (2 * jj (castS w)))⁻¹ * ((S.L : ℝ) ^ jj (castS w))⁻¹ ≤ (S.L : ℝ) ^ 3 * c⁻¹ ^ 3 := by
        have e1 : ((S.L : ℝ) ^ (2 * jj (castS w)))⁻¹ * ((S.L : ℝ) ^ jj (castS w))⁻¹ =
            ((S.L : ℝ) ^ (3 * jj (castS w)))⁻¹ := by
          rw [← mul_inv, ← pow_add, show 2 * jj (castS w) + jj (castS w) = 3 * jj (castS w) by ring]
        have e2 : (S.L : ℝ) ^ 3 * c⁻¹ ^ 3 = (S.L : ℝ) ^ 3 / (S.L : ℝ) ^ (3 * jj z) := by
          rw [hc_def, inv_pow, ← pow_mul, div_eq_mul_inv, mul_comm (jj z) 3]
        rw [e1, e2, le_div_iff₀ (by positivity), inv_mul_eq_div, div_le_iff₀ (by positivity), ← pow_add]
        exact pow_le_pow_right₀ (by linarith) (by omega)
      have h4 := H.exp_phi_box hj hw
      have hw0 := Real.sqrt_nonneg (wN S (eF S (phiY S δ₁ y') u))
      calc Real.sqrt (nsq fun k => Fu k (castS w))
          ≤ Cs * ((S.L : ℝ) ^ (2 * jj (castS w)))⁻¹ * (CF S δ₁ * ((S.L : ℝ) ^ jj (castS w))⁻¹ *
              Real.exp (-phiY S δ₁ y' (castS w)) * Real.sqrt (wN S (eF S (phiY S δ₁ y') u))) := by
            refine h1.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
            unfold CF; unfold phiY at h2 ⊢; linarith
        _ = Cs * CF S δ₁ * (((S.L : ℝ) ^ (2 * jj (castS w)))⁻¹ * ((S.L : ℝ) ^ jj (castS w))⁻¹) *
              Real.exp (-phiY S δ₁ y' (castS w)) * Real.sqrt (wN S (eF S (phiY S δ₁ y') u)) := by ring
        _ ≤ Cs * CF S δ₁ * ((S.L : ℝ) ^ 3 * c⁻¹ ^ 3) * (Real.exp S.L * E) * M0 S Cs y' F G := by
            gcongr
        _ = _ := by ring
    calc _ ≤ (S.L : ℝ) ^ 6 * Real.exp S.L * c⁻¹ ^ 3 * E * M0 S Cs y' F G +
          Cs * CF S δ₁ * (S.L : ℝ) ^ 3 * Real.exp S.L * c⁻¹ ^ 3 * E * M0 S Cs y' F G := add_le_add hB1 hB2
      _ = Fb := by simp only [Fb]; ring
  have hGb : ∀ μ w, InQr c⁻¹ (xbar z) (8 + 2 * S.L) w → Real.sqrt (nsq fun k => g k μ (castS w)) ≤ Gb := by
    intro μ w hw
    by_cases hsrc : (dinf (castS w) y' : ℝ) < (S.L : ℝ) ^ jj y'
    · obtain ⟨hjj, hphi⟩ := H.source_near hj hw hsrc
      have hgG : Real.sqrt (nsq fun k => g k μ (castS w)) ≤ G := by
        rw [Real.sqrt_le_left H.hG]; exact H.hgb _ _
      have h2 : c ^ 2 ≤ (S.L : ℝ) ^ 4 * (S.L : ℝ) ^ (2 * jj y') := by
        rw [hc_def, ← pow_mul, mul_comm]; exact H.pow_le_of_le hjj 2
      have hEL : 1 ≤ Real.exp S.L * E := by
        rw [← Real.exp_add]; exact Real.one_le_exp (by unfold phiY at hphi ⊢; linarith)
      have hGM := H.G_le_M0
      have hGc : G ≤ (S.L : ℝ) ^ 4 * c⁻¹ ^ 2 * ((S.L : ℝ) ^ (2 * jj y') * G) := by
        rw [show (S.L : ℝ) ^ 4 * c⁻¹ ^ 2 * ((S.L : ℝ) ^ (2 * jj y') * G) =
          ((S.L : ℝ) ^ 4 * (S.L : ℝ) ^ (2 * jj y')) * G / c ^ 2 by field_simp]
        rw [le_div_iff₀ (by positivity)]
        have := H.hG
        nlinarith
      calc Real.sqrt (nsq fun k => g k μ (castS w)) ≤ G := hgG
        _ ≤ (S.L : ℝ) ^ 4 * c⁻¹ ^ 2 * ((S.L : ℝ) ^ (2 * jj y') * G) := hGc
        _ ≤ (S.L : ℝ) ^ 4 * c⁻¹ ^ 2 * M0 S Cs y' F G := by gcongr
        _ ≤ (S.L : ℝ) ^ 4 * c⁻¹ ^ 2 * M0 S Cs y' F G * (Real.exp S.L * E) :=
            le_mul_of_one_le_right (by positivity) hEL
        _ = Gb := by simp only [Gb]; ring
    · push_neg at hsrc
      have : (nsq fun k => g k μ (castS w)) = 0 :=
        Finset.sum_eq_zero fun k _ => by show hs2 (g k μ (castS w)) = 0; rw [H.hgs k μ _ hsrc]; simp [hs2, ntr]
      rw [this, Real.sqrt_zero]; positivity
  have hth := theta_u_le S H.hRM8 H.hδ0.le H.hδ H.phi_lip' u hj
  have hTh : c⁻¹ ^ 2 * Real.sqrt (∑ w ∈ QF c⁻¹ (xbar z) (8 + 2 * S.L), nsq fun k => u k (castS w)) +
      c ^ 2 * Fb + c * Gb ≤ CTh S δ₁ Cs * c⁻¹ * E * M0 S Cs y' F G := by
    have hw1 : c⁻¹ ^ 2 * Real.sqrt (∑ w ∈ QF c⁻¹ (xbar z) (8 + 2 * S.L), nsq fun k => u k (castS w)) ≤
        25 * S.L * Real.exp S.L * c⁻¹ * E * M0 S Cs y' F G := by
      refine hth.trans ?_
      gcongr
    have e1 : c ^ 2 * Fb = ((S.L : ℝ) ^ 6 + Cs * CF S δ₁ * (S.L : ℝ) ^ 3) * Real.exp S.L * c⁻¹ * E *
        M0 S Cs y' F G := by
      simp only [Fb]; field_simp
    have e2 : c * Gb = (S.L : ℝ) ^ 4 * Real.exp S.L * c⁻¹ * E * M0 S Cs y' F G := by
      simp only [Gb]; field_simp
    rw [e1, e2]
    unfold CTh
    nlinarith
  refine ⟨Fb, Gb, sfHyp_of S H.hX H.hα0 H.hα H.hRM8 H.hD H.H2 hj H.hCN (H.hZs z hj) (H.hN1 z hj) hFb hGb, ?_⟩
  simp only [Th, sfData]
  rw [pn_liftM]
  have hN : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
  calc Real.sqrt N * c⁻¹ ^ 2 * Real.sqrt (∑ w ∈ QF c⁻¹ (xbar z) (8 + 2 * S.L), nsq fun k => u k (castS w)) +
        Real.sqrt N * c ^ 2 * Fb + Real.sqrt N * c * Gb
      = Real.sqrt N * (c⁻¹ ^ 2 * Real.sqrt (∑ w ∈ QF c⁻¹ (xbar z) (8 + 2 * S.L), nsq fun k => u k (castS w)) +
        c ^ 2 * Fb + c * Gb) := by ring
    _ ≤ Real.sqrt N * (CTh S δ₁ Cs * c⁻¹ * E * M0 S Cs y' F G) := mul_le_mul_of_nonneg_left hTh hN

end SFBHyp

end SFBounds
end CoreLean

end
