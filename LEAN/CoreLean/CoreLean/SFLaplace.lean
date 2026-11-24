/-
`prop:sf-bounds` of BALABAN_CORE.tex (`4252790331fd`), the last bound of (iv): `Δ_𝐔𝒪λ = λ + 𝒵u + 𝒩u + 𝓕u` (`(H2)`,
`g = 0`), on the fine lattice (`a₀ = 1`): for `z ∈ Δ(y) ∩ Ω_D`,
`|(Δ_𝐔u)(z)| ≤ C_Δe^{-(7/8)δ₁d(y, y')}(F + a_j⁻¹G)`.

* `near_scale`, `near_dist`: a site within `2La_j` of `z`, `j(z) = j`, has a scale of at least `j - 1` and lies at a
  weighted distance of at most `8L²` from `z`.
* `ZN_bound`: with the pointwise hypothesis on `𝒵` and `𝒩` of `(H2)`, `|𝒵u(z)| + |𝒩u(z)| ≤ C_*C₂Le^La_j⁻³e^{-φ(z)}M₀`.
* `lap_bound`: the bound of `Δ_𝐔u`.
-/
import CoreLean.SFGradient

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

/-- The number `C_Δ` of the bound of `Δ_𝐔u`. -/
def CDel (S : SeqDom) (δ₁ Cs CN : ℝ) : ℝ :=
  2 + 16 * (S.L : ℝ) ^ 5 * Real.exp (2 * δ₁) * Cs * (Cs * C2 S δ₁ Cs CN * S.L * Real.exp S.L + Cs * CF S δ₁)

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

/-- A site within `2La_j` of `z` has a scale of at least `j(z) - 1`. -/
lemma near_scale {z z' : Site NF} (hz' : (dinf z' z : ℝ) ≤ 2 * (S.L : ℝ) ^ (jj z + 1)) : jj z ≤ jj z' + 1 := by
  have hL := H.L3
  have hRM := H.hRM8
  have hmem : S.ef z' ∈ S.Ω (jj z - 1) := by
    refine S.layer_bonds_i (c := 2 * S.L + 1) (by nlinarith) ((S.toDomSeq).sc_le z) (S.ef_mem_sc z) ?_
    rw [dist_eq_norm, norm_emb_sub S.Lpos (SequenceAverages.N0_eq S)]
    have he := eta_pos (k := S.k) S.Lpos
    have hp : (0 : ℝ) < (S.L : ℝ) ^ jj z := by positivity
    unfold sp
    rw [pow_succ] at hz'
    nlinarith
  have := ((S.toDomSeq).mem_iff z' _).1 (S.mem_toDomSeq_Ω.2 hmem)
  omega

/-- A site within `2La_j` of `z` lies at a weighted distance of at most `8L²` from `z`. -/
lemma near_dist {z z' : Site NF} (hz' : (dinf z' z : ℝ) ≤ 2 * (S.L : ℝ) ^ (jj z + 1)) :
    S.dF z z' ≤ 8 * (S.L : ℝ) ^ 2 := by
  have hL := H.L3
  have hRM := H.hRM8
  have hp : (0 : ℝ) < (S.L : ℝ) ^ jj z := by positivity
  have h1 := S.dF_le_near (c := 2 * S.L + 1) (by nlinarith) z z' (by rw [dinf_comm]; rw [pow_succ] at hz'; nlinarith)
  have hd1 : (d1 z z' : ℝ) ≤ 4 * dinf z z' := by exact_mod_cast d1_le_four_dinf S z z'
  refine h1.trans ?_
  have hp1 : (0 : ℝ) < (S.L : ℝ) ^ (jj z - 1) := by positivity
  rw [div_le_iff₀ hp1]
  have hpow : (S.L : ℝ) ^ (jj z + 1) ≤ (S.L : ℝ) ^ 2 * (S.L : ℝ) ^ (jj z - 1) := by
    rw [← pow_add]; exact pow_le_pow_right₀ (by linarith) (by omega)
  rw [dinf_comm] at hd1
  nlinarith

/-- **The terms `𝒵u` and `𝒩u`.** -/
theorem ZN_bound [NeZero N] {z z' : Site NF} (hz' : (dinf z' z : ℝ) ≤ 2 * (S.L : ℝ) ^ (jj z + 1))
    (hZN : Real.sqrt (nsq fun k => Zu k z) + Real.sqrt (nsq fun k => Nu k z) ≤
      Cs * ((S.L : ℝ) ^ (2 * jj z))⁻¹ * Real.sqrt (nsq fun k => u k z')) :
    Real.sqrt (nsq fun k => Zu k z) + Real.sqrt (nsq fun k => Nu k z) ≤
      Cs * C2 S δ₁ Cs CN * S.L * Real.exp S.L * ((S.L : ℝ) ^ jj z)⁻¹ ^ 3 * Real.exp (-phiY S δ₁ y' z) *
        M0 S Cs y' F G := by
  have hL := H.L3
  have hL0 : (0 : ℝ) < S.L := by linarith
  have hp := H.pointwise z'
  have hsc := H.near_scale hz'
  have hd := H.near_dist hz'
  have hCs := H.hCs
  have hM0 := H.M0_nonneg
  have hC2 : 0 ≤ C2 S δ₁ Cs CN := by
    unfold C2 CTh CF Ksf; have := H.hCN; have := H.c1_nonneg; positivity
  set c : ℝ := (S.L : ℝ) ^ jj z with hc_def
  have hc : 0 < c := by positivity
  have hLj : ((S.L : ℝ) ^ jj z')⁻¹ ≤ S.L * c⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hc, inv_mul_le_iff₀ (by positivity), hc_def, ← pow_succ]
    exact pow_le_pow_right₀ (by linarith) (by omega)
  have hexp : Real.exp (-phiY S δ₁ y' z') ≤ Real.exp S.L * Real.exp (-phiY S δ₁ y' z) := by
    have hlip := (abs_le.1 (H.phi_lip' z z')).2
    have hδ := H.hδ
    have hδ0 := H.hδ0
    have h8 : δ₁ * (8 * (S.L : ℝ) ^ 2) ≤ S.L := by
      have : δ₁ * (8 * (S.L : ℝ) ^ 2) ≤ 1 / (128 * S.L) * (8 * (S.L : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right hδ (by positivity)
      have e : 1 / (128 * (S.L : ℝ)) * (8 * (S.L : ℝ) ^ 2) = S.L / 16 := by field_simp; ring
      linarith
    rw [← Real.exp_add]; refine Real.exp_le_exp.2 ?_
    have : δ₁ * S.dF z z' ≤ δ₁ * (8 * (S.L : ℝ) ^ 2) := mul_le_mul_of_nonneg_left hd hδ0.le
    linarith
  have h2 : ((S.L : ℝ) ^ (2 * jj z))⁻¹ = c⁻¹ ^ 2 := by rw [hc_def, inv_pow, ← pow_mul, mul_comm]
  refine hZN.trans ?_
  rw [h2]
  calc Cs * c⁻¹ ^ 2 * Real.sqrt (nsq fun k => u k z')
      ≤ Cs * c⁻¹ ^ 2 * (C2 S δ₁ Cs CN * (S.L * c⁻¹) * (Real.exp S.L * Real.exp (-phiY S δ₁ y' z)) *
          M0 S Cs y' F G) := by
        gcongr
        exact hp.trans (by gcongr)
    _ = _ := by ring

set_option maxHeartbeats 1000000 in
/-- **The bound of `Δ_𝐔u`** at a site `z ∈ Δ(y) ∩ Ω_D` when `g = 0`. -/
theorem lap_bound [NeZero N] (hg0 : ∀ k μ x, g k μ x = 0) {y z : Site NF} (hy : y ∈ detB S.toDomSeq)
    (hz : z ∈ Blk S.toDomSeq (jj y) y) (hzD : z ∈ ΩD) {z' : Site NF}
    (hz' : (dinf z' z : ℝ) ≤ 2 * (S.L : ℝ) ^ (jj z + 1))
    (hZN : Real.sqrt (nsq fun k => Zu k z) + Real.sqrt (nsq fun k => Nu k z) ≤
      Cs * ((S.L : ℝ) ^ (2 * jj z))⁻¹ * Real.sqrt (nsq fun k => u k z')) :
    Real.sqrt (nsq fun k => Lap 1 (cfgX X) (u k) z) ≤
      CDel S δ₁ Cs CN * Real.exp (-(7 / 8 * δ₁ * S.dF y y')) * (F + ((S.L : ℝ) ^ jj y)⁻¹ * G) := by
  have hL := H.L3
  have hL0 : (0 : ℝ) < S.L := by linarith
  have hsc := sc_of_mem_blk S hy hz
  have hF := H.hF
  have hG := H.hG
  have hCs := H.hCs
  have hM0 := H.M0_nonneg
  have hC2 : 0 ≤ C2 S δ₁ Cs CN := by
    unfold C2 CTh CF Ksf; have := H.hCN; have := H.c1_nonneg; positivity
  have hCF : 0 ≤ CF S δ₁ := by unfold CF; have := H.c1_nonneg; positivity
  set c : ℝ := (S.L : ℝ) ^ jj y with hc_def
  have hc : 0 < c := by positivity
  set e := Real.exp (δ₁ / 8 * S.dF y y')
  have he : 0 < e := Real.exp_pos _
  set D := Real.exp (-(7 / 8 * δ₁ * S.dF y y'))
  have hD : 0 < D := Real.exp_pos _
  -- the equation
  have heq : (fun k => Lap 1 (cfgX X) (u k) z) = fun k => f k z + (Zu k z + (Nu k z + Fu k z)) := by
    funext k
    rw [H.H2.eqn z hzD k]
    have : Ds1 1 (cfgX X) (g k) z = 0 := by
      simp [Ds1, Dbw, hg0, Ad]
    rw [this]; abel
  rw [heq]
  have hA : Real.sqrt (nsq fun k => f k z + (Zu k z + (Nu k z + Fu k z))) ≤
      Real.sqrt (nsq fun k => f k z) + Real.sqrt (nsq fun k => Zu k z + (Nu k z + Fu k z)) := nsq_add_le _ _
  have hB : Real.sqrt (nsq fun k => Zu k z + (Nu k z + Fu k z)) ≤
      Real.sqrt (nsq fun k => Zu k z) + Real.sqrt (nsq fun k => Nu k z + Fu k z) := nsq_add_le _ _
  have hC : Real.sqrt (nsq fun k => Nu k z + Fu k z) ≤
      Real.sqrt (nsq fun k => Nu k z) + Real.sqrt (nsq fun k => Fu k z) := nsq_add_le _ _
  -- the source
  have hf1 : Real.sqrt (nsq fun k => f k z) ≤ 2 * D * F := by
    by_cases hsrc : (dinf z y' : ℝ) < (S.L : ℝ) ^ jj y'
    · have hfF : Real.sqrt (nsq fun k => f k z) ≤ F := by rw [Real.sqrt_le_left hF]; exact H.hfb _
      have hd1 : S.dF y z ≤ 2 := ENNReal.toReal_le_of_le_ofReal (by norm_num) (S.wdist_block_le hy hz)
      have hd2 := S.tilde_dist H.hRML hsrc
      have ht := S.dF_triangle y z y'
      rw [S.dF_comm y' z] at hd2
      have hδ := H.hδ
      have hδ0 := H.hδ0
      have hδL : δ₁ * S.L ≤ 1 / 128 := by
        calc δ₁ * S.L ≤ 1 / (128 * S.L) * S.L := mul_le_mul_of_nonneg_right hδ (by linarith)
          _ = 1 / 128 := by field_simp
      have h1 : 1 ≤ 2 * D := by
        have : 7 / 8 * δ₁ * S.dF y y' ≤ Real.log 2 := by
          have := Real.log_two_gt_d9
          have : δ₁ * S.dF y y' ≤ δ₁ * (2 + 4 * S.L) := mul_le_mul_of_nonneg_left (by linarith) hδ0.le
          nlinarith
        have : Real.exp (-(Real.log 2)) ≤ D := Real.exp_le_exp.2 (by linarith)
        rw [Real.exp_neg, Real.exp_log (by norm_num)] at this
        linarith
      calc Real.sqrt (nsq fun k => f k z) ≤ F := hfF
        _ ≤ 2 * D * F := le_mul_of_one_le_left hF h1
    · push_neg at hsrc
      have : (nsq fun k => f k z) = 0 :=
        Finset.sum_eq_zero fun k _ => by show hs2 (f k z) = 0; rw [H.hfs k _ hsrc]; simp [hs2, ntr]
      rw [this, Real.sqrt_zero]; positivity
  -- the terms `𝒵u`, `𝒩u`
  have hzn := H.ZN_bound hz' hZN
  rw [hsc] at hzn
  -- the term `𝓕u`
  have hfu1 := H.hFu z
  have hfu2 := far_sum S H.hδ0 H.hRM1 H.hRMs H.phi_lip' u z
  rw [hsc] at hfu1 hfu2
  have h2c : ((S.L : ℝ) ^ (2 * jj y))⁻¹ = c⁻¹ ^ 2 := by rw [hc_def, inv_pow, ← pow_mul, mul_comm]
  rw [h2c] at hfu1
  have hfu : Real.sqrt (nsq fun k => Fu k z) ≤
      Cs * CF S δ₁ * c⁻¹ ^ 3 * Real.exp (-phiY S δ₁ y' z) * M0 S Cs y' F G := by
    refine hfu1.trans ?_
    have hW := H.wN_le_M0
    calc Cs * c⁻¹ ^ 2 * ∑ x', ((S.L : ℝ) ^ (4 * jj x'))⁻¹ * Real.exp (-(2 * δ₁ * S.dF z x')) *
          Real.sqrt (nsq fun k => u k x')
        ≤ Cs * c⁻¹ ^ 2 * (CF S δ₁ * c⁻¹ * Real.exp (-phiY S δ₁ y' z) * M0 S Cs y' F G) := by
          refine mul_le_mul_of_nonneg_left (hfu2.trans ?_) (by positivity)
          unfold CF; unfold phiY at hW ⊢
          have hc1 := H.c1_nonneg
          have : 0 ≤ Real.exp (7 * δ₁) * (S.L : ℝ) ^ (4 : ℝ) * (S.toContSeq).c1 (1 / 2) δ₁ * c⁻¹ *
              Real.exp (-(δ₁ * S.dF z y')) := by positivity
          exact mul_le_mul_of_nonneg_left hW this
      _ = _ := by ring
  -- `a_j⁻³M₀ ≤ 16LC_*L⁴e(F + a_j⁻¹G)` and `e^{-φ(z)} ≤ e^{2δ₁}e^{-δ₁d}`
  have h3 := H.scale_nat y 3 (by norm_num)
  have h2 := H.scale_nat y 2 (by norm_num)
  have hph := H.phi_block hy hz
  have hM : c⁻¹ ^ 3 * M0 S Cs y' F G ≤ 16 * S.L * Cs * (S.L : ℝ) ^ 4 * e * (F + c⁻¹ * G) := by
    unfold M0
    have e3 : (S.L : ℝ) ^ (3 * jj y) = c ^ 3 := by simp only [c]; ring
    have e2 : (S.L : ℝ) ^ (2 * jj y) = c ^ 2 := by simp only [c]; ring
    rw [e3] at h3
    rw [e2] at h2
    have hc3 : 0 < c ^ 3 := by positivity
    have hA : c⁻¹ ^ 3 * (S.L : ℝ) ^ (3 * jj y') ≤ (S.L : ℝ) ^ 4 * e := by
      rw [inv_pow, inv_mul_le_iff₀ hc3]; nlinarith
    have hB : c⁻¹ ^ 3 * (S.L : ℝ) ^ (2 * jj y') ≤ (S.L : ℝ) ^ 4 * e * c⁻¹ := by
      rw [show c⁻¹ ^ 3 * (S.L : ℝ) ^ (2 * jj y') = c⁻¹ * (c⁻¹ ^ 2 * (S.L : ℝ) ^ (2 * jj y')) by ring]
      have : c⁻¹ ^ 2 * (S.L : ℝ) ^ (2 * jj y') ≤ (S.L : ℝ) ^ 4 * e := by
        rw [inv_pow, inv_mul_le_iff₀ (by positivity)]; nlinarith
      calc c⁻¹ * (c⁻¹ ^ 2 * (S.L : ℝ) ^ (2 * jj y')) ≤ c⁻¹ * ((S.L : ℝ) ^ 4 * e) := by gcongr
        _ = _ := by ring
    calc c⁻¹ ^ 3 * (16 * S.L * Cs * ((S.L : ℝ) ^ (3 * jj y') * F + (S.L : ℝ) ^ (2 * jj y') * G))
        = 16 * S.L * Cs * ((c⁻¹ ^ 3 * (S.L : ℝ) ^ (3 * jj y')) * F + (c⁻¹ ^ 3 * (S.L : ℝ) ^ (2 * jj y')) * G) := by
          ring
      _ ≤ 16 * S.L * Cs * (((S.L : ℝ) ^ 4 * e) * F + ((S.L : ℝ) ^ 4 * e * c⁻¹) * G) := by gcongr
      _ = 16 * S.L * Cs * (S.L : ℝ) ^ 4 * e * (F + c⁻¹ * G) := by ring
  have hexp : Real.exp (2 * δ₁) * Real.exp (-(δ₁ * S.dF y y')) * e = Real.exp (2 * δ₁) * D := by
    simp only [e, D]; rw [mul_assoc, ← Real.exp_add]; ring_nf
  set K := Cs * C2 S δ₁ Cs CN * S.L * Real.exp S.L + Cs * CF S δ₁
  have hK : 0 ≤ K := by positivity
  have hrest : Real.sqrt (nsq fun k => Zu k z) + Real.sqrt (nsq fun k => Nu k z) +
      Real.sqrt (nsq fun k => Fu k z) ≤
      16 * (S.L : ℝ) ^ 5 * Real.exp (2 * δ₁) * Cs * K * D * (F + c⁻¹ * G) := by
    have hM0' : 0 ≤ c⁻¹ ^ 3 * M0 S Cs y' F G := by positivity
    calc _ ≤ K * Real.exp (-phiY S δ₁ y' z) * (c⁻¹ ^ 3 * M0 S Cs y' F G) := by
          have := add_le_add hzn hfu
          calc _ ≤ _ := this
            _ = _ := by ring
      _ ≤ K * (Real.exp (2 * δ₁) * Real.exp (-(δ₁ * S.dF y y'))) *
            (16 * S.L * Cs * (S.L : ℝ) ^ 4 * e * (F + c⁻¹ * G)) := by gcongr
      _ = 16 * (S.L : ℝ) ^ 5 * Cs * K * (Real.exp (2 * δ₁) * Real.exp (-(δ₁ * S.dF y y')) * e) *
            (F + c⁻¹ * G) := by ring
      _ = _ := by rw [hexp]; ring
  have hFG : F ≤ F + c⁻¹ * G := le_add_of_nonneg_right (by positivity)
  have hf1' : Real.sqrt (nsq fun k => f k z) ≤ 2 * D * (F + c⁻¹ * G) :=
    hf1.trans (mul_le_mul_of_nonneg_left hFG (by positivity))
  have hsum := add_le_add hf1' hrest
  have e1 : Real.sqrt (nsq fun k => f k z) + (Real.sqrt (nsq fun k => Zu k z) +
      (Real.sqrt (nsq fun k => Nu k z) + Real.sqrt (nsq fun k => Fu k z))) =
      Real.sqrt (nsq fun k => f k z) + (Real.sqrt (nsq fun k => Zu k z) + Real.sqrt (nsq fun k => Nu k z) +
        Real.sqrt (nsq fun k => Fu k z)) := by ring
  have e2 : 2 * D * (F + c⁻¹ * G) + 16 * (S.L : ℝ) ^ 5 * Real.exp (2 * δ₁) * Cs * K * D * (F + c⁻¹ * G) =
      CDel S δ₁ Cs CN * D * (F + c⁻¹ * G) := by
    unfold CDel; simp only [K]; ring
  linarith [hA, hB, hC, hsum, e2]

end SFBHyp

end SFBounds
end CoreLean

end
