/-
`prop:sf-bounds` of BALABAN_CORE.tex (`4252790331fd`), the step "First differences", `eq:sf-gradient`, on the fine
lattice (`a₀ = 1`), for `g = 0`: at a bond `b = (z, z + e_ν)`, `z ∈ Δ(y)`,
`|(D_𝐔u)(b)| ≤ C_g e^{-(7/8)δ₁d(y, y')}(a_j‖f‖_∞ + max_μ‖g_μ‖_∞)` (with `G` carried along).

* `diff_bound`: `|u(z + e_ν) - u(z)| ≤ C_d a_j⁻²e^{-φ(z)}M₀`, `C_d = 3L⁴ + K_sf(½)C_Θ`: in the layers `0`, `1` from the
  values (`value_le_wN`), in the layers `j ≥ 2` from `lem:sf-local`(iii) with `β = ½`, `Γ = 0`.
* `cov_bound`: `|(D_𝐔u)(b)| ≤ (C_d + 24α₁L²C₂)a_j⁻²e^{-φ(z)}M₀`, with `(D_𝐔u)(b) = (∂u)(b) + (Ad_{𝐔(b)} - 1)u(z + e_ν)` and
  `eq:adjoint-lipschitz`.
* `gradient`: `eq:sf-gradient`.
-/
import CoreLean.SFTheta

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

/-- The number `C_d = 3L⁴ + K_sf(½)C_Θ`. -/
def Cd (S : SeqDom) (δ₁ Cs CN : ℝ) : ℝ := 3 * (S.L : ℝ) ^ 4 + Ksfb CN (1 / 2) * CTh S δ₁ Cs

/-- The number `C_g` of `eq:sf-gradient`. -/
def Cg (S : SeqDom) (δ₁ Cs CN α₁ : ℝ) : ℝ :=
  16 * (S.L : ℝ) ^ 5 * Real.exp (2 * δ₁) * Cs * (Cd S δ₁ Cs CN + 24 * α₁ * (S.L : ℝ) ^ 2 * C2 S δ₁ Cs CN)

lemma nsq_neg_add (v w : Fin m → Mat) : (nsq fun k => v k - w k) = nsq fun k => v k + -w k := by
  simp only [sub_eq_add_neg]

lemma nsq_neg (w : Fin m → Mat) : (nsq fun k => -w k) = nsq w := by
  simp only [nsq, hs2, conjTranspose_neg, neg_mul_neg]

lemma sqrt_nsq_sub_le [NeZero N] (v w : Fin m → Mat) :
    Real.sqrt (nsq fun k => v k - w k) ≤ Real.sqrt (nsq v) + Real.sqrt (nsq w) := by
  rw [nsq_neg_add]
  refine (nsq_add_le v (fun k => -w k)).trans ?_
  rw [show (nsq fun k => -w k) = nsq w from nsq_neg w]

/-- `|(Ad_W - 1)v| ≤ c|v|` member by member gives it for the family. -/
lemma sqrt_nsq_map_le {T : Mat → Mat} {c : ℝ} (hc : 0 ≤ c) (hT : ∀ Z, hs (T Z) ≤ c * hs Z) (v : Fin m → Mat) :
    Real.sqrt (nsq fun k => T (v k)) ≤ c * Real.sqrt (nsq v) := by
  rw [← Real.sqrt_sq hc, ← Real.sqrt_mul (sq_nonneg c)]
  refine Real.sqrt_le_sqrt ?_
  simp only [nsq, mul_sum]
  refine sum_le_sum fun k _ => ?_
  rw [← hs_sq, ← hs_sq, ← mul_pow]
  exact pow_le_pow_left₀ (hs_nonneg _) (hT _) 2

lemma tc_e4 {ε : ℝ} (hε : 0 ≤ ε) (n₀ : Fin 4 → ℤ) (ν μ : Fin 4) : |tc ε n₀ (n₀ + e4 ν) μ| ≤ ε := by
  unfold tc
  rw [show ((n₀ + e4 ν) μ - n₀ μ : ℤ) = e4 ν μ by simp]
  by_cases h : μ = ν
  · subst h; simp [e4, abs_of_nonneg hε]
  · simp [e4, Pi.single_eq_of_ne h, hε]

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

lemma hRM1' : 1 ≤ S.R * S.L ^ S.mM := by have := Nat.one_le_pow S.mM S.L S.Lpos; nlinarith [S.one_le_R]

/-- `e^{-φ(z + e_ν)} ≤ 2e^{-φ(z)}`. -/
lemma exp_phi_unit (z : Site NF) (ν : Fin 4) :
    Real.exp (-phiY S δ₁ y' (z + unit _ ν)) ≤ 2 * Real.exp (-phiY S δ₁ y' z) := by
  have hd := (S.wdist_unit_le_sc H.hRM1' z ν).1
  have hL := H.L3
  have hδ := H.hδ
  have hδ0 := H.hδ0
  have hpow : (S.L : ℝ) * ((S.L : ℝ) ^ jj z)⁻¹ ≤ S.L := by
    have : ((S.L : ℝ) ^ jj z)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith))
    nlinarith
  have hlip := (abs_le.1 (H.phi_lip' z (z + unit _ ν))).2
  have hδL : δ₁ * S.L ≤ 1 / 128 := by
    calc δ₁ * S.L ≤ 1 / (128 * S.L) * S.L := mul_le_mul_of_nonneg_right hδ (by linarith)
      _ = 1 / 128 := by field_simp
  have hdF : S.dF z (z + unit _ ν) ≤ S.L := hd.trans hpow
  calc Real.exp (-phiY S δ₁ y' (z + unit _ ν)) ≤ Real.exp (1 / 128) * Real.exp (-phiY S δ₁ y' z) := by
        rw [← Real.exp_add]; refine Real.exp_le_exp.2 ?_
        have : δ₁ * S.dF z (z + unit _ ν) ≤ δ₁ * S.L := mul_le_mul_of_nonneg_left hdF hδ0.le
        linarith
    _ ≤ 2 * Real.exp (-phiY S δ₁ y' z) := by
        gcongr
        calc Real.exp (1 / 128) ≤ Real.exp (Real.log 2) :=
              Real.exp_le_exp.2 (by have := Real.log_two_gt_d9; linarith)
          _ = 2 := Real.exp_log (by norm_num)

/-- **The first differences**: `|u(z + e_ν) - u(z)| ≤ C_d a_j⁻²e^{-φ(z)}M₀` when `g = 0`. -/
theorem diff_bound [NeZero N] (hg0 : ∀ k μ x, g k μ x = 0) (z : Site NF) (ν : Fin 4) :
    Real.sqrt (nsq fun k => u k (z + unit _ ν) - u k z) ≤
      Cd S δ₁ Cs CN * ((S.L : ℝ) ^ jj z)⁻¹ ^ 2 * Real.exp (-phiY S δ₁ y' z) * M0 S Cs y' F G := by
  have hL := H.L3
  have hL0 : (0 : ℝ) < S.L := by linarith
  have hM := H.wN_le_M0
  have hM0 := H.M0_nonneg
  set c : ℝ := (S.L : ℝ) ^ jj z with hc_def
  have hc : 0 < c := by positivity
  set E := Real.exp (-phiY S δ₁ y' z)
  have hE : 0 < E := Real.exp_pos _
  have hCTh : 0 ≤ CTh S δ₁ Cs := by unfold CTh CF; have := H.c1_nonneg; have := H.hCs; positivity
  have hKb : 0 ≤ Ksfb CN (1 / 2) := by
    unfold Ksfb; have := KH_ge (1 / 2) (by norm_num); have := KD_ge (1 / 2) (by norm_num) (by norm_num)
    have := H.hCN; positivity
  rcases Nat.lt_or_ge (jj z) 2 with hj | hj
  · have h1 := value_le_wN S (phiY S δ₁ y') u z
    have h2 := value_le_wN S (phiY S δ₁ y') u (z + unit _ ν)
    have hsc := (S.sc_sub_le H.hRM1' z ν).2
    have he := H.exp_phi_unit z ν
    have hW := Real.sqrt_nonneg (wN S (eF S (phiY S δ₁ y') u))
    have hcz : c ≤ S.L := by
      have := pow_le_pow_right₀ (show (1 : ℝ) ≤ S.L by linarith) (show jj z ≤ 1 by omega)
      simpa [c] using this
    have hcz' : (S.L : ℝ) ^ jj (z + unit _ ν) ≤ S.L ^ 2 := pow_le_pow_right₀ (by linarith) (by omega)
    have hinv : 1 ≤ (S.L : ℝ) ^ 2 * c⁻¹ ^ 2 := by
      rw [← mul_pow, one_le_sq_iff_one_le_abs, abs_of_pos (by positivity), le_mul_inv_iff₀ hc, one_mul]
      exact hcz
    calc Real.sqrt (nsq fun k => u k (z + unit _ ν) - u k z)
        ≤ Real.sqrt (nsq fun k => u k (z + unit _ ν)) + Real.sqrt (nsq fun k => u k z) := sqrt_nsq_sub_le _ _
      _ ≤ (S.L : ℝ) ^ 2 * (2 * E) * M0 S Cs y' F G + S.L * E * M0 S Cs y' F G := by
          exact add_le_add (h2.trans (by gcongr)) (h1.trans (by gcongr))
      _ ≤ 3 * (S.L : ℝ) ^ 2 * E * M0 S Cs y' F G := by
          have h0 : 0 ≤ E * M0 S Cs y' F G := mul_nonneg hE.le hM0
          have : (S.L : ℝ) * (E * M0 S Cs y' F G) ≤ (S.L : ℝ) ^ 2 * (E * M0 S Cs y' F G) :=
            mul_le_mul_of_nonneg_right (by nlinarith) h0
          nlinarith
      _ ≤ 3 * (S.L : ℝ) ^ 2 * E * M0 S Cs y' F G * ((S.L : ℝ) ^ 2 * c⁻¹ ^ 2) :=
          le_mul_of_one_le_right (by positivity) hinv
      _ ≤ Cd S δ₁ Cs CN * c⁻¹ ^ 2 * E * M0 S Cs y' F G := by
          unfold Cd
          have : 0 ≤ Ksfb CN (1 / 2) * CTh S δ₁ Cs * c⁻¹ ^ 2 * E * M0 S Cs y' F G := by positivity
          nlinarith
  · obtain ⟨Fb, Gb, Hs, hTh⟩ := H.theta_at hj
    have hg0' : ∀ μ n, (sfData S (jj z) u f g Nu Fu Zc).g μ n = 0 := fun μ n => by
      simp only [sfData, SFBox.liftM, hg0, smul_zero]; rfl
    have hc2 : c⁻¹ ≤ 2 := (inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith))).trans (by norm_num)
    have h3 := Hs.sf_local_iii (β := 1 / 2) (Γ := 0) (by norm_num) (by norm_num) le_rfl
      (fun μ n n' _ _ _ => by rw [hg0', hg0', sub_zero, norm_zero]; simp) ν
      (z := xbar z) (z' := xbar z) (fun μ => by simp [tc])
      (fun μ => (tc_e4 (inv_pos.2 hc).le _ ν μ).trans hc2)
      (fun μ => by simp [tc])
      (fun μ => (tc_e4 (inv_pos.2 hc).le _ ν μ).trans hc2)
    have h3' := h3.1
    simp only [add_zero] at h3'
    -- `‖dfw‖ = c√N|u(z + e_ν) - u(z)|`
    have hdfw : ‖dfw c⁻¹ ν (sfData S (jj z) u f g Nu Fu Zc).u (xbar z)‖ =
        c * (Real.sqrt N * Real.sqrt (nsq fun k => u k (z + unit _ ν) - u k z)) := by
      simp only [dfw, sfData, inv_inv]
      rw [show (SFBox.liftM u (xbar z + e4 ν) - SFBox.liftM u (xbar z) : VS N m) =
          SFBox.liftM (fun k x => u k (x + unit _ ν) - u k x) (xbar z) by
        simp only [SFBox.liftM, castS_add_e4]; rw [← vecOf_subM]]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc, norm_liftM, castS_xbar]
    rw [hdfw] at h3'
    have hN : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N))
    have h4 : c * (Real.sqrt N * Real.sqrt (nsq fun k => u k (z + unit _ ν) - u k z)) ≤
        Ksfb CN (1 / 2) * (Real.sqrt N * (CTh S δ₁ Cs * c⁻¹ * E * M0 S Cs y' F G)) :=
      h3'.trans (mul_le_mul_of_nonneg_left hTh hKb)
    have h5 : Real.sqrt (nsq fun k => u k (z + unit _ ν) - u k z) ≤
        Ksfb CN (1 / 2) * CTh S δ₁ Cs * c⁻¹ ^ 2 * E * M0 S Cs y' F G := by
      have e : Ksfb CN (1 / 2) * (Real.sqrt N * (CTh S δ₁ Cs * c⁻¹ * E * M0 S Cs y' F G)) =
          c * (Real.sqrt N * (Ksfb CN (1 / 2) * CTh S δ₁ Cs * c⁻¹ ^ 2 * E * M0 S Cs y' F G)) := by
        field_simp
      rw [e] at h4
      exact le_of_mul_le_mul_left (le_of_mul_le_mul_left h4 hc) hN
    refine h5.trans ?_
    unfold Cd
    have : 0 ≤ 3 * (S.L : ℝ) ^ 4 * c⁻¹ ^ 2 * E * M0 S Cs y' F G := by positivity
    nlinarith

/-- **The covariant first differences**: `|(D_𝐔u)(b)| ≤ (C_d + 24α₁L²C₂)a_j⁻²e^{-φ(z)}M₀` when `g = 0`. -/
theorem cov_bound [NeZero N] (hg0 : ∀ k μ x, g k μ x = 0) (z : Site NF) (ν : Fin 4) :
    Real.sqrt (nsq fun k => Dfw 1 (cfgX X) ν (u k) z) ≤
      (Cd S δ₁ Cs CN + 24 * α₁ * (S.L : ℝ) ^ 2 * C2 S δ₁ Cs CN) * ((S.L : ℝ) ^ jj z)⁻¹ ^ 2 *
        Real.exp (-phiY S δ₁ y' z) * M0 S Cs y' F G := by
  have hL := H.L3
  have hL0 : (0 : ℝ) < S.L := by linarith
  have hM0 := H.M0_nonneg
  set c : ℝ := (S.L : ℝ) ^ jj z with hc_def
  have hc : 0 < c := by positivity
  set E := Real.exp (-phiY S δ₁ y' z)
  have hE : 0 < E := Real.exp_pos _
  have hα0 := H.hα0
  have hC2 : 0 ≤ C2 S δ₁ Cs CN := by
    unfold C2 CTh CF Ksf; have := H.hCN; have := H.c1_nonneg; have := H.hCs; positivity
  -- the decomposition `D_𝐔u = ∂u + (Ad_𝐔 - 1)u(· + e_ν)`
  have hsplit : (fun k => Dfw 1 (cfgX X) ν (u k) z) =
      fun k => (u k (z + unit _ ν) - u k z) + (Ad (cfgX X ν z) (u k (z + unit _ ν)) - u k (z + unit _ ν)) := by
    funext k; simp only [Dfw, inv_one, one_smul]; abel
  rw [hsplit]
  refine (nsq_add_le _ _).trans ?_
  have h1 := H.diff_bound hg0 z ν
  -- the field at the bond
  set i := min (jj z) (jj (z + unit _ ν))
  have hsc := S.sc_sub_le H.hRM1' z ν
  have hiz : jj z ≤ i + 1 := by simp only [i]; omega
  have hz1 : S.ef z ∈ S.Ω i := (S.toDomSeq).Ω_anti (min_le_left _ _) (S.ef_mem_sc z)
  have hz2 : S.ef (z + unit _ ν) ∈ S.Ω i := (S.toDomSeq).Ω_anti (min_le_right _ _) (S.ef_mem_sc _)
  have hX := H.hX.hA i z ν hz1 hz2
  have hLi : ((S.L : ℝ) ^ i)⁻¹ ≤ S.L * c⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hc, inv_mul_le_iff₀ (by positivity), hc_def, ← pow_succ]
    exact pow_le_pow_right₀ (by linarith) (by omega)
  have hα32 : α₁ ≤ 1 / 32 := by have := H.hα; nlinarith
  have hXs : ‖X ν z‖ ≤ 1 / 32 := by
    have : ((S.L : ℝ) ^ i)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith))
    calc ‖X ν z‖ ≤ α₁ * ((S.L : ℝ) ^ i)⁻¹ := hX
      _ ≤ α₁ * 1 := by gcongr
      _ ≤ 1 / 32 := by linarith
  have h2 := sqrt_nsq_map_le (T := fun Z => Ad (cfgX X ν z) Z - Z) (by positivity)
    (fun Z => hs_Ad_exp_sub_le hXs Z) (fun k => u k (z + unit _ ν))
  have hp := H.pointwise (z + unit _ ν)
  have he := H.exp_phi_unit z ν
  have hLj : ((S.L : ℝ) ^ jj (z + unit _ ν))⁻¹ ≤ S.L * c⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hc, inv_mul_le_iff₀ (by positivity), hc_def, ← pow_succ]
    exact pow_le_pow_right₀ (by linarith) (by omega)
  have h3 : Real.sqrt (nsq fun k => u k (z + unit _ ν)) ≤ C2 S δ₁ Cs CN * (S.L * c⁻¹) * (2 * E) * M0 S Cs y' F G :=
    hp.trans (by gcongr)
  have h4 : Real.sqrt (nsq fun k => Ad (cfgX X ν z) (u k (z + unit _ ν)) - u k (z + unit _ ν)) ≤
      24 * α₁ * (S.L : ℝ) ^ 2 * C2 S δ₁ Cs CN * c⁻¹ ^ 2 * E * M0 S Cs y' F G := by
    refine h2.trans ?_
    calc 6 * ‖X ν z‖ * Real.sqrt (nsq fun k => u k (z + unit _ ν))
        ≤ 6 * (α₁ * (S.L * c⁻¹)) * (C2 S δ₁ Cs CN * (S.L * c⁻¹) * (2 * E) * M0 S Cs y' F G) := by
          gcongr
          exact hX.trans (mul_le_mul_of_nonneg_left hLi hα0)
      _ = 12 * α₁ * (S.L : ℝ) ^ 2 * C2 S δ₁ Cs CN * c⁻¹ ^ 2 * E * M0 S Cs y' F G := by ring
      _ ≤ _ := by
          have : 0 ≤ α₁ * (S.L : ℝ) ^ 2 * C2 S δ₁ Cs CN * c⁻¹ ^ 2 * E * M0 S Cs y' F G := by positivity
          nlinarith
  calc _ ≤ Cd S δ₁ Cs CN * c⁻¹ ^ 2 * E * M0 S Cs y' F G +
        24 * α₁ * (S.L : ℝ) ^ 2 * C2 S δ₁ Cs CN * c⁻¹ ^ 2 * E * M0 S Cs y' F G := add_le_add h1 h4
    _ = _ := by ring

/-- **`eq:sf-gradient`**: at a bond `b = (z, z + e_ν)` with `z ∈ Δ(y)`,
`|(D_𝐔u)(b)| ≤ C_g e^{-(7/8)δ₁d(y, y')}(a_jF + G)` when `g = 0`. -/
theorem gradient [NeZero N] (hg0 : ∀ k μ x, g k μ x = 0) {y z : Site NF} (hy : y ∈ detB S.toDomSeq)
    (hz : z ∈ Blk S.toDomSeq (jj y) y) (ν : Fin 4) :
    Real.sqrt (nsq fun k => Dfw 1 (cfgX X) ν (u k) z) ≤
      Cg S δ₁ Cs CN α₁ * Real.exp (-(7 / 8 * δ₁ * S.dF y y')) * ((S.L : ℝ) ^ jj y * F + G) := by
  have hcb := H.cov_bound hg0 z ν
  rw [sc_of_mem_blk S hy hz] at hcb
  have hL := H.L3
  have hL0 : (0 : ℝ) < S.L := by linarith
  have hF := H.hF
  have hG := H.hG
  have hCs := H.hCs
  have hα0 := H.hα0
  set c : ℝ := (S.L : ℝ) ^ jj y
  have hc : 0 < c := by positivity
  set e := Real.exp (δ₁ / 8 * S.dF y y')
  have he : 0 < e := Real.exp_pos _
  have h3 := H.scale_nat y 3 (by norm_num)
  have h2 := H.scale_nat y 2 (by norm_num)
  have hph := H.phi_block hy hz
  have hK : 0 ≤ Cd S δ₁ Cs CN + 24 * α₁ * (S.L : ℝ) ^ 2 * C2 S δ₁ Cs CN := by
    unfold Cd C2 CTh CF Ksf Ksfb
    have := H.hCN; have := H.c1_nonneg
    have := KH_ge (1 / 2) (by norm_num); have := KD_ge (1 / 2) (by norm_num) (by norm_num)
    positivity
  have hM : c⁻¹ ^ 2 * M0 S Cs y' F G ≤ 16 * S.L * Cs * (S.L : ℝ) ^ 4 * e * (c * F + G) := by
    unfold M0
    have e3 : (S.L : ℝ) ^ (3 * jj y) = c ^ 2 * c := by simp only [c]; ring
    have e2 : (S.L : ℝ) ^ (2 * jj y) = c ^ 2 := by simp only [c]; ring
    rw [e3] at h3
    rw [e2] at h2
    have hc2 : 0 < c ^ 2 := by positivity
    have hA : c⁻¹ ^ 2 * (S.L : ℝ) ^ (3 * jj y') ≤ (S.L : ℝ) ^ 4 * e * c := by
      rw [inv_pow, inv_mul_le_iff₀ hc2]; nlinarith
    have hB : c⁻¹ ^ 2 * (S.L : ℝ) ^ (2 * jj y') ≤ (S.L : ℝ) ^ 4 * e := by
      rw [inv_pow, inv_mul_le_iff₀ hc2]; nlinarith
    calc c⁻¹ ^ 2 * (16 * S.L * Cs * ((S.L : ℝ) ^ (3 * jj y') * F + (S.L : ℝ) ^ (2 * jj y') * G))
        = 16 * S.L * Cs * ((c⁻¹ ^ 2 * (S.L : ℝ) ^ (3 * jj y')) * F + (c⁻¹ ^ 2 * (S.L : ℝ) ^ (2 * jj y')) * G) := by
          ring
      _ ≤ 16 * S.L * Cs * (((S.L : ℝ) ^ 4 * e * c) * F + ((S.L : ℝ) ^ 4 * e) * G) := by gcongr
      _ = 16 * S.L * Cs * (S.L : ℝ) ^ 4 * e * (c * F + G) := by ring
  have hexp : Real.exp (2 * δ₁) * Real.exp (-(δ₁ * S.dF y y')) * e =
      Real.exp (2 * δ₁) * Real.exp (-(7 / 8 * δ₁ * S.dF y y')) := by
    simp only [e]; rw [mul_assoc, ← Real.exp_add]; ring_nf
  have hM0 := H.M0_nonneg
  calc Real.sqrt (nsq fun k => Dfw 1 (cfgX X) ν (u k) z)
      ≤ (Cd S δ₁ Cs CN + 24 * α₁ * (S.L : ℝ) ^ 2 * C2 S δ₁ Cs CN) * c⁻¹ ^ 2 *
          Real.exp (-phiY S δ₁ y' z) * M0 S Cs y' F G := hcb
    _ = (Cd S δ₁ Cs CN + 24 * α₁ * (S.L : ℝ) ^ 2 * C2 S δ₁ Cs CN) * Real.exp (-phiY S δ₁ y' z) *
          (c⁻¹ ^ 2 * M0 S Cs y' F G) := by ring
    _ ≤ (Cd S δ₁ Cs CN + 24 * α₁ * (S.L : ℝ) ^ 2 * C2 S δ₁ Cs CN) *
          (Real.exp (2 * δ₁) * Real.exp (-(δ₁ * S.dF y y'))) *
          (16 * S.L * Cs * (S.L : ℝ) ^ 4 * e * (c * F + G)) := by
        have : 0 ≤ c⁻¹ ^ 2 * M0 S Cs y' F G := by positivity
        gcongr
    _ = 16 * (S.L : ℝ) ^ 5 * Cs * (Cd S δ₁ Cs CN + 24 * α₁ * (S.L : ℝ) ^ 2 * C2 S δ₁ Cs CN) *
          (Real.exp (2 * δ₁) * Real.exp (-(δ₁ * S.dF y y')) * e) * (c * F + G) := by ring
    _ = _ := by rw [hexp]; unfold Cg; ring


end SFBHyp

end SFBounds
end CoreLean

end
