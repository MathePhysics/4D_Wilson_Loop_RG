/-
`prop:sf-bounds` of BALABAN_CORE.tex (`4252790331fd`), the step "The bounds of the values", `eq:sf-pointwise`, on the
fine lattice (`a₀ = 1`): for the data `f`, `g` supported in `Δ̃(y')` and `u` subject to `(H1)` (for these data) and
`(H2)`, with `φ = δ₁d(·, y')` and `M₀ = 16LC_*(a_{j'}³‖f‖_∞ + a_{j'}²max_μ‖g_μ‖_∞)`,
`|u(z)| ≤ C₂a_{j(z)}⁻¹e^{-φ(z)}M₀` at every site.

* `nsq_add_le`: `|v + w| ≤ |v| + |w|`.
* `SFBHyp`: the hypotheses of `prop:sf-bounds` at one source `y'` (the parameters, `(H1)` for the data, `(H2)` with the
  hypotheses on `𝒵`, `𝒩`, `𝓕`).
* `wN_le_M0`: `‖e^φu‖_w ≤ M₀` (`eq:sf-weighted-source`).
* `box_dist`: the fact (c): a site under `Q_{8+2L}` about `z` of a scale `j ≥ 2` is at a weighted distance of at most
  `4(8 + 2L)L` from `z`.
* `pointwise`: `eq:sf-pointwise` with `C₂ = L² + K_sf(C_𝒩)C_Θ`, `C_Θ = (25L + L⁶ + L⁴ + C_*C_𝓕L³)e^L`,
  `C_𝓕 = e^{7δ₁}L⁴c₁(½, δ₁)`.
-/
import CoreLean.SFBoxSum

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

/-- **`|v + w| ≤ |v| + |w|`.** -/
lemma nsq_add_le [NeZero N] (v w : Fin m → Mat) :
    Real.sqrt (nsq fun k => v k + w k) ≤ Real.sqrt (nsq v) + Real.sqrt (nsq w) := by
  have hN : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N))
  have key : ∀ y : Fin m → Mat, Real.sqrt (nsq y) = ‖vecOf (N := N) y‖ / Real.sqrt N := fun y => by
    rw [eq_div_iff hN.ne', ← Real.sqrt_sq (norm_nonneg _), normV_sq, ← Real.sqrt_mul (nsq_nonneg _),
      mul_comm]
    simp [nsq]
  rw [key, key, key, ← add_div]
  refine div_le_div_of_nonneg_right ?_ hN.le
  rw [show (vecOf fun k => v k + w k) = vecOf (N := N) v + vecOf w by ext p; rfl]
  exact norm_add_le _ _

/-- **The hypotheses of `prop:sf-bounds` at one source `y'`.** -/
structure SFBHyp (X : Fin 4 → Site NF → Mat) (α₁ : ℝ) (ΩD : Set (Site NF)) (δ₁ Cs CN : ℝ)
    (u f : Fin m → Site NF → Mat) (g : Fin m → Fin 4 → Site NF → Mat) (Zu Nu Fu : Fin m → Site NF → Mat)
    (Zc : Site NF → (Fin 4 → ℤ) → (VS N m →L[ℝ] VS N m)) (y' : Site NF) (F G : ℝ) : Prop where
  hX : RegField S X α₁
  hα0 : 0 ≤ α₁
  hα : 64 * (S.L : ℝ) ^ 2 * α₁ ≤ 1
  hRM8 : 8 * (S.L : ℝ) ^ 2 ≤ RMS
  hRMs : 32 * Real.log S.L / δ₁ ≤ RMS
  hRM1 : (S.toContSeq).r1 (1 / 2) δ₁ ≤ RMS
  hδ0 : 0 < δ₁
  hδ : δ₁ ≤ 1 / (128 * S.L)
  hD : ∀ x, S.ef x ∈ S.Ω 1 → x ∈ ΩD
  hCs : 1 ≤ Cs
  hCN : 0 ≤ CN
  hy' : y' ∈ detB S.toDomSeq
  hF : 0 ≤ F
  hG : 0 ≤ G
  hfs : ∀ k x, (S.L : ℝ) ^ (S.toDomSeq).sc y' ≤ (dinf x y' : ℝ) → f k x = 0
  hgs : ∀ k μ x, (S.L : ℝ) ^ (S.toDomSeq).sc y' ≤ (dinf x y' : ℝ) → g k μ x = 0
  hfb : ∀ x, nsq (fun k => f k x) ≤ F ^ 2
  hgb : ∀ μ x, nsq (fun k => g k μ x) ≤ G ^ 2
  H1 : ∀ ph : Site NF → ℝ, (∀ x x', |ph x - ph x'| ≤ δ₁ * S.dF x x') →
    Real.sqrt (wN S (eF S ph u)) + Real.sqrt (dN S (eF S ph u)) ≤ Cs * (Real.sqrt (fN S ph f) + Real.sqrt (gN S ph g))
  H2 : LocalEqn S X ΩD u f g Zu Nu Fu Zc
  hZs : ∀ x, 2 ≤ (S.toDomSeq).sc x → ∀ z, InQr ((S.L : ℝ) ^ (S.toDomSeq).sc x)⁻¹ (xbar x) 8 z →
    ((S.L : ℝ) ^ (S.toDomSeq).sc x) ^ 2 * ∑ e ∈ Eoff, ‖Zc (castS z) e‖ ≤ 1 / 4
  hN1 : ∀ x, 2 ≤ (S.toDomSeq).sc x → ∀ z, InQr ((S.L : ℝ) ^ (S.toDomSeq).sc x)⁻¹ (xbar x) 8 z →
    ‖(sfData S ((S.toDomSeq).sc x) u f g Nu Fu Zc).Nu z‖ ≤
      CN * pn ((S.L : ℝ) ^ (S.toDomSeq).sc x)⁻¹ (QF ((S.L : ℝ) ^ (S.toDomSeq).sc x)⁻¹ (xbar x) (8 + 2 * S.L)) 2
        (fun z => ‖SFBox.liftM u z‖)
  hFu : ∀ z, Real.sqrt (nsq fun k => Fu k z) ≤ Cs * ((S.L : ℝ) ^ (2 * (S.toDomSeq).sc z))⁻¹ *
    ∑ x', ((S.L : ℝ) ^ (4 * (S.toDomSeq).sc x'))⁻¹ * Real.exp (-(2 * δ₁ * S.dF z x')) * Real.sqrt (nsq fun k => u k x')

/-- The weight `φ = δ₁d(·, y')`. -/
def phiY (δ₁ : ℝ) (y' : Site NF) : Site NF → ℝ := fun x => δ₁ * S.dF x y'

/-- `M₀ = 16LC_*(a_{j'}³F + a_{j'}²G)`. -/
def M0 (Cs : ℝ) (y' : Site NF) (F G : ℝ) : ℝ :=
  16 * S.L * Cs * ((S.L : ℝ) ^ (3 * jj y') * F + (S.L : ℝ) ^ (2 * jj y') * G)

/-- The number `C_𝓕 = e^{7δ₁}L⁴c₁(½, δ₁)` of `eq:sf-far-term`. -/
def CF (S : SeqDom) (δ₁ : ℝ) : ℝ := Real.exp (7 * δ₁) * (S.L : ℝ) ^ (4 : ℝ) * (S.toContSeq).c1 (1 / 2) δ₁

/-- The number `C_Θ`. -/
def CTh (S : SeqDom) (δ₁ Cs : ℝ) : ℝ :=
  (25 * S.L + (S.L : ℝ) ^ 6 + (S.L : ℝ) ^ 4 + Cs * CF S δ₁ * (S.L : ℝ) ^ 3) * Real.exp S.L

/-- The number `C₂` of `eq:sf-pointwise`. -/
def C2 (S : SeqDom) (δ₁ Cs CN : ℝ) : ℝ := (S.L : ℝ) ^ 2 + Ksf CN * CTh S δ₁ Cs

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

lemma L3 : (3 : ℝ) ≤ S.L := by exact_mod_cast S.three_le_L

lemma hRML : (S.L : ℝ) ≤ RMS := by have := H.hRM8; have := H.L3; nlinarith

lemma phi_lip' : ∀ x x', |phiY S δ₁ y' x - phiY S δ₁ y' x'| ≤ δ₁ * S.dF x x' :=
  fun x x' => phi_lip S H.hδ0.le y' x x'

lemma M0_nonneg : 0 ≤ M0 S Cs y' F G := by
  have := H.hCs; have := H.hF; have := H.hG; have := S.Lpos; unfold M0; positivity

/-- **`‖e^φu‖_w ≤ M₀`** (`eq:sf-weighted-source` and `(H1)`). -/
theorem wN_le_M0 : Real.sqrt (wN S (eF S (phiY S δ₁ y') u)) ≤ M0 S Cs y' F G := by
  have h1 := H.H1 _ H.phi_lip'
  have hf : Real.sqrt (fN S (phiY S δ₁ y') f) ≤ 8 * (S.L : ℝ) ^ (3 * jj y' + 1) * F :=
    weighted_source_f S H.hRML H.hδ0.le H.hδ H.hF H.hfs H.hfb
  have hg : Real.sqrt (gN S (phiY S δ₁ y') g) ≤ 16 * (S.L : ℝ) ^ (2 * jj y') * G :=
    weighted_source_g S H.hRML H.hδ0.le H.hδ H.hG H.hgs H.hgb
  have hd := Real.sqrt_nonneg (dN S (eF S (phiY S δ₁ y') u))
  have hL := H.L3
  have hCs := H.hCs
  have e1 : (S.L : ℝ) ^ (3 * jj y' + 1) = (S.L : ℝ) ^ (3 * jj y') * S.L := pow_succ _ _
  have hp3 : (0 : ℝ) ≤ (S.L : ℝ) ^ (3 * jj y') := by positivity
  have hp2 : (0 : ℝ) ≤ (S.L : ℝ) ^ (2 * jj y') := by positivity
  have hF := H.hF
  have hG := H.hG
  have a1 : 8 * ((S.L : ℝ) ^ (3 * jj y') * S.L) * F ≤ 16 * S.L * ((S.L : ℝ) ^ (3 * jj y') * F) := by
    have : 0 ≤ (S.L : ℝ) ^ (3 * jj y') * S.L * F := by positivity
    nlinarith
  have a2 : 16 * (S.L : ℝ) ^ (2 * jj y') * G ≤ 16 * S.L * ((S.L : ℝ) ^ (2 * jj y') * G) := by
    have : 0 ≤ (S.L : ℝ) ^ (2 * jj y') * G := by positivity
    nlinarith
  unfold M0
  calc Real.sqrt (wN S (eF S (phiY S δ₁ y') u))
      ≤ Cs * (Real.sqrt (fN S (phiY S δ₁ y') f) + Real.sqrt (gN S (phiY S δ₁ y') g)) := by linarith
    _ ≤ Cs * (8 * (S.L : ℝ) ^ (3 * jj y' + 1) * F + 16 * (S.L : ℝ) ^ (2 * jj y') * G) := by
        gcongr
    _ = Cs * (8 * ((S.L : ℝ) ^ (3 * jj y') * S.L) * F + 16 * (S.L : ℝ) ^ (2 * jj y') * G) := by rw [e1]
    _ ≤ Cs * (16 * S.L * ((S.L : ℝ) ^ (3 * jj y') * F) + 16 * S.L * ((S.L : ℝ) ^ (2 * jj y') * G)) :=
        mul_le_mul_of_nonneg_left (add_le_add a1 a2) (by linarith)
    _ = _ := by ring

/-- **The fact (c)**: a site under `Q_{8+2L}` about `z`, `j(z) ≥ 2`, lies within `d ≤ 4(8 + 2L)L` of `z`. -/
theorem box_dist {z : Site NF} (hj : 2 ≤ jj z) {w : Fin 4 → ℤ}
    (hw : InQr ((S.L : ℝ) ^ jj z)⁻¹ (xbar z) (8 + 2 * S.L) w) : S.dF z (castS w) ≤ 4 * (8 + 2 * S.L) * S.L := by
  have hL := H.L3
  have hRM := H.hRM8
  set c : ℝ := (S.L : ℝ) ^ jj z
  have hc : 0 < c := by positivity
  have hdw := dinf_castS_le hc z hw
  rw [dinf_comm] at hdw
  have h1 := S.dF_le_near (c := 9 + 2 * S.L) (by nlinarith) z (castS w) (by nlinarith)
  have hd1 : (d1 z (castS w) : ℝ) ≤ 4 * dinf z (castS w) := by exact_mod_cast d1_le_four_dinf S z (castS w)
  have hpow : c = S.L * (S.L : ℝ) ^ (jj z - 1) := by
    simp only [c]; rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ jj z)]
  have hp1 : (0 : ℝ) < (S.L : ℝ) ^ (jj z - 1) := by positivity
  refine h1.trans ?_
  rw [div_le_iff₀ hp1]
  calc (d1 z (castS w) : ℝ) ≤ 4 * dinf z (castS w) := hd1
    _ ≤ 4 * ((8 + 2 * S.L) * c) := by linarith
    _ = 4 * (8 + 2 * S.L) * S.L * (S.L : ℝ) ^ (jj z - 1) := by rw [hpow]; ring

lemma delta_box : δ₁ * (4 * (8 + 2 * S.L) * S.L) ≤ S.L - 4 * S.L * δ₁ := by
  have hL := H.L3
  have hδ := H.hδ
  have hδ0 := H.hδ0
  have h : δ₁ * S.L ≤ 1 / 128 := by
    calc δ₁ * S.L ≤ 1 / (128 * S.L) * S.L := mul_le_mul_of_nonneg_right hδ (by linarith)
      _ = 1 / 128 := by field_simp
  nlinarith

/-- `e^{-φ(w)} ≤ e^{L}e^{-φ(z)}` under the box about `z`. -/
lemma exp_phi_box {z : Site NF} (hj : 2 ≤ jj z) {w : Fin 4 → ℤ}
    (hw : InQr ((S.L : ℝ) ^ jj z)⁻¹ (xbar z) (8 + 2 * S.L) w) :
    Real.exp (-phiY S δ₁ y' (castS w)) ≤ Real.exp S.L * Real.exp (-phiY S δ₁ y' z) := by
  have hd := H.box_dist hj hw
  have hlip := (abs_le.1 (H.phi_lip' z (castS w))).2
  have hdb := H.delta_box
  have hδ0 := H.hδ0
  have hL := H.L3
  rw [← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have : δ₁ * S.dF z (castS w) ≤ δ₁ * (4 * (8 + 2 * S.L) * S.L) := mul_le_mul_of_nonneg_left hd hδ0.le
  nlinarith

/-- The scale of a site under `Q_{9+2L}` about `z` is at least `j(z) - 1`. -/
lemma sc_box_ge {z : Site NF} {w : Fin 4 → ℤ} {ρ : ℝ} (hρ : ρ ≤ 9 + 2 * S.L)
    (hw : InQr ((S.L : ℝ) ^ jj z)⁻¹ (xbar z) ρ w) : jj z ≤ jj (castS w) + 1 := by
  have h := box_mem_Ω S H.hRM8 z hρ hw
  have := ((S.toDomSeq).mem_iff (castS w) _).1 (S.mem_toDomSeq_Ω.2 h)
  omega

/-- If the source meets the box about `z`, then `j(z) ≤ j' + 2` and `φ(z) ≤ L`. -/
lemma source_near {z : Site NF} (hj : 2 ≤ jj z) {w : Fin 4 → ℤ}
    (hw : InQr ((S.L : ℝ) ^ jj z)⁻¹ (xbar z) (8 + 2 * S.L) w)
    (hsrc : (dinf (castS w) y' : ℝ) < (S.L : ℝ) ^ jj y') :
    jj z ≤ jj y' + 2 ∧ phiY S δ₁ y' z ≤ S.L := by
  have hL := H.L3
  constructor
  · have h1 := H.sc_box_ge (by linarith) hw
    have h2 := (S.tilde_scale H.hRML hsrc).2
    omega
  · have hd1 := H.box_dist hj hw
    have hd2 := S.tilde_dist H.hRML hsrc
    have ht := S.dF_triangle z (castS w) y'
    rw [S.dF_comm y' (castS w)] at hd2
    have hdb := H.delta_box
    have hδ0 := H.hδ0
    unfold phiY
    have : δ₁ * S.dF z y' ≤ δ₁ * (4 * (8 + 2 * S.L) * S.L + 4 * S.L) :=
      mul_le_mul_of_nonneg_left (by linarith) hδ0.le
    nlinarith

lemma pow_le_of_le {a b : ℕ} (hab : a ≤ b + 2) (k : ℕ) :
    (S.L : ℝ) ^ (k * a) ≤ (S.L : ℝ) ^ (2 * k) * (S.L : ℝ) ^ (k * b) := by
  have hL : (1 : ℝ) ≤ S.L := by exact_mod_cast (show 1 ≤ S.L by have := S.three_le_L; omega)
  rw [← pow_add]
  exact pow_le_pow_right₀ hL (by nlinarith)

lemma F_le_M0 : (S.L : ℝ) ^ (3 * jj y') * F ≤ M0 S Cs y' F G := by
  have hL := H.L3; have hCs := H.hCs; have hF := H.hF; have hG := H.hG
  unfold M0
  have h0 : 0 ≤ (S.L : ℝ) ^ (3 * jj y') * F := by positivity
  have h1 : 0 ≤ (S.L : ℝ) ^ (2 * jj y') * G := by positivity
  have h2 : 1 ≤ 16 * S.L * Cs := by nlinarith
  nlinarith

lemma G_le_M0 : (S.L : ℝ) ^ (2 * jj y') * G ≤ M0 S Cs y' F G := by
  have hL := H.L3; have hCs := H.hCs; have hF := H.hF; have hG := H.hG
  unfold M0
  have h0 : 0 ≤ (S.L : ℝ) ^ (3 * jj y') * F := by positivity
  have h1 : 0 ≤ (S.L : ℝ) ^ (2 * jj y') * G := by positivity
  have h2 : 1 ≤ 16 * S.L * Cs := by nlinarith
  nlinarith

lemma c1_nonneg : 0 ≤ (S.toContSeq).c1 (1 / 2) δ₁ := by
  unfold Summation.ContSeq.c1; have := H.hδ0; positivity

/-- **`eq:sf-pointwise`**: `|u(z)| ≤ C₂a_{j(z)}⁻¹e^{-φ(z)}M₀`. -/
theorem pointwise [NeZero N] (z : Site NF) :
    Real.sqrt (nsq fun k => u k z) ≤
      C2 S δ₁ Cs CN * ((S.L : ℝ) ^ jj z)⁻¹ * Real.exp (-phiY S δ₁ y' z) * M0 S Cs y' F G := by
  have hL := H.L3
  have hL0 : (0 : ℝ) < S.L := by linarith
  have hM := H.wN_le_M0
  have hM0 := H.M0_nonneg
  set c : ℝ := (S.L : ℝ) ^ jj z with hc_def
  have hc : 0 < c := by positivity
  set E := Real.exp (-phiY S δ₁ y' z)
  have hE : 0 < E := Real.exp_pos _
  have hKsf : 0 ≤ Ksf CN := by unfold Ksf; have := H.hCN; positivity
  have hCF : 0 ≤ CF S δ₁ := by unfold CF; have := H.c1_nonneg; positivity
  have hCs := H.hCs
  have hCTh : 0 ≤ CTh S δ₁ Cs := by unfold CTh; positivity
  rcases Nat.lt_or_ge (jj z) 2 with hj | hj
  · -- the layers `0` and `1`
    have h := value_le_wN S (phiY S δ₁ y') u z
    have hpow : c ≤ (S.L : ℝ) ^ 2 * c⁻¹ := by
      rw [le_mul_inv_iff₀ hc, hc_def, ← pow_add]
      exact pow_le_pow_right₀ (by linarith) (by omega)
    calc Real.sqrt (nsq fun k => u k z) ≤ c * E * Real.sqrt (wN S (eF S (phiY S δ₁ y') u)) := h
      _ ≤ ((S.L : ℝ) ^ 2 * c⁻¹) * E * M0 S Cs y' F G := by gcongr
      _ ≤ C2 S δ₁ Cs CN * c⁻¹ * E * M0 S Cs y' F G := by
          gcongr
          unfold C2
          have : 0 ≤ Ksf CN * CTh S δ₁ Cs := mul_nonneg hKsf hCTh
          linarith
  · -- the layers `j ≥ 2`: `lem:sf-local`(i)
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
    have hz0 : InQr c⁻¹ (xbar z) 4 (xbar z) := fun μ => by simp [tc]
    have hv := value_high S H.hX H.hα0 H.hα H.hRM8 H.hD H.H2 hj H.hCN (H.hZs z hj) (H.hN1 z hj) hFb hGb hz0
    rw [castS_xbar] at hv
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
    calc Real.sqrt (nsq fun k => u k z) ≤ Ksf CN * (CTh S δ₁ Cs * c⁻¹ * E * M0 S Cs y' F G) :=
          hv.trans (mul_le_mul_of_nonneg_left hTh hKsf)
      _ ≤ C2 S δ₁ Cs CN * c⁻¹ * E * M0 S Cs y' F G := by
          unfold C2
          have : 0 ≤ c⁻¹ * E * M0 S Cs y' F G := by positivity
          nlinarith


end SFBHyp

end SFBounds
end CoreLean

end
