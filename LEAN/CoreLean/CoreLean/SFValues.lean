/-
`prop:sf-bounds` of BALABAN_CORE.tex (`4252790331fd`), `eq:sf-values`, on the fine lattice (`a₀ = 1`): for `z ∈ Δ(y)`,
`y ∈ Γ_j`, and the data supported in `Δ̃(y')`, `y' ∈ Γ_{j'}`,
`|u(z)| ≤ C_v e^{-(7/8)δ₁d(y, y')}(a_j²‖f‖_∞ + a_j max_μ‖g_μ‖_∞)`, `C_v = 16L⁵e^{2δ₁}C_*C₂`.

* `phi_block`: `e^{-φ(z)} ≤ e^{2δ₁}e^{-δ₁d(y, y')}` on `Δ(y)` (the second fact on the distance).
* `scale3`, `scale2`: `a_j⁻¹a_{j'}³ ≤ L⁴a_j²e^{δ₁d/8}` and `a_j⁻¹a_{j'}² ≤ L⁴a_je^{δ₁d/8}` (`eq:sf-scale-shift`).
* `values`: `eq:sf-values`; with `g = 0`, `G = 0` it is the bound of `𝒪λ`, with `f = 0`, `F = 0` that of `𝒪D^*_𝐔λ`.
-/
import CoreLean.SFPointwise

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

/-- The number `C_v = 16L⁵e^{2δ₁}C_*C₂` of `eq:sf-values`. -/
def Cv (S : SeqDom) (δ₁ Cs CN : ℝ) : ℝ := 16 * (S.L : ℝ) ^ 5 * Real.exp (2 * δ₁) * Cs * C2 S δ₁ Cs CN

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

/-- `e^{-φ(z)} ≤ e^{2δ₁}e^{-δ₁d(y, y')}` for `z ∈ Δ(y)`. -/
lemma phi_block {y z : Site NF} (hy : y ∈ detB S.toDomSeq) (hz : z ∈ Blk S.toDomSeq (jj y) y) :
    Real.exp (-phiY S δ₁ y' z) ≤ Real.exp (2 * δ₁) * Real.exp (-(δ₁ * S.dF y y')) := by
  have hd : S.dF y z ≤ 2 := ENNReal.toReal_le_of_le_ofReal (by norm_num) (S.wdist_block_le hy hz)
  have ht := S.dF_triangle y z y'
  have hδ := H.hδ0
  rw [← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  unfold phiY
  nlinarith

/-- `a_j⁻¹a_{j'}^σ ≤ L⁴a_j^{σ-1}e^{δ₁d(y, y')/8}` for `σ ∈ {2, 3}`. -/
lemma scale_nat (y : Site NF) (s : ℕ) (hs : s ≤ 4) :
    (S.L : ℝ) ^ (s * jj y') ≤ (S.L : ℝ) ^ 4 * Real.exp (δ₁ / 8 * S.dF y y') * (S.L : ℝ) ^ (s * jj y) := by
  have h := S.scale_shift H.hδ0 H.hRMs (σ := ((s : ℕ) : ℝ)) (by rw [abs_of_nonneg (by positivity)]; exact_mod_cast hs)
    y y'
  rw [Real.rpow_natCast, Real.rpow_natCast, ← pow_mul, ← pow_mul, mul_comm (jj y'), mul_comm (jj y)] at h
  simpa using h

/-- **`eq:sf-values`.** -/
theorem values [NeZero N] {y z : Site NF} (hy : y ∈ detB S.toDomSeq) (hz : z ∈ Blk S.toDomSeq (jj y) y) :
    Real.sqrt (nsq fun k => u k z) ≤ Cv S δ₁ Cs CN * Real.exp (-(7 / 8 * δ₁ * S.dF y y')) *
      ((S.L : ℝ) ^ (2 * jj y) * F + (S.L : ℝ) ^ jj y * G) := by
  have hp := H.pointwise z
  rw [sc_of_mem_blk S hy hz] at hp
  have hL := H.L3
  have hL0 : (0 : ℝ) < S.L := by linarith
  have hF := H.hF
  have hG := H.hG
  have hCs := H.hCs
  set c : ℝ := (S.L : ℝ) ^ jj y
  have hc : 0 < c := by positivity
  set e := Real.exp (δ₁ / 8 * S.dF y y')
  have he : 0 < e := Real.exp_pos _
  have h3 := H.scale_nat y 3 (by norm_num)
  have h2 := H.scale_nat y 2 (by norm_num)
  have hph := H.phi_block hy hz
  have hC2 : 0 ≤ C2 S δ₁ Cs CN := by
    unfold C2 CTh CF Ksf
    have := H.hCN; have := H.c1_nonneg; positivity
  -- `a_j⁻¹M₀ ≤ 16LC_*L⁴e(a_j²F + a_jG)`
  have hM : c⁻¹ * M0 S Cs y' F G ≤ 16 * S.L * Cs * (S.L : ℝ) ^ 4 * e * ((S.L : ℝ) ^ (2 * jj y) * F + c * G) := by
    unfold M0
    have e3 : (S.L : ℝ) ^ (3 * jj y) = c ^ 2 * c := by simp only [c]; ring
    have e2 : (S.L : ℝ) ^ (2 * jj y) = c * c := by simp only [c]; ring
    rw [e3] at h3
    rw [e2] at h2
    have hA : c⁻¹ * (S.L : ℝ) ^ (3 * jj y') ≤ (S.L : ℝ) ^ 4 * e * c ^ 2 := by
      rw [inv_mul_le_iff₀ hc]; nlinarith
    have hB : c⁻¹ * (S.L : ℝ) ^ (2 * jj y') ≤ (S.L : ℝ) ^ 4 * e * c := by
      rw [inv_mul_le_iff₀ hc]; nlinarith
    have hpos : 0 ≤ 16 * S.L * Cs := by positivity
    calc c⁻¹ * (16 * S.L * Cs * ((S.L : ℝ) ^ (3 * jj y') * F + (S.L : ℝ) ^ (2 * jj y') * G))
        = 16 * S.L * Cs * ((c⁻¹ * (S.L : ℝ) ^ (3 * jj y')) * F + (c⁻¹ * (S.L : ℝ) ^ (2 * jj y')) * G) := by ring
      _ ≤ 16 * S.L * Cs * (((S.L : ℝ) ^ 4 * e * c ^ 2) * F + ((S.L : ℝ) ^ 4 * e * c) * G) := by gcongr
      _ = 16 * S.L * Cs * (S.L : ℝ) ^ 4 * e * ((S.L : ℝ) ^ (2 * jj y) * F + c * G) := by rw [e2]; ring
  have hexp : Real.exp (2 * δ₁) * Real.exp (-(δ₁ * S.dF y y')) * e =
      Real.exp (2 * δ₁) * Real.exp (-(7 / 8 * δ₁ * S.dF y y')) := by
    simp only [e]; rw [mul_assoc, ← Real.exp_add]; ring_nf
  calc Real.sqrt (nsq fun k => u k z) ≤ C2 S δ₁ Cs CN * c⁻¹ * Real.exp (-phiY S δ₁ y' z) * M0 S Cs y' F G := hp
    _ = C2 S δ₁ Cs CN * Real.exp (-phiY S δ₁ y' z) * (c⁻¹ * M0 S Cs y' F G) := by ring
    _ ≤ C2 S δ₁ Cs CN * (Real.exp (2 * δ₁) * Real.exp (-(δ₁ * S.dF y y'))) *
          (16 * S.L * Cs * (S.L : ℝ) ^ 4 * e * ((S.L : ℝ) ^ (2 * jj y) * F + c * G)) := by
        have := H.M0_nonneg
        have : 0 ≤ c⁻¹ * M0 S Cs y' F G := by positivity
        gcongr
    _ = 16 * (S.L : ℝ) ^ 5 * Cs * C2 S δ₁ Cs CN *
          (Real.exp (2 * δ₁) * Real.exp (-(δ₁ * S.dF y y')) * e) * ((S.L : ℝ) ^ (2 * jj y) * F + c * G) := by ring
    _ = _ := by rw [hexp]; unfold Cv; ring

end SFBHyp

end SFBounds
end CoreLean

end
