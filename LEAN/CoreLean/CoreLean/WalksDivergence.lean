/-
`lem:divergence-walks` of BALABAN_CORE.tex (`a021c13be348`), in the abstract form of `WalkProduct.lean`.
* The identity `eq:divergence-walks` (`divergence_identity`): in a ring of operators, from `G - GR_G = G₀`,
  `G₀ = Σ_□h_□G_□h_□`, `R_G = Σ_□ρ_□G_□h_□`, and `ρ_□ = K(h_□) - h_□D_𝐔P_□D^*_𝐔 + D_𝐔PD^*_𝐔h_□`:
  `G = Σ_□h_□G_□h_□ + GΣ_□(K(h_□) - h_□D_𝐔P_□D^*_𝐔)G_□h_□ + GD_𝐔PD^*_𝐔Σ_□h_□G_□h_□`, which applied to `f_𝔰` is
  `Gf_𝔰 = Σ_□𝓤_□𝔰 + GΣ_□𝓥_□𝔰 + GD_𝐔PD^*_𝐔Σ_□𝓤_□𝔰`.
* (W1) for the products: `W_ω𝓥_□` (exponent `1`, rate `δ/2`; `divergence_GV`) and `W_ω𝓟_ι𝓤_□` (exponent `1`, rate
  `(1/2)⁸δ₀/4` from the rates `δ₀/4` of `G` and `𝓤_□` and `(1/2)⁶δ₀/4` of `D_𝐔PD^*_𝐔`; `divergence_GPU`).
The counts (W3), (W2), and the expansion property are not modelled here.
-/
import CoreLean.WalksProjection

open Finset

noncomputable section

namespace CoreLean
namespace WalkProduct

open Composition

/-- **`eq:divergence-walks`**, the identity of the first approximation in a ring of operators. -/
theorem divergence_identity {R ι : Type*} [Ring R] (s : Finset ι) {G G₀ RG DPD : R} (h Gl K DPl ρ : ι → R)
    (hG : G - G * RG = G₀) (hG₀ : G₀ = ∑ q ∈ s, h q * Gl q * h q) (hR : RG = ∑ q ∈ s, ρ q * Gl q * h q)
    (hρ : ∀ q, ρ q = K q - h q * DPl q + DPD * h q) :
    G = ∑ q ∈ s, h q * Gl q * h q + G * ∑ q ∈ s, (K q - h q * DPl q) * Gl q * h q +
      G * DPD * ∑ q ∈ s, h q * Gl q * h q := by
  have h1 : G = G₀ + G * RG := by rw [← hG]; abel
  have h2 : ∑ q ∈ s, ρ q * Gl q * h q =
      ∑ q ∈ s, (K q - h q * DPl q) * Gl q * h q + DPD * ∑ q ∈ s, h q * Gl q * h q := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [hρ q]; noncomm_ring
  conv_lhs => rw [h1]
  rw [hG₀, hR, h2, mul_add, ← mul_assoc, add_assoc]

variable {β Ω : Type*} [Fintype β] [DecidableEq β] {B : Setting β} {W : Walks β Ω}

/-- **`lem:divergence-walks`**, (W1) for `W_ω𝓥_□`: `G` (exponent `1`) after `𝓥_□` (exponent `0`), both at the rate
`δ`: exponent `1`, rate `δ/2`. -/
theorem divergence_GV {SDiv Src Fld : Type*} {nV : SDiv → β → ℝ} {nS : Src → β → ℝ} {nF : Fld → β → ℝ}
    (hnV : ∀ f y, 0 ≤ nV f y) (hnS : ∀ f y, 0 ≤ nS f y) (hd : ∀ ω y y', B.d y y' ≤ W.dw ω y y')
    {δ c₁ : ℝ} (hδ : 0 < δ) (hsum : ∀ y, ∑ y'', Real.exp (-(δ / 4 * B.d y y'')) ≤ c₁)
    {KG : Src → Fld} {KV : SDiv → Src} {ωG ωV : Ω} {bG bV : ℝ} (hbG : 0 ≤ bG) (hbV : 0 ≤ bV)
    (hG : Bound B W nS nF KG ωG bG 1 δ 0) (hV : Bound B W nV nS KV ωV bV 0 δ 0) :
    Bound B W nV nF (KG ∘ KV) (W.comp ωG ωV) (c₁ * bG * bV) 1 (δ / 2) 0 := by
  have hRM := B.RM_pos
  have := prod_step hnS hnV hd hδ le_rfl hsum hbG hbV (by norm_num; positivity) hG hV
  have e : c₁ * B.L ^ |((0 : ℤ) : ℝ)| * bG * bV = c₁ * bG * bV := by norm_num
  rw [e, show (1 : ℤ) + 0 = 1 by norm_num] at this
  exact this

/-- **`lem:divergence-walks`**, (W1) for `W_ω𝓟_ι𝓤_□`: `𝓟_ι` (exponent `-1`, rate `δ/64`) after `𝓤_□` (exponent `1`,
rate `δ`), then `G` (exponent `1`, rate `δ`): exponent `1`, rate `δ/256 = (1/2)⁸δ` with `δ = δ₀/4`. -/
theorem divergence_GPU {SDiv Src Fld S1 : Type*} {nV : SDiv → β → ℝ} {nS : Src → β → ℝ}
    {nF : Fld → β → ℝ} {m1 : S1 → β → ℝ}
    (hnV : ∀ f y, 0 ≤ nV f y) (hnS : ∀ f y, 0 ≤ nS f y) (hnF : ∀ f y, 0 ≤ nF f y)
    (hd : ∀ ω y y', B.d y y' ≤ W.dw ω y y') {δ c₁ : ℝ} (hδ : 0 < δ)
    (hsum : ∀ y, ∑ y'', Real.exp (-(δ / 512 * B.d y y'')) ≤ c₁) (hL : 4 * Real.log B.L ≤ δ / 64 * B.RM)
    {KG : Src → Fld} {KP : Fld → Src} {KU : SDiv → Fld} {ωG ωP ωU : Ω} {bG bP bU : ℝ}
    (hbG : 0 ≤ bG) (hbP : 0 ≤ bP) (hbU : 0 ≤ bU) (hc₁ : 0 ≤ c₁)
    (hG : Bound B W nS nF KG ωG bG 1 δ 0) (hP : Bound B W nF nS KP ωP bP (-1) (δ / 64) 0)
    (hU : Bound B W nV nF KU ωU bU 1 δ 0) :
    Bound B W nV nF (KG ∘ (KP ∘ KU)) (W.comp ωG (W.comp ωP ωU)) (c₁ ^ 2 * B.L * (bG * bP * bU)) 1
      (δ / 256) 0 := by
  have hRM := B.RM_pos
  have hl : 0 ≤ Real.log B.L := Real.log_nonneg B.one_le_L
  have hs : ∀ δ', δ / 128 ≤ δ' → ∀ y, ∑ y'', Real.exp (-(δ' / 4 * B.d y y'')) ≤ c₁ := fun δ' h =>
    sum_mono_rate (δ' := δ / 128) h (fun y => by rw [show δ / 128 / 4 = δ / 512 by ring]; exact hsum y)
  have s1 := prod_step hnF hnV hd (by linarith) le_rfl (hs (δ / 64) (by linarith)) hbP hbU
    (by norm_num; linarith) hP (hU.mono_delta hnV hd hbU (by linarith))
  have s2 := prod_step hnS hnV hd (by linarith) (by linarith) (hs (δ / 64 / 2) (by linarith)) hbG
    (mul_nonneg (mul_nonneg (mul_nonneg hc₁ (Real.rpow_nonneg (le_trans zero_le_one B.one_le_L) _)) hbP) hbU)
    (by norm_num; positivity) hG s1
  have e1 : δ / 64 / 2 / 2 = δ / 256 := by ring
  have e2 : c₁ * B.L ^ |((((-1 : ℤ) + (1 : ℤ)) : ℤ) : ℝ)| * bG * (c₁ * B.L ^ |((1 : ℤ) : ℝ)| * bP * bU) =
      c₁ ^ 2 * B.L * (bG * bP * bU) := by norm_num; ring
  rw [e1, e2, show (1 : ℤ) + (-1 + 1) = 1 by norm_num] at s2
  exact s2

end WalkProduct
end CoreLean

end
