/-
`lem:landau-walks` and `lem:block-walks`(i) of BALABAN_CORE.tex (`a021c13be348`), the bounds (W1) of the products and
the algebra of the inverse, in the abstract form of `WalkProduct.lean`.
* `landau_walks_i`: the product of a term of the family of `lem:divergence-walks` (exponent `1`, rate `δ₈`) and of one of
  `lem:vertex-walks`(ii) (exponent `-1`, rate `δ₁₃ ≤ δ₈`) has the exponent `0` and the rate `δ₁₃/2`, with the constant
  `c₁Lb b'` (the core's `θ_γ = c₁(δ_γ)LN''C_GC_{vx}γ` before the count (W3)).
* `landau_walks_ii_product`: the product of a term of the series of `𝓡` (exponent `0`, rate `δ'`) with one of the
  family of `G` (exponent `1`, rate `δ ≥ δ'`) has the exponent `1` and the rate `δ'/2`, with the constant `c₁Lbb'`.
* `landau_walks_iii`: in a ring, if `G` is the inverse of `Δ_𝖺` and `I - 𝓡`, `𝓡 = GΔ'_π`, is invertible, then
  `Δ_𝖺 - Δ'_π = Δ_𝖺(I - 𝓡)` is invertible with the inverse `G_π = (I - 𝓡)⁻¹G = G + ((I - 𝓡)⁻¹ - I)G`.
* `block_walks_i`: the terms of `Y = QGQ^*`, from `Q^*h̄²_□` (exponent `0`), `G` (exponent `1`), `Qh²_□` (exponent `1`),
  all with the rate `δ₀/4`, have the exponent `2` and the rate `δ₀/16 = δ_Y`, with the constant `c₁²Lb_Qb_Gb_{Q^*}`.
-/
import CoreLean.WalksProjection

open Finset

noncomputable section

namespace CoreLean
namespace WalkProduct

open Composition

variable {β Ω : Type*} [Fintype β] [DecidableEq β] {B : Setting β} {W : Walks β Ω}

/-- **`lem:landau-walks`(i)**, (W1) for the products `G_{div}·𝔰`: exponent `0`, rate `δ₁₃/2`. -/
theorem landau_walks_i {Fld SDiv : Type*} {nF : Fld → β → ℝ} {nS : SDiv → β → ℝ}
    (hnF : ∀ f y, 0 ≤ nF f y) (hnS : ∀ f y, 0 ≤ nS f y) (hd : ∀ ω y y', B.d y y' ≤ W.dw ω y y')
    {δ₈ δ₁₃ c₁ : ℝ} (hδ : 0 < δ₁₃) (h813 : δ₁₃ ≤ δ₈)
    (hsum : ∀ y, ∑ y'', Real.exp (-(δ₁₃ / 4 * B.d y y'')) ≤ c₁) (hL : 4 * Real.log B.L ≤ δ₁₃ * B.RM)
    {KG : SDiv → Fld} {Kv : Fld → SDiv} {ωG ωv : Ω} {bG bv : ℝ} (hbG : 0 ≤ bG) (hbv : 0 ≤ bv)
    (hG : Bound B W nS nF KG ωG bG 1 δ₈ 0) (hv : Bound B W nF nS Kv ωv bv (-1) δ₁₃ 0) :
    Bound B W nF nF (KG ∘ Kv) (W.comp ωG ωv) (c₁ * B.L * bG * bv) 0 (δ₁₃ / 2) 0 := by
  have := prod_step hnS hnF hd hδ h813 hsum hbG hbv (by norm_num; linarith) hG hv
  have e : c₁ * B.L ^ |(((-1 : ℤ)) : ℝ)| * bG * bv = c₁ * B.L * bG * bv := by norm_num
  rw [e, show (1 : ℤ) + (-1) = 0 by norm_num] at this
  exact this

/-- **`lem:landau-walks`(ii)**, (W1) for the products of a term of the series of `𝓡` with a term of `G`. -/
theorem landau_walks_ii_product {Src Fld : Type*} {nS : Src → β → ℝ} {nF : Fld → β → ℝ}
    (hnS : ∀ f y, 0 ≤ nS f y) (hnF : ∀ f y, 0 ≤ nF f y) (hd : ∀ ω y y', B.d y y' ≤ W.dw ω y y')
    {δ δ' c₁ : ℝ} (hδ' : 0 < δ') (hδδ' : δ' ≤ δ)
    (hsum : ∀ y, ∑ y'', Real.exp (-(δ' / 4 * B.d y y'')) ≤ c₁) (hL : 4 * Real.log B.L ≤ δ' * B.RM)
    {KR : Fld → Fld} {KG : Src → Fld} {ωR ωG : Ω} {bR bG : ℝ} (hbR : 0 ≤ bR) (hbG : 0 ≤ bG)
    (hR : Bound B W nF nF KR ωR bR 0 δ' 0) (hG : Bound B W nS nF KG ωG bG 1 δ 0) :
    Bound B W nS nF (KR ∘ KG) (W.comp ωR ωG) (c₁ * B.L * bR * bG) 1 (δ' / 2) 0 := by
  have := prod_step hnF hnS hd hδ' le_rfl hsum hbR hbG (by norm_num; linarith) hR
    (hG.mono_delta hnS hd hbG hδδ')
  have e : c₁ * B.L ^ |((1 : ℤ) : ℝ)| * bR * bG = c₁ * B.L * bR * bG := by norm_num
  rw [e, show (0 : ℤ) + 1 = 1 by norm_num] at this
  exact this

/-- **`lem:landau-walks`(iii)**, the algebra: `Δ_𝖺 - Δ'_π = Δ_𝖺(I - GΔ'_π)` is invertible, with the inverse
`G_π = (I - 𝓡)⁻¹G = G + ((I - 𝓡)⁻¹ - I)G`. -/
theorem landau_walks_iii {R : Type*} [Ring R] {Δ Δ' G V : R} (hΔG : Δ * G = 1) (hGΔ : G * Δ = 1)
    (hV1 : (1 - G * Δ') * V = 1) (hV2 : V * (1 - G * Δ') = 1) :
    (Δ - Δ') * (V * G) = 1 ∧ (V * G) * (Δ - Δ') = 1 ∧ V * G = G + (V - 1) * G := by
  have hfac : Δ - Δ' = Δ * (1 - G * Δ') := by
    rw [mul_sub, mul_one, ← mul_assoc, hΔG, one_mul]
  refine ⟨?_, ?_, by noncomm_ring⟩
  · rw [hfac]
    calc Δ * (1 - G * Δ') * (V * G) = Δ * ((1 - G * Δ') * V) * G := by noncomm_ring
      _ = 1 := by rw [hV1, mul_one, hΔG]
  · rw [hfac]
    calc V * G * (Δ * (1 - G * Δ')) = V * (G * Δ) * (1 - G * Δ') := by noncomm_ring
      _ = 1 := by rw [hGΔ, mul_one, hV2]

/-- **`lem:block-walks`(i)**, (W1) for the terms of `Y = QGQ^*`: exponent `2`, rate `δ₀/16 = δ_Y`. -/
theorem block_walks_i {Dat Src Fld : Type*} {nD : Dat → β → ℝ} {nS : Src → β → ℝ} {nF : Fld → β → ℝ}
    (hnD : ∀ f y, 0 ≤ nD f y) (hnS : ∀ f y, 0 ≤ nS f y) (hnF : ∀ f y, 0 ≤ nF f y)
    (hd : ∀ ω y y', B.d y y' ≤ W.dw ω y y') {δ₀ c₁ : ℝ} (hδ : 0 < δ₀)
    (hsum : ∀ y, ∑ y'', Real.exp (-(δ₀ / 32 * B.d y y'')) ≤ c₁) (hL : 4 * Real.log B.L ≤ δ₀ / 8 * B.RM)
    {KQ : Fld → Dat} {KG : Src → Fld} {KQs : Dat → Src} {ωQ ωG ωQs : Ω} {bQ bG bQs : ℝ}
    (hbQ : 0 ≤ bQ) (hbG : 0 ≤ bG) (hbQs : 0 ≤ bQs) (hc₁ : 0 ≤ c₁)
    (hQ : Bound B W nF nD KQ ωQ bQ 1 (δ₀ / 4) 0) (hG : Bound B W nS nF KG ωG bG 1 (δ₀ / 4) 0)
    (hQs : Bound B W nD nS KQs ωQs bQs 0 (δ₀ / 4) 0) :
    Bound B W nD nD (KQ ∘ (KG ∘ KQs)) (W.comp ωQ (W.comp ωG ωQs)) (c₁ ^ 2 * B.L * (bQ * bG * bQs))
      2 (δ₀ / 16) 0 := by
  have hRM := B.RM_pos
  have hl : 0 ≤ Real.log B.L := Real.log_nonneg B.one_le_L
  have hs : ∀ δ', δ₀ / 8 ≤ δ' → ∀ y, ∑ y'', Real.exp (-(δ' / 4 * B.d y y'')) ≤ c₁ := fun δ' h =>
    sum_mono_rate (δ' := δ₀ / 8) h (fun y => by rw [show δ₀ / 8 / 4 = δ₀ / 32 by ring]; exact hsum y)
  have s1 := prod_step hnS hnD hd (by linarith) le_rfl (hs (δ₀ / 4) (by linarith)) hbG hbQs
    (by norm_num; positivity) hG hQs
  have s2 := prod_step hnF hnD hd (by linarith) (by linarith) (hs (δ₀ / 4 / 2) (by linarith)) hbQ
    (mul_nonneg (mul_nonneg (mul_nonneg hc₁ (Real.rpow_nonneg (le_trans zero_le_one B.one_le_L) _)) hbG) hbQs)
    (by norm_num; linarith) hQ s1
  have e1 : δ₀ / 4 / 2 / 2 = δ₀ / 16 := by ring
  have e2 : c₁ * B.L ^ |((((1 : ℤ) + (0 : ℤ)) : ℤ) : ℝ)| * bQ * (c₁ * B.L ^ |((0 : ℤ) : ℝ)| * bG * bQs) =
      c₁ ^ 2 * B.L * (bQ * bG * bQs) := by norm_num; ring
  rw [e1, e2, show (1 : ℤ) + (1 + 0) = 2 by norm_num] at s2
  exact s2

end WalkProduct
end CoreLean

end
