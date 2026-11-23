/-
`lem:projection-walks` of BALABAN_CORE.tex (`a021c13be348`), the bound (W1) of the products, in the abstract form of
`WalkProduct.lean`. The factors are terms of the families of `G'` (sources to fields, exponent `1`), `Q'h²_□` (fields to
data, `1`), `C` (data to data, `-4`), `Q'^*h²_□` (data to sources, `0`), `D_𝐔h²_□` and `D^*_𝐔h²_□` (`0`), all with the
rate `δ = δ₀/4` (`(W1)` as `Bound`). The products are formed from the right, `Q'G'`, `CQ'G'`, `Q'^*CQ'G'`, `P`, then
`PD^*_𝐔` and `D_𝐔PD^*_𝐔`, by `product_bound` (`lem:walk-expansion-product`(i)), the rate halving at each product, a
factor with a larger rate having every smaller one (`Bound.mono_delta`). The term of `P = G'Q'^*CQ'G'` has the exponent
`-1` and the rate `(1/2)⁴δ` (`projection_P`), that of `D_𝐔PD^*_𝐔` the exponent `-1` and the rate `(1/2)⁶δ`
(`projection_DPD`), with the constants `c₁⁴L⁷b_Gb_{Q'^*}b_Cb_{Q'}b_{G'}` and `c₁⁶L⁸b_Db_Gb_{Q'^*}b_Cb_{Q'}b_{G'}b_{D^*}`,
under `8 log L ≤ (δ/32)RM` (the core's `27δ_wM ≥ 16 log L`) and `eq:summation` at the smallest rate used. The counts
(W3), the holomorphy and covariance (W2), and the expansion property are not modelled here.
-/
import CoreLean.WalkProduct

open Finset

noncomputable section

namespace CoreLean
namespace WalkProduct

open Composition

variable {β Ω : Type*} [Fintype β] [DecidableEq β] {B : Setting β} {W : Walks β Ω}

/-- A smaller rate gives a weaker bound. -/
lemma Bound.mono_delta {V V' : Type*} {nrm : V → β → ℝ} {nrm' : V' → β → ℝ} (hn : ∀ f y, 0 ≤ nrm f y)
    (hd : ∀ ω y y', B.d y y' ≤ W.dw ω y y') {K : V → V'} {ω : Ω} {b : ℝ} {p : ℤ} {δ δ' κ : ℝ}
    (hb : 0 ≤ b) (hδ : δ' ≤ δ) (hK : Bound B W nrm nrm' K ω b p δ κ) : Bound B W nrm nrm' K ω b p δ' κ := by
  intro f
  refine ⟨(hK f).1, fun y hy => ((hK f).2 y hy).trans ?_⟩
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y' _ => ?_)
    (mul_nonneg hb (zpow_pos (B.a_pos _) _).le)
  refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (hn f y')
  have h0 : 0 ≤ W.dw ω y y' := (B.d_nonneg y y').trans (hd ω y y')
  have := mul_le_mul_of_nonneg_right hδ h0
  linarith

lemma sum_mono_rate {c₁ δ δ' : ℝ} (hδ : δ' ≤ δ) (hsum : ∀ y, ∑ y'', Real.exp (-(δ' / 4 * B.d y y'')) ≤ c₁)
    (y : β) : ∑ y'', Real.exp (-(δ / 4 * B.d y y'')) ≤ c₁ := by
  refine le_trans (Finset.sum_le_sum fun y'' _ => Real.exp_le_exp.mpr ?_) (hsum y)
  have := mul_le_mul_of_nonneg_right hδ (B.d_nonneg y y'')
  linarith

/-- One product: the right factor at the rate `δ`, the left one at any rate `δ_K ≥ δ`. -/
lemma prod_step {V₁ V₂ V₃ : Type*} {n₁ : V₁ → β → ℝ} {n₂ : V₂ → β → ℝ} {n₃ : V₃ → β → ℝ}
    (hn₂ : ∀ g y, 0 ≤ n₂ g y) (hn₃ : ∀ f y, 0 ≤ n₃ f y) (hd : ∀ ω y y', B.d y y' ≤ W.dw ω y y')
    {δ δK c₁ : ℝ} (hδ : 0 < δ) (hδK : δ ≤ δK) (hsum : ∀ y, ∑ y'', Real.exp (-(δ / 4 * B.d y y'')) ≤ c₁)
    {K : V₂ → V₁} {K' : V₃ → V₂} {ω ω' : Ω} {b b' : ℝ} {p p' : ℤ} (hb : 0 ≤ b) (hb' : 0 ≤ b')
    (hp' : 4 * |(p' : ℝ)| * Real.log B.L ≤ δ * B.RM)
    (hK : Bound B W n₂ n₁ K ω b p δK 0) (hK' : Bound B W n₃ n₂ K' ω' b' p' δ 0) :
    Bound B W n₃ n₁ (K ∘ K') (W.comp ω ω') (c₁ * B.L ^ |(p' : ℝ)| * b * b') (p + p') (δ / 2) 0 :=
  product_bound hn₂ hn₃ hd hδ hsum hb hb' hp' (hK.mono_delta hn₂ hd hb hδK) hK'

lemma logL_nonneg : 0 ≤ Real.log B.L := Real.log_nonneg B.one_le_L

/-- **`lem:projection-walks`**, (W1) for the terms of `P = G'Q'^*CQ'G'`: exponent `-1`, rate `δ/16`. -/
theorem projection_P {Src Fld Dat : Type*} {nS : Src → β → ℝ} {nF : Fld → β → ℝ} {nD : Dat → β → ℝ}
    (hnS : ∀ f y, 0 ≤ nS f y) (hnF : ∀ f y, 0 ≤ nF f y) (hnD : ∀ f y, 0 ≤ nD f y)
    (hd : ∀ ω y y', B.d y y' ≤ W.dw ω y y') {δ c₁ : ℝ} (hδ : 0 < δ)
    (hsum : ∀ y, ∑ y'', Real.exp (-(δ / 32 * B.d y y'')) ≤ c₁) (hL : 8 * Real.log B.L ≤ δ / 32 * B.RM)
    {KG KG' : Src → Fld} {KQ : Fld → Dat} {KC : Dat → Dat} {KQs : Dat → Src}
    {ωG ωG' ωQ ωC ωQs : Ω} {bG bG' bQ bC bQs : ℝ} (hbG : 0 ≤ bG) (hbG' : 0 ≤ bG') (hbQ : 0 ≤ bQ)
    (hbC : 0 ≤ bC) (hbQs : 0 ≤ bQs) (hc₁ : 0 ≤ c₁)
    (hG : Bound B W nS nF KG ωG bG 1 δ 0) (hG' : Bound B W nS nF KG' ωG' bG' 1 δ 0)
    (hQ : Bound B W nF nD KQ ωQ bQ 1 δ 0) (hC : Bound B W nD nD KC ωC bC (-4) δ 0)
    (hQs : Bound B W nD nS KQs ωQs bQs 0 δ 0) :
    Bound B W nS nF (KG ∘ KQs ∘ KC ∘ KQ ∘ KG')
      (W.comp ωG (W.comp ωQs (W.comp ωC (W.comp ωQ ωG'))))
      (c₁ ^ 4 * B.L ^ 7 * (bG * bQs * bC * bQ * bG')) (-1) (δ / 16) 0 := by
  have hl := logL_nonneg (B := B)
  have hRM := B.RM_pos
  have hL1 : 0 < B.L := lt_of_lt_of_le zero_lt_one B.one_le_L
  have e8 : δ / 8 / 4 = δ / 32 := by ring
  have hs : ∀ δ', δ / 8 ≤ δ' → ∀ y, ∑ y'', Real.exp (-(δ' / 4 * B.d y y'')) ≤ c₁ := fun δ' h =>
    sum_mono_rate (δ' := δ / 8) h (fun y => by rw [e8]; exact hsum y)
  -- `Q'G'`, `CQ'G'`, `Q'^*CQ'G'`, `P`
  have s1 := prod_step hnF hnS hd hδ le_rfl (hs δ (by linarith)) hbQ hbG'
    (by norm_num; nlinarith) hQ hG'
  have s2 := prod_step hnD hnS hd (by linarith) (by linarith) (hs (δ / 2) (by linarith)) hbC
    (by positivity) (by norm_num; nlinarith) hC s1
  have s3 := prod_step hnD hnS hd (by linarith) (by linarith) (hs (δ / 2 / 2) (by linarith)) hbQs
    (by positivity) (by norm_num; nlinarith) hQs s2
  have s4 := prod_step hnS hnS hd (by linarith) (by linarith) (hs (δ / 2 / 2 / 2) (by linarith)) hbG
    (by positivity) (by norm_num; nlinarith) hG s3
  have e1 : δ / 2 / 2 / 2 / 2 = δ / 16 := by ring
  have e2 : ((1 : ℤ) + ((0 : ℤ) + ((-4 : ℤ) + ((1 : ℤ) + (1 : ℤ))))) = -1 := by norm_num
  have e3 : c₁ * B.L ^ |(((0 : ℤ) + ((-4 : ℤ) + ((1 : ℤ) + (1 : ℤ))) : ℤ) : ℝ)| * bG *
      (c₁ * B.L ^ |((((-4 : ℤ) + ((1 : ℤ) + (1 : ℤ))) : ℤ) : ℝ)| * bQs *
        (c₁ * B.L ^ |((((1 : ℤ) + (1 : ℤ)) : ℤ) : ℝ)| * bC * (c₁ * B.L ^ |((1 : ℤ) : ℝ)| * bQ * bG'))) =
      c₁ ^ 4 * B.L ^ 7 * (bG * bQs * bC * bQ * bG') := by
    norm_num
    rw [show (7 : ℕ) = 2 + 2 + 2 + 1 by norm_num, pow_add, pow_add, pow_add]
    simp only [Real.rpow_two, pow_one]
    ring
  rw [e1, e2, e3] at s4
  exact s4

/-- **`lem:projection-walks`**, (W1) for the terms of `D_𝐔PD^*_𝐔`: exponent `-1`, rate `δ/64`. -/
theorem projection_DPD {Src Fld Dat F1 S1 : Type*} {nS : Src → β → ℝ} {nF : Fld → β → ℝ}
    {nD : Dat → β → ℝ} {n1 : F1 → β → ℝ} {m1 : S1 → β → ℝ}
    (hnS : ∀ f y, 0 ≤ nS f y) (hnF : ∀ f y, 0 ≤ nF f y) (hnD : ∀ f y, 0 ≤ nD f y) (hn1 : ∀ f y, 0 ≤ n1 f y)
    (hd : ∀ ω y y', B.d y y' ≤ W.dw ω y y') {δ c₁ : ℝ} (hδ : 0 < δ)
    (hsum : ∀ y, ∑ y'', Real.exp (-(δ / 128 * B.d y y'')) ≤ c₁) (hL : 8 * Real.log B.L ≤ δ / 32 * B.RM)
    {KG KG' : Src → Fld} {KQ : Fld → Dat} {KC : Dat → Dat} {KQs : Dat → Src} {KD : Fld → S1}
    {KDs : F1 → Src} {ωG ωG' ωQ ωC ωQs ωD ωDs : Ω} {bG bG' bQ bC bQs bD bDs : ℝ} (hbG : 0 ≤ bG)
    (hbG' : 0 ≤ bG') (hbQ : 0 ≤ bQ) (hbC : 0 ≤ bC) (hbQs : 0 ≤ bQs) (hbD : 0 ≤ bD) (hbDs : 0 ≤ bDs)
    (hc₁ : 0 ≤ c₁)
    (hG : Bound B W nS nF KG ωG bG 1 δ 0) (hG' : Bound B W nS nF KG' ωG' bG' 1 δ 0)
    (hQ : Bound B W nF nD KQ ωQ bQ 1 δ 0) (hC : Bound B W nD nD KC ωC bC (-4) δ 0)
    (hQs : Bound B W nD nS KQs ωQs bQs 0 δ 0) (hD : Bound B W nF m1 KD ωD bD 0 δ 0)
    (hDs : Bound B W n1 nS KDs ωDs bDs 0 δ 0) :
    Bound B W n1 m1 (KD ∘ ((KG ∘ KQs ∘ KC ∘ KQ ∘ KG') ∘ KDs))
      (W.comp ωD (W.comp (W.comp ωG (W.comp ωQs (W.comp ωC (W.comp ωQ ωG')))) ωDs))
      (c₁ ^ 6 * B.L ^ 8 * (bD * (bG * bQs * bC * bQ * bG') * bDs)) (-1) (δ / 64) 0 := by
  have hl := logL_nonneg (B := B)
  have hRM := B.RM_pos
  have e4 : δ / 128 * 4 / 4 = δ / 128 := by ring
  have hP := projection_P hnS hnF hnD hd hδ
    (fun y => by
      have := sum_mono_rate (B := B) (δ' := δ / 128 * 4) (δ := δ / 32 * 4) (by linarith)
        (fun y => by rw [e4]; exact hsum y) y
      rwa [show δ / 32 * 4 / 4 = δ / 32 by ring] at this)
    hL hbG hbG' hbQ hbC hbQs hc₁ hG hG' hQ hC hQs
  have e32 : δ / 32 / 4 = δ / 128 := by ring
  have hs : ∀ δ', δ / 32 ≤ δ' → ∀ y, ∑ y'', Real.exp (-(δ' / 4 * B.d y y'')) ≤ c₁ := fun δ' h =>
    sum_mono_rate (δ' := δ / 32) h (fun y => by rw [e32]; exact hsum y)
  have hbP : 0 ≤ c₁ ^ 4 * B.L ^ 7 * (bG * bQs * bC * bQ * bG') := by
    have := lt_of_lt_of_le zero_lt_one B.one_le_L
    positivity
  -- `PD^*_𝐔`, `D_𝐔PD^*_𝐔`
  have s5 := prod_step hnS hn1 hd (by linarith) le_rfl (hs (δ / 16) (by linarith)) hbP hbDs
    (by norm_num; nlinarith) hP (hDs.mono_delta hn1 hd hbDs (by linarith))
  have s6 := prod_step hnF hn1 hd (by linarith) (by linarith) (hs (δ / 16 / 2) (by linarith)) hbD
    (mul_nonneg (mul_nonneg (mul_nonneg hc₁ (Real.rpow_nonneg (le_trans zero_le_one B.one_le_L) _)) hbP) hbDs)
    (by norm_num; nlinarith) hD s5
  have e1 : δ / 16 / 2 / 2 = δ / 64 := by ring
  have e2 : ((0 : ℤ) + ((-1 : ℤ) + (0 : ℤ))) = -1 := by norm_num
  have e3 : c₁ * B.L ^ |((((-1 : ℤ) + (0 : ℤ)) : ℤ) : ℝ)| * bD *
      (c₁ * B.L ^ |((0 : ℤ) : ℝ)| * (c₁ ^ 4 * B.L ^ 7 * (bG * bQs * bC * bQ * bG')) * bDs) =
      c₁ ^ 6 * B.L ^ 8 * (bD * (bG * bQs * bC * bQ * bG') * bDs) := by
    norm_num
    ring
  rw [e1, e2, e3] at s6
  exact s6

end WalkProduct
end CoreLean

end
