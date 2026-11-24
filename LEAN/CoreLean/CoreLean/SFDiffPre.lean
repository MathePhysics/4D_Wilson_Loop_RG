/-
`prop:sf-block` of BALABAN_CORE.tex (`d4ef86a9a5fd`), preparations for the difference `G'_𝐔 - G'_id` on the fine lattice
(`a₀ = 1`).

* `ScalarHyp.triv`: the hypotheses of `prop:sf-scalar` hold at the trivial configuration (`X = 0`, `W = id`, `η = 0`).
* `X_bond_le`: `‖X_μ(w)‖ ≤ α₁La_{j(w)}⁻¹` and `≤ α₁La_{j(w + e_μ)}⁻¹` (`RegField`, the scales of neighbours differing by at
  most one).
* `nbr_scale`, `nbr_dist`: for `z ∈ Δ(y'')` and a neighbour `w = z ± e_μ`: `|j(w) - j(y'')| ≤ 1` and
  `d(y'', y(w)) ≤ L + 4`.
-/
import CoreLean.SFKernelApply

open Finset Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean
namespace SFBounds

open Lattices SeqDom Blocks SmallFieldBlocks SFBox SFBox.SeqDomBox SmallFieldDecay SequenceOperators

variable (S : SeqDom) {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "NF" => SequenceAverages.N0 S
set_option quotPrecheck false in
local notation "jj" => (S.toDomSeq).sc

lemma hRM1_of (h : 8 * (S.L : ℝ) ^ 2 ≤ ((S.R * S.L ^ S.mM : ℕ) : ℝ)) : 1 ≤ S.R * S.L ^ S.mM := by
  have := Nat.one_le_pow S.mM S.L S.Lpos; nlinarith [S.one_le_R]

/-- **The bound of the field at a bond.** -/
lemma X_bond_le {X : Fin 4 → Site NF → Mat} {α₁ : ℝ} (hX : RegField S X α₁) (hα0 : 0 ≤ α₁)
    (hRM1 : 1 ≤ S.R * S.L ^ S.mM) (w : Site NF) (μ : Fin 4) :
    ‖X μ w‖ ≤ α₁ * S.L * ((S.L : ℝ) ^ jj w)⁻¹ ∧ ‖X μ w‖ ≤ α₁ * S.L * ((S.L : ℝ) ^ jj (w + unit _ μ))⁻¹ := by
  set i := min (jj w) (jj (w + unit _ μ))
  have hL1 : (1 : ℝ) ≤ S.L := by exact_mod_cast (show 1 ≤ S.L by have := S.three_le_L; omega)
  have h1 : S.ef w ∈ S.Ω i := (S.toDomSeq).Ω_anti (min_le_left _ _) (S.ef_mem_sc w)
  have h2 : S.ef (w + unit _ μ) ∈ S.Ω i := (S.toDomSeq).Ω_anti (min_le_right _ _) (S.ef_mem_sc _)
  have hb := hX.hA i w μ h1 h2
  obtain ⟨hs1, hs2⟩ := S.sc_sub_le hRM1 w μ
  have step : ∀ a : ℕ, a ≤ i + 1 → ((S.L : ℝ) ^ i)⁻¹ ≤ S.L * ((S.L : ℝ) ^ a)⁻¹ := by
    intro a ha
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), inv_mul_le_iff₀ (by positivity)]
    calc (S.L : ℝ) ^ a ≤ (S.L : ℝ) ^ (i + 1) := pow_le_pow_right₀ hL1 ha
      _ = (S.L : ℝ) ^ i * S.L := pow_succ _ _
  constructor
  · calc ‖X μ w‖ ≤ α₁ * ((S.L : ℝ) ^ i)⁻¹ := hb
      _ ≤ α₁ * (S.L * ((S.L : ℝ) ^ jj w)⁻¹) := by gcongr; exact step _ (by simp only [i]; omega)
      _ = _ := by ring
  · calc ‖X μ w‖ ≤ α₁ * ((S.L : ℝ) ^ i)⁻¹ := hb
      _ ≤ α₁ * (S.L * ((S.L : ℝ) ^ jj (w + unit _ μ))⁻¹) := by gcongr; exact step _ (by simp only [i]; omega)
      _ = _ := by ring

/-- The scales of a site and of its neighbours differ by at most one. -/
lemma nbr_scale (hRM1 : 1 ≤ S.R * S.L ^ S.mM) (z : Site NF) (μ : Fin 4) :
    jj (z + unit _ μ) ≤ jj z + 1 ∧ jj z ≤ jj (z + unit _ μ) + 1 ∧
      jj (z - unit _ μ) ≤ jj z + 1 ∧ jj z ≤ jj (z - unit _ μ) + 1 := by
  obtain ⟨a1, a2⟩ := S.sc_sub_le hRM1 z μ
  obtain ⟨b1, b2⟩ := S.sc_sub_le hRM1 (z - unit _ μ) μ
  rw [sub_add_cancel] at b1 b2
  exact ⟨a2, a1, b1, b2⟩

/-- **The distance of the block of a neighbour.** -/
lemma nbr_dist (hRM1 : 1 ≤ S.R * S.L ^ S.mM) {y'' z : Site NF} (hy'' : y'' ∈ detB S.toDomSeq)
    (hz : z ∈ Blk S.toDomSeq (jj y'') y'') (w : Site NF) (hw : S.dF z w ≤ S.L) :
    S.dF y'' (bc S.toDomSeq w) ≤ S.L + 4 := by
  have h1 : S.dF y'' z ≤ 2 := ENNReal.toReal_le_of_le_ofReal (by norm_num) (S.wdist_block_le hy'' hz)
  have h3 : S.dF (bc S.toDomSeq w) w ≤ 2 :=
    ENNReal.toReal_le_of_le_ofReal (by norm_num) (S.wdist_block_le (bc_mem_detB S w) (mem_blk_bc S w))
  have t1 := S.dF_triangle y'' z w
  have t2 := S.dF_triangle y'' w (bc S.toDomSeq w)
  rw [S.dF_comm w (bc S.toDomSeq w)] at t2
  linarith

lemma dF_unit_le (hRM1 : 1 ≤ S.R * S.L ^ S.mM) (z : Site NF) (μ : Fin 4) :
    S.dF z (z + unit _ μ) ≤ S.L ∧ S.dF z (z - unit _ μ) ≤ S.L := by
  have hL1 : (1 : ℝ) ≤ S.L := by exact_mod_cast (show 1 ≤ S.L by have := S.three_le_L; omega)
  have hp : ∀ a : ℕ, (S.L : ℝ) * ((S.L : ℝ) ^ a)⁻¹ ≤ S.L := fun a => by
    have : ((S.L : ℝ) ^ a)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hL1)
    nlinarith
  refine ⟨(S.wdist_unit_le_sc hRM1 z μ).1.trans (hp _), ?_⟩
  have h := (S.wdist_unit_le_sc hRM1 (z - unit _ μ) μ).1
  rw [sub_add_cancel] at h
  rw [S.dF_comm]
  exact h.trans (hp _)

namespace ScalarHyp

variable {S} {X : Fin 4 → Site (SequenceAverages.N0 S) → Matrix (Fin N) (Fin N) ℂ} {α₁ : ℝ}
  {W : Site (SequenceAverages.N0 S) → Site (SequenceAverages.N0 S) → (Matrix (Fin N) (Fin N) ℂ)ˣ} {η : ℝ}
  {ΩD : Set (Site (SequenceAverages.N0 S))} {δ : ℝ}
  (H : ScalarHyp S X α₁ W η ΩD δ)
include H

/-- **The hypotheses at the trivial configuration.** -/
theorem triv [NeZero N] : ScalarHyp (N := N) S (X0 S) 0 (W1 S) 0 ΩD δ where
  hX := ⟨fun i x μ _ _ => by simp, fun i x μ ν _ _ => by simp⟩
  hα0 := le_rfl
  hα := by norm_num
  hη := le_rfl
  hW1 := fun y _ x _ Z => by simp [Ad, hs, hs2, ntr]
  hW := wbound_triv S
  hsmall := by norm_num
  hRM8 := H.hRM8
  hRMs := H.hRMs
  hRM1 := H.hRM1
  hδ0 := H.hδ0
  hδ := H.hδ
  hD := H.hD

end ScalarHyp

end SFBounds
end CoreLean

end
