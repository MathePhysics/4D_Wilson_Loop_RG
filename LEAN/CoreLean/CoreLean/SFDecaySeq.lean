/-
`lem:sf-decay` of BALABAN_CORE.tex (`4252790331fd`) for the sequences of domains on the torus (`SeqDom`), through the
fine-lattice model `toDomSeq` of `SeqDomFine.lean`: the hypotheses on the weight and on the configuration in the
core's form.

* `hbond_of_lip`, `hblock_of_lip`: a weight `φ` with `|φ(x) - φ(x')| ≤ δd(x, x')` (the weighted distance `d` of
  `def:distance`) satisfies the bounds at the bonds and on the blocks of the model, by the two facts on the distance
  (`wdist_unit_le_sc`, `wdist_block_le`; the step "Two facts on the distance").
* `hE_of_field`: for `𝐔 = e^{ia₀A'}` with `‖A'(b)‖ ≤ α₁a_j⁻¹` at the bonds with both ends in `Ω_j` and `α₁ ≤ 1/32`,
  `|E_bZ| ≤ 6α₁La₀a_{j(x')}⁻¹|Z|` at `b = (x, x')` (`eq:adjoint-lipschitz` with the constant `6` of `hs_Ad_exp_sub_le`,
  and the first fact).
* `sf_conjugated_seq`, `sf_decay_seq`: `eq:sf-conjugated` and `eq:sf-decay` under these hypotheses, with `ε = 6α₁`. The
  transports `W` of the averages (`lem:block-average-transports`) are still data with the bounds `hW1`, `hW2`.
-/
import CoreLean.SeqDomFine
import CoreLean.SmallFieldOperator
import CoreLean.ProductExp

open Set
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean
namespace Lattices
namespace SeqDom

open Blocks SmallFieldBlocks SmallFieldDecay SmallFieldCoercivity SequenceOperators

variable (S : SeqDom) {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ
local notation "NF" => SequenceAverages.N0 S

/-- The weighted distance of two fine points as a real number. -/
def dF (x x' : Site NF) : ℝ := (wdist (S.toContSeq).D (S.ef x) (S.ef x')).toReal

lemma dF_comm (x x' : Site NF) : S.dF x x' = S.dF x' x := by
  unfold dF; rw [wdist_comm]

/-- **The weight at the bonds.** -/
theorem hbond_of_lip (hRM : 1 ≤ S.R * S.L ^ S.mM) {ph : Site NF → ℝ} {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hph : ∀ x x', |ph x - ph x'| ≤ δ * S.dF x x') (x : Site NF) (μ : Fin 4) :
    |ph (x + unit _ μ) - ph x| ≤ δ * (S.toDomSeq).L * (((S.toDomSeq).L : ℝ) ^ (S.toDomSeq).sc x)⁻¹ ∧
      |ph (x + unit _ μ) - ph x| ≤ δ * (S.toDomSeq).L * (((S.toDomSeq).L : ℝ) ^ (S.toDomSeq).sc (x + unit _ μ))⁻¹ := by
  have h := hph (x + unit _ μ) x
  rw [dF_comm] at h
  obtain ⟨h1, h2⟩ := S.wdist_unit_le_sc hRM x μ
  simp only [toDomSeq_L]
  refine ⟨h.trans ?_, h.trans ?_⟩
  · rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h1 hδ0
  · rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h2 hδ0

/-- **The weight on the blocks.** -/
theorem hblock_of_lip {ph : Site NF → ℝ} {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hph : ∀ x x', |ph x - ph x'| ≤ δ * S.dF x x') :
    ∀ y ∈ detB S.toDomSeq, ∀ x ∈ Blk S.toDomSeq ((S.toDomSeq).sc y) y, |ph x - ph y| ≤ 2 * δ := by
  intro y hy x hx
  have h := hph x y
  rw [dF_comm] at h
  have h2 : S.dF y x ≤ 2 := ENNReal.toReal_le_of_le_ofReal (by norm_num) (S.wdist_block_le hy hx)
  nlinarith

/-- The configuration `𝐔 = e^{ia₀A'}`. -/
def expCfg (A : Fin 4 → Site NF → Mat) : Config N NF :=
  fun μ x => expU (Complex.I • (((eta S.L S.k : ℝ) : ℂ) • A μ x))

/-- **The bound of `E_b`** at `𝐔 = e^{ia₀A'}`. -/
theorem hE_of_field (hRM : 1 ≤ S.R * S.L ^ S.mM) {A : Fin 4 → Site NF → Mat} {α₁ : ℝ} (hα0 : 0 ≤ α₁)
    (hα : α₁ ≤ 1 / 32)
    (hA : ∀ j x μ, S.ef x ∈ S.Ω j → S.ef (x + unit _ μ) ∈ S.Ω j → ‖A μ x‖ ≤ α₁ * (sp S.L S.k j)⁻¹)
    (x : Site NF) (μ : Fin 4) (Z : Mat) :
    hs (Ad (S.expCfg A μ x) Z - Z) ≤
      6 * α₁ * (S.toDomSeq).L * (((S.toDomSeq).L : ℝ) ^ (S.toDomSeq).sc (x + unit _ μ))⁻¹ * hs Z := by
  set j := min ((S.toDomSeq).sc x) ((S.toDomSeq).sc (x + unit _ μ))
  have he := eta_pos (k := S.k) S.Lpos
  have hL1 : (1 : ℝ) ≤ S.L := by exact_mod_cast (show 1 ≤ S.L by have := S.three_le_L; omega)
  have hx : S.ef x ∈ S.Ω j := (S.toDomSeq).Ω_anti (min_le_left _ _) (S.ef_mem_sc x)
  have hx' : S.ef (x + unit _ μ) ∈ S.Ω j := (S.toDomSeq).Ω_anti (min_le_right _ _) (S.ef_mem_sc _)
  have hAj := hA j x μ hx hx'
  set X : Mat := ((eta S.L S.k : ℝ) : ℂ) • A μ x
  have hX : ‖X‖ ≤ α₁ * ((S.L : ℝ) ^ j)⁻¹ := by
    simp only [X]
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos he]
    calc eta S.L S.k * ‖A μ x‖ ≤ eta S.L S.k * (α₁ * (sp S.L S.k j)⁻¹) := mul_le_mul_of_nonneg_left hAj he.le
      _ = α₁ * ((S.L : ℝ) ^ j)⁻¹ := by
        unfold sp; rw [mul_inv]; field_simp
  have hpow : ((S.L : ℝ) ^ j)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hL1)
  have hX32 : ‖X‖ ≤ 1 / 32 := hX.trans (by nlinarith)
  have h := hs_Ad_exp_sub_le hX32 Z
  have hsc := (S.sc_sub_le hRM x μ).2
  have hstep : ((S.L : ℝ) ^ j)⁻¹ ≤ S.L * ((S.L : ℝ) ^ (S.toDomSeq).sc (x + unit _ μ))⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), inv_mul_le_iff₀ (by positivity)]
    calc (S.L : ℝ) ^ (S.toDomSeq).sc (x + unit _ μ) ≤ (S.L : ℝ) ^ (j + 1) :=
          pow_le_pow_right₀ hL1 (by omega)
      _ = (S.L : ℝ) ^ j * S.L := pow_succ _ _
  have hZ := hs_nonneg (N := N) Z
  simp only [toDomSeq_L]
  calc hs (Ad (S.expCfg A μ x) Z - Z) ≤ 6 * ‖X‖ * hs Z := h
    _ ≤ 6 * (α₁ * (S.L * ((S.L : ℝ) ^ (S.toDomSeq).sc (x + unit _ μ))⁻¹)) * hs Z := by
        gcongr
        exact hX.trans (mul_le_mul_of_nonneg_left hstep hα0)
    _ = _ := by ring

/-- **`eq:sf-conjugated`** for a sequence of domains, with the core's hypotheses on the weight and on the field. -/
theorem sf_conjugated_seq [NeZero N] (hRM : 1 ≤ S.R * S.L ^ S.mM) (A : Fin 4 → Site NF → Mat)
    (W : Site NF → Site NF → GLN) (ph : Site NF → ℝ) (lam : Site NF → Mat) (δ α₁ η : ℝ) (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ 1 / (128 * S.L)) (hα0 : 0 ≤ α₁) (hα : α₁ ≤ 1 / 32) (hη : 0 ≤ η)
    (hph : ∀ x x', |ph x - ph x'| ≤ δ * S.dF x x')
    (hA : ∀ j x μ, S.ef x ∈ S.Ω j → S.ef (x + unit _ μ) ∈ S.Ω j → ‖A μ x‖ ≤ α₁ * (sp S.L S.k j)⁻¹)
    (hW1 : ∀ y ∈ detB S.toDomSeq, ∀ x ∈ Blk S.toDomSeq ((S.toDomSeq).sc y) y, ∀ Z : Mat,
      hs (Ad (W y x) Z - Z) ≤ η * hs Z)
    (hW2 : ∀ y ∈ detB S.toDomSeq, ∀ x ∈ Blk S.toDomSeq ((S.toDomSeq).sc y) y, ∀ Z : Mat,
      hs (Ad (W y x) Z) ≤ 2 * Real.sqrt N * hs Z)
    (hsmall : (4 * (6 * α₁) + (6 * α₁) ^ 2) * (6 * (S.L : ℝ) ^ 2) + 6 * Real.sqrt N * η ≤ 1 / 8) :
    (1 / 8) * (dsqM lam + wnormM S.toDomSeq lam) ≤
      (Phi S.toDomSeq (S.expCfg A) W (conjL ph lam) (conjR ph lam)).re :=
  sf_conjugated S.toDomSeq (S.expCfg A) W ph lam δ (6 * α₁) η hδ0 hδ (by positivity) hη
    (S.hbond_of_lip hRM hδ0 hph) (S.hblock_of_lip hδ0 hph)
    (fun x μ Z => by have := S.hE_of_field hRM hα0 hα hA x μ Z; simpa only [mul_assoc] using this)
    hW1 hW2 hsmall

/-- **`eq:sf-decay`** for a sequence of domains: with `u = e^φG'(f + D^*_𝐔g)`,
`‖u‖_w + ‖∂u‖₂ ≤ 12(‖e^φf‖_{w⁻¹} + 6L‖e^φg‖₂)`, in the units `a₀ = 1` of the fine lattice. -/
theorem sf_decay_seq [NeZero N] (hRM : 1 ≤ S.R * S.L ^ S.mM) (A : Fin 4 → Site NF → Mat)
    (W : Site NF → Site NF → GLN) (ΩD : Set (Site NF)) (ph : Site NF → ℝ) (δ α₁ η : ℝ) (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ 1 / (128 * S.L)) (hα0 : 0 ≤ α₁) (hα : α₁ ≤ 1 / 32) (hη : 0 ≤ η)
    (hph : ∀ x x', |ph x - ph x'| ≤ δ * S.dF x x')
    (hA : ∀ j x μ, S.ef x ∈ S.Ω j → S.ef (x + unit _ μ) ∈ S.Ω j → ‖A μ x‖ ≤ α₁ * (sp S.L S.k j)⁻¹)
    (hW1 : ∀ y ∈ detB S.toDomSeq, ∀ x ∈ Blk S.toDomSeq ((S.toDomSeq).sc y) y, ∀ Z : Mat,
      hs (Ad (W y x) Z - Z) ≤ η * hs Z)
    (hW2 : ∀ y ∈ detB S.toDomSeq, ∀ x ∈ Blk S.toDomSeq ((S.toDomSeq).sc y) y, ∀ Z : Mat,
      hs (Ad (W y x) Z) ≤ 2 * Real.sqrt N * hs Z)
    (hsmall : (4 * (6 * α₁) + (6 * α₁) ^ 2) * (6 * (S.L : ℝ) ^ 2) + 6 * Real.sqrt N * η ≤ 1 / 8)
    (f : Site NF → Mat) (g : Form1 N NF) :
    Real.sqrt (wnormM S.toDomSeq (expS ph (Gp' S.toDomSeq (S.expCfg A) W ΩD (f + Ds1L a1 (S.expCfg A) g)))) +
        Real.sqrt (dsqM (expS ph (Gp' S.toDomSeq (S.expCfg A) W ΩD (f + Ds1L a1 (S.expCfg A) g)))) ≤
      12 * (Real.sqrt (fwinv S.toDomSeq ph f) + 6 * S.L * Real.sqrt (gnorm ph g)) :=
  sf_decay S.toDomSeq (S.expCfg A) W ΩD ph δ (6 * α₁) η hδ0 hδ (by positivity) hη
    (S.hbond_of_lip hRM hδ0 hph) (S.hblock_of_lip hδ0 hph)
    (fun x μ Z => by have := S.hE_of_field hRM hα0 hα hA x μ Z; simpa only [mul_assoc] using this)
    hW1 hW2 hsmall f g

end SeqDom
end Lattices
end CoreLean

end
