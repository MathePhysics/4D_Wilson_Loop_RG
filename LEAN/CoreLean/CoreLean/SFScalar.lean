/-
`prop:sf-scalar` of BALABAN_CORE.tex (`4252790331fd`), the bounds (iv) of `thm:propagators` for `G'`, on the fine
lattice of a sequence of domains (`a₀ = 1`, `a_j = Lʲ`), at `𝐔 = e^{iX}`, `X = a₀A'`, with the hypotheses of
`lem:sf-decay` and `lem:sf-local` on the field (`RegField`), on the transports `W` of the averages (`WBound` and the
bound `η` of `lem:sf-decay`), and with `Ω₁ ⊂ Ω_D`.

* `wN_one`, `dN_one`, `fN_one`, `gN_one`: the norms of `prop:sf-bounds` for `m = 1` are those of `lem:sf-decay`.
* `hE_of_reg`: the bound of `E_b = Ad_{𝐔(b)} - 1` from `RegField` (`ε = 6α₁`).
* `H1_Gp'`: `(H1)` for `G'` with `C_* = 4NL⁴ + 72L` (`eq:sf-decay`).
* `sfbHyp_Gp'`: the hypotheses of `prop:sf-bounds` for `u = G'(f + D^*_𝐔g)`, `f`, `g` supported in `Δ̃(y')`, with
  `𝒵 = 0`, `𝓕 = 0`, `𝒩 = -Q'^*𝖺Q'`, `C_𝒩 = 4NL⁴`.
* `Gp'_values`, `Gp'_Dstar_values`, `Gp'_gradient`, `Gp'_lap`: the bounds (iv) for `G'`: for `y, y' ∈ 𝐁`, `x ∈ Δ(y)`
  and `λ` supported in `Δ(y')` with `|λ| ≤ Λ`: `|(G'λ)(x)| ≤ C_v a_j²e^{-(7/8)δ₁d(y, y')}Λ`,
  `|(G'D^*_𝐔λ)(x)| ≤ C_v a_je^{-(7/8)δ₁d}Λ`, `|(D_𝐔G'λ)(x, x + e_ν)| ≤ C_g a_je^{-(7/8)δ₁d}Λ`, and
  `|(Δ_𝐔G'λ)(x)| ≤ C_Δe^{-(7/8)δ₁d}Λ` at `x ∈ Ω_D`, with the Hilbert–Schmidt norms of the values (which bound the
  operator norms).
-/
import CoreLean.SFScalarBounds

open Finset Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean
namespace SFBounds

open Lattices SeqDom Blocks SmallFieldBlocks SFBox SFBox.SeqDomBox SFLocal LocalLaplacian InteriorSchauder
  SmallFieldDecay SmallFieldCoercivity SequenceOperators CompressedInverse

variable (S : SeqDom) {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ
local notation "NF" => SequenceAverages.N0 S
local notation "RMS" => ((S.R * S.L ^ S.mM : ℕ) : ℝ)
set_option quotPrecheck false in
local notation "jj" => (S.toDomSeq).sc

/-! ### The norms for `m = 1` -/

lemma nsq_one (v : Mat) : (nsq fun (_ : Fin 1) => v) = hs2 v := by simp [nsq]

lemma wN_one (v : Site NF → Mat) : wN S (fun (_ : Fin 1) => v) = wnormM S.toDomSeq v := by
  simp only [wN, wnormM, nsq_one, toDomSeq_L]

lemma dN_one (v : Site NF → Mat) : dN S (fun (_ : Fin 1) => v) = dsqM v := by
  simp only [dN, dsqM, nsq_one]

lemma fN_one (ph : Site NF → ℝ) (f : Site NF → Mat) : fN S ph (fun (_ : Fin 1) => f) = fwinv S.toDomSeq ph f := by
  simp only [fN, fwinv, nsq_one, toDomSeq_L]

lemma gN_one (ph : Site NF → ℝ) (g : Fin 4 → Site NF → Mat) :
    gN S ph (fun (_ : Fin 1) => g) = gnorm ph g := by
  simp only [gN, gnorm, nsq_one]

lemma eF_one (ph : Site NF → ℝ) (v : Site NF → Mat) : eF S ph (fun (_ : Fin 1) => v) = fun _ => expS ph v := rfl

/-! ### The bound of `E_b` -/

/-- **The bound of `E_b`** at `𝐔 = e^{iX}`. -/
theorem hE_of_reg {X : Fin 4 → Site NF → Mat} {α₁ : ℝ} (hX : RegField S X α₁) (hα0 : 0 ≤ α₁) (hα : α₁ ≤ 1 / 32)
    (x : Site NF) (μ : Fin 4) (Z : Mat) :
    hs (Ad (cfgX X μ x) Z - Z) ≤
      6 * α₁ * (S.toDomSeq).L * (((S.toDomSeq).L : ℝ) ^ (S.toDomSeq).sc (x + unit _ μ))⁻¹ * hs Z := by
  have hRM1 : 1 ≤ S.R * S.L ^ S.mM := by have := Nat.one_le_pow S.mM S.L S.Lpos; nlinarith [S.one_le_R]
  set i := min (jj x) (jj (x + unit _ μ))
  have hL1 : (1 : ℝ) ≤ S.L := by exact_mod_cast (show 1 ≤ S.L by have := S.three_le_L; omega)
  have hx : S.ef x ∈ S.Ω i := (S.toDomSeq).Ω_anti (min_le_left _ _) (S.ef_mem_sc x)
  have hx' : S.ef (x + unit _ μ) ∈ S.Ω i := (S.toDomSeq).Ω_anti (min_le_right _ _) (S.ef_mem_sc _)
  have hb := hX.hA i x μ hx hx'
  have hpow : ((S.L : ℝ) ^ i)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hL1)
  have hX32 : ‖X μ x‖ ≤ 1 / 32 := hb.trans (by nlinarith)
  have h := hs_Ad_exp_sub_le hX32 Z
  have hsc := (S.sc_sub_le hRM1 x μ).2
  have hstep : ((S.L : ℝ) ^ i)⁻¹ ≤ S.L * ((S.L : ℝ) ^ jj (x + unit _ μ))⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), inv_mul_le_iff₀ (by positivity)]
    calc (S.L : ℝ) ^ jj (x + unit _ μ) ≤ (S.L : ℝ) ^ (i + 1) := pow_le_pow_right₀ hL1 (by omega)
      _ = (S.L : ℝ) ^ i * S.L := pow_succ _ _
  have hZ := hs_nonneg (N := N) Z
  simp only [toDomSeq_L]
  calc hs (Ad (cfgX X μ x) Z - Z) ≤ 6 * ‖X μ x‖ * hs Z := h
    _ ≤ 6 * (α₁ * (S.L * ((S.L : ℝ) ^ jj (x + unit _ μ))⁻¹)) * hs Z := by
        gcongr
        exact hb.trans (mul_le_mul_of_nonneg_left hstep hα0)
    _ = _ := by ring

/-! ### `(H1)` for `G'` -/

/-- The number `C_* = 4NL⁴ + 72L`. -/
def Csc (S : SeqDom) (N : ℕ) : ℝ := 4 * N * (S.L : ℝ) ^ 4 + 72 * S.L

/-- **`(H1)` for `G'`** (`eq:sf-decay`). -/
theorem H1_Gp' [NeZero N] {X : Fin 4 → Site NF → Mat} {α₁ : ℝ} (hX : RegField S X α₁) (hα0 : 0 ≤ α₁)
    (hα : α₁ ≤ 1 / 32) {W : Site NF → Site NF → GLN} {η : ℝ} (hη : 0 ≤ η)
    (hW1 : ∀ y ∈ detB S.toDomSeq, ∀ x ∈ Blk S.toDomSeq (jj y) y, ∀ Z : Mat, hs (Ad (W y x) Z - Z) ≤ η * hs Z)
    (hW : WBound S W)
    (hsmall : (4 * (6 * α₁) + (6 * α₁) ^ 2) * (6 * (S.L : ℝ) ^ 2) + 6 * Real.sqrt N * η ≤ 1 / 8)
    (ΩD : Set (Site NF)) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / (128 * S.L)) (f : Site NF → Mat)
    (g : Fin 4 → Site NF → Mat) (ph : Site NF → ℝ) (hph : ∀ x x', |ph x - ph x'| ≤ δ * S.dF x x') :
    Real.sqrt (wN S (eF S ph (fun (_ : Fin 1) =>
        Gp' S.toDomSeq (cfgX X) W ΩD (f + Ds1L a1 (cfgX X) g)))) +
      Real.sqrt (dN S (eF S ph (fun (_ : Fin 1) => Gp' S.toDomSeq (cfgX X) W ΩD (f + Ds1L a1 (cfgX X) g)))) ≤
      Csc S N * (Real.sqrt (fN S ph (fun (_ : Fin 1) => f)) + Real.sqrt (gN S ph (fun (_ : Fin 1) => g))) := by
  have hRM1 : 1 ≤ S.R * S.L ^ S.mM := by have := Nat.one_le_pow S.mM S.L S.Lpos; nlinarith [S.one_le_R]
  have h := sf_decay S.toDomSeq (cfgX X) W ΩD ph δ (6 * α₁) η hδ0 hδ (by positivity) hη
    (S.hbond_of_lip hRM1 hδ0 hph) (S.hblock_of_lip hδ0 hph) (fun x μ Z => by
      have := hE_of_reg S hX hα0 hα x μ Z; simpa only [mul_assoc] using this)
    hW1 (fun y hy x hx Z => (hW y hy x hx Z).1) hsmall f g
  simp only [eF_one, wN_one, dN_one, fN_one, gN_one]
  refine h.trans ?_
  have hL : (3 : ℝ) ≤ S.L := by exact_mod_cast S.three_le_L
  have h1 := Real.sqrt_nonneg (fwinv S.toDomSeq ph f)
  have h2 := Real.sqrt_nonneg (gnorm ph g)
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  unfold Csc
  simp only [toDomSeq_L]
  have : 0 ≤ 4 * (N : ℝ) * (S.L : ℝ) ^ 4 * (Real.sqrt (fwinv S.toDomSeq ph f) + Real.sqrt (gnorm ph g)) := by
    positivity
  nlinarith

/-! ### The hypotheses of `prop:sf-bounds` for `G'` -/

/-- The parameters of `prop:sf-scalar` on the fine lattice. -/
structure ScalarHyp (X : Fin 4 → Site NF → Mat) (α₁ : ℝ) (W : Site NF → Site NF → GLN) (η : ℝ)
    (ΩD : Set (Site NF)) (δ : ℝ) : Prop where
  hX : RegField S X α₁
  hα0 : 0 ≤ α₁
  hα : 64 * (S.L : ℝ) ^ 2 * α₁ ≤ 1
  hη : 0 ≤ η
  hW1 : ∀ y ∈ detB S.toDomSeq, ∀ x ∈ Blk S.toDomSeq ((S.toDomSeq).sc y) y, ∀ Z : Mat,
    hs (Ad (W y x) Z - Z) ≤ η * hs Z
  hW : WBound S W
  hsmall : (4 * (6 * α₁) + (6 * α₁) ^ 2) * (6 * (S.L : ℝ) ^ 2) + 6 * Real.sqrt N * η ≤ 1 / 8
  hRM8 : 8 * (S.L : ℝ) ^ 2 ≤ ((S.R * S.L ^ S.mM : ℕ) : ℝ)
  hRMs : 32 * Real.log S.L / δ ≤ ((S.R * S.L ^ S.mM : ℕ) : ℝ)
  hRM1 : (S.toContSeq).r1 (1 / 2) δ ≤ ((S.R * S.L ^ S.mM : ℕ) : ℝ)
  hδ0 : 0 < δ
  hδ : δ ≤ 1 / (128 * S.L)
  hD : ∀ x, S.ef x ∈ S.Ω 1 → x ∈ ΩD

lemma dinf_lt_of_blk {y x : Site NF} (hx : x ∈ Blk S.toDomSeq (jj y) y) : (dinf x y : ℝ) < (S.L : ℝ) ^ jj y := by
  have h1 : ∀ ν, cd (x ν - y ν) ≤ half S.L (jj y) := fun ν => by
    have := cd_le_of_mem (S := S.toDomSeq) hx ν; simpa only [toDomSeq_L] using this
  have hd : dinf x y ≤ half S.L (jj y) := Finset.sup_le fun ν _ => h1 ν
  have hh : (2 * half S.L (jj y) + 1 : ℝ) = (S.L : ℝ) ^ jj y := by exact_mod_cast two_half_add_one S.L_odd _
  have : (dinf x y : ℝ) ≤ half S.L (jj y) := by exact_mod_cast hd
  have h0 : (0 : ℝ) ≤ half S.L (jj y) := Nat.cast_nonneg _
  linarith

namespace ScalarHyp

variable {S} {X : Fin 4 → Site (SequenceAverages.N0 S) → Matrix (Fin N) (Fin N) ℂ} {α₁ : ℝ}
  {W : Site (SequenceAverages.N0 S) → Site (SequenceAverages.N0 S) → (Matrix (Fin N) (Fin N) ℂ)ˣ} {η : ℝ}
  {ΩD : Set (Site (SequenceAverages.N0 S))} {δ : ℝ}
  (H : ScalarHyp S X α₁ W η ΩD δ)
include H

lemma hα32 : α₁ ≤ 1 / 32 := by
  have := H.hα; have hL : (3 : ℝ) ≤ S.L := by exact_mod_cast S.three_le_L
  nlinarith

/-- `Π_DΔ'Π_D` is invertible on the range of `Π_D` (`lem:sf-decay`, from `eq:sf-conjugated` at `φ = 0`). -/
lemma hK [NeZero N] : IsUnit (ckern (piD ΩD) (DeltaS S.toDomSeq (cfgX X) W)) :=
  deltaS_isUnit S.toDomSeq (cfgX X) W ΩD (6 * α₁) η (by have := H.hα0; positivity) H.hη
    (fun x μ Z => by have := hE_of_reg S H.hX H.hα0 H.hα32 x μ Z; simpa only [mul_assoc] using this)
    H.hW1 (fun y hy x hx Z => (H.hW y hy x hx Z).1) H.hsmall

/-- **The hypotheses of `prop:sf-bounds`** for `u = G'(f + D^*_𝐔g)`, `f`, `g` supported in `Δ̃(y')`. -/
theorem sfbHyp [NeZero N] {y' : Site NF} (hy' : y' ∈ detB S.toDomSeq) {f : Site NF → Mat}
    {g : Fin 4 → Site NF → Mat} {F G : ℝ} (hF : 0 ≤ F) (hG : 0 ≤ G)
    (hfs : ∀ x, (S.L : ℝ) ^ jj y' ≤ (dinf x y' : ℝ) → f x = 0)
    (hgs : ∀ μ x, (S.L : ℝ) ^ jj y' ≤ (dinf x y' : ℝ) → g μ x = 0)
    (hfb : ∀ x, hs (f x) ≤ F) (hgb : ∀ μ x, hs (g μ x) ≤ G) :
    SFBHyp S X α₁ ΩD δ (Csc S N) (4 * N * (S.L : ℝ) ^ 4)
      (fun (_ : Fin 1) => Gp' S.toDomSeq (cfgX X) W ΩD (f + Ds1L a1 (cfgX X) g)) (fun (_ : Fin 1) => f)
      (fun (_ : Fin 1) => g) 0
      (fun (_ : Fin 1) x => -Ncon S.toDomSeq W (Gp' S.toDomSeq (cfgX X) W ΩD (f + Ds1L a1 (cfgX X) g)) x) 0 0
      y' F G := by
  set u := Gp' S.toDomSeq (cfgX X) W ΩD (f + Ds1L a1 (cfgX X) g)
  have hL : (3 : ℝ) ≤ S.L := by exact_mod_cast S.three_le_L
  refine ⟨H.hX, H.hα0, H.hα, H.hRM8, H.hRMs, H.hRM1, H.hδ0, H.hδ, H.hD, ?_, by positivity, hy', hF, hG,
    fun k x hx => hfs x hx, fun k μ x hx => hgs μ x hx, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold Csc; have : (0 : ℝ) ≤ 4 * N * (S.L : ℝ) ^ 4 := by positivity
    linarith
  · intro x; rw [nsq_one, ← hs_sq]; exact pow_le_pow_left₀ (hs_nonneg _) (hfb x) 2
  · intro μ x; rw [nsq_one, ← hs_sq]; exact pow_le_pow_left₀ (hs_nonneg _) (hgb μ x) 2
  · exact fun ph hph => H1_Gp' S H.hX H.hα0 H.hα32 H.hη H.hW1 H.hW H.hsmall ΩD H.hδ0.le H.hδ f g ph hph
  · refine ⟨fun x hx k => ?_, fun z => ?_⟩
    · have h := eqn_Gp' S.toDomSeq (cfgX X) W ΩD H.hK (f + Ds1L a1 (cfgX X) g) hx
      rw [h]
      simp only [Pi.add_apply, Ds1L_apply, a1, Complex.ofReal_one, Pi.zero_apply, add_zero]
      abel
    · simp only [Pi.zero_apply, ContinuousLinearMap.zero_apply, Finset.sum_const_zero]
      ext p; rfl
  · intro x _ z _
    simp only [Pi.zero_apply, norm_zero, Finset.sum_const_zero, mul_zero]
    norm_num
  · intro x hj z hz
    exact Ncon_box S H.hRM8 H.hW u (by omega) hz
  · intro z
    simp only [Pi.zero_apply]
    rw [show (nsq fun (_ : Fin 1) => (0 : Mat)) = 0 by simp [nsq, hs2, ntr], Real.sqrt_zero]
    have : 0 ≤ ∑ x', ((S.L : ℝ) ^ (4 * jj x'))⁻¹ * Real.exp (-(2 * δ * S.dF z x')) *
        Real.sqrt (nsq fun k => (fun (_ : Fin 1) => u) k x') :=
      sum_nonneg fun _ _ => by positivity
    have : 0 ≤ Csc S N := by unfold Csc; positivity
    positivity

/-! ### The bounds (iv) for `G'` -/

/-- **`|(G'λ)(x)| ≤ C_v a_j²e^{-(7/8)δd(y, y')}Λ`** for `λ` supported in `Δ(y')`, `x ∈ Δ(y)`. -/
theorem values [NeZero N] {y y' x : Site NF} (hy : y ∈ detB S.toDomSeq) (hy' : y' ∈ detB S.toDomSeq)
    (hx : x ∈ Blk S.toDomSeq (jj y) y) {lam : Site NF → Mat} {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hsupp : ∀ x', x' ∉ Blk S.toDomSeq (jj y') y' → lam x' = 0) (hbd : ∀ x', hs (lam x') ≤ Λ) :
    hs (Gp' S.toDomSeq (cfgX X) W ΩD lam x) ≤
      Cv S δ (Csc S N) (4 * N * (S.L : ℝ) ^ 4) * Real.exp (-(7 / 8 * δ * S.dF y y')) * ((S.L : ℝ) ^ (2 * jj y) * Λ) := by
  have Hb := H.sfbHyp hy' (g := 0) hΛ le_rfl
    (fun x' hx' => hsupp x' fun hm => absurd (dinf_lt_of_blk S hm) (not_lt.2 hx'))
    (fun μ x' _ => rfl) hbd (fun μ x' => by simp [hs, hs2, ntr])
  have h := Hb.values hy hx
  rw [map_zero, add_zero] at h
  simp only [nsq_one, mul_zero, add_zero] at h
  exact h

/-- **`|(G'D^*_𝐔λ)(x)| ≤ C_v a_je^{-(7/8)δd(y, y')}Λ`** for `λ = (λ_μ)` supported in `Δ(y')`, `x ∈ Δ(y)`. -/
theorem Dstar_values [NeZero N] {y y' x : Site NF} (hy : y ∈ detB S.toDomSeq) (hy' : y' ∈ detB S.toDomSeq)
    (hx : x ∈ Blk S.toDomSeq (jj y) y) {lam : Fin 4 → Site NF → Mat} {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hsupp : ∀ μ x', x' ∉ Blk S.toDomSeq (jj y') y' → lam μ x' = 0) (hbd : ∀ μ x', hs (lam μ x') ≤ Λ) :
    hs (Gp' S.toDomSeq (cfgX X) W ΩD (Ds1L a1 (cfgX X) lam) x) ≤
      Cv S δ (Csc S N) (4 * N * (S.L : ℝ) ^ 4) * Real.exp (-(7 / 8 * δ * S.dF y y')) * ((S.L : ℝ) ^ jj y * Λ) := by
  have Hb := H.sfbHyp hy' (f := 0) le_rfl hΛ (fun x' _ => rfl)
    (fun μ x' hx' => hsupp μ x' fun hm => absurd (dinf_lt_of_blk S hm) (not_lt.2 hx'))
    (fun x' => by simp [hs, hs2, ntr]) hbd
  have h := Hb.values hy hx
  rw [zero_add] at h
  simp only [nsq_one, mul_zero, zero_add] at h
  exact h

/-- **`|(D_𝐔G'λ)(x, x + e_ν)| ≤ C_g a_je^{-(7/8)δd(y, y')}Λ`** for `λ` supported in `Δ(y')`, `x ∈ Δ(y)`. -/
theorem gradient [NeZero N] {y y' x : Site NF} (hy : y ∈ detB S.toDomSeq) (hy' : y' ∈ detB S.toDomSeq)
    (hx : x ∈ Blk S.toDomSeq (jj y) y) {lam : Site NF → Mat} {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hsupp : ∀ x', x' ∉ Blk S.toDomSeq (jj y') y' → lam x' = 0) (hbd : ∀ x', hs (lam x') ≤ Λ) (ν : Fin 4) :
    hs (Dfw 1 (cfgX X) ν (Gp' S.toDomSeq (cfgX X) W ΩD lam) x) ≤
      Cg S δ (Csc S N) (4 * N * (S.L : ℝ) ^ 4) α₁ * Real.exp (-(7 / 8 * δ * S.dF y y')) *
        ((S.L : ℝ) ^ jj y * Λ) := by
  have Hb := H.sfbHyp hy' (g := 0) hΛ le_rfl
    (fun x' hx' => hsupp x' fun hm => absurd (dinf_lt_of_blk S hm) (not_lt.2 hx'))
    (fun μ x' _ => rfl) hbd (fun μ x' => by simp [hs, hs2, ntr])
  have h := Hb.gradient (fun k μ x => rfl) hy hx ν
  rw [map_zero, add_zero] at h
  simp only [nsq_one, add_zero] at h
  exact h

/-- **`|(Δ_𝐔G'λ)(x)| ≤ C_Δe^{-(7/8)δd(y, y')}Λ`** for `λ` supported in `Δ(y')`, `x ∈ Δ(y) ∩ Ω_D`. -/
theorem lap [NeZero N] {y y' x : Site NF} (hy : y ∈ detB S.toDomSeq) (hy' : y' ∈ detB S.toDomSeq)
    (hx : x ∈ Blk S.toDomSeq (jj y) y) (hxD : x ∈ ΩD) {lam : Site NF → Mat} {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hsupp : ∀ x', x' ∉ Blk S.toDomSeq (jj y') y' → lam x' = 0) (hbd : ∀ x', hs (lam x') ≤ Λ) :
    hs (Lap 1 (cfgX X) (Gp' S.toDomSeq (cfgX X) W ΩD lam) x) ≤
      CDel S δ (Csc S N) (4 * N * (S.L : ℝ) ^ 4) * Real.exp (-(7 / 8 * δ * S.dF y y')) * Λ := by
  have Hb := H.sfbHyp hy' (g := 0) hΛ le_rfl
    (fun x' hx' => hsupp x' fun hm => absurd (dinf_lt_of_blk S hm) (not_lt.2 hx'))
    (fun μ x' _ => rfl) hbd (fun μ x' => by simp [hs, hs2, ntr])
  set u := Gp' S.toDomSeq (cfgX X) W ΩD (lam + Ds1L a1 (cfgX X) 0)
  obtain ⟨z', hz', hmax⟩ := Ncon_max S H.hW u x
  have hz'd := dinf_blk_le S (mem_blk_bc S x) hz' (bc_mem_detB S x)
  have hZN : Real.sqrt (nsq fun k => (0 : Fin 1 → Site NF → Mat) k x) +
      Real.sqrt (nsq fun k => (fun (_ : Fin 1) x => -Ncon S.toDomSeq W u x) k x) ≤
      Csc S N * ((S.L : ℝ) ^ (2 * jj x))⁻¹ * Real.sqrt (nsq fun k => (fun (_ : Fin 1) => u) k z') := by
    simp only [Pi.zero_apply, nsq_one]
    rw [show hs2 (0 : Mat) = 0 by simp [hs2, ntr], Real.sqrt_zero, zero_add,
      show Real.sqrt (hs2 (-Ncon S.toDomSeq W u x)) = hs (Ncon S.toDomSeq W u x) by
        rw [show Real.sqrt (hs2 (-Ncon S.toDomSeq W u x)) = hs (-Ncon S.toDomSeq W u x) from rfl, SupportCont.hs_neg]]
    refine hmax.trans ?_
    have hN : (4 * N : ℝ) ≤ Csc S N := by
      unfold Csc
      have hL1 : (1 : ℝ) ≤ (S.L : ℝ) ^ 4 := one_le_pow₀ (by linarith [show (3 : ℝ) ≤ S.L by exact_mod_cast S.three_le_L])
      have : (0 : ℝ) ≤ 72 * S.L := by positivity
      nlinarith [show (0 : ℝ) ≤ N from Nat.cast_nonneg _]
    have : 0 ≤ ((S.L : ℝ) ^ (2 * jj x))⁻¹ * hs (u z') := mul_nonneg (by positivity) (hs_nonneg _)
    show 4 * N * ((S.L : ℝ) ^ (2 * jj x))⁻¹ * hs (u z') ≤ Csc S N * ((S.L : ℝ) ^ (2 * jj x))⁻¹ * hs (u z')
    nlinarith
  have h := Hb.lap_bound (fun k μ x => rfl) hy hx hxD hz'd hZN
  have e : lam + Ds1L a1 (cfgX X) 0 = lam := by rw [map_zero, add_zero]
  simp only [u, e, nsq_one, mul_zero, add_zero] at h
  exact h

end ScalarHyp

end SFBounds
end CoreLean

end
