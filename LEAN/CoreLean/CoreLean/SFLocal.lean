/-
`lem:sf-local` of BALABAN_CORE.tex (`4252790331fd`), in the coordinates of the layer: the box `Q_ρ` is
`{|εn - εn₀|_∞ ≤ ρ}` on `εℤ⁴`, `ε = a₀/a`, and the data are those of the core multiplied by the powers of `a` of its step
"The rescaled equation" (`ã = aA'`, `f̃ = a²f`, `g̃ = ag`, `Z̃ = a²𝒵`, `Ñu = a²𝒩u`); the norms `‖·‖_{p,Q_ρ}` with the
weights `ε⁴` are `a^{-4/p}` times those with the weights `a₀⁴`, so that `Θ` is the core's `Θ`.

* `sf_local_i`: `|u(z)| ≤ K_sfΘ` on `Q_4`, `K_sf = 2³⁷(6 + C_𝒩)`.
* `sf_local_ii`: `|u(z) - u(z')| ≤ K_sf(β)Θ|z - z'|₁^β` on `Q_3`, `K_sf(β) = 2³⁹(6 + C_𝒩)K_H(β)K_D(β)`.
* `sf_local_iii`: the first differences and their modulus on `Q_2`, when `g` has the modulus `Γ` on `Q_3`.
* `sf_local_iv`: the second differences in `L²` on `Q_1`, when `g = 0`.
-/
import CoreLean.SFLocalNorms

open Finset Matrix
open scoped Matrix.Norms.L2Operator Classical

noncomputable section

namespace CoreLean
namespace SFLocal

open LocalLaplacian InteriorSchauder

variable {N m : ℕ}

/-- `K_sf = 2³⁷(6 + C_𝒩)`. -/
def Ksf (CN : ℝ) : ℝ := 2 ^ 37 * (6 + CN)

/-- `K_sf(β) = 2³⁹(6 + C_𝒩)K_H(β)K_D(β)`. -/
def Ksfb (CN β : ℝ) : ℝ := 2 ^ 39 * (6 + CN) * KH β * KD β

lemma KH_ge (β : ℝ) (hβ1 : β < 1) : 472 ≤ KH β := by unfold KH; have := CS'_pos hβ1; linarith

lemma KD_ge (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) : 472 ≤ KD β := by
  unfold KD; have := CS_pos hβ0 hβ1; have := CS'_pos hβ1; linarith

/-- The hypotheses of `lem:sf-local` in the coordinates of the layer. -/
structure SFHyp (ε : ℝ) (n₀ : Fin 4 → ℤ) (A : Fin 4 → (Fin 4 → ℤ) → Matrix (Fin N) (Fin N) ℂ) (L α₁ : ℝ)
    (D : SFData N m) (CN Fb Gb : ℝ) : Prop where
  field : FieldHyp ε n₀ A L α₁
  eqn : ∀ n, InQr ε n₀ 8 n → covLapV ε A D.u n = D.f n + ∑ μ, DbwV ε A μ (D.g μ) n + locApp D.Z D.u n + D.Nu n
  hZ : ∀ n, InQr ε n₀ 8 n → ∑ e ∈ Eoff, ‖D.Z n e‖ ≤ 1 / 4
  hCN : 0 ≤ CN
  hf : ∀ n, InQr ε n₀ (8 + 2 * L) n → ‖D.f n‖ ≤ Fb
  hg : ∀ μ n, InQr ε n₀ (8 + 2 * L) n → ‖D.g μ n‖ ≤ Gb
  hN1 : ∀ n, InQr ε n₀ 8 n → ‖D.Nu n‖ ≤ CN * pn ε (QF ε n₀ (8 + 2 * L)) 2 (fun n => ‖D.u n‖)

variable {ε : ℝ} {n₀ : Fin 4 → ℤ} {A : Fin 4 → (Fin 4 → ℤ) → Matrix (Fin N) (Fin N) ℂ} {L α₁ : ℝ}
  {D : SFData N m} {CN Fb Gb : ℝ}

/-- `Θ = ‖u‖_{2,Q_{8+2L}} + ‖f‖_{∞,Q_{8+2L}} + max_μ‖g_μ‖_{∞,Q_{8+2L}}` (with the bounds `Fb`, `Gb`). -/
def Th (ε : ℝ) (n₀ : Fin 4 → ℤ) (L : ℝ) (D : SFData N m) (Fb Gb : ℝ) : ℝ :=
  pn ε (QF ε n₀ (8 + 2 * L)) 2 (fun n => ‖D.u n‖) + Fb + Gb

namespace SFHyp

variable (S : SFHyp ε n₀ A L α₁ D CN Fb Gb)
include S

lemma center (ρ : ℝ) (hρ : 0 ≤ ρ) : InQr ε n₀ ρ n₀ := fun μ => by simp [tc, hρ]

lemma nonneg : 0 ≤ pn ε (QF ε n₀ (8 + 2 * L)) 2 (fun n => ‖D.u n‖) ∧ 0 ≤ Fb ∧ 0 ≤ Gb := by
  have hL := S.field.hL
  have h0 := S.center (8 + 2 * L) (by linarith)
  exact ⟨pn_nonneg fun n _ => norm_nonneg _, (norm_nonneg _).trans (S.hf _ h0),
    (norm_nonneg _).trans (S.hg 0 _ h0)⟩

lemma Θ_nonneg : 0 ≤ Th ε n₀ L D Fb Gb := by obtain ⟨a, b, c⟩ := S.nonneg; unfold Th; linarith

lemma sub8 {z : Fin 4 → ℤ} {ρ ρ' : ℝ} (hz : InQr ε n₀ ρ' z) (h : ρ + ρ' ≤ 8) :
    ∀ k, InQr ε z ρ k → InQr ε n₀ 8 k := fun k hk => inQr_mono h (inQr_trans hk hz)

set_option maxRecDepth 4000 in
lemma eqnL {z : Fin 4 → ℤ} {R ρ' : ℝ} (hz : InQr ε n₀ ρ' z) (h : R - 2 / 3 + ρ' ≤ 8) :
    Eqn (toLData ε A D) ε z R := by
  intro n hn
  have := eqn_of ε A D S.field.hε.ne' (S.eqn n (S.sub8 hz h n hn))
  exact this

lemma locNormL {z : Fin 4 → ℤ} {R ρ' : ℝ} (hz : InQr ε n₀ ρ' z) (h : R + ρ' ≤ 8) :
    LocNorm (toLData ε A D) ε z R :=
  S.field.locNorm_of D (S.sub8 hz (by linarith [S.field.hε]) ) S.hZ

/-- The bound of `h` at the points of `Q_8`. -/
lemma norm_h_le {n : Fin 4 → ℤ} (hn : InQr ε n₀ 8 n) :
    ‖(toLData ε A D).h n‖ ≤ Fb + 24 * (α₁ * L) * Gb + CN * pn ε (QF ε n₀ (8 + 2 * L)) 2 (fun n => ‖D.u n‖) := by
  have H := S.field
  obtain ⟨_, _, hGb⟩ := S.nonneg
  show ‖D.f n + ∑ μ, Kb ε A μ n (D.g μ (n - e4 μ)) + D.Nu n‖ ≤ _
  have hsum : ‖∑ μ, Kb ε A μ n (D.g μ (n - e4 μ))‖ ≤ ∑ _μ : Fin 4, 6 * (α₁ * L) * Gb :=
    (norm_sum_le _ _).trans (sum_le_sum fun μ _ => ((Kb ε A μ n).le_opNorm _).trans
      (mul_le_mul (H.norm_Kb (H.inQ_sub hn μ)) (S.hg μ _ (H.inQ_sub hn μ)) (norm_nonneg _)
        (by have := H.hα0; have := H.hL; positivity)))
  rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have := S.hf n (H.inQ_big0 hn)
  have := S.hN1 n hn
  calc _ ≤ ‖D.f n‖ + ‖∑ μ, Kb ε A μ n (D.g μ (n - e4 μ))‖ + ‖D.Nu n‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ _ := by push_cast at hsum; linarith

/-- `H_r ≤ (5 + C_𝒩)Θ` for the boxes in `Q_8`. -/
lemma H_le : Fb + 24 * (α₁ * L) * Gb + CN * pn ε (QF ε n₀ (8 + 2 * L)) 2 (fun n => ‖D.u n‖) + ∑ _μ : Fin 4, Gb ≤
    (5 + CN) * Th ε n₀ L D Fb Gb := by
  obtain ⟨h1, h2, h3⟩ := S.nonneg
  have := S.field.αL_le
  have hCN := S.hCN
  have hαL : 0 ≤ α₁ * L := by have := S.field.hα0; have := S.field.hL; positivity
  rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  unfold Th
  push_cast
  nlinarith [mul_nonneg hCN h2, mul_nonneg hCN h3, mul_le_mul_of_nonneg_right this h3]

/-- The bounds of the data on a box in `Q_8`. -/
lemma boundsL {z : Fin 4 → ℤ} {r ρ' Su : ℝ} (hz : InQr ε n₀ ρ' z) (h : r + 1 + ρ' ≤ 8)
    (hu : ∀ n, InQr ε z (r + 1) n → ‖D.u n‖ ≤ Su) :
    Bounds (toLData ε A D) ε r z Su (Fb + 24 * (α₁ * L) * Gb + CN * pn ε (QF ε n₀ (8 + 2 * L)) 2 (fun n => ‖D.u n‖))
      (fun _ => Gb) :=
  ⟨hu, fun n hn => S.norm_h_le (S.sub8 hz h n hn),
    fun μ n hn => S.hg μ n (S.field.inQ_big0 (S.sub8 hz h n hn))⟩

/-- **`lem:sf-local`(i)**: `|u(z)| ≤ K_sfΘ` for `z ∈ Q_4`. -/
theorem sf_local_i {z : Fin 4 → ℤ} (hz : InQr ε n₀ 4 z) : ‖D.u z‖ ≤ Ksf CN * Th ε n₀ L D Fb Gb := by
  have H := S.field
  have hL := H.hL
  have hc := local_Linf_chain (toLData ε A D) H.hε H.hε3 (R := 4) (n₀ := z) le_rfl (S.eqnL hz (by norm_num))
    (S.locNormL hz (by norm_num)) (fun n hn => S.norm_h_le (S.sub8 hz (by norm_num) n hn))
    (fun μ n hn => S.hg μ n (H.inQ_big0 (S.sub8 hz (by norm_num) n hn))) (n := z) (fun μ => by simp [tc])
  have hsub : pn ε (QF ε z 4) 2 (fun n => ‖D.u n‖) ≤ pn ε (QF ε n₀ (8 + 2 * L)) 2 (fun n => ‖D.u n‖) :=
    pn_subset (by norm_num) (fun k hk => (mem_QF H.hε).2 (inQr_mono (by linarith) (inQr_trans ((mem_QF H.hε).1 hk) hz)))
      (fun _ _ => norm_nonneg _)
  have hHle := S.H_le
  have hΘ := S.Θ_nonneg
  have hU : pn ε (QF ε n₀ (8 + 2 * L)) 2 (fun n => ‖D.u n‖) ≤ Th ε n₀ L D Fb Gb := by
    obtain ⟨_, h2, h3⟩ := S.nonneg; unfold Th; linarith
  have hc' : ‖D.u z‖ ≤ 2 ^ 36 * (pn ε (QF ε z 4) 2 (fun n => ‖D.u n‖) +
      ((Fb + 24 * (α₁ * L) * Gb + CN * pn ε (QF ε n₀ (8 + 2 * L)) 2 (fun n => ‖D.u n‖)) + ∑ _μ : Fin 4, Gb)) := hc
  refine hc'.trans ?_
  unfold Ksf
  have hCN := S.hCN
  nlinarith

lemma u_le_on4 {n : Fin 4 → ℤ} (hn : InQr ε n₀ (3 + 1) n) : ‖D.u n‖ ≤ Ksf CN * Th ε n₀ L D Fb Gb :=
  S.sf_local_i (inQr_mono (by norm_num) hn)

lemma Hsum_le : Fb + 24 * (α₁ * L) * Gb + CN * pn ε (QF ε n₀ (8 + 2 * L)) 2 (fun n => ‖D.u n‖) +
    ∑ _μ : Fin 4, Gb ≤ (6 + CN) * Th ε n₀ L D Fb Gb := by
  have := S.H_le; have := S.Θ_nonneg; nlinarith

/-- The modulus of `u` on `Q_3` with the constant `2³⁸(6 + C_𝒩)K_H(β)Θ`. -/
theorem sf_local_ii_aux {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {z z' : Fin 4 → ℤ} (hz : InQr ε n₀ 3 z)
    (hz' : InQr ε n₀ 3 z') :
    ‖D.u z - D.u z'‖ ≤ 2 ^ 38 * (6 + CN) * KH β * Th ε n₀ L D Fb Gb * (ε * l1 (z - z')) ^ β := by
  have H := S.field
  have h0 := S.center (n₀ := n₀) 0 le_rfl
  have hb := S.boundsL (r := 3) (Su := Ksf CN * Th ε n₀ L D Fb Gb) h0 (by norm_num) fun n hn => S.u_le_on4 hn
  have hc := local_holder (toLData ε A D) H.hε H.hε3 (r := 3) (R := 4) (by norm_num) (by norm_num) hβ0 hβ1
    (S.eqnL h0 (by norm_num)) (S.locNormL h0 (by norm_num)) hb hz hz'
  have hc' : ‖D.u z - D.u z'‖ ≤ KH β * (Ksf CN * Th ε n₀ L D Fb Gb +
      ((Fb + 24 * (α₁ * L) * Gb + CN * pn ε (QF ε n₀ (8 + 2 * L)) 2 (fun n => ‖D.u n‖)) + ∑ _μ : Fin 4, Gb)) *
      (ε * l1 (z - z')) ^ β := hc
  refine hc'.trans (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (mul_nonneg H.hε.le (l1_nonneg _)) _))
  have hK := KH_ge β hβ1
  have hT := S.Θ_nonneg
  have hH := S.H_le
  have hCN := S.hCN
  unfold Ksf
  have e : Fb + 24 * (α₁ * L) * Gb + CN * pn ε (QF ε n₀ (8 + 2 * L)) 2 (fun n => ‖D.u n‖) + ∑ _μ : Fin 4, Gb ≤
      (6 + CN) * Th ε n₀ L D Fb Gb := S.Hsum_le
  have : 2 ^ 37 * (6 + CN) * Th ε n₀ L D Fb Gb +
      (Fb + 24 * (α₁ * L) * Gb + CN * pn ε (QF ε n₀ (8 + 2 * L)) 2 (fun n => ‖D.u n‖) + ∑ _μ : Fin 4, Gb) ≤
      2 ^ 38 * (6 + CN) * Th ε n₀ L D Fb Gb := by nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 6 + CN) hT]
  calc KH β * (2 ^ 37 * (6 + CN) * Th ε n₀ L D Fb Gb + _) ≤ KH β * (2 ^ 38 * (6 + CN) * Th ε n₀ L D Fb Gb) :=
        mul_le_mul_of_nonneg_left this (by linarith)
    _ = _ := by ring

/-- **`lem:sf-local`(ii)**. -/
theorem sf_local_ii {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {z z' : Fin 4 → ℤ} (hz : InQr ε n₀ 3 z)
    (hz' : InQr ε n₀ 3 z') :
    ‖D.u z - D.u z'‖ ≤ Ksfb CN β * Th ε n₀ L D Fb Gb * (ε * l1 (z - z')) ^ β := by
  refine (S.sf_local_ii_aux hβ0 hβ1 hz hz').trans (mul_le_mul_of_nonneg_right ?_
    (Real.rpow_nonneg (mul_nonneg S.field.hε.le (l1_nonneg _)) _))
  have hK := KH_ge β hβ1
  have hD := KD_ge β hβ0 hβ1
  have hT := S.Θ_nonneg
  have hCN := S.hCN
  unfold Ksfb
  have h1 : 0 ≤ (6 + CN) * KH β * Th ε n₀ L D Fb Gb := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hD h1]

/-- **`lem:sf-local`(iii)**: the first differences and their modulus, when the `g_μ` have the modulus `Γ` on `Q_3`. -/
theorem sf_local_iii {β Γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hΓ0 : 0 ≤ Γ)
    (hΓ : ∀ μ n n', InQr ε n₀ 3 n → InQr ε n₀ 3 n' → ε * l1 (n - n') ≤ 1 →
      ‖D.g μ n - D.g μ n'‖ ≤ Γ * (ε * l1 (n - n')) ^ β) (ν : Fin 4) {z z' : Fin 4 → ℤ}
    (h1 : InQr ε n₀ 2 z) (h2 : InQr ε n₀ 2 (z + e4 ν)) (h1' : InQr ε n₀ 2 z') (h2' : InQr ε n₀ 2 (z' + e4 ν)) :
    ‖dfw ε ν D.u z‖ ≤ Ksfb CN β * (Th ε n₀ L D Fb Gb + Γ) ∧
      ‖dfw ε ν D.u z - dfw ε ν D.u z'‖ ≤ Ksfb CN β * (Th ε n₀ L D Fb Gb + Γ) * (ε * l1 (z - z')) ^ β := by
  have H := S.field
  have h0 := S.center (n₀ := n₀) 0 le_rfl
  have hT := S.Θ_nonneg
  have hCN := S.hCN
  have hK := KH_ge β hβ1
  have hD := KD_ge β hβ0 hβ1
  set Υ := 2 ^ 38 * (6 + CN) * KH β * Th ε n₀ L D Fb Gb with hΥ
  have hΥ0 : 0 ≤ Υ := by positivity
  have hb := S.boundsL (r := 2) (Su := Ksf CN * Th ε n₀ L D Fb Gb) h0 (by norm_num)
    fun n hn => S.sf_local_i (inQr_mono (by norm_num) hn)
  have hMo : Moduli (toLData ε A D) ε 2 n₀ β Υ Γ :=
    ⟨fun n n' hn hn' _ => S.sf_local_ii_aux hβ0 hβ1 (inQr_mono (by norm_num) hn) (inQr_mono (by norm_num) hn'),
      fun μ n n' hn hn' hd => hΓ μ n n' (inQr_mono (by norm_num) hn) (inQr_mono (by norm_num) hn') hd⟩
  have hgl := H.gLip_of D (z := n₀) (ρ := 2 + 1) (S.sub8 h0 (by norm_num))
  have hd := local_derivative (toLData ε A D) H.hε H.hε3 (r := 2) (R := 3) (by norm_num) (by norm_num) hβ0 hβ1
    (S.eqnL h0 (by norm_num)) (S.locNormL h0 (by norm_num)) hgl hb hMo hΥ0 hΓ0 ν h1 h2
  have hdh := local_derivative_holder (toLData ε A D) H.hε H.hε3 (r := 2) (R := 3) (by norm_num) (by norm_num) hβ0
    hβ1 (S.eqnL h0 (by norm_num)) (S.locNormL h0 (by norm_num)) hgl hb hMo hΥ0 hΓ0 ν h1 h2 h1' h2'
  set Hs := Fb + 24 * (α₁ * L) * Gb + CN * pn ε (QF ε n₀ (8 + 2 * L)) 2 (fun n => ‖D.u n‖) + ∑ _μ : Fin 4, Gb
  have hHs : Hs ≤ (6 + CN) * Th ε n₀ L D Fb Gb := S.Hsum_le
  have key : KD β * (Ksf CN * Th ε n₀ L D Fb Gb + Υ + Hs + Γ) ≤ Ksfb CN β * (Th ε n₀ L D Fb Gb + Γ) := by
    unfold Ksf Ksfb
    have hc6 : 0 ≤ 6 + CN := by linarith
    have a1 : 2 ^ 37 * (6 + CN) * Th ε n₀ L D Fb Gb + Υ + Hs ≤ 2 ^ 39 * (6 + CN) * KH β * Th ε n₀ L D Fb Gb := by
      have : 0 ≤ (6 + CN) * Th ε n₀ L D Fb Gb := mul_nonneg hc6 hT
      rw [hΥ]; nlinarith [mul_le_mul_of_nonneg_right hK this]
    have a2 : Γ ≤ 2 ^ 39 * (6 + CN) * KH β * Γ := by
      have : 1 ≤ 2 ^ 39 * (6 + CN) * KH β := by nlinarith
      nlinarith
    have hD0 : 0 ≤ KD β := by linarith
    calc KD β * (2 ^ 37 * (6 + CN) * Th ε n₀ L D Fb Gb + Υ + Hs + Γ)
        ≤ KD β * (2 ^ 39 * (6 + CN) * KH β * Th ε n₀ L D Fb Gb + 2 ^ 39 * (6 + CN) * KH β * Γ) :=
          mul_le_mul_of_nonneg_left (by linarith) hD0
      _ = 2 ^ 39 * (6 + CN) * KH β * KD β * (Th ε n₀ L D Fb Gb + Γ) := by ring
  refine ⟨(show ‖dfw ε ν D.u z‖ ≤ KD β * (Ksf CN * Th ε n₀ L D Fb Gb + Υ + Hs + Γ) from hd).trans key, ?_⟩
  refine (show ‖dfw ε ν D.u z - dfw ε ν D.u z'‖ ≤ KD β * (Ksf CN * Th ε n₀ L D Fb Gb + Υ + Hs + Γ) *
    (ε * l1 (z - z')) ^ β from hdh).trans ?_
  exact mul_le_mul_of_nonneg_right key (Real.rpow_nonneg (mul_nonneg H.hε.le (l1_nonneg _)) _)

/-- **`lem:sf-local`(iv)**: the second differences in `L²`, when `g = 0`. -/
theorem sf_local_iv (hg0 : ∀ μ n, D.g μ n = 0)
    (hN2 : wN (QF ε n₀ 2) (fun _ => ε ^ 4) (fun n => ‖D.Nu n‖) ≤
      CN * wN (QF ε n₀ (2 + 2 * L)) (fun _ => ε ^ 4) (fun n => ‖D.u n‖)) :
    Real.sqrt (∑ κ, ∑ ν, ∑ z ∈ (QF ε n₀ 1).filter (fun z => InQr ε n₀ 1 (z + e4 κ) ∧ InQr ε n₀ 1 (z + e4 ν) ∧
        InQr ε n₀ 1 (z + e4 κ + e4 ν)), ε ^ 4 * ‖dfw ε κ (dfw ε ν D.u) z‖ ^ 2) ≤
      wN (QF ε n₀ 2) (fun _ => ε ^ 4) (fun z => ‖D.f z‖) +
        Ksf CN * (wN (QF ε n₀ (2 + 2 * L)) (fun _ => ε ^ 4) (fun z => ‖D.u z‖) +
          Real.sqrt (∑ μ, ∑ z ∈ (QF ε n₀ 2).filter (fun z => InQr ε n₀ 2 (z + e4 μ)),
            ε ^ 4 * ‖dfw ε μ D.u z‖ ^ 2)) := by
  have H := S.field
  have h0 := S.center (n₀ := n₀) 0 le_rfl
  have hw : ∀ z : Fin 4 → ℤ, 0 ≤ (fun _ => ε ^ 4) z := fun _ => by positivity
  have hs := local_second (toLData ε A D) H.hε H.hε3 (r := 1) (R := 2) (by norm_num) (by norm_num) hg0
    (S.eqnL h0 (by norm_num)) (S.locNormL h0 (by norm_num)) (H.gLip_of D (S.sub8 h0 (by norm_num)))
  rw [show (1 : ℝ) + 1 = 2 by norm_num] at hs
  have hh : wN (QF ε n₀ 2) (fun _ => ε ^ 4) (fun n => ‖(toLData ε A D).h n‖) ≤
      wN (QF ε n₀ 2) (fun _ => ε ^ 4) (fun z => ‖D.f z‖) + wN (QF ε n₀ 2) (fun _ => ε ^ 4) (fun n => ‖D.Nu n‖) := by
    refine (wN_mono hw (fun n _ => norm_nonneg _) fun n _ => ?_).trans (wN_add hw _ _)
    show ‖D.f n + ∑ μ, Kb ε A μ n (D.g μ (n - e4 μ)) + D.Nu n‖ ≤ ‖D.f n‖ + ‖D.Nu n‖
    simp only [hg0, map_zero, sum_const_zero, add_zero]
    exact norm_add_le _ _
  have hsub : wN (QF ε n₀ 2) (fun _ => ε ^ 4) (fun n => ‖D.u n‖) ≤
      wN (QF ε n₀ (2 + 2 * L)) (fun _ => ε ^ 4) (fun n => ‖D.u n‖) :=
    wN_subset (fun k hk => (mem_QF H.hε).2 (inQr_mono (by linarith [H.hL]) ((mem_QF H.hε).1 hk))) _
  have hU := wN_nonneg (s := QF ε n₀ (2 + 2 * L)) (w := fun _ => ε ^ 4) (fun n => ‖D.u n‖)
  have hdU := Real.sqrt_nonneg (∑ μ, ∑ z ∈ (QF ε n₀ 2).filter (fun z => InQr ε n₀ 2 (z + e4 μ)),
    ε ^ 4 * ‖dfw ε μ D.u z‖ ^ 2)
  have hCN := S.hCN
  have hs' : Real.sqrt (∑ κ, ∑ ν, ∑ z ∈ (QF ε n₀ 1).filter (fun z => InQr ε n₀ 1 (z + e4 κ) ∧
      InQr ε n₀ 1 (z + e4 ν) ∧ InQr ε n₀ 1 (z + e4 κ + e4 ν)), ε ^ 4 * ‖dfw ε κ (dfw ε ν D.u) z‖ ^ 2) ≤
      wN (QF ε n₀ 2) (fun _ => ε ^ 4) (fun n => ‖(toLData ε A D).h n‖) +
        2 ^ 11 * (wN (QF ε n₀ 2) (fun _ => ε ^ 4) (fun n => ‖D.u n‖) +
          Real.sqrt (∑ μ, ∑ z ∈ (QF ε n₀ 2).filter (fun z => InQr ε n₀ 2 (z + e4 μ)),
            ε ^ 4 * ‖dfw ε μ D.u z‖ ^ 2)) := hs
  refine hs'.trans ?_
  unfold Ksf
  nlinarith


end SFHyp

end SFLocal
end CoreLean

end
