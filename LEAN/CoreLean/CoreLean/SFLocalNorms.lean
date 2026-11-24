/-
`lem:sf-local` of BALABAN_CORE.tex (`4252790331fd`): the norms of the local operators of the rescaled equation.

* `FieldHyp`: in the coordinates of the layer, `‖Ã_μ(n)‖ ≤ α₁L` and `‖Ã_μ(n + e_ν) - Ã_μ(n)‖ ≤ εα₁L²` on `Q_{8+2L}`
  (the core's `‖A'(b)‖ ≤ α₁La^{-1}`, `‖∂_νA'_μ‖ ≤ α₁L²a^{-2}`, multiplied by `a` and `a²`), `64L²α₁ ≤ 1`, `L ≥ 3`, and
  `ε ≤ 1/3`.
* `norm_Cop_le`: `‖𝒞(n)‖ ≤ 32α₁L² + 144α₁²L²` at the points of `Q_8`;
  `sum_norm_c_le`: `Σ_e‖c_e(n)‖ ≤ 1`, `sum_norm_Gc_le`: `Σ_e‖𝒢'_{μ,e}(n)‖ ≤ 1`, `lip_Gc`: `𝒢'_μ` is Lipschitz on `Q_8`
  with the constant `1`, when `Σ_e‖Z_e‖ ≤ 1/4` (the core: `32α₁L² + 256α₁²L² + 1/4 ≤ 1`, `16α₁L ≤ 1`, `16α₁L² ≤ 1`).
* `inQr_trans`: the box of the radius `ρ` about a point of `Q_{ρ'}` lies in `Q_{ρ+ρ'}`; `locNorm_of`, `gLip_of`: the
  hypotheses of `lem:local-laplacian` on the boxes about the points of `Q_8` which lie in `Q_8`.
-/
import CoreLean.SFLocalEq

open Finset Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean
namespace SFLocal

open LocalLaplacian InteriorSchauder

variable {N m : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ

/-- The hypotheses on the field in the coordinates of the layer. -/
structure FieldHyp (ε : ℝ) (n₀ : Fin 4 → ℤ) (A : Fin 4 → (Fin 4 → ℤ) → Mat) (L α₁ : ℝ) : Prop where
  hε : 0 < ε
  hε3 : ε ≤ 1 / 3
  hL : 3 ≤ L
  hα0 : 0 ≤ α₁
  hα : 64 * L ^ 2 * α₁ ≤ 1
  hA : ∀ μ n, InQr ε n₀ (8 + 2 * L) n → ‖A μ n‖ ≤ α₁ * L
  hdA : ∀ μ ν n, InQr ε n₀ (8 + 2 * L) n → InQr ε n₀ (8 + 2 * L) (n + e4 ν) →
    ‖A μ (n + e4 ν) - A μ n‖ ≤ ε * (α₁ * L ^ 2)

variable {ε : ℝ} {n₀ : Fin 4 → ℤ} {A : Fin 4 → (Fin 4 → ℤ) → Matrix (Fin N) (Fin N) ℂ} {L α₁ : ℝ}

lemma inQr_trans {ρ ρ' : ℝ} {z n : Fin 4 → ℤ} (hn : InQr ε z ρ n) (hz : InQr ε n₀ ρ' z) : InQr ε n₀ (ρ + ρ') n :=
  fun μ => by
    have e : tc ε n₀ n μ = tc ε z n μ + tc ε n₀ z μ := by unfold tc; push_cast; ring
    rw [e]; exact (abs_add_le _ _).trans (add_le_add (hn μ) (hz μ))

lemma inQr_mono {ρ ρ' : ℝ} (h : ρ ≤ ρ') {n : Fin 4 → ℤ} (hn : InQr ε n₀ ρ n) : InQr ε n₀ ρ' n :=
  fun μ => (hn μ).trans h

namespace FieldHyp

variable (H : FieldHyp ε n₀ A L α₁)
include H

lemma αL_le : α₁ * L ≤ 1 / 192 := by
  have h1 := H.hL; have h2 := H.hα; have h3 := H.hα0
  have : α₁ * L * (64 * L) ≤ 1 := by nlinarith
  have h4 : (192 : ℝ) ≤ 64 * L := by linarith
  nlinarith

lemma αL2_le : α₁ * L ^ 2 ≤ 1 / 64 := by have := H.hα; nlinarith

lemma small {μ : Fin 4} {n : Fin 4 → ℤ} (hn : InQr ε n₀ (8 + 2 * L) n) : ε * ‖A μ n‖ ≤ 1 / 32 := by
  have h1 := H.hA μ n hn
  have h2 := H.αL_le
  have hε := H.hε; have hε3 := H.hε3
  calc ε * ‖A μ n‖ ≤ 1 * (α₁ * L) := mul_le_mul (by linarith) h1 (norm_nonneg _) (by norm_num)
    _ ≤ 1 / 32 := by linarith

lemma inQ_big {n : Fin 4 → ℤ} (hn : InQr ε n₀ 8 n) {e : Fin 4 → ℤ} (he : e ∈ Eoff) :
    InQr ε n₀ (8 + 2 * L) (n + e) :=
  inQr_mono (by linarith [H.hL]) (inQ_add_off H.hε H.hε3 hn he)

lemma inQ_big0 {n : Fin 4 → ℤ} (hn : InQr ε n₀ 8 n) : InQr ε n₀ (8 + 2 * L) n := by
  simpa using H.inQ_big hn zero_mem_Eoff

lemma inQ_sub {n : Fin 4 → ℤ} (hn : InQr ε n₀ 8 n) (μ : Fin 4) : InQr ε n₀ (8 + 2 * L) (n - e4 μ) := by
  rw [sub_eq_add_neg]; exact H.inQ_big hn (neg_mem_Eoff (e4_mem μ))

lemma norm_Kf {μ : Fin 4} {n : Fin 4 → ℤ} (hn : InQr ε n₀ (8 + 2 * L) n) :
    ‖(Kf ε A μ n : VS N m →L[ℝ] VS N m)‖ ≤ 6 * (α₁ * L) :=
  (norm_Kf_le H.hε (H.small hn)).trans (by linarith [H.hA μ n hn])

lemma norm_Kb {μ : Fin 4} {n : Fin 4 → ℤ} (hn : InQr ε n₀ (8 + 2 * L) (n - e4 μ)) :
    ‖(Kb ε A μ n : VS N m →L[ℝ] VS N m)‖ ≤ 6 * (α₁ * L) :=
  (norm_Kb_le H.hε (H.small hn)).trans (by linarith [H.hA μ _ hn])

/-- `‖𝒞(n)‖ ≤ 32α₁L² + 144α₁²L²` at the points of `Q_8`. -/
theorem norm_Cop_le {n : Fin 4 → ℤ} (hn : InQr ε n₀ 8 n) :
    ‖(Cop ε A n : VS N m →L[ℝ] VS N m)‖ ≤ 32 * (α₁ * L ^ 2) + 144 * (α₁ * L) ^ 2 := by
  have hε := H.hε
  have hterm : ∀ μ, ‖(ε⁻¹ • (Kb ε A μ n - Kb ε A μ (n + e4 μ)) + (Kb ε A μ n).comp (Kf ε A μ (n - e4 μ)) :
      VS N m →L[ℝ] VS N m)‖ ≤ 8 * (α₁ * L ^ 2) + 36 * (α₁ * L) ^ 2 := fun μ => by
    have hm := H.inQ_sub hn μ
    have h0 := H.inQ_big0 hn
    have hd : ‖(Kb ε A μ n - Kb ε A μ (n + e4 μ) : VS N m →L[ℝ] VS N m)‖ ≤ 8 * (ε * (α₁ * L ^ 2)) := by
      refine (norm_Kb_sub_le hε (H.small hm) (by rw [add_sub_cancel_right]; exact H.small h0)).trans ?_
      rw [add_sub_cancel_right, norm_sub_rev]
      have := H.hdA μ μ (n - e4 μ) hm (by rw [sub_add_cancel]; exact h0)
      rw [sub_add_cancel] at this
      linarith
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hε.le)]
      calc ε⁻¹ * ‖(Kb ε A μ n - Kb ε A μ (n + e4 μ) : VS N m →L[ℝ] VS N m)‖ ≤ ε⁻¹ * (8 * (ε * (α₁ * L ^ 2))) :=
            mul_le_mul_of_nonneg_left hd (inv_nonneg.2 hε.le)
        _ = 8 * (α₁ * L ^ 2) := by field_simp
    · refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
      have h1 := H.norm_Kb (N := N) (m := m) (μ := μ) hm
      have h2 := H.norm_Kf (N := N) (m := m) (μ := μ) hm
      calc _ ≤ 6 * (α₁ * L) * (6 * (α₁ * L)) := mul_le_mul h1 h2 (norm_nonneg _) (by
            have := H.hα0; have := H.hL; positivity)
        _ = 36 * (α₁ * L) ^ 2 := by ring
  unfold Cop
  refine (norm_sum_le _ _).trans ((sum_le_sum fun μ _ => hterm μ).trans (le_of_eq ?_))
  rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; push_cast; ring

lemma Cop_small {n : Fin 4 → ℤ} (hn : InQr ε n₀ 8 n) : ‖(Cop ε A n : VS N m →L[ℝ] VS N m)‖ ≤ 3 / 4 := by
  refine (H.norm_Cop_le hn).trans ?_
  have h1 := H.αL2_le; have h2 := H.αL_le; have h0 : 0 ≤ α₁ * L := by have := H.hα0; have := H.hL; positivity
  nlinarith

omit H in
lemma norm_ite_zero (e : Fin 4 → ℤ) (C : VS N m →L[ℝ] VS N m) :
    ‖(if e = 0 then C else 0 : VS N m →L[ℝ] VS N m)‖ = if e = 0 then ‖C‖ else 0 := by
  split_ifs <;> simp

/-- `Σ_e‖c_e(n)‖ ≤ 1` at the points of `Q_8`. -/
theorem sum_norm_c_le (D : SFData N m) {n : Fin 4 → ℤ} (hn : InQr ε n₀ 8 n) (hZ : ∑ e ∈ Eoff, ‖D.Z n e‖ ≤ 1 / 4) :
    ∑ e ∈ Eoff, ‖(toLData ε A D).c n e‖ ≤ 1 := by
  have hc : ∀ e, (toLData ε A D).c n e = D.Z n e - (if e = 0 then Cop ε A n else 0) := fun e => rfl
  calc ∑ e ∈ Eoff, ‖(toLData ε A D).c n e‖
      ≤ ∑ e ∈ Eoff, (‖D.Z n e‖ + if e = 0 then ‖(Cop ε A n : VS N m →L[ℝ] VS N m)‖ else 0) :=
        sum_le_sum fun e _ => by rw [hc, ← norm_ite_zero]; exact norm_sub_le _ _
    _ = ∑ e ∈ Eoff, ‖D.Z n e‖ + ‖(Cop ε A n : VS N m →L[ℝ] VS N m)‖ := by
        rw [sum_add_distrib, sum_ite_eq' Eoff (0 : Fin 4 → ℤ), if_pos zero_mem_Eoff]
    _ ≤ 1 / 4 + 3 / 4 := add_le_add hZ (H.Cop_small hn)
    _ = 1 := by norm_num

omit H in
lemma sum_Gc (F : (Fin 4 → ℤ) → ℝ) (μ : Fin 4) (hF : ∀ e, e ≠ e4 μ → e ≠ 0 → F e = 0) :
    ∑ e ∈ Eoff, F e = F (e4 μ) + F 0 :=
  sum_eq_add (e4 μ) 0 (e4_ne_zero μ) (fun e _ he => hF e he.1 he.2)
    (fun h => absurd (e4_mem μ) h) (fun h => absurd zero_mem_Eoff h)

/-- `Σ_e‖𝒢'_{μ,e}(n)‖ ≤ 1` at the points of `Q_8`. -/
theorem sum_norm_Gc_le (μ : Fin 4) {n : Fin 4 → ℤ} (hn : InQr ε n₀ 8 n) :
    ∑ e ∈ Eoff, ‖(Gc ε A μ n e : VS N m →L[ℝ] VS N m)‖ ≤ 1 := by
  rw [sum_Gc _ μ fun e h1 h2 => by simp [Gc, h1, h2]]
  simp only [Gc, (e4_ne_zero μ).symm, ↓reduceIte, norm_neg]
  have h0 := H.inQ_big0 hn
  have a1 := H.norm_Kf (N := N) (m := m) (μ := μ) h0
  have a2 := H.norm_Kb (N := N) (m := m) (μ := μ) (n := n + e4 μ) (by rwa [add_sub_cancel_right])
  have := H.αL_le
  linarith

/-- `𝒢'_μ` is Lipschitz on `Q_8` with the constant `1`. -/
theorem lip_Gc (μ : Fin 4) {n n' : Fin 4 → ℤ} (hn : InQr ε n₀ 8 n) (hn' : InQr ε n₀ 8 n') :
    ∑ e ∈ Eoff, ‖(Gc ε A μ n e - Gc ε A μ n' e : VS N m →L[ℝ] VS N m)‖ ≤ ε * l1 (n - n') := by
  rw [sum_Gc _ μ fun e h1 h2 => by simp [Gc, h1, h2]]
  simp only [Gc, (e4_ne_zero μ).symm, ↓reduceIte]
  have h0 := H.inQ_big0 hn
  have h0' := H.inQ_big0 hn'
  have hlip : ‖A μ n - A μ n'‖ ≤ ε * (α₁ * L ^ 2) * l1 (n - n') :=
    lip_box H.hε (g := A μ) (fun k ν hk hk' => H.hdA μ ν k hk hk') h0' h0
  have a1 := norm_Kf_sub_le (N := N) (m := m) H.hε (H.small h0') (H.small h0) (μ := μ)
  have a2 := norm_Kb_sub_le (N := N) (m := m) H.hε (μ := μ) (n := n + e4 μ) (n' := n' + e4 μ)
    (by rw [add_sub_cancel_right]; exact H.small h0) (by rw [add_sub_cancel_right]; exact H.small h0')
  rw [add_sub_cancel_right, add_sub_cancel_right] at a2
  rw [show (-Kf ε A μ n - -Kf ε A μ n' : VS N m →L[ℝ] VS N m) = -(Kf ε A μ n - Kf ε A μ n') by abel, norm_neg]
  have hn1 : ‖A μ n' - A μ n‖ = ‖A μ n - A μ n'‖ := norm_sub_rev _ _
  rw [hn1] at a1
  rw [norm_sub_rev] at a1
  have h16 : 16 * (α₁ * L ^ 2) ≤ 1 := by have := H.hα; nlinarith
  have hl : 0 ≤ ε * l1 (n - n') := mul_nonneg H.hε.le (l1_nonneg _)
  have hk : 16 * (ε * (α₁ * L ^ 2) * l1 (n - n')) ≤ ε * l1 (n - n') := by
    have := mul_le_mul_of_nonneg_right h16 hl; nlinarith
  linarith

/-- The hypotheses on the local operators of `lem:local-laplacian` on a box which lies in `Q_8`. -/
theorem locNorm_of (D : SFData N m) {z : Fin 4 → ℤ} {R : ℝ} (hsub : ∀ k, InQr ε z (R - ε) k → InQr ε n₀ 8 k)
    (hZ : ∀ k, InQr ε n₀ 8 k → ∑ e ∈ Eoff, ‖D.Z k e‖ ≤ 1 / 4) : LocNorm (toLData ε A D) ε z R :=
  ⟨fun k hk => H.sum_norm_c_le D (hsub k hk) (hZ k (hsub k hk)), fun μ k hk => H.sum_norm_Gc_le μ (hsub k hk)⟩

theorem gLip_of (D : SFData N m) {z : Fin 4 → ℤ} {ρ : ℝ} (hsub : ∀ k, InQr ε z ρ k → InQr ε n₀ 8 k) :
    GLip (toLData ε A D) ε z ρ :=
  fun μ k k' hk hk' => H.lip_Gc μ (hsub k hk) (hsub k' hk')


end FieldHyp

end SFLocal
end CoreLean

end
