/-
`lem:local-laplacian` of BALABAN_CORE.tex (`0580551bf179`): the bounds `eq:local-data` of the data of the representation.

* `Sst u n = max_{e ∈ E}‖u(n + e)‖` (the core's `S_*`); `norm_locApp_le`: a local operator of norm at most one at `n`
  is bounded by `S_*(n)`.
* `LocNorm R`: the operators `c` and `G_μ` are local operators of norm at most one on `Q_R` (`Σ_e‖T_e(n)‖ ≤ 1` at the
  points of `Q_{R-ε}`).
* `norm_F0_le`, `norm_Fm_le`, `norm_psiu_le`: `eq:local-data`, `‖F₀‖ ≤ ‖h‖ + (9/2)Σ_μ‖g_μ‖ + 236S_*`,
  `‖F_μ‖ ≤ ‖g_μ‖ + (11/2)S_*`, `‖ψ_μu‖ ≤ (9/2)‖u‖`.
* `sup_F0_le`, `sup_Fm_le`, `sup_psiu_le`: the same with the maxima over `Q_{r+1}`, at every point of `εℤ⁴`.
-/
import CoreLean.LocalRepresentation

open Finset

noncomputable section

namespace CoreLean
namespace LocalLaplacian

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

lemma zero_mem_Eoff : (0 : Fin 4 → ℤ) ∈ Eoff := Fintype.mem_piFinset.2 fun _ => by simp

lemma Eoff_nonempty : (Eoff : Finset (Fin 4 → ℤ)).Nonempty := ⟨0, zero_mem_Eoff⟩

lemma abs_of_mem_Eoff {e : Fin 4 → ℤ} (he : e ∈ Eoff) (μ : Fin 4) : |((e μ : ℤ) : ℝ)| ≤ 1 := by
  have := Fintype.mem_piFinset.1 he μ
  rw [mem_Icc] at this
  have h : |e μ| ≤ 1 := abs_le.2 this
  exact_mod_cast h

/-- `S_*(n) = max_{e ∈ E}‖u(n + e)‖`. -/
def Sst (u : (Fin 4 → ℤ) → V) (n : Fin 4 → ℤ) : ℝ := Eoff.sup' Eoff_nonempty fun e => ‖u (n + e)‖

lemma norm_le_Sst (u : (Fin 4 → ℤ) → V) (n : Fin 4 → ℤ) {e : Fin 4 → ℤ} (he : e ∈ Eoff) :
    ‖u (n + e)‖ ≤ Sst u n :=
  le_sup' (fun e => ‖u (n + e)‖) he

lemma norm_le_Sst_self (u : (Fin 4 → ℤ) → V) (n : Fin 4 → ℤ) : ‖u n‖ ≤ Sst u n := by
  simpa using norm_le_Sst u n zero_mem_Eoff

lemma Sst_nonneg (u : (Fin 4 → ℤ) → V) (n : Fin 4 → ℤ) : 0 ≤ Sst u n :=
  (norm_nonneg _).trans (norm_le_Sst_self u n)

lemma norm_locApp_le (T : (Fin 4 → ℤ) → (Fin 4 → ℤ) → (V →L[ℝ] V)) (u : (Fin 4 → ℤ) → V) (n : Fin 4 → ℤ)
    (hT : ∑ e ∈ Eoff, ‖T n e‖ ≤ 1) : ‖locApp T u n‖ ≤ Sst u n := by
  unfold locApp
  calc ‖∑ e ∈ Eoff, T n e (u (n + e))‖ ≤ ∑ e ∈ Eoff, ‖T n e‖ * Sst u n :=
        (norm_sum_le _ _).trans (sum_le_sum fun e he =>
          ((T n e).le_opNorm _).trans (mul_le_mul_of_nonneg_left (norm_le_Sst u n he) (norm_nonneg _)))
    _ = (∑ e ∈ Eoff, ‖T n e‖) * Sst u n := by rw [sum_mul]
    _ ≤ 1 * Sst u n := mul_le_mul_of_nonneg_right hT (Sst_nonneg u n)
    _ = Sst u n := one_mul _

variable {ε r : ℝ} {n₀ : Fin 4 → ℤ} (D : LData V)

/-- `c` and `G_μ` are local operators of norm at most one on `Q_R`. -/
def LocNorm (ε : ℝ) (n₀ : Fin 4 → ℤ) (R : ℝ) : Prop :=
  (∀ n, InQr ε n₀ (R - ε) n → ∑ e ∈ Eoff, ‖D.c n e‖ ≤ 1) ∧
    ∀ μ n, InQr ε n₀ (R - ε) n → ∑ e ∈ Eoff, ‖D.G μ n e‖ ≤ 1

variable (hε : 0 < ε) (hε3 : ε ≤ 1 / 3)
include hε hε3

lemma inQ_of_lt {R : ℝ} (hr : r ≤ R - 1) {n : Fin 4 → ℤ} (h : ∀ μ, |tc ε n₀ n μ| < r + 2 / 3) :
    InQr ε n₀ (R - ε) n := fun μ => by have := h μ; linarith

lemma norm_vf_le {R : ℝ} (hr : r ≤ R - 1) (hL : LocNorm D ε n₀ R) (μ : Fin 4) {n : Fin 4 → ℤ}
    (h : ∀ μ, |tc ε n₀ n μ| < r + 2 / 3) : ‖vf D μ n‖ ≤ ‖D.g μ n‖ + Sst D.u n :=
  (norm_add_le _ _).trans (add_le_add le_rfl (norm_locApp_le _ _ _ (hL.2 μ n (inQ_of_lt hε hε3 hr h))))

/-- **`eq:local-data`** for `F₀`. -/
theorem norm_F0_le {R : ℝ} (hr : 0 < r) (hrR : r ≤ R - 1) (hL : LocNorm D ε n₀ R) (n : Fin 4 → ℤ) :
    ‖F0 D ε r n₀ n‖ ≤ ‖D.h n‖ + 9 / 2 * ∑ μ, ‖D.g μ n‖ + 236 * Sst D.u n := by
  by_cases hn : ∀ μ, |tc ε n₀ n μ| < r + 2 / 3
  · have hS := Sst_nonneg D.u n
    have hu := norm_le_Sst_self D.u n
    obtain ⟨c0, c1⟩ : 0 ≤ chiL ε r n₀ n ∧ chiL ε r n₀ n ≤ 1 := ⟨chiL_nonneg n, chiL_le_one n⟩
    have t1 : ‖chiL ε r n₀ n • D.h n‖ ≤ ‖D.h n‖ := by
      rw [norm_smul, Real.norm_of_nonneg c0]; exact mul_le_of_le_one_left (norm_nonneg _) c1
    have t2 : ‖chiL ε r n₀ n • locApp D.c D.u n‖ ≤ Sst D.u n := by
      rw [norm_smul, Real.norm_of_nonneg c0]
      exact mul_le_of_le_one_left (norm_nonneg _) c1 |>.trans (norm_locApp_le _ _ _ (hL.1 n (inQ_of_lt hε hε3 hrR hn)))
    have t3 : ‖chiL ε r n₀ n • D.u n‖ ≤ Sst D.u n := by
      rw [norm_smul, Real.norm_of_nonneg c0]; exact (mul_le_of_le_one_left (norm_nonneg _) c1).trans hu
    have t4 : ‖∑ μ, dbw ε μ (dfw ε μ (chiL ε r n₀)) n • D.u n‖ ≤ ∑ _μ : Fin 4, 54 * Sst D.u n :=
      (norm_sum_le _ _).trans (sum_le_sum fun μ _ => by
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul (abs_dbw_dfw_chiL hε hr n μ) hu (norm_nonneg _) (by norm_num))
    have t5 : ‖∑ μ, dfw ε μ (chiL ε r n₀) n • vf D μ n‖ ≤ ∑ μ, 9 / 2 * (‖D.g μ n‖ + Sst D.u n) :=
      (norm_sum_le _ _).trans (sum_le_sum fun μ _ => by
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul (abs_dfw_chiL hε hr n μ) (norm_vf_le D hε hε3 hrR hL μ hn) (norm_nonneg _) (by norm_num))
    unfold F0
    calc _ ≤ ‖chiL ε r n₀ n • D.h n‖ + ‖chiL ε r n₀ n • locApp D.c D.u n‖ + ‖chiL ε r n₀ n • D.u n‖ +
          ‖∑ μ, dbw ε μ (dfw ε μ (chiL ε r n₀)) n • D.u n‖ + ‖∑ μ, dfw ε μ (chiL ε r n₀) n • vf D μ n‖ := by
          refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add ?_ le_rfl)) le_rfl)
          exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ ‖D.h n‖ + Sst D.u n + Sst D.u n + ∑ _μ : Fin 4, 54 * Sst D.u n +
          ∑ μ, 9 / 2 * (‖D.g μ n‖ + Sst D.u n) := by gcongr
      _ = ‖D.h n‖ + 9 / 2 * ∑ μ, ‖D.g μ n‖ + 236 * Sst D.u n := by
          simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_add, sum_add_distrib, ← mul_sum]
          ring
  · rw [F0_supp D hε hε3 n hn, norm_zero]
    have := Sst_nonneg D.u n
    positivity

/-- **`eq:local-data`** for `F_μ`. -/
theorem norm_Fm_le {R : ℝ} (hr : 0 < r) (hrR : r ≤ R - 1) (hL : LocNorm D ε n₀ R) (μ : Fin 4) (n : Fin 4 → ℤ) :
    ‖Fm D ε r n₀ μ n‖ ≤ ‖D.g μ n‖ + 11 / 2 * Sst D.u n := by
  by_cases hn : ∀ μ, |tc ε n₀ n μ| < r + 2 / 3
  · have hu := norm_le_Sst_self D.u n
    unfold Fm
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_of_nonneg (chiL_nonneg _)]
    have a1 := mul_le_mul (abs_dfw_chiL (n₀ := n₀) hε hr n μ) hu (norm_nonneg _) (by norm_num)
    have a2 := mul_le_mul (chiL_le_one (ε := ε) (r := r) (n₀ := n₀) (n + e4 μ)) (norm_vf_le D hε hε3 hrR hL μ hn)
      (norm_nonneg _) zero_le_one
    linarith
  · rw [Fm_supp D hε hε3 μ n hn, norm_zero]
    have := Sst_nonneg D.u n
    positivity

omit hε3 [CompleteSpace V] in
/-- **`eq:local-data`** for `ψ_μu`. -/
theorem norm_psiu_le (hr : 0 < r) (μ : Fin 4) (n : Fin 4 → ℤ) : ‖psiu D ε r n₀ μ n‖ ≤ 9 / 2 * ‖D.u n‖ := by
  unfold psiu
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (abs_dfw_chiL hε hr _ μ) (norm_nonneg _)

/-! ### The maxima over `Q_{r+1}` -/

omit hε3 in
lemma tc_add_off {e : Fin 4 → ℤ} (he : e ∈ Eoff) (n : Fin 4 → ℤ) (ν : Fin 4) :
    |tc ε n₀ (n + e) ν| ≤ |tc ε n₀ n ν| + ε := by
  have h : tc ε n₀ (n + e) ν = tc ε n₀ n ν + ε * (e ν : ℝ) := by unfold tc; simp only [Pi.add_apply]; push_cast; ring
  rw [h]
  refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
  rw [abs_mul, abs_of_pos hε]
  exact mul_le_of_le_one_right hε.le (abs_of_mem_Eoff he ν)

lemma Sst_le {S : ℝ} (hS : ∀ n, InQr ε n₀ (r + 1) n → ‖D.u n‖ ≤ S) {n : Fin 4 → ℤ}
    (hn : ∀ μ, |tc ε n₀ n μ| < r + 2 / 3) : Sst D.u n ≤ S :=
  sup'_le _ _ fun e he => hS _ fun ν => by
    have := tc_add_off (n₀ := n₀) hε he n ν; have := hn ν; linarith

/-- The hypotheses on the data on `Q_{r+1}`: `‖u‖ ≤ S`, `‖h‖ ≤ Hh`, `‖g_μ‖ ≤ Hg_μ`. -/
structure Bounds (D : LData V) (ε r : ℝ) (n₀ : Fin 4 → ℤ) (S Hh : ℝ) (Hg : Fin 4 → ℝ) : Prop where
  hu : ∀ n, InQr ε n₀ (r + 1) n → ‖D.u n‖ ≤ S
  hh : ∀ n, InQr ε n₀ (r + 1) n → ‖D.h n‖ ≤ Hh
  hg : ∀ μ n, InQr ε n₀ (r + 1) n → ‖D.g μ n‖ ≤ Hg μ

omit hε hε3 in
lemma Bounds.nonneg {S Hh : ℝ} {Hg : Fin 4 → ℝ} (B : Bounds D ε r n₀ S Hh Hg) (hr : 0 ≤ r) :
    0 ≤ S ∧ 0 ≤ Hh ∧ ∀ μ, 0 ≤ Hg μ := by
  have h0 : InQr ε n₀ (r + 1) n₀ := fun μ => by simp [tc]; linarith
  exact ⟨(norm_nonneg _).trans (B.hu _ h0), (norm_nonneg _).trans (B.hh _ h0),
    fun μ => (norm_nonneg _).trans (B.hg μ _ h0)⟩

theorem sup_F0_le {R S Hh : ℝ} {Hg : Fin 4 → ℝ} (hr : 0 < r) (hrR : r ≤ R - 1) (hL : LocNorm D ε n₀ R)
    (B : Bounds D ε r n₀ S Hh Hg) (n : Fin 4 → ℤ) :
    ‖F0 D ε r n₀ n‖ ≤ Hh + 9 / 2 * ∑ μ, Hg μ + 236 * S := by
  obtain ⟨hS0, hH0, hG0⟩ := B.nonneg D hr.le
  by_cases hn : ∀ μ, |tc ε n₀ n μ| < r + 2 / 3
  · have hq : InQr ε n₀ (r + 1) n := fun μ => by have := hn μ; linarith
    refine (norm_F0_le D hε hε3 hr hrR hL n).trans ?_
    have := Sst_le D hε hε3 B.hu hn
    have := B.hh n hq
    have : ∑ μ, ‖D.g μ n‖ ≤ ∑ μ, Hg μ := sum_le_sum fun μ _ => B.hg μ n hq
    linarith
  · rw [F0_supp D hε hε3 n hn, norm_zero]
    have := sum_nonneg fun μ (_ : μ ∈ univ) => hG0 μ
    positivity

theorem sup_Fm_le {R S Hh : ℝ} {Hg : Fin 4 → ℝ} (hr : 0 < r) (hrR : r ≤ R - 1) (hL : LocNorm D ε n₀ R)
    (B : Bounds D ε r n₀ S Hh Hg) (μ : Fin 4) (n : Fin 4 → ℤ) :
    ‖Fm D ε r n₀ μ n‖ ≤ Hg μ + 11 / 2 * S := by
  obtain ⟨hS0, hH0, hG0⟩ := B.nonneg D hr.le
  by_cases hn : ∀ μ, |tc ε n₀ n μ| < r + 2 / 3
  · have hq : InQr ε n₀ (r + 1) n := fun μ => by have := hn μ; linarith
    refine (norm_Fm_le D hε hε3 hr hrR hL μ n).trans ?_
    have := Sst_le D hε hε3 B.hu hn
    have := B.hg μ n hq
    linarith
  · rw [Fm_supp D hε hε3 μ n hn, norm_zero]
    have := hG0 μ
    positivity

theorem sup_psiu_le {S Hh : ℝ} {Hg : Fin 4 → ℝ} (hr : 0 < r) (B : Bounds D ε r n₀ S Hh Hg) (μ : Fin 4)
    (n : Fin 4 → ℤ) : ‖psiu D ε r n₀ μ n‖ ≤ 9 / 2 * S := by
  obtain ⟨hS0, -, -⟩ := B.nonneg D hr.le
  by_cases hn : ∀ μ, |tc ε n₀ n μ| < r + 1
  · exact (norm_psiu_le D hε hr μ n).trans (mul_le_mul_of_nonneg_left (B.hu n fun ν => (hn ν).le) (by norm_num))
  · rw [psiu_supp D hε hε3 μ n hn, norm_zero]; positivity

end LocalLaplacian
end CoreLean

end
