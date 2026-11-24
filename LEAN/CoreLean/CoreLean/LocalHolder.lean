/-
`lem:local-laplacian`(ii) of BALABAN_CORE.tex (`0580551bf179`): the Hölder bound
`‖u(z) - u(z')‖ ≤ K_H(β)(‖u‖_{∞,Q_{r+1}} + H_{r+1})|z - z'|₁^β` for `z, z' ∈ Q_r`, `K_H(β) = 40C'_S(β) + 472`.

The proof is the core's: for `|z - z'|₁ > 1` the difference is at most `2S`; otherwise `u = χu` at both points, and the
three terms of `eq:local-representation` change by at most `2‖F₀‖_∞|z - z'|₁` (`eq:free-first`, second bound, along a
shortest path: `norm_sub_le_l1`) and `C'_S(β)‖F_μ‖_∞|z - z'|₁^β`, `C'_S(β)‖ψ_μu‖_∞|z - z'|₁^β` (`eq:free-first`, third
bound), with `eq:local-data` (`sup_F0_le`, `sup_Fm_le`, `sup_psiu_le`).
-/
import CoreLean.LocalData

open Finset

noncomputable section

namespace CoreLean
namespace LocalLaplacian

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- `K_H(β) = 40C'_S(β) + 472`. -/
def KH (β : ℝ) : ℝ := 40 * CS' β + 472

lemma rpow_ge_self {x β : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hβ0 : 0 < β) (hβ1 : β ≤ 1) : x ≤ x ^ β := by
  rcases eq_or_lt_of_le hx0 with h | h
  · rw [← h, Real.zero_rpow hβ0.ne']
  · have := Real.rpow_le_rpow_of_exponent_ge h hx1 hβ1
    rwa [Real.rpow_one] at this

lemma CS'_pos {β : ℝ} (hβ1 : β < 1) : 0 < CS' β := by
  unfold CS'; have : 0 < 1 - β := by linarith
  positivity

variable {ε r : ℝ} {n₀ : Fin 4 → ℤ} (D : LData V)

/-- `u = χu = G₁F₀ + Σ_μ∂^*_μG₁F_μ - Σ_μ∂_μG₁(ψ_μu)` on `Q_r`. -/
lemma u_eq_rep (hε : 0 < ε) (hε3 : ε ≤ 1 / 3) {R : ℝ} (hrR : r ≤ R - 1) (hE : Eqn D ε n₀ R) {n : Fin 4 → ℤ}
    (hn : InQr ε n₀ r n) :
    D.u n = resolvent ε (F0 D ε r n₀) n + ∑ μ, dbw ε μ (resolvent ε (Fm D ε r n₀ μ)) n -
      ∑ μ, dfw ε μ (resolvent ε (psiu D ε r n₀ μ)) n := by
  have h := congrFun (representation D hε hε3 (r := r) (R := R) (by linarith) hE) n
  rw [← h, chiu, chiL_eq_one hn, one_smul]

/-- **`lem:local-laplacian`(ii)**. -/
theorem local_holder (hε : 0 < ε) (hε3 : ε ≤ 1 / 3) {R S Hh β : ℝ} {Hg : Fin 4 → ℝ} (hr : 0 < r)
    (hrR : r ≤ R - 1) (hβ0 : 0 < β) (hβ1 : β < 1) (hE : Eqn D ε n₀ R) (hL : LocNorm D ε n₀ R)
    (B : Bounds D ε r n₀ S Hh Hg) {n n' : Fin 4 → ℤ} (hn : InQr ε n₀ r n) (hn' : InQr ε n₀ r n') :
    ‖D.u n - D.u n'‖ ≤ KH β * (S + (Hh + ∑ μ, Hg μ)) * (ε * l1 (n - n')) ^ β := by
  obtain ⟨hS0, hH0, hG0⟩ := B.nonneg D hr.le
  have hG : 0 ≤ ∑ μ, Hg μ := sum_nonneg fun μ _ => hG0 μ
  have hC := CS'_pos hβ1
  set d := ε * l1 (n - n') with hd
  have hd0 : 0 ≤ d := mul_nonneg hε.le (l1_nonneg _)
  have hdβ : 0 ≤ d ^ β := Real.rpow_nonneg hd0 β
  have hKH : 2 ≤ KH β := by unfold KH; linarith
  rcases le_or_gt d 1 with hd1 | hd1
  · -- the representation at both points
    have hm : n = n' + (n - n') := by abel
    obtain ⟨M0, hM0⟩ : ∃ M0, M0 = Hh + 9 / 2 * ∑ μ, Hg μ + 236 * S := ⟨_, rfl⟩
    have hF0 : ∀ k, ‖F0 D ε r n₀ k‖ ≤ M0 := fun k => hM0 ▸ sup_F0_le D hε hε3 hr hrR hL B k
    have hFm : ∀ μ k, ‖Fm D ε r n₀ μ k‖ ≤ Hg μ + 11 / 2 * S := fun μ k => sup_Fm_le D hε hε3 hr hrR hL B μ k
    have hFp : ∀ μ k, ‖psiu D ε r n₀ μ k‖ ≤ 9 / 2 * S := fun μ k => sup_psiu_le D hε hε3 hr B μ k
    have t1 : ‖resolvent ε (F0 D ε r n₀) n - resolvent ε (F0 D ε r n₀) n'‖ ≤ 2 * M0 * d ^ β := by
      have h := norm_sub_le_l1 hε (g := resolvent ε (F0 D ε r n₀)) (B := 2 * M0)
        (fun lam k => norm_dif_resolvent_le hε hF0 true lam k) n' (n - n')
      rw [← hm] at h
      refine h.trans ?_
      rw [← hd, mul_comm d]
      exact mul_le_mul_of_nonneg_left (rpow_ge_self hd0 hd1 hβ0 hβ1.le)
        (by have := (norm_nonneg _).trans (hF0 0); linarith)
    have t2 : ∀ μ, ‖dbw ε μ (resolvent ε (Fm D ε r n₀ μ)) n - dbw ε μ (resolvent ε (Fm D ε r n₀ μ)) n'‖ ≤
        CS' β * (Hg μ + 11 / 2 * S) * d ^ β := fun μ => by
      have h := norm_dif_resolvent_sub_le hε hβ0 hβ1 (hFm μ) false μ n' (n - n')
      rwa [← hm] at h
    have t3 : ∀ μ, ‖dfw ε μ (resolvent ε (psiu D ε r n₀ μ)) n - dfw ε μ (resolvent ε (psiu D ε r n₀ μ)) n'‖ ≤
        CS' β * (9 / 2 * S) * d ^ β := fun μ => by
      have h := norm_dif_resolvent_sub_le hε hβ0 hβ1 (hFp μ) true μ n' (n - n')
      rwa [← hm] at h
    rw [u_eq_rep D hε hε3 hrR hE hn, u_eq_rep D hε hε3 hrR hE hn']
    have e : resolvent ε (F0 D ε r n₀) n + ∑ μ, dbw ε μ (resolvent ε (Fm D ε r n₀ μ)) n -
        ∑ μ, dfw ε μ (resolvent ε (psiu D ε r n₀ μ)) n -
        (resolvent ε (F0 D ε r n₀) n' + ∑ μ, dbw ε μ (resolvent ε (Fm D ε r n₀ μ)) n' -
        ∑ μ, dfw ε μ (resolvent ε (psiu D ε r n₀ μ)) n') =
        (resolvent ε (F0 D ε r n₀) n - resolvent ε (F0 D ε r n₀) n') +
        ∑ μ, (dbw ε μ (resolvent ε (Fm D ε r n₀ μ)) n - dbw ε μ (resolvent ε (Fm D ε r n₀ μ)) n') -
        ∑ μ, (dfw ε μ (resolvent ε (psiu D ε r n₀ μ)) n - dfw ε μ (resolvent ε (psiu D ε r n₀ μ)) n') := by
      simp only [sum_sub_distrib]; abel
    rw [e]
    calc _ ≤ 2 * M0 * d ^ β + ∑ μ, CS' β * (Hg μ + 11 / 2 * S) * d ^ β + ∑ _μ : Fin 4, CS' β * (9 / 2 * S) * d ^ β :=
          (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add t1
            ((norm_sum_le _ _).trans (sum_le_sum fun μ _ => t2 μ))))
            ((norm_sum_le _ _).trans (sum_le_sum fun μ _ => t3 μ)))
      _ = (2 * Hh + 9 * ∑ μ, Hg μ + 472 * S + CS' β * (∑ μ, Hg μ + 22 * S + 18 * S)) * d ^ β := by
          simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, ← sum_mul, ← mul_sum, sum_add_distrib,
            hM0]
          ring
      _ ≤ KH β * (S + (Hh + ∑ μ, Hg μ)) * d ^ β := by
          refine mul_le_mul_of_nonneg_right ?_ hdβ
          unfold KH
          nlinarith [mul_nonneg hC.le hH0, mul_nonneg hC.le hG, mul_nonneg hC.le hS0]
  · -- far points
    have hnq : InQr ε n₀ (r + 1) n := fun μ => by have := hn μ; linarith
    have hnq' : InQr ε n₀ (r + 1) n' := fun μ => by have := hn' μ; linarith
    have h1 : 1 ≤ d ^ β := Real.one_le_rpow hd1.le hβ0.le
    calc ‖D.u n - D.u n'‖ ≤ S + S := (norm_sub_le _ _).trans (add_le_add (B.hu n hnq) (B.hu n' hnq'))
      _ ≤ KH β * (S + (Hh + ∑ μ, Hg μ)) * 1 := by nlinarith
      _ ≤ KH β * (S + (Hh + ∑ μ, Hg μ)) * d ^ β :=
          mul_le_mul_of_nonneg_left h1 (mul_nonneg (by linarith) (by positivity))

end LocalLaplacian
end CoreLean

end
