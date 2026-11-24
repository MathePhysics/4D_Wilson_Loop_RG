/-
`lem:local-laplacian`(i) of BALABAN_CORE.tex (`0580551bf179`).

* `local_Lq`: for `2 ≤ p < q < ∞`, `1/p - 1/q = 1/6`,
  `‖u‖_{q,Q_r} ≤ ‖h‖_{p,Q_{r+1}} + 10Σ_μ‖g_μ‖_{p,Q_{r+1}} + 2¹²‖u‖_{p,Q_{r+1}}`;
  `local_Linf`: the same for `(p, q) = (6, ∞)`, at every point of `Q_r`.
* `local_Linf_chain`: for `R ≥ 4`, `‖u‖_{∞,Q_1} ≤ 2³⁶(‖u‖_{2,Q_4} + H_4)`.

The proof is the core's: on `Q_r`, `u = G₁F₀ + Σ_μ∂^*_μG₁F_μ - Σ_μ∂_μG₁(ψ_μu)` (`u_eq_rep`); each term is bounded by a
convolution with the kernel `k` of `G₁` or `ε⁻¹dKer` of its differences (`LocalConvolution`), whose `L^{6/5}` norms are at
most `1` and `5` (`LocalKernelNorms`); Young's inequality and `eq:local-data` with `‖S_*‖_p ≤ 9‖u‖_p` give
`‖u‖_q ≤ ‖h‖_p + (19/2)Σ_μ‖g_μ‖_p + (2124 + 990 + 90)‖u‖_p`.
-/
import CoreLean.LocalLp

open Finset

noncomputable section

namespace CoreLean
namespace LocalLaplacian

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
variable {ε r : ℝ} {n₀ : Fin 4 → ℤ} (D : LData V)

/-- The kernel of `∂^*_μG₁` at `w`, `ε⁻¹dKer(w - e_μ)`. -/
def K1 (ε : ℝ) (μ : Fin 4) (w : Fin 4 → ℤ) : ℝ := ε⁻¹ * dKer ε μ (w - e4 μ)

/-- The set of its arguments. -/
def Z1 (ε r : ℝ) (n₀ : Fin 4 → ℤ) (μ : Fin 4) : Finset (Fin 4 → ℤ) :=
  (diffSet ((QF ε n₀ r).image fun n => n - e4 μ) (QF ε n₀ (r + 1))).map (addRightEmbedding (e4 μ))

variable (hε : 0 < ε) (hε3 : ε ≤ 1 / 3)
include hε hε3

omit [CompleteSpace V] in
lemma kernel_k (Z : Finset (Fin 4 → ℤ)) :
    (∑ z ∈ Z, resKernel ε z ^ (6 / 5 : ℝ)) ^ (5 / 6 : ℝ) ≤ 1 * ε ^ (2 / 3 : ℝ) := by
  rw [one_mul]; exact resKernel_l65 hε Z

omit [CompleteSpace V] in
lemma eps_inv_mul (Z : Finset (Fin 4 → ℤ)) (μ : Fin 4) :
    (∑ z ∈ Z, (ε⁻¹ * dKer ε μ z) ^ (6 / 5 : ℝ)) ^ (5 / 6 : ℝ) ≤ 5 * ε ^ (2 / 3 : ℝ) := by
  rw [l65_smul Z (inv_nonneg.2 hε.le) _ fun z _ => dKer_nonneg μ z]
  calc ε⁻¹ * (∑ z ∈ Z, dKer ε μ z ^ (6 / 5 : ℝ)) ^ (5 / 6 : ℝ) ≤ ε⁻¹ * (5 * ε ^ (5 / 3 : ℝ)) :=
        mul_le_mul_of_nonneg_left (dKer_l65 hε Z μ) (inv_nonneg.2 hε.le)
    _ = 5 * ε ^ (2 / 3 : ℝ) := by
        rw [show (5 / 3 : ℝ) = 1 + 2 / 3 by norm_num, Real.rpow_add hε, Real.rpow_one]
        field_simp

omit [CompleteSpace V] in
lemma kernel_K1 (μ : Fin 4) :
    (∑ w ∈ Z1 ε r n₀ μ, K1 ε μ w ^ (6 / 5 : ℝ)) ^ (5 / 6 : ℝ) ≤ 5 * ε ^ (2 / 3 : ℝ) := by
  unfold Z1 K1
  rw [sum_map]
  simp only [addRightEmbedding_apply, add_sub_cancel_right]
  exact eps_inv_mul hε hε3 _ μ

lemma supp_B {f : (Fin 4 → ℤ) → V} {ρ : ℝ} (hρ : ρ ≤ r + 1) (hf : ∀ n, (¬ ∀ μ, |tc ε n₀ n μ| < ρ) → f n = 0) :
    ∀ m, f m ≠ 0 → m ∈ QF ε n₀ (r + 1) := fun m hm => by
  by_contra h
  apply hm; apply hf
  intro hall
  exact h ((mem_QF hε).2 fun μ => ((hall μ).le.trans hρ))

/-- The pointwise bound by the three convolutions. -/
theorem norm_u_le_conv {R : ℝ} (hrR : r ≤ R - 1) (hE : Eqn D ε n₀ R) {n : Fin 4 → ℤ} (hn : n ∈ QF ε n₀ r) :
    ‖D.u n‖ ≤ ∑ z ∈ diffSet (QF ε n₀ r) (QF ε n₀ (r + 1)), resKernel ε z * ‖F0 D ε r n₀ (n - z)‖ +
      ∑ μ, ∑ w ∈ Z1 ε r n₀ μ, K1 ε μ w * ‖Fm D ε r n₀ μ (n - w)‖ +
      ∑ μ, ∑ z ∈ diffSet (QF ε n₀ r) (QF ε n₀ (r + 1)), ε⁻¹ * dKer ε μ z * ‖psiu D ε r n₀ μ (n - z)‖ := by
  obtain ⟨M0, hM0⟩ := bounded_of_supp hε (F0_supp D (r := r) (n₀ := n₀) hε hε3)
  have hMm : ∀ μ, ∃ M, ∀ n, ‖Fm D ε r n₀ μ n‖ ≤ M := fun μ => bounded_of_supp hε (Fm_supp D (r := r) (n₀ := n₀) hε hε3 μ)
  have hMp : ∀ μ, ∃ M, ∀ n, ‖psiu D ε r n₀ μ n‖ ≤ M := fun μ => bounded_of_supp hε (psiu_supp D (r := r) (n₀ := n₀) hε hε3 μ)
  choose Mm hMm using hMm
  choose Mp hMp using hMp
  have s0 := supp_B (r := r) hε hε3 (by linarith) (F0_supp D (r := r) (n₀ := n₀) hε hε3)
  have sm : ∀ μ, _ := fun μ => supp_B (r := r) hε hε3 (by linarith) (Fm_supp D (r := r) (n₀ := n₀) hε hε3 μ)
  have sp : ∀ μ, _ := fun μ => supp_B (r := r) hε hε3 le_rfl (psiu_supp D (r := r) (n₀ := n₀) hε hε3 μ)
  rw [u_eq_rep D hε hε3 hrR hE ((mem_QF hε).1 hn)]
  refine (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
    (norm_resolvent_le_conv hM0 s0 hn) ((norm_sum_le _ _).trans (sum_le_sum fun μ _ => ?_))))
    ((norm_sum_le _ _).trans (sum_le_sum fun μ _ => ?_)))
  · rw [dbw_eq_neg_dfw, norm_neg]
    have hn1 : n - e4 μ ∈ (QF ε n₀ r).image fun n => n - e4 μ := mem_image_of_mem _ hn
    refine (norm_dfw_resolvent_le_conv hε (hMm μ) (sm μ) μ hn1).trans (le_of_eq ?_)
    unfold Z1 K1
    rw [sum_map, mul_sum]
    refine sum_congr rfl fun z _ => ?_
    simp only [addRightEmbedding_apply, add_sub_cancel_right]
    rw [show n - e4 μ - z = n - (z + e4 μ) by abel]; ring
  · refine (norm_dfw_resolvent_le_conv hε (hMp μ) (sp μ) μ hn).trans (le_of_eq ?_)
    rw [mul_sum]; exact sum_congr rfl fun z _ => by ring

/-- The `L^p` norms of the data. -/
theorem data_pn {R p : ℝ} (hr : 0 < r) (hrR : r ≤ R - 1) (hL : LocNorm D ε n₀ R) (hp : 2 ≤ p) :
    pn ε (QF ε n₀ (r + 1)) p (fun n => ‖F0 D ε r n₀ n‖) ≤ pn ε (QF ε n₀ (r + 1)) p (fun n => ‖D.h n‖) +
        9 / 2 * ∑ μ, pn ε (QF ε n₀ (r + 1)) p (fun n => ‖D.g μ n‖) + 2124 * pn ε (QF ε n₀ (r + 1)) p (fun n => ‖D.u n‖) ∧
      (∀ μ, pn ε (QF ε n₀ (r + 1)) p (fun n => ‖Fm D ε r n₀ μ n‖) ≤ pn ε (QF ε n₀ (r + 1)) p (fun n => ‖D.g μ n‖) +
        99 / 2 * pn ε (QF ε n₀ (r + 1)) p (fun n => ‖D.u n‖)) ∧
      (∀ μ, pn ε (QF ε n₀ (r + 1)) p (fun n => ‖psiu D ε r n₀ μ n‖) ≤
        9 / 2 * pn ε (QF ε n₀ (r + 1)) p (fun n => ‖D.u n‖)) := by
  have hp0 : 0 < p := by linarith
  have hp1 : 1 ≤ p := by linarith
  set B := QF ε n₀ (r + 1)
  set B' := QF ε n₀ (r + 2 / 3)
  have hBB : B' ⊆ B := fun n hn => (mem_QF hε).2 fun μ => (((mem_QF hε).1 hn) μ).trans (by linarith)
  have hoff : ∀ {f : (Fin 4 → ℤ) → V}, (∀ n, (¬ ∀ μ, |tc ε n₀ n μ| < r + 2 / 3) → f n = 0) →
      ∀ n ∈ B, n ∉ B' → ‖f n‖ = 0 := fun hf n _ hn => by
    rw [hf n fun hall => hn ((mem_QF hε).2 fun μ => (hall μ).le), norm_zero]
  have nn : ∀ (f : (Fin 4 → ℤ) → V) (T : Finset (Fin 4 → ℤ)), ∀ n ∈ T, 0 ≤ ‖f n‖ := fun f T n _ => norm_nonneg _
  have hSst := pn_Sst (n₀ := n₀) hε hε3 hp (r := r) D.u
  have hg' : ∀ μ, pn ε B' p (fun n => ‖D.g μ n‖) ≤ pn ε B p (fun n => ‖D.g μ n‖) :=
    fun μ => pn_subset hp0 hBB (nn _ _)
  have hh' : pn ε B' p (fun n => ‖D.h n‖) ≤ pn ε B p (fun n => ‖D.h n‖) := pn_subset hp0 hBB (nn _ _)
  have hPu := pn_nonneg (ε := ε) (T := B) (p := p) (nn D.u B)
  refine ⟨?_, fun μ => ?_, fun μ => ?_⟩
  · rw [pn_supp hp0 hBB (hoff (F0_supp D (r := r) (n₀ := n₀) hε hε3))]
    have hS0 : ∀ n ∈ B', 0 ≤ Sst D.u n := fun n _ => Sst_nonneg D.u n
    calc pn ε B' p (fun n => ‖F0 D ε r n₀ n‖)
        ≤ pn ε B' p (fun n => (‖D.h n‖ + 9 / 2 * ∑ μ, ‖D.g μ n‖) + 236 * Sst D.u n) :=
          pn_mono hp0 (nn _ _) fun n _ => by
            have := norm_F0_le D hε hε3 hr hrR hL n; linarith
      _ ≤ (pn ε B' p (fun n => ‖D.h n‖) + 9 / 2 * ∑ μ, pn ε B' p (fun n => ‖D.g μ n‖)) +
            236 * pn ε B' p (Sst D.u) := by
          refine (pn_add hε hp1 (fun n _ => by positivity) (fun n hn => by have := hS0 n hn; positivity)).trans
            (add_le_add ((pn_add hε hp1 (nn _ _) (fun n _ => by positivity)).trans (add_le_add le_rfl ?_)) ?_)
          · rw [pn_smul hp0 (by norm_num) (fun n _ => sum_nonneg fun μ _ => norm_nonneg _)]
            exact mul_le_mul_of_nonneg_left (pn_sum4 hε hp1 _ fun μ => nn _ _) (by norm_num)
          · rw [pn_smul hp0 (by norm_num) hS0]
      _ ≤ (pn ε B p (fun n => ‖D.h n‖) + 9 / 2 * ∑ μ, pn ε B p (fun n => ‖D.g μ n‖)) +
            236 * (9 * pn ε B p (fun n => ‖D.u n‖)) := by
          gcongr
          · exact hg' _
      _ = _ := by ring
  · rw [pn_supp hp0 hBB (hoff (Fm_supp D (r := r) (n₀ := n₀) hε hε3 μ))]
    calc pn ε B' p (fun n => ‖Fm D ε r n₀ μ n‖) ≤ pn ε B' p (fun n => ‖D.g μ n‖ + 11 / 2 * Sst D.u n) :=
          pn_mono hp0 (nn _ _) fun n _ => norm_Fm_le D hε hε3 hr hrR hL μ n
      _ ≤ pn ε B' p (fun n => ‖D.g μ n‖) + 11 / 2 * pn ε B' p (Sst D.u) := by
          refine (pn_add hε hp1 (nn _ _) (fun n _ => by have := Sst_nonneg D.u n; positivity)).trans
            (add_le_add le_rfl (le_of_eq ?_))
          rw [pn_smul hp0 (by norm_num) fun n _ => Sst_nonneg D.u n]
      _ ≤ pn ε B p (fun n => ‖D.g μ n‖) + 11 / 2 * (9 * pn ε B p (fun n => ‖D.u n‖)) := by gcongr; exact hg' μ
      _ = _ := by ring
  · calc pn ε B p (fun n => ‖psiu D ε r n₀ μ n‖) ≤ pn ε B p (fun n => 9 / 2 * ‖D.u n‖) :=
          pn_mono hp0 (nn _ _) fun n _ => norm_psiu_le D hε hr μ n
      _ = _ := pn_smul hp0 (by norm_num) (nn _ _)

/-- **`lem:local-laplacian`(i)**, `q < ∞`. -/
theorem local_Lq {R p q : ℝ} (hr : 0 < r) (hrR : r ≤ R - 1) (hE : Eqn D ε n₀ R) (hL : LocNorm D ε n₀ R)
    (hp : 2 ≤ p) (hpq : p < q) (hrel : 1 / p - 1 / q = 1 / 6) :
    pn ε (QF ε n₀ r) q (fun n => ‖D.u n‖) ≤ pn ε (QF ε n₀ (r + 1)) p (fun n => ‖D.h n‖) +
      10 * ∑ μ, pn ε (QF ε n₀ (r + 1)) p (fun n => ‖D.g μ n‖) +
      2 ^ 12 * pn ε (QF ε n₀ (r + 1)) p (fun n => ‖D.u n‖) := by
  have hq0 : 0 < q := by linarith
  have hq1 : 1 ≤ q := by linarith
  set A := QF ε n₀ r
  set B := QF ε n₀ (r + 1)
  set Z := diffSet A B
  set w0 : (Fin 4 → ℤ) → ℝ := fun n => ∑ z ∈ Z, resKernel ε z * ‖F0 D ε r n₀ (n - z)‖
  set w1 : Fin 4 → (Fin 4 → ℤ) → ℝ := fun μ n => ∑ w ∈ Z1 ε r n₀ μ, K1 ε μ w * ‖Fm D ε r n₀ μ (n - w)‖
  set w2 : Fin 4 → (Fin 4 → ℤ) → ℝ := fun μ n => ∑ z ∈ Z, ε⁻¹ * dKer ε μ z * ‖psiu D ε r n₀ μ (n - z)‖
  have hK1 : ∀ μ w, 0 ≤ K1 ε μ w := fun μ w => mul_nonneg (inv_nonneg.2 hε.le) (dKer_nonneg μ _)
  have hK2 : ∀ μ z, 0 ≤ ε⁻¹ * dKer ε μ z := fun μ z => mul_nonneg (inv_nonneg.2 hε.le) (dKer_nonneg μ _)
  have hw0 : ∀ n, 0 ≤ w0 n := fun n => sum_nonneg fun z _ => mul_nonneg (resKernel_nonneg z) (norm_nonneg _)
  have hw1 : ∀ μ n, 0 ≤ w1 μ n := fun μ n => sum_nonneg fun w _ => mul_nonneg (hK1 μ w) (norm_nonneg _)
  have hw2 : ∀ μ n, 0 ≤ w2 μ n := fun μ n => sum_nonneg fun z _ => mul_nonneg (hK2 μ z) (norm_nonneg _)
  have s0 := supp_B (r := r) hε hε3 (by linarith) (F0_supp D (r := r) (n₀ := n₀) hε hε3)
  have nsupp : ∀ (f : (Fin 4 → ℤ) → V), (∀ m, f m ≠ 0 → m ∈ B) → ∀ m, ‖f m‖ ≠ 0 → m ∈ B :=
    fun f hf m hm => hf m fun h => hm (by rw [h, norm_zero])
  -- the three Young bounds
  have y0 := conv_Lq hε A Z B (fun z => resKernel_nonneg z) (fun m => norm_nonneg (F0 D ε r n₀ m))
    (nsupp _ s0) hw0 (fun n _ => le_rfl) (kernel_k hε hε3 Z) hp hpq hrel
  have y1 : ∀ μ, pn ε A q (w1 μ) ≤ 5 * pn ε B p (fun n => ‖Fm D ε r n₀ μ n‖) := fun μ =>
    conv_Lq hε A (Z1 ε r n₀ μ) B (hK1 μ) (fun m => norm_nonneg _)
      (nsupp _ (supp_B (r := r) hε hε3 (by linarith) (Fm_supp D (r := r) (n₀ := n₀) hε hε3 μ))) (hw1 μ) (fun n _ => le_rfl)
      (kernel_K1 hε hε3 μ) hp hpq hrel
  have y2 : ∀ μ, pn ε A q (w2 μ) ≤ 5 * pn ε B p (fun n => ‖psiu D ε r n₀ μ n‖) := fun μ =>
    conv_Lq hε A Z B (hK2 μ) (fun m => norm_nonneg _)
      (nsupp _ (supp_B (r := r) hε hε3 le_rfl (psiu_supp D (r := r) (n₀ := n₀) hε hε3 μ))) (hw2 μ) (fun n _ => le_rfl)
      (eps_inv_mul hε hε3 Z μ) hp hpq hrel
  obtain ⟨d0, d1, d2⟩ := data_pn D hε hε3 hr hrR hL hp
  -- Minkowski over `A`
  have hmink : pn ε A q (fun n => ‖D.u n‖) ≤ pn ε A q w0 + ∑ μ, pn ε A q (w1 μ) + ∑ μ, pn ε A q (w2 μ) := by
    refine (pn_mono hq0 (fun n _ => norm_nonneg _) fun n hn => norm_u_le_conv D hε hε3 hrR hE hn).trans ?_
    refine (pn_add hε hq1 (fun n _ => add_nonneg (hw0 n) (sum_nonneg fun μ _ => hw1 μ n))
      (fun n _ => sum_nonneg fun μ _ => hw2 μ n)).trans (add_le_add ((pn_add hε hq1 (fun n _ => hw0 n)
      (fun n _ => sum_nonneg fun μ _ => hw1 μ n)).trans (add_le_add le_rfl
      (pn_sum4 hε hq1 _ fun μ n _ => hw1 μ n))) (pn_sum4 hε hq1 _ fun μ n _ => hw2 μ n))
  have hPg : ∀ μ, 0 ≤ pn ε B p (fun n => ‖D.g μ n‖) := fun μ => pn_nonneg fun n _ => norm_nonneg _
  have hPu : 0 ≤ pn ε B p (fun n => ‖D.u n‖) := pn_nonneg fun n _ => norm_nonneg _
  have hPh : 0 ≤ pn ε B p (fun n => ‖D.h n‖) := pn_nonneg fun n _ => norm_nonneg _
  calc pn ε A q (fun n => ‖D.u n‖) ≤ pn ε A q w0 + ∑ μ, pn ε A q (w1 μ) + ∑ μ, pn ε A q (w2 μ) := hmink
    _ ≤ 1 * (pn ε B p (fun n => ‖D.h n‖) + 9 / 2 * ∑ μ, pn ε B p (fun n => ‖D.g μ n‖) +
          2124 * pn ε B p (fun n => ‖D.u n‖)) +
        ∑ μ, 5 * (pn ε B p (fun n => ‖D.g μ n‖) + 99 / 2 * pn ε B p (fun n => ‖D.u n‖)) +
        ∑ _μ : Fin 4, 5 * (9 / 2 * pn ε B p (fun n => ‖D.u n‖)) := by
        refine add_le_add (add_le_add (y0.trans (mul_le_mul_of_nonneg_left d0 (by norm_num)))
          (sum_le_sum fun μ _ => (y1 μ).trans (mul_le_mul_of_nonneg_left (d1 μ) (by norm_num))))
          (sum_le_sum fun μ _ => (y2 μ).trans (mul_le_mul_of_nonneg_left (d2 μ) (by norm_num)))
    _ = pn ε B p (fun n => ‖D.h n‖) + 19 / 2 * ∑ μ, pn ε B p (fun n => ‖D.g μ n‖) +
          3204 * pn ε B p (fun n => ‖D.u n‖) := by
        simp only [mul_add, sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_sum]
        ring
    _ ≤ _ := by
        have := sum_nonneg fun μ (_ : μ ∈ univ) => hPg μ
        nlinarith

/-- **`lem:local-laplacian`(i)**, `(p, q) = (6, ∞)`. -/
theorem local_Linf {R : ℝ} (hr : 0 < r) (hrR : r ≤ R - 1) (hE : Eqn D ε n₀ R) (hL : LocNorm D ε n₀ R)
    {n : Fin 4 → ℤ} (hn : InQr ε n₀ r n) :
    ‖D.u n‖ ≤ pn ε (QF ε n₀ (r + 1)) 6 (fun n => ‖D.h n‖) +
      10 * ∑ μ, pn ε (QF ε n₀ (r + 1)) 6 (fun n => ‖D.g μ n‖) +
      2 ^ 12 * pn ε (QF ε n₀ (r + 1)) 6 (fun n => ‖D.u n‖) := by
  set A := QF ε n₀ r
  set B := QF ε n₀ (r + 1)
  set Z := diffSet A B
  have hnA : n ∈ A := (mem_QF hε).2 hn
  have hK1 : ∀ μ w, 0 ≤ K1 ε μ w := fun μ w => mul_nonneg (inv_nonneg.2 hε.le) (dKer_nonneg μ _)
  have hK2 : ∀ μ z, 0 ≤ ε⁻¹ * dKer ε μ z := fun μ z => mul_nonneg (inv_nonneg.2 hε.le) (dKer_nonneg μ _)
  have nsupp : ∀ (f : (Fin 4 → ℤ) → V), (∀ m, f m ≠ 0 → m ∈ B) → ∀ m, ‖f m‖ ≠ 0 → m ∈ B :=
    fun f hf m hm => hf m fun h => hm (by rw [h, norm_zero])
  have y0 := conv_Linf hε Z B (fun z => resKernel_nonneg z) (fun m => norm_nonneg (F0 D ε r n₀ m))
    (nsupp _ (supp_B (r := r) hε hε3 (by linarith) (F0_supp D (r := r) (n₀ := n₀) hε hε3))) (kernel_k hε hε3 Z) n
  have y1 : ∀ μ, ∑ w ∈ Z1 ε r n₀ μ, K1 ε μ w * ‖Fm D ε r n₀ μ (n - w)‖ ≤
      5 * pn ε B 6 (fun m => ‖Fm D ε r n₀ μ m‖) := fun μ =>
    conv_Linf hε (Z1 ε r n₀ μ) B (hK1 μ) (fun m => norm_nonneg _)
      (nsupp _ (supp_B (r := r) hε hε3 (by linarith) (Fm_supp D (r := r) (n₀ := n₀) hε hε3 μ))) (kernel_K1 hε hε3 μ) n
  have y2 : ∀ μ, ∑ z ∈ Z, ε⁻¹ * dKer ε μ z * ‖psiu D ε r n₀ μ (n - z)‖ ≤
      5 * pn ε B 6 (fun m => ‖psiu D ε r n₀ μ m‖) := fun μ =>
    conv_Linf hε Z B (hK2 μ) (fun m => norm_nonneg _)
      (nsupp _ (supp_B (r := r) hε hε3 le_rfl (psiu_supp D (r := r) (n₀ := n₀) hε hε3 μ))) (eps_inv_mul hε hε3 Z μ) n
  obtain ⟨d0, d1, d2⟩ := data_pn D hε hε3 hr hrR hL (p := 6) (by norm_num)
  have hPg : ∀ μ, 0 ≤ pn ε B 6 (fun n => ‖D.g μ n‖) := fun μ => pn_nonneg fun n _ => norm_nonneg _
  have hPu : 0 ≤ pn ε B 6 (fun n => ‖D.u n‖) := pn_nonneg fun n _ => norm_nonneg _
  calc ‖D.u n‖ ≤ _ := norm_u_le_conv D hε hε3 hrR hE hnA
    _ ≤ 1 * (pn ε B 6 (fun n => ‖D.h n‖) + 9 / 2 * ∑ μ, pn ε B 6 (fun n => ‖D.g μ n‖) +
          2124 * pn ε B 6 (fun n => ‖D.u n‖)) +
        ∑ μ, 5 * (pn ε B 6 (fun n => ‖D.g μ n‖) + 99 / 2 * pn ε B 6 (fun n => ‖D.u n‖)) +
        ∑ _μ : Fin 4, 5 * (9 / 2 * pn ε B 6 (fun n => ‖D.u n‖)) := by
        refine add_le_add (add_le_add (y0.trans (mul_le_mul_of_nonneg_left d0 (by norm_num)))
          (sum_le_sum fun μ _ => (y1 μ).trans (mul_le_mul_of_nonneg_left (d1 μ) (by norm_num))))
          (sum_le_sum fun μ _ => (y2 μ).trans (mul_le_mul_of_nonneg_left (d2 μ) (by norm_num)))
    _ = pn ε B 6 (fun n => ‖D.h n‖) + 19 / 2 * ∑ μ, pn ε B 6 (fun n => ‖D.g μ n‖) +
          3204 * pn ε B 6 (fun n => ‖D.u n‖) := by
        simp only [mul_add, sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_sum]
        ring
    _ ≤ _ := by
        have := sum_nonneg fun μ (_ : μ ∈ univ) => hPg μ
        nlinarith

omit [CompleteSpace V] in
lemma rpow_bounds : (5 : ℝ) ^ (4 / 6 : ℝ) ≤ 3 ∧ (7 : ℝ) ^ (4 / 3 : ℝ) ≤ 14 ∧ (9 : ℝ) ^ (4 / 2 : ℝ) = 81 := by
  refine ⟨?_, ?_, ?_⟩
  · refine le_of_pow_le_pow_left₀ (n := 3) (by norm_num) (by norm_num) ?_
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
  · refine le_of_pow_le_pow_left₀ (n := 3) (by norm_num) (by norm_num) ?_
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
  · rw [show (4 / 2 : ℝ) = (2 : ℕ) by norm_num, Real.rpow_natCast]; norm_num

/-- **`lem:local-laplacian`(i)**, the second bound: `‖u‖_{∞,Q_1} ≤ 2³⁶(‖u‖_{2,Q_4} + H_4)` for `R ≥ 4`. -/
theorem local_Linf_chain {R Hh : ℝ} {Hg : Fin 4 → ℝ} (hR : 4 ≤ R) (hE : Eqn D ε n₀ R) (hL : LocNorm D ε n₀ R)
    (hh : ∀ n, InQr ε n₀ 4 n → ‖D.h n‖ ≤ Hh) (hg : ∀ μ n, InQr ε n₀ 4 n → ‖D.g μ n‖ ≤ Hg μ)
    {n : Fin 4 → ℤ} (hn : InQr ε n₀ 1 n) :
    ‖D.u n‖ ≤ 2 ^ 36 * (pn ε (QF ε n₀ 4) 2 (fun n => ‖D.u n‖) + (Hh + ∑ μ, Hg μ)) := by
  have hε1 : ε ≤ 1 := by linarith
  have h0 : InQr ε n₀ 4 n₀ := fun μ => by simp [tc]
  have hH0 : 0 ≤ Hh := (norm_nonneg _).trans (hh _ h0)
  have hG0 : ∀ μ, 0 ≤ Hg μ := fun μ => (norm_nonneg _).trans (hg μ _ h0)
  have hG : 0 ≤ ∑ μ, Hg μ := sum_nonneg fun μ _ => hG0 μ
  have a := local_Linf D hε hε3 (r := 1) (R := R) one_pos (by linarith) hE hL hn
  have b := local_Lq D hε hε3 (r := 2) (R := R) (p := 3) (q := 6) (by norm_num) (by linarith) hE hL (by norm_num)
    (by norm_num) (by norm_num)
  have c := local_Lq D hε hε3 (r := 3) (R := R) (p := 2) (q := 3) (by norm_num) (by linarith) hE hL (by norm_num)
    (by norm_num) (by norm_num)
  rw [show (1 : ℝ) + 1 = 2 by norm_num] at a
  rw [show (2 : ℝ) + 1 = 3 by norm_num] at b
  rw [show (3 : ℝ) + 1 = 4 by norm_num] at c
  obtain ⟨r5, r7, r9⟩ := rpow_bounds hε hε3
  have hq : ∀ s : ℝ, s ≤ 4 → ∀ m ∈ QF ε n₀ s, InQr ε n₀ 4 m := fun s hs m hm μ =>
    (((mem_QF hε).1 hm) μ).trans hs
  -- the volume bounds
  have vh : ∀ (s p : ℝ), 0 ≤ s → s ≤ 4 → 0 < p →
      pn ε (QF ε n₀ s) p (fun n => ‖D.h n‖) ≤ (2 * s + 1) ^ (4 / p) * Hh := fun s p hs hs4 hp =>
    pn_le_vol hε hε1 hs hp (fun m _ => norm_nonneg _) fun m hm => hh m (hq s hs4 m hm)
  have vg : ∀ (s p : ℝ), 0 ≤ s → s ≤ 4 → 0 < p → ∀ μ,
      pn ε (QF ε n₀ s) p (fun n => ‖D.g μ n‖) ≤ (2 * s + 1) ^ (4 / p) * Hg μ := fun s p hs hs4 hp μ =>
    pn_le_vol hε hε1 hs hp (fun m _ => norm_nonneg _) fun m hm => hg μ m (hq s hs4 m hm)
  have h2 : pn ε (QF ε n₀ 2) 6 (fun n => ‖D.h n‖) ≤ 3 * Hh := (vh 2 6 (by norm_num) (by norm_num) (by norm_num)).trans
    (by rw [show (2 : ℝ) * 2 + 1 = 5 by norm_num]; exact mul_le_mul_of_nonneg_right r5 hH0)
  have g2 : ∑ μ, pn ε (QF ε n₀ 2) 6 (fun n => ‖D.g μ n‖) ≤ 3 * ∑ μ, Hg μ := by
    rw [mul_sum]; exact sum_le_sum fun μ _ => (vg 2 6 (by norm_num) (by norm_num) (by norm_num) μ).trans
      (by rw [show (2 : ℝ) * 2 + 1 = 5 by norm_num]; exact mul_le_mul_of_nonneg_right r5 (hG0 μ))
  have h3 : pn ε (QF ε n₀ 3) 3 (fun n => ‖D.h n‖) ≤ 14 * Hh := (vh 3 3 (by norm_num) (by norm_num) (by norm_num)).trans
    (by rw [show (2 : ℝ) * 3 + 1 = 7 by norm_num]; exact mul_le_mul_of_nonneg_right r7 hH0)
  have g3 : ∑ μ, pn ε (QF ε n₀ 3) 3 (fun n => ‖D.g μ n‖) ≤ 14 * ∑ μ, Hg μ := by
    rw [mul_sum]; exact sum_le_sum fun μ _ => (vg 3 3 (by norm_num) (by norm_num) (by norm_num) μ).trans
      (by rw [show (2 : ℝ) * 3 + 1 = 7 by norm_num]; exact mul_le_mul_of_nonneg_right r7 (hG0 μ))
  have h4 : pn ε (QF ε n₀ 4) 2 (fun n => ‖D.h n‖) ≤ 81 * Hh := (vh 4 2 (by norm_num) le_rfl (by norm_num)).trans
    (by rw [show (2 : ℝ) * 4 + 1 = 9 by norm_num, r9])
  have g4 : ∑ μ, pn ε (QF ε n₀ 4) 2 (fun n => ‖D.g μ n‖) ≤ 81 * ∑ μ, Hg μ := by
    rw [mul_sum]; exact sum_le_sum fun μ _ => (vg 4 2 (by norm_num) le_rfl (by norm_num) μ).trans
      (by rw [show (2 : ℝ) * 4 + 1 = 9 by norm_num, r9])
  have hP : 0 ≤ pn ε (QF ε n₀ 4) 2 (fun n => ‖D.u n‖) := pn_nonneg fun n _ => norm_nonneg _
  have hP3 : 0 ≤ pn ε (QF ε n₀ 3) 3 (fun n => ‖D.u n‖) := pn_nonneg fun n _ => norm_nonneg _
  have hP2 : 0 ≤ pn ε (QF ε n₀ 2) 6 (fun n => ‖D.u n‖) := pn_nonneg fun n _ => norm_nonneg _
  nlinarith

end LocalLaplacian
end CoreLean

end
