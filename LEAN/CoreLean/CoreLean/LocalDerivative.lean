/-
`lem:local-laplacian`(iii) of BALABAN_CORE.tex (`0580551bf179`): the first differences of `u` and their modulus,
`‖∂_νu(z)‖ ≤ K_D(β)(S + Υ + H + Γ)` and `‖∂_νu(z) - ∂_νu(z')‖ ≤ K_D(β)(S + Υ + H + Γ)|z - z'|₁^β`,
`K_D(β) = 918C_S(β) + 236C'_S(β) + 472`.

* `local_product`: `eq:local-product`, the modulus of `φf` from the bound and the Lipschitz constant of `φ` and the
  local modulus of `f` on `Q_ρ`.
* `holder_locApp`: the modulus of `G_μu` on `Q_{r+2/3}`, `(Υ + S)|z₁ - z₂|₁^β`, from the Lipschitz condition.
* `holder_Fm`, `holder_psiu`: the moduli of `F_μ` and of `ψ_μu` at all points, `(117/2)Υ + (243/2)S + (9/2)Γ + 9Hg_μ`
  and `54(Υ + 2S)`, which add up over `μ` to the core's `450Υ + 918S + 18Γ + 9Σ_μHg_μ`.
* `local_derivative`, `local_derivative_holder`: the two bounds of (iii), by `∂_ν` of `eq:local-representation`,
  `eq:free-first` and `eq:free-second`.
-/
import CoreLean.LocalHolder

open Finset

noncomputable section

namespace CoreLean
namespace LocalLaplacian

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- `K_D(β) = 918C_S(β) + 236C'_S(β) + 472`. -/
def KD (β : ℝ) : ℝ := 918 * CS β + 236 * CS' β + 472

lemma CS_pos {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) : 0 < CS β := by
  unfold CS; have : 0 < 1 - β := by linarith
  have := c0_pos; have := zero_lt_one.trans_le one_le_m1
  positivity

variable {ε r : ℝ} {n₀ : Fin 4 → ℤ}

lemma l1_sub_comm (n n' : Fin 4 → ℤ) : l1 (n - n') = l1 (n' - n) := by rw [← l1_neg, neg_sub]

/-- **`eq:local-product`**. -/
theorem local_product (hε : 0 < ε) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {φ : (Fin 4 → ℤ) → ℝ}
    {f : (Fin 4 → ℤ) → V} {ρ A Sf T : ℝ} (hA : 0 ≤ A) (hSf : 0 ≤ Sf) (hT : 0 ≤ T)
    (hφs : ∀ n, ¬ InQr ε n₀ ρ n → φ n = 0) (hφb : ∀ n, |φ n| ≤ A)
    (hφl : ∀ n n', |φ n - φ n'| ≤ A * (ε * l1 (n - n')))
    (hfb : ∀ n, InQr ε n₀ ρ n → ‖f n‖ ≤ Sf)
    (hfh : ∀ n n', InQr ε n₀ ρ n → InQr ε n₀ ρ n' → ε * l1 (n - n') ≤ 1 → ‖f n - f n'‖ ≤ T * (ε * l1 (n - n')) ^ β)
    (n m : Fin 4 → ℤ) :
    ‖φ (n + m) • f (n + m) - φ n • f n‖ ≤ A * (T + 2 * Sf) * (ε * l1 m) ^ β := by
  have hm : n + m - n = m := by abel
  set d := ε * l1 m with hd
  have hd0 : 0 ≤ d := mul_nonneg hε.le (l1_nonneg _)
  have hdβ : 0 ≤ d ^ β := Real.rpow_nonneg hd0 β
  have hpt : ∀ k, ‖φ k • f k‖ ≤ A * Sf := fun k => by
    by_cases hk : InQr ε n₀ ρ k
    · rw [norm_smul, Real.norm_eq_abs]; exact mul_le_mul (hφb k) (hfb k hk) (norm_nonneg _) hA
    · rw [hφs k hk, zero_smul, norm_zero]; positivity
  rcases le_or_gt d 1 with hd1 | hd1
  · have hdd := rpow_ge_self hd0 hd1 hβ0 hβ1.le
    have hl : |φ (n + m) - φ n| ≤ A * d := by have := hφl (n + m) n; rwa [hm] at this
    by_cases h1 : InQr ε n₀ ρ (n + m) <;> by_cases h2 : InQr ε n₀ ρ n
    · have e : φ (n + m) • f (n + m) - φ n • f n = φ (n + m) • (f (n + m) - f n) + (φ (n + m) - φ n) • f n := by
        rw [smul_sub, sub_smul]; abel
      rw [e]
      have hf := hfh (n + m) n h1 h2 (by rw [hm]; exact hd1)
      rw [hm] at hf
      calc _ ≤ A * (T * d ^ β) + A * d * Sf := by
            refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
            · rw [norm_smul, Real.norm_eq_abs]; exact mul_le_mul (hφb _) hf (norm_nonneg _) hA
            · rw [norm_smul, Real.norm_eq_abs]; exact mul_le_mul hl (hfb n h2) (norm_nonneg _) (by positivity)
        _ ≤ A * (T + 2 * Sf) * d ^ β := by nlinarith [mul_le_mul_of_nonneg_left hdd (mul_nonneg hA hSf), mul_nonneg (mul_nonneg hA hSf) hdβ, mul_nonneg (mul_nonneg hA hT) hdβ]
    · rw [hφs n h2, zero_smul, sub_zero]
      have e : φ (n + m) = φ (n + m) - φ n := by rw [hφs n h2, sub_zero]
      rw [e, norm_smul, Real.norm_eq_abs]
      calc |φ (n + m) - φ n| * ‖f (n + m)‖ ≤ A * d * Sf := mul_le_mul hl (hfb _ h1) (norm_nonneg _) (by positivity)
        _ ≤ A * (T + 2 * Sf) * d ^ β := by nlinarith [mul_le_mul_of_nonneg_left hdd (mul_nonneg hA hSf), mul_nonneg (mul_nonneg hA hSf) hdβ, mul_nonneg (mul_nonneg hA hT) hdβ]
    · rw [hφs (n + m) h1, zero_smul, zero_sub, norm_neg]
      have e : φ n = φ n - φ (n + m) := by rw [hφs (n + m) h1, sub_zero]
      rw [e, norm_smul, Real.norm_eq_abs, abs_sub_comm]
      calc |φ (n + m) - φ n| * ‖f n‖ ≤ A * d * Sf := mul_le_mul hl (hfb _ h2) (norm_nonneg _) (by positivity)
        _ ≤ A * (T + 2 * Sf) * d ^ β := by nlinarith [mul_le_mul_of_nonneg_left hdd (mul_nonneg hA hSf), mul_nonneg (mul_nonneg hA hSf) hdβ, mul_nonneg (mul_nonneg hA hT) hdβ]
    · simp only [hφs n h2, hφs (n + m) h1, zero_smul, sub_zero, norm_zero]; positivity
  · have h1 : 1 ≤ d ^ β := Real.one_le_rpow hd1.le hβ0.le
    calc _ ≤ A * Sf + A * Sf := (norm_sub_le _ _).trans (add_le_add (hpt _) (hpt _))
      _ ≤ A * (T + 2 * Sf) * 1 := by nlinarith [mul_nonneg hA hT]
      _ ≤ A * (T + 2 * Sf) * d ^ β := mul_le_mul_of_nonneg_left h1 (by positivity)

variable (D : LData V)

/-- The operators `G_μ` are Lipschitz on `Q_ρ`. -/
def GLip (ε : ℝ) (n₀ : Fin 4 → ℤ) (ρ : ℝ) : Prop :=
  ∀ μ n n', InQr ε n₀ ρ n → InQr ε n₀ ρ n' → ∑ e ∈ Eoff, ‖D.G μ n e - D.G μ n' e‖ ≤ ε * l1 (n - n')

/-- The hypotheses of (iii) on the moduli of `u` and `g_μ` on `Q_{r+1}`. -/
structure Moduli (D : LData V) (ε r : ℝ) (n₀ : Fin 4 → ℤ) (β Υ Γ : ℝ) : Prop where
  hu : ∀ n n', InQr ε n₀ (r + 1) n → InQr ε n₀ (r + 1) n' → ε * l1 (n - n') ≤ 1 →
    ‖D.u n - D.u n'‖ ≤ Υ * (ε * l1 (n - n')) ^ β
  hg : ∀ μ n n', InQr ε n₀ (r + 1) n → InQr ε n₀ (r + 1) n' → ε * l1 (n - n') ≤ 1 →
    ‖D.g μ n - D.g μ n'‖ ≤ Γ * (ε * l1 (n - n')) ^ β

variable (hε : 0 < ε) (hε3 : ε ≤ 1 / 3)
include hε hε3

lemma inQ_add_off {ρ : ℝ} {n : Fin 4 → ℤ} (hn : InQr ε n₀ ρ n) {e : Fin 4 → ℤ} (he : e ∈ Eoff) :
    InQr ε n₀ (ρ + 1 / 3) (n + e) := fun ν => by
  have := tc_add_off (n₀ := n₀) hε he n ν; have := hn ν; linarith

omit hε3 in
lemma inQ_mono {ρ ρ' : ℝ} (h : ρ ≤ ρ') {n : Fin 4 → ℤ} (hn : InQr ε n₀ ρ n) : InQr ε n₀ ρ' n :=
  fun ν => (hn ν).trans h

/-- The modulus of `G_μu` on `Q_{r+2/3}`. -/
lemma holder_locApp {R S β Υ : ℝ} (hrR : r ≤ R - 1) (hβ0 : 0 < β) (hβ1 : β < 1) (hL : LocNorm D ε n₀ R)
    (hGL : GLip D ε n₀ (r + 1)) (hS : ∀ n, InQr ε n₀ (r + 1) n → ‖D.u n‖ ≤ S)
    (hΥ : ∀ n n', InQr ε n₀ (r + 1) n → InQr ε n₀ (r + 1) n' → ε * l1 (n - n') ≤ 1 →
      ‖D.u n - D.u n'‖ ≤ Υ * (ε * l1 (n - n')) ^ β) (hS0 : 0 ≤ S) (μ : Fin 4)
    {n n' : Fin 4 → ℤ} (hn : InQr ε n₀ (r + 2 / 3) n) (hn' : InQr ε n₀ (r + 2 / 3) n')
    (hd : ε * l1 (n - n') ≤ 1) :
    ‖locApp (D.G μ) D.u n - locApp (D.G μ) D.u n'‖ ≤ (Υ + S) * (ε * l1 (n - n')) ^ β := by
  set d := ε * l1 (n - n')
  have hd0 : 0 ≤ d := mul_nonneg hε.le (l1_nonneg _)
  have hdd := rpow_ge_self hd0 hd hβ0 hβ1.le
  have hq : ∀ k e, InQr ε n₀ (r + 2 / 3) k → e ∈ Eoff → InQr ε n₀ (r + 1) (k + e) := fun k e hk he =>
    inQ_mono hε (by linarith) (inQ_add_off hε hε3 hk he)
  have hnR : InQr ε n₀ (R - ε) n := inQ_mono hε (by linarith) hn
  have hdiff : ∀ e, (n + e) - (n' + e) = n - n' := fun e => by abel
  have e1 : locApp (D.G μ) D.u n - locApp (D.G μ) D.u n' =
      ∑ e ∈ Eoff, (D.G μ n e (D.u (n + e) - D.u (n' + e)) + (D.G μ n e - D.G μ n' e) (D.u (n' + e))) := by
    unfold locApp; rw [← sum_sub_distrib]
    refine sum_congr rfl fun e _ => ?_
    rw [map_sub, ContinuousLinearMap.sub_apply]; abel
  rw [e1]
  have hΥ' : ∀ e ∈ Eoff, ‖D.u (n + e) - D.u (n' + e)‖ ≤ Υ * d ^ β := fun e he => by
    have := hΥ _ _ (hq n e hn he) (hq n' e hn' he) (by rw [hdiff]; exact hd)
    rwa [hdiff] at this
  calc ‖∑ e ∈ Eoff, (D.G μ n e (D.u (n + e) - D.u (n' + e)) + (D.G μ n e - D.G μ n' e) (D.u (n' + e)))‖
      ≤ ∑ e ∈ Eoff, (‖D.G μ n e‖ * (Υ * d ^ β) + ‖D.G μ n e - D.G μ n' e‖ * S) :=
        (norm_sum_le _ _).trans (sum_le_sum fun e he => (norm_add_le _ _).trans (add_le_add
          (((D.G μ n e).le_opNorm _).trans (mul_le_mul_of_nonneg_left (hΥ' e he) (norm_nonneg _)))
          (((D.G μ n e - D.G μ n' e).le_opNorm _).trans
            (mul_le_mul_of_nonneg_left (hS _ (hq n' e hn' he)) (norm_nonneg _)))))
    _ = (∑ e ∈ Eoff, ‖D.G μ n e‖) * (Υ * d ^ β) + (∑ e ∈ Eoff, ‖D.G μ n e - D.G μ n' e‖) * S := by
        rw [sum_add_distrib, sum_mul, sum_mul]
    _ ≤ 1 * (Υ * d ^ β) + d * S := by
        have hΥ0 : 0 ≤ Υ * d ^ β := (norm_nonneg _).trans (hΥ' 0 zero_mem_Eoff)
        exact add_le_add (mul_le_mul_of_nonneg_right (hL.2 μ n hnR) hΥ0)
          (mul_le_mul_of_nonneg_right (hGL μ n n' (inQ_mono hε (by linarith) hn) (inQ_mono hε (by linarith) hn')) hS0)
    _ ≤ (Υ + S) * d ^ β := by nlinarith [mul_le_mul_of_nonneg_left hdd hS0]

omit hε3 in
lemma inQ_of_ne_dfw {n : Fin 4 → ℤ} {μ : Fin 4} (hε3 : ε ≤ 1 / 3) (h : dfw ε μ (chiL ε r n₀) n ≠ 0) :
    InQr ε n₀ (r + 2 / 3) n := fun ν => (dfw_chiL_supp hε hε3 h ν).le

/-- The modulus of `F_μ` at all points. -/
theorem holder_Fm {R S Hh β Υ Γ : ℝ} {Hg : Fin 4 → ℝ} (hr : 0 < r) (hrR : r ≤ R - 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hL : LocNorm D ε n₀ R) (hGL : GLip D ε n₀ (r + 1)) (B : Bounds D ε r n₀ S Hh Hg)
    (Mo : Moduli D ε r n₀ β Υ Γ) (hΥ0 : 0 ≤ Υ) (hΓ0 : 0 ≤ Γ) (μ : Fin 4) (n m : Fin 4 → ℤ) :
    ‖Fm D ε r n₀ μ (n + m) - Fm D ε r n₀ μ n‖ ≤
      (117 / 2 * Υ + 243 / 2 * S + 9 / 2 * Γ + 9 * Hg μ) * (ε * l1 m) ^ β := by
  obtain ⟨hS0, -, hG0⟩ := B.nonneg D hr.le
  have hq23 : ∀ k, InQr ε n₀ (r + 2 / 3) k → InQr ε n₀ (r + 1) k := fun k hk => inQ_mono hε (by linarith) hk
  -- the three products
  have p1 := local_product (n₀ := n₀) hε hβ0 hβ1 (φ := dfw ε μ (chiL ε r n₀)) (f := D.u) (ρ := r + 2 / 3)
    (A := 54) (Sf := S) (T := Υ) (by norm_num) hS0 hΥ0
    (fun k hk => by by_contra h; exact hk (inQ_of_ne_dfw hε hε3 h))
    (fun k => (abs_dfw_chiL hε hr k μ).trans (by norm_num))
    (fun k k' => dfw_chiL_lip hε hr k k' μ)
    (fun k hk => B.hu k (hq23 k hk))
    (fun k k' hk hk' hd => Mo.hu k k' (hq23 k hk) (hq23 k' hk') hd) n m
  have hchi_s : ∀ k, ¬ InQr ε n₀ (r + 2 / 3) k → chiL ε r n₀ (k + e4 μ) = 0 := fun k hk => by
    by_contra h; exact hk fun ν => (chiL_add_supp hε hε3 h ν).le
  have hchi_b : ∀ k, |chiL ε r n₀ (k + e4 μ)| ≤ 9 / 2 := fun k => by
    rw [abs_of_nonneg (chiL_nonneg _)]; linarith [chiL_le_one (ε := ε) (r := r) (n₀ := n₀) (k + e4 μ)]
  have hchi_l : ∀ k k', |chiL ε r n₀ (k + e4 μ) - chiL ε r n₀ (k' + e4 μ)| ≤ 9 / 2 * (ε * l1 (k - k')) := fun k k' => by
    have := chiL_lip (ε := ε) (n₀ := n₀) hr (k + e4 μ) (k' + e4 μ)
    rwa [show k + e4 μ - (k' + e4 μ) = k - k' by abel, abs_of_pos hε] at this
  have p2 := local_product (n₀ := n₀) hε hβ0 hβ1 (φ := fun k => chiL ε r n₀ (k + e4 μ)) (f := D.g μ)
    (ρ := r + 2 / 3) (A := 9 / 2) (Sf := Hg μ) (T := Γ) (by norm_num) (hG0 μ) hΓ0 hchi_s hchi_b hchi_l
    (fun k hk => B.hg μ k (hq23 k hk))
    (fun k k' hk hk' hd => Mo.hg μ k k' (hq23 k hk) (hq23 k' hk') hd) n m
  have hGu_b : ∀ k, InQr ε n₀ (r + 2 / 3) k → ‖locApp (D.G μ) D.u k‖ ≤ S := fun k hk =>
    (norm_locApp_le _ _ _ (hL.2 μ k (inQ_mono hε (by linarith) hk))).trans
      (sup'_le _ _ fun e he => B.hu _ (inQ_mono hε (by linarith) (inQ_add_off hε hε3 hk he)))
  have p3 := local_product (n₀ := n₀) hε hβ0 hβ1 (φ := fun k => chiL ε r n₀ (k + e4 μ))
    (f := locApp (D.G μ) D.u) (ρ := r + 2 / 3) (A := 9 / 2) (Sf := S) (T := Υ + S) (by norm_num) hS0
    (by linarith) hchi_s hchi_b hchi_l hGu_b
    (fun k k' hk hk' hd => holder_locApp D hε hε3 hrR hβ0 hβ1 hL hGL B.hu Mo.hu hS0 μ hk hk' hd) n m
  have e : Fm D ε r n₀ μ (n + m) - Fm D ε r n₀ μ n =
      (dfw ε μ (chiL ε r n₀) (n + m) • D.u (n + m) - dfw ε μ (chiL ε r n₀) n • D.u n) +
      (chiL ε r n₀ (n + m + e4 μ) • D.g μ (n + m) - chiL ε r n₀ (n + e4 μ) • D.g μ n) +
      (chiL ε r n₀ (n + m + e4 μ) • locApp (D.G μ) D.u (n + m) - chiL ε r n₀ (n + e4 μ) • locApp (D.G μ) D.u n) := by
    simp only [Fm, vf, smul_add]; abel
  rw [e]
  calc _ ≤ 54 * (Υ + 2 * S) * (ε * l1 m) ^ β + 9 / 2 * (Γ + 2 * Hg μ) * (ε * l1 m) ^ β +
        9 / 2 * (Υ + S + 2 * S) * (ε * l1 m) ^ β :=
        (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add p1 p2)) p3)
    _ = (117 / 2 * Υ + 243 / 2 * S + 9 / 2 * Γ + 9 * Hg μ) * (ε * l1 m) ^ β := by ring

/-- The modulus of `ψ_μu` at all points. -/
theorem holder_psiu {S Hh β Υ : ℝ} {Hg : Fin 4 → ℝ} (hr : 0 < r) (hβ0 : 0 < β) (hβ1 : β < 1)
    (B : Bounds D ε r n₀ S Hh Hg) (hΥ : ∀ n n', InQr ε n₀ (r + 1) n → InQr ε n₀ (r + 1) n' →
      ε * l1 (n - n') ≤ 1 → ‖D.u n - D.u n'‖ ≤ Υ * (ε * l1 (n - n')) ^ β) (hΥ0 : 0 ≤ Υ) (μ : Fin 4)
    (n m : Fin 4 → ℤ) :
    ‖psiu D ε r n₀ μ (n + m) - psiu D ε r n₀ μ n‖ ≤ 54 * (Υ + 2 * S) * (ε * l1 m) ^ β := by
  obtain ⟨hS0, -, -⟩ := B.nonneg D hr.le
  exact local_product (n₀ := n₀) hε hβ0 hβ1 (φ := fun k => dfw ε μ (chiL ε r n₀) (k - e4 μ)) (f := D.u)
    (ρ := r + 1) (A := 54) (Sf := S) (T := Υ) (by norm_num) hS0 hΥ0
    (fun k hk => by by_contra h; exact hk fun ν => (psi_supp hε hε3 h ν).le)
    (fun k => (abs_dfw_chiL hε hr _ μ).trans (by norm_num))
    (fun k k' => by
      have := dfw_chiL_lip (n₀ := n₀) hε hr (k - e4 μ) (k' - e4 μ) μ
      rwa [show k - e4 μ - (k' - e4 μ) = k - k' by abel] at this)
    B.hu hΥ n m

omit hε hε3 in
lemma dfw_sub' (f g : (Fin 4 → ℤ) → V) (ν : Fin 4) (n : Fin 4 → ℤ) :
    dfw ε ν (fun m => f m - g m) n = dfw ε ν f n - dfw ε ν g n := by
  simp only [dfw]; module

omit hε hε3 in
lemma dfw_add' (f g : (Fin 4 → ℤ) → V) (ν : Fin 4) (n : Fin 4 → ℤ) :
    dfw ε ν (fun m => f m + g m) n = dfw ε ν f n + dfw ε ν g n := by
  simp only [dfw]; module

omit hε hε3 in
lemma dfw_sum' (f : Fin 4 → (Fin 4 → ℤ) → V) (ν : Fin 4) (n : Fin 4 → ℤ) :
    dfw ε ν (fun m => ∑ μ, f μ m) n = ∑ μ, dfw ε ν (f μ) n := by
  simp only [dfw, ← smul_sum, ← sum_sub_distrib]

/-- `∂_ν` of the representation. -/
lemma dfw_rep {R : ℝ} (hrR : r ≤ R - 1) (hE : Eqn D ε n₀ R) (ν : Fin 4) (n : Fin 4 → ℤ) :
    dfw ε ν (chiu D ε r n₀) n = dfw ε ν (resolvent ε (F0 D ε r n₀)) n +
      ∑ μ, dfw ε ν (dbw ε μ (resolvent ε (Fm D ε r n₀ μ))) n -
      ∑ μ, dfw ε ν (dfw ε μ (resolvent ε (psiu D ε r n₀ μ))) n := by
  rw [representation D hε hε3 (r := r) (R := R) (by linarith) hE]
  simp only [dfw_sub', dfw_add', dfw_sum']

omit hε hε3 in
/-- `∂_νu = ∂_ν(χu)` at the points `z` with `z, z + εe_ν ∈ Q_r`. -/
lemma dfw_u_eq {ν : Fin 4} {n : Fin 4 → ℤ} (h1 : InQr ε n₀ r n) (h2 : InQr ε n₀ r (n + e4 ν)) :
    dfw ε ν D.u n = dfw ε ν (chiu D ε r n₀) n := by
  simp only [dfw, chiu, chiL_eq_one h1, chiL_eq_one h2, one_smul]

/-- **`lem:local-laplacian`(iii)**, the first bound. -/
theorem local_derivative {R S Hh β Υ Γ : ℝ} {Hg : Fin 4 → ℝ} (hr : 0 < r) (hrR : r ≤ R - 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hE : Eqn D ε n₀ R) (hL : LocNorm D ε n₀ R) (hGL : GLip D ε n₀ (r + 1))
    (B : Bounds D ε r n₀ S Hh Hg) (Mo : Moduli D ε r n₀ β Υ Γ) (hΥ0 : 0 ≤ Υ) (hΓ0 : 0 ≤ Γ) (ν : Fin 4)
    {n : Fin 4 → ℤ} (h1 : InQr ε n₀ r n) (h2 : InQr ε n₀ r (n + e4 ν)) :
    ‖dfw ε ν D.u n‖ ≤ KD β * (S + Υ + (Hh + ∑ μ, Hg μ) + Γ) := by
  obtain ⟨hS0, hH0, hG0⟩ := B.nonneg D hr.le
  have hG : 0 ≤ ∑ μ, Hg μ := sum_nonneg fun μ _ => hG0 μ
  have hC := CS_pos hβ0 hβ1
  have hC' := CS'_pos hβ1
  rw [dfw_u_eq D h1 h2, dfw_rep D hε hε3 hrR hE]
  have hF0 : ∀ k, ‖F0 D ε r n₀ k‖ ≤ Hh + 9 / 2 * ∑ μ, Hg μ + 236 * S := fun k => sup_F0_le D hε hε3 hr hrR hL B k
  have t1 := norm_dif_resolvent_le hε hF0 true ν n
  have t2 : ∀ μ, ‖dfw ε ν (dbw ε μ (resolvent ε (Fm D ε r n₀ μ))) n‖ ≤
      CS β * (117 / 2 * Υ + 243 / 2 * S + 9 / 2 * Γ + 9 * Hg μ) := fun μ =>
    norm_dif_dif_resolvent_le hε hβ0 hβ1 (by have := hG0 μ; positivity)
      (fun k => sup_Fm_le D hε hε3 hr hrR hL B μ k)
      (holder_Fm D hε hε3 hr hrR hβ0 hβ1 hL hGL B Mo hΥ0 hΓ0 μ) true false ν μ n
  have t3 : ∀ μ, ‖dfw ε ν (dfw ε μ (resolvent ε (psiu D ε r n₀ μ))) n‖ ≤ CS β * (54 * (Υ + 2 * S)) := fun μ =>
    norm_dif_dif_resolvent_le hε hβ0 hβ1 (by positivity) (fun k => sup_psiu_le D hε hε3 hr B μ k)
      (holder_psiu D hε hε3 hr hβ0 hβ1 B Mo.hu hΥ0 μ) true true ν μ n
  calc _ ≤ 2 * (Hh + 9 / 2 * ∑ μ, Hg μ + 236 * S) + ∑ μ, CS β * (117 / 2 * Υ + 243 / 2 * S + 9 / 2 * Γ + 9 * Hg μ) +
        ∑ _μ : Fin 4, CS β * (54 * (Υ + 2 * S)) :=
        (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add t1
          ((norm_sum_le _ _).trans (sum_le_sum fun μ _ => t2 μ)))) ((norm_sum_le _ _).trans (sum_le_sum fun μ _ => t3 μ)))
    _ = 2 * Hh + 9 * ∑ μ, Hg μ + 472 * S + CS β * (450 * Υ + 918 * S + 18 * Γ + 9 * ∑ μ, Hg μ) := by
        simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_sum, sum_add_distrib]
        ring
    _ ≤ KD β * (S + Υ + (Hh + ∑ μ, Hg μ) + Γ) := by
        unfold KD
        nlinarith [mul_nonneg hC.le hS0, mul_nonneg hC.le hΥ0, mul_nonneg hC.le hΓ0, mul_nonneg hC.le hH0,
          mul_nonneg hC.le hG, mul_nonneg hC'.le hS0, mul_nonneg hC'.le hΥ0, mul_nonneg hC'.le hΓ0,
          mul_nonneg hC'.le hH0, mul_nonneg hC'.le hG]

/-- **`lem:local-laplacian`(iii)**, the second bound. -/
theorem local_derivative_holder {R S Hh β Υ Γ : ℝ} {Hg : Fin 4 → ℝ} (hr : 0 < r) (hrR : r ≤ R - 1)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hE : Eqn D ε n₀ R) (hL : LocNorm D ε n₀ R) (hGL : GLip D ε n₀ (r + 1))
    (B : Bounds D ε r n₀ S Hh Hg) (Mo : Moduli D ε r n₀ β Υ Γ) (hΥ0 : 0 ≤ Υ) (hΓ0 : 0 ≤ Γ) (ν : Fin 4)
    {n n' : Fin 4 → ℤ} (h1 : InQr ε n₀ r n) (h2 : InQr ε n₀ r (n + e4 ν)) (h1' : InQr ε n₀ r n')
    (h2' : InQr ε n₀ r (n' + e4 ν)) :
    ‖dfw ε ν D.u n - dfw ε ν D.u n'‖ ≤ KD β * (S + Υ + (Hh + ∑ μ, Hg μ) + Γ) * (ε * l1 (n - n')) ^ β := by
  obtain ⟨hS0, hH0, hG0⟩ := B.nonneg D hr.le
  have hG : 0 ≤ ∑ μ, Hg μ := sum_nonneg fun μ _ => hG0 μ
  have hC := CS_pos hβ0 hβ1
  have hC' := CS'_pos hβ1
  have hm : n = n' + (n - n') := by abel
  set d := ε * l1 (n - n')
  have hdβ : 0 ≤ d ^ β := Real.rpow_nonneg (mul_nonneg hε.le (l1_nonneg _)) β
  rw [dfw_u_eq D h1 h2, dfw_u_eq D h1' h2', dfw_rep D hε hε3 hrR hE, dfw_rep D hε hε3 hrR hE]
  have hF0 : ∀ k, ‖F0 D ε r n₀ k‖ ≤ Hh + 9 / 2 * ∑ μ, Hg μ + 236 * S := fun k => sup_F0_le D hε hε3 hr hrR hL B k
  have t1 : ‖dfw ε ν (resolvent ε (F0 D ε r n₀)) n - dfw ε ν (resolvent ε (F0 D ε r n₀)) n'‖ ≤
      CS' β * (Hh + 9 / 2 * ∑ μ, Hg μ + 236 * S) * d ^ β := by
    have h := norm_dif_resolvent_sub_le hε hβ0 hβ1 hF0 true ν n' (n - n')
    rwa [← hm] at h
  have t2 : ∀ μ, ‖dfw ε ν (dbw ε μ (resolvent ε (Fm D ε r n₀ μ))) n - dfw ε ν (dbw ε μ (resolvent ε (Fm D ε r n₀ μ))) n'‖ ≤
      CS β * (117 / 2 * Υ + 243 / 2 * S + 9 / 2 * Γ + 9 * Hg μ) * d ^ β := fun μ => by
    have h := norm_dif_dif_resolvent_sub_le hε hβ0 hβ1 (by have := hG0 μ; positivity)
      (fun k => sup_Fm_le D hε hε3 hr hrR hL B μ k)
      (holder_Fm D hε hε3 hr hrR hβ0 hβ1 hL hGL B Mo hΥ0 hΓ0 μ) true false ν μ n' (n - n')
    rwa [← hm] at h
  have t3 : ∀ μ, ‖dfw ε ν (dfw ε μ (resolvent ε (psiu D ε r n₀ μ))) n - dfw ε ν (dfw ε μ (resolvent ε (psiu D ε r n₀ μ))) n'‖ ≤
      CS β * (54 * (Υ + 2 * S)) * d ^ β := fun μ => by
    have h := norm_dif_dif_resolvent_sub_le hε hβ0 hβ1 (by positivity) (fun k => sup_psiu_le D hε hε3 hr B μ k)
      (holder_psiu D hε hε3 hr hβ0 hβ1 B Mo.hu hΥ0 μ) true true ν μ n' (n - n')
    rwa [← hm] at h
  have e : ∀ (a a' : V) (b b' c c' : Fin 4 → V), a + ∑ μ, b μ - ∑ μ, c μ - (a' + ∑ μ, b' μ - ∑ μ, c' μ) =
      (a - a') + ∑ μ, (b μ - b' μ) - ∑ μ, (c μ - c' μ) := fun a a' b b' c c' => by
    simp only [sum_sub_distrib]; abel
  rw [e]
  calc _ ≤ CS' β * (Hh + 9 / 2 * ∑ μ, Hg μ + 236 * S) * d ^ β +
        ∑ μ, CS β * (117 / 2 * Υ + 243 / 2 * S + 9 / 2 * Γ + 9 * Hg μ) * d ^ β +
        ∑ _μ : Fin 4, CS β * (54 * (Υ + 2 * S)) * d ^ β :=
        (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add t1
          ((norm_sum_le _ _).trans (sum_le_sum fun μ _ => t2 μ)))) ((norm_sum_le _ _).trans (sum_le_sum fun μ _ => t3 μ)))
    _ = (CS' β * (Hh + 9 / 2 * ∑ μ, Hg μ + 236 * S) + CS β * (450 * Υ + 918 * S + 18 * Γ + 9 * ∑ μ, Hg μ)) * d ^ β := by
        simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, ← sum_mul, ← mul_sum, sum_add_distrib]
        ring
    _ ≤ KD β * (S + Υ + (Hh + ∑ μ, Hg μ) + Γ) * d ^ β := by
        refine mul_le_mul_of_nonneg_right ?_ hdβ
        unfold KD
        nlinarith [mul_nonneg hC.le hS0, mul_nonneg hC.le hΥ0, mul_nonneg hC.le hΓ0, mul_nonneg hC.le hH0,
          mul_nonneg hC.le hG, mul_nonneg hC'.le hS0, mul_nonneg hC'.le hΥ0, mul_nonneg hC'.le hΓ0,
          mul_nonneg hC'.le hH0, mul_nonneg hC'.le hG]

end LocalLaplacian
end CoreLean

end
