/-
`lem:local-laplacian`(iv) of BALABAN_CORE.tex (`0580551bf179`): the second differences in `L²`,
`(Σ_{κ,ν}‖∂_κ∂_νu‖²_{2,Q_r})^{1/2} ≤ ‖h‖_{2,Q_{r+1}} + 2¹¹(‖u‖_{2,Q_{r+1}} + ‖∂u‖_{2,Q_{r+1}})`, for `g_μ = 0` and Lipschitz
operators `G_μ`, the norm of `𝖵` that of an inner product.

* `lap_mul_expand`: `Δ(χu) = χΔu + Σ_μ((∂_μχ)(· - εe_μ)∂^*_μu - (∂_μχ)∂_μu + (∂^*_μ∂_μχ)u)`;
  `dbw_locApp`: `∂^*_μ(G_μu)(z) = Σ_e(T_e(z - εe_μ)(∂^*_μu)(z + e) + ε⁻¹(T_e(z - εe_μ) - T_e(z))u(z + e))`.
* `Dm μ z`: the root of the sum of the squares of the admissible differences `‖∂_μu(z')‖`,
  `z' ∈ {z + e, z + e - εe_μ | e ∈ E}`, `z', z' + εe_μ ∈ Q_{r+1}` (it bounds the core's maximum `D_μ(z)`);
  `S2 z`: the root of `Σ_{e ∈ E}‖u(z + e)‖²` (it bounds `S_*(z)`).
* `norm_lap_chiu_le`: `‖Δ(χu)‖ ≤ ‖h‖ + 221S_* + 10Σ_μD_μ`.
* `wN`: the weighted `L²` norm on a finite set; `wN_add`, `wN_mono`, `wN_smul`: Minkowski, monotonicity, scaling.
* `local_second`: (iv).
-/
import CoreLean.LocalSums
import CoreLean.LocalDerivative

open Finset
open scoped RealInnerProductSpace Classical

noncomputable section

namespace CoreLean
namespace LocalLaplacian

/-! ### Weighted `L²` norms on finite sets -/

section WN

variable {ι : Type*}

/-- `(Σ_{i ∈ s} w_i f_i²)^{1/2}`. -/
def wN (s : Finset ι) (w : ι → ℝ) (f : ι → ℝ) : ℝ := Real.sqrt (∑ i ∈ s, w i * f i ^ 2)

variable {s : Finset ι} {w : ι → ℝ}

lemma wN_nonneg (f : ι → ℝ) : 0 ≤ wN s w f := Real.sqrt_nonneg _

lemma wN_sq (hw : ∀ i, 0 ≤ w i) (f : ι → ℝ) : wN s w f ^ 2 = ∑ i ∈ s, w i * f i ^ 2 :=
  Real.sq_sqrt (sum_nonneg fun i _ => mul_nonneg (hw i) (sq_nonneg _))

lemma wN_add (hw : ∀ i, 0 ≤ w i) (f g : ι → ℝ) : wN s w (fun i => f i + g i) ≤ wN s w f + wN s w g := by
  have hcs : ∑ i ∈ s, w i * (f i * g i) ≤ wN s w f * wN s w g := by
    have := Real.sum_mul_le_sqrt_mul_sqrt s (fun i => Real.sqrt (w i) * f i) (fun i => Real.sqrt (w i) * g i)
    simp only [mul_pow, Real.sq_sqrt (hw _)] at this
    unfold wN
    refine le_trans (le_of_eq ?_) this
    refine sum_congr rfl fun i _ => ?_
    rw [show Real.sqrt (w i) * f i * (Real.sqrt (w i) * g i) = (Real.sqrt (w i) * Real.sqrt (w i)) * (f i * g i) by ring,
      Real.mul_self_sqrt (hw i)]
  unfold wN at *
  rw [Real.sqrt_le_left (by positivity)]
  have e : ∑ i ∈ s, w i * (f i + g i) ^ 2 =
      ∑ i ∈ s, w i * f i ^ 2 + 2 * ∑ i ∈ s, w i * (f i * g i) + ∑ i ∈ s, w i * g i ^ 2 := by
    rw [mul_sum, ← sum_add_distrib, ← sum_add_distrib]; exact sum_congr rfl fun i _ => by ring
  rw [e, add_sq, Real.sq_sqrt (sum_nonneg fun i _ => mul_nonneg (hw i) (sq_nonneg _)),
    Real.sq_sqrt (sum_nonneg fun i _ => mul_nonneg (hw i) (sq_nonneg _))]
  linarith

lemma wN_mono (hw : ∀ i, 0 ≤ w i) {f g : ι → ℝ} (hf : ∀ i ∈ s, 0 ≤ f i) (hfg : ∀ i ∈ s, f i ≤ g i) :
    wN s w f ≤ wN s w g :=
  Real.sqrt_le_sqrt (sum_le_sum fun i hi => mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (hf i hi) (hfg i hi) 2) (hw i))

lemma wN_smul (hw : ∀ i, 0 ≤ w i) {c : ℝ} (hc : 0 ≤ c) (f : ι → ℝ) : wN s w (fun i => c * f i) = c * wN s w f := by
  unfold wN
  rw [show ∑ i ∈ s, w i * (c * f i) ^ 2 = c ^ 2 * ∑ i ∈ s, w i * f i ^ 2 by
      rw [mul_sum]; exact sum_congr rfl fun i _ => by ring,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hc]

lemma wN_sum (hw : ∀ i, 0 ≤ w i) (f : Fin 4 → ι → ℝ) : wN s w (fun i => ∑ μ, f μ i) ≤ ∑ μ, wN s w (f μ) := by
  simp only [Fin.sum_univ_four]
  refine (wN_add hw _ _).trans (add_le_add ((wN_add hw _ _).trans (add_le_add (wN_add hw _ _) le_rfl)) le_rfl)

end WN

/-! ### The expansion of `Δ(χu)` -/

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
variable {ε r : ℝ} {n₀ : Fin 4 → ℤ}

lemma lap_mul_expand (χ : (Fin 4 → ℤ) → ℝ) (u : (Fin 4 → ℤ) → V) (z : Fin 4 → ℤ) :
    lap ε (fun m => χ m • u m) z = χ z • lap ε u z + ∑ μ, (dfw ε μ χ (z - e4 μ) • dbw ε μ u z -
      dfw ε μ χ z • dfw ε μ u z + dbw ε μ (dfw ε μ χ) z • u z) := by
  simp only [lap, smul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun μ _ => ?_
  simp only [dbw, dfw, smul_eq_mul, sub_add_cancel]
  module

lemma dbw_locApp (T : (Fin 4 → ℤ) → (Fin 4 → ℤ) → (V →L[ℝ] V)) (u : (Fin 4 → ℤ) → V) (μ : Fin 4) (z : Fin 4 → ℤ) :
    dbw ε μ (locApp T u) z = ∑ e ∈ Eoff, (T (z - e4 μ) e (dbw ε μ u (z + e)) +
      ε⁻¹ • (T (z - e4 μ) e - T z e) (u (z + e))) := by
  simp only [dbw, locApp, ← sum_sub_distrib, smul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun e _ => ?_
  rw [map_smul, map_sub, ContinuousLinearMap.sub_apply, show z + e - e4 μ = z - e4 μ + e by abel]
  module

variable (D : LData V)

/-- The admissible squares: `‖∂_μu(z')‖²` if `z', z' + εe_μ ∈ Q_{r+1}`, else `0`. -/
def adm (ε r : ℝ) (n₀ : Fin 4 → ℤ) (μ : Fin 4) (z' : Fin 4 → ℤ) : ℝ :=
  if InQr ε n₀ (r + 1) z' ∧ InQr ε n₀ (r + 1) (z' + e4 μ) then ‖dfw ε μ D.u z'‖ ^ 2 else 0

lemma adm_nonneg (μ : Fin 4) (z' : Fin 4 → ℤ) : 0 ≤ adm D ε r n₀ μ z' := by
  unfold adm; split_ifs <;> positivity

/-- `D_μ(z)`, as the root of the sum of the admissible squares. -/
def Dm (ε r : ℝ) (n₀ : Fin 4 → ℤ) (μ : Fin 4) (z : Fin 4 → ℤ) : ℝ :=
  Real.sqrt (∑ e ∈ Eoff, (adm D ε r n₀ μ (z + e) + adm D ε r n₀ μ (z + e - e4 μ)))

/-- `(Σ_{e ∈ E}‖u(z + e)‖²)^{1/2}`. -/
def S2 (z : Fin 4 → ℤ) : ℝ := Real.sqrt (∑ e ∈ Eoff, ‖D.u (z + e)‖ ^ 2)

lemma Sst_le_S2 (z : Fin 4 → ℤ) : Sst D.u z ≤ S2 D z := by
  refine sup'_le _ _ fun e he => ?_
  unfold S2
  rw [← Real.sqrt_sq (norm_nonneg (D.u (z + e)))]
  exact Real.sqrt_le_sqrt (single_le_sum (f := fun e => ‖D.u (z + e)‖ ^ 2) (fun _ _ => sq_nonneg _) he)

lemma le_Dm {μ : Fin 4} {z z' : Fin 4 → ℤ} {e : Fin 4 → ℤ} (he : e ∈ Eoff)
    (hz' : z' = z + e ∨ z' = z + e - e4 μ) (h1 : InQr ε n₀ (r + 1) z') (h2 : InQr ε n₀ (r + 1) (z' + e4 μ)) :
    ‖dfw ε μ D.u z'‖ ≤ Dm D ε r n₀ μ z := by
  have ha : adm D ε r n₀ μ z' = ‖dfw ε μ D.u z'‖ ^ 2 := by unfold adm; rw [if_pos ⟨h1, h2⟩]
  unfold Dm
  rw [← Real.sqrt_sq (norm_nonneg (dfw ε μ D.u z')), ← ha]
  refine Real.sqrt_le_sqrt ((le_trans ?_ (single_le_sum (f := fun e => adm D ε r n₀ μ (z + e) +
    adm D ε r n₀ μ (z + e - e4 μ)) (fun e _ => add_nonneg (adm_nonneg D μ _) (adm_nonneg D μ _)) he)))
  rcases hz' with h | h
  · rw [h]; exact le_add_of_nonneg_right (adm_nonneg D μ _)
  · rw [h]; exact le_add_of_nonneg_left (adm_nonneg D μ _)

variable (hε : 0 < ε) (hε3 : ε ≤ 1 / 3)
include hε hε3

omit [CompleteSpace V] in
lemma inQ_e4 {ρ : ℝ} {z : Fin 4 → ℤ} (h : InQr ε n₀ ρ z) (μ : Fin 4) : InQr ε n₀ (ρ + 1 / 3) (z + e4 μ) :=
  inQ_add_off hε hε3 h (e4_mem μ)

omit [CompleteSpace V] in
lemma inQ_sub_e4 {ρ : ℝ} {z : Fin 4 → ℤ} (h : InQr ε n₀ ρ z) (μ : Fin 4) : InQr ε n₀ (ρ + 1 / 3) (z - e4 μ) :=
  fun ν => ((inQ_sub hε (e4_mem μ) h) ν).trans (by linarith)

/-- **The pointwise bound** `‖Δ(χu)‖ ≤ ‖h‖ + 221S_* + 10Σ_μD_μ`. -/
theorem norm_lap_chiu_le {R : ℝ} (hr : 0 < r) (hrR : r ≤ R - 1) (hg0 : ∀ μ n, D.g μ n = 0)
    (hE : Eqn D ε n₀ R) (hL : LocNorm D ε n₀ R) (hGL : GLip D ε n₀ (r + 1)) (z : Fin 4 → ℤ) :
    ‖lap ε (chiu D ε r n₀) z‖ ≤ ‖D.h z‖ + 221 * Sst D.u z + 10 * ∑ μ, Dm D ε r n₀ μ z := by
  have hS := Sst_nonneg D.u z
  have hDm : ∀ μ, 0 ≤ Dm D ε r n₀ μ z := fun μ => Real.sqrt_nonneg _
  have hq : ∀ k ρ, InQr ε n₀ ρ k → ∀ ρ', ρ ≤ ρ' → InQr ε n₀ ρ' k := fun k ρ h ρ' hρ ν => (h ν).trans hρ
  -- the part with `χ(z)`
  have hχpart : ‖chiL ε r n₀ z • lap ε D.u z‖ ≤ ‖D.h z‖ + 5 * Sst D.u z + ∑ μ, Dm D ε r n₀ μ z := by
    by_cases h0 : chiL ε r n₀ z = 0
    · rw [h0, zero_smul, norm_zero]; have := sum_nonneg fun μ (_ : μ ∈ univ) => hDm μ; positivity
    have hz : InQr ε n₀ (r + 1 / 3) z := fun ν => (chiL_supp h0 ν).le
    have hzR : InQr ε n₀ (R - ε) z := hq z _ hz _ (by linarith)
    rw [hE z (hq z _ hz _ (by linarith))]
    obtain ⟨c0, c1⟩ : 0 ≤ chiL ε r n₀ z ∧ chiL ε r n₀ z ≤ 1 := ⟨chiL_nonneg z, chiL_le_one z⟩
    rw [norm_smul, Real.norm_of_nonneg c0]
    refine (mul_le_of_le_one_left (norm_nonneg _) c1).trans ?_
    have hvf : ∀ μ, vf D μ = locApp (D.G μ) D.u := fun μ => by funext n; simp [vf, hg0]
    simp only [hvf, dbw_locApp]
    have hterm : ∀ μ, ‖∑ e ∈ Eoff, ((D.G μ) (z - e4 μ) e (dbw ε μ D.u (z + e)) +
        ε⁻¹ • ((D.G μ) (z - e4 μ) e - (D.G μ) z e) (D.u (z + e)))‖ ≤ Dm D ε r n₀ μ z + Sst D.u z := fun μ => by
      have hzm : InQr ε n₀ (R - ε) (z - e4 μ) := hq _ _ (inQ_sub_e4 hε hε3 hz μ) _ (by linarith)
      have hlip := hGL μ (z - e4 μ) z (hq _ _ (inQ_sub_e4 hε hε3 hz μ) _ (by linarith)) (hq z _ hz _ (by linarith))
      have hl1 : ε * l1 (z - e4 μ - z) = ε := by
        rw [show z - e4 μ - z = -e4 μ by abel, l1_neg]
        unfold l1
        have : ∀ x : Fin 4, |(((e4 μ) x : ℤ) : ℝ)| = if x = μ then 1 else 0 := fun x => by
          by_cases hx : x = μ
          · subst hx; simp [e4]
          · simp [e4, Pi.single_eq_of_ne hx, hx]
        simp only [this, Finset.sum_ite_eq', Finset.mem_univ, if_true, mul_one]
      rw [hl1] at hlip
      rw [sum_add_distrib]
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · calc ‖∑ e ∈ Eoff, (D.G μ) (z - e4 μ) e (dbw ε μ D.u (z + e))‖
            ≤ ∑ e ∈ Eoff, ‖(D.G μ) (z - e4 μ) e‖ * Dm D ε r n₀ μ z := by
              refine (norm_sum_le _ _).trans (sum_le_sum fun e he => ((D.G μ (z - e4 μ) e).le_opNorm _).trans
                (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)))
              rw [dbw_eq_neg_dfw, norm_neg]
              have hze : InQr ε n₀ (r + 2 / 3) (z + e) := fun ν => ((inQ_add_off hε hε3 hz he) ν).trans (by linarith)
              refine le_Dm D he (Or.inr rfl) ?_ ?_
              · exact hq _ _ (inQ_sub_e4 hε hε3 hze μ) _ (by linarith)
              · rw [sub_add_cancel]; exact hq _ _ hze _ (by linarith)
          _ = (∑ e ∈ Eoff, ‖(D.G μ) (z - e4 μ) e‖) * Dm D ε r n₀ μ z := by rw [sum_mul]
          _ ≤ 1 * Dm D ε r n₀ μ z := mul_le_mul_of_nonneg_right (hL.2 μ _ hzm) (hDm μ)
          _ = Dm D ε r n₀ μ z := one_mul _
      · rw [← smul_sum, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hε.le)]
        calc ε⁻¹ * ‖∑ e ∈ Eoff, ((D.G μ) (z - e4 μ) e - (D.G μ) z e) (D.u (z + e))‖
            ≤ ε⁻¹ * ((∑ e ∈ Eoff, ‖(D.G μ) (z - e4 μ) e - (D.G μ) z e‖) * Sst D.u z) := by
              refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hε.le)
              rw [sum_mul]
              exact (norm_sum_le _ _).trans (sum_le_sum fun e he => (ContinuousLinearMap.le_opNorm _ _).trans
                (mul_le_mul_of_nonneg_left (norm_le_Sst D.u z he) (norm_nonneg _)))
          _ ≤ ε⁻¹ * (ε * Sst D.u z) := by gcongr
          _ = Sst D.u z := by field_simp
    calc ‖D.h z + locApp D.c D.u z + ∑ μ, ∑ e ∈ Eoff, ((D.G μ) (z - e4 μ) e (dbw ε μ D.u (z + e)) +
          ε⁻¹ • ((D.G μ) (z - e4 μ) e - (D.G μ) z e) (D.u (z + e)))‖
        ≤ ‖D.h z‖ + Sst D.u z + ∑ μ, (Dm D ε r n₀ μ z + Sst D.u z) :=
          (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add le_rfl
            (norm_locApp_le _ _ _ (hL.1 z hzR)))) ((norm_sum_le _ _).trans (sum_le_sum fun μ _ => hterm μ)))
      _ = ‖D.h z‖ + 5 * Sst D.u z + ∑ μ, Dm D ε r n₀ μ z := by
          rw [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; push_cast; ring
  -- the commutator terms
  have hcterm : ∀ μ, ‖dfw ε μ (chiL ε r n₀) (z - e4 μ) • dbw ε μ D.u z - dfw ε μ (chiL ε r n₀) z • dfw ε μ D.u z +
      dbw ε μ (dfw ε μ (chiL ε r n₀)) z • D.u z‖ ≤ 9 * Dm D ε r n₀ μ z + 54 * Sst D.u z := fun μ => by
    have a1 : ‖dfw ε μ (chiL ε r n₀) (z - e4 μ) • dbw ε μ D.u z‖ ≤ 9 / 2 * Dm D ε r n₀ μ z := by
      by_cases h0 : dfw ε μ (chiL ε r n₀) (z - e4 μ) = 0
      · rw [h0, zero_smul, norm_zero]; have := hDm μ; positivity
      have hzm : InQr ε n₀ (r + 2 / 3) (z - e4 μ) := fun ν => (dfw_chiL_supp hε hε3 h0 ν).le
      rw [norm_smul, Real.norm_eq_abs, dbw_eq_neg_dfw, norm_neg]
      refine mul_le_mul (abs_dfw_chiL hε hr _ μ) (le_Dm D (zero_mem_Eoff) (Or.inr (by simp)) ?_ ?_) (norm_nonneg _)
        (by norm_num)
      · exact hq _ _ hzm _ (by linarith)
      · rw [sub_add_cancel]; exact hq _ _ (show InQr ε n₀ (r + 2 / 3 + 1 / 3) z by
          have := inQ_e4 hε hε3 hzm μ; rwa [sub_add_cancel] at this) _ (by linarith)
    have a2 : ‖dfw ε μ (chiL ε r n₀) z • dfw ε μ D.u z‖ ≤ 9 / 2 * Dm D ε r n₀ μ z := by
      by_cases h0 : dfw ε μ (chiL ε r n₀) z = 0
      · rw [h0, zero_smul, norm_zero]; have := hDm μ; positivity
      have hz : InQr ε n₀ (r + 2 / 3) z := fun ν => (dfw_chiL_supp hε hε3 h0 ν).le
      rw [norm_smul, Real.norm_eq_abs]
      refine mul_le_mul (abs_dfw_chiL hε hr _ μ) (le_Dm D (zero_mem_Eoff) (Or.inl (by simp)) ?_ ?_) (norm_nonneg _)
        (by norm_num)
      · exact hq _ _ hz _ (by linarith)
      · exact hq _ _ (inQ_e4 hε hε3 hz μ) _ (by linarith)
    have a3 : ‖dbw ε μ (dfw ε μ (chiL ε r n₀)) z • D.u z‖ ≤ 54 * Sst D.u z := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (abs_dbw_dfw_chiL hε hr z μ) (norm_le_Sst_self D.u z) (norm_nonneg _) (by norm_num)
    calc _ ≤ 9 / 2 * Dm D ε r n₀ μ z + 9 / 2 * Dm D ε r n₀ μ z + 54 * Sst D.u z :=
          (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add a1 a2)) a3)
      _ = 9 * Dm D ε r n₀ μ z + 54 * Sst D.u z := by ring
  unfold chiu
  rw [lap_mul_expand]
  calc _ ≤ (‖D.h z‖ + 5 * Sst D.u z + ∑ μ, Dm D ε r n₀ μ z) + ∑ μ, (9 * Dm D ε r n₀ μ z + 54 * Sst D.u z) :=
        (norm_add_le _ _).trans (add_le_add hχpart ((norm_sum_le _ _).trans (sum_le_sum fun μ _ => hcterm μ)))
    _ = ‖D.h z‖ + 221 * Sst D.u z + 10 * ∑ μ, Dm D ε r n₀ μ z := by
        rw [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_sum]; push_cast; ring

/-! ### The `L²` bounds -/

omit hε3 [InnerProductSpace ℝ V] [CompleteSpace V] in
lemma SuppIn.lap {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] {ρ : ℝ} {f : (Fin 4 → ℤ) → W}
    (h : SuppIn ε n₀ ρ f) : SuppIn ε n₀ (ρ + ε) (lap ε f) := fun z hz => by
  by_contra hq
  apply hz
  have h0 : ∀ e ∈ Eoff, f (z + e) = 0 := fun e he => by
    by_contra h1
    exact hq (inQ_shift hε he (h _ h1))
  have hz0 : f z = 0 := by simpa using h0 0 zero_mem_Eoff
  have hp : ∀ μ, f (z + e4 μ) = 0 := fun μ => h0 _ (e4_mem μ)
  have hm : ∀ μ, f (z - e4 μ) = 0 := fun μ => by rw [sub_eq_add_neg]; exact h0 _ (neg_mem_Eoff (e4_mem μ))
  rw [lap_eq]
  simp [hz0, hp, hm]

omit hε hε3 [InnerProductSpace ℝ V] [CompleteSpace V] in
lemma sum_le_of_supp {F : (Fin 4 → ℤ) → ℝ} {A B : Finset (Fin 4 → ℤ)} (hB : ∀ w ∈ B, 0 ≤ F w)
    (h : ∀ w ∈ A, F w ≠ 0 → w ∈ B) : ∑ w ∈ A, F w ≤ ∑ w ∈ B, F w := by
  rw [← sum_filter_ne_zero]
  exact sum_le_sum_of_subset_of_nonneg (fun w hw => by
    rw [mem_filter] at hw; exact h w hw.1 hw.2) (fun w hw _ => hB w hw)

omit hε hε3 [InnerProductSpace ℝ V] [CompleteSpace V] in
lemma sum_shift_eq_map {F : (Fin 4 → ℤ) → ℝ} (A : Finset (Fin 4 → ℤ)) (e : Fin 4 → ℤ) :
    ∑ z ∈ A, F (z + e) = ∑ w ∈ A.map (addRightEmbedding e), F w := by rw [sum_map]; rfl

omit hε hε3 [InnerProductSpace ℝ V] [CompleteSpace V] in
lemma card_Eoff : Eoff.card = 81 := by
  simp [Eoff, Fintype.card_piFinset, Int.card_Icc]

omit hε hε3 [InnerProductSpace ℝ V] [CompleteSpace V] in
lemma wN_subset {s s' : Finset (Fin 4 → ℤ)} (h : s ⊆ s') (f : (Fin 4 → ℤ) → ℝ) :
    wN s (fun _ => ε ^ 4) f ≤ wN s' (fun _ => ε ^ 4) f :=
  Real.sqrt_le_sqrt (sum_le_sum_of_subset_of_nonneg h fun _ _ _ => by positivity)

omit [InnerProductSpace ℝ V] [CompleteSpace V] in
lemma count_shift {F : (Fin 4 → ℤ) → ℝ} (hF : ∀ w, 0 ≤ F w) {e : Fin 4 → ℤ} (he : e ∈ Eoff) (ρ : ℝ) :
    ∑ z ∈ QF ε n₀ ρ, F (z + e) ≤ ∑ w ∈ QF ε n₀ (ρ + 1 / 3), F w := by
  rw [sum_shift_eq_map]
  refine sum_le_sum_of_subset_of_nonneg (fun w hw => ?_) (fun w _ _ => hF w)
  obtain ⟨z, hz, hzw⟩ := mem_map.1 hw
  rw [← hzw, addRightEmbedding_apply]
  exact (mem_QF hε).2 (inQ_add_off hε hε3 ((mem_QF hε).1 hz) he)

/-- **`lem:local-laplacian`(iv)**. -/
theorem local_second {R : ℝ} (hr : 0 < r) (hrR : r ≤ R - 1) (hg0 : ∀ μ n, D.g μ n = 0)
    (hE : Eqn D ε n₀ R) (hL : LocNorm D ε n₀ R) (hGL : GLip D ε n₀ (r + 1)) :
    Real.sqrt (∑ κ, ∑ ν, ∑ z ∈ (QF ε n₀ r).filter (fun z => InQr ε n₀ r (z + e4 κ) ∧ InQr ε n₀ r (z + e4 ν) ∧
        InQr ε n₀ r (z + e4 κ + e4 ν)), ε ^ 4 * ‖dfw ε κ (dfw ε ν D.u) z‖ ^ 2) ≤
      wN (QF ε n₀ (r + 1)) (fun _ => ε ^ 4) (fun z => ‖D.h z‖) +
        2 ^ 11 * (wN (QF ε n₀ (r + 1)) (fun _ => ε ^ 4) (fun z => ‖D.u z‖) +
          Real.sqrt (∑ μ, ∑ z ∈ (QF ε n₀ (r + 1)).filter (fun z => InQr ε n₀ (r + 1) (z + e4 μ)),
            ε ^ 4 * ‖dfw ε μ D.u z‖ ^ 2)) := by
  have hw : ∀ z : Fin 4 → ℤ, 0 ≤ (fun _ => ε ^ 4) z := fun _ => by positivity
  have he4 : 0 ≤ ε ^ 4 := by positivity
  set T' := QF ε n₀ (r + 2 / 3)
  have hsupp : SuppIn ε n₀ (r + 1 / 3) (chiu D ε r n₀) := fun z hz ν => by
    have h0 : chiL ε r n₀ z ≠ 0 := fun h => hz (by simp [chiu, h])
    exact (chiL_supp h0 ν).le
  -- step 1: the left side is at most `‖Δ(χu)‖₂` over `T'`
  have hstep1 : Real.sqrt (∑ κ, ∑ ν, ∑ z ∈ (QF ε n₀ r).filter (fun z => InQr ε n₀ r (z + e4 κ) ∧ InQr ε n₀ r (z + e4 ν) ∧
        InQr ε n₀ r (z + e4 κ + e4 ν)), ε ^ 4 * ‖dfw ε κ (dfw ε ν D.u) z‖ ^ 2) ≤
      wN T' (fun _ => ε ^ 4) (fun z => ‖lap ε (chiu D ε r n₀) z‖) := by
    unfold wN
    refine Real.sqrt_le_sqrt ?_
    calc _ ≤ ∑ κ, ∑ ν, ∑ z ∈ QF ε n₀ (r + 2), ε ^ 4 * ‖dfw ε κ (dfw ε ν (chiu D ε r n₀)) z‖ ^ 2 := by
          refine sum_le_sum fun κ _ => sum_le_sum fun ν _ => ?_
          refine le_trans (le_of_eq (sum_congr rfl fun z hz => ?_)) (sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => by positivity)
          · rw [mem_filter] at hz
            obtain ⟨hz0, h1, h2, h3⟩ := hz
            have hz0' := (mem_QF hε).1 hz0
            congr 2
            simp only [dfw, chiu, chiL_eq_one hz0', chiL_eq_one h1, chiL_eq_one h2, chiL_eq_one h3, one_smul]
          · intro z hz
            rw [mem_filter] at hz
            exact (mem_QF hε).2 fun ν => (((mem_QF hε).1 hz.1) ν).trans (by linarith)
      _ = ε ^ 4 * ∑ z ∈ QF ε n₀ (r + 2), ‖lap ε (chiu D ε r n₀) z‖ ^ 2 := by
          simp only [← mul_sum]
          rw [sum_dd_eq_lap hε (ρ := r + 1 / 3) (by linarith) hsupp]
      _ = ∑ z ∈ T', ε ^ 4 * ‖lap ε (chiu D ε r n₀) z‖ ^ 2 := by
          rw [mul_sum]
          have hl := hsupp.lap hε
          refine sum_eq_of_supp (fun z hz => ?_) (fun z hz => ?_)
          · have : lap ε (chiu D ε r n₀) z ≠ 0 := fun h => hz (by rw [h]; simp)
            exact (mem_QF hε).2 fun ν => ((hl z this) ν).trans (by linarith)
          · have : lap ε (chiu D ε r n₀) z ≠ 0 := fun h => hz (by rw [h]; simp)
            exact (mem_QF hε).2 fun ν => ((hl z this) ν).trans (by linarith)
  -- step 2: Minkowski
  have hpt : ∀ z ∈ T', ‖lap ε (chiu D ε r n₀) z‖ ≤ (‖D.h z‖ + 221 * S2 D z) + 10 * ∑ μ, Dm D ε r n₀ μ z :=
    fun z _ => (norm_lap_chiu_le D hε hε3 hr hrR hg0 hE hL hGL z).trans (by
      have := Sst_le_S2 D z; linarith)
  have hstep2 : wN T' (fun _ => ε ^ 4) (fun z => ‖lap ε (chiu D ε r n₀) z‖) ≤
      wN T' (fun _ => ε ^ 4) (fun z => ‖D.h z‖) + 221 * wN T' (fun _ => ε ^ 4) (S2 D) +
        10 * ∑ μ, wN T' (fun _ => ε ^ 4) (Dm D ε r n₀ μ) := by
    refine (wN_mono hw (fun z _ => norm_nonneg _) hpt).trans ?_
    refine (wN_add hw _ _).trans (add_le_add ((wN_add hw _ _).trans (add_le_add le_rfl ?_)) ?_)
    · rw [wN_smul hw (by norm_num)]
    · rw [wN_smul hw (by norm_num)]
      exact mul_le_mul_of_nonneg_left (wN_sum hw _) (by norm_num)
  -- step 3: the three norms
  have hh : wN T' (fun _ => ε ^ 4) (fun z => ‖D.h z‖) ≤ wN (QF ε n₀ (r + 1)) (fun _ => ε ^ 4) (fun z => ‖D.h z‖) :=
    wN_subset (fun z hz => (mem_QF hε).2 fun ν => (((mem_QF hε).1 hz) ν).trans (by linarith)) _
  have hS2 : wN T' (fun _ => ε ^ 4) (S2 D) ≤ 9 * wN (QF ε n₀ (r + 1)) (fun _ => ε ^ 4) (fun z => ‖D.u z‖) := by
    have hsq : wN T' (fun _ => ε ^ 4) (S2 D) ^ 2 ≤ 81 * wN (QF ε n₀ (r + 1)) (fun _ => ε ^ 4) (fun z => ‖D.u z‖) ^ 2 := by
      rw [wN_sq hw, wN_sq hw]
      have e1 : ∀ z, S2 D z ^ 2 = ∑ e ∈ Eoff, ‖D.u (z + e)‖ ^ 2 := fun z =>
        Real.sq_sqrt (sum_nonneg fun _ _ => sq_nonneg _)
      simp only [e1, mul_sum]
      rw [sum_comm]
      have hb : ∀ e ∈ Eoff, ∑ z ∈ T', ε ^ 4 * ‖D.u (z + e)‖ ^ 2 ≤
          ∑ w ∈ QF ε n₀ (r + 1), ε ^ 4 * ‖D.u w‖ ^ 2 := fun e he => by
        have := count_shift hε hε3 (n₀ := n₀) (F := fun w => ε ^ 4 * ‖D.u w‖ ^ 2) (fun w => by positivity) he
          (r + 2 / 3)
        rw [show r + 2 / 3 + 1 / 3 = r + 1 by ring] at this
        exact this
      refine (sum_le_sum hb).trans (le_of_eq ?_)
      rw [sum_const, card_Eoff, nsmul_eq_mul, mul_sum]; norm_num
    have := wN_nonneg (s := QF ε n₀ (r + 1)) (w := fun _ => ε ^ 4) (fun z => ‖D.u z‖)
    have := wN_nonneg (s := T') (w := fun _ => ε ^ 4) (S2 D)
    nlinarith
  set A : Fin 4 → ℝ := fun μ => ∑ z ∈ QF ε n₀ (r + 1), ε ^ 4 * adm D ε r n₀ μ z with hA
  have hA0 : ∀ μ, 0 ≤ A μ := fun μ => sum_nonneg fun z _ => mul_nonneg he4 (adm_nonneg D μ z)
  have hDm : ∀ μ, wN T' (fun _ => ε ^ 4) (Dm D ε r n₀ μ) ≤ Real.sqrt 162 * Real.sqrt (A μ) := fun μ => by
    rw [← Real.sqrt_mul (by norm_num)]
    unfold wN
    refine Real.sqrt_le_sqrt ?_
    have e1 : ∀ z, Dm D ε r n₀ μ z ^ 2 = ∑ e ∈ Eoff, (adm D ε r n₀ μ (z + e) + adm D ε r n₀ μ (z + e - e4 μ)) :=
      fun z => Real.sq_sqrt (sum_nonneg fun _ _ => add_nonneg (adm_nonneg D μ _) (adm_nonneg D μ _))
    simp only [e1, mul_sum, mul_add, sum_add_distrib]
    rw [sum_comm, sum_comm (s := T')]
    have hadm : ∀ w, ε ^ 4 * adm D ε r n₀ μ w ≠ 0 → w ∈ QF ε n₀ (r + 1) := fun w hw => by
      refine (mem_QF hε).2 ?_
      by_contra h
      apply hw; unfold adm; rw [if_neg (fun hh => h hh.1)]; ring
    have hb : ∀ e, ∑ z ∈ T', ε ^ 4 * adm D ε r n₀ μ (z + e) ≤ A μ := fun e => by
      rw [sum_shift_eq_map (F := fun w => ε ^ 4 * adm D ε r n₀ μ w)]
      exact sum_le_of_supp (fun w _ => mul_nonneg he4 (adm_nonneg D μ w)) fun w _ hw => hadm w hw
    have hb' : ∀ e, ∑ z ∈ T', ε ^ 4 * adm D ε r n₀ μ (z + e - e4 μ) ≤ A μ := fun e => by
      have := hb (e - e4 μ)
      simpa only [add_sub_assoc] using this
    calc ∑ e ∈ Eoff, ∑ z ∈ T', ε ^ 4 * adm D ε r n₀ μ (z + e) + ∑ e ∈ Eoff, ∑ z ∈ T', ε ^ 4 * adm D ε r n₀ μ (z + e - e4 μ)
        ≤ ∑ _e ∈ Eoff, A μ + ∑ _e ∈ Eoff, A μ := add_le_add (sum_le_sum fun e _ => hb e) (sum_le_sum fun e _ => hb' e)
      _ = 162 * A μ := by rw [sum_const, card_Eoff, nsmul_eq_mul]; norm_num; ring
  have hAeq : ∑ μ, A μ = ∑ μ, ∑ z ∈ (QF ε n₀ (r + 1)).filter (fun z => InQr ε n₀ (r + 1) (z + e4 μ)),
      ε ^ 4 * ‖dfw ε μ D.u z‖ ^ 2 := by
    refine sum_congr rfl fun μ _ => ?_
    simp only [hA, sum_filter]
    refine sum_congr rfl fun z hz => ?_
    unfold adm
    have := (mem_QF hε).1 hz
    by_cases h : InQr ε n₀ (r + 1) (z + e4 μ)
    · rw [if_pos ⟨this, h⟩, if_pos h]
    · rw [if_neg (fun hh => h hh.2), if_neg h, mul_zero]
  have hsumA : ∑ μ, Real.sqrt (A μ) ≤ 2 * Real.sqrt (∑ μ, A μ) := by
    have := Real.sum_mul_le_sqrt_mul_sqrt univ (fun _ : Fin 4 => (1 : ℝ)) (fun μ => Real.sqrt (A μ))
    simp only [one_mul, one_pow, sum_const, card_univ, Fintype.card_fin, Real.sq_sqrt (hA0 _)] at this
    have h4 : Real.sqrt ((4 : ℕ) • (1 : ℝ)) = 2 := by
      rw [nsmul_eq_mul, show ((4 : ℕ) : ℝ) * 1 = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rwa [h4] at this
  have h162 : Real.sqrt 162 ≤ 13 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hU := wN_nonneg (s := QF ε n₀ (r + 1)) (w := fun _ => ε ^ 4) (fun z => ‖D.u z‖)
  have hdU := Real.sqrt_nonneg (∑ μ, A μ)
  rw [← hAeq]
  calc _ ≤ wN T' (fun _ => ε ^ 4) (fun z => ‖D.h z‖) + 221 * wN T' (fun _ => ε ^ 4) (S2 D) +
        10 * ∑ μ, wN T' (fun _ => ε ^ 4) (Dm D ε r n₀ μ) := hstep1.trans hstep2
    _ ≤ wN (QF ε n₀ (r + 1)) (fun _ => ε ^ 4) (fun z => ‖D.h z‖) +
        221 * (9 * wN (QF ε n₀ (r + 1)) (fun _ => ε ^ 4) (fun z => ‖D.u z‖)) +
        10 * (Real.sqrt 162 * (2 * Real.sqrt (∑ μ, A μ))) := by
        gcongr
        calc ∑ μ, wN T' (fun _ => ε ^ 4) (Dm D ε r n₀ μ) ≤ ∑ μ, Real.sqrt 162 * Real.sqrt (A μ) :=
              sum_le_sum fun μ _ => hDm μ
          _ = Real.sqrt 162 * ∑ μ, Real.sqrt (A μ) := by rw [mul_sum]
          _ ≤ Real.sqrt 162 * (2 * Real.sqrt (∑ μ, A μ)) := mul_le_mul_of_nonneg_left hsumA (Real.sqrt_nonneg _)
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right h162 hdU]

end LocalLaplacian
end CoreLean

end
