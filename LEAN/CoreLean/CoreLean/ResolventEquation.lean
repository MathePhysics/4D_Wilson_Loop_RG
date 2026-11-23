/-
`G₁ = (Δ + 1)⁻¹` on the bounded functions (the first sentence of the proof of `prop:free-schauder`
of BALABAN_CORE.tex): `(Δ + 1) G₁ r = r`, and a bounded function `u` with `(Δ + 1) u = 0` vanishes.

The equation is proved through the kernel `k(z) = ∫_0^∞ e^{-t} p_{t/ε²}(z) dt`, which satisfies
`(Δ + 1) k = δ` by the fundamental theorem of calculus applied to `t ↦ e^{-t} p_{t/ε²}(z)` and the heat
equation `∂_t p_t = -Δ p_t` (`Balaban.LatticeGreen.hasDerivAt_heatKernel`), as in
`Balaban.LatticeGreen.latticeGreen_equation`.
-/
import CoreLean.FreeSchauder

open MeasureTheory Real Balaban.LatticeGreen Filter Topology Set

namespace CoreLean

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
variable {ε : ℝ}

/-- `Δ = Σ_μ ∂^*_μ ∂_μ` (`def:differences`(iv)) on `εℤ⁴`. -/
noncomputable def lap (ε : ℝ) (u : (Fin 4 → ℤ) → V) (n : Fin 4 → ℤ) : V :=
  ∑ μ, dbw ε μ (dfw ε μ u) n

lemma lap_eq (u : (Fin 4 → ℤ) → V) (n : Fin 4 → ℤ) :
    lap ε u n = (ε ^ 2)⁻¹ • ∑ μ, ((2 : ℝ) • u n - u (n + e4 μ) - u (n - e4 μ)) := by
  unfold lap dbw dfw
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [sub_add_cancel, show (ε ^ 2)⁻¹ = ε⁻¹ * ε⁻¹ by rw [sq, mul_inv]]
  module

/-! ### Uniqueness -/

/-- A bounded function with `(Δ + 1) u = 0` vanishes. -/
theorem eq_zero_of_lap_add (hε : 0 < ε) {u : (Fin 4 → ℤ) → V} {B : ℝ} (hu : ∀ n, ‖u n‖ ≤ B)
    (h : ∀ n, lap ε u n + u n = 0) (n : Fin 4 → ℤ) : u n = 0 := by
  set θ := 8 / (ε ^ 2 + 8) with hθ
  have hε2 : 0 < ε ^ 2 := by positivity
  have hθ0 : 0 ≤ θ := by positivity
  have hθ1 : θ < 1 := by rw [hθ, div_lt_one (by positivity)]; linarith
  -- `(ε² + 8) u(n) = Σ_μ (u(n + e_μ) + u(n - e_μ))`
  have hrel : ∀ n, (ε ^ 2 + 8) • u n = ∑ μ : Fin 4, (u (n + e4 μ) + u (n - e4 μ)) := by
    intro n
    have hS : ∑ μ : Fin 4, ((2 : ℝ) • u n - u (n + e4 μ) - u (n - e4 μ)) =
        (8 : ℝ) • u n - ∑ μ : Fin 4, (u (n + e4 μ) + u (n - e4 μ)) := by
      simp only [Fin.sum_univ_four]; module
    have h1 := h n
    rw [lap_eq, hS] at h1
    have h2 : (8 : ℝ) • u n - ∑ μ : Fin 4, (u (n + e4 μ) + u (n - e4 μ)) + ε ^ 2 • u n = 0 := by
      have := congrArg (fun v => ε ^ 2 • v) h1
      simpa only [smul_add, smul_smul, mul_inv_cancel₀ hε2.ne', one_smul, smul_zero] using this
    calc (ε ^ 2 + 8) • u n = ((8 : ℝ) • u n -
          ∑ μ : Fin 4, (u (n + e4 μ) + u (n - e4 μ)) + ε ^ 2 • u n) +
          ∑ μ : Fin 4, (u (n + e4 μ) + u (n - e4 μ)) := by
          rw [add_smul]; abel
      _ = ∑ μ : Fin 4, (u (n + e4 μ) + u (n - e4 μ)) := by rw [h2, zero_add]
  -- iterate `‖u‖ ≤ θ ‖u‖`
  have hstep : ∀ C : ℝ, (∀ n, ‖u n‖ ≤ C) → ∀ n, ‖u n‖ ≤ θ * C := by
    intro C hC n
    have h1 : (ε ^ 2 + 8) * ‖u n‖ ≤ 8 * C := by
      have := congrArg norm (hrel n)
      rw [norm_smul, Real.norm_of_nonneg (by positivity)] at this
      rw [this]
      calc ‖∑ μ : Fin 4, (u (n + e4 μ) + u (n - e4 μ))‖ ≤ ∑ _μ : Fin 4, (C + C) :=
            (norm_sum_le _ _).trans (Finset.sum_le_sum fun μ _ =>
              (norm_add_le _ _).trans (add_le_add (hC _) (hC _)))
        _ = 8 * C := by simp; ring
    rw [hθ, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    linarith
  have hiter : ∀ k : ℕ, ∀ n, ‖u n‖ ≤ θ ^ k * B := by
    intro k
    induction k with
    | zero => simpa using hu
    | succ k ih =>
      intro n
      have := hstep _ ih n
      rwa [pow_succ, mul_comm (θ ^ k) θ, mul_assoc]
  have hlim : Tendsto (fun k : ℕ => θ ^ k * B) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hθ0 hθ1).mul_const B
  have : ‖u n‖ ≤ 0 := ge_of_tendsto' hlim fun k => hiter k n
  exact norm_le_zero_iff.mp this

/-! ### The kernel of `G₁` -/

/-- `k(z) = ∫_0^∞ e^{-t} p_{t/ε²}(z) dt`. -/
noncomputable def resKernel (ε : ℝ) (z : Fin 4 → ℤ) : ℝ :=
  ∫ t in Ioi 0, Real.exp (-t) * heatKernel 4 (t / ε ^ 2) z

lemma heatKernel4_le_one {s : ℝ} (hs : 0 ≤ s) (z : Fin 4 → ℤ) : heatKernel 4 s z ≤ 1 := by
  unfold heatKernel
  rw [Fin.prod_univ_four]
  have h0 := fun n : ℤ => heatKernel1_nonneg hs n
  have h1 := fun n : ℤ => (le_abs_self _).trans (heatKernel1_abs_le_one hs n)
  exact mul_le_one₀ (mul_le_one₀ (mul_le_one₀ (h1 _) (h0 _) (h1 _)) (h0 _) (h1 _)) (h0 _) (h1 _)

lemma integrableOn_exp_neg_heatKernel (z : Fin 4 → ℤ) :
    IntegrableOn (fun t => Real.exp (-t) * heatKernel 4 (t / ε ^ 2) z) (Ioi 0) := by
  refine Integrable.mono' (integrableOn_exp_neg.mul_const 1)
    ((Continuous.aestronglyMeasurable (by fun_prop)).mul
      (((continuous_heatKernel z).comp (continuous_id.div_const _)).aestronglyMeasurable)) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
  have hs : 0 ≤ t / ε ^ 2 := by have : 0 < t := ht; positivity
  rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (heatKernel4_nonneg hs z))]
  exact mul_le_mul_of_nonneg_left (heatKernel4_le_one hs z) (Real.exp_pos _).le

lemma resKernel_nonneg (z : Fin 4 → ℤ) : 0 ≤ resKernel ε z :=
  setIntegral_nonneg measurableSet_Ioi fun t ht =>
    mul_nonneg (Real.exp_pos _).le (heatKernel4_nonneg (by have : 0 < t := ht; positivity) z)

/-- `Σ_z k(z) ≤ 1`, so `k` is summable. -/
lemma summable_resKernel : Summable (resKernel ε) := by
  refine summable_of_sum_le (c := 1) (fun z => resKernel_nonneg z) fun S => ?_
  unfold resKernel
  rw [← integral_finsetSum S fun z _ => integrableOn_exp_neg_heatKernel z]
  calc ∫ t in Ioi 0, ∑ z ∈ S, Real.exp (-t) * heatKernel 4 (t / ε ^ 2) z
      ≤ ∫ t in Ioi 0, Real.exp (-t) := by
        refine setIntegral_mono_on (integrable_finsetSum S fun z _ =>
          integrableOn_exp_neg_heatKernel z) integrableOn_exp_neg measurableSet_Ioi
          fun t ht => ?_
        have hs : 0 ≤ t / ε ^ 2 := by have : 0 < t := ht; positivity
        rw [← Finset.mul_sum]
        refine mul_le_of_le_one_right (Real.exp_pos _).le ?_
        have hsum := hasSum_heatKernel4 hs
        rw [← hsum.tsum_eq]
        exact hsum.summable.sum_le_tsum S fun z _ => heatKernel4_nonneg hs z
    _ = 1 := by simpa using integral_exp_neg_Ioi 0

/-! ### `(Δ + 1) k = δ` -/

/-- The derivative of `t ↦ p_{t/ε²}(z)`. -/
lemma hasDerivAt_heatKernel_scaled (z : Fin 4 → ℤ) (t : ℝ) :
    HasDerivAt (fun s => heatKernel 4 (s / ε ^ 2) z)
      (-((ε ^ 2)⁻¹ * heatLaplacian 4 (t / ε ^ 2) z)) t := by
  have h1 : HasDerivAt (fun s : ℝ => s / ε ^ 2) (ε ^ 2)⁻¹ t := by
    simpa [div_eq_mul_inv] using (hasDerivAt_id t).div_const (ε ^ 2)
  have h0 : HasDerivAt (fun s => heatKernel 4 s z) (-heatLaplacian 4 (t / ε ^ 2) z) (t / ε ^ 2) :=
    hasDerivAt_heatKernel (t / ε ^ 2) z
  have h2 : HasDerivAt ((fun s => heatKernel 4 s z) ∘ fun s : ℝ => s / ε ^ 2)
      (-heatLaplacian 4 (t / ε ^ 2) z * (ε ^ 2)⁻¹) t := h0.comp t h1
  exact h2.congr_deriv (by ring)

/-- `|Δ p_s(z)| ≤ 16`. -/
lemma abs_heatLaplacian_le {s : ℝ} (hs : 0 ≤ s) (z : Fin 4 → ℤ) :
    |heatLaplacian 4 s z| ≤ 16 := by
  unfold heatLaplacian
  calc |∑ μ : Fin 4, (2 * heatKernel 4 s z - heatKernel 4 s (z + Pi.single μ 1) -
        heatKernel 4 s (z - Pi.single μ 1))| ≤ ∑ _μ : Fin 4, (4 : ℝ) := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun μ _ => ?_)
        have h0 := heatKernel4_le_one hs z
        have h1 := heatKernel4_le_one hs (z + Pi.single μ 1)
        have h2 := heatKernel4_le_one hs (z - Pi.single μ 1)
        have g0 := heatKernel4_nonneg hs z
        have g1 := heatKernel4_nonneg hs (z + Pi.single μ 1)
        have g2 := heatKernel4_nonneg hs (z - Pi.single μ 1)
        rw [abs_le]; constructor <;> linarith
    _ = 16 := by simp; norm_num

lemma integrableOn_exp_neg_heatLaplacian (z : Fin 4 → ℤ) :
    IntegrableOn (fun t => Real.exp (-t) * heatLaplacian 4 (t / ε ^ 2) z) (Ioi 0) := by
  refine Integrable.mono' (integrableOn_exp_neg.mul_const 16)
    ((Continuous.aestronglyMeasurable (by fun_prop)).mul
      (((continuous_heatLaplacian z).comp (continuous_id.div_const _)).aestronglyMeasurable)) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
  have hs : 0 ≤ t / ε ^ 2 := by have : 0 < t := ht; positivity
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left (abs_heatLaplacian_le hs z) (Real.exp_pos _).le

/-- `∫ e^{-t} Δ p_{t/ε²}(z) dt = Σ_μ (2k(z) - k(z + e_μ) - k(z - e_μ))`. -/
lemma integral_exp_neg_heatLaplacian (z : Fin 4 → ℤ) :
    ∫ t in Ioi 0, Real.exp (-t) * heatLaplacian 4 (t / ε ^ 2) z =
      ∑ μ : Fin 4, (2 * resKernel ε z - resKernel ε (z + e4 μ) - resKernel ε (z - e4 μ)) := by
  have hI := fun y : Fin 4 → ℤ => integrableOn_exp_neg_heatKernel (ε := ε) y
  -- each term `2k(z) - k(z+e) - k(z-e)` is the integral of `e^{-t}(2p(z) - p(z+e) - p(z-e))`
  have hμ : ∀ μ : Fin 4, 2 * resKernel ε z - resKernel ε (z + e4 μ) - resKernel ε (z - e4 μ) =
      ∫ t in Ioi 0, (2 * (Real.exp (-t) * heatKernel 4 (t / ε ^ 2) z) -
        Real.exp (-t) * heatKernel 4 (t / ε ^ 2) (z + e4 μ)) -
        Real.exp (-t) * heatKernel 4 (t / ε ^ 2) (z - e4 μ) := fun μ => by
    rw [integral_sub, integral_sub, integral_const_mul]
    · rfl
    · exact (hI z).const_mul 2
    · exact hI _
    · exact ((hI z).const_mul 2).sub (hI _)
    · exact hI _
  have hint : ∀ μ : Fin 4, IntegrableOn (fun t => (2 * (Real.exp (-t) * heatKernel 4 (t / ε ^ 2) z) -
        Real.exp (-t) * heatKernel 4 (t / ε ^ 2) (z + e4 μ)) -
        Real.exp (-t) * heatKernel 4 (t / ε ^ 2) (z - e4 μ)) (Ioi 0) := fun μ =>
    (((hI z).const_mul 2).sub (hI _)).sub (hI _)
  simp_rw [hμ]
  rw [← integral_finsetSum _ fun μ _ => hint μ]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [heatLaplacian, Finset.mul_sum, e4]
  refine Finset.sum_congr rfl fun μ _ => ?_
  ring

/-- `(Δ + 1) k = δ`: `k(z) + ε⁻² Σ_μ (2k(z) - k(z + e_μ) - k(z - e_μ)) = δ_{z0}`. -/
theorem resKernel_equation (hε : 0 < ε) (z : Fin 4 → ℤ) :
    resKernel ε z + (ε ^ 2)⁻¹ * ∑ μ : Fin 4, (2 * resKernel ε z - resKernel ε (z + e4 μ) -
      resKernel ε (z - e4 μ)) = if z = 0 then 1 else 0 := by
  have hI := integrableOn_exp_neg_heatKernel (ε := ε) z
  have hL := integrableOn_exp_neg_heatLaplacian (ε := ε) z
  set F : ℝ → ℝ := fun t => Real.exp (-t) * heatKernel 4 (t / ε ^ 2) z with hF
  set F' : ℝ → ℝ := fun t => -(Real.exp (-t) * heatKernel 4 (t / ε ^ 2) z) +
    -((ε ^ 2)⁻¹ * (Real.exp (-t) * heatLaplacian 4 (t / ε ^ 2) z)) with hF'
  have hderiv : ∀ t, HasDerivAt F (F' t) t := fun t => by
    have h2 := ((hasDerivAt_neg t).exp).mul (hasDerivAt_heatKernel_scaled (ε := ε) z t)
    refine h2.congr_deriv ?_
    simp only [hF']; ring
  have hF'int : IntegrableOn F' (Ioi 0) := hI.neg.add (hL.const_mul _).neg
  have hlim : Tendsto F atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (Real.tendsto_exp_neg_atTop_nhds_zero)
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    have hs : 0 ≤ t / ε ^ 2 := by positivity
    rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (heatKernel4_nonneg hs z))]
    exact mul_le_of_le_one_right (Real.exp_pos _).le (heatKernel4_le_one hs z)
  have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto (a := 0) (m := 0)
    ((hderiv 0).continuousAt.continuousWithinAt) (fun t _ => hderiv t) hF'int hlim
  have hF0 : F 0 = if z = 0 then 1 else 0 := by
    simp only [hF, neg_zero, Real.exp_zero, one_mul, zero_div, heatKernel_zero_time]
  have hsplit : ∫ t in Ioi 0, F' t = -resKernel ε z +
      -((ε ^ 2)⁻¹ * ∫ t in Ioi 0, Real.exp (-t) * heatLaplacian 4 (t / ε ^ 2) z) := by
    have hA : IntegrableOn (fun t => -(Real.exp (-t) * heatKernel 4 (t / ε ^ 2) z)) (Ioi 0) :=
      hI.neg
    have hB : IntegrableOn (fun t => -((ε ^ 2)⁻¹ *
        (Real.exp (-t) * heatLaplacian 4 (t / ε ^ 2) z))) (Ioi 0) := (hL.const_mul _).neg
    simp only [hF']
    rw [integral_add hA hB, integral_neg, integral_neg, integral_const_mul]
    rfl
  rw [hsplit, hF0, integral_exp_neg_heatLaplacian] at hFTC
  linarith

/-! ### The equation `(Δ + 1) G₁ r = r` -/

/-- `G₁ r (n) = Σ_z k(z) r(n - z)`. -/
theorem resolvent_eq_tsum {r : (Fin 4 → ℤ) → V} {M : ℝ} (hr : ∀ n, ‖r n‖ ≤ M)
    (n : Fin 4 → ℤ) : resolvent ε r n = ∑' z, resKernel ε z • r (n - z) := by
  set F : (Fin 4 → ℤ) → ℝ → V := fun z t => (Real.exp (-t) * heatKernel 4 (t / ε ^ 2) z) •
    r (n - z) with hF
  have hFint : ∀ z, Integrable (F z) (volume.restrict (Ioi 0)) := fun z =>
    (integrableOn_exp_neg_heatKernel z).smul_const _
  have hFnorm : ∀ z, ∫ t in Ioi 0, ‖F z t‖ ≤ resKernel ε z * M := fun z => by
    unfold resKernel
    rw [← integral_mul_const]
    refine setIntegral_mono_on (hFint z).norm ((integrableOn_exp_neg_heatKernel z).mul_const M)
      measurableSet_Ioi fun t ht => ?_
    have hp := heatKernel4_nonneg (s := t / ε ^ 2) (by have : 0 < t := ht; positivity) z
    simp only [hF]
    rw [norm_smul, Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le hp)]
    exact mul_le_mul_of_nonneg_left (hr _) (mul_nonneg (Real.exp_pos _).le hp)
  have hsum : Summable fun z => ∫ t in Ioi 0, ‖F z t‖ :=
    Summable.of_nonneg_of_le (fun z => integral_nonneg fun t => norm_nonneg _) hFnorm
      ((summable_resKernel).mul_right M)
  have h := integral_tsum_of_summable_integral_norm hFint hsum
  unfold resolvent
  have hl : ∫ t in Ioi 0, Real.exp (-t) • heatOp ε t r n = ∫ t in Ioi 0, ∑' z, F z t := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    unfold heatOp
    rw [← tsum_const_smul'']
    refine tsum_congr fun z => ?_
    simp only [hF, smul_smul]
  rw [hl, ← h]
  refine tsum_congr fun z => ?_
  simp only [hF]
  rw [integral_smul_const]
  rfl

/-- `(Δ + 1) G₁ r = r`: `G₁ = (Δ + 1)⁻¹` on the bounded functions. -/
theorem lap_resolvent_add (hε : 0 < ε) {r : (Fin 4 → ℤ) → V} {M : ℝ} (hr : ∀ n, ‖r n‖ ≤ M)
    (n : Fin 4 → ℤ) : lap ε (resolvent ε r) n + resolvent ε r n = r n := by
  have hk := summable_resKernel (ε := ε)
  have hks : ∀ m, Summable fun z => resKernel ε z • r (m - z) := fun m =>
    Summable.of_norm_bounded (hk.mul_right M) fun z => by
      rw [norm_smul, Real.norm_of_nonneg (resKernel_nonneg z)]
      exact mul_le_mul_of_nonneg_left (hr _) (resKernel_nonneg z)
  -- shifted representations: `G₁ r (n + a) = Σ_z k(z + a) r(n - z)`
  have hshift : ∀ a : Fin 4 → ℤ, resolvent ε r (n + a) = ∑' z, resKernel ε (z + a) • r (n - z) ∧
      Summable fun z => resKernel ε (z + a) • r (n - z) := fun a => by
    have hsa : Summable fun z => resKernel ε (z + a) • r (n - z) := by
      have := (Equiv.addRight a).summable_iff.mpr (hks (n + a))
      refine this.congr fun z => ?_
      simp only [Function.comp_apply, Equiv.coe_addRight]
      rw [show n + a - (z + a) = n - z by abel]
    refine ⟨?_, hsa⟩
    rw [resolvent_eq_tsum hr, ← (Equiv.addRight a).tsum_eq]
    refine tsum_congr fun z => ?_
    simp only [Equiv.coe_addRight]
    rw [show n + a - (z + a) = n - z by abel]
  have hp := fun μ : Fin 4 => hshift (e4 μ)
  have hm := fun μ : Fin 4 => hshift (-e4 μ)
  have hsμ : ∀ μ : Fin 4, Summable fun z => (2 * resKernel ε z - resKernel ε (z + e4 μ) -
      resKernel ε (z + -e4 μ)) • r (n - z) := fun μ =>
    ((((hks n).const_smul (2 : ℝ)).sub (hp μ).2).sub (hm μ).2).congr fun z => by
      rw [sub_smul, sub_smul, mul_smul]
  have hterm : ∀ μ : Fin 4, (2 : ℝ) • resolvent ε r n - resolvent ε r (n + e4 μ) -
      resolvent ε r (n - e4 μ) = ∑' z, (2 * resKernel ε z - resKernel ε (z + e4 μ) -
        resKernel ε (z + -e4 μ)) • r (n - z) := fun μ => by
    rw [sub_eq_add_neg n, (hp μ).1, (hm μ).1, resolvent_eq_tsum hr n, ← tsum_const_smul'',
      ← ((hks n).const_smul (2 : ℝ)).tsum_sub (hp μ).2,
      ← (((hks n).const_smul (2 : ℝ)).sub (hp μ).2).tsum_sub (hm μ).2]
    refine tsum_congr fun z => ?_
    rw [sub_smul, sub_smul, mul_smul]
  rw [lap_eq]
  simp_rw [hterm]
  rw [← Summable.tsum_finsetSum (fun μ _ => hsμ μ), ← tsum_const_smul'', resolvent_eq_tsum hr n,
    ← ((summable_sum fun μ _ => hsμ μ).const_smul _).tsum_add (hks n)]
  have hδ : ∀ z, (ε ^ 2)⁻¹ • ∑ μ : Fin 4, (2 * resKernel ε z - resKernel ε (z + e4 μ) -
      resKernel ε (z + -e4 μ)) • r (n - z) + resKernel ε z • r (n - z) =
      (if z = 0 then (1 : ℝ) else 0) • r (n - z) := fun z => by
    rw [← resKernel_equation hε z, ← Finset.sum_smul, smul_smul, ← add_smul, add_comm]
    simp only [← sub_eq_add_neg]
  simp_rw [hδ]
  rw [tsum_eq_single 0 (fun z hz => by simp [hz])]
  simp

lemma lap_sub (u v : (Fin 4 → ℤ) → V) (n : Fin 4 → ℤ) :
    lap ε (fun m => u m - v m) n = lap ε u n - lap ε v n := by
  rw [lap_eq, lap_eq, lap_eq, ← smul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [smul_sub]; abel

/-- `G₁ = (Δ + 1)⁻¹`: every bounded `u` with `(Δ + 1) u = r` is `G₁ r`. -/
theorem eq_resolvent (hε : 0 < ε) {r : (Fin 4 → ℤ) → V} {M : ℝ} (hr : ∀ n, ‖r n‖ ≤ M)
    {u : (Fin 4 → ℤ) → V} {B : ℝ} (hu : ∀ n, ‖u n‖ ≤ B) (h : ∀ n, lap ε u n + u n = r n) :
    u = resolvent ε r := by
  funext n
  have hz := eq_zero_of_lap_add hε (u := fun m => u m - resolvent ε r m) (B := B + M)
    (fun m => (norm_sub_le _ _).trans (add_le_add (hu m) (norm_resolvent_le hr m)))
    (fun m => by
      rw [lap_sub, show ∀ a b c d : V, a - b + (c - d) = (a + c) - (b + d) from
        fun a b c d => by abel, h m, lap_resolvent_add hε hr m, sub_self]) n
  exact sub_eq_zero.mp hz

end CoreLean
