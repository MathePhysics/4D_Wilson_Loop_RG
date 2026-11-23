/-
`prop:free-schauder` of BALABAN_CORE.tex: the bounds of `G₁ = ∫_0^∞ e^{-t} P_t dt`, uniformly in `ε`.

`G₁` is `CoreLean.resolvent`. That it is `(Δ + 1)⁻¹` on the bounded functions is the first sentence
of the core's proof; it is proved in `CoreLean.ResolventEquation`.
-/
import CoreLean.FreeSchauderBasics

open MeasureTheory Real Balaban.LatticeGreen Filter Topology Set

namespace CoreLean

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
variable {ε : ℝ}

/-- `C_S(β) = c₀ m₁ (8/β + 12/(1-β))` (`eq:schauder-constants`). -/
noncomputable def CS (β : ℝ) : ℝ := c0 * m1 * (8 / β + 12 / (1 - β))
/-- `C'_S(β) = 4 + 4/(1-β)` (`eq:schauder-constants`). -/
noncomputable def CS' (β : ℝ) : ℝ := 4 + 4 / (1 - β)

/-- Measurability of differences of a measurable family. -/
lemma aestronglyMeasurable_dif {g : ℝ → (Fin 4 → ℤ) → V}
    (hg : ∀ k, AEStronglyMeasurable (fun t => g t k) (volume.restrict (Ioi 0))) (b : Bool)
    (μ : Fin 4) (n : Fin 4 → ℤ) :
    AEStronglyMeasurable (fun t => dif ε b μ (g t) n) (volume.restrict (Ioi 0)) := by
  cases b
  · simp only [dif, Bool.false_eq_true, ↓reduceIte, dbw]
    exact ((hg _).sub (hg _)).const_smul _
  · simp only [dif, ↓reduceIte, dfw]
    exact ((hg _).sub (hg _)).const_smul _

lemma aestronglyMeasurable_heatOp_family {r : (Fin 4 → ℤ) → V} {M : ℝ} (hr : ∀ n, ‖r n‖ ≤ M) :
    ∀ k, AEStronglyMeasurable (fun t => heatOp ε t r k) (volume.restrict (Ioi 0)) :=
  fun k => aestronglyMeasurable_heatOp hr k

/-- `l1 m = 0` only for `m = 0`. -/
lemma l1_eq_zero {m : Fin 4 → ℤ} (h : l1 m = 0) : m = 0 := by
  unfold l1 at h
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg (fun μ _ => abs_nonneg _)).mp h
  funext μ
  have := h0 μ (Finset.mem_univ μ)
  simpa using this

lemma c0_mul_sqrt_pi : c0 * Real.sqrt π ≤ 2 := by
  unfold c0
  rw [div_mul_eq_mul_div, Real.mul_self_sqrt Real.pi_pos.le]
  linarith [Real.pi_lt_four]

/-- The integrand of a difference of `D G₁ r` is integrable, with the bound `c₀ t^{-1/2} M`. -/
lemma integrableOn_dif_heatOp (hε : 0 < ε) {r : (Fin 4 → ℤ) → V} {M : ℝ} (hr : ∀ n, ‖r n‖ ≤ M)
    (b : Bool) (μ : Fin 4) (k : Fin 4 → ℤ) :
    IntegrableOn (fun t => Real.exp (-t) • dif ε b μ (heatOp ε t r) k) (Ioi 0) := by
  refine Integrable.mono' (integrableOn_exp_neg_inv_sqrt.mul_const (c0 * M))
    ((Continuous.aestronglyMeasurable (by fun_prop)).smul
      (aestronglyMeasurable_dif_heatOp hr b μ k)) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
  rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
  have := norm_dif_heatOp_le hε ht hr b μ k
  calc Real.exp (-t) * ‖dif ε b μ (heatOp ε t r) k‖ ≤ Real.exp (-t) * (c0 / Real.sqrt t * M) :=
        mul_le_mul_of_nonneg_left this (Real.exp_pos _).le
    _ = Real.exp (-t) * (Real.sqrt t)⁻¹ * (c0 * M) := by ring

/-! ### `prop:free-schauder`(i) -/

/-- `‖G₁ r‖_∞ ≤ ‖r‖_∞`. -/
theorem norm_resolvent_le {r : (Fin 4 → ℤ) → V} {M : ℝ} (hr : ∀ n, ‖r n‖ ≤ M) (n : Fin 4 → ℤ) :
    ‖resolvent ε r n‖ ≤ M := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hr 0)
  unfold resolvent
  calc ‖∫ t in Ioi 0, Real.exp (-t) • heatOp ε t r n‖ ≤ ∫ t in Ioi 0, Real.exp (-t) * M := by
        refine norm_integral_le_of_norm_le (integrableOn_exp_neg.mul_const M) ?_
        refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
        rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
        exact mul_le_mul_of_nonneg_left (norm_heatOp_le (le_of_lt ht) hr n) (Real.exp_pos _).le
    _ = M := by
        rw [integral_mul_const]
        have := integral_exp_neg_Ioi 0
        simp only [neg_zero, Real.exp_zero] at this
        rw [this, one_mul]

/-- `D G₁ r = ∫ e^{-t} D P_t r dt`. -/
lemma dif_resolvent {r : (Fin 4 → ℤ) → V} {M : ℝ} (hr : ∀ n, ‖r n‖ ≤ M) (b : Bool) (μ : Fin 4)
    (n : Fin 4 → ℤ) :
    dif ε b μ (resolvent ε r) n = ∫ t in Ioi 0, Real.exp (-t) • dif ε b μ (heatOp ε t r) n :=
  dif_integral (fun k => integrableOn_resolvent hr k) b μ n

/-- `‖𝒟 G₁ r‖_∞ ≤ 2 ‖r‖_∞`. -/
theorem norm_dif_resolvent_le (hε : 0 < ε) {r : (Fin 4 → ℤ) → V} {M : ℝ} (hr : ∀ n, ‖r n‖ ≤ M)
    (b : Bool) (μ : Fin 4) (n : Fin 4 → ℤ) : ‖dif ε b μ (resolvent ε r) n‖ ≤ 2 * M := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hr 0)
  rw [dif_resolvent hr]
  calc ‖∫ t in Ioi 0, Real.exp (-t) • dif ε b μ (heatOp ε t r) n‖
      ≤ ∫ t in Ioi 0, Real.exp (-t) * (Real.sqrt t)⁻¹ * (c0 * M) := by
        refine norm_integral_le_of_norm_le (integrableOn_exp_neg_inv_sqrt.mul_const _) ?_
        refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
        rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
        calc Real.exp (-t) * ‖dif ε b μ (heatOp ε t r) n‖ ≤ Real.exp (-t) * (c0 / Real.sqrt t * M) :=
              mul_le_mul_of_nonneg_left (norm_dif_heatOp_le hε ht hr b μ n) (Real.exp_pos _).le
          _ = _ := by ring
    _ = c0 * Real.sqrt π * M := by rw [integral_mul_const, integral_exp_neg_inv_sqrt]; ring
    _ ≤ 2 * M := mul_le_mul_of_nonneg_right c0_mul_sqrt_pi hM

/-- The constants of the third bound of (i): `4c₀ + 2c₀² + 4c₀²/(e(1-β)) ≤ C'_S(β)`. -/
lemma constants_first {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    4 * c0 + 2 * c0 ^ 2 + 4 * c0 ^ 2 / (Real.exp 1 * (1 - β)) ≤ CS' β := by
  have h1β : 0 < 1 - β := by linarith
  have hc2 : c0 ^ 2 = π / 4 := by unfold c0; rw [div_pow, Real.sq_sqrt Real.pi_pos.le]; norm_num
  have hpi := Real.pi_lt_d2
  have hpi0 := Real.pi_pos
  have hsq : Real.sqrt π ≤ 1.78 := by
    rw [Real.sqrt_le_left (by norm_num)]; nlinarith
  have hc0 : 4 * c0 ≤ 3.56 := by unfold c0; linarith
  have he := Real.exp_one_gt_d9
  have hu : 1 ≤ 1 / (1 - β) := by rw [le_div_iff₀ h1β]; linarith
  have hfrac : 4 * c0 ^ 2 / (Real.exp 1 * (1 - β)) ≤ 1.17 * (1 / (1 - β)) := by
    rw [hc2, div_mul_eq_div_div_swap, show 4 * (π / 4) = π by ring]
    rw [div_div, one_div, ← div_eq_mul_inv]
    rw [div_le_div_iff₀ (by positivity) h1β]
    nlinarith
  unfold CS'
  rw [hc2] at *
  have : 4 / (1 - β) = 4 * (1 / (1 - β)) := by ring
  rw [this]
  nlinarith

/-- `prop:free-schauder`(i), the third bound:
`‖(𝒟 G₁ r)(x + z) - (𝒟 G₁ r)(x)‖ ≤ C'_S(β) ‖r‖_∞ |z|₁^β` for `0 < β < 1`. -/
theorem norm_dif_resolvent_sub_le (hε : 0 < ε) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    {r : (Fin 4 → ℤ) → V} {M : ℝ} (hr : ∀ n, ‖r n‖ ≤ M) (b : Bool) (μ : Fin 4)
    (n m : Fin 4 → ℤ) :
    ‖dif ε b μ (resolvent ε r) (n + m) - dif ε b μ (resolvent ε r) n‖ ≤
      CS' β * M * (ε * l1 m) ^ β := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hr 0)
  set d := ε * l1 m with hd
  have hd0 : 0 ≤ d := mul_nonneg hε.le (l1_nonneg m)
  have hCS' : 4 ≤ CS' β := by
    unfold CS'; have : 0 ≤ 4 / (1 - β) := div_nonneg (by norm_num) (by linarith); linarith
  rcases eq_or_lt_of_le hd0 with h0 | hdpos
  · -- `z = 0`
    have hl : l1 m = 0 := by
      rcases mul_eq_zero.mp h0.symm with h | h
      · exact absurd h hε.ne'
      · exact h
    rw [l1_eq_zero hl, add_zero, sub_self, norm_zero]
    exact mul_nonneg (mul_nonneg (by linarith) hM) (Real.rpow_nonneg hd0 _)
  rcases le_or_gt d 1 with hd1 | hd1
  swap
  · -- `|z|₁ > 1`: the two values separately
    have h1 : 1 ≤ d ^ β := Real.one_le_rpow hd1.le hβ0.le
    calc ‖dif ε b μ (resolvent ε r) (n + m) - dif ε b μ (resolvent ε r) n‖
        ≤ 2 * M + 2 * M := (norm_sub_le _ _).trans (add_le_add (norm_dif_resolvent_le hε hr b μ _)
          (norm_dif_resolvent_le hε hr b μ _))
      _ = 4 * M * 1 := by ring
      _ ≤ CS' β * M * d ^ β := mul_le_mul (mul_le_mul_of_nonneg_right hCS' hM) h1 zero_le_one
          (mul_nonneg (by linarith) hM)
  -- `0 < |z|₁ ≤ 1`: split the time integral at `τ = |z|₁²`
  set τ := d ^ 2 with hτ
  have hτ0 : 0 < τ := by positivity
  have hτ1 : τ ≤ 1 := by rw [hτ]; nlinarith
  set h : ℝ → V := fun t => Real.exp (-t) •
    (dif ε b μ (heatOp ε t r) (n + m) - dif ε b μ (heatOp ε t r) n) with hh
  have hint : IntegrableOn h (Ioi 0) := by
    have := (integrableOn_dif_heatOp hε hr b μ (n + m)).sub (integrableOn_dif_heatOp hε hr b μ n)
    exact this.congr_fun (fun t _ => by simp only [hh, smul_sub, Pi.sub_apply]) measurableSet_Ioi
  have hrep : dif ε b μ (resolvent ε r) (n + m) - dif ε b μ (resolvent ε r) n =
      ∫ t in Ioi 0, h t := by
    rw [dif_resolvent hr, dif_resolvent hr, ← integral_sub (integrableOn_dif_heatOp hε hr b μ _)
      (integrableOn_dif_heatOp hε hr b μ _)]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [hh, smul_sub]
  have hsplit : Ioi (0 : ℝ) = Ioc 0 τ ∪ Ioi τ := (Ioc_union_Ioi_eq_Ioi hτ0.le).symm
  rw [hrep, hsplit, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
    (hint.mono_set (by rw [hsplit]; exact subset_union_left))
    (hint.mono_set (by rw [hsplit]; exact subset_union_right))]
  -- the part `t ≤ τ`: `≤ 2 c₀ M ∫_0^τ t^{-1/2} dt = 4 c₀ M d`
  have hI1 : ‖∫ t in Ioc 0 τ, h t‖ ≤ 4 * c0 * M * d := by
    have hint1 : IntegrableOn (fun t : ℝ => t ^ (-(1 : ℝ) / 2)) (Ioc 0 τ) := by
      have := intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := τ)
        (r := -(1 : ℝ) / 2) (by norm_num)
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hτ0.le).mp this
    calc ‖∫ t in Ioc 0 τ, h t‖ ≤ ∫ t in Ioc 0 τ, 2 * c0 * M * t ^ (-(1 : ℝ) / 2) := by
          refine norm_integral_le_of_norm_le (hint1.const_mul _) ?_
          refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun t ht => ?_)
          have ht0 : 0 < t := ht.1
          have hb1 := norm_dif_heatOp_le hε ht0 hr b μ (n + m)
          have hb2 := norm_dif_heatOp_le hε ht0 hr b μ n
          have he : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
          have hs : c0 / Real.sqrt t = c0 * t ^ (-(1 : ℝ) / 2) := by
            rw [Real.sqrt_eq_rpow, div_eq_mul_inv, ← Real.rpow_neg ht0.le]; congr 2; ring
          simp only [hh]
          rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
          calc Real.exp (-t) * ‖dif ε b μ (heatOp ε t r) (n + m) - dif ε b μ (heatOp ε t r) n‖
              ≤ 1 * (c0 / Real.sqrt t * M + c0 / Real.sqrt t * M) :=
                mul_le_mul he ((norm_sub_le _ _).trans (add_le_add hb1 hb2)) (norm_nonneg _)
                  zero_le_one
            _ = 2 * c0 * M * t ^ (-(1 : ℝ) / 2) := by rw [hs]; ring
      _ = 2 * c0 * M * (2 * d) := by
          rw [integral_const_mul, ← intervalIntegral.integral_of_le hτ0.le,
            integral_rpow (Or.inl (by norm_num))]
          rw [show -(1 : ℝ) / 2 + 1 = 1 / 2 by norm_num, Real.zero_rpow (by norm_num), sub_zero,
            hτ, ← Real.rpow_natCast, ← Real.rpow_mul hd0]
          norm_num
          left; ring
      _ = 4 * c0 * M * d := by ring
  -- the part `t ≥ τ`: `≤ d · 2c₀² M ∫_τ^∞ e^{-t} t⁻¹ dt ≤ 2c₀² M d (log τ⁻¹ + 1)`
  obtain ⟨hexpint, hexp⟩ := integral_exp_neg_inv_le hτ0 hτ1
  have hI2 : ‖∫ t in Ioi τ, h t‖ ≤ 2 * c0 ^ 2 * M * d * (Real.log τ⁻¹ + 1) := by
    calc ‖∫ t in Ioi τ, h t‖ ≤ ∫ t in Ioi τ, Real.exp (-t) * t⁻¹ * (2 * c0 ^ 2 * M * d) := by
          refine norm_integral_le_of_norm_le (hexpint.mul_const _) ?_
          refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
          have ht0 : 0 < t := lt_trans hτ0 ht
          have hB : ∀ lam k, ‖dfw ε lam (dif ε b μ (heatOp ε t r)) k‖ ≤ 2 * c0 ^ 2 / t * M :=
            fun lam k => norm_dif_dif_heatOp_le hε ht0 hr true b lam μ k
          have hdiff := norm_sub_le_l1 hε hB n m
          simp only [hh]
          rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
          calc Real.exp (-t) * ‖dif ε b μ (heatOp ε t r) (n + m) - dif ε b μ (heatOp ε t r) n‖
              ≤ Real.exp (-t) * (ε * l1 m * (2 * c0 ^ 2 / t * M)) :=
                mul_le_mul_of_nonneg_left hdiff (Real.exp_pos _).le
            _ = Real.exp (-t) * t⁻¹ * (2 * c0 ^ 2 * M * d) := by rw [hd]; field_simp
      _ = (∫ t in Ioi τ, Real.exp (-t) * t⁻¹) * (2 * c0 ^ 2 * M * d) := integral_mul_const _ _
      _ ≤ (Real.log τ⁻¹ + 1) * (2 * c0 ^ 2 * M * d) :=
          mul_le_mul_of_nonneg_right hexp (by positivity)
      _ = 2 * c0 ^ 2 * M * d * (Real.log τ⁻¹ + 1) := by ring
  -- `d ≤ d^β` and `d log d⁻¹ ≤ d^β / (e(1-β))`
  have hdβ : d ≤ d ^ β := by
    calc d = d ^ (1 : ℝ) := (Real.rpow_one d).symm
      _ ≤ d ^ β := Real.rpow_le_rpow_of_exponent_ge hdpos hd1 hβ1.le
  have hlogτ : Real.log τ⁻¹ = 2 * Real.log d⁻¹ := by
    rw [hτ, ← inv_pow, Real.log_pow]; norm_num
  have hdlog : d * Real.log d⁻¹ ≤ d ^ β * (Real.exp 1 * (1 - β))⁻¹ := by
    have h := rpow_mul_log_inv_le hdpos hβ1
    calc d * Real.log d⁻¹ = d ^ β * (d ^ (1 - β) * Real.log d⁻¹) := by
          rw [← mul_assoc, ← Real.rpow_add hdpos, add_sub_cancel, Real.rpow_one]
      _ ≤ d ^ β * (Real.exp 1 * (1 - β))⁻¹ :=
          mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hd0 _)
  have hconst := constants_first hβ0.le hβ1
  have hc := c0_pos
  calc ‖(∫ t in Ioc 0 τ, h t) + ∫ t in Ioi τ, h t‖
      ≤ 4 * c0 * M * d + 2 * c0 ^ 2 * M * d * (Real.log τ⁻¹ + 1) :=
        (norm_add_le _ _).trans (add_le_add hI1 hI2)
    _ = M * ((4 * c0 + 2 * c0 ^ 2) * d + 4 * c0 ^ 2 * (d * Real.log d⁻¹)) := by
        rw [hlogτ]; ring
    _ ≤ M * ((4 * c0 + 2 * c0 ^ 2) * d ^ β + 4 * c0 ^ 2 * (d ^ β * (Real.exp 1 * (1 - β))⁻¹)) := by
        gcongr
    _ = M * d ^ β * (4 * c0 + 2 * c0 ^ 2 + 4 * c0 ^ 2 / (Real.exp 1 * (1 - β))) := by
        rw [div_eq_mul_inv]; ring
    _ ≤ M * d ^ β * CS' β := mul_le_mul_of_nonneg_left hconst (by positivity)
    _ = CS' β * M * d ^ β := by ring

/-! ### `prop:free-schauder`(ii) -/

/-- `Γ(s) ≤ 1/s + 1` for `0 < s ≤ 1`, from `∫_0^1 t^{s-1} dt + ∫_1^∞ e^{-t} dt`. -/
lemma Gamma_le_inv_add_one {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) : Real.Gamma s ≤ 1 / s + 1 := by
  rw [← integral_exp_neg_rpow hs]
  have hint := integrableOn_exp_neg_rpow hs
  have hsplit : Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 := (Ioc_union_Ioi_eq_Ioi zero_le_one).symm
  rw [hsplit, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
    (hint.mono_set (by rw [hsplit]; exact subset_union_left))
    (hint.mono_set (by rw [hsplit]; exact subset_union_right))]
  have hpow : IntegrableOn (fun t : ℝ => t ^ (s - 1)) (Ioc 0 1) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
      (intervalIntegral.intervalIntegrable_rpow' (by linarith))
  have h1 : ∫ t in Ioc 0 1, Real.exp (-t) * t ^ (s - 1) ≤ 1 / s := by
    calc ∫ t in Ioc 0 1, Real.exp (-t) * t ^ (s - 1) ≤ ∫ t in Ioc (0 : ℝ) 1, t ^ (s - 1) := by
          refine setIntegral_mono_on (hint.mono_set (fun t ht => ht.1)) hpow measurableSet_Ioc
            fun t ht => ?_
          have he : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [ht.1])
          nlinarith [Real.rpow_nonneg (le_of_lt ht.1) (s - 1)]
      _ = 1 / s := by
          rw [← intervalIntegral.integral_of_le zero_le_one, integral_rpow (Or.inl (by linarith))]
          rw [sub_add_cancel, Real.one_rpow, Real.zero_rpow hs.ne']; ring
  have h2 : ∫ t in Ioi 1, Real.exp (-t) * t ^ (s - 1) ≤ 1 := by
    calc ∫ t in Ioi 1, Real.exp (-t) * t ^ (s - 1) ≤ ∫ t in Ioi (1 : ℝ), Real.exp (-t) := by
          refine setIntegral_mono_on (hint.mono_set (Ioi_subset_Ioi zero_le_one))
            (by simpa using exp_neg_integrableOn_Ioi 1 zero_lt_one) measurableSet_Ioi
            fun t ht => ?_
          have : t ^ (s - 1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (le_of_lt ht)
            (by linarith)
          nlinarith [Real.exp_pos (-t)]
      _ = Real.exp (-1) := by simpa using integral_exp_neg_Ioi 1
      _ ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  linarith

/-- The integrand of `𝒟𝒟' G₁ f` is integrable, with the bound `2 c₀ m₁ t^{-1+β/2} F`. -/
lemma integrableOn_dif_dif_heatOp (hε : 0 < ε) {β F : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (hF : 0 ≤ F) {f : (Fin 4 → ℤ) → V} {M : ℝ} (hf : ∀ n, ‖f n‖ ≤ M)
    (hhol : ∀ n m, ‖f (n + m) - f n‖ ≤ F * (ε * l1 m) ^ β) (b b' : Bool) (μ ν : Fin 4)
    (k : Fin 4 → ℤ) :
    IntegrableOn (fun t => Real.exp (-t) • dif ε b μ (dif ε b' ν (heatOp ε t f)) k) (Ioi 0) := by
  refine Integrable.mono' ((integrableOn_exp_neg_rpow (s := β / 2) (by positivity)).mul_const
    (2 * c0 * m1 * F))
    ((Continuous.aestronglyMeasurable (by fun_prop)).smul
      (aestronglyMeasurable_dif (fun k => aestronglyMeasurable_dif_heatOp hf b' ν k) b μ k)) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
  rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
  have h := norm_dif_dif_heatOp_le_holder hε ht hβ0.le hβ1 hF hf hhol b b' μ ν k
  calc Real.exp (-t) * ‖dif ε b μ (dif ε b' ν (heatOp ε t f)) k‖
      ≤ Real.exp (-t) * (2 * c0 * m1 * t ^ (-1 + β / 2) * F) :=
        mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    _ = Real.exp (-t) * t ^ (β / 2 - 1) * (2 * c0 * m1 * F) := by
        rw [show β / 2 - 1 = -1 + β / 2 by ring]; ring

/-- `𝒟𝒟' G₁ f = ∫ e^{-t} 𝒟𝒟' P_t f dt`. -/
lemma dif_dif_resolvent (hε : 0 < ε) {f : (Fin 4 → ℤ) → V} {M : ℝ} (hf : ∀ n, ‖f n‖ ≤ M)
    (b b' : Bool) (μ ν : Fin 4) (n : Fin 4 → ℤ) :
    dif ε b μ (dif ε b' ν (resolvent ε f)) n =
      ∫ t in Ioi 0, Real.exp (-t) • dif ε b μ (dif ε b' ν (heatOp ε t f)) n := by
  have h1 : dif ε b' ν (resolvent ε f) = fun k =>
      ∫ t in Ioi 0, Real.exp (-t) • dif ε b' ν (heatOp ε t f) k :=
    funext fun k => dif_resolvent hf b' ν k
  rw [h1]
  exact dif_integral (g := fun t => dif ε b' ν (heatOp ε t f))
    (fun k => integrableOn_dif_heatOp hε hf b' ν k) b μ n

/-- `prop:free-schauder`(ii), first bound: `‖𝒟𝒟' G₁ f‖_∞ ≤ C_S(β) F`. -/
theorem norm_dif_dif_resolvent_le (hε : 0 < ε) {β F : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hF : 0 ≤ F) {f : (Fin 4 → ℤ) → V} {M : ℝ} (hf : ∀ n, ‖f n‖ ≤ M)
    (hhol : ∀ n m, ‖f (n + m) - f n‖ ≤ F * (ε * l1 m) ^ β) (b b' : Bool) (μ ν : Fin 4)
    (n : Fin 4 → ℤ) : ‖dif ε b μ (dif ε b' ν (resolvent ε f)) n‖ ≤ CS β * F := by
  have hc := c0_pos
  have hm := zero_le_one.trans one_le_m1
  rw [dif_dif_resolvent hε hf]
  calc ‖∫ t in Ioi 0, Real.exp (-t) • dif ε b μ (dif ε b' ν (heatOp ε t f)) n‖
      ≤ ∫ t in Ioi 0, Real.exp (-t) * t ^ (β / 2 - 1) * (2 * c0 * m1 * F) := by
        refine norm_integral_le_of_norm_le ((integrableOn_exp_neg_rpow (s := β / 2)
          (by positivity)).mul_const _) ?_
        refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
        rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
        have h := norm_dif_dif_heatOp_le_holder hε ht hβ0.le hβ1.le hF hf hhol b b' μ ν n
        calc Real.exp (-t) * ‖dif ε b μ (dif ε b' ν (heatOp ε t f)) n‖
            ≤ Real.exp (-t) * (2 * c0 * m1 * t ^ (-1 + β / 2) * F) :=
              mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
          _ = _ := by rw [show β / 2 - 1 = -1 + β / 2 by ring]; ring
    _ = Real.Gamma (β / 2) * (2 * c0 * m1 * F) := by
        rw [integral_mul_const, integral_exp_neg_rpow (by positivity)]
    _ ≤ (2 / β + 1) * (2 * c0 * m1 * F) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        have := Gamma_le_inv_add_one (s := β / 2) (by positivity) (by linarith)
        rwa [one_div_div] at this
    _ ≤ CS β * F := by
        unfold CS
        have h1β : 0 < 1 - β := by linarith
        have : 2 ≤ 12 / (1 - β) := by rw [le_div_iff₀ h1β]; linarith
        have hb : (2 / β + 1) * 2 ≤ 8 / β + 12 / (1 - β) := by
          have h48 : 4 / β ≤ 8 / β := div_le_div_of_nonneg_right (by norm_num) hβ0.le
          have e : (2 / β + 1) * 2 = 4 / β + 2 := by ring
          linarith
        calc (2 / β + 1) * (2 * c0 * m1 * F) = c0 * m1 * F * ((2 / β + 1) * 2) := by ring
          _ ≤ c0 * m1 * F * (8 / β + 12 / (1 - β)) :=
              mul_le_mul_of_nonneg_left hb (by positivity)
          _ = c0 * m1 * (8 / β + 12 / (1 - β)) * F := by ring

/-- `prop:free-schauder`(ii), second bound:
`‖(𝒟𝒟' G₁ f)(x + z) - (𝒟𝒟' G₁ f)(x)‖ ≤ C_S(β) F |z|₁^β`. -/
theorem norm_dif_dif_resolvent_sub_le (hε : 0 < ε) {β F : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hF : 0 ≤ F) {f : (Fin 4 → ℤ) → V} {M : ℝ} (hf : ∀ n, ‖f n‖ ≤ M)
    (hhol : ∀ n m, ‖f (n + m) - f n‖ ≤ F * (ε * l1 m) ^ β) (b b' : Bool) (μ ν : Fin 4)
    (n m : Fin 4 → ℤ) :
    ‖dif ε b μ (dif ε b' ν (resolvent ε f)) (n + m) - dif ε b μ (dif ε b' ν (resolvent ε f)) n‖ ≤
      CS β * F * (ε * l1 m) ^ β := by
  have hc := c0_pos
  have hm := zero_le_one.trans one_le_m1
  have h1β : 0 < 1 - β := by linarith
  set d := ε * l1 m with hd
  have hd0 : 0 ≤ d := mul_nonneg hε.le (l1_nonneg m)
  have hCS : 0 ≤ CS β := by unfold CS; positivity
  rcases eq_or_lt_of_le hd0 with h0 | hdpos
  · have hl : l1 m = 0 := by
      rcases mul_eq_zero.mp h0.symm with h | h
      · exact absurd h hε.ne'
      · exact h
    rw [l1_eq_zero hl, add_zero, sub_self, norm_zero]
    exact mul_nonneg (mul_nonneg hCS hF) (Real.rpow_nonneg hd0 _)
  set τ := d ^ 2 with hτ
  have hτ0 : 0 < τ := by positivity
  set g : ℝ → (Fin 4 → ℤ) → V := fun t => dif ε b μ (dif ε b' ν (heatOp ε t f)) with hg
  set h : ℝ → V := fun t => Real.exp (-t) • (g t (n + m) - g t n) with hh
  have hint : IntegrableOn h (Ioi 0) := by
    have := (integrableOn_dif_dif_heatOp hε hβ0 hβ1.le hF hf hhol b b' μ ν (n + m)).sub
      (integrableOn_dif_dif_heatOp hε hβ0 hβ1.le hF hf hhol b b' μ ν n)
    exact this.congr_fun (fun t _ => by simp only [hh, hg, smul_sub, Pi.sub_apply])
      measurableSet_Ioi
  have hrep : dif ε b μ (dif ε b' ν (resolvent ε f)) (n + m) -
      dif ε b μ (dif ε b' ν (resolvent ε f)) n = ∫ t in Ioi 0, h t := by
    rw [dif_dif_resolvent hε hf, dif_dif_resolvent hε hf,
      ← integral_sub (integrableOn_dif_dif_heatOp hε hβ0 hβ1.le hF hf hhol b b' μ ν _)
        (integrableOn_dif_dif_heatOp hε hβ0 hβ1.le hF hf hhol b b' μ ν _)]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [hh, hg, smul_sub]
  have hsplit : Ioi (0 : ℝ) = Ioc 0 τ ∪ Ioi τ := (Ioc_union_Ioi_eq_Ioi hτ0.le).symm
  rw [hrep, hsplit, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
    (hint.mono_set (by rw [hsplit]; exact subset_union_left))
    (hint.mono_set (by rw [hsplit]; exact subset_union_right))]
  have hτβ : τ ^ (β / 2) = d ^ β := by
    rw [hτ, ← Real.rpow_natCast, ← Real.rpow_mul hd0]; congr 1; push_cast; ring
  -- the part `t ≤ τ`
  have hI1 : ‖∫ t in Ioc 0 τ, h t‖ ≤ 8 * c0 * m1 / β * F * d ^ β := by
    have hint1 : IntegrableOn (fun t : ℝ => t ^ (-1 + β / 2)) (Ioc 0 τ) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hτ0.le).mp
        (intervalIntegral.intervalIntegrable_rpow' (by linarith))
    calc ‖∫ t in Ioc 0 τ, h t‖ ≤ ∫ t in Ioc 0 τ, 4 * c0 * m1 * F * t ^ (-1 + β / 2) := by
          refine norm_integral_le_of_norm_le (hint1.const_mul _) ?_
          refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun t ht => ?_)
          have ht0 : 0 < t := ht.1
          have hb1 := norm_dif_dif_heatOp_le_holder hε ht0 hβ0.le hβ1.le hF hf hhol b b' μ ν (n + m)
          have hb2 := norm_dif_dif_heatOp_le_holder hε ht0 hβ0.le hβ1.le hF hf hhol b b' μ ν n
          have he : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
          simp only [hh, hg]
          rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
          calc Real.exp (-t) * ‖dif ε b μ (dif ε b' ν (heatOp ε t f)) (n + m) -
                dif ε b μ (dif ε b' ν (heatOp ε t f)) n‖
              ≤ 1 * (2 * c0 * m1 * t ^ (-1 + β / 2) * F + 2 * c0 * m1 * t ^ (-1 + β / 2) * F) :=
                mul_le_mul he ((norm_sub_le _ _).trans (add_le_add hb1 hb2)) (norm_nonneg _)
                  zero_le_one
            _ = 4 * c0 * m1 * F * t ^ (-1 + β / 2) := by ring
      _ = 4 * c0 * m1 * F * (τ ^ (β / 2) / (β / 2)) := by
          rw [integral_const_mul, ← intervalIntegral.integral_of_le hτ0.le,
            integral_rpow (Or.inl (by linarith))]
          rw [show -1 + β / 2 + 1 = β / 2 by ring, Real.zero_rpow (by positivity), sub_zero]
      _ = 8 * c0 * m1 / β * F * d ^ β := by rw [hτβ]; field_simp; ring
  -- the part `t ≥ τ`
  have hI2 : ‖∫ t in Ioi τ, h t‖ ≤ 12 * c0 ^ 2 * m1 / (1 - β) * F * d ^ β := by
    have ha : -(3 - β) / 2 < -1 := by linarith
    have hint2 : IntegrableOn (fun t : ℝ => t ^ (-(3 - β) / 2)) (Ioi τ) :=
      integrableOn_Ioi_rpow_of_lt ha hτ0
    calc ‖∫ t in Ioi τ, h t‖ ≤ ∫ t in Ioi τ, (6 * c0 ^ 2 * m1 * F * d) * t ^ (-(3 - β) / 2) := by
          refine norm_integral_le_of_norm_le (hint2.const_mul _) ?_
          refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
          have ht0 : 0 < t := lt_trans hτ0 ht
          have hB : ∀ lam k, ‖dfw ε lam (g t) k‖ ≤ 6 * c0 ^ 2 * m1 * t ^ (-(3 - β) / 2) * F :=
            fun lam k => norm_dif_dif_dif_heatOp_le_holder hε ht0 hβ0.le hβ1.le hF hf hhol
              b b' true μ ν lam k
          have hdiff := norm_sub_le_l1 hε hB n m
          have he : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
          simp only [hh]
          rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
          calc Real.exp (-t) * ‖g t (n + m) - g t n‖
              ≤ 1 * (ε * l1 m * (6 * c0 ^ 2 * m1 * t ^ (-(3 - β) / 2) * F)) :=
                mul_le_mul he hdiff (norm_nonneg _) zero_le_one
            _ = 6 * c0 ^ 2 * m1 * F * d * t ^ (-(3 - β) / 2) := by rw [hd]; ring
      _ = (6 * c0 ^ 2 * m1 * F * d) * (-τ ^ (-(3 - β) / 2 + 1) / (-(3 - β) / 2 + 1)) := by
          rw [integral_const_mul, integral_Ioi_rpow_of_lt ha hτ0]
      _ = 12 * c0 ^ 2 * m1 / (1 - β) * F * d ^ β := by
          have hτp : τ ^ (-(3 - β) / 2 + 1) = d ^ (β - 1) := by
            rw [hτ, ← Real.rpow_natCast, ← Real.rpow_mul hd0]; congr 1; push_cast; ring
          have hdd : d * d ^ (β - 1) = d ^ β := by
            rw [mul_comm, ← Real.rpow_add_one hdpos.ne', sub_add_cancel]
          rw [hτp, show -(3 - β) / 2 + 1 = -((1 - β) / 2) by ring]
          field_simp
          rw [← hdd]; ring
  calc ‖(∫ t in Ioc 0 τ, h t) + ∫ t in Ioi τ, h t‖
      ≤ 8 * c0 * m1 / β * F * d ^ β + 12 * c0 ^ 2 * m1 / (1 - β) * F * d ^ β :=
        (norm_add_le _ _).trans (add_le_add hI1 hI2)
    _ = c0 * m1 * (8 / β + c0 * (12 / (1 - β))) * F * d ^ β := by ring
    _ ≤ c0 * m1 * (8 / β + 1 * (12 / (1 - β))) * F * d ^ β := by
        gcongr
        exact c0_le_one
    _ = CS β * F * d ^ β := by unfold CS; ring

end CoreLean
