/-
The time integrals behind `prop:free-schauder` of BALABAN_CORE.tex: measurability of
`t ↦ (P_t r)(n)`, `G₁ r = ∫_0^∞ e^{-t} P_t r dt`, the differences under the integral, and the
elementary integrals `∫_0^∞ e^{-t} t^{-1/2} dt = √π`, `∫_τ^∞ e^{-t} t⁻¹ dt ≤ log τ⁻¹ + 1` (`τ ≤ 1`),
and `s^{1-β} log s⁻¹ ≤ (e(1-β))⁻¹`.
-/
import CoreLean.HeatHigher

open MeasureTheory Real Balaban.LatticeGreen Filter Topology Set

namespace CoreLean

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
variable {ε : ℝ}

/-- `t ↦ (P_t r)(n)` is a.e. strongly measurable on `(0, ∞)`: it is the limit of the finite partial
sums, which are continuous. -/
lemma aestronglyMeasurable_heatOp {r : (Fin 4 → ℤ) → V} {M : ℝ} (hr : ∀ n, ‖r n‖ ≤ M)
    (n : Fin 4 → ℤ) :
    AEStronglyMeasurable (fun t => heatOp ε t r n) (volume.restrict (Ioi 0)) := by
  refine aestronglyMeasurable_of_tendsto_ae (u := (atTop : Filter (Finset (Fin 4 → ℤ))))
    (f := fun s t => ∑ z ∈ s, heatKernel 4 (t / ε ^ 2) z • r (n - z)) (fun s => ?_) ?_
  · refine Continuous.aestronglyMeasurable ?_
    exact continuous_finsetSum _ fun z _ =>
      ((continuous_heatKernel z).comp (continuous_id.div_const _)).smul continuous_const
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    have hs : 0 ≤ t / ε ^ 2 := by have : 0 < t := ht; positivity
    exact (summable_kernel_smul hs hr _ (summable_abs_heatKernel4 hs) n).hasSum

/-- `e^{-t}` is integrable on `(0, ∞)`. -/
lemma integrableOn_exp_neg : IntegrableOn (fun t : ℝ => Real.exp (-t)) (Ioi 0) := by
  have := exp_neg_integrableOn_Ioi 0 (zero_lt_one : (0 : ℝ) < 1)
  simpa using this

/-- An integrand bounded by `e^{-t} M` is integrable on `(0, ∞)`. -/
lemma integrableOn_of_le_exp {g : ℝ → V} (hg : AEStronglyMeasurable g (volume.restrict (Ioi 0)))
    {M : ℝ} (hb : ∀ t ∈ Ioi (0 : ℝ), ‖g t‖ ≤ Real.exp (-t) * M) : IntegrableOn g (Ioi 0) := by
  refine Integrable.mono' (integrableOn_exp_neg.mul_const M) hg ?_
  exact (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall hb)

/-- `G₁ r = ∫_0^∞ e^{-t} P_t r dt`. -/
noncomputable def resolvent (ε : ℝ) (r : (Fin 4 → ℤ) → V) (n : Fin 4 → ℤ) : V :=
  ∫ t in Ioi 0, Real.exp (-t) • heatOp ε t r n

lemma integrableOn_resolvent {r : (Fin 4 → ℤ) → V} {M : ℝ} (hr : ∀ n, ‖r n‖ ≤ M)
    (n : Fin 4 → ℤ) : IntegrableOn (fun t => Real.exp (-t) • heatOp ε t r n) (Ioi 0) := by
  refine integrableOn_of_le_exp (M := M)
    ((Continuous.aestronglyMeasurable (by fun_prop)).smul (aestronglyMeasurable_heatOp hr n))
    fun t ht => ?_
  rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
  exact mul_le_mul_of_nonneg_left (norm_heatOp_le (le_of_lt ht) hr n) (Real.exp_pos _).le

/-- Differences commute with the time integral. -/
lemma dif_integral {g : ℝ → (Fin 4 → ℤ) → V}
    (hg : ∀ k, IntegrableOn (fun t => Real.exp (-t) • g t k) (Ioi 0)) (b : Bool) (μ : Fin 4)
    (n : Fin 4 → ℤ) :
    dif ε b μ (fun k => ∫ t in Ioi 0, Real.exp (-t) • g t k) n =
      ∫ t in Ioi 0, Real.exp (-t) • dif ε b μ (g t) n := by
  cases b
  · simp only [dif, Bool.false_eq_true, ↓reduceIte, dbw]
    rw [← integral_sub (hg _) (hg _), ← integral_smul]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [smul_sub, smul_comm ε⁻¹]
  · simp only [dif, ↓reduceIte, dfw]
    rw [← integral_sub (hg _) (hg _), ← integral_smul]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [smul_sub, smul_comm ε⁻¹]

/-- The differences of `t ↦ P_t r` are a.e. strongly measurable on `(0, ∞)`. -/
lemma aestronglyMeasurable_dif_heatOp {r : (Fin 4 → ℤ) → V} {M : ℝ} (hr : ∀ n, ‖r n‖ ≤ M)
    (b : Bool) (μ : Fin 4) (n : Fin 4 → ℤ) :
    AEStronglyMeasurable (fun t => dif ε b μ (heatOp ε t r) n) (volume.restrict (Ioi 0)) := by
  cases b
  · simp only [dif, Bool.false_eq_true, ↓reduceIte, dbw]
    exact ((aestronglyMeasurable_heatOp hr _).sub (aestronglyMeasurable_heatOp hr _)).const_smul _
  · simp only [dif, ↓reduceIte, dfw]
    exact ((aestronglyMeasurable_heatOp hr _).sub (aestronglyMeasurable_heatOp hr _)).const_smul _

/-! ### Elementary integrals -/

/-- `∫_0^∞ e^{-t} t^{s-1} dt = Γ(s)` and its integrability, for `s > 0`. -/
lemma integrableOn_exp_neg_rpow {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun t : ℝ => Real.exp (-t) * t ^ (s - 1)) (Ioi 0) :=
  Real.GammaIntegral_convergent hs

lemma integral_exp_neg_rpow {s : ℝ} (hs : 0 < s) :
    ∫ t in Ioi (0 : ℝ), Real.exp (-t) * t ^ (s - 1) = Real.Gamma s :=
  (Real.Gamma_eq_integral hs).symm

/-- `∫_0^∞ e^{-t} t^{-1/2} dt = √π`. -/
lemma integral_exp_neg_inv_sqrt :
    ∫ t in Ioi (0 : ℝ), Real.exp (-t) * (Real.sqrt t)⁻¹ = Real.sqrt π := by
  have h := integral_exp_neg_rpow (s := 1 / 2) (by norm_num)
  rw [Real.Gamma_one_half_eq] at h
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (le_of_lt ht)]
  norm_num

lemma integrableOn_exp_neg_inv_sqrt :
    IntegrableOn (fun t : ℝ => Real.exp (-t) * (Real.sqrt t)⁻¹) (Ioi 0) := by
  refine (integrableOn_exp_neg_rpow (s := 1 / 2) (by norm_num)).congr_fun (fun t ht => ?_)
    measurableSet_Ioi
  simp only
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (le_of_lt ht)]
  norm_num

/-- `log x ≤ x / e` for `x > 0`. -/
lemma log_le_div_exp_one {x : ℝ} (hx : 0 < x) : Real.log x ≤ x / Real.exp 1 := by
  have h := Real.log_le_sub_one_of_pos (div_pos hx (Real.exp_pos 1))
  rw [Real.log_div hx.ne' (Real.exp_pos 1).ne', Real.log_exp] at h
  linarith

/-- `s^{1-β} log s⁻¹ ≤ (e(1-β))⁻¹` for `0 < s` and `β < 1`. -/
lemma rpow_mul_log_inv_le {s β : ℝ} (hs : 0 < s) (hβ : β < 1) :
    s ^ (1 - β) * Real.log s⁻¹ ≤ (Real.exp 1 * (1 - β))⁻¹ := by
  have h1β : 0 < 1 - β := by linarith
  -- `log s⁻¹ = (1-β)⁻¹ log (s^{-(1-β)}) ≤ (1-β)⁻¹ s^{-(1-β)} / e`
  have hy : 0 < s ^ (-(1 - β)) := Real.rpow_pos_of_pos hs _
  have hlog : Real.log s⁻¹ = (1 - β)⁻¹ * Real.log (s ^ (-(1 - β))) := by
    rw [Real.log_rpow hs, Real.log_inv]; field_simp
  rw [hlog]
  have hb := log_le_div_exp_one hy
  calc s ^ (1 - β) * ((1 - β)⁻¹ * Real.log (s ^ (-(1 - β))))
      ≤ s ^ (1 - β) * ((1 - β)⁻¹ * (s ^ (-(1 - β)) / Real.exp 1)) := by
        gcongr
    _ = (s ^ (1 - β) * s ^ (-(1 - β))) * ((1 - β)⁻¹ * (Real.exp 1)⁻¹) := by ring
    _ = (Real.exp 1 * (1 - β))⁻¹ := by
        rw [← Real.rpow_add hs, add_neg_cancel, Real.rpow_zero, one_mul, mul_inv, mul_comm]

lemma continuousOn_inv_of_pos (S : Set ℝ) (hS : ∀ t ∈ S, 0 < t) :
    ContinuousOn (fun t : ℝ => t⁻¹) S :=
  fun t ht => (continuousAt_inv₀ (hS t ht).ne').continuousWithinAt

/-- `∫_τ^∞ e^{-t} t⁻¹ dt ≤ log τ⁻¹ + 1` for `0 < τ ≤ 1`, with the integrability. -/
lemma integral_exp_neg_inv_le {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    IntegrableOn (fun t : ℝ => Real.exp (-t) * t⁻¹) (Ioi τ) ∧
      ∫ t in Ioi τ, Real.exp (-t) * t⁻¹ ≤ Real.log τ⁻¹ + 1 := by
  have hint : IntegrableOn (fun t : ℝ => Real.exp (-t) * t⁻¹) (Ioi τ) := by
    refine Integrable.mono' ((exp_neg_integrableOn_Ioi τ zero_lt_one).mul_const τ⁻¹)
      ((Continuous.aestronglyMeasurable (by fun_prop)).mul ?_) ?_
    · exact (continuousOn_inv_of_pos (Ioi τ) fun t ht => lt_trans hτ ht).aestronglyMeasurable
        measurableSet_Ioi
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
      have ht0 : 0 < t := lt_trans hτ ht
      rw [Real.norm_of_nonneg (by positivity), neg_one_mul]
      exact mul_le_mul_of_nonneg_left (inv_anti₀ hτ (le_of_lt ht)) (Real.exp_pos _).le
  refine ⟨hint, ?_⟩
  have hsplit : Ioi τ = Ioc τ 1 ∪ Ioi 1 := (Ioc_union_Ioi_eq_Ioi hτ1).symm
  rw [hsplit, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
    (hint.mono_set (by rw [hsplit]; exact subset_union_left))
    (hint.mono_set (by rw [hsplit]; exact subset_union_right))]
  have h1 : ∫ t in Ioc τ 1, Real.exp (-t) * t⁻¹ ≤ Real.log τ⁻¹ := by
    calc ∫ t in Ioc τ 1, Real.exp (-t) * t⁻¹ ≤ ∫ t in Ioc τ 1, t⁻¹ := by
          refine setIntegral_mono_on (hint.mono_set (fun t ht => ht.1))
            ((continuousOn_inv_of_pos (Icc τ 1) fun t ht => lt_of_lt_of_le hτ ht.1)
              |>.integrableOn_Icc |>.mono_set Ioc_subset_Icc_self) measurableSet_Ioc fun t ht => ?_
          have ht0 : 0 < t := lt_trans hτ ht.1
          have : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
          nlinarith [inv_pos.mpr ht0]
      _ = Real.log τ⁻¹ := by
          rw [← intervalIntegral.integral_of_le hτ1, integral_inv_of_pos hτ zero_lt_one,
            Real.log_div one_ne_zero hτ.ne', Real.log_one, Real.log_inv]; ring
  have h2 : ∫ t in Ioi 1, Real.exp (-t) * t⁻¹ ≤ 1 := by
    calc ∫ t in Ioi 1, Real.exp (-t) * t⁻¹ ≤ ∫ t in Ioi (1 : ℝ), Real.exp (-t) := by
          refine setIntegral_mono_on (hint.mono_set (Ioi_subset_Ioi hτ1))
            (by simpa using exp_neg_integrableOn_Ioi 1 zero_lt_one) measurableSet_Ioi
            fun t ht => ?_
          have : t⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (le_of_lt ht)
          nlinarith [Real.exp_pos (-t)]
      _ = Real.exp (-1) := by
          have := integral_exp_neg_Ioi 1
          simpa using this
      _ ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  linarith

end CoreLean
