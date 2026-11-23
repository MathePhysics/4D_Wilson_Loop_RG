/-
`lem:summation`, `eq:summation` of BALABAN_CORE.tex: the summation over the determining set.

For a sequence of domains on the torus (`ContSeq`) with `RM ≥ r₁(α, δ)` and a point `y` of the
determining set `𝐁`, `Σ_{y' ∈ 𝐁} e^{-αδd(y, y')} ≤ c₁(α, δ) = 2²¹L⁸e^{2αδ}(αδ)⁻⁴`. The proof is the core's:
the exponential at `y' ∈ Γ_i` is at most `e^{2αδ}a_i⁻⁴` times its integral over the open cell of `y'`
(on which `d(y', ·) ≤ 2`), the open cells of a layer are disjoint, and the integral over them is the
integral over `r > 0` of `αδe^{-αδr}` times the measure of the points at a weighted distance of less than
`r`, which lie in an `ℓ¹`-ball of the radius `a_{j+1}L^{r/RM}r` and, for `|i - j| ≥ 2`, at a weighted
distance of at least `RM(|i - j| - 1)` (`lem:distance`(ii)).
-/
import CoreLean.SummationMeasure
import CoreLean.Summation

open Set Finset MeasureTheory
open scoped ENNReal

noncomputable section

namespace CoreLean

namespace Summation

namespace ContSeq

variable {p : ℝ} [Fact (0 < p)] (C : ContSeq p)

/-- The layer `Γ_i = Ω_i^{(i)} \ Ω_{i+1}`. -/
def Gam (i : ℕ) : Set (Tor p) := {y | InLat (C.a i) y ∧ y ∈ C.Ω i ∧ y ∉ C.Ω (i + 1)}

/-- The weighted distance as a real number. -/
def dd (y x : Tor p) : ℝ := (wdist C.D y x).toReal

lemma dd_nonneg (y x : Tor p) : 0 ≤ C.dd y x := ENNReal.toReal_nonneg

lemma ofReal_dd (y x : Tor p) : ENNReal.ofReal (C.dd y x) = wdist C.D y x :=
  ENNReal.ofReal_toReal (wdist_ne_top _ _ _)

lemma dd_triangle (x y z : Tor p) : C.dd x z ≤ C.dd x y + C.dd y z := by
  unfold dd
  rw [← ENNReal.toReal_add (wdist_ne_top _ _ _) (wdist_ne_top _ _ _)]
  exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨wdist_ne_top _ _ _, wdist_ne_top _ _ _⟩)
    (wdist_triangle _ _ _ _)

/-- `d(y, ·)` is continuous: `|d(y, x) - d(y, x')| ≤ d(x, x') ≤ η⁻¹|x - x'|₁`. -/
lemma dd_le (x x' : Tor p) : C.dd x x' ≤ (C.a 0)⁻¹ * dist1 x x' := by
  have h : wdist C.D x x' ≤ ENNReal.ofReal ((C.a 0)⁻¹ * dist1 x x') := wdist_le C.D x x'
  have hnn : 0 ≤ (C.a 0)⁻¹ * dist1 x x' :=
    mul_nonneg (inv_nonneg.mpr (C.a_pos 0).le) (dist1_nonneg _ _)
  unfold dd
  have := (ENNReal.toReal_le_toReal (wdist_ne_top _ _ _) ENNReal.ofReal_ne_top).mpr h
  rwa [ENNReal.toReal_ofReal hnn] at this

lemma dist1_le_four_dist (x x' : Tor p) : dist1 x x' ≤ 4 * dist x x' := by
  unfold dist1
  calc ∑ ν, ‖x ν - x' ν‖ ≤ ∑ _ν : Fin 4, dist x x' :=
        Finset.sum_le_sum fun ν _ => by rw [← dist_eq_norm]; exact dist_le_pi_dist x x' ν
    _ = 4 * dist x x' := by simp

/-- `d(y, ·)` is Lipschitz, hence continuous: `|d(y, x) - d(y, x')| ≤ d(x, x') ≤ η⁻¹|x - x'|₁`. -/
lemma continuous_dd (y : Tor p) : Continuous (C.dd y) := by
  have hL : LipschitzWith (Real.toNNReal (4 * (C.a 0)⁻¹)) (C.dd y) := by
    refine LipschitzWith.of_dist_le_mul fun x x' => ?_
    rw [Real.dist_eq, abs_le, Real.coe_toNNReal _ (by have := C.a_pos 0; positivity)]
    have t1 := C.dd_triangle y x x'
    have t2 := C.dd_triangle y x' x
    have e1 := C.dd_le x x'
    have e2 := C.dd_le x' x
    have h4 := dist1_le_four_dist x x'
    have h4' := dist1_le_four_dist x' x
    rw [dist_comm] at h4'
    have ha := inv_nonneg.mpr (C.a_pos 0).le
    have m1 : (C.a 0)⁻¹ * dist1 x x' ≤ 4 * (C.a 0)⁻¹ * dist x x' := by nlinarith
    have m2 : (C.a 0)⁻¹ * dist1 x' x ≤ 4 * (C.a 0)⁻¹ * dist x x' := by nlinarith
    constructor <;> linarith
  exact hL.continuous

/-! ### The averaging over a cell -/

lemma a_le_p {i : ℕ} (hi : i ≤ C.k) : C.a i ≤ p := by
  have hL1 : (1 : ℝ) ≤ C.L := by have := C.three_le_L; exact_mod_cast (by omega : 1 ≤ C.L)
  have h1 : C.a i ≤ 1 := by
    unfold a aa
    rw [div_le_one (by have := C.L_pos; positivity)]
    exact pow_le_pow_right₀ hL1 hi
  have h2 : (1 : ℝ) ≤ (C.L : ℝ) ^ C.mT := one_le_pow₀ hL1
  calc C.a i ≤ 2 * (C.L : ℝ) ^ C.mT := by linarith
    _ = p := C.p_eq.symm

lemma measurableSet_cellOpen (a : ℝ) (y : Tor p) : MeasurableSet (cellOpen a y) := by
  have : cellOpen a y = ⋂ ν, {z : Tor p | ‖z ν - y ν‖ < a / 2} := by ext; simp [cellOpen]
  rw [this]
  exact MeasurableSet.iInter fun ν =>
    (isOpen_lt ((continuous_apply ν).sub continuous_const).norm continuous_const).measurableSet

/-- The exponential at a point of `Γ_i` is at most `e^{2t}a_i⁻⁴` times its integral over the open cell. -/
theorem average_cell {t : ℝ} (ht : 0 ≤ t) {i : ℕ} (hi : i ≤ C.k) {y' : Tor p} (hy' : y' ∈ C.Gam i)
    (y : Tor p) :
    ENNReal.ofReal (C.a i ^ 4) * ENNReal.ofReal (Real.exp (-t * C.dd y y')) ≤
      ENNReal.ofReal (Real.exp (2 * t)) *
        ∫⁻ x in cellOpen (C.a i) y', ENNReal.ofReal (Real.exp (-t * C.dd y x)) := by
  obtain ⟨hlat, hΩ, hΩ1⟩ := hy'
  -- on the cell, `d(y, x) ≤ d(y, y') + 2`
  have hpt : ∀ x ∈ cellOpen (C.a i) y',
      ENNReal.ofReal (Real.exp (-t * (C.dd y y' + 2))) ≤ ENNReal.ofReal (Real.exp (-t * C.dd y x)) := by
    intro x hx
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
    have h2 : C.dd y' x ≤ 2 := by
      have := C.wdist_cell_le hi hlat hΩ hΩ1 (x := x) fun ν => (hx ν).le
      unfold dd
      exact (ENNReal.toReal_le_toReal (wdist_ne_top _ _ _) ENNReal.ofReal_ne_top).mpr this
        |>.trans (by rw [ENNReal.toReal_ofReal (by norm_num)])
    have := C.dd_triangle y y' x
    nlinarith
  have hvol := volume_cellOpen_ge (C.a_pos i) (C.a_le_p hi) y'
  calc ENNReal.ofReal (C.a i ^ 4) * ENNReal.ofReal (Real.exp (-t * C.dd y y'))
      = ENNReal.ofReal (Real.exp (2 * t)) *
          (ENNReal.ofReal (Real.exp (-t * (C.dd y y' + 2))) * ENNReal.ofReal (C.a i ^ 4)) := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [mul_comm (Real.exp _) (C.a i ^ 4), ← mul_assoc, mul_comm (Real.exp (2 * t)),
          mul_assoc, ← Real.exp_add]
        congr 2; ring
    _ ≤ ENNReal.ofReal (Real.exp (2 * t)) *
          (ENNReal.ofReal (Real.exp (-t * (C.dd y y' + 2))) * volume (cellOpen (C.a i) y')) := by
        gcongr
    _ = ENNReal.ofReal (Real.exp (2 * t)) *
          ∫⁻ _x in cellOpen (C.a i) y', ENNReal.ofReal (Real.exp (-t * (C.dd y y' + 2))) := by
        rw [setLIntegral_const]
    _ ≤ ENNReal.ofReal (Real.exp (2 * t)) *
          ∫⁻ x in cellOpen (C.a i) y', ENNReal.ofReal (Real.exp (-t * C.dd y x)) := by
        refine mul_le_mul_of_nonneg_left ?_ zero_le
        exact setLIntegral_mono (by
          exact (ENNReal.measurable_ofReal.comp (Real.continuous_exp.comp
            (continuous_const.mul (C.continuous_dd y))).measurable)) hpt

/-! ### The integral over a layer by the measure of the sublevel sets -/

/-- `∫_{r > g} te^{-tr} dr = e^{-tg}`. -/
lemma integral_tail {t : ℝ} (ht : 0 < t) (g : ℝ) :
    ∫ r in Ioi g, t * Real.exp (-t * r) = Real.exp (-t * g) := by
  have hderiv : ∀ r ∈ Ici g, HasDerivAt (fun r => -Real.exp (-t * r)) (t * Real.exp (-t * r)) r := by
    intro r _
    have h1 : HasDerivAt (fun r : ℝ => -t * r) (-t) r := by
      simpa using (hasDerivAt_id r).const_mul (-t)
    have h3 := h1.exp.neg
    convert h3 using 1; ring
  have hint : IntegrableOn (fun r => t * Real.exp (-t * r)) (Ioi g) :=
    (exp_neg_integrableOn_Ioi g ht).const_mul t
  have hlim : Filter.Tendsto (fun r => -Real.exp (-t * r)) Filter.atTop (nhds 0) := by
    have : Filter.Tendsto (fun r => Real.exp (-t * r)) Filter.atTop (nhds 0) := by
      have h1 : Filter.Tendsto (fun r : ℝ => -t * r) Filter.atTop Filter.atBot :=
        Filter.tendsto_id.const_mul_atTop_of_neg (by linarith)
      exact Real.tendsto_exp_atBot.comp h1
    simpa using this.neg
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint hlim]
  ring

lemma lintegral_tail {t : ℝ} (ht : 0 < t) {g : ℝ} (hg : 0 ≤ g) :
    ∫⁻ r in Ioi 0, (Ioi g).indicator (fun r => ENNReal.ofReal (t * Real.exp (-t * r))) r =
      ENNReal.ofReal (Real.exp (-t * g)) := by
  rw [lintegral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    show Ioi g ∩ Ioi (0 : ℝ) = Ioi g by
      ext r; simp only [mem_inter_iff, Set.mem_Ioi]; constructor
      · exact fun h => h.1
      · exact fun h => ⟨h, lt_of_le_of_lt hg h⟩]
  rw [← ofReal_integral_eq_lintegral_ofReal ((exp_neg_integrableOn_Ioi g ht).const_mul t)
    (ae_of_all _ fun r => by positivity), integral_tail ht]

/-- Tonelli: `∫_U e^{-td(y,x)}dx = ∫_{r>0} te^{-tr}|U ∩ {d(y, ·) < r}|dr`. -/
theorem lintegral_exp_eq {t : ℝ} (ht : 0 < t) (U : Set (Tor p)) (y : Tor p) :
    ∫⁻ x in U, ENNReal.ofReal (Real.exp (-t * C.dd y x)) =
      ∫⁻ r in Ioi 0, ENNReal.ofReal (t * Real.exp (-t * r)) * volume (U ∩ {x | C.dd y x < r}) := by
  set S : Set (Tor p × ℝ) := {q | C.dd y q.1 < q.2}
  have hS : MeasurableSet S :=
    (isOpen_lt ((C.continuous_dd y).comp continuous_fst) continuous_snd).measurableSet
  set F : Tor p → ℝ → ℝ≥0∞ := fun x r =>
    S.indicator (fun q => ENNReal.ofReal (t * Real.exp (-t * q.2))) (x, r)
  have hF : Measurable (Function.uncurry F) := by
    refine Measurable.indicator ?_ hS
    exact ENNReal.measurable_ofReal.comp (measurable_const.mul
      (Real.measurable_exp.comp (measurable_const.mul measurable_snd)))
  have hpt : ∀ x, ∫⁻ r in Ioi 0, F x r = ENNReal.ofReal (Real.exp (-t * C.dd y x)) := by
    intro x
    rw [← lintegral_tail ht (C.dd_nonneg y x)]
    rfl
  calc ∫⁻ x in U, ENNReal.ofReal (Real.exp (-t * C.dd y x))
      = ∫⁻ x in U, ∫⁻ r in Ioi 0, F x r := by simp_rw [hpt]
    _ = ∫⁻ r in Ioi 0, ∫⁻ x in U, F x r := lintegral_lintegral_swap hF.aemeasurable
    _ = ∫⁻ r in Ioi 0, ENNReal.ofReal (t * Real.exp (-t * r)) * volume (U ∩ {x | C.dd y x < r}) := by
        refine lintegral_congr fun r => ?_
        have hmeas : MeasurableSet {x | C.dd y x < r} :=
          (isOpen_lt (C.continuous_dd y) continuous_const).measurableSet
        have e : (fun x => F x r) =
            {x | C.dd y x < r}.indicator (fun _ => ENNReal.ofReal (t * Real.exp (-t * r))) := by
          funext x; simp only [F, S, indicator, mem_setOf_eq]
        rw [e, lintegral_indicator_const hmeas, Measure.restrict_apply hmeas, inter_comm]

/-- `∫_0^∞ r⁴e^{-cr}dr = 4!/c⁵`. -/
lemma lintegral_pow_four_exp {c : ℝ} (hc : 0 < c) :
    ∫⁻ r in Ioi 0, ENNReal.ofReal (r ^ 4 * Real.exp (-c * r)) = ENNReal.ofReal (24 / c ^ 5) := by
  have hint : IntegrableOn (fun r : ℝ => r ^ (4 : ℝ) * Real.exp (-c * r ^ (1 : ℝ))) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow (by norm_num) (by norm_num) hc
  have hcongr : EqOn (fun r : ℝ => r ^ (4 : ℝ) * Real.exp (-c * r ^ (1 : ℝ)))
      (fun r => r ^ 4 * Real.exp (-c * r)) (Ioi 0) := fun r _ => by
    simp only [Real.rpow_one]
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hint' : IntegrableOn (fun r : ℝ => r ^ 4 * Real.exp (-c * r)) (Ioi 0) :=
    hint.congr_fun hcongr measurableSet_Ioi
  rw [← ofReal_integral_eq_lintegral_ofReal hint' (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have : (0 : ℝ) < r := hr
    positivity)]
  congr 1
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 5) (r := c) (by norm_num) hc
  have hg : Real.Gamma 5 = 24 := by
    have := Real.Gamma_nat_eq_factorial 4
    norm_num at this ⊢; try linarith
  rw [hg] at h
  have hcongr2 : EqOn (fun r : ℝ => r ^ ((5 : ℝ) - 1) * Real.exp (-(c * r)))
      (fun r => r ^ 4 * Real.exp (-c * r)) (Ioi 0) := fun r _ => by
    simp only
    rw [show (5 : ℝ) - 1 = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, neg_mul]
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr2] at h
  rw [h, Real.div_rpow zero_le_one hc.le, Real.one_rpow,
    show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  ring

/-- The bound of the integral over a set of points of the layer `i`, for `y ∈ Γ_j` and
`16 log L ≤ t·RM`: `∫_U e^{-td(y,x)}dx ≤ 16·4⁵ a_{j+1}⁴ e^{-t r_i/2}/t⁴`, `r_i = RM max{|i - j| - 1, 0}`. -/
theorem layer_bound {t : ℝ} (ht : 0 < t) (hRM : 0 < C.RM)
    (hRMt : 16 * Real.log C.L ≤ t * C.RM) {j : ℕ} {y : Tor p} (hyj : y ∈ C.Ω j)
    (hyj1 : y ∉ C.Ω (j + 1)) {i : ℕ} (U : Set (Tor p))
    (hU : ∀ x ∈ U, x ∈ C.Ω i ∧ x ∉ C.Ω (i + 1)) :
    ∫⁻ x in U, ENNReal.ofReal (Real.exp (-t * C.dd y x)) ≤
      ENNReal.ofReal (16 * 4 ^ 5 * C.a (j + 1) ^ 4 *
        Real.exp (-(t / 2) * (C.RM * max (|(i : ℝ) - j| - 1) 0)) / t ^ 4) := by
  set ri := C.RM * max (|(i : ℝ) - j| - 1) 0
  have hri : 0 ≤ ri := mul_nonneg hRM.le (le_max_right _ _)
  set a := C.a (j + 1)
  have ha := C.a_pos (j + 1)
  have hL := C.L_pos
  have hL1 : (1 : ℝ) ≤ C.L := by have := C.three_le_L; exact_mod_cast (by omega : 1 ≤ C.L)
  set c0 := t * (16 / 24) * a ^ 4 * Real.exp (-(t / 2) * ri)
  have hc0 : 0 ≤ c0 := by positivity
  rw [C.lintegral_exp_eq ht U y]
  -- the points of `U` are at a weighted distance of at least `r_i`
  have hfar : ∀ x ∈ U, ri ≤ C.dd y x := by
    intro x hx
    have := wdist_ge_layers C.D (R := C.RM) (M := 1) C.sep hyj hyj1 (hU x hx).1 (hU x hx).2
    rw [← C.ofReal_dd] at this
    have h2 := (ENNReal.ofReal_le_ofReal_iff (C.dd_nonneg y x)).mp this
    simp only [ri, mul_one] at h2 ⊢
    rwa [abs_sub_comm] at h2
  -- the pointwise bound in `r`
  have hpt : ∀ r ∈ Ioi (0 : ℝ),
      ENNReal.ofReal (t * Real.exp (-t * r)) * volume (U ∩ {x | C.dd y x < r}) ≤
        ENNReal.ofReal (c0 * (r ^ 4 * Real.exp (-(t / 4) * r))) := by
    intro r hr
    have hr0 : (0 : ℝ) < r := hr
    by_cases hrri : r ≤ ri
    · have : U ∩ {x | C.dd y x < r} = ∅ := by
        ext x; simp only [mem_inter_iff, mem_setOf_eq, mem_empty_iff_false, iff_false, not_and,
          not_lt]
        exact fun hx => hrri.trans (hfar x hx)
      rw [this, measure_empty, mul_zero]; exact zero_le
    · push_neg at hrri
      set ρ := a * (C.L : ℝ) ^ (r / C.RM) * r
      have hsub : U ∩ {x | C.dd y x < r} ⊆ {x | dist1 x y < ρ} := by
        intro x ⟨_, hx⟩
        refine C.dist1_lt_of_wdist_lt hRM hyj1 ?_
        rw [← C.ofReal_dd]
        exact (ENNReal.ofReal_lt_ofReal_iff hr0).mpr hx
      refine (mul_le_mul_of_nonneg_left ((measure_mono hsub).trans (volume_dist1_lt_le y ρ))
        zero_le).trans ?_
      rw [← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      -- `L^{4r/RM} ≤ e^{tr/4}` and `e^{-3tr/4} ≤ e^{-tr_i/2}e^{-tr/4}`
      have hLp : ((C.L : ℝ) ^ (r / C.RM)) ^ 4 ≤ Real.exp (t / 4 * r) := by
        rw [← Real.rpow_natCast ((C.L : ℝ) ^ (r / C.RM)) 4, ← Real.rpow_mul hL.le,
          Real.rpow_def_of_pos hL]
        refine Real.exp_le_exp.mpr ?_
        have hlog : 0 ≤ Real.log C.L := Real.log_nonneg hL1
        rw [show Real.log C.L * (r / C.RM * ((4 : ℕ) : ℝ)) = (4 * Real.log C.L / C.RM) * r by
          push_cast; field_simp]
        refine mul_le_mul_of_nonneg_right ?_ hr0.le
        rw [div_le_iff₀ hRM]; linarith
      have he : Real.exp (-t * r) * Real.exp (t / 4 * r) ≤
          Real.exp (-(t / 2) * ri) * Real.exp (-(t / 4) * r) := by
        rw [← Real.exp_add, ← Real.exp_add]
        refine Real.exp_le_exp.mpr ?_
        nlinarith
      have hρ4 : ρ ^ 4 = a ^ 4 * ((C.L : ℝ) ^ (r / C.RM)) ^ 4 * r ^ 4 := by
        simp only [ρ]; ring
      rw [hρ4]
      calc t * Real.exp (-t * r) * (16 * (a ^ 4 * ((C.L : ℝ) ^ (r / C.RM)) ^ 4 * r ^ 4) / 24)
          = t * (16 / 24) * a ^ 4 * r ^ 4 *
              (Real.exp (-t * r) * ((C.L : ℝ) ^ (r / C.RM)) ^ 4) := by ring
        _ ≤ t * (16 / 24) * a ^ 4 * r ^ 4 * (Real.exp (-t * r) * Real.exp (t / 4 * r)) := by
            gcongr
        _ ≤ t * (16 / 24) * a ^ 4 * r ^ 4 *
              (Real.exp (-(t / 2) * ri) * Real.exp (-(t / 4) * r)) := by gcongr
        _ = c0 * (r ^ 4 * Real.exp (-(t / 4) * r)) := by simp only [c0]; ring
  calc ∫⁻ r in Ioi 0, ENNReal.ofReal (t * Real.exp (-t * r)) * volume (U ∩ {x | C.dd y x < r})
      ≤ ∫⁻ r in Ioi 0, ENNReal.ofReal (c0 * (r ^ 4 * Real.exp (-(t / 4) * r))) :=
        setLIntegral_mono (ENNReal.measurable_ofReal.comp (measurable_const.mul
          ((measurable_id.pow_const 4).mul (Real.measurable_exp.comp
            (measurable_const.mul measurable_id))))) hpt
    _ = ENNReal.ofReal c0 * ∫⁻ r in Ioi 0, ENNReal.ofReal (r ^ 4 * Real.exp (-(t / 4) * r)) := by
        simp_rw [ENNReal.ofReal_mul hc0]
        exact lintegral_const_mul _ (by fun_prop)
    _ = ENNReal.ofReal c0 * ENNReal.ofReal (24 / (t / 4) ^ 5) := by
        rw [lintegral_pow_four_exp (by positivity)]
    _ = ENNReal.ofReal (16 * 4 ^ 5 * a ^ 4 * Real.exp (-(t / 2) * ri) / t ^ 4) := by
        rw [← ENNReal.ofReal_mul hc0]
        congr 1
        simp only [c0]
        field_simp

/-! ### The determining set -/

lemma inLat_zero {i : ℕ} {y : Tor p} (hy : InLat (C.a i) y) : InLat (C.a 0) y := by
  induction i with
  | zero => exact hy
  | succ i ih => exact ih (C.inLat_succ hy)

/-- The lattice of the spacing `a_0` is finite: its points are `(n_νa_0)_ν` with `0 ≤ n_ν < q`. -/
lemma finite_inLat0 : {y : Tor p | InLat (C.a 0) y}.Finite := by
  have hp := C.p_eq_mul (j := 0) (Nat.zero_le _)
  set q := 2 * C.L ^ (C.mT + C.k - 0) with hq
  have hq0 : 0 < q := C.q_pos 0
  have hqz : (0 : ℤ) < q := by exact_mod_cast hq0
  refine (Set.finite_range (fun f : Fin 4 → Fin q =>
    fun ν => ((((f ν : ℕ) : ℝ) * C.a 0 : ℝ) : AddCircle p))).subset ?_
  intro y hy
  choose n hn using (hy : InLat (C.a 0) y)
  refine ⟨fun ν => ⟨(n ν % (q : ℤ)).toNat, by
    have h1 := Int.emod_nonneg (n ν) hqz.ne'
    have h2 := Int.emod_lt_of_pos (n ν) hqz
    omega⟩, ?_⟩
  funext ν
  simp only
  rw [hn ν]
  have h1 := Int.emod_nonneg (n ν) hqz.ne'
  have hc : (((n ν % (q : ℤ)).toNat : ℕ) : ℝ) = ((n ν % (q : ℤ) : ℤ) : ℝ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg h1]
  rw [hc]
  have e : ((n ν : ℤ) : ℝ) * C.a 0 =
      ((n ν % (q : ℤ) : ℤ) : ℝ) * C.a 0 + (n ν / (q : ℤ)) • p := by
    rw [zsmul_eq_mul]
    have h' : ((n ν : ℤ) : ℝ) = ((n ν % (q : ℤ) : ℤ) : ℝ) + (q : ℝ) * ((n ν / (q : ℤ) : ℤ) : ℝ) := by
      have h0 := Int.mul_ediv_add_emod (n ν) (q : ℤ)
      exact_mod_cast (by linarith : n ν = n ν % (q : ℤ) + (q : ℤ) * (n ν / (q : ℤ)))
    linear_combination (C.a 0) * h' - ((n ν / (q : ℤ) : ℤ) : ℝ) * hp
  rw [e, AddCircle.coe_add, (AddCircle.coe_eq_zero_iff p).mpr ⟨_, rfl⟩, add_zero]

lemma finite_Gam (i : ℕ) : (C.Gam i).Finite :=
  C.finite_inLat0.subset fun _ hy => C.inLat_zero hy.1

/-- The layer `Γ_i` as a finite set. -/
def GamF (i : ℕ) : Finset (Tor p) := (C.finite_Gam i).toFinset

/-- The determining set `𝐁 = ⨆_{j=0}^k Γ_j`. -/
def BF : Finset (Tor p) := (Finset.range (C.k + 1)).biUnion C.GamF

lemma mem_GamF {i : ℕ} {y : Tor p} : y ∈ C.GamF i ↔ y ∈ C.Gam i := Set.Finite.mem_toFinset _

lemma Ω_anti : Antitone C.Ω := antitone_nat_of_succ_le C.Ω_succ

lemma Gam_disjoint {i i' : ℕ} (h : i ≠ i') : Disjoint (C.GamF i) (C.GamF i') := by
  rw [Finset.disjoint_left]
  intro y hy hy'
  rw [mem_GamF] at hy hy'
  rcases lt_or_gt_of_ne h with hlt | hlt
  · exact hy.2.2 (C.Ω_anti (Nat.succ_le_of_lt hlt) hy'.2.1)
  · exact hy'.2.2 (C.Ω_anti (Nat.succ_le_of_lt hlt) hy.2.1)

/-! ### The sum over the layers -/

/-- `Σ_{i < n} 2^{-|i - j|} ≤ 3`. -/
lemma sum_half_pow_dist (j n : ℕ) :
    ∑ i ∈ Finset.range n, (1 / 2 : ℝ) ^ Nat.dist i j ≤ 3 := by
  have key : ∀ n, (n ≤ j → ∑ i ∈ Finset.range n, (1 / 2 : ℝ) ^ Nat.dist i j ≤ (1 / 2) ^ (j - n)) ∧
      (j ≤ n → ∑ i ∈ Finset.range n, (1 / 2 : ℝ) ^ Nat.dist i j ≤ 3 - 2 * (1 / 2) ^ (n - j)) := by
    intro n
    induction n with
    | zero =>
      refine ⟨fun _ => by rw [Finset.sum_range_zero]; positivity, fun h => ?_⟩
      rw [Finset.sum_range_zero, show 0 - j = 0 by omega]
      norm_num
    | succ n ih =>
      rw [Finset.sum_range_succ]
      refine ⟨fun h => ?_, fun h => ?_⟩
      · have h1 := ih.1 (by omega)
        rw [Nat.dist_eq_sub_of_le (by omega : n ≤ j)]
        have e : j - n = (j - (n + 1)) + 1 := by omega
        rw [e, pow_succ] at h1 ⊢
        linarith
      · rcases Nat.lt_or_ge n j with hnj | hnj
        · have h1 := ih.1 hnj.le
          rw [show j - n = 1 by omega] at h1
          rw [Nat.dist_eq_sub_of_le hnj.le, show j - n = 1 by omega, show n + 1 - j = 0 by omega]
          norm_num at h1 ⊢
          linarith
        · have h1 := ih.2 hnj
          rw [Nat.dist_eq_sub_of_le_right hnj, show n + 1 - j = (n - j) + 1 by omega, pow_succ]
          linarith
  rcases le_total n j with h | h
  · exact ((key n).1 h).trans ((pow_le_one₀ (by norm_num) (by norm_num)).trans (by norm_num))
  · have : (0 : ℝ) ≤ (1 / 2) ^ (n - j) := by positivity
    linarith [(key n).2 h]

lemma a_ratio_le (i j : ℕ) : C.a (j + 1) / C.a i ≤ (C.L : ℝ) ^ (Nat.dist i j + 1) := by
  have hL := C.L_pos
  have hL1 : (1 : ℝ) ≤ C.L := by have := C.three_le_L; exact_mod_cast (by omega : 1 ≤ C.L)
  rw [div_le_iff₀ (C.a_pos i)]
  unfold a aa
  rw [← mul_div_assoc, ← pow_add]
  refine div_le_div_of_nonneg_right (pow_le_pow_right₀ hL1 ?_) (by positivity)
  unfold Nat.dist
  omega

/-- For `16 log L + 4 ≤ t·RM`: `(a_{j+1}/a_i)⁴e^{-(t/2)RM max{|i - j| - 1, 0}} ≤ 2L⁸2^{-|i - j|}`. -/
lemma term_le {t : ℝ} (hRMt : 16 * Real.log C.L + 4 ≤ t * C.RM) (i j : ℕ) :
    (C.a (j + 1) / C.a i) ^ 4 * Real.exp (-(t / 2) * (C.RM * max (|(i : ℝ) - j| - 1) 0)) ≤
      2 * (C.L : ℝ) ^ 8 * (1 / 2) ^ Nat.dist i j := by
  have hL := C.L_pos
  have hL1 : (1 : ℝ) ≤ C.L := by have := C.three_le_L; exact_mod_cast (by omega : 1 ≤ C.L)
  have hlog : 0 ≤ Real.log C.L := Real.log_nonneg hL1
  have hrat := C.a_ratio_le i j
  have hrat0 : 0 ≤ C.a (j + 1) / C.a i := by
    have := C.a_pos i; have := C.a_pos (j + 1); positivity
  have habs : |(i : ℝ) - j| = (Nat.dist i j : ℝ) := by
    rcases le_total i j with h | h
    · have : (i : ℝ) ≤ j := by exact_mod_cast h
      rw [Nat.dist_eq_sub_of_le h, Nat.cast_sub h, abs_sub_comm, abs_of_nonneg (by linarith)]
    · have : (j : ℝ) ≤ i := by exact_mod_cast h
      rw [Nat.dist_eq_sub_of_le_right h, Nat.cast_sub h, abs_of_nonneg (by linarith)]
  rw [habs]
  set m := Nat.dist i j
  rcases Nat.eq_zero_or_pos m with hm | hm
  · rw [hm] at hrat ⊢
    simp only [Nat.cast_zero, zero_sub, pow_zero, mul_one,
      max_eq_right (show (-1 : ℝ) ≤ 0 by norm_num), mul_zero, Real.exp_zero]
    have h4 : (C.a (j + 1) / C.a i) ^ 4 ≤ ((C.L : ℝ) ^ (0 + 1)) ^ 4 := pow_le_pow_left₀ hrat0 hrat 4
    have h8 : (C.L : ℝ) ^ 4 ≤ (C.L : ℝ) ^ 8 := pow_le_pow_right₀ hL1 (by norm_num)
    have : (0 : ℝ) ≤ (C.L : ℝ) ^ 8 := by positivity
    rw [show ((C.L : ℝ) ^ (0 + 1)) ^ 4 = (C.L : ℝ) ^ 4 by ring] at h4
    linarith
  · obtain ⟨m', hm'⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rw [hm'] at hrat ⊢
    rw [Nat.cast_add_one, show ((m' : ℝ) + 1 - 1) = m' by ring, max_eq_left (Nat.cast_nonneg m')]
    have hm0 : (0 : ℝ) ≤ m' := Nat.cast_nonneg m'
    have hE : Real.exp (-(t / 2) * (C.RM * m')) ≤ Real.exp (-(8 * Real.log C.L + 2) * m') := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_right hRMt hm0]
    have hP : ((C.L : ℝ) ^ (m' + 1 + 1)) ^ 4 = (C.L : ℝ) ^ 8 * Real.exp (4 * m' * Real.log C.L) := by
      rw [show (4 : ℝ) * m' * Real.log C.L = ((4 * m' : ℕ) : ℝ) * Real.log C.L by push_cast; ring,
        Real.exp_nat_mul, Real.exp_log hL, ← pow_mul, ← pow_add]
      congr 1; ring
    have he2 : Real.exp (-2) ≤ 1 / 2 := by
      have h2 : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp 2]
      calc Real.exp (-2) = (Real.exp 2)⁻¹ := Real.exp_neg 2
        _ ≤ 2⁻¹ := inv_anti₀ (by norm_num) h2
        _ = 1 / 2 := by norm_num
    have hhalf : Real.exp (-2 * m') ≤ (1 / 2 : ℝ) ^ m' := by
      rw [show (-2 : ℝ) * m' = m' * (-2) by ring, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos _).le he2 m'
    calc (C.a (j + 1) / C.a i) ^ 4 * Real.exp (-(t / 2) * (C.RM * m'))
        ≤ ((C.L : ℝ) ^ (m' + 1 + 1)) ^ 4 * Real.exp (-(8 * Real.log C.L + 2) * m') :=
          mul_le_mul (pow_le_pow_left₀ hrat0 hrat 4) hE (Real.exp_pos _).le (by positivity)
      _ = (C.L : ℝ) ^ 8 * (Real.exp (4 * m' * Real.log C.L) *
            Real.exp (-(8 * Real.log C.L + 2) * m')) := by rw [hP]; ring
      _ = (C.L : ℝ) ^ 8 * Real.exp (-4 * m' * Real.log C.L - 2 * m') := by
          rw [← Real.exp_add]; congr 2; ring
      _ ≤ (C.L : ℝ) ^ 8 * Real.exp (-2 * m') :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hm0 hlog]))
            (by positivity)
      _ ≤ (C.L : ℝ) ^ 8 * (1 / 2) ^ m' := mul_le_mul_of_nonneg_left hhalf (by positivity)
      _ = 2 * (C.L : ℝ) ^ 8 * (1 / 2) ^ (m' + 1) := by rw [pow_succ]; ring

/-- The sum over a layer: for `y ∈ Ω_j \ Ω_{j+1}` and `16 log L ≤ t·RM`,
`Σ_{y' ∈ Γ_i} e^{-td(y,y')} ≤ 2¹⁴e^{2t}t⁻⁴(a_{j+1}/a_i)⁴e^{-(t/2)r_i}`. -/
theorem layer_sum {t : ℝ} (ht : 0 < t) (hRM : 0 < C.RM) (hRMt : 16 * Real.log C.L ≤ t * C.RM)
    {j : ℕ} {y : Tor p} (hyj : y ∈ C.Ω j) (hyj1 : y ∉ C.Ω (j + 1)) {i : ℕ} (hi : i ≤ C.k) :
    ∑ y' ∈ C.GamF i, Real.exp (-t * C.dd y y') ≤
      2 ^ 14 * Real.exp (2 * t) / t ^ 4 * ((C.a (j + 1) / C.a i) ^ 4 *
        Real.exp (-(t / 2) * (C.RM * max (|(i : ℝ) - j| - 1) 0))) := by
  set U := ⋃ y' ∈ C.GamF i, cellOpen (C.a i) y'
  have hU : ∀ x ∈ U, x ∈ C.Ω i ∧ x ∉ C.Ω (i + 1) := by
    intro x hx
    simp only [U, Set.mem_iUnion] at hx
    obtain ⟨y', hy', hx⟩ := hx
    rw [mem_GamF] at hy'
    exact ⟨C.cell_subset_Ω hy'.1 hy'.2.1 fun ν => (hx ν).le,
      C.cellOpen_disjoint hi hy'.1 hy'.2.2 hx⟩
  have hLB := C.layer_bound ht hRM hRMt hyj hyj1 U hU
  have hdisj : (C.GamF i : Set (Tor p)).PairwiseDisjoint fun y' => cellOpen (C.a i) y' := by
    intro y₁ h₁ y₂ h₂ hne
    rw [Function.onFun, Set.disjoint_left]
    intro x hx1 hx2
    apply hne
    have h₁' := (C.mem_GamF).mp h₁
    have h₂' := (C.mem_GamF).mp h₂
    refine eq_of_lt (C.a_pos i) (C.q_pos i) (C.p_eq_mul hi) h₁'.1 h₂'.1 fun ν => ?_
    calc ‖y₁ ν - y₂ ν‖ = ‖(x ν - y₂ ν) - (x ν - y₁ ν)‖ := by congr 1; abel
      _ ≤ ‖x ν - y₂ ν‖ + ‖x ν - y₁ ν‖ := norm_sub_le _ _
      _ < C.a i / 2 + C.a i / 2 := add_lt_add (hx2 ν) (hx1 ν)
      _ = C.a i := by ring
  have hsumE : ∑ y' ∈ C.GamF i,
      ∫⁻ x in cellOpen (C.a i) y', ENNReal.ofReal (Real.exp (-t * C.dd y x)) =
        ∫⁻ x in U, ENNReal.ofReal (Real.exp (-t * C.dd y x)) :=
    (lintegral_biUnion_finset hdisj (fun y' _ => measurableSet_cellOpen _ _) _).symm
  have hai := C.a_pos i
  have hpt : ∀ y' ∈ C.GamF i, ENNReal.ofReal (Real.exp (-t * C.dd y y')) ≤
      ENNReal.ofReal ((C.a i ^ 4)⁻¹ * Real.exp (2 * t)) *
        ∫⁻ x in cellOpen (C.a i) y', ENNReal.ofReal (Real.exp (-t * C.dd y x)) := by
    intro y' hy'
    have h := C.average_cell ht.le hi ((C.mem_GamF).mp hy') y
    calc ENNReal.ofReal (Real.exp (-t * C.dd y y'))
        = ENNReal.ofReal ((C.a i ^ 4)⁻¹) *
            (ENNReal.ofReal (C.a i ^ 4) * ENNReal.ofReal (Real.exp (-t * C.dd y y'))) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), inv_mul_cancel₀ (by positivity),
            ENNReal.ofReal_one, one_mul]
      _ ≤ ENNReal.ofReal ((C.a i ^ 4)⁻¹) * (ENNReal.ofReal (Real.exp (2 * t)) *
            ∫⁻ x in cellOpen (C.a i) y', ENNReal.ofReal (Real.exp (-t * C.dd y x))) :=
          mul_le_mul_of_nonneg_left h zero_le
      _ = ENNReal.ofReal ((C.a i ^ 4)⁻¹ * Real.exp (2 * t)) *
            ∫⁻ x in cellOpen (C.a i) y', ENNReal.ofReal (Real.exp (-t * C.dd y x)) := by
          rw [ENNReal.ofReal_mul (by positivity), mul_assoc]
  have hE : ENNReal.ofReal (∑ y' ∈ C.GamF i, Real.exp (-t * C.dd y y')) ≤
      ENNReal.ofReal (2 ^ 14 * Real.exp (2 * t) / t ^ 4 * ((C.a (j + 1) / C.a i) ^ 4 *
        Real.exp (-(t / 2) * (C.RM * max (|(i : ℝ) - j| - 1) 0)))) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => (Real.exp_pos _).le)]
    calc ∑ y' ∈ C.GamF i, ENNReal.ofReal (Real.exp (-t * C.dd y y'))
        ≤ ∑ y' ∈ C.GamF i, ENNReal.ofReal ((C.a i ^ 4)⁻¹ * Real.exp (2 * t)) *
            ∫⁻ x in cellOpen (C.a i) y', ENNReal.ofReal (Real.exp (-t * C.dd y x)) :=
          Finset.sum_le_sum hpt
      _ = ENNReal.ofReal ((C.a i ^ 4)⁻¹ * Real.exp (2 * t)) *
            ∫⁻ x in U, ENNReal.ofReal (Real.exp (-t * C.dd y x)) := by
          rw [← Finset.mul_sum, hsumE]
      _ ≤ ENNReal.ofReal ((C.a i ^ 4)⁻¹ * Real.exp (2 * t)) *
            ENNReal.ofReal (16 * 4 ^ 5 * C.a (j + 1) ^ 4 *
              Real.exp (-(t / 2) * (C.RM * max (|(i : ℝ) - j| - 1) 0)) / t ^ 4) :=
          mul_le_mul_of_nonneg_left hLB zero_le
      _ = _ := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [div_pow]
          field_simp; ring
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hE

/-- `r₁(α, δ) = max{1, (16 log L + 4)/(αδ)}`. -/
def r1 (α δ : ℝ) : ℝ := max 1 ((16 * Real.log C.L + 4) / (α * δ))

/-- `c₁(α, δ) = 2²¹L⁸e^{2αδ}(αδ)⁻⁴`. -/
def c1 (α δ : ℝ) : ℝ := 2 ^ 21 * (C.L : ℝ) ^ 8 * Real.exp (2 * (α * δ)) * (α * δ)⁻¹ ^ 4

/-- `eq:summation`: for `RM ≥ r₁(α, δ)` and `y ∈ 𝐁`, `Σ_{y' ∈ 𝐁} e^{-αδd(y, y')} ≤ c₁(α, δ)`. -/
theorem summation {α δ : ℝ} (hα : 0 < α) (hδ : 0 < δ) (hRM : C.r1 α δ ≤ C.RM) {y : Tor p}
    (hy : y ∈ C.BF) : ∑ y' ∈ C.BF, Real.exp (-(α * δ * C.dd y y')) ≤ C.c1 α δ := by
  have ht : 0 < α * δ := mul_pos hα hδ
  have hRMpos : 0 < C.RM := lt_of_lt_of_le one_pos ((le_max_left _ _).trans hRM)
  have hRMt : 16 * Real.log C.L + 4 ≤ α * δ * C.RM := by
    have := (le_max_right _ _).trans hRM
    rw [div_le_iff₀ ht] at this
    linarith
  obtain ⟨j, -, hyj⟩ := Finset.mem_biUnion.mp hy
  have hyj' := (C.mem_GamF).mp hyj
  rw [BF, Finset.sum_biUnion (fun i _ i' _ h => C.Gam_disjoint h)]
  set t := α * δ with ht_def
  have hpos : (0 : ℝ) ≤ 2 ^ 14 * Real.exp (2 * t) / t ^ 4 := by positivity
  calc ∑ i ∈ Finset.range (C.k + 1), ∑ y' ∈ C.GamF i, Real.exp (-(t * C.dd y y'))
      ≤ ∑ i ∈ Finset.range (C.k + 1), 2 ^ 14 * Real.exp (2 * t) / t ^ 4 *
          ((C.a (j + 1) / C.a i) ^ 4 *
            Real.exp (-(t / 2) * (C.RM * max (|(i : ℝ) - j| - 1) 0))) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hik : i ≤ C.k := by rw [Finset.mem_range] at hi; omega
        have := C.layer_sum ht hRMpos (by linarith) hyj'.2.1 hyj'.2.2 hik
        simp only [neg_mul] at this ⊢
        exact this
    _ ≤ ∑ i ∈ Finset.range (C.k + 1), 2 ^ 14 * Real.exp (2 * t) / t ^ 4 *
          (2 * (C.L : ℝ) ^ 8 * (1 / 2) ^ Nat.dist i j) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (C.term_le hRMt i j) hpos
    _ = 2 ^ 14 * Real.exp (2 * t) / t ^ 4 * (2 * (C.L : ℝ) ^ 8 *
          ∑ i ∈ Finset.range (C.k + 1), (1 / 2 : ℝ) ^ Nat.dist i j) := by
        rw [Finset.mul_sum, Finset.mul_sum]
    _ ≤ 2 ^ 14 * Real.exp (2 * t) / t ^ 4 * (2 * (C.L : ℝ) ^ 8 * 3) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (sum_half_pow_dist j _)
          (by positivity)) hpos
    _ ≤ C.c1 α δ := by
        unfold c1
        rw [← ht_def, inv_pow, ← div_eq_mul_inv]
        have h0 : (0 : ℝ) ≤ (C.L : ℝ) ^ 8 * Real.exp (2 * t) / t ^ 4 := by positivity
        calc 2 ^ 14 * Real.exp (2 * t) / t ^ 4 * (2 * (C.L : ℝ) ^ 8 * 3)
            = (6 * 2 ^ 14) * ((C.L : ℝ) ^ 8 * Real.exp (2 * t) / t ^ 4) := by ring
          _ ≤ 2 ^ 21 * ((C.L : ℝ) ^ 8 * Real.exp (2 * t) / t ^ 4) :=
            mul_le_mul_of_nonneg_right (by norm_num) h0
          _ = 2 ^ 21 * (C.L : ℝ) ^ 8 * Real.exp (2 * t) / t ^ 4 := by ring

lemma one_le_c1 {α δ : ℝ} (hα : 0 < α) (hδ : 0 < δ) : 1 ≤ C.c1 α δ := by
  have ht : 0 < α * δ := mul_pos hα hδ
  set t := α * δ
  have hL8 : (1 : ℝ) ≤ (C.L : ℝ) ^ 8 :=
    one_le_pow₀ (by have := C.three_le_L; exact_mod_cast (by omega : 1 ≤ C.L))
  -- `e^{2t} ≥ (2t)⁴/4! = 2t⁴/3`, so `2²¹e^{2t}t⁻⁴ ≥ 2²²/3 ≥ 1`
  have hexp : (2 * t) ^ 4 / 24 ≤ Real.exp (2 * t) := by
    have := Real.pow_div_factorial_le_exp (2 * t) (by positivity) 4
    simpa [Nat.factorial] using this
  unfold c1
  rw [inv_pow]
  have ht4 : 0 < t ^ 4 := by positivity
  have h1 : 1 ≤ 2 ^ 21 * Real.exp (2 * t) * (t ^ 4)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ ht4]
    nlinarith
  calc (1 : ℝ) ≤ 1 * (2 ^ 21 * Real.exp (2 * t) * (t ^ 4)⁻¹) := by rw [one_mul]; exact h1
    _ ≤ (C.L : ℝ) ^ 8 * (2 ^ 21 * Real.exp (2 * t) * (t ^ 4)⁻¹) :=
        mul_le_mul_of_nonneg_right hL8 (by positivity)
    _ = 2 ^ 21 * (C.L : ℝ) ^ 8 * Real.exp (2 * t) * (t ^ 4)⁻¹ := by ring

open Classical in
/-- `eq:chain-summation` on the determining set: for `RM ≥ r₁(α, δ)`, `n ≥ 1`, and `y₀, y_n ∈ 𝐁`,
`Σ_{y_1, …, y_{n-1} ∈ 𝐁} Π_{i=1}^n e^{-δd(y_{i-1}, y_i)} ≤ c₁(α, δ)^{n-1}e^{-(1-α)δd(y₀, y_n)}`. -/
theorem chain_summation_B {α δ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hδ : 0 < δ)
    (hRM : C.r1 α δ ≤ C.RM) (n : ℕ) (hn : 1 ≤ n) (y₀ yₙ : C.BF) :
    (expKernel (fun y y' : C.BF => C.dd y y') δ ^ n) y₀ yₙ ≤
      C.c1 α δ ^ (n - 1) * Real.exp (-((1 - α) * δ * C.dd y₀ yₙ)) := by
  have hsum : ∀ y : C.BF, ∑ y' : C.BF, Real.exp (-(α * δ * C.dd y y')) ≤ C.c1 α δ := by
    intro y
    have h := C.summation hα hδ hRM y.2
    rwa [← Finset.sum_coe_sort C.BF (fun y' => Real.exp (-(α * δ * C.dd y y')))] at h
  exact CoreLean.chain_summation (fun y y' : C.BF => C.dd y y') (fun _ _ => C.dd_nonneg _ _)
    (fun _ _ _ => C.dd_triangle _ _ _) α δ (C.c1 α δ) hα.le hα1 hδ.le hsum n hn y₀ yₙ

end ContSeq

end Summation

end CoreLean
