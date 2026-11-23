/-
The measure on the torus for `eq:summation`: the lift `ℝ⁴ → (ℝ/pℤ)⁴` is measure preserving on a fundamental
box, so that an open cell of side `a ≤ p` has the measure `a⁴` at least, and the set of the points at an
`ℓ¹`-distance of less than `ρ` from a point has the measure `(2ρ)⁴/4!` at most.
-/
import CoreLean.SummationGeometry

open Set Finset MeasureTheory
open scoped ENNReal

noncomputable section

namespace CoreLean

namespace Summation

variable {p : ℝ} [Fact (0 < p)]

/-- The lift is measure preserving on the box `Π_ν (t_ν, t_ν + p]`. -/
lemma measurePreserving_projT (t : Fin 4 → ℝ) :
    MeasurePreserving (projT p) (volume.restrict (Set.univ.pi fun ν => Ioc (t ν) (t ν + p)))
      volume := by
  have h := measurePreserving_pi (fun _ : Fin 4 => volume.restrict (Ioc (t _) (t _ + p)))
    (fun _ : Fin 4 => (volume : Measure (AddCircle p)))
    (fun ν => AddCircle.measurePreserving_mk p (t ν))
  rw [← Measure.restrict_pi_pi] at h
  exact h

/-- An open cell of side `0 < a ≤ p` has the measure `a⁴` at least. -/
lemma volume_cellOpen_ge {a : ℝ} (ha : 0 < a) (hap : a ≤ p) (y : Tor p) :
    ENNReal.ofReal (a ^ 4) ≤ volume (cellOpen a y) := by
  -- a lift of `y`
  obtain ⟨yh, hyh⟩ : ∃ yh : Fin 4 → ℝ, projT p yh = y := by
    choose u hu using fun ν => QuotientAddGroup.mk_surjective (y ν)
    exact ⟨u, funext hu⟩
  set t : Fin 4 → ℝ := fun ν => yh ν - p / 2
  have hmp := measurePreserving_projT (p := p) t
  have hmeas : MeasurableSet (cellOpen a y) := by
    have : cellOpen a y = ⋂ ν, {z : Tor p | ‖z ν - y ν‖ < a / 2} := by ext; simp [cellOpen]
    rw [this]
    exact MeasurableSet.iInter fun ν =>
      (isOpen_lt ((continuous_apply ν).sub continuous_const).norm continuous_const).measurableSet
  rw [← hmp.measure_preimage hmeas.nullMeasurableSet]
  -- the open box lies in the preimage
  set box : Set (Fin 4 → ℝ) := Set.univ.pi fun ν => Ioo (yh ν - a / 2) (yh ν + a / 2)
  have hbox : box ⊆ projT p ⁻¹' cellOpen a y ∩ Set.univ.pi fun ν => Ioc (t ν) (t ν + p) := by
    intro u hu
    simp only [box, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioo] at hu
    refine ⟨fun ν => ?_, fun ν _ => ?_⟩
    · rw [← hyh]
      simp only [projT]
      refine lt_of_le_of_lt (norm_coe_sub_le _ _) ?_
      rw [abs_lt]; constructor <;> linarith [(hu ν).1, (hu ν).2]
    · simp only [t, Set.mem_Ioc]; constructor <;> linarith [(hu ν).1, (hu ν).2]
  calc ENNReal.ofReal (a ^ 4) = volume box := by
        have e : ∀ ν, yh ν + a / 2 - (yh ν - a / 2) = a := fun ν => by ring
        simp only [box, Real.volume_pi_Ioo, e, Finset.prod_const, Finset.card_univ,
          Fintype.card_fin]
        rw [ENNReal.ofReal_pow ha.le]
    _ ≤ volume (projT p ⁻¹' cellOpen a y ∩ Set.univ.pi fun ν => Ioc (t ν) (t ν + p)) :=
        measure_mono hbox
    _ = (volume.restrict (Set.univ.pi fun ν => Ioc (t ν) (t ν + p))) (projT p ⁻¹' cellOpen a y) := by
        rw [Measure.restrict_apply (hmeas.preimage (continuous_projT).measurable)]

/-- The points at an `ℓ¹`-distance of less than `ρ` from `y` have the measure `(2ρ)⁴/4!` at most. -/
lemma volume_dist1_lt_le (y : Tor p) (ρ : ℝ) :
    volume {x : Tor p | dist1 x y < ρ} ≤ ENNReal.ofReal (16 * ρ ^ 4 / 24) := by
  obtain ⟨yh, hyh⟩ : ∃ yh : Fin 4 → ℝ, projT p yh = y := by
    choose u hu using fun ν => QuotientAddGroup.mk_surjective (y ν)
    exact ⟨u, funext hu⟩
  set t : Fin 4 → ℝ := fun ν => yh ν - p / 2
  have hmp := measurePreserving_projT (p := p) t
  have hmeas : MeasurableSet {x : Tor p | dist1 x y < ρ} := by
    refine (isOpen_lt ?_ continuous_const).measurableSet
    exact continuous_finsetSum _ fun ν _ => ((continuous_apply ν).sub continuous_const).norm
  rw [← hmp.measure_preimage hmeas.nullMeasurableSet,
    Measure.restrict_apply (hmeas.preimage (continuous_projT).measurable)]
  -- on the box centred at `yh`, the circle distance is the absolute value
  have hsub : projT p ⁻¹' {x : Tor p | dist1 x y < ρ} ∩ (Set.univ.pi fun ν => Ioc (t ν) (t ν + p)) ⊆
      (fun u => u - yh) ⁻¹' {w : Fin 4 → ℝ | (∑ ν, |w ν| ^ (1 : ℝ)) ^ (1 / (1 : ℝ)) < ρ} := by
    intro u ⟨hu, hbox⟩
    simp only [Set.mem_preimage, Set.mem_setOf_eq, dist1] at hu ⊢
    simp only [Real.rpow_one, div_one, Pi.sub_apply]
    have e : ∀ ν, ‖(projT p u) ν - y ν‖ = |u ν - yh ν| := by
      intro ν
      rw [← hyh]
      simp only [projT]
      rw [← AddCircle.coe_sub, AddCircle.norm_coe_eq_abs_iff p (Fact.out : 0 < p).ne']
      have := hbox ν (Set.mem_univ ν)
      simp only [t, Set.mem_Ioc] at this
      rw [abs_of_pos (Fact.out : 0 < p), abs_le]; constructor <;> linarith [this.1, this.2]
    simpa [e] using hu
  calc volume (projT p ⁻¹' {x : Tor p | dist1 x y < ρ} ∩ Set.univ.pi fun ν => Ioc (t ν) (t ν + p))
      ≤ volume ((fun u => u - yh) ⁻¹' {w : Fin 4 → ℝ | (∑ ν, |w ν| ^ (1 : ℝ)) ^ (1 / (1 : ℝ)) < ρ}) :=
        measure_mono hsub
    _ = volume {w : Fin 4 → ℝ | (∑ ν, |w ν| ^ (1 : ℝ)) ^ (1 / (1 : ℝ)) < ρ} := by
        rw [show (fun u : Fin 4 → ℝ => u - yh) = fun u => u + (-yh) by funext u; abel]
        exact measure_preimage_add_right _ _ _
    _ = ENNReal.ofReal ρ ^ Fintype.card (Fin 4) * ENNReal.ofReal ((2 * Real.Gamma (1 / 1 + 1)) ^
          Fintype.card (Fin 4) / Real.Gamma (Fintype.card (Fin 4) / 1 + 1)) :=
        volume_sum_rpow_lt (Fin 4) le_rfl ρ
    _ ≤ ENNReal.ofReal (16 * ρ ^ 4 / 24) := by
        have g2 : Real.Gamma (1 / 1 + 1) = 1 := by norm_num [Real.Gamma_two]
        have g5 : Real.Gamma ((Fintype.card (Fin 4) : ℕ) / 1 + 1) = 24 := by
          rw [Fintype.card_fin, div_one]
          have := Real.Gamma_nat_eq_factorial 4
          norm_num at this ⊢
          try exact this
        rw [g2, g5, Fintype.card_fin]
        rcases le_or_gt 0 ρ with h | h
        · rw [← ENNReal.ofReal_pow h, ← ENNReal.ofReal_mul (by positivity)]
          apply le_of_eq; congr 1; ring
        · rw [ENNReal.ofReal_of_nonpos h.le]; simp

/-! ### The `ℓ¹`-ball which contains a sublevel set of the weighted distance -/

lemma dist1_comm' (z z' : Tor p) : dist1 z z' = dist1 z' z := by
  unfold dist1; congr 1; funext ν; exact norm_sub_rev _ _

/-- `w₀|z - z'|₁ ≤ ℓ(γ)` if the weight is at least `w₀ > 0` along the path. -/
lemma mul_dist1_le_wlen (D : DomainData p) {z z' : Tor p} (P : TPath p z z') {w₀ : ℝ}
    (hw0 : 0 ≤ w₀) (hw : ∀ t ∈ Icc 0 P.T, w₀ ≤ D.weight (projT p (P.γ t))) :
    ENNReal.ofReal (w₀ * dist1 z z') ≤ wlen D P.γ 0 P.T := by
  have h1 := ofReal_sum_abs_sub_le P.lip P.T_nonneg
  have h2 : dist1 z z' ≤ ∑ ν, |P.γ P.T ν - P.γ 0 ν| := by
    calc dist1 z z' = dist1 (projT p (P.γ 0)) (projT p (P.γ P.T)) := by rw [P.start, P.stop]
      _ ≤ ∑ ν, |P.γ 0 ν - P.γ P.T ν| := dist1_projT_le _ _
      _ = ∑ ν, |P.γ P.T ν - P.γ 0 ν| := Finset.sum_congr rfl fun ν _ => abs_sub_comm _ _
  rw [ENNReal.ofReal_mul hw0]
  calc ENNReal.ofReal w₀ * ENNReal.ofReal (dist1 z z')
      ≤ ENNReal.ofReal w₀ * ∫⁻ t in Icc 0 P.T, ∑ ν, ‖deriv (fun s => P.γ s ν) t‖ₑ := by
        gcongr; exact (ENNReal.ofReal_le_ofReal h2).trans h1
    _ = ∫⁻ t in Icc 0 P.T, ENNReal.ofReal w₀ * ∑ ν, ‖deriv (fun s => P.γ s ν) t‖ₑ := by
        rw [lintegral_const_mul _ (Finset.measurable_sum _ fun ν _ => (measurable_deriv _).enorm)]
    _ ≤ wlen D P.γ 0 P.T := by
        unfold wlen
        refine setLIntegral_mono (measurable_wIntegrand D P.lip.continuous) fun t ht => ?_
        unfold wIntegrand
        gcongr
        exact hw t ht

namespace ContSeq

variable (C : ContSeq p)

/-- The points at a weighted distance of less than `r` from a point `y ∉ Ω_{j+1}` lie at an
`ℓ¹`-distance of less than `a_{j+1}L^{r/RM}r` from it: along a path of a weighted length of less than
`r` the largest scale `p` satisfies `RM(p - j - 1) < r` (`lem:distance`(ii)), and the weight is at least
`a_p⁻¹`. -/
theorem dist1_lt_of_wdist_lt (hRM : 0 < C.RM) {j : ℕ} {y : Tor p} (hyΩ1 : y ∉ C.Ω (j + 1))
    {x : Tor p} {r : ℝ} (h : wdist C.D y x < ENNReal.ofReal r) :
    dist1 x y < C.a (j + 1) * (C.L : ℝ) ^ (r / C.RM) * r := by
  classical
  have hL1 : (1 : ℝ) ≤ C.L := by have := C.three_le_L; exact_mod_cast (by omega : 1 ≤ C.L)
  unfold wdist at h
  rw [iInf_lt_iff] at h
  obtain ⟨P, hP⟩ := h
  have hr : 0 < r := by
    by_contra hr; push_neg at hr
    rw [ENNReal.ofReal_of_nonpos hr] at hP
    exact (ENNReal.not_lt_zero hP)
  -- the largest scale along the path
  set F := (Finset.range (C.k + 1)).filter
    (fun s => ∃ t ∈ Icc 0 P.T, C.D.scale (projT p (P.γ t)) = s)
  have hne : F.Nonempty := ⟨C.D.scale (projT p (P.γ 0)), by
    simp only [F, Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_succ_of_le (C.D.scale_le _), 0, ⟨le_rfl, P.T_nonneg⟩, rfl⟩⟩
  obtain ⟨m, hmF, hmaxF⟩ : ∃ m, m ∈ F ∧ ∀ s ∈ F, s ≤ m :=
    ⟨F.max' hne, F.max'_mem hne, fun s hs => F.le_max' s hs⟩
  have hmF' := hmF
  simp only [F, Finset.mem_filter, Finset.mem_range] at hmF'
  obtain ⟨hmk, t₀, ht₀, hst₀⟩ := hmF'
  have hmax : ∀ t ∈ Icc 0 P.T, C.D.scale (projT p (P.γ t)) ≤ m := fun t ht =>
    hmaxF _ (by
      simp only [F, Finset.mem_filter, Finset.mem_range]
      exact ⟨Nat.lt_succ_of_le (C.D.scale_le _), t, ht, rfl⟩)
  have hDk : C.D.k = C.k := rfl
  -- the weight is at least `a_m⁻¹`
  have ham := C.a_pos m
  have hw : ∀ t ∈ Icc 0 P.T, (C.a m)⁻¹ ≤ C.D.weight (projT p (P.γ t)) := fun t ht => by
    unfold DomainData.weight
    exact inv_anti₀ (C.a_pos _) (C.D.a_mono _ _ (hmax t ht))
  have hd := mul_dist1_le_wlen C.D P (inv_nonneg.mpr ham.le) hw
  have hd' : (C.a m)⁻¹ * dist1 y x < r :=
    (ENNReal.ofReal_lt_ofReal_iff hr).mp (lt_of_le_of_lt hd hP)
  have hdist : dist1 x y < C.a m * r := by
    rw [dist1_comm']
    rw [inv_mul_lt_iff₀ ham] at hd'
    exact hd'
  -- `a_m ≤ a_{j+1}L^{r/RM}`
  have hLpow : (1 : ℝ) ≤ (C.L : ℝ) ^ (r / C.RM) := Real.one_le_rpow hL1 (by positivity)
  have hamj : C.a m ≤ C.a (j + 1) * (C.L : ℝ) ^ (r / C.RM) := by
    by_cases hmj : m ≤ j + 1
    · calc C.a m ≤ C.a (j + 1) := C.D.a_mono _ _ hmj
        _ ≤ C.a (j + 1) * (C.L : ℝ) ^ (r / C.RM) := le_mul_of_one_le_right (C.a_pos _).le hLpow
    · push_neg at hmj
      -- the sub-path up to the point of the scale `m`
      let P' : TPath p y (projT p (P.γ t₀)) :=
        { T := t₀, T_nonneg := ht₀.1, γ := P.γ, K := P.K, lip := P.lip, start := P.start,
          stop := rfl }
      have hz' : projT p (P.γ t₀) ∈ C.D.Ω m := by
        rw [← hst₀]; exact (C.D.mem_scale _).1
      have hge := wlen_ge_layers C.D (R := C.RM) (M := 1) C.sep (j := j) (j' := m) (by omega)
        (by omega) hyΩ1 hz' P'
      have hsub : wlen C.D P.γ 0 t₀ ≤ wlen C.D P.γ 0 P.T :=
        lintegral_mono_set (Icc_subset_Icc le_rfl ht₀.2)
      have hlt : C.RM * 1 * ((m : ℝ) - j - 1) < r := by
        have := lt_of_le_of_lt (hge.trans hsub) hP
        exact (ENNReal.ofReal_lt_ofReal_iff hr).mp this
      have hexp : ((m - (j + 1) : ℕ) : ℝ) ≤ r / C.RM := by
        rw [le_div_iff₀ hRM]
        push_cast [show j + 1 ≤ m by omega]
        linarith
      have e : C.a m = C.a (j + 1) * (C.L : ℝ) ^ ((m - (j + 1) : ℕ) : ℝ) := by
        unfold a aa
        rw [Real.rpow_natCast, mul_comm, ← mul_div_assoc, ← pow_add,
          show m - (j + 1) + (j + 1) = m by omega]
      rw [e]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL1 hexp) (C.a_pos _).le
  calc dist1 x y < C.a m * r := hdist
    _ ≤ C.a (j + 1) * (C.L : ℝ) ^ (r / C.RM) * r := mul_le_mul_of_nonneg_right hamj hr.le

end ContSeq

end Summation

end CoreLean
