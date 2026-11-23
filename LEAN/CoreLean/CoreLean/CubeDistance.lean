/-
`lem:cube-distance`(i), first statement, of BALABAN_CORE.tex (`a021c13be348`), on the continuum model `ContSeq` of the
sequences of domains (`SummationGeometry.lean`), with the weighted distance `d` of `Distance.lean`: if the scale of `y'`
is at most `j + 1`, `0 < s ≤ 1`, `0 < M ≤ RM`, and `|z - y'|₁ ≥ sMa_j`, then `d(y', z) ≥ sM/L³` (`cube_distance_i`).
The proof: along a path, let `p` be the largest scale of its points; the weight is at least `a_p⁻¹`, so the weighted
length is at least `a_p⁻¹sMa_j ≥ sM/L³` if `p ≤ j + 3`, and by `lem:distance`(ii) at least `RM(p - j - 2) ≥ 2M` otherwise
(the core's proof, which writes the two cases through `L^{2 + r'/(RM)}`).
-/
import CoreLean.GlobalBounds

open Set MeasureTheory

noncomputable section

namespace CoreLean
namespace Summation
namespace ContSeq

variable {p : ℝ} (C : ContSeq p)

lemma a_le_pow {i j : ℕ} (h : i ≤ j + 3) : C.a i ≤ (C.L : ℝ) ^ 3 * C.a j := by
  unfold a aa
  have hL : (1 : ℝ) ≤ C.L := by have := C.three_le_L; exact_mod_cast (by omega : 1 ≤ C.L)
  have hLk : (0 : ℝ) < (C.L : ℝ) ^ C.k := by have := C.L_pos; positivity
  rw [← mul_div_assoc, div_le_div_iff_of_pos_right hLk, ← pow_add]
  exact pow_le_pow_right₀ hL (by omega)

/-- **`lem:cube-distance`(i)**, the first statement. -/
theorem cube_distance_i {M s : ℝ} (hM0 : 0 < M) (hMR : M ≤ C.RM) (hs0 : 0 < s) (hs1 : s ≤ 1) {j : ℕ}
    {y' z : Tor p} (hy' : C.D.scale y' ≤ j + 1) (hz : s * M * C.a j ≤ dist1 y' z) :
    ENNReal.ofReal (s * M / (C.L : ℝ) ^ 3) ≤ wdist C.D y' z := by
  classical
  refine le_iInf fun P => ?_
  set g : ℝ → Tor p := fun t => projT p (P.γ t) with hg
  -- the largest scale along the path
  set Sc := (Finset.range (C.D.k + 1)).filter fun i => ∃ t ∈ Icc 0 P.T, C.D.scale (g t) = i with hSc
  have hmemSc : ∀ t ∈ Icc 0 P.T, C.D.scale (g t) ∈ Sc := fun t ht =>
    Finset.mem_filter.2 ⟨Finset.mem_range.2 (Nat.lt_succ_of_le (C.D.scale_le _)), t, ht, rfl⟩
  have hne : Sc.Nonempty := ⟨_, hmemSc 0 ⟨le_rfl, P.T_nonneg⟩⟩
  set q := Sc.max' hne with hq
  obtain ⟨t₀, ht₀, hqt⟩ := (Finset.mem_filter.1 (Sc.max'_mem hne)).2
  have hle : ∀ t ∈ Icc 0 P.T, C.D.scale (g t) ≤ q := fun t ht => Sc.le_max' _ (hmemSc t ht)
  have hL3 : (1 : ℝ) ≤ (C.L : ℝ) ^ 3 := one_le_pow₀ (by have := C.three_le_L; exact_mod_cast (by omega : 1 ≤ C.L))
  have hDa : ∀ i, C.D.a i = C.a i := fun i => rfl
  rcases le_or_gt q (j + 3) with hqj | hqj
  · -- the weight is at least `a_q⁻¹ ≥ (L³a_j)⁻¹`
    have haq := C.a_pos q
    have hw : ∀ t ∈ Icc 0 P.T, ENNReal.ofReal (C.a q)⁻¹ * ∑ ν, ‖deriv (fun s => P.γ s ν) t‖ₑ ≤ wIntegrand C.D P.γ t := by
      intro t ht
      unfold wIntegrand
      gcongr
      unfold DomainData.weight
      rw [hDa]
      exact inv_anti₀ (C.a_pos _) ((C.D.a_mono _ _ (hle t ht)))
    have h1 : ENNReal.ofReal (C.a q)⁻¹ * ENNReal.ofReal (dist1 y' z) ≤ wlen C.D P.γ 0 P.T := by
      calc ENNReal.ofReal (C.a q)⁻¹ * ENNReal.ofReal (dist1 y' z)
          ≤ ENNReal.ofReal (C.a q)⁻¹ * ∫⁻ t in Icc 0 P.T, ∑ ν, ‖deriv (fun s => P.γ s ν) t‖ₑ := by
            gcongr
            have h2 := ofReal_sum_abs_sub_le P.lip P.T_nonneg
            refine le_trans (ENNReal.ofReal_le_ofReal ?_) h2
            calc dist1 y' z = dist1 (projT p (P.γ 0)) (projT p (P.γ P.T)) := by rw [P.start, P.stop]
              _ ≤ ∑ ν, |P.γ 0 ν - P.γ P.T ν| := dist1_projT_le _ _
              _ = ∑ ν, |P.γ P.T ν - P.γ 0 ν| := Finset.sum_congr rfl fun ν _ => abs_sub_comm _ _
        _ = ∫⁻ t in Icc 0 P.T, ENNReal.ofReal (C.a q)⁻¹ * ∑ ν, ‖deriv (fun s => P.γ s ν) t‖ₑ := by
            rw [lintegral_const_mul _ (Finset.measurable_sum _ fun ν _ => (measurable_deriv _).enorm)]
        _ ≤ wlen C.D P.γ 0 P.T := setLIntegral_mono' measurableSet_Icc hw
    refine le_trans ?_ h1
    rw [← ENNReal.ofReal_mul (inv_nonneg.2 haq.le)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hq3 := C.a_le_pow hqj
    have haj := C.a_pos j
    have key : s * M * C.a q ≤ dist1 y' z * (C.L : ℝ) ^ 3 := by
      calc s * M * C.a q ≤ s * M * ((C.L : ℝ) ^ 3 * C.a j) :=
            mul_le_mul_of_nonneg_left hq3 (by positivity)
        _ = s * M * C.a j * (C.L : ℝ) ^ 3 := by ring
        _ ≤ dist1 y' z * (C.L : ℝ) ^ 3 := mul_le_mul_of_nonneg_right hz (by positivity)
    have hL3p : (0 : ℝ) < (C.L : ℝ) ^ 3 := by have := C.L_pos; positivity
    rw [div_le_iff₀ hL3p, show (C.a q)⁻¹ * dist1 y' z * (C.L : ℝ) ^ 3 = dist1 y' z * (C.L : ℝ) ^ 3 / C.a q by
      field_simp, le_div_iff₀ haq]
    exact key
  · -- the path reaches the scale `q ≥ j + 4`, which costs `RM(q - j - 2) ≥ 2M`
    have hsub : wlen C.D P.γ 0 t₀ ≤ wlen C.D P.γ 0 P.T := lintegral_mono_set (Icc_subset_Icc le_rfl ht₀.2)
    set P' : TPath p y' (g t₀) :=
      { T := t₀, T_nonneg := ht₀.1, γ := P.γ, K := P.K, lip := P.lip, start := P.start, stop := rfl } with hP'
    have hd : wdist C.D y' (g t₀) ≤ wlen C.D P.γ 0 t₀ := iInf_le_of_le P' le_rfl
    have hlay := wdist_ge_layers C.D (R := C.RM) (M := 1) C.sep (C.D.mem_scale y').1 (C.D.mem_scale y').2
      (C.D.mem_scale (g t₀)).1 (C.D.mem_scale (g t₀)).2
    refine le_trans ?_ (hlay.trans (hd.trans hsub))
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hqt]
    have hRM0 : 0 ≤ C.RM := le_trans hM0.le hMR
    have habs : (q : ℝ) - j - 2 ≤ |(C.D.scale y' : ℝ) - q| - 1 := by
      have h1 : (C.D.scale y' : ℝ) ≤ j + 1 := by exact_mod_cast hy'
      have h2 : (q : ℝ) - C.D.scale y' ≤ |(C.D.scale y' : ℝ) - q| := by
        rw [abs_sub_comm]; exact le_abs_self _
      linarith
    have hq4 : (j : ℝ) + 4 ≤ q := by exact_mod_cast hqj
    calc s * M / (C.L : ℝ) ^ 3 ≤ M := by
          rw [div_le_iff₀ (by positivity)]
          nlinarith
      _ ≤ C.RM * 1 * 2 := by linarith
      _ ≤ C.RM * 1 * max (|(C.D.scale y' : ℝ) - q| - 1) 0 := by
          refine mul_le_mul_of_nonneg_left ?_ (by linarith)
          exact le_trans (by linarith) (le_max_left _ _)

end ContSeq
end Summation
end CoreLean

end
