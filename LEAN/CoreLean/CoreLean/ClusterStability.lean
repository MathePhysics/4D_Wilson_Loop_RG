/-
The stability of the polymer logarithm under a change of the activities, the argument of
`lem:threshold-differences`(ii) of BALABAN_CORE.tex (`a021c13be348`). On the grid of `ClusterGrid.lean`, if
`|H'(Z)| + R|H''(Z) - H'(Z)| ≤ εe^{-κd(Z)}` with `κ ≥ κ₂`, `0 ≤ ε ≤ c₇e^{-3κ}`, `R ≥ 2`, then
`|E''(X) - E'(X)| ≤ 2C₇εe^{-(κ-κ₂)d(X)}/R` (`log_stability`). The proof is the core's: the activities
`H(u) = H' + u(H'' - H')` satisfy the hypothesis of `thm:polymer-logarithm` for `|u| ≤ R`, `E(X; u)` is holomorphic
for `|u| < R` and continuous for `|u| ≤ R` and bounded by `C₇εe^{-(κ-κ₂)d(X)}`, and Cauchy's estimate on the discs of
the radius `R - 1 ≥ R/2` about the points of `[0, 1]` bounds the derivative. `threshold_differences_ii` is the form of
the core, with `κ' = (11/10)κ`, `ε = 2^{12}ε'_H`, and `Rε_Δ = ε'_H`; its hypotheses on `H'` and `H'' - H'` are those
which `lem:activity-sum`(i) and `lem:threshold-differences`(i) give.
-/
import CoreLean.ClusterGrid

open Finset Metric

set_option maxRecDepth 100000

noncomputable section

namespace CoreLean
namespace PolymerGrid

open Classical
open TreeGraph

variable {s : ℝ} {N : ℕ} [NeZero N]

/-- The interpolating activities `H(u) = H' + u(H'' - H')`. -/
def Hu {P : Finset (Finset (Cube N))} (H' H'' : P → ℂ) (u : ℂ) : P → ℂ := fun Z => H' Z + u * (H'' Z - H' Z)

lemma norm_Hu_le {P : Finset (Finset (Cube N))} (H' H'' : P → ℂ) {R : ℝ} {u : ℂ} (hu : ‖u‖ ≤ R) (Z : P) :
    ‖Hu H' H'' u Z‖ ≤ ‖H' Z‖ + R * ‖H'' Z - H' Z‖ := by
  unfold Hu
  refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right hu (norm_nonneg _)

variable (hs : 0 < s)
include hs

/-- **The stability of `E(X)`**. -/
theorem log_stability (P : Finset (Finset (Cube N))) (hP : ∀ Z ∈ P, IsConn Z) {κ ε R : ℝ} (hκ : kappa2 ≤ κ)
    (hε0 : 0 ≤ ε) (hε : ε ≤ c7 * Real.exp (-3 * κ)) (hR : 2 ≤ R) (H' H'' : P → ℂ)
    (hH : ∀ Z, ‖H' Z‖ + R * ‖H'' Z - H' Z‖ ≤ ε * Real.exp (-κ * size s N Z.1)) (X : Finset (Cube N)) :
    ‖EX (incP P) Subtype.val H'' X - EX (incP P) Subtype.val H' X‖ ≤
      2 * C7 * ε * Real.exp (-(κ - kappa2) * size s N X) / R := by
  have hR0 : 0 < R := by linarith
  set f : ℂ → ℂ := fun u => EX (incP P) Subtype.val (Hu H' H'' u) X with hf
  set Cb := C7 * ε * Real.exp (-(κ - kappa2) * size s N X) with hCb
  have hbd : ∀ u : ℂ, ‖u‖ ≤ R → ∀ Z, ‖Hu H' H'' u Z‖ ≤ ε * Real.exp (-κ * size s N Z.1) := fun u hu Z =>
    (norm_Hu_le H' H'' hu Z).trans (hH Z)
  -- the bound of `E(X; u)` on the closed disc
  have hfb : ∀ u : ℂ, ‖u‖ ≤ R → ‖f u‖ ≤ Cb := fun u hu =>
    (polymer_logarithm hs P hP hκ hε0 hε (Hu H' H'' u) (hbd u hu)).2.2.2.2.2.2 X
  -- holomorphy on the open disc
  have hdiff : DifferentiableOn ℂ f (ball 0 R) := by
    have h := (polymer_logarithm_holomorphic hs P hP hκ hε0 hε isOpen_ball (fun u Z => Hu H' H'' u Z)
      (fun Z => ((differentiable_const _).add ((differentiable_id).mul (differentiable_const _))).differentiableOn)
      (fun u hu Z => hbd u (le_of_lt (by rwa [mem_ball, dist_zero_right] at hu)) Z) X).2
    exact h
  -- continuity on the closed disc
  obtain ⟨hε', -, hrefl, hsymm, hKP⟩ := setup hs P hP hκ hε0 hε
  set w : P → ℝ := fun Z => ε * Real.exp (3 * κ) * Real.exp (-kappa2 * size s N Z.1) with hw
  have hw0 : ∀ Z, 0 ≤ w Z := fun Z => mul_nonneg hε' (Real.exp_pos _).le
  have hcont : ContinuousOn f (closedBall 0 R) := by
    refine continuousOn_tsum (u := clusterTerm (incP P) w Finset.univ) (fun k => ?_)
      (summable_clusterTerm hrefl hsymm w _ hw0 hKP Finset.univ) (fun k u hu => ?_)
    · refine Continuous.continuousOn ?_
      unfold unionTerm Hu
      refine continuous_const.mul (continuous_finsetSum _ fun Z _ => ?_)
      split_ifs
      · exact continuous_const.mul (continuous_finsetProd _ fun i _ =>
          continuous_const.add (continuous_id.mul continuous_const))
      · exact continuous_const
    · refine norm_unionTerm_le Subtype.val w (Hu H' H'' u) (fun Z => ?_) X k
      exact (hbd u (by simpa using hu) Z).trans (bound_le_hbar hs P hκ hε0 Z)
  -- Cauchy's estimate at the points of `[0, 1]`
  have hderiv : ∀ t ∈ segment ℝ (0 : ℂ) 1, ‖deriv f t‖ ≤ Cb / (R - 1) := by
    intro t ht
    have htn : ‖t‖ ≤ 1 := by
      obtain ⟨a, b, ha, hb, hab, rfl⟩ := ht
      simp only [smul_zero, zero_add, Complex.real_smul, mul_one]
      rw [Complex.norm_real, Real.norm_of_nonneg hb]; linarith
    have hR1 : 0 < R - 1 := by linarith
    refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR1 ⟨?_, ?_⟩ fun z hz => hfb z ?_
    · refine hdiff.mono fun z hz => ?_
      rw [mem_ball, dist_zero_right]
      rw [mem_ball, dist_eq_norm] at hz
      calc ‖z‖ ≤ ‖z - t‖ + ‖t‖ := by rw [← sub_add_cancel z t]; exact norm_add_le _ _ |>.trans (by simp)
        _ < R - 1 + 1 := by linarith
        _ = R := by ring
    · rw [closure_ball _ hR1.ne']
      refine hcont.mono fun z hz => ?_
      rw [mem_closedBall, dist_zero_right]
      rw [mem_closedBall, dist_eq_norm] at hz
      calc ‖z‖ ≤ ‖z - t‖ + ‖t‖ := by rw [← sub_add_cancel z t]; exact norm_add_le _ _ |>.trans (by simp)
        _ ≤ R - 1 + 1 := by linarith
        _ = R := by ring
    · rw [mem_sphere, dist_eq_norm] at hz
      calc ‖z‖ ≤ ‖z - t‖ + ‖t‖ := by rw [← sub_add_cancel z t]; exact norm_add_le _ _ |>.trans (by simp)
        _ ≤ R - 1 + 1 := by linarith
        _ = R := by ring
  -- the mean value inequality
  have hdiffAt : ∀ t ∈ segment ℝ (0 : ℂ) 1, DifferentiableAt ℂ f t := by
    intro t ht
    have htn : ‖t‖ ≤ 1 := by
      obtain ⟨a, b, ha, hb, hab, rfl⟩ := ht
      simp only [smul_zero, zero_add, Complex.real_smul, mul_one]
      rw [Complex.norm_real, Real.norm_of_nonneg hb]; linarith
    exact hdiff.differentiableAt (isOpen_ball.mem_nhds (by rw [mem_ball, dist_zero_right]; linarith))
  have hmv := (convex_segment (0 : ℂ) 1).norm_image_sub_le_of_norm_deriv_le hdiffAt hderiv
    (left_mem_segment ℝ 0 1) (right_mem_segment ℝ 0 1)
  have h0 : Hu H' H'' 0 = H' := by funext Z; simp [Hu]
  have h1 : Hu H' H'' 1 = H'' := by funext Z; simp [Hu]
  simp only [hf, h0, h1, sub_zero, norm_one, mul_one] at hmv
  refine hmv.trans ?_
  have hCb0 : 0 ≤ Cb := by
    have := (norm_nonneg _).trans (hfb 0 (by simp; linarith))
    exact this
  rw [div_le_div_iff₀ (by linarith) hR0]
  nlinarith

/-- **`lem:threshold-differences`(ii)** in the form of the core, given the bounds of the activities which
`lem:activity-sum`(i) and `lem:threshold-differences`(i) give: if `|H'| ≤ 2^{11}ε'_He^{-κ'd}`,
`|H'' - H'| ≤ 2^{11}ε_Δe^{-κ'd}`, `Rε_Δ = ε'_H` with `R ≥ 2`, `κ' ≥ κ₂`, and `2^{12}ε'_H ≤ c₇e^{-3κ'}`, then
`|E''(X) - E'(X)| ≤ 2^{13}C₇ε_Δe^{-(κ' - κ₂)d(X)}`. -/
theorem threshold_differences_ii (P : Finset (Finset (Cube N))) (hP : ∀ Z ∈ P, IsConn Z) {κ' εH εΔ R : ℝ}
    (hκ : kappa2 ≤ κ') (hεH : 0 ≤ εH) (hcond : 2 ^ 12 * εH ≤ c7 * Real.exp (-3 * κ')) (hR : 2 ≤ R)
    (hRε : R * εΔ = εH) (H' H'' : P → ℂ)
    (h1 : ∀ Z, ‖H' Z‖ ≤ 2 ^ 11 * εH * Real.exp (-κ' * size s N Z.1))
    (h2 : ∀ Z, ‖H'' Z - H' Z‖ ≤ 2 ^ 11 * εΔ * Real.exp (-κ' * size s N Z.1)) (X : Finset (Cube N)) :
    ‖EX (incP P) Subtype.val H'' X - EX (incP P) Subtype.val H' X‖ ≤
      2 ^ 13 * C7 * εΔ * Real.exp (-(κ' - kappa2) * size s N X) := by
  have hR0 : 0 < R := by linarith
  have h := log_stability hs P hP hκ (by positivity) hcond hR H' H'' (fun Z => by
    have e := mul_le_mul_of_nonneg_left (h2 Z) hR0.le
    calc ‖H' Z‖ + R * ‖H'' Z - H' Z‖ ≤ 2 ^ 11 * εH * Real.exp (-κ' * size s N Z.1) +
          R * (2 ^ 11 * εΔ * Real.exp (-κ' * size s N Z.1)) := add_le_add (h1 Z) e
      _ = 2 ^ 12 * εH * Real.exp (-κ' * size s N Z.1) := by rw [← hRε]; ring) X
  refine h.trans (le_of_eq ?_)
  rw [← hRε]
  field_simp

end PolymerGrid
end CoreLean

end
