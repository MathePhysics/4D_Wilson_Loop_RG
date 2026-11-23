/-
`lem:near-cancellation`, Step 4, of BALABAN_CORE.tex (`a021c13be348`): the function
`𝗋(L, Y, L') = (1/i)log(e^{iL}e^{iY}e^{-iL'}) - Y - L + L'`, written with the function `Ψ` of `lem:product`
(`Psi.lean`) as `𝗋(L, Y, L') = Ψ(Ψ(L, Y), -L') - Y - L + L'`.

* The quadratic bound: `‖𝗋(L, Y, L')‖ ≤ 512(‖L‖ + ‖Y‖ + ‖L'‖)²` for arguments of norms at most `1/256` (`r_quadratic`),
  from `eq:product-lipschitz` twice (the core: a constant `C` on the polydisc of the radius `1/16`, by Schwarz).
* `Ψ(Y, -Y) = 0` (`psi_neg_self`), so that `(L, Y₀) ↦ 𝗋(L, Y₀, L + Y₀)` vanishes for `L = 0` and for `Y₀ = 0`
  (`r_axes`), the property behind the core's Cauchy estimate for the mixed derivative.
-/
import CoreLean.UnitLocalField
import CoreLean.SpaceStability
import CoreLean.RelativeAverageKernels

open Matrix NormedSpace BakerCampbellHausdorff
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean
namespace NearCancellationR

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ

/-- The function `𝗋`. -/
def rfun (L Y L' : Mat) : Mat := psi (psi L Y) (-L') - Y - L + L'

/-- `Ψ(Y, -Y) = 0`. -/
theorem psi_neg_self (Y : Mat) : psi Y (-Y) = 0 := by
  rw [psi_eq_Log]
  have hc : Commute (Complex.I • Y) (Complex.I • -Y) := by
    rw [smul_neg]; exact (Commute.refl _).neg_right
  rw [← Matrix.exp_add_of_commute _ _ hc, smul_neg, add_neg_cancel, NormedSpace.exp_zero, LogM, sub_self,
    log1p_zero, smul_zero]

/-- `𝗋` vanishes on the two axes. -/
theorem r_axes (L Y₀ : Mat) (hL : ‖L‖ < 1 / 4) (hY : ‖Y₀‖ < 1 / 4) :
    rfun 0 Y₀ (0 + Y₀) = 0 ∧ rfun L 0 (L + 0) = 0 := by
  constructor
  · rw [rfun, psi_zero_left hY, zero_add, psi_neg_self]; abel
  · rw [rfun, psi_zero_right hL, add_zero, psi_neg_self]; abel

/-- **The quadratic bound**: `‖𝗋(L, Y, L')‖ ≤ 512(‖L‖ + ‖Y‖ + ‖L'‖)²`. -/
theorem r_quadratic {L Y L' : Mat} (hL : ‖L‖ ≤ 1 / 256) (hY : ‖Y‖ ≤ 1 / 256) (hL' : ‖L'‖ ≤ 1 / 256) :
    ‖rfun L Y L'‖ ≤ 512 * (‖L‖ + ‖Y‖ + ‖L'‖) ^ 2 := by
  have h1 := SpaceStability.complex_part (X := L) (Y := Y) (by linarith) (by linarith)
  have hP := UnitLocalField.psi_norm_le (Y := L) (Y' := Y) (by linarith) (by linarith) (by linarith)
  have hP' : ‖psi L Y‖ ≤ 1 / 32 := by linarith
  have hnL' : ‖-L'‖ ≤ 1 / 32 := by rw [norm_neg]; linarith
  have h2 := SpaceStability.complex_part (X := psi L Y) (Y := -L') hP' hnL'
  have e : rfun L Y L' = (psi (psi L Y) (-L') - (-L') - psi L Y) + (psi L Y - Y - L) := by
    unfold rfun; abel
  rw [e]
  have hL0 := norm_nonneg L
  have hY0 := norm_nonneg Y
  have hL'0 := norm_nonneg L'
  calc ‖(psi (psi L Y) (-L') - (-L') - psi L Y) + (psi L Y - Y - L)‖
      ≤ ‖psi (psi L Y) (-L') - (-L') - psi L Y‖ + ‖psi L Y - Y - L‖ := norm_add_le _ _
    _ ≤ 256 * ‖psi L Y‖ * ‖-L'‖ + 256 * ‖L‖ * ‖Y‖ := add_le_add h2 h1
    _ ≤ 256 * (2 * (‖L‖ + ‖Y‖)) * ‖L'‖ + 256 * ‖L‖ * ‖Y‖ := by
        rw [norm_neg]; gcongr
    _ ≤ 512 * (‖L‖ + ‖Y‖ + ‖L'‖) ^ 2 := by nlinarith [mul_nonneg hL0 hY0, mul_nonneg hL0 hL'0, mul_nonneg hY0 hL'0]

/-- The function `(L, Y₀) ↦ 𝗋(L, Y₀, L + Y₀)` is holomorphic near `0`. -/
lemma r_diag_analytic : AnalyticOnNhd ℂ (fun v : Mat × Mat => rfun v.1 v.2 (v.1 + v.2))
    (Metric.ball (0 : Mat) (1 / 512) ×ˢ Metric.ball (0 : Mat) (1 / 512)) := by
  intro v hv
  rcases hv with ⟨h1, h2⟩
  rw [Metric.mem_ball, dist_zero_right] at h1 h2
  have hlog := log_two_gt_eighth
  have hin : v ∈ {w : Mat × Mat | ‖w.1‖ + ‖w.2‖ < Real.log 2} := by
    show ‖v.1‖ + ‖v.2‖ < Real.log 2; linarith
  have hpsi : AnalyticAt ℂ (fun w : Mat × Mat => psi w.1 w.2) v := analyticOnNhd_psi v hin
  -- the size of `Ψ(v)` and of `v.1 + v.2`
  have hcp := SpaceStability.complex_part (X := v.1) (Y := v.2) (by linarith) (by linarith)
  have hP : ‖psi v.1 v.2‖ ≤ 1 / 64 := by
    have := norm_add_le (psi v.1 v.2 - v.2 - v.1) (v.2 + v.1)
    rw [show psi v.1 v.2 - v.2 - v.1 + (v.2 + v.1) = psi v.1 v.2 by abel] at this
    have h3 := norm_add_le v.2 v.1
    nlinarith [norm_nonneg v.1, norm_nonneg v.2]
  have hS : ‖-(v.1 + v.2)‖ ≤ 1 / 256 := by
    rw [norm_neg]; have := norm_add_le v.1 v.2; linarith
  have hin2 : (psi v.1 v.2, -(v.1 + v.2)) ∈ {w : Mat × Mat | ‖w.1‖ + ‖w.2‖ < Real.log 2} := by
    show ‖psi v.1 v.2‖ + ‖-(v.1 + v.2)‖ < Real.log 2; linarith
  have hg : AnalyticAt ℂ (fun w : Mat × Mat => (psi w.1 w.2, -(w.1 + w.2))) v :=
    hpsi.prod ((analyticAt_fst.add analyticAt_snd).neg)
  have hcomp' := AnalyticAt.comp (g := fun u : Mat × Mat => psi u.1 u.2)
    (f := fun w : Mat × Mat => (psi w.1 w.2, -(w.1 + w.2))) (analyticOnNhd_psi _ hin2) hg
  have hcomp : AnalyticAt ℂ (fun w : Mat × Mat => psi (psi w.1 w.2) (-(w.1 + w.2))) v := hcomp'
  have : (fun w : Mat × Mat => rfun w.1 w.2 (w.1 + w.2)) =
      fun w : Mat × Mat => psi (psi w.1 w.2) (-(w.1 + w.2)) - w.2 - w.1 + (w.1 + w.2) := by
    funext w; rfl
  rw [this]
  exact ((hcomp.sub analyticAt_snd).sub analyticAt_fst).add (analyticAt_fst.add analyticAt_snd)

/-- **The mixed estimate**: `‖𝗋(L, Y₀, L + Y₀)‖ ≤ 8192‖L‖‖Y₀‖` for `‖L‖, ‖Y₀‖ < 1/512`. -/
theorem r_mixed {L Y₀ : Mat} (hL : ‖L‖ < 1 / 512) (hY : ‖Y₀‖ < 1 / 512) :
    ‖rfun L Y₀ (L + Y₀)‖ ≤ 8192 * ‖L‖ * ‖Y₀‖ := by
  set f : Mat × Mat → Mat := fun v => rfun v.1 v.2 (v.1 + v.2)
  have hd : DifferentiableOn ℂ f (Metric.ball (0 : Mat) (1 / 512) ×ˢ Metric.ball (0 : Mat) (1 / 512)) :=
    r_diag_analytic.differentiableOn
  have hM : ∀ x ∈ Metric.ball (0 : Mat) (1 / 512), ∀ y ∈ Metric.ball (0 : Mat) (1 / 512), ‖f (x, y)‖ ≤ 1 / 32 := by
    intro x hx y hy
    rw [Metric.mem_ball, dist_zero_right] at hx hy
    have hxy : ‖x + y‖ ≤ 1 / 256 := by have := norm_add_le x y; linarith
    have := r_quadratic (L := x) (Y := y) (L' := x + y) (by linarith) (by linarith) hxy
    have h4 : ‖x‖ + ‖y‖ + ‖x + y‖ ≤ 4 / 512 := by linarith
    have h5 : (‖x‖ + ‖y‖ + ‖x + y‖) ^ 2 ≤ (4 / 512) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h4 2
    show ‖rfun x y (x + y)‖ ≤ 1 / 32
    nlinarith
  -- the corrected function vanishes on the axes everywhere and equals `f` on the balls
  set f' : Mat × Mat → Mat := fun v => f v - f (v.1, 0) - f (0, v.2)
  have hf00 : f (0, 0) = 0 := by
    show rfun 0 0 (0 + 0) = 0
    rw [rfun, add_zero, psi_zero_left (by simp), neg_zero, psi_zero_left (by simp)]; abel
  have hx0 : ∀ x, f' (x, 0) = 0 := fun x => by
    show f (x, 0) - f (x, 0) - f (0, 0) = 0
    rw [hf00]; abel
  have h0y : ∀ y, f' (0, y) = 0 := fun y => by
    show f (0, y) - f (0, 0) - f (0, y) = 0
    rw [hf00]; abel
  have heq : ∀ v ∈ Metric.ball (0 : Mat) (1 / 512) ×ˢ Metric.ball (0 : Mat) (1 / 512), f' v = f v := by
    rintro v ⟨h1, h2⟩
    rw [Metric.mem_ball, dist_zero_right] at h1 h2
    have ha := (r_axes v.1 v.2 (by linarith) (by linarith))
    show f v - rfun v.1 0 (v.1 + 0) - rfun 0 v.2 (0 + v.2) = f v
    rw [ha.1, ha.2]; abel
  have hd' : DifferentiableOn ℂ f' (Metric.ball (0 : Mat) (1 / 512) ×ˢ Metric.ball (0 : Mat) (1 / 512)) :=
    hd.congr heq
  have hM' : ∀ x ∈ Metric.ball (0 : Mat) (1 / 512), ∀ y ∈ Metric.ball (0 : Mat) (1 / 512),
      ‖f' (x, y)‖ ≤ 1 / 32 := fun x hx y hy => by
    rw [heq (x, y) ⟨hx, hy⟩]; exact hM x hx y hy
  have hL' : L ∈ Metric.ball (0 : Mat) (1 / 512) := by rw [Metric.mem_ball, dist_zero_right]; exact hL
  have hY' : Y₀ ∈ Metric.ball (0 : Mat) (1 / 512) := by rw [Metric.mem_ball, dist_zero_right]; exact hY
  have hest := (RelativeAverage.holomorphic_estimates (by norm_num) (by norm_num) hd' hM').1 hx0 h0y L hL' Y₀ hY'
  rw [heq (L, Y₀) ⟨hL', hY'⟩] at hest
  calc ‖rfun L Y₀ (L + Y₀)‖ = ‖f (L, Y₀)‖ := rfl
    _ ≤ 1 / 32 * ‖L‖ * ‖Y₀‖ / (1 / 512 * (1 / 512)) := hest
    _ = 8192 * ‖L‖ * ‖Y₀‖ := by ring

end NearCancellationR
end CoreLean

end
