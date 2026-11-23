/-
`lem:unit-average-bond`(ii) of BALABAN_CORE.tex (`a021c13be348`), `eq:unit-remainder`, in abstract form. Let `g` be
holomorphic (analytic) on the ball `‖B‖ < r₀` of a complex normed space, bounded there by `2`, with `g(0) = 0` and
`Dg(0) = 0` (in the core `g(B) = G(A, B) - D_BG(A, 0)B`). Then, as in the core's proof:

* `‖Dg(B)‖ ≤ 4/r₀` for `‖B‖ ≤ r₀/2` (Cauchy's estimate on the ball of the radius `r₀/2` about `B`, `deriv_bound`);
* `‖Dg(B)Y‖ ≤ 16‖B‖‖Y‖/r₀²` for `‖B‖ ≤ r₀/4` (the map `B ↦ Dg(B)Y` vanishes at `0` and is bounded by `4‖Y‖/r₀` on the
  ball of the radius `r₀/2`; `deriv_small`);
* `‖g(B) - g(B')‖ ≤ 16/r₀²·max{‖B‖, ‖B'‖}‖B - B'‖` for `‖B‖, ‖B'‖ ≤ r₀/4` (integration along the segment,
  `remainder_lipschitz`), the second bound of `eq:unit-remainder`;
* `‖g(B)‖ ≤ 4‖B‖²/r₀²` for `‖B‖ < r₀` (`remainder_square`, by `lem:holomorphic-estimates`(ii), which gives the
  factor `2`), the first bound.
-/
import CoreLean.CauchyBanach
import CoreLean.RelativeAverageKernels

open Complex Metric Set

noncomputable section

namespace CoreLean
namespace UnitRemainder

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup V] [NormedSpace ℂ V]
  [CompleteSpace V]

variable {g : E → V} {r₀ : ℝ}

/-- `‖Dg(B)‖ ≤ 4/r₀` for `‖B‖ ≤ r₀/2`. -/
theorem deriv_bound (hr₀ : 0 < r₀) (hg : AnalyticOnNhd ℂ g (ball 0 r₀)) (hb : ∀ x ∈ ball (0 : E) r₀, ‖g x‖ ≤ 2)
    {B : E} (hB : ‖B‖ ≤ r₀ / 2) : ‖fderiv ℂ g B‖ ≤ 4 / r₀ := by
  have := CauchyBanach.norm_fderiv_le hr₀ hg.differentiableOn hb hB
  calc ‖fderiv ℂ g B‖ ≤ 2 * 2 / r₀ := this
    _ = 4 / r₀ := by ring

/-- `‖Dg(B)Y‖ ≤ 16‖B‖‖Y‖/r₀²` for `‖B‖ ≤ r₀/4`. -/
theorem deriv_small (hr₀ : 0 < r₀) (hg : AnalyticOnNhd ℂ g (ball 0 r₀)) (hb : ∀ x ∈ ball (0 : E) r₀, ‖g x‖ ≤ 2)
    (hD0 : fderiv ℂ g 0 = 0) {B : E} (hB : ‖B‖ ≤ r₀ / 4) (Y : E) :
    ‖fderiv ℂ g B Y‖ ≤ 16 * ‖B‖ * ‖Y‖ / r₀ ^ 2 := by
  set F : E → V := fun x => fderiv ℂ g x Y
  have hFa : AnalyticOnNhd ℂ F (ball 0 r₀) := by
    have h1 := hg.fderiv
    intro x hx
    exact (ContinuousLinearMap.apply ℂ V Y).analyticAt _ |>.comp (h1 x hx)
  have hR : 0 < r₀ / 2 := by positivity
  have hsub : ball (0 : E) (r₀ / 2) ⊆ ball 0 r₀ := ball_subset_ball (by linarith)
  have hFd : DifferentiableOn ℂ F (ball 0 (r₀ / 2)) := (hFa.mono hsub).differentiableOn
  have hFb : ∀ x ∈ ball (0 : E) (r₀ / 2), ‖F x‖ ≤ 4 * ‖Y‖ / r₀ := by
    intro x hx
    have hx' : ‖x‖ ≤ r₀ / 2 := by rw [mem_ball, dist_zero_right] at hx; exact hx.le
    calc ‖F x‖ ≤ ‖fderiv ℂ g x‖ * ‖Y‖ := (fderiv ℂ g x).le_opNorm Y
      _ ≤ 4 / r₀ * ‖Y‖ := mul_le_mul_of_nonneg_right (deriv_bound hr₀ hg hb hx') (norm_nonneg _)
      _ = 4 * ‖Y‖ / r₀ := by ring
  have hF0 : F 0 = 0 := by simp [F, hD0]
  have hB' : ‖B‖ ≤ r₀ / 2 / 2 := by linarith
  have := CauchyBanach.norm_le_of_zero hR hFd hFb hF0 hB'
  calc ‖F B‖ ≤ 2 * (4 * ‖Y‖ / r₀) / (r₀ / 2) * ‖B‖ := this
    _ = 16 * ‖B‖ * ‖Y‖ / r₀ ^ 2 := by field_simp; ring

/-- **The second bound of `eq:unit-remainder`**. -/
theorem remainder_lipschitz (hr₀ : 0 < r₀) (hg : AnalyticOnNhd ℂ g (ball 0 r₀))
    (hb : ∀ x ∈ ball (0 : E) r₀, ‖g x‖ ≤ 2) (hD0 : fderiv ℂ g 0 = 0) {B B' : E} (hB : ‖B‖ ≤ r₀ / 4)
    (hB' : ‖B'‖ ≤ r₀ / 4) : ‖g B - g B'‖ ≤ 16 / r₀ ^ 2 * max ‖B‖ ‖B'‖ * ‖B - B'‖ := by
  set m := max ‖B‖ ‖B'‖
  have hm : m ≤ r₀ / 4 := max_le hB hB'
  have hconv : Convex ℝ (closedBall (0 : E) m) := convex_closedBall _ _
  have hsub : closedBall (0 : E) m ⊆ ball 0 r₀ := closedBall_subset_ball (by linarith)
  have hdiff : ∀ x ∈ closedBall (0 : E) m, DifferentiableAt ℂ g x := fun x hx =>
    hg.differentiableOn.differentiableAt (isOpen_ball.mem_nhds (hsub hx))
  have hbound : ∀ x ∈ closedBall (0 : E) m, ‖fderiv ℂ g x‖ ≤ 16 / r₀ ^ 2 * m := by
    intro x hx
    rw [mem_closedBall, dist_zero_right] at hx
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun Y => ?_
    have := deriv_small hr₀ hg hb hD0 (hx.trans hm) Y
    calc ‖fderiv ℂ g x Y‖ ≤ 16 * ‖x‖ * ‖Y‖ / r₀ ^ 2 := this
      _ ≤ 16 * m * ‖Y‖ / r₀ ^ 2 := by gcongr
      _ = 16 / r₀ ^ 2 * m * ‖Y‖ := by ring
  have hBm : B ∈ closedBall (0 : E) m := by rw [mem_closedBall, dist_zero_right]; exact le_max_left _ _
  have hB'm : B' ∈ closedBall (0 : E) m := by rw [mem_closedBall, dist_zero_right]; exact le_max_right _ _
  exact hconv.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℂ) hdiff hbound hB'm hBm

/-- **The first bound of `eq:unit-remainder`**: `‖g(B)‖ ≤ 2‖B‖²/r₀² ≤ 4‖B‖²/r₀²`. -/
theorem remainder_square (hr₀ : 0 < r₀) (hg : AnalyticOnNhd ℂ g (ball 0 r₀))
    (hb : ∀ x ∈ ball (0 : E) r₀, ‖g x‖ ≤ 2) (h0 : g 0 = 0) (hD0 : HasFDerivAt g (0 : E →L[ℂ] V) 0) {B : E}
    (hB : B ∈ ball (0 : E) r₀) : ‖g B‖ ≤ 4 * ‖B‖ ^ 2 / r₀ ^ 2 := by
  set f : E × E → V := fun p => g p.2
  have hfd : DifferentiableOn ℂ f (ball (0 : E) r₀ ×ˢ ball (0 : E) r₀) := by
    intro p hp
    exact (hg.differentiableOn p.2 hp.2).comp p differentiableWithinAt_snd fun q hq => hq.2
  have hM : ∀ x ∈ ball (0 : E) r₀, ∀ y ∈ ball (0 : E) r₀, ‖f (x, y)‖ ≤ 2 := fun x _ y hy => hb y hy
  have h := (RelativeAverage.holomorphic_estimates hr₀ hr₀ hfd hM).2.1 hD0 h0 B hB
  have h2 : 0 ≤ ‖B‖ ^ 2 / r₀ ^ 2 := by positivity
  calc ‖g B‖ = ‖f (0, B)‖ := rfl
    _ ≤ 2 * ‖B‖ ^ 2 / r₀ ^ 2 := h
    _ ≤ 4 * ‖B‖ ^ 2 / r₀ ^ 2 := by
        rw [mul_div_assoc, mul_div_assoc]; nlinarith

end UnitRemainder
end CoreLean

end
