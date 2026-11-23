/-
Cauchy's estimate for holomorphic maps between complex normed spaces, the form in which BALABAN_CORE.tex
(`a021c13be348`) uses it ("Cauchy's estimate on the polydisc", e.g. in `lem:near-data-differences`, `prop:far-terms`,
`lem:jet-cancellation`): if `F` is complex differentiable on the ball `‖X‖ < R` and bounded there by `M`, then
`‖DF(X)‖ ≤ 2M/R` for `‖X‖ ≤ R/2` (`norm_fderiv_le`), by the one-variable estimate on the complex lines
`z ↦ F(X + zY)`. Consequences, as in the proof of `lem:near-data-differences`: `‖F(A') - F(A)‖ ≤ 2M‖A' - A‖/R` on the
ball `‖·‖ ≤ R/2` (`norm_sub_le_of_ball`), and `‖F(A)‖ ≤ 2M‖A‖/R` there if `F(0) = 0` (`norm_le_of_zero`), the first
bound `‖B(c)‖ ≤ (2a_j/r_F)‖A‖_∞` and, with `B(c + e) = F_c(τ_eA)`, the second bound
`‖B(c + e) - B(c)‖ ≤ (2a_j/r_F)‖τ_eA - A‖_∞` of `eq:near-data-differences` (`near_data_first`, `near_data_second`).
-/
import Mathlib

open Complex Metric Set

noncomputable section

namespace CoreLean
namespace CauchyBanach

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- The one-variable estimate with the sharp radius: a function holomorphic on `|z| < ρ` and bounded there by `M`
has `|g'(0)| ≤ M/ρ`. -/
lemma norm_deriv_le_of_ball {g : ℂ → V} {ρ M : ℝ} (hρ : 0 < ρ) (hd : DifferentiableOn ℂ g (ball 0 ρ))
    (hb : ∀ z ∈ ball (0 : ℂ) ρ, ‖g z‖ ≤ M) : ‖deriv g 0‖ ≤ M / ρ := by
  have hr : ∀ r, 0 < r → r < ρ → ‖deriv g 0‖ ≤ M / r := fun r hr0 hrρ => by
    have hsub : closedBall (0 : ℂ) r ⊆ ball 0 ρ := closedBall_subset_ball hrρ
    have hcl : DifferentiableOn ℂ g (closure (ball (0 : ℂ) r)) := by
      rw [closure_ball 0 hr0.ne']; exact hd.mono hsub
    have hdc : DiffContOnCl ℂ g (ball 0 r) := hcl.diffContOnCl
    exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr0 hdc
      fun z hz => hb z (hsub (sphere_subset_closedBall hz))
  have hM : 0 ≤ M := (norm_nonneg _).trans (hb 0 (mem_ball_self hρ))
  by_contra hcon
  push_neg at hcon
  set D := ‖deriv g 0‖
  have hD : 0 < D := lt_of_le_of_lt (by positivity) hcon
  rcases hM.eq_or_lt with hM0 | hM0
  · have := hr (ρ / 2) (by positivity) (by linarith)
    rw [← hM0, zero_div] at this hcon
    linarith
  · have h1 : M / D < ρ := by rw [div_lt_iff₀ hD]; rw [div_lt_iff₀ hρ] at hcon; linarith
    set r := (ρ + M / D) / 2
    have hr0 : 0 < r := by have : 0 < M / D := by positivity
                           positivity
    have hrρ : r < ρ := by simp only [r]; linarith
    have hMDr : M / D < r := by simp only [r]; linarith
    have := hr r hr0 hrρ
    have h2 : M / r < D := by rw [div_lt_iff₀ hr0]; rw [div_lt_iff₀ hD] at hMDr; linarith
    linarith

/-- **Cauchy's estimate**: `‖DF(X)‖ ≤ 2M/R` for `‖X‖ ≤ R/2`. -/
theorem norm_fderiv_le {F : E → V} {R M : ℝ} (hR : 0 < R) (hd : DifferentiableOn ℂ F (ball 0 R))
    (hb : ∀ x ∈ ball (0 : E) R, ‖F x‖ ≤ M) {X : E} (hX : ‖X‖ ≤ R / 2) :
    ‖fderiv ℂ F X‖ ≤ 2 * M / R := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hb 0 (mem_ball_self hR))
  have hXb : X ∈ ball (0 : E) R := by rw [mem_ball, dist_zero_right]; linarith
  have hFX : DifferentiableAt ℂ F X := hd.differentiableAt (isOpen_ball.mem_nhds hXb)
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun Y => ?_
  rcases eq_or_ne Y 0 with rfl | hY
  · simp
  have hY0 : 0 < ‖Y‖ := norm_pos_iff.2 hY
  set ρ := R / 2 / ‖Y‖
  have hρ : 0 < ρ := by positivity
  set g : ℂ → V := fun z => F (X + z • Y)
  have hmaps : ∀ z ∈ ball (0 : ℂ) ρ, X + z • Y ∈ ball (0 : E) R := fun z hz => by
    rw [mem_ball, dist_zero_right] at hz ⊢
    calc ‖X + z • Y‖ ≤ ‖X‖ + ‖z‖ * ‖Y‖ := by rw [← norm_smul]; exact norm_add_le _ _
      _ < R / 2 + ρ * ‖Y‖ := by
          have := mul_lt_mul_of_pos_right hz hY0; linarith
      _ = R := by simp only [ρ]; field_simp; ring
  have hgd : DifferentiableOn ℂ g (ball 0 ρ) := fun z hz =>
    ((hd.differentiableAt (isOpen_ball.mem_nhds (hmaps z hz))).comp z
      ((differentiableAt_const X).add ((differentiableAt_id).smul_const Y))).differentiableWithinAt
  have hgb : ∀ z ∈ ball (0 : ℂ) ρ, ‖g z‖ ≤ M := fun z hz => hb _ (hmaps z hz)
  have hder : deriv g 0 = fderiv ℂ F X Y := by
    have h1 : HasDerivAt (fun z : ℂ => X + z • Y) Y 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).smul_const Y).const_add X
    have h2 : HasFDerivAt F (fderiv ℂ F X) (X + (0 : ℂ) • Y) := by simpa using hFX.hasFDerivAt
    exact (h2.comp_hasDerivAt (0 : ℂ) h1).deriv
  have := norm_deriv_le_of_ball hρ hgd hgb
  rw [hder] at this
  calc ‖fderiv ℂ F X Y‖ ≤ M / ρ := this
    _ = 2 * M / R * ‖Y‖ := by simp only [ρ]; field_simp

/-- The difference on the ball `‖·‖ ≤ R/2`: `‖F(A') - F(A)‖ ≤ 2M‖A' - A‖/R`. -/
theorem norm_sub_le_of_ball {F : E → V} {R M : ℝ} (hR : 0 < R) (hd : DifferentiableOn ℂ F (ball 0 R))
    (hb : ∀ x ∈ ball (0 : E) R, ‖F x‖ ≤ M) {A A' : E} (hA : ‖A‖ ≤ R / 2) (hA' : ‖A'‖ ≤ R / 2) :
    ‖F A' - F A‖ ≤ 2 * M / R * ‖A' - A‖ := by
  have hconv : Convex ℝ (closedBall (0 : E) (R / 2)) := convex_closedBall _ _
  have hsub : closedBall (0 : E) (R / 2) ⊆ ball 0 R := closedBall_subset_ball (by linarith)
  have hdiff : ∀ x ∈ closedBall (0 : E) (R / 2), DifferentiableAt ℂ F x := fun x hx =>
    hd.differentiableAt (isOpen_ball.mem_nhds (hsub hx))
  refine hconv.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℂ) (fun x hx => hdiff x hx)
    (fun x hx => norm_fderiv_le hR hd hb (by rw [mem_closedBall, dist_zero_right] at hx; exact hx))
    (by rw [mem_closedBall, dist_zero_right]; exact hA) (by rw [mem_closedBall, dist_zero_right]; exact hA')

/-- With `F(0) = 0`: `‖F(A)‖ ≤ 2M‖A‖/R` on the ball `‖·‖ ≤ R/2`. -/
theorem norm_le_of_zero {F : E → V} {R M : ℝ} (hR : 0 < R) (hd : DifferentiableOn ℂ F (ball 0 R))
    (hb : ∀ x ∈ ball (0 : E) R, ‖F x‖ ≤ M) (h0 : F 0 = 0) {A : E} (hA : ‖A‖ ≤ R / 2) :
    ‖F A‖ ≤ 2 * M / R * ‖A‖ := by
  have := norm_sub_le_of_ball hR hd hb (A := 0) (by simp; positivity) hA
  rwa [h0, sub_zero, sub_zero] at this

/-- **`eq:near-data-differences`**, the first bound: for `F_c(X) = (1/i)log M^j(e^{ia₀X})(c)`, holomorphic on the ball
`a_j‖X‖_∞ < r` (here the ball of radius `r/a_j`) with `‖F_c‖ ≤ 1` and `F_c(0) = 0`, the data `B(c) = F_c(A)` satisfies
`‖B(c)‖ ≤ (2a_j/r)‖A‖_∞` for `a_j‖A‖_∞ ≤ r/2`. -/
theorem near_data_first {F : E → V} {r aj : ℝ} (hr : 0 < r) (haj : 0 < aj)
    (hd : DifferentiableOn ℂ F (ball 0 (r / aj))) (hb : ∀ x ∈ ball (0 : E) (r / aj), ‖F x‖ ≤ 1) (h0 : F 0 = 0)
    {A : E} (hA : aj * ‖A‖ ≤ r / 2) : ‖F A‖ ≤ 2 * aj / r * ‖A‖ := by
  have hA' : ‖A‖ ≤ r / aj / 2 := by rw [le_div_iff₀ (by norm_num), le_div_iff₀ haj]; linarith
  have := norm_le_of_zero (by positivity) hd hb h0 hA'
  calc ‖F A‖ ≤ 2 * 1 / (r / aj) * ‖A‖ := this
    _ = 2 * aj / r * ‖A‖ := by field_simp

/-- **`eq:near-data-differences`**, the second bound: `‖F_c(τ_eA) - F_c(A)‖ ≤ (2a_j/r)‖τ_eA - A‖_∞`. -/
theorem near_data_second {F : E → V} {r aj : ℝ} (hr : 0 < r) (haj : 0 < aj)
    (hd : DifferentiableOn ℂ F (ball 0 (r / aj))) (hb : ∀ x ∈ ball (0 : E) (r / aj), ‖F x‖ ≤ 1)
    {A A' : E} (hA : aj * ‖A‖ ≤ r / 2) (hA' : aj * ‖A'‖ ≤ r / 2) :
    ‖F A' - F A‖ ≤ 2 * aj / r * ‖A' - A‖ := by
  have h1 : ‖A‖ ≤ r / aj / 2 := by rw [le_div_iff₀ (by norm_num), le_div_iff₀ haj]; linarith
  have h2 : ‖A'‖ ≤ r / aj / 2 := by rw [le_div_iff₀ (by norm_num), le_div_iff₀ haj]; linarith
  have := norm_sub_le_of_ball (by positivity) hd hb h1 h2
  calc ‖F A' - F A‖ ≤ 2 * 1 / (r / aj) * ‖A' - A‖ := this
    _ = 2 * aj / r * ‖A' - A‖ := by field_simp

end CauchyBanach
end CoreLean

end
