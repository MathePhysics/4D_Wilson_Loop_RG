/-
The lemma of Schwarz and Cauchy's estimate on balls of normed spaces over `ℂ`, in the forms used in the proofs of
`prop:relative-average`, `prop:relative-average-order`, `lem:average-kernels`, and `lem:remainder-kernel` of
BALABAN_CORE.tex (`8e81241a94fa`): "the lemma of Schwarz, applied to `z ↦ F(zX/m)`", "the lemma of Schwarz applied
twice", and "Cauchy's estimate on the discs of the radius `r`".

The balls are those of the norm of the space; for families of matrices with the supremum norm (`Π` types) they are
the polydiscs of the core.

* `schwarz_one`: if `f` is holomorphic on `B(c, R)` and `‖f - f(c)‖ ≤ K` there, then `‖f(z) - f(c)‖ ≤ (K/R)‖z - c‖`.
* `schwarz_two`: if moreover the derivative of `f` at `c` vanishes, `‖f(z) - f(c)‖ ≤ K(‖z - c‖/R)²`.
* `cauchy_fderiv`: if `f` is holomorphic on `B(c, R)` and `‖f‖ ≤ K` there, then
  `‖Df(x)v‖ ≤ K‖v‖/(R - ‖x - c‖)` for `x ∈ B(c, R)`.
-/
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Complex.Liouville

open Metric Set Filter Asymptotics
open scoped Topology

noncomputable section

namespace CoreLean
namespace SchwarzCauchy

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- **Schwarz, first order.** -/
theorem schwarz_one {f : E → F} {c : E} {R K : ℝ} (hf : DifferentiableOn ℂ f (ball c R))
    (hK : ∀ y ∈ ball c R, ‖f y - f c‖ ≤ K) {z : E} (hz : z ∈ ball c R) :
    ‖f z - f c‖ ≤ K / R * ‖z - c‖ := by
  have := Complex.dist_le_div_mul_dist_of_mapsTo_ball hf (R₂ := K)
    (fun y hy => by rw [mem_closedBall, dist_eq_norm]; exact hK y hy) hz
  rwa [dist_eq_norm, dist_eq_norm] at this

/-- **Schwarz, second order**: for a map whose derivative vanishes at the centre. -/
theorem schwarz_two {f : E → F} {c : E} {R K : ℝ} (hf : DifferentiableOn ℂ f (ball c R))
    (hK : ∀ y ∈ ball c R, ‖f y - f c‖ ≤ K) (hd : HasFDerivAt f (0 : E →L[ℂ] F) c) {z : E}
    (hz : z ∈ ball c R) : ‖f z - f c‖ ≤ K * (‖z - c‖ / R) ^ 2 := by
  have ho : (f · - f c) =o[𝓝 c] (fun w ↦ ‖w - c‖ ^ 1) := by
    have := hd.isLittleO
    simp only [ContinuousLinearMap.zero_apply, sub_zero] at this
    simpa using this.trans_isBigO (isBigO_refl (fun w => w - c) (𝓝 c)).norm_right
  have := Complex.dist_le_mul_div_pow_of_mapsTo_ball_of_isLittleO hf (R₂ := K)
    (fun y hy => by rw [mem_closedBall, dist_eq_norm]; exact hK y hy) ho hz
  rwa [dist_eq_norm, dist_eq_norm] at this

/-- **Cauchy's estimate** for the derivative. -/
theorem cauchy_fderiv {f : E → F} {c : E} {R K : ℝ} (hf : DifferentiableOn ℂ f (ball c R))
    (hK : ∀ y ∈ ball c R, ‖f y‖ ≤ K) {x : E} (hx : x ∈ ball c R) (v : E) :
    ‖fderiv ℂ f x v‖ ≤ K * ‖v‖ / (R - ‖x - c‖) := by
  have hxc : ‖x - c‖ < R := by rw [mem_ball, dist_eq_norm] at hx; exact hx
  set ρ := R - ‖x - c‖ with hρ
  have hρ0 : 0 < ρ := by linarith
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK x hx)
  rcases eq_or_ne v 0 with rfl | hv
  · simp only [map_zero, norm_zero, mul_zero, zero_div, le_refl]
  have hvn : 0 < ‖v‖ := norm_pos_iff.2 hv
  set u : E := ((‖v‖ : ℂ)⁻¹) • v with hu
  have hun : ‖u‖ = 1 := by
    rw [hu, norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hvn.le, inv_mul_cancel₀ hvn.ne']
  set g : ℂ → F := fun w => f (x + w • u) with hg
  have hmaps : ∀ r, r ≤ ρ → MapsTo (fun w : ℂ => x + w • u) (ball 0 r) (ball c R) := fun r hr w hw => by
    rw [mem_ball, dist_eq_norm] at hw ⊢
    rw [sub_zero] at hw
    calc ‖x + w • u - c‖ ≤ ‖x - c‖ + ‖w • u‖ := by
          rw [show x + w • u - c = (x - c) + w • u by abel]; exact norm_add_le _ _
      _ = ‖x - c‖ + ‖w‖ := by rw [norm_smul, hun, mul_one]
      _ < R := by linarith
  have hgdiff : ∀ r, r ≤ ρ → DifferentiableOn ℂ g (ball 0 r) := fun r hr =>
    hf.comp ((differentiable_const _).add (differentiable_id.smul_const u)).differentiableOn (hmaps r hr)
  have hderiv : deriv g 0 = fderiv ℂ f x u := by
    have hfx : DifferentiableAt ℂ f x := hf.differentiableAt (isOpen_ball.mem_nhds hx)
    have h1 : HasDerivAt (fun w : ℂ => x + w • u) u 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).smul_const u).const_add x
    have h2 : HasFDerivAt f (fderiv ℂ f x) (x + (0 : ℂ) • u) := by simpa using hfx.hasFDerivAt
    exact (h2.comp_hasDerivAt (0 : ℂ) h1).deriv
  -- the bound for every radius `r < ρ`
  have hbound : ∀ r, 0 < r → r < ρ → ‖fderiv ℂ f x u‖ ≤ K / r := fun r hr0 hr => by
    rw [← hderiv]
    refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr0 ?_ fun w hw => ?_
    · refine (hgdiff ρ le_rfl).diffContOnCl_ball ?_
      exact closedBall_subset_ball hr
    · refine hK _ (hmaps ρ le_rfl ?_)
      rw [mem_ball]; rw [mem_sphere] at hw; rw [hw]; exact hr
  have hu_bound : ‖fderiv ℂ f x u‖ ≤ K / ρ := by
    rw [le_div_iff₀ hρ0]
    by_contra hlt
    push_neg at hlt
    set D := ‖fderiv ℂ f x u‖
    have hD : 0 < D := by
      by_contra hD0; push_neg at hD0
      have : D = 0 := le_antisymm hD0 (norm_nonneg _)
      rw [this, zero_mul] at hlt; linarith
    have hKD : K / D < ρ := by rw [div_lt_iff₀ hD]; linarith
    set r := (K / D + ρ) / 2
    have hr0 : 0 < r := by have : 0 ≤ K / D := div_nonneg hK0 hD.le; simp only [r]; linarith
    have hrρ : r < ρ := by simp only [r]; linarith
    have h1 := hbound r hr0 hrρ
    rw [le_div_iff₀ hr0] at h1
    have h2 : D * r = (K + D * ρ) / 2 := by
      simp only [r]; field_simp
    linarith
  have hvu : v = (‖v‖ : ℂ) • u := by
    rw [hu, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hvn.ne'), one_smul]
  have e : fderiv ℂ f x v = (‖v‖ : ℂ) • fderiv ℂ f x u := by
    conv_lhs => rw [hvu]
    rw [map_smul]
  rw [e, norm_smul, Complex.norm_real, Real.norm_of_nonneg hvn.le]
  calc ‖v‖ * ‖fderiv ℂ f x u‖ ≤ ‖v‖ * (K / ρ) := mul_le_mul_of_nonneg_left hu_bound hvn.le
    _ = K * ‖v‖ / ρ := by ring

end SchwarzCauchy
end CoreLean

end
