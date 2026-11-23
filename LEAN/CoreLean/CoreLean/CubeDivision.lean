/-
`lem:cube-division` of BALABAN_CORE.tex (`a021c13be348`), the interpolation of its proof in abstract form. The data
of the cut sequence depend on `(t, t_□)` through the field `(t + t_□ζ_□)𝓗_n`, and `Σ_□ζ_□ = 1`. Abstractly: for a
function `Ψ` on a real normed space `V` (the composite `𝔟 ↦ F(e^{ia_0𝓗^{(j)}(𝔟)}U_{n+1}, 𝐉)` of the proof) which is
differentiable along the segment `t ↦ tH`, `t ∈ [0, 1]`, with a continuous derivative there, and vectors `h_□` with
`Σ_□h_□ = H` (here `h_□ = ζ_□𝓗_n`):
`Ψ(H) - Ψ(0) = Σ_□∫_0^1 ∂/∂t_□ Ψ(tH + t_□h_□)|_{t_□ = 0} dt` (`cube_division`), the partial derivative being
`DΨ(tH)h_□` (`partial_eq`); a cube with `h_□ = 0` contributes nothing (`partial_zero`). The first step of the proof,
that the left side of `eq:cube-division` is `φ(1, 0) - φ(0, 0)` by the gauge invariance of `F`, is
`left_side` for a function invariant under a group action.
-/
import Mathlib

open Set Filter Topology

noncomputable section

namespace CoreLean
namespace CubeDivision

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The partial derivative in `t_□` at `t_□ = 0`. -/
theorem partial_eq {Ψ : V → ℝ} {D : V →L[ℝ] ℝ} {x : V} (hd : HasFDerivAt Ψ D x) (h : V) :
    HasDerivAt (fun r : ℝ => Ψ (x + r • h)) (D h) 0 := by
  have hl : HasDerivAt (fun r : ℝ => x + r • h) h 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const h).const_add x
  have hd' : HasFDerivAt Ψ D (x + (0 : ℝ) • h) := by simpa using hd
  have := hd'.comp_hasDerivAt (0 : ℝ) hl
  simpa [Function.comp_def] using this

theorem partial_zero {Ψ : V → ℝ} (x : V) : deriv (fun r : ℝ => Ψ (x + r • (0 : V))) 0 = 0 := by
  simp

/-- **`eq:cube-division`**, the interpolation. -/
theorem cube_division {ι : Type*} (s : Finset ι) (Ψ : V → ℝ) (DΨ : ℝ → V →L[ℝ] ℝ) (H : V) (h : ι → V)
    (hsum : ∑ i ∈ s, h i = H) (hd : ∀ t ∈ Icc (0 : ℝ) 1, HasFDerivAt Ψ (DΨ t) (t • H))
    (hc : ContinuousOn DΨ (Icc 0 1)) :
    Ψ H - Ψ 0 = ∑ i ∈ s, ∫ t in (0 : ℝ)..1, deriv (fun r : ℝ => Ψ (t • H + r • h i)) 0 := by
  -- the partial derivatives are `DΨ(t)h_□`
  have hpart : ∀ i ∈ s, ∫ t in (0 : ℝ)..1, deriv (fun r : ℝ => Ψ (t • H + r • h i)) 0 =
      ∫ t in (0 : ℝ)..1, DΨ t (h i) := by
    intro i _
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le zero_le_one] at ht
    exact (partial_eq (hd t ht) (h i)).deriv
  rw [Finset.sum_congr rfl hpart]
  have hcont : ∀ v : V, ContinuousOn (fun t => DΨ t v) (Icc 0 1) := fun v =>
    (ContinuousLinearMap.apply ℝ ℝ v).continuous.comp_continuousOn hc
  rw [← intervalIntegral.integral_finsetSum fun i _ =>
    (hcont (h i)).intervalIntegrable_of_Icc zero_le_one]
  -- the derivative along the segment
  have hseg : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt (fun t : ℝ => Ψ (t • H)) (∑ i ∈ s, DΨ t (h i)) t := by
    intro t ht
    have hl : HasDerivAt (fun t : ℝ => t • H) H t := by simpa using (hasDerivAt_id t).smul_const H
    have := (hd t ht).comp_hasDerivAt t hl
    rw [← map_sum, hsum]
    simpa [Function.comp_def] using this
  have hcs : ContinuousOn (fun t => ∑ i ∈ s, DΨ t (h i)) (Icc 0 1) :=
    continuousOn_finsetSum _ fun i _ => hcont (h i)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one
    (fun t ht => (hseg t ht).continuousAt.continuousWithinAt)
    (fun t ht => hseg t (Ioo_subset_Icc_self ht)) (hcs.intervalIntegrable_of_Icc zero_le_one)]
  simp

/-- The left side of `eq:cube-division` by the gauge invariance: if `U_n = g·x₁` and `U_{n+1} = x₀`, with `x_t` the
interpolating configurations, then `F(U_n) - F(U_{n+1}) = F(x₁) - F(x₀)`. -/
theorem left_side {G X : Type*} [Group G] [MulAction G X] (F : X → ℝ) (hF : ∀ (g : G) x, F (g • x) = F x)
    {Un Un1 x₀ x₁ : X} (g : G) (h1 : Un = g • x₁) (h0 : Un1 = x₀) : F Un - F Un1 = F x₁ - F x₀ := by
  rw [h1, h0, hF]

end CubeDivision
end CoreLean

end
