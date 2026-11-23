/-
`lem:global-holder` of BALABAN_CORE.tex (`a021c13be348`), the two steps of the proof of `eq:global-holder`.

* *The cut functions*: with `λ = Σ_{y'}ζ_{y'}λ` (`lem:block-partition`, `0 ≤ ζ ≤ 1`, modulus `C_ζ`), the transported
  difference of `ζλ` at two sites is `ζ(x')(Ad λ(x') - λ(x)) + (ζ(x') - ζ(x))λ(x)` when both lie in `Δ̃(y')`
  (`cut_inside`), and a transport of `(ζ(x') - ζ(x))` times a value of `λ` otherwise (`cut_outside_left`,
  `cut_outside_right`, the transports changing the norm by a factor of at most `2`); so
  `‖ζλ‖_ε + ‖ζλ‖_∞ ≤ (2C_ζ + 1)(‖λ‖_{∞,Δ̃} + [λ]_{ε})` (`cut_norm`).
* *The sum*: with the kernel bound `‖(∇G'∇^*λ)(x)‖ ≤ Σ_{y'}B'_0(ε, 0)e^{-δ₀d(y, y')}(2C_ζ + 2)(‖λ‖_{∞,Δ̃(y')} + [λ]_{ε;y'})`
  (`eq:propagator-second`, stated in the core, the hypothesis here), `weighted_kernel_bound` of `GlobalBounds.lean`
  gives `ϖ(y)‖(∇G'∇^*λ)(x)‖ ≤ L⁴(2C_ζ + 2)B'_0(ε, 0)c a_j^σ‖λ‖_{ε,(σ),ϖ}` (`global_holder_sum`), the first term of
  `B_h(ε)`.
-/
import CoreLean.GlobalBounds

noncomputable section

namespace CoreLean
namespace GlobalHolder

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Both sites in the cube: `‖T(ζ'u') - ζu‖ ≤ |ζ'|‖Tu' - u‖ + |ζ' - ζ|‖u‖`. -/
theorem cut_inside (T : E →L[ℝ] E) (z z' : ℝ) (u u' : E) :
    ‖T (z' • u') - z • u‖ ≤ |z'| * ‖T u' - u‖ + |z' - z| * ‖u‖ := by
  have e : T (z' • u') - z • u = z' • (T u' - u) + (z' - z) • u := by
    rw [map_smul, smul_sub, sub_smul]; abel
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]

/-- The first site outside the cube (`ζ(x) = 0`). -/
theorem cut_outside_left (T : E →L[ℝ] E) (hT : ∀ w, ‖T w‖ ≤ 2 * ‖w‖) (z' : ℝ) (u' : E) :
    ‖T (z' • u') - (0 : ℝ) • (0 : E)‖ ≤ 2 * |z' - 0| * ‖u'‖ := by
  rw [smul_zero, sub_zero, sub_zero, map_smul, norm_smul, Real.norm_eq_abs]
  have := hT u'
  nlinarith [abs_nonneg z']

/-- The second site outside the cube (`ζ(x') = 0`). -/
theorem cut_outside_right (T : E →L[ℝ] E) (z : ℝ) (u : E) :
    ‖T ((0 : ℝ) • (0 : E)) - z • u‖ ≤ |0 - z| * ‖u‖ := by
  rw [smul_zero, map_zero, zero_sub, norm_neg, norm_smul, Real.norm_eq_abs, zero_sub, abs_neg]

/-- The norm of a cut function: `‖ζλ‖_ε + ‖ζλ‖_∞ ≤ (2C_ζ + 1)(‖λ‖ + [λ])`, from the three cases. -/
theorem cut_norm {Cζ S H D : ℝ} (hC : 0 ≤ Cζ) (hS : 0 ≤ S) (hH : 0 ≤ H)
    (hD : D ≤ max (H + Cζ * S) (2 * Cζ * S)) :
    D + S ≤ (2 * Cζ + 1) * (S + H) := by
  have h1 : H + Cζ * S ≤ (2 * Cζ + 1) * (S + H) - S := by nlinarith
  have h2 : 2 * Cζ * S ≤ (2 * Cζ + 1) * (S + H) - S := by nlinarith
  have := hD.trans (max_le h1 h2)
  linarith

/-- **The sum** of `eq:global-holder`, by `weighted_kernel_bound`. -/
theorem global_holder_sum {ι : Type*} (B : Finset ι) (j : ι → ℕ) (d : ι → ι → ℝ) (ϖ Λ : ι → ℝ)
    {L η δ θ RM B0' Cζ c m σ : ℝ} (hL : 1 ≤ L) (hη : 0 < η) (hRMpos : 0 < RM)
    (hRM : 4 * Real.log L ≤ θ * RM) (hσ : |σ| ≤ 4) (hB : 0 ≤ B0') (hC : 0 ≤ Cζ) (hm : 0 ≤ m)
    (hd : ∀ y y', 0 ≤ d y y') (hscale : ∀ y y', |(j y : ℝ) - j y'| ≤ 1 + d y y' / RM)
    (hϖ : ∀ y y', ϖ y ≤ Real.exp (θ * d y y') * ϖ y') (hϖ0 : ∀ y, 0 ≤ ϖ y)
    (hΛ0 : ∀ y, 0 ≤ Λ y) (hlam : ∀ y' ∈ B, ϖ y' * Λ y' ≤ ((L : ℝ) ^ j y' * η) ^ σ * m) {y : ι}
    (hsum : ∑ y' ∈ B, Real.exp (-((δ - 2 * θ) * d y y')) ≤ c) {v : ℝ}
    (hv : v ≤ ∑ y' ∈ B, B0' * Real.exp (-(δ * d y y')) * (2 * Cζ + 2) * Λ y') :
    ϖ y * v ≤ L ^ (4 : ℝ) * (B0' * (2 * Cζ + 2)) * c * ((L : ℝ) ^ j y * η) ^ σ * m := by
  have hv' : v ≤ ∑ y' ∈ B, (B0' * (2 * Cζ + 2)) * ((L : ℝ) ^ j y * η) ^ (0 : ℝ) * Real.exp (-(δ * d y y')) *
      Λ y' := by
    refine hv.trans (le_of_eq (Finset.sum_congr rfl fun y' _ => ?_))
    rw [Real.rpow_zero]; ring
  have := GlobalBounds.weighted_kernel_bound B j d ϖ Λ hL hη hRMpos hRM hσ (by positivity) hm hd hscale hϖ hϖ0 hΛ0 hlam
    hsum hv'
  rwa [add_zero] at this

end GlobalHolder
end CoreLean

end
