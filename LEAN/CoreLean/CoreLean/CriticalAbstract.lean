/-
`lem:critical` of BALABAN_CORE.tex (`a021c13be348`), in abstract form: the three steps of the proof which do not use
the gauge structure. `E` stands for the `1`-forms with values in `𝔤` (`𝒜`), `F` for the functions on the bonds of the
layers (`ℱ`, with the inner product `Σ_c a_c⁴ tr μ(c)ν(c)`), `X` for the relative average `𝖷 = Q + 𝖢` of
`prop:relative-average-order` with the derivative `Q` at `0`, and `S` for the action along `A ↦ e^{ia₀A}U` with the
derivative `ℓ = ⟨·, J(U)⟩` at `0`.
1. *`Q` is onto* (`range_eq_top_of_test`): if every `μ ∈ F` has a test field `f` with `⟨μ, Qf⟩ ≥ c‖μ‖²`, `c > 0` (the
   first line of `eq:test-field`), the only `μ` orthogonal to the range of `Q` is `0`.
2. *A curve of forms with vanishing relative averages* (`critical_curve`): for `δA ∈ ker Q` there is a curve `A_t`
   with `A_0 = 0`, `(d/dt)A_t|₀ = δA`, and `𝖷(A_t) = 0` for small `t` (`eq:critical-curve`), by the implicit function
   theorem.
3. *Criticality* (`critical_of_curves`, (i)): if the action is stationary along every such curve, then
   `⟨δA, J(U)⟩ = ℓ(δA) = 0` on `ker Q`; *conversely* (`curves_of_critical`, (iii)): if `ℓ` vanishes on `ker Q`, the
   action is stationary along every curve in `{𝖷 = 0}` through `0`.
Not formalised: the removal of the site factors by a gauge transformation (which identifies the curves of `{𝖷 = 0}`
with curves in `𝔙(V)`), and (ii).
-/
import Mathlib

open Filter Topology

noncomputable section

namespace CoreLean
namespace Critical

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- **`Q` is onto**: a test field for every `μ` with `⟨μ, Qf⟩ ≥ c‖μ‖²` gives `range Q = F`. -/
theorem range_eq_top_of_test {Q : E →L[ℝ] F} {c : ℝ} (hc : 0 < c)
    (h : ∀ μ : F, ∃ f : E, c * ‖μ‖ ^ 2 ≤ inner ℝ μ (Q f)) : LinearMap.range (Q : E →ₗ[ℝ] F) = ⊤ := by
  have hperp : (LinearMap.range (Q : E →ₗ[ℝ] F))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro μ hμ
    obtain ⟨f, hf⟩ := h μ
    have h0 : inner ℝ (Q f) μ = 0 := (Submodule.mem_orthogonal _ _).1 hμ _ ⟨f, rfl⟩
    rw [real_inner_comm] at h0
    rw [h0] at hf
    have : ‖μ‖ ^ 2 = 0 := le_antisymm (by nlinarith [sq_nonneg ‖μ‖]) (sq_nonneg _)
    simpa using this
  exact Submodule.orthogonal_eq_bot_iff.1 hperp

/-- **A curve of forms with vanishing relative averages** (`eq:critical-curve`): for `δA ∈ ker Q` there is a curve
`A_t` with `A_0 = 0`, derivative `δA` at `0`, and `𝖷(A_t) = 0` for small `t`. -/
theorem critical_curve {X : E → F} {Q : E →L[ℝ] F} (hX : HasStrictFDerivAt X Q 0) (hX0 : X 0 = 0)
    (hQ : LinearMap.range (Q : E →ₗ[ℝ] F) = ⊤) {δ : E} (hδ : Q δ = 0) :
    ∃ γ : ℝ → E, γ 0 = 0 ∧ HasDerivAt γ δ 0 ∧ ∀ᶠ t in 𝓝 0, X (γ t) = 0 := by
  set k : LinearMap.ker (Q : E →ₗ[ℝ] F) := ⟨δ, LinearMap.mem_ker.2 hδ⟩
  set φ := hX.implicitFunction X Q hQ
  refine ⟨fun t => φ (X 0) (t • k), ?_, ?_, ?_⟩
  · simp only [zero_smul]
    exact hX.implicitFunction_apply_image hQ
  · have hφ := (hX.to_implicitFunction hQ).hasFDerivAt
    have hline : HasDerivAt (fun t : ℝ => t • k) k 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const k
    have := hφ.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
    exact this
  · have hlim : Tendsto (fun t : ℝ => (X 0, t • k)) (𝓝 0) (𝓝 (X 0, (0 : LinearMap.ker (Q : E →ₗ[ℝ] F)))) := by
      refine tendsto_const_nhds.prodMk_nhds ?_
      have : Tendsto (fun t : ℝ => t • k) (𝓝 0) (𝓝 ((0 : ℝ) • k)) :=
        (continuous_id.smul continuous_const).tendsto 0
      simpa using this
    filter_upwards [hlim.eventually (hX.map_implicitFunction_eq hQ)] with t ht
    rw [← hX0]
    exact ht

/-- **`lem:critical`(i)**, abstract form: if the action is stationary along every curve in `{𝖷 = 0}` through `0`,
then `ℓ = ⟨·, J(U)⟩` vanishes on `ker Q`, that is, `U` is critical. -/
theorem critical_of_curves {X : E → F} {Q : E →L[ℝ] F} (hX : HasStrictFDerivAt X Q 0) (hX0 : X 0 = 0)
    (hQ : LinearMap.range (Q : E →ₗ[ℝ] F) = ⊤) {S : E → ℝ} {ℓ : E →L[ℝ] ℝ} (hS : HasFDerivAt S ℓ 0)
    (hcurve : ∀ γ : ℝ → E, γ 0 = 0 → DifferentiableAt ℝ γ 0 → (∀ᶠ t in 𝓝 0, X (γ t) = 0) →
      deriv (fun t => S (γ t)) 0 = 0)
    {δ : E} (hδ : Q δ = 0) : ℓ δ = 0 := by
  obtain ⟨γ, hγ0, hγ', hγX⟩ := critical_curve hX hX0 hQ hδ
  have h1 : HasDerivAt (fun t => S (γ t)) (ℓ δ) 0 := hS.comp_hasDerivAt_of_eq 0 hγ' hγ0.symm
  rw [← h1.deriv]
  exact hcurve γ hγ0 hγ'.differentiableAt hγX

/-- **`lem:critical`(iii)**, abstract form: if `ℓ` vanishes on `ker Q`, the action is stationary along every curve
in `{𝖷 = 0}` through `0`. -/
theorem curves_of_critical {X : E → F} {Q : E →L[ℝ] F} (hX : HasFDerivAt X Q 0) {S : E → ℝ}
    {ℓ : E →L[ℝ] ℝ} (hS : HasFDerivAt S ℓ 0) (hcrit : ∀ δ, Q δ = 0 → ℓ δ = 0) {γ : ℝ → E} {v : E}
    (hγ0 : γ 0 = 0) (hγ : HasDerivAt γ v 0) (hγX : ∀ᶠ t in 𝓝 0, X (γ t) = 0) :
    HasDerivAt (fun t => S (γ t)) 0 0 := by
  have h1 : HasDerivAt (fun t => X (γ t)) (Q v) 0 := hX.comp_hasDerivAt_of_eq 0 hγ hγ0.symm
  have h2 : HasDerivAt (fun t => X (γ t)) 0 0 :=
    (hasDerivAt_const (0 : ℝ) (0 : F)).congr_of_eventuallyEq hγX
  have hv : Q v = 0 := h1.unique h2
  have h3 : HasDerivAt (fun t => S (γ t)) (ℓ v) 0 := hS.comp_hasDerivAt_of_eq 0 hγ hγ0.symm
  rwa [hcrit v hv] at h3

end Critical
end CoreLean

end
