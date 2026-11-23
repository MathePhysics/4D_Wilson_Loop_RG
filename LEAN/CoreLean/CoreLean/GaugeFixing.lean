/-
`lem:gauge-fixing` of BALABAN_CORE.tex: the insertion of the gauge fixing.

Setting. `G` is a group with a measurable structure in which multiplication and inversion are measurable,
with a σ-finite measure `dv` which is invariant under left multiplication and under inversion (the
normalised Haar measure of the compact group `G`). The points `x ∈ 𝖯' = ⋃_{y ∈ 𝖯} B(y) \ {y}` form a finite
type, `y(x)` is the point of `𝖯` whose block contains `x`, and the transports `V_n(y(x), x)` are elements
of `G`; `d(v) = ‖v - id‖` and `t(v) = re tr v` are arbitrary real functions on `G`. With
`u(y) = id` for `y ∈ 𝖯` the transports after the gauge transformation are `V_n(y(x), x)u(x)⁻¹`, so that
the integrand is a product over `𝖯'` of one function of `V_n(y(x), x)u(x)⁻¹` (`eq:gauge-fixing-function`);
by Fubini and the invariance of `dv` under `u ↦ V u⁻¹` each factor integrates to `z(g, ε)`. The count
`#𝖯' = (L⁴ - 1)#𝖯` (each block has `L⁴` points, and the blocks are disjoint) enters as the cardinality of
the index type.
-/
import Mathlib

open MeasureTheory

noncomputable section

namespace CoreLean

namespace GaugeFixing

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] [MeasurableInv G]
  (μ : Measure G) [SigmaFinite μ] [μ.IsMulLeftInvariant] [μ.IsInvInvariant]

/-- The integral of `u ↦ φ(V u⁻¹)` is that of `φ`. -/
lemma integral_mul_inv (φ : G → ℝ) (V : G) : ∫ u, φ (V * u⁻¹) ∂μ = ∫ v, φ v ∂μ := by
  rw [integral_inv_eq_self (fun u => φ (V * u)) μ, integral_mul_left_eq_self φ V]

/-- The product form: `∫ Π_{x ∈ 𝖯'} φ(V(x)u(x)⁻¹) Π_x du(x) = (∫ φ)^{#𝖯'}`. -/
theorem integral_prod_mul_inv {ι : Type*} [Fintype ι] (φ : G → ℝ) (V : ι → G) :
    ∫ u : ι → G, ∏ x, φ (V x * (u x)⁻¹) ∂(Measure.pi fun _ => μ) =
      (∫ v, φ v ∂μ) ^ Fintype.card ι := by
  rw [integral_fintype_prod_eq_prod (fun x t => φ (V x * t⁻¹))]
  simp_rw [integral_mul_inv μ φ]
  rw [Finset.prod_const, Finset.card_univ]

/-- `z(g, ε) = ∫_G χ(‖v - id‖ < ε) e^{-(1 - re tr v)/g²} dv` (`eq:gauge-normalisation`). -/
def z (d t : G → ℝ) (g ε : ℝ) : ℝ :=
  ∫ v, Set.indicator {w | d w < ε} (fun w => Real.exp (-(1 / g ^ 2) * (1 - t w))) v ∂μ

/-- `lem:gauge-fixing` (`eq:gauge-fixing-identity`): with `V^u(y(x), x) = V(y(x), x)u(x)⁻¹`,
`∫ χ_Ax(𝖯, V^u) exp(-𝐆(𝖯, V^u)/g²) Π_{x ∈ 𝖯'} du(x) = z(g, ε)^{#𝖯'}`, `#𝖯' = (L⁴ - 1)#𝖯`. -/
theorem gauge_fixing {ι : Type*} [Fintype ι] (d t : G → ℝ) (g ε : ℝ) (V : ι → G) :
    ∫ u : ι → G,
        (∏ x, Set.indicator {w | d w < ε} (fun _ => (1 : ℝ)) (V x * (u x)⁻¹)) *
          Real.exp (-(1 / g ^ 2) * ∑ x, (1 - t (V x * (u x)⁻¹))) ∂(Measure.pi fun _ => μ) =
      z μ d t g ε ^ Fintype.card ι := by
  have e : ∀ u : ι → G,
      (∏ x, Set.indicator {w | d w < ε} (fun _ => (1 : ℝ)) (V x * (u x)⁻¹)) *
          Real.exp (-(1 / g ^ 2) * ∑ x, (1 - t (V x * (u x)⁻¹))) =
        ∏ x, Set.indicator {w | d w < ε} (fun w => Real.exp (-(1 / g ^ 2) * (1 - t w)))
          (V x * (u x)⁻¹) := by
    intro u
    rw [Finset.mul_sum, Real.exp_sum, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun x _ => ?_
    by_cases h : V x * (u x)⁻¹ ∈ {w | d w < ε}
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, one_mul]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, zero_mul]
  simp_rw [e]
  exact integral_prod_mul_inv μ _ V

end GaugeFixing

end CoreLean
