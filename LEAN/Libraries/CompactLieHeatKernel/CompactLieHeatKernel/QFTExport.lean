import CompactLieHeatKernel.GroupHeatKernel

/-!
# QFT-facing central heat-kernel export

This file isolates the one-variable positive-time heat-kernel API used by finite-lattice gauge/QFT
constructions.  It deliberately contains no lattice combinatorics and no dependency on a particular
QFT project: downstream developments should adapt this record to their local heat-kernel interface.

The record carries only theorem-level consequences of `GroupHeatKernelData`.  In particular, the
Bochner integrals below are accompanied by explicit integrability proofs; no totalised fallback
value of `MeasureTheory.integral` is used as an analytic premise.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal Manifold ContDiff

namespace CompactLieHeatKernel

/-- The one-variable central heat-kernel package needed by the finite-volume QFT interface.

`density t g` is the central heat kernel `q_t(g)` relative to the reference Haar probability
measure `μ`.  Time zero is deliberately unconstrained, just as in `MeasurableHeatKernelData`.
-/
structure CentralHeatKernelData
    (G : Type*) [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
    [Group G] [CompactSpace G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] where
  density : ℝ≥0 → G → ℝ
  continuous_density : ∀ t, t ≠ 0 → Continuous (density t)
  measurable_density : ∀ t, t ≠ 0 → Measurable (density t)
  strictlyPositive : ∀ t, t ≠ 0 → ∀ g, 0 < density t g
  nonnegative : ∀ t, t ≠ 0 → ∀ g, 0 ≤ density t g
  lowerBound : ∀ t, t ≠ 0 → ∃ c : ℝ, 0 < c ∧ ∀ g, c ≤ density t g
  upperBound : ∀ t, t ≠ 0 → ∃ C : ℝ, ∀ g, density t g ≤ C
  integrable : ∀ t, t ≠ 0 → Integrable (density t) μ
  mass_one : ∀ t, t ≠ 0 →
    ∫⁻ g, ENNReal.ofReal (density t g) ∂μ = 1
  integral_mass_one : ∀ t, t ≠ 0 →
    (∫ g, density t g ∂μ) = 1 -- totalisation-audit: allow integrable nonnegative heat density with proved lintegral mass one
  central : ∀ t, t ≠ 0 → ∀ a g,
    density t (a * g * a⁻¹) = density t g
  inversion : ∀ t, t ≠ 0 → ∀ g,
    density t g⁻¹ = density t g
  semigroup_integrable : ∀ s t, s ≠ 0 → t ≠ 0 → ∀ g,
    Integrable (fun h => density s h * density t (h⁻¹ * g)) μ
  semigroup : ∀ s t, s ≠ 0 → t ≠ 0 → ∀ g,
    ∫⁻ h, ENNReal.ofReal (density s h) * ENNReal.ofReal (density t (h⁻¹ * g)) ∂μ =
      ENNReal.ofReal (density (s + t) g)
  semigroup_real : ∀ s t, s ≠ 0 → t ≠ 0 → ∀ g,
    (∫ h, density s h * density t (h⁻¹ * g) ∂μ) = density (s + t) g -- totalisation-audit: allow explicitly integrable heat-kernel convolution

namespace GroupHeatKernelData

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H}
    {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [MeasurableSpace G] [BorelSpace G]
    [Group G] [LieGroup I ∞ G] [CompactSpace G]
    {μ : Measure G} [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]

/-- Forget the two-point/manifold scaffolding and expose exactly the reusable central heat-kernel
package needed by lattice QFT constructions. -/
def toCentralHeatKernelData (K : GroupHeatKernelData I G μ) : CentralHeatKernelData G μ where
  density := K.centralDensity
  continuous_density := K.centralDensity_continuous
  measurable_density := K.centralDensity_measurable
  strictlyPositive := K.centralDensity_pos
  nonnegative := K.centralDensity_nonnegative
  lowerBound := K.exists_uniform_central_lower_bound
  upperBound := K.exists_uniform_central_upper_bound
  integrable := K.centralDensity_integrable
  mass_one := K.lintegral_centralDensity_eq_one
  integral_mass_one := K.integral_centralDensity_eq_one
  central := K.centralDensity_conj
  inversion := K.centralDensity_inv
  semigroup_integrable := K.centralDensity_convolution_integrable
  semigroup := K.centralDensity_chapmanKolmogorov
  semigroup_real := K.integral_centralDensity_chapmanKolmogorov

end GroupHeatKernelData

end CompactLieHeatKernel
