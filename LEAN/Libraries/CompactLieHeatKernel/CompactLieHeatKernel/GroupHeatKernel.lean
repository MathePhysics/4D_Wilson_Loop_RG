import CompactLieHeatKernel.HeatKernelData
import Mathlib.MeasureTheory.Group.Defs
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Bi-invariant heat kernels on Lie groups

For a Lie group with a bi-invariant metric, the two-point heat kernel is invariant under simultaneous
left and right translation.  This file records that group-specific structure and derives the usual
one-variable central heat kernel `q_t(g) = k_t(1,g)`.
-/

noncomputable section

open MeasureTheory
open scoped Manifold ContDiff NNReal

namespace CompactLieHeatKernel

/-- Smooth heat-kernel data with the translation symmetries of a bi-invariant Lie-group Laplacian. -/
structure GroupHeatKernelData
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    (G : Type*) [TopologicalSpace G] [ChartedSpace H G] [MeasurableSpace G] [Group G] [LieGroup I ∞ G]
    (μ : Measure G) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
    extends SmoothHeatKernelData I G μ where
  leftInvariant : ∀ t : ℝ≥0, t ≠ 0 → ∀ a x y,
    density t (a * x) (a * y) = density t x y
  rightInvariant : ∀ t : ℝ≥0, t ≠ 0 → ∀ a x y,
    density t (x * a) (y * a) = density t x y

namespace GroupHeatKernelData

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H}
    {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [MeasurableSpace G] [Group G] [LieGroup I ∞ G]
    {μ : Measure G} [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]

/-- The usual one-variable heat kernel based at the identity. -/
def centralDensity (K : GroupHeatKernelData I G μ) (t : ℝ≥0) (g : G) : ℝ :=
  K.density t 1 g

/-- Positive-time central densities are continuous. -/
theorem centralDensity_continuous (K : GroupHeatKernelData I G μ)
    (t : ℝ≥0) (ht : t ≠ 0) :
    Continuous (K.centralDensity t) := by
  exact (K.continuous_density t ht).comp (continuous_const.prodMk continuous_id)

/-- Positive-time central densities are measurable whenever the measurable structure is Borel. -/
theorem centralDensity_measurable [BorelSpace G] (K : GroupHeatKernelData I G μ)
    (t : ℝ≥0) (ht : t ≠ 0) :
    Measurable (K.centralDensity t) :=
  (K.centralDensity_continuous t ht).measurable

/-- Simultaneous left invariance reduces the two-point kernel to a function of `x⁻¹y`. -/
theorem density_eq_centralDensity (K : GroupHeatKernelData I G μ)
    (t : ℝ≥0) (ht : t ≠ 0) (x y : G) :
    K.density t x y = K.centralDensity t (x⁻¹ * y) := by
  have h := K.leftInvariant t ht x⁻¹ x y
  simpa [centralDensity] using h.symm

/-- Strict positivity of the two-point heat kernel gives strict positivity of the central density. -/
theorem centralDensity_pos (K : GroupHeatKernelData I G μ)
    (t : ℝ≥0) (ht : t ≠ 0) (g : G) :
    0 < K.centralDensity t g := by
  simpa [centralDensity] using K.strictlyPositive t ht 1 g

/-- Positive-time central densities are nonnegative. -/
theorem centralDensity_nonnegative (K : GroupHeatKernelData I G μ)
    (t : ℝ≥0) (ht : t ≠ 0) (g : G) :
    0 ≤ K.centralDensity t g :=
  (K.centralDensity_pos t ht g).le

/-- On a compact group, the central density has a uniform positive lower bound at each positive
time. -/
theorem exists_uniform_central_lower_bound [CompactSpace G]
    (K : GroupHeatKernelData I G μ) (t : ℝ≥0) (ht : t ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ g, c ≤ K.centralDensity t g := by
  obtain ⟨c, hc, hbound⟩ :=
    K.toSmoothHeatKernelData.toContinuousHeatKernelData.exists_uniform_positive_lower_bound t ht
  exact ⟨c, hc, fun g ↦ by simpa [centralDensity] using hbound 1 g⟩

/-- On a compact group, the central density also has a uniform finite upper bound at each positive
time. -/
theorem exists_uniform_central_upper_bound [CompactSpace G]
    (K : GroupHeatKernelData I G μ) (t : ℝ≥0) (ht : t ≠ 0) :
    ∃ C : ℝ, ∀ g, K.centralDensity t g ≤ C := by
  let f : G → ℝ := K.centralDensity t
  obtain ⟨g₀, _hg₀, hgmax⟩ :=
    isCompact_univ.exists_isMaxOn Set.univ_nonempty
      (K.centralDensity_continuous t ht).continuousOn
  refine ⟨f g₀, fun g ↦ ?_⟩
  simpa [f] using hgmax (show g ∈ Set.univ by simp)

/-- Positive-time central density has total mass one in the nonnegative extended-real formulation. -/
theorem lintegral_centralDensity_eq_one (K : GroupHeatKernelData I G μ)
    (t : ℝ≥0) (ht : t ≠ 0) :
    ∫⁻ g, ENNReal.ofReal (K.centralDensity t g) ∂μ = 1 := by
  simpa [centralDensity] using K.mass_one t ht 1

/-- On a compact Borel group, every positive-time central density is Bochner integrable. -/
theorem centralDensity_integrable [BorelSpace G] [CompactSpace G]
    (K : GroupHeatKernelData I G μ) (t : ℝ≥0) (ht : t ≠ 0) :
    Integrable (K.centralDensity t) μ := by
  obtain ⟨C, hC⟩ := K.exists_uniform_central_upper_bound t ht
  exact Integrable.of_mem_Icc 0 C (K.centralDensity_measurable t ht).aemeasurable
    (Filter.Eventually.of_forall fun g ↦ ⟨(K.centralDensity_pos t ht g).le, hC g⟩)

/-- The real-valued central density is normalised to total mass one. -/
theorem integral_centralDensity_eq_one [BorelSpace G]
    (K : GroupHeatKernelData I G μ) (t : ℝ≥0) (ht : t ≠ 0) :
    ∫ g, K.centralDensity t g ∂μ = 1 := by -- totalisation-audit: allow nonnegative measurable heat density, whose lintegral is proved equal to one
  rw [integral_eq_lintegral_of_nonneg_ae]
  · rw [K.lintegral_centralDensity_eq_one t ht]
    simp
  · exact Filter.Eventually.of_forall fun g ↦ (K.centralDensity_pos t ht g).le
  · exact (K.centralDensity_measurable t ht).aestronglyMeasurable

/-- One-variable Chapman--Kolmogorov identity for the central heat kernel, in the nonnegative
extended-real formulation used by probability kernels. -/
theorem centralDensity_chapmanKolmogorov (K : GroupHeatKernelData I G μ)
    (s t : ℝ≥0) (hs : s ≠ 0) (ht : t ≠ 0) (g : G) :
    ∫⁻ h, ENNReal.ofReal (K.centralDensity s h) *
        ENNReal.ofReal (K.centralDensity t (h⁻¹ * g)) ∂μ =
      ENNReal.ofReal (K.centralDensity (s + t) g) := by
  calc
    ∫⁻ h, ENNReal.ofReal (K.centralDensity s h) *
        ENNReal.ofReal (K.centralDensity t (h⁻¹ * g)) ∂μ
        = ∫⁻ h, ENNReal.ofReal (K.density s 1 h) *
            ENNReal.ofReal (K.density t h g) ∂μ := by
              apply lintegral_congr
              intro h
              rw [K.density_eq_centralDensity t ht h g]
              rfl
    _ = ENNReal.ofReal (K.density (s + t) 1 g) :=
      K.chapmanKolmogorov s t hs ht 1 g
    _ = ENNReal.ofReal (K.centralDensity (s + t) g) := rfl

/-- Composition with inversion and right multiplication preserves continuity of a positive-time
central density. -/
theorem centralDensity_inv_mul_continuous (K : GroupHeatKernelData I G μ)
    (t : ℝ≥0) (ht : t ≠ 0) (g : G) :
    Continuous (fun h : G ↦ K.centralDensity t (h⁻¹ * g)) := by
  have hinvMul : ContMDiff I I ∞ (fun h : G ↦ h⁻¹ * g) :=
    (contMDiff_inv I ∞).mul contMDiff_const
  exact (K.centralDensity_continuous t ht).comp hinvMul.continuous

/-- The real-valued convolution integrand in the central Chapman--Kolmogorov identity is
integrable at positive times. -/
theorem centralDensity_convolution_integrable [BorelSpace G] [CompactSpace G]
    (K : GroupHeatKernelData I G μ)
    (s t : ℝ≥0) (hs : s ≠ 0) (ht : t ≠ 0) (g : G) :
    Integrable (fun h : G ↦ K.centralDensity s h * K.centralDensity t (h⁻¹ * g)) μ := by
  obtain ⟨Cs, hCs⟩ := K.exists_uniform_central_upper_bound s hs
  obtain ⟨Ct, hCt⟩ := K.exists_uniform_central_upper_bound t ht
  have hCs0 : 0 ≤ Cs :=
    (K.centralDensity_pos s hs 1).le.trans (hCs 1)
  have hmeas : Measurable
      (fun h : G ↦ K.centralDensity s h * K.centralDensity t (h⁻¹ * g)) :=
    ((K.centralDensity_continuous s hs).mul
      (K.centralDensity_inv_mul_continuous t ht g)).measurable
  exact Integrable.of_mem_Icc 0 (Cs * Ct) hmeas.aemeasurable
    (Filter.Eventually.of_forall fun h ↦ ⟨
      mul_nonneg (K.centralDensity_pos s hs h).le
        (K.centralDensity_pos t ht (h⁻¹ * g)).le,
      mul_le_mul (hCs h) (hCt (h⁻¹ * g))
        (K.centralDensity_pos t ht (h⁻¹ * g)).le hCs0⟩)

/-- One-variable Chapman--Kolmogorov identity for the real-valued central heat kernel. -/
theorem integral_centralDensity_chapmanKolmogorov [BorelSpace G] [CompactSpace G]
    (K : GroupHeatKernelData I G μ)
    (s t : ℝ≥0) (hs : s ≠ 0) (ht : t ≠ 0) (g : G) :
    (∫ h, K.centralDensity s h * K.centralDensity t (h⁻¹ * g) ∂μ) = -- totalisation-audit: allow explicitly proved integrable nonnegative convolution
      K.centralDensity (s + t) g := by -- totalisation-audit: allow integrable nonnegative heat-kernel convolution, identified with the proved lintegral semigroup
  have hst : s + t ≠ 0 := by simp [hs, ht]
  have hint := K.centralDensity_convolution_integrable s t hs ht g
  rw [integral_eq_lintegral_of_nonneg_ae]
  · calc
      ENNReal.toReal -- totalisation-audit: allow applied to a lintegral proved equal to finite ENNReal.ofReal data
          (∫⁻ h, ENNReal.ofReal
            (K.centralDensity s h * K.centralDensity t (h⁻¹ * g)) ∂μ)
          = ENNReal.toReal -- totalisation-audit: allow equality-preserving rewrite to the proved finite heat-kernel lintegral
              (∫⁻ h, ENNReal.ofReal (K.centralDensity s h) *
                ENNReal.ofReal (K.centralDensity t (h⁻¹ * g)) ∂μ) := by
              apply congrArg ENNReal.toReal -- totalisation-audit: allow congruence applied to quantities already proved equal to finite heat-kernel lintegrals
              apply lintegral_congr
              intro h
              rw [ENNReal.ofReal_mul (K.centralDensity_pos s hs h).le]
      _ = ENNReal.toReal (ENNReal.ofReal (K.centralDensity (s + t) g)) := by -- totalisation-audit: allow ofReal of a strictly positive finite real value
            rw [K.centralDensity_chapmanKolmogorov s t hs ht g]
      _ = K.centralDensity (s + t) g := by
            rw [ENNReal.toReal_ofReal (K.centralDensity_pos (s + t) hst g).le]
  · exact Filter.Eventually.of_forall fun h ↦
      mul_nonneg (K.centralDensity_pos s hs h).le
        (K.centralDensity_pos t ht (h⁻¹ * g)).le
  · exact hint.aestronglyMeasurable

/-- Symmetry of the two-point kernel gives inversion symmetry of the central density. -/
theorem centralDensity_inv (K : GroupHeatKernelData I G μ)
    (t : ℝ≥0) (ht : t ≠ 0) (g : G) :
    K.centralDensity t g⁻¹ = K.centralDensity t g := by
  have hleft := K.density_eq_centralDensity t ht g 1
  have hright := K.density_eq_centralDensity t ht 1 g
  calc
    K.centralDensity t g⁻¹ = K.density t g 1 := by simpa using hleft.symm
    _ = K.density t 1 g := K.symmetric t ht g 1
    _ = K.centralDensity t g := by simpa using hright

/-- Left and right invariance imply conjugation invariance, i.e. centrality of `q_t`. -/
theorem centralDensity_conj (K : GroupHeatKernelData I G μ)
    (t : ℝ≥0) (ht : t ≠ 0) (a g : G) :
    K.centralDensity t (a * g * a⁻¹) = K.centralDensity t g := by
  unfold centralDensity
  calc
    K.density t 1 (a * g * a⁻¹)
        = K.density t a (a * g) := by
            simpa using K.rightInvariant t ht a⁻¹ a (a * g)
    _ = K.density t 1 g := by
            simpa using K.leftInvariant t ht a 1 g

end GroupHeatKernelData

end CompactLieHeatKernel
