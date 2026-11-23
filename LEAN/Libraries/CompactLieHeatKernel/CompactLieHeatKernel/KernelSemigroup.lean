import CompactLieHeatKernel.HeatKernelData
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Chapman--Kolmogorov as a Markov-kernel semigroup law

`MeasurableHeatKernelData` stores Chapman--Kolmogorov at the density level because this is the
analytic identity naturally produced by the heat equation.  This file proves that the associated
positive-time transition kernels compose in the expected order.  No further analytic assumption is
used: the proof is only `withDensity` bookkeeping and Tonelli.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace CompactLieHeatKernel
namespace MeasurableHeatKernelData

variable {X : Type*} [MeasurableSpace X]
variable {μ : Measure X} [IsProbabilityMeasure μ]

/-- Integrating a measurable nonnegative function against a positive-time transition kernel is
exactly integration against the reference measure with the heat density inserted.  Keeping this
identity separate prevents the Chapman--Kolmogorov proof below from repeatedly elaborating the
`withDensity` implementation. -/
theorem lintegral_transitionKernel
    (K : MeasurableHeatKernelData μ) (t : ℝ≥0) (ht : t ≠ 0) (x : X)
    {g : X → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ z, g z ∂K.transitionKernel t x =
      ∫⁻ z, K.ennDensity t x z * g z ∂μ := by
  rw [K.transitionKernel_apply t ht x]
  simpa only [Pi.mul_apply] using
    (lintegral_withDensity_eq_lintegral_mul μ
      (Measurable.of_uncurry_left (K.measurable_ennDensity t ht)) hg)

/-- Density-level Chapman--Kolmogorov induces the actual Markov-kernel semigroup law.

The order is `transitionKernel t ∘ₖ transitionKernel s`: starting at `x`, first evolve for `s`,
then for `t`. -/
theorem transitionKernel_comp
    (K : MeasurableHeatKernelData μ) (s t : ℝ≥0) (hs : s ≠ 0) (ht : t ≠ 0) :
    K.transitionKernel t ∘ₖ K.transitionKernel s = K.transitionKernel (s + t) := by
  have hst : s + t ≠ 0 := by simp [hs, ht]
  refine Kernel.ext_fun fun x g hg => ?_
  have hsx : Measurable (K.ennDensity s x) :=
    Measurable.of_uncurry_left (K.measurable_ennDensity s hs)
  have htxy : Measurable (Function.uncurry (K.ennDensity t)) :=
    K.measurable_ennDensity t ht
  have hty (y : X) : Measurable (K.ennDensity t y) :=
    Measurable.of_uncurry_left htxy
  have htz (z : X) : Measurable (fun y => K.ennDensity t y z) :=
    Measurable.of_uncurry_right htxy
  have hgKernel : Measurable (fun y => ∫⁻ z, g z ∂K.transitionKernel t y) :=
    hg.lintegral_kernel
  have hprod :
      AEMeasurable
        (Function.uncurry fun y z =>
          K.ennDensity s x y * (K.ennDensity t y z * g z)) (μ.prod μ) := by
    exact ((hsx.comp measurable_fst).mul
      (htxy.mul (hg.comp measurable_snd))).aemeasurable
  calc
    ∫⁻ z, g z ∂(K.transitionKernel t ∘ₖ K.transitionKernel s) x
        = ∫⁻ y, ∫⁻ z, g z ∂K.transitionKernel t y ∂K.transitionKernel s x :=
          Kernel.lintegral_comp _ _ _ hg
    _ = ∫⁻ y, K.ennDensity s x y *
          (∫⁻ z, K.ennDensity t y z * g z ∂μ) ∂μ := by
          rw [K.lintegral_transitionKernel s hs x hgKernel]
          apply lintegral_congr
          intro y
          rw [K.lintegral_transitionKernel t ht y hg]
    _ = ∫⁻ y, ∫⁻ z,
          K.ennDensity s x y * (K.ennDensity t y z * g z) ∂μ ∂μ := by
          apply lintegral_congr
          intro y
          exact (lintegral_const_mul'' (μ := μ) (K.ennDensity s x y)
            (f := fun z => K.ennDensity t y z * g z)
            (((hty y).mul hg).aemeasurable)).symm
    _ = ∫⁻ z, ∫⁻ y,
          K.ennDensity s x y * (K.ennDensity t y z * g z) ∂μ ∂μ := by
          exact lintegral_lintegral_swap hprod
    _ = ∫⁻ z,
          (∫⁻ y, K.ennDensity s x y * K.ennDensity t y z ∂μ) * g z ∂μ := by
          apply lintegral_congr
          intro z
          calc
            ∫⁻ y, K.ennDensity s x y * (K.ennDensity t y z * g z) ∂μ
                = ∫⁻ y, (K.ennDensity s x y * K.ennDensity t y z) * g z ∂μ := by
                    apply lintegral_congr
                    intro y
                    rw [mul_assoc]
            _ = (∫⁻ y, K.ennDensity s x y * K.ennDensity t y z ∂μ) * g z :=
                  lintegral_mul_const'' (μ := μ) (g z)
                    (f := fun y => K.ennDensity s x y * K.ennDensity t y z)
                    ((hsx.mul (htz z)).aemeasurable)
    _ = ∫⁻ z, K.ennDensity (s + t) x z * g z ∂μ := by
          apply lintegral_congr
          intro z
          rw [show (∫⁻ y, K.ennDensity s x y * K.ennDensity t y z ∂μ) =
              K.ennDensity (s + t) x z by
            simpa [ennDensity] using K.chapmanKolmogorov s t hs ht x z]
    _ = ∫⁻ z, g z ∂K.transitionKernel (s + t) x := by
          symm
          exact K.lintegral_transitionKernel (s + t) hst x hg

end MeasurableHeatKernelData
end CompactLieHeatKernel
