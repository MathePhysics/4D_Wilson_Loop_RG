import CoreLean.WilsonLoop.Lattice

/-!
# The measure `dU` is a probability measure

`CoreLean.WilsonLoop.haar G` is the Haar measure `Measure.haarMeasure ⊤` of the gauge group, and
`CoreLean.WilsonLoop.haarField G n` is its product over the positive bonds.  This file checks
that this Haar measure is the normalised one, so that `dU` is a probability measure, as in
[WL] l.91.

## Main statements

* `CoreLean.WilsonLoop.isProbabilityMeasure_haar`
* `CoreLean.WilsonLoop.isProbabilityMeasure_haarField`
-/

namespace CoreLean

namespace WilsonLoop

open MeasureTheory

variable {N : ℕ} (G : GaugeGroup N) [CompactSpace G.carrier]

/-- The Haar measure of the gauge group gives the group the measure `1`. -/
theorem isProbabilityMeasure_haar : IsProbabilityMeasure (haar G) :=
  ⟨by
    simpa [haar] using
      Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts G.carrier))⟩

/-- The measure `dU` on the gauge fields with values in `G` is a probability measure. -/
theorem isProbabilityMeasure_haarField (n : ℕ) [NeZero n] :
    IsProbabilityMeasure (haarField G n) := by
  have := isProbabilityMeasure_haar G
  unfold haarField
  infer_instance

end WilsonLoop

end CoreLean
