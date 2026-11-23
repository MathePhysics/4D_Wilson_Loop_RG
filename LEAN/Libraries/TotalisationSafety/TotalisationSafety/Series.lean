import Mathlib.Topology.Algebra.InfiniteSum.Defs

/-!
# Convergent infinite sums

`tsum` is total in mathlib: a non-summable family is assigned the fallback value `0`.
`ConvergentSeries` carries `Summable` before exposing the sum.
-/

namespace TotalisationSafety

/-- A family together with a proof that its unconditional infinite sum exists. -/
structure ConvergentSeries
    (ι : Type*) (E : Type*) [AddCommMonoid E] [TopologicalSpace E] where
  term : ι → E
  summable : Summable term

namespace ConvergentSeries

variable {ι E : Type*} [AddCommMonoid E] [TopologicalSpace E]

/-- The infinite sum of a family known to be summable. -/
noncomputable def sum (s : ConvergentSeries ι E) : E :=
  ∑' i, s.term i -- totalisation-audit: allow ConvergentSeries carries Summable

/-- The bundled summability proof identifies `sum` as a genuine sum rather than a fallback value. -/
theorem hasSum (s : ConvergentSeries ι E) : HasSum s.term s.sum :=
  s.summable.hasSum

end ConvergentSeries

end TotalisationSafety
