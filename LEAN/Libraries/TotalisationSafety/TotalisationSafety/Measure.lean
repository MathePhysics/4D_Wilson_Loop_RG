import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Measure-theoretic guarded interfaces

The ambient definitions of the Bochner integral and pushforward measure are total.  These wrappers
carry the hypotheses selecting the mathematically intended branches before the corresponding value
is exposed.
-/

namespace TotalisationSafety

open MeasureTheory

/-- A measurable map, bundled before forming a pushforward measure. -/
structure MeasurableMap
    (α : Type*) (β : Type*) [MeasurableSpace α] [MeasurableSpace β] where
  toFun : α → β
  measurable : Measurable toFun

namespace MeasurableMap

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

instance : CoeFun (MeasurableMap α β) (fun _ => α → β) :=
  ⟨MeasurableMap.toFun⟩

/-- Pushforward along a map whose measurability is already part of the data. -/
noncomputable def pushforward (f : MeasurableMap α β) (μ : Measure α) : Measure β :=
  Measure.map f.toFun μ -- totalisation-audit: allow MeasurableMap carries measurability

/-- The bundled measurable map is in particular almost-everywhere measurable for every measure. -/
theorem aemeasurable (f : MeasurableMap α β) (μ : Measure α) : AEMeasurable f.toFun μ :=
  f.measurable.aemeasurable

end MeasurableMap

/-- A Bochner-integrable function with a complete target space.

The target completeness hypothesis is included because the ambient Bochner integral returns a
fallback value when the target is not complete.
-/
structure IntegrableFunction
    (α : Type*) (E : Type*) [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure α) where
  toFun : α → E
  integrable : Integrable toFun μ

namespace IntegrableFunction

variable {α E : Type*} [MeasurableSpace α]
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {μ : Measure α}

instance : CoeFun (IntegrableFunction α E μ) (fun _ => α → E) :=
  ⟨IntegrableFunction.toFun⟩

/-- The Bochner integral, exposed only after integrability and completeness are available. -/
noncomputable def integral (f : IntegrableFunction α E μ) : E :=
  ∫ x, f.toFun x ∂μ -- totalisation-audit: allow IntegrableFunction carries integrability and CompleteSpace

end IntegrableFunction

/-- A finite measure bundled with the proof that it is nonzero.  This rules out the arbitrary
zero-measure branch of `FiniteMeasure.normalize`. -/
structure NonzeroFiniteMeasure
    (Ω : Type*) [MeasurableSpace Ω] where
  measure : FiniteMeasure Ω
  ne_zero : measure ≠ 0

namespace NonzeroFiniteMeasure

variable {Ω : Type*} [MeasurableSpace Ω] [Nonempty Ω]

/-- Normalisation exposed only for a finite measure already known to be nonzero. -/
noncomputable def normalize (μ : NonzeroFiniteMeasure Ω) : ProbabilityMeasure Ω :=
  μ.measure.normalize

end NonzeroFiniteMeasure

/-- A probability defect computed in `ℝ`, avoiding truncated subtraction in `ℝ≥0`. -/
def probabilityDefect
    {Ω : Type*} [MeasurableSpace Ω]
    (P : ProbabilityMeasure Ω) (A : Set Ω) : ℝ :=
  (P A : ℝ) - 1

end TotalisationSafety
