import TotalisationSafety
import FriedrichsExtension.FriedrichsTheorem

/-!
# Friedrichs-specific totalisation-safety certificates

Lean and mathlib deliberately totalise several operations which are mathematically partial.
This project does **not** treat the resulting default/junk values as mathematically meaningful.
Generic checked constructions, reusable partial-operation abstractions and the generic safety
policy now live in the separate `TotalisationSafety` package imported above.

This module contains only the Friedrichs-extension-specific proof obligations needed to instantiate
that generic safety layer for the operators and constants constructed in this project.

In particular:
* reciprocals/division are used only with a proved positive denominator;
* `Real.sqrt` is used only with a proved nonnegative radicand, and reciprocals of square roots
  only with a proved positive radicand;
* `LinearPMap.inverse` is used only after proving trivial kernel;
* `LinearPMap.adjoint`, whose mathlib implementation has a junk-value branch for non-dense
  domains, is used only for operators whose domains have already been proved dense.

-/

open scoped InnerProductSpace

noncomputable section

namespace FriedrichsExtension
namespace SemiboundedSymmetricOperator

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The denominator used in the energy-space embedding is strictly positive. -/
theorem totalisationGuard_energyDenominatorPositive
    (A : SemiboundedSymmetricOperator H) (shift : ℝ)
    (hshift : 0 < A.lowerBound + shift) :
    0 < A.lowerBound + shift :=
  hshift

/-- Hence the square root inverted in the energy-space embedding is nonzero. -/
theorem totalisationGuard_energySqrtPositive
    (A : SemiboundedSymmetricOperator H) (shift : ℝ)
    (hshift : 0 < A.lowerBound + shift) :
    0 < Real.sqrt (A.lowerBound + shift) :=
  Real.sqrt_pos.2 hshift

variable [CompleteSpace H]

/-- The bounded resolvent has trivial kernel before `LinearPMap.inverse` is used. -/
theorem totalisationGuard_resolventInverseKer
    (A : SemiboundedSymmetricOperator H) (shift : ℝ)
    (hshift : 0 < A.lowerBound + shift) :
    (A.friedrichsResolventPMap shift hshift).ker = ⊥ :=
  A.friedrichsResolventPMap_ker_eq_bot shift hshift

/-- The shifted unbounded operator has dense domain before its `LinearPMap.adjoint` value is used. -/
theorem totalisationGuard_shiftedAdjointDense
    (A : SemiboundedSymmetricOperator H) (shift : ℝ)
    (hshift : 0 < A.lowerBound + shift) :
    Dense ((A.shiftedFriedrichsOperator shift hshift).domain : Set H) :=
  A.shiftedFriedrichsOperator_dense_domain shift hshift

/-- The unshifted Friedrichs extension has dense domain before its `LinearPMap.adjoint` value is used. -/
theorem totalisationGuard_extensionAdjointDense
    (A : SemiboundedSymmetricOperator H) (shift : ℝ)
    (hshift : 0 < A.lowerBound + shift) :
    Dense ((A.friedrichsExtension shift hshift).domain : Set H) :=
  A.friedrichsExtension_dense_domain shift hshift

/-- The denominator in the change-of-shift comparison is strictly positive. -/
theorem totalisationGuard_changeShiftDenominatorPositive
    (A : SemiboundedSymmetricOperator H) (shift₁ : ℝ)
    (hshift₁ : 0 < A.lowerBound + shift₁) :
    0 < A.lowerBound + shift₁ :=
  hshift₁

/-- The radicand in the change-of-shift comparison constant is nonnegative. -/
theorem totalisationGuard_changeShiftRadicandNonnegative
    (A : SemiboundedSymmetricOperator H) (shift₁ shift₂ : ℝ)
    (hshift₁ : 0 < A.lowerBound + shift₁) :
    0 ≤ 1 + |shift₂ - shift₁| / (A.lowerBound + shift₁) := by
  exact add_nonneg zero_le_one (div_nonneg (abs_nonneg _) hshift₁.le)

end SemiboundedSymmetricOperator
end FriedrichsExtension
