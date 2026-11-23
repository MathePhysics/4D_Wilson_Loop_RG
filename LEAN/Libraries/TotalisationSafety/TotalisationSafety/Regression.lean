import TotalisationSafety.Basic
import Mathlib.Data.Nat.Basic

/-!
# Regression examples: dangerous ambient totalisations

This file is deliberately not imported by `TotalisationSafety.lean`.  It records small examples of
ambient Lean/mathlib expressions that are mathematically out of domain but still receive values.
They are useful when checking that a project is using the guarded API for semantic reasons rather
than because the underlying totalised operations disappeared.
-/

namespace TotalisationSafety.Regression

/-- Division on naturals is total: division by zero returns zero. -/
example : (1 / 0 : Nat) = 0 := by decide

/-- Inversion in a group-with-zero is total at zero. -/
example : (0 : ℝ)⁻¹ = 0 := by simp

/-- `ENNReal.toReal` sends `⊤` to zero. -/
example : (⊤ : ENNReal).toReal = 0 := by simp

/-- The real logarithm is totalised at zero. -/
example : Real.log 0 = 0 := by simp

end TotalisationSafety.Regression
