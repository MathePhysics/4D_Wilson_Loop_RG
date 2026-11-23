import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Basic.ENNReal.Real

/-!
# Basic guarded values

Small proof-carrying wrappers for operations whose ambient Lean/mathlib versions are total.
The point is not to change Lean's kernel semantics.  Rather, mathematical code can make the
intended domain an explicit part of the input type.
-/

namespace TotalisationSafety

/-- An element supplied together with a proof that it is nonzero. -/
structure NonzeroElement (α : Type*) [Zero α] where
  val : α
  ne_zero : val ≠ 0

namespace NonzeroElement

variable {α : Type*} [Zero α]

instance : Coe (NonzeroElement α) α := ⟨NonzeroElement.val⟩

/-- Inversion whose input type rules out the totalised zero branch. -/
def inv [Inv α] (x : NonzeroElement α) : α := x.val⁻¹

/-- Division whose denominator carries an explicit nonzero proof.

This works for structures such as `Nat` as well as fields: no algebraic cancellation theorem is
asserted unless the ambient type supplies one separately.
-/
def div [Div α] (x : α) (y : NonzeroElement α) : α := x / y.val -- totalisation-audit: allow denominator carries ne_zero

end NonzeroElement

/-- A strictly positive real number, used as the domain of operations such as the analytic
logarithm when the negative/zero extensions of `Real.log` are not mathematically intended. -/
structure PositiveReal where
  val : ℝ
  positive : 0 < val

namespace PositiveReal

instance : Coe PositiveReal ℝ := ⟨PositiveReal.val⟩

/-- Real logarithm restricted to the mathematically intended positive domain. -/
noncomputable def log (x : PositiveReal) : ℝ := Real.log x.val -- totalisation-audit: allow PositiveReal carries 0 < val

end PositiveReal

/-- A finite extended nonnegative real.  Calling `toReal` on this type cannot silently take the
`⊤ ↦ 0` branch of `ENNReal.toReal`. -/
structure FiniteENNReal where
  val : ENNReal
  ne_top : val ≠ ⊤

namespace FiniteENNReal

instance : Coe FiniteENNReal ENNReal := ⟨FiniteENNReal.val⟩

/-- Conversion to `ℝ` with finiteness carried by the input object. -/
def toReal (x : FiniteENNReal) : ℝ := x.val.toReal -- totalisation-audit: allow FiniteENNReal carries ne_top

end FiniteENNReal

end TotalisationSafety
