import Mathlib.Algebra.Module.Submodule.LinearMap

/-!
# Domain-explicit partial maps

The safest representation of a genuinely partial mathematical operation is usually not a total
function with a fallback value, but a function whose input contains a proof of domain membership.
This file provides lightweight generic versions, including a linear-map form useful for unbounded
operators.
-/

namespace TotalisationSafety

/-- A function defined only on an explicit set. -/
structure PartialMap (α β : Type*) where
  domain : Set α
  toFun : {x : α // x ∈ domain} → β

namespace PartialMap

variable {α β : Type*}

/-- Apply a partial map after supplying a proof that the argument lies in its domain. -/
def apply (f : PartialMap α β) (x : α) (hx : x ∈ f.domain) : β :=
  f.toFun ⟨x, hx⟩

end PartialMap

/-- A linear map defined on an explicit submodule of its ambient domain. -/
structure PartialLinearMap
    (R : Type*) (M : Type*) (N : Type*)
    [Semiring R] [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] where
  domain : Submodule R M
  toLinearMap : domain →ₗ[R] N

namespace PartialLinearMap

variable {R M N : Type*}
variable [Semiring R] [AddCommMonoid M] [Module R M]
variable [AddCommMonoid N] [Module R N]

/-- Apply a partial linear map after supplying domain membership. -/
def apply (f : PartialLinearMap R M N) (x : M) (hx : x ∈ f.domain) : N :=
  f.toLinearMap ⟨x, hx⟩

end PartialLinearMap

end TotalisationSafety
