import FriedrichsExtension.FunctionalAnalysisInventory

open scoped InnerProductSpace

noncomputable section

namespace FriedrichsExtension

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/--
A densely defined symmetric operator together with a specified lower bound.

The inequality is written directly on the `LinearPMap` domain.  For the heat-kernel
application one will typically have a nonnegative operator, so `lowerBound = 0`.
-/
structure SemiboundedSymmetricOperator where
  op : H →ₗ.[ℝ] H
  dense_domain : Dense (op.domain : Set H)
  symmetric : op.IsFormalAdjoint op
  lowerBound : ℝ
  lower_bound : ∀ u : op.domain,
    lowerBound * ‖(u : H)‖ ^ 2 ≤ inner ℝ (op u) (u : H)

namespace SemiboundedSymmetricOperator

variable {H}

/-- The algebraic form associated with the operator. -/
def operatorForm (A : SemiboundedSymmetricOperator H) (u v : A.op.domain) : ℝ :=
  inner ℝ (A.op u) (v : H)

/-- Symmetry of the operator form. -/
theorem operatorForm_symm (A : SemiboundedSymmetricOperator H) (u v : A.op.domain) :
    A.operatorForm u v = A.operatorForm v u := by
  calc
    inner ℝ (A.op u) (v : H) = inner ℝ (u : H) (A.op v) := A.symmetric u v
    _ = inner ℝ (A.op v) (u : H) := real_inner_comm _ _

/--
The shifted form used in the Friedrichs construction.

For `shift > -A.lowerBound` this is positive definite on the operator domain.
-/
def shiftedForm (A : SemiboundedSymmetricOperator H) (shift : ℝ)
    (u v : A.op.domain) : ℝ :=
  A.operatorForm u v + shift * inner ℝ (u : H) (v : H)

/-- Symmetry of the shifted form. -/
theorem shiftedForm_symm (A : SemiboundedSymmetricOperator H) (shift : ℝ)
    (u v : A.op.domain) :
    A.shiftedForm shift u v = A.shiftedForm shift v u := by
  rw [shiftedForm, shiftedForm, A.operatorForm_symm u v, real_inner_comm (u : H) (v : H)]

/-- The quadratic energy associated with the shifted form. -/
def shiftedEnergy (A : SemiboundedSymmetricOperator H) (shift : ℝ)
    (u : A.op.domain) : ℝ :=
  A.shiftedForm shift u u

/-- The semiboundedness estimate becomes coercivity after a sufficiently large shift. -/
theorem shiftedEnergy_lower (A : SemiboundedSymmetricOperator H) (shift : ℝ)
    (u : A.op.domain) :
    (A.lowerBound + shift) * ‖(u : H)‖ ^ 2 ≤ A.shiftedEnergy shift u := by
  calc
    (A.lowerBound + shift) * ‖(u : H)‖ ^ 2 =
        A.lowerBound * ‖(u : H)‖ ^ 2 + shift * ‖(u : H)‖ ^ 2 := by ring
    _ ≤ inner ℝ (A.op u) (u : H) + shift * ‖(u : H)‖ ^ 2 :=
      add_le_add (A.lower_bound u) le_rfl
    _ = A.shiftedEnergy shift u := by
      rw [shiftedEnergy, shiftedForm, operatorForm, real_inner_self_eq_norm_sq]

/-- A strictly positive shift makes the shifted energy positive on nonzero domain vectors. -/
theorem shiftedEnergy_pos (A : SemiboundedSymmetricOperator H) {shift : ℝ}
    (hshift : 0 < A.lowerBound + shift) {u : A.op.domain} (hu : u ≠ 0) :
    0 < A.shiftedEnergy shift u := by
  have hcoe : (u : H) ≠ 0 := by
    intro h
    apply hu
    exact Subtype.ext h
  have hnorm : 0 < ‖(u : H)‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hcoe)
  exact lt_of_lt_of_le (mul_pos hshift hnorm) (A.shiftedEnergy_lower shift u)

end SemiboundedSymmetricOperator

end FriedrichsExtension
