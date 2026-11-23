import FriedrichsExtension.SemiboundedOperator

open scoped InnerProductSpace

noncomputable section

namespace FriedrichsExtension
namespace SemiboundedSymmetricOperator

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Additivity of the shifted form in its first variable. -/
theorem shiftedForm_add_left (A : SemiboundedSymmetricOperator H) (shift : ℝ)
    (u v w : A.op.domain) :
    A.shiftedForm shift (u + v) w =
      A.shiftedForm shift u w + A.shiftedForm shift v w := by
  simp only [shiftedForm, operatorForm, A.op.map_add, Submodule.coe_add, inner_add_left]
  ring

/-- Real homogeneity of the shifted form in its first variable. -/
theorem shiftedForm_smul_left (A : SemiboundedSymmetricOperator H) (shift c : ℝ)
    (u v : A.op.domain) :
    A.shiftedForm shift (c • u) v = c * A.shiftedForm shift u v := by
  simp only [shiftedForm, operatorForm, A.op.map_smul, Submodule.coe_smul,
    real_inner_smul_left]
  ring

/--
The positive-definite core associated with the shifted energy scalar product.

This does **not** install a second norm on `A.op.domain`; it is kept as explicit data.  A later file
will transport this core to a dedicated copy of the operator domain before invoking
`InnerProductSpace.Core.toNormedAddCommGroup`.
-/
@[instance_reducible]
def shiftedEnergyCore (A : SemiboundedSymmetricOperator H) (shift : ℝ)
    (hshift : 0 < A.lowerBound + shift) : InnerProductSpace.Core ℝ A.op.domain where
  inner := A.shiftedForm shift
  conj_inner_symm u v := by
    simpa using (A.shiftedForm_symm shift v u)
  re_inner_nonneg u := by
    have hlow := A.shiftedEnergy_lower shift u
    have hnonneg : 0 ≤ (A.lowerBound + shift) * ‖(u : H)‖ ^ 2 :=
      mul_nonneg hshift.le (sq_nonneg _)
    have : 0 ≤ A.shiftedEnergy shift u := hnonneg.trans hlow
    simpa [shiftedEnergy] using this
  add_left u v w := A.shiftedForm_add_left shift u v w
  smul_left u v c := by
    simpa using A.shiftedForm_smul_left shift c u v
  definite u hu := by
    by_contra hne
    have hpos := A.shiftedEnergy_pos hshift hne
    rw [shiftedEnergy, hu] at hpos
    exact (lt_irrefl 0) hpos

end SemiboundedSymmetricOperator
end FriedrichsExtension
