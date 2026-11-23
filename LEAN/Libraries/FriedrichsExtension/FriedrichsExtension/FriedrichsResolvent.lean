import FriedrichsExtension.EnergySpace
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

open scoped InnerProductSpace

noncomputable section

namespace FriedrichsExtension
namespace SemiboundedSymmetricOperator

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (A : SemiboundedSymmetricOperator H) (shift : ℝ)
    (hshift : 0 < A.lowerBound + shift)

/-- The shifted operator value `(A + shift)u` on the original operator domain. -/
def shiftedOperatorValue (u : A.op.domain) : H :=
  A.op u + shift • (u : H)

/--
The adjoint of the energy embedding recovers a core vector from its shifted operator value:
`J* ((A + shift)u) = u` in the completed energy space.
-/
theorem energyEmbedding_adjoint_shiftedOperatorValue (u : A.op.domain) :
    (A.energyEmbedding shift hshift).adjoint (A.shiftedOperatorValue shift u) =
      ((⟨u⟩ : EnergyDomain A shift hshift) : EnergySpace A shift hshift) := by
  let J := A.energyEmbedding shift hshift
  refine UniformSpace.Completion.denseRange_coe.eq_of_inner_left ℝ fun v ↦ ?_
  rw [ContinuousLinearMap.adjoint_inner_left]
  rw [A.energyEmbedding_coe shift hshift]
  rw [UniformSpace.Completion.inner_coe]
  rw [EnergyDomain.inner_eq_shiftedForm]
  simp only [shiftedOperatorValue, shiftedForm, operatorForm, inner_add_left,
    real_inner_smul_left]

/-- The completed energy embedding is injective: the shifted operator form is closable. -/
theorem energyEmbedding_injective :
    Function.Injective (A.energyEmbedding shift hshift) := by
  let J := A.energyEmbedding shift hshift
  intro x y hxy
  refine UniformSpace.Completion.denseRange_coe.eq_of_inner_left ℝ fun u ↦ ?_
  let z : H := A.shiftedOperatorValue shift u.toDomain
  have hu : J.adjoint z = (u : EnergySpace A shift hshift) := by
    simpa [J, z] using A.energyEmbedding_adjoint_shiftedOperatorValue shift hshift u.toDomain
  calc
    inner ℝ x (u : EnergySpace A shift hshift) = inner ℝ x (J.adjoint z) := by rw [hu]
    _ = inner ℝ (J x) z := ContinuousLinearMap.adjoint_inner_right J x z
    _ = inner ℝ (J y) z := by rw [hxy]
    _ = inner ℝ y (J.adjoint z) := (ContinuousLinearMap.adjoint_inner_right J y z).symm
    _ = inner ℝ y (u : EnergySpace A shift hshift) := by rw [hu]

/--
The bounded Friedrichs resolvent candidate

`R_shift = J J*`,

where `J : EnergySpace A shift hshift → H` is the completed energy embedding.
-/
def friedrichsResolvent : H →L[ℝ] H :=
  (A.energyEmbedding shift hshift).comp (A.energyEmbedding shift hshift).adjoint

/-- The resolvent is a left inverse of the shifted operator on the original core. -/
theorem friedrichsResolvent_shiftedOperatorValue (u : A.op.domain) :
    A.friedrichsResolvent shift hshift (A.shiftedOperatorValue shift u) = (u : H) := by
  simp [friedrichsResolvent, A.energyEmbedding_adjoint_shiftedOperatorValue shift hshift,
    A.energyEmbedding_coe shift hshift]

/-- The Friedrichs resolvent candidate is positive. -/
theorem friedrichsResolvent_isPositive :
    (A.friedrichsResolvent shift hshift).IsPositive := by
  let J := A.energyEmbedding shift hshift
  have h := ContinuousLinearMap.isPositive_adjoint_comp_self J.adjoint
  simpa [friedrichsResolvent, J] using h

/-- In particular the Friedrichs resolvent candidate is self-adjoint. -/
theorem friedrichsResolvent_isSelfAdjoint :
    IsSelfAdjoint (A.friedrichsResolvent shift hshift) :=
  (A.friedrichsResolvent_isPositive shift hshift).isSelfAdjoint

/-- Dense range of `J` forces its adjoint to be injective. -/
theorem energyEmbedding_adjoint_injective :
    Function.Injective (A.energyEmbedding shift hshift).adjoint := by
  let J := A.energyEmbedding shift hshift
  intro x y hxy
  have hker : J.adjoint (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have horth : x - y ∈ J.rangeᗮ := by
    rw [J.orthogonal_range, LinearMap.mem_ker]
    exact hker
  exact sub_eq_zero.mp
    ((A.energyEmbedding_range_dense shift hshift).eq_zero_of_mem_orthogonal horth)

/-- The bounded Friedrichs resolvent candidate is injective. -/
theorem friedrichsResolvent_injective :
    Function.Injective (A.friedrichsResolvent shift hshift) := by
  intro x y hxy
  have hadj :
      (A.energyEmbedding shift hshift).adjoint x =
        (A.energyEmbedding shift hshift).adjoint y :=
    A.energyEmbedding_injective shift hshift (by
      simpa [friedrichsResolvent] using hxy)
  exact A.energyEmbedding_adjoint_injective shift hshift hadj

/-- The range of the injective self-adjoint resolvent is dense. -/
theorem friedrichsResolvent_range_dense :
    Dense ((A.friedrichsResolvent shift hshift).range : Set H) := by
  let R := A.friedrichsResolvent shift hshift
  have hker : R.ker = ⊥ :=
    LinearMap.ker_eq_bot.mpr (A.friedrichsResolvent_injective shift hshift)
  have hadj : R.adjoint = R :=
    (A.friedrichsResolvent_isPositive shift hshift).isSymmetric.clm_adjoint_eq
  have horth : R.rangeᗮ = ⊥ := by
    rw [R.orthogonal_range, hadj]
    exact hker
  have hclosure : R.range.topologicalClosure = ⊤ :=
    R.range.topologicalClosure_eq_top_iff.mpr horth
  rw [dense_iff_closure_eq]
  have hclosure_coe := congrArg (fun K : Submodule ℝ H => (K : Set H)) hclosure
  simpa [Submodule.topologicalClosure_coe] using hclosure_coe

end SemiboundedSymmetricOperator
end FriedrichsExtension
