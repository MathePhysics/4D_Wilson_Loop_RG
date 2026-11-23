/-
`prop:second-operators` of BALABAN_CORE.tex (`a021c13be348`), the holomorphy step of its proof in abstract form:
"the inverse of a holomorphic family of invertible operators on a space of finite dimension is holomorphic". For
families `G_c(x)` of operators on `V`, `Q(x) : V → W` and `Q^*(x) : W → V`, holomorphic in the parameter `x` on a set,
with `Q G_c Q^*` invertible there, the operator `H₀ = G_cQ^*(QG_cQ^*)⁻¹` is holomorphic (`H0_holomorphic`), from
`DifferentiableOn.inverse` (Mathlib) and the holomorphy of compositions. The series `G_c = Σ_n(GΔ^{(2)})^nG` is
`LandauNeumann.lean` (`series_right_inverse`, `series_left_inverse`, `series_bound`).
-/
import Mathlib

noncomputable section

namespace CoreLean
namespace SecondOperators

variable {E V W : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup V] [NormedSpace ℂ V]
  [CompleteSpace V] [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]

/-- The inverse of a holomorphic family of invertible operators is holomorphic. -/
theorem inverse_holomorphic {S : Set E} (A : E → W →L[ℂ] W) (hA : DifferentiableOn ℂ A S)
    (hu : ∀ x ∈ S, IsUnit (A x)) : DifferentiableOn ℂ (fun x => Ring.inverse (A x)) S :=
  hA.inverse hu

/-- **`H₀ = G_cQ^*(QG_cQ^*)⁻¹` is holomorphic**. -/
theorem H0_holomorphic {S : Set E} (Gc : E → V →L[ℂ] V) (Q : E → V →L[ℂ] W) (Qs : E → W →L[ℂ] V)
    (hG : DifferentiableOn ℂ Gc S) (hQ : DifferentiableOn ℂ Q S) (hQs : DifferentiableOn ℂ Qs S)
    (hu : ∀ x ∈ S, IsUnit ((Q x).comp ((Gc x).comp (Qs x)))) :
    DifferentiableOn ℂ (fun x => (Gc x).comp ((Qs x).comp (Ring.inverse ((Q x).comp ((Gc x).comp (Qs x)))))) S := by
  have hM : DifferentiableOn ℂ (fun x => (Q x).comp ((Gc x).comp (Qs x))) S :=
    hQ.clm_comp (hG.clm_comp hQs)
  exact hG.clm_comp (hQs.clm_comp (hM.inverse hu))

end SecondOperators
end CoreLean

end
