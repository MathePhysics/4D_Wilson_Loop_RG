/-
`lem:boundary-covariance`(i) of BALABAN_CORE.tex (`a021c13be348`), the algebra of its proof in abstract form. At a
bond `b` of `𝖲` the boundary field is `𝐇(𝐔)(b) = Ad_{τ_{b₋}(𝐔)}⁻¹ (1/i)log(M^n(𝐔)(b)V^{(n)}_𝖸(𝐔)(b)⁻¹)`
(`eq:covariant-boundary-field`). Under a gauge transformation `w` with the induced `ŵ`, the inputs of the proof are:
`M^n(𝐔^w)(b) = ŵ(b₋)M^n(𝐔)(b)ŵ(b₊)⁻¹` (`lem:average`(iii)), `V^{(n)}_𝖸(𝐔^w)(b) = ŵ(b₋)V^{(n)}_𝖸(𝐔)(b)ŵ(b₊)⁻¹`
(`lem:problem-covariance` and the uniqueness in the axial gauge), `τ_x(𝐔^w) = ŵ(x)τ_x(𝐔)w(x)⁻¹`
(`lem:chain-transport`(i)), and `log(gWg⁻¹) = Ad_g log W`. Then `𝐇(𝐔^w)(b) = Ad_{w(b₋)}𝐇(𝐔)(b)`
(`boundary_covariance`). The adjoint action is a `MulAction` of the group on the Lie algebra.
-/
import Mathlib

noncomputable section

namespace CoreLean
namespace BoundaryCov

variable {G A : Type*} [Group G] [MulAction G A]

/-- The boundary field at a bond: `Ad_τ⁻¹ log(MV⁻¹)`. -/
def Hfield (log : G → A) (τ M V : G) : A := τ⁻¹ • log (M * V⁻¹)

/-- **`lem:boundary-covariance`(i)**: `𝐇(𝐔^w)(b) = Ad_{w(b₋)}𝐇(𝐔)(b)`. -/
theorem boundary_covariance (log : G → A) (hlog : ∀ g W, log (g * W * g⁻¹) = g • log W)
    {τ M V τ' M' V' w ŵ ŵ' : G} (hM : M' = ŵ * M * ŵ'⁻¹) (hV : V' = ŵ * V * ŵ'⁻¹)
    (hτ : τ' = ŵ * τ * w⁻¹) : Hfield log τ' M' V' = w • Hfield log τ M V := by
  unfold Hfield
  have e1 : M' * V'⁻¹ = ŵ * (M * V⁻¹) * ŵ⁻¹ := by
    rw [hM, hV]; group
  rw [e1, hlog, hτ, smul_smul, smul_smul]
  congr 1
  group

end BoundaryCov
end CoreLean

end
