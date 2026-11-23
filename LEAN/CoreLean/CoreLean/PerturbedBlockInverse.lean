/-
`lem:perturbed-block-inverse` of BALABAN_CORE.tex (`a021c13be348`), the algebra and the constant of its proof.

* In a ring: if `Y` has the two-sided inverse `Y⁻¹` and `I + 𝒵Y⁻¹` has the two-sided inverse `V`, then
  `Y + 𝒵 = (I + 𝒵Y⁻¹)Y` is invertible with `(Y + 𝒵)⁻¹ = Y⁻¹ + Y⁻¹(V - I)` (`perturbed_inverse`).
* The constant of the union of the families: `C_inv + 2c₁N''C_invθ_{ZY} ≤ C_inv(1 + c₁)` for `N''θ_{ZY} ≤ ½`
  (`perturbed_constant`).
-/
import Mathlib

noncomputable section

namespace CoreLean
namespace PerturbedBlockInverse

variable {R : Type*} [Ring R]

/-- **The inverse of `Y + 𝒵`**. -/
theorem perturbed_inverse (Y Z Yinv V : R) (hY1 : Y * Yinv = 1) (hY2 : Yinv * Y = 1)
    (hV1 : (1 + Z * Yinv) * V = 1) (hV2 : V * (1 + Z * Yinv) = 1) :
    (Y + Z) * (Yinv + Yinv * (V - 1)) = 1 ∧ (Yinv + Yinv * (V - 1)) * (Y + Z) = 1 := by
  have hfac : Y + Z = (1 + Z * Yinv) * Y := by rw [add_mul, one_mul, mul_assoc, hY2, mul_one]
  have hsimp : Yinv + Yinv * (V - 1) = Yinv * V := by rw [mul_sub, mul_one]; abel
  rw [hsimp, hfac]
  constructor
  · calc (1 + Z * Yinv) * Y * (Yinv * V) = (1 + Z * Yinv) * (Y * Yinv) * V := by simp only [mul_assoc]
      _ = 1 := by rw [hY1, mul_one, hV1]
  · calc Yinv * V * ((1 + Z * Yinv) * Y) = Yinv * (V * (1 + Z * Yinv)) * Y := by simp only [mul_assoc]
      _ = 1 := by rw [hV2, mul_one, hY2]

/-- **The constant**. -/
theorem perturbed_constant {Cinv c1 N θ : ℝ} (hC : 0 ≤ Cinv) (hc : 0 ≤ c1) (hNθ : N * θ ≤ 1 / 2) :
    Cinv + 2 * c1 * N * Cinv * θ ≤ Cinv * (1 + c1) := by
  have : 2 * c1 * N * Cinv * θ = 2 * c1 * Cinv * (N * θ) := by ring
  rw [this]
  have h := mul_le_mul_of_nonneg_left hNθ (by positivity : 0 ≤ 2 * c1 * Cinv)
  nlinarith

/-- `cor:landau-block-inverse`(ii): `QG_πQ^* = QGQ^* + Q(G_π - G)Q^*`, so that `lem:perturbed-block-inverse` with
`Y = QGQ^*` and `𝒵 = Q(G_π - G)Q^*` inverts `QG_πQ^*` (`landau_block_inverse`). -/
theorem landau_block_inverse (Q G Gπ Qs Yinv V : R) (hY1 : (Q * G * Qs) * Yinv = 1) (hY2 : Yinv * (Q * G * Qs) = 1)
    (hV1 : (1 + Q * (Gπ - G) * Qs * Yinv) * V = 1) (hV2 : V * (1 + Q * (Gπ - G) * Qs * Yinv) = 1) :
    (Q * Gπ * Qs) * (Yinv + Yinv * (V - 1)) = 1 ∧ (Yinv + Yinv * (V - 1)) * (Q * Gπ * Qs) = 1 := by
  have e : Q * Gπ * Qs = Q * G * Qs + Q * (Gπ - G) * Qs := by
    rw [mul_sub, sub_mul, add_sub_cancel]
  rw [e]
  exact perturbed_inverse _ _ _ _ hY1 hY2 hV1 hV2

end PerturbedBlockInverse
end CoreLean

end
