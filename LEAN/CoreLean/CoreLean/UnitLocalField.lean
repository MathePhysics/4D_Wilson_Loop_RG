/-
`lem:unit-local-field` of BALABAN_CORE.tex (`a021c13be348`), the last step of its proof, with the function `Ψ` of
`lem:product` (`Psi.lean`, `C_Ψ = 256`).

* `‖Ψ(Y, Y')‖ ≤ ‖Y‖ + ‖Y'‖ + C_Ψ‖Y‖‖Y'‖ ≤ 2(‖Y‖ + ‖Y'‖)` for `‖Y‖, ‖Y'‖ ≤ 1/32` and `C_Ψ‖Y‖ ≤ 1` (`psi_norm_le`), from
  `eq:product-lipschitz` at `(0, 0)`.
* With `‖ζ(c_±)‖ ≤ C'₂α₁`, `‖X_n(c)‖ ≤ 2α₁` and `2^{10}(C'₂ + 1)α₁ ≤ 1`, the exponent
  `X(c) = Ψ(Ψ(ζ(c₋), X_n(c)), -Ad_{V(c)}ζ(c₊))` satisfies `‖X(c)‖ ≤ (6C'₂ + 8)α₁ = C_avα₁` (`average_exponent`), the
  adjoint action of the unitary `V(c)` preserving the norm (here: any `Z` with `‖Z‖ ≤ C'₂α₁` in its place).
-/
import CoreLean.Psi

open Matrix NormedSpace
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean
namespace UnitLocalField

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ

/-- `‖Ψ(Y, Y')‖ ≤ 2(‖Y‖ + ‖Y'‖)` for `256‖Y‖ ≤ 1`. -/
theorem psi_norm_le {Y Y' : Mat} (hY : ‖Y‖ ≤ 1 / 32) (hY' : ‖Y'‖ ≤ 1 / 32) (hC : 256 * ‖Y‖ ≤ 1) :
    ‖psi Y Y'‖ ≤ 2 * (‖Y‖ + ‖Y'‖) := by
  have h0 : ‖(0 : Mat)‖ ≤ 1 / 32 := by simp
  have h := psi_lipschitz h0 h0 hY hY'
  have hpsi0 : psi (0 : Mat) 0 = 0 := psi_zero_left (by simp)
  rw [hpsi0, sub_zero, sub_zero, sub_zero, norm_zero, zero_mul, add_zero] at h
  have h1 : ‖psi Y Y'‖ ≤ ‖Y‖ + ‖Y'‖ + 256 * (‖Y'‖ * ‖Y‖) := by
    have := norm_add_le (psi Y Y' - Y - Y') (Y + Y')
    rw [show psi Y Y' - Y - Y' + (Y + Y') = psi Y Y' by abel] at this
    linarith [norm_add_le Y Y']
  have h2 : 256 * (‖Y'‖ * ‖Y‖) ≤ ‖Y'‖ := by
    have := mul_le_mul_of_nonneg_left hC (norm_nonneg Y')
    nlinarith
  nlinarith [norm_nonneg Y, norm_nonneg Y']

/-- **The exponent of the average**: `‖X(c)‖ ≤ (6C'₂ + 8)α₁`. -/
theorem average_exponent {ζm Xn Z : Mat} {C α₁ : ℝ} (hC : 0 ≤ C) (hα : 0 ≤ α₁)
    (hsmall : 2 ^ 10 * (C + 1) * α₁ ≤ 1) (hζ : ‖ζm‖ ≤ C * α₁) (hX : ‖Xn‖ ≤ 2 * α₁) (hZ : ‖Z‖ ≤ C * α₁) :
    ‖psi (psi ζm Xn) Z‖ ≤ (6 * C + 8) * α₁ := by
  have hCa : (C + 1) * α₁ ≤ 1 / 2 ^ 10 := by
    rw [le_div_iff₀ (by norm_num)]; linarith
  have hCα : C * α₁ ≤ 1 / 2 ^ 10 := by nlinarith
  have hα1 : α₁ ≤ 1 / 2 ^ 10 := by nlinarith
  have hζ' : ‖ζm‖ ≤ 1 / 32 := by linarith [hζ.trans hCα]
  have hX' : ‖Xn‖ ≤ 1 / 32 := by linarith [hX]
  have hZ' : ‖Z‖ ≤ 1 / 32 := by linarith [hZ.trans hCα]
  have h1 := psi_norm_le hζ' hX' (by nlinarith [hζ.trans hCα])
  have hP : ‖psi ζm Xn‖ ≤ 2 * (C + 2) * α₁ := by nlinarith
  have hP' : ‖psi ζm Xn‖ ≤ 1 / 256 := by
    have : 2 * (C + 2) * α₁ ≤ 4 * ((C + 1) * α₁) := by nlinarith
    calc ‖psi ζm Xn‖ ≤ 2 * (C + 2) * α₁ := hP
      _ ≤ 4 * ((C + 1) * α₁) := this
      _ ≤ 4 * (1 / 2 ^ 10) := by gcongr
      _ = 1 / 256 := by norm_num
  have h2 := psi_norm_le (Y := psi ζm Xn) (Y' := Z) (by linarith) hZ' (by linarith)
  calc ‖psi (psi ζm Xn) Z‖ ≤ 2 * (‖psi ζm Xn‖ + ‖Z‖) := h2
    _ ≤ 2 * (2 * (C + 2) * α₁ + C * α₁) := by gcongr
    _ = (6 * C + 8) * α₁ := by ring

/-- `lem:unit-objects`, the condition of `lem:unit-maps`: `20α + ‖X‖_∞ ≤ (20 + C_av)(α + α₁) ≤ c_um`. -/
theorem objects_condition {α α₁ nX Cav cum : ℝ} (hα : 0 ≤ α) (hα₁ : 0 ≤ α₁) (hCav : 0 ≤ Cav)
    (hX : nX ≤ Cav * α₁) (hcond : (20 + Cav) * (α + α₁) ≤ cum) : 20 * α + nX ≤ cum := by
  nlinarith

end UnitLocalField
end CoreLean

end
