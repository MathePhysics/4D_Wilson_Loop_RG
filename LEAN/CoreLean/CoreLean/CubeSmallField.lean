/-
`lem:cube-small-field`(i) of BALABAN_CORE.tex (`bf6b2bc552ba`), at one site and one pair of directions.

On a bond `b` the transformed configuration is `U^v(b) = e^{iηÃ(b)} e^{iηA(b)}`, `Ã(b) = Ad_{v(b_-)} A''(b)`,
and `B(b) = η⁻¹ Ψ(ηÃ(b), ηA(b))`. From `eq:product-lipschitz` with `C_Ψ = 256` (`psi_lipschitz`) the
map `Ψ` is Lipschitz with the constant `1 + C_Ψ/32 = 9` on the matrices of norm at most `1/32`
(`psi_lip9`), so that `‖Ψ(X', Y')‖ ≤ 9‖X'‖ + ‖Y'‖`. The differences of `Ã` at the trivial gauge field are
those of `A''` at `U`, transformed, up to the commutator `η⁻¹(Ad_{e^{iηA}} - 1)Ã` (`transported_difference`),
which `eq:adjoint-lipschitz` bounds by `6‖A‖‖A''‖`. Together (`cube_small_field_i`):
`e^{iηB} = e^{iηÃ}e^{iηA}`, `a_j‖B‖ ≤ 9(α + α₁)`, and `a_j²‖∂_μ B‖ ≤ 18(α + α₁)`.

The statement is made for the values of the forms at the two bonds `b = (z, z + e_ν)` and
`b' = (z + e_μ, z + e_μ + e_ν)` which form one difference, with the bounds `eq:cube-setting` at `z` as
hypotheses; the norm is the operator norm, and `v(z)`, `v(z + e_μ)` are unitary.
-/
import CoreLean.Psi
import CoreLean.SupportContinuation

open NormedSpace
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean
namespace CubeSmallField

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

/-- `Ψ` is Lipschitz with the constant `1 + C_Ψ/32 = 9` on the matrices of norm at most `1/32`. -/
theorem psi_lip9 {X Y X' Y' : Mat} (hX : ‖X‖ ≤ 1 / 32) (hY : ‖Y‖ ≤ 1 / 32)
    (hX' : ‖X'‖ ≤ 1 / 32) (hY' : ‖Y'‖ ≤ 1 / 32) :
    ‖psi X' Y' - psi X Y‖ ≤ 9 * (‖X' - X‖ + ‖Y' - Y‖) := by
  have h := psi_lipschitz hX hY hX' hY'
  have e : psi X' Y' - psi X Y =
      (psi X' Y' - psi X Y - (X' - X) - (Y' - Y)) + (X' - X) + (Y' - Y) := by abel
  have h1 := norm_nonneg (X' - X)
  have h2 := norm_nonneg (Y' - Y)
  calc ‖psi X' Y' - psi X Y‖ ≤ ‖psi X' Y' - psi X Y - (X' - X) - (Y' - Y)‖ + ‖X' - X‖ + ‖Y' - Y‖ := by
        conv_lhs => rw [e]
        exact norm_add₃_le
    _ ≤ 256 * (‖Y'‖ * ‖X' - X‖ + ‖X‖ * ‖Y' - Y‖) + ‖X' - X‖ + ‖Y' - Y‖ := by gcongr
    _ ≤ 256 * (1 / 32 * ‖X' - X‖ + 1 / 32 * ‖Y' - Y‖) + ‖X' - X‖ + ‖Y' - Y‖ := by gcongr
    _ = 9 * (‖X' - X‖ + ‖Y' - Y‖) := by ring

/-- `‖Ψ(X', Y')‖ ≤ 9‖X'‖ + ‖Y'‖` on the matrices of norm at most `1/32`. -/
theorem norm_psi_le9 {X' Y' : Mat} (hX' : ‖X'‖ ≤ 1 / 32) (hY' : ‖Y'‖ ≤ 1 / 32) :
    ‖psi X' Y'‖ ≤ 9 * ‖X'‖ + ‖Y'‖ := by
  have h := psi_lipschitz (X := 0) (Y := Y') (by simp) hY' hX' hY'
  rw [psi_zero_left (by linarith)] at h
  simp only [sub_zero, sub_self, norm_zero, mul_zero, add_zero] at h
  have e : psi X' Y' = (psi X' Y' - Y' - X') + X' + Y' := by abel
  calc ‖psi X' Y'‖ ≤ ‖psi X' Y' - Y' - X'‖ + ‖X'‖ + ‖Y'‖ := by
        conv_lhs => rw [e]
        exact norm_add₃_le
    _ ≤ 256 * (‖Y'‖ * ‖X'‖) + ‖X'‖ + ‖Y'‖ := by gcongr
    _ ≤ 256 * (1 / 32 * ‖X'‖) + ‖X'‖ + ‖Y'‖ := by gcongr
    _ = 9 * ‖X'‖ + ‖Y'‖ := by ring

/-- The transported difference: if `v U v'⁻¹ = E`, then
`Ad_v(Ad_U X - Y) = (Ad_{v'} X - Ad_v Y) + (Ad_E - 1)(Ad_{v'} X)`. -/
theorem transported_difference (v v' U E : GLN) (hE : v * U * v'⁻¹ = E) (X Y : Mat) :
    Ad v (Ad U X - Y) = (Ad v' X - Ad v Y) + (Ad E (Ad v' X) - Ad v' X) := by
  rw [Ad_sub, ← hE, Ad_gauge]
  abel

lemma norm_real_smul (η : ℝ) (hη : 0 ≤ η) (X : Mat) : ‖(η : ℂ) • X‖ = η * ‖X‖ := by
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hη]

lemma norm_inv_real_smul (η : ℝ) (hη : 0 < η) (X : Mat) : ‖(η : ℂ)⁻¹ • X‖ = η⁻¹ * ‖X‖ := by
  rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hη.le]

/-- `lem:cube-small-field`(i) at one site and one pair of directions. Here `v₀ = v(z)`,
`v₁ = v(z + e_μ)` are unitary, `U₀ = U(z, z + e_μ)` with `v₀U₀v₁⁻¹ = e^{iηA_μ(z)}`, `X₀ = A''_ν(z)`,
`X₁ = A''_ν(z + e_μ)`, `Y₀ = A_ν(z)`, `Y₁ = A_ν(z + e_μ)`, and `B_i = η⁻¹Ψ(ηAd_{v_i}X_i, ηY_i)` are the
values of `B` at the bonds `b` and `b'`. From `eq:cube-setting` with `α + α₁ ≤ 1/32` and `η ≤ a_j`:
`e^{iηB₀} = e^{iηÃ₀}e^{iηY₀}`, `a_j‖B₀‖ ≤ 9(α + α₁)`, and `a_j²‖η⁻¹(B₁ - B₀)‖ ≤ 18(α + α₁)`. -/
theorem cube_small_field_i (η a α α₁ : ℝ) (hη : 0 < η) (hηa : η ≤ a) (hα : 0 ≤ α) (hα₁ : 0 ≤ α₁)
    (hsum : α + α₁ ≤ 1 / 32) (v₀ v₁ U₀ : GLN) (hv₀ : (v₀ : Mat) ∈ Matrix.unitaryGroup (Fin N) ℂ)
    (hv₁ : (v₁ : Mat) ∈ Matrix.unitaryGroup (Fin N) ℂ) (Aμ X₀ X₁ Y₀ Y₁ B₀ B₁ : Mat)
    (hU : v₀ * U₀ * v₁⁻¹ = expU (Complex.I • ((η : ℂ) • Aμ)))
    (hB₀ : B₀ = (η : ℂ)⁻¹ • psi ((η : ℂ) • Ad v₀ X₀) ((η : ℂ) • Y₀))
    (hB₁ : B₁ = (η : ℂ)⁻¹ • psi ((η : ℂ) • Ad v₁ X₁) ((η : ℂ) • Y₁))
    (hX₀ : a * ‖X₀‖ ≤ α₁) (hX₁ : a * ‖X₁‖ ≤ α₁) (hY₀ : a * ‖Y₀‖ ≤ α) (hY₁ : a * ‖Y₁‖ ≤ α)
    (hAμ : a * ‖Aμ‖ ≤ α)
    (hdX : a ^ 2 * ‖(η : ℂ)⁻¹ • (Ad U₀ X₁ - X₀)‖ ≤ α₁)
    (hdY : a ^ 2 * ‖(η : ℂ)⁻¹ • (Y₁ - Y₀)‖ ≤ α) :
    exp (Complex.I • ((η : ℂ) • B₀)) =
        exp (Complex.I • ((η : ℂ) • Ad v₀ X₀)) * exp (Complex.I • ((η : ℂ) • Y₀)) ∧
      a * ‖B₀‖ ≤ 9 * (α + α₁) ∧ a ^ 2 * ‖(η : ℂ)⁻¹ • (B₁ - B₀)‖ ≤ 18 * (α + α₁) := by
  have ha : 0 < a := lt_of_lt_of_le hη hηa
  have hηc : (η : ℂ) ≠ 0 := by exact_mod_cast hη.ne'
  have iso₀ : ∀ X : Mat, ‖Ad v₀ X‖ = ‖X‖ := SupportCont.opNorm_Ad_unitary hv₀
  have iso₁ : ∀ X : Mat, ‖Ad v₁ X‖ = ‖X‖ := SupportCont.opNorm_Ad_unitary hv₁
  have hsc : ∀ Z : Mat, ‖(η : ℂ) • Z‖ ≤ a * ‖Z‖ := fun Z => by
    rw [norm_real_smul η hη.le]; exact mul_le_mul_of_nonneg_right hηa (norm_nonneg _)
  have small : ∀ Z : Mat, ∀ c, a * ‖Z‖ ≤ c → c ≤ 1 / 32 → ‖(η : ℂ) • Z‖ ≤ 1 / 32 :=
    fun Z c h1 h2 => (hsc Z).trans (h1.trans h2)
  set Xt₀ := Ad v₀ X₀ with hXt₀
  set Xt₁ := Ad v₁ X₁ with hXt₁
  have sX₀ : ‖(η : ℂ) • Xt₀‖ ≤ 1 / 32 := small _ α₁ (by rw [hXt₀, iso₀]; exact hX₀) (by linarith)
  have sX₁ : ‖(η : ℂ) • Xt₁‖ ≤ 1 / 32 := small _ α₁ (by rw [hXt₁, iso₁]; exact hX₁) (by linarith)
  have sY₀ : ‖(η : ℂ) • Y₀‖ ≤ 1 / 32 := small _ α hY₀ (by linarith)
  have sY₁ : ‖(η : ℂ) • Y₁‖ ≤ 1 / 32 := small _ α hY₁ (by linarith)
  set P₀ := psi ((η : ℂ) • Xt₀) ((η : ℂ) • Y₀) with hP₀
  set P₁ := psi ((η : ℂ) • Xt₁) ((η : ℂ) • Y₁) with hP₁
  refine ⟨?_, ?_, ?_⟩
  · rw [hB₀, show (η : ℂ) • ((η : ℂ)⁻¹ • P₀) = P₀ by rw [smul_smul, mul_inv_cancel₀ hηc, one_smul]]
    exact exp_I_psi (by linarith [Real.log_two_gt_d9])
  · have hP := norm_psi_le9 sX₀ sY₀
    rw [norm_real_smul η hη.le, norm_real_smul η hη.le, hXt₀, iso₀] at hP
    rw [hB₀, norm_inv_real_smul η hη]
    have e : a * (η⁻¹ * (9 * (η * ‖X₀‖) + η * ‖Y₀‖)) = 9 * (a * ‖X₀‖) + a * ‖Y₀‖ := by
      field_simp
    calc a * (η⁻¹ * ‖P₀‖) ≤ a * (η⁻¹ * (9 * (η * ‖X₀‖) + η * ‖Y₀‖)) := by gcongr
      _ = 9 * (a * ‖X₀‖) + a * ‖Y₀‖ := e
      _ ≤ 9 * (α + α₁) := by linarith
  · -- the difference of `Ã` at the trivial gauge field
    have htd := transported_difference v₀ v₁ U₀ _ hU X₁ X₀
    have hcomm : ‖Ad (expU (Complex.I • ((η : ℂ) • Aμ))) Xt₁ - Xt₁‖ ≤ 6 * (η * ‖Aμ‖) * ‖X₁‖ := by
      have := norm_Ad_exp_sub_le (small Aμ α hAμ (by linarith)) Xt₁
      rwa [norm_real_smul η hη.le, hXt₁, iso₁] at this
    set g := ‖(η : ℂ)⁻¹ • (Ad U₀ X₁ - X₀)‖ with hg
    set gY := ‖(η : ℂ)⁻¹ • (Y₁ - Y₀)‖ with hgY
    have hgrad : ‖Ad U₀ X₁ - X₀‖ = η * g := by
      rw [hg, norm_inv_real_smul η hη]; field_simp
    have hYd : ‖Y₁ - Y₀‖ = η * gY := by
      rw [hgY, norm_inv_real_smul η hη]; field_simp
    have hdXt : ‖Xt₁ - Xt₀‖ ≤ η * g + 6 * (η * ‖Aμ‖) * ‖X₁‖ := by
      have e : Xt₁ - Xt₀ = Ad v₀ (Ad U₀ X₁ - X₀) -
          (Ad (expU (Complex.I • ((η : ℂ) • Aμ))) Xt₁ - Xt₁) := by rw [htd]; abel
      rw [e]
      refine (norm_sub_le _ _).trans ?_
      rw [iso₀, hgrad]; linarith [hcomm]
    have hL := psi_lip9 sX₀ sY₀ sX₁ sY₁
    rw [← hP₀, ← hP₁, ← smul_sub, ← smul_sub, norm_real_smul η hη.le,
      norm_real_smul η hη.le] at hL
    have hBd : ‖(η : ℂ)⁻¹ • (B₁ - B₀)‖ = η⁻¹ * (η⁻¹ * ‖P₁ - P₀‖) := by
      rw [hB₀, hB₁, ← smul_sub, norm_inv_real_smul η hη, norm_inv_real_smul η hη]
    rw [hBd]
    set nX := ‖Xt₁ - Xt₀‖
    set nP := ‖P₁ - P₀‖
    set nA := ‖Aμ‖
    set n1 := ‖X₁‖
    have hnA : 0 ≤ nA := norm_nonneg _
    have hn1 : 0 ≤ n1 := norm_nonneg _
    have hgn : 0 ≤ g := norm_nonneg _
    have hgYn : 0 ≤ gY := norm_nonneg _
    have hstep : nP ≤ 9 * (η * (η * g + 6 * (η * nA) * n1) + η * (η * gY)) := by
      refine hL.trans ?_
      rw [hYd]; gcongr
    have hfin : a ^ 2 * (η⁻¹ * (η⁻¹ * (9 * (η * (η * g + 6 * (η * nA) * n1) + η * (η * gY))))) =
        9 * (a ^ 2 * g + 6 * (a * nA) * (a * n1) + a ^ 2 * gY) := by
      field_simp
    have h6 : (a * nA) * (a * n1) ≤ α * α₁ :=
      mul_le_mul hAμ hX₁ (by positivity) hα
    calc a ^ 2 * (η⁻¹ * (η⁻¹ * nP))
        ≤ a ^ 2 * (η⁻¹ * (η⁻¹ * (9 * (η * (η * g + 6 * (η * nA) * n1) + η * (η * gY))))) := by
          gcongr
      _ = 9 * (a ^ 2 * g + 6 * (a * nA) * (a * n1) + a ^ 2 * gY) := hfin
      _ ≤ 9 * (α₁ + 6 * (α * α₁) + α) := by nlinarith
      _ ≤ 18 * (α + α₁) := by nlinarith

end CubeSmallField
end CoreLean

end
