/-
`prop:space-stability`(i) of BALABAN_CORE.tex (`a021c13be348`), the step "the complex part" of its proof, with the
function `Ψ` of `lem:product` (`Psi.lean`, `C_Ψ = 256`).

* At a bond, with `X = a₀𝐀(b)` and `Y = a₀𝔷(b)` of norms at most `1/32`: `‖Ψ(X, Y) - Y - X‖ ≤ 256‖X‖‖Y‖`
  (`complex_part`), from `eq:product-lipschitz` at `(0, Y)` and `Ψ(0, Y) = Y`; so `𝔷' = a₀⁻¹Ψ(a₀𝐀, a₀𝔷)` satisfies
  `‖𝔷' - 𝔷 - 𝐀‖ ≤ C_Ψa₀‖𝔷‖‖𝐀‖`.
* The first differences: `eq:product-lipschitz` at the transported pairs gives
  `‖∇𝔷' - ∇𝔷 - ∇𝐀‖ ≤ C_Ψa₀(‖𝔷‖‖∇𝐀‖ + ‖𝐀‖‖∇𝔷‖)` (this is `psi_lipschitz` itself, with `Ad_psi` for the transport).
* The condition (ii) for the moved pair: with `a₀ ≤ a`, `a‖𝐀‖, a²‖∇𝐀‖ ≤ ρ`, `a‖𝔷‖, a²‖∇𝔷‖ ≤ α₁` and `2C_Ψα₁ ≤ 1`,
  `a‖𝔷'‖ ≤ α₁ + 2ρ` and `a²‖∇𝔷'‖ ≤ α₁ + 2ρ` (`moved_field`, `moved_difference`).
-/
import CoreLean.Psi

open Matrix NormedSpace
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean
namespace SpaceStability

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ

/-- **The complex part** at a bond: `‖Ψ(X, Y) - Y - X‖ ≤ 256‖X‖‖Y‖`. -/
theorem complex_part {X Y : Mat} (hX : ‖X‖ ≤ 1 / 32) (hY : ‖Y‖ ≤ 1 / 32) :
    ‖psi X Y - Y - X‖ ≤ 256 * ‖X‖ * ‖Y‖ := by
  have h0 : ‖(0 : Mat)‖ ≤ 1 / 32 := by simp
  have h := psi_lipschitz h0 hY hX hY
  have hY4 : ‖Y‖ < 1 / 4 := by linarith
  rw [psi_zero_left hY4, sub_zero, sub_self, sub_zero, norm_zero, mul_zero, add_zero] at h
  calc ‖psi X Y - Y - X‖ = ‖psi X Y - Y - X‖ := rfl
    _ ≤ 256 * (‖Y‖ * ‖X‖) := h
    _ = 256 * ‖X‖ * ‖Y‖ := by ring

/-- **The field of the moved pair**: `a‖𝔷'‖ ≤ α₁ + 2ρ`. -/
theorem moved_field {a a₀ nz nA nz' α₁ ρ : ℝ} (ha₀ : 0 < a₀) (haa : a₀ ≤ a) (hz0 : 0 ≤ nz) (hA0 : 0 ≤ nA)
    (hz : a * nz ≤ α₁) (hA : a * nA ≤ ρ) (hρ : 0 ≤ ρ) (hsmall : 2 * 256 * α₁ ≤ 1)
    (hz' : nz' ≤ nz + nA + 256 * a₀ * nz * nA) : a * nz' ≤ α₁ + 2 * ρ := by
  have ha : 0 < a := lt_of_lt_of_le ha₀ haa
  -- `a · a₀‖𝔷‖‖𝐀‖ ≤ (a‖𝔷‖)(a‖𝐀‖) ≤ α₁ρ`
  have h1 : a * (a₀ * nz * nA) ≤ α₁ * ρ := by
    have : a * (a₀ * nz * nA) ≤ (a * nz) * (a * nA) := by
      have : a * (a₀ * nz * nA) = a₀ * ((a * nz) * nA) := by ring
      rw [this]
      have h2 : (a * nz) * (a * nA) = a * ((a * nz) * nA) := by ring
      rw [h2]
      exact mul_le_mul_of_nonneg_right haa (by positivity)
    exact this.trans (mul_le_mul hz hA (by positivity) ((mul_nonneg ha.le hz0).trans hz))
  have hα : 0 ≤ α₁ := (mul_nonneg ha.le hz0).trans hz
  calc a * nz' ≤ a * (nz + nA + 256 * a₀ * nz * nA) := mul_le_mul_of_nonneg_left hz' ha.le
    _ = a * nz + a * nA + 256 * (a * (a₀ * nz * nA)) := by ring
    _ ≤ α₁ + ρ + 256 * (α₁ * ρ) := by linarith
    _ ≤ α₁ + 2 * ρ := by nlinarith

/-- **The first differences of the moved pair**: `a²‖∇𝔷'‖ ≤ α₁ + 2ρ`. -/
theorem moved_difference {a a₀ nz nA nDz nDA nDz' α₁ ρ : ℝ} (ha₀ : 0 < a₀) (haa : a₀ ≤ a) (hz0 : 0 ≤ nz)
    (hA0 : 0 ≤ nA) (hDz0 : 0 ≤ nDz) (hDA0 : 0 ≤ nDA) (hz : a * nz ≤ α₁) (hA : a * nA ≤ ρ)
    (hDz : a ^ 2 * nDz ≤ α₁) (hDA : a ^ 2 * nDA ≤ ρ) (hρ : 0 ≤ ρ) (hsmall : 2 * 256 * α₁ ≤ 1)
    (hDz' : nDz' ≤ nDz + nDA + 256 * a₀ * (nz * nDA + nA * nDz)) : a ^ 2 * nDz' ≤ α₁ + 2 * ρ := by
  have ha : 0 < a := lt_of_lt_of_le ha₀ haa
  have hα : 0 ≤ α₁ := (mul_nonneg ha.le hz0).trans hz
  have h1 : a ^ 2 * (a₀ * (nz * nDA + nA * nDz)) ≤ 2 * (α₁ * ρ) := by
    have e : a ^ 2 * (a₀ * (nz * nDA + nA * nDz)) = a₀ * ((a * nz) * (a * nDA) + (a * nA) * (a * nDz)) := by
      ring
    have h2 : (a * nz) * (a ^ 2 * nDA) + (a * nA) * (a ^ 2 * nDz) ≤ α₁ * ρ + ρ * α₁ :=
      add_le_add (mul_le_mul hz hDA (by positivity) hα) (mul_le_mul hA hDz (by positivity) hρ)
    have h3 : a₀ * ((a * nz) * (a * nDA) + (a * nA) * (a * nDz)) ≤
        (a * nz) * (a ^ 2 * nDA) + (a * nA) * (a ^ 2 * nDz) := by
      have : (a * nz) * (a ^ 2 * nDA) + (a * nA) * (a ^ 2 * nDz) =
          a * ((a * nz) * (a * nDA) + (a * nA) * (a * nDz)) := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_right haa (by positivity)
    rw [e]; linarith
  calc a ^ 2 * nDz' ≤ a ^ 2 * (nDz + nDA + 256 * a₀ * (nz * nDA + nA * nDz)) :=
        mul_le_mul_of_nonneg_left hDz' (by positivity)
    _ = a ^ 2 * nDz + a ^ 2 * nDA + 256 * (a ^ 2 * (a₀ * (nz * nDA + nA * nDz))) := by ring
    _ ≤ α₁ + ρ + 256 * (2 * (α₁ * ρ)) := by linarith
    _ ≤ α₁ + 2 * ρ := by nlinarith

/-- **`eq:difference-of-differences`**: with `Ad_{𝐔(b)} = Ad_{e^{ia₀𝔷(b)}}Ad_{U(b)}` and `V = Ad_{U(b)}f(x + a₀e_μ)`,
`a₀⁻¹‖(Ad_{e^{ia₀𝔷(b)}} - 1)V‖ ≤ 8‖𝔷(b)‖‖V‖` for `a₀‖𝔷(b)‖ ≤ 1/32`, by `eq:adjoint-lipschitz`. -/
theorem difference_of_differences {a₀ : ℝ} (ha₀ : 0 < a₀) {z : Mat} (hz : a₀ * ‖z‖ ≤ 1 / 32) (V : Mat) :
    a₀⁻¹ * ‖Ad (expU (Complex.I • (a₀ • z))) V - V‖ ≤ 8 * ‖z‖ * ‖V‖ := by
  have hX : ‖a₀ • z‖ ≤ 1 / 32 := by rw [norm_smul, Real.norm_of_nonneg ha₀.le]; exact hz
  have h := norm_Ad_exp_sub_le hX V
  rw [norm_smul, Real.norm_of_nonneg ha₀.le] at h
  have h1 : a₀⁻¹ * ‖Ad (expU (Complex.I • (a₀ • z))) V - V‖ ≤ a₀⁻¹ * (6 * (a₀ * ‖z‖) * ‖V‖) :=
    mul_le_mul_of_nonneg_left h (inv_nonneg.2 ha₀.le)
  have h2 : a₀⁻¹ * (6 * (a₀ * ‖z‖) * ‖V‖) = 6 * ‖z‖ * ‖V‖ := by field_simp
  have h3 : 6 * ‖z‖ * ‖V‖ ≤ 8 * ‖z‖ * ‖V‖ := by
    have := mul_nonneg (norm_nonneg z) (norm_nonneg V); nlinarith
  linarith

/-- The function `𝖾(Z, W) = a₀⁻¹(Ad_{e^{ia₀Z}} - 1)W` of the second entry. -/
def efun (a₀ : ℝ) (Z W : Mat) : Mat := a₀⁻¹ • (Ad (expU (Complex.I • (a₀ • Z))) W - W)

/-- `‖𝖾(Z, W)‖ ≤ 8‖Z‖‖W‖`. -/
theorem efun_bound {a₀ : ℝ} (ha₀ : 0 < a₀) {Z : Mat} (hZ : a₀ * ‖Z‖ ≤ 1 / 32) (W : Mat) :
    ‖efun a₀ Z W‖ ≤ 8 * ‖Z‖ * ‖W‖ := by
  unfold efun
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 ha₀.le)]
  exact difference_of_differences ha₀ hZ W

/-- `‖𝖾(Z', W') - 𝖾(Z, W)‖ ≤ 8‖Z'‖‖W' - W‖ + 8‖Z' - Z‖‖W‖`. -/
theorem efun_lipschitz {a₀ : ℝ} (ha₀ : 0 < a₀) {Z Z' : Mat} (hZ : a₀ * ‖Z‖ ≤ 1 / 32) (hZ' : a₀ * ‖Z'‖ ≤ 1 / 32)
    (W W' : Mat) : ‖efun a₀ Z' W' - efun a₀ Z W‖ ≤ 8 * ‖Z'‖ * ‖W' - W‖ + 8 * ‖Z' - Z‖ * ‖W‖ := by
  have e : efun a₀ Z' W' - efun a₀ Z W = efun a₀ Z' (W' - W) +
      a₀⁻¹ • (Ad (expU (Complex.I • (a₀ • Z'))) W - Ad (expU (Complex.I • (a₀ • Z))) W) := by
    unfold efun
    rw [Ad_sub, ← smul_add, ← smul_sub]
    congr 1
    abel
  rw [e]
  refine (norm_add_le _ _).trans (add_le_add (efun_bound ha₀ hZ' _) ?_)
  have hX : ‖a₀ • Z‖ ≤ 1 / 32 := by rw [norm_smul, Real.norm_of_nonneg ha₀.le]; exact hZ
  have hX' : ‖a₀ • Z'‖ ≤ 1 / 32 := by rw [norm_smul, Real.norm_of_nonneg ha₀.le]; exact hZ'
  have h := norm_Ad_exp_sub_Ad_exp_le hX hX' W
  rw [← smul_sub, norm_smul, Real.norm_of_nonneg ha₀.le] at h
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 ha₀.le)]
  calc a₀⁻¹ * ‖Ad (expU (Complex.I • (a₀ • Z'))) W - Ad (expU (Complex.I • (a₀ • Z))) W‖
      ≤ a₀⁻¹ * (8 * (a₀ * ‖Z' - Z‖) * ‖W‖) := mul_le_mul_of_nonneg_left h (inv_nonneg.2 ha₀.le)
    _ = 8 * ‖Z' - Z‖ * ‖W‖ := by field_simp

/-- The bound `a²‖E‖ ≤ 16α₁ρ` of `E_{μν} = 𝖾(𝔷_μ, W_{μν}) - 𝖾(𝔷_ν, W_{νμ})`, from `‖𝖾(Z, W)‖ ≤ 8‖Z‖‖W‖`,
`a‖𝔷‖ ≤ α₁`, and `a‖W‖ ≤ ρ` (the transports preserving the norm). -/
theorem E_bound {a nE nz nW1 nW2 α₁ ρ : ℝ} (ha : 0 < a) (hz0 : 0 ≤ nz)
    (hE : nE ≤ 8 * nz * nW1 + 8 * nz * nW2) (hz : a * nz ≤ α₁) (hW1 : a * nW1 ≤ ρ) (hW2 : a * nW2 ≤ ρ)
    (hW10 : 0 ≤ nW1) (hW20 : 0 ≤ nW2) : a ^ 2 * nE ≤ 16 * α₁ * ρ := by
  have hα : 0 ≤ α₁ := (mul_nonneg ha.le hz0).trans hz
  have h1 : (a * nz) * (a * nW1) ≤ α₁ * ρ := mul_le_mul hz hW1 (by positivity) hα
  have h2 : (a * nz) * (a * nW2) ≤ α₁ * ρ := mul_le_mul hz hW2 (by positivity) hα
  calc a ^ 2 * nE ≤ a ^ 2 * (8 * nz * nW1 + 8 * nz * nW2) := mul_le_mul_of_nonneg_left hE (by positivity)
    _ = 8 * ((a * nz) * (a * nW1)) + 8 * ((a * nz) * (a * nW2)) := by ring
    _ ≤ 16 * α₁ * ρ := by linarith

/-- The remainder of the current: `C₈((ρ + 2ρ)(2ρ + α₀) + ρ³) ≤ 3C₈ρ` when `2ρ + α₀ + ρ²/3 ≤ 1`. -/
theorem current_remainder_bound {C8 ρ α₀ : ℝ} (hC : 0 ≤ C8) (hρ : 0 ≤ ρ) (h : 2 * ρ + α₀ + ρ ^ 2 / 3 ≤ 1) :
    C8 * ((ρ + 2 * ρ) * (2 * ρ + α₀) + ρ ^ 3) ≤ 3 * C8 * ρ := by
  have : (ρ + 2 * ρ) * (2 * ρ + α₀) + ρ ^ 3 = 3 * ρ * (2 * ρ + α₀ + ρ ^ 2 / 3) := by ring
  rw [this]
  have h1 : 3 * ρ * (2 * ρ + α₀ + ρ ^ 2 / 3) ≤ 3 * ρ := by nlinarith
  nlinarith

/-- **The second entry**: `a³‖p'‖ ≤ γ₀ + (80α₁ + 3C₈)ρ ≤ γ₀ + C₂₂ρ`, `C₂₂ = 13 + 3C₈`, for `80α₁ ≤ 1`. -/
theorem second_entry_size {γ₀ np nz nK nψ nF a α₁ ρ C8 : ℝ} (ha : 0 < a) (hz0 : 0 ≤ nz) (hρ : 0 ≤ ρ)
    (hp : a ^ 3 * np ≤ γ₀ + 24 * (a * nz) * (a ^ 2 * nK) + 8 * (a * nz) * (a ^ 2 * nψ) + a ^ 3 * nF)
    (hz : a * nz ≤ α₁) (hK : a ^ 2 * nK ≤ 3 * ρ) (hψ : a ^ 2 * nψ ≤ ρ) (hF : a ^ 3 * nF ≤ 3 * C8 * ρ)
    (hK0 : 0 ≤ nK) (hψ0 : 0 ≤ nψ) (hα : 80 * α₁ ≤ 1) :
    a ^ 3 * np ≤ γ₀ + (80 * α₁ + 3 * C8) * ρ ∧ a ^ 3 * np ≤ γ₀ + (13 + 3 * C8) * ρ := by
  have hα0 : 0 ≤ α₁ := (mul_nonneg ha.le hz0).trans hz
  have h1 : (a * nz) * (a ^ 2 * nK) ≤ α₁ * (3 * ρ) := mul_le_mul hz hK (by positivity) hα0
  have h2 : (a * nz) * (a ^ 2 * nψ) ≤ α₁ * ρ := mul_le_mul hz hψ (by positivity) hα0
  have h3 : a ^ 3 * np ≤ γ₀ + (80 * α₁ + 3 * C8) * ρ := by nlinarith
  refine ⟨h3, h3.trans ?_⟩
  nlinarith

end SpaceStability
end CoreLean

end
