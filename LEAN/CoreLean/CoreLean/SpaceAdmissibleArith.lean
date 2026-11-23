/-
`lem:space-admissible` of BALABAN_CORE.tex (`a021c13be348`), the arithmetic of its proof.

* `unit_conversion`: `(L⁻¹ + L⁻²)·2MB_rα₀ ≤ 4MB_rα₀/L` for `L ≥ 1`.
* `cE_small`: `c'_Γ ≤ c_E/(2C_E) ≤ 1/28` for `c_E ≤ 1/8`, `C_E ≥ 32L²`, `L ≥ 1`.
* `size_bound`: `5γ₀ + 16α'₁γ₀ + 40α'₁γ₀ = (5 + 56α'₁)γ₀ ≤ 7γ₀` for `α'₁ ≤ 1/28`.
* `size_bound_t`: `(1 + |t|)(5 + 40α'₁)γ₀ + 16(1 + |t|)α'₁(1 + |t|)γ₀ ≤ 7(1 + |t|)γ₀` for `(1 + |t|)α'₁ ≤ 1/28`.
-/
import Mathlib

noncomputable section

namespace CoreLean
namespace SpaceAdmissibleArith

/-- `(L⁻¹ + L⁻²)·2x ≤ 4x/L` for `L ≥ 1`, `x ≥ 0`. -/
theorem unit_conversion {L x : ℝ} (hL : 1 ≤ L) (hx : 0 ≤ x) : (L⁻¹ + (L ^ 2)⁻¹) * (2 * x) ≤ 4 * x / L := by
  have hL0 : 0 < L := by linarith
  have h : (L ^ 2)⁻¹ ≤ L⁻¹ := by
    rw [inv_le_inv₀ (by positivity) hL0]; nlinarith
  have : (L⁻¹ + (L ^ 2)⁻¹) * (2 * x) ≤ (2 * L⁻¹) * (2 * x) :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  calc (L⁻¹ + (L ^ 2)⁻¹) * (2 * x) ≤ (2 * L⁻¹) * (2 * x) := this
    _ = 4 * x / L := by field_simp; ring

/-- `c_E/(2C_E) ≤ 1/28`. -/
theorem cE_small {cE CE L : ℝ} (hL : 1 ≤ L) (hcE0 : 0 ≤ cE) (hcE : cE ≤ 1 / 8) (hCE : 32 * L ^ 2 ≤ CE) :
    cE / (2 * CE) ≤ 1 / 28 := by
  have hCE0 : 32 ≤ CE := le_trans (by nlinarith) hCE
  rw [div_le_iff₀ (by linarith)]
  nlinarith

/-- `(5 + 56α'₁)γ₀ ≤ 7γ₀` for `α'₁ ≤ 1/28`. -/
theorem size_bound {α γ : ℝ} (hα : α ≤ 1 / 28) (hγ : 0 ≤ γ) : 5 * γ + 16 * α * γ + 40 * α * γ ≤ 7 * γ := by
  nlinarith

/-- The size along `q_t`. -/
theorem size_bound_t {α γ s : ℝ} (hs : 1 ≤ s) (hα0 : 0 ≤ α) (hsα : s * α ≤ 1 / 28) (hγ : 0 ≤ γ) :
    s * (5 + 40 * α) * γ + 16 * (s * α) * (s * γ) ≤ 7 * s * γ := by
  have h1 : 40 * α ≤ 40 * (s * α) := by nlinarith
  have h2 : s * (5 + 40 * α) * γ + 16 * (s * α) * (s * γ) ≤ s * (5 + 56 * (s * α)) * γ := by
    have : 0 ≤ s * γ := by positivity
    nlinarith
  have h3 : s * (5 + 56 * (s * α)) * γ ≤ 7 * s * γ := by
    have : 0 ≤ s * γ := by positivity
    nlinarith
  linarith

end SpaceAdmissibleArith
end CoreLean

end
