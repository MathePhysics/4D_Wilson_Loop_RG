/-
`prop:boundary-change` of BALABAN_CORE.tex (`a021c13be348`), the arithmetic of its proof.

* `distance_S`: `MR a - 2M₂R a - a_n ≥ (L² - 2)M₂R a - a_n` from `L²M₂ ≤ M` (`def:parameters`), and
  `(L² - 2)M₂R - 20M_c - 3 ≥ 2M₂R` for `L ≥ 3`, `M_c ≤ M₂`, `M₂ ≥ 1`, `R ≥ 50`.
* `eps_prime`: `ε' = 2L²(1 + κ_s)ε̂ ≤ 3L²ε̂` for `κ_s ≤ ½`.
* `h_small`: `h = C₁₃ε̂e^{-δ₂M₂R} ≤ ϑ_n/C₁₃` from `C₁₃²ε̂e^{-δ₂M₂R} ≤ ϑ_n`, and `h ≤ ϑ_n/12 ≤ 1/768` for `C₁₃ ≥ 12`,
  `ϑ_n ≤ 1/64`.
* `dpsi_bound`: `(C_Ψ + 11‖φ'₁‖/(5ϑ_n))h ≤ ½` for `h ≤ ϑ_n/C₁₃`, `C₁₃ ≥ 2C_Ψ + 5‖φ'₁‖`, `0 < ϑ_n ≤ 1/64`.
-/
import Mathlib

noncomputable section

namespace CoreLean
namespace BoundaryChangeArith

/-- **The distance of the bonds of `𝖲`.** -/
theorem distance_S {M M₂ R a an L Mc : ℝ} (hL : 3 ≤ L) (hM : L ^ 2 * M₂ ≤ M) (hR : 0 ≤ R) (ha : 0 ≤ a)
    (hMc : Mc ≤ M₂) (hM₂ : 1 ≤ M₂) (hR50 : 50 ≤ R) :
    (L ^ 2 - 2) * M₂ * R * a - an ≤ M * R * a - 2 * M₂ * R * a - an ∧
      2 * M₂ * R ≤ (L ^ 2 - 2) * M₂ * R - 20 * Mc - 3 := by
  refine ⟨?_, ?_⟩
  · have : L ^ 2 * M₂ * (R * a) ≤ M * (R * a) := mul_le_mul_of_nonneg_right hM (mul_nonneg hR ha)
    nlinarith
  · have hL2 : 9 ≤ L ^ 2 := by nlinarith
    have h1 : 7 * (M₂ * R) ≤ (L ^ 2 - 2) * (M₂ * R) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have h2 : 50 * M₂ ≤ M₂ * R := by nlinarith
    nlinarith

/-- `ε' = 2L²(1 + κ_s)ε̂ ≤ 3L²ε̂`. -/
theorem eps_prime {L κ ε : ℝ} (hκ : κ ≤ 1 / 2) (hε : 0 ≤ ε) : 2 * L ^ 2 * (1 + κ) * ε ≤ 3 * L ^ 2 * ε := by
  have : 0 ≤ L ^ 2 * ε := by positivity
  nlinarith

/-- `h ≤ ϑ_n/C₁₃`, `h ≤ ϑ_n/12 ≤ 1/768`. -/
theorem h_small {C ε e ϑ : ℝ} (hC : 12 ≤ C) (hεe : 0 ≤ ε * e) (h : C ^ 2 * (ε * e) ≤ ϑ) (hϑ : ϑ ≤ 1 / 64) :
    C * (ε * e) ≤ ϑ / C ∧ C * (ε * e) ≤ ϑ / 12 ∧ ϑ / 12 ≤ 1 / 768 := by
  have hC0 : 0 < C := by linarith
  have h1 : C * (ε * e) ≤ ϑ / C := by
    rw [le_div_iff₀ hC0]; nlinarith
  have hϑ0 : 0 ≤ ϑ := le_trans (by positivity) h
  have h2 : ϑ / C ≤ ϑ / 12 := div_le_div_of_nonneg_left hϑ0 (by norm_num) hC
  exact ⟨h1, h1.trans h2, by linarith⟩

/-- **The derivative of `ψ_b`**: `(C_Ψ + 11‖φ'₁‖/(5ϑ))h ≤ ½`. -/
theorem dpsi_bound {CΨ φ ϑ h C : ℝ} (hCΨ : 0 ≤ CΨ) (hφ : 0 ≤ φ) (hϑ0 : 0 < ϑ) (hϑ : ϑ ≤ 1 / 64) (hh0 : 0 ≤ h)
    (hh : h ≤ ϑ / C) (hC : 2 * CΨ + 5 * φ ≤ C) (hCpos : 0 < C) :
    (CΨ + 11 * φ / (5 * ϑ)) * h ≤ 1 / 2 := by
  have hhC : h * C ≤ ϑ := by rw [le_div_iff₀ hCpos] at hh; linarith
  -- `C_Ψh ≤ C_Ψϑ/C ≤ C_Ψ/(64C)` and `(11φ/(5ϑ))h ≤ 11φ/(5C)`
  have e1 : (CΨ + 11 * φ / (5 * ϑ)) * h = CΨ * h + 11 * φ * h / (5 * ϑ) := by ring
  rw [e1]
  have t1 : CΨ * h * C ≤ CΨ / 64 := by
    have : CΨ * (h * C) ≤ CΨ * (1 / 64) := mul_le_mul_of_nonneg_left (hhC.trans hϑ) hCΨ
    nlinarith
  have t2 : 11 * φ * h / (5 * ϑ) * C ≤ 11 * φ / 5 := by
    have : 11 * φ * (h * C) ≤ 11 * φ * ϑ := mul_le_mul_of_nonneg_left hhC (by positivity)
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  have hsum : (CΨ * h + 11 * φ * h / (5 * ϑ)) * C ≤ 1 / 2 * C := by nlinarith
  exact le_of_mul_le_mul_right hsum hCpos

end BoundaryChangeArith
end CoreLean

end
