/-
`lem:scalar-walk-expansion` of BALABAN_CORE.tex (`a021c13be348`), two steps of its proof.

* (W3): at most `N'^n_𝒟` walks of the length `n` begin with a given cube, each with the number
  `b_ω = B_w(C_wM_w^{-1})^n`, so that the sum is at most `B_wΣ_n(N'_𝒟C_wM_w^{-1})^n ≤ 2B_w` for `M_w ≥ 2N'_𝒟C_w`
  (`walk_count`).
* The constant: `3⁴L⁴·2⁹L²·L²·24C_nB_e(β)(C_ζ + 1)e^{3L⁴δ_sf} ≤ B''_w = 2^{20}L⁸(C_ζ + 1)e^{3L⁴δ_sf}C_nB_e(β)`
  (`constant_B''`), since `3⁴·2⁹·24 = 995328 ≤ 2^{20}`.
-/
import Mathlib

open Finset

noncomputable section

namespace CoreLean
namespace ScalarWalkExpansion

/-- **(W3)**: `Σ_{n < K}N^n·B(C/M)^n ≤ 2B` for `2NC ≤ M`. -/
theorem walk_count {N C M B : ℝ} (hN : 0 ≤ N) (hC : 0 ≤ C) (hM : 0 < M) (hB : 0 ≤ B) (hcond : 2 * N * C ≤ M)
    (K : ℕ) : ∑ n ∈ range K, N ^ n * (B * (C / M) ^ n) ≤ 2 * B := by
  set q := N * (C / M)
  have hq0 : 0 ≤ q := by positivity
  have hq : q ≤ 1 / 2 := by
    simp only [q]; rw [← mul_div_assoc, div_le_iff₀ hM]; linarith
  have e : ∀ n : ℕ, N ^ n * (B * (C / M) ^ n) = B * q ^ n := fun n => by
    simp only [q]; rw [mul_pow]; ring
  simp only [e]
  rw [← Finset.mul_sum]
  have hgeo : ∑ n ∈ range K, q ^ n ≤ 2 := by
    have hq1 : q < 1 := by linarith
    calc ∑ n ∈ range K, q ^ n ≤ (1 - q)⁻¹ := by
          rw [geom_sum_eq hq1.ne, div_le_iff_of_neg (by linarith)]
          rw [show (1 - q)⁻¹ * (q - 1) = -1 by field_simp; ring]
          linarith [pow_nonneg hq0 K]
      _ ≤ 2 := by rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  nlinarith

/-- **The constant `B''_w`**. -/
theorem constant_B'' {L Cn Be Cζ E : ℝ} (hL : 0 ≤ L) (hCn : 0 ≤ Cn) (hBe : 0 ≤ Be) (hCζ : 0 ≤ Cζ) (hE : 0 ≤ E) :
    3 ^ 4 * L ^ 4 * (2 ^ 9 * L ^ 2) * L ^ 2 * (24 * Cn * Be * (Cζ + 1) * E) ≤
      2 ^ 20 * L ^ 8 * (Cζ + 1) * E * Cn * Be := by
  have h : 0 ≤ L ^ 8 * (Cζ + 1) * E * Cn * Be := by positivity
  have e : 3 ^ 4 * L ^ 4 * (2 ^ 9 * L ^ 2) * L ^ 2 * (24 * Cn * Be * (Cζ + 1) * E) =
      995328 * (L ^ 8 * (Cζ + 1) * E * Cn * Be) := by ring
  rw [e]
  nlinarith

end ScalarWalkExpansion
end CoreLean

end
