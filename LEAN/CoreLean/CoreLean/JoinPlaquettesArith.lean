/-
`lem:join-plaquettes` of BALABAN_CORE.tex (`a021c13be348`), the arithmetic of its proof, with `D ≥ 31M_c + 2`,
`M_c ≥ L ≥ 1`.

* `separation_D`: `D - 4M_c ≥ 27M_c` and `4M_c + 3 ≤ D`.
* `weighted_D`: `D - 4M_c - 1 - L ≥ ½D`, so `d ≥ 27M_ck + ½D`.
* `exp_split`: from `d ≥ 27M_ck + ½D`, `½δ₂ ≥ 2δ_⋆`, `27δ_⋆M_c ≥ 8 log L`:
  `e^{-½δ₂d} ≤ L^{-16k}e^{-¼δ₂D}`.
* `b2_condition`: `b₂ = 2C_sσ ≤ 8C_sB₃a_⋆` for `σ ≤ 4B₃a_⋆`, and `C_pC_cb₂ = C₃₅σ` with `C₃₅ = 2C_pC_cC_s`.
* `particular_case`: `MR_n ≥ L²M_c ≥ 31M_c + 2` for `M ≥ L²M_c`, `R_n ≥ 1`, `L ≥ 6`, `M_c ≥ 1`.
-/
import Mathlib

noncomputable section

namespace CoreLean
namespace JoinPlaquettesArith

/-- `D - 4M_c ≥ 27M_c` and `4M_c + 3 ≤ D`. -/
theorem separation_D {D Mc : ℝ} (hMc : 1 ≤ Mc) (hD : 31 * Mc + 2 ≤ D) : 27 * Mc ≤ D - 4 * Mc ∧ 4 * Mc + 3 ≤ D :=
  ⟨by linarith, by linarith⟩

/-- `D - 4M_c - 1 - L ≥ ½D` for `M_c ≥ L`. -/
theorem weighted_D {D Mc L : ℝ} (hMc : 0 ≤ Mc) (hL : L ≤ Mc) (hD : 31 * Mc + 2 ≤ D) : 1 / 2 * D ≤ D - 4 * Mc - 1 - L := by
  linarith

/-- `e^{-½δ₂d} ≤ L^{-16k}e^{-¼δ₂D}`. -/
theorem exp_split {δ₂ δs Mc L D d : ℝ} (k : ℕ) (hL : 1 ≤ L) (hδ : 2 * δs ≤ 1 / 2 * δ₂) (hMc : 0 ≤ Mc)
    (hlog : 8 * Real.log L ≤ 27 * δs * Mc) (hδ₂ : 0 ≤ δ₂) (hd : 27 * Mc * k + 1 / 2 * D ≤ d) :
    Real.exp (-(1 / 2) * δ₂ * d) ≤ (L ^ (16 * k))⁻¹ * Real.exp (-(1 / 4) * δ₂ * D) := by
  have hL0 : 0 < L := by linarith
  rw [← Real.exp_log (by positivity : (0 : ℝ) < (L ^ (16 * k))⁻¹), ← Real.exp_add, Real.log_inv, Real.log_pow]
  apply Real.exp_le_exp.2
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h1 : 2 * δs * (27 * Mc * k) ≤ 1 / 2 * δ₂ * (27 * Mc * k) := mul_le_mul_of_nonneg_right hδ (by positivity)
  have h2 : 16 * Real.log L * k ≤ 2 * (27 * δs * Mc) * k := by nlinarith
  have h3 : 1 / 2 * δ₂ * (27 * Mc * k + 1 / 2 * D) ≤ 1 / 2 * δ₂ * d := mul_le_mul_of_nonneg_left hd (by positivity)
  push_cast
  nlinarith

/-- `b₂ = 2C_sσ ≤ 8C_sB₃a_⋆` and `C_pC_cb₂ = C₃₅σ`. -/
theorem b2_condition {Cs σ B₃ a Cp Cc : ℝ} (hCs : 0 ≤ Cs) (hσ : σ ≤ 4 * B₃ * a) :
    2 * Cs * σ ≤ 8 * Cs * B₃ * a ∧ Cp * Cc * (2 * Cs * σ) = 2 * Cp * Cc * Cs * σ := by
  refine ⟨by nlinarith, by ring⟩

/-- `MR_n ≥ L²M_c ≥ 31M_c + 2`. -/
theorem particular_case {M R L Mc : ℝ} (hL : 6 ≤ L) (hMc : 1 ≤ Mc) (hM : L ^ 2 * Mc ≤ M) (hR : 1 ≤ R) :
    L ^ 2 * Mc ≤ M * R ∧ 31 * Mc + 2 ≤ L ^ 2 * Mc := by
  have hM0 : 0 ≤ M := le_trans (by positivity) hM
  refine ⟨hM.trans (le_mul_of_one_le_right hM0 hR), ?_⟩
  have : 36 ≤ L ^ 2 := by nlinarith
  nlinarith

end JoinPlaquettesArith
end CoreLean

end
