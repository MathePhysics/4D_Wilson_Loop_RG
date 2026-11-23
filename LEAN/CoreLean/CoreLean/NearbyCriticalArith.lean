/-
`lem:nearby-critical` and `lem:plaquette-fields` of BALABAN_CORE.tex (`a021c13be348`), the arithmetic of their proofs.

`lem:nearby-critical`, with `s = C_pfα₀ + ‖𝔟‖`:
* `s_small`: `512(B₅ + √NC_pf)s ≤ 1` and `C_pf ≥ 1` give `s ≤ 1/512 < log 2`, `√Nα₀ ≤ √NC_pf s ≤ 1/512`, and
  `B₅s ≤ 1/512`.
* `A_small`: `LB₅s < c'₄` gives `B₅s < c'₄/L`.
* `moved_plaquette`: `α₀ + 10B₅s ≤ (1 + 10B₅)s`.
* `class_constant`: the plaquettes at most `(1 + 10B₅)s` and the current at most `C_J(1 + 10B₅)s` give the class
  `𝔘((1 + C_J)(1 + 10B₅)s)` (the two constants are at most the sum).

`lem:plaquette-fields`:
* `pf_constant`: `C_pf = max{1, C_reg}` gives `C_regα₀ ≤ C_pfα₀` and `α₀ ≤ C_pfα₀`, so that
  `𝔘(α₀) ⊂ 𝔘(C_pfα₀)` (monotonicity of the class in the constant).
-/
import Mathlib

noncomputable section

namespace CoreLean
namespace NearbyCriticalArith

/-- `s ≤ 1/512 < log 2`, `√Nα₀ ≤ 1/512`, `B₅s ≤ 1/512`. -/
theorem s_small {B₅ N Cpf α₀ b s : ℝ} (hB : 0 ≤ B₅) (hN : 1 ≤ N) (hC : 1 ≤ Cpf) (hα : 0 ≤ α₀) (hb : 0 ≤ b)
    (hs : s = Cpf * α₀ + b) (h : 512 * (B₅ + Real.sqrt N * Cpf) * s ≤ 1) :
    s ≤ 1 / 512 ∧ (1 / 512 : ℝ) < Real.log 2 ∧ Real.sqrt N * α₀ ≤ 1 / 512 ∧ B₅ * s ≤ 1 / 512 := by
  have hs0 : 0 ≤ s := by rw [hs]; positivity
  have hsqN : 1 ≤ Real.sqrt N := by rw [Real.le_sqrt (by norm_num) (by linarith)]; linarith
  have hsC : 1 ≤ Real.sqrt N * Cpf := by nlinarith
  have hαs : α₀ ≤ Cpf * α₀ := le_mul_of_one_le_left hα hC
  have hCs : Cpf * α₀ ≤ s := by rw [hs]; linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · nlinarith
  · have := Real.log_two_gt_d9; linarith
  · have h1 : Real.sqrt N * α₀ ≤ Real.sqrt N * Cpf * s := by
      calc Real.sqrt N * α₀ ≤ Real.sqrt N * (Cpf * α₀) :=
            mul_le_mul_of_nonneg_left hαs (Real.sqrt_nonneg _)
        _ = Real.sqrt N * Cpf * α₀ := by ring
        _ ≤ Real.sqrt N * Cpf * s := by
            have : Cpf * α₀ ≤ s := hCs
            nlinarith [Real.sqrt_nonneg N]
    nlinarith [mul_nonneg hB hs0]
  · nlinarith [mul_nonneg (Real.sqrt_nonneg N) (by linarith : (0 : ℝ) ≤ Cpf)]

/-- `LB₅s < c'₄` gives `B₅s < c'₄/L`. -/
theorem A_small {L B₅ s c₄ : ℝ} (hL : 0 < L) (h : L * (B₅ * s) < c₄) : B₅ * s < c₄ / L := by
  rw [lt_div_iff₀ hL]; linarith

/-- `α₀ + 10B₅s ≤ (1 + 10B₅)s` for `α₀ ≤ C_pfα₀ ≤ s`. -/
theorem moved_plaquette {α₀ B₅ s : ℝ} (hα : α₀ ≤ s) : α₀ + 10 * B₅ * s ≤ (1 + 10 * B₅) * s := by nlinarith

/-- The class: both constants are at most `(1 + C_J)(1 + 10B₅)s`. -/
theorem class_constant {CJ e : ℝ} (hCJ : 0 ≤ CJ) (he : 0 ≤ e) : e ≤ (1 + CJ) * e ∧ CJ * e ≤ (1 + CJ) * e :=
  ⟨by nlinarith, by nlinarith⟩

/-- `C_pf = max{1, C_reg}`: `C_regα₀ ≤ C_pfα₀` and `α₀ ≤ C_pfα₀`. -/
theorem pf_constant {Creg α₀ : ℝ} (hα : 0 ≤ α₀) :
    Creg * α₀ ≤ max 1 Creg * α₀ ∧ α₀ ≤ max 1 Creg * α₀ :=
  ⟨mul_le_mul_of_nonneg_right (le_max_right _ _) hα,
    (one_mul α₀).symm.le.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hα)⟩

end NearbyCriticalArith
end CoreLean

end
