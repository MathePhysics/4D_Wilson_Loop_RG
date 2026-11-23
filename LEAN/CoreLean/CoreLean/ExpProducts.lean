/-
`cor:exp-products` of BALABAN_CORE.tex (`50787904c4ef`): a product of exponentials of small matrices of `𝔤^c` is the
exponential of a matrix of `𝔤^c`, controlled by the sum of their norms. With the constant `C_Ψ = 256` of
`psi_lipschitz` (the core's `C_Ψ = 64`), for `s = Σ‖Z_k‖ ≤ 2^{-10}`: `e^{iZ_1}⋯e^{iZ_m} = e^{iZ}`, `Z ∈ 𝔤^c`, `‖Z‖ ≤ 2s`,
and `‖Z - ΣZ_k‖ ≤ 2C_Ψs² = 512s²`.
-/
import CoreLean.CloseTransports

open Matrix NormedSpace
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean
namespace ExpProducts

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

/-- **`cor:exp-products`**: for `Z_1, …, Z_m ∈ 𝔤^c` with `s = Σ‖Z_k‖ ≤ 2^{-10}`, `e^{iZ_1}⋯e^{iZ_m} = e^{iZ}` with
`Z ∈ 𝔤^c`, `‖Z‖ ≤ 2s`, and `‖Z - ΣZ_k‖ ≤ 512s²`. Induction on the factors from the right, `e^{iZ_1}e^{iW} = e^{iΨ(Z_1, W)}`,
with `‖Ψ(Z, W) - Z - W‖ ≤ 256‖Z‖‖W‖` (`psi_lipschitz` at the pairs `(Z, W)` and `(0, 0)`). -/
theorem exp_products {G : GaugeGroup N} (hG : G.LieInput) :
    ∀ l : List Mat, (∀ Y ∈ l, Y ∈ G.lieC) → (l.map norm).sum ≤ 1 / 1024 →
      ∃ Z ∈ G.lieC, expU (Complex.I • Z) = (l.map fun Y => expU (Complex.I • Y)).prod ∧
        ‖Z‖ ≤ 2 * (l.map norm).sum ∧ ‖Z - l.sum‖ ≤ 512 * (l.map norm).sum ^ 2
  | [], _, _ => ⟨0, GaugeGroup.lie_subset_lieC G.zero_mem_lie, by simp, by simp, by simp⟩
  | Y :: l, hC, hs => by
    have hsum : ((Y :: l).map norm).sum = ‖Y‖ + (l.map norm).sum := by simp
    have hs0 : 0 ≤ (l.map norm).sum := List.sum_nonneg fun a ha => by
      obtain ⟨b, -, rfl⟩ := List.mem_map.1 ha; exact norm_nonneg _
    have hY0 := norm_nonneg Y
    rw [hsum] at hs ⊢
    obtain ⟨W, hWC, hWe, hWn, hWerr⟩ := exp_products hG l (fun Z hZ => hC Z (List.mem_cons_of_mem _ hZ))
      (by linarith)
    set s := (l.map norm).sum
    have hW32 : ‖W‖ ≤ 1 / 32 := by linarith
    have hY32 : ‖Y‖ ≤ 1 / 32 := by linarith
    -- `‖Ψ(Y, W) - Y - W‖ ≤ 256‖W‖‖Y‖`
    have hlip := psi_lipschitz (X := 0) (Y := 0) (X' := Y) (Y' := W) (by simp) (by simp) hY32 hW32
    simp only [psi_zero_right (X := (0 : Mat)) (by simp), sub_zero, norm_zero, zero_mul, add_zero] at hlip
    have hl2 := Real.log_two_gt_d9
    refine ⟨psi Y W, psi_mem hG (hC Y List.mem_cons_self) hWC (by linarith), ?_, ?_, ?_⟩
    · rw [List.map_cons, List.prod_cons, ← hWe]
      exact (LatticeKappa.expU_mul_expU (A := Y) (B := W) (by linarith)).symm
    · have h1 : ‖psi Y W‖ ≤ ‖Y‖ + ‖W‖ + 256 * (‖W‖ * ‖Y‖) := by
        have := norm_add_le (psi Y W - Y - W) (Y + W)
        have e : psi Y W - Y - W + (Y + W) = psi Y W := by abel
        rw [e] at this
        linarith [norm_add_le Y W]
      have h2 : 256 * (‖W‖ * ‖Y‖) ≤ ‖Y‖ := by
        have : ‖W‖ ≤ 1 / 512 := by linarith
        nlinarith
      linarith
    · have e : psi Y W - (Y :: l).sum = (psi Y W - Y - W) + (W - l.sum) := by
        rw [List.sum_cons]; abel
      rw [e]
      calc ‖(psi Y W - Y - W) + (W - l.sum)‖ ≤ ‖psi Y W - Y - W‖ + ‖W - l.sum‖ := norm_add_le _ _
        _ ≤ 256 * (‖W‖ * ‖Y‖) + 512 * s ^ 2 := add_le_add hlip hWerr
        _ ≤ 256 * (2 * s * ‖Y‖) + 512 * s ^ 2 := by
          have := mul_le_mul_of_nonneg_right hWn hY0
          linarith
        _ ≤ 512 * (‖Y‖ + s) ^ 2 := by nlinarith

end ExpProducts
end CoreLean

end
