/-
`lem:pair-disc`(ii) of BALABAN_CORE.tex (`a021c13be348`), on the lattice of `MovedPlaquette.lean`. For a plaquette `p`
of `Ω_j` with `|U(∂p) - id| ≤ ε_p(a₀/a_j)²`, a form with `a_j‖zA'‖ ≤ L|z|α₁` at the four bonds and
`a_j²‖∇(zA')‖ ≤ L²|z|α₁` (`eq:regular-complex` for the index `j - 1`), `√Nε_p ≤ 1/512` and `L²|z|α₁ ≤ 1/512`:
`‖𝐔_z(∂p) - id‖ ≤ (√Nε_p + 10L²|z|α₁)(a₀/a_j)² ≤ ¼(a₀/a_j)²` (`pair_disc_plaquette`), by `cor:moved-plaquette`
(`moved_plaquette`) and `‖·‖ ≤ √N|·|` (`lem:norms`(i)).
-/
import CoreLean.MovedPlaquette

open Matrix NormedSpace
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean
namespace MovedPlaquette

open LatticePaths LatticeKappa RegularAverages

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

variable {n : ℕ} [NeZero n]

/-- **`lem:pair-disc`(ii)**. -/
theorem pair_disc_plaquette (G : GaugeGroup N) (hN : 1 ≤ N) (U : Config N n) (hU : IsGField G U)
    (A : Fin 4 → Site n → Mat) (μ ν : Fin 4) (x : Site n) {η a L t εp : ℝ} (hη : 0 < η) (ha : η ≤ a)
    (hL : 1 ≤ L) (ht : 0 ≤ t) (hεp : 0 ≤ εp)
    (hP : hs (((plaq U μ ν x : GLN) : Mat) - 1) ≤ εp * (η / a) ^ 2)
    (hA1 : a * ‖A μ x‖ ≤ L * t) (hA2 : a * ‖A ν (x + unit n μ)‖ ≤ L * t)
    (hA3 : a * ‖A μ (x + unit n ν)‖ ≤ L * t) (hA4 : a * ‖A ν x‖ ≤ L * t)
    (hD1 : a ^ 2 * ‖Dcov U A η μ ν x‖ ≤ L ^ 2 * t) (hD2 : a ^ 2 * ‖Dcov U A η ν μ x‖ ≤ L ^ 2 * t)
    (hsm : Real.sqrt N * εp ≤ 1 / 512) (hρs : L ^ 2 * t ≤ 1 / 512) :
    ‖((plaq (move U A η) μ ν x : GLN) : Mat) - 1‖ ≤ (Real.sqrt N * εp + 10 * (L ^ 2 * t)) * (η / a) ^ 2 ∧
      (Real.sqrt N * εp + 10 * (L ^ 2 * t)) * (η / a) ^ 2 ≤ 1 / 4 * (η / a) ^ 2 := by
  have hLt : L * t ≤ L ^ 2 * t := by
    have : L ≤ L ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_right this ht
  have hρ : 0 ≤ L ^ 2 * t := by positivity
  have hM := (moved_plaquette G hN U hU A μ ν x hη ha hεp hρ hP (hA1.trans hLt) (hA2.trans hLt)
    (hA3.trans hLt) (hA4.trans hLt) hD1 hD2 hsm hρs).2
  have hU1 : ‖((plaq U μ ν x : GLN) : Mat) - 1‖ ≤ Real.sqrt N * (εp * (η / a) ^ 2) :=
    (opNorm_le_sqrt_mul_hs _).trans (mul_le_mul_of_nonneg_left hP (Real.sqrt_nonneg _))
  constructor
  · calc ‖((plaq (move U A η) μ ν x : GLN) : Mat) - 1‖
        = ‖(((plaq (move U A η) μ ν x : GLN) : Mat) - ((plaq U μ ν x : GLN) : Mat)) +
            (((plaq U μ ν x : GLN) : Mat) - 1)‖ := by congr 1; abel
      _ ≤ ‖((plaq (move U A η) μ ν x : GLN) : Mat) - ((plaq U μ ν x : GLN) : Mat)‖ +
            ‖((plaq U μ ν x : GLN) : Mat) - 1‖ := norm_add_le _ _
      _ ≤ 10 * (L ^ 2 * t) * (η / a) ^ 2 + Real.sqrt N * (εp * (η / a) ^ 2) := add_le_add hM hU1
      _ = (Real.sqrt N * εp + 10 * (L ^ 2 * t)) * (η / a) ^ 2 := by ring
  · have h : Real.sqrt N * εp + 10 * (L ^ 2 * t) ≤ 1 / 4 := by linarith
    exact mul_le_mul_of_nonneg_right h (sq_nonneg _)

end MovedPlaquette
end CoreLean

end
