/-
`lem:divergence-sources`(i) of BALABAN_CORE.tex (`a021c13be348`), the identity, in the lattice model of
`InteriorSetup.lean` (`ηℤ⁴ = ℤ⁴`, `𝐔 = e^{iη𝐚}`): for a `0`-form `ψ` and a direction `μ`,
`D_{𝐔,μ}ψ = D^*_{𝐔,μ}φ_μ` with `φ_μ(x) = -Ad_{𝐔(x, x + a₀e_μ)}ψ(x + a₀e_μ)` (`divergence_identity`), because the
transport back along a bond undoes the transport forward.
-/
import CoreLean.InteriorSetup

open Matrix NormedSpace

noncomputable section

namespace CoreLean
namespace InteriorSchauder

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ

/-- The form `φ_μ(x) = -Ad_{𝐔(x, x + e_μ)}ψ(x + e_μ)`. -/
def phiForm (η : ℝ) (A : Fin 4 → (Fin 4 → ℤ) → Mat) (μ : Fin 4) (ψ : (Fin 4 → ℤ) → Mat) (n : Fin 4 → ℤ) : Mat :=
  -Ad (Uf η A μ n) (ψ (n + e4 μ))

/-- **`lem:divergence-sources`(i)**: `D_μψ = D^*_μφ_μ`. -/
theorem divergence_identity (η : ℝ) (A : Fin 4 → (Fin 4 → ℤ) → Mat) (μ : Fin 4) (ψ : (Fin 4 → ℤ) → Mat)
    (n : Fin 4 → ℤ) : Dfw η A μ ψ n = Dbw η A μ (phiForm η A μ ψ) n := by
  unfold Dfw Dbw phiForm
  have h := Ad_Ub_Ad_Uf η A μ (n - e4 μ) (ψ (n - e4 μ + e4 μ))
  rw [sub_add_cancel] at h
  rw [Ad_neg, sub_add_cancel, h]
  congr 1
  abel

end InteriorSchauder
end CoreLean

end
