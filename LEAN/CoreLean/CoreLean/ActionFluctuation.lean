/-
`prop:action-fluctuation` of BALABAN_CORE.tex (`a021c13be348`), the algebra of `eq:action-fluctuation`. With the
expansion of the action at the move by `X` (`lem:functional`), `A(e^{ia₀X}U) = A(U) + ⟨X, J⟩ + ½⟨X, KX⟩ + 𝖵_π(X)`,
`K = Δ(U) - Δ'_π - Δ^{(2)}_π` symmetric, at `X = Y + Z` with `Y = H₁𝔟` and `Z = 𝒜₁`:

* the cross terms vanish, `⟨Z, J⟩ = 0` and `⟨Z, KY⟩ = 0`, because `QZ = 0` while `J = Q^*μ` (`lem:critical-current`) and
  `KY = G₁^{-1}H₁𝔟 = Q^*(QG₁Q^*)^{-1}𝔟` lie in the range of `Q^*` (`cross_vanish`);
* hence `A = A(U) + ⟨Y, J⟩ + ½⟨Y, KY⟩ + 𝖶`, `𝖶 = ½⟨Z, KZ⟩ + 𝖵_π(Y + Z)` (`action_split`), which is
  `eq:action-fluctuation` with `eq:fluctuation-potential`.
-/
import Mathlib

open scoped InnerProductSpace

noncomputable section

namespace CoreLean
namespace ActionFluctuation

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F]

/-- **The cross terms vanish**. -/
theorem cross_vanish (Q : E →L[ℝ] F) (Qs : F →L[ℝ] E) (hQ : ∀ u w, ⟪Q u, w⟫_ℝ = ⟪u, Qs w⟫_ℝ) (K : E →L[ℝ] E)
    {J Y Z : E} {μ ν : F} (hJ : J = Qs μ) (hKY : K Y = Qs ν) (hZ : Q Z = 0) :
    ⟪Z, J⟫_ℝ = 0 ∧ ⟪Z, K Y⟫_ℝ = 0 := by
  constructor
  · rw [hJ, ← hQ, hZ, inner_zero_left]
  · rw [hKY, ← hQ, hZ, inner_zero_left]

/-- **`eq:action-fluctuation`**. -/
theorem action_split (K : E →L[ℝ] E) (hK : ∀ u v, ⟪u, K v⟫_ℝ = ⟪K u, v⟫_ℝ) (Vπ : E → ℝ) {A A₀ : ℝ} {J Y Z : E}
    (hA : A = A₀ + ⟪Y + Z, J⟫_ℝ + 1 / 2 * ⟪Y + Z, K (Y + Z)⟫_ℝ + Vπ (Y + Z))
    (hZJ : ⟪Z, J⟫_ℝ = 0) (hZKY : ⟪Z, K Y⟫_ℝ = 0) :
    A = A₀ + ⟪Y, J⟫_ℝ + 1 / 2 * ⟪Y, K Y⟫_ℝ + (1 / 2 * ⟪Z, K Z⟫_ℝ + Vπ (Y + Z)) := by
  have hYKZ : ⟪Y, K Z⟫_ℝ = 0 := by rw [hK, real_inner_comm, hZKY]
  rw [hA]
  simp only [map_add, inner_add_left, inner_add_right, hZJ, hZKY, hYKZ]
  ring

end ActionFluctuation
end CoreLean

end
