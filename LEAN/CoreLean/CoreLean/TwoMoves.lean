/-
`lem:two-moves` of BALABAN_CORE.tex (`a021c13be348`), the identity `eq:entry-size` in abstract form. With the expansion
of the current of a move of the base, `J(e^{ia₀𝔶}W₀) = J(W₀) + D^*_{W₀}D_{W₀}𝔶 + 𝐅(W₀, 𝔶)` (`eq:current-expansion`),
for the two moves `𝔶` and `𝔶'` the current of `W₀` cancels and
`J(e^{ia₀𝔶}W₀) - J(e^{ia₀𝔶'}W₀) = D^*_UK + p` with `K = D_{W₀}(𝔶 - 𝔶')` and
`p = (D^*_{W₀} - D^*_U)K + 𝐅(W₀, 𝔶) - 𝐅(W₀, 𝔶')` (`entry_size`).
-/
import Mathlib

noncomputable section

namespace CoreLean
namespace TwoMoves

variable {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]

/-- **`eq:entry-size`**. -/
theorem entry_size (J : X → X) (DW : X →+ Y) (DWs DUs : Y →+ X) (F : X → X) (J₀ : X)
    (hJ : ∀ 𝔶, J 𝔶 = J₀ + DWs (DW 𝔶) + F 𝔶) (𝔶 𝔶' : X) :
    J 𝔶 - J 𝔶' = DUs (DW (𝔶 - 𝔶')) + ((DWs (DW (𝔶 - 𝔶')) - DUs (DW (𝔶 - 𝔶'))) + (F 𝔶 - F 𝔶')) := by
  rw [hJ, hJ]
  simp only [map_sub]
  abel

end TwoMoves
end CoreLean

end
