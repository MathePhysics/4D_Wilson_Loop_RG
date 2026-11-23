/-
`lem:minimiser-function`(iii) of BALABAN_CORE.tex (`a021c13be348`), the algebra of `eq:transform-base`, with the gauge
action of `GaugedCovariance.lean`. If `W = c^g` and `U_{Y'}(𝖵_W) = c^{ḡ}` (the covariance of the minimiser,
`lem:complex-minimisers`(iii), with `ḡ(x) = g(y)` on the block of `y ∈ 𝐁'`), then `W = U_{Y'}(𝖵_W)^{g₀}` with
`g₀ = gḡ⁻¹` (`transform_base`), and `g₀` is trivial at the points of `𝐁'`, where `ḡ = g` (`g0_trivial`).
-/
import CoreLean.GaugedCovariance

noncomputable section

namespace CoreLean
namespace MinimiserFunction

open GaugedCovariance

variable {G X B : Type*} [Group G]

/-- **`eq:transform-base`**: `W = c^g = (c^{ḡ})^{gḡ⁻¹}`. -/
theorem transform_base (src tgt : B → X) (c : B → G) (g gbar : X → G) {W Umin : B → G}
    (hW : W = gauge src tgt c g) (hU : Umin = gauge src tgt c gbar) :
    W = gauge src tgt Umin (fun x => g x * (gbar x)⁻¹) := by
  rw [hW, hU, gauge_gauge]
  congr 1
  funext x
  group

/-- `g₀ = gḡ⁻¹` is trivial where `ḡ = g`. -/
theorem g0_trivial (g gbar : X → G) {y : X} (hy : gbar y = g y) : g y * (gbar y)⁻¹ = 1 := by
  rw [hy, mul_inv_cancel]

end MinimiserFunction
end CoreLean

end
