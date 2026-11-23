/-
`prop:far-terms` of BALABAN_CORE.tex (`a021c13be348`), in abstract form. The term `t_□ ↦ 𝐄(X, (e^{ia₀𝐀}𝐔, 𝐉'), z)`,
`𝐀 = 𝐀₀ + t_□δ𝐀`, is holomorphic on a neighbourhood of the closed disc `|t_□| ≤ r` and bounded there by `E₀e^{-κd_j(X)}`
(`prop:space-stability`(ii), the hypothesis here); Cauchy's estimate for the derivative at the centre gives
`|∂_{t_□}𝐄|_{t_□ = 0}| ≤ r⁻¹E₀e^{-κd_j(X)}` (`far_term`, `eq:far-term`). Not formalised: the holomorphy of the
derivative in the other variables, the bound of the disc (`prop:space-stability`(ii)), and the two special cases.
-/
import Mathlib

open Complex Metric

noncomputable section

namespace CoreLean
namespace FarTerms

/-- **`eq:far-term`**: Cauchy's estimate at the centre of the disc of the radius `r`. -/
theorem far_term {f : ℂ → ℂ} {r E₀ κ d : ℝ} (hr : 0 < r) (hf : DiffContOnCl ℂ f (ball 0 r))
    (hb : ∀ t ∈ sphere (0 : ℂ) r, ‖f t‖ ≤ E₀ * Real.exp (-κ * d)) :
    ‖deriv f 0‖ ≤ 1 / r * (E₀ * Real.exp (-κ * d)) := by
  have := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr hf hb
  rwa [div_eq_inv_mul, ← one_div] at this

end FarTerms
end CoreLean

end
