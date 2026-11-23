/-
`prop:far-fields` of BALABAN_CORE.tex (`a021c13be348`), the step `eq:far-data-derivative` of its proof: the function
`t_□ ↦ B(t, t_□)(c')` is holomorphic on the disc of the radius `ρ_{c'} = ½r_c/(a_{i'}‖ζ_□𝓗_n‖_{∞,𝖡_{c'}})` and bounded
by `1` there, so that Cauchy's estimate gives `‖∂_{t_□}B(t, t_□)(c')|_{t_□ = 0}‖ ≤ 1/ρ_{c'} ≤ (2/r_c)a_j‖ζ_□𝓗_n‖_∞`, the
units satisfying `a_{i'} ≤ a_j` and the supremum over `𝖡_{c'}` being at most the global one (`far_data_derivative`).
-/
import CoreLean.CauchyBanach

open Metric

noncomputable section

namespace CoreLean
namespace FarFields

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- **`eq:far-data-derivative`**. -/
theorem far_data_derivative {g : ℂ → V} {rc ai aj hloc hglob : ℝ} (hrc : 0 < rc) (hai : 0 < ai) (haij : ai ≤ aj)
    (hloc0 : 0 < hloc) (hlg : hloc ≤ hglob)
    (hd : DifferentiableOn ℂ g (ball 0 (rc / 2 / (ai * hloc)))) (hb : ∀ z ∈ ball (0 : ℂ) (rc / 2 / (ai * hloc)), ‖g z‖ ≤ 1) :
    ‖deriv g 0‖ ≤ 2 / rc * (aj * hglob) := by
  have hρ : 0 < rc / 2 / (ai * hloc) := by positivity
  have haj : 0 ≤ aj := le_trans hai.le haij
  have h := CauchyBanach.norm_deriv_le_of_ball hρ hd hb
  calc ‖deriv g 0‖ ≤ 1 / (rc / 2 / (ai * hloc)) := h
    _ = 2 / rc * (ai * hloc) := by field_simp
    _ ≤ 2 / rc * (aj * hglob) := by gcongr

end FarFields
end CoreLean

end
