/-
`prop:step-interpolations` of BALABAN_CORE.tex (`a021c13be348`), the first two terms of `eq:step-interpolations`:
`lem:interpolation` (`Interpolation.lean`) for the families `t ↦ 𝖨(1, t)` and `s ↦ 𝖨(s, 0)`, whose exponents `f(s, t)` have
the derivatives `Θ_𝐁` in `t` and `Θ_𝐑` in `s`, gives
`log 𝖨(1, 1) - log 𝖨(0, 0) = ∫_0^1⟨Θ_𝐁⟩_{1,t} dt + ∫_0^1⟨Θ_𝐑⟩_{s,0} ds` (`two_interpolations`), the expectations being those of
the normalised integrands.
-/
import CoreLean.Interpolation

open MeasureTheory Set

noncomputable section

namespace CoreLean
namespace StepInterpolations

variable {α : Type*} [MeasurableSpace α]

/-- **The first two terms of `eq:step-interpolations`**. -/
theorem two_interpolations (μ : Measure α) [IsFiniteMeasure μ] (hμ : μ ≠ 0) (f : ℝ → ℝ → α → ℝ)
    (ΘB ΘR : ℝ → α → ℝ) (M MB MR : ℝ)
    (hmB : ∀ t ∈ Icc (0 : ℝ) 1, Measurable (f 1 t)) (hmR : ∀ s ∈ Icc (0 : ℝ) 1, Measurable (f s 0))
    (hbB : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, |f 1 t x| ≤ M) (hbR : ∀ s ∈ Icc (0 : ℝ) 1, ∀ x, |f s 0 x| ≤ M)
    (hdB : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, HasDerivWithinAt (fun t' => f 1 t' x) (ΘB t x) (Icc 0 1) t)
    (hdR : ∀ s ∈ Icc (0 : ℝ) 1, ∀ x, HasDerivWithinAt (fun s' => f s' 0 x) (ΘR s x) (Icc 0 1) s)
    (hbB' : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, |ΘB t x| ≤ MB) (hbR' : ∀ s ∈ Icc (0 : ℝ) 1, ∀ x, |ΘR s x| ≤ MR) :
    Real.log (∫ x, Real.exp (f 1 1 x) ∂μ) - Real.log (∫ x, Real.exp (f 0 0 x) ∂μ) =
      (∫ t in (0 : ℝ)..1, (∫ x, ΘB t x * Real.exp (f 1 t x) ∂μ) / (∫ x, Real.exp (f 1 t x) ∂μ)) +
      (∫ s in (0 : ℝ)..1, (∫ x, ΘR s x * Real.exp (f s 0 x) ∂μ) / (∫ x, Real.exp (f s 0 x) ∂μ)) := by
  have h1 := interpolation μ hμ (fun t => f 1 t) ΘB M MB hmB hbB hdB hbB'
  have h2 := interpolation μ hμ (fun s => f s 0) ΘR M MR hmR hbR hdR hbR'
  rw [← h1, ← h2]
  ring

end StepInterpolations
end CoreLean

end
