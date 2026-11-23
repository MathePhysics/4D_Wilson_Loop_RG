/-
`lem:average-weighted`(iii) of BALABAN_CORE.tex (`a021c13be348`), the passage from the weighted norms to the entries, in
abstract form. If a linear map `𝒴` on the functions on `𝐁₁` (values in a normed space) satisfies
`ϖ(c)a_c‖(𝒴ν)(c)‖ ≤ K max_{c'}ϖ(c')a_{c'}³‖ν(c')‖` for every weight `ϖ` of the rate `θ` (here `θ = δ₀/8`), then its
entries satisfy `a_c‖𝒴[c, c']Z‖ ≤ Ka_{c'}³e^{-θd(c₋, c'₋)}‖Z‖`, by the weight `ϖ(y) = e^{θd(y, c'₋)}`, a weight by the
triangle inequality, and the function `ν` with the value `Z` at `c'` (`entry_from_weighted`); this is
`eq:block-entries` with `K = κ_bB_♯` for the scaled form. The conjugated operator is then bounded by `local_inverse_i`.
-/
import Mathlib

noncomputable section

namespace CoreLean
namespace AverageWeighted

variable {ι β V : Type*} [DecidableEq ι] [PseudoMetricSpace β] [NormedAddCommGroup V]

/-- **The entries from the weighted bound**. -/
theorem entry_from_weighted (pt : ι → β) (a : ι → ℝ) (ha : ∀ c, 0 < a c) (Y : (ι → V) → ι → V)
    {K θ : ℝ} (hθ : 0 ≤ θ)
    (hY : ∀ ϖ : β → ℝ, (∀ y, 0 < ϖ y) → (∀ y y', ϖ y ≤ Real.exp (θ * dist y y') * ϖ y') →
      ∀ (ν : ι → V) (N : ℝ), (∀ c', ϖ (pt c') * a c' ^ 3 * ‖ν c'‖ ≤ N) →
        ∀ c, ϖ (pt c) * a c * ‖Y ν c‖ ≤ K * N)
    (c c' : ι) (Z : V) :
    a c * ‖Y (Pi.single c' Z) c‖ ≤ K * a c' ^ 3 * Real.exp (-θ * dist (pt c) (pt c')) * ‖Z‖ := by
  set ϖ : β → ℝ := fun y => Real.exp (θ * dist y (pt c'))
  have hϖ : ∀ y, 0 < ϖ y := fun y => Real.exp_pos _
  have hrate : ∀ y y', ϖ y ≤ Real.exp (θ * dist y y') * ϖ y' := fun y y' => by
    simp only [ϖ, ← Real.exp_add, Real.exp_le_exp]
    have := dist_triangle y y' (pt c')
    nlinarith
  have hN : ∀ c'', ϖ (pt c'') * a c'' ^ 3 * ‖(Pi.single c' Z : ι → V) c''‖ ≤ a c' ^ 3 * ‖Z‖ := by
    intro c''
    by_cases h : c'' = c'
    · subst h; simp [ϖ]
    · simp [h]; exact mul_nonneg (pow_nonneg (ha c').le 3) (norm_nonneg Z)
  have := hY ϖ hϖ hrate (Pi.single c' Z) _ hN c
  have hpos : 0 < ϖ (pt c) := hϖ _
  have e : Real.exp (-θ * dist (pt c) (pt c')) * ϖ (pt c) = 1 := by
    simp only [ϖ, ← Real.exp_add]; rw [show -θ * dist (pt c) (pt c') + θ * dist (pt c) (pt c') = 0 by ring,
      Real.exp_zero]
  calc a c * ‖Y (Pi.single c' Z) c‖ = Real.exp (-θ * dist (pt c) (pt c')) *
        (ϖ (pt c) * a c * ‖Y (Pi.single c' Z) c‖) := by
        rw [← mul_assoc, ← mul_assoc, e, one_mul]
    _ ≤ Real.exp (-θ * dist (pt c) (pt c')) * (K * (a c' ^ 3 * ‖Z‖)) :=
        mul_le_mul_of_nonneg_left this (Real.exp_pos _).le
    _ = K * a c' ^ 3 * Real.exp (-θ * dist (pt c) (pt c')) * ‖Z‖ := by ring

end AverageWeighted
end CoreLean

end
