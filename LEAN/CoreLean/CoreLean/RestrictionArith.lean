/-
`lem:restriction` of BALABAN_CORE.tex (`a021c13be348`), the arithmetic of the gauges of (i) for `j' > j`. With
`λ = a_j/a_{j'} ≤ 1/L`, a box `□` of the side `s ≥ Ma_j` (at most `20LMa_j`) and the box `□'` of the side
`s' ≤ s + 2Ma_{j'}` of the cubes of `π_{j'}` meeting it: `s' ≤ 3λ⁻¹s` and `s' ≤ 20LMa_{j'}` for `L ≥ 2`
(`box_sides`), and the gauge bounds of `□'` at the scale `j'`, `a_{j'}‖A‖ ≤ (s'/a_{j'})B_rα₀` and
`a_{j'}²‖∇A‖ ≤ (s'/a_{j'})B_rα₀`, give `a_j‖A‖ ≤ 3λ(s/a_j)B_rα₀` and `a_j²‖∇A‖ ≤ 3λ²(s/a_j)B_rα₀` (`restriction_gauge`),
the constants `3λα₀` of `eq:restriction`.
-/
import Mathlib

noncomputable section

namespace CoreLean
namespace Restriction

/-- The sides of the boxes. -/
theorem box_sides {L M aj aj' s s' : ℝ} (hL : 2 ≤ L) (hM : 0 < M) (haj : 0 < aj) (hlam : L * aj ≤ aj')
    (hs : M * aj ≤ s) (hs20 : s ≤ 20 * L * M * aj) (hs' : s' ≤ s + 2 * M * aj') :
    s' ≤ 3 * (aj' / aj) * s ∧ s' ≤ 20 * L * M * aj' := by
  have haj' : 0 < aj' := lt_of_lt_of_le (by positivity) hlam
  have hq : 1 ≤ aj' / aj := by rw [le_div_iff₀ haj]; nlinarith
  constructor
  · have h1 : 2 * M * aj' ≤ 2 * (aj' / aj) * s := by
      have : M * aj' = (aj' / aj) * (M * aj) := by field_simp
      rw [show 2 * M * aj' = 2 * (M * aj') by ring, this]
      nlinarith
    have hs0 : 0 ≤ s := le_trans (by positivity) hs
    have : s ≤ (aj' / aj) * s := le_mul_of_one_le_left hs0 hq
    linarith
  · have h1 : s ≤ 20 * M * aj' := by nlinarith
    have hMa : 0 ≤ M * aj' := by positivity
    have : 22 * (M * aj') ≤ 20 * L * (M * aj') := mul_le_mul_of_nonneg_right (by linarith) hMa
    nlinarith

/-- The gauge bounds at the finer scale. -/
theorem restriction_gauge {aj aj' s s' Br α₀ nA nDA : ℝ} (haj : 0 < aj) (haj' : 0 < aj') (hBr : 0 ≤ Br * α₀)
    (hs'3 : s' ≤ 3 * (aj' / aj) * s) (hA : aj' * nA ≤ s' / aj' * (Br * α₀))
    (hDA : aj' ^ 2 * nDA ≤ s' / aj' * (Br * α₀)) :
    aj * nA ≤ 3 * (aj / aj') * (s / aj) * (Br * α₀) ∧
      aj ^ 2 * nDA ≤ 3 * (aj / aj') ^ 2 * (s / aj) * (Br * α₀) := by
  have hlam : 0 < aj / aj' := by positivity
  have key : s' / aj' * (Br * α₀) ≤ 3 * (s / aj) * (Br * α₀) := by
    have : s' / aj' ≤ 3 * (s / aj) := by
      rw [div_le_iff₀ haj']
      calc s' ≤ 3 * (aj' / aj) * s := hs'3
        _ = 3 * (s / aj) * aj' := by field_simp
    exact mul_le_mul_of_nonneg_right this hBr
  constructor
  · have e : aj * nA = (aj / aj') * (aj' * nA) := by field_simp
    rw [e]
    calc aj / aj' * (aj' * nA) ≤ aj / aj' * (3 * (s / aj) * (Br * α₀)) :=
          mul_le_mul_of_nonneg_left (hA.trans key) hlam.le
      _ = 3 * (aj / aj') * (s / aj) * (Br * α₀) := by ring
  · have e : aj ^ 2 * nDA = (aj / aj') ^ 2 * (aj' ^ 2 * nDA) := by field_simp
    rw [e]
    calc (aj / aj') ^ 2 * (aj' ^ 2 * nDA) ≤ (aj / aj') ^ 2 * (3 * (s / aj) * (Br * α₀)) :=
          mul_le_mul_of_nonneg_left (hDA.trans key) (by positivity)
      _ = 3 * (aj / aj') ^ 2 * (s / aj) * (Br * α₀) := by ring

end Restriction
end CoreLean

end
