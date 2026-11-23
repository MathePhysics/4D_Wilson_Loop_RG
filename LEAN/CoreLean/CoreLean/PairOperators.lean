/-
`prop:pair-operators` of BALABAN_CORE.tex (`a021c13be348`), two steps of its proof in abstract form.
* *The lemma of Schwarz on the disc* (`schwarz_difference`): a holomorphic function of `z` on the disc `|z| < R`
  (`R = c_z/α₁`), with values in a complex normed space and bounded there by `B`, has `‖f(1) - f(0)‖ ≤ 2B/R` for
  `R > 1`; the core applies it to the conjugated scaled forms `𝒯(z)` with `B = C_SB_g`, which gives the bound
  `2C_SB_gα₁/c_z` of `𝒯(1) - 𝒯(0)`.
* *From the entries to the weighted norm* (`weighted_from_entries`): entries
  `‖𝒴⁻¹[c, c']‖ ≤ B_ba_c^{-3}a_{c'}e^{-θd(c₋, c'₋)}`, a weight of a rate at most `θ/2`, and the sum
  `Σ_{c'}e^{-(θ/2)d(c₋, c'₋)} ≤ c₁` give `ϖ(c)a_c³‖(𝒴⁻¹ν)(c)‖ ≤ B_bc₁‖ϖν‖_{∞,(-1)}`, the bound
  `‖ϖ𝒴⁻¹ν‖_{∞,(-3)} ≤ C_inv‖ϖν‖_{∞,(-1)}` of (ii).
-/
import Mathlib

open Complex Metric Set

noncomputable section

namespace CoreLean
namespace PairOperators

/-- **The lemma of Schwarz on the disc**: `‖f(1) - f(0)‖ ≤ 2B/R`. -/
theorem schwarz_difference {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : ℂ → E} {R B : ℝ}
    (hR : 1 < R) (hd : DifferentiableOn ℂ f (ball 0 R)) (hb : ∀ z ∈ ball (0 : ℂ) R, ‖f z‖ ≤ B) :
    ‖f 1 - f 0‖ ≤ 2 * B / R := by
  have hR0 : 0 < R := by linarith
  have hmaps : MapsTo f (ball 0 R) (closedBall (f 0) (2 * B)) := fun z hz => by
    rw [mem_closedBall, dist_eq_norm]
    calc ‖f z - f 0‖ ≤ ‖f z‖ + ‖f 0‖ := norm_sub_le _ _
      _ ≤ B + B := add_le_add (hb z hz) (hb 0 (mem_ball_self hR0))
      _ = 2 * B := by ring
  have h1 : (1 : ℂ) ∈ ball (0 : ℂ) R := by rw [mem_ball, dist_zero_right, norm_one]; exact hR
  have hs := Complex.norm_dslope_le_div_of_mapsTo_ball hd hmaps h1
  have e : f 1 - f 0 = dslope f 0 1 := by
    have := sub_smul_dslope f 0 1
    rw [sub_zero, one_smul] at this
    exact this.symm
  rw [e]; exact hs

/-- **From the entries to the weighted norm**. -/
theorem weighted_from_entries {ι β : Type*} [Fintype ι] (pt : ι → β) (d : β → β → ℝ) (a : ι → ℝ)
    (ha : ∀ c, 0 < a c) (Y : ι → ι → ℝ) (ν : ι → ℝ) (hν : ∀ c, 0 ≤ ν c) {Bb θ c₁ N : ℝ} (hBb : 0 ≤ Bb)
    (hY : ∀ c c', |Y c c'| ≤ Bb * (a c)⁻¹ ^ 3 * a c' * Real.exp (-θ * d (pt c) (pt c')))
    (ϖ : ι → ℝ) (hϖ : ∀ c, 0 < ϖ c) (hrate : ∀ c c', ϖ c ≤ Real.exp (θ / 2 * d (pt c) (pt c')) * ϖ c')
    (hsum : ∀ c, ∑ c', Real.exp (-(θ / 2) * d (pt c) (pt c')) ≤ c₁) (hN : ∀ c', ϖ c' * a c' * ν c' ≤ N)
    (c : ι) : ϖ c * a c ^ 3 * |∑ c', Y c c' * ν c'| ≤ Bb * c₁ * N := by
  have hac := ha c
  have hN0 : 0 ≤ N := le_trans (mul_nonneg (mul_nonneg (hϖ c).le (ha c).le) (hν c)) (hN c)
  have hterm : ∀ c', ϖ c * a c ^ 3 * |Y c c' * ν c'| ≤ Bb * N * Real.exp (-(θ / 2) * d (pt c) (pt c')) := by
    intro c'
    rw [abs_mul, abs_of_nonneg (hν c')]
    have hE : Real.exp (θ / 2 * d (pt c) (pt c')) * Real.exp (-θ * d (pt c) (pt c')) =
        Real.exp (-(θ / 2) * d (pt c) (pt c')) := by rw [← Real.exp_add]; congr 1; ring
    calc ϖ c * a c ^ 3 * (|Y c c'| * ν c')
        ≤ ϖ c * a c ^ 3 * (Bb * (a c)⁻¹ ^ 3 * a c' * Real.exp (-θ * d (pt c) (pt c')) * ν c') :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hY c c') (hν c'))
            (mul_nonneg (hϖ c).le (pow_pos hac 3).le)
      _ = Bb * Real.exp (-θ * d (pt c) (pt c')) * (ϖ c * (a c' * ν c')) := by
          field_simp
      _ ≤ Bb * Real.exp (-θ * d (pt c) (pt c')) *
            (Real.exp (θ / 2 * d (pt c) (pt c')) * ϖ c' * (a c' * ν c')) := by
          gcongr
          · exact mul_nonneg (ha c').le (hν c')
          · exact hrate c c'
      _ = Bb * (Real.exp (θ / 2 * d (pt c) (pt c')) * Real.exp (-θ * d (pt c) (pt c'))) *
            (ϖ c' * a c' * ν c') := by ring
      _ ≤ Bb * Real.exp (-(θ / 2) * d (pt c) (pt c')) * N := by
          rw [hE]; exact mul_le_mul_of_nonneg_left (hN c') (by positivity)
      _ = Bb * N * Real.exp (-(θ / 2) * d (pt c) (pt c')) := by ring
  calc ϖ c * a c ^ 3 * |∑ c', Y c c' * ν c'| ≤ ϖ c * a c ^ 3 * ∑ c', |Y c c' * ν c'| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (mul_nonneg (hϖ c).le (pow_pos hac 3).le)
    _ = ∑ c', ϖ c * a c ^ 3 * |Y c c' * ν c'| := Finset.mul_sum _ _ _
    _ ≤ ∑ c', Bb * N * Real.exp (-(θ / 2) * d (pt c) (pt c')) := Finset.sum_le_sum fun c' _ => hterm c'
    _ = Bb * N * ∑ c', Real.exp (-(θ / 2) * d (pt c) (pt c')) := (Finset.mul_sum _ _ _).symm
    _ ≤ Bb * N * c₁ := mul_le_mul_of_nonneg_left (hsum c) (mul_nonneg hBb hN0)
    _ = Bb * c₁ * N := by ring

end PairOperators
end CoreLean

end
