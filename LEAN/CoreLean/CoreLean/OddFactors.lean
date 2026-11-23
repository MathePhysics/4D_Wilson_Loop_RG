/-
`lem:odd-factors` of BALABAN_CORE.tex (`a021c13be348`), in abstract form. The activity of the odd part of the marked
factor, as a function of the parameter `u` of the potentials `𝐕^{ev} + u𝐕^{od}`, is holomorphic on `|u| < R'`, bounded
there by the right side `B` of `eq:marked-activity-bound`, and odd (`lem:activity-parameters`(i)); hence it vanishes at
`0`, and `‖H(1)‖ ≤ B/R'  ≤ B/R` (`odd_bound`, by Schwarz's lemma, where the core writes `H(u) = ug(u)` and applies the
maximum principle to `g`). With the activity linear in the marked factor, `H = H(𝒳^{ev}) + H(𝒳^{od})`, and the bound
`B(‖𝒳‖) = ‖𝒳‖·b` linear in the factor, `‖H‖ ≤ (‖𝒳^{ev}‖ + R⁻¹‖𝒳^{od}‖)b` (`odd_factors`). The bounds of the activities
themselves (`lem:marked-activity`) and the parity (`lem:activity-parameters`) are the hypotheses.
-/
import Mathlib

open Complex Metric Set

noncomputable section

namespace CoreLean
namespace OddFactors

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- An odd function holomorphic on `|u| < R'` and bounded there by `B` has `‖H(1)‖ ≤ B/R` for `1 ≤ R < R'`. -/
theorem odd_bound {H : ℂ → E} {R R' B : ℝ} (hR : 1 ≤ R) (hRR' : R < R')
    (hd : DifferentiableOn ℂ H (ball 0 R')) (hb : ∀ u ∈ ball (0 : ℂ) R', ‖H u‖ ≤ B)
    (hodd : ∀ u, H (-u) = -H u) : ‖H 1‖ ≤ B / R := by
  have h0 : H 0 = 0 := by
    have := hodd 0
    rw [neg_zero] at this
    have h2 : (2 : ℂ) • H 0 = 0 := by
      rw [two_smul]
      calc H 0 + H 0 = -H 0 + H 0 := by rw [← this]
        _ = 0 := neg_add_cancel _
    exact (smul_eq_zero.1 h2).resolve_left two_ne_zero
  have hR'0 : 0 < R' := by linarith
  have hB : 0 ≤ B := (norm_nonneg _).trans (hb 0 (mem_ball_self hR'0))
  have hmaps : MapsTo H (ball 0 R') (closedBall (H 0) B) := fun u hu => by
    rw [h0, mem_closedBall, dist_zero_right]; exact hb u hu
  have h1 : (1 : ℂ) ∈ ball (0 : ℂ) R' := by
    rw [mem_ball, dist_zero_right, norm_one]; linarith
  have hs := Complex.norm_dslope_le_div_of_mapsTo_ball hd hmaps h1
  have e : H 1 = dslope H 0 1 := by
    have := sub_smul_dslope H 0 1
    rw [sub_zero, one_smul, h0, sub_zero] at this
    exact this.symm
  rw [e]
  refine hs.trans ?_
  exact div_le_div_of_nonneg_left hB (by linarith) hRR'.le

/-- **`lem:odd-factors`**: the activity of the marked factor `𝒳 = 𝒳^{ev} + 𝒳^{od}` is at most
`(‖𝒳^{ev}‖ + R⁻¹‖𝒳^{od}‖)b`, when the activity of `𝒳^{ev}` is at most `‖𝒳^{ev}‖b` and that of `𝒳^{od}`, as a function
of the parameter `u`, is odd, holomorphic on `|u| < R'`, and at most `‖𝒳^{od}‖b` there. -/
theorem odd_factors {Hev : E} {Hod : ℂ → E} {R R' b xev xod : ℝ} (hR : 1 ≤ R) (hRR' : R < R')
    (hev : ‖Hev‖ ≤ xev * b) (hd : DifferentiableOn ℂ Hod (ball 0 R'))
    (hb : ∀ u ∈ ball (0 : ℂ) R', ‖Hod u‖ ≤ xod * b) (hodd : ∀ u, Hod (-u) = -Hod u) :
    ‖Hev + Hod 1‖ ≤ (xev + R⁻¹ * xod) * b := by
  have h := odd_bound hR hRR' hd hb hodd
  calc ‖Hev + Hod 1‖ ≤ ‖Hev‖ + ‖Hod 1‖ := norm_add_le _ _
    _ ≤ xev * b + xod * b / R := add_le_add hev h
    _ = (xev + R⁻¹ * xod) * b := by field_simp

end OddFactors
end CoreLean

end
