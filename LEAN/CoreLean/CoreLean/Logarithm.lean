/-
`lem:logarithm` of BALABAN_CORE.tex (`0d76a9bf9596`), in the core's form, from the results of `lem:chart` of the earlier
numbering (`ChartLog.lean`, `ChartLocal.lean`, `ChartBounds.lean`), the logarithm series of the BCH library, and
`carrier_le_complexified`.
-/
import CoreLean.AverageHolo
import CoreLean.ChartBounds

open Matrix NormedSpace Filter Topology Metric
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean
namespace Logarithm

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

/-- **`lem:logarithm`**: (i) `log` is holomorphic on `{‖W - id‖ < 1}`, `‖log W‖ ≤ -log(1 - ‖W - id‖)`, `e^{log W} = W`,
`log e^{iX} = iX` for `‖X‖ < log 2`, and `log(uWu⁻¹) = Ad_u log W`; (ii) there is `r_G ∈ (0, 1)` with every `W ∈ G`,
`‖W - id‖ ≤ r_G`, equal to `e^{iA}` with `A ∈ 𝔤`, `‖A‖ < log 2`, and `log W = iA`, and a connected `G` lies in `G^c`;
(iii) for Hermitean `X` with `‖X‖ ≤ π`, `‖e^{iX} - id‖ ≤ ‖X‖ ≤ (π/2)‖e^{iX} - id‖`, and the same in the Hilbert–Schmidt
norm. -/
theorem logarithm (G : GaugeGroup N) (hG : IsClosed G.mats) :
    (AnalyticOnNhd ℂ (LogM (N := N)) {W | ‖W - 1‖ < 1} ∧
      (∀ W : Mat, ‖W - 1‖ < 1 → ‖LogM W‖ ≤ -Real.log (1 - ‖W - 1‖) ∧ exp (LogM W) = W) ∧
      (∀ X : Mat, ‖X‖ < Real.log 2 → LogM (exp (Complex.I • X)) = Complex.I • X) ∧
      (∀ (u : GLN) (W : Mat), LogM (Ad u W) = Ad u (LogM W))) ∧
    (∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∀ U ∈ G.carrier, ‖(U : Mat) - 1‖ ≤ r →
        ∃ A ∈ G.lie, exp (Complex.I • A) = (U : Mat) ∧ ‖A‖ < Real.log 2 ∧ LogM (U : Mat) = Complex.I • A) ∧
    (IsConnected (G.carrier : Set GLN) → G.carrier ≤ G.complexified) ∧
    (∀ X : Mat, X.IsHermitian → ‖X‖ ≤ Real.pi →
      ‖exp (Complex.I • X) - 1‖ ≤ ‖X‖ ∧ ‖X‖ ≤ Real.pi / 2 * ‖exp (Complex.I • X) - 1‖ ∧
        hs (exp (Complex.I • X) - 1) ≤ hs X ∧ hs X ≤ Real.pi / 2 * hs (exp (Complex.I • X) - 1)) := by
  refine ⟨⟨analyticOnNhd_LogM, fun W hW => ⟨?_, exp_LogM hW⟩, fun X hX => ?_, fun u W => LogM_conj u W⟩, ?_,
    AverageHolo.carrier_le_complexified G hG, fun X hX hXn => ChartBounds.chart_iii hX hXn⟩
  · exact BakerCampbellHausdorff.norm_log1p_le hW
  · refine LogM_exp ?_
    rw [norm_smul, Complex.norm_I, one_mul]; exact hX
  · obtain ⟨r, hr0, hr1, hch⟩ := GaugeGroup.chart_ii (G := G) hG
    refine ⟨min r (2 / 5), lt_min hr0 (by norm_num), lt_of_le_of_lt (min_le_left _ _) hr1, fun U hU hUr => ?_⟩
    obtain ⟨A, hA, hAn, hAe, hAl, -⟩ := hch U hU (hUr.trans (min_le_left _ _))
    refine ⟨A, hA, hAe, ?_, hAl⟩
    have hherm : A.IsHermitian := hA.1
    have h3 := (ChartBounds.chart_iii hherm hAn.le).2.1
    rw [hAe] at h3
    have hpi := Real.pi_lt_d2
    have hlog := Real.log_two_gt_d9
    have hU' : ‖(U : Mat) - 1‖ ≤ 2 / 5 := hUr.trans (min_le_right _ _)
    nlinarith [norm_nonneg ((U : Mat) - 1)]

end Logarithm
end CoreLean

end
