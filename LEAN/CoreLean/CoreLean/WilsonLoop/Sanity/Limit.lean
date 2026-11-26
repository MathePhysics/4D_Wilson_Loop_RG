import CoreLean.WilsonLoop.Statement

/-!
# The limit follows from the conclusions of `BoundAndLimit`

[WL] Theorem 1.5 continues "In particular the limit `W(𝒞) = lim W_K(𝒞)` exists"
(`eq:main-limit`, l.170-173), and [WL] `prop:nonvanishing` continues "so that `|W(𝒞)| ≥ 1/2`"
(`eq:nonvanishing-bound`, l.5315).  `CoreLean.WilsonLoop.BoundAndLimit` states neither, because both
follow from what it does state.  This file proves the implications for an arbitrary sequence,
in the form in which `BoundAndLimit` states its conclusions.

## Main statements

* `CoreLean.WilsonLoop.MainBound.exists_limit`: the limit exists.
* `CoreLean.WilsonLoop.MainBound.norm_le_of_tendsto`: the limit is bounded by `B`.
* `CoreLean.WilsonLoop.half_le_norm_of_tendsto`: the lower bound `1/2` passes to the limit.
-/

namespace CoreLean

namespace WilsonLoop

open Filter Topology

/-- If `∑_{K ≥ K₀} |W_{K+1} - W_K| < ∞`, then `lim_{K → ∞} W_K` exists. -/
theorem MainBound.exists_limit {W : ℕ → ℂ} {K₀ : ℕ} {B : ℝ} (h : MainBound W K₀ B) :
    ∃ w : ℂ, Tendsto W atTop (𝓝 w) := by
  have hc : CauchySeq fun K ↦ W (K₀ + K) := by
    refine cauchySeq_of_summable_dist ?_
    simpa [dist_eq_norm, norm_sub_rev, add_assoc] using h.2
  obtain ⟨w, hw⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨w, (tendsto_add_atTop_iff_nat K₀).1 ?_⟩
  simpa [add_comm] using hw

/-- If `|W_K| ≤ B` for `K ≥ K₀` and `W_K → w`, then `|w| ≤ B`. -/
theorem MainBound.norm_le_of_tendsto {W : ℕ → ℂ} {K₀ : ℕ} {B : ℝ} (h : MainBound W K₀ B)
    {w : ℂ} (hW : Tendsto W atTop (𝓝 w)) : ‖w‖ ≤ B := by
  refine le_of_tendsto hW.norm ?_
  filter_upwards [eventually_ge_atTop K₀] with K hK using h.1 K hK

/-- If `|W_K| ≥ 1/2` for `K ≥ K₀` and `W_K → w`, then `|w| ≥ 1/2`. -/
theorem half_le_norm_of_tendsto {W : ℕ → ℂ} {K₀ : ℕ} {w : ℂ} (hW : Tendsto W atTop (𝓝 w))
    (h : ∀ K, K₀ ≤ K → 1 / 2 ≤ ‖W K‖) : 1 / 2 ≤ ‖w‖ := by
  refine ge_of_tendsto hW.norm ?_
  filter_upwards [eventually_ge_atTop K₀] with K hK using h K hK

end WilsonLoop

end CoreLean
