import Mathlib

/-! Truncated expectations (cumulants) of a random variable from its moments (Bałaban I (3.23)): with the moments
`m_n = ⟨V^n⟩`, the truncated expectations `⟨V^n⟩^T` are defined by the recursion
`m_{n+1} = Σ_{j=0}^{n} C(n, j) ⟨V^{j+1}⟩^T m_{n-j}`, i.e. `⟨V^{n+1}⟩^T = m_{n+1} - Σ_{j<n} C(n, j) ⟨V^{j+1}⟩^T m_{n-j}`
(for `m_0 = 1`), the coefficient form of `⟨e^{tV}⟩ = exp Σ_{n≥1} t^n ⟨V^n⟩^T / n!`. -/

namespace GaussianBlockSpin

open MeasureTheory

/-- `⟨V^n⟩^T` from the moment sequence `m` (`⟨V^0⟩^T = 0`). -/
noncomputable def truncExp (m : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => m (n + 1) - ∑ j : Fin n, (n.choose j : ℝ) * truncExp m (j + 1) * m (n - j)
decreasing_by exact Nat.succ_lt_succ j.isLt

/-- The recursion in the form `m_{n+1} = Σ_{j=0}^{n} C(n, j) ⟨V^{j+1}⟩^T m_{n-j}` (when `m_0 = 1`). -/
theorem moment_succ_eq (m : ℕ → ℝ) (hm0 : m 0 = 1) (n : ℕ) :
    m (n + 1) = ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * truncExp m (j + 1) * m (n - j) := by
  rw [Finset.sum_range_succ, Nat.choose_self, Nat.sub_self, hm0, truncExp, Finset.sum_range]
  push_cast
  ring

theorem truncExp_one (m : ℕ → ℝ) : truncExp m 1 = m 1 := by
  rw [truncExp]
  simp

theorem truncExp_two (m : ℕ → ℝ) : truncExp m 2 = m 2 - m 1 ^ 2 := by
  rw [truncExp, Fin.sum_univ_one]
  norm_num [truncExp_one]
  ring

/-- `⟨V^3⟩^T = ⟨V^3⟩ - 3 ⟨V^2⟩ ⟨V⟩ + 2 ⟨V⟩^3` (the corrected reading E5 of the display after (3.23)). -/
theorem truncExp_three (m : ℕ → ℝ) : truncExp m 3 = m 3 - 3 * m 2 * m 1 + 2 * m 1 ^ 3 := by
  rw [truncExp, Fin.sum_univ_two]
  norm_num [truncExp_one, truncExp_two]
  ring

/-- The moments `⟨V^n⟩ = ∫ V^n dμ` for a probability measure `μ` (the source's expectation is with respect to the
normalised Gaussian measure, L946-L947; the recursion of `truncExp` presumes `⟨V^0⟩ = 1`, `moments_zero`). -/
noncomputable def moments {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (V : Ω → ℝ)
    (n : ℕ) : ℝ :=
  ∫ ω, V ω ^ n ∂μ -- totalisation-audit: allow junk 0 if V^n is not integrable; (3.23)-(3.24) use polynomials V under Gaussian measures, where every moment exists

lemma moments_zero {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (V : Ω → ℝ) :
    moments μ V 0 = 1 := by
  simp [moments]

/-- The truncated cumulant sum `Σ_{n=1}^{n̄} ⟨V^n⟩^T / n!` for a probability measure `μ`, the exponent of (3.24)
without its error term. -/
noncomputable def cumulantSum {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (V : Ω → ℝ)
    (nbar : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 nbar, truncExp (moments μ V) n / (n.factorial : ℝ) -- totalisation-audit: allow factorials are positive

end GaussianBlockSpin
