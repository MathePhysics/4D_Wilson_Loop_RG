import GaussianBlockSpin.CumulantSplit
import GaussianBlockSpin.LogDerivatives

/-! The cumulant formula with remainder for a bounded random variable (the "cumulant formula" of [2], (5.21), used in
each box): if `|V| ≤ M` under a probability measure `ν`, then
`|log ∫ e^V dν - Σ_{n=1}^t ⟨V^n⟩^T / n!| ≤ c_{t+1} M^{t+1} / (t+1)!` (`c = cumBound`). The proof: `g(λ) = log ∫ e^{λV}`
is smooth with `g^{(n)}(λ)` the truncated expectation of order `n` under the tilted measure `e^{λV} ν / Z(λ)`
(Mathlib's iteratedDeriv_mgf and iteratedDerivWithin_log_eq_truncExp), whose moments are bounded by `M^j`; Taylor
with the Lagrange remainder on `[0, 1]`. -/

namespace GaussianBlockSpin

open MeasureTheory ProbabilityTheory Real
open scoped Nat

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A truncated expectation from moments bounded by `M^j`: `|⟨V^n⟩^T| ≤ c_n M^n`. -/
lemma abs_truncExp_le (m : ℕ → ℝ) (hm0 : m 0 = 1) {M : ℝ} (hM : 0 ≤ M) (hm : ∀ j, |m j| ≤ M ^ j) (n : ℕ) :
    |truncExp m n| ≤ cumBound n * M ^ n := by
  rcases n with _ | n
  · simp [truncExp, cumBound]
  · have h := jointCumulant_eq_truncExp (n := n + 1) m hm0 Finset.univ Finset.univ_nonempty
    rw [Finset.card_univ, Fintype.card_fin] at h
    rw [← h]
    have hb := abs_jointCumulant_le (fun S : Finset (Fin (n + 1)) => m S.card) (fun _ => M) (fun _ => hM)
      Finset.univ (fun U _ => by rw [Finset.prod_const]; exact hm U.card)
    rwa [Finset.card_univ, Fintype.card_fin, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hb

/-- **The cumulant formula with remainder**: for `V` measurable with `|V| ≤ M` under a probability measure,
`|log ∫ e^V dν - Σ_{n=1}^t ⟨V^n⟩^T/n!| ≤ c_{t+1} M^{t+1}/(t+1)!`. -/
theorem abs_log_integral_exp_sub_cumulantSum_le (ν : Measure Ω) [IsProbabilityMeasure ν] {V : Ω → ℝ}
    (hV : Measurable V) {M : ℝ} (hM : 0 ≤ M) (hVM : ∀ ω, |V ω| ≤ M) (t : ℕ) :
    |Real.log (∫ ω, Real.exp (V ω) ∂ν) - cumulantSum ν V t| ≤ cumBound (t + 1) * M ^ (t + 1) / (t + 1)! := by
  -- every exponential moment exists
  have hint : ∀ s : ℝ, Integrable (fun ω => Real.exp (s * V ω)) ν := by
    intro s
    refine Integrable.of_bound (by fun_prop) (Real.exp (|s| * M)) (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_exp.mpr ?_
    calc s * V ω ≤ |s * V ω| := le_abs_self _
      _ = |s| * |V ω| := abs_mul _ _
      _ ≤ |s| * M := mul_le_mul_of_nonneg_left (hVM ω) (abs_nonneg _)
  have hset : integrableExpSet V ν = Set.univ := Set.eq_univ_of_forall hint
  have hint' : ∀ s, s ∈ interior (integrableExpSet V ν) := fun s => by rw [hset, interior_univ]; trivial
  set Z := mgf V ν with hZ
  have hZpos : ∀ s, 0 < Z s := fun s => mgf_pos (hint s)
  have hZsmooth : ContDiff ℝ ⊤ Z := by
    have h : AnalyticOnNhd ℝ Z Set.univ := by
      have := analyticOnNhd_mgf (X := V) (μ := ν)
      rwa [hset, interior_univ] at this
    exact contDiff_iff_contDiffAt.mpr fun s => (h s trivial).contDiffAt
  set g : ℝ → ℝ := fun s => Real.log (Z s) with hg
  have hgsmooth : ContDiff ℝ ⊤ g := hZsmooth.log fun s => (hZpos s).ne'
  -- the derivatives of `g` are truncated expectations of the tilted moments
  have hderiv : ∀ (s : ℝ) (n : ℕ), iteratedDeriv (n + 1) g s =
      truncExp (fun j => iteratedDeriv j Z s / Z s) (n + 1) := by
    intro s n
    have hZn : ContDiff ℝ ((n : WithTop ℕ∞) + 1) Z := hZsmooth.of_le le_top
    have h := iteratedDerivWithin_log_eq_truncExp uniqueDiffOn_univ (Set.mem_univ s)
      hZn.contDiffAt.contDiffWithinAt (hZpos s)
    simp only [iteratedDerivWithin_univ] at h
    exact h
  have hmom : ∀ (s : ℝ) (j : ℕ), |iteratedDeriv j Z s / Z s| ≤ M ^ j := by
    intro s j
    rw [hZ, iteratedDeriv_mgf (hint' s) j, abs_div, abs_of_pos (hZpos s), div_le_iff₀ (hZpos s)]
    calc |∫ ω, V ω ^ j * Real.exp (s * V ω) ∂ν| ≤ ∫ ω, |V ω ^ j * Real.exp (s * V ω)| ∂ν :=
          abs_integral_le_integral_abs
      _ ≤ ∫ ω, M ^ j * Real.exp (s * V ω) ∂ν := by
          refine integral_mono_of_nonneg (ae_of_all _ fun ω => abs_nonneg _)
            ((hint s).const_mul _) (ae_of_all _ fun ω => ?_)
          dsimp only
          rw [abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)]
          exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) (hVM ω) j) (Real.exp_pos _).le
      _ = M ^ j * Z s := by rw [integral_const_mul, hZ]; rfl
  have hm0 : ∀ s, (fun j => iteratedDeriv j Z s / Z s) 0 = 1 := fun s => by
    simp [(hZpos s).ne']
  -- Taylor with the Lagrange remainder on `[0, 1]`
  obtain ⟨ξ, -, hξ⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (f := g) (x₀ := 0) (x := 1) (n := t)
    zero_ne_one (hgsmooth.contDiffOn.of_le le_top)
  have huniq : UniqueDiffOn ℝ (Set.uIcc (0 : ℝ) 1) := uniqueDiffOn_uIcc zero_ne_one
  have hZ0 : Z 0 = 1 := by simp [hZ]
  have htaylor : taylorWithinEval g t (Set.uIcc 0 1) 0 1 = cumulantSum ν V t := by
    rw [taylor_within_apply, cumulantSum]
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos t)]
    have hg0 : iteratedDerivWithin 0 g (Set.uIcc 0 1) 0 = 0 := by
      simp [hg, hZ0]
    rw [hg0, smul_zero, zero_add]
    have hIcc : Finset.Ico (0 + 1) (t + 1) = Finset.Icc 1 t := by
      ext k; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega
    rw [hIcc]
    refine Finset.sum_congr rfl fun k hk => ?_
    obtain ⟨hk1, -⟩ := Finset.mem_Icc.mp hk
    obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
    rw [iteratedDerivWithin_eq_iteratedDeriv huniq (hgsmooth.contDiffAt.of_le le_top)
      (Set.left_mem_uIcc), hderiv 0 n]
    have hmoments : (fun j => iteratedDeriv j Z 0 / Z 0) = moments ν V := by
      funext j
      have h1 : iteratedDeriv j Z 0 = ∫ ω, (V ^ j) ω ∂ν := by
        rw [hZ]; exact iteratedDeriv_mgf_zero (hint' 0) j
      rw [h1, hZ0, div_one, moments]
      rfl
    rw [hmoments, smul_eq_mul, sub_zero, one_pow, mul_one]
    ring
  have hg1 : g 1 = Real.log (∫ ω, Real.exp (V ω) ∂ν) := by simp [hg, hZ, mgf]
  rw [← hg1, ← htaylor, hξ, hderiv ξ t, sub_zero, one_pow, mul_one, abs_div,
    abs_of_pos (by positivity : (0 : ℝ) < ((t + 1)! : ℝ))]
  gcongr
  exact abs_truncExp_le _ (hm0 ξ) hM (hmom ξ) (t + 1)

end GaussianBlockSpin
