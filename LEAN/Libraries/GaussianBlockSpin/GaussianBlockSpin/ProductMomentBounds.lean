import GaussianBlockSpin.MonomialBounds

/-! Products over the coordinates of one-dimensional moments (the moments of products of monomials, by
integral_prod_monoVal): with exponents `e_c` of total degree `Q = Σ_c e_c`,
* abs_prod_moments_le: if `|∫ x^q dμ_c| ≤ 2 q! K` for all `q` (`K ≥ 1/2`), then `|∏_c ∫ x^{e_c} dμ_c| ≤ Q! (2K)^Q`;
* abs_prod_moments_sub_le: if moreover `|∫ x^q dν_c - ∫ x^q dγ_c| ≤ η q!` (`η ≥ 0`), the two products differ by
  at most `η Q Q! (2K)^Q`. -/

namespace GaussianBlockSpin

open MeasureTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The per-coordinate bound `M_q = q! (2K)^q`. -/
lemma moment_le_M {K : ℝ} (hK : 1 ≤ 2 * K) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ q : ℕ, |∫ x, x ^ q ∂μ| ≤ 2 * (q.factorial * K)) (q : ℕ) :
    |∫ x, x ^ q ∂μ| ≤ q.factorial * (2 * K) ^ q := by
  rcases q with _ | q
  · simp
  · refine (hμ (q + 1)).trans ?_
    have : 2 * K ≤ (2 * K) ^ (q + 1) := by
      calc 2 * K = (2 * K) ^ 1 := (pow_one _).symm
        _ ≤ (2 * K) ^ (q + 1) := pow_le_pow_right₀ hK (by omega)
    have hf : (0 : ℝ) ≤ (q + 1).factorial := Nat.cast_nonneg _
    nlinarith

omit [DecidableEq ι] in
/-- `∏_c e_c! (2K)^{e_c} ≤ Q! (2K)^Q`. -/
lemma prod_M_le {K : ℝ} (hK : 0 ≤ 2 * K) (e : ι → ℕ) :
    ∏ c, ((e c).factorial * (2 * K) ^ e c : ℝ) ≤ (∑ c, e c).factorial * (2 * K) ^ (∑ c, e c) := by
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  gcongr
  have := Nat.le_of_dvd (Nat.factorial_pos _) (Nat.prod_factorial_dvd_factorial_sum Finset.univ e)
  exact_mod_cast this

omit [DecidableEq ι] in
/-- **Bound on product moments**. -/
lemma abs_prod_moments_le {K : ℝ} (hK : 1 ≤ 2 * K) (μ : ι → Measure ℝ) [∀ c, IsProbabilityMeasure (μ c)]
    (hμ : ∀ c, ∀ q : ℕ, |∫ x, x ^ q ∂(μ c)| ≤ 2 * (q.factorial * K)) (e : ι → ℕ) :
    |∏ c, ∫ x, x ^ e c ∂(μ c)| ≤ (∑ c, e c).factorial * (2 * K) ^ (∑ c, e c) := by
  rw [Finset.abs_prod]
  exact (Finset.prod_le_prod₀ (fun c _ => abs_nonneg _) fun c _ => moment_le_M hK (μ c) (hμ c) (e c)).trans
    (prod_M_le (by linarith) e)

/-- **Difference of product moments**. -/
lemma abs_prod_moments_sub_le {K η : ℝ} (hK : 1 ≤ 2 * K) (hη : 0 ≤ η) (ν γ : ι → Measure ℝ)
    [∀ c, IsProbabilityMeasure (ν c)] [∀ c, IsProbabilityMeasure (γ c)]
    (hν : ∀ c, ∀ q : ℕ, |∫ x, x ^ q ∂(ν c)| ≤ 2 * (q.factorial * K))
    (hγ : ∀ c, ∀ q : ℕ, |∫ x, x ^ q ∂(γ c)| ≤ 2 * (q.factorial * K))
    (hd : ∀ c, ∀ q : ℕ, |∫ x, x ^ q ∂(ν c) - ∫ x, x ^ q ∂(γ c)| ≤ η * q.factorial) (e : ι → ℕ) :
    |∏ c, ∫ x, x ^ e c ∂(ν c) - ∏ c, ∫ x, x ^ e c ∂(γ c)| ≤
      η * (∑ c, e c) * ((∑ c, e c).factorial * (2 * K) ^ (∑ c, e c)) := by
  set M : ι → ℝ := fun c => (e c).factorial * (2 * K) ^ e c with hM
  have hM0 : ∀ c, 0 ≤ M c := fun c => by positivity
  have h := abs_prod_sub_prod_le Finset.univ (fun c => ∫ x, x ^ e c ∂(ν c)) (fun c => ∫ x, x ^ e c ∂(γ c)) M
    (fun c _ => moment_le_M hK (ν c) (hν c) (e c)) (fun c _ => moment_le_M hK (γ c) (hγ c) (e c))
  refine h.trans ?_
  have hterm : ∀ c, |∫ x, x ^ e c ∂(ν c) - ∫ x, x ^ e c ∂(γ c)| * ∏ c' ∈ Finset.univ.erase c, M c' ≤
      η * (e c : ℝ) * ∏ c', M c' := by
    intro c
    rcases Nat.eq_zero_or_pos (e c) with h0 | hpos
    · simp [h0]
    · have hd' := hd c (e c)
      have hfac : ((e c).factorial : ℝ) ≤ M c := le_mul_of_one_le_right (Nat.cast_nonneg _) (one_le_pow₀ hK)
      rw [← Finset.mul_prod_erase Finset.univ M (Finset.mem_univ c)]
      have hprod : 0 ≤ ∏ c' ∈ Finset.univ.erase c, M c' := Finset.prod_nonneg fun c' _ => hM0 c'
      have hec : (1 : ℝ) ≤ e c := by exact_mod_cast hpos
      calc |∫ x, x ^ e c ∂(ν c) - ∫ x, x ^ e c ∂(γ c)| * ∏ c' ∈ Finset.univ.erase c, M c'
          ≤ η * (e c).factorial * ∏ c' ∈ Finset.univ.erase c, M c' := by gcongr
        _ ≤ η * M c * ∏ c' ∈ Finset.univ.erase c, M c' := by gcongr
        _ = η * 1 * (M c * ∏ c' ∈ Finset.univ.erase c, M c') := by ring
        _ ≤ η * (e c : ℝ) * (M c * ∏ c' ∈ Finset.univ.erase c, M c') := by
            have : 0 ≤ M c * ∏ c' ∈ Finset.univ.erase c, M c' := mul_nonneg (hM0 c) hprod
            gcongr
  calc ∑ c, |∫ x, x ^ e c ∂(ν c) - ∫ x, x ^ e c ∂(γ c)| * ∏ c' ∈ Finset.univ.erase c, M c'
      ≤ ∑ c, η * (e c : ℝ) * ∏ c', M c' := Finset.sum_le_sum fun c _ => hterm c
    _ = η * (∑ c, (e c : ℝ)) * ∏ c', M c' := by rw [← Finset.sum_mul, ← Finset.mul_sum]
    _ ≤ η * (∑ c, e c : ℕ) * ((∑ c, e c).factorial * (2 * K) ^ (∑ c, e c)) := by
        push_cast
        gcongr
        exact prod_M_le (by linarith) e

end GaussianBlockSpin
