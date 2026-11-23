import Mathlib

/-!
# The block-spin coefficients `a_k`

Bałaban I.(2.13)-(2.15): the coefficients of the composed block-spin kernels satisfy
`a_{k+1} = a a_k / (a L⁻² + a_k)` with `a_1 = a`. This sequence is unique and equals

  `a_k = a (1 - L⁻²) / (1 - L^{-2k})`,  `k ≥ 1`,

it decreases, and it tends to `a_∞ = a (1 - L⁻²)`.

The source indexes the sequence from `k = 1`, so no function on all of `ℕ` is defined here; the
results are stated for an arbitrary sequence satisfying the recursion.
-/

open Filter Topology

namespace GaussianBlockSpin

variable {a L : ℝ}

/-- The closed form satisfies the recursion I.(2.13). -/
theorem blockCoeff_closed_form_succ (ha : 0 < a) (hL : 1 < L) {k : ℕ} (hk : 1 ≤ k) :
    a * (1 - L ^ (-2 : ℤ)) / (1 - L ^ (-(2 * (k + 1) : ℤ))) =
      a * (a * (1 - L ^ (-2 : ℤ)) / (1 - L ^ (-(2 * k : ℤ)))) /
        (a * L ^ (-2 : ℤ) + a * (1 - L ^ (-2 : ℤ)) / (1 - L ^ (-(2 * k : ℤ)))) := by
  set r : ℝ := L ^ (-2 : ℤ) with hr
  have hL0 : 0 < L := by linarith
  have hr0 : 0 < r := by rw [hr]; positivity
  have hr1 : r < 1 := by
    rw [hr, zpow_neg, inv_lt_one₀ (by positivity)]
    exact one_lt_zpow₀ hL (by norm_num)
  have hpow : ∀ n : ℕ, L ^ (-(2 * n : ℤ)) = r ^ n := by
    intro n
    rw [hr, ← zpow_natCast, ← zpow_mul]
    congr 1
  have hk' : (k : ℤ) + 1 = ((k + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [hk', hpow, hpow]
  have hrk : r ^ k < 1 := pow_lt_one₀ hr0.le hr1 (by omega)
  have hrk1 : r ^ (k + 1) < 1 := pow_lt_one₀ hr0.le hr1 (by omega)
  have h1 : 0 < 1 - r ^ k := by linarith
  have h2 : 0 < 1 - r ^ (k + 1) := by linarith
  have h3 : 0 < 1 - r := by linarith
  field_simp
  ring

/-- **Uniqueness and closed form**, I.(2.15): a sequence with `c 1 = a` satisfying I.(2.13) is
`c k = a (1 - L⁻²) / (1 - L^{-2k})` for all `k ≥ 1`. -/
theorem blockCoeff_eq_closed_form (ha : 0 < a) (hL : 1 < L) (c : ℕ → ℝ) (h1 : c 1 = a)
    (hrec : ∀ k, 1 ≤ k → c (k + 1) = a * c k / (a * L ^ (-2 : ℤ) + c k)) :
    ∀ k, 1 ≤ k → c k = a * (1 - L ^ (-2 : ℤ)) / (1 - L ^ (-(2 * k : ℤ))) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    have hL0 : 0 < L := by linarith
    have hne : 1 - L ^ (-2 : ℤ) ≠ 0 := by
      have : L ^ (-2 : ℤ) < 1 := by
        rw [zpow_neg, inv_lt_one₀ (by positivity)]
        exact one_lt_zpow₀ hL (by norm_num)
      linarith
    have hL2 : L ^ 2 - 1 ≠ 0 := by nlinarith
    rw [h1]
    push_cast
    field_simp
  | succ k hk ih =>
    rw [hrec k hk, ih]
    push_cast
    exact (blockCoeff_closed_form_succ ha hL hk).symm

/-- `L^{-2k} = (L⁻²)^k`. -/
lemma zpow_neg_two_mul (L : ℝ) (k : ℕ) : L ^ (-(2 * k : ℤ)) = (L ^ (-2 : ℤ)) ^ k := by
  rw [← zpow_natCast, ← zpow_mul]
  congr 1

/-- `a_k` decreases strictly, I.(2.15). -/
theorem blockCoeff_closed_form_strictAnti (ha : 0 < a) (hL : 1 < L) {k : ℕ} (hk : 1 ≤ k) :
    a * (1 - L ^ (-2 : ℤ)) / (1 - L ^ (-(2 * (k + 1) : ℤ))) <
      a * (1 - L ^ (-2 : ℤ)) / (1 - L ^ (-(2 * k : ℤ))) := by
  have hk' : (k : ℤ) + 1 = ((k + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [hk', zpow_neg_two_mul, zpow_neg_two_mul]
  set r : ℝ := L ^ (-2 : ℤ)
  have hL0 : 0 < L := by linarith
  have hr0 : 0 < r := by positivity
  have hr1 : r < 1 := by
    simp only [r, zpow_neg, inv_lt_one₀ (by positivity : (0 : ℝ) < L ^ (2 : ℤ))]
    exact one_lt_zpow₀ hL (by norm_num)
  have hrk : r ^ k < 1 := pow_lt_one₀ hr0.le hr1 (by omega)
  have hlt : r ^ (k + 1) < r ^ k := pow_lt_pow_right_of_lt_one₀ hr0 hr1 (Nat.lt_succ_self k)
  apply div_lt_div_of_pos_left (by nlinarith) (by linarith) (by linarith)

/-- `a_k → a_∞ = a (1 - L⁻²)`, I.(2.15). -/
theorem tendsto_blockCoeff_closed_form (hL : 1 < L) :
    Tendsto (fun k : ℕ => a * (1 - L ^ (-2 : ℤ)) / (1 - L ^ (-(2 * k : ℤ)))) atTop
      (𝓝 (a * (1 - L ^ (-2 : ℤ)))) := by
  simp_rw [zpow_neg_two_mul]
  have hL0 : 0 < L := by linarith
  have hr0 : 0 ≤ L ^ (-2 : ℤ) := by positivity
  have hr1 : L ^ (-2 : ℤ) < 1 := by
    rw [zpow_neg, inv_lt_one₀ (by positivity)]
    exact one_lt_zpow₀ hL (by norm_num)
  have h := ((tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).const_sub 1).inv₀ (by norm_num)
  simpa [div_eq_mul_inv] using h.const_mul (a * (1 - L ^ (-2 : ℤ)))

end GaussianBlockSpin
