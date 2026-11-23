import Mathlib

/-! The coefficients of `(1 - x)^{-1/2} = Σ_n c_n x^n`, defined by `c_0 = 1`, `c_{n+1} = c_n (2n + 1)/(2n + 2)` (the
closed form `c_n = binom(2n, n)/4^n` is neither proved nor used here):
* sqrtCoef_nonneg, sqrtCoef_le_one: `0 ≤ c_n ≤ 1`;
* sum_antidiagonal_sqrtCoef: `Σ_{i+j=n} c_i c_j = 1`, so `(Σ c_n x^n)² = Σ x^n` (proof: with `S_n` the left side and
  `T_n = Σ_{i+j=n} i c_i c_j`, symmetry gives `n S_n = 2 T_n` and the recurrence gives `2 T_{n+1} = 2 T_n + S_n`). -/

namespace GaussianBlockSpin

/-- The coefficients of `(1 - x)^{-1/2}`. -/
noncomputable def sqrtCoef : ℕ → ℝ
  | 0 => 1
  | n + 1 => sqrtCoef n * (2 * n + 1) / (2 * n + 2)

lemma sqrtCoef_succ (n : ℕ) : sqrtCoef (n + 1) = sqrtCoef n * (2 * n + 1) / (2 * n + 2) := rfl

lemma sqrtCoef_rec (n : ℕ) : 2 * ((n : ℝ) + 1) * sqrtCoef (n + 1) = (2 * n + 1) * sqrtCoef n := by
  rw [sqrtCoef_succ]
  have : (2 * (n : ℝ) + 2) ≠ 0 := by positivity
  field_simp

lemma sqrtCoef_nonneg (n : ℕ) : 0 ≤ sqrtCoef n := by
  induction n with
  | zero => simp [sqrtCoef]
  | succ n ih => rw [sqrtCoef_succ]; positivity

lemma sqrtCoef_le_one (n : ℕ) : sqrtCoef n ≤ 1 := by
  induction n with
  | zero => simp [sqrtCoef]
  | succ n ih =>
    rw [sqrtCoef_succ]
    have h2 : (0 : ℝ) < 2 * n + 2 := by positivity
    rw [div_le_one h2]
    have := sqrtCoef_nonneg n
    nlinarith

/-- `S_n = Σ_{i+j=n} c_i c_j`. -/
noncomputable def sqrtConv (n : ℕ) : ℝ := ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, sqrtCoef p.1 * sqrtCoef p.2

/-- `T_n = Σ_{i+j=n} i c_i c_j`. -/
noncomputable def sqrtConvT (n : ℕ) : ℝ := ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, (p.1 : ℝ) * (sqrtCoef p.1 * sqrtCoef p.2)

lemma two_sqrtConvT (n : ℕ) : 2 * sqrtConvT n = n * sqrtConv n := by
  have hswap : sqrtConvT n = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, (p.2 : ℝ) * (sqrtCoef p.1 * sqrtCoef p.2) := by
    unfold sqrtConvT
    rw [← Finset.Nat.sum_antidiagonal_swap]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [Prod.fst_swap, Prod.snd_swap]
    ring
  have hsum : ∀ p ∈ Finset.HasAntidiagonal.antidiagonal n, ((p.1 : ℝ) + p.2) = n := fun p hp => by
    have := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    exact_mod_cast this
  calc 2 * sqrtConvT n = sqrtConvT n + ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, (p.2 : ℝ) * (sqrtCoef p.1 * sqrtCoef p.2) := by
        rw [← hswap]; ring
    _ = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, ((p.1 : ℝ) + p.2) * (sqrtCoef p.1 * sqrtCoef p.2) := by
        unfold sqrtConvT; rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun p _ => by ring
    _ = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, (n : ℝ) * (sqrtCoef p.1 * sqrtCoef p.2) :=
        Finset.sum_congr rfl fun p hp => by rw [hsum p hp]
    _ = n * sqrtConv n := by unfold sqrtConv; rw [Finset.mul_sum]

lemma two_sqrtConvT_succ (n : ℕ) : 2 * sqrtConvT (n + 1) = 2 * sqrtConvT n + sqrtConv n := by
  unfold sqrtConvT sqrtConv
  rw [Finset.Nat.antidiagonal_succ, Finset.sum_cons, Finset.sum_map]
  simp only [Nat.cast_zero, zero_mul, zero_add, Function.Embedding.coe_prodMap, Function.Embedding.coeFn_mk,
    Prod.map_fst, Prod.map_snd, Function.Embedding.refl_apply, Nat.cast_succ, Nat.succ_eq_add_one]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  have h := sqrtCoef_rec p.1
  calc 2 * (((p.1 : ℝ) + 1) * (sqrtCoef (p.1 + 1) * sqrtCoef p.2))
      = (2 * ((p.1 : ℝ) + 1) * sqrtCoef (p.1 + 1)) * sqrtCoef p.2 := by ring
    _ = ((2 * p.1 + 1) * sqrtCoef p.1) * sqrtCoef p.2 := by rw [h]
    _ = 2 * ((p.1 : ℝ) * (sqrtCoef p.1 * sqrtCoef p.2)) + sqrtCoef p.1 * sqrtCoef p.2 := by ring

/-- **`Σ_{i+j=n} c_i c_j = 1`**. -/
theorem sum_antidiagonal_sqrtCoef (n : ℕ) : sqrtConv n = 1 := by
  induction n with
  | zero => simp [sqrtConv, sqrtCoef]
  | succ n ih =>
    have h1 := two_sqrtConvT (n + 1)
    have h2 := two_sqrtConvT_succ n
    have h3 := two_sqrtConvT n
    rw [ih] at h2 h3
    push_cast at h1
    have hn : (0 : ℝ) < n + 1 := by positivity
    have : ((n : ℝ) + 1) * sqrtConv (n + 1) = (n + 1) * 1 := by linarith
    exact mul_left_cancel₀ hn.ne' this

end GaussianBlockSpin
