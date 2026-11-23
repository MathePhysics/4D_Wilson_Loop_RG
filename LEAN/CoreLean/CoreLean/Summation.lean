/-
`lem:summation` of BALABAN_CORE.tex: `eq:chain-summation` from `eq:summation`, the part of the
lemma whose proof is given in the core.

The statement is proved for any nonnegative function `d` on a finite set which satisfies the
triangle inequality; the weighted distance on the determining set `𝐁` is such a function by
`lem:distance`(i). The chain sum `Σ_{y_1, …, y_{n-1}} Π_{i=1}^n e^{-δ d(y_{i-1}, y_i)}` is the
entry `(K^n)(y_0, y_n)` of the `n`-th power of the matrix `K(y, y') = e^{-δ d(y, y')}`.
-/
import Mathlib

open Matrix

namespace CoreLean

variable {B : Type*} [Fintype B] [DecidableEq B]

/-- The kernel `K(y, y') = e^{-δ d(y, y')}`. -/
noncomputable def expKernel (d : B → B → ℝ) (δ : ℝ) : Matrix B B ℝ :=
  Matrix.of fun y y' => Real.exp (-(δ * d y y'))

lemma expKernel_pow_nonneg (d : B → B → ℝ) (δ : ℝ) (n : ℕ) (y y' : B) :
    0 ≤ (expKernel d δ ^ n) y y' := by
  induction n generalizing y y' with
  | zero => simp [Matrix.one_apply]; split_ifs <;> norm_num
  | succ n ih =>
    rw [pow_succ', Matrix.mul_apply]
    exact Finset.sum_nonneg fun z _ =>
      mul_nonneg (Real.exp_pos _).le (ih z y')

/-- `eq:chain-summation` from `eq:summation`: if `Σ_{y'} e^{-αδ d(y, y')} ≤ c` for every `y`,
then `(K^n)(y_0, y_n) ≤ c^{n-1} e^{-(1-α)δ d(y_0, y_n)}` for `n ≥ 1`. -/
theorem chain_summation (d : B → B → ℝ) (hd0 : ∀ y y', 0 ≤ d y y')
    (htri : ∀ y y' y'', d y y'' ≤ d y y' + d y' y'') (α δ c : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hδ : 0 ≤ δ) (hsum : ∀ y, ∑ y', Real.exp (-(α * δ * d y y')) ≤ c) (n : ℕ) (hn : 1 ≤ n)
    (y₀ yₙ : B) :
    (expKernel d δ ^ n) y₀ yₙ ≤ c ^ (n - 1) * Real.exp (-((1 - α) * δ * d y₀ yₙ)) := by
  have hc : 0 ≤ c := (Finset.sum_nonneg fun y' _ => (Real.exp_pos _).le).trans (hsum y₀)
  induction n, hn using Nat.le_induction generalizing y₀ with
  | base =>
    simp only [pow_one, expKernel, Matrix.of_apply, Nat.sub_self, pow_zero, one_mul]
    apply Real.exp_le_exp.mpr
    have : 0 ≤ α * δ * d y₀ yₙ := mul_nonneg (mul_nonneg hα0 hδ) (hd0 _ _)
    nlinarith
  | succ n hn ih =>
    rw [pow_succ', Matrix.mul_apply]
    -- peel off the first factor: `K(y_0, y') (K^n)(y', y_n)`
    have hterm : ∀ y', expKernel d δ y₀ y' * (expKernel d δ ^ n) y' yₙ ≤
        c ^ (n - 1) * Real.exp (-((1 - α) * δ * d y₀ yₙ)) * Real.exp (-(α * δ * d y₀ y')) := by
      intro y'
      have h1 := ih y'
      calc expKernel d δ y₀ y' * (expKernel d δ ^ n) y' yₙ
          ≤ Real.exp (-(δ * d y₀ y')) * (c ^ (n - 1) * Real.exp (-((1 - α) * δ * d y' yₙ))) :=
            mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
        _ = c ^ (n - 1) * (Real.exp (-((1 - α) * δ * (d y₀ y' + d y' yₙ))) *
              Real.exp (-(α * δ * d y₀ y'))) := by
            rw [← Real.exp_add, mul_left_comm, ← Real.exp_add]
            congr 2
            ring
        _ ≤ c ^ (n - 1) * (Real.exp (-((1 - α) * δ * d y₀ yₙ)) *
              Real.exp (-(α * δ * d y₀ y'))) := by
            gcongr
            have h1α : 0 ≤ (1 - α) * δ := mul_nonneg (by linarith) hδ
            nlinarith [htri y₀ y' yₙ]
        _ = _ := by ring
    calc ∑ y', expKernel d δ y₀ y' * (expKernel d δ ^ n) y' yₙ
        ≤ ∑ y', c ^ (n - 1) * Real.exp (-((1 - α) * δ * d y₀ yₙ)) *
            Real.exp (-(α * δ * d y₀ y')) := Finset.sum_le_sum fun y' _ => hterm y'
      _ = c ^ (n - 1) * Real.exp (-((1 - α) * δ * d y₀ yₙ)) *
            ∑ y', Real.exp (-(α * δ * d y₀ y')) := by rw [Finset.mul_sum]
      _ ≤ c ^ (n - 1) * Real.exp (-((1 - α) * δ * d y₀ yₙ)) * c := by
            gcongr
            exact hsum y₀
      _ = c ^ (n + 1 - 1) * Real.exp (-((1 - α) * δ * d y₀ yₙ)) := by
            rw [show n + 1 - 1 = (n - 1) + 1 by omega, pow_succ]
            ring

end CoreLean
