import BakerCampbellHausdorff.LogSeries
import BakerCampbellHausdorff.ExpBounds
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# `exp (log (1 + u)) = 1 + u` in a Banach algebra

For `‖u‖ < 1` in a Banach algebra over `𝕂 = ℝ` or `ℂ`, `exp (log1p 𝕂 u) = 1 + u`.

## Proof

Everything happens in the commuting family `L t = log (1 + t u)`, `t ∈ 𝕂`, `‖t‖ < R`, where
`R = 2 / (1 + ‖u‖)` satisfies `1 < R` and `R ‖u‖ < 1`.

1. Term-by-term differentiation (`hasDerivAt_tsum_of_isPreconnected`): `L` has derivative
   `L' t = ∑_{n ≥ 1} (-1)^(n+1) t^(n-1) uⁿ = u ∑_k (-t u)^k`, so `L' t (1 + t u) = u` by the
   geometric series.
2. Since `L s` and `L t` commute, `exp (-L s) = exp (-L t) exp (L t - L s)`, and `exp` has
   derivative `1` at `0`; hence `exp (-L ·)` has derivative `-exp (-L t) L' t` at `t`.  No
   derivative of `exp` away from `0` in a noncommutative algebra is needed.
3. `F t = exp (-L t) (1 + t u)` therefore has derivative
   `-exp (-L t) L' t (1 + t u) + exp (-L t) u = 0`, so `F` is constant on the ball:
   `exp (-log1p 𝕂 u) (1 + u) = F 1 = F 0 = 1`.  Multiplying by `exp (log1p 𝕂 u)` gives the claim.

## Main result

* `exp_log1p`: `‖u‖ < 1 → exp (log1p 𝕂 u) = 1 + u`.
-/

noncomputable section

open NormedSpace

namespace BakerCampbellHausdorff

variable {𝕂 𝔸 : Type*} [RCLike 𝕂] [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [CompleteSpace 𝔸]

/-- The terms `(-1)^(n+1)/n tⁿ uⁿ` of `log (1 + t u)`. -/
def logTerm (u : 𝔸) (n : ℕ) (t : 𝕂) : 𝔸 := (logCoeff 𝕂 n * t ^ n) • u ^ n

/-- The derivatives in `t` of the terms `logTerm u n t`. -/
def logTermDeriv (u : 𝔸) (n : ℕ) (t : 𝕂) : 𝔸 := (logCoeff 𝕂 n * (n * t ^ (n - 1))) • u ^ n

omit [CompleteSpace 𝔸] in
theorem hasDerivAt_logTerm (u : 𝔸) (n : ℕ) (t : 𝕂) :
    HasDerivAt (logTerm u n) (logTermDeriv u n t) t :=
  ((hasDerivAt_pow n t).const_mul (logCoeff 𝕂 n)).smul_const (u ^ n)

omit [CompleteSpace 𝔸] in
theorem log1p_smul_eq_tsum (u : 𝔸) (t : 𝕂) :
    log1p 𝕂 (t • u) = ∑' n, logTerm u n t := by  -- totalisation-audit: allow definition of log1p
  rw [log1p_eq_tsum]
  congr 1
  ext n
  rw [logTerm, smul_pow, smul_smul]

omit [CompleteSpace 𝔸] in
theorem logTerm_zero_right (u : 𝔸) (n : ℕ) : logTerm u n (0 : 𝕂) = 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [logTerm]
  · simp [logTerm, zero_pow hn.ne']

omit [CompleteSpace 𝔸] in
theorem logTermDeriv_succ (u : 𝔸) (k : ℕ) (t : 𝕂) :
    logTermDeriv u (k + 1) t = u * (-(t • u)) ^ k := by
  rw [logTermDeriv, ← mul_assoc, Nat.cast_succ, logCoeff_succ_mul, Nat.add_sub_cancel,
    ← neg_smul, smul_pow, mul_smul_comm, ← pow_succ', neg_pow t k]

omit [CompleteSpace 𝔸] in
theorem norm_logTermDeriv_le (u : 𝔸) (n : ℕ) {t : 𝕂} {R : ℝ} (hR : 0 < R) (ht : ‖t‖ < R) :
    ‖logTermDeriv u n t‖ ≤ (R * ‖u‖) ^ n / R := by  -- totalisation-audit: allow R > 0 by hR
  rcases n with _ | k
  · simp only [logTermDeriv, logCoeff_zero, zero_mul, zero_smul, norm_zero, pow_zero]
    positivity
  · have e : (R * ‖u‖) ^ (k + 1) / R =  -- totalisation-audit: allow R > 0 by hR
        R ^ k * ‖u‖ ^ (k + 1) := by
      rw [mul_pow, pow_succ]
      field_simp
    rw [e, logTermDeriv, ← mul_assoc, Nat.cast_succ, logCoeff_succ_mul, Nat.add_sub_cancel,
      norm_smul, norm_mul, norm_pow, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg t) ht.le k) (norm_pow_le' u k.succ_pos)
      (norm_nonneg _) (by positivity)

/-- The derivative `L' t = ∑ (-1)^(n+1) t^(n-1) uⁿ` of `L t = log (1 + t u)` satisfies
`L' t (1 + t u) = u`. -/
theorem tsum_logTermDeriv_mul (u : 𝔸) {t : 𝕂} (ht : ‖t • u‖ < 1) :
    (∑' n, logTermDeriv u n t) * (1 + t • u) = u := by  -- totalisation-audit: allow summable (h2)
  have hw1 : ‖-(t • u)‖ < 1 := by rwa [norm_neg]
  have hS := (summable_geometric_of_norm_lt_one hw1).hasSum
  have h1 : HasSum (fun k => logTermDeriv u (k + 1) t)
      (u * ∑' k, (-(t • u)) ^ k) := by  -- totalisation-audit: allow summable (hS)
    simp_rw [logTermDeriv_succ]
    exact hS.mul_left u
  have h0 : ∑ i ∈ Finset.range 1, logTermDeriv u i t = 0 := by simp [logTermDeriv]
  have h2 : HasSum (fun n => logTermDeriv u n t)
      (u * ∑' k, (-(t • u)) ^ k) := by  -- totalisation-audit: allow summable (hS)
    rw [← hasSum_nat_add_iff' 1, h0, sub_zero]
    exact h1
  have e : (1 : 𝔸) + t • u = 1 - -(t • u) := by rw [sub_neg_eq_add]
  rw [h2.tsum_eq, mul_assoc, e, geom_series_mul_neg _ hw1, mul_one]

/-- Term-by-term differentiation of `t ↦ log (1 + t u)` on the ball `‖t‖ < R`, `R ‖u‖ < 1`. -/
theorem hasDerivAt_log1p_smul (u : 𝔸) {R : ℝ} (hR : 0 < R) (hRu : R * ‖u‖ < 1) {t : 𝕂}
    (ht : ‖t‖ < R) :
    HasDerivAt (fun s : 𝕂 => log1p 𝕂 (s • u))
      (∑' n, logTermDeriv u n t) t := by  -- totalisation-audit: allow summable, dominated by hsum
  have hsum : Summable fun n => (R * ‖u‖) ^ n / R :=  -- totalisation-audit: allow R > 0 by hR
    (summable_geometric_of_lt_one (by positivity) hRu).div_const R
  have h := hasDerivAt_tsum_of_isPreconnected hsum Metric.isOpen_ball
    (convex_ball (0 : 𝕂) R).isPreconnected (fun n y _ => hasDerivAt_logTerm u n y)
    (fun n y hy => norm_logTermDeriv_le u n hR (mem_ball_zero_iff.mp hy))
    (Metric.mem_ball_self hR) (by simp only [logTerm_zero_right]; exact summable_zero)
    (mem_ball_zero_iff.mpr ht)
  simpa only [log1p_smul_eq_tsum] using h

/-- The derivative of `t ↦ exp (-log (1 + t u))`, computed from the derivative of `exp` at `0`
only, using that the values `log (1 + s u)` commute with each other. -/
theorem hasDerivAt_exp_neg_log1p_smul (u : 𝔸) {L' : 𝔸} {t : 𝕂}
    (hL : HasDerivAt (fun s : 𝕂 => log1p 𝕂 (s • u)) L' t) :
    HasDerivAt (fun s : 𝕂 => exp (-log1p 𝕂 (s • u))) (exp (-log1p 𝕂 (t • u)) * -L') t := by
  have hcomm : ∀ s : 𝕂, Commute (log1p 𝕂 (t • u)) (log1p 𝕂 (s • u)) := fun s =>
    (((Commute.refl u).smul_left t).smul_right s).log1p_right.log1p_left
  have heq : (fun s : 𝕂 => exp (-log1p 𝕂 (s • u))) = fun s =>
      exp (-log1p 𝕂 (t • u)) * exp (log1p 𝕂 (t • u) - log1p 𝕂 (s • u)) := by
    funext s
    rw [← exp_add_of_commute' 𝕂 ((Commute.refl _).sub_right (hcomm s)).neg_left]
    congr 1
    abel
  have hinner : HasDerivAt (fun s : 𝕂 => log1p 𝕂 (t • u) - log1p 𝕂 (s • u)) (-L') t := by
    exact hL.const_sub (log1p 𝕂 (t • u))
  have hexp : HasFDerivAt exp (1 : 𝔸 →L[𝕂] 𝔸) (log1p 𝕂 (t • u) - log1p 𝕂 (t • u)) := by
    rw [sub_self]
    exact hasFDerivAt_exp_zero
  have h := (hexp.comp_hasDerivAt t hinner).const_mul (exp (-log1p 𝕂 (t • u)))
  rw [heq]
  simpa using h

variable (𝕂) in
/-- **`exp (log (1 + u)) = 1 + u`** for `‖u‖ < 1` in a Banach algebra over `𝕂 = ℝ` or `ℂ`. -/
theorem exp_log1p {u : 𝔸} (hu : ‖u‖ < 1) : exp (log1p 𝕂 u) = 1 + u := by
  have hu0 := norm_nonneg u
  set R : ℝ := 2 / (1 + ‖u‖) with hRdef  -- totalisation-audit: allow 1 + ‖u‖ > 0
  have hR : 0 < R := by positivity
  have hR1 : 1 < R := by
    rw [hRdef, lt_div_iff₀ (by positivity)]
    linarith
  have hRu : R * ‖u‖ < 1 := by
    rw [hRdef, div_mul_eq_mul_div, div_lt_one (by positivity)]
    linarith
  let F : 𝕂 → 𝔸 := fun s => exp (-log1p 𝕂 (s • u)) * (1 + s • u)
  have hF : ∀ t ∈ Metric.ball (0 : 𝕂) R, HasDerivAt F 0 t := by
    intro t ht
    have ht' : ‖t‖ < R := mem_ball_zero_iff.mp ht
    have htu : ‖t • u‖ < 1 := by
      rw [norm_smul]
      calc ‖t‖ * ‖u‖ ≤ R * ‖u‖ := by gcongr
        _ < 1 := hRu
    have hE := hasDerivAt_exp_neg_log1p_smul u (hasDerivAt_log1p_smul (𝕂 := 𝕂) u hR hRu ht')
    have hlin : HasDerivAt (fun s : 𝕂 => 1 + s • u) u t := by
      simpa using ((hasDerivAt_id t).smul_const u).const_add 1
    have h := hE.mul hlin
    convert h using 1
    rw [mul_neg, neg_mul, mul_assoc, tsum_logTermDeriv_mul u htu, neg_add_cancel]
  have hconst := IsOpen.is_const_of_deriv_eq_zero Metric.isOpen_ball
    (convex_ball (0 : 𝕂) R).isPreconnected
    (fun t ht => (hF t ht).differentiableAt.differentiableWithinAt)
    (fun t ht => by simpa using (hF t ht).deriv)
    (mem_ball_zero_iff.mpr (by simpa using hR1) : (1 : 𝕂) ∈ Metric.ball 0 R)
    (Metric.mem_ball_self hR)
  simp only [F, one_smul, zero_smul, log1p_zero, neg_zero, exp_zero, add_zero, mul_one]
    at hconst
  calc exp (log1p 𝕂 u) = exp (log1p 𝕂 u) * (exp (-log1p 𝕂 u) * (1 + u)) := by
        rw [hconst, mul_one]
    _ = 1 + u := by rw [← mul_assoc, exp_mul_exp_neg 𝕂, one_mul]

end BakerCampbellHausdorff
