/-
`lem:chain-conditions` of BALABAN_CORE.tex (`a021c13be348`), two steps of its proof.

* `half_bound`: `L^{-s}(1 + β₀)s^{1/2} ≤ ½` for integers `s ≥ 1`, `L ≥ 3`, `1 + β₀ ≤ √2` (so that
  `(a_i/a_h)ρ_{0,h} ≤ ρ_{0,i}` for `i ≤ h`).
* `power_log_tendsto`: `x^{a - r}(1 + log x)^{1/2} → 0` as `x → ∞` for `a < r`; with the exponents
  `a ∈ {p₀ + a_ε - q₀, 0, q₁ - q₀}` (all `< r` by `eq:chain-exponents` and `p₀ + a_ε < q₀ + r`) this is the statement
  that `e(x)x^{-r}(1 + log x)^{1/2}` tends to zero, apart from the term `ω_h/ρ_{0,n}`.
-/
import Mathlib

open Filter Topology Asymptotics

noncomputable section

namespace CoreLean
namespace ChainConditionsArith

lemma nine_pow (s : ℕ) (hs : 1 ≤ s) : 8 * (s : ℝ) ≤ 9 ^ s := by
  induction s with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; norm_num
    · have := ih h
      have hn : (1 : ℝ) ≤ n := by exact_mod_cast h
      push_cast
      rw [pow_succ]
      nlinarith

/-- `L^{-s}(1 + β₀)s^{1/2} ≤ ½`. -/
theorem half_bound {L c : ℝ} (s : ℕ) (hs : 1 ≤ s) (hL : 3 ≤ L) (hc0 : 0 ≤ c) (hc : c ≤ Real.sqrt 2) :
    (L ^ s)⁻¹ * c * Real.sqrt s ≤ 1 / 2 := by
  have hLs : (3 : ℝ) ^ s ≤ L ^ s := pow_le_pow_left₀ (by norm_num) hL s
  have h3 : 0 < (3 : ℝ) ^ s := by positivity
  -- `2√2·√s ≤ 3^s`, from `8s ≤ 9^s`
  have key : 2 * (Real.sqrt 2 * Real.sqrt s) ≤ 3 ^ s := by
    have h8 := nine_pow s hs
    have hsq : (2 * (Real.sqrt 2 * Real.sqrt s)) ^ 2 = 8 * s := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt (Nat.cast_nonneg s)]; ring
    have h9 : ((3 : ℝ) ^ s) ^ 2 = 9 ^ s := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    exact (sq_le_sq₀ (by positivity) h3.le).1 (by rw [hsq, h9]; exact h8)
  have hcs : c * Real.sqrt s ≤ Real.sqrt 2 * Real.sqrt s := mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg _)
  rw [mul_assoc, inv_mul_le_iff₀ (by positivity)]
  nlinarith

/-- **`x^{a - r}(1 + log x)^{1/2} → 0`** for `a < r`. -/
theorem power_log_tendsto {a r : ℝ} (har : a < r) :
    Tendsto (fun x : ℝ => x ^ (a - r) * Real.sqrt (1 + Real.log x)) atTop (𝓝 0) := by
  set ε := r - a with hε
  have hε0 : 0 < ε := by linarith
  -- `√(1 + log x) ≤ 1 + log x ≤ C x^{ε/2}` eventually, and `x^{-ε}x^{ε/2} → 0`
  have hlog : (fun x : ℝ => 1 + Real.log x) =o[atTop] fun x => x ^ (ε / 2) := by
    have h1 := isLittleO_log_rpow_atTop (half_pos hε0)
    have h2 : (fun _ : ℝ => (1 : ℝ)) =o[atTop] fun x => x ^ (ε / 2) :=
      isLittleO_const_left.2 (Or.inr (tendsto_norm_atTop_atTop.comp (tendsto_rpow_atTop (half_pos hε0))))
    exact h2.add h1
  have hpow : Tendsto (fun x : ℝ => x ^ (a - r) * x ^ (ε / 2)) atTop (𝓝 0) := by
    have : (fun x : ℝ => x ^ (a - r) * x ^ (ε / 2)) =ᶠ[atTop] fun x => x ^ (-(ε / 2)) := by
      filter_upwards [eventually_gt_atTop 0] with x hx
      rw [← Real.rpow_add hx]; congr 1; rw [hε]; ring
    rw [tendsto_congr' this]
    exact tendsto_rpow_neg_atTop (half_pos hε0)
  -- squeeze: `0 ≤ x^{a-r}√(1 + log x) ≤ x^{a-r}(1 + log x)` for `x ≥ 1`
  have hbig : (fun x : ℝ => x ^ (a - r) * (1 + Real.log x)) =o[atTop] fun x => x ^ (a - r) * x ^ (ε / 2) :=
    (isBigO_refl (fun x : ℝ => x ^ (a - r)) atTop).mul_isLittleO hlog
  have hlim : Tendsto (fun x : ℝ => x ^ (a - r) * (1 + Real.log x)) atTop (𝓝 0) := hbig.trans_tendsto hpow
  apply squeeze_zero' _ _ hlim
  · filter_upwards [eventually_gt_atTop 0] with x hx
    positivity
  · filter_upwards [eventually_ge_atTop 1] with x hx
    have hl : 0 ≤ Real.log x := Real.log_nonneg hx
    have hs : Real.sqrt (1 + Real.log x) ≤ 1 + Real.log x := by
      rw [Real.sqrt_le_left (by linarith)]; nlinarith
    exact mul_le_mul_of_nonneg_left hs (by positivity)

end ChainConditionsArith
end CoreLean

end
