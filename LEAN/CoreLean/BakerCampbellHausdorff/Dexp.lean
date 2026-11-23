import BakerCampbellHausdorff.Operators
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Data.Nat.Choose.Sum

/-!
# The derivative of the exponential map of a Banach algebra

For a Banach algebra `𝔸` over `𝕂 = ℝ` or `ℂ`, not necessarily commutative, the exponential map
`exp : 𝔸 → 𝔸` has Fréchet derivative
`D exp(Z) V = e^Z · ((1 - e^{-ad Z}) / ad Z) V = exp Z * expSubOneDiv 𝕂 (-ad 𝕂 Z) V`.

## Main results

* `hasDerivAt_pow_of_hasDerivAt`: the noncommutative derivative of `s ↦ c s ^ n`.
* `hasDerivAt_exp_add_smul`: the directional derivative
  `d/dh exp (Z + h V) |_{h=0} = exp Z * expSubOneDiv 𝕂 (-ad 𝕂 Z) V`.
* `hasFDerivAt_exp`: `exp` has Fréchet derivative `mulLeft 𝕂 (exp Z) * expSubOneDiv 𝕂 (-ad 𝕂 Z)`
  at `Z`.

## Proof

1. Term-by-term differentiation (`hasDerivAt_tsum_of_isPreconnected`) of
   `exp (Z + h V) = ∑ₙ (Z + h V)ⁿ / n!` gives the derivative
   `∑ₙ (1 / n!) ∑_{i < n} Zⁱ V Z^(n-1-i)` at `h = 0`.
2. With `L = mulLeft 𝕂 Z`, `R = mulRight 𝕂 Z` and `d = R - L = -ad 𝕂 Z` in the Banach algebra
   `𝔸 →L[𝕂] 𝔸`, the operators `L` and `d` commute, and `Zⁱ V Zʲ = (Lⁱ Rʲ) V`.  The Cauchy
   product of `exp L = ∑ Lᵏ / k!` and `expSubOneDiv 𝕂 d = ∑ dᵐ / (m + 1)!` is
   `∑ₚ (1 / (p + 1)!) ∑_{k ≤ p} C(p + 1, k) Lᵏ d^(p-k)`, and the binomial identity
   `∑_{k ≤ p} C(p + 1, k) aᵏ d^(p-k) = ∑_{i ≤ p} aⁱ (a + d)^(p-i)` for commuting `a`, `d`
   (`sum_pow_mul_pow_mul_choose`) turns it into the series of step 1, applied to `V`.  Since
   `exp L = mulLeft 𝕂 (exp Z)`, this is `hasDerivAt_exp_add_smul`.
3. `exp` is analytic, hence differentiable; composing its derivative with the lines
   `h ↦ Z + h V` identifies it by uniqueness of derivatives.
-/

noncomputable section

open NormedSpace Finset
open scoped Nat

namespace BakerCampbellHausdorff

variable {𝕂 𝔸 : Type*} [RCLike 𝕂] [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [CompleteSpace 𝔸]

omit [CompleteSpace 𝔸] in
/-- Derivative of a power along a curve (noncommutative). -/
theorem hasDerivAt_pow_of_hasDerivAt {c : 𝕂 → 𝔸} {c' : 𝔸} {t : 𝕂} (hc : HasDerivAt c c' t)
    (n : ℕ) :
    HasDerivAt (fun s => c s ^ n) (∑ i ∈ Finset.range n, c t ^ i * c' * c t ^ (n - 1 - i)) t := by
  induction n with
  | zero => simpa using hasDerivAt_const t (1 : 𝔸)
  | succ n ih =>
    have h := ih.mul hc
    have e : (fun s => c s ^ (n + 1)) = (fun s => c s ^ n) * c := by
      funext s
      simp [pow_succ]
    rw [e]
    convert h using 1
    rw [Finset.sum_range_succ, Finset.sum_mul, Nat.add_sub_cancel, Nat.sub_self, pow_zero,
      mul_one]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : n - 1 - i + 1 = n - i := by
      have := Finset.mem_range.mp hi
      omega
    rw [mul_assoc (c t ^ i * c'), ← pow_succ, hi']

/-- The binomial identity `∑_{k ≤ p} C(p + 1, k) aᵏ d^(p-k) = ∑_{i ≤ p} aⁱ (a + d)^(p-i)` for
commuting `a` and `d`. -/
theorem sum_pow_mul_pow_mul_choose {R : Type*} [Ring R] {a d : R} (h : Commute a d) (p : ℕ) :
    ∑ k ∈ range (p + 1), a ^ k * d ^ (p - k) * ((p + 1).choose k : R) =
      ∑ i ∈ range (p + 1), a ^ i * (a + d) ^ (p - i) := by
  induction p with
  | zero => simp
  | succ p ih =>
    have hS : ∑ k ∈ range (p + 1 + 1), a ^ k * d ^ (p + 1 - k) * ((p + 1 + 1).choose k : R) =
        a * ∑ k ∈ range (p + 1), a ^ k * d ^ (p - k) * ((p + 1).choose k : R) +
          (a + d) ^ (p + 1) := by
      rw [h.add_pow, Finset.sum_range_succ' _ (p + 1), Finset.sum_range_succ' _ (p + 1),
        Finset.mul_sum, Nat.choose_zero_right, Nat.choose_zero_right,
        ← add_assoc, ← Finset.sum_add_distrib]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Nat.add_sub_add_right, Nat.choose_succ_succ,
        Nat.cast_add, mul_add, pow_succ']
      simp only [mul_assoc]
    have hT : ∑ i ∈ range (p + 1 + 1), a ^ i * (a + d) ^ (p + 1 - i) =
        a * ∑ i ∈ range (p + 1), a ^ i * (a + d) ^ (p - i) + (a + d) ^ (p + 1) := by
      rw [Finset.sum_range_succ', Finset.mul_sum, pow_zero, one_mul, Nat.sub_zero]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [pow_succ', mul_assoc, Nat.add_sub_add_right]
    rw [hS, hT, ih]

/-- The Cauchy product of `exp a = ∑ aᵏ / k!` and `expSubOneDiv 𝕂 d = ∑ dᵐ / (m + 1)!` for
commuting `a` and `d`: `exp a * expSubOneDiv 𝕂 d = ∑ₚ (1 / (p + 1)!) ∑_{i ≤ p} aⁱ (a + d)^(p-i)`. -/
theorem hasSum_exp_mul_expSubOneDiv {𝔹 : Type*} [NormedRing 𝔹] [NormedAlgebra 𝕂 𝔹]
    [CompleteSpace 𝔹] {a d : 𝔹} (h : Commute a d) :
    HasSum (fun p => ((p + 1)! : 𝕂)⁻¹ • ∑ i ∈ range (p + 1), a ^ i * (a + d) ^ (p - i))
      (exp a * expSubOneDiv 𝕂 d) := by
  have hc := hasSum_sum_range_mul_of_summable_norm (norm_expSeries_summable' (𝕂 := 𝕂) a)
    (summable_norm_expSubOneDiv (𝕂 := 𝕂) d)
  rw [(exp_series_hasSum_exp' (𝕂 := 𝕂) a).tsum_eq, (hasSum_expSubOneDiv (𝕂 := 𝕂) d).tsum_eq]
    at hc
  convert hc using 1
  funext p
  rw [← sum_pow_mul_pow_mul_choose h, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkp : k ≤ p := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have e : (((p + 1).choose k : ℕ) : 𝕂) * (k ! : 𝕂) * ((p - k + 1)! : 𝕂) = ((p + 1)! : 𝕂) := by
    have h1 := Nat.choose_mul_factorial_mul_factorial (Nat.le_succ_of_le hkp)
    rw [show p + 1 - k = p - k + 1 by omega] at h1
    exact_mod_cast h1
  have hC : (((p + 1).choose k : ℕ) : 𝕂) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.choose_pos (Nat.le_succ_of_le hkp)).ne'
  rw [smul_mul_smul_comm, ← Nat.cast_comm, ← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul 𝕂,
    smul_smul, ← e]
  congr 1
  field_simp

/-- The series of the directional derivative of `exp`:
`∑ₙ (1 / n!) ∑_{i < n} Zⁱ V Z^(n-1-i) = exp Z * expSubOneDiv 𝕂 (-ad 𝕂 Z) V`. -/
theorem hasSum_dexp_series (Z V : 𝔸) :
    HasSum (fun n => (n !⁻¹ : 𝕂) • ∑ i ∈ range n, Z ^ i * V * Z ^ (n - 1 - i))
      (exp Z * expSubOneDiv 𝕂 (-ad 𝕂 Z) V) := by
  have hcomm : Commute (mulLeft 𝕂 Z) (-ad 𝕂 Z) :=
    ((Commute.refl _).sub_right (commute_mulLeft_mulRight Z Z)).neg_right
  have hLd : mulLeft 𝕂 Z + -ad 𝕂 Z = mulRight 𝕂 Z := by
    rw [ad]
    abel
  have h1 := (hasSum_exp_mul_expSubOneDiv (𝕂 := 𝕂) hcomm).mapL
    (ContinuousLinearMap.apply 𝕂 𝔸 V)
  rw [exp_mulLeft, hLd] at h1
  simp only [ContinuousLinearMap.apply_apply, _root_.smul_apply,
    _root_.sum_apply, mul_apply_eq_comp, ← mulLeft_pow, ← mulRight_pow,
    mulLeft_apply, mulRight_apply] at h1
  rw [← hasSum_nat_add_iff' 1]
  simpa [← mul_assoc] using h1

omit [CompleteSpace 𝔸] in
/-- Without `‖1‖ = 1`: `‖xⁿ‖ ≤ max 1 ‖1‖ ‖x‖ⁿ` for all `n`, including `n = 0`. -/
theorem norm_pow_le_max_one_mul (x : 𝔸) (n : ℕ) : ‖x ^ n‖ ≤ max 1 ‖(1 : 𝔸)‖ * ‖x‖ ^ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact (norm_pow_le' x hn).trans (le_mul_of_one_le_left (by positivity) (le_max_left _ _))

/-- `n / n! ≤ 1 / (n - 1)!`. -/
theorem natCast_mul_inv_factorial_le (n : ℕ) : (n !⁻¹ : ℝ) * n ≤ ((n - 1)!⁻¹ : ℝ) := by
  rcases n with _ | k
  · simp
  · rw [Nat.factorial_succ, Nat.cast_mul, Nat.add_sub_cancel]
    field_simp
    rfl

omit [CompleteSpace 𝔸] in
/-- The bound on the derivative terms of `h ↦ (Z + h V)ⁿ / n!`. -/
theorem norm_dexp_term_le (y V : 𝔸) (n : ℕ) :
    ‖(n !⁻¹ : 𝕂) • ∑ i ∈ range n, y ^ i * V * y ^ (n - 1 - i)‖ ≤
      max 1 ‖(1 : 𝔸)‖ ^ 2 * ‖V‖ * (((n - 1)!⁻¹ : ℝ) * ‖y‖ ^ (n - 1)) := by
  set c := max 1 ‖(1 : 𝔸)‖
  have hc : 0 ≤ c := zero_le_one.trans (le_max_left _ _)
  have hterm : ∀ i ∈ range n, ‖y ^ i * V * y ^ (n - 1 - i)‖ ≤ c ^ 2 * ‖V‖ * ‖y‖ ^ (n - 1) := by
    intro i hi
    have hi' : i + (n - 1 - i) = n - 1 := by
      have := mem_range.mp hi
      omega
    calc ‖y ^ i * V * y ^ (n - 1 - i)‖ ≤ ‖y ^ i‖ * ‖V‖ * ‖y ^ (n - 1 - i)‖ := norm_mul₃_le
      _ ≤ (c * ‖y‖ ^ i) * ‖V‖ * (c * ‖y‖ ^ (n - 1 - i)) := by
          gcongr <;> exact norm_pow_le_max_one_mul _ _
      _ = c ^ 2 * ‖V‖ * ‖y‖ ^ (n - 1) := by
          rw [show ‖y‖ ^ (n - 1) = ‖y‖ ^ i * ‖y‖ ^ (n - 1 - i) by rw [← pow_add, hi']]
          ring
  have hsum : ‖∑ i ∈ range n, y ^ i * V * y ^ (n - 1 - i)‖ ≤
      n * (c ^ 2 * ‖V‖ * ‖y‖ ^ (n - 1)) := by
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hK : 0 ≤ c ^ 2 * ‖V‖ * ‖y‖ ^ (n - 1) := by positivity
  rw [norm_smul, norm_inv, RCLike.norm_natCast]
  calc (n !⁻¹ : ℝ) * ‖∑ i ∈ range n, y ^ i * V * y ^ (n - 1 - i)‖
      ≤ (n !⁻¹ : ℝ) * (n * (c ^ 2 * ‖V‖ * ‖y‖ ^ (n - 1))) := by gcongr
    _ = ((n !⁻¹ : ℝ) * n) * (c ^ 2 * ‖V‖ * ‖y‖ ^ (n - 1)) := by ring
    _ ≤ ((n - 1)!⁻¹ : ℝ) * (c ^ 2 * ‖V‖ * ‖y‖ ^ (n - 1)) := by
        gcongr
        exact natCast_mul_inv_factorial_le n
    _ = c ^ 2 * ‖V‖ * (((n - 1)!⁻¹ : ℝ) * ‖y‖ ^ (n - 1)) := by ring

omit [CompleteSpace 𝔸] in
/-- The line `s ↦ Z + s V` has derivative `V`. -/
theorem hasDerivAt_add_smul (Z V : 𝔸) (y : 𝕂) : HasDerivAt (fun s : 𝕂 => Z + s • V) V y := by
  simpa using ((hasDerivAt_id y).smul_const V).const_add Z

/-- Term-by-term differentiation of `h ↦ exp (Z + h V) = ∑ₙ (Z + h V)ⁿ / n!` at `h = 0`. -/
theorem hasDerivAt_exp_add_smul_of_hasSum (Z V : 𝔸) {D : 𝔸}
    (hD : HasSum (fun n => (n !⁻¹ : 𝕂) • ∑ i ∈ range n, Z ^ i * V * Z ^ (n - 1 - i)) D) :
    HasDerivAt (fun h : 𝕂 => exp (Z + h • V)) D 0 := by
  set c := max 1 ‖(1 : 𝔸)‖
  set M := ‖Z‖ + ‖V‖
  have hu : Summable fun n : ℕ => c ^ 2 * ‖V‖ * (((n - 1)!⁻¹ : ℝ) * M ^ (n - 1)) := by
    refine (summable_nat_add_iff 1).mp ?_
    simp only [Nat.add_sub_cancel]
    have h := (hasSum_real_exp M).summable
    simp only [smul_eq_mul] at h
    exact h.mul_left _
  have hbound : ∀ (n : ℕ), ∀ y ∈ Metric.ball (0 : 𝕂) 1,
      ‖(n !⁻¹ : 𝕂) • ∑ i ∈ range n, (Z + y • V) ^ i * V * (Z + y • V) ^ (n - 1 - i)‖ ≤
        c ^ 2 * ‖V‖ * (((n - 1)!⁻¹ : ℝ) * M ^ (n - 1)) := by
    intro n y hy
    have hy' : ‖y‖ < 1 := mem_ball_zero_iff.mp hy
    have hZy : ‖Z + y • V‖ ≤ M := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul]
      have := mul_le_of_le_one_left (norm_nonneg V) hy'.le
      simp only [M]
      linarith
    refine (norm_dexp_term_le (𝕂 := 𝕂) _ V n).trans ?_
    gcongr
  have h := hasDerivAt_tsum_of_isPreconnected
    (g := fun n (s : 𝕂) => (n !⁻¹ : 𝕂) • (Z + s • V) ^ n)
    (g' := fun n (s : 𝕂) =>
      (n !⁻¹ : 𝕂) • ∑ i ∈ range n, (Z + s • V) ^ i * V * (Z + s • V) ^ (n - 1 - i))
    hu Metric.isOpen_ball (convex_ball (0 : 𝕂) 1).isPreconnected
    (fun n y _ =>
      (hasDerivAt_pow_of_hasDerivAt (hasDerivAt_add_smul Z V y) n).const_smul (n !⁻¹ : 𝕂))
    hbound (Metric.mem_ball_self one_pos)
    (exp_series_hasSum_exp' (𝕂 := 𝕂) (Z + (0 : 𝕂) • V)).summable (Metric.mem_ball_self one_pos)
  simp only [zero_smul, add_zero] at h
  rw [hD.tsum_eq] at h
  exact h.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun z => (exp_series_hasSum_exp' (𝕂 := 𝕂) _).tsum_eq.symm)

/-- Directional derivative of `exp`: `D exp(Z) V = e^Z · (1 - e^{-ad Z})/ad Z · V`. -/
theorem hasDerivAt_exp_add_smul (Z V : 𝔸) :
    HasDerivAt (fun h : 𝕂 => exp (Z + h • V)) (exp Z * expSubOneDiv 𝕂 (-ad 𝕂 Z) V) 0 :=
  hasDerivAt_exp_add_smul_of_hasSum Z V (hasSum_dexp_series Z V)

/-- **Derivative of the exponential map** of a Banach algebra:
`D exp(Z) = mulLeft (exp Z) ∘ (1 - e^{-ad Z}) / ad Z`. -/
theorem hasFDerivAt_exp (Z : 𝔸) :
    HasFDerivAt (exp : 𝔸 → 𝔸) (mulLeft 𝕂 (exp Z) * expSubOneDiv 𝕂 (-ad 𝕂 Z)) Z := by
  obtain ⟨f', hf'⟩ := (exp_analytic (𝕂 := 𝕂) Z).differentiableAt
  convert hf' using 1
  ext V
  have h1 := hf'.comp_hasDerivAt_of_eq (0 : 𝕂) (hasDerivAt_add_smul Z V 0) (by simp)
  rw [mul_apply_eq_comp, mulLeft_apply]
  exact ((hasDerivAt_exp_add_smul Z V).unique h1)

end BakerCampbellHausdorff
