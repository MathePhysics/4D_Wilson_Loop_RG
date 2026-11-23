module

public import CoreLean.Vendor.HeatKernel
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Contour-shifted representation of the lattice heat kernel and its differences

`heatKernelC m t n = (1/2π) ∫_{-π}^{π} e^{inθ}(e^{iθ}-1)^m e^{-2t(1-cos θ)} dθ` is the `m`-th forward
difference of `n ↦ q_t(n)`.  The integrand is entire and `2π`-periodic, so the contour can be
shifted to `Im z = τ`; this gives the exponential bounds on `q_t` and its differences.

Provenance: copied from `Balaban/Green/Lattice/HeatKernelBounds.lean` of
https://github.com/scottnarmstrong/balaban-lean at commit
`493e9eb97292ebf6070c1c217a09bcf1adc23857`, Apache License 2.0 (`LICENSE-balaban-lean`); the only
change is the import path of `HeatKernel`.
-/

@[expose] public section

noncomputable section

namespace Balaban.LatticeGreen

open MeasureTheory Real Complex
open scoped Real

/-- The entire, `2π`-periodic integrand of the `m`-th difference of the heat kernel. -/
def heatIntegrandC (m : ℕ) (t : ℝ) (n : ℤ) (z : ℂ) : ℂ :=
  Complex.exp (Complex.I * n * z) * (Complex.exp (Complex.I * z) - 1) ^ m *
    Complex.exp (-(2 * (t : ℂ)) * (1 - Complex.cos z))

/-- The `m`-th forward difference `Δ^m q_t (n)` as a Fourier integral (complex valued). -/
def heatKernelC (m : ℕ) (t : ℝ) (n : ℤ) : ℂ :=
  (((2 * π : ℝ) : ℂ))⁻¹ * ∫ θ in (-π)..π, heatIntegrandC m t n (θ : ℂ)

/-- The `m`-th forward difference of `n ↦ q_t(n)`. -/
def heatDiff : ℕ → ℝ → ℤ → ℝ
  | 0, t, n => heatKernel1 t n
  | m + 1, t, n => heatDiff m t (n + 1) - heatDiff m t n

theorem differentiable_heatIntegrandC (m : ℕ) (t : ℝ) (n : ℤ) :
    Differentiable ℂ (heatIntegrandC m t n) := by
  unfold heatIntegrandC; fun_prop

theorem continuous_heatIntegrandC (m : ℕ) (t : ℝ) (n : ℤ) :
    Continuous (heatIntegrandC m t n) :=
  (differentiable_heatIntegrandC m t n).continuous

theorem heatIntegrandC_periodic (m : ℕ) (t : ℝ) (n : ℤ) (z : ℂ) :
    heatIntegrandC m t n (z + 2 * π) = heatIntegrandC m t n z := by
  unfold heatIntegrandC
  have h1 : Complex.exp (Complex.I * n * (z + 2 * π)) = Complex.exp (Complex.I * n * z) := by
    have : Complex.I * n * (z + 2 * π) = Complex.I * n * z + (n : ℂ) * (2 * π * Complex.I) := by
      ring
    rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have h2 : Complex.exp (Complex.I * (z + 2 * π)) = Complex.exp (Complex.I * z) := by
    have : Complex.I * (z + 2 * π) = Complex.I * z + 2 * π * Complex.I := by ring
    rw [this, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  have h3 : Complex.cos (z + 2 * π) = Complex.cos z := Complex.cos_add_two_pi z
  rw [h1, h2, h3]

/-- Shifting the contour of `∫_{-π}^{π}` by `τ i`. -/
theorem integral_heatIntegrandC_shift (m : ℕ) (t : ℝ) (n : ℤ) (τ : ℝ) :
    ∫ θ in (-π)..π, heatIntegrandC m t n ((θ : ℂ) + τ * Complex.I) =
      ∫ θ in (-π)..π, heatIntegrandC m t n (θ : ℂ) := by
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (heatIntegrandC m t n) ((-π : ℝ) : ℂ) ((π : ℝ) + τ * Complex.I)
    (differentiable_heatIntegrandC m t n).differentiableOn
  simp only [Complex.ofReal_re, Complex.add_re, Complex.mul_re, Complex.I_re, mul_zero,
    Complex.I_im, Complex.ofReal_im, mul_one, sub_self, add_zero, Complex.add_im, Complex.mul_im,
    zero_add] at h
  have hside : ∀ y : ℝ, heatIntegrandC m t n ((-π : ℝ) + y * Complex.I) =
      heatIntegrandC m t n ((π : ℝ) + y * Complex.I) := fun y => by
    have := heatIntegrandC_periodic m t n (((-π : ℝ) : ℂ) + y * Complex.I)
    rw [← this]; congr 1; push_cast; ring
  simp only [hside] at h
  simp only [Complex.ofReal_zero, zero_mul, add_zero] at h
  linear_combination (exp := 1) -h

theorem norm_exp_I_mul_int_mul_shift (n : ℤ) (θ τ : ℝ) :
    ‖Complex.exp (Complex.I * n * ((θ : ℂ) + τ * Complex.I))‖ = Real.exp (-(n * τ)) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

theorem norm_exp_I_shift_sub_one_le (θ τ : ℝ) (hτ : |τ| ≤ 1) :
    ‖Complex.exp (Complex.I * ((θ : ℂ) + τ * Complex.I)) - 1‖ ≤ 3 * (|θ| + |τ|) := by
  have e : Complex.exp (Complex.I * ((θ : ℂ) + τ * Complex.I)) - 1 =
      (Real.exp (-τ) : ℝ) * (Complex.exp (Complex.I * θ) - 1) + ((Real.exp (-τ) - 1 : ℝ) : ℂ) := by
    have : Complex.I * ((θ : ℂ) + τ * Complex.I) = Complex.I * θ + ((-τ : ℝ) : ℂ) := by
      push_cast; ring_nf; simp [Complex.I_sq]; ring
    rw [this, Complex.exp_add, ← Complex.ofReal_exp]
    push_cast; ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  have h1 : ‖((Real.exp (-τ) : ℝ) : ℂ) * (Complex.exp (Complex.I * θ) - 1)‖ ≤ 3 * |θ| := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have h2 : Real.exp (-τ) ≤ 3 := by
      have : Real.exp (-τ) ≤ Real.exp 1 :=
        Real.exp_le_exp.mpr (by linarith [neg_abs_le τ, abs_le.mp hτ |>.1, abs_le.mp hτ |>.2])
      linarith [Real.exp_one_lt_three]
    have h3 := norm_exp_I_mul_ofReal_sub_one_le (x := θ)
    rw [Real.norm_eq_abs] at h3
    exact mul_le_mul h2 h3 (norm_nonneg _) (by norm_num)
  have h4 : ‖((Real.exp (-τ) - 1 : ℝ) : ℂ)‖ ≤ 2 * |τ| := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    have := Real.abs_exp_sub_one_le (x := -τ) (by rwa [abs_neg])
    rwa [abs_neg] at this
  linarith [abs_nonneg θ, abs_nonneg τ]

theorem norm_exp_symbol_shift_le {t : ℝ} (ht : 0 ≤ t) (θ τ : ℝ) :
    ‖Complex.exp (-(2 * (t : ℂ)) * (1 - Complex.cos ((θ : ℂ) + τ * Complex.I)))‖ ≤
      Real.exp (2 * t * (Real.cosh τ - 1)) * heatSymbol t θ := by
  rw [Complex.norm_exp]
  have hre : (-(2 * (t : ℂ)) * (1 - Complex.cos ((θ : ℂ) + τ * Complex.I))).re =
      -(2 * t * (1 - Real.cos θ * Real.cosh τ)) := by
    rw [Complex.cos_add_mul_I]
    simp [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin, ← Complex.ofReal_cosh, ← Complex.ofReal_sinh]
  rw [hre, heatSymbol, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h1 : Real.cos θ ≤ 1 := Real.cos_le_one θ
  have h2 : 0 ≤ Real.cosh τ - 1 := by linarith [Real.one_le_cosh τ]
  nlinarith [mul_nonneg ht h2, mul_nonneg ht (mul_nonneg h2 (sub_nonneg.mpr h1))]

theorem integral_sin_mul_heatSymbol (t : ℝ) (n : ℤ) :
    ∫ θ in (-π)..π, Real.sin ((n : ℝ) * θ) * heatSymbol t θ = 0 := by
  set g : ℝ → ℝ := fun θ => Real.sin ((n : ℝ) * θ) * heatSymbol t θ with hg
  have hodd : ∀ x, g (-x) = -g x := fun x => by
    simp [hg, heatSymbol, mul_neg, Real.sin_neg, Real.cos_neg]
  have h := intervalIntegral.integral_comp_neg (a := -π) (b := π) g
  simp only [neg_neg] at h
  have h2 : ∫ x in (-π)..π, g (-x) = -∫ x in (-π)..π, g x := by
    simp_rw [hodd]; rw [intervalIntegral.integral_neg]
  rw [h2] at h
  linarith

theorem heatIntegrandC_zero_real (t : ℝ) (n : ℤ) (θ : ℝ) :
    heatIntegrandC 0 t n (θ : ℂ) =
      ((Real.cos ((n : ℝ) * θ) * heatSymbol t θ : ℝ) : ℂ) +
        Complex.I * ((Real.sin ((n : ℝ) * θ) * heatSymbol t θ : ℝ) : ℂ) := by
  unfold heatIntegrandC heatSymbol
  have : Complex.I * (n : ℂ) * (θ : ℂ) = (((n : ℝ) * θ : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.exp_mul_I, pow_zero, mul_one]
  have h2 : Complex.exp (-(2 * (t : ℂ)) * (1 - Complex.cos (θ : ℂ))) =
      ((Real.exp (-(2 * t * (1 - Real.cos θ))) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp]; push_cast; congr 1; ring
  rw [h2, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  push_cast; ring

theorem heatKernelC_zero (t : ℝ) (n : ℤ) : heatKernelC 0 t n = (heatKernel1 t n : ℂ) := by
  unfold heatKernelC heatKernel1
  simp_rw [heatIntegrandC_zero_real]
  have hc1 : Continuous fun θ : ℝ => Real.cos ((n : ℝ) * θ) * heatSymbol t θ := by
    unfold heatSymbol; fun_prop
  have hc2 : Continuous fun θ : ℝ => Real.sin ((n : ℝ) * θ) * heatSymbol t θ := by
    unfold heatSymbol; fun_prop
  have i1 : IntervalIntegrable (fun θ : ℝ => ((Real.cos ((n : ℝ) * θ) * heatSymbol t θ : ℝ) : ℂ))
      volume (-π) π := (Complex.continuous_ofReal.comp hc1).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun θ : ℝ => Complex.I *
      ((Real.sin ((n : ℝ) * θ) * heatSymbol t θ : ℝ) : ℂ)) volume (-π) π :=
    (continuous_const.mul (Complex.continuous_ofReal.comp hc2)).intervalIntegrable _ _
  rw [intervalIntegral.integral_add i1 i2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal,
    intervalIntegral.integral_ofReal, integral_sin_mul_heatSymbol]
  push_cast
  ring

theorem heatIntegrandC_succ (m : ℕ) (t : ℝ) (n : ℤ) (z : ℂ) :
    heatIntegrandC (m + 1) t n z = heatIntegrandC m t (n + 1) z - heatIntegrandC m t n z := by
  unfold heatIntegrandC
  have : Complex.exp (Complex.I * ((n + 1 : ℤ) : ℂ) * z) =
      Complex.exp (Complex.I * n * z) * Complex.exp (Complex.I * z) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [this]; ring

theorem heatKernelC_succ (m : ℕ) (t : ℝ) (n : ℤ) :
    heatKernelC (m + 1) t n = heatKernelC m t (n + 1) - heatKernelC m t n := by
  unfold heatKernelC
  simp_rw [heatIntegrandC_succ]
  have i1 : IntervalIntegrable (fun θ : ℝ => heatIntegrandC m t (n + 1) (θ : ℂ)) volume (-π) π :=
    ((continuous_heatIntegrandC m t (n + 1)).comp Complex.continuous_ofReal).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun θ : ℝ => heatIntegrandC m t n (θ : ℂ)) volume (-π) π :=
    ((continuous_heatIntegrandC m t n).comp Complex.continuous_ofReal).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub i1 i2]
  ring

theorem heatKernelC_eq_heatDiff (m : ℕ) (t : ℝ) :
    ∀ n : ℤ, heatKernelC m t n = (heatDiff m t n : ℂ) := by
  induction m with
  | zero => intro n; exact heatKernelC_zero t n
  | succ m ih => intro n; rw [heatKernelC_succ, ih, ih]; simp [heatDiff]

/-- The absolute moments `(1/2π) ∫_{-π}^{π} |θ|^k e^{-2t(1-cos θ)} dθ`. -/
def heatMoment (k : ℕ) (t : ℝ) : ℝ :=
  (2 * π)⁻¹ * ∫ θ in (-π)..π, |θ| ^ k * heatSymbol t θ

theorem add_pow_le_two_pow_mul (m : ℕ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) ^ m ≤ 2 ^ m * (a ^ m + b ^ m) := by
  rcases le_total a b with h | h
  · calc (a + b) ^ m ≤ (2 * b) ^ m := pow_le_pow_left₀ (by linarith) (by linarith) m
      _ = 2 ^ m * b ^ m := mul_pow _ _ _
      _ ≤ 2 ^ m * (a ^ m + b ^ m) := by
        gcongr; exact le_add_of_nonneg_left (pow_nonneg ha m)
  · calc (a + b) ^ m ≤ (2 * a) ^ m := pow_le_pow_left₀ (by linarith) (by linarith) m
      _ = 2 ^ m * a ^ m := mul_pow _ _ _
      _ ≤ 2 ^ m * (a ^ m + b ^ m) := by
        gcongr; exact le_add_of_nonneg_right (pow_nonneg hb m)

theorem continuous_heatMomentIntegrand (k : ℕ) (t : ℝ) :
    Continuous fun θ : ℝ => |θ| ^ k * heatSymbol t θ := by
  unfold heatSymbol; fun_prop

theorem heatMoment_nonneg (k : ℕ) {t : ℝ} : 0 ≤ heatMoment k t := by
  unfold heatMoment
  refine mul_nonneg (by positivity) (intervalIntegral.integral_nonneg (by linarith [Real.pi_pos]) ?_)
  intro θ _
  exact mul_nonneg (by positivity) (heatSymbol_pos t θ).le

theorem heatMoment_zero_le_one {t : ℝ} (ht : 0 ≤ t) : heatMoment 0 t ≤ 1 := by
  unfold heatMoment
  have h : ∫ θ in (-π)..π, |θ| ^ 0 * heatSymbol t θ ≤ ∫ θ in (-π)..π, (1 : ℝ) := by
    apply intervalIntegral.integral_mono_on (by linarith [Real.pi_pos])
      ((continuous_heatMomentIntegrand 0 t).intervalIntegrable _ _) intervalIntegrable_const
    intro θ _
    simpa using heatSymbol_le_one ht θ
  have h2 : ∫ _θ in (-π)..π, (1 : ℝ) = 2 * π := by simp; ring
  rw [h2] at h
  calc (2 * π)⁻¹ * ∫ θ in (-π)..π, |θ| ^ 0 * heatSymbol t θ ≤ (2 * π)⁻¹ * (2 * π) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = 1 := inv_mul_cancel₀ (by positivity)

theorem pow_mul_exp_neg_le {k : ℕ} (hk : k ≤ 2) {y : ℝ} :
    y ^ k * Real.exp (-(y ^ 2 / 2)) ≤ 2 := by
  have h1 : y ^ k ≤ 1 + y ^ 2 := by
    interval_cases k
    · simp; linarith [sq_nonneg y]
    · nlinarith [sq_nonneg (y - 1)]
    · linarith
  have h2 : 1 + y ^ 2 / 2 ≤ Real.exp (y ^ 2 / 2) := by linarith [Real.add_one_le_exp (y ^ 2 / 2)]
  have h3 : y ^ k ≤ 2 * Real.exp (y ^ 2 / 2) := by linarith
  have h4 : Real.exp (-(y ^ 2 / 2)) * Real.exp (y ^ 2 / 2) = 1 := by
    rw [← Real.exp_add]; simp
  calc y ^ k * Real.exp (-(y ^ 2 / 2)) ≤ 2 * Real.exp (y ^ 2 / 2) * Real.exp (-(y ^ 2 / 2)) :=
        mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
    _ = 2 := by rw [mul_assoc, mul_comm (Real.exp _), h4, mul_one]

theorem gaussian_moment_le {b : ℝ} (hb : 0 < b) {k : ℕ} (hk : k ≤ 2) :
    ∫ θ in (-π)..π, |θ| ^ k * Real.exp (-(b * θ ^ 2)) ≤
      2 * ((Real.sqrt b)⁻¹) ^ k * Real.sqrt (2 * π / b) := by
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  have hpt : ∀ θ : ℝ, |θ| ^ k * Real.exp (-(b * θ ^ 2)) ≤
      2 * ((Real.sqrt b)⁻¹) ^ k * Real.exp (-(b / 2 * θ ^ 2)) := by
    intro θ
    have h := pow_mul_exp_neg_le hk (y := Real.sqrt b * |θ|)
    have e1 : (Real.sqrt b * |θ|) ^ 2 / 2 = b / 2 * θ ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hb.le, sq_abs]; ring
    rw [e1, mul_pow] at h
    have e2 : Real.exp (-(b * θ ^ 2)) = Real.exp (-(b / 2 * θ ^ 2)) * Real.exp (-(b / 2 * θ ^ 2)) := by
      rw [← Real.exp_add]; congr 1; ring
    have e3 : |θ| ^ k = ((Real.sqrt b)⁻¹) ^ k * (Real.sqrt b ^ k * |θ| ^ k) := by
      rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hsb.ne', one_pow, one_mul]
    rw [e2, e3]
    have hp : 0 ≤ Real.exp (-(b / 2 * θ ^ 2)) := (Real.exp_pos _).le
    have hq : 0 ≤ ((Real.sqrt b)⁻¹) ^ k := by positivity
    calc ((Real.sqrt b)⁻¹) ^ k * (Real.sqrt b ^ k * |θ| ^ k) *
          (Real.exp (-(b / 2 * θ ^ 2)) * Real.exp (-(b / 2 * θ ^ 2)))
        = ((Real.sqrt b)⁻¹) ^ k * ((Real.sqrt b ^ k * |θ| ^ k) * Real.exp (-(b / 2 * θ ^ 2))) *
          Real.exp (-(b / 2 * θ ^ 2)) := by ring
      _ ≤ ((Real.sqrt b)⁻¹) ^ k * 2 * Real.exp (-(b / 2 * θ ^ 2)) := by gcongr
      _ = _ := by ring
  have hint : MeasureTheory.Integrable (fun θ : ℝ => Real.exp (-(b / 2 * θ ^ 2))) := by
    have := integrable_exp_neg_mul_sq (b := b / 2) (by positivity)
    simpa only [neg_mul] using this
  calc ∫ θ in (-π)..π, |θ| ^ k * Real.exp (-(b * θ ^ 2))
      ≤ ∫ θ in (-π)..π, 2 * ((Real.sqrt b)⁻¹) ^ k * Real.exp (-(b / 2 * θ ^ 2)) := by
        apply intervalIntegral.integral_mono_on (by linarith [Real.pi_pos])
        · exact (by fun_prop : Continuous fun θ : ℝ => |θ| ^ k * Real.exp (-(b * θ ^ 2))).intervalIntegrable _ _
        · exact (by fun_prop : Continuous fun θ : ℝ =>
            2 * ((Real.sqrt b)⁻¹) ^ k * Real.exp (-(b / 2 * θ ^ 2))).intervalIntegrable _ _
        · intro θ _; exact hpt θ
    _ = 2 * ((Real.sqrt b)⁻¹) ^ k * ∫ θ in (-π)..π, Real.exp (-(b / 2 * θ ^ 2)) := by
        rw [intervalIntegral.integral_const_mul]
    _ ≤ 2 * ((Real.sqrt b)⁻¹) ^ k * ∫ θ : ℝ, Real.exp (-(b / 2 * θ ^ 2)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
        exact MeasureTheory.setIntegral_le_integral hint
          (Filter.Eventually.of_forall fun θ => (Real.exp_pos _).le)
    _ = 2 * ((Real.sqrt b)⁻¹) ^ k * Real.sqrt (2 * π / b) := by
        congr 1
        have := integral_gaussian (b / 2)
        simp_rw [neg_mul] at this ⊢
        rw [this]; congr 1; field_simp

theorem heatSymbol_le_gaussian {t : ℝ} (ht : 0 ≤ t) {θ : ℝ} (hθ : |θ| ≤ π) :
    heatSymbol t θ ≤ Real.exp (-(4 * t / π ^ 2 * θ ^ 2)) := by
  unfold heatSymbol
  apply Real.exp_le_exp.mpr
  have h := Real.cos_le_one_sub_mul_cos_sq hθ
  have h3 : 2 / π ^ 2 * θ ^ 2 ≤ 1 - Real.cos θ := by linarith
  have h4 : 2 * t * (2 / π ^ 2 * θ ^ 2) ≤ 2 * t * (1 - Real.cos θ) :=
    mul_le_mul_of_nonneg_left h3 (by linarith)
  have h5 : 2 * t * (2 / π ^ 2 * θ ^ 2) = 4 * t / π ^ 2 * θ ^ 2 := by ring
  linarith

theorem heatMoment_le {k : ℕ} (hk : k ≤ 2) {t : ℝ} (ht : 0 < t) :
    heatMoment k t ≤ 4 * ((Real.sqrt t)⁻¹) ^ (k + 1) := by
  set s := Real.sqrt t with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr ht
  have hst : s ^ 2 = t := Real.sq_sqrt ht.le
  set b : ℝ := 4 * t / π ^ 2 with hb
  have hb0 : 0 < b := by positivity
  have hsb : Real.sqrt b = 2 * s / π := by
    rw [hb, ← hst]
    rw [show 4 * s ^ 2 / π ^ 2 = (2 * s / π) ^ 2 by ring]
    exact Real.sqrt_sq (by positivity)
  have h1 : ∫ θ in (-π)..π, |θ| ^ k * heatSymbol t θ ≤
      ∫ θ in (-π)..π, |θ| ^ k * Real.exp (-(b * θ ^ 2)) := by
    apply intervalIntegral.integral_mono_on (by linarith [Real.pi_pos])
    · exact (continuous_heatMomentIntegrand k t).intervalIntegrable _ _
    · exact (by fun_prop : Continuous fun θ : ℝ => |θ| ^ k * Real.exp (-(b * θ ^ 2))).intervalIntegrable _ _
    · intro θ hθ
      have hθ' : |θ| ≤ π := abs_le.mpr ⟨hθ.1, hθ.2⟩
      exact mul_le_mul_of_nonneg_left (heatSymbol_le_gaussian ht.le hθ') (by positivity)
  have h2 := gaussian_moment_le hb0 hk
  rw [hsb] at h2
  have h3 : Real.sqrt (2 * π / b) = Real.sqrt (2 * π) * (π / (2 * s)) := by
    rw [Real.sqrt_div (by positivity), hsb]
    field_simp
  rw [h3] at h2
  have hpi := Real.pi_lt_d2
  have h4 : Real.sqrt (2 * π) ≤ 3 := by
    rw [Real.sqrt_le_left (by norm_num)]; nlinarith
  have hpi0 := Real.pi_pos
  unfold heatMoment
  calc (2 * π)⁻¹ * ∫ θ in (-π)..π, |θ| ^ k * heatSymbol t θ
      ≤ (2 * π)⁻¹ * (2 * ((2 * s / π)⁻¹) ^ k * (Real.sqrt (2 * π) * (π / (2 * s)))) :=
        mul_le_mul_of_nonneg_left (h1.trans h2) (by positivity)
    _ = (π / 2) ^ k * Real.sqrt (2 * π) / 2 * (s⁻¹) ^ (k + 1) := by
        have e : ((2 * s / π)⁻¹) ^ k = (π / 2) ^ k * (s⁻¹) ^ k := by
          rw [← mul_pow]; congr 1; field_simp
        rw [e, pow_succ]
        field_simp
    _ ≤ 4 * (s⁻¹) ^ (k + 1) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have h5 : (π / 2) ^ k ≤ 2.5 := by
          have h6 : π / 2 ≤ 1.58 := by linarith
          interval_cases k
          · norm_num
          · norm_num; linarith
          · nlinarith
        have h7 : 0 ≤ (π / 2) ^ k := by positivity
        have h8 := Real.sqrt_nonneg (2 * π)
        nlinarith

theorem norm_heatIntegrandC_shift_le (m : ℕ) {t : ℝ} (ht : 0 ≤ t) (n : ℤ) {τ : ℝ} (hτ : |τ| ≤ 1)
    (θ : ℝ) :
    ‖heatIntegrandC m t n ((θ : ℂ) + τ * Complex.I)‖ ≤
      Real.exp (-(n * τ) + 2 * t * (Real.cosh τ - 1)) * 6 ^ m *
        (|θ| ^ m * heatSymbol t θ + |τ| ^ m * (|θ| ^ 0 * heatSymbol t θ)) := by
  unfold heatIntegrandC
  rw [norm_mul, norm_mul, norm_pow, norm_exp_I_mul_int_mul_shift]
  have h1 := norm_exp_I_shift_sub_one_le θ τ hτ
  have h2 := norm_exp_symbol_shift_le ht θ τ
  have h3 : ‖Complex.exp (Complex.I * ((θ : ℂ) + τ * Complex.I)) - 1‖ ^ m ≤
      (3 * (|θ| + |τ|)) ^ m := pow_le_pow_left₀ (norm_nonneg _) h1 m
  have h4 : (3 * (|θ| + |τ|)) ^ m ≤ 6 ^ m * (|θ| ^ m + |τ| ^ m) := by
    rw [mul_pow]
    have := add_pow_le_two_pow_mul m (abs_nonneg θ) (abs_nonneg τ)
    calc 3 ^ m * (|θ| + |τ|) ^ m ≤ 3 ^ m * (2 ^ m * (|θ| ^ m + |τ| ^ m)) := by gcongr
      _ = 6 ^ m * (|θ| ^ m + |τ| ^ m) := by rw [← mul_assoc, ← mul_pow]; norm_num
  have hS := (heatSymbol_pos t θ).le
  have hE := (Real.exp_pos (-(n * τ))).le
  calc Real.exp (-(n * τ)) * ‖Complex.exp (Complex.I * ((θ : ℂ) + τ * Complex.I)) - 1‖ ^ m *
        ‖Complex.exp (-(2 * (t : ℂ)) * (1 - Complex.cos ((θ : ℂ) + τ * Complex.I)))‖
      ≤ Real.exp (-(n * τ)) * (6 ^ m * (|θ| ^ m + |τ| ^ m)) *
          (Real.exp (2 * t * (Real.cosh τ - 1)) * heatSymbol t θ) := by
        gcongr
        exact h3.trans h4
    _ = _ := by
        rw [show -(n * τ) + 2 * t * (Real.cosh τ - 1) =
          -(n * τ) + 2 * t * (Real.cosh τ - 1) from rfl, Real.exp_add]
        simp only [pow_zero, one_mul]
        ring

theorem norm_heatKernelC_le (m : ℕ) {t : ℝ} (ht : 0 ≤ t) (n : ℤ) {τ : ℝ} (hτ : |τ| ≤ 1) :
    ‖heatKernelC m t n‖ ≤
      Real.exp (-(n * τ) + 2 * t * (Real.cosh τ - 1)) * 6 ^ m *
        (heatMoment m t + |τ| ^ m * heatMoment 0 t) := by
  set E := Real.exp (-(n * τ) + 2 * t * (Real.cosh τ - 1)) with hE
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hshift := integral_heatIntegrandC_shift m t n τ
  unfold heatKernelC
  rw [norm_mul, ← hshift]
  have hpi : (0 : ℝ) < 2 * π := by positivity
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpi]
  have hle : ‖∫ θ in (-π)..π, heatIntegrandC m t n ((θ : ℂ) + τ * Complex.I)‖ ≤
      ∫ θ in (-π)..π, E * 6 ^ m * (|θ| ^ m * heatSymbol t θ + |τ| ^ m * (|θ| ^ 0 * heatSymbol t θ)) := by
    apply intervalIntegral.norm_integral_le_of_norm_le (by linarith [Real.pi_pos])
    · exact Filter.Eventually.of_forall fun θ _ => norm_heatIntegrandC_shift_le m ht n hτ θ
    · exact (by unfold heatSymbol; fun_prop : Continuous fun θ : ℝ =>
        E * 6 ^ m * (|θ| ^ m * heatSymbol t θ + |τ| ^ m * (|θ| ^ 0 * heatSymbol t θ))).intervalIntegrable _ _
  have hint : ∫ θ in (-π)..π, E * 6 ^ m * (|θ| ^ m * heatSymbol t θ + |τ| ^ m * (|θ| ^ 0 * heatSymbol t θ))
      = E * 6 ^ m * ((2 * π) * heatMoment m t + |τ| ^ m * ((2 * π) * heatMoment 0 t)) := by
    have i1 : IntervalIntegrable (fun θ : ℝ => |θ| ^ m * heatSymbol t θ) volume (-π) π :=
      (continuous_heatMomentIntegrand m t).intervalIntegrable _ _
    have i2 : IntervalIntegrable (fun θ : ℝ => |τ| ^ m * (|θ| ^ 0 * heatSymbol t θ)) volume
        (-π) π := (continuous_const.mul (continuous_heatMomentIntegrand 0 t)).intervalIntegrable _ _
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add i1 i2,
      intervalIntegral.integral_const_mul]
    unfold heatMoment
    rw [mul_inv_cancel_left₀ hpi.ne', mul_inv_cancel_left₀ hpi.ne']
  calc (2 * π)⁻¹ * ‖∫ θ in (-π)..π, heatIntegrandC m t n ((θ : ℂ) + τ * Complex.I)‖
      ≤ (2 * π)⁻¹ * (E * 6 ^ m * ((2 * π) * heatMoment m t + |τ| ^ m * ((2 * π) * heatMoment 0 t))) :=
        mul_le_mul_of_nonneg_left (hle.trans_eq hint) (by positivity)
    _ = E * 6 ^ m * (heatMoment m t + |τ| ^ m * heatMoment 0 t) := by
        field_simp

theorem cosh_sub_one_le_sq {x : ℝ} (hx : |x| ≤ 1) : Real.cosh x - 1 ≤ x ^ 2 := by
  have h1 := Real.cosh_le_exp_half_sq x
  have hx2 : x ^ 2 ≤ 1 := by
    have := sq_le_one_iff_abs_le_one x |>.mpr hx
    exact this
  have h2 : Real.exp (x ^ 2 / 2) ≤ 1 + x ^ 2 := by
    rcases eq_or_lt_of_le (sq_nonneg x) with h0 | hpos
    · rw [← h0]; simp
    · have h3 := Real.exp_bound_div_one_sub_of_interval' (x := x ^ 2 / 2) (by positivity)
        (by linarith)
      have h4 : 1 / (1 - x ^ 2 / 2) ≤ 1 + x ^ 2 := by
        rw [div_le_iff₀ (by linarith)]
        nlinarith
      linarith
  linarith

theorem pow_le_const_mul_exp_neg {m : ℕ} (hm : m ≤ 2) {a : ℝ} (ha : 0 ≤ a) :
    a ^ m * Real.exp (-(a / 4)) ≤ 33 := by
  have h1 : a ^ m ≤ 1 + a ^ 2 := by
    interval_cases m
    · simp; linarith [sq_nonneg a]
    · nlinarith [sq_nonneg (a - 1)]
    · linarith
  have h2 : (a / 4) ^ 2 / 2 ≤ Real.exp (a / 4) := by
    have := Real.pow_div_factorial_le_exp (a / 4) (by positivity) 2
    simpa [Nat.factorial] using this
  have h3 : 1 ≤ Real.exp (a / 4) := Real.one_le_exp (by positivity)
  have h4 : a ^ m ≤ 33 * Real.exp (a / 4) := by nlinarith
  have h5 : Real.exp (-(a / 4)) * Real.exp (a / 4) = 1 := by rw [← Real.exp_add]; simp
  calc a ^ m * Real.exp (-(a / 4)) ≤ 33 * Real.exp (a / 4) * Real.exp (-(a / 4)) :=
        mul_le_mul_of_nonneg_right h4 (Real.exp_pos _).le
    _ = 33 := by rw [mul_assoc, mul_comm (Real.exp (a / 4)), h5, mul_one]

theorem exists_shift_param (n : ℤ) {τ0 : ℝ} (h0 : 0 ≤ τ0) :
    ∃ τ : ℝ, |τ| = τ0 ∧ (n : ℝ) * τ = |(n : ℝ)| * τ0 ∧ Real.cosh τ = Real.cosh τ0 := by
  by_cases hn : 0 ≤ n
  · refine ⟨τ0, abs_of_nonneg h0, ?_, rfl⟩
    rw [abs_of_nonneg (by exact_mod_cast hn)]
  · refine ⟨-τ0, by rw [abs_neg, abs_of_nonneg h0], ?_, Real.cosh_neg τ0⟩
    have : (n : ℝ) < 0 := by exact_mod_cast not_le.mp hn
    rw [abs_of_neg this]; ring

theorem abs_heatDiff_le_large {m : ℕ} (hm : m ≤ 2) {t : ℝ} (ht : 1 ≤ t) (n : ℤ) :
    |heatDiff m t n| ≤ 5000 * ((Real.sqrt t)⁻¹) ^ (m + 1) *
      (Real.exp (-((n : ℝ) ^ 2 / (16 * t))) + Real.exp (-(|(n : ℝ)| / 4))) := by
  have ht0 : 0 < t := by linarith
  set s := Real.sqrt t with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr ht0
  have hst : s ^ 2 = t := Real.sq_sqrt ht0.le
  have hs1 : 1 ≤ s := by
    by_contra h
    have h := not_le.mp h
    nlinarith
  set a := |(n : ℝ)| with ha
  have ha0 : 0 ≤ a := abs_nonneg _
  have hn2 : (n : ℝ) ^ 2 = a ^ 2 := (sq_abs _).symm
  have hnorm : |heatDiff m t n| = ‖heatKernelC m t n‖ := by
    rw [heatKernelC_eq_heatDiff, Complex.norm_real, Real.norm_eq_abs]
  rw [hnorm, hn2]
  set τ0 := min (a / (4 * t)) 1 with hτ0
  have hτ00 : 0 ≤ τ0 := le_min (by positivity) zero_le_one
  have hτ01 : τ0 ≤ 1 := min_le_right _ _
  obtain ⟨τ, hτabs, hnτ, hcosh⟩ := exists_shift_param n hτ00
  have hτ : |τ| ≤ 1 := hτabs ▸ hτ01
  have hmain := norm_heatKernelC_le m ht0.le n hτ
  rw [hnτ, hcosh, hτabs] at hmain
  have hMm := heatMoment_le hm ht0
  have hM0 := heatMoment_le (k := 0) (Nat.zero_le 2) ht0
  rw [← hs] at hMm hM0
  have h6 : (6 : ℝ) ^ m ≤ 36 := by
    calc (6 : ℝ) ^ m ≤ 6 ^ 2 := pow_le_pow_right₀ (by norm_num) hm
      _ = 36 := by norm_num
  have hsum : heatMoment m t + τ0 ^ m * heatMoment 0 t ≤
      4 * (s⁻¹) ^ (m + 1) + τ0 ^ m * (4 * (s⁻¹) ^ (0 + 1)) := by
    have := mul_le_mul_of_nonneg_left hM0 (pow_nonneg hτ00 m)
    linarith
  have hX : 0 ≤ Real.exp (-(a * τ0) + 2 * t * (Real.cosh τ0 - 1)) * 6 ^ m := by positivity
  have hmain2 : ‖heatKernelC m t n‖ ≤
      Real.exp (-(a * τ0) + 2 * t * (Real.cosh τ0 - 1)) * 6 ^ m *
        (4 * (s⁻¹) ^ (m + 1) + τ0 ^ m * (4 * (s⁻¹) ^ (0 + 1))) :=
    hmain.trans (mul_le_mul_of_nonneg_left hsum hX)
  have hsi : 0 < s⁻¹ := inv_pos.mpr hs0
  have hsip : 0 < (s⁻¹) ^ (m + 1) := pow_pos hsi _
  by_cases hcase : a ≤ 4 * t
  · -- Gaussian regime
    have hτ0e : τ0 = a / (4 * t) := min_eq_left (by rw [div_le_one (by positivity)]; exact hcase)
    have hcsh := cosh_sub_one_le_sq (x := τ0) (by rw [abs_of_nonneg hτ00]; exact hτ01)
    have hexp : -(a * τ0) + 2 * t * (Real.cosh τ0 - 1) ≤ -(a ^ 2 / (16 * t)) - a ^ 2 / (16 * t) := by
      have h1 : 2 * t * (Real.cosh τ0 - 1) ≤ 2 * t * τ0 ^ 2 :=
        mul_le_mul_of_nonneg_left hcsh (by linarith)
      have h2 : a * τ0 = a ^ 2 / (4 * t) := by rw [hτ0e]; ring
      have h3 : 2 * t * τ0 ^ 2 = a ^ 2 / (8 * t) := by rw [hτ0e]; field_simp; ring
      have h4 : a ^ 2 / (4 * t) - a ^ 2 / (8 * t) = a ^ 2 / (8 * t) := by field_simp; ring
      have h5 : a ^ 2 / (16 * t) + a ^ 2 / (16 * t) = a ^ 2 / (8 * t) := by field_simp; ring
      linarith
    set w := a / (s * Real.sqrt 8) with hw
    have hw2 : w ^ 2 / 2 = a ^ 2 / (16 * t) := by
      rw [hw, div_pow, mul_pow, hst, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 8)]; field_simp; ring
    have hwm : (a / (4 * s)) ^ m ≤ w ^ m := by
      apply pow_le_pow_left₀ (by positivity)
      rw [hw]
      apply div_le_div_of_nonneg_left ha0 (by positivity)
      have h8 := Real.sq_sqrt (show (0 : ℝ) ≤ 8 by norm_num)
      have h8' := Real.sqrt_nonneg 8
      have : Real.sqrt 8 ≤ 4 := by nlinarith
      nlinarith
    have hτm : τ0 ^ m = (a / (4 * s)) ^ m * (s⁻¹) ^ m := by
      rw [← mul_pow, hτ0e, ← hst]; congr 1; field_simp
    have hterm : τ0 ^ m * (4 * (s⁻¹) ^ (0 + 1)) = 4 * (s⁻¹) ^ (m + 1) * (a / (4 * s)) ^ m := by
      rw [hτm]; simp only [zero_add, pow_succ]; ring
    have hkey : (a / (4 * s)) ^ m * Real.exp (-(a ^ 2 / (16 * t)) - a ^ 2 / (16 * t)) ≤
        2 * Real.exp (-(a ^ 2 / (16 * t))) := by
      have h := pow_mul_exp_neg_le hm (y := w)
      rw [hw2] at h
      have hq : Real.exp (-(a ^ 2 / (16 * t)) - a ^ 2 / (16 * t)) =
          Real.exp (-(a ^ 2 / (16 * t))) * Real.exp (-(a ^ 2 / (16 * t))) := by
        rw [← Real.exp_add]; congr 1
      rw [hq]
      have hp := (Real.exp_pos (-(a ^ 2 / (16 * t)))).le
      calc (a / (4 * s)) ^ m * (Real.exp (-(a ^ 2 / (16 * t))) * Real.exp (-(a ^ 2 / (16 * t))))
          ≤ w ^ m * (Real.exp (-(a ^ 2 / (16 * t))) * Real.exp (-(a ^ 2 / (16 * t)))) := by gcongr
        _ = (w ^ m * Real.exp (-(a ^ 2 / (16 * t)))) * Real.exp (-(a ^ 2 / (16 * t))) := by ring
        _ ≤ 2 * Real.exp (-(a ^ 2 / (16 * t))) := by gcongr
    have hE1 : Real.exp (-(a * τ0) + 2 * t * (Real.cosh τ0 - 1)) ≤
        Real.exp (-(a ^ 2 / (16 * t)) - a ^ 2 / (16 * t)) := Real.exp_le_exp.mpr hexp
    have hE2 : Real.exp (-(a ^ 2 / (16 * t)) - a ^ 2 / (16 * t)) ≤ Real.exp (-(a ^ 2 / (16 * t))) :=
      Real.exp_le_exp.mpr (by have : 0 ≤ a ^ 2 / (16 * t) := by positivity
                              linarith)
    rw [hterm] at hmain2
    have hexp0 := Real.exp_pos (-(a ^ 2 / (16 * t)))
    have hexp1 := Real.exp_pos (-(a / 4))
    calc ‖heatKernelC m t n‖
        ≤ Real.exp (-(a * τ0) + 2 * t * (Real.cosh τ0 - 1)) * 6 ^ m *
          (4 * (s⁻¹) ^ (m + 1) + 4 * (s⁻¹) ^ (m + 1) * (a / (4 * s)) ^ m) := hmain2
      _ ≤ Real.exp (-(a ^ 2 / (16 * t)) - a ^ 2 / (16 * t)) * 36 *
          (4 * (s⁻¹) ^ (m + 1) + 4 * (s⁻¹) ^ (m + 1) * (a / (4 * s)) ^ m) := by gcongr
      _ = 144 * (s⁻¹) ^ (m + 1) * (Real.exp (-(a ^ 2 / (16 * t)) - a ^ 2 / (16 * t)) +
            (a / (4 * s)) ^ m * Real.exp (-(a ^ 2 / (16 * t)) - a ^ 2 / (16 * t))) := by ring
      _ ≤ 144 * (s⁻¹) ^ (m + 1) * (Real.exp (-(a ^ 2 / (16 * t))) +
            2 * Real.exp (-(a ^ 2 / (16 * t)))) := by gcongr
      _ ≤ 5000 * (s⁻¹) ^ (m + 1) *
          (Real.exp (-(a ^ 2 / (16 * t))) + Real.exp (-(a / 4))) := by
          linarith [mul_nonneg hsip.le hexp1.le, mul_nonneg hsip.le hexp0.le]
  · -- exponential regime
    have hcase := not_le.mp hcase
    have hτ0e : τ0 = 1 := min_eq_right (by rw [le_div_iff₀ (by positivity)]; linarith)
    have hexp : -(a * τ0) + 2 * t * (Real.cosh τ0 - 1) ≤ -(a / 4) - a / 4 := by
      have hcsh := cosh_sub_one_le_sq (x := τ0) (by rw [abs_of_nonneg hτ00]; exact hτ01)
      rw [hτ0e] at hcsh ⊢
      nlinarith
    have hss : s ≤ a := by nlinarith
    have hsm : (s⁻¹) ^ (0 + 1) = (s⁻¹) ^ (m + 1) * s ^ m := by
      have h1 : (s⁻¹) ^ m * s ^ m = 1 := by
        rw [← mul_pow, inv_mul_cancel₀ hs0.ne', one_pow]
      calc (s⁻¹) ^ (0 + 1) = s⁻¹ * ((s⁻¹) ^ m * s ^ m) := by rw [h1]; simp
        _ = (s⁻¹) ^ (m + 1) * s ^ m := by ring
    have hsma : s ^ m ≤ a ^ m := pow_le_pow_left₀ hs0.le hss m
    rw [hτ0e] at hmain2 hexp
    simp only [one_pow, one_mul, hsm] at hmain2
    have hq : Real.exp (-(a / 4) - a / 4) = Real.exp (-(a / 4)) * Real.exp (-(a / 4)) := by
      rw [← Real.exp_add]; congr 1
    have hc := pow_le_const_mul_exp_neg hm ha0
    have hE1 : Real.exp (-(a * 1) + 2 * t * (Real.cosh 1 - 1)) ≤ Real.exp (-(a / 4) - a / 4) :=
      Real.exp_le_exp.mpr hexp
    have hexp0 := Real.exp_pos (-(a ^ 2 / (16 * t)))
    have hexp1 := Real.exp_pos (-(a / 4))
    calc ‖heatKernelC m t n‖
        ≤ Real.exp (-(a * 1) + 2 * t * (Real.cosh 1 - 1)) * 6 ^ m *
          (4 * (s⁻¹) ^ (m + 1) + 4 * ((s⁻¹) ^ (m + 1) * s ^ m)) := hmain2
      _ ≤ Real.exp (-(a / 4) - a / 4) * 36 *
          (4 * (s⁻¹) ^ (m + 1) + 4 * ((s⁻¹) ^ (m + 1) * a ^ m)) := by gcongr
      _ = 144 * (s⁻¹) ^ (m + 1) * (Real.exp (-(a / 4)) * (Real.exp (-(a / 4)) +
            a ^ m * Real.exp (-(a / 4)))) := by rw [hq]; ring
      _ ≤ 144 * (s⁻¹) ^ (m + 1) * (Real.exp (-(a / 4)) * (1 + 33)) := by
          gcongr
          have : Real.exp (-(a / 4)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
          linarith
      _ ≤ 5000 * (s⁻¹) ^ (m + 1) *
          (Real.exp (-(a ^ 2 / (16 * t))) + Real.exp (-(a / 4))) := by
          linarith [mul_nonneg hsip.le hexp1.le, mul_nonneg hsip.le hexp0.le]

theorem abs_heatKernel1_le_small {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) (n : ℤ) :
    |heatKernel1 t n| ≤ 2 * Real.exp 2 * Real.exp (-|(n : ℝ)|) := by
  have hnorm : |heatKernel1 t n| = ‖heatKernelC 0 t n‖ := by
    rw [heatKernelC_zero, Complex.norm_real, Real.norm_eq_abs]
  rw [hnorm]
  obtain ⟨τ, hτabs, hnτ, hcosh⟩ := exists_shift_param n (zero_le_one' ℝ)
  have hτ : |τ| ≤ 1 := hτabs.le
  have hmain := norm_heatKernelC_le 0 ht n hτ
  rw [hnτ, hcosh, hτabs] at hmain
  have hcsh := cosh_sub_one_le_sq (x := 1) (by simp)
  have hM := heatMoment_zero_le_one ht
  have hM0 := heatMoment_nonneg 0 (t := t)
  have hE : Real.exp (-(|(n : ℝ)| * 1) + 2 * t * (Real.cosh 1 - 1)) ≤
      Real.exp (-|(n : ℝ)|) * Real.exp 2 := by
    calc Real.exp (-(|(n : ℝ)| * 1) + 2 * t * (Real.cosh 1 - 1))
        ≤ Real.exp (-|(n : ℝ)| + 2) := Real.exp_le_exp.mpr (by nlinarith)
      _ = _ := Real.exp_add _ _
  simp only [pow_zero, one_mul, mul_one] at hmain hE
  calc ‖heatKernelC 0 t n‖
      ≤ Real.exp (-|(n : ℝ)| + 2 * t * (Real.cosh 1 - 1)) * (heatMoment 0 t + heatMoment 0 t) :=
        hmain
    _ ≤ (Real.exp (-|(n : ℝ)|) * Real.exp 2) * (1 + 1) :=
        mul_le_mul hE (by linarith) (by positivity) (by positivity)
    _ = 2 * Real.exp 2 * Real.exp (-|(n : ℝ)|) := by ring

theorem abs_heatDiff_le_small (m : ℕ) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    ∀ n : ℤ, |heatDiff m t n| ≤ 2 * Real.exp 2 * (2 * Real.exp 1) ^ m * Real.exp (-|(n : ℝ)|) := by
  induction m with
  | zero => intro n; simpa [heatDiff] using abs_heatKernel1_le_small ht ht1 n
  | succ m ih =>
    intro n
    have h1 := ih (n + 1)
    have h2 := ih n
    have h3 : Real.exp (-|((n + 1 : ℤ) : ℝ)|) ≤ Real.exp 1 * Real.exp (-|(n : ℝ)|) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      push_cast
      have h4 : |(n : ℝ)| ≤ |(n : ℝ) + 1| + 1 := by
        have := abs_sub ((n : ℝ) + 1) 1
        simpa using this
      linarith
    have hB : 0 ≤ 2 * Real.exp 2 * (2 * Real.exp 1) ^ m := by positivity
    have hE := Real.exp_pos (-|(n : ℝ)|)
    have he1 : Real.exp 1 ≥ 1 := Real.one_le_exp (by norm_num)
    calc |heatDiff (m + 1) t n| = |heatDiff m t (n + 1) - heatDiff m t n| := rfl
      _ ≤ |heatDiff m t (n + 1)| + |heatDiff m t n| := abs_sub _ _
      _ ≤ 2 * Real.exp 2 * (2 * Real.exp 1) ^ m * Real.exp (-|((n + 1 : ℤ) : ℝ)|) +
          2 * Real.exp 2 * (2 * Real.exp 1) ^ m * Real.exp (-|(n : ℝ)|) := add_le_add h1 h2
      _ ≤ 2 * Real.exp 2 * (2 * Real.exp 1) ^ m * (Real.exp 1 * Real.exp (-|(n : ℝ)|)) +
          2 * Real.exp 2 * (2 * Real.exp 1) ^ m * Real.exp (-|(n : ℝ)|) := by gcongr
      _ ≤ 2 * Real.exp 2 * (2 * Real.exp 1) ^ (m + 1) * Real.exp (-|(n : ℝ)|) := by
          rw [pow_succ]
          nlinarith [mul_nonneg hB hE.le, mul_nonneg (mul_nonneg hB hE.le) (sub_nonneg.mpr he1)]

end Balaban.LatticeGreen
