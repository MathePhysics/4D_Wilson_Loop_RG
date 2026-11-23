import BakerCampbellHausdorff.ExpBounds
import Mathlib.Analysis.Normed.Operator.Mul

/-!
# Multiplication operators and `ad` on a Banach algebra

For a Banach algebra `𝔸` over `𝕂 = ℝ` or `ℂ`, the left and right multiplication operators
`mulLeft 𝕂 a = (x ↦ a x)` and `mulRight 𝕂 a = (x ↦ x a)` and `ad 𝕂 a = mulLeft 𝕂 a - mulRight 𝕂 a`
live in the Banach algebra `𝔸 →L[𝕂] 𝔸`.  Left and right multiplications commute, so
`exp (ad 𝕂 a) = mulLeft 𝕂 (exp a) * mulRight 𝕂 (exp (-a))`, i.e. `exp (ad a) x = e^a x e^(-a)`.

The series `expSubOneDiv 𝕂 T = ∑ₖ Tᵏ / (k + 1)!`, the function `(e^T - 1) / T` of `T`, is the
factor in the derivative of `exp` (`BakerCampbellHausdorff.Dexp`).

## Main definitions and results

* `mulLeft`, `mulRight`, `ad`, with norms `≤ ‖a‖`, `≤ ‖a‖`, `≤ 2 ‖a‖`.
* `exp_mulLeft`, `exp_mulRight`, `exp_ad`, `exp_ad_apply`.
* `expSubOneDiv`, `hasSum_expSubOneDiv`, `norm_expSubOneDiv_sub_one_le`:
  `‖expSubOneDiv 𝕂 T - 1‖ ≤ e^‖T‖ - 1`.
-/

noncomputable section

open NormedSpace
open scoped Nat

namespace BakerCampbellHausdorff

section Operators

variable (𝕂 : Type*) {𝔸 : Type*} [RCLike 𝕂] [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸]

/-- Left multiplication `x ↦ a x` as an element of the Banach algebra `𝔸 →L[𝕂] 𝔸`. -/
def mulLeft (a : 𝔸) : 𝔸 →L[𝕂] 𝔸 := ContinuousLinearMap.mul 𝕂 𝔸 a

/-- Right multiplication `x ↦ x a` as an element of the Banach algebra `𝔸 →L[𝕂] 𝔸`. -/
def mulRight (a : 𝔸) : 𝔸 →L[𝕂] 𝔸 := (ContinuousLinearMap.mul 𝕂 𝔸).flip a

/-- The adjoint action `ad a = [a, ·] : x ↦ a x - x a`. -/
def ad (a : 𝔸) : 𝔸 →L[𝕂] 𝔸 := mulLeft 𝕂 a - mulRight 𝕂 a

variable {𝕂}

@[simp]
theorem mulLeft_apply (a x : 𝔸) : mulLeft 𝕂 a x = a * x := rfl

@[simp]
theorem mulRight_apply (a x : 𝔸) : mulRight 𝕂 a x = x * a := rfl

@[simp]
theorem ad_apply (a x : 𝔸) : ad 𝕂 a x = a * x - x * a := rfl

variable (𝕂) in
theorem mulLeft_one : mulLeft 𝕂 (1 : 𝔸) = 1 := by
  ext x
  simp

variable (𝕂) in
theorem mulRight_one : mulRight 𝕂 (1 : 𝔸) = 1 := by
  ext x
  simp

theorem mulLeft_mul (a b : 𝔸) : mulLeft 𝕂 (a * b) = mulLeft 𝕂 a * mulLeft 𝕂 b := by
  ext x
  simp [mul_assoc]

theorem mulRight_mul (a b : 𝔸) : mulRight 𝕂 (a * b) = mulRight 𝕂 b * mulRight 𝕂 a := by
  ext x
  simp [mul_assoc]

theorem mulLeft_pow (a : 𝔸) (n : ℕ) : mulLeft 𝕂 (a ^ n) = mulLeft 𝕂 a ^ n := by
  induction n with
  | zero => simp [mulLeft_one]
  | succ n ih => rw [pow_succ, mulLeft_mul, ih, pow_succ]

theorem mulRight_pow (a : 𝔸) (n : ℕ) : mulRight 𝕂 (a ^ n) = mulRight 𝕂 a ^ n := by
  induction n with
  | zero => simp [mulRight_one]
  | succ n ih => rw [pow_succ', mulRight_mul, ih, pow_succ]

theorem mulLeft_smul (c : 𝕂) (a : 𝔸) : mulLeft 𝕂 (c • a) = c • mulLeft 𝕂 a :=
  map_smul _ _ _

theorem mulRight_smul (c : 𝕂) (a : 𝔸) : mulRight 𝕂 (c • a) = c • mulRight 𝕂 a :=
  map_smul _ _ _

theorem mulRight_neg (a : 𝔸) : mulRight 𝕂 (-a) = -mulRight 𝕂 a :=
  map_neg _ _

theorem ad_smul (c : 𝕂) (a : 𝔸) : ad 𝕂 (c • a) = c • ad 𝕂 a := by
  rw [ad, ad, mulLeft_smul, mulRight_smul, smul_sub]

theorem ad_neg (a : 𝔸) : ad 𝕂 (-a) = -ad 𝕂 a := by
  ext x
  show -a * x - x * -a = -(a * x - x * a)
  noncomm_ring

/-- Left and right multiplications commute. -/
theorem commute_mulLeft_mulRight (a b : 𝔸) : Commute (mulLeft 𝕂 a) (mulRight 𝕂 b) := by
  ext x
  simp [mul_assoc]

theorem norm_mulLeft_le (a : 𝔸) : ‖mulLeft 𝕂 a‖ ≤ ‖a‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg a) fun x => norm_mul_le a x

theorem norm_mulRight_le (a : 𝔸) : ‖mulRight 𝕂 a‖ ≤ ‖a‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg a) fun x => by
    rw [mulRight_apply, mul_comm ‖a‖]
    exact norm_mul_le x a

/-- `‖ad a‖ ≤ 2 ‖a‖`. -/
theorem norm_ad_le (a : 𝔸) : ‖ad 𝕂 a‖ ≤ 2 * ‖a‖ := by
  have h1 : ‖mulLeft 𝕂 a‖ ≤ ‖a‖ := norm_mulLeft_le a
  have h2 : ‖mulRight 𝕂 a‖ ≤ ‖a‖ := norm_mulRight_le a
  exact (norm_sub_le _ _).trans (by linarith)

variable [CompleteSpace 𝔸]

/-- `exp (mulLeft a) = mulLeft (exp a)`. -/
theorem exp_mulLeft (a : 𝔸) : exp (mulLeft 𝕂 a) = mulLeft 𝕂 (exp a) := by
  have h1 : HasSum (fun n => mulLeft 𝕂 ((n !⁻¹ : 𝕂) • a ^ n)) (mulLeft 𝕂 (exp a)) :=
    (exp_series_hasSum_exp' (𝕂 := 𝕂) a).mapL (ContinuousLinearMap.mul 𝕂 𝔸)
  simp only [mulLeft_smul, mulLeft_pow] at h1
  exact (exp_series_hasSum_exp' (𝕂 := 𝕂) (mulLeft 𝕂 a)).unique h1

/-- `exp (mulRight a) = mulRight (exp a)`. -/
theorem exp_mulRight (a : 𝔸) : exp (mulRight 𝕂 a) = mulRight 𝕂 (exp a) := by
  have h1 : HasSum (fun n => mulRight 𝕂 ((n !⁻¹ : 𝕂) • a ^ n)) (mulRight 𝕂 (exp a)) :=
    (exp_series_hasSum_exp' (𝕂 := 𝕂) a).mapL (ContinuousLinearMap.mul 𝕂 𝔸).flip
  simp only [mulRight_smul, mulRight_pow] at h1
  exact (exp_series_hasSum_exp' (𝕂 := 𝕂) (mulRight 𝕂 a)).unique h1

/-- **`exp ∘ ad = Ad ∘ exp`**: `exp (ad a) = mulLeft (exp a) * mulRight (exp (-a))`. -/
theorem exp_ad (a : 𝔸) : exp (ad 𝕂 a) = mulLeft 𝕂 (exp a) * mulRight 𝕂 (exp (-a)) := by
  have h : ad 𝕂 a = mulLeft 𝕂 a + mulRight 𝕂 (-a) := by
    rw [ad, mulRight_neg, sub_eq_add_neg]
  rw [h, exp_add_of_commute' 𝕂 (commute_mulLeft_mulRight a (-a)), exp_mulLeft, exp_mulRight]

/-- `exp (ad a) x = e^a x e^(-a)`. -/
theorem exp_ad_apply (a x : 𝔸) : exp (ad 𝕂 a) x = exp a * x * exp (-a) := by
  rw [exp_ad]
  show exp a * (x * exp (-a)) = exp a * x * exp (-a)
  rw [mul_assoc]

end Operators

section ExpSubOneDiv

variable (𝕂 : Type*) {𝔹 : Type*} [RCLike 𝕂] [NormedRing 𝔹] [NormedAlgebra 𝕂 𝔹]

/-- `expSubOneDiv 𝕂 T = ∑ₖ Tᵏ / (k + 1)!`, the entire function `(e^T - 1) / T` of `T`. -/
def expSubOneDiv (T : 𝔹) : 𝔹 :=
  ∑' k, ((k + 1)! : 𝕂)⁻¹ • T ^ k  -- totalisation-audit: allow summable for every T

variable {𝕂}

theorem norm_expSubOneDiv_term_le (T : 𝔹) {k : ℕ} (hk : 0 < k) :
    ‖((k + 1)! : 𝕂)⁻¹ • T ^ k‖ ≤ (k !⁻¹ : ℝ) • ‖T‖ ^ k := by
  rw [norm_smul, norm_inv, RCLike.norm_natCast, smul_eq_mul]
  refine mul_le_mul ?_ (norm_pow_le' T hk) (by positivity) (by positivity)
  exact inv_anti₀ (by positivity) (by exact_mod_cast Nat.factorial_le (Nat.le_succ k))

theorem summable_norm_expSubOneDiv (T : 𝔹) :
    Summable fun k => ‖((k + 1)! : 𝕂)⁻¹ • T ^ k‖ := by
  refine (summable_nat_add_iff 1).mp ?_
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun k => norm_expSubOneDiv_term_le T k.succ_pos) ?_
  exact (summable_nat_add_iff 1).mpr (hasSum_real_exp ‖T‖).summable

variable [CompleteSpace 𝔹]

theorem hasSum_expSubOneDiv (T : 𝔹) :
    HasSum (fun k => ((k + 1)! : 𝕂)⁻¹ • T ^ k) (expSubOneDiv 𝕂 T) :=
  (summable_norm_expSubOneDiv T).of_norm.hasSum

/-- `‖expSubOneDiv 𝕂 T - 1‖ ≤ e^‖T‖ - 1`. -/
theorem norm_expSubOneDiv_sub_one_le (T : 𝔹) :
    ‖expSubOneDiv 𝕂 T - 1‖ ≤ Real.exp ‖T‖ - 1 := by
  have h1 := (hasSum_nat_add_iff' 1).mpr (hasSum_expSubOneDiv (𝕂 := 𝕂) T)
  have h2 := (hasSum_nat_add_iff' 1).mpr (hasSum_real_exp ‖T‖)
  have e1 : ∑ i ∈ Finset.range 1, (((i + 1)! : 𝕂)⁻¹ • T ^ i) = 1 := by simp
  have e2 : ∑ i ∈ Finset.range 1, (i !⁻¹ : ℝ) • ‖T‖ ^ i = 1 := by simp
  rw [e1] at h1
  rw [e2] at h2
  exact h1.norm_le_of_bounded h2 fun n => norm_expSubOneDiv_term_le T n.succ_pos

end ExpSubOneDiv

end BakerCampbellHausdorff
