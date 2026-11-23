/-
`lem:block-interpolation` of BALABAN_CORE.tex (`bf6b2bc552ba`), in part: the two steps of its proof which
do not depend on the space `𝔤^c_m`.

* The test of Schur (`schur`, `schur_sqrt`): for a kernel `K(x, x')` of linear maps between normed
  spaces on finite sets with weights (the weights `η⁴` of the lattice), if the sums of `‖K(x, x')‖` over
  `x'` are at most `A` and over `x` at most `B`, then `‖Tf‖₂² ≤ AB‖f‖₂²`.
* The sums of kernels for a scalar kernel (`row_sum_le`): if `‖Tf‖_∞ ≤ b‖f‖_∞`, then
  `Σ_{x'} η⁴ |K(x, x')| ≤ b`; the core's vector-valued step with a basis of `𝔤^c` and the constant
  `m²N⁵` applies this to each pair of coordinates.

Not formalised: the norms `‖·‖` and `|·|` on `𝔤^c_m` and the comparison of a map with its transpose
(`‖K^T‖ ≤ mN‖K‖`), which give the constant `c_I = 2¹²N⁶`.
-/
import Mathlib

open Finset

noncomputable section

namespace CoreLean
namespace Schur

variable {X Y : Type*} [Fintype X] [Fintype Y] {E F : Type*} [NormedAddCommGroup E]
  [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The test of Schur: `Σ_x w(x)‖Σ_{x'} w'(x') K(x, x') f(x')‖² ≤ AB Σ_{x'} w'(x')‖f(x')‖²` if
`Σ_{x'} w'(x')‖K(x, x')‖ ≤ A` for every `x` and `Σ_x w(x)‖K(x, x')‖ ≤ B` for every `x'`. -/
theorem schur (w : X → ℝ) (w' : Y → ℝ) (hw : ∀ x, 0 ≤ w x) (hw' : ∀ y, 0 ≤ w' y)
    (K : X → Y → E →L[ℂ] F) (A B : ℝ) (hA0 : 0 ≤ A)
    (hA : ∀ x, ∑ y, w' y * ‖K x y‖ ≤ A) (hB : ∀ y, ∑ x, w x * ‖K x y‖ ≤ B) (f : Y → E) :
    ∑ x, w x * ‖∑ y, w' y • K x y (f y)‖ ^ 2 ≤ A * B * ∑ y, w' y * ‖f y‖ ^ 2 := by
  -- one row: `‖(Tf)(x)‖² ≤ A Σ_{x'} w'‖K‖‖f‖²`
  have row : ∀ x, ‖∑ y, w' y • K x y (f y)‖ ^ 2 ≤ A * ∑ y, w' y * ‖K x y‖ * ‖f y‖ ^ 2 := fun x => by
    have h1 : ‖∑ y, w' y • K x y (f y)‖ ≤ ∑ y, w' y * ‖K x y‖ * ‖f y‖ := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => ?_)
      rw [norm_smul, Real.norm_of_nonneg (hw' y), mul_assoc]
      exact mul_le_mul_of_nonneg_left ((K x y).le_opNorm _) (hw' y)
    have h2 : (∑ y, w' y * ‖K x y‖ * ‖f y‖) ^ 2 ≤
        (∑ y, w' y * ‖K x y‖) * ∑ y, w' y * ‖K x y‖ * ‖f y‖ ^ 2 :=
      Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun y _ => mul_nonneg (hw' y) (norm_nonneg _))
        (fun y _ => mul_nonneg (mul_nonneg (hw' y) (norm_nonneg _)) (sq_nonneg _))
        (fun y _ => le_of_eq (by ring))
    have h3 : 0 ≤ ∑ y, w' y * ‖K x y‖ * ‖f y‖ ^ 2 :=
      Finset.sum_nonneg fun y _ => mul_nonneg (mul_nonneg (hw' y) (norm_nonneg _)) (sq_nonneg _)
    calc ‖∑ y, w' y • K x y (f y)‖ ^ 2 ≤ (∑ y, w' y * ‖K x y‖ * ‖f y‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ (∑ y, w' y * ‖K x y‖) * ∑ y, w' y * ‖K x y‖ * ‖f y‖ ^ 2 := h2
      _ ≤ A * ∑ y, w' y * ‖K x y‖ * ‖f y‖ ^ 2 := mul_le_mul_of_nonneg_right (hA x) h3
  calc ∑ x, w x * ‖∑ y, w' y • K x y (f y)‖ ^ 2
      ≤ ∑ x, w x * (A * ∑ y, w' y * ‖K x y‖ * ‖f y‖ ^ 2) :=
        Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (row x) (hw x)
    _ = A * ∑ y, w' y * ‖f y‖ ^ 2 * ∑ x, w x * ‖K x y‖ := by
        rw [Finset.mul_sum]
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => by ring
    _ ≤ A * ∑ y, w' y * ‖f y‖ ^ 2 * B := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y _ => ?_) hA0
        exact mul_le_mul_of_nonneg_left (hB y) (mul_nonneg (hw' y) (sq_nonneg _))
    _ = A * B * ∑ y, w' y * ‖f y‖ ^ 2 := by rw [← Finset.sum_mul]; ring

/-- The test of Schur in norms: `‖Tf‖₂ ≤ √(AB) ‖f‖₂`. -/
theorem schur_sqrt (w : X → ℝ) (w' : Y → ℝ) (hw : ∀ x, 0 ≤ w x) (hw' : ∀ y, 0 ≤ w' y)
    (K : X → Y → E →L[ℂ] F) (A B : ℝ) (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hA : ∀ x, ∑ y, w' y * ‖K x y‖ ≤ A) (hB : ∀ y, ∑ x, w x * ‖K x y‖ ≤ B) (f : Y → E) :
    Real.sqrt (∑ x, w x * ‖∑ y, w' y • K x y (f y)‖ ^ 2) ≤
      Real.sqrt (A * B) * Real.sqrt (∑ y, w' y * ‖f y‖ ^ 2) := by
  rw [← Real.sqrt_mul (mul_nonneg hA0 hB0)]
  exact Real.sqrt_le_sqrt (schur w w' hw hw' K A B hA0 hA hB f)

/-- The sums of kernels, for a scalar kernel: if `|Σ_{x'} w'(x') k(x, x') f(x')| ≤ b` for every `f`
with `|f| ≤ 1`, then `Σ_{x'} w'(x') |k(x, x')| ≤ b`. -/
theorem row_sum_le (w' : Y → ℝ) (hw' : ∀ y, 0 ≤ w' y) (k : Y → ℂ) (b : ℝ)
    (hT : ∀ f : Y → ℂ, (∀ y, ‖f y‖ ≤ 1) → ‖∑ y, (w' y : ℂ) * k y * f y‖ ≤ b) :
    ∑ y, w' y * ‖k y‖ ≤ b := by
  classical
  set f : Y → ℂ := fun y => if k y = 0 then 0 else (starRingEnd ℂ) (k y) / (‖k y‖ : ℂ)
  have hf : ∀ y, ‖f y‖ ≤ 1 := fun y => by
    by_cases h : k y = 0
    · simp [f, h]
    · simp only [f, h, ite_false, norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
        abs_norm]
      rw [div_self (norm_ne_zero_iff.mpr h)]
  have hkf : ∀ y, k y * f y = (‖k y‖ : ℂ) := fun y => by
    by_cases h : k y = 0
    · simp [f, h]
    · simp only [f, h, ite_false]
      have hn : (‖k y‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr h
      rw [mul_div_assoc', Complex.mul_conj, Complex.normSq_eq_norm_sq]
      field_simp
      push_cast; ring
  have hsum : ∑ y, (w' y : ℂ) * k y * f y = ((∑ y, w' y * ‖k y‖ : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [mul_assoc, hkf]
  have := hT f hf
  rw [hsum, Complex.norm_real, Real.norm_of_nonneg
    (Finset.sum_nonneg fun y _ => mul_nonneg (hw' y) (norm_nonneg _))] at this
  exact this

end Schur
end CoreLean

end
