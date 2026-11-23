import GaussianBlockSpin.GaussianIntegral

/-!
# The Gaussian block-spin kernel

For finite-dimensional real inner product spaces `E` (fine fields) and `F` (block fields), a
linear averaging map `Q : E →ₗ[ℝ] F` and a stiffness `a > 0`, the block-spin kernel is

  `t_a(ψ, φ) = (a / 2π) ^ (dim F / 2) * exp (-(a / 2) ‖ψ - Q φ‖²)`.

This is Bałaban's kernel I.(2.6), resp. I.(2.10), with the product over the blocks `y` taken
together: if `F` carries the Euclidean norm `‖ψ‖² = ∑_y |ψ(y)|²` and `a` is Bałaban's
`a (L^{k+1} ε)^{d-2}`, the product of the per-block kernels is `t_a`.

Main result: the kernel is a probability density in `ψ`, I.(2.8).
-/

open MeasureTheory Real
open scoped RealInnerProductSpace

namespace GaussianBlockSpin

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- The Gaussian block-spin kernel `(a / 2π) ^ (dim F / 2) * exp (-(a / 2) ‖ψ - Q φ‖²)`.
It is the source's kernel only for `a > 0` (for `a ≤ 0` it is not a probability density, and Mathlib's
real power of a negative base is a junk value), so `0 < a` is a gate argument, as in the source. -/
noncomputable def blockKernel (a : ℝ) (_ha : 0 < a) (Q : E →ₗ[ℝ] F) (ψ : F) (φ : E) : ℝ :=
  (a / (2 * π)) ^ ((Module.finrank ℝ F : ℝ) / 2) * Real.exp (-(a / 2) * ‖ψ - Q φ‖ ^ 2) -- totalisation-audit: allow 2π ≠ 0, a > 0 by the gate

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
lemma blockKernel_pos {a : ℝ} (ha : 0 < a) (Q : E →ₗ[ℝ] F) (ψ : F) (φ : E) :
    0 < blockKernel a ha Q ψ φ := by
  unfold blockKernel
  have : 0 < a / (2 * π) := by positivity
  positivity

omit [FiniteDimensional ℝ F] in
/-- The scalar map `a • id` is symmetric. -/
lemma isSymmetric_smul_id (a : ℝ) : (a • LinearMap.id : F →ₗ[ℝ] F).IsSymmetric := by
  intro x y
  simp [inner_smul_left, inner_smul_right]

omit [FiniteDimensional ℝ F] in
lemma inner_smul_id_pos {a : ℝ} (ha : 0 < a) :
    ∀ x : F, x ≠ 0 → 0 < ⟪x, (a • LinearMap.id : F →ₗ[ℝ] F) x⟫ := by
  intro x hx
  rw [LinearMap.smul_apply, LinearMap.id_apply, inner_smul_right, real_inner_self_eq_norm_sq]
  have : 0 < ‖x‖ := norm_pos_iff.mpr hx
  positivity

variable [MeasurableSpace F] [BorelSpace F]

/-- The isotropic Gaussian integral `∫ exp (-(a / 2) ‖x‖²) = (2π / a) ^ (dim F / 2)`. -/
lemma integral_exp_neg_half_mul_norm_sq {a : ℝ} (ha : 0 < a) :
    ∫ x : F, Real.exp (-(a / 2) * ‖x‖ ^ 2) =
      (2 * π) ^ ((Module.finrank ℝ F : ℝ) / 2) / (a ^ ((Module.finrank ℝ F : ℝ) / 2)) := by
  have h := integral_exp_neg_half_inner (isSymmetric_smul_id (F := F) a) (inner_smul_id_pos ha)
  have hform : ∀ x : F, -(1 / 2) * ⟪x, (a • LinearMap.id : F →ₗ[ℝ] F) x⟫ =
      -(a / 2) * ‖x‖ ^ 2 := by
    intro x
    rw [LinearMap.smul_apply, LinearMap.id_apply, inner_smul_right, real_inner_self_eq_norm_sq]
    ring
  simp_rw [hform] at h
  rw [h, LinearMap.det_smul, LinearMap.det_id, mul_one, Real.sqrt_eq_rpow,
    ← Real.rpow_natCast, ← Real.rpow_mul ha.le]
  congr 2
  ring

omit [FiniteDimensional ℝ E] in
/-- **Normalisation**, Bałaban I.(2.8): the block-spin kernel is a probability density in `ψ`. -/
theorem integral_blockKernel {a : ℝ} (ha : 0 < a) (Q : E →ₗ[ℝ] F) (φ : E) :
    ∫ ψ : F, blockKernel a ha Q ψ φ = 1 := by
  unfold blockKernel
  rw [integral_const_mul,
    ← integral_add_right_eq_self (fun ψ : F => Real.exp (-(a / 2) * ‖ψ - Q φ‖ ^ 2)) (Q φ)]
  simp only [add_sub_cancel_right]
  rw [integral_exp_neg_half_mul_norm_sq ha, Real.div_rpow ha.le (by positivity)]
  have h1 : 0 < a ^ ((Module.finrank ℝ F : ℝ) / 2) := by positivity
  have h2 : 0 < (2 * π) ^ ((Module.finrank ℝ F : ℝ) / 2) := by positivity
  field_simp

end GaussianBlockSpin
