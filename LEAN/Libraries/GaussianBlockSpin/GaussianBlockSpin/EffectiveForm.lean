import GaussianBlockSpin.Kernel

/-!
# The effective quadratic form after a block-spin transformation

Bałaban I.(2.19)-(2.21): integrating the Gaussian weight `exp (-(1/2) ⟪φ, H φ⟫)` against the
block-spin kernel `t_α(ψ, Q φ)` gives `Z * exp (-(1/2) ⟪ψ, Δ ψ⟫)` with the Schur complement

  `⟪ψ, Δ ψ⟫ = α ‖ψ‖² - α² ⟪ψ, Q G Q* ψ⟫`,  `G = (H + α Q* Q)⁻¹`,

and `Z = (α / 2π) ^ (dim F / 2) * (2π) ^ (dim E / 2) / √(det (H + α Q* Q))`.

The vector `G Q* ψ` is represented by any `w` with `(H + α Q* Q) w = Q* ψ`; such a `w` exists and
is unique (`exists_apply_eq_of_pos`, and `H + α Q* Q` is injective).

Convention (as in `Kernel` and `Convolution`): `E`, `F` carry the plain Euclidean norms
`Σ_x |φ(x)|²`, so the volumes are the coordinate Lebesgue measures of the source. Then
Bałaban's I.(2.19)-(2.21) is the case `α = a_k (L^k ε)^{d-2}`, `Q = Q_k(A)` (plain adjoint
`Qᵀ`), `H = ε^d (-Δ^{ε,N}_{A,Ω} + m²)` as a plain matrix. Since the adjoint for the lattice
products I.(1.5) is `Q_k^* = L^{kd} Qᵀ`, one gets `G = ε^{-d} G_k^ε(Ω, A)` with `G_k^ε` of
I.(2.20); the exponent `α ‖ψ‖² - α² ⟪ψ, Q G Qᵀ ψ⟫` equals Bałaban's `⟨ψ, Δ^{(k)} ψ⟩`
(lattice product), and `Z` is his `Z_k^ε` with respect to the coordinate measures.
-/

open MeasureTheory Real
open scoped RealInnerProductSpace

namespace GaussianBlockSpin

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- The operator `H + α Q* Q` whose inverse is the propagator. -/
noncomputable def effStiffness (α : ℝ) (H : E →ₗ[ℝ] E) (Q : E →ₗ[ℝ] F) : E →ₗ[ℝ] E :=
  H + α • (LinearMap.adjoint Q ∘ₗ Q)

lemma inner_effStiffness (α : ℝ) (H : E →ₗ[ℝ] E) (Q : E →ₗ[ℝ] F) (x : E) :
    ⟪x, effStiffness α H Q x⟫ = ⟪x, H x⟫ + α * ‖Q x‖ ^ 2 := by
  simp only [effStiffness, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    inner_add_right, inner_smul_right, LinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq]

lemma isSymmetric_effStiffness (α : ℝ) {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric) (Q : E →ₗ[ℝ] F) :
    (effStiffness α H Q).IsSymmetric := by
  intro x y
  simp only [effStiffness, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_right, hH x y]

lemma effStiffness_pos {α : ℝ} (hα : 0 ≤ α) {H : E →ₗ[ℝ] E}
    (hHpos : ∀ x, x ≠ 0 → 0 < ⟪x, H x⟫) (Q : E →ₗ[ℝ] F) :
    ∀ x, x ≠ 0 → 0 < ⟪x, effStiffness α H Q x⟫ := by
  intro x hx
  rw [inner_effStiffness]
  have := hHpos x hx
  positivity

/-- **The translated completed square** (Bałaban I.(3.10)-(3.11), (3.18)-(3.19), (3.41), (3.48)): with
`K = H + α Q* Q` and `K w = Q* ψ`, the translation `φ = φ' + α w` gives
`α ‖ψ - Q φ‖² + ⟪φ, H φ⟫ = (α ‖ψ‖² - α² ⟪ψ, Q w⟫) + ⟪φ', K φ'⟫`. -/
theorem complete_square_translate {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric) (α : ℝ) (Q : E →ₗ[ℝ] F) (ψ : F) (w : E)
    (hw : effStiffness α H Q w = LinearMap.adjoint Q ψ) (φ : E) :
    α * ‖ψ - Q φ‖ ^ 2 + ⟪φ, H φ⟫ =
      α * ‖ψ‖ ^ 2 - α ^ 2 * ⟪ψ, Q w⟫ + ⟪φ - α • w, effStiffness α H Q (φ - α • w)⟫ := by
  have h1 : ⟪φ, H w⟫ + α * ⟪Q φ, Q w⟫ = ⟪ψ, Q φ⟫ := by
    have h := congrArg (fun v => ⟪φ, v⟫) hw
    simp only [effStiffness, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply, inner_add_right,
      inner_smul_right, LinearMap.adjoint_inner_right] at h
    rwa [real_inner_comm ψ (Q φ)] at h
  have h2 : ⟪w, H w⟫ + α * ‖Q w‖ ^ 2 = ⟪ψ, Q w⟫ := by
    have h := congrArg (fun v => ⟪w, v⟫) hw
    simp only [effStiffness, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply, inner_add_right,
      inner_smul_right, LinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq] at h
    rwa [real_inner_comm ψ (Q w)] at h
  have hs : ⟪w, H φ⟫ = ⟪φ, H w⟫ := by rw [← hH w φ, real_inner_comm]
  have e1 : ‖ψ - Q φ‖ ^ 2 = ‖ψ‖ ^ 2 - 2 * ⟪ψ, Q φ⟫ + ‖Q φ‖ ^ 2 := norm_sub_sq_real ψ (Q φ)
  have e3 : ⟪φ - α • w, H (φ - α • w)⟫ = ⟪φ, H φ⟫ - 2 * α * ⟪φ, H w⟫ + α ^ 2 * ⟪w, H w⟫ := by
    simp only [map_sub, map_smul, inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right, hs]
    ring
  have e4 : ‖Q (φ - α • w)‖ ^ 2 = ‖Q φ‖ ^ 2 - 2 * α * ⟪Q φ, Q w⟫ + α ^ 2 * ‖Q w‖ ^ 2 := by
    rw [map_sub, map_smul, norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  rw [inner_effStiffness, e1, e3, e4]
  linear_combination (2 * α) * h1 - α ^ 2 * h2

variable [MeasurableSpace E] [BorelSpace E]

/-- **Effective quadratic form**, Bałaban I.(2.19)-(2.21). -/
theorem integral_blockKernel_mul_gaussian {α : ℝ} (hα : 0 < α) {H : E →ₗ[ℝ] E}
    (hH : H.IsSymmetric) (hHpos : ∀ x, x ≠ 0 → 0 < ⟪x, H x⟫) (Q : E →ₗ[ℝ] F) (ψ : F) (w : E)
    (hw : effStiffness α H Q w = LinearMap.adjoint Q ψ) :
    ∫ φ : E, blockKernel α hα Q ψ φ * Real.exp (-(1 / 2) * ⟪φ, H φ⟫) =
      (α / (2 * π)) ^ ((Module.finrank ℝ F : ℝ) / 2) *
        ((2 * π) ^ ((Module.finrank ℝ E : ℝ) / 2) /
          Real.sqrt (LinearMap.det (effStiffness α H Q))) *
        Real.exp (-(1 / 2) * (α * ‖ψ‖ ^ 2 - α ^ 2 * ⟪ψ, Q w⟫)) := by
  have hKw : effStiffness α H Q (α • w) = α • LinearMap.adjoint Q ψ := by
    rw [map_smul, hw]
  have hint : ∀ φ : E, blockKernel α hα Q ψ φ * Real.exp (-(1 / 2) * ⟪φ, H φ⟫) =
      (α / (2 * π)) ^ ((Module.finrank ℝ F : ℝ) / 2) * Real.exp (-(α / 2) * ‖ψ‖ ^ 2) *
        Real.exp (-(1 / 2) * ⟪φ, effStiffness α H Q φ⟫ + ⟪effStiffness α H Q (α • w), φ⟫) := by
    intro φ
    unfold blockKernel
    rw [hKw, real_inner_smul_left, LinearMap.adjoint_inner_left, inner_effStiffness,
      norm_sub_sq_real]
    have hexp : -(α / 2) * (‖ψ‖ ^ 2 - 2 * ⟪ψ, Q φ⟫ + ‖Q φ‖ ^ 2) + -(1 / 2) * ⟪φ, H φ⟫ =
        -(α / 2) * ‖ψ‖ ^ 2 + (-(1 / 2) * (⟪φ, H φ⟫ + α * ‖Q φ‖ ^ 2) + α * ⟪ψ, Q φ⟫) := by
      ring
    rw [mul_assoc, ← Real.exp_add, hexp, Real.exp_add]
    ring
  simp only [hint]
  rw [integral_const_mul, integral_exp_neg_half_inner_add (isSymmetric_effStiffness α hH Q)
    (effStiffness_pos hα.le hHpos Q) (α • w), hKw, real_inner_smul_left, real_inner_smul_right,
    LinearMap.adjoint_inner_right, real_inner_comm]
  have hexp2 : -(α / 2) * ‖ψ‖ ^ 2 + 1 / 2 * (α * (α * ⟪ψ, Q w⟫)) =
      -(1 / 2) * (α * ‖ψ‖ ^ 2 - α ^ 2 * ⟪ψ, Q w⟫) := by
    ring
  rw [← hexp2, Real.exp_add]
  ring

end GaussianBlockSpin
