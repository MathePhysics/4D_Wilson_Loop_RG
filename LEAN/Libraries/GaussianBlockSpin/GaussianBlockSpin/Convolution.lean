import GaussianBlockSpin.Kernel

/-!
# Composition of Gaussian block-spin kernels

If the averaging map `Q : F →ₗ[ℝ] G` satisfies `Q Q* = s • id` (for Bałaban's block averages
with the Euclidean norms of the kernels, `s = L^{-d}`), then integrating out the intermediate
field composes two block-spin kernels into one:

  `∫ θ, t_α(ψ, Q θ) t_β(θ, R φ) = t_γ(ψ, Q R φ)`,  `γ = α β / (β + s α)`.

This is Bałaban I.(2.12)-(2.13): with `α = a (L^{k+1} ε)^{d-2}`, `β = a_k (L^k ε)^{d-2}`,
`s = L^{-d}` one gets `γ = a_{k+1} (L^{k+1} ε)^{d-2}` with `a_{k+1} = a a_k / (a L^{-2} + a_k)`.
-/

open MeasureTheory Real
open scoped RealInnerProductSpace

namespace GaussianBlockSpin

/-- **Weinstein–Aronszajn identity** for linear maps between finite-dimensional spaces. -/
theorem det_id_add_comp_comm {F G : Type*} [AddCommGroup F] [Module ℝ F] [FiniteDimensional ℝ F]
    [AddCommGroup G] [Module ℝ G] [FiniteDimensional ℝ G] (X : G →ₗ[ℝ] F) (Y : F →ₗ[ℝ] G) :
    LinearMap.det (LinearMap.id + X ∘ₗ Y) = LinearMap.det (LinearMap.id + Y ∘ₗ X) := by
  let bF := Module.finBasis ℝ F
  let bG := Module.finBasis ℝ G
  rw [← LinearMap.det_toMatrix bF, ← LinearMap.det_toMatrix bG, map_add, map_add,
    LinearMap.toMatrix_id, LinearMap.toMatrix_id, LinearMap.toMatrix_comp bF bG bF,
    LinearMap.toMatrix_comp bG bF bG]
  exact Matrix.det_one_add_mul_comm _ _

variable {F G : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]

/-- The stiffness operator `T = β • id + α • Q* Q` of the intermediate field. -/
noncomputable def convStiffness (α β : ℝ) (Q : F →ₗ[ℝ] G) : F →ₗ[ℝ] F :=
  β • LinearMap.id + α • (LinearMap.adjoint Q ∘ₗ Q)

lemma inner_convStiffness (α β : ℝ) (Q : F →ₗ[ℝ] G) (x : F) :
    ⟪x, convStiffness α β Q x⟫ = β * ‖x‖ ^ 2 + α * ‖Q x‖ ^ 2 := by
  simp only [convStiffness, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
    LinearMap.comp_apply, inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq,
    LinearMap.adjoint_inner_right]

lemma isSymmetric_convStiffness (α β : ℝ) (Q : F →ₗ[ℝ] G) :
    (convStiffness α β Q).IsSymmetric := by
  intro x y
  simp only [convStiffness, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
    LinearMap.comp_apply, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_right, conj_trivial]

lemma convStiffness_pos {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 < β) (Q : F →ₗ[ℝ] G) :
    ∀ x : F, x ≠ 0 → 0 < ⟪x, convStiffness α β Q x⟫ := by
  intro x hx
  rw [inner_convStiffness]
  have : 0 < ‖x‖ := norm_pos_iff.mpr hx
  positivity

/-- `det (β • id + α • Q* Q) = β ^ dim F * (1 + s α / β) ^ dim G` when `Q Q* = s • id`. -/
lemma det_convStiffness {α β s : ℝ} (hβ : 0 < β) (Q : F →ₗ[ℝ] G)
    (hQ : Q ∘ₗ LinearMap.adjoint Q = s • LinearMap.id) :
    LinearMap.det (convStiffness α β Q) =
      β ^ Module.finrank ℝ F * (1 + s * α / β) ^ Module.finrank ℝ G := by
  have h1 : convStiffness α β Q =
      β • (LinearMap.id + ((α / β) • LinearMap.adjoint Q) ∘ₗ Q) := by
    ext x
    simp only [convStiffness, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
      LinearMap.comp_apply, smul_add, smul_smul]
    congr 2
    field_simp
  have h2 : Q ∘ₗ ((α / β) • LinearMap.adjoint Q) = (s * α / β) • (LinearMap.id : G →ₗ[ℝ] G) := by
    rw [LinearMap.comp_smul, hQ, smul_smul]
    congr 1
    ring
  have h3 : (LinearMap.id : G →ₗ[ℝ] G) + (s * α / β) • LinearMap.id =
      (1 + s * α / β) • LinearMap.id := by
    rw [add_smul, one_smul]
  rw [h1, LinearMap.det_smul, det_id_add_comp_comm, h2, h3, LinearMap.det_smul, LinearMap.det_id,
    mul_one]

/-- The normalising constants of the composed kernel combine into that of `t_γ`. -/
lemma convolution_prefactor {α β s : ℝ} (hα : 0 < α) (hβ : 0 < β) (hs : 0 ≤ s) (nF nG : ℕ) :
    (α / (2 * π)) ^ ((nG : ℝ) / 2) * (β / (2 * π)) ^ ((nF : ℝ) / 2) *
        ((2 * π) ^ ((nF : ℝ) / 2) / Real.sqrt (β ^ nF * (1 + s * α / β) ^ nG)) =
      (α * β / (β + s * α) / (2 * π)) ^ ((nG : ℝ) / 2) := by
  have hπ : 0 < 2 * π := by positivity
  have hk : 0 < 1 + s * α / β := by positivity
  have hγ : α * β / (β + s * α) = α / (1 + s * α / β) := by
    field_simp
  have hr : ∀ (x : ℝ) (n : ℕ), 0 ≤ x → Real.sqrt (x ^ n) = x ^ ((n : ℝ) / 2) := by
    intro x n hx
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx]
    ring_nf
  rw [Real.sqrt_mul (pow_nonneg hβ.le _), hr β nF hβ.le, hr _ nG hk.le, hγ,
    Real.div_rpow hα.le hπ.le, Real.div_rpow hβ.le hπ.le,
    Real.div_rpow (div_pos hα hk).le hπ.le, Real.div_rpow hα.le hk.le]
  have h1 : 0 < α ^ ((nG : ℝ) / 2) := by positivity
  have h2 : 0 < β ^ ((nF : ℝ) / 2) := by positivity
  have h3 : 0 < (1 + s * α / β) ^ ((nG : ℝ) / 2) := by positivity
  have h4 : 0 < (2 * π) ^ ((nF : ℝ) / 2) := by positivity
  have h5 : 0 < (2 * π) ^ ((nG : ℝ) / 2) := by positivity
  field_simp

variable [MeasurableSpace F] [BorelSpace F]

/-- The composed stiffness `γ = α β / (β + s α)` is positive. -/
lemma convCoeff_pos {α β s : ℝ} (hα : 0 < α) (hβ : 0 < β) (hs : 0 ≤ s) :
    0 < α * β / (β + s * α) := by
  positivity

/-- **Composition of block-spin kernels**, Bałaban I.(2.12)-(2.13): if `Q Q* = s • id`, then
`∫ θ, t_α(ψ, Q θ) t_β(θ, R φ) = t_γ(ψ, Q R φ)` with `γ = α β / (β + s α)`. -/
theorem integral_blockKernel_mul_blockKernel {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {α β s : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hs : 0 ≤ s) (Q : F →ₗ[ℝ] G) (R : E →ₗ[ℝ] F)
    (hQ : Q ∘ₗ LinearMap.adjoint Q = s • LinearMap.id) (ψ : G) (φ : E) :
    ∫ θ : F, blockKernel α hα Q ψ θ * blockKernel β hβ R θ φ =
      blockKernel (α * β / (β + s * α)) (convCoeff_pos hα hβ hs) (Q ∘ₗ R) ψ φ := by
  have hpos : 0 < β + s * α := by positivity
  set u := ψ - Q (R φ) with hu
  set w := (α / (β + s * α)) • LinearMap.adjoint Q u with hw
  have hQQ : Q (LinearMap.adjoint Q u) = s • u := by
    simpa using congrArg (fun f => f u) hQ
  have hTw : convStiffness α β Q w = α • LinearMap.adjoint Q u := by
    simp only [hw, convStiffness, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
      LinearMap.comp_apply, map_smul, hQQ]
    match_scalars
    field_simp
  have hwTw : ⟪w, convStiffness α β Q w⟫ = α ^ 2 * s / (β + s * α) * ‖u‖ ^ 2 := by
    rw [hTw, hw, real_inner_smul_left, real_inner_smul_right, LinearMap.adjoint_inner_left, hQQ,
      real_inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
  have hint : ∀ θ : F, blockKernel α hα Q ψ (θ + R φ) * blockKernel β hβ R (θ + R φ) φ =
      (α / (2 * π)) ^ ((Module.finrank ℝ G : ℝ) / 2) *
        (β / (2 * π)) ^ ((Module.finrank ℝ F : ℝ) / 2) * Real.exp (-(α / 2) * ‖u‖ ^ 2) *
        Real.exp (-(1 / 2) * ⟪θ, convStiffness α β Q θ⟫ + ⟪convStiffness α β Q w, θ⟫) := by
    intro θ
    unfold blockKernel
    have e1 : ψ - Q (θ + R φ) = u - Q θ := by
      rw [hu, map_add]
      abel
    have e2 : θ + R φ - R φ = θ := by abel
    rw [e1, e2, hTw, real_inner_smul_left, LinearMap.adjoint_inner_left, inner_convStiffness,
      norm_sub_sq_real]
    have hexp : -(α / 2) * (‖u‖ ^ 2 - 2 * ⟪u, Q θ⟫ + ‖Q θ‖ ^ 2) + -(β / 2) * ‖θ‖ ^ 2 =
        -(α / 2) * ‖u‖ ^ 2 + (-(1 / 2) * (β * ‖θ‖ ^ 2 + α * ‖Q θ‖ ^ 2) + α * ⟪u, Q θ⟫) := by
      ring
    rw [show ∀ x y z v : ℝ, x * Real.exp y * (z * Real.exp v) = x * z * Real.exp (y + v) from
      fun x y z v => by rw [Real.exp_add]; ring, hexp, Real.exp_add]
    ring
  rw [← integral_add_right_eq_self (fun θ => blockKernel α hα Q ψ θ * blockKernel β hβ R θ φ) (R φ)]
  simp only [hint]
  rw [integral_const_mul, integral_exp_neg_half_inner_add (isSymmetric_convStiffness α β Q)
    (convStiffness_pos hα.le hβ Q) w, det_convStiffness hβ Q hQ, hwTw]
  unfold blockKernel
  rw [LinearMap.comp_apply, ← hu, ← convolution_prefactor hα hβ hs (Module.finrank ℝ F)
    (Module.finrank ℝ G)]
  have hexp2 : -(α / 2) * ‖u‖ ^ 2 + 1 / 2 * (α ^ 2 * s / (β + s * α) * ‖u‖ ^ 2) =
      -(α * β / (β + s * α) / 2) * ‖u‖ ^ 2 := by
    field_simp
    ring
  rw [← hexp2, Real.exp_add]
  ring

end GaussianBlockSpin
