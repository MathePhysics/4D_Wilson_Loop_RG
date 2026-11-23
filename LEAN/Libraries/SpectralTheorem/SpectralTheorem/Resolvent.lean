import KatoRellich.Resolvent
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The resolvents `(A ± i)⁻¹` of a self-adjoint operator

For a self-adjoint `A` on a complex Hilbert space, `A + i` and `A - i` are bijections from `D(A)`
onto `H` with `‖(A ± i) x‖ ≥ ‖x‖`, so their inverses are bounded operators of norm at most `1`.
Reed–Simon I, proof of Theorem VIII.4, p. 261: `(A + i)⁻¹` and `(A - i)⁻¹` commute, and
`((A + i)⁻¹)* = (A - i)⁻¹`, so `(A + i)⁻¹` is a bounded normal operator; its kernel is trivial and
its range is `D(A)`.  This is the bridge from the spectral theorem for bounded normal operators
to unbounded self-adjoint ones.

We write `A + i s` for `s = ±1`, i.e. `KatoRellich.addScalar A ((s : ℂ) * RCLike.I)`, so that the
estimates and the surjectivity statement of `KatoRellich.Resolvent` apply directly.

## Main definitions and results

* `SpectralTheorem.resolventI hA s hs`: the bounded operator `(A + i s)⁻¹`, for `|s| = 1`.
* `SpectralTheorem.resolventI_mem_domain`, `SpectralTheorem.addScalar_resolventI`,
  `SpectralTheorem.resolventI_addScalar`: it is the inverse of `A + i s : D(A) → H`.
* `SpectralTheorem.adjoint_resolventI`: `((A + i s)⁻¹)† = (A - i s)⁻¹`.
* `SpectralTheorem.resolventI_commute`: `(A + i s)⁻¹` and `(A - i s)⁻¹` commute.
* `SpectralTheorem.isStarNormal_resolventI`: `(A + i s)⁻¹` is normal.
-/

noncomputable section

open scoped InnerProductSpace ComplexConjugate
open KatoRellich

namespace SpectralTheorem

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem rclikeI_ne_zero : (RCLike.I : ℂ) ≠ 0 := by
  simp

theorem ne_zero_of_abs_eq_one {s : ℝ} (hs : |s| = 1) : s ≠ 0 := by
  rintro rfl
  simp at hs

theorem abs_neg_eq_one {s : ℝ} (hs : |s| = 1) : |-s| = 1 := by
  rwa [abs_neg]

theorem conj_shift (s : ℝ) : conj (((-s : ℝ) : ℂ) * RCLike.I) = (s : ℂ) * RCLike.I := by
  rw [map_mul, Complex.conj_ofReal, RCLike.conj_I, Complex.ofReal_neg, neg_mul_neg]

variable {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
include hA

/-- `‖x‖ ≤ ‖(A + i s) x‖` for `x ∈ D(A)` and `|s| = 1`. -/
theorem norm_le_norm_shift {s : ℝ} (hs : |s| = 1) (x : A.domain) :
    ‖(x : H)‖ ≤ ‖A x + ((s : ℂ) * RCLike.I) • (x : H)‖ := by
  have h := (norm_le_norm_addScalar_I (IsSymmetric.of_isSelfAdjoint hA) rclikeI_ne_zero s x).1
  rwa [hs, one_mul] at h

/-- `A + i s`, `|s| = 1`, as a linear bijection `D(A) → H`. -/
def shiftEquiv (s : ℝ) (hs : |s| = 1) : A.domain ≃ₗ[ℂ] H :=
  LinearEquiv.ofBijective (addScalar A ((s : ℂ) * RCLike.I)).toFun
    ⟨(injective_iff_map_eq_zero _).mpr fun x hx => by
        have h := norm_le_norm_shift hA hs x
        change ‖(x : H)‖ ≤ ‖(addScalar A ((s : ℂ) * RCLike.I)).toFun x‖ at h
        rw [hx, norm_zero] at h
        exact Subtype.ext (norm_le_zero_iff.mp h),
      LinearMap.range_eq_top.mp
        (range_addScalar_I_eq_top hA rclikeI_ne_zero (ne_zero_of_abs_eq_one hs))⟩

theorem shiftEquiv_apply {s : ℝ} (hs : |s| = 1) (x : A.domain) :
    shiftEquiv hA s hs x = A x + ((s : ℂ) * RCLike.I) • (x : H) :=
  rfl

/-- **The resolvent** `(A + i s)⁻¹`, `|s| = 1`: a bounded operator of norm at most `1`. -/
def resolventI (s : ℝ) (hs : |s| = 1) : H →L[ℂ] H :=
  LinearMap.mkContinuous (A.domain.subtype ∘ₗ (shiftEquiv hA s hs).symm.toLinearMap) 1
    fun f => by
      have h := norm_le_norm_shift hA hs ((shiftEquiv hA s hs).symm f)
      rw [← shiftEquiv_apply hA hs, LinearEquiv.apply_symm_apply] at h
      rw [one_mul]
      exact h

theorem resolventI_apply {s : ℝ} (hs : |s| = 1) (f : H) :
    resolventI hA s hs f = ((shiftEquiv hA s hs).symm f : H) :=
  rfl

/-- `(A + i s)⁻¹ f ∈ D(A)`. -/
theorem resolventI_mem_domain {s : ℝ} (hs : |s| = 1) (f : H) :
    resolventI hA s hs f ∈ A.domain :=
  ((shiftEquiv hA s hs).symm f).2

/-- `(A + i s) (A + i s)⁻¹ f = f`. -/
theorem addScalar_resolventI {s : ℝ} (hs : |s| = 1) (f : H) :
    A ⟨resolventI hA s hs f, resolventI_mem_domain hA hs f⟩ +
      ((s : ℂ) * RCLike.I) • resolventI hA s hs f = f := by
  have h := (shiftEquiv hA s hs).apply_symm_apply f
  rw [shiftEquiv_apply] at h
  exact h

/-- `(A + i s)⁻¹ (A + i s) x = x` for `x ∈ D(A)`. -/
theorem resolventI_addScalar {s : ℝ} (hs : |s| = 1) (x : A.domain) :
    resolventI hA s hs (A x + ((s : ℂ) * RCLike.I) • (x : H)) = x := by
  rw [resolventI_apply, ← shiftEquiv_apply hA hs, LinearEquiv.symm_apply_apply]

/-- `(A + i s)⁻¹` is injective. -/
theorem resolventI_injective {s : ℝ} (hs : |s| = 1) :
    Function.Injective (resolventI hA s hs) := fun f g hfg => by
  rw [← addScalar_resolventI hA hs f, ← addScalar_resolventI hA hs g]
  simp only [hfg]

/-- The range of `(A + i s)⁻¹` is `D(A)`. -/
theorem mem_domain_iff_exists_resolventI {s : ℝ} (hs : |s| = 1) (x : H) :
    x ∈ A.domain ↔ ∃ f, resolventI hA s hs f = x := by
  refine ⟨fun hx => ⟨A ⟨x, hx⟩ + ((s : ℂ) * RCLike.I) • x, ?_⟩, ?_⟩
  · exact resolventI_addScalar hA hs ⟨x, hx⟩
  · rintro ⟨f, rfl⟩
    exact resolventI_mem_domain hA hs f

/-- **`((A + i s)⁻¹)† = (A - i s)⁻¹`** (Reed–Simon I, proof of Theorem VIII.4, p. 261). -/
theorem adjoint_resolventI {s : ℝ} (hs : |s| = 1) :
    ContinuousLinearMap.adjoint (resolventI hA s hs) =
      resolventI hA (-s) (abs_neg_eq_one hs) := by
  have hsymm := IsSymmetric.of_isSelfAdjoint hA
  refine ((ContinuousLinearMap.eq_adjoint_iff _ _).mpr fun g f => ?_).symm
  set y := resolventI hA (-s) (abs_neg_eq_one hs) g
  set x := resolventI hA s hs f
  have hy := addScalar_resolventI hA (abs_neg_eq_one hs) g
  have hx := addScalar_resolventI hA hs f
  have hAxy := hsymm.isFormalAdjoint ⟨y, resolventI_mem_domain hA _ g⟩
    ⟨x, resolventI_mem_domain hA hs f⟩
  change ⟪y, f⟫_ℂ = ⟪g, x⟫_ℂ
  rw [← hx, ← hy, inner_add_right, inner_smul_right, inner_add_left, inner_smul_left,
    conj_shift, hAxy]

/-- If `(A - i s) y = f`, then `y = (A + i s)⁻¹ f + 2 i s (A + i s)⁻¹ y`. -/
theorem eq_resolventI_of_neg {s : ℝ} (hs : |s| = 1) (f y : H) (hy : y ∈ A.domain)
    (h : A ⟨y, hy⟩ + (((-s : ℝ) : ℂ) * RCLike.I) • y = f) :
    y = resolventI hA s hs f + ((2 * s : ℝ) * RCLike.I : ℂ) • resolventI hA s hs y := by
  have hshift : A ⟨y, hy⟩ + ((s : ℂ) * RCLike.I) • y =
      f + ((2 * s : ℝ) * RCLike.I : ℂ) • y := by
    rw [← h]
    push_cast
    module
  have h' := resolventI_addScalar hA hs ⟨y, hy⟩
  rw [hshift, map_add, map_smul] at h'
  exact h'.symm

/-- **The resolvent identity** `(A - i s)⁻¹ = (A + i s)⁻¹ + 2 i s (A + i s)⁻¹ (A - i s)⁻¹`. -/
theorem resolventI_neg_eq {s : ℝ} (hs : |s| = 1) (f : H) :
    resolventI hA (-s) (abs_neg_eq_one hs) f =
      resolventI hA s hs f + ((2 * s : ℝ) * RCLike.I : ℂ) •
        resolventI hA s hs (resolventI hA (-s) (abs_neg_eq_one hs) f) :=
  eq_resolventI_of_neg hA hs f _ (resolventI_mem_domain hA _ f)
    (addScalar_resolventI hA (abs_neg_eq_one hs) f)

/-- **`(A + i s)⁻¹` and `(A - i s)⁻¹` commute** (Reed–Simon I, proof of Theorem VIII.4, p. 261,
by Theorem VIII.2). -/
theorem resolventI_commute {s : ℝ} (hs : |s| = 1) :
    resolventI hA s hs * resolventI hA (-s) (abs_neg_eq_one hs) =
      resolventI hA (-s) (abs_neg_eq_one hs) * resolventI hA s hs := by
  ext f
  have h1 := resolventI_neg_eq hA hs f
  have h2 := resolventI_neg_eq hA (abs_neg_eq_one hs) f
  simp only [neg_neg] at h2
  have hc : ((2 * s : ℝ) * RCLike.I : ℂ) ≠ 0 := by
    simp [ne_zero_of_abs_eq_one hs]
  have key : ((2 * s : ℝ) * RCLike.I : ℂ) •
      (resolventI hA s hs (resolventI hA (-s) (abs_neg_eq_one hs) f) -
        resolventI hA (-s) (abs_neg_eq_one hs) (resolventI hA s hs f)) = 0 := by
    rw [smul_sub]
    push_cast at h1 h2 ⊢
    linear_combination (norm := module) -h1 - h2
  have := (smul_eq_zero.mp key).resolve_left hc
  rw [mul_apply_eq_comp, mul_apply_eq_comp]
  exact sub_eq_zero.mp this

/-- **`(A + i s)⁻¹` is normal** (Reed–Simon I, proof of Theorem VIII.4, p. 261). -/
theorem isStarNormal_resolventI {s : ℝ} (hs : |s| = 1) : IsStarNormal (resolventI hA s hs) := by
  refine ⟨?_⟩
  rw [ContinuousLinearMap.star_eq_adjoint, adjoint_resolventI]
  exact (resolventI_commute hA hs).symm

end SpectralTheorem
