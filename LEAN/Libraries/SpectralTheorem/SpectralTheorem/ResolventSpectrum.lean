import SpectralTheorem.Resolvent
import SpectralTheorem.SpectralProjection

/-!
# The spectrum and the spectral measures of `(A + i)⁻¹`

Let `A` be self-adjoint and `R = (A + i)⁻¹`, a bounded normal operator with trivial kernel
(`SpectralTheorem.Resolvent`).  Two facts about `R` turn its spectral representation into one
for `A` (Reed–Simon I, proof of Theorem VIII.4, p. 261):

* **`σ(R)` lies on the circle `|z|² + Im z = 0`**, so that `z⁻¹ - i` is real for `z ∈ σ(R)`,
  `z ≠ 0`.  This replaces Reed–Simon's final step ("`f` is real-valued, since multiplication by
  `f` is self-adjoint"): the resolvent identity gives `R - R† + 2i R R† = 0`, so the continuous
  function `z - z̄ + 2i |z|²` vanishes on `σ(R)` because the continuous functional calculus is
  injective.
* **`{0}` is a null set for every spectral measure of `R`**, which is Reed–Simon's
  "`g(m) ≠ 0` a.e.": `R χ_{0}(R) = (z χ_{0})(R) = 0`, so `χ_{0}(R) = 0` because `R` is injective,
  and `μ_ψ({0}) = ⟪ψ, χ_{0}(R) ψ⟫ = 0`.

The map `z ↦ (z⁻¹ - i).re` (`SpectralTheorem.resolventCoord`) sends `σ(R) \ {0}` to the real
numbers `λ` with `z = (λ + i)⁻¹`.

## Main results

* `SpectralTheorem.resolvent hA`: `R = (A + i)⁻¹`, with its `IsStarNormal` instance.
* `SpectralTheorem.resolvent_sub_star`: `R - R† + 2i R R† = 0`.
* `SpectralTheorem.normSq_add_im_eq_zero_of_mem_spectrum`: `|z|² + Im z = 0` on `σ(R)`.
* `SpectralTheorem.resolventCoord_add_I_mul`: `(λ + i) z = 1` for `λ = resolventCoord z`,
  `z ∈ σ(R) \ {0}`.
* `SpectralTheorem.spectralProjection_resolvent_zero`: `χ_{0}(R) = 0`.
* `SpectralTheorem.CyclicDecomposition.ae_coord_ne_zero`: the spectral variable of `R` is
  nonzero almost everywhere.
-/

noncomputable section

open scoped InnerProductSpace ComplexConjugate
open MeasureTheory Filter KatoRellich

namespace SpectralTheorem

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)

/-- The resolvent `R = (A + i)⁻¹` of a self-adjoint operator. -/
def resolvent : H →L[ℂ] H :=
  resolventI hA 1 abs_one

/-- `(A + i)⁻¹` is normal. -/
instance isStarNormal_resolvent : IsStarNormal (resolvent hA) :=
  isStarNormal_resolventI hA abs_one

/-- `R† = (A - i)⁻¹`. -/
theorem star_resolvent :
    star (resolvent hA) = resolventI hA (-1) (abs_neg_eq_one abs_one) := by
  rw [ContinuousLinearMap.star_eq_adjoint, resolvent, adjoint_resolventI]

/-- **The resolvent identity** in the form `R - R† + 2i R R† = 0`. -/
theorem resolvent_sub_star :
    resolvent hA - star (resolvent hA) +
      (2 * Complex.I) • (resolvent hA * star (resolvent hA)) = 0 := by
  ext1 f
  have h := resolventI_neg_eq hA (s := 1) abs_one f
  rw [star_resolvent, add_apply, sub_apply, FunLike.coe_smul, Pi.smul_apply, mul_apply_eq_comp,
    zero_apply]
  change resolventI hA 1 abs_one f - resolventI hA (-1) _ f +
    (2 * Complex.I) • resolventI hA 1 abs_one (resolventI hA (-1) _ f) = 0
  simp only [RCLike.I_to_complex, mul_one, Complex.ofReal_ofNat] at h
  linear_combination (norm := module) -h

/-- **The spectrum of `(A + i)⁻¹` lies on the circle `|z|² + Im z = 0`.** -/
theorem normSq_add_im_eq_zero_of_mem_spectrum {z : ℂ} (hz : z ∈ spectrum ℂ (resolvent hA)) :
    ‖z‖ ^ 2 + z.im = 0 := by
  let ι : C(spectrum ℂ (resolvent hA), ℂ) := (ContinuousMap.id ℂ).restrict _
  let F := ι - star ι + (2 * Complex.I) • (ι * star ι)
  have hF : cfcHom (isStarNormal_resolvent hA) F =
      cfcHom (isStarNormal_resolvent hA) (0 : C(spectrum ℂ (resolvent hA), ℂ)) := by
    rw [map_zero, map_add, map_sub, map_smul, map_mul, map_star, cfcHom_id]
    exact resolvent_sub_star hA
  have h0 := DFunLike.congr_fun (cfcHom_injective (isStarNormal_resolvent hA) hF) ⟨z, hz⟩
  simp only [F, ι, ContinuousMap.add_apply, ContinuousMap.sub_apply, ContinuousMap.smul_apply,
    ContinuousMap.mul_apply, ContinuousMap.star_apply, ContinuousMap.restrict_apply,
    ContinuousMap.id_apply, ContinuousMap.zero_apply, RCLike.star_def, smul_eq_mul] at h0
  have him := congrArg Complex.im h0
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at him
  simp at him
  rw [← Complex.ofReal_pow, Complex.ofReal_re] at him
  linarith

/-- The real number `λ = (z⁻¹ - i).re` attached to a point `z` of `σ(A + i)⁻¹`: for
`z ∈ σ(R) \ {0}`, `z = (λ + i)⁻¹` (`resolventCoord_add_I_mul`). -/
def resolventCoord (z : ℂ) : ℝ :=
  (z⁻¹ - Complex.I).re -- totalisation-audit: allow used only for z ≠ 0; {0} is null (below)

theorem measurable_resolventCoord : Measurable resolventCoord :=
  Complex.measurable_re.comp (measurable_inv.sub measurable_const)

/-- For `z ∈ σ(R)`, `z ≠ 0`: `z⁻¹ - i` is real, equal to `resolventCoord z`. -/
theorem ofReal_resolventCoord {z : ℂ} (hz : z ∈ spectrum ℂ (resolvent hA)) (h0 : z ≠ 0) :
    (resolventCoord z : ℂ) = z⁻¹ - Complex.I := by
  have hc := normSq_add_im_eq_zero_of_mem_spectrum hA hz
  have hn : Complex.normSq z ≠ 0 := by rwa [Ne, Complex.normSq_eq_zero]
  refine Complex.ext (by simp [resolventCoord]) ?_
  rw [Complex.ofReal_im, Complex.sub_im, Complex.inv_im, Complex.I_im,
    Complex.normSq_eq_norm_sq]
  have hz2 : ‖z‖ ^ 2 ≠ 0 := by rwa [← Complex.normSq_eq_norm_sq]
  field_simp
  linarith

/-- For `z ∈ σ(R)`, `z ≠ 0`: `(λ + i) z = 1` with `λ = resolventCoord z`. -/
theorem resolventCoord_add_I_mul {z : ℂ} (hz : z ∈ spectrum ℂ (resolvent hA)) (h0 : z ≠ 0) :
    ((resolventCoord z : ℂ) + Complex.I) * z = 1 := by
  rw [ofReal_resolventCoord hA hz h0, sub_add_cancel, inv_mul_cancel₀ h0]

/-- **`χ_{0}(R) = 0`**: `R χ_{0}(R) = (z χ_{0}(z))(R) = 0` and `R` is injective. -/
theorem spectralProjection_resolvent_zero :
    spectralProjection (resolvent hA) (measurableSet_singleton (0 : ℂ)) = 0 := by
  have hmul : resolvent hA * spectralProjection (resolvent hA) (measurableSet_singleton 0) = 0 := by
    have hzero : idBM (resolvent hA) * indicatorBM (resolvent hA) (measurableSet_singleton 0) =
        0 := by
      refine Subtype.ext (funext fun x => ?_)
      change (x : ℂ) * ({0} : Set ℂ).indicator (fun _ => (1 : ℂ)) (x : ℂ) = 0
      by_cases hx : (x : ℂ) = 0 <;> simp [hx]
    have h := congrArg (borelCalc (resolvent hA)) hzero
    rw [map_mul, map_zero, borelCalc_id] at h
    exact h
  ext1 h
  apply resolventI_injective hA abs_one
  rw [zero_apply, map_zero]
  have h' := DFunLike.congr_fun hmul h
  rwa [mul_apply_eq_comp, zero_apply] at h'

/-- **`{0}` is null for the spectral measures of `R`**: `μ_ψ({0}) = ⟪ψ, χ_{0}(R) ψ⟫ = 0`. -/
theorem spectralMeasure_resolvent_zero (ψ : H) :
    spectralMeasure (resolvent hA) ψ (Subtype.val ⁻¹' {0}) = 0 := by
  have h := inner_spectralProjection (T := resolvent hA) ψ (measurableSet_singleton (0 : ℂ))
  rw [spectralProjection_resolvent_zero, zero_apply, inner_zero_right, eq_comm,
    Complex.ofReal_eq_zero, measureReal_eq_zero_iff (measure_ne_top _ _)] at h
  exact h

/-- **The spectral variable of `R` is nonzero almost everywhere**, for every cyclic
decomposition of `R` (Reed–Simon I, p. 261: "`g(m) ≠ 0` a.e."). -/
theorem CyclicDecomposition.ae_coord_ne_zero (D : CyclicDecomposition (resolvent hA)) :
    ∀ᵐ p ∂D.measure, D.coord p ≠ 0 := by
  refine (ae_sigmaMeasure_iff _).mpr fun ψ => ?_
  rw [ae_iff]
  convert spectralMeasure_resolvent_zero hA (ψ : H) using 2
  ext x
  simp [CyclicDecomposition.coord]

end SpectralTheorem
