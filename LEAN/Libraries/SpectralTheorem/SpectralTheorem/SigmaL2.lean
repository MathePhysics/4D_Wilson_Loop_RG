import SpectralTheorem.SigmaMeasure
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.Normed.Lp.lpSpace

/-!
# `L²` of a disjoint union is the Hilbert sum of the `L²` spaces

For a family of measure spaces `(X i, μ i)` indexed by an arbitrary (possibly uncountable) type
`ι`, we construct the isometric isomorphism
`sigmaL2Equiv μ : Lp ℂ 2 (sigmaMeasure μ) ≃ₗᵢ[ℂ] lp (fun i => Lp ℂ 2 (μ i)) 2`
sending `f` to the family of its slices `i ↦ [x ↦ f ⟨i, x⟩]`.

Injectivity and the isometry property come from `eLpNorm_sigmaMeasure_two_sq`.  For surjectivity,
a family `F` in the `ℓ²` sum is glued from strongly measurable representatives of its components;
the glued function is measurable because measurability on a sigma type is checked slice by slice.

## Main definitions

* `sigmaL2Slice μ f i`: the `i`-th slice of `f ∈ L²(sigmaMeasure μ)`, as an element of `L²(μ i)`.
* `sigmaL2Glue μ F`: a measurable function glued from representatives of the components of `F`.
* `sigmaL2Equiv μ`: the isometric isomorphism.

## Main results

* `hasSum_norm_sigmaL2Slice_sq`: `‖f‖²` is the sum of the squared norms of the slices.
* `sigmaL2Equiv_apply_ae_eq`: each component of `sigmaL2Equiv μ f` is a.e. the slice of `f`.
* `sigmaL2Equiv_symm_ae_eq`: `(sigmaL2Equiv μ).symm F` is a.e. equal to `fun p => F p.1 p.2`.
* `sigmaL2Equiv_symm_apply`: `(sigmaL2Equiv μ).symm F` is the class of `sigmaL2Glue μ F`.
* `sigmaL2Equiv_symm_apply_eq_toLp`: `(sigmaL2Equiv μ).symm F` is the class of any `L²` function
  whose slices represent the components of `F`.
* `sigmaL2Equiv_mul_ae_eq`: multiplication by a function on the sigma type acts slice by slice;
  `sigmaL2_memLp_mul` gives the needed `L²` membership for essentially bounded multipliers.
-/

open MeasureTheory Set Filter
open scoped ENNReal

namespace SpectralTheorem

variable {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)] (μ : ∀ i, Measure (X i))

/-! ### Slices of `L²` functions -/

/-- The `i`-th slice `x ↦ f ⟨i, x⟩` of `f ∈ L²(sigmaMeasure μ)`, as an element of `L²(μ i)`. -/
noncomputable def sigmaL2Slice (f : Lp ℂ 2 (sigmaMeasure μ)) (i : ι) : Lp ℂ 2 (μ i) :=
  (memLp_sigma_slice μ (Lp.memLp f) i).toLp fun x => f ⟨i, x⟩

/-- The slice `sigmaL2Slice μ f i` is represented by `x ↦ f ⟨i, x⟩`. -/
theorem sigmaL2Slice_ae_eq (f : Lp ℂ 2 (sigmaMeasure μ)) (i : ι) :
    (sigmaL2Slice μ f i : X i → ℂ) =ᵐ[μ i] fun x => f ⟨i, x⟩ :=
  MemLp.coeFn_toLp _

/-- An element of `L²(μ i)` represented by the slice of `f` is `sigmaL2Slice μ f i`. -/
theorem sigmaL2Slice_eq_of_ae_eq {f : Lp ℂ 2 (sigmaMeasure μ)} {i : ι} {g : Lp ℂ 2 (μ i)}
    (h : (g : X i → ℂ) =ᵐ[μ i] fun x => f ⟨i, x⟩) : sigmaL2Slice μ f i = g :=
  Lp.ext ((sigmaL2Slice_ae_eq μ f i).trans h.symm)

/-- The slice of the class of an `L²` function is the class of its slice. -/
theorem sigmaL2Slice_toLp {f : (Σ i, X i) → ℂ} (hf : MemLp f 2 (sigmaMeasure μ)) (i : ι) :
    sigmaL2Slice μ (hf.toLp f) i = (memLp_sigma_slice μ hf i).toLp fun x => f ⟨i, x⟩ :=
  sigmaL2Slice_eq_of_ae_eq μ <| (MemLp.coeFn_toLp _).trans
    ((ae_eq_sigmaMeasure_iff μ).1 (MemLp.coeFn_toLp hf) i).symm

/-- Slicing is additive. -/
theorem sigmaL2Slice_add (f g : Lp ℂ 2 (sigmaMeasure μ)) (i : ι) :
    sigmaL2Slice μ (f + g) i = sigmaL2Slice μ f i + sigmaL2Slice μ g i := by
  refine sigmaL2Slice_eq_of_ae_eq μ ?_
  refine (Lp.coeFn_add _ _).trans (((sigmaL2Slice_ae_eq μ f i).add
    (sigmaL2Slice_ae_eq μ g i)).trans ?_)
  exact ((ae_eq_sigmaMeasure_iff μ).1 (Lp.coeFn_add f g) i).symm

/-- Slicing commutes with scalar multiplication. -/
theorem sigmaL2Slice_smul (c : ℂ) (f : Lp ℂ 2 (sigmaMeasure μ)) (i : ι) :
    sigmaL2Slice μ (c • f) i = c • sigmaL2Slice μ f i := by
  refine sigmaL2Slice_eq_of_ae_eq μ ?_
  refine (Lp.coeFn_smul _ _).trans (((sigmaL2Slice_ae_eq μ f i).const_smul c).trans ?_)
  exact ((ae_eq_sigmaMeasure_iff μ).1 (Lp.coeFn_smul c f) i).symm

/-- The extended norm of a slice is the `L²` seminorm of the slice function. -/
theorem enorm_sigmaL2Slice (f : Lp ℂ 2 (sigmaMeasure μ)) (i : ι) :
    ‖sigmaL2Slice μ f i‖ₑ = eLpNorm (fun x => f ⟨i, x⟩) 2 (μ i) :=
  Lp.enorm_toLp _

/-- The squared norm of `f ∈ L²(sigmaMeasure μ)` is the sum of the squared norms of its slices,
in `ℝ≥0∞`. -/
theorem tsum_enorm_sigmaL2Slice_sq (f : Lp ℂ 2 (sigmaMeasure μ)) :
    ∑' i, ‖sigmaL2Slice μ f i‖ₑ ^ 2 = ‖f‖ₑ ^ 2 := by -- totalisation-audit: allow ℝ≥0∞ sum
  simp_rw [enorm_sigmaL2Slice, Lp.enorm_def]
  exact (eLpNorm_sigmaMeasure_two_sq μ f).symm

/-- The squared norm of `f ∈ L²(sigmaMeasure μ)` is the sum of the squared norms of its
slices. -/
theorem hasSum_norm_sigmaL2Slice_sq (f : Lp ℂ 2 (sigmaMeasure μ)) :
    HasSum (fun i => ‖sigmaL2Slice μ f i‖ ^ 2) (‖f‖ ^ 2) := by
  have hne := (tsum_enorm_sigmaL2Slice_sq μ f).trans_ne (ENNReal.pow_ne_top enorm_ne_top)
  have hsum := (ENNReal.summable_toReal hne).hasSum
  rw [← ENNReal.tsum_toReal_eq fun i => ENNReal.pow_ne_top enorm_ne_top,
    tsum_enorm_sigmaL2Slice_sq] at hsum
  simpa [ENNReal.toReal_pow] using hsum

/-- The family of slices of `f ∈ L²(sigmaMeasure μ)` is square summable. -/
theorem memℓp_sigmaL2Slice (f : Lp ℂ 2 (sigmaMeasure μ)) : Memℓp (sigmaL2Slice μ f) 2 := by
  refine memℓp_gen ?_
  simpa [Real.rpow_two] using (hasSum_norm_sigmaL2Slice_sq μ f).summable

/-! ### Gluing a square-summable family -/

/-- The function on the sigma type glued from strongly measurable representatives of the
components of `F`. -/
noncomputable def sigmaL2Glue (F : lp (fun i => Lp ℂ 2 (μ i)) 2) : (Σ i, X i) → ℂ :=
  fun p => (Lp.aestronglyMeasurable (F p.1)).mk _ p.2

/-- The glued function is measurable. -/
theorem measurable_sigmaL2Glue (F : lp (fun i => Lp ℂ 2 (μ i)) 2) :
    Measurable (sigmaL2Glue μ F) :=
  measurable_sigma_iff.2 fun i => (Lp.aestronglyMeasurable (F i)).measurable_mk

/-- The slices of the glued function represent the components of `F`. -/
theorem sigmaL2Glue_slice_ae_eq (F : lp (fun i => Lp ℂ 2 (μ i)) 2) (i : ι) :
    (F i : X i → ℂ) =ᵐ[μ i] fun x => sigmaL2Glue μ F ⟨i, x⟩ :=
  (Lp.aestronglyMeasurable (F i)).ae_eq_mk

/-- The glued function of a square-summable family is in `L²(sigmaMeasure μ)`. -/
theorem memLp_sigmaL2Glue (F : lp (fun i => Lp ℂ 2 (μ i)) 2) :
    MemLp (sigmaL2Glue μ F) 2 (sigmaMeasure μ) := by
  refine (memLp_two_sigma_iff μ).2
    ⟨fun i => (Lp.memLp (F i)).ae_eq (sigmaL2Glue_slice_ae_eq μ F i), ?_⟩
  have heq : ∀ i, eLpNorm (fun x => sigmaL2Glue μ F ⟨i, x⟩) 2 (μ i) ^ 2 =
      ENNReal.ofReal (‖F i‖ ^ 2) := fun i => by
    rw [eLpNorm_congr_ae (sigmaL2Glue_slice_ae_eq μ F i).symm, ← Lp.enorm_def,
      ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  have hs : Summable fun i => ‖F i‖ ^ 2 := by
    simpa [Real.rpow_two] using (lp.memℓp F).summable (by norm_num)
  simp_rw [heq]
  exact hs.tsum_ofReal_lt_top

/-! ### The isometric isomorphism -/

/-- Slicing, as a linear isometry from `L²(sigmaMeasure μ)` to the `ℓ²` sum of the `L²(μ i)`. -/
noncomputable def sigmaL2Isometry :
    Lp ℂ 2 (sigmaMeasure μ) →ₗᵢ[ℂ] lp (fun i => Lp ℂ 2 (μ i)) 2 where
  toFun f := ⟨sigmaL2Slice μ f, memℓp_sigmaL2Slice μ f⟩
  map_add' f g := lp.ext <| funext fun i => sigmaL2Slice_add μ f g i
  map_smul' c f := lp.ext <| funext fun i => sigmaL2Slice_smul μ c f i
  norm_map' f := by
    set F : lp (fun i => Lp ℂ 2 (μ i)) 2 := ⟨sigmaL2Slice μ f, memℓp_sigmaL2Slice μ f⟩
    have h := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) F
    simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h
    have h2 : ‖F‖ ^ 2 = ‖f‖ ^ 2 := h.trans (hasSum_norm_sigmaL2Slice_sq μ f).tsum_eq
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h2

/-- The components of `sigmaL2Isometry μ f` are the slices of `f`. -/
theorem sigmaL2Isometry_apply (f : Lp ℂ 2 (sigmaMeasure μ)) (i : ι) :
    sigmaL2Isometry μ f i = sigmaL2Slice μ f i :=
  rfl

/-- The class of the glued function is mapped to `F`. -/
theorem sigmaL2Isometry_toLp_sigmaL2Glue (F : lp (fun i => Lp ℂ 2 (μ i)) 2) :
    sigmaL2Isometry μ ((memLp_sigmaL2Glue μ F).toLp _) = F :=
  lp.ext <| funext fun i => sigmaL2Slice_eq_of_ae_eq μ <| (sigmaL2Glue_slice_ae_eq μ F i).trans
    ((ae_eq_sigmaMeasure_iff μ).1 (MemLp.coeFn_toLp (memLp_sigmaL2Glue μ F)) i).symm

/-- Slicing is surjective onto the `ℓ²` sum. -/
theorem sigmaL2Isometry_surjective : Function.Surjective (sigmaL2Isometry μ) :=
  fun F => ⟨_, sigmaL2Isometry_toLp_sigmaL2Glue μ F⟩

/-- **`L²` of a disjoint union is the Hilbert sum of the `L²` spaces**: the isometric isomorphism
`L²(Σ i, X i, sigmaMeasure μ) ≃ ⨁ᵢ L²(X i, μ i)` sending `f` to its family of slices.  The index
type `ι` is arbitrary. -/
noncomputable def sigmaL2Equiv : Lp ℂ 2 (sigmaMeasure μ) ≃ₗᵢ[ℂ] lp (fun i => Lp ℂ 2 (μ i)) 2 :=
  LinearIsometryEquiv.ofSurjective (sigmaL2Isometry μ) (sigmaL2Isometry_surjective μ)

/-- The components of `sigmaL2Equiv μ f` are the slices of `f`. -/
@[simp]
theorem sigmaL2Equiv_apply (f : Lp ℂ 2 (sigmaMeasure μ)) (i : ι) :
    sigmaL2Equiv μ f i = sigmaL2Slice μ f i :=
  rfl

/-- The `i`-th component of `sigmaL2Equiv μ f` is represented by the slice `x ↦ f ⟨i, x⟩`. -/
theorem sigmaL2Equiv_apply_ae_eq (f : Lp ℂ 2 (sigmaMeasure μ)) (i : ι) :
    (sigmaL2Equiv μ f i : X i → ℂ) =ᵐ[μ i] fun x => f ⟨i, x⟩ :=
  sigmaL2Slice_ae_eq μ f i

/-- The inverse of `sigmaL2Equiv μ` glues the components: `(sigmaL2Equiv μ).symm F` is a.e. equal
to `fun p => F p.1 p.2`, for any choice of representatives of the components. -/
theorem sigmaL2Equiv_symm_ae_eq (F : lp (fun i => Lp ℂ 2 (μ i)) 2) :
    ((sigmaL2Equiv μ).symm F : (Σ i, X i) → ℂ) =ᵐ[sigmaMeasure μ] fun p => F p.1 p.2 := by
  refine (ae_eq_sigmaMeasure_iff μ).2 fun i => ?_
  have h := sigmaL2Equiv_apply_ae_eq μ ((sigmaL2Equiv μ).symm F) i
  rw [LinearIsometryEquiv.apply_symm_apply] at h
  exact h.symm

/-- The inverse of `sigmaL2Equiv μ` is the class of any `L²` function whose slices represent the
components of `F`. -/
theorem sigmaL2Equiv_symm_apply_eq_toLp {F : lp (fun i => Lp ℂ 2 (μ i)) 2}
    {g : (Σ i, X i) → ℂ} (hg : MemLp g 2 (sigmaMeasure μ))
    (h : ∀ i, (F i : X i → ℂ) =ᵐ[μ i] fun x => g ⟨i, x⟩) :
    (sigmaL2Equiv μ).symm F = hg.toLp g := by
  rw [LinearIsometryEquiv.symm_apply_eq]
  refine lp.ext <| funext fun i => (sigmaL2Slice_eq_of_ae_eq μ ?_).symm
  exact (h i).trans ((ae_eq_sigmaMeasure_iff μ).1 (MemLp.coeFn_toLp hg) i).symm

/-- The inverse of `sigmaL2Equiv μ` is the class of the measurable function glued from strongly
measurable representatives of the components. -/
theorem sigmaL2Equiv_symm_apply (F : lp (fun i => Lp ℂ 2 (μ i)) 2) :
    (sigmaL2Equiv μ).symm F = (memLp_sigmaL2Glue μ F).toLp (sigmaL2Glue μ F) :=
  sigmaL2Equiv_symm_apply_eq_toLp μ _ (sigmaL2Glue_slice_ae_eq μ F)

/-! ### Multiplication acts slice by slice -/

/-- Multiplication by a function `g` on the sigma type corresponds to multiplying the `i`-th
component by the slice `x ↦ g ⟨i, x⟩`. -/
theorem sigmaL2Equiv_mul_ae_eq {g : (Σ i, X i) → ℂ} {f : Lp ℂ 2 (sigmaMeasure μ)}
    (hgf : MemLp (fun p => g p * f p) 2 (sigmaMeasure μ)) (i : ι) :
    (sigmaL2Equiv μ (hgf.toLp _) i : X i → ℂ) =ᵐ[μ i]
      fun x => g ⟨i, x⟩ * sigmaL2Equiv μ f i x := by
  refine (sigmaL2Equiv_apply_ae_eq μ _ i).trans ?_
  filter_upwards [(ae_eq_sigmaMeasure_iff μ).1 (MemLp.coeFn_toLp hgf) i,
    sigmaL2Equiv_apply_ae_eq μ f i] with x hx1 hx2
  rw [hx1, hx2]

/-- The product of an a.e. strongly measurable, essentially bounded function with an element of
`L²(sigmaMeasure μ)` is in `L²`. -/
theorem sigmaL2_memLp_mul {g : (Σ i, X i) → ℂ} (hg : AEStronglyMeasurable g (sigmaMeasure μ))
    {C : ℝ} (hC : ∀ᵐ p ∂sigmaMeasure μ, ‖g p‖ ≤ C) (f : Lp ℂ 2 (sigmaMeasure μ)) :
    MemLp (fun p => g p * f p) 2 (sigmaMeasure μ) :=
  (Lp.memLp f).of_le_mul (hg.mul (Lp.aestronglyMeasurable f)) <| by
    filter_upwards [hC] with p hp
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right hp (norm_nonneg _)

end SpectralTheorem
