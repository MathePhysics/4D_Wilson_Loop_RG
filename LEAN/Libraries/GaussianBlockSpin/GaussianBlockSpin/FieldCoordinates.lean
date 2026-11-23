import GaussianBlockSpin.GaussChangeOfVariables
import GaussianBlockSpin.PiLpVolume

/-! Coordinates on a field space `PiLp 2 (ι → EuclideanSpace ℝ κ)`:
* fieldCoord: the linear equivalence with `ι × κ → ℝ` (`fieldCoord z i k = z (i, k)`), volume preserving
  (measurePreserving_fieldCoord) and inner-product preserving (inner_fieldCoord: `⟪φ u, φ w⟫ = u·w`);
* fieldMatrix T: the matrix of an operator in these coordinates, with `z·(M z) = ⟪φ z, T φ z⟫`
  (dotProduct_fieldMatrix), entries `M (i, k) (j, l) = (T (φ e_{(j, l)})) i k` (fieldMatrix_apply), symmetric for
  symmetric `T` (fieldMatrix_transpose). -/

namespace GaussianBlockSpin

open MeasureTheory Matrix
open scoped RealInnerProductSpace

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- The coordinates `z (i, k)` of a field. -/
noncomputable def fieldCoord : ((ι × κ) → ℝ) ≃ₗ[ℝ] PiLp 2 (fun _ : ι => EuclideanSpace ℝ κ) :=
  (WithLp.linearEquiv 2 ℝ ((ι × κ) → ℝ)).symm.trans (flattenIsometry (ι := ι) (κ := κ)).symm.toLinearEquiv

omit [DecidableEq ι] [DecidableEq κ] in
@[simp] lemma fieldCoord_apply (z : (ι × κ) → ℝ) (i : ι) (k : κ) : fieldCoord z i k = z (i, k) := rfl

omit [DecidableEq ι] [DecidableEq κ] in
@[simp] lemma fieldCoord_symm_apply (f : PiLp 2 (fun _ : ι => EuclideanSpace ℝ κ)) (p : ι × κ) :
    fieldCoord.symm f p = f p.1 p.2 := rfl

omit [DecidableEq ι] [DecidableEq κ] in
lemma measurePreserving_fieldCoord :
    MeasurePreserving (fieldCoord (ι := ι) (κ := κ)) volume volume :=
  ((flattenIsometry (ι := ι) (κ := κ)).symm.measurePreserving).comp (PiLp.volume_preserving_toLp (ι × κ))

omit [DecidableEq ι] [DecidableEq κ] in
lemma continuous_fieldCoord_symm :
    Continuous (fieldCoord (ι := ι) (κ := κ)).symm :=
  (PiLp.continuous_ofLp 2 _).comp (flattenIsometry (ι := ι) (κ := κ)).continuous

omit [DecidableEq ι] [DecidableEq κ] in
lemma inner_fieldCoord (u w : (ι × κ) → ℝ) : ⟪(fieldCoord u : PiLp 2 (fun _ : ι => EuclideanSpace ℝ κ)),
    fieldCoord w⟫ = u ⬝ᵥ w := by
  simp only [PiLp.inner_apply, fieldCoord_apply, RCLike.inner_apply, conj_trivial, dotProduct]
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => mul_comm _ _

/-- The matrix of an operator in the coordinates. -/
noncomputable def fieldMatrix (T : PiLp 2 (fun _ : ι => EuclideanSpace ℝ κ) →ₗ[ℝ] PiLp 2 (fun _ : ι => EuclideanSpace ℝ κ)) :
    Matrix (ι × κ) (ι × κ) ℝ :=
  LinearMap.toMatrix' ((fieldCoord (ι := ι) (κ := κ)).symm.toLinearMap ∘ₗ T ∘ₗ
    (fieldCoord (ι := ι) (κ := κ)).toLinearMap)

lemma fieldMatrix_mulVec (T : PiLp 2 (fun _ : ι => EuclideanSpace ℝ κ) →ₗ[ℝ] PiLp 2 (fun _ : ι => EuclideanSpace ℝ κ))
    (z : (ι × κ) → ℝ) : fieldMatrix T *ᵥ z = fieldCoord.symm (T (fieldCoord z)) := by
  rw [fieldMatrix, LinearMap.toMatrix'_mulVec]
  rfl

lemma dotProduct_fieldMatrix (T : PiLp 2 (fun _ : ι => EuclideanSpace ℝ κ) →ₗ[ℝ] PiLp 2 (fun _ : ι => EuclideanSpace ℝ κ))
    (z : (ι × κ) → ℝ) : z ⬝ᵥ fieldMatrix T *ᵥ z = ⟪(fieldCoord z : PiLp 2 (fun _ : ι => EuclideanSpace ℝ κ)),
      T (fieldCoord z)⟫ := by
  rw [fieldMatrix_mulVec, ← inner_fieldCoord, LinearEquiv.apply_symm_apply]

lemma fieldMatrix_apply (T : PiLp 2 (fun _ : ι => EuclideanSpace ℝ κ) →ₗ[ℝ] PiLp 2 (fun _ : ι => EuclideanSpace ℝ κ))
    (p q : ι × κ) : fieldMatrix T p q = T (fieldCoord (Pi.single q 1)) p.1 p.2 := by
  rw [fieldMatrix, LinearMap.toMatrix'_apply]
  rfl

/-- The entries as matrix elements: `M p q = ⟪φ e_p, T φ e_q⟫`. -/
lemma fieldMatrix_eq_inner (T : PiLp 2 (fun _ : ι => EuclideanSpace ℝ κ) →ₗ[ℝ] PiLp 2 (fun _ : ι => EuclideanSpace ℝ κ))
    (p q : ι × κ) : fieldMatrix T p q =
      ⟪(fieldCoord (Pi.single p 1) : PiLp 2 (fun _ : ι => EuclideanSpace ℝ κ)), T (fieldCoord (Pi.single q 1))⟫ := by
  have h : T (fieldCoord (Pi.single q 1)) = fieldCoord (fieldCoord.symm (T (fieldCoord (Pi.single q 1)))) :=
    (LinearEquiv.apply_symm_apply _ _).symm
  rw [h, inner_fieldCoord, single_dotProduct, one_mul, fieldMatrix_apply, fieldCoord_symm_apply]

lemma fieldMatrix_smul (s : ℝ)
    (T : PiLp 2 (fun _ : ι => EuclideanSpace ℝ κ) →ₗ[ℝ] PiLp 2 (fun _ : ι => EuclideanSpace ℝ κ)) :
    fieldMatrix (s • T) = s • fieldMatrix T := by
  unfold fieldMatrix
  rw [LinearMap.smul_comp, LinearMap.comp_smul, map_smul]

lemma fieldMatrix_transpose {T : PiLp 2 (fun _ : ι => EuclideanSpace ℝ κ) →ₗ[ℝ] PiLp 2 (fun _ : ι => EuclideanSpace ℝ κ)}
    (hT : T.IsSymmetric) : (fieldMatrix T)ᵀ = fieldMatrix T := by
  ext p q
  rw [transpose_apply, fieldMatrix_eq_inner, fieldMatrix_eq_inner, ← hT, real_inner_comm]

end GaussianBlockSpin
