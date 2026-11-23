import FriedrichsExtension.FriedrichsResolvent
import Mathlib.Analysis.InnerProductSpace.LinearPMap

open scoped InnerProductSpace

noncomputable section

namespace FriedrichsExtension
namespace SemiboundedSymmetricOperator

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (A : SemiboundedSymmetricOperator H) (shift : ℝ)
    (hshift : 0 < A.lowerBound + shift)

/-- The bounded Friedrichs resolvent, regarded as a partially defined operator with full domain. -/
def friedrichsResolventPMap : H →ₗ.[ℝ] H :=
  (A.friedrichsResolvent shift hshift).toLinearMap.toPMap ⊤

@[simp]
theorem friedrichsResolventPMap_domain :
    (A.friedrichsResolventPMap shift hshift).domain = ⊤ := rfl

@[simp]
theorem friedrichsResolventPMap_apply
    (x : (A.friedrichsResolventPMap shift hshift).domain) :
    A.friedrichsResolventPMap shift hshift x =
      A.friedrichsResolvent shift hshift (x : H) := rfl

/-- The full-domain partial resolvent is injective. -/
theorem friedrichsResolventPMap_ker_eq_bot :
    (A.friedrichsResolventPMap shift hshift).ker = ⊥ := by
  rw [LinearPMap.ker_eq_bot]
  intro x y hxy
  apply Subtype.ext
  apply A.friedrichsResolvent_injective shift hshift
  calc
    A.friedrichsResolvent shift hshift (x : H) =
        A.friedrichsResolventPMap shift hshift x :=
      (A.friedrichsResolventPMap_apply shift hshift x).symm
    _ = A.friedrichsResolventPMap shift hshift y := hxy
    _ = A.friedrichsResolvent shift hshift (y : H) :=
      A.friedrichsResolventPMap_apply shift hshift y

/--
The shifted Friedrichs operator is the partial inverse of the bounded resolvent.
Its domain is therefore the range of the resolvent.
-/
def shiftedFriedrichsOperator : H →ₗ.[ℝ] H :=
  (A.friedrichsResolventPMap shift hshift).inverse

/-- The domain of the shifted Friedrichs operator is exactly the resolvent range. -/
theorem shiftedFriedrichsOperator_domain :
    (A.shiftedFriedrichsOperator shift hshift).domain =
      (A.friedrichsResolvent shift hshift).range := by
  rw [shiftedFriedrichsOperator, LinearPMap.inverse_domain]
  ext y
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨(x : H), ?_⟩
    calc
      A.friedrichsResolvent shift hshift (x : H) =
          A.friedrichsResolventPMap shift hshift x :=
        (A.friedrichsResolventPMap_apply shift hshift x).symm
      _ = y := hx
  · rintro ⟨x, hx⟩
    let xₚ : (A.friedrichsResolventPMap shift hshift).domain := ⟨x, by simp⟩
    refine ⟨xₚ, ?_⟩
    calc
      A.friedrichsResolventPMap shift hshift xₚ =
          A.friedrichsResolvent shift hshift (xₚ : H) :=
        A.friedrichsResolventPMap_apply shift hshift xₚ
      _ = A.friedrichsResolvent shift hshift x := by rfl
      _ = y := hx

/-- The shifted Friedrichs operator is densely defined. -/
theorem shiftedFriedrichsOperator_dense_domain :
    Dense ((A.shiftedFriedrichsOperator shift hshift).domain : Set H) := by
  rw [A.shiftedFriedrichsOperator_domain shift hshift]
  exact A.friedrichsResolvent_range_dense shift hshift

/-- Every vector in the inverse domain has its unique resolvent preimage. -/
theorem shiftedFriedrichsOperator_exists_preimage
    (x : (A.shiftedFriedrichsOperator shift hshift).domain) :
    ∃ z : H,
      A.friedrichsResolvent shift hshift z = (x : H) ∧
      A.shiftedFriedrichsOperator shift hshift x = z := by
  have hxrange : (x : H) ∈ (A.friedrichsResolvent shift hshift).range := by
    rw [← A.shiftedFriedrichsOperator_domain shift hshift]
    exact x.prop
  rcases hxrange with ⟨z, hz⟩
  let Rₚ := A.friedrichsResolventPMap shift hshift
  let zₚ : Rₚ.domain := ⟨z, by simp [Rₚ]⟩
  have hzₚ : Rₚ zₚ = (x : H) := by
    simpa [Rₚ, zₚ, friedrichsResolventPMap] using hz
  refine ⟨z, hz, ?_⟩
  have hinv := LinearPMap.inverse_apply_eq
    (f := Rₚ) (A.friedrichsResolventPMap_ker_eq_bot shift hshift)
    (y := x) (x := zₚ) hzₚ
  change Rₚ.inverse x = z
  simpa [zₚ] using hinv

/-- The inverse relation on an actual resolvent value. -/
theorem shiftedFriedrichsOperator_apply_resolvent
    (z : H)
    (hz : A.friedrichsResolvent shift hshift z ∈
      (A.shiftedFriedrichsOperator shift hshift).domain) :
    A.shiftedFriedrichsOperator shift hshift
        ⟨A.friedrichsResolvent shift hshift z, hz⟩ = z := by
  rcases A.shiftedFriedrichsOperator_exists_preimage shift hshift
      ⟨A.friedrichsResolvent shift hshift z, hz⟩ with ⟨w, hw, hTw⟩
  have hwz : w = z := A.friedrichsResolvent_injective shift hshift (by simpa using hw)
  simpa [hwz] using hTw

/-- The shifted Friedrichs operator is symmetric. -/
theorem shiftedFriedrichsOperator_symmetric :
    (A.shiftedFriedrichsOperator shift hshift).IsFormalAdjoint
      (A.shiftedFriedrichsOperator shift hshift) := by
  intro x y
  rcases A.shiftedFriedrichsOperator_exists_preimage shift hshift x with
    ⟨a, hRa, hTx⟩
  rcases A.shiftedFriedrichsOperator_exists_preimage shift hshift y with
    ⟨b, hRb, hTy⟩
  have hR := (A.friedrichsResolvent_isPositive shift hshift).isSymmetric a b
  calc
    inner ℝ (A.shiftedFriedrichsOperator shift hshift x) (y : H) =
        inner ℝ a (A.friedrichsResolvent shift hshift b) := by rw [hTx, hRb]
    _ = inner ℝ (A.friedrichsResolvent shift hshift a) b := hR.symm
    _ = inner ℝ (x : H) (A.shiftedFriedrichsOperator shift hshift y) := by rw [hRa, hTy]

/--
For a vector in the adjoint domain of the inverse, the resolvent applied to its adjoint value
recovers the original vector. This is the key maximality step in self-adjointness.
-/
theorem shiftedFriedrichsOperator_resolvent_adjoint
    (y : (A.shiftedFriedrichsOperator shift hshift).adjoint.domain) :
    A.friedrichsResolvent shift hshift
        ((A.shiftedFriedrichsOperator shift hshift).adjoint y) = (y : H) := by
  let T := A.shiftedFriedrichsOperator shift hshift
  let R := A.friedrichsResolvent shift hshift
  let w : H := T.adjoint y
  refine ext_inner_right ℝ fun z ↦ ?_
  have hzmem : R z ∈ T.domain := by
    rw [A.shiftedFriedrichsOperator_domain shift hshift]
    exact ⟨z, rfl⟩
  let rz : T.domain := ⟨R z, hzmem⟩
  have hTrz : T rz = z := by
    simpa [T, R, rz] using
      A.shiftedFriedrichsOperator_apply_resolvent shift hshift z hzmem
  have hformal := LinearPMap.adjoint_isFormalAdjoint
      (T := T) (hT := A.shiftedFriedrichsOperator_dense_domain shift hshift)
  calc
    inner ℝ (R w) z = inner ℝ w (R z) :=
      (A.friedrichsResolvent_isPositive shift hshift).isSymmetric w z
    _ = inner ℝ (T.adjoint y) (rz : H) := rfl
    _ = inner ℝ (y : H) (T rz) := hformal y rz
    _ = inner ℝ (y : H) z := by rw [hTrz]

/-- The adjoint domain of the shifted Friedrichs operator is contained in its inverse domain. -/
theorem shiftedFriedrichsOperator_adjoint_domain_le :
    (A.shiftedFriedrichsOperator shift hshift).adjoint.domain ≤
      (A.shiftedFriedrichsOperator shift hshift).domain := by
  let T := A.shiftedFriedrichsOperator shift hshift
  intro y hy
  let yy : T.adjoint.domain := ⟨y, hy⟩
  have hRy : A.friedrichsResolvent shift hshift (T.adjoint yy) = y := by
    simpa [T, yy] using
      A.shiftedFriedrichsOperator_resolvent_adjoint shift hshift yy
  rw [A.shiftedFriedrichsOperator_domain shift hshift]
  exact ⟨T.adjoint yy, hRy⟩

/-- The adjoint of the shifted Friedrichs operator is contained in the operator itself. -/
theorem shiftedFriedrichsOperator_adjoint_le :
    (A.shiftedFriedrichsOperator shift hshift).adjoint ≤
      A.shiftedFriedrichsOperator shift hshift := by
  let T := A.shiftedFriedrichsOperator shift hshift
  refine ⟨A.shiftedFriedrichsOperator_adjoint_domain_le shift hshift, ?_⟩
  intro x y hxy
  have hxmem : (x : H) ∈ T.domain :=
    A.shiftedFriedrichsOperator_adjoint_domain_le shift hshift x.prop
  let xT : T.domain := ⟨x, hxmem⟩
  rcases A.shiftedFriedrichsOperator_exists_preimage shift hshift xT with
    ⟨z, hRz, hTxT⟩
  have hR : A.friedrichsResolvent shift hshift (T.adjoint x) = (x : H) :=
    A.shiftedFriedrichsOperator_resolvent_adjoint shift hshift x
  have hz : z = T.adjoint x :=
    A.friedrichsResolvent_injective shift hshift (hRz.trans hR.symm)
  have hxT : T xT = T.adjoint x := by
    simpa [hz] using hTxT
  have hyx : y = xT := Subtype.ext hxy.symm
  rw [hyx, hxT]

/-- The shifted Friedrichs operator is self-adjoint. -/
theorem shiftedFriedrichsOperator_isSelfAdjoint :
    IsSelfAdjoint (A.shiftedFriedrichsOperator shift hshift) := by
  rw [LinearPMap.isSelfAdjoint_def]
  apply le_antisymm
  · exact A.shiftedFriedrichsOperator_adjoint_le shift hshift
  · exact LinearPMap.IsFormalAdjoint.le_adjoint
      (T := A.shiftedFriedrichsOperator shift hshift)
      (S := A.shiftedFriedrichsOperator shift hshift)
      (hT := A.shiftedFriedrichsOperator_dense_domain shift hshift)
      (A.shiftedFriedrichsOperator_symmetric shift hshift)

/-- Positivity of the shifted Friedrichs operator in quadratic-form form. -/
theorem shiftedFriedrichsOperator_inner_nonneg
    (x : (A.shiftedFriedrichsOperator shift hshift).domain) :
    0 ≤ inner ℝ (A.shiftedFriedrichsOperator shift hshift x) (x : H) := by
  rcases A.shiftedFriedrichsOperator_exists_preimage shift hshift x with
    ⟨z, hRz, hTx⟩
  rw [hTx, ← hRz]
  exact (A.friedrichsResolvent_isPositive shift hshift).inner_nonneg_right z

/-- The shifted inverse is positive and self-adjoint. -/
theorem shiftedFriedrichsOperator_isPositive :
    IsSelfAdjoint (A.shiftedFriedrichsOperator shift hshift) ∧
      ∀ x : (A.shiftedFriedrichsOperator shift hshift).domain,
        0 ≤ inner ℝ (A.shiftedFriedrichsOperator shift hshift x) (x : H) :=
  ⟨A.shiftedFriedrichsOperator_isSelfAdjoint shift hshift,
    A.shiftedFriedrichsOperator_inner_nonneg shift hshift⟩

/-- The unshifted Friedrichs extension obtained from `R_shift⁻¹ - shift`.

We express the scalar subtraction using the affine action of a full linear map on a `LinearPMap`.
This preserves the partial map domain by construction and avoids transporting subtype elements
between propositionally equal domain submodules. -/
@[reducible]
def friedrichsExtension : H →ₗ.[ℝ] H :=
  (-shift • (LinearMap.id : H →ₗ[ℝ] H)) +ᵥ
    A.shiftedFriedrichsOperator shift hshift

@[simp]
theorem friedrichsExtension_domain :
    (A.friedrichsExtension shift hshift).domain =
      (A.shiftedFriedrichsOperator shift hshift).domain := rfl

@[simp]
theorem friedrichsExtension_apply
    (x : (A.friedrichsExtension shift hshift).domain) :
    A.friedrichsExtension shift hshift x =
      A.shiftedFriedrichsOperator shift hshift x - shift • (x : H) := by
  change
    ((-shift • (LinearMap.id : H →ₗ[ℝ] H)) +ᵥ
        A.shiftedFriedrichsOperator shift hshift) x =
      A.shiftedFriedrichsOperator shift hshift x - shift • (x : H)
  rw [LinearPMap.vadd_apply]
  simp [sub_eq_add_neg, add_comm]

/-- The Friedrichs extension has the same dense domain as the shifted inverse. -/
theorem friedrichsExtension_dense_domain :
    Dense ((A.friedrichsExtension shift hshift).domain : Set H) := by
  rw [A.friedrichsExtension_domain shift hshift]
  exact A.shiftedFriedrichsOperator_dense_domain shift hshift

/-- Subtracting the real scalar shift preserves symmetry. -/
theorem friedrichsExtension_symmetric :
    (A.friedrichsExtension shift hshift).IsFormalAdjoint
      (A.friedrichsExtension shift hshift) := by
  intro x y
  rw [A.friedrichsExtension_apply shift hshift x,
    A.friedrichsExtension_apply shift hshift y,
    inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
    A.shiftedFriedrichsOperator_symmetric shift hshift x y]

/-- The adjoint domain of the unshifted Friedrichs extension is contained in its domain. -/
theorem friedrichsExtension_adjoint_domain_le :
    (A.friedrichsExtension shift hshift).adjoint.domain ≤
      (A.friedrichsExtension shift hshift).domain := by
  let S := A.friedrichsExtension shift hshift
  let T := A.shiftedFriedrichsOperator shift hshift
  have hSdense : Dense (S.domain : Set H) := by
    simpa [S] using A.friedrichsExtension_dense_domain shift hshift
  have hSformal := LinearPMap.adjoint_isFormalAdjoint (T := S) (hT := hSdense)
  have hTself : T.adjoint = T := by
    exact LinearPMap.isSelfAdjoint_def.mp
      (A.shiftedFriedrichsOperator_isSelfAdjoint shift hshift)
  intro y hy
  let yy : S.adjoint.domain := ⟨y, hy⟩
  let w : H := S.adjoint yy
  have hyTadj : (y : H) ∈ T.adjoint.domain := by
    apply LinearPMap.mem_adjoint_domain_of_exists
    refine ⟨w + shift • (y : H), ?_⟩
    intro x
    let xs : S.domain := x
    have hfa : inner ℝ w (x : H) = inner ℝ (y : H) (S xs) := by
      simpa [w, yy, xs] using hSformal yy xs
    have hSxs : S xs = T x - shift • (x : H) := by
      simpa [S, T, xs] using A.friedrichsExtension_apply shift hshift xs
    calc
      inner ℝ (w + shift • (y : H)) (x : H) =
          inner ℝ w (x : H) + shift * inner ℝ (y : H) (x : H) := by
            rw [inner_add_left, real_inner_smul_left]
      _ = inner ℝ (y : H) (S xs) + shift * inner ℝ (y : H) (x : H) := by
            rw [hfa]
      _ = inner ℝ (y : H)
          (T x - shift • (x : H)) + shift * inner ℝ (y : H) (x : H) := by
            rw [hSxs]
      _ = inner ℝ (y : H) (T x) := by
            rw [inner_sub_right, real_inner_smul_right]
            ring
  rw [hTself] at hyTadj
  simpa [S, T, friedrichsExtension] using hyTadj

/-- The adjoint of the Friedrichs extension is contained in the extension itself. -/
theorem friedrichsExtension_adjoint_le :
    (A.friedrichsExtension shift hshift).adjoint ≤
      A.friedrichsExtension shift hshift := by
  let S := A.friedrichsExtension shift hshift
  have hSdense : Dense (S.domain : Set H) := by
    simpa [S] using A.friedrichsExtension_dense_domain shift hshift
  refine ⟨A.friedrichsExtension_adjoint_domain_le shift hshift, ?_⟩
  intro x y hxy
  have hxmem : (x : H) ∈ S.domain :=
    A.friedrichsExtension_adjoint_domain_le shift hshift x.prop
  let xS : S.domain := ⟨x, hxmem⟩
  have hAdj : S.adjoint x = S xS := by
    apply LinearPMap.adjoint_apply_eq (T := S) (hT := hSdense) x
    intro v
    simpa [S, xS] using A.friedrichsExtension_symmetric shift hshift xS v
  have hyx : y = xS := Subtype.ext hxy.symm
  rw [hyx, hAdj]

/-- The unshifted Friedrichs extension is self-adjoint. -/
theorem friedrichsExtension_isSelfAdjoint :
    IsSelfAdjoint (A.friedrichsExtension shift hshift) := by
  rw [LinearPMap.isSelfAdjoint_def]
  apply le_antisymm
  · exact A.friedrichsExtension_adjoint_le shift hshift
  · exact LinearPMap.IsFormalAdjoint.le_adjoint
      (T := A.friedrichsExtension shift hshift)
      (S := A.friedrichsExtension shift hshift)
      (hT := A.friedrichsExtension_dense_domain shift hshift)
      (A.friedrichsExtension_symmetric shift hshift)

/-- The shifted inverse agrees with `(A + shift)` on the original operator domain. -/
theorem shiftedFriedrichsOperator_on_core
    (u : A.op.domain)
    (hu : (u : H) ∈ (A.shiftedFriedrichsOperator shift hshift).domain) :
    A.shiftedFriedrichsOperator shift hshift ⟨u, hu⟩ =
      A.shiftedOperatorValue shift u := by
  rcases A.shiftedFriedrichsOperator_exists_preimage shift hshift ⟨u, hu⟩ with
    ⟨z, hRz, hTz⟩
  have hRcore := A.friedrichsResolvent_shiftedOperatorValue shift hshift u
  have hz : z = A.shiftedOperatorValue shift u :=
    A.friedrichsResolvent_injective shift hshift (hRz.trans hRcore.symm)
  simpa [hz] using hTz

/-- The original symmetric operator is contained in its Friedrichs extension. -/
theorem op_le_friedrichsExtension :
    A.op ≤ A.friedrichsExtension shift hshift := by
  refine ⟨?_, ?_⟩
  · intro x hx
    rw [A.friedrichsExtension_domain shift hshift,
      A.shiftedFriedrichsOperator_domain shift hshift]
    let u : A.op.domain := ⟨x, hx⟩
    refine ⟨A.shiftedOperatorValue shift u, ?_⟩
    simpa [u] using A.friedrichsResolvent_shiftedOperatorValue shift hshift u
  · intro x y hxy
    let T := A.shiftedFriedrichsOperator shift hshift
    have hyT : (y : H) ∈ T.domain := by
      simpa [T, friedrichsExtension] using y.prop
    have hxT : (x : H) ∈ T.domain := by
      simpa [hxy] using hyT
    let xT : T.domain := ⟨(x : H), hxT⟩
    have hyxT : y = xT := Subtype.ext hxy.symm
    rw [hyxT]
    rw [A.friedrichsExtension_apply shift hshift xT]
    rw [A.shiftedFriedrichsOperator_on_core shift hshift x hxT]
    change
      (A.op x : H) =
        (A.op x : H) + shift • (x : H) - shift • (xT : H)
    have hxTcoe : (xT : H) = (x : H) := rfl
    rw [hxTcoe, add_sub_cancel_right]

end SemiboundedSymmetricOperator
end FriedrichsExtension
