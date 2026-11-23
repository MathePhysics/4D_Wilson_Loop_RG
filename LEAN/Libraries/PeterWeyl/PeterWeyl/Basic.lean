import Mathlib

/-!
# The Peter–Weyl theorem: shared definitions

This file fixes the definitions used by every later module of the library.

## Standing assumptions

The main theorems of the library are stated under the following assumptions.  `G` is a compact
Hausdorff topological group with its Borel σ-algebra, `μ` is a Haar probability measure on `G`,
and all scalars are complex.

```
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]
```

Each declaration below asks only for the assumptions it uses.  Two further properties of `μ` are
derived rather than assumed, and are instances: a Haar measure on a compact group is right
invariant (`isMulRightInvariant_of_compactSpace`) and invariant under inversion
(`isInvInvariant_of_compactSpace`).  Mathlib already provides regularity and inner regularity of
such a measure.  A Haar probability measure exists (`haarProbability`) and is unique
(`eq_haarProbability`).

Second countability of `G` is not needed.  The adjoint formula for convolution operators swaps
integrals of continuous functions on `G × G`, which mathlib allows without it
(`MeasureTheory.integral_integral_swap_of_hasCompactSupport`), and continuous functions are dense
in `L²` for any compact topological group (`ContinuousMap.toLp_denseRange`).  The Hausdorff
property is used only to separate points by representations.

## Main definitions

* `rightTranslate g : C(G, ℂ) ≃ₗᵢ[ℂ] C(G, ℂ)`, `(R_g f) x = f (x * g)`, as a monoid homomorphism
  in `g`; `continuous_rightTranslate_apply` is continuity in `g`.
* `rightTranslateL2 μ g : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ`, the same on `L²` for a right invariant
  measure; `continuous_rightTranslateL2_apply` is continuity in `g`, and
  `rightTranslateL2_toLp` is compatibility with `ContinuousMap.toLp`.
* `IsContinuousUnitary ρ`: a representation `ρ : Representation ℂ G V` on a complex inner product
  space is strongly continuous and unitary.
* `rightRegular μ : Representation ℂ G (Lp ℂ 2 μ)`, the right regular representation, which is
  continuous and unitary for a Haar measure on a compact group
  (`isContinuousUnitary_rightRegular`).
* `IsContinuousUnitary.coeff hρ v w : C(G, ℂ)`, the matrix coefficient `g ↦ ⟪w, ρ g v⟫`.
* `FDUnitaryRep G`: a bundled finite-dimensional continuous unitary representation with carrier in
  `Type`, and its matrix coefficients `FDUnitaryRep.coeff`.
* `matrixCoefficients G : Submodule ℂ C(G, ℂ)`, the span of all matrix coefficients of
  finite-dimensional continuous unitary representations.
* `transportRep e ρ` and `conjRep ρ`: transport along a linear isometry equivalence, and the
  complex conjugate of a representation on `EuclideanSpace ℂ ι`.
* `adjointKernel φ`, `φ* g = conj (φ g⁻¹)`, the kernel of the adjoint of convolution by `φ`.
* `convolutionFun μ φ f x = ∫ φ (x * y⁻¹) * f y ∂μ(y)`, the pointwise convolution formula, and
  `kernelRow φ x = conj (φ (x * ·⁻¹))`, the kernel row at `x`.

## Main statements

* `IsContinuousUnitary.coeff_mem_matrixCoefficients`: a matrix coefficient of a
  finite-dimensional continuous unitary representation on a space in any universe lies in
  `matrixCoefficients G`.  This is the entry point for eigenspaces of convolution operators,
  which live in the universe of `G`.
* `IsContinuousUnitary.subrepresentation`: restriction to a subrepresentation, for instance of
  `rightRegular μ` to an invariant eigenspace, preserves continuity and unitarity.
* `const_mem_matrixCoefficients`, `rightTranslate_mem_matrixCoefficients`,
  `star_mem_matrixCoefficients`: closure under constants, right translation and complex
  conjugation.
* `integrable_convolutionFun_integrand` and `convolutionFun_congr_ae`: the convolution integral is
  taken of an integrable function when `f ∈ L²`, and depends only on the class of `f`.
* `convolutionFun_eq_inner`: `(φ ⋆ f) x = ⟪kernelRow φ x, f⟫` in `L²`; with
  `continuous_kernelRow` this gives linearity, continuity and the supremum bound of convolution
  operators without further integration theory.

## Conventions

Matrix coefficients are `g ↦ ⟪w, ρ g v⟫`, linear in `v` and conjugate linear in `w`.  Convolution
is `(φ ⋆ f) x = ∫ φ (x * y⁻¹) f y dμ(y)`; it commutes with right translations, and its adjoint is
convolution by `adjointKernel φ`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal ComplexConjugate

namespace PeterWeyl

/-! ### Haar measure on a compact group -/

section Haar

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G]

/-- A Haar measure on a compact group is right invariant: right translation multiplies it by the
modular character, and it preserves the finite nonzero total mass. -/
instance (priority := 100) isMulRightInvariant_of_compactSpace (μ : Measure G)
    [μ.IsHaarMeasure] : μ.IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  have hmap := Measure.map_right_mul_eq_modularCharacterFun_smul μ g
  have huniv := congrArg (fun ν : Measure G => ν Set.univ) hmap
  simp only [Measure.map_apply (measurable_mul_const g) MeasurableSet.univ, Set.preimage_univ,
    Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at huniv
  have hne : μ Set.univ ≠ 0 := isOpen_univ.measure_ne_zero μ Set.univ_nonempty
  have hone : (Measure.modularCharacterFun g : ℝ≥0∞) = 1 := by
    rw [← ENNReal.mul_left_inj hne (measure_ne_top μ Set.univ), one_mul]
    exact huniv.symm
  rw [hmap, ENNReal.coe_eq_one.1 hone, one_smul]

/-- A Haar measure on a compact group is invariant under inversion: its image is a Haar measure
of the same total mass. -/
instance (priority := 100) isInvInvariant_of_compactSpace (μ : Measure G) [μ.IsHaarMeasure] :
    μ.IsInvInvariant := by
  refine ⟨?_⟩
  have h := Measure.isMulInvariant_eq_smul_of_compactSpace μ.inv μ
  have huniv : μ.inv Set.univ = μ Set.univ := by rw [Measure.inv_apply, Set.inv_univ]
  rw [h, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at huniv
  have hne : μ Set.univ ≠ 0 := isOpen_univ.measure_ne_zero μ Set.univ_nonempty
  have hone : ((μ.inv.haarScalarFactor μ : NNReal) : ℝ≥0∞) = 1 := by
    rw [← ENNReal.mul_left_inj hne (measure_ne_top μ Set.univ), one_mul]
    exact huniv
  rw [h, ENNReal.coe_eq_one.1 hone, one_smul]

variable (G) in
/-- The Haar probability measure of a compact group. -/
def haarProbability : Measure G :=
  Measure.haarMeasure ⊤

instance : (haarProbability G).IsHaarMeasure :=
  Measure.isHaarMeasure_haarMeasure _

instance : IsProbabilityMeasure (haarProbability G) := by
  refine ⟨?_⟩
  simpa [haarProbability] using
    Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts G))

/-- A Haar probability measure on a compact group is `haarProbability G`. -/
theorem eq_haarProbability (μ : Measure G) [μ.IsHaarMeasure] [IsProbabilityMeasure μ] :
    μ = haarProbability G :=
  Measure.isHaarMeasure_eq_of_isProbabilityMeasure μ _

end Haar

/-! ### Right translation on continuous functions -/

section RightTranslation

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]

/-- Right translation preserves the supremum norm. -/
theorem norm_comp_mulRight (f : C(G, ℂ)) (g : G) :
    ‖f.comp (ContinuousMap.mulRight g)‖ = ‖f‖ := by
  refine le_antisymm ((ContinuousMap.norm_le _ (norm_nonneg f)).2 fun x => f.norm_coe_le_norm _)
    ((ContinuousMap.norm_le _ (norm_nonneg _)).2 fun x => ?_)
  simpa using (f.comp (ContinuousMap.mulRight g)).norm_coe_le_norm (x * g⁻¹)

/-- Right translation `(R_g f) x = f (x * g)` on continuous functions, as a monoid homomorphism
into linear isometry equivalences: `R_(g * h) = R_g ∘ R_h`. -/
def rightTranslate : G →* (C(G, ℂ) ≃ₗᵢ[ℂ] C(G, ℂ)) where
  toFun g :=
    { toFun := fun f => f.comp (ContinuousMap.mulRight g)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := fun f => f.comp (ContinuousMap.mulRight g⁻¹)
      left_inv := fun f => by ext x; simp
      right_inv := fun f => by ext x; simp
      norm_map' := fun f => norm_comp_mulRight f g }
  map_one' := by ext f x; simp
  map_mul' g h := by ext f x; simp [mul_assoc]

@[simp]
theorem rightTranslate_apply (g : G) (f : C(G, ℂ)) (x : G) :
    rightTranslate g f x = f (x * g) :=
  rfl

/-- Right translates of a continuous function depend continuously on the translation. -/
theorem continuous_rightTranslate_apply (f : C(G, ℂ)) :
    Continuous fun g : G => rightTranslate g f :=
  (ContinuousMap.mk (fun p : G × G => f (p.2 * p.1)) (by fun_prop)).curry.continuous

end RightTranslation

/-! ### Right translation on `L²` -/

section RightTranslationL2

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G)

section Invariant

variable [μ.IsMulRightInvariant]

/-- Right translation on `L²`, before bundling. -/
private def rightTranslateL2Aux (g : G) : Lp ℂ 2 μ →ₗᵢ[ℂ] Lp ℂ 2 μ :=
  Lp.compMeasurePreservingₗᵢ ℂ (· * g) (measurePreserving_mul_right μ g)

private theorem rightTranslateL2Aux_ae (g : G) (f : Lp ℂ 2 μ) :
    rightTranslateL2Aux μ g f =ᵐ[μ] fun x => f (x * g) :=
  Lp.coeFn_compMeasurePreserving _ _

private theorem rightTranslateL2Aux_mul (g h : G) (f : Lp ℂ 2 μ) :
    rightTranslateL2Aux μ (g * h) f = rightTranslateL2Aux μ g (rightTranslateL2Aux μ h f) := by
  refine Lp.ext ?_
  have h3 := (measurePreserving_mul_right μ g).quasiMeasurePreserving.ae_eq_comp
    (rightTranslateL2Aux_ae μ h f)
  filter_upwards [rightTranslateL2Aux_ae μ (g * h) f,
    rightTranslateL2Aux_ae μ g (rightTranslateL2Aux μ h f), h3] with x hx1 hx2 hx3
  simp only [Function.comp_apply] at hx3
  rw [hx1, hx2, hx3, mul_assoc]

private theorem rightTranslateL2Aux_one (f : Lp ℂ 2 μ) : rightTranslateL2Aux μ 1 f = f := by
  refine Lp.ext ?_
  filter_upwards [rightTranslateL2Aux_ae μ 1 f] with x hx
  rw [hx, mul_one]

/-- Right translation `(R_g f) x = f (x * g)` on `L²(G, μ)` for a right invariant measure, as a
monoid homomorphism into linear isometry equivalences: `R_(g * h) = R_g ∘ R_h`. -/
def rightTranslateL2 : G →* (Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ) where
  toFun g :=
    { rightTranslateL2Aux μ g with
      invFun := rightTranslateL2Aux μ g⁻¹
      left_inv := fun f => by
        simp [← rightTranslateL2Aux_mul, rightTranslateL2Aux_one]
      right_inv := fun f => by
        simp [← rightTranslateL2Aux_mul, rightTranslateL2Aux_one] }
  map_one' := by ext1 f; exact rightTranslateL2Aux_one μ f
  map_mul' g h := by ext1 f; exact rightTranslateL2Aux_mul μ g h f

/-- The translate `R_g f` is represented by `x ↦ f (x * g)`. -/
theorem coeFn_rightTranslateL2 (g : G) (f : Lp ℂ 2 μ) :
    rightTranslateL2 μ g f =ᵐ[μ] fun x => f (x * g) :=
  rightTranslateL2Aux_ae μ g f

/-- Right translation commutes with the inclusion of continuous functions into `L²`. -/
theorem rightTranslateL2_toLp [CompactSpace G] [IsFiniteMeasure μ] (g : G) (f : C(G, ℂ)) :
    rightTranslateL2 μ g (ContinuousMap.toLp 2 μ ℂ f) =
      ContinuousMap.toLp 2 μ ℂ (rightTranslate g f) := by
  refine Lp.ext ?_
  have h := (measurePreserving_mul_right μ g).quasiMeasurePreserving.ae_eq_comp
    (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) μ f)
  filter_upwards [coeFn_rightTranslateL2 μ g (ContinuousMap.toLp 2 μ ℂ f), h,
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) μ (rightTranslate g f)] with x hx1 hx2 hx3
  simp only [Function.comp_apply] at hx2
  rw [hx1, hx2, hx3, rightTranslate_apply]

end Invariant

/-- For a Haar measure on a compact group, right translates of an `L²` function depend
continuously on the translation. -/
theorem continuous_rightTranslateL2_apply [CompactSpace G] [μ.IsHaarMeasure] (f : Lp ℂ 2 μ) :
    Continuous fun g : G => rightTranslateL2 μ g f :=
  Continuous.compMeasurePreservingLp (g := fun g : G => ContinuousMap.mulRight g)
    continuous_const
    (ContinuousMap.mk (fun p : G × G => p.2 * p.1) (by fun_prop)).curry.continuous
    (fun g => measurePreserving_mul_right μ g) ENNReal.ofNat_ne_top

end RightTranslationL2

/-! ### Transport and conjugation of representations -/

section Algebraic

variable {G : Type*} [Group G]

/-- Transport of a representation along a linear isometry equivalence of the carriers. -/
def transportRep {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] (e : V ≃ₗᵢ[ℂ] W) (ρ : Representation ℂ G V) :
    Representation ℂ G W where
  toFun g := e.toLinearEquiv.toLinearMap ∘ₗ ρ g ∘ₗ e.symm.toLinearEquiv.toLinearMap
  map_one' := by ext x; simp
  map_mul' g h := by ext x; simp

@[simp]
theorem transportRep_apply {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] (e : V ≃ₗᵢ[ℂ] W) (ρ : Representation ℂ G V)
    (g : G) (x : W) : transportRep e ρ g x = e (ρ g (e.symm x)) :=
  rfl

variable {ι : Type*} [Fintype ι]

/-- Coordinatewise complex conjugation on `EuclideanSpace ℂ ι`, a conjugate linear isometric
involution. -/
def euclideanConj (x : EuclideanSpace ℂ ι) : EuclideanSpace ℂ ι :=
  WithLp.toLp 2 (star (WithLp.ofLp x))

omit [Fintype ι] in
@[simp]
theorem euclideanConj_euclideanConj (x : EuclideanSpace ℂ ι) :
    euclideanConj (euclideanConj x) = x := by
  simp [euclideanConj]

omit [Fintype ι] in
@[simp]
theorem euclideanConj_add (x y : EuclideanSpace ℂ ι) :
    euclideanConj (x + y) = euclideanConj x + euclideanConj y := by
  simp [euclideanConj]

@[simp]
theorem euclideanConj_smul (c : ℂ) (x : EuclideanSpace ℂ ι) :
    euclideanConj (c • x) = conj c • euclideanConj x := by
  simp [euclideanConj]

theorem inner_euclideanConj (x y : EuclideanSpace ℂ ι) :
    ⟪euclideanConj x, euclideanConj y⟫_ℂ = ⟪y, x⟫_ℂ := by
  simp [euclideanConj, EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]

omit [Fintype ι] in
theorem continuous_euclideanConj : Continuous (euclideanConj (ι := ι)) := by
  unfold euclideanConj
  fun_prop

/-- The complex conjugate `g ↦ J ∘ ρ g ∘ J` of a representation on `EuclideanSpace ℂ ι`, where `J`
is coordinatewise conjugation. -/
def conjRep (ρ : Representation ℂ G (EuclideanSpace ℂ ι)) :
    Representation ℂ G (EuclideanSpace ℂ ι) where
  toFun g :=
    { toFun := fun x => euclideanConj (ρ g (euclideanConj x))
      map_add' := fun x y => by simp
      map_smul' := fun c x => by simp }
  map_one' := by ext1 x; simp
  map_mul' g h := by ext1 x; simp

@[simp]
theorem conjRep_apply (ρ : Representation ℂ G (EuclideanSpace ℂ ι)) (g : G)
    (x : EuclideanSpace ℂ ι) : conjRep ρ g x = euclideanConj (ρ g (euclideanConj x)) :=
  rfl

end Algebraic

/-! ### Finite-dimensional continuous unitary representations -/

section Representation

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- A representation `ρ` of `G` on a complex inner product space is continuous and unitary if
every orbit map `g ↦ ρ g v` is continuous and every `ρ g` preserves inner products.  In finite
dimension the first condition is equivalent to continuity of `g ↦ ρ g` in operator norm. -/
structure IsContinuousUnitary {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (ρ : Representation ℂ G V) : Prop where
  /-- Every orbit map is continuous. -/
  continuous_apply : ∀ v : V, Continuous fun g => ρ g v
  /-- Every `ρ g` preserves inner products. -/
  inner_map_map : ∀ (g : G) (v w : V), ⟪ρ g v, ρ g w⟫_ℂ = ⟪v, w⟫_ℂ

namespace IsContinuousUnitary

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] {ρ : Representation ℂ G V}

/-- Every `ρ g` is an isometry. -/
theorem norm_map (hρ : IsContinuousUnitary ρ) (g : G) (v : V) : ‖ρ g v‖ = ‖v‖ := by
  rw [@norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ, hρ.inner_map_map]

/-- The adjoint of `ρ g` is `ρ g⁻¹`. -/
theorem inner_map_left (hρ : IsContinuousUnitary ρ) (g : G) (v w : V) :
    ⟪ρ g v, w⟫_ℂ = ⟪v, ρ g⁻¹ w⟫_ℂ := by
  conv_lhs => rw [← Representation.self_inv_apply ρ g w]
  exact hρ.inner_map_map g v (ρ g⁻¹ w)

/-- The matrix coefficient `g ↦ ⟪w, ρ g v⟫` of a continuous unitary representation. -/
def coeff (hρ : IsContinuousUnitary ρ) (v w : V) : C(G, ℂ) :=
  ⟨fun g => ⟪w, ρ g v⟫_ℂ, continuous_const.inner (hρ.continuous_apply v)⟩

@[simp]
theorem coeff_apply (hρ : IsContinuousUnitary ρ) (v w : V) (g : G) :
    hρ.coeff v w g = ⟪w, ρ g v⟫_ℂ :=
  rfl

/-- The restriction to a subrepresentation of a continuous unitary representation is continuous
and unitary. -/
theorem subrepresentation (hρ : IsContinuousUnitary ρ) (σ : Subrepresentation ρ) :
    IsContinuousUnitary σ.toRepresentation where
  continuous_apply v := continuous_induced_rng.2 (hρ.continuous_apply (v : V))
  inner_map_map g v w := hρ.inner_map_map g v w

/-- Transport along a linear isometry equivalence preserves continuity and unitarity. -/
theorem transportRep (hρ : IsContinuousUnitary ρ) (e : V ≃ₗᵢ[ℂ] W) :
    IsContinuousUnitary (transportRep e ρ) where
  continuous_apply x := e.continuous.comp (hρ.continuous_apply (e.symm x))
  inner_map_map g x y := by simp [hρ.inner_map_map]

/-- Transport along a linear isometry equivalence does not change matrix coefficients. -/
theorem coeff_transportRep (hρ : IsContinuousUnitary ρ) (e : V ≃ₗᵢ[ℂ] W) (v w : V) :
    (hρ.transportRep e).coeff (e v) (e w) = hρ.coeff v w := by
  ext g
  simp

variable {ι : Type*} [Fintype ι] {σ : Representation ℂ G (EuclideanSpace ℂ ι)}

/-- The complex conjugate of a continuous unitary representation is continuous and unitary. -/
theorem conjRep (hσ : IsContinuousUnitary σ) : IsContinuousUnitary (conjRep σ) where
  continuous_apply x := continuous_euclideanConj.comp (hσ.continuous_apply (euclideanConj x))
  inner_map_map g x y := by simp [inner_euclideanConj, hσ.inner_map_map]

/-- The matrix coefficients of the conjugate representation are the complex conjugates of the
matrix coefficients. -/
theorem coeff_conjRep (hσ : IsContinuousUnitary σ) (v w : EuclideanSpace ℂ ι) :
    hσ.conjRep.coeff (euclideanConj v) (euclideanConj w) = star (hσ.coeff v w) := by
  ext g
  simp [inner_euclideanConj]

end IsContinuousUnitary

/-- A finite-dimensional continuous unitary representation of `G`, with carrier in `Type`.  Every
finite-dimensional continuous unitary representation, with carrier in any universe, is unitarily
equivalent to one of these (see `IsContinuousUnitary.coeff_mem_matrixCoefficients`). -/
structure FDUnitaryRep (G : Type*) [Group G] [TopologicalSpace G] where
  /-- The representation space. -/
  V : Type
  [instNormedAddCommGroup : NormedAddCommGroup V]
  [instInnerProductSpace : InnerProductSpace ℂ V]
  [instFiniteDimensional : FiniteDimensional ℂ V]
  /-- The action of `G` by linear maps. -/
  ρ : Representation ℂ G V
  /-- The action is continuous and unitary. -/
  isContinuousUnitary : IsContinuousUnitary ρ

attribute [instance] FDUnitaryRep.instNormedAddCommGroup FDUnitaryRep.instInnerProductSpace
  FDUnitaryRep.instFiniteDimensional

namespace FDUnitaryRep

/-- The matrix coefficient `g ↦ ⟪w, π.ρ g v⟫` of a finite-dimensional continuous unitary
representation. -/
def coeff (π : FDUnitaryRep G) (v w : π.V) : C(G, ℂ) :=
  π.isContinuousUnitary.coeff v w

@[simp]
theorem coeff_apply (π : FDUnitaryRep G) (v w : π.V) (g : G) :
    π.coeff v w g = ⟪w, π.ρ g v⟫_ℂ :=
  rfl

end FDUnitaryRep

variable (G) in
/-- The space of matrix coefficients: the complex span of all matrix coefficients of
finite-dimensional continuous unitary representations of `G`.  The Peter–Weyl theorem states that
it is dense in `C(G, ℂ)` for the supremum norm. -/
def matrixCoefficients : Submodule ℂ C(G, ℂ) :=
  Submodule.span ℂ {f | ∃ (π : FDUnitaryRep G) (v w : π.V), π.coeff v w = f}

theorem FDUnitaryRep.coeff_mem_matrixCoefficients (π : FDUnitaryRep G) (v w : π.V) :
    π.coeff v w ∈ matrixCoefficients G :=
  Submodule.subset_span ⟨π, v, w, rfl⟩

/-- A matrix coefficient of a finite-dimensional continuous unitary representation, with carrier
in any universe, lies in `matrixCoefficients G`. -/
theorem IsContinuousUnitary.coeff_mem_matrixCoefficients {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] {ρ : Representation ℂ G V}
    (hρ : IsContinuousUnitary ρ) (v w : V) : hρ.coeff v w ∈ matrixCoefficients G := by
  let e := (stdOrthonormalBasis ℂ V).repr
  let π : FDUnitaryRep G :=
    { V := EuclideanSpace ℂ (Fin (Module.finrank ℂ V))
      ρ := PeterWeyl.transportRep e ρ
      isContinuousUnitary := hρ.transportRep e }
  rw [← hρ.coeff_transportRep e]
  exact π.coeff_mem_matrixCoefficients (e v) (e w)

/-- The trivial representation on `ℂ` is continuous and unitary. -/
theorem isContinuousUnitary_trivial : IsContinuousUnitary (Representation.trivial ℂ G ℂ) where
  continuous_apply v := by simpa using continuous_const
  inner_map_map g v w := by simp

/-- Constant functions are matrix coefficients of the trivial representation. -/
theorem const_mem_matrixCoefficients (c : ℂ) :
    ContinuousMap.const G c ∈ matrixCoefficients G := by
  have h := isContinuousUnitary_trivial.coeff_mem_matrixCoefficients (G := G) c 1
  convert h using 1
  ext g
  simp

theorem one_mem_matrixCoefficients : (1 : C(G, ℂ)) ∈ matrixCoefficients G :=
  const_mem_matrixCoefficients 1

/-- Matrix coefficients are closed under complex conjugation: the conjugate of a matrix
coefficient is a matrix coefficient of the conjugate representation. -/
theorem star_mem_matrixCoefficients {f : C(G, ℂ)} (hf : f ∈ matrixCoefficients G) :
    star f ∈ matrixCoefficients G := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨π, v, w, rfl⟩ := hf
    let e := (stdOrthonormalBasis ℂ π.V).repr
    have hσ := π.isContinuousUnitary.transportRep e
    show star (π.isContinuousUnitary.coeff v w) ∈ matrixCoefficients G
    rw [← π.isContinuousUnitary.coeff_transportRep e, ← hσ.coeff_conjRep]
    exact hσ.conjRep.coeff_mem_matrixCoefficients _ _
  | zero => simp
  | add f₁ f₂ _ _ h₁ h₂ => simpa using add_mem h₁ h₂
  | smul c f _ h => simpa using Submodule.smul_mem _ (conj c) h

/-- Matrix coefficients are closed under right translation:
`f (x * g) = ⟪w, ρ x (ρ g v)⟫` for `f x = ⟪w, ρ x v⟫`. -/
theorem rightTranslate_mem_matrixCoefficients [IsTopologicalGroup G] [CompactSpace G]
    {f : C(G, ℂ)} (hf : f ∈ matrixCoefficients G) (g : G) :
    rightTranslate g f ∈ matrixCoefficients G := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨π, v, w, rfl⟩ := hf
    convert π.coeff_mem_matrixCoefficients (π.ρ g v) w using 1
    ext x
    simp [map_mul, Module.End.mul_apply]
  | zero => simp
  | add f₁ f₂ _ _ h₁ h₂ => simpa using add_mem h₁ h₂
  | smul c f _ h => simpa using Submodule.smul_mem _ c h

end Representation

/-! ### The right regular representation -/

section RightRegular

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G)

/-- The right regular representation of `G` on `L²(G, μ)`, `g ↦ R_g`, for a right invariant
measure. -/
def rightRegular [μ.IsMulRightInvariant] : Representation ℂ G (Lp ℂ 2 μ) where
  toFun g := (rightTranslateL2 μ g).toLinearEquiv.toLinearMap
  map_one' := by ext1 f; simp
  map_mul' g h := by ext1 f; simp

@[simp]
theorem rightRegular_apply [μ.IsMulRightInvariant] (g : G) (f : Lp ℂ 2 μ) :
    rightRegular μ g f = rightTranslateL2 μ g f :=
  rfl

/-- For a Haar measure on a compact group, the right regular representation is continuous and
unitary. -/
theorem isContinuousUnitary_rightRegular [CompactSpace G] [μ.IsHaarMeasure] :
    IsContinuousUnitary (rightRegular μ) where
  continuous_apply f := continuous_rightTranslateL2_apply μ f
  inner_map_map g f f' := (rightTranslateL2 μ g).inner_map_map f f'

end RightRegular

/-! ### Convolution with a continuous kernel -/

section AdjointKernel

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The kernel of the adjoint of convolution by `φ`: `φ* g = conj (φ g⁻¹)`.  Convolution by `φ` is
self-adjoint on `L²` when `adjointKernel φ = φ`. -/
def adjointKernel (φ : C(G, ℂ)) : C(G, ℂ) :=
  ⟨fun g => conj (φ g⁻¹), Complex.continuous_conj.comp (φ.continuous.comp continuous_inv)⟩

@[simp]
theorem adjointKernel_apply (φ : C(G, ℂ)) (g : G) : adjointKernel φ g = conj (φ g⁻¹) :=
  rfl

@[simp]
theorem adjointKernel_adjointKernel (φ : C(G, ℂ)) : adjointKernel (adjointKernel φ) = φ := by
  ext g
  simp

/-- The row `y ↦ conj (φ (x * y⁻¹))` of the convolution kernel, so that
`(φ ⋆ f) x = ⟪kernelRow φ x, f⟫` in `L²` (`convolutionFun_eq_inner`). -/
def kernelRow (φ : C(G, ℂ)) (x : G) : C(G, ℂ) :=
  ⟨fun y => conj (φ (x * y⁻¹)),
    Complex.continuous_conj.comp (φ.continuous.comp (continuous_const.mul continuous_inv))⟩

@[simp]
theorem kernelRow_apply (φ : C(G, ℂ)) (x y : G) : kernelRow φ x y = conj (φ (x * y⁻¹)) :=
  rfl

/-- The kernel rows depend continuously on the row index, for the compact-open topology, which is
the topology of the supremum norm on a compact group. -/
theorem continuous_kernelRow (φ : C(G, ℂ)) : Continuous (kernelRow φ) :=
  (ContinuousMap.mk (fun p : G × G => conj (φ (p.1 * p.2⁻¹)))
    (Complex.continuous_conj.comp
      (φ.continuous.comp (continuous_fst.mul continuous_snd.inv)))).curry.continuous

end AdjointKernel

section Convolution

variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]

/-- The convolution `(φ ⋆ f) x = ∫ φ (x * y⁻¹) * f y ∂μ(y)` of a continuous kernel `φ` with a
function `f`.  For `f` in `L²` the integrand is integrable
(`integrable_convolutionFun_integrand`), and the value depends only on the almost everywhere
class of `f` (`convolutionFun_congr_ae`). -/
def convolutionFun (μ : Measure G) (φ : C(G, ℂ)) (f : G → ℂ) (x : G) : ℂ :=
  ∫ y, φ (x * y⁻¹) * f y ∂μ -- totalisation-audit: allow integrable for f ∈ L², see integrable_convolutionFun_integrand

variable {μ : Measure G}

theorem convolutionFun_congr_ae (φ : C(G, ℂ)) {f f' : G → ℂ} (h : f =ᵐ[μ] f') :
    convolutionFun μ φ f = convolutionFun μ φ f' := by
  funext x
  exact integral_congr_ae (h.mono fun y hy => by simp [hy])

/-- On a compact group with a finite measure, the convolution integrand of a continuous kernel and
an `L²` function is integrable. -/
theorem integrable_convolutionFun_integrand [IsTopologicalGroup G] [BorelSpace G] [CompactSpace G]
    [IsFiniteMeasure μ] (φ : C(G, ℂ)) {f : G → ℂ} (hf : MemLp f 2 μ) (x : G) :
    Integrable (fun y => φ (x * y⁻¹) * f y) μ :=
  (hf.integrable one_le_two).bdd_mul
    ((φ.continuous.comp (continuous_const.mul continuous_inv)).aestronglyMeasurable)
    (ae_of_all _ fun y => φ.norm_coe_le_norm (x * y⁻¹))

/-- For `f ∈ L²`, the convolution at `x` is the `L²` inner product of the kernel row at `x` with
`f`.  Linearity, continuity and the supremum bound of convolution operators follow from this
identity and `continuous_kernelRow`. -/
theorem convolutionFun_eq_inner [IsTopologicalGroup G] [BorelSpace G] [CompactSpace G]
    [IsFiniteMeasure μ] (φ : C(G, ℂ)) (f : Lp ℂ 2 μ) (x : G) :
    convolutionFun μ φ f x = ⟪ContinuousMap.toLp 2 μ ℂ (kernelRow φ x), f⟫_ℂ := by
  rw [convolutionFun, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) μ (kernelRow φ x)] with y hy
  rw [hy, RCLike.inner_apply, kernelRow_apply, Complex.conj_conj, mul_comm]

end Convolution

end PeterWeyl
