import PeterWeyl.Basic

/-!
# Invariant eigenspaces and matrix coefficients

Let `T` be a bounded operator on `L²(G, μ)` that commutes with right translations.  Its
eigenspaces are then invariant under the right regular representation.  If `T` is compact, its
eigenspaces for nonzero eigenvalues are finite-dimensional, so the right regular representation
restricted to such an eigenspace is a finite-dimensional continuous unitary representation.

If moreover `T` factors through continuous functions, `T = toLp ∘ S` with
`S : Lp ℂ 2 μ →L[ℂ] C(G, ℂ)`, then every eigenvector `f` for an eigenvalue `c ≠ 0` has the
continuous representative `c⁻¹ • S f`, and this representative is a matrix coefficient of the
restricted representation: evaluation at `1` of `c⁻¹ • S` is a linear functional on the
finite-dimensional eigenspace, hence of the form `⟪w, ·⟫`, and right equivariance of `S` gives
`(c⁻¹ • S f) g = ⟪w, R_g f⟫`.

The statements are abstract in `T` and `S`.  They apply to the convolution operators of
`PeterWeyl.ConvolutionOperator`, which are compact, commute with right translations and factor
through continuous functions by construction.

## Main definitions

* `CommutesRight μ T`: `T` commutes with every right translation `rightTranslateL2 μ g`.
* `eigenSubrep μ hT c`: the eigenspace of `T` for `c`, as a subrepresentation of `rightRegular μ`.

## Main statements

* `finiteDimensional_eigenSubrep`: for compact `T` and `c ≠ 0` the eigenspace is
  finite-dimensional.
* `isContinuousUnitary_eigenSubrep`: the restricted representation is continuous and unitary.
* `CommutesRight.factor_rightTranslateL2`: a factor `S` through continuous functions commutes with
  right translations.
* `toLp_inv_smul_factor`: `c⁻¹ • S f` is a continuous representative of an eigenvector `f`.
* `inv_smul_factor_mem_matrixCoefficients`: this representative is a matrix coefficient.
* `exists_mem_matrixCoefficients_toLp_eq`, `eigenspace_le_map_matrixCoefficients`: every
  eigenvector for a nonzero eigenvalue is the class of a matrix coefficient.
* `factor_mem_matrixCoefficients`, `iSup_eigenspace_le_comap_factor`: `S` maps every eigenvector,
  and hence the span of all eigenspaces, into `matrixCoefficients G`.

No self-adjointness is assumed.
-/

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace PeterWeyl

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G)

/-! ### Eigenspaces of operators commuting with right translations -/

section Eigenspace

variable [μ.IsMulRightInvariant]

/-- The operator `T` on `L²(G, μ)` commutes with every right translation. -/
def CommutesRight (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) : Prop :=
  ∀ (g : G) (f : Lp ℂ 2 μ), T (rightTranslateL2 μ g f) = rightTranslateL2 μ g (T f)

variable {μ} {T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ}

/-- The eigenspaces of an operator commuting with right translations are invariant under right
translations. -/
theorem CommutesRight.rightTranslateL2_mem_eigenspace (hT : CommutesRight μ T) (c : ℂ) (g : G)
    {f : Lp ℂ 2 μ} (hf : f ∈ Module.End.eigenspace (T : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ) c) :
    rightTranslateL2 μ g f ∈ Module.End.eigenspace (T : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ) c := by
  rw [Module.End.mem_eigenspace_iff] at hf ⊢
  rw [ContinuousLinearMap.coe_coe] at hf ⊢
  rw [hT, hf, map_smul]

variable (μ) in
/-- The eigenspace of an operator commuting with right translations, as a subrepresentation of the
right regular representation. -/
def eigenSubrep (hT : CommutesRight μ T) (c : ℂ) : Subrepresentation (rightRegular μ) where
  toSubmodule := Module.End.eigenspace (T : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ) c
  apply_mem_toSubmodule g _ hf := hT.rightTranslateL2_mem_eigenspace c g hf

@[simp]
theorem eigenSubrep_toSubmodule (hT : CommutesRight μ T) (c : ℂ) :
    (eigenSubrep μ hT c).toSubmodule = Module.End.eigenspace (T : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ) c :=
  rfl

@[simp]
theorem coe_eigenSubrep_toRepresentation_apply (hT : CommutesRight μ T) (c : ℂ) (g : G)
    (f : (eigenSubrep μ hT c).toSubmodule) :
    ((eigenSubrep μ hT c).toRepresentation g f : Lp ℂ 2 μ) = rightTranslateL2 μ g f :=
  rfl

/-- For a compact operator commuting with right translations, the eigenspace of a nonzero
eigenvalue is finite-dimensional. -/
theorem finiteDimensional_eigenSubrep (hT : CommutesRight μ T) (hK : IsCompactOperator T)
    {c : ℂ} (hc : c ≠ 0) : FiniteDimensional ℂ (eigenSubrep μ hT c).toSubmodule :=
  ContinuousLinearMap.finite_dimensional_eigenspace hK c hc

end Eigenspace

/-! ### Matrix coefficients -/

section MatrixCoefficients

variable [CompactSpace G] [μ.IsHaarMeasure] {μ} {T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ}

/-- For a Haar measure on a compact group, the right regular representation restricted to an
invariant eigenspace is continuous and unitary. -/
theorem isContinuousUnitary_eigenSubrep (hT : CommutesRight μ T) (c : ℂ) :
    IsContinuousUnitary (eigenSubrep μ hT c).toRepresentation :=
  (isContinuousUnitary_rightRegular μ).subrepresentation _

/-- For a compact operator commuting with right translations and `c ≠ 0`, every matrix coefficient
of the right regular representation restricted to the eigenspace of `c` lies in
`matrixCoefficients G`. -/
theorem coeff_eigenSubrep_mem_matrixCoefficients (hT : CommutesRight μ T)
    (hK : IsCompactOperator T) {c : ℂ} (hc : c ≠ 0) (v w : (eigenSubrep μ hT c).toSubmodule) :
    (isContinuousUnitary_eigenSubrep hT c).coeff v w ∈ matrixCoefficients G :=
  haveI := finiteDimensional_eigenSubrep hT hK hc
  IsContinuousUnitary.coeff_mem_matrixCoefficients _ v w

variable {S : Lp ℂ 2 μ →L[ℂ] C(G, ℂ)}

/-- If `T = toLp ∘ S` commutes with right translations, then so does `S`, now acting on continuous
functions. -/
theorem CommutesRight.factor_rightTranslateL2 (hT : CommutesRight μ T)
    (hTS : T = (ContinuousMap.toLp 2 μ ℂ).comp S) (g : G) (f : Lp ℂ 2 μ) :
    S (rightTranslateL2 μ g f) = rightTranslate g (S f) := by
  refine ContinuousMap.toLp_injective (p := 2) (𝕜 := ℂ) μ ?_
  rw [← rightTranslateL2_toLp]
  have h := hT g f
  rw [hTS] at h
  exact h

omit [IsTopologicalGroup G] in
/-- If `T = toLp ∘ S`, then an eigenvector `f` of `T` for `c ≠ 0` is the class of the continuous
function `c⁻¹ • S f`. -/
theorem toLp_inv_smul_factor (hTS : T = (ContinuousMap.toLp 2 μ ℂ).comp S) {c : ℂ} (hc : c ≠ 0)
    {f : Lp ℂ 2 μ} (hf : f ∈ Module.End.eigenspace (T : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ) c) :
    ContinuousMap.toLp 2 μ ℂ (c⁻¹ • S f) = f := by -- totalisation-audit: allow c ≠ 0 by hc
  rw [Module.End.mem_eigenspace_iff, ContinuousLinearMap.coe_coe, hTS] at hf
  rw [map_smul, ← ContinuousLinearMap.comp_apply, hf, smul_smul, inv_mul_cancel₀ hc, one_smul]

/-- Let `T = toLp ∘ S` be compact and commute with right translations.  For an eigenvector `f` of
`T` with eigenvalue `c ≠ 0`, the continuous representative `c⁻¹ • S f` is a matrix coefficient of
the right regular representation restricted to the eigenspace of `c`, hence lies in
`matrixCoefficients G`. -/
theorem inv_smul_factor_mem_matrixCoefficients (hT : CommutesRight μ T)
    (hK : IsCompactOperator T) (hTS : T = (ContinuousMap.toLp 2 μ ℂ).comp S) {c : ℂ}
    (hc : c ≠ 0) {f : Lp ℂ 2 μ}
    (hf : f ∈ Module.End.eigenspace (T : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ) c) :
    c⁻¹ • S f ∈ matrixCoefficients G := by -- totalisation-audit: allow c ≠ 0 by hc
  set E := (eigenSubrep μ hT c).toSubmodule
  have : FiniteDimensional ℂ E := finiteDimensional_eigenSubrep hT hK hc
  have : CompleteSpace E := FiniteDimensional.complete ℂ E
  let ℓ : StrongDual ℂ E :=
    c⁻¹ • ((ContinuousMap.evalCLM (R := ℂ) (M := ℂ) (1 : G)).comp (S.comp E.subtypeL)) -- totalisation-audit: allow c ≠ 0 by hc
  let w : E := (InnerProductSpace.toDual ℂ E).symm ℓ
  have key : c⁻¹ • S f = (isContinuousUnitary_eigenSubrep hT c).coeff ⟨f, hf⟩ w := by -- totalisation-audit: allow c ≠ 0 by hc
    ext g
    rw [IsContinuousUnitary.coeff_apply, InnerProductSpace.toDual_symm_apply]
    simp only [ℓ, smul_apply, ContinuousLinearMap.comp_apply,
      Submodule.subtypeL_apply, coe_eigenSubrep_toRepresentation_apply,
      hT.factor_rightTranslateL2 hTS, ContinuousMap.evalCLM_apply, rightTranslate_apply, one_mul,
      ContinuousMap.smul_apply, smul_eq_mul]
  rw [key]
  exact coeff_eigenSubrep_mem_matrixCoefficients hT hK hc _ _

/-- Let `T = toLp ∘ S` be compact and commute with right translations.  Every eigenvector of `T`
for a nonzero eigenvalue is the class of a matrix coefficient. -/
theorem exists_mem_matrixCoefficients_toLp_eq (hT : CommutesRight μ T)
    (hK : IsCompactOperator T) (hTS : T = (ContinuousMap.toLp 2 μ ℂ).comp S) {c : ℂ}
    (hc : c ≠ 0) {f : Lp ℂ 2 μ}
    (hf : f ∈ Module.End.eigenspace (T : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ) c) :
    ∃ F ∈ matrixCoefficients G, ContinuousMap.toLp 2 μ ℂ F = f :=
  ⟨_, inv_smul_factor_mem_matrixCoefficients hT hK hTS hc hf, toLp_inv_smul_factor hTS hc hf⟩

/-- Let `T = toLp ∘ S` be compact and commute with right translations.  The image of
`matrixCoefficients G` in `L²` contains every eigenspace of `T` for a nonzero eigenvalue. -/
theorem eigenspace_le_map_matrixCoefficients (hT : CommutesRight μ T)
    (hK : IsCompactOperator T) (hTS : T = (ContinuousMap.toLp 2 μ ℂ).comp S) {c : ℂ}
    (hc : c ≠ 0) :
    Module.End.eigenspace (T : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ) c ≤
      (matrixCoefficients G).map (ContinuousMap.toLp (E := ℂ) 2 μ ℂ).toLinearMap := by
  intro f hf
  obtain ⟨F, hF, hFf⟩ := exists_mem_matrixCoefficients_toLp_eq hT hK hTS hc hf
  exact ⟨F, hF, hFf⟩

/-- Let `T = toLp ∘ S` be compact and commute with right translations.  Then `S` maps every
eigenvector of `T` into `matrixCoefficients G`; for the eigenvalue `0` the image is `0`. -/
theorem factor_mem_matrixCoefficients (hT : CommutesRight μ T) (hK : IsCompactOperator T)
    (hTS : T = (ContinuousMap.toLp 2 μ ℂ).comp S) (c : ℂ) {f : Lp ℂ 2 μ}
    (hf : f ∈ Module.End.eigenspace (T : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ) c) :
    S f ∈ matrixCoefficients G := by
  rcases eq_or_ne c 0 with rfl | hc
  · have h0 : S f = 0 := by
      refine ContinuousMap.toLp_injective (p := 2) (𝕜 := ℂ) μ ?_
      rw [Module.End.mem_eigenspace_iff, ContinuousLinearMap.coe_coe, hTS] at hf
      rw [map_zero, ← ContinuousLinearMap.comp_apply, hf, zero_smul]
    rw [h0]
    exact zero_mem _
  · have h := Submodule.smul_mem _ c (inv_smul_factor_mem_matrixCoefficients hT hK hTS hc hf)
    rwa [smul_smul, mul_inv_cancel₀ hc, one_smul] at h

/-- Let `T = toLp ∘ S` be compact and commute with right translations.  Then `S` maps the span of
all eigenspaces of `T` into `matrixCoefficients G`. -/
theorem iSup_eigenspace_le_comap_factor (hT : CommutesRight μ T) (hK : IsCompactOperator T)
    (hTS : T = (ContinuousMap.toLp 2 μ ℂ).comp S) :
    ⨆ c, Module.End.eigenspace (T : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ) c ≤
      (matrixCoefficients G).comap (S : Lp ℂ 2 μ →ₗ[ℂ] C(G, ℂ)) :=
  iSup_le fun c _ hf => factor_mem_matrixCoefficients hT hK hTS c hf

end MatrixCoefficients

end PeterWeyl
