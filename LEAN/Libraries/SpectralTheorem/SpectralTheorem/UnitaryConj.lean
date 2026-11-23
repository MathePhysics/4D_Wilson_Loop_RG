import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
# Conjugation of an unbounded operator by a unitary

For a unitary `U : H → K` and a partially defined operator `T` on `K`, the operator `U⁻¹ T U` on
`H` has domain `{ψ | U ψ ∈ D(T)}` and acts by `ψ ↦ U⁻¹ (T (U ψ))`.  Reed–Simon use this
construction throughout Chapter VIII, e.g. for `g(A) = U⁻¹ T_{g(f)} U` (Reed–Simon I, p. 261 and
Theorem VIII.6, pp. 263–264).  Conjugation preserves density of the domain, commutes with taking
adjoints, and so preserves self-adjointness.

## Main definitions and results

* `SpectralTheorem.unitaryConj U T`: the operator `U⁻¹ T U` with domain `U⁻¹ D(T)`.
* `SpectralTheorem.mem_unitaryConj_domain`, `SpectralTheorem.unitaryConj_apply`.
* `SpectralTheorem.dense_unitaryConj_domain`: `U⁻¹ D(T)` is dense when `D(T)` is.
* `SpectralTheorem.adjoint_unitaryConj`: `(U⁻¹ T U)† = U⁻¹ T† U` for densely defined `T`.
* `SpectralTheorem.isSelfAdjoint_unitaryConj`: `U⁻¹ T U` is self-adjoint when `T` is.
* `SpectralTheorem.unitaryConj_toPMap`: for bounded `B`, `U⁻¹ B U` is the bounded operator
  `U⁻¹ ∘ B ∘ U`, everywhere defined.
-/

noncomputable section

open scoped InnerProductSpace LinearPMap

namespace SpectralTheorem

universe u v

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- **Conjugation by a unitary**: the operator `U⁻¹ T U` on `H`, with domain
`{ψ | U ψ ∈ D(T)}` and `U⁻¹ T U ψ = U⁻¹ (T (U ψ))`. -/
def unitaryConj (U : H ≃ₗᵢ[ℂ] K) (T : K →ₗ.[ℂ] K) : H →ₗ.[ℂ] H where
  domain := T.domain.comap (U : H →ₗ[ℂ] K)
  toFun :=
    { toFun := fun ψ => U.symm (T ⟨U ψ, ψ.2⟩)
      map_add' := fun ψ φ => by
        have h : (⟨U ((ψ + φ : T.domain.comap (U : H →ₗ[ℂ] K)) : H), (ψ + φ).2⟩ : T.domain) =
            ⟨U ψ, ψ.2⟩ + ⟨U φ, φ.2⟩ :=
          Subtype.ext (by simp)
        rw [h, LinearPMap.map_add, map_add]
      map_smul' := fun c ψ => by
        have h : (⟨U ((c • ψ : T.domain.comap (U : H →ₗ[ℂ] K)) : H), (c • ψ).2⟩ : T.domain) =
            c • ⟨U ψ, ψ.2⟩ :=
          Subtype.ext (by simp)
        rw [h, LinearPMap.map_smul, map_smul, RingHom.id_apply] }

variable (U : H ≃ₗᵢ[ℂ] K) (T : K →ₗ.[ℂ] K)

/-- The domain of `U⁻¹ T U` is `{ψ | U ψ ∈ D(T)}`. -/
theorem mem_unitaryConj_domain {ψ : H} : ψ ∈ (unitaryConj U T).domain ↔ U ψ ∈ T.domain :=
  Iff.rfl

/-- `U⁻¹ T U ψ = U⁻¹ (T (U ψ))`. -/
theorem unitaryConj_apply (ψ : (unitaryConj U T).domain) :
    unitaryConj U T ψ = U.symm (T ⟨U ψ, ψ.2⟩) :=
  rfl

/-- `U (U⁻¹ T U ψ) = T (U ψ)`. -/
theorem apply_unitaryConj (ψ : (unitaryConj U T).domain) :
    U (unitaryConj U T ψ) = T ⟨U ψ, ψ.2⟩ :=
  U.apply_symm_apply _

/-- `U⁻¹ D(T)` is dense when `D(T)` is. -/
theorem dense_unitaryConj_domain (hT : Dense (T.domain : Set K)) :
    Dense ((unitaryConj U T).domain : Set H) := by
  have h := hT.preimage U.toHomeomorph.isOpenMap
  rw [LinearIsometryEquiv.coe_toHomeomorph] at h
  exact h

/-- For a bounded `B` on `K`, `U⁻¹ B U` is the everywhere defined operator `C = U⁻¹ ∘ B ∘ U`
(stated for any bounded `C` with `C ψ = U⁻¹ (B (U ψ))`). -/
theorem unitaryConj_toPMap (B : K →L[ℂ] K) (C : H →L[ℂ] H) (hC : ∀ ψ, C ψ = U.symm (B (U ψ))) :
    unitaryConj U ((B : K →ₗ[ℂ] K).toPMap ⊤) = (C : H →ₗ[ℂ] H).toPMap ⊤ := by
  refine LinearPMap.ext ?_ fun x y hxy => ?_
  · rw [LinearMap.toPMap_domain]
    exact eq_top_iff.2 fun ψ _ => Submodule.mem_top
  · change U.symm (B (U x)) = C x
    exact (hC x).symm

section Adjoint

variable [CompleteSpace H] [CompleteSpace K]

omit [CompleteSpace H] in
/-- `U⁻¹ T† U` is a formal adjoint of `U⁻¹ T U`. -/
theorem isFormalAdjoint_unitaryConj (hT : Dense (T.domain : Set K)) :
    (unitaryConj U T).IsFormalAdjoint (unitaryConj U T†) := by
  intro x y
  rw [unitaryConj_apply, unitaryConj_apply, LinearIsometryEquiv.inner_map_eq_flip,
    LinearIsometryEquiv.symm_symm, ← LinearIsometryEquiv.inner_map_eq_flip]
  exact (LinearPMap.adjoint_isFormalAdjoint hT).symm ⟨U x, x.2⟩ ⟨U y, y.2⟩

/-- **The adjoint of a conjugated operator**: `(U⁻¹ T U)† = U⁻¹ T† U` for densely defined `T`. -/
theorem adjoint_unitaryConj (hT : Dense (T.domain : Set K)) :
    (unitaryConj U T)† = unitaryConj U T† := by
  have hT' := dense_unitaryConj_domain U T hT
  have hle := (isFormalAdjoint_unitaryConj U T hT).le_adjoint hT'
  refine (LinearPMap.eq_of_le_of_domain_eq hle (le_antisymm hle.1 fun y hy => ?_)).symm
  rw [mem_unitaryConj_domain]
  refine LinearPMap.mem_adjoint_domain_of_exists _ ⟨U ((unitaryConj U T)† ⟨y, hy⟩), fun z => ?_⟩
  have hz : U.symm (z : K) ∈ (unitaryConj U T).domain := by
    rw [mem_unitaryConj_domain, LinearIsometryEquiv.apply_symm_apply]
    exact z.2
  have hzz : (⟨U (U.symm (z : K)), hz⟩ : T.domain) = z :=
    Subtype.ext (LinearIsometryEquiv.apply_symm_apply U _)
  have h := LinearPMap.adjoint_isFormalAdjoint hT' ⟨y, hy⟩ ⟨U.symm z, hz⟩
  rw [unitaryConj_apply] at h
  rw [LinearIsometryEquiv.inner_map_eq_flip, h, ← LinearIsometryEquiv.inner_map_eq_flip]
  exact congrArg (fun w => ⟪U y, T w⟫_ℂ) hzz

/-- **Conjugation preserves self-adjointness**: if `T` is self-adjoint, so is `U⁻¹ T U`. -/
theorem isSelfAdjoint_unitaryConj (hT : IsSelfAdjoint T) : IsSelfAdjoint (unitaryConj U T) := by
  rw [LinearPMap.isSelfAdjoint_def, adjoint_unitaryConj U T hT.dense_domain]
  exact congrArg (unitaryConj U) hT

end Adjoint

end SpectralTheorem
