import SpectralTheorem.RealCalculus
import SpectralTheorem.SeparableDecomposition
import Mathlib.Topology.Algebra.Module.Star

/-!
# Real cyclic vectors on the complexification

Let `E` be a real Hilbert space and `E_ℂ` its complexification, with conjugation `conj`.  To
obtain the multiplication operator form of the spectral theorem over `ℝ` (Reed–Simon I, Theorem
VIII.4, pp. 260–261, and Theorem VII.3, p. 227, for real Hilbert spaces) from the complex one, we
choose the cyclic vectors of the complex construction **real**, i.e. fixed by `conj`.  This file
proves the facts about the continuous functional calculus and the cyclic decomposition needed
for that.

Let `B` be a bounded normal operator on `E_ℂ` with `conj (B (conj z)) = B† z` for all `z`
(`IsConjAdjoint B`).  This holds for `B = (A_ℂ + i)⁻¹`, `A` self-adjoint on `E`, whose adjoint is
`(A_ℂ - i)⁻¹`, and for `B = T_ℂ` with `T` bounded self-adjoint.

Proof sketch.
1. `g ↦ conj ∘ ḡ(B) ∘ conj` is a continuous `⋆`-homomorphism `C(σ(B), ℂ) → 𝓛(E_ℂ)` sending the
   variable to `conj ∘ B† ∘ conj = B`, so it is `cfcHom` (uniqueness of the continuous functional
   calculus): `conj (g(B) z) = ḡ(B) (conj z)`.
2. For a real vector `ψ` the cyclic subspace `H_ψ` is `conj`-invariant and the cyclic isometry
   `U_ψ : L²(σ(B), μ_ψ) → E_ℂ` satisfies `conj (U_ψ φ) = U_ψ φ̄` (on continuous `φ` by 1, then by
   density).
3. Zorn's lemma over sets of real vectors with pairwise orthogonal cyclic subspaces gives a
   cyclic decomposition with real vectors: a vector `v` orthogonal to all `H_ψ` has `conj v`
   orthogonal to them too, hence so are the real vectors `v + conj v = 2 re v` and
   `-i (v - conj v) = 2 im v`, which vanish by maximality.
4. For such a decomposition `D`, the unitary `U : E_ℂ ≃ L²(Σ_ψ σ(B))` commutes with the
   conjugations: `U (conj z) = conj (U z)` (on each summand by 2, then on the Hilbert sum).

## Main definitions and results

* `SpectralTheorem.Complexification.IsConjAdjoint B`: `conj ∘ B ∘ conj = B†`.
* `SpectralTheorem.conjLp μ`: pointwise conjugation on `L²(μ; ℂ)`.
* `SpectralTheorem.conj_cfcHom`: `conj (g(B) z) = ḡ(B) (conj z)`.
* `SpectralTheorem.conj_mem_cyclicSubmodule`, `SpectralTheorem.conj_cyclicIsometry`.
* `SpectralTheorem.CyclicDecomposition.exists_real`: a cyclic decomposition with real vectors.
* `SpectralTheorem.CyclicDecomposition.unitary_conj`: `U (conj z) = conj (U z)`.
* `SpectralTheorem.isConjAdjoint_resolvent`, `SpectralTheorem.isConjAdjoint_complexifyCLM`: the
  two instances.
-/

noncomputable section

open scoped InnerProductSpace ENNReal
open MeasureTheory Filter

namespace SpectralTheorem

universe u

open Complexification

/-! ### Pointwise conjugation on `L²` -/

section ConjLp

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

/-- Pointwise complex conjugation `φ ↦ φ̄` on `L²(μ; ℂ)`, a conjugate-linear isometry. -/
def conjLp : Lp ℂ 2 μ →L⋆[ℂ] Lp ℂ 2 μ :=
  ((starL ℂ : ℂ ≃L⋆[ℂ] ℂ) : ℂ →L⋆[ℂ] ℂ).compLpL 2 μ

variable {μ}

/-- `conjLp φ` is represented by `x ↦ conj (φ x)`. -/
theorem coeFn_conjLp (φ : Lp ℂ 2 μ) :
    (conjLp μ φ : X → ℂ) =ᵐ[μ] fun x => starRingEnd ℂ (φ x) :=
  ContinuousLinearMap.coeFn_compLpL _ φ

/-- Conjugation on `L²` is an involution. -/
@[simp]
theorem conjLp_conjLp (φ : Lp ℂ 2 μ) : conjLp μ (conjLp μ φ) = φ := by
  refine Lp.ext ?_
  filter_upwards [coeFn_conjLp (conjLp μ φ), coeFn_conjLp φ] with x h1 h2
  rw [h1, h2, Complex.conj_conj]

/-- The conjugate of the `L²` class of a function is the class of the conjugate function. -/
theorem conjLp_toLp {f : X → ℂ} (hf : MemLp f 2 μ)
    (hf' : MemLp (fun x => starRingEnd ℂ (f x)) 2 μ) :
    conjLp μ (hf.toLp f) = hf'.toLp fun x => starRingEnd ℂ (f x) := by
  refine Lp.ext ?_
  filter_upwards [coeFn_conjLp (hf.toLp f), hf.coeFn_toLp, hf'.coeFn_toLp] with x h1 h2 h3
  rw [h1, h2, h3]

end ConjLp

/-! ### Conjugation symmetry of the continuous functional calculus -/

section Cfc

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- An operator `B` on `E_ℂ` whose conjugate `z ↦ conj (B (conj z))` is its adjoint `B†`. -/
def Complexification.IsConjAdjoint (B : Complexification E →L[ℂ] Complexification E) : Prop :=
  ∀ z, conj (B (conj z)) = star B z

variable (B : Complexification E →L[ℂ] Complexification E) [hB : IsStarNormal B]

/-- The conjugated calculus `g ↦ conj ∘ ḡ(B) ∘ conj`, a `⋆`-homomorphism. -/
def conjCfc : C(spectrum ℂ B, ℂ) →⋆ₐ[ℂ] (Complexification E →L[ℂ] Complexification E) where
  toFun g := conjOp (cfcHom hB (star g))
  map_one' := by rw [star_one, map_one, conjOp_one]
  map_mul' f g := by rw [star_mul', map_mul, conjOp_mul]
  map_zero' := by rw [star_zero, map_zero, conjOp_zero]
  map_add' f g := by rw [star_add, map_add, conjOp_add]
  commutes' c := by
    change conjOp (cfcHom hB (star (algebraMap ℂ _ c))) = _
    rw [← algebraMap_star_comm, AlgHomClass.commutes]
    exact conjOp_algebraMap c
  map_star' g := by
    rw [ContinuousLinearMap.star_eq_adjoint, adjoint_conjOp,
      ← ContinuousLinearMap.star_eq_adjoint, ← map_star]

theorem conjCfc_apply (g : C(spectrum ℂ B, ℂ)) (z : Complexification E) :
    conjCfc B g z = conj (cfcHom hB (star g) (conj z)) :=
  rfl

/-- The conjugated calculus is continuous: `‖conj ∘ ḡ(B) ∘ conj‖ ≤ ‖ḡ(B)‖ = ‖g‖`. -/
theorem continuous_conjCfc : Continuous (conjCfc B) :=
  AddMonoidHomClass.continuous_of_bound (conjCfc B) 1 fun g => by
    rw [one_mul]
    refine (norm_conjOp_le _).trans ?_
    rw [norm_cfcHom B (star g) hB, norm_star]

variable {B}

/-- The conjugated calculus sends the variable to `conj ∘ B† ∘ conj = B`. -/
theorem conjCfc_id (hBc : IsConjAdjoint B) :
    conjCfc B ((ContinuousMap.id ℂ).restrict (spectrum ℂ B)) = B := by
  change conjOp (cfcHom hB (star ((ContinuousMap.id ℂ).restrict (spectrum ℂ B)))) = B
  rw [map_star, cfcHom_id]
  refine ContinuousLinearMap.ext fun z => ?_
  rw [conjOp_apply, ← hBc, conj_conj, conj_conj]

/-- By uniqueness of the continuous functional calculus, the conjugated calculus is `cfcHom`. -/
theorem cfcHom_eq_conjCfc (hBc : IsConjAdjoint B) : cfcHom hB = conjCfc B :=
  cfcHom_eq_of_continuous_of_map_id hB _ (continuous_conjCfc B) (conjCfc_id hBc)

/-- **Conjugation symmetry**: `conj (g(B) z) = ḡ(B) (conj z)`. -/
theorem conj_cfcHom (hBc : IsConjAdjoint B) (g : C(spectrum ℂ B, ℂ)) (z : Complexification E) :
    conj (cfcHom hB g z) = cfcHom hB (star g) (conj z) := by
  have e := DFunLike.congr_fun (DFunLike.congr_fun (cfcHom_eq_conjCfc hBc) (star g)) (conj z)
  rw [e, conjCfc_apply, star_star, conj_conj]

/-! ### Real cyclic vectors -/

/-- For a real vector `ψ`, `conj (g(B) ψ) = ḡ(B) ψ`. -/
theorem conj_cfcHom_of_real (hBc : IsConjAdjoint B) {ψ : Complexification E} (hψ : conj ψ = ψ)
    (g : C(spectrum ℂ B, ℂ)) : conj (cfcHom hB g ψ) = cfcHom hB (star g) ψ := by
  rw [conj_cfcHom hBc, hψ]

/-- The cyclic subspace of a real vector is invariant under the conjugation. -/
theorem conj_mem_cyclicSubmodule (hBc : IsConjAdjoint B) {ψ : Complexification E}
    (hψ : conj ψ = ψ) {v : Complexification E} (hv : v ∈ cyclicSubmodule B ψ) :
    conj v ∈ cyclicSubmodule B ψ := by
  have hmaps : Set.MapsTo conj (Set.range (cyclicMap B ψ)) (Set.range (cyclicMap B ψ)) := by
    rintro _ ⟨g, rfl⟩
    exact ⟨star g, by rw [cyclicMap_apply, cyclicMap_apply, conj_cfcHom_of_real hBc hψ]⟩
  rw [cyclicSubmodule, ← SetLike.mem_coe, Submodule.topologicalClosure_coe,
    LinearMap.coe_range] at hv ⊢
  exact hmaps.closure conj.continuous hv

/-- The conjugate of the `L²` class of a continuous function is the class of its conjugate. -/
theorem conjLp_toLp_continuousMap {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ] (f : C(X, ℂ)) :
    conjLp μ (ContinuousMap.toLp 2 μ ℂ f) = ContinuousMap.toLp 2 μ ℂ (star f) := by
  refine Lp.ext ?_
  filter_upwards [coeFn_conjLp (ContinuousMap.toLp 2 μ ℂ f),
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) μ f,
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) μ (star f)] with x h1 h2 h3
  rw [h1, h2, h3, ContinuousMap.star_apply, starRingEnd_apply]

/-- **The cyclic isometry of a real vector intertwines the conjugations**:
`conj (U_ψ φ) = U_ψ φ̄`.  For continuous `φ` this is `conj (φ(B) ψ) = φ̄(B) ψ`; both sides are
continuous in `φ`, and continuous functions are dense in `L²(σ(B), μ_ψ)`. -/
theorem conj_cyclicIsometry (hBc : IsConjAdjoint B) {ψ : Complexification E} (hψ : conj ψ = ψ)
    (φ : Lp ℂ 2 (spectralMeasure B ψ)) :
    conj (cyclicIsometry B ψ φ) = cyclicIsometry B ψ (conjLp _ φ) := by
  refine (denseRange_toLp B ψ).induction_on φ
    (isClosed_eq (conj.continuous.comp (cyclicIsometry B ψ).continuous)
      ((cyclicIsometry B ψ).continuous.comp (conjLp _).continuous)) fun f => ?_
  rw [conjLp_toLp_continuousMap, cyclicIsometry_toLp, cyclicIsometry_toLp,
    conj_cfcHom_of_real hBc hψ]

/-- If `v` is orthogonal to the cyclic subspace of a real vector `ψ`, so is `conj v`. -/
theorem conj_mem_orthogonal_cyclicSubmodule (hBc : IsConjAdjoint B) {ψ : Complexification E}
    (hψ : conj ψ = ψ) {v : Complexification E} (hv : v ∈ (cyclicSubmodule B ψ)ᗮ) :
    conj v ∈ (cyclicSubmodule B ψ)ᗮ := by
  refine (Submodule.mem_orthogonal _ _).mpr fun u hu => ?_
  rw [← conj_conj u, inner_conj_conj']
  exact (Submodule.mem_orthogonal' _ _).mp hv _ (conj_mem_cyclicSubmodule hBc hψ hu)

/-- **A cyclic decomposition with real vectors** (step 3 of the module docstring): Zorn's lemma
over sets of real vectors with pairwise orthogonal cyclic subspaces, as in
`CyclicDecomposition.nonempty`.  If `v` is orthogonal to all the cyclic subspaces, so is
`conj v`, hence so are the real vectors `v + conj v` and `i (v - conj v)`; by maximality they
vanish, so `v = 0`. -/
theorem CyclicDecomposition.exists_real (hBc : IsConjAdjoint B) :
    ∃ D : CyclicDecomposition B, ∀ ψ ∈ D.vectors, conj ψ = ψ := by
  obtain ⟨s, hs⟩ := zorn_subset
    {s : Set (Complexification E) | IsCyclicOrthogonal B s ∧ ∀ ψ ∈ s, conj ψ = ψ}
    fun c hc hchain => by
      refine ⟨⋃₀ c, ⟨fun ψ hψ φ hφ hne => ?_, fun ψ hψ => ?_⟩,
        fun s hs => Set.subset_sUnion_of_mem hs⟩
      · obtain ⟨a, ha, hψa⟩ := Set.mem_sUnion.mp hψ
        obtain ⟨b, hb, hφb⟩ := Set.mem_sUnion.mp hφ
        rcases hchain.total ha hb with hab | hba
        · exact (hc hb).1 (hab hψa) hφb hne
        · exact (hc ha).1 hψa (hba hφb) hne
      · obtain ⟨a, ha, hψa⟩ := Set.mem_sUnion.mp hψ
        exact (hc ha).2 ψ hψa
  have hreal : ∀ w : Complexification E, conj w = w →
      (∀ ψ ∈ s, w ∈ (cyclicSubmodule B ψ)ᗮ) → w = 0 := by
    intro w hw hv
    have hins : insert w s ∈
        {s : Set (Complexification E) | IsCyclicOrthogonal B s ∧ ∀ ψ ∈ s, conj ψ = ψ} := by
      refine ⟨hs.prop.1.insert fun ψ hψ _ => ⟨?_, ?_⟩, fun ψ hψ => ?_⟩
      · exact cyclicSubmodule_isOrtho B (hv ψ hψ)
      · exact (cyclicSubmodule_isOrtho B (hv ψ hψ)).symm
      · rcases hψ with rfl | hψ
        · exact hw
        · exact hs.prop.2 ψ hψ
    have hws : w ∈ s := hs.eq_of_subset hins (Set.subset_insert w s) ▸ Set.mem_insert w s
    exact inner_self_eq_zero.mp
      ((Submodule.mem_orthogonal' _ _).mp (hv w hws) w (mem_cyclicSubmodule_self B w))
  refine ⟨⟨s, hs.prop.1, fun v hv => ?_⟩, hs.prop.2⟩
  have hc : ∀ ψ ∈ s, conj v ∈ (cyclicSubmodule B ψ)ᗮ := fun ψ hψ =>
    conj_mem_orthogonal_cyclicSubmodule hBc (hs.prop.2 ψ hψ) (hv ψ hψ)
  have h1 : v + conj v = 0 := by
    refine hreal _ ?_ fun ψ hψ => Submodule.add_mem _ (hv ψ hψ) (hc ψ hψ)
    rw [map_add, conj_conj, add_comm]
  have h2 : Complex.I • (v - conj v) = 0 := by
    refine hreal _ ?_ fun ψ hψ =>
      Submodule.smul_mem _ _ (Submodule.sub_mem _ (hv ψ hψ) (hc ψ hψ))
    rw [LinearIsometryEquiv.map_smulₛₗ, map_sub, conj_conj, Complex.conj_I, neg_smul,
      ← smul_neg, neg_sub]
  have h3 : v - conj v = 0 := (smul_eq_zero.mp h2).resolve_left Complex.I_ne_zero
  have h4 : (2 : ℂ) • v = 0 := by
    rw [two_smul]
    calc v + v = (v + conj v) + (v - conj v) := by abel
      _ = 0 := by rw [h1, h3, add_zero]
  exact (smul_eq_zero.mp h4).resolve_left two_ne_zero

end Cfc

/-! ### The spectral representation commutes with the conjugations -/

section SigmaConj

variable {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)] (μ : ∀ i, Measure (X i))

/-- The components of the conjugate of `f ∈ L²(Σ i, X i)` are the conjugates of the
components. -/
theorem sigmaL2Equiv_conjLp (f : Lp ℂ 2 (sigmaMeasure μ)) (i : ι) :
    sigmaL2Equiv μ (conjLp _ f) i = conjLp (μ i) (sigmaL2Equiv μ f i) := by
  refine Lp.ext ?_
  filter_upwards [sigmaL2Equiv_apply_ae_eq μ (conjLp _ f) i,
    (ae_eq_sigmaMeasure_iff μ).1 (coeFn_conjLp f) i, coeFn_conjLp (sigmaL2Equiv μ f i),
    sigmaL2Equiv_apply_ae_eq μ f i] with x h1 h2 h3 h4
  rw [h1, h2, h3, h4]

/-- The conjugate of an element of `L²(Σ i, X i)` supported on one slice. -/
theorem conjLp_sigmaL2Equiv_symm_single [DecidableEq ι] (i : ι) (φ : Lp ℂ 2 (μ i)) :
    conjLp _ ((sigmaL2Equiv μ).symm (lp.single 2 i φ)) =
      (sigmaL2Equiv μ).symm (lp.single 2 i (conjLp _ φ)) := by
  rw [LinearIsometryEquiv.eq_symm_apply]
  refine lp.ext (funext fun j => ?_)
  rw [sigmaL2Equiv_conjLp, LinearIsometryEquiv.apply_symm_apply]
  by_cases hj : j = i
  · subst hj
    rw [lp.single_apply_self, lp.single_apply_self]
  · rw [lp.single_apply_ne 2 i _ hj, lp.single_apply_ne 2 i _ hj, map_zero]

end SigmaConj

/-! ### The unitary of a real cyclic decomposition -/

section Unitary

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {B : Complexification E →L[ℂ] Complexification E} [hB : IsStarNormal B]

namespace CyclicDecomposition

variable (D : CyclicDecomposition B)

open scoped Classical in
/-- **The spectral representation of a real cyclic decomposition commutes with the
conjugations**: `U (conj z) = conj (U z)`.  On a single summand, `z = U_ψ φ`, this is
`conj (U_ψ φ) = U_ψ φ̄` (`conj_cyclicIsometry`) together with the fact that conjugation acts
componentwise on `L²(Σ_ψ σ(B))`; both sides are continuous and additive in `z`, so it holds on
the Hilbert sum. -/
theorem unitary_conj (hBc : IsConjAdjoint B) (hD : ∀ ψ ∈ D.vectors, conj ψ = ψ)
    (z : Complexification E) : D.unitary (conj z) = conjLp _ (D.unitary z) := by
  obtain ⟨w, rfl⟩ := D.equiv.symm.surjective z
  let L₁ : lp D.Summand 2 →+ Lp ℂ 2 D.measure :=
    AddMonoidHom.mk' (fun w => D.unitary (conj (D.equiv.symm w))) fun a b => by
      simp only [map_add]
  let L₂ : lp D.Summand 2 →+ Lp ℂ 2 D.measure :=
    AddMonoidHom.mk' (fun w => conjLp _ (D.unitary (D.equiv.symm w))) fun a b => by
      simp only [map_add]
  have hc₁ : Continuous L₁ :=
    D.unitary.continuous.comp (conj.continuous.comp D.equiv.symm.continuous)
  have hc₂ : Continuous L₂ :=
    (conjLp _).continuous.comp (D.unitary.continuous.comp D.equiv.symm.continuous)
  change L₁ w = L₂ w
  have hsum := lp.hasSum_single (E := D.Summand) (p := 2) ENNReal.ofNat_ne_top w
  refine (hsum.map L₁ hc₁).unique ?_
  convert hsum.map L₂ hc₂ using 1
  funext ψ
  simp only [Function.comp_apply, L₁, L₂, AddMonoidHom.mk'_apply, D.equiv_symm_single]
  rw [conj_cyclicIsometry hBc (hD ψ ψ.2), D.unitary_cyclicIsometry, D.unitary_cyclicIsometry]
  exact (conjLp_sigmaL2Equiv_symm_single (fun ψ : D.vectors => spectralMeasure B (ψ : _)) ψ
    (w ψ)).symm

end CyclicDecomposition

end Unitary

/-! ### The two instances -/

section Instances

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The complexification of a bounded self-adjoint operator is conjugate-adjoint:
`conj ∘ T_ℂ ∘ conj = T_ℂ = T_ℂ†`. -/
theorem isConjAdjoint_complexifyCLM {T : E →L[ℝ] E} (hT : IsSelfAdjoint T) :
    IsConjAdjoint (complexifyCLM T) := fun z => by
  rw [complexifyCLM_conj, conj_conj, (isSelfAdjoint_complexifyCLM_iff.mpr hT).star_eq]

variable {A : E →ₗ.[ℝ] E}

/-- The resolvent `(A_ℂ + i)⁻¹` of the complexification of a self-adjoint `A` is
conjugate-adjoint: `conj ((A_ℂ + i)⁻¹ (conj z)) = (A_ℂ - i)⁻¹ z = ((A_ℂ + i)⁻¹)† z`, because
`A_ℂ` commutes with the conjugation. -/
theorem isConjAdjoint_resolvent (hA : IsSelfAdjoint (complexifyPMap A)) :
    IsConjAdjoint (resolvent hA) := fun z => by
  rw [star_resolvent]
  set y := resolvent hA (conj z) with hy
  have hyD : y ∈ (complexifyPMap A).domain := resolventI_mem_domain hA abs_one (conj z)
  have hAy : complexifyPMap A ⟨y, hyD⟩ + (((1 : ℝ) : ℂ) * RCLike.I) • y = conj z :=
    addScalar_resolventI hA abs_one (conj z)
  have key : complexifyPMap A ⟨conj y, conj_mem_complexifyPMap_domain hyD⟩ +
      (((-1 : ℝ) : ℂ) * RCLike.I) • conj y = z := by
    rw [complexifyPMap_conj ⟨y, hyD⟩]
    have h := congrArg conj hAy
    rw [conj_conj, map_add, LinearIsometryEquiv.map_smulₛₗ] at h
    rw [← h]
    congr 1
    simp
  rw [← key, resolventI_addScalar]

end Instances

end SpectralTheorem
