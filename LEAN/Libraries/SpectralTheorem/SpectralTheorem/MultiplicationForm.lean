import SpectralTheorem.Decomposition
import SpectralTheorem.SigmaL2
import SpectralTheorem.MultiplicationBounded

/-!
# The spectral theorem for bounded normal operators: multiplication operator form

Reed–Simon I, Theorem VII.3, p. 227 (for bounded self-adjoint `A` on a separable space; the
normal case is Problem VII.5): there are measures `μₙ` on `σ(A)` and a unitary
`U : H → ⊕ₙ L²(ℝ, dμₙ)` with `(U A U⁻¹ ψ)ₙ(λ) = λ ψₙ(λ)`; equivalently (the Corollary on the
same page) a measure space `⟨M, μ⟩`, a bounded function `F` on `M` and a unitary
`U : H → L²(M, dμ)` with `(U A U⁻¹ f)(m) = F(m) f(m)`.

Here `T` is a bounded normal operator on an arbitrary complex Hilbert space.  For a cyclic
decomposition `D` (`SpectralTheorem.Decomposition`) the measure space is the disjoint union
`M = Σ_{ψ ∈ D} σ(T)` with `μ = Σ_ψ μ_ψ` (`SpectralTheorem.sigmaMeasure`), and `F(ψ, λ) = λ`.
The unitary `U : H ≃ L²(M, μ)` is the Hilbert-sum unitary `H ≃ ⊕̂_ψ L²(σ(T), μ_ψ)` followed by
`⊕̂_ψ L²(σ(T), μ_ψ) ≃ L²(M, μ)` (`SpectralTheorem.sigmaL2Equiv`).  More generally
`U g(T) U⁻¹` is multiplication by `g(λ)` for every continuous `g`.  Without separability `μ` need
not be finite or σ-finite; for separable `H` it can be made finite
(`SpectralTheorem.exists_unitary_mulL_finite` in `SpectralTheorem.SeparableDecomposition`).

## Main definitions and results

* `SpectralTheorem.CyclicDecomposition.Space`, `.measure`, `.coord`: the measure space
  `Σ_ψ σ(T)`, the measure `Σ_ψ μ_ψ` and the spectral variable `λ`.
* `SpectralTheorem.CyclicDecomposition.unitary`: the unitary `U : H ≃ L²(Σ_ψ σ(T), Σ_ψ μ_ψ)`.
* `SpectralTheorem.CyclicDecomposition.unitary_cfcHom`: `U (g(T) h) = g(λ) · U h`.
* `SpectralTheorem.CyclicDecomposition.unitary_apply_T`: `U (T h) = λ · U h`.
* `SpectralTheorem.exists_unitary_mulL`: **Reed–Simon I, Theorem VII.3** for bounded normal
  operators: `T` is unitarily equivalent to multiplication by a bounded measurable function.
-/

noncomputable section

open scoped InnerProductSpace ENNReal
open MeasureTheory Filter

namespace SpectralTheorem

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {T : H →L[ℂ] H} [hT : IsStarNormal T]

namespace CyclicDecomposition

variable (D : CyclicDecomposition T)

/-- The measure space `Σ_ψ σ(T)` of the spectral representation. -/
abbrev Space : Type _ :=
  Σ _ψ : D.vectors, spectrum ℂ T

/-- The measure `Σ_ψ μ_ψ` on `Σ_ψ σ(T)`. -/
abbrev measure : Measure D.Space :=
  sigmaMeasure fun ψ : D.vectors => spectralMeasure T (ψ : H)

/-- The spectral variable `λ` on `Σ_ψ σ(T)`. -/
def coord (p : D.Space) : ℂ :=
  (p.2 : ℂ)

/-- **The spectral representation** `U : H ≃ L²(Σ_ψ σ(T), Σ_ψ μ_ψ)`. -/
def unitary : H ≃ₗᵢ[ℂ] Lp ℂ 2 D.measure :=
  D.equiv.trans (sigmaL2Equiv fun ψ : D.vectors => spectralMeasure T (ψ : H)).symm

/-- A function of the spectral variable, `(ψ, λ) ↦ g(λ)`, is measurable when `g` is. -/
theorem measurable_comp_snd {g : spectrum ℂ T → ℂ} (hg : Measurable g) :
    Measurable fun p : D.Space => g p.2 :=
  measurable_sigma_iff.mpr fun _ => hg

/-- A bounded measurable function of the spectral variable is in `L^∞`. -/
theorem memLp_top_comp_snd {g : spectrum ℂ T → ℂ} (hg : Measurable g) {C : ℝ}
    (hC : ∀ z, ‖g z‖ ≤ C) : MemLp (fun p : D.Space => g p.2) ∞ D.measure :=
  memLp_top_of_bound (D.measurable_comp_snd hg).aestronglyMeasurable C
    (Filter.Eventually.of_forall fun p => hC p.2)

/-- A continuous function of the spectral variable is in `L^∞`. -/
theorem memLp_top_continuousMap (g : C(spectrum ℂ T, ℂ)) :
    MemLp (fun p : D.Space => g p.2) ∞ D.measure :=
  D.memLp_top_comp_snd g.continuous.measurable fun z => g.norm_coe_le_norm z

/-- The spectral variable is in `L^∞`. -/
theorem memLp_top_coord : MemLp D.coord ∞ D.measure :=
  D.memLp_top_continuousMap ((ContinuousMap.id ℂ).restrict (spectrum ℂ T))

open scoped Classical in
/-- `U (U_ψ φ)` is the element of `L²(Σ_ψ σ(T))` supported on the `ψ`-th copy of `σ(T)`, where it
is `φ`. -/
theorem unitary_cyclicIsometry (ψ : D.vectors) (φ : D.Summand ψ) :
    D.unitary (cyclicIsometry T (ψ : H) φ) =
      (sigmaL2Equiv fun ψ : D.vectors => spectralMeasure T (ψ : H)).symm (lp.single 2 ψ φ) := by
  rw [unitary, LinearIsometryEquiv.trans_apply, ← D.equiv_symm_single,
    LinearIsometryEquiv.apply_symm_apply]

open scoped Classical in
/-- `U (g(T) h) = g(λ) · U h` for `h` in a single cyclic subspace, `h = U_ψ φ`: by
`cyclicIsometry_smul`, `g(T) U_ψ φ = U_ψ (g φ)`, and both sides are supported on the `ψ`-th
copy of `σ(T)`, where they are `g φ`. -/
theorem unitary_cfcHom_cyclicIsometry (g : C(spectrum ℂ T, ℂ)) (ψ : D.vectors)
    (φ : D.Summand ψ) :
    D.unitary (cfcHom hT g (cyclicIsometry T (ψ : H) φ)) =
      mulL (fun p : D.Space => g p.2) (D.memLp_top_continuousMap g)
        (D.unitary (cyclicIsometry T (ψ : H) φ)) := by
  set σE := sigmaL2Equiv fun ψ : D.vectors => spectralMeasure T (ψ : H) with hσE
  rw [← cyclicIsometry_smul, D.unitary_cyclicIsometry, D.unitary_cyclicIsometry]
  apply σE.injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  refine lp.ext (funext fun j => Lp.ext ?_)
  have hmul := sigmaL2Equiv_mul_ae_eq (fun ψ : D.vectors => spectralMeasure T (ψ : H))
    (memLp_two_mul (D.memLp_top_continuousMap g) (σE.symm (lp.single 2 ψ φ))) j
  rw [← mulL_apply (D.memLp_top_continuousMap g), LinearIsometryEquiv.apply_symm_apply] at hmul
  refine EventuallyEq.trans ?_ hmul.symm
  by_cases hj : j = ψ
  · subst hj
    rw [lp.single_apply_self, lp.single_apply_self, toLp_top_smul_eq_toLp]
    exact MemLp.coeFn_toLp _
  · rw [lp.single_apply_ne 2 ψ _ hj, lp.single_apply_ne 2 ψ _ hj]
    filter_upwards [Lp.coeFn_zero ℂ 2 (spectralMeasure T (j : H))] with x hx
    rw [hx]
    simp

/-- **`U g(T) U⁻¹` is multiplication by `g(λ)`** for continuous `g : σ(T) → ℂ`: the identity
holds on each cyclic summand (`unitary_cfcHom_cyclicIsometry`), and both sides are continuous
and linear in `h`, so it holds on the Hilbert sum. -/
theorem unitary_cfcHom (g : C(spectrum ℂ T, ℂ)) (h : H) :
    D.unitary (cfcHom hT g h) =
      mulL (fun p : D.Space => g p.2) (D.memLp_top_continuousMap g) (D.unitary h) := by
  classical
  obtain ⟨w, rfl⟩ := D.equiv.symm.surjective h
  let L₁ : lp D.Summand 2 →L[ℂ] Lp ℂ 2 D.measure :=
    D.unitary.toLinearIsometry.toContinuousLinearMap ∘L cfcHom hT g ∘L
      D.equiv.symm.toLinearIsometry.toContinuousLinearMap
  let L₂ : lp D.Summand 2 →L[ℂ] Lp ℂ 2 D.measure :=
    mulL (fun p : D.Space => g p.2) (D.memLp_top_continuousMap g) ∘L
      D.unitary.toLinearIsometry.toContinuousLinearMap ∘L
        D.equiv.symm.toLinearIsometry.toContinuousLinearMap
  change L₁ w = L₂ w
  have hsum := lp.hasSum_single (E := D.Summand) (p := 2) ENNReal.ofNat_ne_top w
  refine (hsum.mapL L₁).unique ?_
  convert hsum.mapL L₂ using 1
  funext ψ
  simp only [L₁, L₂, ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
    D.equiv_symm_single]
  exact D.unitary_cfcHom_cyclicIsometry g ψ (w ψ)

/-- **`U T U⁻¹` is multiplication by the spectral variable `λ`** (Reed–Simon I, Theorem VII.3,
p. 227, and Lemma 1, p. 226). -/
theorem unitary_apply_T (h : H) :
    D.unitary (T h) = mulL D.coord D.memLp_top_coord (D.unitary h) := by
  have hT' := D.unitary_cfcHom ((ContinuousMap.id ℂ).restrict (spectrum ℂ T)) h
  rw [cfcHom_id] at hT'
  exact hT'

end CyclicDecomposition

/-- **The spectral theorem for bounded normal operators, multiplication operator form**
(Reed–Simon I, Theorem VII.3 and its Corollary, p. 227; normal case, Problem VII.5): there are a
measure space `(M, μ)`, a unitary `U : H ≃ L²(M, μ)` and a bounded measurable function `F` on
`M` such that `U T U⁻¹` is multiplication by `F`, `(U T U⁻¹ f)(m) = F(m) f(m)`.  More generally
`U g(T) U⁻¹` is multiplication by `g ∘ F` for every continuous `g` on `σ(T)`. -/
theorem exists_unitary_mulL :
    ∃ (M : Type u) (_ : MeasurableSpace M) (μ : Measure M) (U : H ≃ₗᵢ[ℂ] Lp ℂ 2 μ)
      (F : M → spectrum ℂ T) (_ : Measurable F),
      (∀ g : C(spectrum ℂ T, ℂ), ∃ hg : MemLp (fun m => g (F m)) ∞ μ,
        ∀ h : H, U (cfcHom hT g h) = mulL (fun m => g (F m)) hg (U h)) ∧
      ∃ hF : MemLp (fun m => (F m : ℂ)) ∞ μ,
        ∀ h : H, U (T h) = mulL (fun m => (F m : ℂ)) hF (U h) := by
  obtain ⟨D⟩ := CyclicDecomposition.nonempty T
  refine ⟨D.Space, inferInstance, D.measure, D.unitary, fun p => p.2,
    measurable_sigma_iff.mpr fun _ => measurable_id, fun g => ⟨D.memLp_top_continuousMap g,
      D.unitary_cfcHom g⟩, D.memLp_top_coord, D.unitary_apply_T⟩

end SpectralTheorem

