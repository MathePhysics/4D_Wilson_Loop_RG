import SpectralTheorem.ResolventSpectrum
import SpectralTheorem.MultiplicationUnbounded

/-!
# The spectral theorem for unbounded self-adjoint operators: multiplication operator form

**Reed–Simon I, Theorem VIII.4, pp. 260–261.**  Let `A` be a self-adjoint operator on a
separable Hilbert space `H` with domain `D(A)`.  Then there is a measure space `⟨M, μ⟩` with `μ`
a finite measure, a unitary operator `U : H → L²(M, dμ)`, and a real-valued function `f` on `M`
which is finite a.e. so that (a) `ψ ∈ D(A)` if and only if `f(·)(Uψ)(·) ∈ L²(M, dμ)`; (b) if
`φ ∈ U[D(A)]`, then `(U A U⁻¹ φ)(m) = f(m) φ(m)`.

Reed–Simon's proof: `R = (A + i)⁻¹` is a bounded normal operator; by the bounded spectral
theorem `U R U⁻¹` is multiplication by a bounded function `g` with `g ≠ 0` a.e.; put
`f = g⁻¹ - i`.  Here `U` is the spectral representation of `R` for a cyclic decomposition
(`SpectralTheorem.MultiplicationForm`), `g = λ` is the spectral variable, `λ ≠ 0` a.e. and
`f = λ⁻¹ - i` is real on `σ(R) \ {0}` (`SpectralTheorem.ResolventSpectrum`).  Then:

* if `ψ ∈ D(A)`, write `ψ = R φ` with `φ = (A + i) ψ`; then `U ψ = λ U φ`, so
  `f U ψ = (1 - i λ) U φ = U φ - i U ψ = U (A ψ)` a.e.;
* if `f U ψ ∈ L²`, put `φ = U⁻¹ ((f + i) U ψ)`; then `U (R φ) = λ (f + i) U ψ = U ψ`, so
  `ψ = R φ ∈ D(A)`.

`f` is real everywhere (it is `λ ↦ (λ⁻¹ - i).re`), so "finite a.e." is automatic.  No separability
is assumed; the measure `μ = Σ_ψ μ_ψ` on `Σ_ψ σ(R)` is then not finite in general.  Reed–Simon's
finite `μ` for separable `H` is `SpectralTheorem.exists_unitary_mulPMap_finite`
(`SpectralTheorem.SeparableDecomposition`).

## Main results

* `SpectralTheorem.CyclicDecomposition.realCoord`: the function `f = λ⁻¹ - i`, real-valued.
* `SpectralTheorem.CyclicDecomposition.mem_domain_iff`: (a).
* `SpectralTheorem.CyclicDecomposition.unitary_apply_selfAdjoint`: (b), with the unbounded
  multiplication operator `mulPMap μ f`.
* `SpectralTheorem.exists_unitary_mulPMap`: **Reed–Simon I, Theorem VIII.4** (without the
  finiteness of `μ`).
-/

noncomputable section

open scoped InnerProductSpace ComplexConjugate ENNReal
open MeasureTheory Filter KatoRellich

namespace SpectralTheorem

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {A : H →ₗ.[ℂ] H} {hA : IsSelfAdjoint A}

namespace CyclicDecomposition

variable (D : CyclicDecomposition (resolvent hA))

/-- The spectral variable of `R`, as a complex function, is measurable. -/
theorem measurable_coord : Measurable D.coord :=
  measurable_sigma_iff.mpr fun _ => measurable_subtype_coe

/-- **The function `f = λ⁻¹ - i`** (Reed–Simon's `g(m)⁻¹ - i`), real-valued. -/
def realCoord (p : D.Space) : ℝ :=
  resolventCoord (D.coord p)

theorem measurable_realCoord : Measurable D.realCoord :=
  measurable_resolventCoord.comp D.measurable_coord

/-- `(f + i) λ = 1` almost everywhere. -/
theorem ae_realCoord_add_I_mul :
    ∀ᵐ p ∂D.measure, ((D.realCoord p : ℂ) + Complex.I) * D.coord p = 1 := by
  filter_upwards [D.ae_coord_ne_zero hA] with p hp
  exact resolventCoord_add_I_mul hA p.2.2 hp

/-- `U (R h) = λ · U h`. -/
theorem unitary_resolvent (h : H) :
    D.unitary (resolvent hA h) = mulL D.coord D.memLp_top_coord (D.unitary h) :=
  D.unitary_apply_T h

/-- The a.e. identity `U (R h) = λ · U h`. -/
theorem coeFn_unitary_resolvent (h : H) :
    (D.unitary (resolvent hA h) : D.Space → ℂ) =ᵐ[D.measure]
      fun p => D.coord p * D.unitary h p := by
  rw [D.unitary_resolvent h]
  exact coeFn_mulL (μ := D.measure) D.memLp_top_coord _

/-- For `ψ ∈ D(A)`: `U (A ψ) = f · U ψ` almost everywhere.  With `φ = (A + i) ψ`, `ψ = R φ`, so
`U ψ = λ U φ` and `f U ψ = (1 - i λ) U φ = U φ - i U ψ = U (A ψ)`. -/
theorem coeFn_unitary_selfAdjoint (ψ : H) (hψ : ψ ∈ A.domain) :
    (D.unitary (A ⟨ψ, hψ⟩) : D.Space → ℂ) =ᵐ[D.measure]
      fun p => (D.realCoord p : ℂ) * D.unitary ψ p := by
  set φ : H := A ⟨ψ, hψ⟩ + (((1 : ℝ) : ℂ) * RCLike.I) • ψ with hφ
  have hRφ : resolvent hA φ = ψ := resolventI_addScalar hA abs_one ⟨ψ, hψ⟩
  have hAψ : A ⟨ψ, hψ⟩ = φ - Complex.I • ψ := by
    rw [hφ, Complex.ofReal_one, one_mul, RCLike.I_to_complex, add_sub_cancel_right]
  have hUψ := D.coeFn_unitary_resolvent φ
  rw [hRφ] at hUψ
  rw [hAψ, map_sub, map_smul]
  filter_upwards [Lp.coeFn_sub (D.unitary φ) (Complex.I • D.unitary ψ),
    Lp.coeFn_smul Complex.I (D.unitary ψ), hUψ, D.ae_realCoord_add_I_mul] with p h1 h2 h3 h4
  rw [h1, Pi.sub_apply, h2, Pi.smul_apply, smul_eq_mul, h3]
  linear_combination (-(D.unitary φ p)) * h4

/-- If `f · U ψ ∈ L²`, then `ψ ∈ D(A)`: with `φ = U⁻¹ ((f + i) U ψ)`,
`U (R φ) = λ (f + i) U ψ = U ψ`, so `ψ = R φ`. -/
theorem mem_domain_of_mem_mulPMap (ψ : H)
    (h : D.unitary ψ ∈ (mulPMap D.measure fun p => (D.realCoord p : ℂ)).domain) :
    ψ ∈ A.domain := by
  set w : Lp ℂ 2 D.measure :=
    mulPMap D.measure (fun p => (D.realCoord p : ℂ)) ⟨D.unitary ψ, h⟩ +
      Complex.I • D.unitary ψ with hw
  set φ : H := D.unitary.symm w
  have hkey : D.unitary (resolvent hA φ) = D.unitary ψ := by
    refine Lp.ext ?_
    have h1 := D.coeFn_unitary_resolvent φ
    rw [show D.unitary φ = w from D.unitary.apply_symm_apply w] at h1
    filter_upwards [h1, Lp.coeFn_add (mulPMap D.measure (fun p => (D.realCoord p : ℂ))
        ⟨D.unitary ψ, h⟩) (Complex.I • D.unitary ψ), Lp.coeFn_smul Complex.I (D.unitary ψ),
      coeFn_mulPMap (μ := D.measure) ⟨D.unitary ψ, h⟩, D.ae_realCoord_add_I_mul]
      with p h1 h2 h3 h4 h5
    rw [h1, hw, h2, Pi.add_apply, h3, Pi.smul_apply, smul_eq_mul, h4]
    linear_combination (D.unitary ψ p) * h5
  have hR : resolvent hA φ = ψ := D.unitary.injective hkey
  rw [← hR]
  exact resolventI_mem_domain hA abs_one φ

/-- **Reed–Simon I, Theorem VIII.4 (a)**: `ψ ∈ D(A)` if and only if `f · U ψ ∈ L²`, i.e.
`U ψ` is in the domain of multiplication by `f`. -/
theorem mem_domain_iff (ψ : H) :
    ψ ∈ A.domain ↔ D.unitary ψ ∈ (mulPMap D.measure fun p => (D.realCoord p : ℂ)).domain :=
  ⟨fun hψ => mem_mulPMap_domain_of_ae_eq (D.coeFn_unitary_selfAdjoint ψ hψ),
    D.mem_domain_of_mem_mulPMap ψ⟩

/-- **Reed–Simon I, Theorem VIII.4 (b)**: `U A U⁻¹` is multiplication by `f` on `U[D(A)]`. -/
theorem unitary_apply_selfAdjoint (ψ : H) (hψ : ψ ∈ A.domain) :
    D.unitary (A ⟨ψ, hψ⟩) =
      mulPMap D.measure (fun p => (D.realCoord p : ℂ)) ⟨D.unitary ψ, (D.mem_domain_iff ψ).mp hψ⟩ :=
  (mulPMap_apply_of_ae_eq (D.coeFn_unitary_selfAdjoint ψ hψ)).symm

end CyclicDecomposition

/-- **The spectral theorem for unbounded self-adjoint operators, multiplication operator form**
(Reed–Simon I, Theorem VIII.4, pp. 260–261): there are a measure space `(M, μ)`, a unitary
`U : H ≃ L²(M, μ)` and a real-valued measurable function `f` on `M` such that (a)
`ψ ∈ D(A) ↔ f · U ψ ∈ L²(M, μ)`, and (b) `U (A ψ) = f · U ψ` for `ψ ∈ D(A)`.  Reed–Simon also
take `μ` finite, for separable `H`: `exists_unitary_mulPMap_finite`. -/
theorem exists_unitary_mulPMap (hA : IsSelfAdjoint A) :
    ∃ (M : Type u) (_ : MeasurableSpace M) (μ : Measure M) (U : H ≃ₗᵢ[ℂ] Lp ℂ 2 μ)
      (f : M → ℝ), Measurable f ∧
      (∀ ψ : H, ψ ∈ A.domain ↔ MemLp (fun m => (f m : ℂ) * U ψ m) 2 μ) ∧
      ∀ (ψ : H) (hψ : ψ ∈ A.domain),
        (U (A ⟨ψ, hψ⟩) : M → ℂ) =ᵐ[μ] fun m => (f m : ℂ) * U ψ m := by
  obtain ⟨D⟩ := CyclicDecomposition.nonempty (resolvent hA)
  exact ⟨D.Space, inferInstance, D.measure, D.unitary, D.realCoord, D.measurable_realCoord,
    D.mem_domain_iff, D.coeFn_unitary_selfAdjoint⟩

end SpectralTheorem
