import SpectralTheorem.UnboundedCalculus

/-!
# Properties (c), (e), (f) of the functional calculus of a self-adjoint operator

Reed–Simon I, Theorem VIII.5, p. 262, for `h(A) = selfAdjointCalc hA h`
(`SpectralTheorem.UnboundedCalculus`):

* (c) if `hₙ(x) → x` for each `x` and `|hₙ(x)| ≤ |x|` for all `x` and `n`, then `hₙ(A) ψ → A ψ`
  for `ψ ∈ D(A)`.  In the multiplication form, `U (hₙ(A) ψ) = hₙ(f) · U ψ` and
  `U (A ψ) = f · U ψ`; the convergence is dominated convergence in `L²` on the domain of
  multiplication by `f` (`tendsto_mulL_apply_mulPMap`).
* (e) if `A ψ = λ ψ`, then `h(A) ψ = h(λ) ψ`: `R ψ = (λ + i)⁻¹ ψ`, and (e) for the Borel calculus
  of `R` applies with `ρ((λ + i)⁻¹) = λ`.
* (f) if `h ≥ 0`, then `h(A) ≥ 0`, from (f) for the Borel calculus of `R`.

## Main results

* `SpectralTheorem.tendsto_selfAdjointCalc_apply_self`: (c).
* `SpectralTheorem.selfAdjointCalc_apply_of_eigen`: (e).
* `SpectralTheorem.selfAdjointCalc_nonneg`, `SpectralTheorem.isPositive_selfAdjointCalc`: (f).
-/

noncomputable section

open scoped InnerProductSpace ComplexConjugate ENNReal Topology ComplexOrder
open MeasureTheory Filter KatoRellich

namespace SpectralTheorem

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)

/-- (c) **`hₙ(A) ψ → A ψ`** for `ψ ∈ D(A)` when `hₙ(x) → x` and `|hₙ(x)| ≤ |x|` (Reed–Simon I,
Theorem VIII.5 (c), p. 262). -/
theorem tendsto_selfAdjointCalc_apply_self (h : ℕ → boundedMeasurable ℝ)
    (hbound : ∀ n x, ‖(h n : ℝ → ℂ) x‖ ≤ |x|)
    (hlim : ∀ x, Tendsto (fun n => (h n : ℝ → ℂ) x) atTop (𝓝 (x : ℂ)))
    (ψ : H) (hψ : ψ ∈ A.domain) :
    Tendsto (fun n => selfAdjointCalc hA (h n) ψ) atTop (𝓝 (A ⟨ψ, hψ⟩)) := by
  obtain ⟨D⟩ := CyclicDecomposition.nonempty (resolvent hA)
  simp only [selfAdjointCalc_apply hA D]
  have hAψ : A ⟨ψ, hψ⟩ = D.unitary.symm (mulPMap D.measure (fun p => (D.realCoord p : ℂ))
      ⟨D.unitary ψ, (D.mem_domain_iff ψ).mp hψ⟩) := by
    rw [← D.unitary_apply_selfAdjoint ψ hψ, LinearIsometryEquiv.symm_apply_apply]
  rw [hAψ]
  refine (D.unitary.symm.continuous.tendsto _).comp ?_
  have hb : ∀ n, ∀ᵐ p ∂D.measure,
      ‖(h n : ℝ → ℂ) (D.realCoord p)‖ ≤ ‖((D.realCoord p : ℝ) : ℂ)‖ := fun n =>
    Eventually.of_forall fun p => by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact hbound n _
  have hl : ∀ᵐ p ∂D.measure,
      Tendsto (fun n => (h n : ℝ → ℂ) (D.realCoord p)) atTop (𝓝 ((D.realCoord p : ℝ) : ℂ)) :=
    Eventually.of_forall fun p => hlim _
  exact tendsto_mulL_apply_mulPMap (μ := D.measure)
    (fun n => memLp_top_comp D.measure D.measurable_snd
      (boundedMeasurable.comap (spectrumToReal hA) (measurable_spectrumToReal hA) (h n)))
    hb hl ⟨D.unitary ψ, (D.mem_domain_iff ψ).mp hψ⟩

/-- If `A ψ = λ ψ`, then `R ψ = (λ + i)⁻¹ ψ`. -/
theorem resolvent_apply_of_eigen {ψ : H} (hψ : ψ ∈ A.domain) {l : ℝ}
    (heig : A ⟨ψ, hψ⟩ = (l : ℂ) • ψ) :
    resolvent hA ψ = ((l : ℂ) + Complex.I)⁻¹ • ψ := by -- totalisation-audit: allow l + i ≠ 0
  have hne : (l : ℂ) + Complex.I ≠ 0 := fun h => by simpa using congrArg Complex.im h
  have h1 := resolventI_addScalar hA abs_one ⟨ψ, hψ⟩
  have hsum : A ⟨ψ, hψ⟩ + (((1 : ℝ) : ℂ) * RCLike.I) • ψ = ((l : ℂ) + Complex.I) • ψ := by
    rw [heig, Complex.ofReal_one, one_mul, RCLike.I_to_complex, add_smul]
  change resolventI hA 1 abs_one (A ⟨ψ, hψ⟩ + (((1 : ℝ) : ℂ) * RCLike.I) • ψ) = ψ at h1
  rw [hsum, map_smul] at h1
  change resolventI hA 1 abs_one ψ = _
  calc resolventI hA 1 abs_one ψ
      = ((l : ℂ) + Complex.I)⁻¹ • -- totalisation-audit: allow l + i ≠ 0
          (((l : ℂ) + Complex.I) • resolventI hA 1 abs_one ψ) := by
        rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
    _ = ((l : ℂ) + Complex.I)⁻¹ • ψ := by rw [h1] -- totalisation-audit: allow l + i ≠ 0

/-- (e) **Eigenvectors**: if `A ψ = λ ψ`, then `h(A) ψ = h(λ) ψ` (Reed–Simon I, Theorem VIII.5 (e),
p. 262). -/
theorem selfAdjointCalc_apply_of_eigen (h : boundedMeasurable ℝ) {ψ : H} (hψ : ψ ∈ A.domain)
    {l : ℝ} (heig : A ⟨ψ, hψ⟩ = (l : ℂ) • ψ) : selfAdjointCalc hA h ψ = (h : ℝ → ℂ) l • ψ := by
  by_cases h0 : ψ = 0
  · subst h0
    simp
  have hR := resolvent_apply_of_eigen hA hψ heig
  have hc := mem_spectrum_of_apply_eq_smul h0 hR
  rw [selfAdjointCalc_def, borelCalc_apply_of_apply_eq_smul _ ⟨_, hc⟩ hR]
  congr 1
  change (h : ℝ → ℂ) (resolventCoord ((l : ℂ) + Complex.I)⁻¹) = _ -- totalisation-audit: allow ≠ 0
  simp [resolventCoord]

/-- (f) **`h ≥ 0` implies `h(A) ≥ 0`** (Reed–Simon I, Theorem VIII.5 (f), p. 262). -/
theorem selfAdjointCalc_nonneg {h : boundedMeasurable ℝ} (hh : ∀ x, 0 ≤ (h : ℝ → ℂ) x) :
    0 ≤ selfAdjointCalc hA h :=
  borelCalc_nonneg fun _ => hh _

/-- (f), as positivity of the operator. -/
theorem isPositive_selfAdjointCalc {h : boundedMeasurable ℝ} (hh : ∀ x, 0 ≤ (h : ℝ → ℂ) x) :
    (selfAdjointCalc hA h).IsPositive :=
  ContinuousLinearMap.nonneg_iff_isPositive.mp (selfAdjointCalc_nonneg hA hh)

end SpectralTheorem
