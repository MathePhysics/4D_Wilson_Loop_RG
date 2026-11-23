import SpectralTheorem.UnboundedMultiplicationForm
import SpectralTheorem.BorelCalculusProperties

/-!
# The functional calculus of an unbounded self-adjoint operator

**Reed–Simon I, Theorem VIII.5 (spectral theorem, functional calculus form), p. 262.**  Let `A` be
a self-adjoint operator on `H`.  Then there is a unique map `φ̂` from the bounded Borel functions
on `ℝ` into `𝓛(H)` so that (a) `φ̂` is an algebraic `⋆`-homomorphism; (b) `φ̂` is norm continuous,
`‖φ̂(h)‖ ≤ ‖h‖∞`; (c) if `hₙ(x) → x` for each `x` and `|hₙ(x)| ≤ |x|` for all `x` and `n`, then
`φ̂(hₙ) ψ → A ψ` for `ψ ∈ D(A)`; (d) if `hₙ(x) → h(x)` pointwise and `‖hₙ‖∞` is bounded, then
`φ̂(hₙ) → φ̂(h)` strongly.  In addition (e) if `A ψ = λ ψ`, then `φ̂(h) ψ = h(λ) ψ`; (f) if
`h ≥ 0`, then `φ̂(h) ≥ 0`.

Construction: with `R = (A + i)⁻¹` (bounded, normal, `SpectralTheorem.ResolventSpectrum`) put
`h(A) = (h ∘ ρ)(R)`, where `ρ(z) = (z⁻¹ - i).re` maps `σ(R) \ {0}` onto the corresponding real
numbers, and `(·)(R)` is the Borel calculus of `R` (`SpectralTheorem.borelCalc`).  In the
multiplication form of `A` (`SpectralTheorem.UnboundedMultiplicationForm`) this is
multiplication by `h ∘ f`, `f = λ⁻¹ - i` (Reed–Simon's definition `h(A) = U⁻¹ T_{h(f)} U`, p. 261).
Uniqueness is proved in `SpectralTheorem.UnboundedCalculusUnique`.

## Main definitions and results

* `SpectralTheorem.selfAdjointCalc hA`: `h ↦ h(A)`, a `⋆`-homomorphism, i.e. (a).
* `SpectralTheorem.norm_selfAdjointCalc_le`: (b).
* `SpectralTheorem.tendsto_selfAdjointCalc_apply_self`: (c).
* `SpectralTheorem.tendsto_selfAdjointCalc_apply`: (d).
* `SpectralTheorem.selfAdjointCalc_apply_of_eigen`: (e).
* `SpectralTheorem.selfAdjointCalc_nonneg`: (f).
* `SpectralTheorem.selfAdjointCalc_apply`: `U (h(A) ψ) = h(f) · U ψ`.
-/

noncomputable section

open scoped InnerProductSpace ComplexConjugate ENNReal Topology ComplexOrder
open MeasureTheory Filter KatoRellich

namespace SpectralTheorem

universe u

/-- Composition with a measurable map, as a `⋆`-homomorphism of bounded measurable functions. -/
def boundedMeasurable.comap {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (F : X → Y)
    (hF : Measurable F) : boundedMeasurable Y →⋆ₐ[ℂ] boundedMeasurable X where
  toFun g := ⟨(g : Y → ℂ) ∘ F, (boundedMeasurable.measurable g).comp hF, by
    obtain ⟨C, hC⟩ := g.2.2
    exact ⟨C, fun x => hC (F x)⟩⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

@[simp]
theorem boundedMeasurable.coe_comap {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (F : X → Y) (hF : Measurable F) (g : boundedMeasurable Y) :
    ((boundedMeasurable.comap F hF g : boundedMeasurable X) : X → ℂ) = (g : Y → ℂ) ∘ F :=
  rfl

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)

/-- The map `σ(R) → ℝ`, `z ↦ (z⁻¹ - i).re`. -/
def spectrumToReal (z : spectrum ℂ (resolvent hA)) : ℝ :=
  resolventCoord z

theorem measurable_spectrumToReal : Measurable (spectrumToReal hA) :=
  measurable_resolventCoord.comp measurable_subtype_coe

/-- **The functional calculus of the self-adjoint operator `A`** (Reed–Simon I, Theorem VIII.5,
p. 262): `h(A) = (h ∘ ρ)((A + i)⁻¹)` for bounded Borel `h : ℝ → ℂ`, with `ρ(z) = (z⁻¹ - i).re`.
It is a `⋆`-homomorphism by construction, which is (a). -/
def selfAdjointCalc : boundedMeasurable ℝ →⋆ₐ[ℂ] (H →L[ℂ] H) :=
  (borelCalc (resolvent hA)).comp
    (boundedMeasurable.comap (spectrumToReal hA) (measurable_spectrumToReal hA))

theorem selfAdjointCalc_def (h : boundedMeasurable ℝ) :
    selfAdjointCalc hA h = borelCalc (resolvent hA)
      (boundedMeasurable.comap (spectrumToReal hA) (measurable_spectrumToReal hA) h) :=
  rfl

/-- (b) `‖h(A)‖ ≤ C` when `‖h(x)‖ ≤ C` for all `x`. -/
theorem norm_selfAdjointCalc_le (h : boundedMeasurable ℝ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x, ‖(h : ℝ → ℂ) x‖ ≤ C) : ‖selfAdjointCalc hA h‖ ≤ C :=
  norm_borelCalc_le _ hC0 fun _ => hC _

/-- (d) If `hₙ → h` pointwise with `‖hₙ‖ ≤ C`, then `hₙ(A) ψ → h(A) ψ`. -/
theorem tendsto_selfAdjointCalc_apply (h : ℕ → boundedMeasurable ℝ) (h₀ : boundedMeasurable ℝ)
    (C : ℝ) (hC : ∀ n x, ‖(h n : ℝ → ℂ) x‖ ≤ C)
    (hlim : ∀ x, Tendsto (fun n => (h n : ℝ → ℂ) x) atTop (𝓝 ((h₀ : ℝ → ℂ) x))) (ψ : H) :
    Tendsto (fun n => selfAdjointCalc hA (h n) ψ) atTop (𝓝 (selfAdjointCalc hA h₀ ψ)) :=
  tendsto_borelCalc_apply _ _ C (fun n _ => hC n _) (fun _ => hlim _) ψ

/-- **`h(A)` in the multiplication form**: `h(A) ψ = U⁻¹ (h(f) · U ψ)`, where `U` and
`f = λ⁻¹ - i` come from any cyclic decomposition of `R` (Reed–Simon I, p. 261). -/
theorem selfAdjointCalc_apply (D : CyclicDecomposition (resolvent hA))
    (h : boundedMeasurable ℝ) (ψ : H) :
    selfAdjointCalc hA h ψ = D.unitary.symm (mulL (fun p => (h : ℝ → ℂ) (D.realCoord p))
      (memLp_top_comp D.measure D.measurable_snd
        (boundedMeasurable.comap (spectrumToReal hA) (measurable_spectrumToReal hA) h))
      (D.unitary ψ)) := by
  rw [selfAdjointCalc_def, borelCalc_apply D]
  rfl

end SpectralTheorem
