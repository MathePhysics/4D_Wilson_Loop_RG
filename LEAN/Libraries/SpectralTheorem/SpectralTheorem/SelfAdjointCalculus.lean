import SpectralTheorem.UnboundedCalculusProperties
import SpectralTheorem.UnboundedCalculusUnique

/-!
# The spectral theorem for self-adjoint operators, functional calculus form

**Reed–Simon I, Theorem VIII.5, p. 262.**  Let `A` be a self-adjoint operator on `H`.  Then there
is a unique map `φ̂` from the bounded Borel functions on `ℝ` into `𝓛(H)` so that (a) `φ̂` is an
algebraic `⋆`-homomorphism; (b) `‖φ̂(h)‖ ≤ ‖h‖∞`; (c) if `hₙ(x) → x` for each `x` and
`|hₙ(x)| ≤ |x|` for all `x` and `n`, then `φ̂(hₙ) ψ → A ψ` for `ψ ∈ D(A)`; (d) if `hₙ(x) → h(x)`
pointwise and `‖hₙ‖∞` is bounded, then `φ̂(hₙ) → φ̂(h)` strongly.  In addition (e) if
`A ψ = λ ψ`, then `φ̂(h) ψ = h(λ) ψ`; (f) if `h ≥ 0`, then `φ̂(h) ≥ 0`.

This file puts together the existence (`SpectralTheorem.UnboundedCalculus`,
`SpectralTheorem.UnboundedCalculusProperties`) and the uniqueness
(`SpectralTheorem.UnboundedCalculusUnique`).  Properties (e) and (f) are
`SpectralTheorem.selfAdjointCalc_apply_of_eigen` and `SpectralTheorem.selfAdjointCalc_nonneg`.

## Main results

* `SpectralTheorem.isSelfAdjointCalculus_selfAdjointCalc`: `selfAdjointCalc hA` has (a)–(d).
* `SpectralTheorem.existsUnique_isSelfAdjointCalculus`: **Reed–Simon I, Theorem VIII.5** (a)–(d).
-/

noncomputable section

namespace SpectralTheorem

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)

/-- `h ↦ h(A)` has properties (b)–(d) of Theorem VIII.5; (a) holds by construction. -/
theorem isSelfAdjointCalculus_selfAdjointCalc : IsSelfAdjointCalculus hA (selfAdjointCalc hA) where
  norm_le h _ hC0 hC := norm_selfAdjointCalc_le hA h hC0 hC
  tendsto_self h hb hl ψ hψ := tendsto_selfAdjointCalc_apply_self hA h hb hl ψ hψ
  tendsto h h₀ C hC hl ψ := tendsto_selfAdjointCalc_apply hA h h₀ C hC hl ψ

/-- **The spectral theorem for self-adjoint operators, functional calculus form** (Reed–Simon I,
Theorem VIII.5 (a)–(d), p. 262): there is exactly one `⋆`-homomorphism from the bounded Borel
functions on `ℝ` to `𝓛(H)` with (b)–(d), namely `selfAdjointCalc hA`. -/
theorem existsUnique_isSelfAdjointCalculus :
    ∃! Φ : boundedMeasurable ℝ →⋆ₐ[ℂ] (H →L[ℂ] H), IsSelfAdjointCalculus hA Φ :=
  ⟨selfAdjointCalc hA, isSelfAdjointCalculus_selfAdjointCalc hA,
    fun _ hΦ => hΦ.eq_selfAdjointCalc⟩

end SpectralTheorem
