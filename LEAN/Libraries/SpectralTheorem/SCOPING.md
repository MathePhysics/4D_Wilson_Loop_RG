# Scoping: the spectral theorem for self-adjoint operators

Target: the three forms of the spectral theorem for **unbounded self-adjoint operators** in
Reed–Simon I (1972), §VIII.3, together with their bounded counterparts in Chapter VII, on top of
mathlib `8d52ea9a` (Lean `v4.34.0-rc2`).  All statements below were checked on page images of
Reed–Simon I on 2026-09-21.

## What mathlib already has

* **Continuous functional calculus.**  `E →L[ℂ] E` is a `CStarAlgebra`
  (`Analysis/CStarAlgebra/ContinuousLinearMap.lean`), so `cfcHom : C(σ(T), ℂ) →⋆ₐ[ℂ] (E →L[ℂ] E)`
  exists for every bounded normal `T`.  This is Reed–Simon's Theorem VII.1 (p. 222), for normal
  operators.
* **Riesz–Markov–Kakutani** for positive functionals on `C_c(X, ℝ)`, giving a regular measure
  (`RealRMK.rieszMeasure`, `integral_rieszMeasure`, uniqueness).
* **`L²` density of continuous functions** for finite weakly regular measures
  (`ContinuousMap.toLp_denseRange`), Hilbert sums (`IsHilbertSum`, `lp`), Hölder products on `Lᵖ`,
  vector measures.
* Finite-dimensional and compact self-adjoint spectral theorems (not used).
* **Not in mathlib:** Borel functional calculus, spectral measures, projection-valued measures,
  multiplication operators on `L²`, anything for unbounded operators.

## Target statements (Reed–Simon I)

| Result | Page | Content |
|---|---|---|
| Theorem VII.2 | 225 | bounded Borel functional calculus: unique `*`-homomorphism `𝓑(ℝ) → 𝓛(H)`, norm-continuous, `x ↦ A`, bounded pointwise limits go to strong limits; (e)–(g) |
| Theorem VII.3 | 227 | multiplication operator form, bounded self-adjoint `A`, separable `H`: `U : H → ⊕ₙ L²(ℝ, dμₙ)` unitary, `(UAU⁻¹ψ)ₙ(λ) = λψₙ(λ)`; corollary: one finite measure space |
| Definition, p.v.m. | 234–235 | `P_Ω` orthogonal projections, `P_∅ = 0`, `P_(−a,a) = I`, strong countable additivity, `P_Ω₁ P_Ω₂ = P_(Ω₁∩Ω₂)` |
| Theorems VII.7, VII.8 | 235 | `∫ f dP` for bounded Borel `f`; bijection between bounded self-adjoint operators and bounded p.v.m.'s |
| Proposition VIII.3.1 | 259 | multiplication by a real measurable `f` finite a.e. on `L²(M, μ)`, `μ` finite, is self-adjoint on `{φ : fφ ∈ L²}` |
| Theorem VIII.4 | 260–261 | multiplication operator form for unbounded self-adjoint `A`, separable `H`: finite `⟨M, μ⟩`, unitary `U : H → L²(M, μ)`, real `f` finite a.e., `ψ ∈ D(A) ⟺ f·Uψ ∈ L²`, `UAU⁻¹φ = fφ` |
| Theorem VIII.5 | 262 | functional calculus for unbounded self-adjoint `A`: unique `φ̂ : 𝓑(ℝ) → 𝓛(H)` with (a) `*`-homomorphism, (b) `‖φ̂(h)‖ ≤ ‖h‖∞`, (c) `hₙ → x`, `|hₙ| ≤ |x|` ⟹ `φ̂(hₙ)ψ → Aψ` on `D(A)`, (d) bounded pointwise limits go to strong limits; (e), (f) |
| Theorem VIII.6 | 263–264 | p.v.m. form: bijection between self-adjoint operators and p.v.m.'s on `ℝ`, `A = ∫ λ dP_λ`; `g(A)` for unbounded Borel `g` on `D_g = {φ : ∫ |g|² d(φ, P_λ φ) < ∞}` |

Reed–Simon prove the unbounded case (VIII.4) by applying the bounded **normal** case to
`(A + i)⁻¹` (p. 261), whose proof they leave to Problems VII.3–5.  We therefore work with bounded
normal operators throughout; mathlib's `cfcHom` covers them directly.

## Design decisions

1. **Scalars: complex Hilbert spaces** (`[InnerProductSpace ℂ H] [CompleteSpace H]`), as in
   Reed–Simon.  Real Hilbert spaces (needed by `FiniteVolumeYM2Phi42`) are a later milestone,
   through the complexification.
2. **Operators:** bounded ones are `H →L[ℂ] H`; unbounded ones are `H →ₗ.[ℂ] H` with
   `IsSelfAdjoint` meaning `T† = T`, as in `KatoRellich`.  `KatoRellich` may be imported for
   `IsSymmetric`, the basic criterion and `Ran(A ± i) = H`.
3. **Measures:** the spectral measure of `ψ` for a bounded normal `T` is
   `RealRMK.rieszMeasure` of `f ↦ re ⟪ψ, f(T) ψ⟫` on the compact space `σ(T) ⊆ ℂ`.
4. **One measure space.**  Instead of `⊕ₙ L²(μₙ)`, use a single `L²(X, μ)`: for a family of
   cyclic vectors `(ψᵢ)ᵢ∈I`, `X = Σ i, σ(T)` with `μ = Σᵢ μ_ψᵢ`.  Every operator in the
   development is then a multiplication operator on one `L²` space.  For separable `H`, `I` is
   countable and the `ψᵢ` can be scaled so that `μ` is finite, which is Reed–Simon's form of
   VIII.4.  Without separability the theorem still holds with this (non-finite) `μ`.
5. **Uniqueness of the functional calculus** (VII.2, VIII.5) by a monotone-class argument: two
   calculi agree on continuous functions (uniqueness of the continuous functional calculus), and
   the functions on which they agree are closed under bounded pointwise limits.
6. **Hygiene** as in the sibling libraries: no `sorry`, `admit`, axioms or `set_option`
   overrides; no warnings; lines ≤ 100 characters; totalisation audit clean.

## Milestones

| # | Module | Content | Source | Estimate |
|---|---|---|---|---|
| M1 | `SpectralMeasure` | spectral measure `μ_ψ` of a bounded normal `T`; `∫ f dμ_ψ = ⟪ψ, f(T)ψ⟫` for continuous `f`; `μ_ψ(σ(T)) = ‖ψ‖²` | VII.2, pp. 224–225 | 250–400 |
| M2 | `MultiplicationOperator` | bounded multiplication by `g ∈ L∞` on `L²`; adjoint, `*`-homomorphism, strong continuity under bounded pointwise convergence; unbounded `T_f` on `{φ : fφ ∈ L²}`, adjoint `T_f† = T_{f̄}`, self-adjoint for real `f` | VIII.3 Prop. 1, pp. 259–260 | 500–800 |
| M3 | `Cyclic` | cyclic subspace of `ψ`; unitary `L²(σ(T), μ_ψ) ≅ H_ψ` with `T ↦` multiplication by `z` | VII.2 Lemma 1, p. 226 | 300–500 |
| M4 | `Decomposition` | orthogonal decomposition into cyclic subspaces (Zorn); unitary `U : H ≃ L²(X, μ)` with `UTU⁻¹ = ` multiplication by a bounded function; finite `μ` for separable `H` | VII.2 Lemma 2, VII.3, pp. 226–227 | 500–800 |
| M5 | `BorelCalculus` | bounded Borel calculus `g(T) = U⁻¹ M_{g∘F} U` for bounded normal `T`; VII.2 (a)–(g); uniqueness; independence of `U` | VII.2, p. 225 | 600–900 |
| M6 | `ProjectionValuedMeasure` | p.v.m.'s, `∫ f dP` for bounded `f`, spectral projections, VII.7–VII.8 | pp. 234–235 | 500–800 |
| M7 | `Unbounded` | `(A + i)⁻¹` bounded normal with trivial kernel; VIII.4 | pp. 260–261 | 500–700 |
| M8 | `UnboundedCalculus` | VIII.5 (a)–(f) and uniqueness | p. 262 | 500–800 |
| M9 | `UnboundedPVM` | `g(A)` for unbounded Borel `g` on `D_g`; VIII.6 bijection | pp. 262–264 | 600–900 |
| M10 | `Real` | real Hilbert spaces by complexification | — | open |
| M12 | `VonNeumann`, `Normal*` | von Neumann's theorem on `1 + T†T`; unbounded normal operators and their p.v.m. | Rudin, *Functional Analysis*, Ch. 13; R–S II, Thm X.25 | 1,500–2,500 |
| M11 | `Rep*`, `Comm*` | representations of `C(X)`; commutative C*-algebras of operators (Gelfand); joint spectral theorem for commuting families | Rudin, *Functional Analysis*, Ch. 12 | 2,000–3,000 |

Progress (2026-09-22, v0.6): all milestones M1–M12 done.  See `STATUS.md`.

Total estimate: 4,500–7,000 lines.  M1 and M2 are independent; M3 needs M1; M4 needs M2 and M3;
M5–M9 are sequential.
