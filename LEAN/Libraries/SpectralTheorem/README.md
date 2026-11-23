# SpectralTheorem v0.6

The spectral theorem for normal and self-adjoint operators on complex Hilbert spaces, following
Reed–Simon I, Chapters VII–VIII, on top of mathlib `8d52ea9a` (Lean `v4.34.0-rc2`) and the sibling
library `KatoRellich`, with a transfer to real Hilbert spaces and the commutative C*-algebra
form.  No `sorry`, `admit`, axioms or
option overrides; every module compiles without warnings, and the 191 declarations in
`checks/Axioms.lean` depend only on `propext`, `Classical.choice` and `Quot.sound`.

**Status.**  All milestones of `SCOPING.md` are done.  The three forms of the spectral theorem
(multiplication operator, functional calculus, projection-valued measure) are complete for
bounded normal operators (Theorems VII.2, VII.3, VII.7, VII.8) and for unbounded self-adjoint
operators (Theorems VIII.4, VIII.5, VIII.6, with `g(A)` for unbounded Borel `g`); so are, for
self-adjoint operators on real Hilbert spaces, the multiplication operator form and the
functional calculus, through the complexification; and so are the spectral theorem for a
representation of `C(X)` on a compact Hausdorff space, for a commutative C*-algebra of operators,
and the joint spectral theorem for a commuting family (M11); and so is the spectral theorem for
an arbitrary unbounded **normal** operator (M12), which needs von Neumann's theorem on
`1 + T†T`.  See `STATUS.md` for the deviations from Reed–Simon.

## Main results

**`SpectralTheorem.exists_unitary_mulL`** (Reed–Simon I, Theorem VII.3 and its Corollary,
p. 227, for normal operators): for a bounded normal `T` on any complex Hilbert space `H` there
are a measure space `(M, μ)`, a unitary `U : H ≃ₗᵢ[ℂ] L²(M, μ)` and a bounded measurable
`F : M → σ(T)` such that `U T U⁻¹` is multiplication by `F`, and `U g(T) U⁻¹` is multiplication
by `g ∘ F` for every continuous `g` on `σ(T)`.  Reed–Simon assume `A` self-adjoint and `H`
separable; neither is needed here.  The measure space is `M = Σ_ψ σ(T)` over a cyclic
decomposition, with `μ = Σ_ψ μ_ψ`.

**`SpectralTheorem.existsUnique_isBorelCalculus`** (Reed–Simon I, Theorem VII.2, p. 225, for
normal operators): there is a unique `⋆`-homomorphism `borelCalc T` from bounded Borel functions
on `σ(T)` to `𝓛(H)` with (b) `‖g(T)‖ ≤ ‖g‖∞`, (c) `(λ ↦ λ)(T) = T`, and (d) bounded pointwise
convergence goes to strong convergence.  It extends mathlib's continuous functional calculus,
does not depend on the cyclic decomposition, and satisfies (e) `g(T) ψ = g(λ) ψ` for eigenvectors,
(f) `g ≥ 0 ⟹ g(T) ≥ 0`, (g) commutation with every `B` commuting with `T` and `T†`, and
`⟪ψ, g(T) ψ⟫ = ∫ g dμ_ψ`.  The spectral projections `P_Ω = χ_Ω(T)` satisfy Reed–Simon's
Proposition on p. 234: they are orthogonal projections, `P_∅ = 0`, `P_Ω = I` for `Ω ⊇ σ(T)`,
`P_Ω₁ P_Ω₂ = P_{Ω₁∩Ω₂}`, strong countable additivity, and `⟪ψ, P_Ω ψ⟫ = μ_ψ(Ω)`.

Reed–Simon state Theorem VII.2 for functions on `ℝ` with `φ̂(x) = A`; since `x ↦ x` is not
bounded on `ℝ`, the statement is read here with functions on `σ(T)`, where only their values
matter.

For separable `H`, **`SpectralTheorem.exists_unitary_mulL_finite`** gives Theorem VII.3 with a
finite measure, as Reed–Simon state it (cyclic vectors of norm `2⁻ⁿ`).

**`SpectralTheorem.exists_unitary_mulPMap`** (Reed–Simon I, Theorem VIII.4, pp. 260–261): for a
self-adjoint `A` there are a measure space `(M, μ)`, a unitary `U : H ≃ₗᵢ[ℂ] L²(M, μ)` and a
measurable `f : M → ℝ` such that `ψ ∈ D(A) ↔ f · U ψ ∈ L²` and `U A ψ = f · U ψ`.  As in
Reed–Simon, it comes from the multiplication form of `R = (A + i)⁻¹`, with `f = λ⁻¹ − i`; that
`f` is real and `λ ≠ 0` a.e. is proved from the circle `|z|² + Im z = 0` containing `σ(R)` and
from `χ_{0}(R) = 0`.  For separable `H`, **`exists_unitary_mulPMap_finite`** adds that `μ` is
finite, which is Reed–Simon's statement.

**`SpectralTheorem.existsUnique_isSelfAdjointCalculus`** (Reed–Simon I, Theorem VIII.5, p. 262):
there is a unique `⋆`-homomorphism `selfAdjointCalc hA` from bounded Borel functions on `ℝ` to
`𝓛(H)` with (b) `‖h(A)‖ ≤ ‖h‖∞`, (c) `hₙ(A) ψ → A ψ` for `ψ ∈ D(A)` when `hₙ(x) → x` with
`|hₙ(x)| ≤ |x|`, and (d) bounded pointwise convergence goes to strong convergence.  It also
satisfies (e) `h(A) ψ = h(λ) ψ` for eigenvectors and (f) `h ≥ 0 ⟹ h(A) ≥ 0`.  The construction is
`h(A) = (h ∘ ρ)(R)` with `ρ(z) = (z⁻¹ − i).re`.  Reed–Simon leave the uniqueness to the reader;
here it is reduced to the uniqueness of the continuous functional calculus of `R` on the circle,
followed by the monotone class theorem.

**Projection-valued measures** (Reed–Simon I, pp. 234–235, 263): `ProjectionValuedMeasure X H`
on any measurable space, with (d) `P_Ω₁ P_Ω₂ = P_{Ω₁∩Ω₂}` derived from (a)–(c) (Problem VII.22),
the measures `(ψ, P_Ω ψ)`, and **Theorem VII.7** (`existsUnique_inner_integral`): for bounded
Borel `f` there is a unique operator `∫ f dP` with `(ψ, (∫ f dP) ψ) = ∫ f d(ψ, P ψ)`; `P.integral`
is a `⋆`-homomorphism taking bounded pointwise limits to strong limits.

**`SpectralTheorem.spectralPVMEquiv`** (Reed–Simon I, Theorem VII.8, p. 235, for normal
operators): `T ↦ {χ_Ω(T)}` is a bijection from bounded normal operators to bounded p.v.m.'s on
`ℂ`, with inverse `P ↦ ∫ λ dP_λ`; `f(T) = ∫ f dP` (Problem 23), and `σ(T)` is the support of `P`.
**`selfAdjointPVMEquiv`** is Reed–Simon's statement: bounded self-adjoint operators correspond to
bounded p.v.m.'s on `ℝ`.

**`SpectralTheorem.borelPMap`** (Reed–Simon I, pp. 263–264): `g(A)` for an unbounded Borel
`g : ℝ → ℂ`, on `D_g = {ψ | ∫ |g|² dμ_ψ < ∞}` (dense), with `(ψ, g(A) ψ) = ∫ g dμ_ψ`,
`g(A)† = ḡ(A)`, self-adjoint for real `g`, `h(A)` of Theorem VIII.5 for bounded `h`, and `A` for
`g(λ) = λ`.  The same for any p.v.m. (`ProjectionValuedMeasure.integralPMap`).

**`SpectralTheorem.selfAdjointEquivPVM`** (Reed–Simon I, Theorem VIII.6, pp. 263–264): a
bijection between self-adjoint operators and p.v.m.'s on `ℝ`, `A = ∫ λ dP_λ`.

**Real Hilbert spaces.**  `Complexification E` is the complexification `E ⊕ i E` of a real
Hilbert space as a complex Hilbert space, with the complexification of bounded and unbounded
operators (adjoints, self-adjointness, positivity) and descent of operators commuting with the
conjugation.  **`SpectralTheorem.existsUnique_isRealSelfAdjointCalculus`**: Theorem VIII.5 for a
self-adjoint `A : E →ₗ.[ℝ] E` on a real Hilbert space, with real bounded Borel functions
(`realCalc hA`, (a)–(f), uniqueness), real spectral projections, `g(A)` for unbounded real `g`
(self-adjoint), and for semibounded `A ≥ c` the vanishing of `P_(-∞, c)`.
**Representations of `C(X)` and commutative algebras** (Rudin, *Functional Analysis*, Ch. 12).
For a unital `⋆`-representation `π : C(X, ℂ) →⋆ₐ[ℂ] 𝓛(H)`, `X` compact Hausdorff, there is a
projection-valued measure `P` on `X` with `π f = ∫ f dP` (`SpectralTheorem.repPVM`,
`toRep_repPVM`), whose measures are regular; it is unique among p.v.m.'s with regular measures
(`existsUnique_regular_pvm`), and unique outright for metrizable `X`, giving an `Equiv` between
representations of `C(X)` and p.v.m.'s (`repPVMEquiv`).  Every `P Ω` commutes with every operator
commuting with the range of `π`.  `π` also has a multiplication operator form
(`exists_unitary_mulL_rep`).  Applied to the Gelfand representation of a closed commutative
`⋆`-subalgebra `𝒜 ⊆ 𝓛(H)` this is the spectral theorem for commutative C*-algebras of operators:
`T = ∫ T̂ dP` on the Gelfand spectrum (`CommOperatorAlgebra.integral_commPVM`,
`existsUnique_regular_commPVM`), with the simultaneous multiplication form
`U T U⁻¹ = M_{T̂ ∘ F}` (`exists_unitary_mulL_gelfandTransform`).  For a star-commuting family
`T : ι → 𝓛(H)` there is a joint p.v.m. on `ι → ℂ` carried by the joint spectrum with
`T i = ∫ zᵢ dP` (`jointPVM`, `integral_jointPVM_coordBall`), unique for countable `ι`, a joint
multiplication form (`exists_unitary_mulL_joint`), and, for self-adjoint families, a p.v.m. on
`ι → ℝ` (`jointPVMReal`).

**Unbounded normal operators** (Rudin, *Functional Analysis*, Ch. 13; Reed–Simon treat only the
self-adjoint case).  `SpectralTheorem.IsNormalPMap N` is `D(N†) = D(N)` with `‖N ψ‖ = ‖N† ψ‖`;
such an `N` is automatically closed.  The integral `∫ g dP` of a measurable `g` against a p.v.m.
is normal, with `(∫ g dP)† = ∫ ḡ dP` and `(∫ ḡ dP)(∫ g dP) = ∫ |g|² dP = (∫ g dP)(∫ ḡ dP)`, and it
is self-adjoint exactly when `g` is a.e. real (`isSelfAdjoint_integralPMap_iff`).  Conversely
**`SpectralTheorem.IsNormalPMap.exists_pvm`**: every normal `N` is `∫ z dP` for a p.v.m. `P` on
`ℂ`, with no hypothesis on the spectrum (which may be all of `ℂ`); `N` is self-adjoint iff `P` is
carried by `ℝ` (`isSelfAdjoint_iff_apply_real_eq_one`).  The proof uses **von Neumann's theorem**
(Reed–Simon II, Theorem X.25, p. 180), proved here from the graph decomposition: for closed
densely defined `T`, `1 + T†T` is a bijection onto `H` with bounded positive inverse `Q`, `T†T` is
self-adjoint, `T Q` is bounded and `D(T†T)` is a core of `T`.  Applied to `Q = (1 + N†N)⁻¹` and
`S = N Q`, which star-commute, the joint spectral theorem gives a p.v.m. on `ℂ²` whose
pushforward along `z ↦ z₁/z₀` is `P`.  For a normal `N` with a bounded normal resolvent there is
also the direct route through `(N - z₀)⁻¹` (`exists_pvm_integralPMap_eq`).

**`SpectralTheorem.exists_orthogonal_mulReal`** (Theorem VIII.4 over `ℝ`): an orthogonal
`V : E ≃ₗᵢ[ℝ] L²(M, μ; ℝ)` and a real measurable `f` with `ψ ∈ D(A) ↔ f · V ψ ∈ L²` and
`V (A ψ) = f · V ψ`; `μ` finite for separable `E` (`_finite`), and the bounded case (Theorem VII.3
over `ℝ`, `_bounded`, `|f| ≤ ‖T‖`).  It comes from the complex construction with **real**
cyclic vectors, for which the unitary commutes with the conjugations.

## Modules

| Module | Content | Reed–Simon I |
|---|---|---|
| `SpectralMeasure` | spectral measure `μ_ψ` of a bounded normal `T` (Riesz–Markov–Kakutani for `f ↦ ⟪ψ, f(T)ψ⟫`); `∫ f dμ_ψ = ⟪ψ, f(T)ψ⟫`, `∫ |g|² dμ_ψ = ‖g(T)ψ‖²`, `μ_ψ(σ(T)) = ‖ψ‖²`, uniqueness | §VII.2, pp. 224–225 |
| `MultiplicationBounded` | multiplication `mulL g` by `g ∈ L^∞` on `L²(μ)`: norm, algebra, adjoint `mulL (star g)`, strong convergence under bounded pointwise convergence | Thm VII.2 (d), p. 225 |
| `MultiplicationUnbounded` | unbounded multiplication `mulPMap μ f` on `{φ : fφ ∈ L²}`: dense domain, adjoint `mulPMap μ (star f)`, self-adjoint for real `f`; dominated convergence on the domain | Prop. VIII.3.1, pp. 259–260 |
| `Cyclic` | cyclic subspace `H_ψ`; isometry `L²(σ(T), μ_ψ) → H`, `f ↦ f(T)ψ`, onto `H_ψ`, intertwining multiplication by `g` with `g(T)` | §VII.2 Lemma 1, p. 226 |
| `SigmaMeasure`, `SigmaL2` | the measure `Σᵢ μᵢ` on `Σ i, Xᵢ` for any index set; `L²(Σ i, Xᵢ) ≃ ⊕̂ᵢ L²(Xᵢ)` | — |
| `Decomposition` | cyclic decompositions exist (Zorn); `H` is the Hilbert sum of the `L²(σ(T), μ_ψ)` | §VII.2 Lemma 2, p. 226 |
| `MultiplicationForm` | the unitary `U : H ≃ L²(Σ_ψ σ(T), Σ_ψ μ_ψ)`; `U g(T) U⁻¹ = g(λ)·`; Theorem VII.3 | Thm VII.3, p. 227 |
| `BoundedMeasurable` | the `⋆`-algebra of bounded Borel functions; multiplication `g ↦ M_{g∘F}` as a `⋆`-homomorphism | — |
| `BorelCalculus` | `borelCalc T`: `g(T) = U⁻¹ M_{g(λ)} U`; (a)–(d), uniqueness, independence of the decomposition, extension of `cfcHom` | Thm VII.2, p. 225 |
| `BorelCalculusProperties` | (e) eigenvectors, (f) positivity and monotonicity, (g) commutation; `g(T)` normal, self-adjoint for real `g` | Thm VII.2, p. 225 |
| `SpectralProjection` | `⟪ψ, g(T)ψ⟫ = ∫ g dμ_ψ`; spectral projections `P_Ω` and their properties (a)–(d) | pp. 225, 234 |
| `MonotoneClass` | a property of bounded functions that holds for continuous ones and passes to bounded pointwise limits holds for all bounded Borel functions (for the uniqueness in VII.2 and VIII.5) | p. 225 |
| `Resolvent` | for self-adjoint `A`: `(A ± i)⁻¹` bounded, injective, onto `D(A)`, `((A + i)⁻¹)† = (A − i)⁻¹`, normal | proof of Thm VIII.4, p. 261 |
| `ResolventSpectrum` | `R = (A + i)⁻¹`: `σ(R) ⊆ {|z|² + Im z = 0}`, `χ_{0}(R) = 0`, so the spectral variable of `R` is nonzero a.e.; `ρ(z) = (z⁻¹ − i).re` | proof of Thm VIII.4, p. 261 |
| `UnboundedMultiplicationForm` | the multiplication form of `A`: `D(A) = U⁻¹ D(M_f)`, `U A U⁻¹ = M_f` with `f = λ⁻¹ − i` real | Thm VIII.4, pp. 260–261 |
| `SeparableDecomposition` | separable `H`: countably many cyclic vectors, rescaled to norms `2⁻ⁿ`; Theorems VII.3 and VIII.4 with a finite measure | Cor. to Thm VII.3, p. 227; Thm VIII.4 |
| `UnboundedCalculus` | `selfAdjointCalc hA`: `h(A) = (h ∘ ρ)(R)`; (a), (b), (d); `U h(A) U⁻¹ = M_{h∘f}` | Thm VIII.5, pp. 261–262 |
| `UnboundedCalculusProperties` | (c) `hₙ(A) ψ → A ψ`, (e) eigenvectors, (f) positivity | Thm VIII.5, p. 262 |
| `UnboundedCalculusUnique` | uniqueness: `Φ((x + i)⁻¹) = R`, Stone–Weierstrass on the circle, monotone class | Thm VIII.5, p. 262 |
| `SelfAdjointCalculus` | Theorem VIII.5 (a)–(d): existence and uniqueness | Thm VIII.5, p. 262 |
| `ProjectionValuedMeasure` | p.v.m.'s on a measurable space; (d) from (a)–(c); the measures `(ψ, P_Ω ψ)`; pushforward | pp. 234–235, 263; Problem VII.22 |
| `PVMIntegral` | `∫ f dP` for bounded Borel `f`: `⋆`-homomorphism, norm bound, strong continuity; Theorem VII.7; uniqueness criterion | Thm VII.7, p. 235 |
| `SpectralPVM` | the p.v.m. of a bounded normal `T`; `f(T) = ∫ f dP`; support `= σ(T)`; Theorem VII.8 (normal and self-adjoint versions) | Thm VII.8, p. 235 |
| `UnitaryConj` | conjugation `U⁻¹ T U` of an unbounded operator by a unitary; adjoint, self-adjointness | — |
| `UnboundedBorel` | spectral measures `μ_ψ` of a self-adjoint `A`; `g(A)` for unbounded Borel `g` on `D_g` | pp. 263–264 |
| `PVMUnbounded` | `∫ g dP` for unbounded Borel `g` and any p.v.m.; adjoint; self-adjoint for real `g` | p. 263 |
| `UnboundedSpectralPVM` | the p.v.m. of `A`; `∫ g dP = g(A)`; Theorem VIII.6 | Thm VIII.6, pp. 263–264 |
| `Complexification` | the complexification of a real Hilbert space: inner product, completeness, `ofReal`, conjugation | — |
| `ComplexificationOperator` | complexification and descent of bounded and unbounded operators; adjoints, self-adjointness, positivity | — |
| `RealCalculus` | Theorem VIII.5 on a real Hilbert space: `realCalc hA`, (a)–(f), uniqueness; real spectral projections | Thm VIII.5, p. 262 (over `ℝ`) |
| `RealUnboundedBorel` | `g(A)` for unbounded real `g` on a real Hilbert space, self-adjoint; semibounded `A` | Thm VIII.6 (over `ℝ`) |
| `RealCyclic` | normal `B` on `E_ℂ` with `conj B conj = B†`: `conj g(B) conj = ḡ(B)`; cyclic decompositions with real vectors; the unitary commutes with the conjugations | — |
| `RealMultiplicationForm` | the orthogonal map `E ≃ L²(M, μ; ℝ)`; Theorems VIII.4 and VII.3 over `ℝ`, finite `μ` for separable `E` | Thms VIII.4, VII.3 (over `ℝ`) |
| `RepSpectralMeasure`, `RepCyclic`, `RepDecomposition` | for a representation `π` of `C(X)`, `X` compact Hausdorff: spectral measures `μ_ψ`, cyclic subspaces, cyclic decomposition, multiplication operator form | §VII.2, pp. 224–227, for `π` |
| `RepPVM` | the p.v.m. of `π`: `π f = ∫ f dP`, regularity, uniqueness, commutant, representations `≃` p.v.m.'s | Thm VII.8, p. 235, for `π` |
| `CommOperatorAlgebra` | closed commutative `⋆`-subalgebras of `𝓛(H)` as C*-algebras; Gelfand spectrum, `gelfandRep`; algebra and joint spectrum of a star-commuting family; joint continuous calculus | p. 224, remarks (2)–(4); Rudin Ch. 12 |
| `CommutativeSpectral` | `T = ∫ T̂ dP` for a commutative algebra; simultaneous multiplication form; joint p.v.m. of a commuting family, real version for self-adjoint families | Rudin Ch. 12 |
| `VonNeumann` | von Neumann's theorem: `1 + T†T` bijective with bounded positive inverse, `T†T` self-adjoint, `T Q` bounded, `D(T†T)` a core of `T` | R–S II, Thm X.25, p. 180 |
| `NormalPMap` | unbounded normal operators: the definition, closedness, `∫ g dP` normal, the product formula | Rudin Ch. 13 |
| `NormalSpectral` | a normal operator with a bounded normal resolvent is `∫ z dP` | Rudin Ch. 13 |
| `NormalSpectralProperties` | `∫ g dP` self-adjoint iff `g` a.e. real; mirror product formula; support; `N` self-adjoint iff `P` carried by `ℝ` | Rudin Ch. 13 |
| `NormalGeneral` | `T†† = T`; `N†N = N N†`; `Q = (1 + N†N)⁻¹` and `S = N Q` star-commute; **every normal operator is `∫ z dP`** | Rudin Ch. 13 |

## Build

The library has no mathlib checkout of its own.  Build it through a host project that has one, as
a Lake path dependency, together with `KatoRellich` (which it requires through `../KatoRellich`).
No project requires it yet: v0.6 was compiled module by module with `lean` against the mathlib
build of `FiniteVolumeYM2Phi42` (same toolchain and mathlib revision), not with `lake build`.

## Policy

The totalisation audit of the sibling `TotalisationSafety` library passes on `SpectralTheorem/`.
The reviewed markers are the Bochner integrals of continuous or bounded functions against the
finite spectral measures (`SpectralMeasure.lean`, `SpectralProjection.lean`), `ℝ≥0∞`-valued sums
(`SigmaMeasure.lean`, `SigmaL2.lean`, `SeparableDecomposition.lean`), inverses of numbers shown
nonzero (`x + i`, `r(x) + z` with `Im z ≠ 0`, `2`, `‖ψ‖ > 0`, `z₀ − z` off a ball, `ε > 0`),
integrals of functions in `L²` of a finite measure (hence in `L¹`), and `ρ(z) = (z⁻¹ − i).re`,
which is used only off the null set `{0}` (`ResolventSpectrum.lean`).
