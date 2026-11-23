# KatoRellich v0.1

Self-adjointness of perturbed operators and of operators defined by closed forms, following
Reed–Simon, on top of mathlib `8d52ea9a` (Lean `v4.34.0-rc2`).  No `sorry`, `admit`, axioms or
option overrides; every module compiles without warnings, and the 26 declarations in
`checks/Axioms.lean` depend only on `propext`, `Classical.choice` and `Quot.sound`.

Setting: operators are mathlib's partially defined linear maps `E →ₗ.[𝕜] E` on a Hilbert space
`E` over any `RCLike 𝕜` (so both `ℂ` and `ℝ`).  The adjoint is `LinearPMap.adjoint` and
self-adjointness is mathlib's `IsSelfAdjoint`, i.e. `T† = T`.

## Results

| Reed–Simon | Lean (namespace `KatoRellich`) | Scalars |
|---|---|---|
| II, Theorem X.12 (Kato–Rellich), p. 162: `A` self-adjoint, `B` symmetric and `A`-bounded with relative bound `< 1` ⟹ `A + B` self-adjoint on `D(A)` | `isSelfAdjoint_add`, `isSelfAdjoint_add_complex` | `ℂ` (any `RCLike` with `I ≠ 0`) |
| the same for `A` bounded below | `isSelfAdjoint_add_of_isBoundedBelow` | any, including `ℝ` |
| the same for bounded `V` (relative bound `0`), with `(A + V)† = A† + V†` | `isSelfAdjoint_addBounded`, `isSelfAdjoint_addBounded_neg`, `adjoint_addBounded` | any |
| II, Theorem X.12: `A + B` essentially self-adjoint on every core of `A` | `isEssentiallySelfAdjoint_add`, `isEssentiallySelfAdjoint_add_of_isBoundedBelow`, `hasCore_add` | as above |
| I, Theorem VIII.3, (c) ⟹ (a), pp. 256–257: symmetric `T` with `Ran(T ± i) = H` is self-adjoint | `isSelfAdjoint_of_range_addScalar` (shifts `z`, `z̄`), `isSelfAdjoint_of_range_addScalar_ofReal` (one real shift) | any |
| I, Theorem VIII.15, p. 278: a closed semibounded form is the form of a unique self-adjoint operator | `QuadForm.existsUnique_isSelfAdjoint_isFormOf` | any |

All statements were checked against page images of Reed–Simon I (1972) and II (1975).

## Modules

| Module | Content |
|---|---|
| `Basic` | `IsSymmetric`, `addScalar T z` (= `T + z`), `IsRelBounded B A a b` (`D(A) ⊆ D(B)`, `‖Bx‖ ≤ a‖Ax‖ + b‖x‖`), `IsBoundedBelow A M` |
| `Criterion` | the basic criterion for self-adjointness |
| `BoundedPerturbation` | `addBounded A V`, the adjoint of a bounded perturbation, self-adjointness of `A ± V` |
| `Resolvent` | closed operators bounded below in norm have closed range; `Ran(A + z) = H` for self-adjoint `A` (real shifts under a lower bound, imaginary shifts in general); `‖(A + iμ)x‖² = ‖Ax‖² + μ²‖x‖²` |
| `Neumann` | `S` bijective and `‖Bx‖ ≤ q‖Sx‖`, `q < 1` ⟹ `S + B` onto |
| `Theorem` | the Kato–Rellich theorem, both forms |
| `Core` | cores are preserved by relatively bounded perturbations; `IsEssentiallySelfAdjoint`; essential self-adjointness on cores |
| `QuadraticForm` | `QuadForm` (dense form domain, sesquilinear form), `IsSymmetric`, `IsSemibounded`, `plusOneNorm` (`‖·‖₊₁`), `IsClosed`, `IsFormOf`; the Hilbert space `(Q(q), (·,·)₊₁)` |
| `FormRepresentation` | `QuadForm.toOperator`, its self-adjointness, form core, lower bound and uniqueness; Theorem VIII.15 |

## Formulation notes

* **Real scalars.**  Reed–Simon's proof of Kato–Rellich uses the shifts `±iμ`, which do not exist
  on a real Hilbert space.  Over any `RCLike 𝕜` the theorem is proved for `A` bounded below, using
  a large real shift instead (the estimate Reed–Simon use for their semiboundedness clause).  The
  bounded case needs no lower bound.  The general real case, which would go through the
  complexification, is not formalised.
* **"The quadratic form of `T`."**  Reed–Simon define it with the spectral theorem (I, p. 277,
  Example 2), which mathlib lacks for unbounded operators.  `QuadForm.IsFormOf q M T` asks for
  `D(T) ⊆ Q(q)`, `q(φ, ψ) = ⟪φ, Tψ⟫` for `φ ∈ Q(q)`, `ψ ∈ D(T)`, and `D(T)` dense in `Q(q)` for
  `‖·‖₊₁`.  These are the facts from which Reed–Simon's own proof (p. 279) concludes that `q` is
  the form of the operator; `QuadraticForm.lean` explains the equivalence.
* **Symmetric forms.**  On a complex space a semibounded form is automatically symmetric
  (Reed–Simon I, p. 276).  Over a general `RCLike 𝕜`, symmetry is an explicit hypothesis.
* **Relative bound.**  Reed–Simon's relative bound is the infimum of the admissible `a`, so
  "relative bound `< 1`" is `IsRelBounded B A a b` for some `a < 1` and some `b`.

## Not formalised

* The last clause of Theorem X.12: if `A ≥ M`, then `A + B ≥ M − max{b/(1−a), a|M| + b}`.
  Reed–Simon's proof shows that `−t` lies in the resolvent set of `A + B` whenever
  `−t < M − max{…}`; passing from this to the lower bound uses the spectral theorem.  See
  `STATUS.md` for a spectral-free route.
* Kato–Rellich on a real Hilbert space without a lower bound on `A`.

## Build

The library has no mathlib checkout of its own.  Build it through a host project that has one, as
a Lake path dependency.  For `Projects/FiniteVolumeYM2Phi42`, add to its `lakefile.toml`

```toml
[[require]]
name = "KatoRellich"
path = "../../Libraries/KatoRellich"
```

and run `lake build KatoRellich`.  No project requires the library yet: v0.1 was compiled module
by module with `lean` against the mathlib build of `FiniteVolumeYM2Phi42` (same toolchain and
mathlib revision), not with `lake build`.

## Relation to FiniteVolumeYM2Phi42

The literature axiom `oneFormResolvent_of_uniformlyConvex`
(`FiniteVolumeYM2Phi42/Literature/HelfferSjostrand.lean`) cites Reed–Simon II, Theorem X.12, to
make the block-diagonal operator `H_diag = A₁ − V` self-adjoint on `D(A₁)` for a bounded `V`, and
Reed–Simon I, Theorem VIII.15, to identify it as the operator of a closed form.
`isSelfAdjoint_addBounded_neg` and `QuadForm.existsUnique_isSelfAdjoint_isFormOf` are the abstract
results used in those two steps.  The axiom is not removed by this: its imported content is the
Witten Laplacian `A₁` and the Helffer–Sjöstrand identity, which this library does not touch.

## Policy

The totalisation audit of the sibling `TotalisationSafety` library passes on `KatoRellich/`.  The
one reviewed marker is the constant `q = max a 0 + |b| / c` in `Theorem.lean`, whose denominator
is proved positive on the line before.
