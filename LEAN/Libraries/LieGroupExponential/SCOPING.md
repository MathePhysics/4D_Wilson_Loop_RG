# LieGroupExponential: scoping pass (2026-09-17)

Status: **carried out.**  The library was written on 2026-09-17 following this note; see `README.md`
and `STATUS.md`.  The prototype files mentioned below became the modules `OmegaLemma` and `ParamODE`.

## Verdict

Worth doing, and much cheaper than it looked.  The feared obstacle was smooth dependence of ODE
solutions on parameters, which mathlib does not have.  For the exponential map it reduces to two
self-contained results, and both are already written and checked in `prototype/ParamODE.lean`
(333 lines, no errors, no warnings, axioms `propext`, `Classical.choice`, `Quot.sound` only):

1. **Omega lemma.**  For compact `K` and `f : E → F` of class `C^n`, post-composition `γ ↦ f ∘ γ`
   is a `C^n` map `C(K, E) → C(K, F)` (`OmegaLemma.contDiff_superposition`).
2. **Solutions near a stationary parameter.**  If `F : E × P → E` is `C^n` and `F (x, 0) = 0` for
   all `x`, the solutions of `γ' = F (γ, p)`, `γ 0 = 0` on a fixed interval `[-T, T]` form a family
   `p ↦ Γ p` that is `C^n` at `p = 0` as a map into `C([-T, T], E)`
   (`ParamODE.exists_contDiffAt_solutions`).

The second result is exactly the exponential map read in a chart: `F (x, ξ)` is the left-invariant
vector field of `ξ`, and it vanishes identically when `ξ = 0`.  What remains is Lie-group and
manifold bookkeeping, estimated at **1,500–2,400 lines** in five modules.  For comparison, v39 of
`FiniteVolumeYM2Phi42` added about 4,000 lines in seven modules.

## Why the analytic part is small

The standard proof of smooth dependence applies the implicit function theorem to the Picard map
`Φ (p, γ) = γ − ∫₀ᵗ F (γ s, p) ds` on the Banach space of continuous curves.  Three facts make this
short here.

* Mathlib at the pinned commit already has the `C^n` implicit function theorem
  (`ContDiffAt.implicitFunction`, `ContDiffAt.contDiffAt_implicitFunction`, 2025).
* At `(p, γ) = (0, 0)` the partial derivative of `Φ` in `γ` is the identity, because
  `F (·, 0) ≡ 0` kills the linearised integral term.  So no Neumann series and no smallness of `T`
  are needed, and the time interval can be `[-2, 2]` from the start.
* The only missing analytic input is that `γ ↦ F ∘ γ` is `C^n` on `C(K, E)`.  Its proof is an
  induction on `n` through `contDiff_succ_iff_hasFDerivAt`, where the derivative is pointwise
  application of `DF ∘ γ`.  The `C¹` step uses the mean value inequality and uniform continuity of
  `DF` at the compact range of `γ`.

A general theorem (smooth dependence around an arbitrary solution, not the zero solution) would
need invertibility of `1 − (Volterra operator)`.  The exponential map does not need it, so it is
left out.

## What the manuscript needs from `exp`

Sections 2–4 only use quadratic remainder bounds for the group law in a chart, and v39 proves them
for any chart centred at the identity (`Section03LieChart.CentredChart`).  Later sections use
properties that a general chart does not have:

* `Ad`-equivariance of `log`, for the atlas and the Ward identities (tex lines 9587–9746,
  13263–13369);
* the one-parameter subgroup law, in the subdivision `exp(√(nt) Y) = ∏ exp(√t X_i)` (line 12449);
* `exp` as the Riemannian exponential of the bi-invariant metric, in the heat-kernel parametrix
  `−log q_{g²}(exp(gX)) = c + ½|X|² + R(X)` (eq:scaled-heat-parametrix, line 5452);
* the commutator structure of the BCH expansion (lines 5461, 12627).

The first two follow from uniqueness of integral curves and need no regularity.  The third and
fourth need more than this library (see "Out of scope").

## What mathlib already provides

All names below were checked against mathlib `8d52ea9a` in the `FiniteVolumeYM2Phi42` environment.

* Lie algebra and invariant fields: `GroupLieAlgebra`, `mulInvariantVectorField`,
  `contMDiff_mulInvariantVectorField`, `mpullback_mulInvariantVectorField`, and the `LieAlgebra`
  instance with bracket defined through `mlieBracket`.
* Integral curves on manifolds: `IsMIntegralCurve`,
  `exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless`,
  `isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless`, time shift and scaling
  (`IsMIntegralCurve.comp_add`, `comp_mul`), and global existence from a uniform existence time
  (`exists_isMIntegralCurve_of_isMIntegralCurveOn`).  Left translation gives the uniform time.
* ODEs in a Banach space: Picard–Lindelöf local flows, Grönwall, uniqueness, Lipschitz and joint
  continuous dependence on the initial point, `C^n` regularity in time.  **Not** present:
  differentiability in the initial point or in parameters, the omega lemma, any exponential map of
  a Lie group or one-parameter subgroups.
* Inverse and implicit function theorems of class `C^n`: `ContDiffAt.toOpenPartialHomeomorph`,
  `ContDiffAt.to_localInverse`, `ContDiffAt.implicitFunction`.
* `prototype/Stage1Probe.lean` (38 lines, compiles cleanly) checks that the entry points apply to a
  `LieGroup 𝓘(ℝ, E) ∞ G`: the invariant field is a `C¹` section, local integral curves exist at the
  identity, and global integral curves are unique.

## Proposed modules

| Module | Content | Size |
|---|---|---|
| `OmegaLemma` | superposition operator on `C(K, E)` is `C^n` | done in prototype (140 lines) |
| `ParamODE` | `C^n` solution family at a stationary parameter | done in prototype (190 lines) |
| `OneParameter` | global integral curve of `mulInvariantVectorField v` through `1`; `exp v`; `exp ((s+t)•v) = exp (s•v) * exp (t•v)`; `exp (-v)`; `exp (n•v) = (exp v)^n`; velocity `v` at `0` | 400–600 |
| `Naturality` | `φ (exp v) = exp (dφ v)` for smooth homomorphisms; `g * exp v * g⁻¹ = exp (Ad g v)`, with `Ad` matched to `CompactLieHeatKernel.adjointDifferential` | 150–250 |
| `ChartField` | the invariant field read in the centred chart at `1`, `F (x, ξ)`: linear in `ξ`, jointly `C^n` near `x = 0`, cut off by a bump function to a global `C^n` field | 300–500 |
| `Smoothness` | `chart (exp ξ) = Γ ξ 1` near `0` by uniqueness of integral curves; hence `exp` is `C^n` at `0` for every `n`, `D exp 0 = id`, and `exp` is smooth everywhere through `exp ξ = (exp (ξ/N))^N` | 350–550 |
| `ExpChart` | inverse function theorem, `log`, a constructor for `FiniteVolumeYM2Phi42`'s `CentredChart`, and `log (g h g⁻¹) = Ad g (log h)` where both sides are defined | 300–500 |

`OneParameter` and `Naturality` already deliver `Ad`-equivariance and the subdivision law, and they
do not depend on the regularity modules.  They are the natural first milestone.

After `ExpChart`, every result of `Section03CurvatureChart` applies to the exponential chart without
change, and the v39 caveat "the exponential chart is not constructed" disappears.

## Risks

* **Manifold bookkeeping** in `ChartField` and `Smoothness` is the main risk.  Relating
  `mfderiv (g * ·) 1 v` to the derivative of the chart group law goes through
  `tangentCoordChange`.  Mathlib's own proofs in this area need
  `set_option backward.isDefEq.respectTransparency false`, so elaboration is delicate.  Mathlib's
  proof of `exists_isMIntegralCurveAt_of_contMDiffAt` shows the chart-to-manifold conversion and can
  be adapted.
* **Elaboration on `C(K, E)`.**  `LinearMap.mkContinuous` needed all type arguments spelled out
  before instances unified.  This cost a few iterations in the prototype and is solved there.
* **Hypotheses.**  The cutoff needs `HasContDiffBump E`, which holds in finite dimension.  The
  integral-curve API needs `BoundarylessManifold`, `T2Space G` and `CompleteSpace E`.  The prototype
  keeps `E` and `P` in one universe; the application has `P = E`.
* **`Ad`-equivariance of `log`** on a whole ball needs an `Ad`-invariant norm.
  `CompactLieHeatKernel` records `Ad`-invariance of the inner product as a hypothesis, not a
  theorem, so the equivariance statement will be conditional in the same way or local.

## Out of scope

* The convergent BCH series and analyticity of the group law.
* The second-order term `log (exp X exp Y) = X + Y + ½[X, Y] + O(3)`.  It is reachable afterwards
  from smoothness of `exp` and mathlib's bracket, perhaps 500–1,000 lines, and is what the
  manuscript's commutator counting would need.
* `exp` as the Riemannian exponential, and the heat-kernel parametrix.
* Lie group structures on the physical gauge groups.  Mathlib has `LieGroup` instances only for
  products, normed spaces, units of a normed algebra (`GL`) and `Circle`.  There is no `SU(N)` or
  `SO(N)`, and no closed-subgroup theorem.  So every Lie-group result in the project stays abstract
  for non-Abelian compact groups until that gap is closed; `Circle` is the available test case.

## Setup when the library is started

Follow the sibling libraries: `lakefile.toml` with mathlib pinned to
`8d52ea9a145a9255c4d301c0d1a1b8bf6e59305a`, toolchain `leanprover/lean4:v4.34.0-rc2`, a path
dependency on `../TotalisationSafety` for the audit policy, and optionally on
`../CompactLieHeatKernel` for `adjointDifferential`.  `FiniteVolumeYM2Phi42` would then add a path
dependency on `../../Libraries/LieGroupExponential`.

The totalisation audit script flags 16 textual occurrences in `prototype/ParamODE.lean`: raw
`fderiv` (13) and interval integrals (3).  All are guarded: every `fderiv` is of a `C¹` map, and
every integrand is continuous.  They will need `totalisation-audit: allow` markers, or statements
in terms of `HasFDerivAt`, when the files move into the library.

## How the prototypes were checked

From `Projects/FiniteVolumeYM2Phi42`, which supplies the mathlib build:

```bash
lake env lean ../../Libraries/LieGroupExponential/prototype/ParamODE.lean
```

```bash
lake env lean ../../Libraries/LieGroupExponential/prototype/Stage1Probe.lean
```

Both exit with code 0 and print nothing.  `#print axioms` on
`OmegaLemma.contDiff_superposition` and `ParamODE.exists_contDiffAt_solutions` reports only
`propext`, `Classical.choice` and `Quot.sound`.
