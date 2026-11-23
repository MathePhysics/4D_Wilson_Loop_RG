# LieGroupExponential v0.3

The exponential map of a real Lie group, on top of mathlib `8d52ea9a`
(Lean `v4.34.0-rc2`).  No `sorry`, `admit` or option overrides; every module compiles without
warnings.  The root module `LieGroupExponential` is axiom-free: its proofs depend only on
`propext`, `Classical.choice` and `Quot.sound`.  Two literature axioms live in
`LieGroupExponential/Literature/`, which the root does not import; see `LITERATURE_AXIOMS.md`.

Setting: `G` a Lie group of class `C^∞` modelled on a complete normed space `E` through a model
with corners `I` without boundary.  The regularity results also assume smooth bump functions on
`E` (`HasContDiffBump E`), which holds in finite dimension and for Hilbert spaces.

| Module | Content |
|---|---|
| `OmegaLemma` | post-composition `γ ↦ f ∘ γ` is `C^n` on `C(K, E)` for compact `K` and `f` of class `C^n` |
| `ParamODE` | `C^n` family of solutions of `γ' = F (γ, p)` at a stationary parameter, by the implicit function theorem |
| `OneParameter` | global integral curves of left-invariant fields; `exp`; `exp ((s+t)•v) = exp (s•v) * exp (t•v)`; `exp (n•v) = exp v ^ n`; characterisation of one-parameter subgroups by their velocity; a Lie group is Hausdorff |
| `Naturality` | `φ (exp v) = exp (dφ v)` for homomorphisms differentiable at `1`; `Ad`, `Ad_mul`, `AdEquiv`; `g * exp v * g⁻¹ = exp (Ad g v)`; `exp (v + w)` for commuting one-parameter subgroups |
| `ChartField` | the left-invariant fields read in the chart at `1`; `C^∞` dependence; global cut-off field; conversion of chart solutions to integral curves; `C^∞` invariant vector fields |
| `Smoothness` | `exp` is `C^∞` (`contMDiff_exp`), with differential the identity at `0` |
| `ExpChart` | `expChart : OpenPartialHomeomorph E G` with symmetric source; `log`, `C^∞` on the target; `log g⁻¹ = -log g`; group law `expMul` in exponential coordinates, `C^∞` at `0` with derivative `X + Y`; `log (g x g⁻¹) = Ad g (log x)`; `log (exp ξ ^ n) = n • ξ` |
| `Literature.ContinuousRepresentation` (not imported by the root) | **literature axiom** `exists_isDifferential` (Hall 2015, Proposition 4.4): a continuous orthogonal action of a closed subgroup of `GL(n, ℝ)` has a real-linear differential with `ρ(exp X) = exp (L X)` on the Lie algebra; `SmoothOrthogonalAction` bundles the action with it; axiom-free API `iso_exp_smul`, `hasDerivAt_iso_exp`, `norm_exp_smul_diff_le` |
| `Literature.IsometricExponential` (not imported by the root) | **literature axiom** `dist_expE_eq_norm_of_biInvariant` (Lee 2018, Problem 5-8(c), Corollary 6.12, Proposition 2.51): for a bi-invariant Riemannian metric whose distance is the metric of `G`, `dist (exp v) 1 = ‖v‖` for small `v ∈ T₁G` and translations are isometries |

## Build

The library has no mathlib checkout of its own.  Build it through a host project that has one, as a
Lake path dependency; `Projects/FiniteVolumeYM2Phi42` is set up this way:

```bash
lake build LieGroupExponential
```

## Policy

The totalisation audit of the sibling `TotalisationSafety` library passes on `LieGroupExponential/`;
every raw `mfderiv`, `fderiv`, interval integral, scalar inverse and `Classical.choose` carries a
reviewed marker.  See `STATUS.md` for scope and open ends, and `SCOPING.md` for the design note.
