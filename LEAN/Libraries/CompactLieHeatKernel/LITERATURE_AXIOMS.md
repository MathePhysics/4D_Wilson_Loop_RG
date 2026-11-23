# Literature axioms

Results that are classical but not yet proved in Lean are imported **temporarily** as axioms.  They
live only in `CompactLieHeatKernel/Literature/`, which the root module `CompactLieHeatKernel` does not
import, so `import CompactLieHeatKernel` stays axiom-free.  A downstream declaration depends on a
literature axiom exactly when `#print axioms` shows it by name.

Each axiom must satisfy three rules:

1. it states a published theorem with the same hypotheses, with the references in its docstring;
2. it is a single `Prop`, never a data constant with separately postulated properties, so it cannot
   contradict itself;
3. any hypothesis the literature needs but the Lean structure does not force is added explicitly,
   since a false instance of an axiom makes Lean inconsistent.

## Ledger

| Axiom | File | Replaces | Consumers |
|---|---|---|---|
| `CompactLieHeatKernel.Literature.nonempty_heatSemigroupKernelBridge` | `CompactLieHeatKernel/Literature/HeatKernel.lean` | gaps A, B and C of `ANALYTIC_GAP.md` | `FiniteVolumeYM2Phi42/Section02LiteratureHeatKernel.lean`, `FiniteVolumeYM2Phi42/Section02LiteratureModel.lean` |
| `CompactLieHeatKernel.Literature.heatKernel_gaussian_lower` | `CompactLieHeatKernel/Literature/GaussianBounds.lean` | the lower half of (eq:heat-gaussian-slack) | `FiniteVolumeYM2Phi42/Section05LiteratureHeatKernel.lean` |
| `CompactLieHeatKernel.Literature.heatKernel_gaussian_upper` | `CompactLieHeatKernel/Literature/GaussianBounds.lean` | the upper half of (eq:heat-gaussian-slack) | `FiniteVolumeYM2Phi42/Section05LiteratureHeatKernel.lean` |

### `nonempty_heatSemigroupKernelBridge`

**Statement.**  Let `G` be a compact connected Lie group modelled without boundary on a
finite-dimensional inner product space `E`, with `Ad`-invariant inner product on the Lie algebra,
and let `μ` be a left- and right-invariant Borel probability measure on `G` (hence the normalised
Haar measure).  Then `Nonempty (HeatSemigroupKernelBridge (I := I) (G := G) (μ := μ))`: there is a
self-adjoint Markov semigroup on `L²(G, μ)` whose generator is `½Δ_G` on smooth functions, together
with its smooth, strictly positive, symmetric, bi-invariant heat kernel of mass one that satisfies
Chapman–Kolmogorov and represents the semigroup on continuous functions.

**Why the hypotheses.**
* `ConnectedSpace G`: strict positivity of the kernel fails on a disconnected group.
* `IsAdInvariantInnerProduct`: right invariance of the kernel needs a bi-invariant metric.
* `I.Boundaryless`: excludes boundary models, where manifold derivatives are taken within a
  half-space.
* `BorelSpace G`: a coarser σ-algebra could force the measurable density to be constant.
* The formal `leftLaplacian` is `∑ᵢ Xᵢ Xᵢ` over left-invariant fields.  On a compact, hence
  unimodular, group this is the Laplace–Beltrami operator of the left-invariant metric.  All
  kernel fields are required only at positive times.

**Why at the level of the bridge.**  `GroupHeatKernelData` alone is satisfied by the constant
density `1`, so its existence is provable and would carry no information.  The identification of
the generator with `½Δ_G` is the content.

**References.**  Page numbers are those printed in the books.
* A. Grigor'yan, *Heat Kernel and Analysis on Manifolds*, AMS/IP Studies in Advanced Mathematics 47,
  American Mathematical Society, 2009.
* M. Liao, *Invariant Markov Processes Under Lie Group Actions*, Springer, 2018,
  doi:10.1007/978-3-319-92324-6.
* T. Lévy, *Yang–Mills measure on compact surfaces*, Mem. Amer. Math. Soc. 166 (2003), no. 790;
  preprint arXiv:math/0101239.  Checked in both (2026-09-19); the numbering differs, see the table.
* Background, not relied on and not yet checked: I. Chavel, *Eigenvalues in Riemannian Geometry*,
  Pure and Applied Mathematics 115, Academic Press, 1984; B. K. Driver, *YM₂: continuum
  expectations, lattice convergence, and lassos*, Comm. Math. Phys. 123 (1989), 575–616.

**Checked against the sources (2026-09-17).**

| Field of the bridge | Source | Checked |
|---|---|---|
| `leftLaplacian` is the Laplace–Beltrami operator | Liao, Thm 3.21, Prop 3.22, p. 95; Grigor'yan, Def 3.17 and §3.6, pp. 67–68 (Haar is a constant multiple of the Riemannian measure) | yes |
| self-adjoint, nonpositive generator | Grigor'yan, Thm 4.6, p. 107 | yes |
| strongly continuous self-adjoint contraction semigroup with that generator | Grigor'yan, Thm 4.9, p. 115 | yes |
| positivity preserving, `P_t 1 ≤ 1` | Grigor'yan, Thm 5.11, p. 133 | yes |
| kernel exists, symmetric, represents `P_t`, Chapman–Kolmogorov | Grigor'yan, Thm 7.13, p. 198 | yes |
| kernel jointly smooth | Grigor'yan, Thm 7.20, p. 208 | yes |
| kernel strictly positive (connected `G`) | Grigor'yan, Cor 8.12, p. 229 | yes |
| mass one, `P_t 1 = 1` (compact `G`) | Grigor'yan, Exercise 8.7, p. 233; Thm 11.8, p. 303, with (11.23), p. 304 | yes |
| left and right invariance (bi-invariant metric) | Grigor'yan, Thm 9.12, p. 250: invariance under isometries | yes; that translations are isometries is immediate |
| uniqueness of the generator | Grigor'yan, Thm 11.5, p. 301 | yes |
| symmetry and smoothness, group-theoretic proof | Liao, Prop 4.11, p. 115; Thm 4.17, p. 124; Remark 5.24, p. 159 | yes |
| the plaquette weight of the lattice measure is this kernel (manuscript convention) | Lévy, memoir §1.4, (1.6)–(1.10), pp. 7–8 (preprint §1.4, (1.1)–(1.3)); subdivision invariance from the convolution identity, memoir §1.6, Theorem 1.22 and Proposition 1.26, pp. 13–16 (preprint Theorem 1.6.1, p. 11, and Proposition 1.6.5) | yes, in both |

Conventions: Grigor'yan's semigroup is `e^{tΔ}`; the bridge uses `½Δ_G`, whose kernel with respect
to the normalised Haar measure is `p_{t/2}`.

Removed after checking: Liao 2004 (*Lévy Processes in Lie Groups*) and Varopoulos–Saloff-Coste–Coulhon
1992, since Liao 2018 covers what they were cited for and its introduction describes Liao 2004 as
treating noncompact semisimple groups; Strichartz 1983, since Grigor'yan, Theorem 11.5, covers
uniqueness of the generator.  Chavel 1984 and the Lévy memoir were first supplied as DjVu files that
could not be read; the Lévy entry was checked in the arXiv preprint, and on 2026-09-19 also in the
memoir (text extracted with DjVuLibre).  Nothing above depends on Chavel.  The manuscript cites the
memoir with the preprint's numbering ("Section 1.6, Theorem 1.6.1"); in the memoir the result is
Theorem 1.22.  Lévy scales the bi-invariant metric to volume 1, whereas the axiom allows any
`Ad`-invariant inner product and normalises only the Haar measure; the kernels differ by a time
rescaling.

**Derived declarations.**  `Literature.heatKernelBridge` (a choice of bridge) and
`Literature.heatKernel` (its kernel).  The bridge is unique mathematically (Grigor'yan, Theorem
11.5), but Lean does not know this, so results should be proved for an arbitrary bridge and
specialised last.

**To discharge.**  Construct a `HeatSemigroupKernelBridge` under these hypotheses and replace
`axiom` by `theorem` in place.  No consumer changes.

### `heatKernel_gaussian_lower` and `heatKernel_gaussian_upper`

**Statements.**  Same setting as `nonempty_heatSemigroupKernelBridge`, plus a smooth Riemannian
bundle structure on the tangent spaces whose inner product is `leftMetric` (`hmetric`) and the
Riemannian distance as the metric of `G` (`IsRiemannianManifold`).  For every
`HeatSemigroupKernelBridge` `B`, with `n = dim G` and `k_t = B.kernel.density t`:

* lower: there is `c > 0` with `c t^{-n/2} e^{-d(x,y)²/(2t)} ≤ k_t(x, y)` for `0 < t < 1`;
* upper: there are `C, t₀ > 0` with
  `k_t(x, y) ≤ C (1 + d(x,y)²/t)^{n/2} t^{-n/2} e^{-d(x,y)²/(2t)}` for `0 < t ≤ t₀`.

**Why for every bridge.**  The generator of `B` is `½Δ_G`, the Laplace–Beltrami operator of
`leftMetric` (Liao, Theorem 3.21 and Proposition 3.22), and the self-adjoint generator is unique
(Grigor'yan, Theorem 11.5), so `k_t = vol(G) p_M(t, ·, ·)` for the heat kernel `p_M` of
`∂_t − ½Δ_G` with respect to the Riemannian volume.

**Why the hypotheses.**
* `IsRiemannianManifold`: for the metric `d/2` (same topology) the lower bound fails.
* `hmetric`: for the metric `4 · leftMetric` the upper bound fails.
* `IsContMDiffRiemannianBundle`: both books assume a smooth metric.
* `CompactSpace`: Hsu's theorem is for compact manifolds; the minimum of Grigor'yan's `r(x)` is
  positive on a compact set.
* The remaining hypotheses are those of `nonempty_heatSemigroupKernelBridge`.

**Checked against the sources (2026-09-19).**

| Field | Source | Checked |
|---|---|---|
| lower bound, `C₁ t^{-d/2} e^{-d²/2t} ≤ p_M(t,x,y)` for `(t,x,y) ∈ (0,1) × M × M`, `M` compact | E. P. Hsu, *Stochastic Analysis on Manifolds*, GSM 38, AMS, 2002, Theorem 5.3.4, p. 141 | yes |
| Hsu's convention: heat operator `∂_t − ½Δ_M`, kernel with respect to the Riemannian volume | Hsu, §4.1, p. 102 | yes |
| upper bound, `p_t ≤ C (1+ρ²/t)^{n/2} e^{−ρ²/4t − λ(t−t₀)} / (min(t₀,r(x)²) min(t₀,r(y)²))^{n/4}` for `t ≥ t₀ > 0` | Grigor'yan, Corollary 15.15, p. 406 | yes |
| alternative proof of the upper bound under a lower Ricci bound | P. Li, *Geometric Analysis*, CUP, 2012, Theorem 13.4, p. 139 | yes, not relied on |

Specialisation of the upper bound: on a compact manifold `r` has a positive minimum `r₀`; take
`t = t₀ = τ ≤ r₀²`, use `λ ≥ 0`, and rescale from `e^{tΔ}` to `e^{t½Δ}` (`τ = t/2`).

**Derived declarations.**  `FiniteVolumeYM2Phi42.Section05.LiteratureHeatKernel`:
`gaussianHeatBounds_ofBridge` proves the Section 5 hypothesis (H1), (eq:heat-gaussian-slack) with
arbitrary slack, and `heat_bridge_exp_moment_ofBridge` instantiates Proposition "Heat-Bridge
Exponential Moment".

**To discharge.**  Prove the bounds for a `HeatSemigroupKernelBridge` under these hypotheses (for
example by the parametrix and the Varadhan-type argument of Hsu, §§5.1–5.3) and replace `axiom` by
`theorem`.

## Not yet stated

* The small-time parametrix with its derivative expansion (`eq:scaled-heat-parametrix`,
  `eq:differentiated-heat-parametrix`, citing N. Berline, E. Getzler, M. Vergne, *Heat Kernels and
  Dirac Operators*, Grundlehren 298, Springer, 1992, Chapter 2).  Checked 2026-09-19: Theorem 2.30,
  p. 84, gives `‖∂_t^k (p_t − k_t^N)‖_ℓ = O(t^{N−n/2−ℓ/2−k})` with an *absolute* remainder.  This
  implies the manuscript's relative form `{1 + t a_t(X)}` with polynomially bounded derivatives only
  on `|X| ≤ C p_j` with `p_j² ≍ log(1/a_j)` (the loss `e^{C p_j²}` is a power of `a_j`), not on a
  whole fixed ball as `eq:differentiated-heat-parametrix` states; the "other geodesic images"
  formula it also uses is not in the supplied books.  Stating it needs the Jacobian of `exp`, which
  has no Lean definition yet.
* The time-Harnack inequality (optional hypothesis (H3) of `Section05HeatBridgeMoment`): P. Li,
  *Geometric Analysis*, Corollary 12.3, p. 126, and Corollary 12.5, p. 131 (nonnegative Ricci
  curvature).  Not needed by the manuscript after v128.

## Checks

From `Projects/FiniteVolumeYM2Phi42`:

```bash
lake env lean checks/LiteratureAxioms.lean
```

```bash
grep -rn "^axiom" --include=*.lean ../../Libraries/CompactLieHeatKernel/CompactLieHeatKernel FiniteVolumeYM2Phi42
```

The first lists the declarations that depend on the axiom; the second must report only files under
`CompactLieHeatKernel/Literature/`.
