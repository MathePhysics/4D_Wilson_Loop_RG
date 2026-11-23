# BlockPoincare v0.1

The **fractional block Poincaré estimate** — the manuscript's `lem:app-block-poincare` (v163,
line 12046) — on top of mathlib `8d52ea9a` (Lean `v4.34.0-rc2`). There are no `sorry`s, `admit`s,
axioms, literature axioms or option overrides, and no module produces a warning. The 75
declarations in `checks/Axioms.lean` depend only on `propext`, `Classical.choice` and
`Quot.sound`.

Setting: `X` is a metric space with a measure `μ` (`[MeasurableSpace X] [MetricSpace X]`,
`μ : Measure X`). The two-dimensional torus `T_L = AddCircle L × AddCircle L`, with its quotient
distance and its Haar measure, **is constructed**, together with its subdivision into `M²`
squares of side `L/M` (`BlockPoincare.Torus.squares`), so the estimate is available there in the
manuscript's form. A two-point model with the counting measure is also constructed
(`BlockPoincare.Witness`), and on it both sides of the estimate are positive. Functions are real
valued.

The estimate:

> Let `P` be a partition of `X` into finitely many congruent blocks of measure `vol` and diameter
> at most `side`, and let `f ∈ L²` have zero integral on every block. Then
> `‖f‖_{H^{-s}} ≤ √(side^(2+2s) / vol) ‖f‖_{L²}` for every `s > 0`.
> For cubes of side `l` in two dimensions (`vol = l²`, `diam ≤ √2 l`) this reads
> `‖f‖_{H^{-s}} ≤ 2^((1+s)/2) l^s ‖f‖_{L²}`.

With `l = a_{j-1} = M a_j` this is the manuscript's `‖f_j‖_{H^{-s}} ≤ C_{s,M} a_j^s ‖f_j‖_{L²}`
with `C_{s,M} = 2^((1+s)/2) M^s`.

The manuscript derives the estimate from a fractional Poincaré inequality on a cube which it
cites to Hurri-Syrjänen–Vähäkangas (John domains). **On a cube that citation is not needed**, and
this library replaces it by a three-line convexity argument (`BlockPoincare.Cube`). The library
is therefore axiom-free and citation-free.

## Definitions

All in `ℝ≥0∞`, so that they are total: no integrability hypothesis enters a definition.

| Notion | Lean | Definition |
|---|---|---|
| `‖g‖²_{L²(A)}` | `l2sq μ A g` | `∫⁻ x in A, ofReal (g x ^ 2)` |
| `[g]²_{Hˢ(A)}` | `gagliardoSq s μ A g` | `∫⁻ x in A, ∫⁻ y in A, ofReal ((g x - g y)^2) / ofReal (dist x y ^ (2 + 2 s))` |
| `‖g‖²_{Hˢ}` | `hsNormSq s μ g` | `l2sq μ univ g + gagliardoSq s μ univ g` |
| `‖f‖_{H^{-s}}` | `hNegNorm s μ f` | `⨆ ψ ∈ unitBall s μ f, ofReal (∫ x, f x * ψ x ∂μ)` |
| mean of `g` on `A` | `mean μ A g` | `(μ A).toReal⁻¹ * ∫ x in A, g x ∂μ` |

`unitBall s μ f` is the set of `ψ` that are `AEStronglyMeasurable`, have `hsNormSq s μ ψ ≤ 1`, and
pair integrably with `f`. These are the definitions the brief fixes for the joint use with
`ParaproductTorus`; that library is **not** imported, and the overlap is exactly `l2sq`,
`gagliardoSq`, `hsNormSq` and `hNegNorm`, which are duplicated verbatim in the sense of the
formulas above.

Junk-value conventions: in `ℝ≥0∞`, `a / 0 = ∞` for `a ≠ 0` and `0 / 0 = 0`. On the diagonal the
Gagliardo integrand is `0 / 0 = 0`, which is the intended value; this is why `X` is a metric
space and not merely a pseudometric one. `mean μ A g` is junk when `μ A ∈ {0, ∞}`, and every
lemma about it assumes `μ A ≠ 0` and `μ A ≠ ∞`.

## Results

All names are in namespace `BlockPoincare`.

| Statement | Lean |
|---|---|
| The mean minimises the `L²` distance: `∫_A (g - mean)² ≤ ∫_A (g - c)²` | `integral_sub_mean_sq_le` |
| Averaged Jensen: `μ A * ‖g - mean‖²_{L²(A)} ≤ ∫_A ∫_A \|g x - g y\|²` | `mul_l2sq_sub_mean_le` |
| Diameter step: `∫_A ∫_A \|g x - g y\|² ≤ D^(2+2s) [g]²_{Hˢ(A)}` if `diam A ≤ D` | `lintegral_sq_diff_le` |
| **Fractional Poincaré on a set of diameter `D`**: `‖g - mean‖²_{L²(A)} ≤ D^(2+2s) / μ A * [g]²_{Hˢ(A)}` | `l2sq_sub_mean_le_diam`, `mul_l2sq_sub_mean_le_diam` |
| Block partitions: `Σ_B ∫_B = ∫`, `Σ_B ‖f‖²_{L²(B)} = ‖f‖²_{L²}`, `Σ_B [ψ]²_{Hˢ(B)} ≤ [ψ]²_{Hˢ}` | `BlockPartition.sum_setLIntegral`, `.sum_setIntegral`, `.sum_l2sq`, `.sum_gagliardoSq_le` |
| Cauchy–Schwarz for the Bochner integral | `integral_mul_le_sqrt_mul_sqrt` |
| Poincaré on one block, in real form | `integral_sub_bmean_sq_le` |
| **The block estimate, pairing form**: `⟪f, ψ⟫ ≤ √(side^(2+2s)/vol) ‖f‖_{L²} [ψ]_{Hˢ}` | `pairing_le` |
| **The block estimate, dual-norm form**: `‖f‖_{H^{-s}} ≤ √(side^(2+2s)/vol) ‖f‖_{L²}` | `hNegNorm_le_of_blockIntegral_zero` |
| **Cubes of side `l` in two dimensions**: `‖f‖_{H^{-s}} ≤ 2^((1+s)/2) l^s ‖f‖_{L²}` | `hNegNorm_le_cube`, `sqrt_cube_const` |
| Homogeneity of degree two of the three quantities | `l2sq_const_mul`, `gagliardoSq_const_mul`, `hsNormSq_const_mul` |
| **Non-vacuity**: `∫ f² > 0` and `‖f‖_{Hˢ} < ∞` imply `‖f‖_{H^{-s}} > 0` | `hNegNorm_pos` |
| **The manuscript's form**: `‖f‖_{H^{-s}} ≤ 2^((1+s)/2) M^s a^s ‖f‖_{L²}` for blocks of side `M a` | `hNegNorm_le_scale` |
| `Σ_j a_j^s < ∞` for `a_j = a₀ M^{-j}`, `M > 1`, `s > 0` | `summable_scale_rpow` |
| A space with a block partition has measure `card ι * vol`, hence is finite | `BlockPartition.measure_univ_eq`, `.isFiniteMeasure` |
| **Centred fibre coordinate** `D_B ζ = ζ - 1_B m_B ζ`: on a block it is `ζ - mean`, its block integrals vanish, it is the identity on that class, it is idempotent, it preserves `L²` | `BlockPartition.centre`, `.centre_apply`, `.setIntegral_centre`, `.centre_eq_self_of_setIntegral_eq_zero`, `.centre_idem`, `.memLp_centre` |
| The estimate applied to a centred function | `BlockPartition.hNegNorm_centre_le` |
| **A concrete instance**: the two-point space, its one-block partition, and `f = ±1` with `‖f‖²_{L²} = 2`, `‖f‖²_{Hˢ} = 10`, `0 < ‖f‖_{H^{-s}} ≤ 1` | `TwoPoint.blocks`, `TwoPoint.witness`, `TwoPoint.witness_nontrivial` |
| The quotient map `ℝ → AddCircle T` does not increase distances | `Torus.dist_coe_le` |
| **The circle cut into `M` arcs**: measure `T/M`, diameter `≤ T/M`, disjoint, covering | `Torus.arc`, `Torus.volume_arc`, `Torus.arc_disjoint`, `Torus.iUnion_arc`, `Torus.dist_le_of_mem_arc`, `Torus.arcs` |
| **On the circle**: `‖f‖_{H^{-s}} ≤ (T/M)^((1+2s)/2) ‖f‖_{L²}` | `Torus.hNegNorm_le_arcs` |
| The product of two block partitions | `BlockPartition.prod` |
| **On the two-dimensional torus**, cut into `M²` squares of side `l = T/M`: `‖f‖_{H^{-s}} ≤ l^s ‖f‖_{L²}` | `Torus.squares`, `Torus.hNegNorm_le_squares` |
| **The manuscript's form on the torus**: `M = M₀^j`, `a_j = T/M₀^j`, `‖f‖_{H^{-s}} ≤ a_j^s ‖f‖_{L²}`, and `Σ_j a_j^s < ∞` | `Torus.hNegNorm_le_scale_pow`, `Torus.summable_torus_scale` |
| **Every `L²` field on the torus, once centred on the squares, obeys the estimate** | `Torus.hNegNorm_centre_le_squares` |
| Formal API: monotonicity in the set, invariance under constants and sign, the two supremum properties | `l2sq_mono_set`, `gagliardoSq_mono_set`, `gagliardoSq_add_const`, `neg_mem_unitBall`, `le_hNegNorm`, `hNegNorm_le`, `hNegNorm_zero` |

## Modules

| Module | Content |
|---|---|
| `Defs` | `l2sq`, `mean`, `gagliardoSq`, `hsNormSq`, `unitBall`, `hNegNorm`, and their formal API |
| `Cube` | the fractional Poincaré inequality on a set of finite diameter: Jensen, averaging, the diameter step |
| `Blocks` | `BlockPartition`; the three summation facts the block sum needs |
| `Estimate` | Cauchy–Schwarz; the block estimate in pairing and in dual-norm form |
| `Nontrivial` | homogeneity; positivity of the dual norm |
| `Scales` | the two-dimensional cube constant; the manuscript's form; `a_j = a₀ M^{-j}` and its summability |
| `Centred` | the centred fibre coordinate `D_B` of `lem:app-centred-fibre` |
| `Torus` | `AddCircle T`: the quotient distance, the coordinate in `(0, T]`, the `M` arcs and their `BlockPartition` |
| `Product` | products of block partitions; the two-dimensional torus and the manuscript's scales |
| `Witness` | the two-point model: a space, a partition and an `f` for which every hypothesis holds and both sides of the estimate are positive |

## The proof

1. **Fractional Poincaré on a cube (`Cube`).** For a constant `c`,
   `∫_A (g - c)² - ∫_A (g - mean)² = μ A (mean - c)² ≥ 0`, so the mean minimises. Taking
   `c = g y` and integrating over `y ∈ A` gives `μ A ∫_A (g - mean)² ≤ ∫_A ∫_A |g x - g y|²`.
   Since `dist x y ≤ D` on `A`, `|g x - g y|² ≤ D^(2+2s) |g x - g y|² / dist x y ^ (2+2s)`
   pointwise, whence `μ A ‖g - mean‖²_{L²(A)} ≤ D^(2+2s) [g]²_{Hˢ(A)}`. No John-domain theory.
2. **Duality and the block sum (`Estimate`).** `∫_B f ψ = ∫_B f (ψ - ψ_B)` because `∫_B f = 0`;
   Cauchy–Schwarz on `B`; step 1 on `B`; Cauchy–Schwarz over the blocks
   (`Real.sum_sqrt_mul_sqrt_le`); and `Σ_B [ψ]²_{Hˢ(B)} ≤ [ψ]²_{Hˢ(X)}` because the blocks are
   disjoint, so the squares `B × B` are disjoint subsets of `X × X`. Taking the supremum over the
   unit ball gives the dual-norm form.

The `ℝ≥0∞` formulation does the work here: steps 1 and 3 of the proof are monotonicity of a lower
integral and need no integrability side conditions at all. Only the duality step is in `ℝ`, and
there `f, ψ ∈ L²` gives everything (`MemLp.integrable_mul`).

## Uniformity of the constant

`√(side^(2+2s) / vol)` involves the partition only through `side` and `vol`. It does not depend
on the block, on the number of blocks, on the index `j`, or on the total measure of `X`. This is
checked by inspection of the statement of `hNegNorm_le_of_blockIntegral_zero`: `P` occurs on the
right only through `P.side` and `P.vol`. The hypothesis `measure_block : ∀ i, μ (block i) = vol`
of `BlockPartition` is what makes this possible — with blocks of different sizes the argument
would give the worst block's constant.

## Non-vacuity

`hNegNorm_pos`: if `f ∈ L²` with `∫ f² > 0` and `‖f‖_{Hˢ} < ∞`, then `‖f‖_{H^{-s}} > 0`. The test
function is `f` itself, normalised: `ψ = f / ‖f‖_{Hˢ}` lies in the unit ball and
`⟪f, ψ⟫ = ‖f‖²_{L²} / ‖f‖_{Hˢ} > 0`. So the block estimate is never an inequality between two
zeros, once its `f` has finite `Hˢ` norm.

`BlockPoincare.Witness` discharges that hypothesis on a concrete space: the two-point metric
space with the counting measure, the one-block partition (`side = 1`, `vol = 2`) and `f = ±1`,
for which `‖f‖²_{L²} = 2`, `‖f‖²_{Hˢ} = 10` and `0 < ‖f‖_{H^{-s}} ≤ 1` (`witness_nontrivial`).
A partition into finitely many blocks of finite diameter forces the space to be bounded, so the
smallest models are of this kind; the two-point model is a sanity check on the definitions, not
the intended application.

## Not done

* **No concrete `f` on the torus.** `Torus.hNegNorm_le_squares` is an implication: it assumes an
  `f ∈ L²` with zero integral on every square. No such `f` is exhibited on the torus, and in
  particular the non-vacuity of the torus statement rests on `hNegNorm_pos`, whose hypothesis
  `‖f‖_{Hˢ} < ∞` is not discharged for a concrete torus function. For a piecewise constant `f`
  that hypothesis holds exactly for `s < 1/2`, and proving it needs the integrability of
  `dist ^ (-2-2s)` off the diagonal, which is not formalised. The two-point model
  (`BlockPoincare.Witness`) is where both sides are shown to be positive.
* **The torus distance is the supremum distance**, because that is mathlib's metric on a product.
  A square of side `l` then has diameter `l`, and the constant is `l^s`. With the Euclidean
  distance the diameter is `√2 l` and the constant `2^((1+s)/2) l^s`; that statement is
  `Scales.hNegNorm_le_cube`, which is proved for any space whose blocks satisfy `diam ≤ √2 l`,
  but the Euclidean torus itself is not constructed.
* **`s = 1` in this formulation.** The estimate is proved for every `s > 0`, so `s = 1` is
  included. But the Gagliardo seminorm `[·]_1` is degenerate: on a space like the torus, only
  constants have finite `[·]_1`, so at `s = 1` the statement, while true, is empty. The
  `H¹`-gradient version of the block Poincaré inequality (`∫ |∇ψ|²` in place of `[ψ]²_1`) is
  *not* proved here; it needs derivatives on the torus. The manuscript's
  `eq:uv-hierarchy-fractional-Poincare` should therefore be discharged from this library only for
  `s < 1`. (The degeneracy at `s = 1` is a classical fact about the Gagliardo seminorm; it is not
  formalised here either, so the `s = 1` statement is simply left as it stands.)
* **`lem:app-centred-fibre`** (v163, line 12013): `D_B ζ = ζ - 1_B m_B ζ` is formalised in
  `Centred` as a projection (idempotent, range in the zero-mean class, identity on it). The
  *isomorphism onto the zero-mean subspace* as a statement about submodules, and the inverse map,
  are not formalised.
* **No sharpness, no converse**, and no `H^{-s}`-completion: `hNegNorm` is a supremum of
  pairings, which is what the manuscript uses, not the norm of an element of a dual space.
* **Vector-valued `f`.** Only real-valued functions; the finite-dimensional case follows
  componentwise but is not stated.

## Build

The library has no mathlib checkout of its own. Build it as a Lake path dependency of a host
project that has one:

```toml
[[require]]
name = "BlockPoincare"
path = "../../Libraries/BlockPoincare"
```

No project requires it yet. v0.1 was compiled module by module with
`lean +leanprover/lean4:v4.34.0-rc2` against the mathlib build of `FiniteVolumeYM2Phi42`, not
with `lake build`. Each module takes about 8 s.

## Relation to FiniteVolumeYM2Phi42

The manuscript uses the estimate to bound the `H^{-s}` norm of a block-constant field by its `L²`
norm times `a_j^s`, and then sums `Σ_j a_j^s < ∞`. On the torus this is
`Torus.hNegNorm_le_scale_pow` together with `Torus.summable_torus_scale`: take `M = M₀^j`
squares in each direction, so `a_j = L / M₀^j`, and supply the hypothesis that `f_j` has zero
integral on every square — which is what the manuscript's construction provides, since `f_j` is
constant on the fine blocks and has zero mean on each coarse block. If the blocks come with a
Euclidean rather than a supremum diameter, use `Scales.hNegNorm_le_scale` instead, at the cost of
the factor `2^((1+s)/2)`.

## Policy

The totalisation audit of the sibling `TotalisationSafety` library passes on `BlockPoincare/`
with 144 reviewed `-- totalisation-audit: allow` markers, of the three kinds:

* `L1 hyp` — a Bochner integral `∫`, whose integrand is integrable by an explicit `MemLp` or
  `Integrable` hypothesis at that point (never by default: when integrability is unavailable the
  quantity is a lower integral `∫⁻` instead);
* `finite` — a `.toReal`, always of a value carrying a `≠ ∞` hypothesis or bounded by `1`;
* `> 0` — a division, always by `μ A`, `vol`, `M`, `M ^ j`, `l`, `l ^ 2` or `‖f‖_{Hˢ}`, each
  positive by hypothesis at that point.
