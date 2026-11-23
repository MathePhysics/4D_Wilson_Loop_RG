# QFT Interface

`CompactLieHeatKernel.QFTExport` is the downstream-facing boundary for finite-lattice gauge/QFT
formalisation.  It deliberately does not import a QFT project.

## Exported object

For compact Borel groups with Haar probability, `CentralHeatKernelData G μ` packages the positive-time
one-variable heat kernel `q_t : G → ℝ` with:

* continuity and measurability;
* strict positivity;
* uniform positive lower and finite upper bounds at each fixed `t > 0`;
* Bochner integrability;
* real and `ENNReal` mass-one identities;
* conjugation invariance and inversion symmetry;
* integrability of the real Chapman--Kolmogorov convolution integrand;
* real and `ENNReal` Chapman--Kolmogorov identities in the orientation
  `q_(s+t)(g) = ∫ q_s(h) q_t(h⁻¹ g) dμ(h)`.

Every field is derived from `GroupHeatKernelData`; no additional analytic assumption is introduced.
The constructor is

```lean
GroupHeatKernelData.toCentralHeatKernelData
```

## Mapping to the finite-volume QFT interface

The current QFT formalisation describes `HeatKernelSemigroupData` as carrying normalised left/right
Haar measure together with positive-time measurability, positivity, boundedness, centrality,
integrability, and Chapman--Kolmogorov.  The intended downstream adapter is therefore field-for-field:

| QFT requirement | `CompactLieHeatKernel` source |
|---|---|
| density `q_t` | `CentralHeatKernelData.density` |
| measurability | `measurable_density` |
| strict positivity | `strictlyPositive` |
| nonnegativity | `nonnegative` |
| boundedness | `upperBound` |
| integrability | `integrable` |
| normalisation | `mass_one` / `integral_mass_one` |
| centrality | `central` |
| Chapman--Kolmogorov integrability | `semigroup_integrable` |
| Chapman--Kolmogorov | `semigroup` / `semigroup_real` |
| Haar left/right invariance | the typeclass parameters `μ.IsMulLeftInvariant`, `μ.IsMulRightInvariant` |

The adapter itself should live in the QFT project so that dependency remains one-way.  The raw Lean
source containing the QFT project's `HeatKernelSemigroupData` declaration was not available in the
current Project/Library snapshot, so this release does not guess its constructor field names.

## Not included here

This export does not attempt to formalise lattice gauge combinatorics, BCH/local-curvature charts,
spin-network representation theory, or the eventual PDE theorem constructing the heat kernel from
the Friedrichs Laplacian.  Those are separate dependency layers.
