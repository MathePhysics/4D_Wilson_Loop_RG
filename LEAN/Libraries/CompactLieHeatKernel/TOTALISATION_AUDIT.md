# Totalisation Audit — CompactLieHeatKernel v0.16

CompactLieHeatKernel v0.16 uses the supplied `TotalisationSafety_v05` source bundle (Lake package `totalisationSafety`) as its sole generic totalisation audit.
The HeatKernel-specific `mfderiv` scanner introduced in v0.4 has been removed because manifold
derivatives are now covered by the shared library.

## Dependency

Expected sibling layout:

```text
Lean/Libraries/
├── TotalisationSafety/
└── CompactLieHeatKernel/
```

`lakefile.toml` uses

```toml
[[require]]
name = "totalisationSafety"
path = "../TotalisationSafety"
```

## Shared totalisation improvements used here

`TotalisationSafety`:

- scans raw `mfderiv` and `mfderivWithin`;
- strips Lean comments and strings before matching;
- distinguishes Bochner integral notation `∫` from `lintegral` notation `∫⁻`;
- does not blanket-classify every `g⁻¹` as hazardous, so ordinary Lie-group inversion no longer
  needs audit markers;
- detects typed scalar inverses and raw division notation;
- provides proof-carrying `ManifoldDerivativeAt` and `ManifoldDerivativeWithinAt` interfaces.

Accordingly the old `lintegral` and group-inverse markers were removed from HeatKernel v0.5.

## Formal HeatKernel guards

`CompactLieHeatKernel.TotalisationAudit` proves or records:

1. `(2 : ℝ) ≠ 0` for the fixed `1/2` Laplacian factor;
2. `(t : ℝ) ≠ 0` on the punctured positive-time filter used by the generator limit;
3. the extended-chart derivative at its centre is genuine (retained as an auxiliary regression guard; v0.14 does not extract it to construct `tangentChartModelEquiv`);
4. any scalar function carrying an explicit `ContMDiff I 𝓘(ℝ) ∞` witness is manifold-differentiable;
5. fixed-element conjugation is manifold-differentiable;
6. the smooth-scalar and conjugation derivative facts are packaged as `TotalisationSafety.ManifoldDerivativeAt` values;
7. `LeftHessianDifferentiabilityAt` is the exact still-open second-order differentiability
   obligation, and any proof of it can now be packaged immediately through the generic safe API.

## Reviewed boundaries

### `leftDifferential`

The raw definition still accepts an arbitrary `f : G → ℝ`; intended Laplacian-facing use is on
smooth functions. The shared scanner therefore continues to require review of its raw `mfderiv`.

### `leftHessian`

The second manifold derivative remains an explicit open second-order calculus boundary rather than
being silently identified with a genuine derivative.

### `kernelAction`

The broad arbitrary-function integral API remains a reviewed boundary. Intended bridge inputs are
continuous functions on compact probability spaces, but the public definition does not yet carry an
integrability witness in its type.

## Running the audit

From the HeatKernel root in the VS Code integrated terminal:

```powershell
powershell -ExecutionPolicy Bypass -File .\scripts\Audit-HeatKernelTotalisations.ps1 -Path .
```

The wrapper delegates the generic scan to the sibling `TotalisationSafety` package.

## v0.14 QFT export

The new QFT-facing real integral statements are not used through totalised fallback branches:

- `integral_centralDensity_eq_one` is reduced to the proved nonnegative `lintegral` mass-one identity;
- `centralDensity_convolution_integrable` proves Bochner integrability before the real semigroup integral is exposed;
- `integral_centralDensity_chapmanKolmogorov` converts to `lintegral` only after nonnegativity and measurability are supplied, and every `ENNReal.toReal` is applied after identifying the quantity with finite `ENNReal.ofReal` data;
- `CentralHeatKernelData` merely packages these already proved facts.

The emulated shared scanner passes on the full v0.16 Lean source tree with no unapproved textual
hazards.  The authoritative PowerShell scanner remains the local VS Code verification step.
