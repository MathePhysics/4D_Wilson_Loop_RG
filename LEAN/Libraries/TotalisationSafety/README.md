# TotalisationSafety

A small Lean 4 library for mathematical developments that do **not** want to rely silently on
fallback values introduced by total operations.

The library does not and cannot change Lean's kernel or Mathlib's definitions. Instead it provides
proof-carrying interfaces in which the intended mathematical domain is explicit before a value is
exposed. This prevents a large class of accidental arguments based on conventions such as
`1 / 0 = 0`, `ENNReal.toReal ⊤ = 0`, a non-summable `tsum = 0`, or a non-differentiable derivative
being represented by the zero map.

## Pinned environment

- Lean: `v4.34.0-rc2`
- Mathlib: `8d52ea9a145a9255c4d301c0d1a1b8bf6e59305a`

## Modules

- `TotalisationSafety.Basic`
  - `NonzeroElement`: proof-carrying input to inversion/division;
  - `PositiveReal`: positive-domain real logarithm;
  - `FiniteENNReal`: finite-domain `ENNReal.toReal`.
- `TotalisationSafety.Partial`
  - `PartialMap`;
  - `PartialLinearMap` with an explicit submodule domain.
- `TotalisationSafety.Series`
  - `ConvergentSeries`, carrying `Summable` before exposing `tsum`.
- `TotalisationSafety.Measure`
  - `MeasurableMap` before `Measure.map`;
  - `IntegrableFunction` before a Bochner integral;
  - `NonzeroFiniteMeasure` before `FiniteMeasure.normalize`;
  - `probabilityDefect` in `ℝ`, avoiding truncated subtraction.
- `TotalisationSafety.Calculus`
  - `FrechetDerivativeAt`, carrying `HasFDerivAt` and the actual continuous linear derivative.
- `TotalisationSafety.Manifold`
  - `ManifoldDerivativeAt`, carrying `HasMFDerivAt`;
  - `ManifoldDerivativeWithinAt`, carrying `HasMFDerivWithinAt`;
  - guarded constructors from explicit manifold differentiability witnesses.
- `TotalisationSafety.Regression`
  - deliberate examples of ambient totalised behaviour; it is **not** part of the umbrella import.

## Recommended layout

For reusable formalisation libraries:

```text
C:\Users\marti\Documents\Scientia\Mathematics\Lean\Libraries\
├── TotalisationSafety\
├── FriedrichsExtension\
└── CompactLieHeatKernel\
```

A sibling package can depend on this library with

```toml
[[require]]
name = "totalisationSafety"
path = "../TotalisationSafety"
```

and then use

```lean
import TotalisationSafety
```

or a narrow module import such as

```lean
import TotalisationSafety.Manifold
```

## Manifold derivative safety

Mathlib deliberately defines `mfderiv` and `mfderivWithin` to be zero when differentiability fails.
For mathematical code which must not use this fallback, write the differentiability hypothesis into
the data:

```lean
noncomputable def D
    (h : MDifferentiableAt I I' f x) :
    TotalisationSafety.ManifoldDerivativeAt (I := I) (I' := I') f x :=
  TotalisationSafety.ManifoldDerivativeAt.ofMDifferentiableAt h
```

The analogous within-set constructor is
`ManifoldDerivativeWithinAt.ofMDifferentiableWithinAt`.

## Textual regression audit

Run from a downstream library root in the VS Code integrated terminal:

```powershell
powershell -ExecutionPolicy Bypass -File `
  ..\TotalisationSafety\scripts\Audit-Totalisations.ps1 -Path .
```

Version 0.4.2 scans both Fréchet and manifold derivatives. It ignores comments/string literals,
distinguishes Bochner integrals from `lintegral`, and no longer treats every group inverse `g⁻¹` as
a totalisation hazard merely because the notation is overloaded. The PowerShell audit sources are
ASCII-only for Windows PowerShell 5.1 compatibility, and the scanner reads Lean source explicitly
as UTF-8. Hazard matching is case-sensitive, and Lean import declarations are excluded from term-level scanning.

An intentional occurrence can be reviewed with

```lean
-- totalisation-audit: allow <mathematical reason>
```

Run the audit regression suite itself with

```powershell
powershell -ExecutionPolicy Bypass -File .\scripts\Test-Audit-Totalisations.ps1
```

The textual scanner is a regression aid, not a proof of semantic safety. Public mathematical APIs
should still carry the relevant domain witnesses in their types.
