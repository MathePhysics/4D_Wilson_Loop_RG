# Totalisation Safety Policy

## Principle

A totalised ambient operation may be used internally only after the hypotheses selecting its
mathematical branch have already been established. Public proof-layer APIs should expose the
hypotheses structurally, preferably through a subtype or proof-carrying structure.

| Ambient operation | Hazard | Preferred interface |
|---|---|---|
| `x / y`, scalar `y⁻¹` | zero denominator/inverse is assigned a value | `NonzeroElement` denominator |
| `∑' i, f i` | non-summable family is assigned `0` | `ConvergentSeries`, `Summable`, or `HasSum` |
| `ENNReal.toReal x` | `⊤` is sent to `0` | `FiniteENNReal` |
| `∫ x, f x ∂μ` | non-integrable or incomplete-target branch gives `0` | `IntegrableFunction` |
| `Measure.map f μ` | non-a.e.-measurable map receives a fallback pushforward | `MeasurableMap` |
| `FiniteMeasure.normalize` | zero measure receives an arbitrary probability measure | `NonzeroFiniteMeasure` |
| `fderiv` / `deriv` | non-differentiability is represented by a fallback derivative | `FrechetDerivativeAt`, `HasFDerivAt` |
| `mfderiv` / `mfderivWithin` | non-differentiability is represented by the zero tangent map | `ManifoldDerivativeAt`, `ManifoldDerivativeWithinAt`, `HasMFDerivAt` |
| `Real.log x` | total extension is defined outside `(0,∞)` | `PositiveReal.log` when positivity is intended |
| partial operator inverse | value outside the true operator domain is artificial | `PartialLinearMap` / an explicit submodule domain |
| choice-valued minimiser | existence/uniqueness can disappear behind choice | bundle a witness and prove minimality/uniqueness |

## Important distinctions

### Group inversion versus scalar inversion

The notation `x⁻¹` is overloaded. In a genuine `Group`, inversion is a total algebraic operation and
is not a fallback branch. In a group-with-zero or field, the same notation can hide the convention
`0⁻¹ = 0`.

The textual audit therefore **does not flag every occurrence of `⁻¹`**. It flags explicit inverse
APIs (`Inv.inv`, `Ring.inverse`) and scalar inverse notation when a standard scalar type annotation
is visible. This avoids treating ordinary Lie-group inversion as a mathematical domain error. A
project with additional zero-sensitive inverse types should add a project-specific textual pattern
or, preferably, expose nonzeroness through `NonzeroElement`.

### `lintegral` versus the Bochner integral

`∫⁻ x, f x ∂μ` is an extended nonnegative integral valued in `ℝ≥0∞`; it is not the
zero-on-nonintegrable Bochner fallback. The shared textual audit therefore excludes `∫⁻` while
continuing to flag ordinary Bochner integral notation `∫`.

## Textual audit semantics

`scripts/Audit-Totalisations.ps1` is a regression aid. It:

- ignores Lean comments and string literals;
- scans `mfderiv` and `mfderivWithin` as well as Fréchet derivatives;
- scans raw division notation;
- distinguishes `∫` from `∫⁻`;
- does not blanket-flag group inverse notation;
- ignores `TotalisationSafety.Regression`, whose purpose is to record unsafe ambient semantics;
- can audit `TotalisationSafety` itself.

An intentional reviewed occurrence is marked on the same source line with

```lean
-- totalisation-audit: allow <mathematical reason>
```

The marker is a review record, not a proof. The strongest protection remains proof-carrying theorem
and definition interfaces.

## What this package does not claim

1. It does not alter Lean's trusted kernel.
2. It does not remove Mathlib's totalised operations from scope.
3. It does not prove that a downstream project contains no semantic use of a totalisation merely
   because the textual audit passes.
4. The PowerShell audit is not a kernel-checked semantic linter.
5. Overloaded notation cannot always be classified from source text; the type-level API is the
   authoritative safety mechanism.
