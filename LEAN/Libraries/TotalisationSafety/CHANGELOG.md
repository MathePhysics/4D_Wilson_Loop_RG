# Changelog

## v0.4.2

- Made hazard regex matching case-sensitive, matching Lean's identifier semantics and preventing `Measure.Map` module names from being mistaken for the term `Measure.map`.
- Excluded Lean `import` declarations from term-level totalisation scanning.
- Added regressions requiring `import Mathlib.MeasureTheory.Measure.Map` to pass while an actual `Measure.map f mu` term still fails.
- Retained the v0.4.1 Windows PowerShell 5.1 encoding repair; both audit scripts remain ASCII-only and Lean sources are still read explicitly as UTF-8.
- No Lean source, theorem statement, proof, or proof-carrying API changed from v0.4.1.

## v0.4.1

- Made both PowerShell audit scripts ASCII-only so Windows PowerShell 5.1 does not depend on UTF-8 BOM detection when parsing them.
- Replaced literal Lean Unicode in audit regular expressions with .NET regex `\uHHHH` escapes.
- Made the scanner read every `.lean` source explicitly with `Get-Content -Encoding UTF8`.
- Constructed Unicode regression fixtures at runtime from `[char]` code points instead of embedding Unicode in the `.ps1` source.
- No Lean source, theorem statement, proof, or proof-carrying API changed from v0.4.0.

## v0.4.0

- Added `TotalisationSafety.Manifold`.
- Added proof-carrying `ManifoldDerivativeAt` and `ManifoldDerivativeWithinAt` interfaces.
- Added guarded constructors from `MDifferentiableAt` and `MDifferentiableWithinAt`.
- Added `mfderiv` and `mfderivWithin` to the shared textual audit.
- Refined the audit to strip Lean comments and string literals before matching.
- Distinguished Bochner integral notation from `lintegral` (`∫⁻`).
- Replaced blanket inverse-notation matching with typed-scalar inverse and explicit inverse-API
  matching, so ordinary group inversion is not automatically classified as a fallback hazard.
- Added raw division notation to the textual audit.
- Added `scripts/Test-Audit-Totalisations.ps1` with positive and negative regression cases.
- Made the package capable of auditing its own proof-layer source; `Regression.lean` remains
  intentionally excluded.

No existing proof-carrying API was removed.
