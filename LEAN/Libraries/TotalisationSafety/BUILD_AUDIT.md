# Build audit

Version: 0.4.2

Pinned environment:

- Lean `v4.34.0-rc2`
- Mathlib `8d52ea9a145a9255c4d301c0d1a1b8bf6e59305a`

## Source/API audit

The new manifold module was written against the pinned Mathlib APIs:

- `HasMFDerivAt I I' f x f'`;
- `HasMFDerivWithinAt I I' f s x f'`;
- `MDifferentiableAt.hasMFDerivAt`;
- `MDifferentiableWithinAt.hasMFDerivWithinAt`;
- `HasMFDerivAt.mdifferentiableAt`;
- `HasMFDerivWithinAt.mdifferentiableWithinAt`.

Mathlib's own documentation at the pinned API states that `mfderiv` and `mfderivWithin` are zero
when differentiability fails; this is the totalisation addressed by `TotalisationSafety.Manifold`.

The v0.4.2 audit scripts contain only ASCII bytes. Unicode Lean notation is represented by .NET regex
Unicode escapes, and `.lean` files are read with explicit UTF-8 decoding. This avoids Windows
PowerShell 5.1's legacy no-BOM script-decoding failure. Hazard matching is now case-sensitive, and import declarations are excluded from term-level scanning.

An equivalent local run of the v0.4.2 textual matching logic over the package proof-layer sources
finds zero unapproved hazards. The actual PowerShell script cannot be executed in this assistant
runtime because PowerShell is unavailable.

## Compile status

This assistant runtime does not contain `lean` or `lake`. v0.4.2 therefore remains pending local Lean
compilation. Verify in the VS Code integrated terminal with:

```powershell
lake update
lake exe cache get
lake build
powershell -ExecutionPolicy Bypass -File .\scripts\Audit-Totalisations.ps1 -Path .
powershell -ExecutionPolicy Bypass -File .\scripts\Test-Audit-Totalisations.ps1
```

No `sorry`, `admit`, or `axiom` is intentionally present.
