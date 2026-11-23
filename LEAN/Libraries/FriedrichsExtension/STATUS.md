# FriedrichsExtension v0.17 Status

## Mathematical status

The Friedrichs-extension construction and full theorem layer are complete.  The user has confirmed
that v0.16 compiles in full under Lean `v4.34.0-rc2` with the pinned mathlib revision.

The substantive mathematical modules are unchanged in v0.17:

- `SemiboundedOperator.lean`
- `EnergyCore.lean`
- `EnergySpace.lean`
- `FriedrichsResolvent.lean`
- `FriedrichsOperator.lean`
- `FriedrichsTheorem.lean`

## v0.17 change

The embedded generic totalisation-safety implementation has been removed.  FriedrichsExtension now
requires the separate sibling Lake package `TotalisationSafety` and imports its public root module.

`FriedrichsExtension/TotalisationAudit.lean` remains local because its declarations are statements
about the particular Friedrichs operators constructed here.  It now imports `TotalisationSafety`
and acts as the project-specific instantiation layer.

## Verification boundary

- v0.16: **fully compile-verified externally**.
- v0.17 mathematical theorem modules: byte-for-byte inherited from v0.16.
- v0.17 dependency/integration changes: source-audited here; pending the user's local Lake build
  against the separately installed `TotalisationSafety` package.

## Required local layout

```text
.../Lean/Libraries/TotalisationSafety/
.../Lean/Libraries/FriedrichsExtension/
```

The `lakefile.toml` path dependency is `../TotalisationSafety`.
