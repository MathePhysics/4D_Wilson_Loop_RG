# FriedrichsExtension

Lean formalisation of the Friedrichs extension for densely defined semibounded symmetric operators
on real Hilbert spaces.

## Current checkpoint: v0.17

The full mathematical construction and theorem layer through v0.16 has been compile-verified by the
user with Lean `v4.34.0-rc2` and mathlib commit
`8d52ea9a145a9255c4d301c0d1a1b8bf6e59305a`.

v0.17 changes only the totalisation-safety integration.  The reusable machinery now lives in the
separate `TotalisationSafety` Lake package.  FriedrichsExtension keeps only the project-specific
proof certificates in `FriedrichsExtension/TotalisationAudit.lean`.

## Dependency layout

The supplied `lakefile.toml` expects the two projects to be siblings:

```text
Lean/Libraries/
├── TotalisationSafety/
└── FriedrichsExtension/
```

The dependency is declared as:

```toml
[[require]]
name = "TotalisationSafety"
path = "../TotalisationSafety"
```

`FriedrichsExtension.lean` and `FriedrichsExtension/TotalisationAudit.lean` both import the public
root module `TotalisationSafety`.  No Friedrichs source depends on the library's internal module
layout.

## Totalisation boundary

`TotalisationSafety` is now the authoritative reusable library for generic totalisation-safe
constructions and checks.  `FriedrichsExtension.TotalisationAudit` contains only facts specific to
this project:

- positivity of the shifted energy denominator;
- positivity of the square root used in the ambient embedding;
- trivial kernel of the bounded resolvent before partial inversion;
- density of the shifted/unshifted operator domains before use of the unbounded adjoint;
- positivity/nonnegativity conditions in the change-of-shift comparison.

The previous embedded generic scanner, allowlist implementation, safe-build wrappers and generic
policy document have been removed from this package to avoid maintaining two copies of the safety
infrastructure.

## Build

From the VS Code integrated terminal, with both projects in the sibling layout above:

```powershell
cd C:\Users\marti\Documents\Scientia\Mathematics\Lean\Libraries\FriedrichsExtension
lake build
```

The separate `TotalisationSafety` dependency is then resolved by Lake and its public Lean modules
are available to this project.

## Main result

For a densely defined symmetric operator `A` with lower bound `m`, the project constructs the
canonical Friedrichs extension, proves self-adjointness, the sharp lower bound, the closed-form
representation, uniqueness/maximality in the form sense, and independence of the auxiliary positive
shift.
