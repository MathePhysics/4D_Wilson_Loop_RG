# TotalisationSafety integration

`FriedrichsExtension` no longer carries a private copy of generic totalisation-safety tooling.
The reusable implementation is the separate Lake package `TotalisationSafety`.

## Package dependency

The standard local layout is

```text
.../Lean/Libraries/
├── TotalisationSafety/
└── FriedrichsExtension/
```

and `lakefile.toml` contains

```toml
[[require]]
name = "TotalisationSafety"
path = "../TotalisationSafety"
```

The Friedrichs package imports only `TotalisationSafety`, the public root module.  It does not
import `TotalisationSafety.Basic`, `TotalisationSafety.Partial`, `TotalisationSafety.Series`, or
other implementation modules directly.

## Project-specific layer

`FriedrichsExtension/TotalisationAudit.lean` is intentionally retained.  Its declarations are not
generic safety infrastructure: they prove that the hypotheses required by totalisation-safe
operations hold for this particular construction.  Specifically they prove positivity of the
energy denominators/radicands, triviality of the resolvent kernel before inversion, and density of
operator domains before the unbounded adjoint is evaluated.

Generic abstractions, tests, policies and scanners belong in `TotalisationSafety`; Friedrichs-only
mathematical certificates belong here.

## Build

From the VS Code integrated terminal:

```powershell
cd C:\Users\marti\Documents\Scientia\Mathematics\Lean\Libraries\FriedrichsExtension
lake build
```

Lake resolves `../TotalisationSafety` as the local dependency.  If the Friedrichs archive is tested
from another directory (for example `D:\Downloads`), either place a `TotalisationSafety` checkout
next to it or move the Friedrichs project into the standard sibling-library layout first.
