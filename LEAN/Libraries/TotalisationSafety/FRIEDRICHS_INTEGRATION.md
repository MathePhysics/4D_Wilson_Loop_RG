# Integration with FriedrichsExtension

`TotalisationSafety` and `FriedrichsExtension` are sibling reusable Lean libraries:

```text
Lean/Libraries/
├── TotalisationSafety/
└── FriedrichsExtension/
```

The Friedrichs package should depend on the public package root:

```toml
[[require]]
name = "totalisationSafety"
path = "../TotalisationSafety"
```

and import either

```lean
import TotalisationSafety
```

or a narrower module.

`TotalisationSafety_v05` is backward-compatible with the interfaces used by the current
FriedrichsExtension totalisation audit. The new `TotalisationSafety.Manifold` module is additive and
does not require changes to FriedrichsExtension.
