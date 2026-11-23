# Dependency Bootstrap

CompactLieHeatKernel v0.16 uses the sibling `TotalisationSafety` library through a local Lake path.
The expected layout is:

```text
C:\Users\marti\Documents\Scientia\Mathematics\Lean\Libraries\
├── TotalisationSafety\
├── FriedrichsExtension\
└── CompactLieHeatKernel\
```

Whenever the sibling `TotalisationSafety` source is replaced or upgraded (for example to v0.5),
refresh the local Lake manifest from the VS Code integrated terminal:

```powershell
cd C:\Users\marti\Documents\Scientia\Mathematics\Lean\Libraries\CompactLieHeatKernel
lake update totalisationSafety
lake build
```

If the Lean server was already running while the dependency or source tree changed, restart the
Lean server afterwards.

`FriedrichsExtension` is a separate sibling project, not a direct Lake dependency of
`CompactLieHeatKernel`; no manifest update for it is required here.

The helper remains available:

```powershell
.\scripts\bootstrap-dependencies.ps1 -Build
```
