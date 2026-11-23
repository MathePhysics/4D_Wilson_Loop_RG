# Roadmap after v0.17

The Friedrichs theorem is complete.  Totalisation safety is now delegated to the reusable
`TotalisationSafety` package, with only Friedrichs-specific certificates retained locally.

Next maintenance steps:

1. Compile v0.17 in the standard sibling-library layout and record it as the new verified baseline.
2. Keep Friedrichs-specific safety facts in `FriedrichsExtension.TotalisationAudit`; put generic
   abstractions, scanners, tests and policy changes in `TotalisationSafety` itself.
3. When `TotalisationSafety` acquires a stable Git/Reservoir location, replace the local path
   dependency with a pinned remote/versioned dependency for portable builds.
4. Continue to avoid introducing direct reliance on totalised fallback values in mathematical
   source; domain/nonzero/density hypotheses must remain explicit.
