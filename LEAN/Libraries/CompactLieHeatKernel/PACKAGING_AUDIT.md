# Packaging Audit

Version 0.16 is generated from one canonical source directory. It is a linter-only cleanup on top of the externally successful v0.15 build (3054 jobs), removing the final unused-section-variable warning in `CompactManifoldRegularisationData.symmetric`.  ZIP and TAR.GZ are produced only after `SHA256SUMS.txt` is regenerated.

The release procedure verifies all of the following before the archives are issued:

1. `SHA256SUMS.txt` matches every regular source/documentation file except itself;
2. independently extracted ZIP and TAR.GZ trees have the same relative file set;
3. every corresponding extracted file has the same SHA-256 digest;
4. no `.lake` directory or build cache is present;
5. no `sorry` or `admit` occurs in project Lean source, and `axiom` occurs only in
   `CompactLieHeatKernel/Literature/` (literature axioms, not imported by the root module; see
   `LITERATURE_AXIOMS.md`).

This specifically prevents the ZIP/TAR source divergence that occurred in v0.5.

After extraction on Windows, source hashes can be checked from the VS Code integrated terminal with:

```powershell
Get-Content .\SHA256SUMS.txt | ForEach-Object {
  $hash, $path = $_ -split '  ', 2
  $actual = (Get-FileHash -Algorithm SHA256 $path).Hash.ToLowerInvariant()
  if ($actual -ne $hash) { throw "checksum mismatch: $path" }
}
```

## v0.16 release result

The canonical v0.16 tree was checked after the linter-only source change. The only Lean source
difference from the externally successful v0.15 tree is the local `omit [T2Space M] in` scope before
`CompactManifoldRegularisationData.symmetric`. No build cache or proof placeholder is packaged.
