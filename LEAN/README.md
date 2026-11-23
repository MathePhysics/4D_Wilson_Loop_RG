# Lean formalisation

[CoreLean](CoreLean/) is a work in progress formalising parts of the Bałaban core manuscript.
It uses Lean and Mathlib v4.36.0. With Elan installed, run from this directory:

```sh
cd CoreLean
lake exe cache get
lake build
```

[Supporting libraries](Libraries/) are separate Lake projects for the Gaussian block-spin
transformation, block Poincaré estimates, Lie theory, and related analysis. Each library
keeps its own Lean and Mathlib pins. Sibling dependencies resolve within that directory.
CoreLean carries its own compatible copy of Baker–Campbell–Hausdorff sources.

The vendored Bałaban Lean files retain their upstream licence in
[`CoreLean/Vendor`](CoreLean/CoreLean/Vendor/LICENSE-balaban-lean).
