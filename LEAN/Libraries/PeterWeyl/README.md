# PeterWeyl v0.1 (paused)

The first steps of the Peter–Weyl theorem for compact topological groups, on top of mathlib
`8d52ea9a` (Lean `v4.34.0-rc2`).  No `sorry`, `admit`, `axiom` or option overrides; every module
compiles without warnings; the declarations checked in `checks/Axioms.lean` depend only on
`propext`, `Classical.choice` and `Quot.sound`.

**Paused (2026-09-17).**  The library was started as a route to constructing the heat kernel of
`½Δ_G` on a compact Lie group.  That existence result is classical, and the formalisation of
`FiniteVolumeYM2Phi42` assumes it, so work stopped after milestones M1–M3.  The density theorem (M4)
is not proved.  See `STATUS.md`.

Setting: `G` a compact group with `[TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
[BorelSpace G]`, and a measure `μ`; each theorem asks only for the measure hypotheses it uses
(finite, right invariant, weakly regular, or Haar).  Neither `T2Space` nor second countability is
needed.

| Module | Content |
|---|---|
| `Basic` | right invariance and inversion invariance of Haar measure on a compact group; `haarProbability`; right translation on `C(G, ℂ)` and `L²(G)`; the right regular representation, continuous and unitary; finite-dimensional continuous unitary representations; the span `matrixCoefficients G` and its closure under constants, conjugation and right translation; `convolutionFun`, the kernel row and `(φ ⋆ f) x = ⟪kernelRow φ x, f⟫` |
| `ConvolutionOperator` | `convolutionC μ φ : L² →L C(G, ℂ)` with `‖convolutionC μ φ‖ ≤ ‖φ‖`; equicontinuity of the image of bounded sets; `convolutionOperator μ φ` on `L²` is compact, commutes with right translations, has adjoint `convolutionOperator μ (adjointKernel φ)`, and is self-adjoint for a symmetric kernel |
| `InvariantSubspaces` | for a compact `T` on `L²` commuting with right translations and factoring through `C(G, ℂ)`: each eigenspace for `c ≠ 0` is a finite-dimensional continuous unitary subrepresentation, and its elements are matrix coefficients (`eigenspace_le_map_matrixCoefficients`, `iSup_eigenspace_le_comap_factor`) |
| `ApproximateIdentity` | symmetric nonnegative bump kernels of mass one supported in any neighbourhood of `1`; `φ ⋆ f → f` uniformly for `f ∈ C(G, ℂ)` (`exists_convolutionFun_approx`) |

## Build

The library has no mathlib checkout of its own.  Build it through a host project that has one, as a
Lake path dependency; `Projects/FiniteVolumeYM2Phi42` is set up this way (it does not import the
library):

```bash
lake build PeterWeyl
```

```bash
lake env lean ../../Libraries/PeterWeyl/checks/Axioms.lean
```

## Policy

The totalisation audit of the sibling `TotalisationSafety` library passes on `PeterWeyl/`; every
Bochner integral and scalar inverse carries a reviewed marker.  `SCOPING.md` is the design note,
including the milestones that were not carried out.
