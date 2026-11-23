# Status: PeterWeyl v0.1 (2026-09-17, paused)

`Basic` and milestones M1–M3 of `SCOPING.md` are written and build without warnings
(`lake build PeterWeyl` through `FiniteVolumeYM2Phi42`, 1,373 lines in four modules).  The
totalisation audit passes, and the 27 declarations in `checks/Axioms.lean` depend only on
`propext`, `Classical.choice` and `Quot.sound`.

**Decision.**  Work stopped here.  The library was a route to constructing the heat kernel of
`½Δ_G`, but that construction is classical and not part of the manuscript's argument, so
`FiniteVolumeYM2Phi42` takes the heat kernel as a hypothesis (`HeatKernelSemigroupData`, or
`HeatSemigroupKernelBridge` from `CompactLieHeatKernel`).  Nothing in the project imports this
library.

Changes against the scoping note:

* Hypotheses are weaker than planned: the convolution operator needs only a finite measure, its
  adjoint and self-adjointness need `μ.WeaklyRegular` instead of a Haar measure, and the
  approximation of M3 uses left invariance and inversion invariance but not right invariance.
* M2 is stated for an abstract compact `T` commuting with right translations and factoring as
  `toLp ∘ S`, and needs no self-adjointness.  The matrix-coefficient step goes through the Riesz
  representation of `e ↦ c⁻¹ (S e)(1)` on the eigenspace.
* Uniform continuity in M3 comes from the tube lemma `IsCompact.eventually_forall_of_forall_eventually`
  rather than the right uniform structure.
* Additional results: `iSup_eigenspace_le_comap_factor` (the containment M4 needs),
  `exists_convolutionFun_approx` (the kernel M4 needs), `exists_nhds_one_convolutionFun_sub_le`
  (a uniform modulus of continuity).

Not done:

* M4, the density theorem: `(matrixCoefficients G).topologicalClosure = ⊤` and `L²` density.  All
  three ingredients are in place (spectral theorem from mathlib, M2's containment, M3's kernel);
  `SCOPING.md` gives the plan and estimates 300–500 lines.
* M5–M9 (Schur orthogonality, characters, smoothness of representations of Lie groups, Laplacian
  eigenvalues, the heat series): not started and not planned.
