# Status: LieGroupExponential v0.3 (2026-09-19)

v0.3 adds `LieGroupExponential/Literature/IsometricExponential.lean`, which the root module does not
import.  It holds the literature axiom `dist_expE_eq_norm_of_biInvariant`: for a Lie group whose
metric is the Riemannian distance of a smooth bi-invariant Riemannian metric, the exponential map
satisfies `dist (exp v) 1 = ‖v‖` for `v` in a ball of `T₁G` (Riemannian norm), and left and right
translations are isometries.  The source is Lee, *Introduction to Riemannian Manifolds*, 2nd ed.,
2018 (Problem 5-8(c), Corollaries 6.12–6.13, Proposition 2.51), checked against the text; the ledger
is `LITERATURE_AXIOMS.md`.  Its consumer is the tree atlas of `FiniteVolumeYM2Phi42`
(`Section04AtlasLiterature`).  It builds without warnings, and the totalisation audit reports no
unapproved hazards.

## v0.2 (2026-09-18)

v0.2 adds `LieGroupExponential/Literature/ContinuousRepresentation.lean`, which the root module
does not import.  It holds the literature axiom `exists_isDifferential`: a continuous orthogonal
action of a closed subgroup of `GL(n, ℝ)` has a differential intertwining the two exponentials.
The source is Hall, *Lie Groups, Lie Algebras, and Representations*, 2nd ed., 2015,
Proposition 4.4, checked against the text; the ledger is `LITERATURE_AXIOMS.md`.
`SmoothOrthogonalAction` is the orthogonal action together with this smooth structure.  Its API
(`iso_exp_smul`, `hasDerivAt_iso_exp`, `norm_exp_smul_diff_le`) is proved without the axiom, and
only `ContinuousOrthogonalAction.toSmooth` uses it.  The module is stated for closed matrix groups,
so it applies to `SU(N)` and `SO(N)` realised as matrices, which the manifold-level modules cannot
reach yet; see the last item below.  It builds without warnings, and the totalisation audit reports
no unapproved hazards.

## v0.1 (2026-09-17)

All seven modules planned in `SCOPING.md` are written and build without warnings
(`lake build LieGroupExponential` through `FiniteVolumeYM2Phi42`).

Process: `OneParameter`, `Naturality`, `ChartField` and `Smoothness` were each reviewed by two
independent reviewers (statement fidelity; build hygiene and audit markers) and then fixed.
`ChartField`, `Smoothness` and `ExpChart` were each written twice independently and merged by a
judge.  `ExpChart` was merged and compiles clean, but its independent review was cut short.

Changes against the scoping note:

* The Hausdorff hypothesis is not needed: `t2Space_of_lieGroup` proves it.
* Regularity needs `HasContDiffBump E` instead of finite dimension.
* `ChartField` proves that invariant vector fields are `C^∞` sections; mathlib has `C^2` only.
* `Ad = CompactLieHeatKernel.adjointDifferential` is proved in
  `FiniteVolumeYM2Phi42/Section03ExpChart.lean` (`Ad_eq_adjointDifferential`), which imports both.
* The `CentredChart` constructor lives in `FiniteVolumeYM2Phi42/Section03ExpChart.lean`, since the
  structure is defined there.

Not done:

* second-order BCH term `log (exp X exp Y) = X + Y + ½[X, Y] + O(3)` and the convergent series;
* `exp` as the Riemannian exponential of a bi-invariant metric;
* Lie group structures on `SU(N)`, `SO(N)`: mathlib has none, so there is no non-Abelian compact
  instance to which the library can be applied yet.
