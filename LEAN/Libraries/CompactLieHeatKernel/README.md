# CompactLieHeatKernel

## v0.18: Opt-in literature axioms for the small-time Gaussian bounds

v0.18 adds `CompactLieHeatKernel/Literature/GaussianBounds.lean` with two axioms, imported
temporarily from the literature because the results are classical: for every
`HeatSemigroupKernelBridge` of a compact connected Lie group, whose metric is the Riemannian distance
of the left-invariant metric, the small-time Gaussian lower bound (E. P. Hsu, *Stochastic Analysis on
Manifolds*, 2002, Theorem 5.3.4) and upper bound (A. Grigor'yan, *Heat Kernel and Analysis on
Manifolds*, 2009, Corollary 15.15); theorem and page numbers checked against the text.  The root
module does not import this file.  The Lévy references now give the memoir numbering as well.

## v0.17: Opt-in literature axiom for the heat kernel

v0.17 adds `CompactLieHeatKernel/Literature/HeatKernel.lean` with one axiom, imported temporarily
from the literature because the result is classical: a compact connected Lie group with an
`Ad`-invariant inner product and its normalised Haar measure carries a `HeatSemigroupKernelBridge`
(Grigor'yan 2009; Liao 2018; theorem and page numbers checked against the text).
The root module does not import this file, so `import CompactLieHeatKernel` remains axiom-free.
See `LITERATURE_AXIOMS.md` for the statement, the reason for each hypothesis, the references and
the checks.

## v0.16: Warning-Free Release Cleanup

The external v0.15 build completed successfully with all 3054 jobs, certifying the complete QFT-facing export. v0.16 makes exactly one Lean-source cleanup: it omits the unused `[T2Space M]` section instance from `CompactManifoldRegularisationData.symmetric`, as suggested by the linter. No proof body, theorem conclusion, or analytic assumption changes.

## v0.15: Lie-Group Continuity Repair

The external v0.14 build reached the new QFT-facing group-kernel code and found one hard error: the proof of `centralDensity_inv_mul_continuous` used topological-group continuity lemmas whose `ContinuousMul` and `ContinuousInv` typeclasses are intentionally not installed from `LieGroup`. v0.15 uses the Lie-group smoothness API directly, via `contMDiff_inv` and `ContMDiff.mul`, and then takes continuity. The only reported linter warning in `transpose_represents` is also removed with a parser-safe local `omit`.


Independent Lean library for the compact-Lie-group analytic infrastructure needed by the
finite-volume heat-kernel Yang--Mills formalisation.

## v0.14: QFT-Facing Central Heat-Kernel Export

v0.14 adds the one-variable compact-group heat-kernel API needed by the finite-volume QFT formalisation. `GroupHeatKernelData` now proves continuity, measurability, fixed-time upper bounds, real/extended-real mass one, explicit convolution integrability, and real/extended-real Chapman--Kolmogorov for `centralDensity`.

`QFTExport.lean` packages these consequences as `CentralHeatKernelData`, with constructor `GroupHeatKernelData.toCentralHeatKernelData`.  This module has no dependency on a QFT project: the downstream adapter remains in the consumer, preserving a one-way dependency.  See `QFT_INTERFACE.md` for the exact field map.

The external v0.15 build completed successfully with all 3054 jobs, so the complete QFT-facing export is compiler-certified. v0.16 is linter-only.

## v0.13: Clean Successful Build

The final external v0.12 `lake build` completed successfully with all 3053 jobs built.  v0.13 therefore makes no mathematical repair: it only removes the final three linter warnings reported by that successful build.

`integral_feller_eq_transpose` omits the two section instances Lean proved unused; `continuous_toL2_denseRange` omits its unused second-countability instance and keeps its bridge parameter under the intentionally-unused name `_B` for API compatibility.  All `omit ... in` scopes are placed before docstrings in the parser-safe form already accepted elsewhere in the project.

## v0.12: Analytic-Bridge Closure

v0.12 follows the final external v0.11 build.  That build confirms that all previously failing modules now compile through `CompactManifoldTheorem`; the sole hard failure is `AnalyticBridge.continuous_toL2_denseRange`, where an explicitly written `∞` is ambiguous between ENNReal and an extended-natural infinity.

The dense-range proof now leaves that type to the already fixed parameter `p := (2 : ℝ≥0∞)` and supplies only `by norm_num`.  The remaining compiler warnings are removed with parser-safe `omit ... in` scopes placed before docstrings, and the smooth-scalar totalisation guard is restated using an explicit `ContMDiff` witness so it no longer acquires an irrelevant `IsManifold` parameter.

## v0.11: Parser Closure

v0.11 follows the latest external v0.10 build, in which `GroupHeatKernel` and `TotalisationAudit`
already compile and the only failed target is `CompactManifoldTheorem`.  The two remaining hard
errors were parser errors caused by placing command-level `set_option ... in` between a docstring
and the theorem it documented.  Those wrappers are removed.  The underlying theorem bodies had
already elaborated without errors in the same build.

The remaining `TotalisationAudit` linter warning is removed by localising `[IsManifold I ∞ G]` to
the extended-chart guard that actually needs it.  Confirmed-unused simp arguments and the unused
regularisation-data binder in `feller_pairing_symmetric` are also cleaned.  No mathematical theorem
statement is weakened and no proof placeholder is introduced.

## v0.10: Final-Build Repair

v0.10 repairs every failure in the final supplied v0.9 build. `GroupHeatKernel` now handles the `a * 1 = a` transport explicitly; the real-valued Fubini and transpose calculations in `CompactManifoldTheorem` use direct pinned integral identities after explicit target reshaping; `toLp` representatives are rewritten before inner-product simplification; and `TotalisationAudit` separates generic smooth-manifold guards from Lie-group-specific guards while proving conjugation smoothness at the function level before differentiating.

The same build confirms that the v0.9 `KernelSemigroup` repair has cleared: it is no longer among the final failed targets. No proof placeholder is introduced.

## v0.9: Compiler Closure Repair

v0.9 repairs every failure in the supplied second v0.8 build: the missing `NNReal` notation scopes in `GroupHeatKernel` and `TotalisationAudit`, the two function-product matching failures in the Tonelli proof, and the incorrect `one_ne_zero` witnesses for smoothness order `∞`.  The same notation-scope issue is repaired proactively in `AnalyticBridge`.  Finite-dimensionality is now required only at the canonical contraction defining `leftLaplacian`, not by the first- or second-order differential layers.

The preceding v0.8 repairs to `InvariantMetric` and `FellerLift` are retained; those modules no longer appear among the failures in the second supplied build.  No proof placeholder is introduced.

See `BUILD_AUDIT.txt` and `CHANGELOG.md` for the exact repairs.

## v0.8: Compiler-Feedback Repair


v0.8 repairs every failure in the supplied v0.7 build: the chart equivalence is now constructed from the data-valued chart derivative rather than a Prop-valued invertibility witness; the Feller assumptions are scoped without unsupported `omit` syntax; Haar-invariance classes are correctly namespace-qualified; and the kernel-semigroup Tonelli proof is split into smaller explicitly measurable steps to avoid rewrite and heartbeat failures. No proof placeholder is introduced.

See `BUILD_AUDIT.txt` and `CHANGELOG.md` for the exact repairs.

## v0.6: Build and Packaging Repair

v0.6 repairs the stale v0.5 TAR.GZ and makes the smoothness notation explicit at the module level.
The affected Lean sources are `InvariantMetric.lean`, `HeatKernelData.lean`, `FellerLift.lean`, and
the downstream modules that use the `ContDiff` smoothness exponent.  The mathematical theorem
surface is unchanged.

Both v0.6 archives are generated from the same canonical source tree, and `SHA256SUMS.txt` is
regenerated from that tree.  See `PACKAGING_AUDIT.md` and `BUILD_AUDIT.txt`.


## v0.5: Shared Totalisation Safety

v0.5 upgrades the sibling dependency to `TotalisationSafety_v04`. The generic library now audits
Mathlib's totalised `mfderiv`/`mfderivWithin` directly and provides proof-carrying manifold
derivative wrappers, so the HeatKernel-local manifold scanner from v0.4 has been removed.

The project-specific audit keeps only HeatKernel mathematics: nonzero scalar denominators,
smoothness/differentiability of intended first-order inputs, and the explicit open second-order
`leftHessian` boundary. Ordinary Lie-group inversion and `lintegral` are no longer misclassified as
fallback operations by the shared textual scanner.

See `TOTALISATION_AUDIT.md`.

## v0.3: Compact-Manifold Reduction

v0.3 finishes the **abstract compact-manifold heat-kernel theorem downstream of regularisation**.
It deliberately does not claim that current mathlib can already prove the classical PDE existence
theorem from a bare Riemannian Laplacian.

### Feller lift

`FellerLift.lean` relates a semigroup on `C(M,ℝ)` to the existing self-adjoint Markov semigroup on
`L²(M,μ)`.  For a compact space with full-support finite Borel measure, the map
`C(M) → L²(M,μ)` is injective.  The project therefore proves rather than assumes:

* identity at time zero;
* the Feller semigroup law;
* preservation of the constant-one function.

### Compact-manifold kernel theorem

`CompactManifoldTheorem.lean` introduces `CompactManifoldRegularisationData`: a jointly smooth,
positive, symmetric density representing an L²-compatible Feller lift.  From this data the project
proves:

* row integrability and mass one;
* continuity of the convolution row;
* Chapman--Kolmogorov against every continuous test function by Fubini;
* pointwise Chapman--Kolmogorov using the full support of `μ`;
* the `ENNReal` Chapman--Kolmogorov identity required by probability kernels;
* construction of the full `SmoothHeatKernelData` object.

Thus normalisation and Chapman--Kolmogorov are no longer independent fields at the compact-manifold
analytic boundary.

### Actual Markov-kernel semigroup

`KernelSemigroup.lean` proves directly that density-level Chapman--Kolmogorov gives

`transitionKernel t ∘ₖ transitionKernel s = transitionKernel (s+t)`

for positive `s,t`.  The old v0.2 bookkeeping gap is closed.

### Lie-group bridge

`AnalyticBridge.lean` adds `GroupRegularisationData`.  Compact-manifold regularisation plus left/right
translation invariance constructs the complete `GroupHeatKernelData`, and
`HeatSemigroupKernelBridge.ofRegularisation` constructs the old generator/kernel bridge.  Its
continuous-test representation property is derived from Feller/L² compatibility rather than
assumed separately.

## What remains genuinely external

The remaining large theorem is the classical PDE/spectral statement producing
`CompactManifoldRegularisationData` from the self-adjoint Laplacian heat semigroup:

1. `L² → C(M)` Feller regularisation;
2. existence of a jointly `C^∞` positive-time kernel;
3. strict positivity on a connected compact manifold;
4. symmetry (or its derivation from self-adjointness and kernel uniqueness).

Current mathlib has strong Hilbert-space, unbounded-operator, completion, L² and compact-operator
infrastructure, but no ready compact-manifold elliptic regularity/heat-kernel/strong-maximum-principle
package.  v0.3 isolates exactly this theorem rather than hiding it behind mass-one/CK assumptions.

## Environment and local dependency

* Lean `v4.34.0-rc2`;
* mathlib commit `8d52ea9a145a9255c4d301c0d1a1b8bf6e59305a`;
* `TotalisationSafety_v05` source bundle, installed as sibling `../TotalisationSafety`.

After adding the dependency, run `lake update totalisationSafety` once before building.  See
`DEPENDENCY_BOOTSTRAP.md`.
