# Changelog

## v0.18

* Added `CompactLieHeatKernel/Literature/GaussianBounds.lean` with the literature axioms
  `Literature.heatKernel_gaussian_lower` (Hsu 2002, Theorem 5.3.4, p. 141) and
  `Literature.heatKernel_gaussian_upper` (Grigor'yan 2009, Corollary 15.15, p. 406, specialised to a
  compact manifold), stated for every `HeatSemigroupKernelBridge` and the Riemannian distance of the
  left-invariant metric (`IsRiemannianManifold`, `hmetric`).  The root module does not import it.
* `Literature/HeatKernel.lean` and `LITERATURE_AXIOMS.md`: the Lévy references give the memoir
  numbering (Theorem 1.22, Proposition 1.26, (1.6)–(1.10)) next to the preprint's, now that the
  memoir has been read; the parametrix finding (absolute remainder in Berline–Getzler–Vergne,
  Theorem 2.30) is recorded.

## v0.17

* Added `CompactLieHeatKernel/Literature/HeatKernel.lean` with the literature axiom
  `Literature.nonempty_heatSemigroupKernelBridge` and the derived `Literature.heatKernelBridge` and
  `Literature.heatKernel`.  The axiom is imported temporarily from the literature because the result
  is classical; its docstring gives the references.
* The axiom adds `ConnectedSpace G`, `IsAdInvariantInnerProduct` and `I.Boundaryless` to the
  hypotheses of the bridge; without them some field of the bridge would be false.
* The root module `CompactLieHeatKernel` does not import the new file, so no existing declaration
  depends on the axiom.  Added `LITERATURE_AXIOMS.md`.

## v0.16

* Based on the external v0.15 build, which completed successfully: all 3054 jobs built.
* Removed the sole remaining linter warning by placing `omit [T2Space M] in` before the docstring of `CompactManifoldRegularisationData.symmetric`, exactly as suggested by Lean.
* No proof body, theorem conclusion, QFT-facing export, or analytic assumption was changed.
* v0.15 is therefore the compiler-certified mathematical baseline; v0.16 is a linter-only cleanup.

## v0.15

* Repaired the only hard error in the external v0.14 build: `centralDensity_inv_mul_continuous` no longer asks typeclass inference for `ContinuousMul G` / `ContinuousInv G`.
* The continuity proof now uses the pinned Lie-group smoothness API directly: `(contMDiff_inv I ∞).mul contMDiff_const`, followed by `.continuous`.  This is the intended route because mathlib deliberately does not install `IsTopologicalGroup G` as an instance from `LieGroup I ∞ G`.
* Removed the sole reported linter warning by placing `omit [T2Space M] in` before the docstring of `CompactManifoldRegularisationData.transpose_represents`.
* No QFT-export statement, analytic assumption, or proof conclusion was changed.


## v0.14

* Added positive-time one-variable central-kernel continuity and measurability theorems.
* Added a compactness-derived uniform finite upper bound, complementing the existing uniform positive lower bound.
* Added real and `ENNReal` mass-one theorems for `centralDensity`.
* Added explicit Bochner integrability of `centralDensity` and of the real Chapman--Kolmogorov convolution integrand.
* Added one-variable Chapman--Kolmogorov in both `ENNReal` and real Bochner-integral formulations, in the QFT orientation `q_s(h) q_t(h⁻¹ g)`.
* Added `QFTExport.lean` with the dependency-neutral `CentralHeatKernelData` package and `GroupHeatKernelData.toCentralHeatKernelData`.
* Added `QFT_INTERFACE.md`, mapping this export to the finite-volume QFT project's documented `HeatKernelSemigroupData` requirements.
* No additional analytic assumption, `axiom`, `sorry`, or `admit` is introduced.

## v0.13

* Based on the final external v0.12 build, which completed successfully: all 3053 jobs built.
* Removed the last three linter warnings reported by that successful build without changing any proof body or theorem conclusion.
* `CompactManifoldRegularisationData.integral_feller_eq_transpose` now omits exactly the unused `[T2Space M]` and `[μ.IsOpenPosMeasure]` section instances reported by Lean.
* `HeatSemigroupKernelBridge.continuous_toL2_denseRange` now omits the unused `[SecondCountableTopology G]` section instance and renames its intentionally API-preserving but unused bridge argument to `_B`.
* The cleanup uses parser-safe `omit ... in` placement before docstrings, matching the form already accepted by the successful v0.12 build.
* No `axiom`, `sorry`, or `admit` was introduced.

## v0.12

* Based on the final external v0.11 build, which confirms that `CompactManifoldTheorem`, `GroupHeatKernel`, `KernelSemigroup`, and `TotalisationAudit` all compile.  The sole remaining failed target is `AnalyticBridge`.
* Removed the ambiguous explicit `∞` literal from the `ContinuousMap.toLp_denseRange` proof; the proof obligation is now inferred from `p := (2 : ℝ≥0∞)` and discharged by `norm_num`.
* Applied Lean's exact unused-section-variable recommendations in parser-safe `omit ... in` scopes placed **before** docstrings for `AnalyticBridge.dense_generator_domain`, `GroupRegularisationData.toGroupHeatKernelData_density`, and the three warning-producing compact-manifold helper theorems.
* Rephrased the smooth-scalar totalisation guard using an explicit `ContMDiff I 𝓘(ℝ) ∞ f` witness.  This removes the remaining spurious `IsManifold` linter dependency while preserving the genuine-branch certificate for `mfderiv`.
* No mathematical theorem statement used downstream was weakened, and no `axiom`, `sorry`, or `admit` was introduced.

## v0.11

* Based on the latest external v0.10 build, which confirms that `GroupHeatKernel` and `TotalisationAudit` compile; the only failed target is `CompactManifoldTheorem`.
* Removed the two parser-breaking `set_option linter.unusedSectionVars false in` commands that sat between docstrings and their theorem declarations (`transposeAction_apply` and `transpose_test_integrable`).
* Localised `[IsManifold I ∞ G]` in `TotalisationAudit` to `totalisationGuard_extChartAt_mdifferentiableAt`, removing the surviving unused-section-variable warning without linter suppression.
* Removed the compiler-confirmed unused `RCLike.inner_apply'` simp arguments in `feller_pairing_symmetric` and renamed its unused regularisation-data binder `_R`.
* No mathematical statement was weakened; no `axiom`, `sorry`, or `admit` was introduced.


## v0.10

* Repaired every failure in the final external v0.9 build.  That build confirms that `KernelSemigroup`, `InvariantMetric`, `FellerLift`, and `LaplacianGeneratorBridge` now compile past their previously reported failures; the remaining failed targets were `GroupHeatKernel`, `CompactManifoldTheorem`, and `TotalisationAudit`.
* `GroupHeatKernel.centralDensity_conj` now discharges the harmless `a * 1 = a` base-point simplification explicitly with `simpa`, instead of asking Lean to accept the unsimplified left-invariance equality directly.
* Reworked the real-valued Fubini calculation in `CompactManifoldTheorem.integral_convolutionRow_mul`: multiplication by a fixed endpoint value is moved through the integral by direct applications of the pinned `integral_mul_const` / `integral_const_mul` theorems after an explicit `change`, and the Feller representation step is likewise exposed before rewriting.
* Repaired `feller_pairing_symmetric` by rewriting the two `ContinuousMap.coeFn_toLp` almost-everywhere identities before simplifying the real inner product.  This avoids premature unfolding to `ContinuousMap.toAEEqFun`.
* Reworked `integral_feller_eq_transpose` in the same explicit-target style: the representation, constant-multiplication, product-reassociation, and transposed-action steps no longer depend on rewrite matching through lambda wrappers.
* Split `TotalisationAudit` into generic smooth-manifold guards and Lie-group-specific guards.  The generic first-derivative guards now assume only `[IsManifold I ∞ G]`, while conjugation and left-Hessian guards retain the Lie-group hypotheses.
* The conjugation audit now first proves smoothness of the actual lambda `fun h ↦ g * h * g⁻¹` and only then takes `mdifferentiableAt`, eliminating the composition-vs-lambda definitional mismatch reported by Lean.
* Removed the reported unused-variable/linter noise associated with the repaired declarations without changing any theorem conclusion.
* No `axiom`, `sorry`, or `admit` was introduced.


## v0.9

* Repaired all failures reported by the second external v0.8 build.
* Opened the `NNReal` scope in `GroupHeatKernel` and `TotalisationAudit`; the reported `LE Type` / `OfNat Type 0` errors came from parsing `ℝ≥0` as an order expression on the type `ℝ`.
* Opened both `NNReal` and `ENNReal` scopes proactively in `AnalyticBridge`, which was blocked behind the group-kernel failure and uses both notations.
* Made positive-time binders explicit as `(t : ℝ≥0)` in the group-kernel and group-regularisation interfaces, eliminating reliance on downstream inference for the time type.
* Hardened `centralDensity_inv` by replacing two fragile rewrites across group simplifications with an explicit `calc` and `simpa`.
* Replaced the two remaining `KernelSemigroup` `rw` steps by direct applications of `lintegral_const_mul''` and `lintegral_mul_const''` to explicitly supplied functions; this avoids matching pointwise lambdas against bundled function products.
* Replaced `one_ne_zero` by the correctly inferred `(by simp)` witness for smoothness exponent `∞` in both manifold-differentiability guards.
* Moved `[FiniteDimensional ℝ E]` from the first/second derivative layer to the actual canonical contraction defining `leftLaplacian`; the totalisation guards therefore no longer carry an irrelevant finite-dimensional assumption.
* Removed the unused `SecondCountableTopology` and `μ.WeaklyRegular` assumptions from `LaplacianGeneratorBridge`, eliminating the warning reported by the compiler without using parser-sensitive `omit` syntax.
* No theorem statement was weakened in mathematical content and no `axiom`, `sorry`, or `admit` was introduced.
* ZIP and TAR.GZ are generated from one canonical v0.9 source tree with fresh checksums.


## v0.8

* Repaired all failures reported by the external v0.7 build.
* `InvariantMetric.leftTranslationTangentEquiv` now proves the base-point identity by an explicit
  `change g * 1 = g`, avoiding the failed simplification of the bundled diffeomorphism application.
* Replaced the attempt to eliminate the Prop-valued `ContinuousLinearMap.IsInvertible` witness into
  a `ContinuousLinearEquiv`.  `tangentChartModelEquiv` now uses the data-valued
  `OpenPartialHomeomorph.MDifferentiable.mfderiv` of the actual chart and then
  `tangentSpaceCastModel` for the model-space tangent identification.
* Corrected the orientation of `real_inner_comm` in `leftMetric_symm`.
* Removed the unsupported command-level `omit ... in` syntax from `FellerLift`.  Instead the
  `IsOpenPosMeasure` assumption is scoped only to the injectivity theorems, and the unused
  `SecondCountableTopology` assumption is removed from the file.
* Qualified Haar-invariance typeclasses as `[μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]` in
  `GroupHeatKernel` and the latent downstream copy in `AnalyticBridge`; this prevents Lean's
  `autoImplicit` fallback from inventing an unrelated identifier.
* Refactored `KernelSemigroup.transitionKernel_comp` into a small
  `lintegral_transitionKernel` helper plus explicit measurability witnesses.  This removes the
  failed rewrite under a function-product application and avoids the previous `fun_prop`/
  definitional-equality heartbeat blow-up.
* No theorem statement was weakened and no `axiom`, `sorry`, or `admit` was introduced.
* ZIP and TAR.GZ are generated from one canonical v0.8 source tree with fresh checksums.


## v0.7

* Repaired the remaining external v0.6 build failures in `InvariantMetric.lean` and
  `HeatKernelData.lean`; `FellerLift.lean` had already compiled in the supplied v0.6 build.
* Removed every reliance on reducing mathlib's intentionally non-reducible `TangentSpace` synonym
  in the invariant-metric and left-Laplacian layers.
* Rebuilt the left-translation equivalence with the actual differential of left multiplication and
  explicit transport only along proved equalities of base points.
* Added `tangentChartModelEquiv`: the Lie algebra is related to the normed model space through the
  derivative of `extChartAt`, whose derivative is proved invertible by mathlib, followed by
  `NormedSpace.fromTangentSpace` for the genuine normed-vector-space target.
* Re-expressed `leftMetric`, Ad-invariance, `leftDifferential`, `leftHessian`, and the basis-free
  contraction in these explicit chart/model coordinates.  This eliminates the missing
  `InnerProductSpace` instance on `GroupLieAlgebra` without installing an artificial tangent-space
  instance.
* Explicitly transported the codomains of manifold derivatives into `ℝ` and `E →L[ℝ] ℝ` with
  `NormedSpace.fromTangentSpace`, closing the same latent target-tangent mismatch in the first- and
  second-order Laplacian definitions.
* Added a formal differentiability guard for the extended-chart derivative used by the new
  Lie-algebra/model equivalence; the derivative's invertibility is supplied directly by mathlib's
  `isInvertible_mfderiv_extChartAt`.
* Made `MeasurableHeatKernelData.ennDensity` reducible and changed
  `measurable_ennDensity` to an explicit `change`/`exact` proof, resolving the remaining density
  elaboration mismatch.
* Removed the three reported unused-section-variable warnings from `FellerLift` with the `omit`
  declarations suggested by Lean's linter.
* No `axiom`, `sorry`, or `admit` was introduced.  The open second-order differentiability theorem
  for `leftHessian` remains explicit rather than being hidden behind totalised `mfderiv`.
* ZIP and TAR.GZ are regenerated from one canonical v0.7 source tree with fresh checksums.

## v0.6

* Repaired the v0.5 packaging divergence: the v0.5 TAR.GZ contained stale copies of
  `InvariantMetric.lean`, `HeatKernelData.lean`, and `FellerLift.lean`, while the v0.5 ZIP contained
  the intended fixes.
* Opened the `ContDiff` scope in `InvariantMetric.lean`, so the smoothness exponent `∞` and the
  smooth-diffeomorphism notation elaborate in client source.
* Extended the same `ContDiff`-scope repair to every downstream module that uses the smoothness exponent `∞`, preventing the next wave of identical elaboration failures.
* Repaired the three positive-time structure fields in `HeatKernelData.lean` by replacing the
  malformed comma after `t ≠ 0` with implication `→`.
* Applied the same positive-time field repair to both `smooth_density` declarations in `CompactManifoldTheorem.lean`.
* Made the compact-minimum argument in `exists_uniform_positive_lower_bound` explicit by unfolding
  the local function `f` at the final step.
* Repaired `FellerLift.op_zero` and `FellerLift.op_add` by applying
  `ContinuousLinearMap.ext` first and only then using `ContinuousMap.toLp_injective`; this avoids
  over-extensionalising the goal to pointwise scalar equality.
* Regenerated `SHA256SUMS.txt` from the canonical v0.6 source tree and generated both ZIP and
  TAR.GZ from that same tree.
* No mathematical theorem statement was weakened and no proof placeholder was introduced.

## v0.5

* Upgraded the safety dependency to `TotalisationSafety_v04`.
* Removed the HeatKernel-local `mfderiv`/`mfderivWithin` scanner; the shared library now covers manifold derivatives.
* Packaged certified smooth-scalar and conjugation derivatives through `TotalisationSafety.ManifoldDerivativeAt`.
* Removed obsolete audit markers from `lintegral` and ordinary Lie-group inversion.
* Retained `leftHessian` as an explicit reviewed second-order differentiability boundary.
* Retained the broad `kernelAction` integrability issue as a reviewed API boundary.
* Mathematical theorem statements and proof terms outside the audit module are unchanged from v0.4.

## v0.4

* Added `TotalisationSafety_v03` as a sibling Lake dependency (`name = "totalisationSafety"`).
* Added `CompactLieHeatKernel.TotalisationAudit` with project-specific formal guards.
* Added formal nonzero guards for the fixed `1/2` Laplacian factor and positive-time generator
  denominator.
* Added manifold-differentiability guards for smooth scalar functions and Lie-group conjugation.
* Exposed the exact `LeftHessianDifferentiabilityAt` obligation selecting the genuine second-order
  `mfderiv` branch.
* Added `scripts/Audit-HeatKernelTotalisations.ps1`, which runs the shared TotalisationSafety audit
  and then additionally scans for raw `mfderiv`/`mfderivWithin`.
* Reviewed and marked all existing total-operation occurrences.  The combined textual audit has no
  unapproved current occurrence.
* Recorded `leftDifferential`/`leftHessian` and broad `kernelAction` as explicit reviewed API
  boundaries rather than silently certifying them.
* Added dependency bootstrap instructions for Lake's manifest update.
* Mathematical theorem/proof source from v0.3 is unchanged except for trailing audit comments.


## v0.3

* Added `FellerLift` and proved its identity, semigroup law and constant-one preservation from L²
  compatibility and injectivity of `C(M) → L²(M,μ)` under full support.
* Added `CompactManifoldHeatKernelCore` and `CompactManifoldRegularisationData`.
* Removed nonnegativity as an independent regularisation hypothesis; it follows from strict positivity.
* Derived kernel symmetry from L² self-adjointness, Fubini and full-support uniqueness.
* Derived positive-time mass one from preservation of constants.
* Constructed continuous-map-valued convolution rows by Bochner integration.
* Derived Chapman--Kolmogorov against continuous test functions via Fubini.
* Upgraded Chapman--Kolmogorov to pointwise equality using a difference-squared argument and
  full-support uniqueness of continuous functions.
* Converted real Chapman--Kolmogorov to the `ENNReal` identity used by probability kernels.
* Added `KernelSemigroup.lean` and closed the v0.2 transition-kernel composition gap by Tonelli.
* Added `GroupRegularisationData.toGroupHeatKernelData` and
  `HeatSemigroupKernelBridge.ofRegularisation`.
* Repaired the positive-time interface so measurability and nonnegativity no longer impose an
  artificial density condition at `t=0`, where the heat kernel is a Dirac mass.
* Narrowed the sole large point-4 gap to the classical compact-manifold regularisation/strict
  positivity theorem.

## v0.2

* Added real L² strongly continuous symmetric Markov semigroup data.
* Added genuine unbounded generators via mathlib `LinearPMap` and proved density of the domain from
  self-adjointness.
* Added `LaplacianGeneratorBridge`, requiring agreement with `Δ_G/2` on bundled smooth functions.
* Added measurable/continuous/smooth heat-kernel density layers.
* Constructed positive-time `ProbabilityTheory.Kernel`s and proved their Markov property.
* Proved fixed-time uniform positive lower bounds from compactness + strict positivity.
* Added a group heat-kernel layer and centrality consequences.
