# Formalisation Status: Compact Lie Heat Kernel v0.16

v0.16 is a linter-only cleanup on top of the externally successful v0.15 build (3054 jobs). The complete QFT-facing export is now compiler-certified; the only v0.16 Lean change removes the unused `T2Space M` section instance from `CompactManifoldRegularisationData.symmetric`.

## Totalisation-safety status

| Item | Status |
|---|---|
| Shared `TotalisationSafety` dependency | added, sibling path `../TotalisationSafety` |
| Generic textual totalisation regression audit | integrated |
| Shared `mfderiv` / `mfderivWithin` regression scan | integrated in the supplied `TotalisationSafety_v05` bundle |
| Fixed reciprocal `1/2` | formally guarded |
| Generator `1/t` on right derivative | formally guarded for `t>0`; filter excludes `t=0` |
| Extended-chart `mfderiv` | auxiliary formal guard retained; v0.16 chart-model equivalence uses the data-valued chart derivative instead |
| Conjugation `mfderiv` | formally guarded by smoothness/differentiability |
| First `leftDifferential` with an explicit `ContMDiff` witness | formally guarded |
| Second derivative in `leftHessian` | **reviewed open boundary**; exact `MDifferentiableAt` obligation exposed |
| Broad arbitrary-function `kernelAction` | **reviewed API boundary**; intended continuous compact inputs are integrable |
| New unreviewed scanner occurrence | audit failure |

The scanner is not itself a semantic proof.  Formal branch selection is carried by
`CompactLieHeatKernel.TotalisationAudit` where currently available.  See `TOTALISATION_AUDIT.md`.


Status labels:

* **proved in source**: declaration carries a Lean proof term in this project;
* **constructed**: mathematical object/interface is defined without an axiom;
* **external PDE input**: genuinely missing theorem not supplied by current mathlib/project code.

## Points 1--2 retained from v0.1

| Item | Status | Declaration |
|---|---|---|
| Left translation tangent equivalence and left trivialisation | constructed | `leftTranslationTangentEquiv`, `leftTrivialisation` |
| Transported positive symmetric metric | proved/constructed | `leftMetric`, `leftMetric_symm`, `leftMetric_pos` |
| Ad-invariance predicate | constructed | `IsAdInvariantInnerProduct` |
| Basis-free canonical contraction | constructed | `contractDiagonal` |
| ONB formula and basis independence | proved in source | `contractDiagonal_eq_sum`, `sum_diagonal_orthonormalBasis_independent` |
| Left differential/Hessian/Laplacian | constructed | `leftDifferential`, `leftHessian`, `leftLaplacian` |
| ONB formula for group Laplacian candidate | proved in source | `leftLaplacian_eq_sum_leftHessian` |
| Identify Hessian diagonal with `X_v(X_v f)` | open smaller calculus proof | -- |
| Smooth Riemannian metric packaging/right invariance | open geometric proof | -- |

## Point 3: L² semigroup and generator

| Item | Status | Declaration |
|---|---|---|
| Real `L²(μ)` and constant-one vector | constructed | `RealL2`, `oneL2` |
| Strongly continuous symmetric Markov contraction semigroup | constructed interface | `L2SelfAdjointMarkovSemigroup` |
| Time-zero action and commuting time slices | proved in source | `op_zero_apply`, `op_comm` |
| Densely-defined generator via mathlib `LinearPMap` | constructed | `SelfAdjointMarkovGenerator.generator` |
| Density of self-adjoint generator domain | proved from mathlib | `dense_generator_domain` |
| Generator agrees with `Δ_G/2` on smooth core | constructed target | `LaplacianGeneratorBridge` |
| Feller lift compatible with L² semigroup | constructed | `FellerLift` |
| Feller identity at time zero | proved from L² compatibility | `FellerLift.op_zero` |
| Feller semigroup law | proved from L² compatibility/injectivity | `FellerLift.op_add` |
| Feller preservation of constant one | proved from L² compatibility | `FellerLift.op_one` |
| Friedrichs/self-adjoint realisation and semigroup existence | delegated to separate `FriedrichsExtension` project | -- |

## Point 4: compact-manifold heat kernel

| Item | Status | Declaration |
|---|---|---|
| Positive-time density interface no longer constrains `t=0` | repaired | `MeasurableHeatKernelData` |
| Transition kernel from density | constructed | `transitionKernel` |
| Positive-time transition kernel is Markov | proved in source | `transitionKernel_isMarkov` |
| Density CK implies actual kernel composition | proved in source via Tonelli | `MeasurableHeatKernelData.transitionKernel_comp` |
| Reduced Feller/smoothing theorem core | constructed | `CompactManifoldHeatKernelCore` |
| Jointly continuous row family `x ↦ k_t(x,·)` | constructed | `densityContinuousMap`, `densityRows` |
| Positive-time row integrability | proved in source | `densityRow_integrable` |
| Mass one from `P_t 1 = 1` | proved in source | `integral_density_eq_one`, `lintegral_density_eq_one` |
| Continuous convolution row | constructed/proved | `convolutionIntegrand`, `convolutionRow`, `convolutionRow_apply` |
| CK equality against continuous tests | proved by Fubini + Feller semigroup | `integral_convolutionRow_mul` |
| Pointwise real Chapman--Kolmogorov | proved using full support | `real_chapmanKolmogorov` |
| Extended-real Chapman--Kolmogorov | proved in source | `lintegral_chapmanKolmogorov` |
| Full `SmoothHeatKernelData` from reduced core | constructed from proved consequences | `CompactManifoldHeatKernelCore.toSmoothHeatKernelData` |
| Regularisation data tied to an L²-compatible Feller lift | constructed | `CompactManifoldRegularisationData` |
| Nonnegativity from strict positivity | proved in source | `CompactManifoldHeatKernelCore.toSmoothHeatKernelData` |
| Transposed representation from L² self-adjointness | proved in source | `transpose_represents` |
| Kernel symmetry from L² self-adjointness + full support | proved in source | `CompactManifoldRegularisationData.symmetric` |
| Compact-manifold theorem in conditional/existential form | proved in source | `compactManifoldHeatKernel_of_regularisation` |
| Resulting transition kernels form a Markov semigroup | proved in source | `CompactManifoldRegularisationData.transitionKernel_comp` |
| Uniform positive lower bound on compact space | proved in source | `exists_uniform_positive_lower_bound` |

## Lie-group specialisation

| Item | Status | Declaration |
|---|---|---|
| Normalised bi-invariant reference-measure boundary | explicit | `GroupHeatKernelData` parameters |
| `k_t(x,y)=q_t(x⁻¹y)` | proved in source | `density_eq_centralDensity` |
| inversion symmetry of `q_t` | proved in source | `centralDensity_inv` |
| conjugation invariance / centrality | proved in source | `centralDensity_conj` |
| uniform positive lower bound for central `q_t` | proved in source | `exists_uniform_central_lower_bound` |
| uniform finite upper bound for central `q_t` | proved in source | `exists_uniform_central_upper_bound` |
| central density continuity/measurability | proved in source | `centralDensity_continuous`, `centralDensity_measurable` |
| central density integrability and mass one | proved in source | `centralDensity_integrable`, `lintegral_centralDensity_eq_one`, `integral_centralDensity_eq_one` |
| one-variable central Chapman--Kolmogorov | proved in real and ENNReal forms | `centralDensity_chapmanKolmogorov`, `integral_centralDensity_chapmanKolmogorov` |
| QFT-facing central-kernel package | constructed from group kernel | `CentralHeatKernelData`, `GroupHeatKernelData.toCentralHeatKernelData` |
| Group regularisation data -> complete group kernel | constructed | `GroupRegularisationData.toGroupHeatKernelData` |
| Regularisation data -> old generator/kernel bridge | constructed; representation derived | `HeatSemigroupKernelBridge.ofRegularisation` |

## Exact remaining compact-manifold theorem

The project no longer needs nonnegativity, symmetry, mass one, Chapman--Kolmogorov, kernel
composition, or the Feller semigroup law as external heat-kernel assumptions.  They are theorems.

The remaining external PDE statement is precisely the construction of
`CompactManifoldRegularisationData` for the heat semigroup of the compact connected Riemannian
manifold/Lie group.  Concretely one still needs to prove:

1. the self-adjoint heat semigroup regularises into continuous functions, giving an L²-compatible
   `FellerLift`;
2. for every `t>0`, that Feller operator has a jointly smooth density;
3. the density is strictly positive on a connected manifold;
4. in the Lie-group case, the density is invariant under simultaneous left and right translations.

Current mathlib does not contain the compact-manifold elliptic/parabolic regularity, compact-resolvent
spectral package, or strong maximum principle required to establish these statements intrinsically.
No axiom is introduced in their place in the library proper.  Since v0.17 the opt-in module
`CompactLieHeatKernel/Literature/HeatKernel.lean` imports the whole bridge from the literature as
one axiom; since v0.18 the opt-in module `CompactLieHeatKernel/Literature/GaussianBounds.lean`
imports the small-time Gaussian bounds as two axioms; see `LITERATURE_AXIOMS.md`.
