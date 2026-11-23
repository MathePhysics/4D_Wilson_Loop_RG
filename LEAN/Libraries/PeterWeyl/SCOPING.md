# PeterWeyl: scoping pass (2026-09-17)

Status: **paused after M3 (2026-09-17).**  `Basic`, M1, M2 and M3 are written and built; M4–M9 were
not carried out, because the heat kernel is assumed in `FiniteVolumeYM2Phi42`.  See `STATUS.md` for
what changed against this note.  The rest of this note is the original plan.  All mathlib names below were checked against mathlib `8d52ea9a` in the
`FiniteVolumeYM2Phi42` environment, and all statements below were typechecked (see "How the
statements were checked").

## Verdict

Milestone 1 (Peter–Weyl for compact groups, uniform and `L²` density of matrix coefficients) is
worth doing and is of moderate size: **1,200–2,000 lines** in four modules after `Basic`.  Mathlib
supplies the two heavy inputs, the spectral theorem for compact self-adjoint operators and the
Arzelà–Ascoli theorem, and several expected obstacles turned out not to exist:

* Right invariance and inversion invariance of Haar measure on a compact group are not in
  mathlib, but follow in a few lines from the modular character and from uniqueness of Haar
  measure.  `Basic` proves both as instances.
* Second countability is **not** needed.  The adjoint formula swaps integrals of continuous
  functions on `G × G`, and `MeasureTheory.integral_integral_swap_of_hasCompactSupport` does this
  without σ-finiteness or second countability.  `ContinuousMap.toLp_denseRange` needs only
  `NormalSpace G` and `μ.WeaklyRegular`, both found by instance search for a compact group with a
  Haar measure, even without `T2Space`.
* The analytic estimates of M1 need almost no integration theory: `(φ ⋆ f) x` is the `L²` inner
  product of `f` with the kernel row `kernelRow φ x`, and `x ↦ kernelRow φ x` is continuous into
  `C(G, ℂ)` by currying (`Basic.convolutionFun_eq_inner`, `Basic.continuous_kernelRow`).
  Linearity, continuity, the supremum bound and equicontinuity are then one-line consequences of
  Cauchy–Schwarz.

The later milestones towards the heat kernel are much larger, and the convergence and positivity
of the heat series is research-level for mathlib (see "Later milestones").

## Setup

* The library is compiled through `Projects/FiniteVolumeYM2Phi42`, which lists it as a path
  dependency.  Check a module with
  `lake env lean ../../Libraries/PeterWeyl/PeterWeyl/<Module>.lean` and build it for importing with
  `lake build PeterWeyl.<Module>`, both from the host root.
* The root file `PeterWeyl.lean` imports `Basic`, `ConvolutionOperator`, `InvariantSubspaces` and
  `ApproximateIdentity`.
* The lakefile has no dependency on `../TotalisationSafety`.  The textual audit script works on
  the directory without it; a path dependency is needed only if proof-carrying wrappers from that
  library are used.

## `PeterWeyl.Basic` (done)

`PeterWeyl/Basic.lean`, 616 lines, compiles with no output and builds with
`lake build PeterWeyl.Basic`.  Axioms: `propext`, `Classical.choice`, `Quot.sound`.  One audited
line (the Bochner integral in `convolutionFun`).  Namespace `PeterWeyl`.

Standing assumptions of the library (each declaration takes only what it uses):

```lean
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]
```

`T2Space G` is needed only for point separation (M4).

Shared declarations (signatures abbreviated: implicit variables and some instance arguments are
omitted; see the file for the exact forms):

```lean
-- Haar measure (compact group, Borel)
instance isMulRightInvariant_of_compactSpace (μ : Measure G) [μ.IsHaarMeasure] :
  μ.IsMulRightInvariant
instance isInvInvariant_of_compactSpace (μ : Measure G) [μ.IsHaarMeasure] : μ.IsInvInvariant
def haarProbability (G) : Measure G              -- with IsHaarMeasure, IsProbabilityMeasure
theorem eq_haarProbability (μ) [μ.IsHaarMeasure] [IsProbabilityMeasure μ] :
  μ = haarProbability G

-- Right translation [IsTopologicalGroup G] [CompactSpace G]
def rightTranslate : G →* (C(G, ℂ) ≃ₗᵢ[ℂ] C(G, ℂ))           -- rightTranslate g f x = f (x * g)
theorem continuous_rightTranslate_apply (f : C(G, ℂ)) : Continuous fun g => rightTranslate g f
-- [BorelSpace G] (μ) [μ.IsMulRightInvariant]
def rightTranslateL2 : G →* (Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ)
theorem coeFn_rightTranslateL2 (g) (f : Lp ℂ 2 μ) :
  rightTranslateL2 μ g f =ᵐ[μ] fun x => f (x * g)
theorem rightTranslateL2_toLp [CompactSpace G] [IsFiniteMeasure μ] (g) (f : C(G, ℂ)) :
  rightTranslateL2 μ g (ContinuousMap.toLp 2 μ ℂ f) = ContinuousMap.toLp 2 μ ℂ (rightTranslate g f)
theorem continuous_rightTranslateL2_apply [CompactSpace G] [μ.IsHaarMeasure] (f : Lp ℂ 2 μ) :
  Continuous fun g => rightTranslateL2 μ g f
def rightRegular [μ.IsMulRightInvariant] : Representation ℂ G (Lp ℂ 2 μ)
theorem isContinuousUnitary_rightRegular [CompactSpace G] [μ.IsHaarMeasure] :
  IsContinuousUnitary (rightRegular μ)

-- Representations [TopologicalSpace G]
structure IsContinuousUnitary {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (ρ : Representation ℂ G V) : Prop where
  continuous_apply : ∀ v : V, Continuous fun g => ρ g v
  inner_map_map : ∀ (g : G) (v w : V), ⟪ρ g v, ρ g w⟫_ℂ = ⟪v, w⟫_ℂ
def IsContinuousUnitary.coeff (hρ : IsContinuousUnitary ρ) (v w : V) : C(G, ℂ)  -- g ↦ ⟪w, ρ g v⟫
theorem IsContinuousUnitary.subrepresentation (hρ) (σ : Subrepresentation ρ) :
  IsContinuousUnitary σ.toRepresentation
structure FDUnitaryRep (G) [Group G] [TopologicalSpace G] where
  V : Type
  [instNormedAddCommGroup : NormedAddCommGroup V]
  [instInnerProductSpace : InnerProductSpace ℂ V]
  [instFiniteDimensional : FiniteDimensional ℂ V]
  ρ : Representation ℂ G V
  isContinuousUnitary : IsContinuousUnitary ρ
def FDUnitaryRep.coeff (π : FDUnitaryRep G) (v w : π.V) : C(G, ℂ)
def matrixCoefficients (G) : Submodule ℂ C(G, ℂ) :=
  Submodule.span ℂ {f | ∃ (π : FDUnitaryRep G) (v w : π.V), π.coeff v w = f}
theorem IsContinuousUnitary.coeff_mem_matrixCoefficients {V : Type*} [...]
  [FiniteDimensional ℂ V] (hρ : IsContinuousUnitary ρ) (v w : V) :
  hρ.coeff v w ∈ matrixCoefficients G
theorem const_mem_matrixCoefficients (c : ℂ) : ContinuousMap.const G c ∈ matrixCoefficients G
theorem star_mem_matrixCoefficients (hf : f ∈ matrixCoefficients G) :
  star f ∈ matrixCoefficients G
theorem rightTranslate_mem_matrixCoefficients (hf : f ∈ matrixCoefficients G) (g : G) :
  rightTranslate g f ∈ matrixCoefficients G
def transportRep (e : V ≃ₗᵢ[ℂ] W) (ρ : Representation ℂ G V) : Representation ℂ G W
def conjRep (ρ : Representation ℂ G (EuclideanSpace ℂ ι)) : Representation ℂ G (EuclideanSpace ℂ ι)

-- Convolution
def adjointKernel (φ : C(G, ℂ)) : C(G, ℂ)                      -- g ↦ conj (φ g⁻¹)
def kernelRow (φ : C(G, ℂ)) (x : G) : C(G, ℂ)                  -- y ↦ conj (φ (x * y⁻¹))
theorem continuous_kernelRow (φ) : Continuous (kernelRow φ)
def convolutionFun (μ) (φ : C(G, ℂ)) (f : G → ℂ) (x : G) : ℂ   -- ∫ y, φ (x * y⁻¹) * f y ∂μ
theorem convolutionFun_congr_ae (φ) (h : f =ᵐ[μ] f') : convolutionFun μ φ f = convolutionFun μ φ f'
theorem integrable_convolutionFun_integrand [CompactSpace G] [IsFiniteMeasure μ] (φ)
  (hf : MemLp f 2 μ) (x) : Integrable (fun y => φ (x * y⁻¹) * f y) μ
theorem convolutionFun_eq_inner [CompactSpace G] [IsFiniteMeasure μ] (φ) (f : Lp ℂ 2 μ) (x) :
  convolutionFun μ φ f x = ⟪ContinuousMap.toLp 2 μ ℂ (kernelRow φ x), f⟫_ℂ
```

### Design decisions

* **Representations.**  `Representation ℂ G V` (mathlib's `G →* V →ₗ[ℂ] V`) plus a `Prop`
  predicate `IsContinuousUnitary`, so that mathlib's `Subrepresentation`, `IsIrreducible`, Schur's
  lemma (`Representation.IsIrreducible.bijective_or_eq_zero`,
  `finrank_intertwiningMap_self`), `Representation.character` and `Representation.tprod` apply
  unchanged in M5–M6.  Mathlib's `ContRepresentation` is not used: it does not ask for continuity
  in `g`.
* **Universes.**  `FDUnitaryRep G` has carrier in `Type`, so `matrixCoefficients` quantifies over
  a single universe.  Eigenspaces of operators on `L²(G)` live in the universe of `G`;
  `IsContinuousUnitary.coeff_mem_matrixCoefficients` transports any finite-dimensional
  representation to `EuclideanSpace ℂ (Fin n)` along `stdOrthonormalBasis`, so no universe lifting
  is ever needed downstream.
* **Matrix coefficients** are `g ↦ ⟪w, ρ g v⟫` (mathlib's inner product is conjugate linear in
  the first argument), so they are linear in `v`.
* **Convolution operator** is factored as `T_φ = toLp ∘ S_φ` with `S_φ : Lp ℂ 2 μ →L[ℂ] C(G, ℂ)`.
  The continuous representative is then built in, compactness of `S_φ` gives compactness of
  `T_φ` (`IsCompactOperator.continuous_comp`), and M4's "`L²` convergence becomes uniform
  convergence" is just continuity of `S_φ`.
* **Kernels** are complex (`C(G, ℂ)`); approximate identities are real kernels composed with
  `Complex.ofReal`.

## M1 `ConvolutionOperator`

Hypotheses: standing ones without `T2Space`.  The adjoint formula uses neither invariance nor
second countability; right equivariance uses right invariance.

```lean
def convolutionC (φ : C(G, ℂ)) : Lp ℂ 2 μ →L[ℂ] C(G, ℂ)
theorem convolutionC_apply (φ) (f : Lp ℂ 2 μ) (x : G) :
    convolutionC μ φ f x = convolutionFun μ φ f x
theorem norm_convolutionC_le (φ) : ‖convolutionC μ φ‖ ≤ ‖φ‖
theorem equicontinuous_convolutionC (φ) :
    Equicontinuous fun f : Metric.closedBall (0 : Lp ℂ 2 μ) 1 => convolutionFun μ φ f
theorem isCompactOperator_convolutionC (φ) : IsCompactOperator (convolutionC μ φ)
theorem convolutionC_rightTranslateL2 (φ) (g : G) (f : Lp ℂ 2 μ) :
    convolutionC μ φ (rightTranslateL2 μ g f) = rightTranslate g (convolutionC μ φ f)
def convolutionOperator (φ : C(G, ℂ)) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (ContinuousMap.toLp 2 μ ℂ).comp (convolutionC μ φ)
theorem isCompactOperator_convolutionOperator (φ) : IsCompactOperator (convolutionOperator μ φ)
theorem convolutionOperator_rightTranslateL2 (φ) (g) (f) :
    convolutionOperator μ φ (rightTranslateL2 μ g f) =
      rightTranslateL2 μ g (convolutionOperator μ φ f)
theorem adjoint_convolutionOperator (φ) :
    ContinuousLinearMap.adjoint (convolutionOperator μ φ) = convolutionOperator μ (adjointKernel φ)
theorem isSelfAdjoint_convolutionOperator {φ} (hφ : adjointKernel φ = φ) :
    IsSelfAdjoint (convolutionOperator μ φ)
-- optional: uniform modulus
theorem exists_nhds_one_convolutionFun_sub_le (φ) (ε) (hε : 0 < ε) : ∃ U ∈ 𝓝 (1 : G),
    ∀ x x', x' * x⁻¹ ∈ U → ∀ f : Lp ℂ 2 μ, ‖f‖ ≤ 1 →
      ‖convolutionFun μ φ f x' - convolutionFun μ φ f x‖ ≤ ε
```

Plan and mathlib lemmas.

* `convolutionC`: `LinearMap.mkContinuous` on `f ↦ ⟨convolutionFun μ φ f, _⟩`.  By
  `convolutionFun_eq_inner` the map is `f ↦ (x ↦ ⟪toLp (kernelRow φ x), f⟫)`: linearity from
  `inner_add_right`, `inner_smul_right`; continuity in `x` from `continuous_kernelRow`,
  `ContinuousLinearMap.continuous` and `Continuous.inner`; the bound from `norm_inner_le_norm`,
  `ContinuousMap.norm_le`, and `ContinuousMap.toLp_norm_le` (operator norm
  `≤ measureUnivNNReal μ ^ p.toReal⁻¹`, which is `1` for a probability measure; the `toReal` line
  needs an audit marker) and `kernelRow` having supremum norm `‖φ‖` (`norm_comp_mulRight`-style).
* Equicontinuity: `‖S f x' − S f x‖ ≤ ‖kernelRow φ x' − kernelRow φ x‖ · ‖f‖`, and continuity of
  `kernelRow φ` at `x`.  Compactness: `BoundedContinuousFunction.arzela_ascoli` through
  `ContinuousMap.linearIsometryBoundedOfCompact`, with pointwise range in the closed ball of
  radius `‖φ‖` (`ProperSpace ℂ`), then `isCompactOperator_iff_isCompact_closure_image_closedBall`.
  The alternative is `ArzelaAscoli.isCompact_closure_of_isClosedEmbedding`.
* Right equivariance: `MeasureTheory.integral_mul_right_eq_self` with `y ↦ y * g`, after
  `convolutionFun_congr_ae` and `coeFn_rightTranslateL2`.
* Adjoint: `ContinuousLinearMap.eq_adjoint_iff`.  For continuous `f`, `h`,
  `MeasureTheory.ContinuousMap.inner_toLp` (note the namespace) turns both sides into iterated integrals of continuous functions on
  `G × G`, swapped by `integral_integral_swap_of_hasCompactSupport` with
  `HasCompactSupport.of_compactSpace`; then `integral_conj`, `integral_const_mul`.  Extend to
  `L²` by `DenseRange.induction_on₂` (closed predicate) with `ContinuousMap.toLp_denseRange`.
  Self-adjointness: `IsSelfAdjoint` is `adjoint T = T`
  (`ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric` if the symmetric form is preferred).
* Optional uniform modulus: `IsTopologicalGroup.rightUniformSpace` as a local instance,
  `CompactSpace.uniformContinuous_of_continuous`, `uniformity_eq_comap_nhds_one'`.

Size: **350–600 lines.**  Difficulty: moderate.

Risks.

* Coercion bookkeeping between `C(G, ℂ)`, `α →ᵇ ℂ` and `Lp` (three function coercions,
  `toAEEqFun`).  `simp` rewrites `↑↑(toLp f)` to `toAEEqFun` before an a.e. hypothesis can fire;
  use `rw` with `ContinuousMap.coeFn_toLp` first (already met in `Basic`).
* The norm topology of `C(G, ℂ)` must be the compact-open topology for currying to give continuity.
  It is definitionally so at this commit (`Basic.continuous_kernelRow` relies on it).
* Arzelà–Ascoli is stated for bounded continuous functions; transporting compactness of closures
  along `linearIsometryBoundedOfCompact` costs some lines.

## M2 `InvariantSubspaces`

Hypotheses: standing ones without `T2Space`.

```lean
/-- `T` commutes with right translations. -/
def CommutesRight (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) : Prop :=
  ∀ (g : G) (f : Lp ℂ 2 μ), T (rightTranslateL2 μ g f) = rightTranslateL2 μ g (T f)
theorem rightTranslateL2_mem_eigenspace {T} (hT : CommutesRight μ T) (c : ℂ) (g : G)
    {f : Lp ℂ 2 μ} (hf : f ∈ Module.End.eigenspace (T : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ) c) :
    rightTranslateL2 μ g f ∈ Module.End.eigenspace (T : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ) c
def eigenSubrep {T} (hT : CommutesRight μ T) (c : ℂ) : Subrepresentation (rightRegular μ)
theorem eigenSubrep_toSubmodule : (eigenSubrep μ hT c).toSubmodule =
    Module.End.eigenspace (T : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ) c
theorem finiteDimensional_eigenSubrep (hK : IsCompactOperator T) (hc : c ≠ 0) :
    FiniteDimensional ℂ (eigenSubrep μ hT c).toSubmodule
theorem exists_mem_matrixCoefficients_of_mem_eigenspace (φ : C(G, ℂ)) {c : ℂ} (hc : c ≠ 0)
    {f : Lp ℂ 2 μ}
    (hf : f ∈ Module.End.eigenspace (convolutionOperator μ φ : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ) c) :
    ∃ F ∈ matrixCoefficients G, ContinuousMap.toLp 2 μ ℂ F = f
```

Plan.

* Invariance: `Module.End.mem_eigenspace_iff` and `hT`.  `eigenSubrep` is the structure
  `Subrepresentation` with that submodule.  Continuity and unitarity:
  `(isContinuousUnitary_rightRegular μ).subrepresentation _`, already in `Basic`.
* Finite dimension: `ContinuousLinearMap.finite_dimensional_eigenspace` (compact, `c ≠ 0`, no
  self-adjointness needed).
* Matrix coefficient.  Put `F := c⁻¹ • convolutionC μ φ f`, so `toLp F = f`.  Then
  `F g = F (1 * g) = (rightTranslate g F) 1 = c⁻¹ • convolutionC μ φ (R_g f) 1` by
  `convolutionC_rightTranslateL2`.  On the finite-dimensional eigenspace `E`, the functional
  `e ↦ c⁻¹ • convolutionC μ φ e 1` is represented by some `w ∈ E`
  (`InnerProductSpace.toDual` on `E`, complete since finite-dimensional, or directly
  `OrthonormalBasis.sum_repr'` with `stdOrthonormalBasis`).  Hence `F = hσ.coeff ⟨f, hf⟩ w` and
  `IsContinuousUnitary.coeff_mem_matrixCoefficients` concludes.  Evaluation at `1`:
  `ContinuousMap.evalCLM`.  The scalar `c⁻¹` needs an audit marker (reason `c ≠ 0`), or use
  `Units.mk0`.

Size: **300–500 lines.**  Difficulty: moderate, mostly subtype and coercion management.

Risks.  Subtype coercions `↥(eigenspace ...)` inside `Lp` inside functions; `Module.End.eigenspace`
of `(T : Lp →ₗ Lp)` versus `T` as a continuous linear map (mathlib's spectral lemmas use the
coercion `↑T`, so keep that form everywhere).

## M3 `ApproximateIdentity`

Hypotheses: standing ones without `T2Space`.  Write
`complexify ψ := (ContinuousMap.mk ((↑) : ℝ → ℂ) Complex.continuous_ofReal).comp ψ`.

```lean
theorem exists_approxKernel {U : Set G} (hU : U ∈ 𝓝 (1 : G)) :
    ∃ ψ : C(G, ℝ), (∀ g, 0 ≤ ψ g) ∧ tsupport ψ ⊆ U ∧ (∀ g, ψ g⁻¹ = ψ g) ∧ ∫ g, ψ g ∂μ = 1
theorem adjointKernel_complexify {ψ : C(G, ℝ)} (hψ : ∀ g, ψ g⁻¹ = ψ g) :
    adjointKernel (complexify ψ) = complexify ψ
theorem exists_nhds_one_convolutionFun_approx (f : C(G, ℂ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ U ∈ 𝓝 (1 : G), ∀ ψ : C(G, ℝ), (∀ g, 0 ≤ ψ g) → tsupport ψ ⊆ U → ∫ g, ψ g ∂μ = 1 →
      ∀ x, ‖convolutionFun μ (complexify ψ) f x - f x‖ ≤ ε
```

Plan.

* Kernel: shrink `U` to a closed symmetric neighbourhood `V` (`exists_nhds_one_split`,
  `inv_mem_nhds_one`, closure inside `U` by regularity); Urysohn
  `exists_continuous_one_zero_of_isCompact` with `s = {1}` and `t` the complement of the interior
  of `V` (or `exists_tsupport_one_of_isOpen_isClosed`, needs only `R1Space`); symmetrise
  `ψ + ψ ∘ inv`; positivity of the integral by
  `Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero`; divide by it (audit marker,
  reason: integral positive).
* Approximation: `∫ ψ (x * y⁻¹) dy = 1` from `integral_mul_right_eq_self` and
  `integral_inv_eq_self`, so `ψ ⋆ f x − f x = ∫ ψ (x * y⁻¹) (f y − f x) dy`; on the support
  `x * y⁻¹ ∈ U`; conclude by uniform continuity of `f` (as in the optional part of M1) and
  `norm_integral_le_of_norm_le`.

Size: **250–400 lines.**  Difficulty: low to moderate.  Risk: Urysohn variants differ in their
separation hypotheses; `RegularSpace G` and `LocallyCompactSpace G` are available, `T2Space` is not
assumed.

## M4 `PeterWeyl`

Hypotheses: standing ones; `T2Space G` only for the last statement.

```lean
theorem matrixCoefficients_topologicalClosure : (matrixCoefficients G).topologicalClosure = ⊤
theorem dense_matrixCoefficients : Dense (matrixCoefficients G : Set C(G, ℂ))
theorem matrixCoefficients_toLp_topologicalClosure :
    ((matrixCoefficients G).map (ContinuousMap.toLp (E := ℂ) 2 μ ℂ).toLinearMap).topologicalClosure
      = ⊤
theorem exists_fdUnitaryRep_ne_one [T2Space G] {g : G} (hg : g ≠ 1) :
    ∃ π : FDUnitaryRep G, π.ρ g ≠ 1
```

`matrixCoefficients_topologicalClosure` needs no measure in its statement: apply the proof to
`haarProbability G`.

Plan.

1. Given `f : C(G, ℂ)` and `ε`, M3 gives a symmetric kernel `φ = complexify ψ` with
   `‖φ ⋆ f − f‖∞ ≤ ε`; `φ ⋆ f = convolutionC μ φ (toLp f)` (`convolutionFun_congr_ae`,
   `ContinuousMap.coeFn_toLp`).
2. `T = convolutionOperator μ φ` is compact and self-adjoint (M1, M3).  By
   `ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot` and
   `Submodule.orthogonal_eq_bot_iff`, `Submodule.topologicalClosure_eq_top_iff`, the sum of all
   eigenspaces is dense in `L²`.  So there is `h` in it with `‖toLp f − h‖₂ ≤ ε / ‖φ‖`, and
   `h = ∑ c ∈ s, h_c` with `h_c` in the eigenspace of `c` (`Submodule.mem_iSup_iff_exists_finset`).
3. `convolutionC μ φ h_0 = 0`: `toLp (convolutionC μ φ h_0) = T h_0 = 0` and
   `ContinuousMap.toLp_injective` (Haar measure is `IsOpenPosMeasure`).  For `c ≠ 0`,
   `convolutionC μ φ h_c = c • F_c` with `F_c ∈ matrixCoefficients G` by M2 (and
   `ContinuousMap.toLp_injective`).  So `convolutionC μ φ h ∈ matrixCoefficients G`.
4. `‖φ ⋆ f − convolutionC μ φ h‖∞ ≤ ‖φ‖ · ‖toLp f − h‖₂ ≤ ε` by `norm_convolutionC_le`.
   Conclude with `Metric.mem_closure_iff` and `Submodule.topologicalClosure_coe`.
5. `L²` version: `DenseRange.topologicalClosure_map_submodule` with
   `ContinuousMap.toLp_denseRange`, exactly as mathlib's `span_fourierLp_closure_eq_top`.
6. Separation: `exists_continuous_zero_one_of_isClosed` (compact Hausdorff is normal) gives `f`
   with `f 1 ≠ f g`; approximate within a third of the gap; some generator `π.coeff v w` differs
   at `1` and `g`, so `π.ρ g ≠ 1`.

Size: **300–500 lines.**  Difficulty: moderate.  Risks: the finite eigen-decomposition in step 2 is
the fiddliest part (finset sums of submodule elements, `Module.End.eigenspace` indexed by all
`c : ℂ` including non-eigenvalues).  Dividing by `‖φ‖` needs `φ ≠ 0` or a `max 1 ‖φ‖` trick.

## How the statements were checked

The file
`C:\Users\marti\AppData\Local\Temp\claude\C--Users-marti-Documents-Scientia-Mathematics-Lean\9cbb2fd1-5197-43f7-a750-25a321ec4246\scratchpad\peterweyl\Statements.lean`
(outside the library, no `sorry`) imports `PeterWeyl.Basic` and compiles with no output.  Since
`convolutionC` and `convolutionOperator` do not exist yet, it states each theorem as
`def Statement_Mk : Prop`, with the future operator replaced by a universally quantified
`S : Lp ℂ 2 μ →L[ℂ] C(G, ℂ)` satisfying `∀ f x, S f x = convolutionFun μ φ f x`, and
`convolutionOperator` by `(ContinuousMap.toLp 2 μ ℂ).comp S`:

* M1: `Statement_M1_bound`, `Statement_M1_equicontinuous`, `Statement_M1_uniform_modulus`,
  `Statement_M1_convolutionC`, `Statement_M1_convolutionOperator`, `Statement_M1_adjoint`,
  `Statement_M1_isSelfAdjoint`;
* M2: `Statement_M2_eigenspace`, `Statement_M2_eigenSubrep`, `Statement_M2_eigenRep`,
  `Statement_M2_mem_matrixCoefficients`;
* M3: `Statement_M3_exists_kernel`, `Statement_M3_adjointKernel`, `Statement_M3_approx`;
* M4: `Statement_M4_dense`, `Statement_M4_dense'`, `Statement_M4_dense_L2`,
  `Statement_M4_separates`;
* M5–M6 sketches: `Statement_M5_schur_inequivalent`, `Statement_M5_schur_self`,
  `Statement_M6_class_functions`.

The same file checks by `example` that instance search finds `μ.IsMulRightInvariant`,
`μ.IsInvInvariant`, `μ.Regular`, `μ.WeaklyRegular`, `NormalSpace G` and `CompleteSpace (Lp ℂ 2 μ)`
without `T2Space` or second countability; that `ContinuousMap.toLp_denseRange` and
`ContinuousMap.toLp_injective` apply; that `integral_integral_swap_of_hasCompactSupport` applies
on `G × G`; and that the coefficient of a finite-dimensional subrepresentation of `rightRegular μ`
lies in `matrixCoefficients G` through `Basic` alone.

## Later milestones towards the heat kernel

The target is `q_t = ∑_π d_π e^{-t c_π / 2} χ_π` on a compact Lie group.  Estimates assume
M1–M4 done and count new library code only.

### M5 Schur orthogonality and complete reducibility (800–1,300 lines)

```lean
theorem integral_coeff_mul_conj_coeff_of_irreducible (π : FDUnitaryRep G)
    [Representation.IsIrreducible π.ρ] (v w v' w' : π.V) :
    ∫ g, π.coeff v w g * conj (π.coeff v' w' g) ∂μ =
      ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (Module.finrank ℂ π.V : ℂ)
theorem integral_coeff_mul_conj_coeff_eq_zero (π σ : FDUnitaryRep G) (irreducibility)
    (h : ∀ A : π.V →ₗ[ℂ] σ.V, (∀ g, A ∘ₗ π.ρ g = σ.ρ g ∘ₗ A) → A = 0) (v w v' w') :
    ∫ g, π.coeff v w g * conj (σ.coeff v' w' g) ∂μ = 0
```

Averaging `∫ σ g ∘ A ∘ π g⁻¹ dμ` (Bochner integral in a finite-dimensional space of linear maps)
gives an intertwiner; Schur's lemma is in mathlib (`Representation.IsIrreducible`,
`bijective_or_eq_zero`, `finrank_intertwiningMap_self` over an algebraically closed field).
Complete reducibility: the orthogonal complement of a subrepresentation of a unitary
representation is a subrepresentation; induction on `finrank`.  Consequence: `matrixCoefficients`
is spanned by coefficients of irreducible representations.  Gaps: no unitary-representation API
(orthogonal complements, unitary equivalence), no operator-valued averaging in mathlib's
representation theory.  Closure under products (tensor products,
`TensorProduct.instInnerProductSpace`, `TensorProduct.inner_tmul`, `Representation.tprod`) is a
cheap side result (100–200 lines) making `matrixCoefficients` a star subalgebra.

### M6 Characters and class functions (800–1,500 lines)

Characters `χ_π = Representation.character π.ρ` as continuous functions; orthonormality from M5;
the conjugation average `f ↦ ∫ f (h g h⁻¹) dh` maps `C(G, ℂ)` onto continuous class functions and
the coefficients of an irreducible `π` into `ℂ χ_π` (Schur), so M4 gives density of characters in
continuous class functions (`Statement_M6_class_functions`) and an orthonormal basis of the
closed subspace of central `L²` functions (`HilbertBasis`, `IsHilbertSum`).  Gaps: a unitary dual
type (quotient of irreducible `FDUnitaryRep G` by unitary equivalence, in `Type 1` or `Type u`),
its countability for second countable `G`, and the statement that the character determines the
class.

### M7 Smoothness of representations of Lie groups (1,500–3,000 lines)

A continuous finite-dimensional representation of a Lie group is smooth, and its derived
representation `dπ : 𝔤 → End V` is a Lie algebra homomorphism.  Route: `t ↦ π (exp (t • X))` is a
continuous one-parameter group in `GL(V)`, hence `t ↦ NormedSpace.exp (t • A)` (integrate over a
short interval to get differentiability); then smoothness of `π` near `1` through the exponential
chart of `LieGroupExponential.ExpChart`, and everywhere by translation.  The homomorphism property
of `dπ` needs `Ad`/`ad` compatibility, available only partly (`LieGroupExponential.Naturality`
gives `g * exp v * g⁻¹ = exp (Ad g v)`).  Gaps: no continuous-to-smooth theorem for homomorphisms,
no closed subgroup theorem, no Lie group structure on `SU(N)` in mathlib.  Depends on
`LieGroupExponential`, whose `Smoothness` and `ExpChart` modules are the relevant inputs.

### M8 Casimir and Laplacian eigenvalues (1,000–2,000 lines)

For an `Ad`-invariant inner product on `𝔤` (average any inner product over `G` with
`haarProbability`, cheap once M7 gives continuity of `Ad`) and an orthonormal basis `X_i`, the
Casimir `C_π = ∑ dπ(X_i)^2` commutes with `π` and is `−c_π · id` by Schur, `c_π ≥ 0` since
`dπ(X)` is skew-adjoint.  The left-invariant Laplacian applied to `g ↦ ⟪w, π g v⟫` gives
`−c_π` times it.  Connecting to `CompactLieHeatKernel.leftLaplacian` (real valued, through
`leftHessian`) needs the second derivative along `t ↦ g * exp (t • X)`, which is exactly the
second-order manifold calculus that `CompactLieHeatKernel` records as open
(`LeftHessianDifferentiabilityAt`), and `IsAdInvariantInnerProduct` there is a hypothesis.  Gaps:
second-order `mfderiv` calculus along curves, universal enveloping algebra action (avoidable).

### M9 The heat series (conditional part 1,000–2,000 lines; unconditional part out of scope)

* *Conditional identification.*  Given the heat semigroup and a continuous central kernel from
  `CompactLieHeatKernel` data (`GroupHeatKernelData`, `LaplacianGeneratorBridge`), the kernel's
  character coefficients are `d_π e^{-t c_π/2}`: smooth matrix coefficients are eigenvectors of
  the generator (M7, M8), and an eigenvector of the generator of a strongly continuous semigroup
  is an eigenvector of the semigroup.  Mathlib has no C₀-semigroup theory; this one implication is
  a short ODE uniqueness argument (200–400 lines).  Uniform convergence for `t > 0` then follows
  from positive definiteness of `q_t = q_{t/2} ⋆ q_{t/2}` and a Godement-type identity
  `∑_π d_π^2 e^{-t c_π/2} = q_t(1)` (600–1,000 lines on top of M6).
* *Unconditional convergence* (without an analytically constructed kernel) needs
  `∑_π d_π^2 e^{-t c_π/2} < ∞`, i.e. either the Weyl dimension formula and highest weight theory
  (roots, weights, classification of irreducibles; mathlib has `RootPairing` but nothing on
  representations of compact Lie groups), or Sobolev embedding and elliptic regularity on a
  compact manifold.  Either is well beyond 10,000 lines at the current state of mathlib.
* *Positivity* `q_t > 0` is not visible from the series.  It needs the Markov property of the
  semigroup (Beurling–Deny or a maximum principle) and strict positivity from connectedness,
  which is analytic gap B of `CompactLieHeatKernel`.  Nonnegativity alone is also not a
  consequence of positive definiteness.

## Overall estimate and risks

| Milestone | Content | Lines |
|---|---|---|
| `Basic` | shared definitions and closure lemmas | done (616) |
| M1 `ConvolutionOperator` | `convolutionC`, bound, compactness, equivariance, adjoint | 350–600 |
| M2 `InvariantSubspaces` | eigen-subrepresentations, matrix coefficients | 300–500 |
| M3 `ApproximateIdentity` | kernels, uniform approximation | 250–400 |
| M4 `PeterWeyl` | uniform and `L²` density, point separation | 300–500 |
| M5 | Schur orthogonality, complete reducibility, products | 800–1,300 |
| M6 | characters, class functions | 800–1,500 |
| M7 | smoothness of representations of Lie groups | 1,500–3,000 |
| M8 | Casimir, Laplacian eigenvalues | 1,000–2,000 |
| M9 | heat series, conditional on kernel data | 1,000–2,000 |

Design risks.

* **Two instances in `Basic`** (`isMulRightInvariant_of_compactSpace`,
  `isInvInvariant_of_compactSpace`) are global.  If mathlib adds the same facts, the duplicates are
  harmless but should then be removed.
* **Carrier in `Type`.**  Quantifying over `FDUnitaryRep G` makes a unitary dual live in
  `Type (max 1 u)`.  Sums over it (M6, M9) are fine, but any construction that wants the dual as a
  subtype of `L²(G)`-data must go through `IsContinuousUnitary.coeff_mem_matrixCoefficients`.
* **`convolutionFun` on plain functions** keeps M3 free of `L²`, but every use on `f : Lp ℂ 2 μ`
  goes through the double coercion `↑↑f`; lemmas should be stated for `f : Lp ℂ 2 μ` where
  possible and for `C(G, ℂ)` through `ContinuousMap.coeFn_toLp`.
* **Conjugation** (`star_mem_matrixCoefficients`) uses coordinates in `EuclideanSpace ℂ ι`, because
  mathlib has no conjugate Hilbert space.  Irreducibility of the conjugate representation (M5–M6)
  will need a small transport lemma for `Subrepresentation` along `euclideanConj`.
* **Totalisation audit.**  Expected markers: Bochner integrals in M1 (adjoint), M3 (mass one), M5
  and M6; `toReal` in the operator norm bound of `ContinuousMap.toLp`; scalar inverses `c⁻¹` in M2
  and the normalisation in M3.  Each has a structural reason (integrand continuous on a compact
  space, eigenvalue nonzero, integral positive).
