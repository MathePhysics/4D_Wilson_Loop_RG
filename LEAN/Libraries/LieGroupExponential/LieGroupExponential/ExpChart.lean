import Mathlib
import LieGroupExponential.Smoothness
import LieGroupExponential.Naturality

/-!
# The exponential chart of a Lie group at the identity

Let `G` be a real Lie group of class `C^∞` modelled on a complete normed space `E` through a model
with corners `I` without boundary.  The module `Smoothness` shows that the exponential map
`expE I G : E → G` is smooth and that its differential at `0`, read in the chart at the identity,
is the identity of `E`.  This file applies the inverse function theorem: the exponential map is a
local homeomorphism at `0`, with a smooth inverse, the logarithm.

## Construction

Write `e = extChartAt I (1 : G)` and `chartExp I G ξ = e (expE I G ξ)`.

* The map `chartExp I G : E → E` has the identity as strict derivative at `0`.  The inverse
  function theorem gives an open partial homeomorphism `chartExpHomeomorph I G` of `E` whose
  forward map is `chartExp I G` and whose source contains `0`.
* `expRegularSet I G` is the set of those `ξ` in the source of `chartExpHomeomorph I G` for which
  `expE I G ξ` lies in the source of the chart `e` and at which `chartExp I G` has an invertible
  derivative.  The last condition is needed for the smoothness of the inverse at every point: a
  smooth homeomorphism may have a singular derivative, and then its inverse is not
  differentiable there.  The condition is open, because `chartExp I G` is of class `C^1` wherever
  `expE I G ξ` lies in the source of `e`, and because the invertible operators form an open set.
* `expSource I G` is the symmetric part of `expRegularSet I G`: the set of `ξ` such that both `ξ`
  and `-ξ` lie in it.  It is open, contains `0`, and is invariant under `ξ ↦ -ξ`.
* `log I G g` is the local inverse of `chartExp I G` applied to `e g`.  It is a total function;
  it is meaningful on `expTarget I G`, the set of those `g` in the source of `e` for which `e g`
  lies in the target of `chartExpHomeomorph I G` and `log I G g` lies in `expSource I G`.
* `expChart I G : OpenPartialHomeomorph E G` has forward map `expE I G`, inverse map `log I G`,
  source `expSource I G` and target `expTarget I G`; all four identities hold by definition.

## Main results

* `log_expE`, `expE_log`, `log_one`, `expE_mem_expChart_target`, `log_mem_expChart_source`,
  `continuousOn_log`, `injOn_expE`: the logarithm inverts the exponential map between the source
  and the target of `expChart I G`.
* `contMDiffOn_log`: the logarithm is smooth on the target of `expChart I G`, which is an open
  neighbourhood of the identity.
* `neg_mem_expChart_source_iff`, `inv_mem_expChart_target`, `log_inv`: the source is symmetric,
  the target is stable under inversion, and `log g⁻¹ = -log g` on the target.
* `expMul I G (X, Y) = log (exp X * exp Y)` is the group law in exponential coordinates.  It is
  smooth at every `(X, Y)` with `exp X * exp Y` in the target (`contDiffAt_expMul`), in
  particular at `0` (`contDiffAt_expMul_zero`).  Moreover `expMul I G (X, 0) = X`,
  `expMul I G (0, Y) = Y`, and `expMul I G (s • X, t • X) = (s + t) • X` as soon as
  `(s + t) • X` lies in the source.  The inversion in exponential coordinates is `X ↦ -X` on the
  source (`log_inv_expE`), hence smooth there (`contDiffAt_log_inv_expE`), in particular at `0`
  (`contDiffAt_log_inv_expE_zero`).
* `log_conj_expE`: `log (g * exp ξ * g⁻¹) = Ad I g ξ` whenever `Ad I g ξ` lies in the source.
  `log_conj`: `log (g * x * g⁻¹) = Ad I g (log x)` for `x` in the target, whenever
  `Ad I g (log x)` lies in the source; the conjugate `g * x * g⁻¹` then lies in the target
  (`conj_mem_expChart_target`).  `log_expE_pow` and `log_expE_zpow`:
  `log ((exp ξ) ^ n) = n • ξ` whenever `n • ξ` lies in the source.
* `exists_ball_subset_expChart_source`: the source contains a ball centred at `0`.
* `hasMFDerivAt_log_one`: the differential of the logarithm at the identity is the identity of
  `E`.  `hasFDerivAt_expMul_zero`: the differential of `expMul I G` at the origin is the addition
  `(X, Y) ↦ X + Y`; it is a strict derivative (`hasStrictFDerivAt_expMul_zero`).

The statements carry only the membership hypotheses which their proofs use.  For instance
`expMul_smul_smul` asks only that `(s + t) • X` lie in the source, because
`exp (s • X) * exp (t • X) = exp ((s + t) • X)` holds without restriction, and `log_conj_expE`
does not ask that `ξ` lie in the source.

The logarithm is a total function.  Its values outside the target of `expChart I G` carry no
meaning, and every statement about it is restricted to the target.

All regularity statements are in class `C^∞`.  A statement of finite order `n` follows by
`ContDiffAt.of_le` or `ContMDiffAt.of_le`, with `ENat.LEInfty.out : n ≤ ∞`.

## Hypotheses and conventions

The hypotheses are those of `Smoothness`: `E` complete, `I` without boundary, and
`[HasContDiffBump E]`.  The identities `expE_neg`, `expE_add_smul`, `expE_zsmul` and `conj_expE`
and the definition of `chartExp` do not use the last one.  As in `Smoothness`, `I` and `G` are
explicit arguments, except that `G` is implicit in `conj_expE`, `log_conj_expE`,
`conj_mem_expChart_target` and `log_conj`, where it is determined by the group element `g`, as in
`Ad I g`.

The Lie algebra `GroupLieAlgebra I G` is definitionally `E` but carries no norm, and `log I G`
takes values in `E`.  To apply `Ad I g` to a logarithm, write
`((log I G x : E) : GroupLieAlgebra I G)`: the inner ascription fixes the model space of `log`
before its value is regarded as an element of the Lie algebra.
-/

noncomputable section

open scoped Manifold ContDiff Topology
open Set Filter

namespace LieGroupExponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  [CompleteSpace E] [I.Boundaryless]

variable (I G)

/-! ### Identities for the exponential map on the model space -/

/-- The exponential map sends negatives to inverses. -/
theorem expE_neg (ξ : E) : expE I G (-ξ) = (expE I G ξ)⁻¹ :=
  exp_neg (I := I) (G := G) (ξ : GroupLieAlgebra I G)

/-- The one-parameter subgroup law for the exponential map on the model space. -/
theorem expE_add_smul (s t : ℝ) (ξ : E) :
    expE I G ((s + t) • ξ) = expE I G (s • ξ) * expE I G (t • ξ) :=
  exp_add_smul (I := I) (G := G) s t (ξ : GroupLieAlgebra I G)

/-- The exponential of an integer multiple is an integer power of the exponential. -/
theorem expE_zsmul (n : ℤ) (ξ : E) : expE I G (n • ξ) = expE I G ξ ^ n :=
  exp_zsmul (I := I) (G := G) n (ξ : GroupLieAlgebra I G)

variable {G} in
/-- Conjugation by `g` of the exponential of `ξ` is the exponential of `Ad I g ξ`. -/
theorem conj_expE (g : G) (ξ : E) :
    g * expE I G ξ * g⁻¹ = expE I G (Ad I g (ξ : GroupLieAlgebra I G) : E) :=
  conj_exp (I := I) g (ξ : GroupLieAlgebra I G)

/-! ### The exponential map read in the chart at the identity -/

/-- The exponential map read in the chart at the identity, as a map from `E` to `E`. -/
def chartExp (ξ : E) : E :=
  extChartAt I (1 : G) (expE I G ξ)

/-- `chartExp I G ξ` is the chart coordinate of `exp ξ`. -/
theorem chartExp_apply (ξ : E) : chartExp I G ξ = extChartAt I (1 : G) (expE I G ξ) :=
  rfl

variable [HasContDiffBump E]

/-- The exponential map read in the chart at the identity is smooth at every `ξ` whose
exponential lies in the chart domain. -/
theorem contDiffAt_chartExp {ξ : E} (hξ : expE I G ξ ∈ (extChartAt I (1 : G)).source) :
    ContDiffAt ℝ ∞ (chartExp I G) ξ := by
  rw [extChartAt_source] at hξ
  have h1 : ContMDiffAt I 𝓘(ℝ, E) ∞ (extChartAt I (1 : G)) (expE I G ξ) :=
    contMDiffAt_extChartAt' hξ
  exact (h1.comp ξ (contMDiff_exp I G ξ)).contDiffAt

/-- The strict derivative of `chartExp I G` at `0` is the identity, regarded as a continuous
linear equivalence.  This is the hypothesis of the inverse function theorem. -/
theorem hasStrictFDerivAt_chartExp_zero :
    HasStrictFDerivAt (chartExp I G)
      ((ContinuousLinearEquiv.refl ℝ E : E ≃L[ℝ] E) : E →L[ℝ] E) 0 :=
  hasStrictFDerivAt_extChartAt_exp_zero I G

/-- The inverse function theorem applied to `chartExp I G` at `0`: an open partial homeomorphism
of `E` whose forward map is `chartExp I G` and whose source contains `0`. -/
def chartExpHomeomorph : OpenPartialHomeomorph E E :=
  (hasStrictFDerivAt_chartExp_zero I G).toOpenPartialHomeomorph (chartExp I G)

/-- The forward map of `chartExpHomeomorph I G` is `chartExp I G`. -/
@[simp]
theorem chartExpHomeomorph_coe : ⇑(chartExpHomeomorph I G) = chartExp I G :=
  rfl

/-- The origin lies in the source of `chartExpHomeomorph I G`. -/
theorem zero_mem_chartExpHomeomorph_source : (0 : E) ∈ (chartExpHomeomorph I G).source :=
  (hasStrictFDerivAt_chartExp_zero I G).mem_toOpenPartialHomeomorph_source

/-! ### The source of the exponential chart -/

/-- The set of those `ξ` in the source of `chartExpHomeomorph I G` whose exponential lies in the
domain of the chart at the identity and at which `chartExp I G` has an invertible derivative. -/
def expRegularSet : Set E :=
  {ξ | ξ ∈ (chartExpHomeomorph I G).source ∧ expE I G ξ ∈ (extChartAt I (1 : G)).source ∧
    ∃ A : E ≃L[ℝ] E, HasFDerivAt (chartExp I G) (A : E →L[ℝ] E) ξ}

/-- The origin lies in `expRegularSet I G`. -/
theorem zero_mem_expRegularSet : (0 : E) ∈ expRegularSet I G := by
  refine ⟨zero_mem_chartExpHomeomorph_source I G, ?_, ContinuousLinearEquiv.refl ℝ E,
    (hasStrictFDerivAt_chartExp_zero I G).hasFDerivAt⟩
  rw [expE_zero]
  exact mem_extChartAt_source (1 : G)

/-- `expRegularSet I G` is open: invertibility of the derivative is an open condition, because
`chartExp I G` is of class `C^1` and the invertible operators form an open set. -/
theorem isOpen_expRegularSet : IsOpen (expRegularSet I G) := by
  rw [isOpen_iff_mem_nhds]
  rintro ξ ⟨h1, h2, A, hA⟩
  have hsrc : (chartExpHomeomorph I G).source ∈ 𝓝 ξ :=
    (chartExpHomeomorph I G).open_source.mem_nhds h1
  have hch : expE I G ⁻¹' (extChartAt I (1 : G)).source ∈ 𝓝 ξ :=
    (continuous_expE I G).continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_source (1 : G)).mem_nhds h2)
  have hC1 : ContDiffAt ℝ 1 (chartExp I G) ξ :=
    (contDiffAt_chartExp I G h2).of_le (by exact_mod_cast le_top)
  obtain ⟨f', u, hu, hf'c, hf'⟩ := contDiffAt_one_iff.1 hC1
  have hfA : f' ξ = (A : E →L[ℝ] E) := (hf' ξ (mem_of_mem_nhds hu)).unique hA
  have hinv : f' ⁻¹' range ((↑) : (E ≃L[ℝ] E) → E →L[ℝ] E) ∈ 𝓝 ξ := by
    refine (hf'c.continuousAt hu).preimage_mem_nhds ?_
    rw [hfA]
    exact A.nhds
  filter_upwards [hsrc, hch, hu, hinv] with η h1' h2' h3' h4'
  obtain ⟨B, hB⟩ := h4'
  refine ⟨h1', h2', B, ?_⟩
  rw [hB]
  exact hf' η h3'

/-- The source of the exponential chart: the symmetric part of `expRegularSet I G`. -/
def expSource : Set E :=
  {ξ | ξ ∈ expRegularSet I G ∧ -ξ ∈ expRegularSet I G}

/-- Membership in `expSource I G`. -/
theorem mem_expSource_iff {ξ : E} :
    ξ ∈ expSource I G ↔ ξ ∈ expRegularSet I G ∧ -ξ ∈ expRegularSet I G :=
  Iff.rfl

/-- The origin lies in `expSource I G`. -/
theorem zero_mem_expSource : (0 : E) ∈ expSource I G := by
  rw [mem_expSource_iff, neg_zero]
  exact ⟨zero_mem_expRegularSet I G, zero_mem_expRegularSet I G⟩

/-- `expSource I G` is open. -/
theorem isOpen_expSource : IsOpen (expSource I G) :=
  (isOpen_expRegularSet I G).inter ((isOpen_expRegularSet I G).preimage continuous_neg)

/-- `expSource I G` is symmetric. -/
theorem neg_mem_expSource {ξ : E} (hξ : ξ ∈ expSource I G) : -ξ ∈ expSource I G := by
  rw [mem_expSource_iff, neg_neg]
  exact ⟨hξ.2, hξ.1⟩

/-! ### The logarithm and the exponential chart -/

/-- The logarithm of `G`: the local inverse of the exponential map at the identity.  It is a total
function, given by the local inverse of `chartExp I G` applied to the chart coordinate of `g`; it
inverts `expE I G` between the source and the target of `expChart I G` (`log_expE`,
`expE_log`). -/
def log (g : G) : E :=
  (chartExpHomeomorph I G).symm (extChartAt I (1 : G) g)

/-- The logarithm of `g` is the local inverse of `chartExp I G`, given by the inverse function
theorem, applied to the chart coordinate of `g`. -/
theorem log_apply (g : G) :
    log I G g = (chartExpHomeomorph I G).symm (extChartAt I (1 : G) g) :=
  rfl

/-- The target of the exponential chart: the points of the chart domain at the identity whose
chart coordinate lies in the target of `chartExpHomeomorph I G` and whose logarithm lies in
`expSource I G`. -/
def expTarget : Set G :=
  {g | g ∈ (extChartAt I (1 : G)).source ∧
    extChartAt I (1 : G) g ∈ (chartExpHomeomorph I G).target ∧ log I G g ∈ expSource I G}

/-- `expTarget I G` is open. -/
theorem isOpen_expTarget : IsOpen (expTarget I G) :=
  isOpen_extChartAt_preimage' (1 : G)
    ((chartExpHomeomorph I G).isOpen_inter_preimage_symm (isOpen_expSource I G))

/-- **The exponential chart.**  The exponential map as an open partial homeomorphism from `E` to
`G`, with forward map `expE I G`, inverse map `log I G`, source `expSource I G`, which is a
symmetric open neighbourhood of `0`, and target `expTarget I G`, an open neighbourhood of the
identity. -/
def expChart : OpenPartialHomeomorph E G where
  toFun := expE I G
  invFun := log I G
  source := expSource I G
  target := expTarget I G
  map_source' := fun ξ hξ => by
    refine ⟨hξ.1.2.1, (chartExpHomeomorph I G).map_source hξ.1.1, ?_⟩
    have h : log I G (expE I G ξ) = ξ := (chartExpHomeomorph I G).left_inv hξ.1.1
    rw [h]
    exact hξ
  map_target' := fun _ hg => hg.2.2
  left_inv' := fun _ hξ => (chartExpHomeomorph I G).left_inv hξ.1.1
  right_inv' := fun g hg => by
    have h : chartExp I G (log I G g) = extChartAt I (1 : G) g :=
      (chartExpHomeomorph I G).right_inv hg.2.1
    exact (extChartAt I (1 : G)).injOn hg.2.2.1.2.1 hg.1 h
  open_source := isOpen_expSource I G
  open_target := isOpen_expTarget I G
  continuousOn_toFun := (continuous_expE I G).continuousOn
  continuousOn_invFun := by
    have h1 : ContinuousOn (extChartAt I (1 : G)) (expTarget I G) :=
      (continuousOn_extChartAt (1 : G)).mono fun g hg => hg.1
    exact (chartExpHomeomorph I G).continuousOn_symm.comp h1 fun g hg => hg.2.1

/-- The forward map of the exponential chart is the exponential map. -/
@[simp]
theorem expChart_coe : ⇑(expChart I G) = expE I G :=
  rfl

/-- The forward map of the exponential chart is the exponential map. -/
theorem expChart_apply (ξ : E) : expChart I G ξ = expE I G ξ :=
  rfl

/-- The inverse map of the exponential chart is the logarithm. -/
@[simp]
theorem expChart_symm_coe : ⇑(expChart I G).symm = log I G :=
  rfl

/-- The inverse map of the exponential chart is the logarithm. -/
theorem expChart_symm_apply (g : G) : (expChart I G).symm g = log I G g :=
  rfl

/-- The source of the exponential chart is `expSource I G`. -/
theorem expChart_source : (expChart I G).source = expSource I G :=
  rfl

/-- The target of the exponential chart is `expTarget I G`. -/
theorem expChart_target : (expChart I G).target = expTarget I G :=
  rfl

/-- Membership in the source of the exponential chart. -/
theorem mem_expChart_source_iff {ξ : E} :
    ξ ∈ (expChart I G).source ↔ ξ ∈ expRegularSet I G ∧ -ξ ∈ expRegularSet I G :=
  Iff.rfl

/-- Membership in the target of the exponential chart. -/
theorem mem_expChart_target_iff {g : G} :
    g ∈ (expChart I G).target ↔ g ∈ (extChartAt I (1 : G)).source ∧
      extChartAt I (1 : G) g ∈ (chartExpHomeomorph I G).target ∧
        log I G g ∈ (expChart I G).source :=
  Iff.rfl

/-- The origin lies in the source of the exponential chart. -/
theorem zero_mem_expChart_source : (0 : E) ∈ (expChart I G).source :=
  zero_mem_expSource I G

/-- The source of the exponential chart is a neighbourhood of `0`. -/
theorem expChart_source_mem_nhds : (expChart I G).source ∈ 𝓝 (0 : E) :=
  (expChart I G).open_source.mem_nhds (zero_mem_expChart_source I G)

/-- The exponential chart maps `0` to the identity. -/
theorem expChart_zero : expChart I G 0 = 1 :=
  expE_zero I G

/-- The identity lies in the target of the exponential chart. -/
theorem one_mem_expChart_target : (1 : G) ∈ (expChart I G).target := by
  have h := (expChart I G).map_source (zero_mem_expChart_source I G)
  rwa [expChart_zero] at h

/-- The target of the exponential chart is a neighbourhood of the identity. -/
theorem expChart_target_mem_nhds : (expChart I G).target ∈ 𝓝 (1 : G) :=
  (expChart I G).open_target.mem_nhds (one_mem_expChart_target I G)

/-- The source of the exponential chart is symmetric. -/
theorem neg_mem_expChart_source {ξ : E} (hξ : ξ ∈ (expChart I G).source) :
    -ξ ∈ (expChart I G).source :=
  neg_mem_expSource I G hξ

/-- The source of the exponential chart is symmetric. -/
@[simp]
theorem neg_mem_expChart_source_iff {ξ : E} :
    -ξ ∈ (expChart I G).source ↔ ξ ∈ (expChart I G).source :=
  ⟨fun h => by simpa using neg_mem_expChart_source I G h, neg_mem_expChart_source I G⟩

/-- The source of the exponential chart contains a ball centred at `0`. -/
theorem exists_ball_subset_expChart_source :
    ∃ r : ℝ, 0 < r ∧ Metric.ball (0 : E) r ⊆ (expChart I G).source :=
  Metric.isOpen_iff.1 (expChart I G).open_source 0 (zero_mem_expChart_source I G)

/-- The source of the exponential chart lies in the source of `chartExpHomeomorph I G`. -/
theorem mem_chartExpHomeomorph_source {ξ : E} (hξ : ξ ∈ (expChart I G).source) :
    ξ ∈ (chartExpHomeomorph I G).source :=
  hξ.1.1

/-- On the source of the exponential chart, the exponential map takes values in the domain of the
chart at the identity. -/
theorem expE_mem_extChartAt_source {ξ : E} (hξ : ξ ∈ (expChart I G).source) :
    expE I G ξ ∈ (extChartAt I (1 : G)).source :=
  hξ.1.2.1

/-- At every point of the source of the exponential chart, the exponential map read in the chart
at the identity has an invertible derivative. -/
theorem exists_hasFDerivAt_chartExp {ξ : E} (hξ : ξ ∈ (expChart I G).source) :
    ∃ A : E ≃L[ℝ] E, HasFDerivAt (chartExp I G) (A : E →L[ℝ] E) ξ :=
  hξ.1.2.2

/-- The target of the exponential chart lies in the domain of the chart at the identity. -/
theorem expChart_target_subset : (expChart I G).target ⊆ (extChartAt I (1 : G)).source :=
  fun _ hg => hg.1

/-! ### The logarithm inverts the exponential map -/

/-- The exponential map sends the source of the exponential chart into its target. -/
theorem expE_mem_expChart_target {ξ : E} (hξ : ξ ∈ (expChart I G).source) :
    expE I G ξ ∈ (expChart I G).target :=
  (expChart I G).map_source hξ

/-- The logarithm sends the target of the exponential chart into its source. -/
theorem log_mem_expChart_source {g : G} (hg : g ∈ (expChart I G).target) :
    log I G g ∈ (expChart I G).source :=
  (expChart I G).map_target hg

/-- The target of the exponential chart is the image of its source under the exponential map. -/
theorem expChart_target_eq_image :
    (expChart I G).target = expE I G '' (expChart I G).source :=
  (expChart I G).image_source_eq_target.symm

/-- On the source of the exponential chart, the logarithm is a left inverse of the exponential
map. -/
theorem log_expE {ξ : E} (hξ : ξ ∈ (expChart I G).source) : log I G (expE I G ξ) = ξ :=
  (expChart I G).left_inv hξ

/-- On the target of the exponential chart, the logarithm is a right inverse of the exponential
map. -/
theorem expE_log {g : G} (hg : g ∈ (expChart I G).target) : expE I G (log I G g) = g :=
  (expChart I G).right_inv hg

/-- The logarithm of the identity is `0`. -/
@[simp]
theorem log_one : log I G (1 : G) = 0 := by
  have h := log_expE I G (zero_mem_expChart_source I G)
  rwa [expE_zero] at h

/-- The exponential map is injective on the source of the exponential chart. -/
theorem injOn_expE : InjOn (expE I G) (expChart I G).source :=
  (expChart I G).injOn

/-- The logarithm is injective on the target of the exponential chart. -/
theorem injOn_log : InjOn (log I G) (expChart I G).target :=
  (expChart I G).symm.injOn

/-- On the target of the exponential chart, `log g = ξ` if and only if `g = exp ξ`, for `ξ` in the
source. -/
theorem log_eq_iff {g : G} {ξ : E} (hg : g ∈ (expChart I G).target)
    (hξ : ξ ∈ (expChart I G).source) : log I G g = ξ ↔ g = expE I G ξ := by
  constructor
  · rintro rfl
    exact (expE_log I G hg).symm
  · rintro rfl
    exact log_expE I G hξ

/-- The exponential map is continuous on the source of the exponential chart. -/
theorem continuousOn_expE : ContinuousOn (expE I G) (expChart I G).source :=
  (continuous_expE I G).continuousOn

/-- The logarithm is continuous on the target of the exponential chart. -/
theorem continuousOn_log : ContinuousOn (log I G) (expChart I G).target :=
  (expChart I G).continuousOn_symm

/-- The logarithm is continuous at every point of the target of the exponential chart. -/
theorem continuousAt_log {g : G} (hg : g ∈ (expChart I G).target) : ContinuousAt (log I G) g :=
  (expChart I G).continuousAt_symm hg

/-! ### Smoothness of the logarithm -/

/-- The logarithm is smooth at every point of the target of the exponential chart.  This is the
inverse function theorem in class `C^∞`: the derivative of `chartExp I G` is invertible at every
point of the source. -/
theorem contMDiffAt_log {g : G} (hg : g ∈ (expChart I G).target) :
    ContMDiffAt I 𝓘(ℝ, E) ∞ (log I G) g := by
  obtain ⟨h1, h2, h3⟩ := hg
  obtain ⟨A, hA⟩ := h3.1.2.2
  have hsymm : ContDiffAt ℝ ∞ (chartExpHomeomorph I G).symm (extChartAt I (1 : G) g) :=
    (chartExpHomeomorph I G).contDiffAt_symm h2 hA (contDiffAt_chartExp I G h3.1.2.1)
  have he : ContMDiffAt I 𝓘(ℝ, E) ∞ (extChartAt I (1 : G)) g :=
    contMDiffAt_extChartAt' (by rwa [extChartAt_source] at h1)
  exact hsymm.contMDiffAt.comp g he

/-- **The logarithm is smooth** on the target of the exponential chart. -/
theorem contMDiffOn_log : ContMDiffOn I 𝓘(ℝ, E) ∞ (log I G) (expChart I G).target :=
  fun _ hg => (contMDiffAt_log I G hg).contMDiffWithinAt

/-- The logarithm is smooth at the identity. -/
theorem contMDiffAt_log_one : ContMDiffAt I 𝓘(ℝ, E) ∞ (log I G) (1 : G) :=
  contMDiffAt_log I G (one_mem_expChart_target I G)

/-- The logarithm is smooth at every point of a neighbourhood of the identity. -/
theorem eventually_contMDiffAt_log : ∀ᶠ g in 𝓝 (1 : G), ContMDiffAt I 𝓘(ℝ, E) ∞ (log I G) g := by
  filter_upwards [expChart_target_mem_nhds I G] with g hg
  exact contMDiffAt_log I G hg

/-- The exponential map is smooth on the source of the exponential chart. -/
theorem contMDiffOn_expE : ContMDiffOn 𝓘(ℝ, E) I ∞ (expE I G) (expChart I G).source :=
  (contMDiff_exp I G).contMDiffOn

/-! ### Inversion -/

/-- The target of the exponential chart is stable under inversion. -/
theorem inv_mem_expChart_target {g : G} (hg : g ∈ (expChart I G).target) :
    g⁻¹ ∈ (expChart I G).target := by
  have h : expE I G (-log I G g) ∈ (expChart I G).target :=
    expE_mem_expChart_target I G (neg_mem_expChart_source I G (log_mem_expChart_source I G hg))
  rwa [expE_neg, expE_log I G hg] at h

/-- The target of the exponential chart is stable under inversion. -/
@[simp]
theorem inv_mem_expChart_target_iff {g : G} :
    g⁻¹ ∈ (expChart I G).target ↔ g ∈ (expChart I G).target :=
  ⟨fun h => by simpa using inv_mem_expChart_target I G h, inv_mem_expChart_target I G⟩

/-- In exponential coordinates, inversion is `ξ ↦ -ξ`. -/
theorem log_inv_expE {ξ : E} (hξ : ξ ∈ (expChart I G).source) :
    log I G (expE I G ξ)⁻¹ = -ξ := by
  rw [← expE_neg, log_expE I G (neg_mem_expChart_source I G hξ)]

/-- **The logarithm of an inverse** is the negative of the logarithm, on the target of the
exponential chart. -/
theorem log_inv {g : G} (hg : g ∈ (expChart I G).target) : log I G g⁻¹ = -log I G g := by
  have h := log_inv_expE I G (log_mem_expChart_source I G hg)
  rwa [expE_log I G hg] at h

/-- Inversion read in exponential coordinates is smooth at every point of the source of the
exponential chart, where it is `X ↦ -X`. -/
theorem contDiffAt_log_inv_expE {ξ : E} (hξ : ξ ∈ (expChart I G).source) :
    ContDiffAt ℝ ∞ (fun X : E => log I G (expE I G X)⁻¹) ξ := by
  refine contDiff_neg.contDiffAt.congr_of_eventuallyEq ?_
  filter_upwards [(expChart I G).open_source.mem_nhds hξ] with X hX
  exact log_inv_expE I G hX

/-- **Inversion read in exponential coordinates is smooth at the origin.** -/
theorem contDiffAt_log_inv_expE_zero :
    ContDiffAt ℝ ∞ (fun X : E => log I G (expE I G X)⁻¹) 0 :=
  contDiffAt_log_inv_expE I G (zero_mem_expChart_source I G)

/-! ### The group law in exponential coordinates -/

/-- The group law in exponential coordinates: `expMul I G (X, Y) = log (exp X * exp Y)`. -/
def expMul (p : E × E) : E :=
  log I G (expE I G p.1 * expE I G p.2)

/-- `expMul I G p = log (exp p.1 * exp p.2)`. -/
theorem expMul_apply (p : E × E) : expMul I G p = log I G (expE I G p.1 * expE I G p.2) :=
  rfl

/-- `expMul I G (X, Y) = log (exp X * exp Y)`. -/
theorem expMul_mk (X Y : E) : expMul I G (X, Y) = log I G (expE I G X * expE I G Y) :=
  rfl

/-- The map `(X, Y) ↦ exp X * exp Y` is smooth on `E × E`. -/
theorem contMDiff_expE_mul_expE :
    ContMDiff 𝓘(ℝ, E × E) I ∞ (fun p : E × E => expE I G p.1 * expE I G p.2) := by
  have h1 : ContMDiff 𝓘(ℝ, E × E) I ∞ (fun p : E × E => expE I G p.1) :=
    (contMDiff_exp I G).comp contDiff_fst.contMDiff
  have h2 : ContMDiff 𝓘(ℝ, E × E) I ∞ (fun p : E × E => expE I G p.2) :=
    (contMDiff_exp I G).comp contDiff_snd.contMDiff
  exact h1.mul h2

/-- The group law in exponential coordinates is smooth at every `(X, Y)` for which `exp X * exp Y`
lies in the target of the exponential chart. -/
theorem contDiffAt_expMul {p : E × E}
    (hp : expE I G p.1 * expE I G p.2 ∈ (expChart I G).target) :
    ContDiffAt ℝ ∞ (expMul I G) p :=
  ((contMDiffAt_log I G hp).comp p (contMDiff_expE_mul_expE I G p)).contDiffAt

/-- For `(X, Y)` near the origin, `exp X * exp Y` lies in the target of the exponential chart. -/
theorem eventually_expE_mul_expE_mem_expChart_target :
    ∀ᶠ p in 𝓝 (0 : E × E), expE I G p.1 * expE I G p.2 ∈ (expChart I G).target := by
  have hc : ContinuousAt (fun p : E × E => expE I G p.1 * expE I G p.2) 0 :=
    (contMDiff_expE_mul_expE I G).continuous.continuousAt
  refine hc.eventually_mem ((expChart I G).open_target.mem_nhds ?_)
  rw [Prod.fst_zero, Prod.snd_zero, expE_zero, mul_one]
  exact one_mem_expChart_target I G

/-- **The group law in exponential coordinates is smooth at the origin.** -/
theorem contDiffAt_expMul_zero : ContDiffAt ℝ ∞ (expMul I G) 0 :=
  contDiffAt_expMul I G (eventually_expE_mul_expE_mem_expChart_target I G).self_of_nhds

/-- The group law in exponential coordinates is smooth at every point of a neighbourhood of the
origin. -/
theorem eventually_contDiffAt_expMul :
    ∀ᶠ p in 𝓝 (0 : E × E), ContDiffAt ℝ ∞ (expMul I G) p := by
  filter_upwards [eventually_expE_mul_expE_mem_expChart_target I G] with p hp
  exact contDiffAt_expMul I G hp

/-- If `exp X * exp Y` lies in the target of the exponential chart, then `expMul I G (X, Y)` lies
in its source. -/
theorem expMul_mem_expChart_source {p : E × E}
    (hp : expE I G p.1 * expE I G p.2 ∈ (expChart I G).target) :
    expMul I G p ∈ (expChart I G).source :=
  log_mem_expChart_source I G hp

/-- If `exp X * exp Y` lies in the target of the exponential chart, then it is the exponential of
`expMul I G (X, Y)`. -/
theorem expE_expMul {p : E × E} (hp : expE I G p.1 * expE I G p.2 ∈ (expChart I G).target) :
    expE I G (expMul I G p) = expE I G p.1 * expE I G p.2 :=
  expE_log I G hp

/-- The origin is a right unit of the group law in exponential coordinates. -/
theorem expMul_zero_right {X : E} (hX : X ∈ (expChart I G).source) : expMul I G (X, 0) = X := by
  rw [expMul_mk, expE_zero, mul_one, log_expE I G hX]

/-- The origin is a left unit of the group law in exponential coordinates. -/
theorem expMul_zero_left {Y : E} (hY : Y ∈ (expChart I G).source) : expMul I G (0, Y) = Y := by
  rw [expMul_mk, expE_zero, one_mul, log_expE I G hY]

/-- The group law in exponential coordinates maps the origin to the origin. -/
@[simp]
theorem expMul_zero : expMul I G 0 = 0 :=
  expMul_zero_right I G (zero_mem_expChart_source I G)

/-- Along a line through the origin, the group law in exponential coordinates is the addition.
Only `(s + t) • X` has to lie in the source of the exponential chart. -/
theorem expMul_smul_smul {s t : ℝ} {X : E} (h : (s + t) • X ∈ (expChart I G).source) :
    expMul I G (s • X, t • X) = (s + t) • X := by
  rw [expMul_mk, ← expE_add_smul, log_expE I G h]

/-- In exponential coordinates, `-X` is a right inverse of `X`. -/
theorem expMul_neg_right (X : E) : expMul I G (X, -X) = 0 := by
  rw [expMul_mk, expE_neg, mul_inv_cancel, log_one]

/-- In exponential coordinates, `-X` is a left inverse of `X`. -/
theorem expMul_neg_left (X : E) : expMul I G (-X, X) = 0 := by
  rw [expMul_mk, expE_neg, inv_mul_cancel, log_one]

/-! ### Equivariance of the logarithm -/

variable {G} in
/-- **The logarithm intertwines conjugation with the adjoint action**:
`log (g * exp ξ * g⁻¹) = Ad I g ξ`, provided `Ad I g ξ` lies in the source of the exponential
chart. -/
theorem log_conj_expE (g : G) {ξ : E}
    (h : (Ad I g (ξ : GroupLieAlgebra I G) : E) ∈ (expChart I G).source) :
    log I G (g * expE I G ξ * g⁻¹) = (Ad I g (ξ : GroupLieAlgebra I G) : E) := by
  rw [conj_expE, log_expE I G h]

variable {G} in
/-- If `x` lies in the target of the exponential chart and `Ad I g (log x)` lies in its source,
then the conjugate `g * x * g⁻¹` lies in the target. -/
theorem conj_mem_expChart_target (g : G) {x : G} (hx : x ∈ (expChart I G).target)
    (h : (Ad I g ((log I G x : E) : GroupLieAlgebra I G) : E) ∈ (expChart I G).source) :
    g * x * g⁻¹ ∈ (expChart I G).target := by
  have h' := expE_mem_expChart_target I G h
  rwa [← conj_expE I g, expE_log I G hx] at h'

variable {G} in
/-- The logarithm of a conjugate, for an element `x` of the target of the exponential chart:
`log (g * x * g⁻¹) = Ad I g (log x)`, provided `Ad I g (log x)` lies in the source. -/
theorem log_conj (g : G) {x : G} (hx : x ∈ (expChart I G).target)
    (h : (Ad I g ((log I G x : E) : GroupLieAlgebra I G) : E) ∈ (expChart I G).source) :
    log I G (g * x * g⁻¹) = (Ad I g ((log I G x : E) : GroupLieAlgebra I G) : E) := by
  have h' := log_conj_expE I g h
  rwa [expE_log I G hx] at h'

/-- The logarithm of a power: `log ((exp ξ) ^ n) = n • ξ`, provided `n • ξ` lies in the source of
the exponential chart. -/
theorem log_expE_pow {n : ℕ} {ξ : E} (h : n • ξ ∈ (expChart I G).source) :
    log I G (expE I G ξ ^ n) = n • ξ := by
  rw [← expE_nsmul, log_expE I G h]

/-- The logarithm of an integer power: `log ((exp ξ) ^ n) = n • ξ`, provided `n • ξ` lies in the
source of the exponential chart. -/
theorem log_expE_zpow {n : ℤ} {ξ : E} (h : n • ξ ∈ (expChart I G).source) :
    log I G (expE I G ξ ^ n) = n • ξ := by
  rw [← expE_zsmul, log_expE I G h]

/-! ### Differentials at the origin and at the identity -/

/-- The manifold derivative of the logarithm at the identity is the identity of `E`.  Both the
tangent space of `G` at `1` and the tangent space of `E` at `log 1 = 0` are definitionally `E`. -/
theorem hasMFDerivAt_log_one :
    HasMFDerivAt I 𝓘(ℝ, E) (log I G) (1 : G) (ContinuousLinearMap.id ℝ E) := by
  have hd : MDifferentiableAt I 𝓘(ℝ, E) (log I G) (1 : G) :=
    (contMDiffAt_log_one I G).mdifferentiableAt (by simp)
  obtain ⟨L, hL⟩ : ∃ L : E →L[ℝ] E, HasMFDerivAt I 𝓘(ℝ, E) (log I G) (1 : G) L :=
    ⟨_, hd.hasMFDerivAt⟩
  -- the base point is written as `exp 0`, so that the chain rule applies
  have hL0 : HasMFDerivAt I 𝓘(ℝ, E) (log I G) (expE I G 0) L := by
    rw [expE_zero]
    exact hL
  have hc : HasFDerivAt (log I G ∘ expE I G) (L.comp (ContinuousLinearMap.id ℝ E)) 0 :=
    (HasMFDerivAt.comp (0 : E) hL0 (hasMFDerivAt_expE_zero I G)).hasFDerivAt
  have hid : HasFDerivAt (log I G ∘ expE I G) (ContinuousLinearMap.id ℝ E) 0 := by
    refine (hasFDerivAt_id (0 : E)).congr_of_eventuallyEq ?_
    filter_upwards [expChart_source_mem_nhds I G] with ξ hξ
    exact log_expE I G hξ
  have hLid : L = ContinuousLinearMap.id ℝ E := by
    have h := hc.unique hid
    rwa [ContinuousLinearMap.comp_id] at h
  rw [← hLid]
  exact hL

/-- **The differential of the group law in exponential coordinates at the origin is the
addition** `(X, Y) ↦ X + Y`. -/
theorem hasFDerivAt_expMul_zero :
    HasFDerivAt (expMul I G)
      (ContinuousLinearMap.fst ℝ E E + ContinuousLinearMap.snd ℝ E E) 0 := by
  obtain ⟨D, hD⟩ := (contDiffAt_expMul_zero I G).differentiableAt (by simp)
  have hD0 : HasFDerivAt (expMul I G) D ((0 : E), (0 : E)) := hD
  -- the partial maps `X ↦ expMul (X, 0)` and `Y ↦ expMul (0, Y)` are the identity near `0`
  have hl : D.comp (ContinuousLinearMap.inl ℝ E E) = ContinuousLinearMap.id ℝ E := by
    have h1 : HasFDerivAt (fun X : E => expMul I G (X, 0))
        (D.comp (ContinuousLinearMap.inl ℝ E E)) 0 :=
      HasFDerivAt.comp (f := fun X : E => (X, (0 : E))) (0 : E) hD0
        (hasFDerivAt_prodMk_left (0 : E) (0 : E))
    have h2 : HasFDerivAt (fun X : E => expMul I G (X, 0)) (ContinuousLinearMap.id ℝ E) 0 := by
      refine (hasFDerivAt_id (0 : E)).congr_of_eventuallyEq ?_
      filter_upwards [expChart_source_mem_nhds I G] with X hX
      exact expMul_zero_right I G hX
    exact h1.unique h2
  have hr : D.comp (ContinuousLinearMap.inr ℝ E E) = ContinuousLinearMap.id ℝ E := by
    have h1 : HasFDerivAt (fun Y : E => expMul I G (0, Y))
        (D.comp (ContinuousLinearMap.inr ℝ E E)) 0 :=
      HasFDerivAt.comp (f := fun Y : E => ((0 : E), Y)) (0 : E) hD0
        (hasFDerivAt_prodMk_right (0 : E) (0 : E))
    have h2 : HasFDerivAt (fun Y : E => expMul I G (0, Y)) (ContinuousLinearMap.id ℝ E) 0 := by
      refine (hasFDerivAt_id (0 : E)).congr_of_eventuallyEq ?_
      filter_upwards [expChart_source_mem_nhds I G] with Y hY
      exact expMul_zero_left I G hY
    exact h1.unique h2
  refine hD.congr_fderiv (ContinuousLinearMap.ext fun p => ?_)
  have e1 : D (p.1, 0) = p.1 := DFunLike.congr_fun hl p.1
  have e2 : D (0, p.2) = p.2 := DFunLike.congr_fun hr p.2
  have e3 : D p = D (p.1, 0) + D (0, p.2) := by
    rw [← map_add, Prod.mk_add_mk, add_zero, zero_add]
  rw [e3, e1, e2]
  rfl

/-- The differential of the group law in exponential coordinates at the origin is a strict
derivative. -/
theorem hasStrictFDerivAt_expMul_zero :
    HasStrictFDerivAt (expMul I G)
      (ContinuousLinearMap.fst ℝ E E + ContinuousLinearMap.snd ℝ E E) 0 :=
  (contDiffAt_expMul_zero I G).hasStrictFDerivAt' (hasFDerivAt_expMul_zero I G) (by simp)

end LieGroupExponential
