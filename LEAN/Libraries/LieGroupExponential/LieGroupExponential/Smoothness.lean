import Mathlib
import LieGroupExponential.ParamODE
import LieGroupExponential.OneParameter
import LieGroupExponential.ChartField

/-!
# Smoothness of the exponential map

Let `G` be a real Lie group of class `C^∞` modelled on a complete normed space `E` through a model
with corners `I` without boundary.  The module `OneParameter` constructs the exponential map
`exp : GroupLieAlgebra I G → G` from the global integral curves of the left-invariant vector
fields, with no information on how `exp v` depends on `v`.  This file proves that `exp` is smooth
and that its differential at the origin is the identity.

## The exponential map on the model space

`GroupLieAlgebra I G` is the tangent space at the identity.  It is definitionally `E`, but it is
not reducible to `E` and carries no norm.  Regularity is therefore stated for
`expE I G : E → G`, `expE I G ξ = exp (ξ : GroupLieAlgebra I G)`.  The definition unfolds to
`fun ξ : E => exp (ξ : GroupLieAlgebra I G)`, so every statement below also applies to that
function.  The identities of `OneParameter` are transferred to `expE` once, by definitional
unfolding (`expE_zero`, `expE_nsmul`, `expE_eq_pow`, `isMIntegralCurve_expE_smul`); afterwards all
rewriting takes place in `E`.

## Main results

Write `e = extChartAt I (1 : G)` for the extended chart at the identity and
`c = chartCentre I G = e 1`.

* `exists_chartSolution` (local identification): for every natural number `n ≠ 0` there is a map
  `Γ : E → C([-2, 2], E)` which is `C^n` at `0`, with `Γ 0 = 0`, such that for `ξ` near `0`
  the point `Γ ξ 1 + c` lies in the target of `e` and `exp ξ = chartPoint I G (Γ ξ 1)`.
  The version `exists_chartSolution_smul` gives `exp (t • ξ) = chartPoint I G (Γ ξ t)` for all
  `t` in `(-2, 2)`.
* `contDiffAt_extChartAt_exp`: the map `ξ ↦ e (exp ξ)` is `C^∞` at `0`.  Moreover `exp ξ` lies in
  the source of `e` for `ξ` near `0` (`eventually_expE_mem_source`), and `exp` is continuous and
  smooth at `0` (`continuousAt_expE_zero`, `contMDiffAt_expE_zero`).
* `hasFDerivAt_extChartAt_exp_zero`: the differential of `ξ ↦ e (exp ξ)` at `0` is the identity of
  `E`.  It is a strict derivative (`hasStrictFDerivAt_extChartAt_exp_zero`), which is the form
  required by the inverse function theorem, and the manifold derivative of `exp` at `0` is the
  identity (`hasMFDerivAt_expE_zero`).
* `contMDiff_exp`: the exponential map is smooth on all of `E`.  Consequently it is continuous
  (`continuous_expE`), the map `(t, ξ) ↦ exp (t • ξ)` is smooth on `ℝ × E` (`contMDiff_expE_smul`,
  `contMDiff_expE_smul_prod`), and every one-parameter subgroup `t ↦ exp (t • v)` is a smooth
  curve (`contMDiff_exp_smul_const`).

## Method

The left-invariant vector field of `ξ`, read in the chart at the identity recentred at `0`, is
`x ↦ chartField I G x ξ`.  The module `ChartField` cuts it off to a globally defined `C^n` map
`F : E × E → E` with `F (x, 0) = 0` for all `x` and `F (x, ξ) = chartField I G x ξ` for `‖x‖ < r`.
The module `ParamODE` then gives a family `Γ ξ` of solutions of `γ' = F (γ, ξ)`, `γ 0 = 0` on the
fixed interval `[-2, 2]`, which is `C^n` at `ξ = 0` as a map into the Banach space of continuous
curves, and `Γ 0 = 0`.  By continuity, `‖Γ ξ‖ < r` for `ξ` near `0`.  For such `ξ` the curve `Γ ξ`
solves the equation of the chart field itself, so `t ↦ chartPoint I G (Γ ξ t)` is an integral
curve on `(-2, 2)` of the left-invariant vector field of `ξ` starting at the identity.  By
uniqueness of integral curves it is `t ↦ exp (t • ξ)`
(`expE_smul_eq_chartPoint_of_solution`).  Evaluation at `t = 1` is a continuous linear map on the
space of curves, hence `ξ ↦ e (exp ξ) = Γ ξ 1 + c` is `C^n` at `0`.  Since `n` is arbitrary, it is
`C^∞` at `0`; the map `Γ` and the neighbourhood depend on `n`.

The differential at `0` is computed along rays.  The curve `t ↦ e (exp (t • ξ))` has derivative
`ξ` at `t = 0`, because `t ↦ exp (t • ξ)` is an integral curve through the identity, where the
left-invariant vector field of `ξ` takes the value `ξ`
(`hasDerivAt_extChartAt_expE_smul_zero`).  By the chain rule the Fréchet derivative at `0` maps
`ξ` to `ξ`.

Global smoothness follows from the identity `exp ξ = (exp (s • ξ)) ^ N`, valid for all `ξ` when
`N * s = 1`.  For a natural number `n`, `exp` is `C^n` on a neighbourhood `U` of `0`.  Given `ξ₀`,
choose `N ≥ 1` and `s` with `N * s = 1` and `s • ξ₀ ∈ U` (`exists_nat_mul_eq_one_smul_mem`).
Then `exp` is, globally, the composition of the scaling by `s`, of `exp`, and of the `N`-th power
map of `G`, so it is `C^n` at `ξ₀`.  This holds for all `n`, hence `exp` is `C^∞` at `ξ₀`.

## Hypotheses

The exponential map needs `E` complete and `I` without boundary.  The regularity results need in
addition `[HasContDiffBump E]`, used only for the cut-off of the chart field
(`exists_cutoffField_of_hasContDiffBump`).  It holds for Hilbert spaces and for finite-dimensional
spaces.  In finite dimension completeness of `E` is automatic, but it must be available as an
instance, for example through `have := FiniteDimensional.complete ℝ E`.

From the definition of `expE` onwards, `I` and `G` are explicit arguments, as in `ChartField`,
except in `expE_smul_eq_chartPoint_of_solution` and `contMDiff_exp_smul_const`, where they are
determined by the other arguments.
-/

noncomputable section

open scoped Manifold ContDiff Topology
open Set Filter

namespace LieGroupExponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

/-! ### Auxiliary results -/

/-- Let `M` be a smooth manifold.  A map `f` from a normed space into `M` which, near `x₀`, takes
its values in the source of the chart at `y`, and which is of class `C^n` at `x₀` when read in
that chart, is of class `C^n` at `x₀` as a map into the manifold `M`.  No group structure is
involved. -/
theorem contMDiffAt_of_contDiffAt_extChartAt {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M] {n : ℕ∞ω} (hn : n ≤ ∞) {f : E → M} {x₀ : E}
    {y : M} (hs : ∀ᶠ x in 𝓝 x₀, f x ∈ (extChartAt I y).source)
    (hf : ContDiffAt ℝ n (fun x => extChartAt I y (f x)) x₀) :
    ContMDiffAt 𝓘(ℝ, E) I n f x₀ := by
  have : IsManifold I n M := IsManifold.of_le hn
  have hs₀ : f x₀ ∈ (extChartAt I y).source := hs.self_of_nhds
  -- continuity: near `x₀` the map is the inverse chart applied to its chart reading
  have hc : ContinuousAt f x₀ := by
    have h1 : ContinuousAt (fun x => (extChartAt I y).symm (extChartAt I y (f x))) x₀ :=
      ContinuousAt.comp (g := (extChartAt I y).symm)
        (continuousAt_extChartAt_symm'' ((extChartAt I y).map_source hs₀)) hf.continuousAt
    refine h1.congr ?_
    filter_upwards [hs] with x hx
    exact (extChartAt I y).left_inv hx
  rw [contMDiffAt_iff_target_of_mem_source (y := y) (by rwa [extChartAt_source] at hs₀)]
  exact ⟨hc, hf.contMDiffAt⟩

/-- Every vector is a natural multiple of a vector in a given neighbourhood of `0`: there are a
natural number `N` and a real number `s` with `N * s = 1` and `s • ξ` in the neighbourhood. -/
theorem exists_nat_mul_eq_one_smul_mem {U : Set E} (hU : U ∈ 𝓝 (0 : E)) (ξ : E) :
    ∃ (N : ℕ) (s : ℝ), (N : ℝ) * s = 1 ∧ s • ξ ∈ U := by
  have h1 := (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).smul_const ξ
  rw [zero_smul] at h1
  obtain ⟨N, hNU, hN1⟩ := ((h1.eventually_mem hU).and (eventually_ge_atTop 1)).exists
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.one_le_iff_ne_zero.1 hN1)
  exact ⟨N, (N : ℝ)⁻¹, mul_inv_cancel₀ hN0, hNU⟩ -- totalisation-audit: allow N ≥ 1, so N is non-zero in ℝ and the inverse is the genuine one

/-- The time `1` in the interval `[-2, 2]`. -/
def timeOne : ParamODE.Time 2 := ⟨1, by norm_num⟩

/-- The time `1` in the interval `[-2, 2]` is the real number `1`. -/
@[simp]
theorem coe_timeOne : ((timeOne : ParamODE.Time 2) : ℝ) = 1 :=
  rfl

variable {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]

section Exp

variable [CompleteSpace E] [I.Boundaryless]

/-- If `N * s = 1`, then `exp v` is the `N`-th power of `exp (s • v)`. -/
theorem exp_eq_pow_of_mul_eq_one {N : ℕ} {s : ℝ} (h : (N : ℝ) * s = 1)
    (v : GroupLieAlgebra I G) : exp v = exp (s • v) ^ N := by
  rw [← exp_nsmul, ← Nat.cast_smul_eq_nsmul ℝ N (s • v), smul_smul, h, one_smul]

/-! ### The exponential map on the model space -/

variable (I G)

/-- The exponential map of `G` as a map defined on the model space `E`, which is definitionally the
Lie algebra `GroupLieAlgebra I G`.  The model space carries the norm needed to state regularity;
the Lie algebra, a tangent space, does not. -/
def expE (ξ : E) : G :=
  exp (I := I) (G := G) (ξ : GroupLieAlgebra I G)

/-- `expE` is `exp`, with the Lie algebra identified with the model space. -/
theorem expE_apply (ξ : E) : expE I G ξ = exp (I := I) (G := G) (ξ : GroupLieAlgebra I G) :=
  rfl

/-- The exponential of `0` is the identity. -/
@[simp]
theorem expE_zero : expE I G 0 = 1 :=
  exp_zero

/-- The curve `t ↦ exp (t • ξ)` is a global integral curve of the left-invariant vector field
of `ξ`. -/
theorem isMIntegralCurve_expE_smul (ξ : E) :
    IsMIntegralCurve (fun t : ℝ => expE I G (t • ξ))
      (mulInvariantVectorField (I := I) (ξ : GroupLieAlgebra I G)) :=
  isMIntegralCurve_exp_smul (I := I) (G := G) (ξ : GroupLieAlgebra I G)

/-- The exponential of a natural multiple is a power of the exponential. -/
theorem expE_nsmul (N : ℕ) (ξ : E) : expE I G (N • ξ) = expE I G ξ ^ N :=
  exp_nsmul (I := I) (G := G) N (ξ : GroupLieAlgebra I G)

/-- If `N * s = 1`, then `exp ξ = (exp (s • ξ)) ^ N`. -/
theorem expE_eq_pow {N : ℕ} {s : ℝ} (h : (N : ℝ) * s = 1) (ξ : E) :
    expE I G ξ = expE I G (s • ξ) ^ N :=
  exp_eq_pow_of_mul_eq_one h (ξ : GroupLieAlgebra I G)

/-! ### Chart solutions are one-parameter subgroups -/

variable {I G} in
/-- Let `F` agree with the chart field on the ball of radius `r`, which lies in the chart domain.
A continuous curve `γ` on `[-2, 2]` of norm less than `r` which solves the integral equation
`γ t = ∫₀ᵗ F (γ s, ξ) ds` is the one-parameter subgroup of `ξ` read in the recentred chart:
`exp (t • ξ) = chartPoint I G (γ t)` for `t` in `(-2, 2)`.  This is uniqueness of integral curves
of the left-invariant vector field of `ξ`. -/
theorem expE_smul_eq_chartPoint_of_solution {F : E × E → E} {r : ℝ} (hF : Continuous F)
    (hmem : ∀ x, ‖x‖ < r → x + chartCentre I G ∈ (extChartAt I (1 : G)).target)
    (hFeq : ∀ x ξ, ‖x‖ < r → F (x, ξ) = chartField I G x ξ)
    {ξ : E} {γ : C(ParamODE.Time 2, E)} (hγ : ‖γ‖ < r)
    (hsol : ∀ t : ParamODE.Time 2,
      γ t = ∫ s in (0 : ℝ)..t, F (ParamODE.extend (zero_le_two : (0 : ℝ) ≤ 2) γ s, ξ)) -- totalisation-audit: allow continuous integrand on a compact interval is interval integrable, and E is complete
    (t : ParamODE.Time 2) (ht : (t : ℝ) ∈ Ioo (-2 : ℝ) 2) :
    expE I G ((t : ℝ) • ξ) = chartPoint I G (γ t) := by
  have : T2Space G := t2Space_of_lieGroup I G
  have hT : (0 : ℝ) ≤ 2 := zero_le_two
  have hgc : Continuous fun s : ℝ => F (ParamODE.extend hT γ s, ξ) :=
    hF.comp ((ParamODE.continuous_extend hT γ).prodMk continuous_const)
  -- the right-hand side of the integral equation, defined for all real times
  let f : ℝ → E := fun u => ∫ s in (0 : ℝ)..u, F (ParamODE.extend hT γ s, ξ) -- totalisation-audit: allow continuous integrand on a compact interval is interval integrable, and E is complete
  have hfγ : ∀ (u : ℝ) (hu : u ∈ Icc (-2 : ℝ) 2), f u = γ ⟨u, hu⟩ := fun u hu =>
    (hsol ⟨u, hu⟩).symm
  have hnorm : ∀ u ∈ Icc (-2 : ℝ) 2, ‖f u‖ < r := fun u hu => by
    rw [hfγ u hu]
    exact (γ.norm_coe_le_norm _).trans_lt hγ
  -- on `(-2, 2)` it solves the equation of the chart field
  have hderiv : ∀ u ∈ Ioo (-2 : ℝ) 2, HasDerivAt f (chartField I G (f u) ξ) u := by
    intro u hu
    have hu' : u ∈ Icc (-2 : ℝ) 2 := Ioo_subset_Icc_self hu
    have h1 : HasDerivAt f (F (ParamODE.extend hT γ u, ξ)) u :=
      (hgc.integral_hasStrictDerivAt 0 u).hasDerivAt
    have h2 : ParamODE.extend hT γ u = f u := by
      rw [hfγ u hu']
      exact ParamODE.extend_coe hT γ ⟨u, hu'⟩
    rw [h2, hFeq _ _ (hnorm u hu')] at h1
    exact h1
  -- hence it gives an integral curve of the left-invariant vector field, starting at `1`
  have hcurve := isMIntegralCurveOn_chartPoint (I := I) (G := G) (ξ := ξ) isOpen_Ioo hderiv
    (fun u hu => hmem _ (hnorm u (Ioo_subset_Icc_self hu)))
  have h0 : chartPoint I G (f 0) = expE I G ((0 : ℝ) • ξ) := by
    have hf0 : f 0 = 0 := intervalIntegral.integral_same
    rw [hf0, chartPoint_zero, zero_smul, expE_zero]
  have huniq := isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless (t₀ := (0 : ℝ))
    (by norm_num : (0 : ℝ) ∈ Ioo (-2 : ℝ) 2)
    (contMDiff_one_mulInvariantVectorField (ξ : GroupLieAlgebra I G)) hcurve
    ((isMIntegralCurve_expE_smul I G ξ).isMIntegralCurveOn _) h0
  have h3 : chartPoint I G (f t) = expE I G ((t : ℝ) • ξ) := huniq ht
  rw [hfγ (t : ℝ) (Ioo_subset_Icc_self ht)] at h3
  exact h3.symm

/-! ### The velocity of one-parameter subgroups in the chart -/

/-- Read in the chart at the identity, the curve `t ↦ exp (t • ξ)` has derivative `ξ` at time
`0`. -/
theorem hasDerivAt_extChartAt_expE_smul_zero (ξ : E) :
    HasDerivAt (fun t : ℝ => extChartAt I (1 : G) (expE I G (t • ξ))) ξ 0 := by
  -- the base point `exp (0 • ξ)` of the chart is generalised, so that it can be replaced by `1`
  have key : ∀ g : G, expE I G ((0 : ℝ) • ξ) = g →
      HasDerivAt (extChartAt I g ∘ fun t : ℝ => expE I G (t • ξ))
        (tangentCoordChange I g g g
          (mulInvariantVectorField (I := I) (ξ : GroupLieAlgebra I G) g)) 0 := by
    rintro g rfl
    exact ((isMIntegralCurve_expE_smul I G ξ).isMIntegralCurveAt
      0).eventually_hasDerivAt.self_of_nhds
  have e1 : tangentCoordChange I (1 : G) 1 1
      (mulInvariantVectorField (I := I) (ξ : GroupLieAlgebra I G) (1 : G)) = ξ :=
    (tangentCoordChange_self (mem_extChartAt_source (1 : G))).trans
      (mulInvariantVectorField_one (I := I) (G := G) (ξ : GroupLieAlgebra I G))
  exact (key 1 (by rw [zero_smul, expE_zero])).congr_deriv e1

section Bump

variable [HasContDiffBump E]

/-! ### Local identification with the solution family -/

/-- **Local identification along one-parameter subgroups.**  For every `n ≠ 0` there is a family
`Γ` of continuous curves on `[-2, 2]`, of class `C^n` at `0` and with `Γ 0 = 0`, such that for
`ξ` near `0` the curve `Γ ξ` stays in the chart domain at all times of `[-2, 2]` and is the
one-parameter subgroup of `ξ` read in the recentred chart at the identity for times in the open
interval: `exp (t • ξ) = chartPoint I G (Γ ξ t)` for `t` in `(-2, 2)`. -/
theorem exists_chartSolution_smul {n : ℕ} (hn : n ≠ 0) :
    ∃ Γ : E → C(ParamODE.Time 2, E), ContDiffAt ℝ n Γ 0 ∧ Γ 0 = 0 ∧
      ∀ᶠ ξ in 𝓝 (0 : E), ∀ t : ParamODE.Time 2,
        Γ ξ t + chartCentre I G ∈ (extChartAt I (1 : G)).target ∧
          ((t : ℝ) ∈ Ioo (-2 : ℝ) 2 → expE I G ((t : ℝ) • ξ) = chartPoint I G (Γ ξ t)) := by
  obtain ⟨F, r, hr, hF, hF0, hmem, hFeq⟩ := exists_cutoffField_of_hasContDiffBump I G n
  have hT : (0 : ℝ) ≤ 2 := zero_le_two
  obtain ⟨Γ, hΓ, hΓ0, hsol⟩ := ParamODE.exists_contDiffAt_solutions hn hF hF0 hT
  refine ⟨Γ, hΓ, hΓ0, ?_⟩
  -- near `0`, the curve `Γ ξ` stays in the ball on which `F` is the chart field
  have hsmall : ∀ᶠ ξ in 𝓝 (0 : E), ‖Γ ξ‖ < r := by
    have hlt : ‖Γ 0‖ < r := by
      rw [hΓ0, norm_zero]
      exact hr
    exact hΓ.continuousAt.norm.eventually_lt continuousAt_const hlt
  filter_upwards [hsol, hsmall] with ξ hξ hξr t
  exact ⟨hmem _ ((ContinuousMap.norm_coe_le_norm (Γ ξ) t).trans_lt hξr),
    expE_smul_eq_chartPoint_of_solution hF.continuous hmem hFeq hξr hξ t⟩

/-- **Local identification.**  For every `n ≠ 0` there is a family `Γ` of continuous curves on
`[-2, 2]`, of class `C^n` at `0` and with `Γ 0 = 0`, such that for `ξ` near `0` the exponential
of `ξ` is the point with recentred chart coordinate `Γ ξ 1`. -/
theorem exists_chartSolution {n : ℕ} (hn : n ≠ 0) :
    ∃ Γ : E → C(ParamODE.Time 2, E), ContDiffAt ℝ n Γ 0 ∧ Γ 0 = 0 ∧
      ∀ᶠ ξ in 𝓝 (0 : E), Γ ξ timeOne + chartCentre I G ∈ (extChartAt I (1 : G)).target ∧
        expE I G ξ = chartPoint I G (Γ ξ timeOne) := by
  obtain ⟨Γ, hΓ, hΓ0, hev⟩ := exists_chartSolution_smul I G hn
  refine ⟨Γ, hΓ, hΓ0, ?_⟩
  filter_upwards [hev] with ξ hξ
  refine ⟨(hξ timeOne).1, ?_⟩
  have h := (hξ timeOne).2 (by norm_num)
  rwa [coe_timeOne, one_smul] at h

/-! ### Regularity at the origin -/

/-- The exponential map read in the chart at the identity is `C^n` at `0`, for every natural
number `n`. -/
theorem contDiffAt_extChartAt_exp_nat (n : ℕ) :
    ContDiffAt ℝ n (fun ξ : E => extChartAt I (1 : G) (expE I G ξ)) 0 := by
  obtain ⟨Γ, hΓ, -, hev⟩ := exists_chartSolution I G (Nat.succ_ne_zero n)
  have h1 : ContDiffAt ℝ (n + 1 : ℕ) (fun ξ : E => Γ ξ timeOne + chartCentre I G) 0 :=
    ((ContinuousMap.evalCLM ℝ timeOne).contDiff.contDiffAt.comp (0 : E) hΓ).add contDiffAt_const
  refine (h1.of_le (by exact_mod_cast Nat.le_succ n)).congr_of_eventuallyEq ?_
  filter_upwards [hev] with ξ hξ
  rw [hξ.2, extChartAt_chartPoint hξ.1]

/-- The exponential map read in the chart at the identity is smooth at `0`. -/
theorem contDiffAt_extChartAt_exp :
    ContDiffAt ℝ ∞ (fun ξ : E => extChartAt I (1 : G) (expE I G ξ)) 0 :=
  contDiffAt_infty.2 fun n => contDiffAt_extChartAt_exp_nat I G n

/-- Near `0` the exponential map takes values in the source of the chart at the identity. -/
theorem eventually_expE_mem_source :
    ∀ᶠ ξ in 𝓝 (0 : E), expE I G ξ ∈ (extChartAt I (1 : G)).source := by
  obtain ⟨Γ, -, -, hev⟩ := exists_chartSolution I G one_ne_zero
  filter_upwards [hev] with ξ hξ
  rw [hξ.2]
  exact chartPoint_mem_source hξ.1

/-- For each natural number `n`, the exponential map is `C^n` at every point of a neighbourhood
of `0`.  The neighbourhood may depend on `n`. -/
theorem eventually_contMDiffAt_expE (n : ℕ) :
    ∀ᶠ η in 𝓝 (0 : E), ContMDiffAt 𝓘(ℝ, E) I n (expE I G) η := by
  have h1 := (contDiffAt_extChartAt_exp_nat I G n).eventually (by simp)
  have h2 := (eventually_expE_mem_source I G).eventually_nhds
  filter_upwards [h1, h2] with η hη hsrc
  exact contMDiffAt_of_contDiffAt_extChartAt (mod_cast le_top) hsrc hη

/-- The exponential map is smooth at `0`. -/
theorem contMDiffAt_expE_zero : ContMDiffAt 𝓘(ℝ, E) I ∞ (expE I G) 0 :=
  contMDiffAt_of_contDiffAt_extChartAt le_rfl (eventually_expE_mem_source I G)
    (contDiffAt_extChartAt_exp I G)

/-- The exponential map is continuous at `0`. -/
theorem continuousAt_expE_zero : ContinuousAt (expE I G) 0 :=
  (contMDiffAt_expE_zero I G).continuousAt

/-! ### The differential at the origin -/

/-- **The differential of the exponential map at the origin is the identity.**  The statement is
for the exponential map read in the chart at the identity, as a map from `E` to `E`. -/
theorem hasFDerivAt_extChartAt_exp_zero :
    HasFDerivAt (fun ξ : E => extChartAt I (1 : G) (expE I G ξ))
      (ContinuousLinearMap.id ℝ E) 0 := by
  obtain ⟨L, hL⟩ := (contDiffAt_extChartAt_exp_nat I G 1).differentiableAt (by simp)
  refine hL.congr_fderiv (ContinuousLinearMap.ext fun ξ => ?_)
  -- the value of `L` on `ξ` is the derivative along the ray `t ↦ t • ξ`
  have h1 : HasDerivAt (fun t : ℝ => t • ξ) ξ 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const ξ
  have hL0 : HasFDerivAt (fun ξ : E => extChartAt I (1 : G) (expE I G ξ)) L ((0 : ℝ) • ξ) := by
    rwa [zero_smul]
  have h2 := hL0.comp_hasDerivAt (0 : ℝ) h1
  rw [ContinuousLinearMap.id_apply]
  exact h2.unique (hasDerivAt_extChartAt_expE_smul_zero I G ξ)

/-- The differential of the exponential map at the origin, read in the chart at the identity, is
a strict derivative.  This is the hypothesis of the inverse function theorem. -/
theorem hasStrictFDerivAt_extChartAt_exp_zero :
    HasStrictFDerivAt (fun ξ : E => extChartAt I (1 : G) (expE I G ξ))
      (ContinuousLinearMap.id ℝ E) 0 :=
  (contDiffAt_extChartAt_exp_nat I G 1).hasStrictFDerivAt'
    (hasFDerivAt_extChartAt_exp_zero I G) (by simp)

/-- The manifold derivative of the exponential map at the origin is the identity of `E`.  Both
the tangent space of `E` at `0` and the tangent space of `G` at `exp 0 = 1` are definitionally
`E`. -/
theorem hasMFDerivAt_expE_zero :
    HasMFDerivAt 𝓘(ℝ, E) I (expE I G) 0 (ContinuousLinearMap.id ℝ E) := by
  -- the base point `exp 0` of the chart is generalised, so that it can be replaced by `1`
  have key : ∀ g : G, (1 : G) = g →
      HasFDerivWithinAt (extChartAt I g ∘ expE I G ∘ (extChartAt 𝓘(ℝ, E) (0 : E)).symm)
        (ContinuousLinearMap.id ℝ E) (range 𝓘(ℝ, E)) (extChartAt 𝓘(ℝ, E) (0 : E) 0) := by
    rintro g rfl
    rw [extChartAt_model_space_eq_id, PartialEquiv.refl_symm, PartialEquiv.refl_coe,
      Function.comp_id, ModelWithCorners.range_eq_univ, hasFDerivWithinAt_univ]
    exact hasFDerivAt_extChartAt_exp_zero I G
  exact ⟨continuousAt_expE_zero I G, key _ (expE_zero I G).symm⟩

/-! ### Global smoothness -/

/-- The exponential map is `C^n` at every point, for every natural number `n`.  It is the
composition of a scaling into the neighbourhood of `0` where it is already `C^n`, of `exp`, and of
a power map of `G`. -/
theorem contMDiffAt_expE_nat (n : ℕ) (ξ₀ : E) : ContMDiffAt 𝓘(ℝ, E) I n (expE I G) ξ₀ := by
  obtain ⟨N, s, hNs, hU⟩ :=
    exists_nat_mul_eq_one_smul_mem (eventually_contMDiffAt_expE I G n) ξ₀
  have h1 : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) n (fun ξ : E => s • ξ) ξ₀ :=
    (contDiff_const_smul s).contMDiff.contMDiffAt
  have h2 : ContMDiffAt 𝓘(ℝ, E) I n (fun ξ : E => expE I G (s • ξ)) ξ₀ :=
    ContMDiffAt.comp ξ₀ hU h1
  have h3 : ContMDiffAt I I n (fun g : G => g ^ N) (expE I G (s • ξ₀)) :=
    ((contMDiff_pow (I := I) (n := ∞) N).of_le (mod_cast le_top)).contMDiffAt
  exact (h3.comp ξ₀ h2).congr_of_eventuallyEq
    (Eventually.of_forall fun ξ => expE_eq_pow I G hNs ξ)

/-- **The exponential map of a Lie group is smooth.** -/
theorem contMDiff_exp : ContMDiff 𝓘(ℝ, E) I ∞ (expE I G) := fun ξ₀ =>
  contMDiffAt_infty.2 fun n => contMDiffAt_expE_nat I G n ξ₀

/-- The exponential map is continuous. -/
theorem continuous_expE : Continuous (expE I G) :=
  (contMDiff_exp I G).continuous

/-- The map `(t, ξ) ↦ exp (t • ξ)` is smooth on the normed space `ℝ × E`. -/
theorem contMDiff_expE_smul :
    ContMDiff 𝓘(ℝ, ℝ × E) I ∞ (fun p : ℝ × E => expE I G (p.1 • p.2)) :=
  (contMDiff_exp I G).comp (contDiff_fst.smul contDiff_snd).contMDiff

/-- The map `(t, ξ) ↦ exp (t • ξ)` is smooth on the product manifold `ℝ × E`. -/
theorem contMDiff_expE_smul_prod :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) I ∞ (fun p : ℝ × E => expE I G (p.1 • p.2)) := by
  have h := contMDiff_expE_smul I G
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod] at h
  exact h

/-- Each one-parameter subgroup `t ↦ exp (t • ξ)` is smooth. -/
theorem contMDiff_expE_smul_const (ξ : E) :
    ContMDiff 𝓘(ℝ, ℝ) I ∞ (fun t : ℝ => expE I G (t • ξ)) :=
  (contMDiff_exp I G).comp (contDiff_id.smul contDiff_const).contMDiff

variable {I G} in
/-- The one-parameter subgroup `t ↦ exp (t • v)` of an element `v` of the Lie algebra is a smooth
curve. -/
theorem contMDiff_exp_smul_const (v : GroupLieAlgebra I G) :
    ContMDiff 𝓘(ℝ, ℝ) I ∞ (fun t : ℝ => exp (t • v)) :=
  contMDiff_expE_smul_const I G v

end Bump

end Exp

end LieGroupExponential
