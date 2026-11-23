import Mathlib

/-!
# Left-invariant vector fields in the chart at the identity

Let `G` be a real Lie group of class `C^∞` modelled on a normed space `E` through a model with
corners `I`.  This file reads the left-invariant vector fields of `G` in the preferred chart at
the identity, recentred so that the identity corresponds to `0 : E`.

## The recentred chart

`chartCentre I G` is the image `c` of `1 : G` under the extended chart `φ` at the identity, and
`chartPoint I G x = φ.symm (x + c)` is the point of `G` with recentred coordinate `x`, so that
`chartPoint I G 0 = 1`.  The recentred chart domain is `chartDomain I G`.  Without boundary it is
an open neighbourhood of `0`, and `chartPoint` maps a ball around `0` into the chart source.

## The chart field

`chartField I G x ξ` is the left-invariant vector field of `ξ`, evaluated at `g = chartPoint I G x`
and expressed in the chart at the identity: it is `tangentCoordChange I g 1 g` applied to
`mulInvariantVectorField ξ g`.  It is linear in `ξ`, the bundled form being `chartFieldCLM`, and
at `x = 0` it is the identity (`chartField_zero_left`).  The chart meaning holds for `x` in
`chartDomain I G`.  For other `x` the definition still returns a value, linear in `ξ`, but it has
no geometric meaning; every statement that uses the chart meaning carries the hypothesis that `x`
lies in the chart domain.

## Regularity

Two independent arguments are given.

* `contMDiff_mulInvariantVectorField_infty`: the left-invariant vector field of a `C^∞` Lie group
  is a `C^∞` section of the tangent bundle.  Mathlib proves class `C^2` for a `C^3` group; the same
  argument, which writes the field as the tangent map of the multiplication composed with smooth
  maps, gives `C^∞` here.  Reading this section in the trivialisation of the tangent bundle at `1`,
  whose second component is exactly the `tangentCoordChange` expression, shows that
  `x ↦ chartField I G x ξ` is `C^∞` on the whole chart domain for each fixed `ξ`
  (`contDiffOn_chartField`).  No hypothesis on the boundary or on the dimension is needed.
* The group law read in the recentred chart is
  `chartMul I G (x, y) = φ (chartPoint I G x * chartPoint I G y) - c`.  It is smooth at `(0, 0)`
  because multiplication is smooth (`contDiffAt_chartMul`).  For `x` in the chart domain the chain
  rule identifies `chartFieldCLM I G x` with the partial derivative of the chart group law in its
  second variable at `y = 0` (`hasFDerivAt_chartMul_right`).  Hence `x ↦ chartFieldCLM I G x` is
  smooth at `0` as a map into `E →L[ℝ] E` (`contDiffAt_chartFieldCLM`), and the chart field is
  jointly smooth at every point `(0, ξ)` (`contDiffAt_chartField`).  This needs a model without
  boundary, but no finite dimensionality.

## Cut-off

Multiplying by a smooth bump function which is `1` near `0` and supported in the chart domain
gives a globally defined map `F : E × E → E` with `F (x, 0) = 0` for all `x` and
`F (x, ξ) = chartField I G x ξ` for `‖x‖ < r`.  This is the form of right-hand side required by
`ParamODE.exists_contDiffAt_solutions`.

* `exists_cutoffField_of_hasContDiffBump` assumes only that `E` has smooth bump functions and
  uses the second regularity argument: `F (x, ξ) = χ x • chartFieldCLM I G x ξ`.  The map `F` and
  the radius `r` depend on the class `C^n` asked for.
* `exists_cutoffField_infty` works in finite dimension and uses the first regularity argument: it
  is the sum over a basis `b` of `ξ ↦ b.coord i ξ • (χ x • chartField I G x (b i))`.  It gives a
  single `C^∞` map `F` and a single radius, and records that `F` is additive and homogeneous in
  `ξ`.  `exists_cutoffField` is its `C^n` form, without the linearity clauses.

## Back to the group

`isMIntegralCurveOn_chartPoint`: a solution `f` of `f' = chartField I G (f t) ξ` that stays in the
chart domain gives the integral curve `t ↦ chartPoint I G (f t)` of the left-invariant vector
field of `ξ`.  The pointwise statement is `hasMFDerivAt_chartPoint`.  The argument is the
chart-to-manifold conversion in the proof of `exists_isMIntegralCurveAt_of_contMDiffAt` in mathlib.
-/

noncomputable section

open scoped Manifold ContDiff Topology
open Set Metric Bundle Function

namespace LieGroupExponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  (G : Type*) [TopologicalSpace G] [ChartedSpace H G] [Group G]

/-! ### The recentred chart at the identity -/

/-- The image of the identity under the extended chart at the identity. -/
def chartCentre : E := extChartAt I (1 : G) 1

/-- The point of `G` whose coordinate in the chart at the identity, recentred at `0`, is `x`.
Outside `chartDomain I G` the value is whatever the total inverse chart returns. -/
def chartPoint (x : E) : G := (extChartAt I (1 : G)).symm (x + chartCentre I G)

/-- The domain of the recentred chart: those `x` for which `x + chartCentre I G` lies in the
target of the extended chart at the identity. -/
def chartDomain : Set E := {x | x + chartCentre I G ∈ (extChartAt I (1 : G)).target}

/-- The group law read in the recentred chart at the identity. -/
def chartMul (p : E × E) : E :=
  extChartAt I (1 : G) (chartPoint I G p.1 * chartPoint I G p.2) - chartCentre I G

variable {I G} in
/-- Membership of the chart domain, unfolded. -/
theorem mem_chartDomain_iff {x : E} :
    x ∈ chartDomain I G ↔ x + chartCentre I G ∈ (extChartAt I (1 : G)).target := Iff.rfl

/-- The origin lies in the chart domain; it is the coordinate of the identity. -/
theorem zero_mem_chartDomain : (0 : E) ∈ chartDomain I G := by
  rw [mem_chartDomain_iff, zero_add]
  exact mem_extChartAt_target (1 : G)

/-- The recentred chart sends `0` to the identity. -/
@[simp]
theorem chartPoint_zero : chartPoint I G 0 = 1 := by
  rw [chartPoint, zero_add, chartCentre, extChartAt_to_inv]

variable {I G} in
/-- `chartPoint` maps the chart domain into the source of the chart at the identity. -/
theorem chartPoint_mem_source {x : E} (hx : x ∈ chartDomain I G) :
    chartPoint I G x ∈ (extChartAt I (1 : G)).source :=
  (extChartAt I (1 : G)).map_target hx

variable {I G} in
/-- On the chart domain, the chart at the identity inverts `chartPoint` up to the recentring. -/
theorem extChartAt_chartPoint {x : E} (hx : x ∈ chartDomain I G) :
    extChartAt I (1 : G) (chartPoint I G x) = x + chartCentre I G :=
  (extChartAt I (1 : G)).right_inv hx

/-- Without boundary, the chart domain is open. -/
theorem isOpen_chartDomain [I.Boundaryless] : IsOpen (chartDomain I G) :=
  (isOpen_extChartAt_target (I := I) (1 : G)).preimage
    (continuous_id.add continuous_const)

/-- Without boundary, the chart domain is a neighbourhood of the origin. -/
theorem eventually_add_chartCentre_mem_target [I.Boundaryless] :
    ∀ᶠ x in 𝓝 (0 : E), x + chartCentre I G ∈ (extChartAt I (1 : G)).target :=
  (isOpen_chartDomain I G).eventually_mem (zero_mem_chartDomain I G)

/-- A ball around `0` lies in the chart domain, so that `chartPoint` maps it into the source of
the chart at the identity. -/
theorem exists_ball_chartPoint_mem_source [I.Boundaryless] :
    ∃ r : ℝ, 0 < r ∧ ∀ x : E, ‖x‖ < r →
      x + chartCentre I G ∈ (extChartAt I (1 : G)).target ∧
        chartPoint I G x ∈ (extChartAt I (1 : G)).source := by
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.1 (isOpen_chartDomain I G) 0 (zero_mem_chartDomain I G)
  refine ⟨r, hr, fun x hx => ?_⟩
  have hxU : x ∈ chartDomain I G := hsub (mem_ball_zero_iff.2 hx)
  exact ⟨hxU, chartPoint_mem_source hxU⟩

/-! ### The left-invariant vector fields read in the chart -/

variable [LieGroup I ∞ G]

/-- The left-invariant vector field of `ξ`, evaluated at `chartPoint I G x` and expressed in the
chart at the identity.  Here `ξ : E` is regarded as an element of `GroupLieAlgebra I G`, which is
definitionally `E`.

The chart interpretation holds for `x` in `chartDomain I G`.  For `x` outside it,
`chartPoint I G x` is an unspecified value of the total inverse chart and need not lie in the
source of the chart at the identity, so `tangentCoordChange` is not a genuine change of
coordinates there.  The value is then unspecified, although still linear in `ξ`; all statements
below that use the chart meaning restrict to the chart domain. -/
def chartField (x ξ : E) : E :=
  tangentCoordChange I (chartPoint I G x) (1 : G) (chartPoint I G x)
    (mulInvariantVectorField (I := I) (ξ : GroupLieAlgebra I G) (chartPoint I G x))

/-- `chartField I G x` as a continuous linear map: the derivative at the identity of left
multiplication by `chartPoint I G x`, followed by the change of coordinates to the chart at the
identity.  As for `chartField`, this has its chart meaning only for `x` in `chartDomain I G`. -/
def chartFieldCLM (x : E) : E →L[ℝ] E :=
  (tangentCoordChange I (chartPoint I G x) 1 (chartPoint I G x)).comp
    (mfderiv I I (fun h : G => chartPoint I G x * h) 1) -- totalisation-audit: allow left multiplication in a Lie group is smooth, so mfderiv is its genuine derivative

/-- `chartFieldCLM` is the bundled form of `chartField`. -/
@[simp]
theorem chartFieldCLM_apply (x ξ : E) : chartFieldCLM I G x ξ = chartField I G x ξ := rfl

/-- The chart field of `ξ = 0` vanishes identically.  This is the stationary parameter of
`ParamODE.exists_contDiffAt_solutions`. -/
@[simp]
theorem chartField_zero (x : E) : chartField I G x 0 = 0 := by
  rw [← chartFieldCLM_apply, map_zero]

/-- The chart field is additive in the Lie algebra variable. -/
theorem chartField_add (x ξ η : E) :
    chartField I G x (ξ + η) = chartField I G x ξ + chartField I G x η := by
  simp only [← chartFieldCLM_apply, map_add]

/-- The chart field is homogeneous in the Lie algebra variable. -/
theorem chartField_smul (x : E) (c : ℝ) (ξ : E) :
    chartField I G x (c • ξ) = c • chartField I G x ξ := by
  simp only [← chartFieldCLM_apply, map_smul]

/-- At the origin of the recentred chart, the chart field of `ξ` is `ξ`. -/
theorem chartField_zero_left (ξ : E) : chartField I G 0 ξ = ξ := by
  have h1 : mulInvariantVectorField (I := I) (ξ : GroupLieAlgebra I G) (1 : G) = ξ := by
    have hid : (fun h : G => (1 : G) * h) = id := funext one_mul
    have hd := mfderiv_id (I := I) (M := G) (x := (1 : G))
    unfold mulInvariantVectorField
    rw [hid, hd]
    rfl
  unfold chartField
  rw [chartPoint_zero, h1]
  exact tangentCoordChange_self (mem_extChartAt_source (1 : G))

/-- Expansion of `chartField` in a finite basis of `E`. -/
theorem chartField_eq_sum {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E) (x ξ : E) :
    chartField I G x ξ = ∑ i, b.coord i ξ • chartField I G x (b i) := by
  conv_lhs => rw [← b.sum_repr ξ]
  simp only [← chartFieldCLM_apply, map_sum, map_smul, Module.Basis.coord_apply]

/-! ### Smoothness on the chart domain -/

variable {I G} in
/-- The left-invariant vector field of a `C^∞` Lie group is a `C^∞` section of the tangent bundle.
The proof is that of mathlib's `contMDiff_mulInvariantVectorField`, with the smoothness classes
`C^2` and `C^3` replaced by `C^∞`. -/
theorem contMDiff_mulInvariantVectorField_infty (v : GroupLieAlgebra I G) :
    ContMDiff I I.tangent ∞
      (fun g : G => (⟨g, mulInvariantVectorField v g⟩ : TangentBundle I G)) := by
  let fg : G → TangentBundle I G := fun g ↦ TotalSpace.mk' E g 0
  have sfg : ContMDiff I I.tangent ∞ fg := contMDiff_zeroSection _ _
  let fv : G → TangentBundle I G := fun _ ↦ TotalSpace.mk' E 1 v
  have sfv : ContMDiff I I.tangent ∞ fv := contMDiff_const
  let F₁ : G → (TangentBundle I G × TangentBundle I G) := fun g ↦ (fg g, fv g)
  have S₁ : ContMDiff I (I.tangent.prod I.tangent) ∞ F₁ := sfg.prodMk sfv
  let F₂ : (TangentBundle I G × TangentBundle I G) → TangentBundle (I.prod I) (G × G) :=
    (equivTangentBundleProd I G I G).symm
  have S₂ : ContMDiff (I.tangent.prod I.tangent) (I.prod I).tangent ∞ F₂ :=
    contMDiff_equivTangentBundleProd_symm
  let F₃ : TangentBundle (I.prod I) (G × G) → TangentBundle I G :=
    tangentMap (I.prod I) I (fun (p : G × G) ↦ p.1 * p.2)
  have S₃ : ContMDiff (I.prod I).tangent I.tangent ∞ F₃ := by
    apply ContMDiff.contMDiff_tangentMap _ (m := ∞) le_rfl
    exact contMDiff_mul I ∞
  have S := (S₃.comp S₂).comp S₁
  convert! S with g
  · simp [F₁, F₂, F₃, fg, fv]
  · simp only [comp_apply, tangentMap, F₃, F₂, F₁, fg, fv]
    rw [mfderiv_prod_eq_add_apply ((contMDiff_mul I ∞).mdifferentiableAt (by simp))]
    change _ = (mfderiv I I (fun z : G => z * (1 : G)) g) 0 + -- totalisation-audit: allow right multiplication in a Lie group is smooth, so mfderiv is its genuine derivative
      (mfderiv I I (fun z : G => g * z) 1) v -- totalisation-audit: allow left multiplication in a Lie group is smooth, so mfderiv is its genuine derivative
    rw [map_zero, zero_add]
    rfl

variable {I G} in
/-- The left-invariant vector field, read in the trivialisation of the tangent bundle at the
identity, is `C^∞` on the source of the chart at the identity. -/
theorem contMDiffOn_tangentCoordChange_mulInvariantVectorField (v : GroupLieAlgebra I G) :
    ContMDiffOn I 𝓘(ℝ, E) ∞
      (fun g : G => tangentCoordChange I g 1 g (mulInvariantVectorField v g))
      (chartAt H (1 : G)).source := by
  have h := (contMDiff_mulInvariantVectorField_infty (I := I) (G := G) v).contMDiffOn
    (s := (chartAt H (1 : G)).source)
  have he : MapsTo (fun g : G => (⟨g, mulInvariantVectorField v g⟩ : TangentBundle I G))
      (chartAt H (1 : G)).source (trivializationAt E (TangentSpace I) (1 : G)).source := by
    intro g hg
    simpa using hg
  exact (((trivializationAt E (TangentSpace I) (1 : G)).contMDiffOn_iff he).1 h).2

/-- For fixed `ξ`, the map `x ↦ chartField I G x ξ` is `C^∞` on the chart domain. -/
theorem contDiffOn_chartField (ξ : E) :
    ContDiffOn ℝ ∞ (fun x => chartField I G x ξ) (chartDomain I G) := by
  have h1 := contMDiffOn_tangentCoordChange_mulInvariantVectorField (I := I) (G := G)
    (ξ : GroupLieAlgebra I G)
  have h2 : ContMDiffOn 𝓘(ℝ, E) I ∞ (extChartAt I (1 : G)).symm (extChartAt I (1 : G)).target :=
    contMDiffOn_extChartAt_symm (1 : G)
  have h3 : ContDiffOn ℝ ∞
      ((fun g : G => tangentCoordChange I g 1 g
          (mulInvariantVectorField (I := I) (ξ : GroupLieAlgebra I G) g)) ∘
        (extChartAt I (1 : G)).symm)
      (extChartAt I (1 : G)).target := by
    refine (h1.comp h2 fun y hy => ?_).contDiffOn
    rw [mem_preimage, ← extChartAt_source I]
    exact (extChartAt I (1 : G)).map_target hy
  have h4 : ContDiffOn ℝ ∞ (fun x : E => x + chartCentre I G) (chartDomain I G) :=
    (contDiff_id.add contDiff_const).contDiffOn
  exact h3.comp h4 fun x hx => hx

/-! ### Regularity through the chart group law -/

/-- The chart group law is smooth at the origin. -/
theorem contDiffAt_chartMul [I.Boundaryless] : ContDiffAt ℝ ∞ (chartMul I G) 0 := by
  have hm := (contMDiff_mul I ∞ (G := G)).contMDiffAt (x := ((1 : G), (1 : G)))
  rw [contMDiffAt_iff] at hm
  obtain ⟨-, hdiff⟩ := hm
  rw [ModelWithCorners.range_eq_univ, contDiffWithinAt_univ] at hdiff
  set c : E := chartCentre I G with hc
  have hshift : ContDiffAt ℝ ∞ (fun p : E × E => (p.1 + c, p.2 + c)) 0 :=
    (contDiffAt_fst.add contDiffAt_const).prodMk (contDiffAt_snd.add contDiffAt_const)
  have hpt : (fun p : E × E => (p.1 + c, p.2 + c)) 0 =
      extChartAt (I.prod I) ((1 : G), (1 : G)) ((1 : G), (1 : G)) := by
    simp [hc, chartCentre]
  rw [← hpt] at hdiff
  have hcomp := (hdiff.comp (0 : E × E) hshift).sub (contDiffAt_const (c := c))
  refine hcomp.congr_of_eventuallyEq (Filter.Eventually.of_forall fun p => ?_)
  simp only [Function.comp_apply, extChartAt_prod, PartialEquiv.prod_symm,
    PartialEquiv.prod_coe]
  simp [hc, chartMul, chartPoint]

/-- On the recentred chart domain, the chart field at `x` is the partial derivative at `0` of the
chart group law in its second variable. -/
theorem hasFDerivAt_chartMul_right [I.Boundaryless] {x : E}
    (hx : x + chartCentre I G ∈ (extChartAt I (1 : G)).target) :
    HasFDerivAt (fun y : E => chartMul I G (x, y)) (chartFieldCLM I G x) 0 := by
  set g : G := chartPoint I G x with hg
  have hgs : g ∈ (chartAt H (1 : G)).source := by
    have h := chartPoint_mem_source (I := I) (G := G) hx
    rwa [extChartAt_source] at h
  have hL := ((contMDiff_mul_left (I := I) (n := ∞) (a := g)).contMDiffAt.mdifferentiableAt
    (x := (1 : G)) (by simp)).hasMFDerivAt
  have hgs' : (fun h : G => g * h) 1 ∈ (chartAt H (1 : G)).source := by
    rw [show (fun h : G => g * h) 1 = g from mul_one g]
    exact hgs
  have hcomp := (hasMFDerivAt_extChartAt (I := I) hgs').comp 1 hL
  have key : ∀ g' : G, g' = g → ∀ w : E,
      mfderiv I I (chartAt H (1 : G)) g' w = tangentCoordChange I g 1 g w := by -- totalisation-audit: allow g' = g lies in the chart source, where the chart is differentiable
    rintro g' rfl w
    rw [mfderiv_chartAt_eq_tangentCoordChange hgs]
    rfl
  have h2 := hcomp.2
  rw [I.range_eq_univ, hasFDerivWithinAt_univ] at h2
  have h3 := h2.congr_fderiv (g' := chartFieldCLM I G x) (ContinuousLinearMap.ext fun ξ =>
    key ((fun h : G => g * h) 1) (mul_one g)
      (mulInvariantVectorField (I := I) (ξ : GroupLieAlgebra I G) g))
  have h4 : HasFDerivAt (fun y : E => writtenInExtChartAt I 𝓘(ℝ, E) (1 : G)
      (extChartAt I (1 : G) ∘ HMul.hMul g) (y + chartCentre I G)) (chartFieldCLM I G x) 0 := by
    rw [hasFDerivAt_comp_add_right, zero_add]
    exact h3
  exact h4.sub_const (chartCentre I G)

/-- The chart field depends smoothly on the base point near the origin, as a map into the
continuous linear maps. -/
theorem contDiffAt_chartFieldCLM [I.Boundaryless] : ContDiffAt ℝ ∞ (chartFieldCLM I G) 0 := by
  have hμ : ContDiffAt ℝ ∞ (Function.uncurry fun x y : E => chartMul I G (x, y))
      ((0 : E), (fun _ : E => (0 : E)) 0) := contDiffAt_chartMul I G
  refine (ContDiffAt.fderiv (f := fun x y : E => chartMul I G (x, y))
    (g := fun _ : E => (0 : E)) hμ contDiffAt_const (by simp)).congr_of_eventuallyEq ?_
  filter_upwards [eventually_add_chartCentre_mem_target I G] with x hx
  exact (hasFDerivAt_chartMul_right I G hx).fderiv.symm

/-- The chart field is jointly smooth at every point `(0, ξ)`. -/
theorem contDiffAt_chartField [I.Boundaryless] (ξ : E) :
    ContDiffAt ℝ ∞ (fun p : E × E => chartField I G p.1 p.2) (0, ξ) := by
  have h1 : ContDiffAt ℝ ∞ (fun p : E × E => chartFieldCLM I G p.1) ((0 : E), ξ) :=
    (contDiffAt_chartFieldCLM I G).comp ((0 : E), ξ) contDiffAt_fst
  exact h1.clm_apply contDiffAt_snd

/-! ### Cut-off to a globally defined field -/

/-- A globally defined `C^n` field which agrees with the chart field near the origin, on a
space with smooth bump functions. -/
theorem exists_cutoffField_of_hasContDiffBump [HasContDiffBump E] [I.Boundaryless] (n : ℕ) :
    ∃ (F : E × E → E) (r : ℝ), 0 < r ∧ ContDiff ℝ n F ∧ (∀ x, F (x, 0) = 0) ∧
      (∀ x, ‖x‖ < r → x + chartCentre I G ∈ (extChartAt I (1 : G)).target) ∧
      ∀ x ξ, ‖x‖ < r → F (x, ξ) = chartField I G x ξ := by
  have hA : ContDiffAt ℝ n (chartFieldCLM I G) 0 :=
    (contDiffAt_chartFieldCLM I G).of_le (by exact_mod_cast le_top)
  have hev := (hA.eventually (by simp)).and (eventually_add_chartCentre_mem_target I G)
  obtain ⟨r₀, hr₀, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
  obtain ⟨r₁, hr₁, hr₁₀⟩ := exists_between hr₀
  obtain ⟨r, hr, hrr₁⟩ := exists_between hr₁
  let χ : ContDiffBump (0 : E) := ⟨r, r₁, hr, hrr₁⟩
  refine ⟨fun p => χ p.1 • chartFieldCLM I G p.1 p.2, r, hr, ?_, ?_, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro p
    by_cases hp : p.1 ∈ ball (0 : E) r₀
    · have h1 : ContDiffAt ℝ n (fun q : E × E => χ q.1) p :=
        χ.contDiff.contDiffAt.comp p contDiffAt_fst
      have h2 : ContDiffAt ℝ n (fun q : E × E => chartFieldCLM I G q.1) p :=
        (hball p.1 hp).1.comp p contDiffAt_fst
      exact h1.smul (h2.clm_apply contDiffAt_snd)
    · have hzero : (fun q : E × E => χ q.1 • chartFieldCLM I G q.1 q.2) =ᶠ[𝓝 p]
          fun _ => (0 : E) := by
        have hopen : IsOpen {q : E × E | r₁ < ‖q.1‖} :=
          isOpen_lt continuous_const continuous_fst.norm
        have hmem : p ∈ {q : E × E | r₁ < ‖q.1‖} := by
          rw [mem_ball_zero_iff, not_lt] at hp
          exact lt_of_lt_of_le hr₁₀ hp
        filter_upwards [hopen.mem_nhds hmem] with q hq
        have hq' : χ.rOut ≤ dist q.1 0 := by
          rw [dist_zero_right]
          exact le_of_lt hq
        rw [χ.zero_of_le_dist hq', zero_smul]
      exact contDiffAt_const.congr_of_eventuallyEq hzero
  · intro x
    simp
  · intro x hx
    exact (hball x (mem_ball_zero_iff.2 (hx.trans (hrr₁.trans hr₁₀)))).2
  · intro x ξ hx
    have h1 : χ x = 1 := χ.one_of_mem_closedBall (mem_closedBall_zero_iff.2 hx.le)
    simp [h1]

/-- In finite dimension and without boundary, the chart field is the restriction to a ball of a
globally `C^∞` map which is linear in the Lie algebra variable.  Linearity is recorded by the last
two clauses, additivity and homogeneity in `ξ`, which hold for every `x`. -/
theorem exists_cutoffField_infty [FiniteDimensional ℝ E] [I.Boundaryless] :
    ∃ (F : E × E → E) (r : ℝ), 0 < r ∧ ContDiff ℝ ∞ F ∧ (∀ x, F (x, 0) = 0) ∧
      (∀ x, ‖x‖ < r → x + chartCentre I G ∈ (extChartAt I (1 : G)).target) ∧
      (∀ x ξ, ‖x‖ < r → F (x, ξ) = chartField I G x ξ) ∧
      (∀ x ξ η, F (x, ξ + η) = F (x, ξ) + F (x, η)) ∧
      ∀ x (c : ℝ) ξ, F (x, c • ξ) = c • F (x, ξ) := by
  have hU : IsOpen (chartDomain I G) := isOpen_chartDomain I G
  obtain ⟨ρ, hρ, hρU⟩ := Metric.nhds_basis_closedBall.mem_iff.1
    (hU.mem_nhds (zero_mem_chartDomain I G))
  obtain ⟨r, hr, hrρ⟩ := exists_between hρ
  let φ : ContDiffBump (0 : E) := ⟨r, ρ, hr, hrρ⟩
  let b := Module.finBasis ℝ E
  -- the cut-off coefficient fields are globally smooth
  have hg : ∀ i, ContDiff ℝ ∞ (fun x : E => φ x • chartField I G x (b i)) := by
    intro i
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ chartDomain I G
    · exact φ.contDiffAt.smul ((contDiffOn_chartField I G (b i)).contDiffAt (hU.mem_nhds hx))
    · have hxφ : x ∉ tsupport φ := by
        rw [φ.tsupport_eq]
        exact fun h => hx (hρU h)
      have h0 : (fun x : E => φ x • chartField I G x (b i)) =ᶠ[𝓝 x] fun _ => (0 : E) := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hxφ] with y hy
        simp [hy]
      exact contDiffAt_const.congr_of_eventuallyEq h0
  refine ⟨fun p => ∑ i, (LinearMap.toContinuousLinearMap (b.coord i)) p.2 •
    (φ p.1 • chartField I G p.1 (b i)), r, hr, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ContDiff.sum fun i _ => ?_
    exact ((LinearMap.toContinuousLinearMap (b.coord i)).contDiff.comp contDiff_snd).smul
      ((hg i).comp contDiff_fst)
  · intro x
    simp
  · intro x hx
    exact hρU (mem_closedBall_zero_iff.2 (hx.le.trans hrρ.le))
  · intro x ξ hx
    have hφ : φ x = 1 := φ.one_of_mem_closedBall (mem_closedBall_zero_iff.2 hx.le)
    simp only [hφ, one_smul, LinearMap.coe_toContinuousLinearMap']
    exact (chartField_eq_sum I G b x ξ).symm
  · intro x ξ η
    simp only [map_add, add_smul, Finset.sum_add_distrib]
  · intro x c ξ
    simp only [map_smul, smul_eq_mul, mul_smul, Finset.smul_sum]

/-- In finite dimension and without boundary, the chart field is the restriction to a ball of a
globally `C^n` map vanishing at `ξ = 0`.  This is the input of
`ParamODE.exists_contDiffAt_solutions`. -/
theorem exists_cutoffField [FiniteDimensional ℝ E] [I.Boundaryless] (n : ℕ) :
    ∃ (F : E × E → E) (r : ℝ), 0 < r ∧ ContDiff ℝ n F ∧ (∀ x, F (x, 0) = 0) ∧
      (∀ x, ‖x‖ < r → x + chartCentre I G ∈ (extChartAt I (1 : G)).target) ∧
      ∀ x ξ, ‖x‖ < r → F (x, ξ) = chartField I G x ξ := by
  obtain ⟨F, r, hr, hF, hF0, hmem, hFeq, -, -⟩ := exists_cutoffField_infty I G
  exact ⟨F, r, hr, hF.of_le (mod_cast le_top), hF0, hmem, hFeq⟩

/-! ### From chart solutions to integral curves -/

variable {I G} in
/-- If `f` has derivative `chartField I G (f t) ξ` at `t` and `f t` lies in the chart domain, then
`t ↦ chartPoint I G (f t)` has the left-invariant vector field of `ξ` as velocity at `t`. -/
theorem hasMFDerivAt_chartPoint [I.Boundaryless] {ξ : E} {f : ℝ → E} {t : ℝ}
    (hf : HasDerivAt f (chartField I G (f t) ξ) t)
    (hmem : f t + chartCentre I G ∈ (extChartAt I (1 : G)).target) :
    HasMFDerivAt 𝓘(ℝ, ℝ) I (fun t => chartPoint I G (f t)) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (mulInvariantVectorField (I := I) (ξ : GroupLieAlgebra I G) (chartPoint I G (f t)))) := by
  let f' : ℝ → E := fun s => f s + chartCentre I G
  let xₜ : G := chartPoint I G (f t)
  let w : E := mulInvariantVectorField (I := I) (ξ : GroupLieAlgebra I G) xₜ
  have h : HasDerivAt f' (tangentCoordChange I xₜ 1 xₜ w) t := hf.add_const _
  have hft1 : xₜ ∈ (extChartAt I (1 : G)).source := (extChartAt I (1 : G)).map_target hmem
  have hft2 : xₜ ∈ (extChartAt I xₜ).source := mem_extChartAt_source (I := I) xₜ
  have hpt : extChartAt I (1 : G) xₜ = f' t := (extChartAt I (1 : G)).right_inv hmem
  have hc : ContinuousAt (fun s => chartPoint I G (f s)) t :=
    ContinuousAt.comp (g := (extChartAt I (1 : G)).symm) (f := f') (x := t)
      (continuousAt_extChartAt_symm'' hmem) h.continuousAt
  -- changing from the chart at `1` to the chart at `xₜ` and back does nothing to `w`
  have hcomp : tangentCoordChange I (1 : G) xₜ xₜ (tangentCoordChange I xₜ 1 xₜ w) = w := by
    rw [tangentCoordChange_comp ⟨⟨hft2, hft1⟩, hft2⟩, tangentCoordChange_self hft2]
  have hD : HasFDerivWithinAt (extChartAt I xₜ ∘ (extChartAt I (1 : G)).symm)
      (tangentCoordChange I (1 : G) xₜ xₜ) (range I) (f' t) := by
    rw [← hpt]
    exact hasFDerivWithinAt_tangentCoordChange ⟨hft1, hft2⟩
  -- the curve read in the chart at `xₜ` is the chart solution followed by a change of charts
  have key : HasDerivAt ((extChartAt I xₜ ∘ (extChartAt I (1 : G)).symm) ∘ f') w t := by
    have hk := (hD.hasFDerivAt (by simp [I.range_eq_univ])).comp_hasDerivAt t h
    rwa [hcomp] at hk
  exact ⟨hc, key.hasFDerivAt.hasFDerivWithinAt⟩

variable {I G} in
/-- A solution of the chart equation `f' = chartField I G (f t) ξ` which stays in the chart domain
gives an integral curve of the left-invariant vector field of `ξ`.  Openness of `s` is not
essential: the pointwise statement `hasMFDerivAt_chartPoint` holds at each time without it. -/
theorem isMIntegralCurveOn_chartPoint [I.Boundaryless] {ξ : E} {f : ℝ → E} {s : Set ℝ}
    (hs : IsOpen s)
    (hf : ∀ t ∈ s, HasDerivAt f (chartField I G (f t) ξ) t)
    (hmem : ∀ t ∈ s, f t + chartCentre I G ∈ (extChartAt I (1 : G)).target) :
    IsMIntegralCurveOn (fun t => chartPoint I G (f t))
      (mulInvariantVectorField (I := I) (ξ : GroupLieAlgebra I G)) s := by
  rw [isMIntegralCurveOn_iff_isMIntegralCurveAt hs]
  intro t ht
  filter_upwards [hs.mem_nhds ht] with t' ht'
  exact hasMFDerivAt_chartPoint (hf t' ht') (hmem t' ht')

end LieGroupExponential
