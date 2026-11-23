import LieGroupExponential.Smoothness
import Mathlib.Geometry.Manifold.Riemannian.Basic

/-!
# Literature axiom: the exponential map of a bi-invariant metric is radially isometric

**This file contains an axiom.  It is imported temporarily from the literature because the result
is classical; it is not proved in Lean.**  The root module `LieGroupExponential` does not import
this file, so `import LieGroupExponential` stays axiom-free.  Every declaration that depends on the
axiom shows `LieGroupExponential.Literature.dist_expE_eq_norm_of_biInvariant` under
`#print axioms`.  The ledger is `LITERATURE_AXIOMS.md` at the library root.

## Setting

`G` is a Lie group of class `C^∞` modelled without boundary on a finite-dimensional real inner
product space `E`.  Its tangent spaces carry a smooth Riemannian metric (`RiemannianBundle`,
`IsContMDiffRiemannianBundle`), and the metric-space structure of `G` is the Riemannian distance:
`IsRiemannianManifold I G` says that `dist x y` is the infimum of the lengths of `C^1` paths from
`x` to `y`.  The metric is *bi-invariant*: the differentials of the left and right translations
are linear isometries of the tangent spaces (`hleft`, `hright`).  The exponential map
`expE I G : E → G` of this library is the Lie group exponential, `t ↦ expE I G (t • ξ)` being the
one-parameter subgroup with velocity `ξ ∈ T₁G` at `t = 0`; the model space `E` is definitionally
`T₁G`.  For `v : TangentSpace I 1`, `‖v‖` is the Riemannian norm of `v` at the identity.

The norm must be taken on a term *of type* `TangentSpace I 1`: an ascription
`(ξ : TangentSpace I 1)` of `ξ : E` leaves the inferred type `E`, so `‖(ξ : TangentSpace I 1)‖`
would be the norm of `E`, and the statement would then be false whenever the metric at `1` is not
the inner product of `E`.
The axiom therefore quantifies over `v : TangentSpace I 1`; the `example` after the axiom checks
that this norm is not definitionally the norm of `E`.

## Statement

`dist_expE_eq_norm_of_biInvariant`:

* there is `ρ > 0` with `dist (expE I G v) 1 = ‖v‖` (Riemannian norm at `1`) for every
  `v : T₁G` with `‖v‖ < ρ`;
* left and right translations preserve the distance.

## Why the statement is a published theorem

With `M = G` and `p = 1` (J. M. Lee, *Introduction to Riemannian Manifolds*):

* for a bi-invariant metric the geodesics starting at the identity are exactly the one-parameter
  subgroups, so the restricted Riemannian exponential map at `1` is the Lie group exponential map
  (Problem 5-8(c), p. 147);
* the injectivity radius `inj(1)` is positive (definition, p. 165; for compact `M` also
  `inj(M) > 0`, Lemma 6.16, p. 166): `exp₁` is a diffeomorphism from `B_ρ(0)` onto the geodesic ball
  `exp₁ B_ρ(0)` for `0 < ρ ≤ inj(1)`;
* within a geodesic ball around `1` the radial distance function equals the Riemannian distance
  from `1` (Corollary 6.12, p. 162, via the Gauss lemma, Theorem 6.9, p. 159, and Proposition 6.11,
  p. 161), so `d(1, exp₁ v) = |v|_g` for `|v|_g < ρ`;
* an isometry preserves the Riemannian distance (Proposition 2.51, p. 37); bi-invariance says that
  the left and right translations are isometries.

The distance in Lee (p. 36) is the infimum over admissible (piecewise regular) curves, the one of
`IsRiemannianManifold` the infimum over `C^1` paths.  Corollary 6.12 holds for both: its lower
bound, from the Gauss lemma, applies to every piecewise `C^1` curve, and its upper bound is attained
by a radial geodesic, which is smooth.  Proposition 2.51 holds for both, since a diffeomorphism that
is an isometry maps `C^1` paths to `C^1` paths of the same length.

## Why each hypothesis is needed

An axiom with a false instance would make Lean inconsistent, so each hypothesis is load-bearing:

* `IsRiemannianManifold I G`: without it the metric of `G` is arbitrary; for a snowflaked metric
  `d^{1/2}`, still bi-invariant and inducing the same topology, `dist (expE ξ) 1` is of order
  `‖ξ‖^{1/2}`, not `‖ξ‖`;
* `hleft` and `hright`: for a metric that is only left invariant the geodesics through `1` are in
  general not one-parameter subgroups, and right translations are not isometries;
* `IsContMDiffRiemannianBundle`: Lee's Riemannian metrics are smooth (for an invariant metric this
  is automatic, but it is kept to match the source);
* `I.Boundaryless` and `FiniteDimensional ℝ E`: Lee's manifolds are finite-dimensional and without
  boundary here.

Compactness and connectedness are not assumed.  A `MetricSpace` structure satisfying
`IsRiemannianManifold` forces the Riemannian distance to be finite, hence `G` to be connected;
compactness is not needed for the local statement.

## References

J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Graduate Texts in Mathematics 176,
Springer, 2018, doi:10.1007/978-3-319-91755-9.  The copy used is the eBook, ISBN 978-3-319-91755-9.
Checked against the text on 2026-09-18; page numbers are those printed in the book:

* Riemannian distance as an infimum of lengths of admissible curves, p. 36; Proposition 2.51
  (isometry invariance of the Riemannian distance), p. 37;
* Proposition 3.12, p. 69, Theorem 3.14 and Corollary 3.15, p. 70: bi-invariant metrics
  correspond to `Ad`-invariant inner products on `𝔤`; every compact Lie group has one;
* Problem 5-8(c), p. 147: for a bi-invariant metric the geodesics starting at the identity are
  exactly the one-parameter subgroups, and the restricted Riemannian exponential map at the identity
  is the Lie group exponential map;
* Theorem 6.9 (the Gauss lemma), p. 159; Proposition 6.11, p. 161; Corollary 6.12 and
  Corollary 6.13, p. 162: within a geodesic ball the radial distance function is the Riemannian
  distance, and geodesic balls are metric balls of the same radius;
* injectivity radius, p. 165, and Lemma 6.16, p. 166.

Problem 5-8(c) is an exercise in Lee; the fact that the geodesics of a bi-invariant metric through
the identity are the one-parameter subgroups is also standard in J. Milnor, *Curvatures of left
invariant metrics on Lie groups*, Adv. Math. 21 (1976), 293–329, and in J. Cheeger and D. G. Ebin,
*Comparison Theorems in Riemannian Geometry*, North-Holland, 1975 (not checked against the text).
-/

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace LieGroupExponential.Literature

/-- **Literature axiom, imported temporarily because the result is classical.**

For a Lie group whose metric is the Riemannian distance of a smooth bi-invariant Riemannian metric,
the Lie group exponential is radially isometric near `0`: `dist (exp v) 1 = ‖v‖` for `v` in a ball
of `T₁G` (Riemannian norm), and left and right translations preserve the distance.

Reference (checked against the text): J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed.,
GTM 176, Springer, 2018: Proposition 2.51, Problem 5-8(c), Theorem 6.9, Proposition 6.11,
Corollaries 6.12 and 6.13, and the definition of the injectivity radius.  The module docstring
gives page numbers, how the results combine, and why each hypothesis is needed. -/
axiom dist_expE_eq_norm_of_biInvariant
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    (G : Type*) [MetricSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
    [RiemannianBundle (fun x : G => TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : G => TangentSpace I x)]
    [IsRiemannianManifold I G]
    (hleft : ∀ (g x : G) (v w : TangentSpace I x),
      inner ℝ (mfderiv I I (fun y => g * y) x v) (mfderiv I I (fun y => g * y) x w) = -- totalisation-audit: allow left translation is smooth, so mfderiv is its genuine differential
        inner ℝ v w)
    (hright : ∀ (g x : G) (v w : TangentSpace I x),
      inner ℝ (mfderiv I I (fun y => y * g) x v) (mfderiv I I (fun y => y * g) x w) = -- totalisation-audit: allow right translation is smooth, so mfderiv is its genuine differential
        inner ℝ v w) :
    (∃ ρ : ℝ, 0 < ρ ∧ ∀ v : TangentSpace I (1 : G), ‖v‖ < ρ → dist (expE I G v) 1 = ‖v‖) ∧
      (∀ g x y : G, dist (g * x) (g * y) = dist x y) ∧
      (∀ g x y : G, dist (x * g) (y * g) = dist x y)

/-- Regression check for the statement of the axiom: on `T₁G` the norm is the Riemannian one, not
definitionally the norm of the model space `E`. -/
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    (G : Type*) [MetricSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
    [RiemannianBundle (fun x : G => TangentSpace I x)] (_v : TangentSpace I (1 : G)) : True := by
  fail_if_success exact (rfl : ‖_v‖ = ‖(id _v : E)‖)
  trivial

end LieGroupExponential.Literature
