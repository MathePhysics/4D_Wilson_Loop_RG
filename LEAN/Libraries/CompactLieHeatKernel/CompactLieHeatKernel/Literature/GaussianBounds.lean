import CompactLieHeatKernel.AnalyticBridge
import Mathlib.Geometry.Manifold.Riemannian.Basic

/-!
# Literature axioms: small-time Gaussian bounds for the heat kernel of a compact Lie group

**This file contains two axioms.  They are imported temporarily from the literature because the
results are classical; they are not proved in Lean.**  The root module `CompactLieHeatKernel` does
not import this file, so `import CompactLieHeatKernel` stays axiom-free.  Every declaration that
depends on them shows `CompactLieHeatKernel.Literature.heatKernel_gaussian_lower` or
`CompactLieHeatKernel.Literature.heatKernel_gaussian_upper` under `#print axioms`.  The ledger is
`LITERATURE_AXIOMS.md` at the library root.

## Setting

`G` is a compact connected Lie group modelled without boundary on a finite-dimensional inner
product space `E`, and `μ` is its normalised Haar measure.  The Lie algebra carries the inner
product of `E` through the chart at the identity, and `leftMetric` is its left translate to every
tangent space.  The tangent spaces also carry a Riemannian bundle structure (`RiemannianBundle`,
`IsContMDiffRiemannianBundle`) whose inner product is `leftMetric` (`hmetric`), and the
metric-space structure of `G` is the Riemannian distance of that metric (`IsRiemannianManifold`:
`dist x y` is the infimum of the lengths of `C^1` paths from `x` to `y`).

`B` is an arbitrary `HeatSemigroupKernelBridge`: a self-adjoint Markov semigroup on `L²(G, μ)` whose
generator agrees with `½Δ_G` on smooth functions, where `Δ_G = ∑ᵢ XᵢXᵢ` over a `leftMetric`
orthonormal basis of left-invariant vector fields, with a smooth kernel that represents the
semigroup on continuous functions.  On a compact, hence unimodular, group `Δ_G` is the
Laplace–Beltrami operator of `leftMetric` (Liao 2018, Theorem 3.21 and Proposition 3.22, p. 95), and
the self-adjoint generator is unique (Grigor'yan 2009, Theorem 11.5, p. 301).  So
`B.kernel.density t` is the heat kernel of `∂_t − ½Δ_G` with respect to `μ`:
`B.kernel.density t x y = vol(G) · p_M(t, x, y)`, where `p_M` is the heat kernel with respect to the
Riemannian volume, whose total mass is `vol(G)`.  The axioms are stated for every bridge, which is
true because the heat kernel is unique.  `n = finrank ℝ E = dim G`.

## Statements

* `heatKernel_gaussian_lower`: there is `c > 0` with
  `c t^{-n/2} exp(−d(x, y)²/(2t)) ≤ k_t(x, y)` for all `0 < t < 1` and all `x, y`.
* `heatKernel_gaussian_upper`: there are `C, t₀ > 0` with
  `k_t(x, y) ≤ C (1 + d(x, y)²/t)^{n/2} t^{-n/2} exp(−d(x, y)²/(2t))` for all `0 < t ≤ t₀` and all
  `x, y`.

Together they give (eq:heat-gaussian-slack) of the manuscript: for every slack `0 < δ < 1`,
`c t^{-n/2} e^{−d²/(2(1−δ)t)} ≤ k_t ≤ C_δ t^{-n/2} e^{−d²/(2(1+δ)t)}` at small times, since
`(1 + u)^{n/2} e^{−u/2} ≤ C_δ e^{−u/(2(1+δ))}` for `u ≥ 0`.

## Why the statements are published theorems

* **Lower bound.**  E. P. Hsu, *Stochastic Analysis on Manifolds*, Graduate Studies in Mathematics
  38, American Mathematical Society, 2002, Theorem 5.3.4, p. 141: on a compact Riemannian manifold
  of dimension `d` there are `C₁, C₂ > 0` such that for all `(t, x, y) ∈ (0, 1) × M × M`,
  `C₁ t^{-d/2} e^{−d(x,y)²/2t} ≤ p_M(t, x, y) ≤ C₂ t^{-(2d−1)/2} e^{−d(x,y)²/2t}`.
  Hsu's heat operator is `∂_t − ½Δ_M` and `p_M` is taken with respect to the Riemannian volume
  (§4.1, p. 102), so the time convention is that of the bridge and only the constant changes:
  `c = vol(G) C₁`.  Only the lower half is imported.
* **Upper bound.**  A. Grigor'yan, *Heat Kernel and Analysis on Manifolds*, AMS/IP Studies in
  Advanced Mathematics 47, American Mathematical Society, 2009, Corollary 15.15, p. 406: on any
  weighted manifold there is a continuous function `r(x) > 0` such that for all `x, y` and
  `t ≥ t₀ > 0`,
  `p_t(x, y) ≤ C (1 + ρ²/t)^{n/2} exp(−ρ²/(4t) − λ(t − t₀))
    / (min(t₀, r(x)²) min(t₀, r(y)²))^{n/4}`,
  with `ρ = d(x, y)`, `λ = λ_min(M) ≥ 0` and `C = C(n)`.  Take the Riemannian volume as the weight,
  so that `Δ_μ` is the Laplace–Beltrami operator (Definition 3.17 and §3.6, pp. 67–68).  On a
  compact manifold `r` has a positive minimum `r₀`; for `τ ≤ r₀²` put `t = t₀ = τ` to get
  `p_τ(x, y) ≤ C (1 + ρ²/τ)^{n/2} τ^{-n/2} e^{−ρ²/(4τ)}`.  Grigor'yan's semigroup is `e^{tΔ}`, so
  the kernel of `½Δ` at time `t` is `p_{t/2}`, and `1 + 2ρ²/t ≤ 2(1 + ρ²/t)`.  This gives the stated
  form with `t₀ = 2r₀²` and `C` multiplied by `vol(G) 2^n`.

Both books use the geodesic distance, the infimum of lengths of piecewise `C^1` curves.  That of
`IsRiemannianManifold` is the infimum over `C^1` paths, and the two agree: a piecewise `C^1` curve
can be reparametrised to a `C^1` path of the same length, by making it stop at the breakpoints.

## Why each hypothesis is needed

An axiom with a false instance would make Lean inconsistent, so each hypothesis is load-bearing:

* `IsRiemannianManifold I G`: without it `dist` is arbitrary.  For the metric `d/2`, which induces
  the same topology, the lower bound fails at fixed `x ≠ y` as `t → 0`.
* `hmetric`: the distance must be that of the metric whose Laplacian generates `B`.  For the metric
  `4 · leftMetric` distances double and the upper bound fails at fixed `x ≠ y` as `t → 0`.
* `IsContMDiffRiemannianBundle`: both books assume a smooth metric (here it also follows from
  `hmetric`, but it is kept to match the sources).
* `[CompactSpace G]`: both specialisations use compactness (Hsu's theorem is for compact `M`;
  the minimum of `r` is positive on a compact set).
* `[ConnectedSpace G]`, `[BorelSpace G]`, `[I.Boundaryless]`, `[FiniteDimensional ℝ E]`: those of
  `nonempty_heatSemigroupKernelBridge`; for a bridge to exist the density must be strictly positive
  and measurable.
* `hAd`: not needed for the bounds, which hold for any compact Riemannian manifold, but a bridge
  (whose kernel is right invariant) exists only for a bi-invariant metric; it is kept so that the
  hypotheses are those of `nonempty_heatSemigroupKernelBridge`.

## Remark

Hsu's upper bound has the weaker prefactor `t^{-(2d−1)/2}`.  Hsu's Theorem 5.1.1 (p. 130) and
Corollary 5.3.5 (p. 142) sharpen it near the diagonal, but Theorem 5.1.1 is only sketched there.
The upper bound is therefore taken from Grigor'yan, whose proof is complete.  Li, *Geometric
Analysis*, Cambridge Studies in Advanced Mathematics 134, CUP, 2012, Theorem 13.4, p. 139, gives
another proof of the upper bound, under a lower Ricci bound, which also holds on a compact
manifold.
-/

noncomputable section

open MeasureTheory Bundle
open scoped Manifold ContDiff NNReal

namespace CompactLieHeatKernel.Literature

/-- **Literature axiom, imported temporarily because the result is classical.**

Small-time Gaussian **lower** bound for the heat kernel of `½Δ_G` on a compact connected Lie
group, for the Riemannian distance of the left-invariant metric: `c t^{-n/2} e^{-d²/(2t)} ≤ k_t`
for `0 < t < 1`.

Reference (checked against the text): E. P. Hsu, *Stochastic Analysis on Manifolds*, GSM 38,
AMS, 2002, Theorem 5.3.4, p. 141 (lower half), with the convention of §4.1, p. 102.  The module
docstring gives the specialisation and why each hypothesis is needed. -/
axiom heatKernel_gaussian_lower
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    (G : Type*) [MetricSpace G] [ChartedSpace H G] [MeasurableSpace G] [BorelSpace G]
    [CompactSpace G] [ConnectedSpace G] [Group G] [LieGroup I ∞ G]
    [RiemannianBundle (fun x : G => TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : G => TangentSpace I x)]
    [IsRiemannianManifold I G]
    (μ : Measure G) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
    (hAd : IsAdInvariantInnerProduct (I := I) (G := G))
    (hmetric : ∀ (g : G) (v w : TangentSpace I g), inner ℝ v w = leftMetric (I := I) g v w)
    (B : HeatSemigroupKernelBridge (I := I) (G := G) (μ := μ)) :
    ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ≥0, 0 < t → t < 1 → ∀ x y : G,
      c * (t : ℝ) ^ (-((Module.finrank ℝ E : ℝ) / 2)) * -- totalisation-audit: allow the denominators 2 and 2t are positive (t > 0 is a hypothesis)
          Real.exp (-(dist x y ^ 2 / (2 * (t : ℝ)))) ≤ -- totalisation-audit: allow the denominators 2 and 2t are positive (t > 0 is a hypothesis)
        B.kernel.density t x y

/-- **Literature axiom, imported temporarily because the result is classical.**

Small-time Gaussian **upper** bound for the heat kernel of `½Δ_G` on a compact connected Lie
group, for the Riemannian distance of the left-invariant metric:
`k_t ≤ C (1 + d²/t)^{n/2} t^{-n/2} e^{-d²/(2t)}` for `0 < t ≤ t₀`.

Reference (checked against the text): A. Grigor'yan, *Heat Kernel and Analysis on Manifolds*,
AMS/IP Stud. Adv. Math. 47, AMS, 2009, Corollary 15.15, p. 406, specialised to a compact manifold
with `t = t₀` and rescaled from `e^{tΔ}` to `e^{t½Δ}`.  The module docstring gives the
specialisation and why each hypothesis is needed. -/
axiom heatKernel_gaussian_upper
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    (G : Type*) [MetricSpace G] [ChartedSpace H G] [MeasurableSpace G] [BorelSpace G]
    [CompactSpace G] [ConnectedSpace G] [Group G] [LieGroup I ∞ G]
    [RiemannianBundle (fun x : G => TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : G => TangentSpace I x)]
    [IsRiemannianManifold I G]
    (μ : Measure G) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
    (hAd : IsAdInvariantInnerProduct (I := I) (G := G))
    (hmetric : ∀ (g : G) (v w : TangentSpace I g), inner ℝ v w = leftMetric (I := I) g v w)
    (B : HeatSemigroupKernelBridge (I := I) (G := G) (μ := μ)) :
    ∃ C t₀ : ℝ, 0 < C ∧ 0 < t₀ ∧ ∀ t : ℝ≥0, 0 < t → (t : ℝ) ≤ t₀ → ∀ x y : G,
      B.kernel.density t x y ≤
        C * (1 + dist x y ^ 2 / (t : ℝ)) ^ ((Module.finrank ℝ E : ℝ) / 2) * -- totalisation-audit: allow the denominators 2 and t are positive (t > 0 is a hypothesis)
          (t : ℝ) ^ (-((Module.finrank ℝ E : ℝ) / 2)) * -- totalisation-audit: allow the denominators 2 and 2t are positive (t > 0 is a hypothesis)
            Real.exp (-(dist x y ^ 2 / (2 * (t : ℝ)))) -- totalisation-audit: allow the denominators 2 and 2t are positive (t > 0 is a hypothesis)

/-- Regression check for the statement of the axioms: on a tangent space the inner product is the
Riemannian one, not definitionally the inner product of the model space `E`, so `hmetric` is a
genuine hypothesis. -/
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    (G : Type*) [MetricSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
    [RiemannianBundle (fun x : G => TangentSpace I x)] (_v : TangentSpace I (1 : G)) : True := by
  fail_if_success exact (rfl : inner ℝ _v _v = inner ℝ (id _v : E) (id _v : E))
  trivial

end CompactLieHeatKernel.Literature
