# Literature axioms

Results that are classical but not yet proved in Lean are imported **temporarily** as axioms.  They
live only in `LieGroupExponential/Literature/`, which the root module `LieGroupExponential` does not
import, so `import LieGroupExponential` stays axiom-free.  A downstream declaration depends on a
literature axiom exactly when `#print axioms` shows it by name.

The rules are those of `../CompactLieHeatKernel/LITERATURE_AXIOMS.md`:

1. the axiom states a published theorem with the same hypotheses, with the references in its
   docstring;
2. it is a single `Prop`, never a data constant with separately postulated properties, so it cannot
   contradict itself;
3. any hypothesis the literature needs but the Lean structure does not force is added explicitly,
   since a false instance of an axiom makes Lean inconsistent.

## Ledger

| Axiom | File | Supplies | Consumers |
|---|---|---|---|
| `LieGroupExponential.Literature.exists_isDifferential` | `LieGroupExponential/Literature/ContinuousRepresentation.lean` | the differential of a continuous orthogonal representation of a closed matrix group | `ContinuousOrthogonalAction.toSmooth` only; no downstream consumer yet |
| `LieGroupExponential.Literature.dist_expE_eq_norm_of_biInvariant` | `LieGroupExponential/Literature/IsometricExponential.lean` | for a bi-invariant Riemannian metric, `dist (exp v) 1 = ‖v‖` near `0` and translations are isometries | `FiniteVolumeYM2Phi42/Section04AtlasLiterature.lean` (the tree atlas of Section 4) |

### `exists_isDifferential`

**Statement.**  Let `G` be a closed subgroup of `GL (Fin n) ℝ` and let `ρ` be a
`ContinuousOrthogonalAction` of `G` on a finite-dimensional real inner product space `V`: linear
isometries `ρ g` with `ρ 1 = 1`, `ρ (g h) = ρ g ∘ ρ h`, and `g ↦ ρ g` continuous into the
operator-norm topology.  Then there is a real-linear `L : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] (V →L[ℝ] V)`
with `ρ g = exp (L X)` whenever `X` lies in `matrixLieAlgebra G` and `g = exp X`.

**What is proved without it.**  `SmoothOrthogonalAction` carries the differential as data, and its
API does not use the axiom:

* `iso_exp_smul`: `ρ (exp (t X)) = exp (t • L X)`;
* `hasDerivAt_iso_exp`: `L X` is the derivative of `t ↦ ρ (exp (t X))` at `0`, so `L` is
  determined on the Lie algebra;
* `norm_exp_smul_diff_le`: `‖exp (t • L X)‖ ≤ 1`.

Only `ContinuousOrthogonalAction.toSmooth`, which builds the smooth structure from a continuous
action, depends on the axiom.

**Why the hypotheses are Hall's.**
* *Closed subgroup of `GL (Fin n) ℝ`.*  `GL(n, ℝ)` is closed in `GL(n, ℂ)`, since a limit of real
  matrices is real.  So a closed subgroup of `GL(n, ℝ)` is a matrix Lie group in Hall's sense
  (Definition 1.4).  Mathlib topologises `GL (Fin n) ℝ` as units, through `u ↦ (u, u⁻¹)`.
  Inversion is continuous on invertible matrices, so this agrees with the subspace topology from
  the matrices, which Hall uses.
* *Lie algebra.*  `matrixLieAlgebra G` is Hall's Definition 3.18.  A complex `X` with `e^{tX}` real
  for every `t` is real, so nothing is lost by taking real matrices.
* *Representation.*  A continuous homomorphism into the invertible operators of a
  finite-dimensional real space is a real representation (Definitions 1.18 and 4.1).  Hall
  requires `dim V ≥ 1`.  For `V = 0` the statement holds trivially, since every operator on the
  zero space is zero.
* *`L` on all matrices.*  Hall's `π` is real-linear on `𝔤`, which is a real subspace (Theorem 3.20).
  A linear map on a subspace extends linearly to the whole space.

**Why a literature axiom.**  The project's `OrthogonalAction` is an abstract group action with no
smooth structure, and mathlib has no `LieGroup` instance on `SU(N)` or `SO(N)` (see `STATUS.md`).
Proving the result needs the closed-subgroup theorem and the logarithm on a neighbourhood of the
identity of a matrix group (Hall, Theorem 3.42 and Corollaries 3.44–3.50), which is out of scope
for this release.

**Reference.**  B. C. Hall, *Lie Groups, Lie Algebras, and Representations: An Elementary
Introduction*, 2nd ed., Graduate Texts in Mathematics 222, Springer, 2015,
doi:10.1007/978-3-319-13467-3.  The copy used is the eBook, ISBN 978-3-319-13467-3.  Page numbers
are those printed in the book.

**Checked against the source (2026-09-18).**

| Ingredient | Source | Checked |
|---|---|---|
| matrix Lie group = closed subgroup of `GL(n; ℂ)`, topology inherited from `M_n(ℂ)` | Hall, Definition 1.4, p. 4 | yes |
| Lie group homomorphism = continuous group homomorphism | Hall, Definition 1.18, p. 22 | yes |
| Lie algebra `{X : e^{tX} ∈ G ∀ t ∈ ℝ}` | Hall, Definition 3.18, p. 56 | yes |
| the Lie algebra is a real subspace closed under the bracket | Hall, Theorem 3.20, p. 56 | yes |
| `Φ(e^X) = e^{φ(X)}` with `φ` unique and real-linear; `φ(X) = d/dt Φ(e^{tX})` at `0` | Hall, Theorem 3.28, p. 60 | yes |
| continuous homomorphisms of matrix Lie groups are smooth | Hall, Corollary 3.50, p. 72 | yes |
| finite-dimensional real representation = Lie group homomorphism into `GL(V)` | Hall, Definition 4.1, p. 77 | yes |
| `Π(e^X) = e^{π(X)}` for a representation, `π(X) = d/dt Π(e^{tX})` at `0` | Hall, Proposition 4.4, p. 79 | yes |

**Axiom report** (`#print axioms`, 2026-09-18).  `exists_isDifferential` and `toSmooth` depend on
`propext`, `Classical.choice`, `Quot.sound` and `exists_isDifferential`.  `iso_exp_smul`,
`norm_exp_smul_diff_le`, `hasDerivAt_iso_exp` and `smul_mem_matrixLieAlgebra` depend only on
`propext`, `Classical.choice` and `Quot.sound`.  The root module's declarations are unaffected.

### `dist_expE_eq_norm_of_biInvariant`

**Statement.**  Let `G` be a Lie group of class `C^∞` modelled without boundary on a
finite-dimensional real inner product space `E`, with a smooth Riemannian metric on its tangent
spaces (`RiemannianBundle`, `IsContMDiffRiemannianBundle`) whose distance is the metric of `G`
(`IsRiemannianManifold`: `dist` is the infimum of the lengths of `C^1` paths).  Suppose the
differentials of all left and all right translations are linear isometries of the tangent spaces.
Then

* there is `ρ > 0` with `dist (expE I G v) 1 = ‖v‖` for every `v : T₁G` with `‖v‖ < ρ`, the norm
  being the Riemannian norm at the identity;
* `dist (g * x) (g * y) = dist x y` and `dist (x * g) (y * g) = dist x y`.

**Why the hypotheses.**
* `IsRiemannianManifold`: without it the metric is arbitrary.  A snowflaked metric `d^{1/2}` is
  still bi-invariant and induces the same topology, but `dist (exp v) 1` is then of order
  `‖v‖^{1/2}`.
* Left and right invariance: for a merely left-invariant metric the geodesics through `1` are in
  general not one-parameter subgroups, and right translations are not isometries.
* Smoothness of the metric, no boundary and finite dimension: Lee's setting.
* Compactness and connectedness are not assumed.  A metric space satisfying `IsRiemannianManifold`
  has finite Riemannian distances, so it is connected, and the statement is local.

**Pitfall recorded in the file.**  The norm must be applied to a term of type `TangentSpace I 1`.
An ascription `(ξ : TangentSpace I 1)` of `ξ : E` keeps the inferred type `E`, so it would silently
use the norm of `E`.  The statement would then be false whenever the metric at `1` is not the inner
product of `E`, which would make Lean inconsistent.  The axiom therefore quantifies over
`v : TangentSpace I 1`, and an `example` in the file checks that this norm is not definitionally the
norm of `E`.

**Why at this level.**  The axiom asserts only the radial distance along the Lie group exponential
and the isometry of translations.  Everything else the Section 4 atlas needs is proved from the
library: the logarithm on the target of `expChart`, its continuity and smoothness, the smooth face
word (`CentredChart.ofExp_smoothFace`) and the face bounds
(`CentredChart.ofExp_nonempty_faceBounds`).  The downstream module derives the isometric chart
`IsometricChart (CentredChart.ofExp I G)` in about thirty lines.

**Reference.**  J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Graduate Texts in
Mathematics 176, Springer, 2018, doi:10.1007/978-3-319-91755-9.  The copy used is the eBook, ISBN
978-3-319-91755-9.  Page numbers are those printed in the book.

**Checked against the source (2026-09-19).**

| Ingredient | Source | Checked |
|---|---|---|
| Riemannian distance = infimum of lengths of admissible curves | Lee, p. 36 | yes |
| isometries preserve the Riemannian distance | Lee, Proposition 2.51, p. 37 | yes |
| bi-invariant metrics ↔ `Ad`-invariant inner products; compact groups have one | Lee, Proposition 3.12, p. 69; Theorem 3.14 and Corollary 3.15, p. 70 | yes |
| for a bi-invariant metric the geodesics from `e` are the one-parameter subgroups, so `exp_e` is the Lie exponential | Lee, Problem 5-8(c), p. 147 | yes (an exercise with hints (a)–(b)) |
| Gauss lemma | Lee, Theorem 6.9, p. 159 | yes |
| radial geodesics in a geodesic ball are minimising | Lee, Proposition 6.11, p. 161 | yes |
| in a geodesic ball the radial distance is the Riemannian distance; geodesic balls are metric balls | Lee, Corollaries 6.12 and 6.13, p. 162 | yes |
| injectivity radius; positive on compact manifolds | Lee, p. 165; Lemma 6.16, p. 166 | yes |

Lee's distance uses admissible (piecewise regular) curves, Mathlib's `riemannianEDist` `C^1`
paths.  Corollary 6.12 holds for both: its lower bound, from the Gauss lemma, applies to every
piecewise `C^1` curve, and the upper bound is attained by a smooth radial geodesic.  Proposition
2.51 holds for both, since an isometric diffeomorphism maps `C^1` paths to `C^1` paths of the same
length.  Problem 5-8(c) is an exercise in Lee; the same fact is standard in J. Milnor, *Curvatures
of left invariant metrics on Lie groups*, Adv. Math. 21 (1976), 293–329, and in J. Cheeger and D.
G. Ebin, *Comparison Theorems in Riemannian Geometry*, North-Holland, 1975 (not checked against the
text).

**Axiom report** (`#print axioms`, 2026-09-19).  The eight consumers in
`FiniteVolumeYM2Phi42/Section04AtlasLiterature.lean` depend on `propext`, `Classical.choice`,
`Quot.sound` and `dist_expE_eq_norm_of_biInvariant`, and on no other axiom.  The root module's
declarations are unaffected.
