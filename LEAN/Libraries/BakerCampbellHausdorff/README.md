# BakerCampbellHausdorff v0.4

The Baker–Campbell–Hausdorff theorem in a Banach algebra, in analytic and in Lie-algebraic form,
on top of mathlib `8d52ea9a` (Lean `v4.34.0-rc2`). There are no `sorry`s, `admit`s, axioms or
option overrides, and no module produces a warning. The 78 declarations in `checks/Axioms.lean`
depend only on `propext`, `Classical.choice` and `Quot.sound`.

Setting: `𝔸` is a complete normed algebra over `𝕂 = ℝ` or `ℂ` (`[RCLike 𝕂] [NormedRing 𝔸]
[NormedAlgebra 𝕂 𝔸] [CompleteSpace 𝔸]`). The library does not assume `‖1‖ = 1`. The exponential
is mathlib's `NormedSpace.exp`.

* **Analytic form (v0.1).**
  1. Define `log (1 + u) = ∑ (-1)^(n+1) uⁿ / n` as a `FormalMultilinearSeries`.
  2. Set `bch 𝕂 X Y = log (exp X exp Y)`.
  3. Get analyticity by composing power series.
  4. Get the geometric coefficient bound from mathlib's radius API.

  The one step mathlib does not supply is `exp (log (1 + u)) = 1 + u`.
* **Lie-algebraic form (v0.2).** If `𝔤` is a closed real Lie subalgebra, then `bch X Y ∈ 𝔤` for
  small `X, Y ∈ 𝔤`. This extends to short products of exponentials. It follows that every
  homogeneous term of the BCH series lies in every closed Lie subalgebra containing `X` and `Y`.
  The proof is analytic: it uses the derivative of `exp`, which mathlib lacks for noncommutative
  algebras and which is proved here. It needs no free Lie algebras.
* **Explicit uniform constants (v0.3).** `‖bchSeries 𝕂 𝔸 n‖ ≤ 4ⁿ`. For `m` factors there is an
  explicit series `bchProdSeries 𝕂 𝔸 m` with `‖bchProdSeries 𝕂 𝔸 m n‖ ≤ (2m)ⁿ`, and after a
  chart `L` the bound is `(2m‖L‖)ⁿ`. The constants depend on nothing else: not on `𝔸`, `𝕂`, the
  arguments, a scale or a plaquette. Each series converges to its function on an explicit ball
  (`‖(X, Y)‖ < 1/4`, resp. `‖X‖ < 1/(2m)`), with an explicit geometric tail. The first-order
  term of `bchProd` after a chart is `∑ᵢ (L A)ᵢ`.

## Results

All names are in namespace `BakerCampbellHausdorff`, except the `_root_` extensions such as
`HasFPowerSeriesAt.log1p_sub_one`.

### Analytic form

| Statement | Lean |
|---|---|
| `log (1 + u)`: coefficients of norm `≤ 1/n`, radius `≥ 1`, analytic on `‖u‖ < 1` | `logSeries`, `log1p`, `one_le_radius_logSeries`, `hasFPowerSeriesOnBall_log1p`, `analyticOnNhd_log1p` |
| `exp (log (1 + u)) = 1 + u` for `‖u‖ < 1` | `exp_log1p` |
| `log (exp Z) = Z` for `‖Z‖ < 1/4`; `exp` is injective on that ball | `log1p_exp_sub_one`, `exp_injOn`, `eq_log1p_of_exp_eq` |
| If `F` has power series `p` at `x` and `F x = 1`, then `log F` has power series `(logSeries 𝕂 𝔸).comp p`, with geometrically bounded coefficients, and `exp (log F) = F` near `x` | `HasFPowerSeriesAt.log1p_sub_one`, `HasFPowerSeriesAt.exists_geometricBound_log`, `AnalyticAt.log1p_sub_one`, `ContinuousAt.eventually_exp_log1p_sub_one` |
| **BCH**: `exp (bch 𝕂 X Y) = exp X exp Y` for `‖X‖ + ‖Y‖ < log 2` | `exp_bch`, `exp_bch_of_norm_lt` |
| Uniqueness: a logarithm of `exp X exp Y` of norm `< 1/4` equals `bch 𝕂 X Y` | `eq_bch_of_exp_eq` |
| `bchSeries 𝕂 𝔸` is the power series of `bch` at `0`, and `‖bchSeries 𝕂 𝔸 n‖ ≤ K Cⁿ` | `hasFPowerSeriesAt_bch`, `bchSeries_radius_pos`, `exists_geometricBound_bchSeries` |
| `bch` is analytic on `‖X‖ + ‖Y‖ < log 2` | `analyticAt_bch`, `analyticOnNhd_bch` |
| `bch 𝕂 X Y = X + Y + ½[X, Y] + O(‖(X, Y)‖³)` | `bchSeries_one_apply`, `bchSeries_two_apply_diag`, `hasFDerivAt_bch`, `bch_sub_isBigO` |
| `‖bch 𝕂 X Y‖ ≤ -log (2 - e^(‖X‖+‖Y‖))`; `≤ (3/2)(‖X‖ + ‖Y‖)` for `‖X‖ + ‖Y‖ ≤ 1/6` | `norm_bch_le`, `norm_bch_le_mul` |
| Local group law: commuting case, inverse, associativity | `bch_eq_add_of_commute`, `bch_zero_left`, `bch_zero_right`, `bch_neg_right`, `bch_neg_neg`, `bch_assoc` |
| `m`-fold products `log (exp X₀ ⋯ exp Xₘ₋₁)`, also composed with a linear chart | `bchProd`, `exp_bchProd`, `eq_bchProd_of_exp_eq`, `analyticOnNhd_bchProd`, `exists_hasFPowerSeriesAt_bchProd`, `exists_hasFPowerSeriesAt_bchProd_comp` |
| Geometric bounds `‖p n‖ ≤ K Cⁿ`: equivalent to positive radius, preserved by linear maps on either side | `GeometricBound`, `FormalMultilinearSeries.exists_geometricBound`, `GeometricBound.le_radius`, `GeometricBound.radius_pos`, `GeometricBound.compContinuousLinearMap`, `GeometricBound.compFormalMultilinearSeries` |

### Derivative of `exp` and Lie-algebraic form

| Statement | Lean |
|---|---|
| `exp (ad a) x = e^a x e^(-a)` in the operator algebra `𝔸 →L[𝕂] 𝔸` | `mulLeft`, `mulRight`, `ad`, `exp_ad`, `exp_ad_apply` |
| **Derivative of `exp`** (noncommutative): `D exp (Z) = e^Z · (1 - e^(-ad Z)) / ad Z` | `expSubOneDiv`, `hasDerivAt_exp_add_smul`, `hasFDerivAt_exp` |
| **Lie-algebraic BCH**: `𝔤` a closed real Lie subalgebra, `X, Y ∈ 𝔤`, `‖X‖ + ‖Y‖ < 1/10` ⟹ `bch ℝ X Y ∈ 𝔤` | `bch_mem` |
| The same for products: `Xᵢ ∈ 𝔤`, `∑ ‖Xᵢ‖ < 1/10` ⟹ `log (e^X₀ ⋯ e^Xₘ₋₁) ∈ 𝔤` | `bchProd_mem` |
| The same over `𝕂`, e.g. `𝔰𝔲(n) ⊆ Mₙ(ℂ)`: `bch ℂ X Y ∈ 𝔤` | `bch_mem_of_isScalarTower`, `bchProd_mem_of_isScalarTower`, `log1p_eq_log1p_real` |
| Every homogeneous BCH term at `X, Y ∈ 𝔤` lies in `𝔤` | `bchSeries_apply_diag_mem` |

### Explicit constants and the principal term

| Statement | Lean |
|---|---|
| If `‖P b‖ ≤ Mᵇ` for `b ≥ 1`, then `‖(logSeries 𝕂 𝔸).comp P n‖ ≤ (2 M)ⁿ` | `norm_logSeries_comp_le` |
| `‖bchSeries 𝕂 𝔸 n‖ ≤ 4ⁿ`, i.e. `GeometricBound (bchSeries 𝕂 𝔸) 1 4`; radius `≥ 1/4` | `norm_bchSeries_le`, `geometricBound_bchSeries`, `quarter_le_radius_bchSeries` |
| `bchSeries` converges to `bch` on `‖(X, Y)‖ < 1/4`, with tail `≤ (4‖v‖)ᴺ / (1 - 4‖v‖)` | `hasFPowerSeriesOnBall_bch`, `norm_bch_sub_partialSum_le` |
| Explicit power series of `exp X₀ ⋯ exp Xₘ₋₁` with `‖Pₙ‖ ≤ mⁿ/n!` and `P₁ X = ∑ᵢ Xᵢ` | `expProdSeries`, `hasFPowerSeriesOnBall_expProd`, `norm_expProdSeries_le`, `expProdSeries_one_apply` |
| `bchProdSeries 𝕂 𝔸 m` is the power series of `bchProd 𝕂`, with `‖·ₙ‖ ≤ (2m)ⁿ` (`GeometricBound … 1 (2m)`) | `bchProdSeries`, `hasFPowerSeriesAt_bchProdSeries`, `norm_bchProdSeries_le`, `geometricBound_bchProdSeries` |
| It converges to `bchProd` on `‖X‖ < 1/(2m)`, with tail `≤ (2m‖X‖)ᴺ / (1 - 2m‖X‖)` | `hasFPowerSeriesOnBall_bchProd`, `norm_bchProd_sub_partialSum_le` |
| First-order term `∑ᵢ Xᵢ`; `bchProd 𝕂 ![X, Y] = bch 𝕂 X Y` | `bchProdSeries_one_apply`, `bchProd_two` |
| Chart `L : E →L[𝕂] (Fin m → 𝔸)`: `‖(bchProdSeries ∘ L)ₙ‖ ≤ (2m‖L‖)ⁿ`, first-order term `∑ᵢ (L A)ᵢ`, `bchProd 𝕂 (L A) = ∑ᵢ (L A)ᵢ + O(‖A‖²)`, explicit tail | `norm_bchProdSeries_comp_le`, `geometricBound_bchProdSeries_comp`, `bchProdSeries_comp_one_apply`, `hasFDerivAt_bchProd_comp`, `bchProd_comp_sub_sum_isBigO`, `norm_bchProd_comp_sub_partialSum_le` |
| Cauchy product of algebra-valued power series, with explicit bounds | `mulConcat`, `mulSeries`, `HasFPowerSeriesOnBall.mulSeries`, `norm_mulSeries_le` |

## Modules

| Module | Content |
|---|---|
| `ExpBounds` | `exp (x + y) = exp x exp y` for commuting `x`, `y` over `𝕂`. Mathlib's version needs a `NormedAlgebra ℚ 𝔸` instance, which a `𝕂`-algebra does not provide. Also the bounds `‖exp x - 1‖ ≤ e^‖x‖ - 1`, `‖exp x - 1 - x‖ ≤ e^‖x‖ - 1 - ‖x‖` and `‖exp x exp y - 1‖ ≤ e^(‖x‖+‖y‖) - 1`, and the fact that `exp w = 1` with `‖w‖ < 1` gives `w = 0`. |
| `LogSeries` | `logCoeff`, `logSeries`, `log1p`: radius, analyticity, `HasSum`, commutation, norm bounds |
| `ExpLog` | `exp (log1p 𝕂 u) = 1 + u` |
| `LogExp` | `log1p 𝕂 (exp Z - 1) = Z` for `‖Z‖ < 1/4`, and uniqueness of small logarithms |
| `AnalyticLog` | `GeometricBound`; the logarithm of an analytic function near `1` |
| `ExpMulExpSeries` | the explicit power series of `(X, Y) ↦ exp X exp Y`, with infinite radius, obtained by a Cauchy product; its coefficients of order 0, 1 and 2 |
| `Theorem` | `bch`, `bchSeries`, the BCH theorem, low-order terms, the second coefficient of a composition `q.comp p` |
| `GroupLaw` | linear norm bound, inverse law, associativity |
| `Product` | `expProd`, `bchProd`: the `m`-fold version and its composition with a chart |
| `Operators` | `mulLeft`, `mulRight`, `ad` in `𝔸 →L[𝕂] 𝔸`; `exp (ad a) = Ad (e^a)`; `expSubOneDiv 𝕂 T = ∑ Tᵏ / (k + 1)!` |
| `Dexp` | the Fréchet derivative of `exp` |
| `Lie` | the operators preserving `𝔤`; the Lie-algebraic BCH theorem; the ℝ-to-𝕂 bridge; membership of the coefficients |
| `MulSeries` | the concatenation product of multilinear maps and the Cauchy product of power series |
| `ExpProdSeries` | the explicit power series of `expProd`, by recursion on `m` |
| `Explicit` | the composition bound; explicit constants, balls of convergence and tails for `bch` and `bchProd`; first-order term and principal part in a chart |
| `ExpTaylor` | (v0.4, `𝕂 = ℝ`) Taylor's formula `exp z = ∑_{m ≤ n} z^m / m! + z^{n+1} / (n+1)! · expRem n z` with `expRem n z = (n+1) ∫_0^1 (1-t)^n exp(t z) dt`, and `‖expRem n z‖ ≤ 1` when `‖exp(t z)‖ ≤ 1` on `[0, 1]` |

## Proof of `exp (log (1 + u)) = 1 + u`

Put `L t = log (1 + t u)` for `t ∈ 𝕂`, `‖t‖ < R = 2 / (1 + ‖u‖)`. Then `R > 1` and `R ‖u‖ < 1`.
All the values `L t` commute with each other.

1. Differentiating term by term (`hasDerivAt_tsum_of_isPreconnected`) gives
   `L' t = u ∑ (-t u)^k`. The geometric series then gives `L' t (1 + t u) = u`.
2. Because the `L t` commute, `exp (-L s) = exp (-L t) exp (L t - L s)`. With `D exp (0) = id`,
   this gives the derivative `-exp (-L t) L' t` of `t ↦ exp (-L t)`.
3. So `F t = exp (-L t) (1 + t u)` has derivative `0` on the ball. Hence `F 1 = F 0 = 1`, which
   gives the claim.

This avoids the commutative subalgebra generated by `u`. It only uses that the `L t` commute
(`Commute.log1p_right`).

## Proof of the Lie-algebraic form

**Setup.** Let `S` be the operators `T : 𝔸 →L[ℝ] 𝔸` with `T 𝔤 ⊆ 𝔤` (`preserving`). This is a
closed subalgebra. It contains `ad X` for `X ∈ 𝔤`, and it is closed under `exp`, `log1p`,
`expSubOneDiv` and Neumann series. Take `W, Y ∈ 𝔤` and `Z t = log (e^W e^(t Y))` for
`t ∈ [0, 1]`.

1. **`ad Z ∈ S`, without knowing `Z ∈ 𝔤`.** We have
   `e^(ad Z) = Ad (e^Z) = Ad (e^W) Ad (e^(t Y)) = e^(ad W) e^(ad (t Y))`, which lies in `S`.
   Since `‖ad Z‖ < 1/4`, the identity `log ∘ exp = id` of `LogExp`, applied in the Banach algebra
   `𝔸 →L[ℝ] 𝔸`, gives `ad Z = log (e^(ad Z)) ∈ S`.
2. **`Z' ∈ 𝔤`.** Differentiate `e^(Z t) = e^W e^(t Y)` using `hasFDerivAt_exp`. This gives
   `Φ Z' = Y` with `Φ = (1 - e^(-ad Z)) / ad Z ∈ S` and `‖1 - Φ‖ < 1`. The Neumann inverse of
   `Φ` lies in `S`, so `Z' ∈ 𝔤`.
3. **Conclusion.** Let `f` be a continuous functional vanishing on `𝔤`. Then `f ∘ Z` has
   derivative `0`, so `f (Z 1) = f (Z 0) = f W = 0`. By Hahn–Banach
   (`geometric_hahn_banach_point_closed`), `Z 1 ∈ 𝔤`.

`bch_mem` is this with `W = X`. `bchProd_mem` follows by induction on the number of factors, with
`W` the logarithm of all but the last factor. For `bchSeries_apply_diag_mem`, observe that
`s ↦ bch (s X) (s Y)` takes values in `𝔤` for small `s > 0`. Its `n`-th Taylor coefficient is
`lim_{s → 0⁺} s⁻ⁿ (f s - ∑_{k<n} sᵏ qₖ)`, a limit of elements of `𝔤`.

The derivative of `exp` (`Dexp`) comes from term-by-term differentiation of
`exp (Z + h V) = ∑ (Z + h V)ⁿ / n!`. The result is written with `L = mulLeft Z` and
`R = mulRight Z`, which commute. A Cauchy product with the binomial identity
`∑_{k ≤ p} C(p+1, k) aᵏ d^(p-k) = ∑_{i ≤ p} aⁱ (a + d)^(p-i)` (for commuting `a`, `d`) then
identifies it with `e^L · expSubOneDiv (R - L)`.

## Formulation notes

* **Scalar field argument.** `log1p 𝕂 u`, `bch 𝕂 X Y` and `bchProd 𝕂 X` take `𝕂` explicitly, as
  mathlib's `exp 𝕂` used to. Their coefficients are rational, and `log1p_eq_log1p_real` shows that
  the value does not depend on `𝕂`.
* **Lie subalgebras.** In this mathlib, `LieRing.ofAssociativeRing` is only a local instance. So a
  Lie subalgebra is a `Submodule ℝ 𝔸` with the hypothesis `∀ x y ∈ 𝔤, x * y - y * x ∈ 𝔤`, plus
  `IsClosed`. It is an `ℝ`-submodule, so real forms such as `𝔰𝔲(n) ⊆ Mₙ(ℂ)` are covered. A
  finite-dimensional subspace is automatically closed.
* **"Lie polynomial".** `bchSeries_apply_diag_mem` puts the degree-`n` BCH term in every closed
  Lie subalgebra containing `X` and `Y`. In a finite-dimensional `𝔸`, such as `Mₙ(ℂ)`, the Lie
  subalgebra generated by `X` and `Y` is closed. So there the term is a linear combination of
  iterated brackets of `X` and `Y`. In general it is a limit of such combinations. A statement in
  the free Lie algebra is not formalised.
* **Junk values.** `bch 𝕂 X Y` is defined for all `X`, `Y`. Outside `‖exp X exp Y - 1‖ < 1` the
  defining series is not summable, and the `tsum` returns `0`. Every theorem assumes smallness.
* **Radii and constants.** The constants `log 2`, `1/4`, `1/6`, `1/10`, `C = 4` and `C = 2m`
  were chosen because they are easy to prove, not because they are sharp.
  * The bound `(2M)ⁿ` counts all `2ⁿ⁻¹` compositions of `n` and discards the factors `1/k` and
    `1/b!`.
  * Keeping those factors instead gives the majorant `1/(2 - e^(2z))` for `bch`, which would
    improve `C = 4` to about `2/log 2 ≈ 2.89`.
  * The existential `exists_geometricBound_bchSeries` from v0.1 is superseded by
    `geometricBound_bchSeries`.
* **Multilinear coefficients.** Only the diagonal values of a power series on `𝔸 × 𝔸` are
  canonical. `bchSeries 𝕂 𝔸` is the formal composition of `logSeries` with `expMulExpSeries`.

## Not formalised

* **Dynkin's explicit formula**, and the Lie-polynomial statement in the free Lie algebra. Both
  need the algebraic route (free Lie algebras and the universal enveloping algebra).
* `bch` on an abstract Lie group, other than through an ambient Banach algebra.

## Build

The library has no mathlib checkout of its own. Build it as a Lake path dependency of a host
project that has one. For `Projects/FiniteVolumeYM2Phi42`, add to its `lakefile.toml`

```toml
[[require]]
name = "BakerCampbellHausdorff"
path = "../../Libraries/BakerCampbellHausdorff"
```

and run `lake build BakerCampbellHausdorff`. `higgs23_lower_bound` imports `ExpTaylor` (compiled with its
own `tools/leanc.sh`, not with `lake`). v0.3 was
compiled module by module with `lean +leanprover/lean4:v4.34.0-rc2` against the mathlib build of
`FiniteVolumeYM2Phi42`, not with `lake build`; v0.4 against the same mathlib revision `8d52ea9a`
in `Projects/balaban`. Each module takes about 8–10 s.

## Relation to FiniteVolumeYM2Phi42

`Section06VertexSuppressionModel` takes the uniform BCH coefficient bound `GeometricBound P K C`
as a hypothesis. Its docstring gives the reason: "Mathlib has no BCH series". This library's
`GeometricBound` over `𝕂 = ℝ` has the same three fields (`K_nonneg`, `C_pos`, `norm_le`), so
`⟨h.K_nonneg, h.C_pos, h.norm_le⟩` converts one into the other.

Take a plaquette holonomy `U(A) = exp (X₁) ⋯ exp (X₄)` with each link variable `Xᵢ = ι (ℓᵢ A)`
linear in the chart variable `A`, where `ι` embeds the Lie algebra coordinates into the matrix
algebra. Then `U(A) = expProd (L A)` for the continuous linear map
`L = ContinuousLinearMap.pi fun i => ι ∘L ℓᵢ`, and `P = (bchProdSeries ℝ 𝔸 4).compContinuousLinearMap L`
satisfies:

* **Power series:** `P` is the power series of `A ↦ log U(A)` at `0`
  (`hasFPowerSeriesAt_bchProd_comp`).
* **Uniform bound:** `‖P n‖ ≤ (8 ‖L‖)ⁿ` (`norm_bchProdSeries_comp_le`), so
  `GeometricBound P 1 (8 (‖L‖ + 1))` (`geometricBound_bchProdSeries_comp`). The constants depend
  only on `‖L‖`, so they are uniform over scales and plaquettes whenever `‖L‖` is.
* **Principal term:** `P 1 A = ∑ᵢ ι (ℓᵢ A)`, the sum of the link variables
  (`bchProdSeries_comp_one_apply`). Equivalently `log U(A) = ∑ᵢ ι (ℓᵢ A) + O(‖A‖²)`
  (`bchProd_comp_sub_sum_isBigO`).
* **Convergence:** for `8 ‖L A‖ < 1`, `P` converges to `log U(A)` with tail
  `(8 ‖L A‖)ᴺ / (1 - 8 ‖L A‖)` (`norm_bchProd_comp_sub_partialSum_le`).
* **Coordinates:** `GeometricBound.compFormalMultilinearSeries` transfers the bound through a
  linear map `π` to Lie algebra coordinates, with `K = ‖π‖`.
* **Lie algebra:** `bchProd_mem_of_isScalarTower` shows that `log U ∈ 𝔤` when `∑ ‖Xᵢ‖ < 1/10`.
  For example `𝔤 = 𝔰𝔲(N) ⊆ M_N(ℂ)`, which is closed because it is finite-dimensional.

The library's `GeometricBound` over `ℝ` has the same fields as the one in
`Section06VertexSuppressionModel`. What remains on the project side is to identify the
manuscript's `X_{p,s}` and the chart of `Section03LieChart` with this construction: the chart has
to be the exponential chart in the representation, and each link has to be the chart value of a
linear function of the tree-gauge variable.

## Policy

The totalisation audit of the sibling `TotalisationSafety` library passes on
`BakerCampbellHausdorff/`, with 100 reviewed `-- totalisation-audit: allow` markers:

* literal denominators such as `1 / 4`;
* `n !` in denominators;
* `Real.log 2`;
* `Real.log (1 - ‖u‖)` and `Real.log (2 - e^s)` with positive arguments;
* divisions by `R > 0`, `1 + ‖u‖ > 0`, `f b ≠ 0` and, in the tail bounds, `1 - C ‖y‖ > 0`;
* `tsum`s that unfold a definition or are proved summable.

The coefficients `logCoeff` are defined by cases, so they do not rely on `0⁻¹ = 0`. The Lie proof
obtains derivatives from `DifferentiableAt` witnesses instead of `fderiv`.
