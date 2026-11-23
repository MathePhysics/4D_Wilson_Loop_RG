# Status: BakerCampbellHausdorff v0.4 (2026-10-08)

The library has sixteen modules. With the root file and `checks/Axioms.lean` it comes to 3,443
lines.

* Every module compiles without errors or warnings.
* The totalisation audit passes, with 116 reviewed markers.
* The 78 declarations in `checks/Axioms.lean` depend only on `propext`, `Classical.choice` and
  `Quot.sound`.

Everything was compiled module by module with `lean +leanprover/lean4:v4.34.0-rc2` against the
mathlib build of `FiniteVolumeYM2Phi42`. Nothing has been built with `lake` yet, because no host
project requires the library.

## Versions

* **v0.1: analytic BCH.** Nine modules: `ExpBounds`, `LogSeries`, `ExpLog`, `LogExp`,
  `AnalyticLog`, `ExpMulExpSeries`, `Theorem`, `GroupLaw` and `Product`.
* **v0.2: Lie-algebraic BCH.** Three new modules: `Operators`, `Dexp` and `Lie`. Also a new lemma
  `expProd_castSucc` in `Product`.
* **v0.3: explicit uniform constants and the principal term of `bchProd`.** Three new modules:
  `MulSeries`, `ExpProdSeries` and `Explicit`. They answer two requests from the project:
  * a coefficient bound with admissible `K`, `C` that are explicit and uniform (now `K = 1`,
    `C = 4` for `bch`, and `C = 2m`, or `2m‖L‖` after a chart, for `m` factors);
  * the first-order term `∑ᵢ (L A)ᵢ` of `bchProd ∘ L`.
* **v0.4: Taylor's formula for `exp` with integral remainder.** One new module, `ExpTaylor`, over
  `𝕂 = ℝ`, requested by `higgs23_lower_bound` (Bałaban, (Higgs)_{2,3} I (3.14)):
  `exp z = ∑_{m ≤ n} z^m / m! + z^{n+1} / (n+1)! · R_{n+1}(z)` with
  `R_{n+1}(z) = (n+1) ∫_0^1 (1-t)^n exp(t z) dt`, and `‖R_{n+1}(z)‖ ≤ 1` when `‖exp(t z)‖ ≤ 1` on
  `[0, 1]`. Written by the lead.

## Process

* **Written by the lead:** everything except the four modules below.
* **Written by background agents:** `ExpMulExpSeries` (v0.1), `Dexp` (v0.2), `MulSeries` and
  `ExpProdSeries` (v0.3). Each agent worked from a brief that fixed the definitions and theorem
  statements. The lead then reviewed the module.
* **Parallel development in v0.3:** `Explicit` was written while the agent built the product
  series; its `m`-fold part was drafted against the specified interface of `ExpProdSeries`.
* **Parallel development:** `Lie` was developed at the same time as `Dexp`. Its core lemma
  `log1p_mem_of_dexp` takes the derivative formula as a hypothesis, and the final theorems
  instantiate it with `hasFDerivAt_exp`.

The Lie-algebraic proof is analytic; see `README.md`. Its key point is that
`ad (log (e^W e^(t Y)))` preserves `𝔤` before `log (e^W e^(t Y)) ∈ 𝔤` is known. It is the
logarithm, taken in the operator algebra, of `e^(ad W) e^(t ad Y)`.

## Checks

* **Line length and endings.** No line in the v0.1–v0.3 modules is longer than 100 characters;
  `ExpTaylor` (v0.4) has longer lines. All files use LF endings.
* **Totalisation audit.** `Audit-Totalisations.ps1 -Path Libraries\BakerCampbellHausdorff` reports
  no unapproved hazards.
* **Name clashes.** The root `BakerCampbellHausdorff.lean` imports all sixteen modules and
  compiles.
* **Mathlib name overlap.** `BakerCampbellHausdorff.hasFDerivAt_exp` has the same short name as
  mathlib's root `hasFDerivAt_exp`, the version for commutative algebras. Refer to it with the
  full name after `open BakerCampbellHausdorff`.

## Possible next steps

1. **Wire the library into the project.** Add it as a path dependency of `FiniteVolumeYM2Phi42`
   and confirm `lake build BakerCampbellHausdorff`. Then do two things with it:
   * derive the `GeometricBound` hypothesis of `Section06VertexSuppressionModel` from
     `geometricBound_bchProdSeries_comp`, with the principal term from
     `bchProdSeries_comp_one_apply`;
   * place the plaquette logarithm in the gauge Lie algebra with `bchProd_mem_of_isScalarTower`.
2. **Sharper constants.** The majorant `1/(2 - e^(2z))` would improve `C = 4` to about `2.89`.
   The project does not need this, since only uniformity matters there.
3. **Algebraic route.** Dynkin's formula in the free Lie algebra, if a statement independent of
   the ambient algebra is needed.
