# Status

Checked on 2026-09-21 against Mathlib `8d52ea9a145a9255c4d301c0d1a1b8bf6e59305a` with
`leanprover/lean4:v4.34.0-rc2`.

## Build

| File | Lines | Result |
|---|---|---|
| `SchwarzTheorem/IteratedFDeriv.lean` | 230 | compiles, no errors, no warnings |
| `SchwarzTheorem.lean` (root) | 3 | compiles, no errors, no warnings |

* `IteratedFDeriv.lean` was compiled from the workspace root
  `Projects/FiniteVolumeYM2Phi42` with `lake env lean <file>`.
* The root file and a downstream `import SchwarzTheorem` test were compiled against scratch
  `.olean` files. These were produced with `lake env lean --root=<library> -o <scratch>`, and
  nothing was written to the library or to the workspace.
* `lake build` was not run, as instructed.
* Both files are Lean modules (`module` / `public import` / `public section`), as in current
  Mathlib.

## Gates

* No `sorry`, `admit`, `native_decide` or `set_option`.
* The longest line has 98 characters, counted as Unicode code points. There is no trailing
  whitespace.
* Every public theorem has a docstring. The module docstring has `## Main results` and
  `## Implementation notes`.

## Axioms

`#print axioms` was run in a scratch copy for every public declaration:

* `fderiv_domDomCongr_apply`
* `iteratedFDeriv_add_two_apply_left`
* `ContDiffAt.iteratedFDeriv_comp_perm_of_minSmoothness_le`
* `ContDiffAt.domDomCongr_iteratedFDeriv_of_minSmoothness_le`
* `ContDiff.iteratedFDeriv_comp_perm_of_minSmoothness_le`
* `ContDiff.domDomCongr_iteratedFDeriv_of_minSmoothness_le`
* `ContDiffWithinAt.domDomCongr_iteratedFDerivWithin_of_minSmoothness_le`
* `ContDiffWithinAt.iteratedFDerivWithin_comp_perm_of_minSmoothness_le`
* `ContDiffAt.iteratedFDeriv_comp_perm_of_omega`

Each depends only on `propext`, `Classical.choice` and `Quot.sound`. The private auxiliary
`iteratedFDeriv_comp_perm_aux` is covered transitively, through the main theorem.

The same scratch file also checks these usage cases:

* over `ℝ`, `C^k` with `by simp`;
* over any `[IsRCLikeNormedField 𝕜]`, `ContDiff 𝕜 n f` with `k ≤ n`;
* within a set over `ℝ`;
* the analytic corollary has the statement of Mathlib's `ContDiffAt.iteratedFDeriv_comp_perm`,
  checked by `rfl` between the two proofs.

## Totalisation audit

`Audit-Totalisations.ps1` was run on a scratch copy of both `.lean` files. It reports "no
unapproved textual hazards found". Three lines carry an allowance, on the flagged line itself.
All three are raw `fderiv` in the statements of the helper lemmas.

* Lines 69–70, `fderiv_domDomCongr_apply` ("isometric reindexing"). The identity holds for the
  total `fderiv` without any differentiability hypothesis. `domDomCongr` is a linear isometric
  equivalence, so both sides vanish together when `g` is not differentiable.
* Line 78, `iteratedFDeriv_add_two_apply_left` ("true by definition"). It unfolds the definition
  of `iteratedFDeriv` and holds for every `f`.

The main theorems mention only `iteratedFDeriv` and `iteratedFDerivWithin`, under `ContDiff`
hypotheses.

## Not done

* **The `Within` version does not generalise Mathlib's analytic `Within` lemma.** It requires
  `x ∈ closure (interior s)`, as the order-two lemma `ContDiffWithinAt.isSymmSndFDerivWithinAt`
  does. Mathlib's analytic `ContDiffWithinAt.iteratedFDerivWithin_comp_perm` does not. At a
  point, `ContDiffAt.iteratedFDeriv_comp_perm_of_omega` does recover Mathlib's statement.
* **There is no `ContDiffOn` / `iteratedFDerivWithin` version on a whole set.** It would be an
  immediate corollary of the `Within` theorem. It was not requested.
* **There is no Mathlib copyright header.** Mathlib requires
  `Copyright (c) <year> <author>` and `Authors:`. The author's name was not available, so it
  must be added before a PR.
* **Naming.** The `_of_minSmoothness_le` suffix only avoids clashing with Mathlib's existing
  `ContDiffAt.iteratedFDeriv_comp_perm`. See `README.md` for the rename intended upstream.

## Fragility for upstreaming

These dependencies are sound, but could break or need adjusting when Mathlib moves:

* **`LinearIsometryEquiv.comp_fderiv` in `iteratedFDeriv_add_two_apply_left`.** It is called
  with named arguments `(𝕜 := 𝕜) (E := …) (F := …) (G := …)`. Without them, unification fails
  between the `SeminormedAddCommGroup` instances in the statement of
  `continuousMultilinearCurryLeftEquiv` and the `NormedAddCommGroup.toSeminormedAddCommGroup`
  path that `comp_fderiv` expects. The named arguments depend on the variable names in
  `Mathlib/Analysis/Calculus/FDeriv/Equiv.lean`.
* **Definitional unfolding (`rfl`).**
  * `iteratedFDeriv_add_two_apply_left` relies on `iteratedFDeriv_succ_apply_left` and
    `iteratedFDeriv_succ_eq_comp_left` being `rfl`, and on `continuousMultilinearCurryLeftEquiv`
    applying by definition.
  * The `swap 0 1` case closes by `rfl`, by computing `swap 0 1` on `Fin (m + 2)`.
* **Recently renamed API.**
  * `eventuallyEqSet_univ` and the `…EventuallyEqSet` names (deprecations dated 2026-08-14).
  * `exist_minSmoothness_le_ne_infty`, a technical lemma that Mathlib could restate.
  * `Set.mem_setOf_eq` is deprecated in this Mathlib in favour of `Set.mem_ofPred_eq`, so the
    code avoids both.
* **Stable ingredients.** `ContDiffAt.isSymmSndFDerivAt`, `minSmoothness_add`,
  `minSmoothness_monotone`, `ContDiffAt.iteratedFDeriv_right`, `ContDiffAt.eventually`,
  `Equiv.Perm.mclosure_swap_castSucc_succ`, `ContinuousMultilinearMap.domDomCongrₗᵢ` and
  `ContDiffWithinAt.contDiffOn'`.
