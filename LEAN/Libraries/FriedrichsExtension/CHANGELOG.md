## v0.17

- Incremented the project version to `0.17.0`.
- Recorded the user's confirmation that **v0.16 compiles in full**, including the local
  totalisation audit layer.
- Added the separate `TotalisationSafety` package as a Lake path dependency at
  `../TotalisationSafety`.
- Added `import TotalisationSafety` at the package API boundary and in
  `FriedrichsExtension.TotalisationAudit`.
- Kept all substantive Friedrichs mathematical modules byte-for-byte unchanged from v0.16.
- Retained `FriedrichsExtension.TotalisationAudit` only for Friedrichs-specific positivity,
  injectivity and density certificates.
- Removed the duplicated generic checker, allowlist, safe-build wrappers, CI audit workflow and
  generic policy/report files from FriedrichsExtension; these belong to the separate reusable
  library.
- The integration intentionally uses only the public root module `TotalisationSafety`, not internal
  `Basic`/`Partial`/`Series` modules.

## v0.16

- Incremented project version to `0.16.0`.
- Recorded the user's confirmation that **v0.15 compiles in full**.
- Kept every v0.15 mathematical theorem module byte-for-byte unchanged.
- Added `FriedrichsExtension/TotalisationAudit.lean` with formal positivity, injectivity and density certificates guarding all currently approved totalised operations.
- Added `scripts/check_totalisations.py`, which strips Lean comments/literals and rejects unaudited uses of division/reciprocal, `LinearPMap.inverse`, unbounded adjoints, `Real.sqrt`, and other high-risk default APIs.
- Added an explicit audited allowlist tying each approved occurrence to a formal guard theorem and rationale.
- Added Windows and Unix safe-build wrappers plus GitHub CI enforcement.
- Added `TOTALISATION_POLICY.md` documenting the no-silent-totalisation policy and review procedure.
- Verified the checker negatively by temporarily inserting `1 / 0`; the audit failed as intended, and the source was restored.
- No `axiom`, `sorry`, or `admit` was introduced.

## v0.15

- Incremented project version to `0.15.0`.
- Recorded the v0.14 compiler run, which reached `FriedrichsTheorem.lean` and exposed six proof-elaboration failures.
- Repaired all six reported failures without changing theorem statements or mathematical content.
- Only `FriedrichsTheorem.lean` changed among Lean modules relative to v0.14.
- No `axiom`, `sorry`, or `admit` was introduced.

## v0.14

- Incremented project version to `0.14.0`.
- Recorded the user's confirmation that **v0.13 compiles in full** in the pinned environment.
- Added `FriedrichsExtension/FriedrichsTheorem.lean`; all v0.13 Lean source files are unchanged.
- Proved the completion-level coercivity estimate for the energy embedding.
- Defined the closed unshifted Friedrichs form on the completed energy space.
- Proved the form agrees with the original operator form on the core, the core is dense, the form is
  jointly continuous, and it is the unique jointly continuous extension of the core form.
- Defined the ambient form domain as `range J` and identified it algebraically with the energy space.
- Added the closed-form representer relation and proved uniqueness of representing vectors.
- Proved exact equivalence between membership in the Friedrichs-operator domain and existence of a
  closed-form representer, plus the corresponding intrinsic operator uniqueness/maximality theorem.
- Proved the sharp inherited lower bound `A.lowerBound` for both the closed form and the operator.
- Constructed the canonical continuous linear equivalence between energy completions associated with
  any two admissible shifts, from explicit two-sided norm comparison estimates on the core.
- Proved that this equivalence intertwines the ambient embeddings and preserves the unshifted closed
  form exactly.
- Proved shift-invariance of form representability, equality of the ambient form domains, and
  independence of the Friedrichs extension from the auxiliary shift.
- Added the shift-free `canonicalFriedrichsExtension`, based on the canonical shift
  `1 - A.lowerBound`, together with self-adjointness, extension, lower-bound, domain and intrinsic
  uniqueness theorems.
- Added packaged shifted and canonical Friedrichs extension theorems.
- No `axiom`, `sorry`, or `admit` was introduced.

## v0.13

- Incremented the project version to `0.13.0`.
- Replaced the final failed rewrite in `friedrichsExtension_apply` by an explicit `change` to the
  `LinearPMap.vadd` representation and `LinearPMap.vadd_apply`.
- The user subsequently confirmed that v0.13 compiles in full.

## Earlier versions

See the previous version archives for the detailed v0.1--v0.12 compiler-repair history.
