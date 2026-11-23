# Totalisation-safety policy

Lean/mathlib intentionally assign values to several operations that are mathematically partial.  In
this project those fallback values are **not** accepted as mathematical semantics.  A theorem must
never become true merely because an undefined expression has been totalised to a default value.

The project therefore uses two independent checks.

## 1. Formal guard certificates

`FriedrichsExtension/TotalisationAudit.lean` contains the propositions which justify every current
use of a totalised operation.  At present these certify:

- `Real.sqrt (A.lowerBound + shift)` is applied to a strictly positive number before its reciprocal
  is used;
- every denominator in the change-of-shift estimate is strictly positive;
- the radicand in the change-of-shift comparison constant is nonnegative;
- the bounded resolvent has trivial kernel before `LinearPMap.inverse` is used;
- the shifted Friedrichs operator has dense domain before its `LinearPMap.adjoint` value is used;
- the unshifted Friedrichs extension has dense domain before its `LinearPMap.adjoint` value is used.

The last point matters because mathlib's `LinearPMap.adjoint` explicitly uses a junk-value branch
when the source domain is not dense.

## 2. Static source audit

Run

```text
python scripts/check_totalisations.py
```

(or `py -3 scripts/check_totalisations.py` on a standard Windows Python installation).

The checker strips Lean comments and literals, scans every `.lean` file in `FriedrichsExtension/`,
and rejects new occurrences of high-risk syntax/APIs.  The current policy watches, among other
things:

- `/`, `⁻¹`, `Inv.inv`, `Div.div`, `HDiv.hDiv`;
- `LinearPMap.inverse`;
- unbounded `.adjoint` uses in `FriedrichsOperator.lean`, and explicit `LinearPMap.adjoint`/`†`;
- `Real.sqrt`, `Real.log`;
- `Nat.div`, `Nat.mod`, `%`, and the corresponding integer division/modulus APIs;
- `ENNReal.toReal`;
- unsafe/default getters (`get!`, `getD`, `Option.get`);
- `default` / `Inhabited.default`;
- `Fin.ofNat` and `Matrix.inv`.

`TotalisationAudit.lean` itself is the trusted boundary and is not lexically scanned; its job is to
*prove* the domain conditions named by the allowlist.

The explicit allowlist is `scripts/totalisation_allowlist.json`.  Each entry records the exact
source line, category, multiplicity, mathematical rationale, and the formal guard declaration which
justifies it.  The checker also verifies that the named guard declaration exists.

### Adding a new use

Do **not** regenerate the allowlist from the source.  Instead:

1. Decide whether the operation can be reformulated with a genuine domain/subtype.  Prefer that.
2. If a totalised mathlib operation is unavoidable, prove the missing domain condition in
   `TotalisationAudit.lean` (nonzero/positive denominator, nonnegative radicand, injectivity,
   density, finiteness, etc.).
3. Add only the intended source occurrence to `totalisation_allowlist.json`, naming that guard and
   explaining why the fallback branch is unreachable.
4. Run the audit and the full Lean build.
5. Review the diff.  A changed or removed allowlisted line is deliberately treated as an audit
   failure until reviewed.

## Safe build wrappers

On Windows PowerShell:

```powershell
.\scripts\lake-safe.ps1 build
```

On Unix-like systems:

```sh
./scripts/lake-safe.sh build
```

Both run the totalisation audit before invoking Lake.  CI does the same.

## Scope and limitation

This mechanism protects the Friedrichs-extension source tree; it does not change Lean's kernel or
mathlib's global design.  It is intentionally conservative and should be extended whenever a new
class of totalised API becomes relevant.  The formal guard certificates are the decisive part: the
static checker prevents an accidental raw use from entering the project without an explicit review.
