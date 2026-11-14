# Packet 11 r12 Triage (LF §4(a)–(b) and #0.17)

Review: verification/isolated_reviewer/reviews/lf-p11-20261105-r12/review.md (full round), on LF e6b4035819ae and table ede3cd24c7da.

## Verdict

r12 has one minor finding (m-1) and trivials t-1 to t-5, so it is **not clean**. The clean count restarts. r13 is a changed-lines round, and r14 is a full round.

## Repairs

| Finding | Lines | Repair |
|---|---|---|
| m-1 | new #4.12-2, #4.12-2-1, #4.12-2-2; #4.13, #4.14, #4.14-0, #4.14-2 | The joins' domains are taken within Z by the note's convention (R-Z) (#4.172–#4.172-1), which LFR II p.371 l.26–27 forces. #4.12-2-1 derives that ∂Ω and the strip S lie in Z at ℓ¹-distance ≥ 5LMR_{h+1} − 2dM₁ > M₁ from Z^c. #4.12-2-2 derives Ω″^∼_{h+1} ∩ Z ⊂ Ω″_h with margin 2LMR_{h+1} > 2dM₁, and that off Z, 𝐁₁ is 𝐁″_k and 𝐁₂ is void. #4.13, #4.14, #4.14-0, and #4.14-2 now state the containment on Z and treat (Ω″_j)^c ∖ Z separately. |
| t-1 | #4.12-1 | "at least 2MR_j wide (CRE p.256 l.21–24)". |
| t-2 | #4.24 | "R₁M₁ is sufficiently big, so that", checked against VAR p.304 l.2 (corrected file). |
| t-3 | new #4.9-1-1; #4.18-2; #4.40.2-2 | These now name the layers of earlier R-operations and at ∂Z, at least LM₁ wide (#4.18-2-2). |
| t-4 | #4.537 | "Z is a union of components of Λ_k^c (LFR I p.177 l.17, l.33)". |
| t-5 | #4.21-1 | "at least one big block in B^j(Λ_j)", checked against PBG p.408 l.21. |

## Pre-check

- **Sources quoted.**
  - LFR I p.177: l.17 ("It is a union of connected components"), l.33–34, and l.41–42.
  - LFR II pp.370–371: (1.52), (1.53), and p.371 l.26 ("This configuration restricted to Z^c is equal to U_1").
  - CRE p.256 l.21–24; VAR p.304 l.2; PBG p.408 l.21.
- **(R-Z) already in the note.** The grep found #4.172–#4.172-1. #4.12-2 cites it rather than re-quoting.
- **The path argument.** A point just outside Z belongs to Λ_k, because Z is a union of components of Λ_k^c. Also Λ_k ⊂ Ω_k ⊂ Ω_{h+1}, and Z″_{h+1} ⊂ (Ω^{∼5}_{h+1})^c lies ≥ 5LMR_{h+1} from Ω_{h+1} in scale-h units.
- **Directions and units.** All widths are lower bounds. 5LMR_{h+1} − 2dM₁ > M₁ and 2LMR_{h+1} > 2dM₁ follow from M > L²M₁, R ≥ 1, and L ≥ 12d + 6.
- **Greps for other occurrences.** No other occurrence of "wider than 2MR", "a component of Λ_k^c", "one big block", or the unquoted VAR phrase. The other uses of Ω″^∼_{h+1} in §4(c)–(d) already use (R-Z).
- **Lines.** Every changed line is under 600 characters, except the pre-existing long lines #4.21-1, #4.24, and #4.537, which got one-word changes.

## Repaired files

LF 81b55840acbd, labels d356d8f6cba2 (multiply defined 101, CR 0), table ede3cd24c7da unchanged.
