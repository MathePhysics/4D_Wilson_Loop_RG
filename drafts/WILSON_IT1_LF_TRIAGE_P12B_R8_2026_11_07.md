# Triage of p12b r8 (lf-p12b-20261106-r8, 7 Nov 2026)

**Verdict.** Clean: no fatal, serious, or minor findings, and two trivia. The referee confirms that all r7 findings (m1, t1–t3) and the 2τ → 4τ count are repaired. This was a full round, so it is the first clean round of part 12b; r9 must be a second clean full round.

**Coverage caveat (the referee's own).** The referee re-read in the print LFR I pp.184–201, LFR II pp.358 and 378, CRE pp.244–245 and 264–266, and REG p.87. For the steps resting on VAR, CMP98, REG pp.77–83, and the other LFR II and CRE pages (marked † in the review), it checked against the argument's quotations and the r7 review's quotations instead. The r7 referee had opened most of those pages (VAR pp.278–279, 301, 308; CMP98 p.19; REG pp.75, 77–83, 87; LFR II pp.356–358, 363–368, 378–381, 390–391) and found them correct. The r9 provenance note asks that every cited page be opened.

## Repairs (all in place)

| Finding | Words at stake | Repair |
|---|---|---|
| t1, #3.64 | "so (1.3) and (1.4) are on their plateaus" | Now "(1.3), and (1.4) for j + 1 < k, are on their plateaus; at j + 1 = k (1.4) stays as χ_k(Ω_k^{∼4}) (p.184 l.14–15)", checked against the corrected file l.13–15. |
| t2, #3.93–#3.94 | "At complex backgrounds, d(s) − d(1) …" | #3.94 now opens "At real and at complex backgrounds". #3.93 now says that #3.94–#3.94-1 bound d(1 + κ_s)/d(1) − 1. At real backgrounds the form's lower bound is (1.9) itself. |
| non-finding, #3.76 | "for M ≥ (dL + 4)M₂ (p.245 l.37–38)" | Now "(one instance of M "much larger than M₂", p.245 l.37–38)". The line went over 600 characters, so it is split at "By CRE (3.2)–(3.5)" into #3.76.1. |
| non-finding, #3.94-1 | the factor abs(Λ^{(k)}) | Kept: it is the union bound over the bonds b of the shell, and it is correct. |

## Pre-check of r9 (lf-p12b-20261106-r9)
- **Changed tags (gate).** 5: #3.64, #3.76, #3.76.1, #3.93, and #3.94.
- **Changed lines.** I re-read each one. #3.64 was checked against LFR I p.184 (corrected file l.12–17). #3.93–#3.95 read consistently at both kinds of background.
- **Consumers.** #3.84-1 cites "(as in #3.76)" for the distance bound, which stays in #3.76. The spec's ranges "#3.76–#3.76-1" cover #3.76.1.
- **Line lengths.** All lines of the part are ≤ 610 characters (#3.85.1 is the longest).
- **Definition check.** 0 conflicts.
- **Size.** 24,924 characters (r8: 24,741).
- **Pins.** LF cdf81e25ac5a (labels 3b0a810050ae), table 1e392e405632.
- **Status.** Launched on the user's go (7 Nov).
