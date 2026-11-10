# Packet 11 r17 Triage (LF §4(a)–(b) and #0.17)

Review: verification/isolated_reviewer/reviews/lf-p11-20261105-r17/review.md (changed lines), on LF 941aa3d49cc0, labels a0d6f3509b45, and table 3a1f61afdbe0.

## Verdict

r17 has no fatal, serious, or minor finding, so it is **clean**. It resolves r16's m-1 to m-3 and t-1. The trivials t-1 and t-2 are repaired. r18 is a full round; packet 11 closes if it is clean.

## Repairs

| Finding | Lines | Repair |
|---|---|---|
| t-1 | #4.7-1-5-1 | The layer 0 takes Ω_{−1} := Ω_0 (T_η for 𝐁 and 𝐁″_k, Ω for a join). |
| t-2 | #4.7-1-5-2-1 | "if the layer j + 1 is the top one, Ω_{j+2} = ∅ and no width is needed". |

## Pre-check

- **Correctness.** Both repairs are wording only. Ω_0 = T_η for 𝐁 and 𝐁″_k is #4.7-1-4, and Ω_0 = Ω for a join is CRE p.256 l.60.
- **Every use.** No other line cites the wording.
- **Lines.** Both lines are under 600 characters; CR 0.

## Repaired files

LF 488d57f31aae, table 3a1f61afdbe0 (unchanged), labels 31c594f34c04.
