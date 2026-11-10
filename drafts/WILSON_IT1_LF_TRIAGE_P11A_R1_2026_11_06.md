# Packet 11a r1 Triage (LF #0.17 and #4.1–#4.9-3)

Review: verification/isolated_reviewer/reviews/lf-p11a-20261105-r1/review.md (full round of part 11a), on LF ec27d1b32902, labels cf626884b711, and table 5c3dda77979a.

## Verdict

r1 has no fatal or serious finding, one minor finding, M-1, and two trivial findings, t-1 and t-2. So it is **not clean**. The prior findings m-1, t-a, t-b, and t-e are resolved.

## Repairs

| Finding | Lines | Repair |
|---|---|---|
| M-1 | #0.17, new #4.10-1 | #0.17 is one line: the printed widths are cited, and the others, every layer of 𝐁″_k below the top at least M wide and every layer of the joins below the top at least LM₁, are Bałaban proofs (#4.10-1), not yet reviewed. The width proofs (#4.11–#4.18-2-2) moved to balaban_proofs/BP_LAYER_WIDTHS.md; the LF keeps the statement #4.10-1. |
| t-1 | #4.5-1-0 | The index h + 1 is forced by ∂Z″_{h+2} lying in 𝐁″_k's layer h + 1, and (2.14)'s other hypotheses are cited from #4.12-2–#4.12-3, which name the unconstrained boundary on Ω's outer side, ∂Ω″_{h+2} for 𝐁_{1.70}. |
| t-2 | #4.7-1-4-3-2 | U″^B at a_1 on run B's layer 1 within run A's layer 1: run B's class cube of the index 1 with the parameter LM′ gives L^{1+p}B₃M′ε₁ times a_1^{−p}, within C₀^{ms} = 2L⁴C₀. |

## Pre-check

- **Discipline pass.** Every symbol of the part grepped against the table; restatements replaced by row citations (#T1.5, #T2.5, #T2.9, #T2.13, #T2.15, #T2.21, #T3.31, #T4.23, #T4.26, #T4.34, #T4.35). Roadmaps, restated facts, and pre-emptive asides deleted: #0.17-1–#0.17-2, #4.1's second sentence, #4.6's opening, #4.9-3's roadmap, five "(derived)" sub-heading labels.
- **Bałaban-proof split.** Re-derivations of Bałaban's work moved verbatim, tags kept, to balaban_proofs/ (five files, lower priority, not yet reviewed): the covering by VAR's class cubes (#4.7-1-1–#4.7-1-3-1, #4.7-1-5–#4.7-1-5-2-1), the widths (#4.11–#4.18-2-2), the theorems at the joins at the block size M′ (#4.19–#4.29), the kernel form of VAR Proposition 4 (#4.34–#4.36-3-1), and the profiles (#4.41-1-2–#4.41-1-4). The LF keeps the statements #4.7-1-0, #4.10-1, #4.10-2, #4.33-1, and #4.41-1-1-1.
- **Size.** Packet 11 was 89.3k characters at r1, 73.3k after the discipline pass, and 38.5k after the split. Lines over 600 characters: #4.7-1-4-3 (632) and #4.9-0 (615).
- **Citations.** Every citation of the LF resolves in the LF, the table, the cited notes, or balaban_proofs/; every #4.x citation in the five files resolves. CR 0; no duplicate tags.
- **Table.** #T4.35 re-pointed to #4.7-1-4-1–#4.7-1-4-2 and #4.7-1-4-3–#4.7-1-4-3-2; the edit was announced to the fork before it was made, and the SHAs were sent after.

## Repaired files

LF 733a94dbf091, table e02c753f1f9d, labels 6fdee887f47a.
