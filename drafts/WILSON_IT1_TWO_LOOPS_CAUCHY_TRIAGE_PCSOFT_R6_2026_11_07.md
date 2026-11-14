# Triage of pc-soft r6 (7 Nov 2026)

Review: verification\isolated_reviewer\reviews\pc-soft-20261107-r6\review.md, read in full.

## Verdict

CLEAN, and a full round: no fatal, serious, or minor findings; one trivial pin. r5 and r6 are two consecutive clean rounds, the second a full one, so **the pc-soft part (#6.16–#6.16.5, #167-1–#167-1-1, #167-8, #130.12.1, #212–#212-1, #910, #920) is DONE.**

The referee confirmed that r5's five trivial points are resolved. It re-derived these and found them correct:
- the band X_x and its set;
- the gauge t_x with REG Lemma 1 and CMP98 (53), giving 9d²κ_x;
- the locality τ^x(c) ≤ (1+β₀)²L²τ^d(y);
- q^d and a* ≤ (2B₃C^d + 1)s^X, uniformly in X, p, and k.

It found no volume or scale dependence, no circularity, and no SU(N)-specific fact.

## Repairs

| Point | Where | Repair |
| --- | --- | --- |
| A bond with one end in Λ_l belongs to Λ_l by VAR's convention at p.277 l.17, not l.21 alone | #6.16.3-5-0-1 | The pin reads "(p.277 l.17, l.21)". l.17 was checked: "We identify domains Ω_j with sets of bonds … with at least one end-point belonging to Ω_j". This is bookkeeping and needs no round. |

## Standing qualification

The referee notes, as not a finding, that (2.37) in each factor domain's collar is established at the own index. This is R-mJ §7's reading, labelled "inferred, not printed" in #6.16.3-2-1-1, #6.16.5, #167-8, and the claim. The printed (2.37) there would need a further factor L^{−(min(p,m)−j)}. The reading of 𝐁_p(X)'s collar index is the one D2.7 and R-mJ use; it is recorded, not open.

## SHAs

TL 3880cb811b25 (labels b74c687b4bb8); PC 04cd2db746a7; LF ce6207d4b3e5 (labels eb0744201b11); table 1e392e405632; D2.7 4070b2971733.

pc-rstep r29, pc-links-a r1, and pc-links-b r1 are re-pinned to TL 3880cb811b25 and LF ce6207d4b3e5.
