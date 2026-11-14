# Packet 11 r10 Triage (LF §4(a)–(b) and #0.17)

Review: verification/isolated_reviewer/reviews/lf-p11-20261105-r10/review.md, on LF f7822366eb84 and table ede3cd24c7da.

## Verdict

r10 is a changed-lines round. r9's m-r and t-a to t-f are resolved. It has one minor finding, m-s: the r9 repair gave the frozen layers' width LM to layers that are not frozen. It also has trivials t-g and t-h, and one pre-existing point. It is not clean.

## Repairs

| Finding | Lines | Repair |
|---|---|---|
| m-s | #4.530-1 | Every crossed layer is at least LM₁ wide in its own units. CRE's layers are ≥ 2MR_j (CRE p.256 l.21–23); those of 𝐁″_k and of earlier R-operations are covered by #4.18-2-2; at the joins, by #4.17. So each is at least LM₁ ≥ 1 units of d, whose unit is the layer's spacing (PRT2 (2.46), #4.20). This also answers the reviewer's point on d's unit. |
| m-s | #4.530-1-1, #4.454.18, #4.537 | "at least LM₁ wide in its own units (#4.530-1)". Each use needs only one unit of d per crossed layer. |
| t-g | #4.27-0 | "would need RM below the layer width, which at the width LM allows only R < L". |
| t-h | #4.338 | "at least W wide". The later "since W > 8" is unchanged and holds for W ≥ LM₁. |
| pre-existing | new #4.317-0 | The middle layers are at least LMR_{j+1}a_j ≥ LM₁ε wide (#4.18-1), and the earlier R-operation layers at least LM₁ε (#4.18-2-2). #4.318 covers every W ≥ LM₁. |
| long lines | #4.27 split into #4.27 and #4.27-0; #4.530-1 into #4.530-1 and #4.530-1-0 | The citations of #4.27 for widths ≥ R′M′ (#4.22.3, #A.11.1.2, #A.11.1.6-1) now cite #4.27-0. Those for the device (#4.18-2-2, #A.11.1.1) cite #4.27–#4.27-0. |

## Pre-check

- Sources: CRE p.256 l.21–23 (domains of the j-th transformation, boundaries ≥ 2MR_j apart); #4.20 (the distance is PRT2 (2.46), in the block units of each layer).
- Directions and units: each width is a lower bound. LM₁ ≥ 1 in the layer's spacing, so every crossed layer gives at least one unit of d. 2MR_j ≥ 2M > LM₁. a_j ≥ ε for j ≥ 0.
- Greps: "LM wide", "LMε wide", and "W = LM" now occur only for LFR I's frozen layers (#0.17-1, #4.9-1, #4.17, #4.21-1 (PBG's own M, not the frozen layers), #4.27-0, #4.317, #4.338). I listed and updated every citation of #4.27 in the LF; no other note cites it.

## Repaired files

LF ff2822a40dff, labels 0fe27bd6216e (rows 208, multiply defined 101, CR 0), table ede3cd24c7da unchanged.
