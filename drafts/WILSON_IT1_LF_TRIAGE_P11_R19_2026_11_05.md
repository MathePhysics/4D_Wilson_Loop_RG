# Packet 11 r19 Triage (LF §4(a)–(b) and #0.17)

Review: verification/isolated_reviewer/reviews/lf-p11-20261105-r19/review.md (changed lines), on LF 5bac61c02c1f, labels b8de63b42e23, and table 39fe437e0921.

## Verdict

r19 has no fatal, serious, or minor finding, so it is **clean**. It resolves r18's m-1, m-2, and t-1 to t-3. Its trivials t-A to t-C are repaired. r20 is a full round; packet 11 closes if it is clean.

## Repairs

| Finding | Lines | Repair |
|---|---|---|
| t-A | new #4.41-2-2; #4.41-2, #4.41-3 | The evaluation points are stated: w at a plaquette's centre and at a bond's midpoint, with the Euclidean gradient as in #4.41-1-4. The bond's midpoint is ½ε from the plaquette's centre, and a fine plaquette's centre is within ε/√2 of its coarse plaquette's centre. So each difference is ≤ ε times the gradient bound. |
| t-B | #4.338 | W is the least width of the crossed layers ("W the least crossed width"). |
| t-C | #4.41-1-3-2 | On Z, CRE (2.3). Off Z, LFR I's convention that Z_j stands for Z_j ∩ Z (p.177 l.33–35). |

## Pre-check

- **Sources read.** LFR I p.177 l.33–35: "For simplicity we denote intersections of the regions Z_j with Z by Z_j also".
- **Arithmetic.**
  - The midpoint of an edge of a square of side ε is ε/2 from the centre.
  - The centres of an L × L subdivision lie within (ε/2 − ε/(2L))√2 < ε/√2 of the centre.
- **Every use.**
  - #4.41-2 and #4.41-3 now cite #4.41-2-2.
  - The constants 12, 48, and 96 are unchanged.
- **Lines.** The new and changed lines are under 600 characters (#4.338 at 596, after shortening its frozen-layer parenthesis); CR 0; no duplicate tags.

## Repaired files

LF 5fe659239484, table 39fe437e0921 (unchanged), labels caf325444449.
