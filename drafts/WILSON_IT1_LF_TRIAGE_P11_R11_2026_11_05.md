# Packet 11 r11 Triage (LF §4(a)–(b) and #0.17)

Review: verification/isolated_reviewer/reviews/lf-p11-20261105-r11/review.md, on LF ff2822a40dff and table ede3cd24c7da.

## Verdict

r11 is a changed-lines round. It has no fatal, serious, or minor finding, so it is **clean** (first clean round). It has trivials t-i, t-j, and t-k and one out-of-scope point (#4.23's reference order). All are repaired. r12 is the full round.

## Repairs

| Finding | Lines | Repair |
|---|---|---|
| t-i | #4.454.18, #4.537 | "at least LM₁ wide in its own units, L ≥ 1 M₁-cubes", the unit of these lines' d. |
| t-j | #4.22.3-0, #A.11.1.2, #A.11.1.6-1 | The width pointers now cite #4.18-2-2 and #4.17 besides #4.24 and #4.27-0. |
| t-k | #4.317-0 | Names the layer h on Z, the ∂Z layers, and the earlier R-operation layers under #4.18-2-2. |
| out of scope | #4.23-0 | "[3, 5, 6] (PRT2, PBG, REG; VAR p.309)", checked against VAR p.309: [3] PRT2 (CMP 96), [5] PBG (CMP 99, 389), [6] REG (CMP 99, 75). |
| long lines | #4.22.3 into #4.22.3, #4.22.3-0, #4.22.3-1; #4.23 into #4.23, #4.23-0, #4.23-0-1, #4.23-1 | Text unchanged. #4.22-1-1-1's pointer to the layer widths now cites #4.22.3-0. The table's citations of #4.23 (the R₁ = 1 reading) and the LF's of #4.22.3 (the condition) still point at the right pieces. |

## Pre-check

- Directions and units: L ≥ 1 M₁-cubes is LM₁ in M₁ units. R′M′ < LM₁, so the added pointers support "≥ R′M′".
- Greps: the citations of #4.23 and #4.22.3 in the LF and the table were checked; there are no other uses.

## Repaired files

LF e6b4035819ae, labels 87c648204791 (rows 208, multiply defined 101, CR 0), table ede3cd24c7da unchanged.
