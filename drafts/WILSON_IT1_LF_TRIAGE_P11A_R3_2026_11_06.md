# Packet 11a r3 Triage (LF #0.17 and #4.1–#4.9-3)

Review: verification/isolated_reviewer/reviews/lf-p11a-20261106-r3/review.md (full round of part 11a; the rerun of r2, which the system stopped at its disclosure for low memory), on LF 733a94dbf091, labels 6fdee887f47a, and table e02c753f1f9d.

## Verdict

r3 has no fatal or serious finding, one minor finding, m-1, and three trivial points. So it is **not clean**. r1's M-1, t-1, and t-2 are resolved, and the earlier m-1, t-a, t-b, and t-e remain resolved after the condensation and the split.

## Repairs

| Finding | Lines | Repair |
|---|---|---|
| m-1 | #4.7-1-0 | "Neither uses the width of the layer j" now reads "Neither uses the width of the layer j when it is the top layer": below the top, #4.7-1-3-1 uses that width to keep □̃ off Ω_{j+1}. |
| t (Ũ before its tag) | #4.5-2-1 | "So Ũ = MU″^B" now reads "So the blocked configuration Ũ = MU″^B of #4.7". |
| t (#4.7-1-2 at LM′) | #4.7-1-4-3-2 | "#4.7-1-2 at M = LM′ ≤ M(ε₁), #4.7-3-1" now reads "#4.7-1-2 with LM′ in place of M′, and LM′ ≤ M(ε₁) by #4.7-3-1". |
| t (6c₀^d loose) | #4.9-1-1 | No change: the reviewer finds the constant valid, and it is Bałaban's printed form of (2.58). |

## Pre-check

- **m-1.** BP #4.7-1-2 uses only the layer j + 1's width; BP #4.7-1-3-1 uses the layer j's width R′M′ only for □̃ ∩ Ω_{j+1} = ∅, vacuous at the top. Below the top the width is ≥ LM₁ = (R′ + 1)M′ (#4.10-1).
- **Lines.** Three substitutions, each matched once before and once after; no line grows past 600 characters beyond the two already recorded. CR 0; no duplicate tags; every citation resolves.

## Repaired files

LF 218183a287fc, table e02c753f1f9d, labels 4b2d2037cc39.
