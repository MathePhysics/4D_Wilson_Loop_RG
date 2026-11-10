# Packet 11 r21 Triage (LF §4(a)–(b) and #0.17)

Review: verification/isolated_reviewer/reviews/lf-p11-20261105-r21/review.md (changed lines), on LF f7d2cf3872b9, labels 7b8c355c75b3, and table b562b85c8322.

## Verdict

r21 has no fatal, serious, or minor finding, so it is **clean**. It resolves r20's m-1 and t-1 to t-4. The trivial t-a is repaired. r22 is a full round; packet 11 closes if it is clean.

## Repairs

| Finding | Lines | Repair |
|---|---|---|
| t-a | #4.537 | The counts are in units of d: each crossed layer is ≥ LM₁ ≥ 1 units of d, and the crossing of the layer k₀ + 1 is ≥ 8LMR_{k₀+2} ≥ 8MR_k/M₁ units of d. |

## Pre-check

- **Correctness.** The length 8MR_{k₀+2}a_{k₀+2} at the spacing a_{k₀+1} is 8LMR_{k₀+2} units. 8LMR_{k₀+2} ≥ 8MR_k ≥ 8MR_k/M₁ by CRE (2.9) and M₁ ≥ 1. The chain d(p, Λ) ≥ max(k − m − 1, 8MR_k/M₁) is unchanged.
- **Every use.** #4.454.18 cites the max only, which is unchanged.
- **Lines.** Same-length edits in #4.537; CR 0.

## Repaired files

LF d1de5b46e7af, table b562b85c8322 (unchanged), labels d77b22572463.
