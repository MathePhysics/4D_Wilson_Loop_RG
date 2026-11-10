# Packet 11a r7 Triage (LF #0.17 and #4.1–#4.9-3)

Review: verification/isolated_reviewer/reviews/lf-p11a-20261106-r7/review.md (full round of part 11a), on LF 9ee9725548ae, labels 76a33fb2e599, and table e02c753f1f9d. The run used the config directory .claude-IF; r6b used .claude-Main. Both reviewers report the same automatically supplied AGENTS.md context, as r5 did.

## Verdict

r7 has no fatal, serious, or minor finding, so it is **clean**. r6b's t-1 and t-2 are resolved, and all earlier repairs were rechecked in place. r6b (full) and r7 (full) are two consecutive clean rounds, the second full, so **part 11a is done**. The two trivial points are repaired below by rewording the existing sentences.

## Repairs

| Finding | Lines | Repair |
|---|---|---|
| t-1 | #4.7-00-1 | "the argument of #4.7-1-4-2–#4.7-1-4-2-1 bounds it directly" now reads "the argument of #4.7-1-4-2–#4.7-1-4-2-1, linear in the cube's side as PBG (3.35)–(3.36) ask, bounds it directly". To keep the line under 600 characters, "the cubes are those of run A's layers, Ũ being on run A's lattice" now reads "the cubes are run A's, Ũ being on its lattice". |
| t-2 | #4.7-00 | The condition on □̃ now reads "lies in the bottom domain of the set and, for a cube of the index j ≥ 1, in Ω_{j−1} (REG p.098 l.18–19), under REG's L^{−1}RM > 2dR₁M₁ (BP #4.24-2), which Bałaban's sets meet as printed and the joins at R′ = LK_{M′} − 1 > 2dL (#4.24)". |
| Observation (PBG p.397 l.29, "(2.36) in [4]") | none | Not a finding. #4.9-0 cites PRT2 (2.46), as TRANSCRIPTION_FINDINGS records. |

## Pre-check

- **t-1.** In the complete axial gauge on a cube of side s·a_0, a_0|A| ≤ (d − 1)s(π/2)ε₁. This is #4.7-1-4-2's bound with 2M′ replaced by s, and the differences of order m ≤ 2 stay within 2^m times it. So the bound is linear in the side, as PBG (3.35)–(3.36) require.
- **t-2.** REG p.098 l.18–19 reads "We assume that RM is bigger than R₁M₁, for example L^{−1}RM > 2dR₁M₁, thus we have □̃ ⊂ Ω_{k−1}". With R₁M₁ = M′ (#4.23) and the joins' separation R′M′ (#4.24), the condition becomes R′ > 2dL. That holds, since R′ = LK_{M′} − 1 and K_{M′} ≥ 12d + 1 (#4.22-0). 𝐁″_k and 𝐁 are Bałaban's own sets, and REG's condition is his assumption on them. 𝐁_{1.70} is a join, with collar layers of width ≥ M₁a_m (#4.5-2).
- **Consumers.** #4.7-2-0 cites #4.7-00–#4.7-00-1, and its statement is unchanged. No other line cites either tag.
- **Lines.** #4.7-00 has 486 characters and #4.7-00-1 has 597. CR 0; every citation resolves.

## Repaired files

LF dface007550b, table e02c753f1f9d, labels ebed65a74a3e.
