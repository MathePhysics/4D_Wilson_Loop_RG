# Packet 11a r6b Triage (LF #0.17 and #4.1–#4.9-3)

Review: verification/isolated_reviewer/reviews/lf-p11a-20261106-r6b/review.md (full round of part 11a), on LF 27b8858fc692, labels f37e89c7f85d, and table e02c753f1f9d.

## Verdict

r6b has no fatal, serious, or minor finding, so it is **clean**: the first clean full round of 11a. r5's m-1, m-2, and t-1–t-5 are resolved. Two trivial points, t-1 and t-2, are repaired below. r7, a full round, is the second clean round needed.

## Repairs

| Finding | Lines | Repair |
|---|---|---|
| t-1 | #4.7-00, new #4.7-00-1, #4.7-2-0 | PBG (3.36) for Ũ is sourced per cube. Cubes whose REG cube □̃ lies in the bottom domain use REG Proposition 6 (#C9.8.4-2). For 𝐁_{1.70} the cubes are run A's, Ũ being on run A's lattice. □̃ extends 2R₁M₁a = 2M′a beyond its cube (REG p.098 l.13–19), and run A's layer m ≥ 1 lies at depth ≥ M₁a_m > 24M′a_m (K_{M′} ≥ 12d + 1, #4.22-0), so the remaining cubes are of the layer 0 within 24M′a_0 < M₁a_1 of ∂Ω, in T_{1.70}. There Ũ is the a_0-lift, bounded directly by #4.7-1-4-2–#4.7-1-4-2-1. #4.7-2-0 cites #4.7-00–#4.7-00-1. |
| t-2 | #4.7-1-4-1-2 | "Bałaban takes U_{k,Λ} as a base in this class" now reads "Bałaban's use of U_{k,Λ} as a minimal configuration (p.371 l.32–37) presupposes regular data, the mixed plaquettes at ∂Λ included (CRE p.256 l.43: …; inferred, not printed)". |
| Observation (#T3.25) | none | Not a finding. O(1)B₃²B₅M⁶ε_k is the data parameter of the background pairs (#4.281, ε_d at #4.284.12), a different quantity from (1.84)'s O(1)B₃B₅M⁶ε_k. #4.177 already uses C(M) ≥ O(1)B₃²B₅M⁶ + M₀, which contains #4.43's added bound. |

## Pre-check

- **t-1 home and consumers.** The source of Ũ's cube-gauge regularity is #4.7-00–#4.7-00-1. Its only citation is #4.7-2-0, which is updated. Ũ is defined once, at #4.5-2-1. T_{1.70} := Ω ∖ Ω^B_2 has width 2M₁a_1 (#4.5-2). The bottom-strip bound is #4.7-1-4-2.
- **t-2 source.** CRE p.256 l.43 (corrected file): "A regular configuration V on 𝐁 determines the minimal orbit". This is the sentence introducing (2.12).
- **11b repairs applied since r6b** (outside 11a): ε₃ is now set at each use (#4.33, #4.37, #4.38-1, #4.40.1-1-0, #4.47, #4.561); ρ̄(x) at #5.1; #4.40.1-2-1's citation. The user-approved renames are done: (c)'s weight at #4.47 is w_Λ; the appendix point x − Le₁ at #A.11.12 is z₁; and (K2)–(K6) (#A.13, #A.15, #A.15-1, #A.17-2) write w_{x̄} for the dropped abbreviation w. The remaining w in the appendix are bound variables. #A.17 names its boundary point, λ(w), w ∈ ∂B.
- **Recorded for later packets.** The tags {#D.S_j} (#4.61 and #A.11.46), {#D.ψ_f} (#4.206 and #A.11.4-1), and {#D.δ_H} (#4.235-1 and #A.11.29) each appear on two lines. The other meanings of w are at #0.1.17-2, #4.106, #4.236, #4.284.14, #4.413, and #4.454.35.
- **Lines.** In characters, the part's longest lines are 615 (#4.9-0), 613 (#4.7-1-0), and 601 (#4.5-2-2), as at r5; #4.7-00-1 is under 600. CR 0; every citation resolves, with the balaban_proofs tags included.
- **Size.** Argument of the r7 packet 21.7k characters (≤ 25k). Definition check: 0 conflicts.

## Repaired files

LF 9ee9725548ae, table e02c753f1f9d, labels 76a33fb2e599.
