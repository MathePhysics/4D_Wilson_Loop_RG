# Triage of lf-p12a-20261108-r14

## Verdict

- r14 was a focused round of 12a at LF 315b050eea14, table 6d09b1b5054d, and labels 971e7d7d5325.
  - Under review: #3.25–#3.36, and #4.53-1–#4.53-1.0-2 as #3.27-1-1 uses them.
- **Fatal:** none. **Serious:** none. **Minor:** none. **Cosmetic:** five, c1–c5.
- The round is clean. It is focused, so it is 12a's first clean round, and the clean count is 1. The second clean round must be a full round of 12a.
- Round 13's remarks c1–c4 were confirmed repaired.
- The referee re-derived the corner geometry (CMP98 (2), PRT1 (1.6)–(1.7)) and confirmed c_{ax} = 2d(L − 1) + 1. It also noted that the bound holds without assuming that run B's background is already axial: with u_V(x) = P_V and u_W(x) = P_W, the difference abs(P_V − P_W) gives the same bound.

## Repairs

| Finding | Line | Issue | Repair |
|---|---|---|---|
| c1 | #3.27-1-1 | CRE (3.10)–(3.11) print the axial gauge of V^{(k)} = M^k(U_{k+1}) itself, whereas p.266 l.34 concerns V^{(k)}_{□′}. The pins are LFR I p.187 l.39–40 and CRE p.248 l.35–37 | The line now cites "CRE (3.10)–(3.11), p.266 l.44–58, and p.248 l.35–37, p.266 l.34" and "LFR I p.187 l.39–40". I checked each pin against the corrected transcription: (3.10) at p.266 l.44–52, (3.11) at l.56–58, and "we perform all the operations discussed in Sect. 3 [III]" at p.187 l.39–40 |
| c1, c2 | #3.27-1-1, #3.27-1-2 | "y ∈ T^{(j+1)}" and "u = 1 on T^{(j+1)}" should name the data block points of the scale j + 1. The residual group is printed at LFR I p.182 l.41–43 | "y the data block points of the scale j + 1", and "u = 1 at these block points (LFR I p.182 l.41–43, REG (1.14))". At p.182 l.41–43, v is 1 on the set's intersection with T^{(j+1)}. The sentence of the conversion is split off as #3.27-1-2 (the line would have been over 600 characters), and #3.28-1 now cites #3.27-1-2 for c_{ax} |
| c3 | #3.27-1 | (1.16) at j + 1 covers j ≤ k − 2 only | "(LFR I (1.16) at j + 1; at j = k − 1 the sentence after it and (1.17), p.180 l.27–33)". Checked: p.180 l.27–30 replace the bracket at j = k by (Ω_k^c ∖ Z″_k)^{(k)}, …, and (1.17) gives 𝔹_k″ |
| c4 | #3.27-1, #3.27-1.0 | Why the averaging blocks see only the layers ≥ j, and #4.53-1's hypotheses at the scale j, were not stated | #3.27-1.0 (split off #3.27-1, which would have been 759 characters): the blocks lie in the layers j + 1 and j, where (P′) gives a_j abs(A′*) ≤ 2ρ̄_j, since ρ̄ decreases in the layer and a_j ≤ a_{j+1}. MU^B satisfies (52) by #4.7-2, as in #4.53-1.0. CMP 98 (159)–(163) is cited as #4.53-1, with 2ρ̄_j small |
| c5 | table, labels | The table's LF symbol list and the labels lack #3.27-1-1 and #D.c_ax | Bookkeeping, for the table fork. The rows and a relabel are requested at the new SHA |

**Consolidation.** #4.53-1 said "as in #3.27-1", while #3.27-1.0 now cites #4.53-1 for CMP 98 (159)–(163). The pointer in #4.53-1 is deleted, so the bound is stated once, in #4.53-1.

**Queued repair applied.** #4.53-1.0-1's "which has W's data" is deleted (see WILSON_IT1_LF_TRIAGE_P13B_R9_2026_11_08.md, Rounds). Part 13a2's r11 reviews it.

## Checks

- No duplicate tags. No CRLF.
- Line lengths: #3.27-1 370, #3.27-1.0 406, #3.27-1-1 427, #3.27-1-2 303, #3.28-1 491, and #4.53-1.0-1 550 characters.
- New tags: {#3.27-1.0} and {#3.27-1-2}. {#D.c_ax} moved to #3.27-1-2.
- A grep for citations of #3.27-1: #3.26-1 and #3.28-3 cite its first sentence (equal data, (P′)), which stays in #3.27-1. #3.28-1 cites #3.27-1-2.

## Rounds

- 12a's next round is a full round, for the second clean round.
- Before it, as queued: 13b r10 (narrow) and 13a2 r11 (focused). Both specs move to the new LF SHA.

## Pre-check of lf-p13a2-20261108-r11 (focused)

- **Spec.** specs\spec_p13a2_r11.json at LF efa2e2fdb7b1 (after 13b r10's repairs), prior r10. --check gives 0 conflicts (7 allowed). Built: 17,035 argument characters, under 25k.
- **Changed tags since r10 (16), all under review.** Besides those below:
  - **#4.52-1-2** is new, split off #4.52-1-1 by 13b r10's m1. #4.52-1-1 now reads (1.19) at the base 1 as fixing U_0 in its orbit under REG (1.14)'s subgroup (REG p.079 l.16), after V_Λ's axial gauge in Λ^{(k)} (LFR I p.197 l.3–4). Both pins are checked in WILSON_IT1_LF_TRIAGE_P13B_R10_2026_11_08.md. #4.53-1.1-1 cites #4.52-1-2.
  - The spec's claim (ii) and Q2 carry this reading.
  - **#4.51-2 and #4.51-2-1.** The curve U^X_t and its critical orbit (VAR Theorem 1, p.279 l.8–15; (100)–(102), p.293 l.20–31). Re-derived in WILSON_IT1_LF_TRIAGE_P13A2_R10_2026_11_08.md. H₁𝔛 is the data derivative because 𝒜₁ and HD vanish to second order (#4.46-2.1, VAR (73)).
  - **#4.52-1 and #4.52-1-1.** Run A's ū₀ (LFR I p.197 l.39–42), and the axial gauge with the corners. Re-derived in the r10 triage and in WILSON_IT1_LF_TRIAGE_P13B_R9_2026_11_08.md. 13b r10 reviews them.
  - **#4.53.** U^A(V′^B₀) is the element in #4.52-1-1's gauge of run A's critical orbit at V′^B₀. The two brackets compare W to elements of that gauge.
  - **#4.53-1.** Only the pointer "as in #3.27-1" is deleted.
  - **#4.53-1.0-1 and #4.53-1.0-2.** The lemma with d(L − 1) bonds and 2d + 1, re-derived in the 13b r9 triage. "which has W's data" is deleted: in #4.53-1.1, V = U^A_1 has the data V′^B₀, and at m = k, #4.53-1 bounds M^k(V) − M^k(W) directly.
  - **#4.53-1.1 and #4.53-1.1-1.** The brackets with (2d + 1). The hypotheses of the lemma hold at both W:
    - W = U^A(V′^A₀) = U^A_0 is in LFR I's gauge (#4.52-1-1) and satisfies (52) (#4.53-1.0);
    - W = MU^B satisfies both (#4.52-1-1, #4.53-1.0);
    - a_ksup abs(A) and a_ksup abs(A′*) are below α₁^{CMP} (#4.50-1.1.0-0).
  - **#4.53-1.2.** C′_Δ(M) and c_{δD} with (2d + 1). Their consumers cite them by name and are unchanged: #4.54 (abs(δD)), #4.54-0-1 (ε_{D″}), and #4.55, through C_A(M).
  - **#4.54-0.0.** U_t is taken as in #4.51-2, up to REG (1.14). The actions of #4.54-0.1 are gauge invariant, and (3.133) is applied at U_t.
  - **#4.55-1-1.** C_h is the sup over n, at each s used, with the prefactors, and its dependences are listed (r10's m1).
  - **#4.44-2 and #4.50-1.1.0-0.** r10's t4 and t1, reworded in place.
- **Symbols.** No new symbol beyond those in the rows requested from the fork (U^X_t, C′_Δ(M), c_{δD}).
- **Size.** Part 13a2 (#4.51–#4.55-1-1) is 14,676 characters of tagged lines, against 12,585 before r10. The increase is the new mathematics of S1, and it is under 25k.
- No known weak point and no OPEN is in these lines.

## SHAs

LF 315b050eea14 → d9e8d74b97a1. Table 6d09b1b5054d (the fork's rows are pending).
