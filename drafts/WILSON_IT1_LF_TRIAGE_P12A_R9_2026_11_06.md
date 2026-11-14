# LF review, part 12a, round 9: triage and repairs (6 Nov 2026)

Review: `verification/isolated_reviewer/reviews/lf-p12a-20261106-r9/review.md`, LF 741f6df6e370, focused on the round-8 repairs. Result: 0 fatal, 0 serious, 1 minor (m9-1), and 5 cosmetic (c9-1 to c9-5). All round-8 repairs were confirmed. Not clean, so round 10 is focused and round 11 must be full.

Why m9-1 escaped: r9 was launched before the wider-implications pass. That pass, run afterwards, found the cross-step question and judged it covered by §4(e) #4.635, but the conclusion went into the triage, not the note.

| Finding | Line | Repair |
|---|---|---|
| m9-1 | LF #3.28-4–#3.28-7, #3.36 | The cascade is compared step by step at equal data of the step. After (1.29) the step's tests are (1.9), (1.27), the decomposition (1.55), and χ_k^{(n+1)} (LFR I p.187 l.35–39). On the χ′^{(j)} components the soft (1.27) is 1, its argument ∣e^{igB}e^{iℍ_Z^{(j)}} − 1∣ < δ′_j + O(1)e^{−R_j}ε_j < 2δ′_j. On the others (1.59) and 1 − χ′^{(j)} test B_j alone (p.188 l.42). χ_k^{(n+1)} is 1 on the support of χ_k^{(n+2)} (#3.68-2). The components excluded at the step j by 1 − χ_k^{(n+1)}, 1 − χ′_j, or (1.28) leave Z before (1.53), so their variables stay the shared block variables (Cauchy #C6.2.1-2). Their tests, χ_k^{(n)} included, depend only on the variables of their component (p.183 l.14–17). So on Z the output depends on its data only through analytic terms, whose passage to the next step's data is §4(e)'s variation (#4.626, #4.635). No test is compared at run-dependent data. #3.36 now says "pointwise in the shared variables of the step". |
| c9-1 | LF #3.28-3 | (1.59)'s test is radial in B_j for ∣g_jB_j∣ ≤ π (2∣sin(sθ/2)∣ per eigenvalue). Its soft forms differ by ∣g^A − g^B∣∣B_j∣/(2δ′_j) plus the threshold's part, a coupling part of δ^s_j. |
| c9-2 | LF #3.28-1 | ∣g^A_jB_j∣ < 6δ′^A_j on run A's support, and on run B's up to 1 + Cg_j²∣δ_j∣, absorbed in C. |
| c9-3 | LF #3.31 | C of the coupling term at least 2 + κ_s times #2.10's, covering t^A/t^B ≤ 2. |
| c9-4 | LF #3.28-4 | LFR I (1.5), which #2.4 compares at a shared V_j(y, x), is not among the step's tests. |
| c9-5 | Cauchy #C6.2.1-7-1 | "Z_k there read as the large-field region off Z, a reading of the print (LFR II's Z_k contains Z, p.364 l.29), to which the components with the large-field function are joined in the new large-field region". |

Wider implications (checked before launch; every line that uses the runs' identification, the shell constants, or the tests touched):
- LF §4(e) #4.626 already shares A_j and B_j in (1.60). #4.628–#4.635 compare the remaining terms as variations, and #4.249-1 and #4.251 share A. Consistent.
- LF #4.634 (repaired after round 9's launch): (1.9) and (1.55) are sharp, with coupling shells at the shared A_j and B_j, and (1.59)'s shell is the coupling part of δ^s_j/κ_s. It is in §4(e), outside 12a.
- LF #1.2–#1.2-1 and Cauchy #C6.2.1-2 (shared V in the large-field operations) agree with #3.28-6: the excluded components keep V.
- LF #3.39 (χ_k^{(n−1)} with 1 − χ_k^{(n)}) is the excluded branch of #3.28-6.
- #3.40–#3.40-1 count (1.59)'s coupling part among the soft tests', unchanged. #3.26-3 uses C_{1.27} directly, unchanged.
- The table has no row for C_{1.27} or for δ^s_j's constants. D2.7 does not use the cascade identification.
- Line lengths: all changed lines ≤ 600 except #3.29 (679), which is unchanged here.

Hashes: LF 00a7d8553b7f, labels 58eb59c674d0, table 23e44e965fcb, Cauchy 8eb6206f0587.

## Pre-check for lf-p12a-20261106-r10

Spec `specs/spec_p12a_r10.json`, lf_sha 00a7d8553b7f, focused. Definition check: 0 conflicts (1 allowed). Packet built: 24,535 argument characters, within 25k. #1.1–#1.2-1, #5.6, and #5.66–#5.66-2 are unchanged since r9 and moved to permitted background for this focused round; the full round restores them.

Changed LF tags (the gate's list, 9): #3.28-1, #3.28-2, #3.28-3, #3.28-4, #3.28-5, #3.28-6, #3.28-7, #3.31, #3.36, all re-read and re-derived. Outside the extracts: Cauchy #C6.2.1-7-1, and LF #4.634 (§4(e), named in the provenance).

Checks:
- Changed lines re-derived: yes, every one. That includes the excluded-component branch of #3.28-6, read in LFR I p.182 l.36–38 and p.183 l.3–17.
- Arithmetic and citations: yes. LFR I p.187 l.35–39, p.188 l.42, p.182–183, and LFR II p.364 l.29 were re-read. 2∣sin(sθ/2)∣ is increasing for sθ ≤ π. The soft (1.27) argument is < δ′_j + O(1)e^{−R_j}ε_j < 2δ′_j, at either reading of (1.55)'s threshold.
- New symbols and claims: none new; the claim "no test is compared at run-dependent data" was checked branch by branch.
- Wider implications: done before launch, listed above.
- Linear order kept: yes.
