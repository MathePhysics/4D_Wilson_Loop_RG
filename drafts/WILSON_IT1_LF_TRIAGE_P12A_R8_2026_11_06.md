# LF review, part 12a, round 8: triage and repairs (6 Nov 2026)

Review: `verification/isolated_reviewer/reviews/lf-p12a-20261106-r8/review.md`, LF 54586e59a1ab, focused on the round-7 repairs. Result: 0 fatal, 0 serious, 1 minor (m8-1), and 6 cosmetic (c8-1 to c8-6). All round-7 repairs were confirmed. Not clean, so round 9 is focused and round 10 must be full.

| Finding | Line | Repair |
|---|---|---|
| m8-1 | LF #3.27-1, #3.28–#3.28-2, #3.31 | Option (a): at the step j the runs share B_j of LFR I (1.53), as §4 shares B (#4.219). The linearisation and C change only the bonds b₀(c) (CRE p.249 l.14–16, l.21–24), which the tested bonds exclude, so V^X_j(b) = e^{ig^X_jB_j(b)}V^{(j),X}(b). The tested quantities of (1.27) differ by ≤ ∣e^{ig^AB} − e^{ig^BB}∣ + ∣V^{(j),A} − V^{(j),B}∣ + ∣W_A − W_B∣ ≤ 6Cg_j²∣δ_j∣δ′_j + 4c_vρ̄_j, using ∣g_jB_j∣ < 6δ′_j (LFR I (1.54), whose 3δ′_j holds at the soft threshold) and (P′) for both cascade averages (#3.27-1). Relative to 2δ′_j: 2c_vρ̄_j/δ′_j + 3Cg_j²∣δ_j∣, so the C of δ^f_j is at least 2C_{1.27} and the coupling C of δ^s_j at least twice #2.10's. At the common B_j, (1.55) is the pure coupling shell, and so is (1.59) at the common new B_j, its change of variables leaving χ′^{(j)} unchanged (CRE p.252 l.2–3, l.9–10). |
| c8-1 | Cauchy #C6.2.20-2-1, #C6.2.20-2-2 | (1.55) is a test of the common B_j under a CRE (3.15)-type form; #C8.6.9-3's density bound with LF #2.12's per-bond precision ("verbatim" dropped). The threshold on the scaled B_j is g_j^{−1}δ′_j = A₁p₁(g_j) (LFR II p.383 l.21); (1.55) prints δ′_j, a slip; the bound holds at both, since A₁ < A₀ and p₁ < p₀. |
| c8-2 | Cauchy #C6.2.1-7–#C6.2.1-7-2 | The sources moved to a new line #C6.2.1-7-1, with Z_k of p.390 l.34 read as the large-field region off Z (LFR II p.378 l.8, (1.72) at p.379 l.13–20); the ingredients line is now #C6.2.1-7-2. LF #5.6 cites #C6.2.1-7–#C6.2.1-7-2. |
| c8-3 | Cauchy #C6.2.20-3 | Cites #C6.2.20-2-1–#C6.2.20-2-2. |
| c8-4 | LF #1.1, #5.6 | #1.1: j₀ is the pair's birth scale, that of its oldest alive component (#CP.2), X born at a scale ≥ j₀, and Ω_i = T for i < j₀ by #C6.2.1-7. #5.6 cites #C6.2.1-7. |
| c8-5 | LF #5.66 | Cites #C7.8-9-8–#C7.8-9-8-2. |
| c8-6 | Table #T4.40 | The κ₀ parenthetical follows "summable for κ₀ ≥ 11". |

Wider implications:
- The shared variable B_j at the cascade step agrees with §4's shared (B, V″, V_k) and with the Cauchy note's #C6.2.1-2 read step by step, the not yet integrated variables being the minimisers' data (#3.27-1).
- C_{1.27} enters only #3.26-3 (cascade tests, unchanged) and #3.31 (now 2C_{1.27}); C_h and #3.37–#3.40-1 use the generic C of δ^s_j, so their form is unchanged.
- #1.1's j₀ now matches #5.6, #C6.2.1-7, and #CP.2; §1's later lines use j₀ only through Ω_{j₀−1} = T and scales ≥ j₀ − 1, which hold for every alive component.
- No other file cites #C6.2.1-7-1 or #C6.2.20-2-1 for the moved content (grep).
- Added after launch (the first pass skipped these). The rest of the cascade integrand: LF §4(e) #4.626 already shares A_j and B_j in (1.60), and #4.628–#4.635 compare the 𝐄-, 𝐑-, 𝐁-terms, ℍ_Z^{(j)}, and V^{(j)} at the two runs' fluctuated configurations as variations. So the shared B_j of #3.28 is the convention already used there, and the outer comparison at different V_{j+1} is #4.635's variation.
- #4.634 contradicted #3.21: it called χ^{(j)} (1.9) and χ′^{(j)} (1.55) soft and gave (1.59) a factor e^{−cp₁²}. Repaired: both are sharp, with coupling shells Cp₀^{d_G}g_j²∣δ_j∣ at the shared A_j and B_j, and (1.59)'s shell is the coupling part of δ^s_j/κ_s. This is §4(e), outside 12a; its packet reviews it. LF 6e1ff0377576, labels c47f59411049.
- The other e^{−cp²} factors: Cauchy #C6.2.1-4 is (1.5)'s (LF #2.11), and #C8.2.1-15 is the small-field step's Gaussian tail, where the density is bounded above. Both are right.
- D2.7: table #T4.42 now has u := 640(2^d + 8), L₀^× := 4·10⁴u, and 2ℓ_P in ŷ_g and y_c (table 23e44e965fcb). D2.7 cites the fork's #629-5 and #288, and (2-2) drops "and with the links" (two-loops #826 now has them). D2.7 e12e607334d8.
- (T0): D2.7 15.8-1(3-1)'s (420 + C_win)uM(…) ≤ ν_r/8 is two-loops #572's condition with 420 in place of 170 (𝒟(𝒴) has the pair's eight sides), C_win ≤ 196u/c_w by #568; both are the same smallness of g. Stated in (3-1).

Hashes: LF 741f6df6e370, labels 4df8400ba4b1, table fd3c08b35015, Cauchy 60b68ceb2400.

## Pre-check for lf-p12a-20261106-r9

Spec `specs/spec_p12a_r9.json`, lf_sha 741f6df6e370, focused. Definition check: 0 conflicts (1 allowed). Packet built: 25,717 argument characters (#1.1 and #5.6 added to the extracts).

Changed LF tags (the gate's list, 8): #1.1, #3.27-1, #3.28, #3.28-1, #3.28-2, #3.31, #5.6, #5.66, all re-read and re-derived. Outside the LF: Cauchy #C6.2.1-7–#C6.2.1-7-2, #C6.2.20-2-1–#C6.2.20-3, and table #T4.40, named in the spec.

Checks:
- Changed lines re-derived: yes, every repair, the cosmetic ones included (round 8's m8-1 came from a cosmetic pointer whose presupposition was not checked).
- Arithmetic and citations: yes; CRE p.248 l.11, p.249 l.14–24, p.252 l.2–10, LFR I p.187 l.42–56, p.188 l.1–8, LFR II p.378 l.8, p.379 l.13–20, p.383 l.21, p.390 l.34–35 re-read in the corrected transcripts.
- New symbols and claims: the shared B_j and V^X_j(b) = e^{ig^X_jB_j(b)}V^{(j),X}(b) on the tested bonds; checked against the b₀(c) exclusion of the star sets.
- Each pointer checked against every line treating the same object: (1.55), (1.27), and (1.59) now share one identification; #1.1's j₀ matches #5.6, #C6.2.1-7, and #CP.2.
- Wider implications: as above.
- Linear order kept: yes.
