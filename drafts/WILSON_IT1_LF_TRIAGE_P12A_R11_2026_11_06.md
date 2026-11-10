# LF review, part 12a, round 11: triage and repairs (6 Nov 2026)

Review: `verification/isolated_reviewer/reviews/lf-p12a-20261106-r11/review.md`, LF 31dff43f304e, the full round of the part. Result: 0 fatal, 0 serious, 1 minor (m11-1), and 4 cosmetic (c11-1 to c11-4). All of r10's remarks were confirmed repaired. **Not clean**, so the clean count restarts. r12 must be clean, and r13 must be a clean full round. The user asked to pause launches, so r12 is not launched.

Why m11-1 escaped:
- #5.66-2 has been unchanged since round 9, and rounds 7–10 left no finding on it.
- In my own read of the whole part before r11, I took its justification "a power of log g_k^{−2}, which is a power of log k" as given. I did not check the cited support #5.39-3-3, which lies outside the part and reverses CRE (2.6).
- The check that was missed: for every cited inequality, re-derive it from the print, including in lines outside the part.

| Finding | Line | Repair |
|---|---|---|
| m11-1 | LF #5.39-3-3, #5.66-2, #5.65 | CRE (2.6) (p.255 l.44–46) gives g_k ≤ (1 + β₀)(k − n)^{1/2}g_n for n < k, so g_n^{−2} ≤ (1 + β₀)²(k − n + 1)g_k^{−2} for n ≤ k. Two places used it. (1) #5.39-3-3: ε^R_A and ε^{(2)}_A(j), which are powers of log g_n^{−2} at k − m_W < n ≤ k (#5.39-1; closure 7.2's ε_A ≤ C_εM^dL^{d+1}R_j^{d+2}), are at most powers of log g_k^{−2} + log(k + 1). (2) #5.66-2: at k = K − j(C), log g_k^{−2} ≤ log(ḡ^{−2} + b′j(C) + C) by Lemma 2.1(i), so ε̄_A grows at most as a power of log(k + 2). The summability of c̄^W_Kε̄_A is unchanged, since #5.66-2 already covers any power of log K. The consumer #5.65 now reads "up to powers of log g_k^{−2} and log(k + 2) (R_k, CRE (2.5), and ε̄_A, #5.66-2)". |
| c11-1 | LF #3.28-3 | Added "and at j + 1 = k χ_k(Ω_k^{∼4}) (p.183 l.34)". It tests V_k, which is data of the step. Checked in the transcript: "for j+1=k the right-hand side above is multiplied by χ_k(Ω_k^{∼4})". |
| c11-2 | LF #3.28-5 | Added "the later CRE steps k′ ≥ k test only V_{k′}, V_{k′+1}, and A_{k′} (CRE (2.17), (3.2), (3.3), (3.16))". |
| c11-3 | LF #3.28-2 | Now cites #C6.2.20-2-1–#C6.2.20-2-2. |
| c11-4 | LF #3.28-5 | Now quotes p.181 l.17–18, "we have introduced new large fields, therefore they do not satisfy the condition (ii)", alongside p.177 (ii). |

Line lengths: #3.28-3 reached 636 characters, so it was split at a sentence boundary into #3.28-3 (300) and #3.28-3-1 (337). #3.36's range #3.28-3–#3.28-6 still covers both. The other changed lines are all under 600: #3.28-2 514, #3.28-5 595, #5.39-3-3 424, #5.65 about 190, and #5.66-2 483.

Wider implications. I checked every use of "power(s) of log g_k" and of ε̄_A and ε^R_A, in LF, Cauchy, the table, and D2.7:
- #4.208, #4.553, #4.562-1, #4.568, and #5.43 bound quantities at the scale k itself, or use g_m ≤ (1 + β₀)g_k for m ≤ k, which is the right direction. They are unaffected.
- #5.53 uses c̄^W_Kε̄_A, whose summability #5.66-2 covers. #5.65 is repaired above.
- Cauchy #C8.2.4 and the C8.2 line that follows it, and D2.7 15.7, are at the scale k. They are unaffected.
- No other line used the reversed inequality: a grep for "(1 + β₀)²g" finds nothing after the repair.

## Recheck (user request, 20:23)

I re-derived every line changed this session, and every outside line that the part cites for an inequality or a form: LF #2.10, #2.12, #2.17, #4.43-1, #4.480, #5.1, #5.3, #5.38-2, #5.39-2, #5.43, and Cauchy #CP.13-1, #CP.14, #CP.26-3, #C6.2.3, #C6.2.9-1, #C6.2.9-3, #C6.2.17-1, #C6.2.17-2, #C7.6-6-2-1-2. CRE (2.6) (p.255 l.44–46) and LFR I p.183 l.28–36 were re-read in the transcripts.

- **One gap, now repaired.** In #3.28-2, the bound |g^A − g^B||B_j|/(2δ′_j) was called "a coupling part" without the bound on |g_jB_j|; the deleted ray argument had carried it. #3.28-2 now adds that |g_jB_j(b)| ≤ (π/2)|e^{ig_jB_j(b)} − 1| < π(1 + κ_s)δ′_j on either support, for |g_jB_j| ≤ π, by |2sin(θ/2)| ≥ 2|θ|/π per eigenvalue. The line is 594 characters.
- **Re-derived as correct:**
  - (2.6)'s direction in #3.29-1 (g_k ≤ (1 + β₀)(k − j + 1)^{1/2}g_j and g_j ≤ (1 + β₀)g_k) and in #4.562-1;
  - #3.30's k + 1 ≤ 8(1 + j(C))(j + 1);
  - #3.39's L^{−(1−2ε₀)j} ≤ θ̃^jL^{−(3−7ε₀)j/4};
  - #3.39-1-1's coefficient 2Cn_T + 32C(1 + j(C));
  - #3.40's N̄(K − k′) ≤ N̄(K − j);
  - #5.6's j₀ − 1 ≥ k − m_W ≥ 7k/8;
  - #5.38-2 and #5.66's θ̃^{7k/8−1};
  - #5.66-2's K²w_K, which is summable for κ₀ > 10.
- **Other files:**
  - The λ_𝔏 and C_ϑ renames are complete. No bare λσ or λℓ remains in D2.7 or the table, and no C_s remains in D2.7.
  - D2.7 15.8-1(6)'s arithmetic, (1/640 + 1/3888)νσ < νσ/256, is right.
  - D2.7's #286 and #844-7 cite the right lines.

Hashes: LF 036c68e6658f, labels a39f0469a9ab, table f977a24fa070, Cauchy 8eb6206f0587, D2.7 05b327829cca.

## Pre-check for lf-p12a-20261106-r12

Spec `specs/spec_p12a_r12.json`, lf_sha 036c68e6658f. A focused round with three extracts: #3.25–#3.36, #5.39-1–#5.39-3-3, and #5.64–#5.66-2. The part's other lines are permitted background, and r13 will be the full round. Definition check: 0 conflicts (1 allowed). Packet: 17,575 argument characters.

Changed LF tags (the gate's list, 7): #3.28-2, #3.28-3, #3.28-3-1, #3.28-5, #5.39-3-3, #5.65, #5.66-2. Each was re-read and re-derived (see *Recheck* above).

Checks:
- Changed lines re-derived: yes.
- Citations re-read in the transcripts: CRE (2.6), p.255 l.44–46; LFR I p.177, p.178 (1.2), p.181 l.16–19, p.183 l.28–36, and p.188.
- New symbols: none. k″ is local to #3.28-5.
- Wider implications: done (above). The consumer #5.65 is in the packet.
- Lines ≤ 600: #3.28-2 594, #3.28-3 300, #3.28-3-1 337, #3.28-5 595.
- Linear order: 12a r12, then r13 (full), then 12b r3.
