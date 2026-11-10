# LF review, part 12a, round 4: triage and repairs (6 Nov 2026)

Review: `verification/isolated_reviewer/reviews/lf-p12a-20261106-r4/review.md`, LF 0cb0774db832, a full round. Result: 0 fatal, 0 serious, 2 minor (m4, m5), and 3 cosmetic remarks (c1–c3). Verdict: the claim holds. All five are repaired in place.

| Finding | Line | Repair |
|---|---|---|
| m4 | #3.39-1 | c_{hs} used s_T(j) = 2 + N̄(K − j), which depends on K. New #3.39-1 defines ŝ_T(j) := 3 + (2log(ḡ^{−2} + C + 8b′(1 + j(C))(j + 1)))^ν and shows s_T(j) ≤ ŝ_T(j) at the young-history scales by #CP.14 and #3.30. #3.39-1-1 uses ŝ_T in the first-part bound and in c_{hs}, which is now K-free. |
| m5 | #3.40-1, #5.66-1 | The tests stand at scales j ≥ j₀ − 1 ≥ k − m, so the caller's term is now 10sup_{i≥k−m}∣δ_i∣. (8.6) at i ≥ k − m ≥ k/2 gives the same form C[kθ̃^{k/2} + Kw_K]. |
| m5, Cauchy §6.2 | #C6.2.1-4, #C6.2.1-7, #C6.2.3, #C6.2.9-1, #C6.2.9-3, #C6.2.19-3, #C6.2.20-3 | sup_{i>k−m} becomes sup_{i≥k−m}. #C6.2.1-7 and #C6.2.3 now state that the ingredients at i < j₀ − 1 are the all-small-field pair's, and that the step at j₀ − 1 carries run-dependent thresholds (CRE (3.3) at 2ϑ_{j₀−1}; the Q-test threshold 2ϑ_k at LF l.311). #C6.2.9-3 derives the bound at i ≥ k − m. The other terms of s′_K already start at k − m. Packet 10 (clean) is reopened for these seven lines; 12a r5 reviews them. |
| c1 | #3.21 | "The radial cutoffs other than χ(Λ_i) of #3.22, and the fluctuation and gauge-fixing cutoffs, stay sharp". |
| c2 | #3.24-1 | The underived 1 + 1/22 is dropped. The other margins absorb 1 + 2κ_s = 1 + 1/120, as checked at each line (#3.48–#3.99). |
| c3 | #3.30-2 | The dependence list of C_{1.27} adds r, p₀, β₀, c_v, C_G(ε₀), c″_K, and Lemma 2.1(i)'s b′ and C. |

New D-tag: ŝ_T (#3.39-1). Relabelled. LF 754049c02d44, labels a9531159e21e, Cauchy c8758558b2b2, table a8041051efc3 (unchanged).

## Pre-check for lf-p12a-20261106-r5

Rev lf-p12a-20261106-r5, focused on the round-4 repairs. Spec `specs/spec_p12a_r5.json`, lf_sha 754049c02d44. Definition check: 0 conflicts (1 allowed). Packet built: 22,576 argument characters.

Changed tags in the extracts since the r4 snapshot (the gate's list, 7): #3.21, #3.24-1, #3.30-2, #3.39-1, #3.39-1-1, #3.40-1, #5.66-1. Each line was re-read and re-derived:
- #3.21: the soft χ(Λ_i) is excluded explicitly. The sharp list is unchanged and was confirmed by r4 against CRE and LFR I/II.
- #3.24-1: 2κ_s = 2/240 = 1/120. The cited range #3.48–#3.99 is the page checks (#3.100-1 names #3.49–#3.99), and #3.24 states that they hold with 1 + 2κ_s.
- #3.30-2: the list matches the factors of #3.30-1's C_{1.27}: c_v, C_G(ε₀), c″_K, C(M), A₀/A₁, β₀, 2^{p₀+2r+1}, L, and the b′ and C inside the log.
- #3.39-1:
  - j ≥ n − 1 and K < 8n + j(C) give K − j < 8(j + 1) + j(C) (#3.30).
  - Lemma 2.1(i) gives log g_j^{−2} ≤ log(ḡ^{−2} + b′(K − j) + C) ≤ log(ḡ^{−2} + 8b′(j + 1) + b′j(C) + C).
  - 8(j + 1) + j(C) ≤ 8(j + 1) + 8(j + 1)j(C) = 8(1 + j(C))(j + 1).
  - #CP.14 gives N̄(K − j) ≤ (2log g_j^{−2})^ν + 1.
  - So s_T(j) = 2 + N̄(K − j) ≤ ŝ_T(j). No k or K appears in ŝ_T.
- #3.39-1-1: s_T ≤ ŝ_T replaces s_T in the r4-checked bound. ŝ_T(j) = O((log j)^ν), against L^{−(3−7ε₀)j/4} with 3 − 7ε₀ > 0, so c_{hs} < ∞.
- #3.40-1:
  - The tests stand at j ≥ j₀ − 1 (#1.7, #3.7).
  - A young pair has j₀ > k − m (#C6.2.3), so j₀ − 1 ≥ k − m.
  - The per-cube bound ≤ ∣δ_j∣ is unchanged.
- #5.66-1:
  - (8.6) is ∣δ_i∣ ≤ 2C_sC_β[2(1 − θ̃)^{−2}(i + 1)θ̃^{i+1} + (K + 1 − i)w_K].
  - At k − m ≤ i ≤ k: i + 1 ≥ k/2 and i + 1 ≤ k + 1, so (i + 1)θ̃^{i+1} ≤ (k + 1)θ̃^{k/2}. Also K + 1 − i ≤ 2K.
  - So the bound is C[kθ̃^{k/2} + Kw_K].

Changed Cauchy lines (not snapshotted; the reviewer reads the live file, c8758558b2b2): #C6.2.1-4, #C6.2.1-7, #C6.2.3, #C6.2.9-1, #C6.2.9-3, #C6.2.19-3, #C6.2.20-3. They were re-read and checked:
- k − m = ⌈k/2⌉ ≥ k/2.
- The terms (k + 1)θ̃^{k−m}, L^{−γ_H(k−m−1)}, and L^{−(1−ε₀)(k−m)} of s′_K bound the D_i, r_i parts at every i ≥ k − m.
- The CRE (3.3) Q-test threshold is 2ϑ_k at step k (LF l.311).
- The pre-check fix on #C6.2.9-3 removes a doubled "since".

New symbols or claims: ŝ_T only, checked above. Linear order: 12a is the current packet. 12b r3 and p13 r1 wait for 12a to be done.
