# LF review, part 12a, round 6: triage and repairs (6 Nov 2026)

Review: `verification/isolated_reviewer/reviews/lf-p12a-20261106-r6/review.md`, LF 69b89ae84241, focused on the round-5 repairs. Result: 0 fatal, 0 serious, 1 minor (m6-1), and 3 cosmetic (c6-1 to c6-3). All round-5 repairs were confirmed. Not clean, so round 7 is focused and round 8 must be full.

m6-1 was introduced by my round-5 repair: I carried #C6.2.1-4's factor e^{−cp₀²} over to every sharp cutoff.

| Finding | Line | Repair |
|---|---|---|
| m6-1 | Cauchy #C6.2.20-2-1 | Each shell is ≤ Cp₀(g_i)^{d_G}g_i²∣δ_i∣ (LF §2(b), #2.10–#2.15, and the Cauchy note's §8.6), the e^{−cp₀²} holding for (1.5) only. 8s_T(i)·Cp₀^{d_G}g_i²∣δ_i∣ ≤ ∣δ_i∣ for γ small. |
| c6-1 | LF #5.66, #5.66-1; table #T4.40 | "geometric in k up to polynomial factors in k and powers of log(K + 2)". |
| c6-2 | LF #5.66-1 | The pointer is now #C6.2.9-1, #C6.2.17-1–#C6.2.17-2. |
| c6-3 | Cauchy #C6.2.1-7 | j₀ := the least i with a non-empty Z_i in a run's term. The post-R domains (LFR II Theorem 1, p.355) leave no region of a removed component, so j₀ is the oldest alive component's birth scale, and Λ_i = Ω_i = T for i < j₀ globally. This keeps LF #1.1 and the walk note's citation of it valid. |

Wider implications:
- LF #5.6 said "the ingredients at the scales i < j₀ are the all-small-field pair's (#C6.2.3)". #C6.2.3 says i < j₀ − 1 since round 4, so #5.6 now reads i < j₀ − 1. Its layers still start at j₀ − 1 ≥ k − m_W.
- "Radial shells" (LF #3.40-1, Cauchy #C6.2.20-3, l.1047, l.1384) is tied to the sharp-cutoff shells in #C6.2.20-2-1.

Hashes: LF 045941f2b1f1, labels cec43cc0d0c5, table f8e065517a74, Cauchy d357dffb46bd.

## Pre-check for lf-p12a-20261106-r7

Spec `specs/spec_p12a_r7.json`, lf_sha 045941f2b1f1, focused. Definition check: 0 conflicts (1 allowed). Packet built: 22,665 argument characters.

Changed LF tag in the extracts (the gate's list, 1): #5.66-1, re-read. Outside the extracts: #5.6 and #5.66 (wording only), named in the spec.

Cauchy #C6.2.1-7 and #C6.2.20-2-1 were re-read and re-derived:
- **#C6.2.20-2-1:**
  - #2.13 gives Cp₀^{d_G}g²∣x − x′∣ per variable.
  - #2.14 gives the same for χ^{(j−1)c}(R_j).
  - #2.15 refers the R-operation's radial cutoffs to §8.6 and §4(d).
  - (1.82)'s threshold A₁p₁(g) ≤ Cp₀(g).
  - The pre-check also changed "radial cutoffs" to "sharp cutoffs" and wrote "this note's §8.6".

Checks:
- Changed lines re-derived: yes.
- Arithmetic and citations: yes.
- New symbols and claims: none new.
- Wider implications: LF #5.6, #5.66, #T4.40, and the "radial shells" wording, as above.
- Linear order kept: yes.
