# LF review, part 12a, round 7: triage and repairs (6 Nov 2026)

Review: `verification/isolated_reviewer/reviews/lf-p12a-20261106-r7/review.md`, LF 045941f2b1f1, focused on the round-6 repairs. Result: 0 fatal, 0 serious, 1 minor (m7-1), and 3 cosmetic (c7-1 to c7-3). All round-6 repairs were confirmed. Not clean, so round 8 is focused and round 9 must be full.

| Finding | Line | Repair |
|---|---|---|
| m7-1 | LF #5.66, #5.66-1, #5.66-2; table #T4.40 | ρ^{LF}_K ≤ η^{gen}_K + ρ^E_K, and ρ^E_K = ρ^E_{K,0} + 2K_ΔC″c″x^*_K/(1 − θ_Q) (#C7.6-6-4-4) with x^*_K = C_pos(2τ^{pt}_K + Δ̄₀₀)/(1 − G_w), Δ̄₀₀ ≤ C[ρ^E_{K,0} + e^{−C_Pk/4} + r̄_K], τ^{pt}_K = τ^w_K/(4ℓ_C) (#C7.8-9-3-1, #C7.8-9-8). So c̄^W_K ≤ C[kγ_K + kKw_K + kτ^w_K], and kτ^w_K ≤ Clog(K + 2)(K + 2)^{−2} since k ≤ K, summable also times any power of log K. |
| c7-1 | Cauchy #C6.2.1-7 | The post-R domains are cited at LFR II p.378 l.14–27, p.390 l.10 and l.34–35, and LFR I p.179 l.40 (all re-read), not Theorem 1. The line was split at a sentence boundary into #C6.2.1-7 and #C6.2.1-7-1; LF #5.6 now cites #C6.2.1-7–#C6.2.1-7-1. |
| c7-2 | Cauchy #C6.2.20-2-1 | LFR I (1.55) (p.188 l.6–8) is a test of B_j at δ′_j = g_jA₁p₁(g_j) (p.183 l.2) under a Gaussian form, so #C8.6.9-3–#C8.6.9-6 give Cp₁^{d_G}g_j²∣δ_j∣ ≤ Cp₀^{d_G}g_j²∣δ_j∣. Pointer added; the line was split, its last two sentences becoming #C6.2.20-2-2. |
| c7-3 | Cauchy #C6.2.17-2 | "geometric in k up to polynomial factors in k". |

Wider implications:
- #5.41.6 and #5.65.1 bound D^{w,LF}_K through the Cauchy note's #C7.8-7, which already carries ρ^E_K in full. Unaffected.
- The pair note (#PC4.14-5.6.2, #PC6.4.1-1) uses only the summability of c̄^W_K times powers of log K, which #5.66-2 keeps. The fork will be told.
- No other file states a bound of c̄^W_K, ρ^{LF}_K, or ρ^E_K in the old form (grep of LF, Cauchy, D2.7, table).

Hashes: LF 54586e59a1ab, labels 74e750f26ac5, table 1b3e435ba9ef, Cauchy 7e5cafafdf19.

## Pre-check for lf-p12a-20261106-r8

Spec `specs/spec_p12a_r8.json`, lf_sha 54586e59a1ab, focused. Definition check: 0 conflicts (1 allowed). Packet built: 23,613 argument characters (22,665 before; the extract grew to #5.66–#5.66-2).

Changed LF tags (the gate's list, 3): #5.66, #5.66-1, #5.66-2, all re-read and re-derived. Outside the extracts: #5.6 (pointer only), named in the spec.

Checks:
- Changed lines re-derived: yes (x^*_K from #C7.8-9-8, τ^w_K from #C7.8-3 and #T4.40, k = K − j(C) ≤ K).
- Arithmetic and citations: yes; the LFR I and LFR II lines re-read in the corrected transcripts.
- New symbols and claims: no new symbols; the new claim kτ^w_K ≤ Clog(K + 2)(K + 2)^{−2} checked (log(K + 2) ≥ 1 for K ≥ 1).
- Wider implications: as above.
- Linear order kept: yes.
