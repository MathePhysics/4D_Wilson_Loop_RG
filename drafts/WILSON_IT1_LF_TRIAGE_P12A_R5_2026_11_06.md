# LF review, part 12a, round 5: triage and repairs (6 Nov 2026)

Review: `verification/isolated_reviewer/reviews/lf-p12a-20261106-r5/review.md`, LF 754049c02d44, focused on the round-4 repairs. Result: 0 fatal, 0 serious, 1 minor (m-a), 3 cosmetic (c-a to c-c), and one aside on the table. All round-4 repairs were confirmed. Not clean, so round 6 is focused and round 7 must be full.

| Finding | Line | Repair |
|---|---|---|
| m-a | Cauchy #C6.2.20-3 | The per-test bound did not fit a per-point term with constant C_M. New #C6.2.20-2-1 states two ingredients per point at i ≥ k − m. The radial shells number at most 8s_T(i) per variable, each ≤ Cp₀^{d_G}e^{−cp₀²}g_i²∣δ_i∣, so they sum to ≤ ∣δ_i∣ by s_T(i) ≤ 3 + (2log g_i^{−2})^ν. The coupling parts of all the soft tests at a cube, with the cascade factor N + 1, sum to ≤ ∣δ_i∣ (LF #3.40-1). #C6.2.20-3 now cites it. This also answers the referee's request on restated radial cutoffs. |
| c-a | Cauchy #C6.2.1-7 | j₀ is defined as the least i with Z_i = Λ_i^c ≠ ∅ (#CP.2). The step at j₀ − 1 creates Λ_{j₀} through Ω_{j₀} or R_{j₀}, with thresholds 2ϑ_{j₀−1}, ε_{j₀}, and ϑ_{j₀−1}. Γ_{j₀−1} "may be" non-trivial. |
| c-b | LF #5.66-1 | Adds "or at most a constant times w_K ≤ Kw_K". |
| c-c | Cauchy #C6.2.17-1 | "i > k/2" becomes "i ≥ k − m" (#C6.2.9-3). |
| aside | table #T3.34, #T3.34-1 | "CRE's β" becomes Bałaban's β, one constant of CRE, LFR I, and LFR II, chosen below LFR I (1.24) (p.182 l.16–17; LF #4.465–#4.470). |

Hashes: LF 69b89ae84241, labels 72b7b6332a21, table ddd74a0dabc1, Cauchy 735666069f37. The table also gained #T3.34-2, #T4.42, and #T4.43 for the fork's announcements.

## Pre-check for lf-p12a-20261106-r6

Spec `specs/spec_p12a_r6.json`, lf_sha 69b89ae84241, focused. Definition check: 0 conflicts (1 allowed). Packet built: 22,585 argument characters.

Changed LF tag in the extracts (the gate's list, 1): #5.66-1. Re-read: w_K ≤ Kw_K for K ≥ 1, and s′_K's 2C_aw_K term is now covered.

Changed Cauchy lines (read live): #C6.2.1-7, #C6.2.17-1, #C6.2.20-2-1, #C6.2.20-3. Re-derived:
- **#C6.2.1-7:**
  - Ω_i ⊃ Λ_i (CRE (2.1)), so Λ_i = T gives Ω_i = T.
  - (3.16) can create Z_{j₀} through R_{j₀} with Ω_{j₀} = T, as the referee noted.
- **#C6.2.20-2-1:**
  - #C6.2.1-4's shell bound carries e^{−cp₀²}, which beats (3 + (2log g^{−2})^ν)·8 for γ small.
  - The pre-check corrected "6s_T(i)" to "8s_T(i)", the list in LF #3.21 having eight equations.
- **#C6.2.17-1:** m := ⌊k/2⌋ is #C6.2.1-8's.

Wider implications:
- #C6.2.9-1's "C_M … a constant of d, L, and G" now matches the per-point bundling.
- LF #3.40-1 already states the per-cube sum.
- No other "per variable or test", "i > k/2", or "CRE's β" remains in LF, the Cauchy note, the table, or D2.7. The Cauchy note's "CRE's β₀" (l.380) is a different constant.
- The table rows for β agree with LF #3.24 and #4.465–#4.470.

Linear order: 12a is the current packet.
