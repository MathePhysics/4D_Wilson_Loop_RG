# Triage: LF part 13a2, round 6 (lf-p13a2-20261107-r6), 7 Nov 2026

## Verdict

Clean: no fatal, serious, or minor finding. There are two trivial findings (t1, t2) and one observation. This is 13a2's first clean round. The next round, r7, is a full round; if it is also clean, part 13a2 is done.

LF reviewed at ff32ad403ddb (table d3fd1c0fcdf7, LABELS 3371dd395591). The referee confirmed the round-5 repairs m1–m3 and t1–t4. It found no misquotation, no circularity, no volume or scale dependence, and no SU(N)-specific fact.

## Repairs

| Finding | Where | Repair |
|---|---|---|
| t1: #4.54-0 cites #1.3 for (7) on all of 𝐁″_k, but #1.3 says (7) holds on the support of the term | #4.54-0 | The citation now reads "(#1.7, (7) on the whole determining set, with #1.3's ε₁)". #1.7 states (7) on VAR Theorem 1's determining sets, with the ε₁ of #1.3 |
| t2: #4.55-1's polylog form also uses the bound on R_k, which is not cited; C_h's dependence list leaves b′, C_W, and r implicit; C_h is given only by existence | #4.55-1 | The line now opens "With R_k ≤ 2^{r+1}L(log g_k^{−2})^r (#3.29-1)". C_h is "at least the sup over n of these factors times L^{−(1−ε₀)n/12}, a constant of M, ε₀, ḡ, j(C), r, b′, C_W, and Bałaban's constants" (C_h is cumulative, as in #3.30-2 and #4.42-1) |
| Observation: the leading 2 in ε_{D″} is slack | none | No change. A larger regularity parameter is harmless, and (T-Λ) covers it (#4.50-1.2) |

## Re-derivation

- t1: #1.7 applies VAR Theorem 1 to the determining set 𝐁″_k of U″_k and states that its hypothesis (7) holds with #1.3's ε₁. That is (7) on the whole determining set, mixed plaquettes included (#1.3's second sentence). The chain to ε₁ in #4.54-0 is unchanged.
- t2: #3.29-1 gives R_k ≤ 2^{r+1}L(log g_k^{−2})^r, and p₀(g_k) = A₀(log g_k^{−2})^{p₀}. So g_j^{−2}ε₁² ≤ 2C(M)²(1 + β₀)²(k − j + 1)·4^{r+1}L²A₀²(log g_k^{−2})^{2r+2p₀}, and #4.55-0.1 bounds log g_k^{−2} by log(ḡ^{−2} + 8b′n + b′j(C) + C_W). With k − j + 1 ≤ k + 1 ≤ 8n + j(C), the product with L^{−(1−ε₀)n/12} is bounded in n, so the sup is finite.

## Consumers

- #4.54-0 and #4.55-1 change no bound. C_h's callers (Cauchy §6.2, §8.6, #C6.2.19-2) already list its dependence on j(C) and ḡ; r, b′, and C_W are fixed constants of the setting.

## Pre-check for r7 (lf-p13a2-20261107-r7, full round)

Gate answers, all yes:
- The changed lines (#4.51, #4.54-0, #4.55-1) are re-derived above. #4.51 changed only by taking Δ's definition, at its first use.
- The arithmetic and the citations (#1.7, #3.29-1) are re-checked.
- There is no new symbol, and the claims are unchanged. The wider implications, C_h's callers, are covered under Consumers.
- Linear order is kept: 13a1 is done, 13a2 runs next, and 13b waits.
- Relabelled at LF d7604c80f69f (table 29f7da24a7d9, LABELS 83db907f3cf4, verified). The spec is current, and the packet is built (argument 11,941 characters).

- Changed lines re-read: #4.54-0 (589 characters) and #4.55-1 (523). Since the r6 snapshot, Δ's definition moved into #4.51 (13a1 r7). The rest of the part is unchanged.
- I read the whole part (#4.51–#4.55-1) and found no gap.
- Definition check for spec_p13a2_r7.json: 0 conflicts (7 allowed).
- The argument is about 13.3k characters, under the 25k limit.
- No queued repair touches 13a2. The LF edits outside the part (#4.502, #4.521.3, #4.597, #4.609, #4.663, #4.668) are background.

## Repaired SHAs

LF ff32ad403ddb → … → 61466edebeb6. That SHA includes the 13a1 r7 repairs, the (3.43) A-radius removal, the C_ds rename in #4.597/#4.609 (it was C_F, which clashed with #4.328's C_F), the removal of the D-tags in #4.502/#4.663/#4.668, and the split of #4.521.3. Table 9ecb9616e8e5 and LABELS 4f889431c141 (fork, at 61466edebeb6) verified. The queued §4(d) long lines were then split at sentence boundaries (#4.593-1, #4.596-1-1, #4.596-1-2, #4.598-1, #4.600-1; bookkeeping): LF d7604c80f69f, relabel requested. Map #MD2.4.11.15-2 now cites #T4.50's r^{an}_k, 𝒫_k^{3/4}, and #MD2.2.6.170-7 (map 67f7b32fa4eb).
