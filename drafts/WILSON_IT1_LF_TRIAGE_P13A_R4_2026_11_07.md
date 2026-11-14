# Packet 13a r3 Result and r4 Repairs (7 Nov 2026)

lf-p13a-20261107-r3 (LF edbeac67699f, table cd814aac5ad0, labels 328e517d7d93) found no fatal and no serious findings, one minor finding (m1), and two trivial ones (t1, t2). It confirmed that r2's m1–m6 are repaired. The round is not clean, so 13a's clean count stays 0. All three findings are repaired in place. r4 is a full round of 13a, #4.43–#4.55-1, with r3's review as its prior.

## Open

None.

## Repairs (in place)

| Item | Line | Repair |
|---|---|---|
| m1 | #4.50-1.1.1, new #4.50-1.1.1-1 | The reason given for the k-uniformity of the first (T-Λ) threshold was "ε_k and R_k are functions of g_k (CRE (2.4), (2.5))". That is false, since R_k = R̄(K − k) (the Cauchy note's #CP.13). It is replaced by the bound 2(log ḡ^{−2})^r ≤ R̄(K − k) ≤ 2^{r+1}L(log g_k^{−2})^r for each run, with its own g_k (#CP.13 with bn ≥ 0, #3.29-1). This gives e^{−R_k} ≤ e^{−2(log ḡ^{−2})^r} and e^{−(δ₀/8)MR_k} ≤ e^{−(δ₀/4)M(log ḡ^{−2})^r}. Since R_k and ε_k are each the larger of the runs' values (#4.43-1), #4.50-1.1.1-1 takes g_k from the run with the larger ε_k. The runs' g_k^{−2} differ by a factor ≤ 2 (Cauchy #C5.7-3–#C5.7-8), so M⁶R_kε_k ≤ 2^{2r+1}LA₀M⁶g_k(log g_k^{−2})^{p₀+r}. That is small for γ small, since both couplings are ≤ (1 + β₀)γ (Cauchy #C5.7-5) and g(log g^{−2})^s increases for g < e^{−s}. |
| t1 | #4.48-3 | The choice of ζ₀ now states 0 ≤ ζ₀ ≤ 1, which "with a weight ≤ 1" in #4.48-3.0.2 uses. |
| t2 | #4.45, new #4.45-0, #4.48-3 | The splitting of the form is moved to the new #4.45-0, for line length. Each weighted form is identified with twice its own second-order Taylor coefficient, because V(ζ₀, ·) of (1.2) is "at least of third order" (LFR II p.357 l.9), as RG I's V is for the weight 1 (p.266 l.39). #4.48-3 now cites #4.45-0. |

## Checked

- LFR II p.357 l.9, verbatim: "the function V is at least of third order in the argument".
- RG I p.266 l.32 and l.39–42.
- The Cauchy note's #CP.13–#CP.14 (R̄(n) ≥ 2(log(ḡ^{−2} + bn))^r) and LF #3.29 (ε_k = g_kp₀(g_k), p₀(g) = A₀(log g^{−2})^{p₀}) and #3.29-1 (R_k ≤ 2^{r+1}L(log g_k^{−2})^r).
- The arithmetic: 2(δ₀/8) = δ₀/4. (g′)^{−2} ≤ 2g^{−2} gives log(g′)^{−2} ≤ log 2 + log g^{−2} ≤ 2log g^{−2}, so R_k ≤ 2^{r+1}L·2^r(log g_k^{−2})^r. And d/dg[g(log g^{−2})^s] = (log g^{−2})^{s−1}(log g^{−2} − 2s) > 0 for g < e^{−s}.
- The Cauchy note's #C5.7-3–#C5.7-8 (the runs' couplings at aligned scales, (3/2) and ½ factors) and #C5.7-5 (couplings in ]0, (1 + β₀)γ]). Both are in the packet's permitted background.
- On the user's question, the first m1 repair was rechecked and corrected before launch. It had used one g_k for R_k and ε_k, which are each the larger of the two runs' values. It had also cited #4.55-0.1, a forward citation, and ḡ as the bound on g_k. It now uses the run with the larger ε_k, the Cauchy note's #C5.7-3–#C5.7-8 and #C5.7-5, and (1 + β₀)γ.
- t1 is consistent with the Cauchy note's #C8.6.4, which uses 0 ≤ ζ₀ ≤ 1.

## Pre-check, lf-p13a-20261107-r4

- Changed since r3: #4.45, #4.45-0, #4.48-3, #4.50-1.1.1, #4.50-1.1.1-1. Each was re-derived against the sources under *Checked*.
- New symbols: none. ḡ, γ, A₀, p₀, r, β₀ and R̄ are the note's or the Cauchy note's existing symbols; 0 definition conflicts.
- Linear order: #4.45-0 cites only Bałaban; #4.48-3 cites the earlier #4.45-0; #4.50-1.1.1 cites #CP.13 and the earlier #3.29-1; #4.50-1.1.1-1 cites only CRE and the Cauchy note. None cites a later tag.
- Relabelled (48aa1d1831b3), spec current (LF 0e0a28f49094), packet built.
- Every changed line was re-read. Lines #4.45, #4.45-0, #4.48-3 and #4.50-1.1.1 are ≤ 600 characters.
- Callers: #4.50-1.1.1 is cited nowhere outside the LF note, the labels file and the triage files. #4.45 is cited by #4.48-4 ("the form of #4.45"), where the form is still defined, and by table l.95 for κ_Λ, which is in #4.45-1 and unchanged.
- The new tag #4.45-0 is sent to the table fork for the labels file.

## SHAs

- LF edbeac67699f → 77b17b229d29 → 0e0a28f49094 (the m1 recheck, with the new tag #4.50-1.1.1-1).

## Status

The fork relabelled to 48aa1d1831b3, with #4.45-0 and #4.50-1.1.1-1 indexed, and the table is unchanged at cd814aac5ad0. spec_p13a_r4.json is built at LF 0e0a28f49094: 20,140 argument characters, 0 definition conflicts. The earlier unlaunched build at 77b17b229d29 was removed. The Cauchy note's #CP.14 and RG I p.266 are added to the permitted background, and Q1–Q3 name the weight splitting and the k- and K-uniformity of (T-Λ). Launched headless on 7 Nov 2026 on the user's "Continue". Its files are frozen while it runs. 13b's r2 findings wait until 13a is done.
