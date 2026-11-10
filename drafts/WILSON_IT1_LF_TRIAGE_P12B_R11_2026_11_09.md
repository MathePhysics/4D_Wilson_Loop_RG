# Triage of p12b r11 (lf-p12b-20261109-r11, 9 Nov 2026)

**Verdict.** Clean. There are no fatal, serious, or minor findings, and six trivia. It was a full round of part 12b (#3.63–#3.100-1 without #3.84–#3.90). It is the part's first clean round. r12 must be full and clean for the part to be done.

## Repairs (in place, rewordings)

| Finding | Words at stake | Repair |
|---|---|---|
| t1, #3.70-2 | "with q₀ > p₀ (#T1.2) exceeds it for γ small" | Now "exceeds it for γ small by the project's choice q₀ > p₀ (#T1.2; CRE (2.28) asks only for integers greater than 1)". The table's stage 0 requires q₀ > p₀ + 3r anyway (#T1.2). I tried an argument at q₀ = p₀ through C₀ large and withdrew it: it needs C₀ to be chosen after A₀, an order the table does not record. |
| t2, #3.70-5-1 | the inferred reading could be replaced by a direct α_{0,m}/ε_m check | No change. The referee calls this not a defect. The line already states the reading as what Bałaban's bounds on (1.63) require, labelled "inferred, not printed". A direct check would need the printed passed regularity of the real configurations on the domains (iii) of (1.68)–(1.69), on m < h, and outside Z. LFR I pp.190–191 (read in full) do not print it. |
| t3, #3.77 | (1.94)'s inputs not named | #3.77 now names (1.94): B₃δ′_k + L^{−(k−h)}O(1)B₃³B₅M⁶ε_k < αε_h through p₁ < p₀, γ small, and N large (p.198 l.49–57, read), so that it absorbs 1 + 2κ_s. |
| t4, #3.82-2 | the radial cutoff's extra 1 + κ_s | The sentence now adds that where the radial cutoff M₀A₀p₀(g_k) enters (p.357 (1.6), and the A₀p₀(g_k) of p.363), it gains a further 1 + κ_s on the support of χ̄(Λ), as #3.94 uses. |
| t5, #3.97 | "1 − χ′_m with both functions of LFR I (1.28)" | Now "1 − χ′_m (LFR I (1.27)), the second function of LFR I (1.28), a complement of a product of the sharp cutoffs (1.9)". Checked against LFR I p.182 l.52–55, p.183 l.9–13, and LFR II p.381 l.25–29. The line then measured 659 characters, so it is split at the sentence "1 − χ′ is sharp, …" into the new sub-line #3.97.1. |
| t6, #3.100.1 | "constants changed by the factor 1 + 2κ_s" | Now "the factor 1 + 2κ_s being absorbed by the constants inside their proofs". |

## Pre-check of lf-p12b-20261109-r12 (full)

- **Changed lines re-read** in their final form: #3.70-2, #3.70-3 (unchanged after the withdrawn t1 variant), #3.77, #3.82-2, #3.97, #3.97.1, and #3.100.1.
- **Displays checked against the print:** LFR I (1.27) (p.182), (1.28) (p.183), (1.94) (p.198), and pp.190–191, (1.64)–(1.69); LFR II p.381 l.24–32.
- **Uses grepped:** #3.97.1 is new and unique. No tag was renamed. "q₀ > p₀" agrees with the table's q₀ row.
- **Size:** 20.3k characters (19.8k before). The growth is in the trivia rewordings. No line is over 600 characters (the largest is 598). CR is 0, and there are no trailing spaces.
- **Whole part:** read for r11's pre-check on 9 Nov 2026. Since then only the lines above changed.
- **Spec:** specs\spec_p12b_r12.json, the r11 spec with the rev, the LF SHA, the prior review, and the provenance updated.
- **Order:** launch after the table fork's relabel at LF d598eaace460.

## Pins

LF d598eaace460 (407d8571498c at r11). Cauchy note e5112202b24f; BP_CMP98_ADJOINT_AVERAGING.md 474f89c50ed0; BP_LFR2_CHI_K_LAMBDA.md c7167759d4de. The table fork was sent the LF SHA and the new tag #3.97.1.

Written 2026-11-09 03:48.
