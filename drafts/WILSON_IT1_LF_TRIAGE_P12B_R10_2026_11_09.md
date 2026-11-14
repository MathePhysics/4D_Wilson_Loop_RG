# Triage of p12b r10 (lf-p12b-20261109-r10, 9 Nov 2026)

**Verdict.** Not clean: one minor finding (m1, #3.70-5-1) and seven trivia. There are no fatal or serious findings. It was a narrow round on the lines changed since r9 and their consumers. The next round of part 12b can be the first clean one; a full round must follow it.

## Repairs (in place)

| Finding | Words at stake | Repair |
|---|---|---|
| m1, #3.70-5-1 and claim (i) | "on the others because these are there configurations of Bałaban's supports at these constants" | Correct: a term also carries failed tests, which hold at t, not at (1 + 2κ_s)t. So a configuration with a failed test in (t, (1 + 2κ_s)t] lies in no support of Bałaban's with that geometry. #3.70-4 now says the configuration passes each passed test below (1 + 2κ_s) times its sharp threshold and that its failed tests hold at t as lower bounds (#3.48). #3.70-5-1 now says that on the other domains the configurations satisfy the passed tests of his supports at these constants, and that his spaces contain the real configurations satisfying these passed tests, since the conditions of (1.64)–(1.69) are upper bounds which his supports supply only through passed tests (p.191 l.49–51; inferred, not printed). This is the referee's corrected statement. |
| t1, #3.76 | #CP.13 outside the permitted background | Spec only: the next spec lists the Cauchy note's #CP.13 as permitted background. |
| t2, #3.84-1.1 against #3.85.1 | CMP98 (15) against RG I (0.4)/(0.12) | #3.85.1 now adds that the CMP98 (15) average of #3.84-1.1, RG I's "definition introduced in [12]" (p.252 l.34), reads the same contours and so is as local. |
| t3, #3.85.1-1 | the case of bonds not meeting □^{∼4} left implicit | Now stated: on the other bonds the averages read only k-blocks off □^{∼4}, whose bonds miss Ω_1 by dist(Ω_1, Ω_0^c) ≥ LξM₁ (CRE p.256 l.61, read). |
| t4, #3.97 | χ^{(j−1)c}(R_j) and the second function of (1.28) not named | #3.97 now names 1 − χ′_m "with both functions of LFR I (1.28)" (p.381 l.29) and says that the fluctuation cutoff χ^{(j−1)c}(R_j) is sharp (p.380 l.43–46, #3.21). Both were read. |
| t5, #3.97-1 | LFR I (1.83)–(1.87) re-used with the factor R_j (p.382 l.35–36) | Named, with "whose O(1) carries 1 + κ_s as in #3.72". "Both absorb" became "All absorb". Read at p.382 l.33–36. |
| t6, claim (vii) | its list omits #3.61 | Spec only: the next spec's claim lists #3.61. |
| t7, #3.95 and #3.96-1 | range #C8.6.5–#C8.6.8-1 | Now #C8.6.5–#C8.6.8-3 in both lines. #C8.6.8-3, the complex-class bound, uses the same lower bound of p.358. |

## Size: the χ_{k,Λ} derivation moved to balaban_proofs/

- After these repairs the part measured 26.7k characters, and its full round needs ≤ 25k.
- #3.84–#3.90 derive what LFR II p.378 l.10 states without proof ("This is clear for χ_{k,Λ}"). That is a re-derivation of Bałaban's work, which by the workflow goes to balaban_proofs/ with the statement and the pointer kept in the note.
- They were moved verbatim, tags kept, into balaban_proofs/BP_LFR2_CHI_K_LAMBDA.md. The copy was checked line by line against the LF block (17 lines, 0 differences, indentation shifted by 6).
- #3.83 keeps the tested quantities. The new #3.83-1 states the result: on the first-class components, those carrying the small-field function χ_k((Ω_k^{∼4})^c) of p.378 l.4–6 (checked in the print), |U_{k,Z}(∂p) − 1| < 2ε_kη², so χ_{k,Λ} = 1 there with the room 2/(1 + κ_s) of (1.75). It points to the BP file.
- The LF citations of the moved tags (the lines of #3.26's paragraph, §4's #3.84-1 and #3.84-1.1 uses, and the three §4/§0 uses of #3.85–#3.85-1) now name the file; this is bookkeeping.
- Also deleted: #3.68-3's last sentence, a dead-route remark ("A single width κ_s for all n does not work, …").
- Part 12b (#3.63–#3.100-1) now measures 19.8k characters, and BP_LFR2_CHI_K_LAMBDA.md measures 7.7k. CR is 0, and no line is over 600 characters.

## Rounds

- **Part 12b** (#3.63–#3.100-1 without #3.84–#3.90): the next round, r11, may be full (≤ 25k). If r11 and r12 are clean and r12 is full, the part is done.
- **Packet 12b-bp** (BP_LFR2_CHI_K_LAMBDA.md, #3.84–#3.90): r8 and r9 (full) were clean on these lines. Since then #3.85.1, #3.85.1-1, and #3.86-1-1 changed; r10 found no minor finding in them, and the t2 and t3 rewordings followed. Because r10 was not clean as a round, the block gets its own two rounds: a narrow or full round, then a full round.
- One referee at a time; packet 14 also waits.

## Pins

LF 407d8571498c, BP_LFR2_CHI_K_LAMBDA.md c7167759d4de, table ef5624a45a08 and labels 7c21b96e4753 (before the fork's relabel for these edits). Messages: the table fork got the moved tags, table rows 607 and 624, and the c_T → c_{av} rename. The two-loops session got BP_TL_EVAL_POINTS.md's citation of #3.90.

Written 2026-11-09 03:25.

## Pre-check of lf-p12b-20261109-r11 (full)

- **Changed lines re-read** in their final form: #3.68-3, #3.70-4, #3.70-5-1, #3.83, #3.83-1, #3.85.1 and #3.85.1-1 (now in the BP file), #3.95, #3.96-1, #3.97, and #3.97-1.
- **Displays checked against the print** (corrected transcriptions):
  - LFR I p.190 l.13–54 and p.191 l.1–49: the spaces' conditions (i)–(iii) are upper bounds.
  - CRE p.261 l.5–40: (2.34)–(2.39), CRE's spaces.
  - LFR II p.378 l.1–18: the decomposition 1 = χ_k((Ω_k^{∼4})^c) + χ_k^c((Ω_k^{∼4})^c) and the first class.
  - LFR II p.380 l.43–46, p.381 l.27–31, and p.382 l.33–38.
  - CRE p.256 l.58–63.
  - RG I p.252 l.28–35 and p.254 l.1–12.
- **Uses grepped:**
  - every citation of #3.84–#3.90, re-pointed in the LF, listed for the table fork, and sent to the two-loops session for BP_TL_EVAL_POINTS.md;
  - "first class", consistent with #3.91 and BP #3.84;
  - #C8.6.8-3, which exists and uses p.358.
- **Restatements:** #3.83-1 restates only the result that #3.89–#3.90 derive, as the pointer's statement. #3.68-3's dead-route sentence is deleted.
- **Whole part read** (#3.63–#3.100-1) on 9 Nov 2026 during this triage. No other gap was found.
- **Size:** 26.7k before the move and 19.8k after. No line is over 600 characters, and CR is 0.
- **Spec:** specs\spec_p12b_r11.json. Its definition check gives 0 conflicts (1 allowed); the allowances for B, W, and X were dropped with the move. The t1 and t6 trivia are handled in the spec: #CP.13 is in the permitted background, and the claim lists #3.61.
- **Order:** launch after the table fork's relabel at LF 407d8571498c.
