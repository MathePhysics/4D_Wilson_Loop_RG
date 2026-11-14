# LF packet 12b, round 3 (full): triage

Review: verification/isolated_reviewer/reviews/lf-p12b-20261106-r3/review.md. Under review: LF 2cf459f08800 (labels bdd692ad0d20), table 1e392e405632.

## Verdict

No fatal or serious finding. There are four minor findings and three trivia, so r3 is not clean. The referee found all eight r2 findings repaired, and found the #3.86-1 repair (the reasoning of REG (1.65)) correct. Every finding was checked against the print and repaired in place.

## Repairs

- **m1 (#3.82-1, p.366).** The corrected transcription has M^{14}, with M⁹ the printed misprint (LFR2 p366_corrected.tex l.9; tnote in p366.tex l.12: the left-hand side has M⁴·M^{10}). The entry now reads "M^{14}R_k⁷ε_k² (printed M⁹; the left-hand side has M⁴·M^{10})". The bound is used at fixed M for γ small, so no conclusion changes.
- **m2 (#3.64).** The wording dropped the factor of the printed inequality (LFR I p.184 l.4: B₃exp(−δ2M₂R_j)22d²ε_j < (β/10)ε_j). It now reads "the boundary-layer bound B₃e^{−2δM₂R_j}22d²(1 + 2κ_s)ε_j < (β/10)ε_j of p.184 l.4 holding for γ small".
- **m3 (#3.99).** The activity term Σ_{j≤K′}CL^{K′−j}ρ̂_je^{−cN^{(j)}_min/M} of the continuum note's (5.3) (#ND.5.4), which is 2C sup_jρ̂_je^{…} in its (8.1) (#ND.8.1), was not classified. It is a bound of D(K′)(ii) and holds with the soft tests by (R-s)(b) (#3.45). That sentence and the B_LF sentence are now one sentence. The line reached 753 characters and was split into #3.99 and #3.99-1. The ranges in #3.48 ("#3.48–#3.99-1") and #3.100-1 ("#3.49–#3.99-1") were re-pointed to match.
- **m4 (the claim's "order condition of the Cauchy note's §8.6").** This was spec wording, not note text. The r4 claim now states the ordering: C(M) ≥ 8(1 + κ_s)max(M₀, C_X(M)) is chosen after M₀ (#4.152), and the polydisc contains the denominator's domain (#3.96–#3.96-1-1). Question 4 is reworded to match.
- **Trivia.**
  - #3.79 now reads "for κ_s < 5/48 and γ small, the factors (1 + L^{−j}αε_j)² adding O(ε_k)".
  - #3.94 now reads "extend".
  - #3.97 now names the gains of χ^c_j(P_j) and χ′^c_j(Q_j) (LFR II p.380 l.31–40), which enter through the minimum of p.381 l.4–5, beside those of p.381 l.15–32.

## Pre-check for lf-p12b-20261106-r4

- **Changed tags:** #3.64, #3.79, #3.94, #3.97, #3.99, #3.99-1, #3.100-1, and the p.366 entry of #3.82-1. #3.48 (in 12a, done) was re-pointed only.
- **Each line re-read.** #3.64 is 424 characters, #3.79 464, #3.94 476, #3.97 445, #3.99 442, #3.99-1 320, and #3.100-1 563.
- **Prints checked.** LFR I p.184 l.4. LFR II p.366 (corrected l.9 and tnote), p.380 l.31–46, and p.381 l.1–8. Continuum note #ND.5.4 (line 158), #ND.5.6 (line 164), and #ND.8.1 (line 267).
- **Arithmetic.** #3.79: 2(1 + κ_s) + 5/12 < 21/8 iff κ_s < 5/48, with O(ε_k) taken up by γ small.
- **Consumers.** #3.47 cites "the factor 1 + 2κ_s of #3.99", which is still in #3.99. No other line cites M⁹ or the old #3.64 wording.
- **Size.** The packet is 19.3k (r3: 19.0k); the growth is the m3 clause and the m1 note. There are 0 definition conflicts.
- **Pins.** LF a4a5e1332d54 (labels 644901ba13c6), table 1e392e405632, Cauchy 4138f0908f6d.
- **Recheck at the user's go ("Recheck everything and launch").** The pins still match: LF a4a5e1332d54, table 1e392e405632. The changed lines were re-read in the built packet, and the reviewer's (1 + L^{−j}αε_j)² of #3.79 was checked against LFR I p.200 l.6 and l.22–23. #3.99-1's terms match continuum note line 158 and line 267. No line of the Cauchy note, the table, D2.7, or the continuum note cites a changed tag. The two-loops session re-pointed TL #920 to #3.99-1, and TL #910's sentence stays in #3.99. The rest of the packet is unchanged since the line-by-line read before r3.
- **Status.** Launched.
