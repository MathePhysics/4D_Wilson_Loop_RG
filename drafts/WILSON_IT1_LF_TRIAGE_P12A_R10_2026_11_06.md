# LF review, part 12a, round 10: triage and repairs (6 Nov 2026)

Review: `verification/isolated_reviewer/reviews/lf-p12a-20261106-r10/review.md`, LF 00a7d8553b7f, focused on the round-9 repairs. Result: 0 fatal, 0 serious, 0 minor, and 6 cosmetic (c10-1 to c10-6). **Clean.** This is the first clean round. r11 is the full round, as one packet of the whole part.

| Remark | Line | Repair |
|---|---|---|
| c10-1 | LF #3.28-2, #3.28-3 | (1.55) is cited at LFR I p.188 l.4–8. (1.59) is (1.27) after #3.69's change of variables. |
| c10-2 | LF #3.28-3, #3.39 | χ_k^{(n+1)} is 1 on the support of χ_k^{(n+2)} and the next step's other tests (#3.68-2–#3.68-3). #3.39 has the same reading. |
| c10-3 | LF #3.28-6 | "only through χ_k^{(n+1)}, removed as above, and analytic terms". |
| c10-4 | LF #4.634 | Its pointer (#3.28-2, #3.32) is right again, since the coupling part of (1.59) is now in #3.28-2. |
| c10-5 | spec claim (c) | "(1.55) by its threshold, and (1.59) by coupling parts". |
| c10-6 | LF #3.28-5 (new) | No later operation tests V_j on the excluded components. The step's later operations leave them unchanged (LFR I p.181 l.17–19). A later 𝐑-operation at k″ acts on a component containing them only if no step from k″ − N̄(K − k″) on created their large fields (p.177 (ii)). So j < k ≤ k″ − N̄(K − k″), and that operation reopens only the scales ≥ k″ − N̄(K − k″) ((1.2), p.178 l.4–7). |

Compression, done with the same pass:
- The old #3.28-3 (radial monotonicity) is merged into #3.28-2. The bound needs only |e^{ig^AB} − e^{ig^BB}| ≤ |g^A − g^B||B|, so the ray argument is deleted.
- The (1.5) sentence of #3.28-4 is replaced by the citation of (1.29) at p.183 l.22–34.
- The old #3.28-7 is folded into #3.28-6.
- #3.29 (678) is split at a sentence boundary into #3.29 and #3.29-1.
- Lines #3.28-2–#3.28-6 total 2,250 characters, against 2,284 before, now including c10-6. All of them are ≤ 600, and so are the part's other lines.

Wider implications:
- The tags #3.28-2–#3.28-7 are cited only in LF #3.36 (now #3.28-3–#3.28-6) and in #4.634 (#3.28-2, still right). Neither Cauchy, nor the table, nor D2.7, nor the two-loops note, nor the pair note cites them.
- "radial" elsewhere means §2(b)'s radial shells, which are unaffected.
- #3.28-5 uses N̄(K − k″) as #3.38-1 and #CP.13-1 do, and j ≤ k − 1, the cascade's integration scales (𝐓^{(j)}, j = k − 1, …, h, (1.2)).

Other edits in this session, made between rounds:
- At the two-loops session's request: λ → λ_𝔏 in #T4.42 and in D2.7 15.8-1, C_s → C_ϑ in D2.7 15.5 and 15.8, and #T4.42's link payment changed to "the first eighth of the links' quarter (two-loops #629-4)".
- D2.7 15.8-1(6) and (6-2) now pay the links from the first eighth of their quarter.
- In D2.7 15.8, l.841, l.844, and l.286 are now cited as tags.
- None of this is in part 12a.

Hashes: LF 31dff43f304e, labels cbb65e626b93, table f977a24fa070, Cauchy 8eb6206f0587, D2.7 dbe7f99a98b6.

## Pre-check for lf-p12a-20261106-r11

Spec `specs/spec_p12a_r11.json`, lf_sha 31dff43f304e, the full round of the whole part. Definition check: 0 conflicts (1 allowed). Packet: 27,833 argument characters. That is over the 25k limit; the user decided not to split for this round.

Changed LF tags (the gate's list, 9): #3.28-2, #3.28-3, #3.28-4, #3.28-5, #3.28-6, #3.29, #3.29-1, #3.36, #3.39. Each was re-read and re-derived.

Checks:
- I read the whole part myself before this full round: #1.1–#1.2-1, #3.16–#3.62-1, #5.6, and #5.66–#5.66-2. I found no gap. The redundancies found were removed as listed above.
- Citations re-read in the transcripts: LFR I p.177 (i)–(ii), p.178 (1.2), p.181 l.16–19, and p.188 l.4–43. #3.68-2–#3.68-3 and #3.69 were re-read in LF.
- New symbols: k″ (a later 𝐑-step, local to #3.28-5). No new definitions.
- Quantifiers: in #3.28-5, j < k ≤ k″ − N̄(K − k″) holds under either reading of (ii)'s window of N steps.
- Every queued repair is applied. Linear order is kept: 12a r11, then 12b r3.
