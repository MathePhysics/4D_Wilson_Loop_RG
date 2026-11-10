# Pair note triage: PC24 (R-step booking and totals, full round)

Note: WILSON_IT1_TWO_LOOPS_CAUCHY_2026_11_05.md, owned by the two-loops session.
Reviewed SHA: c71d1a0499ba, with the two-loops note at 4b0b4faae66c (both frozen during the round). Repaired SHA: b5f6615367a2 (82,965 bytes; was 82,743); two-loops note unchanged.
Referee: referee_cli_20261106-143323_scope_pairCauchy_PC24.json (opus-5-5, $4.17), section in reviews\REVIEW_LOG.md. The referee ran no shell command.
LF pin: 21cfe3f3a8b6 at review, now a33a242b3be4 (checked by hash). Table 88a6dcbd277a. D2.7 55e50090afd6.

## Verdict

No ERROR. Two MINOR findings, and the numbers stand in both, so the round is not clean. PC23-1 is resolved for the q = 0 dev parts, PC23-2 and PC23-3 are resolved, and so is PC23's own point on N(Y_i).

## Repairs

| Finding | Severity | Repair (in place) | Lines |
|---|---|---|---|
| PC24-1: the word pieces whose set K contains a second-class Y_i (D2.7 15.5(i), att(k, Y_i) by 15.6(e)'s rule, charged to Y_i in 15.8(c)) are neither put to 0 nor productions; their mass is a polylog times (d'+1), with no e^{-p0} | MINOR | -4.5.4-3 adds them to the factors whose groups are put to 0 (the block, these word pieces, and the q = 0 dev parts), so they enter no c^a, no N and no M^map; the new -4.5.4-3-1 carries them with 15.8(c)'s bound, paid at Y_i by 15.8(c) | #PC4.14.4-4.5.4-3, -4.5.4-3-1 |
| PC24-2: item 7's block is carried by D26 5.0 with the factor 2 (15.8(c)), but -4.5.4-3 gave it item 5(b)'s bound | MINOR | -4.5.4-3-1: item 5(b)'s bound for the block and 15.8(c)'s for the word pieces, each doubled by D26 5.0's carry (15.8(c) quoted), which costs log 2 within 15.8(c)'s margins for small g_k; #815's bound for the clusters, which already has the factor 2 | #PC4.14.4-4.5.4-3-1 |
| (consumer) -4.5.4-1's "the factors of -4.5.4-3 as there" | (own) | now cites -4.5.4-3-1, where they are paid | #PC4.14.4-4.5.4-1 |
| (own, found in the pre-check for PC25) D2.7 15.4(iii)'s terms of E^{R,∂}_k(ℓ) are att species of the post-R bracket, attached per component (15.8), and so carried lineages, but were not among the productions | (own) | -4.5.4-7 lists them as productions, charged to the component 15.4(iii) names; -4.5.4-8's e^{-p0/2} is now said of the groups and the clusters only; -4.5.4-9 bounds them by 13^d m^R_k at most O(1)13^d e^{-p0(g_k)/4} per MR_k-cube of Z (15.4(iii), N(Y_i) included there), which is P^R's form, so C^P(j) is unchanged; -4.10.1: D2.7 pays them within Res (15.8); -4.5.4-9's last sentence moved to the new -4.5.4-9-1 (line length) | #PC4.14.4-4.5.4-7, -4.5.4-8, -4.5.4-9, -4.5.4-9-1, -4.10.1 |
| LF pin | bookkeeping | 21cfe3f3a8b6 replaced by a33a242b3be4 (LF #0.20.1, #1.2 and #3.16 to #3.62-1 changed; neither note cites them) | #PC.1-1.2 |

## Pre-check

- D2.7 55e50090afd6 re-read: 15.5(i) (l.175: "a set K containing a second-class component Y_i gives an att(k, Y_i) insertion by 15.6(e)'s scope rule, charged to Y_i in 15.8(c)"), 15.6(e) (l.187), and 15.8(c) (l.191: the cost exp(4C_alpha(MR_k(d'_k(Y_i)+1) + 2M delta^{-1}) delta^{-1}), "att(k, Y_i), carried by D26 5.0 with theta := 0", the d'-parts paid by kappa_k(Y_i)'s p0^2(d'+1) term for small g_k). Doubling a bound multiplies it by 2, i.e. log 2 in the exponent, which fits within these margins for small g_k.
- The word pieces lie in no polymer and no group of 15.6, so they are att lineages from step k on. Putting every group that holds one at any depth to 0 is the rule already used for the block, and an untouched member adds nothing (-4.4). So they enter no c^a and no N.
- Every use of the -4.5.4-3 tag grepped: #PC4.14.4-4 (the groups put to 0), -4.5.4-1 (now -4.5.4-3-1), -4.5.4-7 (excepted). Uses of item 5(b) in the two-loops note (#783 and others) concern step k only.
- labels_pair_cauchy.py: 320 tags, all checks pass. Changed lines: -4.5.4-1 at 574 characters, -4.5.4-3 at 453, -4.5.4-3-1 at 325. LF line endings.
- LF #5.39-3's list omits the same word pieces and counts the block with mass 1 where its carried bound can be 2. Both points are LF's; sent to the LF session at 14:50 GMT.

- 15.4(iii) re-read (D2.7 l.173: the rooted sum of the cluster terms through an MR_k-cube of Z^{~6} is at most m^R_k := O(1)e^{-p0(g_k)/4}, N(Y_i) included at Y_i's cubes, and the per-step cost per MR_k-cube of Z at most 13^d m^R_k; l.191: "the terms of E^{R,∂}_k(ℓ) attached per component by 15.4(iii)", paid "within Res"). Counting them as productions only adds to Sigma P, and their bound has C^P's form, so -4.10 to -4.13.1 are unchanged.
- After the own repair: pair note 01c05a30d80f (83,226 bytes), 321 tags, labels pass (one 646-character line split first). Changed lines -4.5.4-7 at 588 characters, -4.5.4-8 at 556, -4.10.1 at 383.

- LF now 640c0fddd9ad (checked by hash). The LF session repaired both points sent at 14:50: #5.39-3 lists the word pieces, the new #5.39-3-1-1 bounds them by 2c^w_n(d'+1) with a polylog c^w_n, #5.39-3-2 gives the block mass 2, and #5.39-3-3's eps^R_A gains 2c^w_n, a power of log g_k^{-2}. Re-read: it holds (the +1 covers the block's 2, as 2 is at most 2|Y_i|_n). #PC4.14.4-4.12.1's reading 3 sup(eps^(2)_A + C^P) + eps^R_A is still an upper bound, and every use of eps-bar_A tolerates a power of log (#PC6.4.1-1, LF #5.66-2). #PC.1-1.2 re-pinned to 640c0fddd9ad. Pair note dfc8ee5b72bc (83,226 bytes), 321 tags, labels pass.

## Handover

- 2026-11-06 (during PC25): LF now 462dc146eba3 (checked by hash). The changes are in LF #4.43 (VAR Sect. F's representation, C(M) ≥ 4C_X(M), split into #4.43-1) and #4.45 (pin p.358 l.19-22). Neither note cites LF #4.43, #4.45 or #4.51 (case-sensitive grep), so nothing it cites changed. Queued bookkeeping for after PC25: re-pin #PC.1-1.2 to 462dc146eba3.

- 2026-11-06 15:20 GMT: PC24 triaged and repaired, with the own E^{R,∂} repair; pair note 01c05a30d80f, two-loops 4b0b4faae66c. PC25 (full round, the same lines plus -4.5.4-3-1 and -4.5.4-9-1) written and launched under the user's standing "Continue until everything has been closed and reviewed".
