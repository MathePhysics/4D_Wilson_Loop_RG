# Pair note triage: PC21a (R-step booking), with PC21b folded in

Note: WILSON_IT1_TWO_LOOPS_CAUCHY_2026_11_05.md, owned by the two-loops session.
Reviewed SHA (PC21a): 2e1475266d9c (frozen during the round); repaired SHA: d4cdc0edc4bd (82,857 bytes; was 82,822).
LF pin: 36c22ebe3cfa (labels 8a80856836c4), checked by hash. Table: 697a56eb4c81, checked by hash.

## Verdict of PC21a

One ERROR and four MINOR findings, so the round is not clean. PC21b (totals) was never launched; its lines changed with the repairs below and go into PC22.

## Repairs

| Finding | Severity | Repair (in place) | Lines |
|---|---|---|---|
| PC21a-1: a case-(a) group with a plain wrap(j) member is wrap(k), not an att(k, .) production | ERROR | -03 now restricts productions to groups with no carrier member and no wrap member; a group with a wrap member is wrap(k) (#278, #848), a carried wrap | #PC4.14.4-4.5.4-03 |
| PC21a-2: the T-step sentence of the root rule contradicts the rule | MINOR | sentence deleted; the R-step pointer kept inside the parenthesis | #PC4.14.4-4.5.1-00.1 |
| PC21a-3: the list of R-step places misses the untouched and split carriers; "verbatim" overstated | MINOR | fourth place is now "continues, whole or on its part D^0 (h(D) empty) while its other parts are members or in slots", growth at most 1 + C_s theta_k (#844); "verbatim" removed | #PC4.14.4-4.5.4 |
| PC21a-4: masses made at earlier R-steps are not in D2.6's Sigma A, so kappa does not pay them in a slot or block | MINOR | -01 splits the payment: D2.6 species by kappa (15.8(b)), masses rooted at R-step productions by the new term 2 sup M^R of -4.12, item 7's blocks by D2.7; -01.1 points to -01 | #PC4.14.4-4.5.4-01, -01.1, -4.12 |
| PC21a-5: the block's region is Y_i^~, not Y_i^+ | MINOR | Y_i^~ in -1.2 and -01.1 | #PC4.14.4-1.2, -4.5.4-01.1 |
| OPEN -04.1: the block's weighted mass in N | (own) | closed by a structural fact: every term of a group holding the block holds the block, an attached factor, so its gauged activity is 0; the comparison gas of #PC4.14.4-4 puts these groups at 0 too (as #430, #436 do for cross groups), and 7.4(a)'s bound holds there since it uses the activities only through the majorants and a cluster holding an activity 0 is 0. So the block's lineage enters no c^a, no N, no M^map; -04.1 deleted, the block removed from P^R | #PC4.14.4-4, -4.5.4-01.2 (new), -04, -04.2, -4.11 |
| symbol clash: C^R(j) against #PC5.2-4's cross constant C^R | (own) | renamed C^P(j) everywhere (no hit in the note, the table, or LF) | -04.2, -4.10.1, -4.10.2, -4.12, -4.12.1, -4.13.1 |
| totals after PC21a-4 | (own) | sup M^R at most (8/3) Sigma P^R by -4.10's recursion restricted to R-rooted terms; E + Sigma N + 2 sup M^R at most 3E + 8 C^P (d'+1); eps-bar_A read as 3 sup(eps^(2)_A + 3 C^P) | -4.12, -4.12.1, -4.13.1 |
| line rules | (own) | sub-lines merged into their parents: -02.1-1 into -02.1, -04.2-1 into -04.2, -4.13.1-1 into -4.13.1; -01.1 split at a sentence into -01.1 and -01.2 (it was 637 characters) | as listed |
| LF pin | bookkeeping | ec27d1b32902 replaced by 36c22ebe3cfa | #PC.1-1.2 |

## Pre-check

- Every changed line was re-read in the repaired file (lines 136, 141, 150, 157-168, 174-182).
- Grep of the removed tags (-02.1-1, -04.1, -04.2-1, -4.13.1-1) and of "C^R(": no hits left in the note; the only C^R is #PC5.2-4's own constant.
- Arithmetic. Sigma N at most (4/3)E + (8/3)C^P(d'+1) (-4.10.2). sup M^R at most 2(Sigma P^R + Sigma N^R/8) at most 2(1 + 1/3)Sigma P^R = (8/3)Sigma P^R. E + Sigma N + 2 sup M^R at most (7/3)E + (8/3 + 16/3)C^P(d'+1) = (7/3)E + 8C^P(d'+1), at most 3(eps^(2)_A + 3C^P)(d'+1). In -4.13.1, (4/3)(eps + 2C^P) at most 3(eps + 3C^P).
- Sources quoted and checked: #844 (h(D) empty: untouched on D^0, a member on its other parts, factor 1 + y^s_k at most 1 + C_s theta_k); #430 and #436 (cross groups at activity 0 in the pair's reference gas); D2.6 closure 7.4(a) (the KP tree bound with the majorants and the per-traversal sums Cρ̂); D2.7 item 7, 15.8(b)-(c); LF #5.39-#5.39-1.
- Lines: all of lines 130-190 are at most 600 characters; LF line endings kept.
- No OPEN item and no known weak point in the packet's lines.

## Restructure to the review workflow (after the repairs, before PC22)

Note now at 8b909fa9a898 (81,704 bytes, was 82,857 at d4cdc0edc4bd). Bookkeeping and deletions only; no bound changes.

| Change | Lines |
|---|---|
| roadmap and aside lines deleted (they restated where later sections compare what) | #PC.1.1, #PC.1-2, #PC.1-2.1, #PC2.5, #PC4.14.5 |
| tags put in reading order, internal-only tags only (tags cited by the N-loops note, the pair-factorisation note, or the BETA handover keep their names) | #PC2.1-5/-6 swapped; #PC4.14-4.6.1-4 in order; #PC4.14-6.3.1/-2 swapped; #PC5.4-2/-3 swapped, with #PC5.4-2.1 |
| -4.5.4 sub-lines renumbered: -01, -01.1, -01.2, -02, -02.1, -02.2, -03, -04, -04.2 become -1 to -9; the register lines -4.5.4-1, -4.5.4-2 become -4.5.5, -4.5.5-1 | #PC4.14.4-4.5.4-1 to -9, -4.5.5, -4.5.5-1 |
| -4.5.1 sub-lines renumbered: -00 becomes -1; -00.1 and -0 (one sentence split over two lines) merged into -2; -1, -2 become -3, -4 | #PC4.14.4-4.5.1-1 to -4 |
| a fact stated once: cross groups at activity 0 cited to #PC4.14.3; the doubled carry factor at most 3 cited to #PC4.13-1.2 | -4.5.1, -4.5.4-3, #PC4.2-2.5, #PC4.14-1b.5, #PC4.14-5.0.1 |
| symbol clashes with table #T4.40 (one loop's tau^w_K, D^w_K, a_w) and rows 137, 212 (e_i, H_i): the pair's are now tau^{w,x}_K, D^{w,x}_K, a^x_w, e^{cw}_i, H^{cw}_i; #PC4.2-2.2 names LF's tau^w_K, D^{w,LF}_K with #T4.40 | all uses |
| labels: labels_pair_cauchy.py (new) writes LABELS_PAIR_CAUCHY.md and checks one tag per line, unique tags, lines at most 600 characters, and that every #PC reference exists | 319 tags, all checks pass |

Every renumbered citation was re-read against the new tag's content. All tags cited by other notes exist, except #PC.0, #PC4.13-3, #PC4.13-5 and #PC4.9-3a, which only old entries of the BETA handover cite and which were gone before this restructure. Not changed: C_w is #893's (the two-loops note) and the table's C_w(ε₀) of #T4.35 is a different constant; the pair note writes C_w without an argument and cites #893 at its definition (#PC4.11.1).

## Outside this note (D2.7, owned by the LF session)

D2.7 15.8(c) pays the block's e^3 by the quarter and its e^{2 Sigma A} by kappa, then says that closure 5.0-5.5 "run verbatim" at Y_i. Closure 5.0's carry factor for the block is 1 + e^{c_W} w(B) Pi(1 + delta), and w(B) contains the reserve weight e^{nu_r sigma(B)} over the box Y_i^~. That costs nu_r sigma(Y_i^~), linear in d'_k(Y_i) + 1, and 15.8(c) does not name who pays it; kappa_k(Y_i)'s p_0^2(d'+1) term would cover it, as it covers the words' pieces there. The masses rooted at R-step productions inside the block's e^{2 Sigma A} are also not D2.6's. The pair note no longer depends on the block's mass, only on D2.7's carry of it.

## Handover

- 2026-11-06 12:22 GMT: PC21a triaged; all five findings and the OPEN -04.1 repaired in place; note at d4cdc0edc4bd. PC22 (booking and totals, one scope) written. Not launched: the user asked to pause before launching.
- 2026-11-06 (during PC22): LF now 039f871a34db (checked by hash; table unchanged at 697a56eb4c81). The changes are rewordings in LF #4.40–#4.42, which the pair note does not cite (it cites LF §5). Queued bookkeeping: re-pin #PC.1-1.2 to 039f871a34db after PC22.
- 2026-11-06 (during PC22): D2.7 now 7323426aafcf. The LF session repaired both 15.8(c) points: the block's weight e^{ν_rσ_k + (3/8)ν_e·ext + c_W} is paid by κ_k(Y_i)'s p₀²(d′+1) term and the "≤ ¼p₀(g_k)" margin, and 15.3 enlarges κ's per-step summand at each R-step n by c^R_n(d′_n+1), c^R_n := O(1)e^{−p₀(g_n)/2} ≥ twice 15.6(e)'s charge (carry factor 2), which pays the R-made masses in e^{2ΣA} (15.8(b)–(c)). Re-derived against the D2.7 text: it holds. Queued for the pair note after PC22 (the note is frozen): (1) #PC4.14.4-4.10.1 says D2.7 bounds the R-step productions "within Res(Z) (15.6(e), 15.8)", which should now read "by the R-step summand of κ (D2.7 15.3)"; (2) #PC4.14.4-4.5.4-1 and -4.5.4-2 pay the R-rooted masses in a slot or block by the pair note's own 2 sup M^R, which now duplicates D2.7 15.3's payment, so cite 15.3 and drop 2 sup M^R from #PC4.14.4-4.12. That returns ε̄_A to 3 sup(ε^{(2)}_A + C^P) (E + ΣN ≤ (7/3)E + (8/3)C^P(d′+1)), with -4.12.1 and -4.13.1 to match.
- 2026-11-06 12:48 GMT: PC22 launched at the user's "Launch" (note 8b909fa9a898, scope_pairCauchy_PC22.md, run_referee_beta_scoped.ps1, opus-5-5 xhigh). The note is frozen while it runs.
- 2026-11-06 12:46 GMT: note restructured to the review workflow (section above), now 8b909fa9a898; LABELS_PAIR_CAUCHY.md generated; PC22 scope rewritten with the new tags. Paused before launch at the user's request.
- 2026-11-06 12:40 GMT: at the user's request, the D2.7 15.8(c) point above was sent to the LF session (block's reserve weight; masses rooted at R-step productions inside e^{2ΣA}).
