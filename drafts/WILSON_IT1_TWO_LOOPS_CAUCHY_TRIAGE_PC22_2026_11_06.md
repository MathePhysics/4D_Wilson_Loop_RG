# Pair note triage: PC22 (R-step booking and totals)

Note: WILSON_IT1_TWO_LOOPS_CAUCHY_2026_11_05.md, owned by the two-loops session.
Reviewed SHA: 8b909fa9a898 (frozen during the round). Repaired SHA: b2d19b69258c (82,182 bytes; was 81,704).
Referee: referee_cli_20261106-124649_scope_pairCauchy_PC22.json (opus-5-5, xhigh, $5.58), section in reviews\REVIEW_LOG.md.
LF pin: 6124a4ed5b5d, checked by hash; #5.39, #5.39-1 and #5.50 re-read. Table: 697a56eb4c81, checked by hash. D2.7: 7323426aafcf. Two-loops note: b35769e221d9 (was 5f3948e3e320; #815 and #817 repaired, below).

## Verdict

No ERROR, three MINOR findings, so the round is not clean. PC21a-1, -2 and -5 are resolved, PC21a-4 is resolved in substance, and PC21a-3 is resolved except for PC22-1. The referee issued one shell command outside the permitted set (a python -c); it was denied and nothing ran.

## Repairs

| Finding | Severity | Repair (in place) | Lines |
|---|---|---|---|
| PC22-1: the R-step places miss a single-loop carrier that is a member of a cross group (#761, #799) | MINOR | the member place now reads "a member of a single-loop group g of 15.6 (#825) or of a cross group (#761, #799), which leaves the count with it (#PC4.14.4-4.5.1)" | #PC4.14.4-4.5.4 |
| PC22-2(i): the slot payment sorts partly by species and partly by root, so an R-made case-(a) group with a D2.6-rooted member falls in neither category | MINOR | sorted by species, as D2.7 15.8(b) sorts: D2.6's species by their components' kappa_j (D26 7.2), the factors of -4.5.4-3 as there, the other att(n, .) of earlier R-steps (15.6(e)-(f)) by kappa's R-step summand, at least twice 15.6(e)'s charge (15.3) | #PC4.14.4-4.5.4-1 |
| PC22-2(ii): 2 sup M^R needs M^R cumulative | MINOR | moot: the term 2 sup M^R and M^R are deleted, since D2.7 15.3's R-step summand (summed over every R-step, twice each step's charge) pays the R-made masses in e^{2 Sigma A} (queued item 2 of PC21a's handover) | #PC4.14.4-4.12 |
| PC22-3: P^R counts only the case-(a) groups and leaves out the att(k, .) dev parts of the cluster terms of E_k^R(C;V_k) and Psi(S) near the collars (15.6(d) last sentence, (e)) | MINOR | the productions now include these dev parts, each its own root (#PC4.14.4-4.5.4-7, citing #680 for the pair); P^R's per-cube bound O(1)e^{-p0(g_k)/2} covers them by 15.7's sum over the clusters through a cube, at the amplitude of *The payment* that the clusters without q = 0 keep (#815), their weights paid by the activities as a group's polymer part is (#723, #685). C^P keeps its form | #PC4.14.4-4.5.4-7, -4.5.4-8 |
| (own, found checking PC22-3) the dev parts of the clusters with q = 0 through a second-class Y_i have amplitude alpha^{1/3} (#812), not e^{-p0/2}, and total up to 2C_Psi'' per Y_i, which P^R's small form cannot hold | (own) | structural, as for item 7's block: they are att(k, Y_i) (15.6(e), the cluster contains Y_i), every term of a group holding one holds it, so these groups are put at activity 0 in the comparison gas too; they enter no c^a, no N, no M^map, and are carried in Y^d with #814-#818's bounds, paid at Y_i and carried by D2.7 (15.8(c)) | #PC4.14.4-4, -4.5.4-3, -4.5.4-7 |
| (own) the same dev parts, expanded term by term (15.6(d)), cost up to e^{3C_Psi''} per Y_i, not the e^{C_Psi''} in E(Y_i) | (own) | two-loops note: #815 adds that the dev part (value less flat value) is at most 2C_Psi''; #817's E(Y_i) and its margin use 3C_Psi'' (the margin p0(g_k)/32 still holds for small g_k, C_Psi'' being a constant) | two-loops #815, #817 |
| (own) the referee's unchecked point: #840 takes the first non-dev member in D2.0(3)'s order at the top level, while the pair's W_1 holds the root at any depth, so the two can differ (a member att(k', .) holding an older att(j, Z) beside a member att(j_2, Z_2), j < j_2 < k') | (own) | -4.5.4-6 now gives case (b)'s species as "the species of its first non-dev member (#840), which need not be W_1"; the booking in W_1's register is for the cost only, as -4.5.4-5 already states | #PC4.14.4-4.5.4-6 |
| queued item 1 (D2.7 7323426aafcf) | (own) | "which D2.7 bounds within Res(Z) (15.6(e), 15.8)" now reads "which D2.7 pays by kappa's R-step summand (15.3, 15.6(e))" | #PC4.14.4-4.10.1 |
| totals after dropping 2 sup M^R | (own) | E + Sigma N at most (7/3)E + (8/3)C^P(d'+1), at most 3(eps^(2)_A + C^P)(d'+1); eps-bar_A read as 3 sup(eps^(2)_A + C^P); -4.13.1 to match | #PC4.14.4-4.12, -4.12.1, -4.13.1 |
| LF pin | bookkeeping | 36c22ebe3cfa replaced by 6124a4ed5b5d (the LF changes since are rewordings in LF §4, #4.40-#4.42, which the note does not cite) | #PC.1-1.2 |

## Pre-check

- Every changed line re-read in the repaired file: #PC.1-1.2, #PC4.14.4-4, -4.5.4, -4.5.4-1, -4.5.4-3, -4.5.4-6, -4.5.4-7, -4.5.4-8, -4.10.1, -4.12, -4.12.1, -4.13.1; two-loops #815, #817.
- Grep: no M^R, 2sup, 3C^P, Res(Z), 36c22ebe3cfa or 039f871a34db left in the note. Every other use of eps-bar_A (#PC.1-1.2.1, #PC4.14-3a.4, #PC6.4.1, #PC6.4.1-1) needs only that it is a power of log(K + 2) times g-small constants, which 3 sup(eps^(2)_A + C^P) is. C_Psi'' elsewhere: two-loops #37 names it only; no use in LF, D2.7 or the table.
- Arithmetic. Sigma N at most (4/3)E + (8/3)C^P(d'+1) (-4.10.2). E + Sigma N at most (7/3)E + (8/3)C^P(d'+1), at most 3(eps + C^P)(d'+1). In -4.13.1, (4/3)eps + (8/3)C^P at most 3(eps + C^P), and Sigma_Z (d'+1) at most 2 Sigma_Z |Z| at most 2P(X).
- Sources quoted and checked: D2.7 15.3 (l.167: the R-step summand c^R_n(d'_n(Z_n)+1), at least twice 15.6(e)'s charge), 15.6(d)-(f), 15.7 (the sums over the groups and the clusters through a fixed cube, by (1.96)-(1.97) with 15.3's amplitude), 15.8(b)-(c) (E(Y_i), the q = 0 clusters, att(k, Y_i) carried by D26 5.0 with theta := 0); two-loops #680, #723, #761, #799, #812-#818, #840, #841; LF #5.39, #5.39-1, #5.50.
- labels_pair_cauchy.py: 319 tags, one per line, unique, every line at most 600 characters, every #PC reference exists; labels_two_loops.py: 1005 tags. LF line endings kept in both notes.
- Packet PC23 (the same lines as PC22): 8.2k characters of reviewed lines (7.4k before).
- No OPEN item and no known weak point in the packet's lines.

## Outside this note (D2.7, owned by the LF session; sent to the LF session at 13:24 GMT with the two-loops #815/#817 change, under the updated workflow)

- 15.6(e) says the per-component charge of every att(k, .) dev term is at most O(1) components' worth of activities bounded by c-hat_1. That holds for the groups (the first-class component with the slot pays e^{-p0}), but not for the dev parts of the clusters with q = 0 through a Y_i, whose amplitude is alpha^{1/3} (two-loops #812-#815). 15.8(c) pays them inside E(Y_i) by the quarter, so (e) needs only to except them. No bound of D2.7 changes; E(Y_i) is still at most e^{p0(g_k)/16} with #817's 3C_Psi''.
- 15.7 carries "the dev parts of the cluster terms" as dev, while 15.6(e) makes those near the collars att(k, .); 15.7 is read as the ones outside (e)'s scope.

## Handover

- 2026-11-06 (during PC23): LF now 82fcc5b842a5 (checked by hash; table unchanged at 697a56eb4c81), the 11b r3 repairs: Δ(y) a fixed partition (#4.30-1), the pairing count (3/2)d in #4.40.1-1-1, #4.40.1-2 and C_{HX}'s first entry, so C_q and C′_gap(ε₀) grow by at most 3/2 with their definitions unchanged; #4.41-1-1 cites #4.41-1-1-1. These are used only in LF §4 (#4.40-0, #4.40-1, #4.40.1-3-1, #4.42-2); neither the pair note nor the two-loops note uses C_{HX}, C_q or C′_gap or cites LF §4 (case-sensitive grep), and the pair note uses c̄^W_K (#5.41) and C_Q^W (#5.42) by name and form only, with their definitions unchanged. Queued bookkeeping: re-pin #PC.1-1.2 to 82fcc5b842a5 after PC23.
- 2026-11-06 13:28 GMT: PC23 launched at the user's "Launch" (note 088cd8fd4229, two-loops b35769e221d9, scope_pairCauchy_PC23.md, run_referee_beta_scoped.ps1, opus-5-5 xhigh). Both notes are frozen while it runs.
- 2026-11-06 13:27 GMT: D2.7 now d0f52784cc8f (checked by hash). The LF session repaired the three points sent at 13:24: 15.6(e) excepts the dev parts of the clusters with q = 0 (paid inside E(Y_i), 15.8(c)), 15.3's summand is "twice 15.6(e)'s ĉ₁ charge", 15.7 carries the cluster dev parts only outside (e)'s scope, and 15.8(c)'s E(Y_i) includes the q = 0 dev parts and cites two-loops #815, #817. Re-read against the text: it holds; (R-eval) (l.5) untouched. The pair note's quote of 15.6(e) in #PC4.14.4-4.5.4-8 is still exact; #PC4.14.4-4.5.4-1 now says "15.6(e)'s ĉ₁ charge" (bookkeeping). Note now 088cd8fd4229 (82,188 bytes).
- 2026-11-06 13:20 GMT: PC22 triaged (three MINOR, no ERROR); all findings, the queued D2.7 items and the LF re-pin (6124a4ed5b5d) repaired in place; note at b2d19b69258c; two-loops note #815, #817 repaired (b35769e221d9). PC23 (full round of the same lines) written; not launched, waiting for the user's "Launch".
