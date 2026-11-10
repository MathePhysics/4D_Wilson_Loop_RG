# Pair note triage: PC28 (pc-rstep-20261106-r28 and pc-soft-20261106-r1)

Notes: the pair note WILSON_IT1_TWO_LOOPS_CAUCHY_2026_11_05.md and the two-loops note WILSON_IT1_TWO_LOOPS_UNIFORM_BOUND_2026_10_27.md, owned by the two-loops session.
Reviewed SHAs: pair note 1c06afc7c236, two-loops note 64b10fbd541a, LF 69b89ae84241, table ddd74a0dabc1, labels 72b7b6332a21. Both notes were frozen during the rounds.
Reviews: verification\isolated_reviewer\reviews\pc-rstep-20261106-r28\review.md and reviews\pc-soft-20261106-r1\review.md. Both referees opened only permitted files, and their hashes match.
Launch: both through build_packet.py and the gate. They ran at the same time, against "one referee of one's own at a time" (PC27 triage, Workflow breaches).

## Verdicts

- pc-rstep r28: one SERIOUS (F1) and six MINOR (m1-m6). Not clean.
- pc-soft r1: one SERIOUS (S1) and seven MINOR (m1-m7). Not clean.
- The clean count for both parts is 0.

## Findings and repairs

| Finding | Severity | Repair | Owner, lines | Status |
|---|---|---|---|---|
| rstep F1: the q = 0 cluster pieces' weight e^{c_off} per pi_k-cube of X_c off the Y_j is said to be paid by (1.95)'s leftover decay, which lives only on the localisation domains X'. X_c is undefined, and it holds spans, other polymers' domains and link cubes | SERIOUS | Each q = 0 cluster piece carries a reserve sigma-tilde(c) and the weight y_c = w_c abs(e^{-d_c} - 1), w_c := e^{nu_r sigma-tilde(c) + (3/8)nu_e(2 Sigma(D-union_P + 2 l_P) + 1)}, paid inside #814's Kotecky-Preiss sum by 15.8-1(6) and (6-3). The links got their own count and budget: #629-4, #629-4-1, #629-5 (u_L := 640(2^d + 8), L_0^x := 4 10^4 u_L), carried through (R-member), (6A)(i), (6B), (6C) | LF (D2.7 15.8-1(2-2), (4-1), (6), (6-3)); two-loops #815.1, #815.2, #629-4 to #859 | done; LF made the D2.7 part and table #T4.42 |
| rstep m1: #816 counts MR_k-cubes, while D2.7 15.4(i) says size(P) counts pi_k-cubes | MINOR | #816 cites #637's MR_k reading; 15.4(i)'s wording went to LF | two-loops #816; LF for 15.4(i) | done |
| rstep m2: 15.8-1 is written for one loop; for the pair a class can hold both loops' word pieces | MINOR | #PC4.14.4-4.5.4-3-3: 15.8-1 runs with C := C_1 ⊔ C_2, the window meets C's eight sides within 15.8-1(3-1)'s count, two-loop att register (#844), activity 0 either way | pair -4.5.4-3-3 | done |
| rstep m3: "meets" (#850) / "domain contains" (15.8-1(1-1), -4.5.4-3-2) / "a localisation domain contains" (#800, #803) | MINOR | One criterion everywhere: a localisation domain of a polymer of g contains a second-class component (#803), in #850 and -4.5.4-3-2; 15.8-1(1-1) went to LF | two-loops #850, pair -4.5.4-3-2; LF | done |
| rstep m4: "att lineages" does not say whether lw(Z) and att(j, coll) lineages are carriers | MINOR | -4.5.1-1: "the att lineages, of att(j, Z) and att(j, coll) (there is no lw, LF #5.12)" | pair -4.5.1-1 | done |
| rstep m5: "no doubling" reads as denying 15.8-1(5)'s lineage factor 2 | MINOR | "no 1 + per piece to exponentiate" in -4.5.4-3-1 and #815.1 | pair -4.5.4-3-1, two-loops #815.1 | done |
| rstep m6: -4.13.1's step from 2 to 4 is unexplained | MINOR | -4.13.1 states it: d'_j(Z) + 1 ≤ 2 abs(Z)_j per run (LF #5.39-1), the two runs together 4 | pair -4.13.1 | done |
| soft S1: #6.16.2 applies VAR Theorem 1 per layer, but its single constant misses alpha_{0,n} by up to (1+beta_0)^2 sqrt(k-n) | SERIOUS | Split by layer. On Omega_k, Z included (Z joins the new Omega_k, #47), VAR Theorem 1 at the R-step's data bounds gives B_3 eps^V, eps^V = O(1)B_5M^6L^3R_k eps_k, a vanishing part of the top-layer room (#6.16.1 to #6.16.1-2). On the layers n < k off Z, the base is a G-gauge transform of a pre-R point (#191, #212), and the response chain (map #MD2.2.6.190-50 to -53, #MOMGD.11) gives O(1)eps_n plus a term below every power of g_n; R-bg for the current and derived parts, inferred (#6.16.2 to #6.16.3-1) | two-loops #6.16 to #6.16.5, #212 | done |
| soft m1: #6.16 omits the soft factor off Z | MINOR | (1 + 2kappa_s^LF)2L_0^{2N_0} in #6.16.1 | two-loops #6.16.1 | done |
| soft m2: #173.3.2 attaches the soft factor to (2.34), which is a domain condition | MINOR | factor dropped there; (2.34) named a condition of the domain, not a test | two-loops #173.3.2 | done |
| soft m3: "with that eps" may count the factor twice | MINOR | eps := (1 + 2kappa_s^LF)L^2R_k eps_k defined once, (1.78) at B_5M^5 eps | two-loops #6.16.1-0 | done |
| soft m4: K is both the stopping index and #167's VAR factor in #130.12.1 | MINOR | "the O carrying VAR Proposition 9's factor (#8)" | two-loops #130.12.1 | done |
| soft m5: B^x_W depends on K | MINOR | B^x_W := sup over K of #918's right side, finite by #919 | pair #PC2.2 | done |
| soft m6: #206's "each factor depending on its cube only" | MINOR | "each factor determined by its cube alone, through U_{k,square}(V_k) on the plaquettes of square-tilde" | two-loops #206 | done |
| soft m7: #920 omits #602's exclusion of the cross insertions | MINOR | "#602's supremum of LF #3.99's B_LF for C_1 ⊔ C_2 with the words' bound taken without the cross insertions" | two-loops #920 | done |
| packaging: provenance names the LF as the source of note extracts; line counts one higher than wc -l | packaging | build_packet.py: notes branch names the notes; counts by count of newlines; LF-only branch unchanged (backup build_packet.py.bak_pc) | build_packet.py (shared) | done |

## Found in the pre-checks (no round)

- #762 and #758 both used the last c_F/4 of #729's split. #729 now halves it: join positions (#758), and either the join offsets (span, #754) or the first-case separation (no span, #762, decay e^{-nu_r D L^m/(1076M)}, #778).
- The S1 rewrite first dropped the data on Z, which joins the post-R top layer and which the pre-R clause cannot reach. Restored as #6.16.1-0 to #6.16.1-2 (r1's reviewed print readings, with m1 and m3 applied); #6.16.4's (2.38) and #212's scope re-cited; #6.16.4 split at a sentence (#6.16.4-1), its beta cited as CRE p.261 l.42's beta ≤ 1/4 (not table #T1.2's beta).
- Pair note: its restatements of the two-loops constants replaced by citations (#PC4.3, #PC4.4, #PC5.2-4, #PC5.2-5); -4.5.4-3-3 updated to 15.8-1(3-1)'s count; #PC.1-1.2 re-pinned to LF 6e1ff0377576 (LF #1.1, #5.6, #5.66 to #5.66-2 checked at 741f6df6e370; the uses hold).
- Queued from PC27: #PC4.8-1.3 against LF #5.6 (i < j_0 - 1), #PC4.14-5.6.2 and #PC6.4.1-1 against LF #5.66: checked, they hold as written.

## Peer messages

- To LF: F1's D2.7 part, 15.4(i), 15.8-1(1-1); the links budget (lambda = 1/640, u_L, L_0^x), the exact 1/1458 (I first wrote 1/729; both bounds are true).
- From LF: D2.7 69800c824127 and table #T4.42 updated; LF 6e1ff0377576, then 00a7d8553b7f (12a r9: #3.28-3 to #3.28-7, #3.36's wording; no bound changed). LF #3.44, #3.45, #3.47, #3.96-1-1 and #3.99, which this part cites, are unchanged at 00a7d8553b7f.

- To LF (during soft r2): #212's narrowed scope (Z joins the new Omega_k; #6.16.1-1 covers it); D2.7 15.8-1(6) and (6-2) charged a link's whole quarter e^{a°/4} to the weights, double-using the length-decay eighth that pays the joins (#629-4-1). From LF: D2.7 d5cb428e6c91 pays them from the first eighth (nu_r lambda sigma + (3/2)nu_e sigma < a°/8, checked: (1/640 + 1/3888) < 1/256); item 5(a) does not cite #212 and uses no real base point on Z.
- Read ahead for the next rounds: pc-rstep r29's part (totals of -4.10.2 to -4.13.1 re-added; 15.8-1 (1-1), (1-2), (2-2), (2-5), (3), (3-1), (4-1), (5), (5-1), (6-1), (6-3) match) and pc-links-a's part (share 0.22605 ≤ 0.227; 8320u/L_0^x and 128(65u + 450)/L_0^x ≤ 0.21; #583's 8832u ≤ L_0^x; #716 and #720 at d = 4). No finding.

- From LF: renames done, D2.7 dbe7f99a98b6 (lambda_L in 15.8-1(2-2), (2-5), (6), (6-2); C_theta at 15.5(i) and 15.8; l.841, l.844, l.286 cited as #841, #844, #286), table f977a24fa070 (#T4.42 lambda_L, y-hat_g paid by the first eighth), labels 1fb0f5a867a4; LF 12a r10 clean, LF stays 00a7d8553b7f. Confirmed to LF: #286 is the pair's carry condition (its C_delta c-bar S_R + (1 + C_s + C_att C_y)S^R ≤ log 2).

## Queued (notes frozen during pc-soft r2; apply before the next launch)

Found by build_packet.py --check on the next three specs (renames only, no bound changes):
- w_c of #815.1 to #815.2 clashes with #52.1's contact weight w_c: rename w^Psi_c.
- lambda := 1/640 (#629-4) clashes with the dilation lambda of D^lambda_k (#48 to #54): rename lambda_L in #629-4 to #629-5, #691, #716, #720, #829; LF renames table #T4.42 and D2.7 15.8-1(2-2), (2-5), (6), (6-2) (asked).
- l_P and lambda_L are table #T4.42's: #629-2 and #629-4 cite the row instead of defining them.
- C_s of #844 clashes with #T4.26's and Cauchy 8.7's: rename C_theta in two-loops #844, l.415, l.1042, and pair -4.5.4, -4.5.4-3-3, -4.5.5-1 and their neighbours; LF renames D2.7 l.175, l.191 (asked).
- a_* of #PC4.4 clashes with LF #4.101's: rename a-hat_*.
- C := C_1 ⊔ C_2 in -4.5.4-3-3: written "with C_1 ⊔ C_2 for C".
- the local m := K' - j (#PC5.2), m := K' - k (#844) and a := ... (#665, #777, #844, and the other sum-lemma lines) written as "at a = ..." and "m = ...", not as definitions.

## Packet plan

One referee at a time, in this order: pc-soft r2 (narrow: the changed lines and their consumers), pc-rstep r29 (r28's pair extracts and two-loops #812 to #817, #849 to #850), pc-links-a r1 (#629 to #629-5 and the (R-member), (6A)(i), (6B) count lines), pc-links-b r1 (#660 to #666, the (6B) joins and first case, (6C), #PC4.3 to #PC4.4, #PC5.2 to #PC5.2-5). Each under 25k.

## Pre-check: pc-soft-20261106-r2 (2026-11-06)

- Gate's changed list (27 tags, #6.16 to #PC2.2) equals the packet's extracts; every one re-derived below. Linear order: #6.16.2 cites #191 and #212 ahead, as before the repair.

- Per tag: #6.16, #6.16.1, #6.16.1-0, #6.16.1-1 (R_n eps_n ≤ O(1)L R_k eps_k, g(log g^{-2})^{p_0+r} increasing, g_n ≤ (1+beta_0)g_k), #6.16.1-2, #6.16.2, #6.16.3 (R-bg's current and averaged parts labelled inferred; VAR (2)'s global eps O(L^2)(1+beta_0)eps_n per map #MD2.2.6.190-53), #6.16.3-1, #6.16.4, #6.16.4-1; #167 and #167-1 to #167-8 (the split of #167: #167-1 r^ext and c_ext with VAR's factor K (#8), #167-2 the two readings of p_1 and the radii alpha_{0,k}, alpha_{1,k} (#T2.24), #167-3 the Cauchy step's points within 2r^ext, #167-4 U_k(V_k) = U_{B_k}(V_k) and VAR's own setting, #167-5 the deviation below ((1+beta_0)/L)alpha_{0,k}, #167-6 J^h and the slots, #167-7 no conjugation factor, #167-8 the pointer to #6.16); #173.1, #173.3.2, #130.12.1, #206, #212, #212-1, #920, #PC2.2.
- Changed lines re-read: two-loops #6.16 to #6.16.5, #167 to #167-8, #173.1, #173.3.2, #130.12.1, #206, #212 to #212-1, #920; pair #PC2.2.
- Cited prints re-read in the corrected transcripts: CRE p.261 (2.34) to (2.39) and l.42 to 44; LFR I p.193 l.21 to 27, p.194 (1.78); LFR II p.378 l.10 to 22; map #MD2.2.6.135-1, -136, -136-5, -190-7, -190-50 to -53, #MOMGD.11. (2.36) is on J itself, so the base current is compared with alpha_{0,n}(L^n xi)^{-3}, and #51's J - J_k condition is the family's.
- Arithmetic: on Omega_k, B_3 eps^V / alpha_{0,k} = O(1)B_3B_5M^6L^4(A_0/C_0)(log g_k^{-2})^{r+p_0-q_0}, to 0 since q_0 > p_0 + 3r (table #T1.2); on n < k, eps_n/alpha_{0,n} = (A_0/C_0)(log g_n^{-2})^{p_0-q_0}, the chain's theta-term o(1); #6.16.4: 8(8/7)^3/(3L) < 1/2 at L ≥ 8 (#T1.3).
- Symbols against the table: kappa_s^LF (#T3.34-1), q_0, p_0, beta_0 (#T1.2), L (#T1.3), eps_1^JB (#T3.34-2). No restatement of a row.
- Uses grepped: #6.16.x cited by #167-8, #173.3, #910, #920, #212; table #T3.34-1 cites #6.16.1, which still defines kappa_s^LF.
- Size: 12.8k characters of reviewed blocks (r1's packet 13.4k).
- Definition check: eps on Z renamed eps^Z (table #T2.4 has eps), #6.16.4's m written "with m = k - n".
- SHAs: two-loops 7173e85fd0b1; pair 306c621284a4; LF 00a7d8553b7f; table 23e44e965fcb.
- No known weak point; a clean round is expected.

## Handover

- 2026-11-06: PC28 triaged: rstep r28 1 SERIOUS (F1, the q = 0 cluster pieces' weight) + 6 MINOR; soft r1 1 SERIOUS (S1, #6.16.2's per-layer VAR) + 7 MINOR. F1's D2.7 part was sent to the LF session. Repairs in place follow; no launch until all are made and pre-checked.
- 2026-11-06 19:50: all PC28 findings repaired (table above), the links cascade and the #729 split made, build_packet.py fixed. pc-soft r2 pre-checked; launching it alone; rstep r29, links-a r1 and links-b r1 follow one at a time.
