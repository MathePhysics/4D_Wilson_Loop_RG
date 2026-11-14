# Pair note triage: PC26 (R-step booking and totals, full round)

Note: WILSON_IT1_TWO_LOOPS_CAUCHY_2026_11_05.md, owned by the two-loops session.
Reviewed SHA: 5ee561774ff5, with the two-loops note at 6b3d1f0d7c47 (both frozen during the round). LF 98afdbda7e48 at review, now d50e92b09804. Table 88a6dcbd277a. D2.7 55e50090afd6.
Referee: referee_cli_20261106-161557_scope_pairCauchy_PC26.json (opus-5-5, $4.25), section in reviews\REVIEW_LOG.md. The referee ran no shell command.

## Verdict

One ERROR and one MINOR, so the round is not clean. PC25-1, PC25-2 and PC25-3 are resolved as worded.

## Findings

- PC26-1 (ERROR, repaired; see Repairs): two-loops #815 and #817 carry the q = 0 dev parts with D26 5.0's factor 2 but use their norm masses. D26 5.0 carries weighted masses w(D) = e^{nu_r sigma} e^{(3/8) nu_e ext^coll} e^theta norm(Y_D) (D26 l.86), and D2.7 15.8(c) gives att(k, Y_i) "the weight ... beyond its mass". Each q = 0 cluster has a domain X' containing Y_i (#812), so each of these many insertions carries at least e^{nu_r #pi_k(Y_i)}, and the carried cost exp(2e^{c_W} Sigma_c w(c)) is not of E(Y_i)'s form. #PC4.14.4-4.5.4-3-1 ("#815's for the clusters"), LF #5.39-3-1 and #5.39-3-3 (m_Psi), and D2.7 15.8(c) inherit this.
- PC26-2 (MINOR, tied to PC26-1): #PC4.14.4-4.5.4-3-1's e^{2S} for the word pieces counts norms, while 5.0 doubles weighted masses. If a piece's domain contains Y_i, PC26-1 applies to it.

## Status of PC26-1 (work in progress, 2026-11-06)

Facts established, each from its source:
- Bałaban LFR II (1.95) (p.389 l.23-24): a q = 0 domain X' has c_0 = alpha^{1/3}, the decay e^{-(1+beta) kappa d_{k, union Y}(X')} and e^{-(beta kappa/(6 2^d)) M^{-d} abs(X' minus union Y)}, where q counts the first-class components X_{j_h} in X' (l.28-29). (1.96) uses only e^{-p0/2} 100^d R_k^{-d} per pi_k-cube of the last factor, and beta kappa/(6 2^d) is at least 1 (p.389 l.13). So at least e^{-1/2} per pi_k-cube of X' outside union Y is left over beyond (1.97), and it pays the weights e^{2 nu} per cube off union Y, since nu is at most 1/1000 (map #MD2.4.12.25). The cluster's other domains (q at least 1) pay theirs by e^{-p0(g_k)/2} (#723, #685).
- So the only weight not paid by decay is the one on the cubes (and the arc) of the second-class components themselves. Y_i has at most 101^d MR_k-cubes (#816), so one copy of that weight per Y_i is a polylog in the exponent, of 15.8(c)'s form (paid by kappa_k(Y_i)'s p0^2(d'+1) term, as 15.8(c) pays the block's weight).
- At a T-step n > k the new constituents lie in Omega_{n+1}, a subset of Lambda_n, at distance at least 6LR_{n+1} from Lambda_n^c, which contains every Y_j (D26 (T3): Lambda_{m+1} in Omega_{m+1} in Lambda_m). So touches and the second rule's incompatibilities (map #MD2.2.5.38) never reach a cube of union Y. Arc links can, since a new group's hull along C may cross Y_i.

Candidate repairs:
- (A) One fixed member per Y_i, or per labelled term: treat the product of the q = 0 insertions picked by a term as a single D26 fixed member, so that the cubes of each Y_j enter its weight once. This needs the arc part of the combined member's weight (its interval along C) to be paid.
- (B) D26 5.0's weights read off union Y: show that the reserve is spent only on positions a later step can link, namely cubes of new constituents and the arc, and that the arc positions inside union Y are paid.
- Both turn on the arc term. D2.7 15.8(c) makes the same one-weight-per-Y_i claim for all of att(k, Y_i), including the word pieces, so the LF session (owner of D2.7) is told.

Interim edit: two-loops #815 now states the norm mass m_Psi and marks the carried weighted cost OPEN (PC26-1); #817's 2m_Psi is marked not derived. No round is launched while PC26-1 is open.

## Repairs (after the LF session's answer, 2026-11-06 evening)

| Finding | Severity | Repair (in place) | Lines |
|---|---|---|---|
| PC26-1: q = 0 dev parts carried with norm masses, while D26 5.0 carries weighted masses | ERROR | route (A), derived by the LF session in D2.7 15.8-1 (D2.7 1804eb9f3061) and re-derived here: the att(k, Y_i) pieces form one fixed member per class of second-class components, carried once with the set count sigma^set and no doubling. Each piece's weighted size is y_c at most e^{c_off #off}abs(d_c)e^{abs(d_c)}; e^{c_off} per off-Y cube is paid by the (1.95) decay left beyond (1.97), which the sum of #814 (D2.7 15.3, (1.96)-(1.97)) does not use. So the sum of y_c is at most m^w_Psi = 2C_Psi'' e^{2C_Psi''} (LF #5.39-3-1-2); E(Y_i) uses C_Psi'' + m^w_Psi; the member's own log 4 + c_W + log b_Y is paid by 15.8(c) | two-loops #815, #815.1, #815.2, #817 |
| PC26-2: word pieces doubled with norms | MINOR | the word pieces are pieces of the same member, not doubled; -4.5.4-3 lists the pieces of 15.8-1(1) (R-group dev parts added); -4.5.4-3-1 states the carriage and payment; -4.5.4-4 excludes a D_g that is a piece | #PC4.14.4-4.5.4-3, -3-1, -4 |

## LF's soft tests (LF #3.17, #3.45, #3.47, #3.96, #3.99), propagated to my notes

- Two-loops #206 used chi^2 = chi for R-combined; #206.1 now takes the soft product and only its support.
- #173.1 and #173.3.1-#173.3.2: eps_1' carries the factor 1 + 2kappa_s^LF; kappa_s^LF = 1/240 is LF's test width, not the note's kappa_s (RG2's kappa_1, map #MD2.1.1.1).
- Line 56 and #245's line: the soft radial cutoff's support (1 + kappa_s^LF)M_0 eps_k, with LF #3.96's M_0.
- #910.1: eps_{K'} in #910 and #918 is the enlarged value, and the O(1) of O(C_chi rho_{K'}) carries the factor, as LF #3.99 does for B_W; pair note #PC2.2 reads it.

## Question to the LF session (answered)

- Asked whether 15.8-1(1)'s R-groups include groups with carrier or wrap members. Answer (D2.7 aace9f917430, 15.8-1(1-1)-(1-2)): every 15.6 group with a polymer domain containing a component of the class, whatever its members, enters as D-hat_g (D_g = D-hat_g[W_g], multilinear, norm at most B(g), on hull(g)+), the members keeping their own species, masses, weights and lineages. Re-derived: both terms of D_g carry each member as an ordered factor on its interval (15.6(f)), so D_g is multilinear in them; the members' weights stay with the members, so 15.8-1(4) needs none for them.
- Repairs: new #PC4.14.4-4.5.4-3-2 (such a group is a piece, no production, carried wrap or carrier of its own; a carrier member stays in the count at its own root); -4.5.4-3 cites it; -4.5.4 (a member of such a group continues); -4.5.4-4 and -4.5.4-7 (the exceptions); #PC4.14.4-4.5.1-1 (not a single-loop carrier); -4.5.4-3-1 split into -4.5.4-3-1-1 (the D-hat_g by B(g), parts at Y_i within E(Y_i), #818).
- Pre-check: a carrier member's options still carry at most 1 + C_s theta_k times its weighted mass (#844): the Y-groups' D-hat_g go into the sum over S of 15.8-1(5-1), so counting them also in #844 only overcounts. Cross R-groups containing a Y_i stay cross (#PC4.14.4-4.5.1): their weight at Y_i's cubes is within E(Y_i) (#806, #818), Y_i having at most 101^d MR_k-cubes (#816), against their amplitude e^{-p0(g_k)/2}.

## Handover

- 2026-11-06: PC26 triaged; PC26-1 OPEN, analysis above; sent to the LF session.
- 2026-11-06 evening: LF ad44c62ee742, then d3399ecd0784, then f4cbd0993021 (checked by hash); D2.7 1804eb9f3061 (15.8-1 added). The LF §5 lines the pair note cites were re-read; #PC.1-1.2 re-pinned to f4cbd0993021. PC26-1 and PC26-2 repaired as above; the soft-test propagation done. Labels pass. PC27 (full) waits for the answer to the open question.
- 2026-11-06 later: answer received and applied (above). LF f1f82651705d (only #4.561 split since f4cbd0993021; §5 unchanged), D2.7 aace9f917430, table a8041051efc3 (#T3.34-1 separates LF's kappa_s from the map's). #PC.1-1.2 re-pinned. Pair note and two-loops labels pass; changed lines at most 600 characters. scope_pairCauchy_PC27.md updated. No OPEN item, no known weak point; PC27 launched (full) under the user's standing "Continue until everything has been closed and reviewed".
- 2026-11-06 (during PC27): D2.7 now 0527bedce549 (checked by hash): 15.8-1(1-1) adds that with one loop no group is cross, and that for a pair a cross group stays cross with its weight at Y_i within E(Y_i) (two-loops #806, #816, #818), which matches #PC4.14.4-4.5.1 and the pre-check above. LF f1f82651705d and table a8041051efc3 unchanged. Nothing in either note changes; the PC27 scope's D2.7 pin (aace9f917430) differs from the current file only by this sentence.
- 2026-11-06 (during PC27, read-only recheck after the user asked whether the full recheck was done; it was not complete before launch): re-read every reviewed pair line not re-read earlier (#PC.1-1.2.1, -1.2, #PC4.14.4-4, -4.10.1, -4.10.2, -4.11, -4.12, -4.12.1, -4.13.1): consistent with the pieces of 15.8-1 and with LF's new eps^R_A, which -4.12.1 reads by reference. Re-derived 15.8-1(2) against D26 (T0)-(T3), 5.3 and 5.5 (a fixed member's sigma enters only through its positions, the charge b = (nu_r/4)sigma paid from its own reserve, and w(D) in the bridge; none uses the vertex multiplicity) and 15.8-1(3)'s window count (4(41 diam + 42) at most 168(diam + 1), at most 336M sigma^set; 81 + 336 = 417).
- QUEUED REPAIR (MINOR, own, found by the soft-test sweep; files frozen during PC27): two-loops #173.2 (chi_0 dropped), #190-#200 and #864 state Bałaban's removals of redundant tests ("equals 1 on the support of the remaining ones"). With soft tests these hold on the plateau, given the other soft tests at their support thresholds (LF #3.44, with LF #3.90 for chi_{k,Lambda}), which the lines do not cite. Repair after PC27 reports, and include these lines in the next round; PC27 cannot count as clean while this is open.
- 2026-11-06 (during PC27): LF now 0cb0774db832 (checked by hash), Cauchy note 7b77257e745a. Neither note uses the renamed symbols (delta_H, S_j, mu_0, psi_f, b_w; the pair note's b_wrap is another symbol). LF #3.99 adds that B_LF holds with the soft tests by (R-s)(b); nothing in either note claims otherwise. LF #3.96-1 was split, and the support bound (1 + kappa_s)M_0 eps_k is now in #3.96-1-1. QUEUED (bookkeeping): the two-loops line of #245's R-step restriction cites LF #3.96-1 and becomes LF #3.96-1-1; re-pin #PC.1-1.2 to the LF current after PC27.

## Workflow breaches in PC26-PC27 (found on re-reading ym4-review-workflow.md, 2026-11-06)

- §3 repair in place: corrections were tacked on beside the lines they correct instead of rewriting those lines: #173.3.1 patches #173.3's thresholds (rewrite #173.3 and #173.6 with the enlarged thresholds and delete #173.3.1); #910.1 redefines eps_{K'} for #910 and #918 (rewrite #910 and #918 with the factor and delete #910.1); "(the factor is #173.3.1's)" in #173.1 and "the soft tests' factors (#173.3.1) inside the O(1)" on line 56 are appended clauses; #PC4.14.4-4.5.4's "(of #PC4.14.4-4.5.4-3-2's, it continues)" and -4.5.4-7's "not one of -3-2" likewise. Rewrite each step so it reads as one argument.
- §2 and §4: new symbols were not grepped against the table before use (kappa_s^LF, epsilon_1' are this note's; sigma^set, m^w_Psi, c_off, b_Y, D-hat_g are D2.7's and LF's and have no table row). The table rows go to the LF session (owner) to enter.
- §4 pre-check: not recorded in full before PC27: no part size before and after, no packet-size measurement (measured now: 18,208 characters of reviewed lines, within 25k), no quoting of each cited display, no reading of the whole part for gaps, no definition check. The soft-test sweep was incomplete (the #173.2, #190-#200, #864 gap above). So PC27 was launched without a clean round expected.
- §5: PC24-PC27 were launched with run_referee_beta_scoped.ps1 and a scope file, not run_app_review_cli.ps1 after build_packet.py. build_packet.py reads only the LF, so the definition check it enforces was not run for these notes at all; it is now run by hand and recorded in each pre-check.
- §6: no dated lines were appended to SESSION_HANDOVER.md for PC24-PC27.
- Consequence: PC27's outcome is triaged as usual, but it cannot count toward the clean count. After it reports: rewrite the lines above in place, apply the queued repairs, run the full §4 pre-check with the hand definition check and record it here, then launch.
