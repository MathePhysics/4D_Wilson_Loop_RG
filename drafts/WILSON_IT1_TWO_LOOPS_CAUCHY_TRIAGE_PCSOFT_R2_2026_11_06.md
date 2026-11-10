# Triage: pc-soft r2 (6 Nov 2026)

Review: verification\isolated_reviewer\reviews\pc-soft-20261106-r2\review.md, read in full. Two-loops session.

## Verdict

No fatal finding; two serious (S-A, S-B), four minor (n1 to n4). r1's m1 to m7 resolved; r1's S1 resolved on Omega_k, Z included. Clean count for pc-soft: 0.

## Findings and repairs

| Finding | Where | Repair (in place) | Status |
|---|---|---|---|
| S-A, serious | #6.16.1, #6.16.2, #6.16.3-1, #920 | The chain's root on a layer n < k is at most B_3 eps^V_n in each weight: p.268's 2B_3 eps_n off an earlier R-step's region Z_n, VAR Theorem 1 at step n (the argument of #6.16.1-1) on Z_n. An R-step adds no response off its Z (#191); later Z_m never meet layer n, since Z_m goes into the new Omega_m, inside Omega_{n+1} (#47, #130.12.1). The T-steps' responses are the chain's (#6.16.2-1, new sub-line from #6.16.2). eps^V_j defined at every step j in #6.16.1-1; the ratio exponent r + p_0 - q_0 in #6.16.3-1. | done |
| S-B, serious | #6.16.3 | The current derived for U_k: the root's B_3 eps^V_n (L^n xi)^{-3} plus the responses' changes D*D H_m + F(U, H_m) (RG1 (3.11) to (3.12), p.272); D*D H_m = Delta_U H_m - P_1 H_m + lower order, by the Landau gauge condition R D* H_m = 0 (RG1 p.272 l.20 to 22); R-dec bounds H_m in the sup, gradient, Laplacian and P_1 norms with the same bound (map #MOMGD.54, -55, -57), so the changes add O(1) Delta^(n) in (2.36)'s weight (#6.16.3, #6.16.3-0). The R-bg identification is deleted. | done |
| n1, minor | #6.16.1-1 | (2.38)'s A and gradient cited to VAR Theorem 1's (9), p.279 l.17 to 24; the curvature and current to (2). | done |
| n2, minor | #6.16.3-1 | RG1 (1.12)'s field bound taken from the chain's (2.38) on Omega_n minus Omega_{n+1}. | done |
| n3, minor | #6.16.4-1 | f_n at least 1 - beta, at least 3/4, with the project's beta = 1/8 (table #T3.34, #75); CRE's beta = 1/4 is its example. | done |
| n4, trivial | #130.12.1 | Omega_1' = Omega_1 union Z (#173.5). | done |

## Found in the pre-check (no round)

- #6.16.3's first repair cited R-dec's Laplacian norm for D*D H_m directly. D*D is not the covariant Laplacian; the Landau gauge identity of RG1 p.272 is what turns one into the other. Now cited (#6.16.3-0).
- C_av in #6.16.3 was #6.15's 2B_3, not shown for the chain; replaced by "a constant, as at #6.16.1-2".
- #6.16.3-1 restated #6.16.1-2's formulas for eps and alpha_0; now cited.
- labels_two_loops.py indexed only tags N(.M)*: the 34 sub-line tags (#844-1, #6.16.1-0, #629-4, and so on) were absent from LABELS_TWO_LOOPS.md, and citations of them were not validated. Its two regexes now take (-d)* suffixes: 1057 tags, no unresolved citation. build_packet.py reads tags from the note itself, so earlier packets were built correctly.
- Bookkeeping, no round: C_s renamed C_theta, w_c renamed w^Psi_c (#815.1, #815.2), lambda renamed lambda_L (#629-4, -5, #691, #716, #720, #829), a_* renamed a-hat_* (PC), m and a written "with m =", "at a =" (#665, #777, #844-5, #PC5.2). Lines split at sentence boundaries: #212 into #212 and #212-1; #6.16.4 into #6.16.4 and -1; #844 into #844 to #844-9 and #844-4-1.
- Over-length lines: 180 of the two-loops note's lines exceed 620 characters (one, #130.15.2, has 7363). Those not rewritten in this round stay as they are; each is split when it is next repaired.

## Full recheck before r3 (user's request, 2026-11-06 20:15 to 20:57)

Every line of the r3 repair and every citation re-read against the corrected transcripts (pNNN_corrected.tex).

| Found | Where | Repair (in place) | Status |
|---|---|---|---|
| (a) The derived configurations were bounded by R-av, whose hypothesis X inside Omega_j fails for factor domains X straddling the layers and the R-steps' regions | #6.16.3-1 (old) | New lemma #6.16.3-2 to #6.16.3-6 (derived, not reviewed): localisation to the three layers n-1 to n+1 (X_n, its maximal sequence by RG1 (iv), p.262 l.41 to 43); the localised data meet VAR (7) by CMP98 Proposition 2 in its local form (p.26, as at #173.3.2); VAR Theorem 1 bounds U^d_n; off quarter-width strips U^d and U^d_n are the same pinned problem's minimiser by the uniqueness clause (p.279 l.15, as at #173.4); VAR Proposition 9 and (190) bound U^d - U^d_n by O(K) eps^D theta^X_n, theta^X_n of order exp(-delta_0 M_1 (log g_n^{-2})^2 / (64(1+beta_0))) | done |
| (b) The derived configurations' change along the segment had no bound | #6.16.4-1 (old) | #6.16.4-2 to #6.16.4-2-1: at most C_mJ times the deviation's bound, by R-mJ section 4 to 6 and the map's Assembly #MD2.2.6.142-68; the layer sum is O(L^2) since h_{n'} is at most L^{n'-n} h_n against w_{n,n'} = L^{3(n-n')} exp(-delta_2 R_1 M_1(abs(n-n')-1)); c_ext reduced to (1+beta_0)/(2LKC_mJ) (#167-1), C_mJ defined at #167-1-1 and fixed after L. D2.7 15.6(d) changed by the LF session to match (22e10e0cd238) | done |
| (c) RG1 (3.11) taken at the wrong base | #6.16.3 | U = U_{m+1}, A = H_m (RG1 p.265 l.37 to 39; Bałaban's own use at p.272 l.25); change -D*D H_m - F(U_{m+1}, H_m) | done |
| (d) A dimensionally wrong current conversion | #6.16.3 | J of RG1 (1.8) changes by the (3.11) terms in (2.36)'s weight | done |
| (e) VAR (9)'s factor M omitted | #6.16.1-1-1 | B_3 M^V eps^V_k, cubes of side 2M^V L^k eta | done |
| (f) The single eps^V_k used on older layers, where it misses alpha_{0,n} by up to (1+beta_0)^2 sqrt(k-n) | #6.16.1-3 | Older layers take the chain (#53, map #MD2.2.6.190-7) | done |
| (g) #6.16.4-1 claimed the derived configurations change by the same bound as the curvature | #6.16.4-1 | Replaced by (b) | done |
| (h) #920 restated #290; nu cited to #MD2.4.13.19 instead of -3 | #920, #287, #290 | #920 cites #290; the three nu citations re-pointed (bookkeeping) | done |

Renames (bookkeeping): rho_n to s^U_n (clash with TL's rho_k = C_rho g_k^2 (1+r_k)^4), theta-hat to theta^X_n (clash with LF #D.theta-hat), W, W_n to U^d, U^d_n (clash with TL's W and the pair note's W_n), a_i to a^U_i (VAR's a_0 is Theorem 1's constant), eps_0 not named in #6.16.3-4-1 (table #T3.1's eps_0 is an exponent), Omega_{k+1} empty cited to #130.15.2. #6.16.1-2's pointer to the lemma deleted (stated once at #6.16). Lines split: #6.16.1-1 to -1-1, #6.16.3 to -0 and -0-1, #6.16.3-3 to -3-1, #6.16.3-4 to -4-1, #6.16.4-2 to -2-1.

A transient error of mine in this pass: I read the raw pNNN.tex (one line higher than the corrected file) and moved six VAR pins by one; all were reverted after checking p278_corrected.tex and p279_corrected.tex, where the original pins are right.

LF's point on logarithms (table #T11.26): the two-loops note and the pair note take (1/i)log only of elements near 1 (BCH, REG (1.70) to (1.72)); no (pi/2) or pi bound occurs, so nothing cites #T11.26.

## Pre-check: pc-soft-20261106-r3 (2026-11-06 20:57)

- Changed tags: #6.16, #6.16.1, #6.16.1-1, #6.16.1-1-1, #6.16.1-2, #6.16.1-3, #6.16.2, #6.16.2-1, #6.16.3, #6.16.3-0, #6.16.3-0-1, #6.16.3-1, #6.16.3-2, #6.16.3-3, #6.16.3-3-1, #6.16.3-4, #6.16.3-4-1, #6.16.3-5, #6.16.3-6, #6.16.4-1, #6.16.4-2, #6.16.4-2-1, #130.12.1 (r2's n4), #167-1, #167-1-1, #920; #287, #290 bookkeeping. Consumers: #167-8, #212-1, #920 (under review), D2.7 15.6(d) and 15.7 (LF session, updated), #173.3 and #910 (cite #6.16 only).
- Regions re-derived: Omega_k, Z included (VAR Theorem 1 at eps^V_k); layers n < k off and on earlier Z_n (root B_3 eps^V_n plus the chain); the current (RG1 (3.11) at U_{m+1}, Landau identity, R-dec); derived configurations for every X, p, n (the lemma), uniform since every bound is per layer; the segment (#6.16.4 to #6.16.4-2-1).
- Cited prints re-read in the corrected files: VAR p.278 l.5 to 6, l.34 to 46, p.279 l.9 to 28, pp.308 to 309; CMP98 p.26 Proposition 2 and its locality sentence; RG1 p.261 (1.8), p.262 l.41 to 43, p.265 l.37 to 39, p.272 l.12 to 30; CRE p.255 l.33 to 57, p.261 l.6 to 43; R-mJ sections 3 to 7; map #MD2.2.6.142-69.
- Units: xi = eta (#52); (2.35)'s weight alpha_{0,n} L^{-2p}(L^n L^{-p})^{-2} = alpha_{0,n} L^{-2n} equals (2.34)'s; (2.37)'s scale factors carried by R-mJ's C_{(2.37)}.
- Arithmetic: s^U_n as at #6.16.1-2, uniform by q_0 > p_0 + 3r (#T1.2) and g_n at most (1+beta_0) g_k (#130.12); eps^D at most a_1 for g small; C_mJ 2K r^ext_k at most ((1+beta_0)/L) alpha_{0,k}; #6.16.4-1's 8(8/7)^3/(3L) < 1/2 for L at least 8 (#T1.3).
- Symbols: s^U, a^U, U^d, eps^D, theta^X, X_n, C_mJ, M^V absent from the table, the LF note, and the pair note; definition check 0 conflicts for soft r3, rstep r29, links-a r1, links-b r1.
- Lines: all of #6.16 to #6.16.5 at most 613 characters.
- Recheck at the user's "Recheck soft r3 and launch" (21:00 to 21:10), the built packet read in full. Four repairs: #6.16.3-3-1 and #6.16.3-6 had alpha_{0,i} at most (1+beta_0) alpha_{0,n} cited to map #MD2.2.4.72, which is about radii; derived from CRE (2.6) to (2.7) at n - m = 1 it is (1+beta_0)^2, now so stated. #6.16.3-6's theta^X_n bound now 32(1+beta_0) (was a looser 64), from (2.5) with r at least 2 (CRE p.245) and (2.7)'s second line for R_{n+1}, first line for R_{n-1}. #6.16.3-3 says where its L^2 comes from and that L^{2(p-i)} replaces it above p, matching #6.16.3-3-1's count. #6.16.1-2's theta-term coefficient 4 replaced by O(1), which covers #6.16.3-0-1's O(1). #6.16.3-4-1 cites table #T1.6 for VAR's a_0, a_1.
- Size: 13.9k characters of reviewed blocks (r2: 12.8k), the growth being the new lemma and #167-1-1.
- SHAs: two-loops 76bed9fd03f0; pair 04cd2db746a7; LF 91951cbcc102; table 25bbcd6bd3f0; labels 946fae7624bf; D2.7 22e10e0cd238. All four specs re-pinned, definition check 0 conflicts each; r3 rebuilt.
- No known weak point; a clean round is expected.
- Launched at the user's go (21:10).

## Handover

- 2026-11-06 20:10: pc-soft r2 triaged (S-A, S-B, n1 to n4) and repaired in place.
- 2026-11-06 20:57: full recheck at the user's request found (a) to (h); all repaired in place, the derived configurations by a new localisation lemma (#6.16.3-2 to #6.16.3-6) and their segment change through R-mJ with c_ext reduced by 1/C_mJ. r3 re-pre-checked and rebuilt (13.7k), not launched at the user's request. Next launches, one at a time: soft r3, rstep r29, links-a r1, links-b r1.
