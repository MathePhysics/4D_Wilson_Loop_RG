# Triage of Round 47 (21:58, 26 Oct 2026, date)

Review (CLI run, claude-opus-5-5, effort high; launched 21:17; no prior review; packet by build_round47_review_packets_20261026.py): verification\isolated_reviewer\reviews\it1-bg-20261026-r1\review.md (b9c1587b166b, 250 lines, landed 21:28; WILSON_IT1_BACKGROUND_ITERATION_CLOSURE_2026_10_26.md, map l.165, the background terms iterated to the final scale).

**Open after this round: nothing new. The note's reorganisation is correct (linearity, the shed word as the difference of the two chains' insertion words, parity at the general step, the identity's algebra, the telescoping, the k = K form, b_d). Its labels overstated what was closed: items (i) and (ii) of the map's (7)(e) are reduced to the interfaces (iii-a), (iii-c), (iv-a)–(iv-c), not closed independently of them, and the identity's remainder over the labels without the coarse D(K) form was unassigned. Both repaired: the labels in the note, the map (l.63, 66, 135, 141, 161, 165) and the status report now say "reduced to"; the remainder R_bad is defined, identified with the label set ℒ_k of (iv-b), bounded crudely by the positivity of the step map at real fields (new §1.6, derived from CRE (2.18)–(2.23), (1.5)–(1.6), (3.15)), and reduced to (iv-a)–(iv-c) for k < K; (iv-b)'s per-cube weight w_K is reduced to LFR II (1.80)–(1.89) (accepted) with the D2.6 closure §7.2–7.3 and the summability over the steps. The twelve minors applied. (iii-a) and (iii-c) are delivered by WILSON_IT1_COARSE_CHAIN_INTERFACES_CLOSURE_2026_10_26.md (round 48, it1-coarse-20261026-r1, running). Repairs not re-reviewed.**

## Verdict

NOT CLOSED as labelled; no fatal finding. Serious S1: map l.141, l.161, l.165 said "Derived … the expectation-level closure" while §2.3's coarse bounds, §3.2's second and third terms and (C5) use the coarse amplitude 𝔞^g, which is "expected", not derived; (iii-c) is conditional because l.166 is a step-2 result for D2.1(2)'s slots. Serious S2: §3.1's "exactly" holds on the labels where both chains have their D(K) forms; the complement R_bad was unbounded and unassigned, (iv-b) bounding only the β-part. Minors 3–12: §1.1's "for every function 𝒲_k" needs Cov(k) for the gauge fixing (vii); §3.2's size of N_k off by a factor L (Σ_{m=1}^{K−k}L^m); §4.2's complex case omits ‖∏′‖ ≤ e^{LΔ_i} (8.91 ≤ 9.2, b_d^c = 1.2b_d stands); (D5) "entire" is wrong (analytic on the (α)–(β) domain); §2.2's interior scope omits l.166's exclusions (𝐁_j, A(g^{−2}(·) − g^{−2}, ·), V^{(j)}(S_{j+1}), touched old insertions); §3.4's display follows from the fine D(K) form, not from "§3.1 reads"; §2.3 has b_d^{2k} where (iii-a) has (b_d^c)^{2k}; §3.5 should write ⟨g_1^{(1)}⟩_1; the absolute weights presuppose ρ_K^ℓ ≥ 0 and |χ| ≤ 1 off the small-field region presupposes M^kU_K ∈ G; (C4)'s k-dependence changes the fine chain's ε′ unless ε_H is fixed once at the largest k used. Correct: What the Objects Are, §1.2–1.5, §2.2's parity, §2.3's arithmetic and D2.3 inputs, §2.4, §3.1's algebra, §3.2's first and second terms, §3.3, §3.4, §4.1(1)–(4), §4.2's real case, (D1)–(D4), (iii-b), (iv-d), (C1)–(C3), (C6).

## Repairs

- Background note (WILSON_IT1_BACKGROUND_ITERATION_CLOSURE_2026_10_26.md, 134 lines): the header rewritten ("Open after this work": (i), (ii) reduced to (iii-a), (iii-c), (iv-a)–(iv-c); the remainder R_bad; positivity); §1.1 restricted to Cov(k)-invariant words (map l.578–580); new §1.6 *Positivity of the step map at real fields*: every labelled term of ρ_k is nonnegative (CRE (2.18)–(2.23), pp.257–258, read), every factor the step inserts is nonnegative (the decompositions of unity, the Gaussian, CRE (3.15)'s real exponent, the gauge fixing (1.5)–(1.6), p.247, read), so the step map is an integral against a nonnegative measure on each labelled term, ρ_{k+1}^{ℓ′} ≥ 0, and sup|𝒲_{k+1}| ≤ sup|𝒲_k| on every label; the coarse loop taken as V_k ↦ W_χ(C^{(k)};V_k), defined on every label without the chart; §2.2's scope lists l.166's exclusions; §2.3's (b_d^c)^{2k}; §3.1 restated with ⟨·⟩_K^{good} and R_bad := Σ_{ℓ∉𝔏_good}∫(𝒲^f_K − N_k𝒲^{g_k}_K)ρ_K^ℓ dV_K/Z, with the paragraph *The complement*: the fine chain has its D(K) form on every label (D2.6 closure §2, §9), so 𝔏_good's complement is exactly ℒ_k by §1.2, §5.1 and the nesting; with (iv-a)'s carrier item R_bad = 0; without it |R_bad| ≤ (1 + |N_k|)N_tubew_K^{(0)}, of the right order at k = K only, since N_k/κ_f^{(K)} = e^{E^f_{const,k}}/κ^{g_k,(K)} is exponentially large in P_k(C) for k < K; so R_bad is the whole-label content of (iv-a)–(iv-c), not a further interface; §3.2's first term over 𝔏_good; the size of N_k corrected (Σ_{m=1}^{K−k}L^m, order 2𝔞̄^∨P_k(C)L/(L−1)); §3.4 derived from the fine D(K) form directly, with R_bad at k = K; §3.5 with ⟨g_1^{(1)}⟩_1 and R_bad; §4.1(3) and (C4): ε_H fixed once at k = 1, and the Claim's condition with c_C = 4 (map l.378; the note had 4L) gives (C4)'s first part once M ≥ 11(d+2)c_h/c_π (a condition on M, not on L); §4.2's complex case with ‖∏′‖ ≤ e^{LΔ_i} (8.91 ≤ 9.2; ratio ≤ 1.184 for d ≥ 2); (D5) analytic on the (α)–(β) domain with norm ≤ 1 + (b_d^cL)^kΔ_0; (iv-b) restated as the whole-label term with both chains' D(K) forms on ℒ_k, |R_bad| ≤ Cκ_f^{(K)}N_tubew_K, w_K the weighted per-cube large-field weight over both chains' factors, and *What gives w_K*: Bałaban's per-component factor exp(−κ_j(Z) − 2p₀(g_{j(Z)})) (LFR II p.384, read; accepted), the D2.6 closure §7.2–7.3's payment of |e^{𝓔(ℓ)}| out of κ with κ̂ ≥ Pol + Res ≥ 0 and Pol ≥ (K_j/2)(d′+1), the shape count C_d^{D+1} against K_j ≥ 4 log C_d, the positions paid by the future sums of (1.80)–(1.81) (accepted; not re-run), so w_K ≤ Σ_{j≤K}2e^{−2p₀(g_j)} ≤ 4e^{−2p₀(g_K)} by the summability of the D2.7 note item 9; for K > N through (1.89) at the R-operation; the "Derived here" and "Not derived here" lists updated.
- Map l.63, 66, 135, 141, 161, 165: the labels "under review in round 47" replaced by the round-47 outcome and "reduced to the interfaces (iii-a), (iii-c), (iv-a)–(iv-c)"; l.66, 161, 165 carry R_bad, ⟨·⟩_K^{good}, the positivity, and (iv-b)'s w_K ≤ 4e^{−2p₀(g_K)} with its reduction. 1614 lines, LF.
- Status report: the background bullet relabelled.

## Findings and dispositions

| Id | Finding | Disposition | Where |
|---|---|---|---|
| S1 | labels overstate: (i), (ii) closed only given 𝔞^g of (iii-a); (iii-c) conditional | repaired: "reduced to (iii-a), (iii-c), (iv-a)–(iv-c)" everywhere; (iii-a), (iii-c) delivered by the coarse-chain note, in review (round 48) | note header, "Not derived here"; map l.63, 66, 135, 141, 161, 165; status report |
| S2 | §3.1 "exactly" leaves R_bad unassigned | repaired: R_bad defined, identified with ℒ_k, bounded by positivity, reduced to (iv-a)–(iv-c); (iv-b) restated as the whole-label term | note §1.6, §3.1 *The complement*, §3.2, §3.4, §3.5, (iv-b); map l.66, 161, 165 |
| 3 | §1.1 "for every function 𝒲_k" | Cov(k)-invariant words, map l.578–580 | note §1.1 |
| 4 | size of N_k off by L | corrected sum and order | note §3.2 |
| 5 | §4.2 complex case omits ‖∏′‖ | included; 8.91 ≤ 9.2 | note §4.2 |
| 6 | (D5) "entire" | analytic on the (α)–(β) domain | note §4.3 |
| 7 | §2.2 scope omits l.166's exclusions | listed | note §2.2 |
| 8 | §3.4 "§3.1 reads" | from the fine D(K) form directly | note §3.4 |
| 9 | b_d^{2k} vs (b_d^c)^{2k} | (b_d^c)^{2k} | note §2.3 |
| 10 | §3.5 ⟨W_χ(C^{(1)};V₁)⟩_1 | ⟨g_1^{(1)}⟩_1, the coarse loop as a function of the block field | note §3.5, §1.6 |
| 11 | ρ_K^ℓ ≥ 0 and M^kU_K ∈ G presupposed | §1.6 derives the positivity; the coarse loop W_χ(C^{(k)};V_k) needs no chart | note §1.6, §3.2 |
| 12 | (C4) k-dependence | ε_H fixed once at the largest k used (k = 1); the Claim's condition with c_C = 4 gives a condition on M | note §4.1(3), (C4) |

## Not Re-Reviewed

All repairs above (the background note; map l.63, 66, 135, 141, 161, 165).

## Sources Read for the Dispositions

CRE p.247 (1.5)–(1.8), p.257 (2.13)–(2.18), p.258 (2.19)–(2.23); LFR II p.384 (the factorisation in components, the inductive statement (1.80)); map l.563–580 (D2.2(2) *Linearity* and the gauge fixing), l.378 (c_C = 4); D2.6 closure §7.1–7.4 (l.120–153); the review in full; the background note in full.

## Files Changed

WILSON_IT1_BACKGROUND_ITERATION_CLOSURE_2026_10_26.md, WILSON_IT1_D2_STEP_MAP_2026_10_22.md (l.63, 66, 135, 141, 161, 165; also l.156, 193, 342, 1094, 1095, 1097 for the D2.7 fold; 1614 lines, LF), WILSON_IT1_STATUS_REPORT_2026_10_26.md.
