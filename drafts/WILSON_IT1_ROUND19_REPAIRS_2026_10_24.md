# Round 19 (reviews of D2.4(10)–(13), 24 Oct 2026): findings and repairs

Reviews: verification/isolated_reviewer/reviews/it1-d2-4s10-20261024-r1, …4s11…, …4s12…, …4s13… (claude-opus-5-5, xhigh; packets built 16:39 on D2 SHA 9e7240650b85; all four landed by 17:05, date). Each read in full. No fatal finding in any of them. Repairs applied to WILSON_IT1_D2_STEP_MAP_2026_10_22.md 17:15–17:35, 24 Oct (date): (10), (11), D2.2(6)(d) l.907, (12)(a)–(b) and the minors of (12), (13)(a), the "superseded" labels on (12)(c)–(f), (13)(b)–(d), (Z-d) and (Z-e), the pointers in the gaps block, D2.0(3), (7) and (9), and the new consolidated Steps 3–4, D2.4(14) (written 17:20–17:31; not reviewed). D2 map 1663 lines. V4 untouched (b35c60e537b8).

## Open after the repairs (own lines)

- OPEN (user's review): the amendments D2.4(12)(a)–(b) (σ_{k+1} = #_{k+1} + n_{k+1}/M; the reserve/extent weights (ii-w) inside D(k)(ii)–(iii), per traversal, dev species; w_t at the rate (7/8)η_V; the reading of V3 L2791's M_Λ as a complex-domain pin — the ρ-size base is (c4-6-5), V3 L4619–4622), the new conditions κ ≥ κ_D′, L ≥ L₀ = 5000, and (14)(f)'s condition (R-m′) on R-m's exponent q = min(q₀,q₁): q > p₀, or q = p₀ with C_TC₁^{RG2}A₁/C_i small.
- OPEN (inherited, unchanged): (Z)'s step-1 base; D(k)(iii)'s complex-data dev clause for the touched insertions ((4), (5), (9)); D2.6's kinds (γ) and species (incl. ω′ ≠ 0 polymers, where the parity argument fails); (5)'s older-layer size (incl. CRE's boundary-type potentials 𝐁_k, A(g^{−2}(·) − g^{−2}, ·), V^{(k)}(S_{k+1})); (T) with the network weight in the reference-gas KP weight; (LPG), (T-dev)'s inputs.

## 4s10 (D2.4(10)) — S1, S2 and m1–m6 applied

- S1: the counting inequality's constant 9 was false (a curve of length a along a lattice edge meets 24 cubes; pieces branch). Now #(X∖D) ≤ 80#(D) + 324·d(X;D) by the closed-walk covering. Propagated: 324A ≤ δλ_Lκ in (10)(b), (e); (11)(f)'s 27A → 972A; (10)(f)'s /9 → /324; (12)(f) and (14): r/324, 20c_Dr, charges r/648.
- S2: (2.36′)'s 81⌈ℓ/(LM)⌉ was false for branched pieces; closed walk gives 243ℓ/(LM), (1+486/L), λ_L := L/max{2, 1+486/L} (= L/2 for L ≥ 486).
- m1: counterexample to (2.32) restated with d_k(Z₀) ≥ 8(n−1) (sharp constant between 8 and 18). m2: threshold t_k = δ_k/g_k = r_k in ‖𝒳‖_sup and the P-factors; γ-conditions become g_K-smallness; δ_k < ε₁. m3: scope label for (2.15)–(2.26) on CRE (3.27)'s measure (Bałaban's, pp.276–279, R-I7). m4: C₃^{(10)}; A is (10)'s own; "added restriction", not a reading. m5: (10) needs ½(κ₁−1) ≥ 2Lκ only; the order of choices is (1)–(2)'s, not p.21's; γ after ε₁. m6: product form of (2.26) over components.

## 4s11 (D2.4(11)) — S1, S2 and m1–m12 applied

- S1: (β) a′-transports: the gaps reach the touched intervals inside X_W; cost ≤ exp(#(G) + n(G) + Σ_W 20c_πM‖a′‖(diam X_W + 1)), paid from W's reserve weight ν_rσ_k(W) ((12)(b), (14)(d)), under c_πα_{1,k+1}·20M/L ≤ ν_r/16; never from e^{θ_k(W)}.
- S2: parity (f) stated at ω′ = 0 and away from older layers: the potentials are 𝐄_k's and 𝐑_k's terms with Lemma 2's structure (CRE p.276, Bałaban's); the boundary-type terms are analytic only on (3.43) with an extra O(ε_k) (CRE pp.276–277) and belong to the older-layer item.
- m1 (|𝐃| ≤ #_k(Y₀) false → (2.20)'s sum), m2 (B′_ev = −[hD̃(g_kCB)]_ev, second order, RG1 p.267), m3 ("forced" dropped), m4 (δ_k = (A₁/A₀)g_kp₀(g_k)), m5 (m(M) − 1 ≤ c_D#(G_M)), m6 (c_B M-independent), m7 (19683c_DA for the odd terms), m8 (polylog absent iff q ≥ p₀ + (q₁−q₀)₊), m9 (arcs in Ω_k), m10 (dev clause listed), m11 (touched X_W not in D_J^#; D2.2(6)(d) l.907 corrected), m12 (cosmetics).

## 4s12 (D2.4(12)) — S1–S5 and minors: (c)–(f) superseded by (14)

- S1: the arc link (iv) was group-dependent. (14)(b): windows win(v) = int(v) ± 20(diam_v+1), pair relation (iv′), covering lemma.
- S2: the root-position sum spent the shares twice. (14)(e): root at the vertex whose window or support contains p, paid by the root's spare e^{b/4}; the marked polymer found by the marked-vertex induction.
- S3: uniformity in k was false for kind (β) and for M-free groups. (14)(e)–(f): ε^{new} = ε^{new,α} + ε^{new,β}, ε^{new,β} ≤ K_β(b_k/ᾱ_k)ε^{old}; M-free groups quadratic; recursion C^{(k+1)} ≤ 2C_winC_M + θ_kC^{(k)} with θ_k ≤ ½ under (R-m′).
- S4: the per-cube clause of (ii-w) does not carry (factor ~L²). (12)(b): (ii-w) per traversal only; cube positions by the box reduction.
- S5: the weighted interaction clause misused (5.11). (14)(d): FV Thm 5.4 with activities |c|e^{sh+b} and weight a(W′) = positions·ε̂.
- Minors: vertices carry their touched W and vacuum links (dual role resolved); e^{|x|} of the vacuum links absorbed as e^{5c#(M)}; gap cubes in #(X(𝒢)); sh(M)'s ν_e·21#(M); transport budget ν_r/16; r = (L+2)κ/4; c_W = 0 by "vanishes at the reference point"; c5-5-8(a); (c4-6-5); (30/8)η_V → (6/8)η_V for (iii); species scope; grouping deterministic (D2.2(4)(e)); κ_D′, L₀ flagged.

## 4s13 (D2.4(13)) — S1, S2, m1–m12, m-T: (b)–(c) superseded by (14)(g)

- S1: group-level step missing. (14)(g): marked-vertex lemma with vertices = groups, links = incompatibility, weights |c_𝒢|e^{a°}, KP at a°/2; cluster sum ≤ 2δ_{k+1}.
- S2: vacuum links and flat factors differ on T, T′ by the non-embedding clusters. (14)(g): tail C_vacε^{new}e^{−ι_{T,k+1}/(2M)}; C_rel's recursion gets a tail term; (Z-d)/(Z-e)'s "no tail term" withdrawn.
- m-T: marks on touched insertions inside the M-vertex: the first term of the F recursion. m1: ext in the step metric, C_box ≥ 4A_E. m3/m10: pl in (ii-t)'s constant and in C_Z. m7/m8: ε^{diff} at amplitude ρ_k·pl; the factor ρ_{k+1}pl kept in the constant (contraction). m11: (13)(d)'s list corrected. (12)(d)'s "0.87Lκ" removed.
