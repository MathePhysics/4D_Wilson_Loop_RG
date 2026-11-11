# Table and Background Note after the D26, O4 and O2 Consolidations (10 Nov 2026): Triage

Input: (4)'s message of 10 Nov 2026 (D26 e966df384742, map e31a51aceaa4, O4 66508a10abe6, O2 c287b8f06abc), items 0–12, naming table rows #T12.14 and #T12.19-2 to #T12.19-11 and the background note as stale. Every quoted D26 text was checked against the file before any edit; all agree. The rows were announced to (4) before editing.

## Table (d71e239470ea → eb5a6a505303)

- #T12.14: #MD2.0.4.6-9 (absent from the map) dropped from the η_w, ν_e and τ̂² citations; C_X deleted (map #MD2.0.5.37 now has 8(64)^d and no C_X).
- #T12.19-2: ρ_ω := 2c_G′(C_w′ + 4C_{c₀} + 8C_odL)(1+β₀)²α_{1,1}r (D26 l.204), with #T12.15's C_w′, #T12.13's C_{c₀}, and C_o at BP_TL_GC_TRANSFORMS #6.17-2. The 5.0 constants after it moved to the new sub-row #T12.19-2-1 (length).
- #T12.19-3: (T0), (T2), (T3) are in D26 5.2, not 5.1; the old §8 pointer is dropped.
- #T12.19-4: c_A and H′ deleted (not in D26); C_inp := max(C_m^ℂϑ_V, 1) and C_I″ := C_link′C_inp·max_i#𝓕_{r_i} (l.283, l.289); C_III := e^{√2C_πϑ_*/2} + 1 (l.285).
- #T12.19-5: ℓ_𝐔, ‖A‖_μ, E, C_E, q_s^ℂ, C_K, C_Δ and their clash notes deleted; σ_γ := γ⁻¹N_lat(μ_H), C_m^ℂ := 2N_nbσ_γc_ℓ, K(s), m̂(s) with P and K_Δ, and ℓ_Λ (all 6.3, l.300–304); ℓ is the side of the aligned ℓ-cubes of CRE (1.10), (1.20) (l.290), not "V3's cubes".
- #T12.19-6: abs(𝓕), C′ with its ‖Y_i‖ clause, and m̂₀ deleted (not in D26); old §8 pointer dropped; C_m identified as IT-1 note §3j(5)'s constant (l.299), with clash notes against #T3.13 and #T12.7-19.
- #T12.19-7: R₀ := 1 + 2N_adj²e^{2^d+1}, C_st := 2^{N_adj+1}N_adj^{2N_adj}, D_i(X) as at l.326; F_i cites #T12.19-5's m̂(s).
- #T12.19-8 and new #T12.19-8-1: a_j (clash note against #T2.3's spacing), C_{B,1} (l.358), N′_{s,b} with P^s_W (l.362), C_h written out (l.379; clash note against #T4.35), 𝔅_Z with radius R_t and ties by the fixed order (l.382), C_in (l.383).
- #T12.19-9 and new #T12.19-9-1: C_A(j) := a_j + …; ε_A gains its j = 1 term 205^d(ℓ/ℓ₀+2)⁴C_rτ₁²·3·2^{d−1} (l.395), with ℓ₀ named as IT-1 note §3i(7)'s box scale; C_X deleted.
- #T12.19-10 and new #T12.19-10-1: Res(X) := (K₁/8)(d₁′(X)+1), Pol(X) := (K₁ − 2B₁ − K₁/4)(d₁′(X)+1) ≥ (K₁/2)(d₁′(X)+1) (l.409, which needs K₁ ≥ 8B₁, l.408); κ₁ as the modified (1.76), κ₁(Z) ≥ K₁(d₁′(Z)+1) − O(1)M^dR₁^{d+1}d₁′(Z) (l.405); LFR II's κ_j(Z) named apart from #T12.14's κ_j.
- #T12.19-11: B₁(Z) and y deleted; ε₁ cited to §8.3 (2)(iii) (l.477, l.493).
- #T12.19-12: §8.1 (l.440) and §8.3 (l.458–505; C_9 is in 8.3). A pre-existing circular entry "𝔹_j(Ω) := (𝔹 ∩ Ω^{∼−2}) ∪ (𝔹_j(Ω) ∩ …)" now reads "𝔹 ∪ 𝔹_j(Ω) := …", as at l.458.
- Back-references: #T12.7's C_K note, #T12.21's C′ note and #T12.23's C_X note no longer name the deleted entries; #T12.15-1's c̄ pointer, #T12.21's g_* pointer and #T12.23's K₁ pointer re-pointed to the sub-rows.
- My rows #T12.30-8 to #T12.30-10: 2√d → 2d in C_{A,n}, C_{A,1}, C^g_{A,n}; a_1 → a_j in a_j^g and C_A^g(j).
- Checks: relabel (LABELS 2d2801629f41 → 756f6e34c78b → 146c7b49d22b at LF 94d3e82675b1); defcheck "-- 0 lines"; dmarks2 "unentered candidates 16"; deadcheck and prefcheck known hits only; columns 9×5, 74×6, 267×7. Every edited row ≤ 660 characters.

## Background Note, Round 6 (narrow: the lines that cite D26)

Verdict: not clean (two minor findings).
- **F1** (minor, (iv-e)): the bound d_n′ + 1 ≤ √d·#cubes_n was cited to D26's ledger at j = 1, which no longer states it. D26 7.2's replacement "d_n′ ≤ #cubes_n" (l.393) is false for ∗-connected domains. Counterexample: the diagonal chain Q_k = [k, k+1]^d, whose corners are cut points, needs length ≥ √d(n − 2) (Euclidean) or d(n − 2) (edges). Repair: d_n′ + 1 ≤ d·#cubes_n, derived in place from RG1 p.257's definition of the linear size (in MR_n-cubes, LFR II p.380). A spanning tree of the ∗-adjacent cubes, with each cube's shared lattice vertices joined along its edges, gives an admissible connected graph of length ≤ d(#cubes_n − 2). So C_{A,n}, C_{A,1}, the class-(III) term of (W) and C^g_{A,n} carry 2d. The defect in D26 7.2 (and the factor d it puts on C_d′) was sent to (4).
- **F2** (minor, §5.3 (5) and the conditions list): the older-layer transports were quoted as 2c_π(b_d^c)^kα per traversal under 8c_π(b_d^c)^kMα ≤ 1, while D26 5.4 has c_π′ := 2c_π·max(1, c_h) and 4c_π′Mα ≤ 1. These agree only when c_h ≤ 1. Repair: the note now quotes c_π′ and 4c_π′.
- Bookkeeping: "D2.6 closure §9" → "§8" (seven places, §9.1 → §8.1); the carrier item's conclusion is stated as 8.3's, with 8.2's class empty; (iv-c)'s same-activity step now cites D26 7.4(a)'s locality with the coarse polymers X^g, and the conditions list no longer names D2.4(4) *Scope* and D2.3; "V3's marks" → "V4's marks"; a_1^g → a_j^g; the source lists name §8 for §8/§9 and add RG1 p.257 l.14–18 and LFR II p.380 l.28–29.
- Pre-check: every changed line re-read. bgptr reports only the known non-tags; bgdefs: 58 symbols, each defined once; bginternal: every interface item and condition defined; longest line 659 (the (iv-e) line was split at a sentence boundary). D26 2.1, 2.2 (ε^{new,α} ≤ C_Mb_k·pl), 4.2 (T_Y), 5.4, 6.2 *Units* and 7.1 *Which M* re-checked against the note's citations.
- Messages: two-loops (#NV.3-4-3, #NV.3-4-5 to #NV.3-4-7 quote 2√d, a_1 and the old C_{B,1}); (4) (the D26 7.2 defect, the ℓ₀ double use in 7.4(a), the SHAs).
- Size: 360 lines and 100,784 characters (249ae1a46a2a) → 362 lines and 101,074 characters (8510ab0aebd7).

## D26 30cd68b6dc51 (the Linear-Size Fix)

(4) fixed 7.2 (its *Linear size and cubes*: d_n′(X) ≤ d·max(N − 2, 0) for a ∗-connected union of N MR_n-cubes, by the spanning-tree construction above). C_d′ is now d(3(126)^d + 64^d + 2^d), which covers both Σ_{n>j}(d_n′+1) ≤ d(3(126)^dd_j′ + 64^dR_j) and Σ_{n≥j}#cubes_n. The box scale is now written ℓ₀^{box}, and the collar is defined in §1. All of this was checked against the file.
- Table (eb5a6a505303 → b168c70703ab): #T12.19's collar reads as D26 §1 (within 6 layers of Λ_{k+1}ᶜ, those of Λ_{k+1}ᶜ included); C_d′ is updated and moved to #T12.19-9-1 (length), with #T12.19-9 citing it; ℓ₀^{box} in #T12.19-9; #T12.30-8's C_{A,1} is written with LM_VR₁/ℓ₀^{box}. LABELS 146c7b49d22b → 4fa7e813cc81 → d444e40b4233. Checks as above, all passed.
- Background note (8510ab0aebd7 → 7bb5f99918ab): (iv-e) cites D26 7.2 *Linear size and cubes* for d_n′ + 1 ≤ d·#cubes_n and drops its own derivation (state once), so the RG1 p.257 and LFR II p.380 source entries go too.
- **F3** (minor, round 6, (iv-e)): the note uses ℓ and ℓ₀ for labels (§1.6, (iv-e)'s opening), but (iv-e)'s 205^d(ℓ/ℓ₀+2)⁴C_rτ₁² used them for the cube side and the box scale. Repair: 205^d(LM_VR₁/ℓ₀^{box}+2)⁴C_rτ₁² per cube of side LM_VR₁, naming D26's ℓ and ℓ₀^{box}.
- Messages: to (4), the SHAs, the #T12.19 collar edit (not announced before) and the SW re-point. To two-loops (NV 53550dbb2832): #NV.3-4-5's ℓ/ℓ₀ clashes with NV's labels (D26 writes ℓ₀^{box}), and #NV.3-4-3 and #NV.3-4-7 carry 2d and 4d. A third point, that C_lw^{III} is no longer defined in D26 6.3, was wrong (l.308 defines it) and was retracted.
- Bookkeeping: (C6)'s "(S-w) with k-independent constants (SW closure §7)" now cites SW §6(6e) ("C_S = e^{2ν_e}C_S′ … uniformly in k") and map #MD2.4.13.19-11 (pl = 2), since SW §7 is being deleted; the SW source entry reads §6(6a)–(6c), (6e).

## Background Note, Round 7 (narrow: the changed lines and their consumers)

Verdict: clean. No fatal, serious, minor, or cosmetic finding.
- Re-read: §3.1 *The complement*, §3.4's carrier-item line, (a) of the attached-species list, (iv-a), R_bad, (iv-e) through *The weights fit (11.3)*, §5.3 *What the objects force*, (5), *The totals*, *The carrier item*, (iv-c), (iv-b) at k = 1, (C6), and the conditions list ((W), (W^g), the transport conditions).
- C_{A,n}: 2A_n ≤ 2e^{c_W}C_A(n)(d_n′+1) ≤ 2d·e^{c_W}C_A(n)#cubes_n. At n = 1 the class-(III) term 2d·e^{c_W}C_lw^{III}M_VR₁ against L^dM^dR₁^d. Every consumer uses the 2d form.
- (iv-a) asks for the carrier item at general k; §5.3 discharges it at k = 1 with no carrier species. These are consistent.
- Pending in another session's file: two-loops' #NV.3-4-2, which (W) cites, states (W^𝔉) for (iv-e)'s C_{A,n}, but its proof (#NV.3-4-3, #NV.3-4-5 to #NV.3-4-7) still quotes 2√d, a_1 and the old C_{B,1}. The argument is unchanged; two-loops has been sent the corrections.
- bgptr (known non-tags only), bgdefs (58, each once), bginternal (all items and conditions defined); longest line 659; 361 lines and 100,676 characters.

## Background Note, Round 8 (full: every line of 7bb5f99918ab)

Verdict: not clean (one minor finding and one cosmetic finding).
- **F4** (minor, (iv-a)'s carrier item): it asked that g_k^{(j+1)}'s pending-variable dependence be "carried as the carrier species with §8's bound". D26 30cd68b6dc51 §8 has no species and no bound. Its conclusion (8.1, 8.3, 8.4) is a support statement: V_i^* = M^iU_{k+1} lies in the full step-i support (χ_i(□)(V_i^*) = 1 and χ_Ax = 1), which is the input of (T-dev)'s global induction (map #MD2.4.5.13-9). Repair in place: (iv-a) now asks for exactly that, plus g_k^{(j)} = g_k^{(j+1)} at B′_j = 0 on 5.1(a)'s terms, which §5.3 *The carrier item* proves. §5.3 now cites (iv-a) for the gloss instead of restating it, and it, *The complement* and 5.1(a) no longer use the undefined "carrier species". The opening list reads "attached species with D2.6's bounds and its carrier item".
- **F5** (cosmetic, §1.1): two parentheticals in a row ("… T_c) (for k ≤ N − 1, …"); reworded to "…, and for k ≤ N − 1 (…)".
- Re-derived in full and correct: §3.1's identity (N_kκ^{g_k,(K)} = κ_f^{(K)}e^{E^f_{const,k}}); §3.2's 𝐑-part sum (the bracket, 2s_j + 1 ≤ MR_j(8/c^R_E + 1)(2y + 1), (1 + x)e^{−x/2} ≤ 2e^{−1/2}, m̂^{β₀} ≤ L^{m/2}, the sum lemma, r^R_K), the exponent-difference factor, and log N_k; the §3.3 sum 8.48/(L − 1); §4.1(3)'s chart arithmetic (0.05 + 0.048, the M ≥ 6(d+2)/c_π step, 1.06·44/8 = 5.83); §4.2's b_d and 1.2b_d (8.91 ≤ 9.2, ratio ≤ 1.184), and ‖V − 1‖ ≤ 0.075 and 1.04; (iii-d)'s 17/16·3.1 ≤ 3.3, 4θ(1 + θ)³ ≤ 4.1θ, (103R_j)^d, 3.31, 1330, 444 + 400, and τ_c ≤ e^{0.52} under (C4R); (iv-b)'s tube count and the β-function sum (both ranges, 5/4 + 2G′/(p₀b(log G′)^{p₀−1})); (iv-e)'s ℒ_K term 2e^{c_C}δ_LF; §5.3's ε_A^g against D26 l.392–395, c_X = 81·25921·e^{1+ν_e}, (4)'s 1.12, and (iv-b) at k = 1 with e^{1/10} under (C5); the constant conditions (C1)–(C6).
- Pre-check: changed lines re-read; "carrier" grepped file-wide (l.6, 39, 104, 110, 140, 235, 239, 243, 245, 263, 291, 292, 295); the map's #MD2.4.5.12 and #MD2.4.5.13-9 looked up and added to the sources; table #T12.30's "V_i^* (iv-a) is #T12.19-12's" still holds. bgptr (known non-tags only), bgdefs (58, each once), bginternal (all items and conditions defined); longest line 659; LF only (byte count; Git Bash's grep -c for CR gave a false count); 360 lines and 101,130 characters.

## Background Note, Round 9 (narrow: F4 and F5 and their consumers)

Verdict: clean. Re-read l.6, 33, 39, 104, 235, 239, 243, 291, 292, 295 and 323. (iv-a)'s two parts are exactly what §5.3 *The carrier item* proves: the support statement holds for both chains, and g_k^{(j)} at B′_j = 0 is g_k^{(j+1)} on every term, with the pending variables entering through U_{j+1}(V_{j+1}) as in f_{j+1}. 5.1(a), l.239 and l.295 read consistently with it.

## Background Note, Round 10 (narrow: every SW citation, against SW 1eeaeff9e212)

Input: (4)'s message (SW 18ca95375171 → 1eeaeff9e212, map 796d26f6e193, D26 30cd68b6dc51, D27 9b3902e3545b). I read SW's opening, §1–§4, §5's heading and (e), and §6(6a)–(6e) in the new file. Verdict: not clean (two minor findings).
- **F6** (minor, §4.1(3), (C4)): the chart proof bounded a′ only by α_{1,j+1}L^{−(j+1)}, which is the radius on Ω_{j+1}, or on 𝒟^{sub}, where (S-w) is evaluated (SW §3(b3), (6b)). But (D3) and (iii-b) assert analyticity on all of D(j+1)(iii)'s domain, as SW §3(b2) needs for the class. That domain's older-layer radius is f_{j+1,n}α_{1,n}L^{−n} (SW §3(b1)), and the round 8 check of (C1)–(C6) missed this. Re-derived: an inner bond's blocks lie in Ω_k (§1.6), so the tube's layers have n ≥ k. Hence L^k·phase ≤ max(α_{1,j+1}L^{k−j−1}, α_{1,n}L^{k−n}) ≤ (1+β₀)α_{1,K}, and |𝐇| ≤ O(1)·4B₀e^{16κ_s}ε_H on every layer (D26 4.2's form, Lθ ≤ 1 by SW §6(6e)). Repair in place: (C4) := 1.06(d+2)(b_d^c)^{k−1}c_h(O(1)·4B₀e^{16κ_s}ε_H + (1+β₀)α_{1,K}) ≤ 1/22, on every layer. At k = 1 it holds under (Cε), since O(1)·4B₀e^{16κ_s}ε_H ≤ 1/(4.48c_π′M) and 1.06(d+2)/(8.96c_πM) ≤ 1/44 once M ≥ 6(d+2)/c_π (1.06·44/8.96 = 5.21). (C4γ) was (C4) with /L on 𝒟^{sub}, so (C4) now implies it and it is deleted; §5.3 (4) cites (C4), and its transport count names 𝒟^{sub}_{j+1}. Consumers re-read: the opening, 4.1(4), 4.2's complex recursion, (D3), *At another fixed k*, and *Derived here*. None depends on the /L.
- **F7** (minor, 5.1(a)): it listed groups that "meet the collar Coll_{j+1} …" as excluded from (S-w)'s scope by SW §1(a3)(i)–(iii). Under SW §1(a1) the scope tests are D26 2.1(i)–(iii), and (i) concerns the one-layer neighbourhood of Λ_{j+1}ᶜ, not the collar. Repair: §2.2's parity exclusions (map (5) *Scope*); the groups failing 2.1(i)–(iii), outside (S-w)'s scope and att(j+1, coll); and a group failing only 2.1(iv), att(j+1, Z) inside the scope (SW §1(a2)).
- Bookkeeping: (iii-b) cites the species of map #MD2.0.3.22–#MD2.0.3.25-1 by D26 2.1's tests (SW §1(a2)), read in full and added to the sources. The SW source entry reads "the opening, §1–§4, §5's heading and (e), §6(6a)–(6c), (6e)". (C6)'s SW §6(6e) and map #MD2.4.13.19-11 were checked against the new text.

## Background Note, Round 11 (narrow: F6, F7 and their consumers)

Verdict: clean. Re-read l.9, 158–161, 163, 172, 179, 186, 236, 284–285, 309, 317 and 354. One cosmetic finding was repaired: in 5.1(a) "these" could be read to include the parity exclusions, so the scope clause is now a parenthesis on the failing groups. bgptr (known non-tags only), bgdefs (58, each once), bginternal (all items and conditions defined; (C4γ) is gone); longest line 659; LF only; 361 lines and 101,353 characters.

## Table: SW's Conditions (9f6ebf47c805)

Announced to (4) before the edit. #T3.31 (VAR's a₁) now records SW's shrink conditions a₁ ≤ 2/(9O(1)B₃R₁M₁) and O(1)ξa₁ ≤ 1. Here ξ = L^{−1}η ≤ 1 (SW §5(2), (6)), and a₁ is taken at #T2.7's printed R₁M₁ (R₁ = R₁^V, map #MD2.2.6.190-22), not at #T1.6's raised M′. New sub-row #T1.5-1 holds (C-M), whose M₁ is VAR's, not #T1.5's CRE M₁. Lθ ≤ 1 is a smallness condition on g and gets no row. The printed-versus-raised point was sent to (4) for SW. Relabel → LABELS 1f2b3fa09b9d at LF 94d3e82675b1. defcheck "-- 0 lines"; dmarks2 16; deadcheck and prefcheck known hits only, shifted one line by the new row; columns 10×5, 74×6, 267×7.

## Background Note, Round 12 (full: every line of 22a230556c65)

Verdict: clean. Every line was read, and every arithmetic step was redone: §3.2's 𝐑-part bounds (2s_j + 1 ≤ MR_j(8/c^R_E + 1)(2y + 1), (1 + x)e^{−x/2} ≤ 2, the m̂ exponents at β₀ ≤ 1/4, the Cauchy sum lemma's 2 + 24R̂_K/c^R_E), the r_j and N_k sums (P_{j−1}(C) = 4ℓ_CL^{K−j+1}), 4.1(3)'s layer maximum, 4.1(4)'s constants (1.04·1.06 ≤ 1.11), 4.2's ratio 1.184 and the bound 0.075, (iii-d)'s numbers (4.1θ, 103R_j, 1330, 444 and 400), §5.2's series in G′, and 5.3 (4)'s per-cube factor.
The NV update 53550dbb2832 → 0c758282badc keeps #NV.3-4-2's statement, and (W^𝔉) at N_C = 1 is (iv-e)'s (W) (#NV.3-4-1), so l.316, 328 and 348 stand. Two consecutive clean rounds (11 narrow, 12 full): the note is done at 22a230556c65.

## D26 7.3's Conversion Factor: K₁ and K_{j+1}

Source: RC_PAYMENT 672f30ee25ee #RP.5-2-1 to #RP.5-2-2, re-derived here.
- K₁ takes d^{−1}(434)^{−d}. 𝒳 is ∗-connected, so d₁′(𝒳) + 1 ≤ d·#cubes₁(𝒳) ≤ (3/2)d(430)^dΣ_G(d₁′(G)+1), and at d = 4 this exceeds 2(434)^d, as (434/430)⁴ < 3.
- K_{j+1} can keep 2(14)^d. p.385's first inequality holds: (Z^{(i)})^{∼3} is face-connected, so a tree through face-adjacent centres gives d₁′ ≤ #cubes − 1. The gap is the union step d′(Z) ≤ Σ_id′((Z^{(i)})^{∼3}), whose trees need not lie in Z. The ∼2 route closes it: d′(Z) + 1 ≤ (3/2)d·10^dΣ_i(d′(Z^{(i)})+1), and (3/2)d·10^d ≤ 2(14)^d for every d ≥ 1 ((3/4)d ≤ 1.4^d).
- My 18:24 message to (4) wrongly gave K_{j+1} the factor d, since I had not checked that the enlargement is face-connected. Two-loops corrected it at 18:25, and I sent (4) a retraction.
D26 2dce56a49737 (checked at l.29, 389, 409–410, 414–415 and 427–430): K₁ has d^{−1}, κ₁'s absorption term is ·(d₁′+1), and K_{j+1} keeps 2(14)^d by the direct route (d ≤ (4/3)(7/5)^d). l.410 and l.428 place the gap at the union step, and §1 *Counting cubes* quotes RG1 p.257's "contained in X".
Table edited after the announcement to (4): #T12.19-9-1 (K₁ with d^{−1}) and #T12.19-10 (absorption term ·(d₁′(Z)+1)); #T12.19-11 is unchanged, and #T10.28-1 already has "contained in X". Relabel → LABELS 740b198d7a9d, table 0fa578b35726, at LF 94d3e82675b1. defcheck "-- 0 lines"; dmarks2 16; deadcheck and prefcheck known hits only; columns 10×5, 74×6, 267×7. The background note is unaffected: it uses K_{j+1} only in "ε_A^g ≤ K_{j+1}/8 for small g_*" and "Pol(Z) ≥ (K_j/2)(d_j′(Z)+1)".

## COMPLEX_COVARIANCE f1cbf76fb687, Map 656eed60159c, SW 2be3106d4b2f

Table #T12.13: δ̄_m := min(δ̄, μ4^{−m}) → δ̄₀ := min(δ̄, μ), δ̄ := min(1/2, CM/(2L)), with C the cube constant of CRE (2.38) (the note's (K1)). Checked against map #MOMGD.5-15 and the note's l.68 and l.101. δ_W (#MOMGD.5-10) is the same object. #T4.45 still matches the note: C_av, μ, *Averaging bound*, and the smallness of C_av(T₁ + T₃).
The table lists no K₁, Ĉ, c_nc or L ≥ 8 from the note, and it does not mirror #MOMGD.5-4 (deleted) or #MOMGD.23-1. The note's L ≥ 12(1+β₀)² and L > (1+β₀)⁹ follow from #T1.3's L ≥ L₀ = 5000. Announced to (4). Relabel → LABELS 58050f8936d3, table ef03c153b6ad; checks as before.
Background note: bgptr gives known non-tags only against map 656eed60159c, so every cited map tag resolves. SW 2be3106d4b2f keeps the opening's (a)–(d), §1(a1)–(a2), §3(b1)–(b3), §5(e) and §6(6a)–(6e), and its new opening sentence (the printed R₁M₁) matches table #T2.7 and #T2.7-1. The note needs no change.

## O6 908c956d462e, Map 4393221aa40a

Table #T3.36: S_H ≤ g_k^{3/2}/16 (map #MOMGD.58) → S_H ≤ g_k^{3/2}/40 (map #MD2.2.6.193: 10S_H/g_j ≤ g_j^{1/2}/4), with S_H of #T12.13 (#MD2.2.6.185-2), whose definition is not repeated. "O6's (C1)" → "O6's (C3)", since O6's (C3), C₁^{RG2}ε_k^♯ < r_{α,k}/2, gives membership in 𝒫_k^m (O6 l.107, l.227). Announced to (4).
The other O6 row citing a condition already reads "𝒫_k^{3/4} under O6's (C3)". The table has no q₁ = p₀ condition. The background note's map tags all resolve in 4393221aa40a (bgptr known non-tags only). Relabel → LABELS 0e94a6174742, table cc3949e005fb; checks as before.

## Coarse-Chain d02ba134814f: Background Note and Table

Input: two-loops' message on the coarse-chain note d02ba134814f, with replacements proposed for the old l.184, 285, 289 and 317. Each was re-derived against the coarse-chain note before use. They were applied in c_π′ form, with the old l.183–184 merged into a pointer to #CC.2.2-4 and #CC.2.2-5.
- (iii-a): ε_H^{(k)} := ε_H/(b_d^c)^k, and I^{(k)}(G) as #CC.0.9–#CC.0.10 define it, a bond carrying (M^k𝐔)(c) or T_c(𝐔) by #CC.0.6. The arc product is #CC.2.2-4, from #CC.1.3's per-bond bound exp(c_π′(b_d^c)^kℓ_kh(c)) and #CC.1.2-2's 1.03c_CML^{j−k} bonds per cube, with ℓ_k (#CC.0.3) and h(c) defined in place. 𝔞̄^g ≤ c_X(b_d^c)^{2k}𝔞̄ is cited to #CC.4.4 and #CC.K.3.
- §5.3: the (1) domains cite #CC.4.1-4–#CC.4.1-6, #CC.0.10 and #CC.3.3-1. (4)'s per-cube factor is exp(1.03c_π′c_CM·O(1)·4B₀e^{16κ_s}ε_H)·exp(1.03c_π′c_CM(b_d^c)^kα_{1,j+1}/L). (5) is under (C9). c_X = 2099601e^{1+ν_e+5ν_f/L}(1+Ĉ^g)/(1+Ĉ), with pointers for ν_e, ν_f, Ĉ and Ĉ^g. (iv-c)'s locality cites #CC.1.1-1 and #CC.4.1-4. (Cε) now also implies the coarse-chain note's (C7), and the conditions list cites (C9).
- Re-derived: per cube, 1.03c_CML^{j−k} bonds times c_π′(b_d^c)^kL^{k−j}h(c) give 1.03c_π′c_CM(b_d^c)^kh. The 𝐇 part is ≤ 1 under (Cε), as 1.12 ≥ 1.03 and O(1) ≥ 1. (C9) at i = j+1 gives 1.03·4M·c_π′(b_d^c)^kα_{1,j+1}/L ≤ 4.12ν/(4096L) ≤ 1 and 4c_π′(b_d^c)^kMα_{1,j+1} ≤ 4ν/4096 ≤ 1, with ν ≤ 1/1000 (map #MD2.4.13.19-3).
- Pre-check before round 13: ℓ_k and h(c) were undefined at their first use, ν_e, ν_f, Ĉ and Ĉ^g lacked pointers, and table #T12.13-1 still listed (iii-a) as a c_π^ℂ user. All three were repaired.
- Table, announced to (4): #T12.30-9's c_X is the coarse-chain note's (#CC.K.3), not #T12.20's. #T12.13-1's pointer is now "(background note 4.1(4), (iii-d))". LABELS 0e94a6174742 → 021eb3aaac12 → 4c2c66efb348; table cc3949e005fb → 7d4eab358ced → 77c1b5ec9928. defcheck "-- 0 lines"; dmarks2 16; deadcheck and prefcheck known hits only; columns 10×5, 74×6, 267×7.
- Round 13 (narrow: the changed lines and their consumers): clean.
- Round 14 (full): not clean (two minor findings).
  - **F8** (l.280): X^g, 81 and 25921 were cited to "coarse-chain note §1–§2", and the sets were written Q^g. Repair: #CC.4.1-4–#CC.4.1-6 and 𝒬^g.
  - **F9** (l.293): (iv-c)'s locality pointer was stale. Repair: #CC.1.1-1, #CC.4.1-4.
- Round 15 (narrow): not clean (two minor findings in the repairs).
  - **F10**: F8's repair cited I^{(k)}(𝒢) to "§1–§2 there". Repair: #CC.0.10, #CC.3.3-1.
  - **F11** (l.182): the description of I^{(k)}(G) did not match #CC.0.9–#CC.0.10. Repair: the union over Y ∈ G of the smallest arcs of C^{(k)} containing the scale-k bonds whose blocks meet Y.
- Round 16 (full, c7612b0d6f3b): not clean (one minor finding).
  - **F12** (l.326): the coarse-chain source entry read "its notation, §1–§4, …". The note has no notation section, and the note cites #CC.0.1, #CC.0.3, #CC.0.4 (its opening) and #CC.0.6, #CC.0.9, #CC.0.10 (*What the Objects Are*). Repair: "its opening (#CC.0.1–#CC.0.4), *What the Objects Are*, §1–§4, §6, *Constants and Conditions*".
- Round 17 (narrow: F12): clean. Every #CC tag the note cites lies in the listed parts and exists in d02ba134814f, and so do §3.3, §3.5 and §6.
- Round 18 (full: every line of df792ffa33f3): clean. Map d3dc46ddacc5 still states what the note cites (ν_f = 17ν/16 and ν_e = ν/(2C_box) at #MD2.4.12.21, ν ≤ 1/1000, and the e^{1} per cube of #MD2.4.11.4-1). bgptr gives known non-tags only, bgdefs 58 symbols, and bginternal reports (C7) and (C9) as the coarse-chain note's. Longest line 659; LF only; 360 lines and 101,347 characters.

## Map d3dc46ddacc5: C_pc′ and c_π′ (Table)

Input: (4)'s message. Checked against the map (#MD2.4.8.1, #MD2.4.12.21-1, #MD2.4.12.27-1, #MD2.4.12.27-3, #MD2.4.12.27-6, #MD2.4.12.28, #MD2.4.12.28-0). Re-derived: 40c_π′α_{1,k+1} ≤ 40ν/(4096M) ≤ 1, and ν_e + ν_r/16 = ν/(2C_box) + ν/16 ≤ ν ≤ 1/1000, so e²C_pc bounds C_pce^{40c_π′α_{1,k+1}}e^{ν_e+ν_r/16}.
- #T12.17: sh(v)'s transport term is c_π′α_{1,k+1}abs(win(v)), with #T12.20-3-2's c_π′. C_pc′ := e²C_pc bounds a piece's C_pce^{40c_π′α_{1,k+1}}, times e^{ν_e+ν_r/16} for a touched W. b(M-vertex)'s (r/648) now reads (r_κ/648), as #MD2.4.12.27-3 prints it.
- #T12.13-1: #MD2.4.8.1's transport constant is now c_π′, so the row says that in a sentence of its own, after the c_π identifications, naming #T12.20-3-2's c_π′.
- #T3.37's ε′, with (20c_πc_hC₁^{RG2})^{−1}, agrees with the CA closure's and the map's ε′, and #T4.46's 2.12c_πc_h agrees with the map's #MOMST.50-1. Both are unchanged. The background note uses neither C_pc′ nor #MD2.4.8.1, so it needs no change.
- Announced to (4). LABELS 4c2c66efb348 → eb6a64d31149 → 734a37930def; table 77c1b5ec9928 → 33fe77b016b2 → 18cbd119fc8f. defcheck "-- 0 lines"; dmarks2 16; deadcheck and prefcheck known hits only; columns 10×5, 74×6, 267×7.

## NL 204c1c20c891: L₀^{(N)}, u_𝔏^{(N)} and A′_E (Table)

Input: two-loops' message (NL 204c1c20c891, NV 5137fb31c48d). Checked against NL #NL6A.6, #NL6A.9, #NL6A.9-1, #NL6B.1-1, #NL6B.1-2, #NL12.1, #NL1.5 and #NL9.6-1.
- Re-derived: #569's condition at u_𝔏^{(N)} = (N_C/2)u_𝔏 reads (N_C/2)²u_𝔏(8496ν_f + 88ν_e)/L ≤ ν_r/4. With ν_f = 17ν/16, ν_e ≤ ν/8 and ν_r = ν, it needs L ≥ (N_C/2)²·36152u_𝔏, which L₀^{(N)} := (N_C/2)²·4·10⁴u_𝔏 = 10⁴N_C²u_𝔏 covers. The transport check 352N_C²u_𝔏 ≤ 4096L also holds.
- #T1.3-1: L₀^{(N)} := (N_C/2)²L₀^× = 10⁴N_C²u_𝔏, still L₀^× at N_C = 2. The row adds the unit u_𝔏^{(N)} := (N_C/2)u_𝔏 of the 𝐑-made insertions, which replaces u_𝔏 in every condition of two-loops #917 that contains u_𝔏.
- #T4.51: A′_E := 17(2R_e + 1)⁴, the pair's, for every N_C (#NL1.5, #NL9.6-1), in place of (8N_C + 1)(2R_e + 1)⁴. N_C is dropped from ν_×'s dependencies.
- No row cites NL's u₁^{(N)} or C′. The table's u₁ is the pair's (#532).
- Announced to (4). LABELS 734a37930def → c59773513fd1; table 18cbd119fc8f → 05cbd40be4db. defcheck "-- 0 lines"; dmarks2 16; deadcheck and prefcheck known hits only; columns 10×5, 74×6, 267×7.

## General Loops 1d61bc4589e2: #T12.31 Rows and #T4.53's C_w (Table)

Input: the BETA session's message (general-loops note 1d61bc4589e2, derived, not reviewed). All 246 lines were read. Every symbol the note defines with ":=" was entered, and every clash, square-case, and pair-case pointer was looked up in its table row.
- New rows #T12.31, #T12.31-0, #T12.31-1, #T12.31-2, #T12.31-3, #T12.31-3-1, #T12.31-4, #T12.31-5, #T12.31-5-1, and #T12.31-6 to #T12.31-11, after #T12.30-10. Local symbols are listed with their tags.
- Re-derived: 1000·9Λ̄η(C) = 0.0075 < 1/128; 1000·9Λ̄η(𝒞) = 0.015/max(N_C, 2) < 1/(64max(N_C, 2)); 2(10Λ̄ + 1 + 10Λ̄/c_w) ≤ 41Λ̄/c_w; 2N_C(14Λ̄u + 1 + 14Λ̄u/c_w) ≤ 58N_CΛ̄u/c_w; (1 + (5/2)N_C)ν + (3/8)ν/5832 ≤ 4N_Cν; and u_𝔏(𝒞) ≥ u_𝔏^{(N)} and L₀(𝒞) ≥ L₀^{(N)}, as Λ_N ≥ 4N_C.
- The square cases were checked against #T12.13 (A_h = 17, η = 1/2 400 000), #T12.17 (C_win, abs(win_M)), #T12.16 (κ_{k+1} = e^{−δm_{k+1}P_k}z_{k+1}⁴ with z_{k+1} = e^{ζ_{k+1}}), #T12.20-5, #T12.10, #T4.36, and #T12.30-4's x_k. The pair cases were checked against #T4.54's λ_K, #T12.2-15's E* and w̄^×, #T4.52's A^cr, and #T4.42's c_off.
- Pre-check, before entry: #T4.31 and #T4.53 have ε^r_k, not r_k. #T4.54's λ_K is the pair sum that λ^{(N)}_K generalises, not a clash. The map's c_h is #T3.37's.
- Round 1 (full): G1, (v_c, w_c) was not ordered. G2, 𝒞 and N_C were used before they were defined. G3, the general stopping j was undefined. G4, the physical u and the insertion's units factor u shared one row. G5, V4's R_* and μ were undefined and clash with #T2.11's R_* and the table's μ's. G6, σ, ℓ_σ, v_σ, κ_v, and ζ_{v,w} in κ_C were undefined, and n_σ was listed as local. G7, κ^R_v was undefined.
- These were repaired with the sub-rows #T12.31-0, #T12.31-3-1, and #T12.31-5-1; no tag was renumbered.
- Round 2 (narrow): G8, ℓ_v was undefined. G9, #T12.31-10 restated 𝒞 = (C_i). Round 3 (narrow): G10, "bent path" was undefined. Round 4 (narrow) was clean.
- Round 5 (full): G11, C^𝒦_E was called a coefficient of the remainder rather than of its bound. G12, the map's C_Σ in B_E and E* clashed with #T10.35's and Cauchy §8's C_Σ; it is now C^E_Σ, as in #T4.37.
- G13, the pair's wrap constant C_w of #T12.2-15's w̄^×, #T12.3-1's τ^{w,×}_K, and #T12.3-3-1's t_m was never defined in the table. #T4.53 now defines it from two-loops #893, and #T12.31-11 cites it. Round 6 (narrow): G14, "at most 16" read as a bound on C_w; it is the product of the 𝐑-steps' factors.
- Round 7 (narrow) and round 8 (full) are clean, so the rows are done.
- For the BETA session (information only): #GL5.6 says that P_{K′}(C) replaces 4ℓ_C in #ND.5.3, but #ND.5.3's B_E has ℓ_CA^R_ES_E. With #GL5.4-2's "P_{K′}(C) for ℓ_C", the note's B_E is a valid weakening, but #GL5.6's wording does not match #ND.5.3.
- Announced to (4). LABELS c59773513fd1 → da1678b546aa → 8dfd147baf9e → dedd7d4ac789 → 3a3ed06cb922 → 68c8c9eaccb0 → be350896ce4a; table 05cbd40be4db → 40393683f6ae → fae38e82fd19 → 7ecb9fb4dd48 → 3448ffd15a23 → 6a98e1e05152 → 7b51b1177ee9. defcheck on LF and on the general-loops note: "-- 0 lines" each; dmarks2 16; deadcheck and prefcheck known hits only; columns 10×5, 74×6, 267×7.

## General Loops 6919e16b2fdd and the Pair Note's §3: #T12.31-0, #T12.31-11-1 to #T12.31-15, #T12.4-1-1 to #T12.4-1-3 (Table)

Input: the BETA session's message (general-loops note 1c99048d720c, §3.13, §3.14 and §8; then 6919e16b2fdd, which restructured #GL3.13), and the ten ":=" lines of the pair note's §3 (9b4918036466) that no row cited.
- New rows #T12.4-1-1, #T12.4-1-1-1, #T12.4-1-2 and #T12.4-1-3 after #T12.4-1, and #T12.31-11-1 and #T12.31-12 to #T12.31-15 after #T12.31-11. #T12.31-0 now defines Q and the general stopping j, and #T12.31-11 lists its local symbols.
- Re-derived: for a square, N_lad = ℓ_i² and P_{K′} = 4ℓ_i give a^{ty}_i ≤ c_tyℓ_i²ε_ty + ι^{ℓ₀}_i. N_lad ≤ 12ℓ̄_idiam_{K′} ≤ 6ℓ̄_iN_s, ℓ̄_i ≥ 1 and 4·1.06 = 4.24 give a^{ty}_i ≤ ℓ̄_i(c^𝒦_tyN_sε_ty + ι^{ℓ₀}_i). Also ℓ̄_iuL^{−j} = P_phys(C_i)/4.
- Pre-check, before entry: defcheck flagged #GL.1's ℓ̄_i and #GL3.13-2's S_q, and both are now cited.
- Round 1 (full): H1, #T12.4-1-1 gave #T12.7-13 for P(Z), which is #T12.7-29's history volume (and C_P is #T12.7-31's). H2, ext_𝒜 was compared with ext^{coll}_j, which is measured in π_j-sides; ext_𝒜 is #T12.19-2's ext^{(n)}, and at j = 1 #T12.19-3's ext^{𝒩,(n)}.
- H3, #T12.4-1-2 left IT-1's μ₁′, C_s, C_net and N_nb unnamed, and its C_s and C_net clash with #T4.26's C_s and #T12.31-3-1's C_net(C). Also, κ is set in §3i(6), not §3i(7). H4, #T12.4-1-3 gave no pointers for c_d (the map's, #T12.16, which clashes with #T4.20's) or for 𝔞_{K′} (#T12.14).
- H5, #T12.31-13's N^{nr} omitted the general forms of A^×, C^×_E and C^{R×}_E, and the long-group term that it drops. H6, #T12.31-14's C_i^{(K′)} clashed with #T12.4-4-1's coarse square.
- After the repairs, #T12.4-1-1 had 743 characters, so it was split, giving #T12.4-1-1-1. N_nb := 7⁴ also defines #T12.19-5's N_nb.
- Round 2 (narrow) was clean.
- Round 3 (full): H7, the table lacked the general-loop C^×_E (its third term from #GL6.5-1), A^{cr,R} and C^{R×}_E. The new row #T12.31-11-1 gives them.
- Between rounds 2 and 3, general-loops note 6919e16b2fdd removed ρ_q, S_q and Sq from #GL3.13. #T12.31-12 now records only C_lift, re-derived against #GL3.13-2 to #GL3.13-5.
- Round 4 (narrow): H8, #T12.31-11-1 wrote ℓ₁ + ℓ₂ where #GL6.5, which covers N loops, has ℓ_Σ, and its "there" was ambiguous. Rounds 5 (full) and 6 (full) are clean, so the rows are done.
- The map's C_box against V4's requirement (V4 sec:c4-8-4, L5445; sec:c4-11-4, L5665, L5669), reported by the BETA session, is closed by map #MD2.4.12.7-1-1 to #MD2.4.12.7-1-5 (next section).
- #T12.4-1-1-1, #T12.4-1-3, #T12.31-11-1 and #T12.31-15 were entered without being announced first; (4) was told with the SHAs. LABELS be350896ce4a → db3a90533fee → d69b9435f903 → 5d8d0ba1ca16 → 2a8dd17d3301 → 540553777186 → ffab237c713a → 9eeed3a7792e.
- Table 7b51b1177ee9 → 5aa1d07d9bc7 → f5ad27b19f5e → 5d3828b85a8c → 037a49add938 → 3bc66748fda4 → 2a080272da0e → bb2bbb3fbd08. defcheck on LF, on the general-loops note and on the pair note: "-- 0 lines" each; dmarks2 16; deadcheck and prefcheck known hits only; columns 10×5, 74×6, 267×7.

## IT-1 caac168e83ce: C_box, ϑ_V, c_b and the §3e Constants, #T12.32 to #T12.32-9 (Table)

Input: (4)'s messages (the map's C_box count; ϑ_V, c_b, B₁, the §3e constants and C_DJ; IT-1 §3g consolidated, §3h deleted).
- Rows: #T4.44 cites #MD2.4.12.7-1-5. New #T12.19-4-1 gives ϑ_V. #T12.19-9-1 now carries c_b and separates CRE's B₁. The new block #T12.32 to #T12.32-9 covers IT-1 §3e(0)–(6), §3f(3) M8 and §3g(1).
- Re-derived (C_box), from map #MD2.4.12.7-1-2 to #MD2.4.12.7-1-5:
  - diam_∞(Q_W) ≤ 18LMn(W) + 4L + 2(8M + 4L) ≤ 19LMn(W), since LM ≥ 12L + 16M for L ≥ 54 and M ≥ 8L.
  - Under (eq:c4-8-9), n(W) < b/(4C_boxLM), so C_box ≥ 19 makes the lift injective and puts Q_W within b/4 of a contact.
  - The Euclidean diameter is at most twice the ℓ∞ one, so C_box ≥ 38 suffices, and 2916 meets V4's requirement.
- Round 1 (full) found R1–R3:
  - R1: #T12.32 used h_ℂ undefined.
  - R2: #T12.32-4 said ϑ_* is taken over the closure of 𝒱_{ρ₀}, but ϑ_* is chosen, not a supremum.
  - R3: #T12.32-6 left V4's C_M and N_lat unnamed.
- Round 2 (narrow) found R4. The R2 repair said ϑ_* is chosen from C_C and C^a_k. In fact V4 fixes C^a_k after ϑ_* (V4 L4264, L4542), and ϑ_*'s conditions use only ϱ_*, H_* and K_*. #T12.32-4 now lists the six constants that K′ takes over the closure.
- Also from round 2: IT-1's K′ bullet places C^a_k and C_p before ϑ_*, although its *(iv) at 𝐔* needs C^a_k ≥ e^kk!(4/ϑ_*)^kC_𝒢. Reported to (4), with a suggested repair. The table row holds under either order.
- Round 3 (narrow) was clean. Round 4 (full) found R5 and R6:
  - R5: #T12.19-4-1 omitted #T12.19-8-1's C_h, which writes ϑ_V as ϑ (D26 §7.1, l.381; reported to (4)).
  - R6: #T12.32-5 cited 𝓔(r_n) to §3e(3.9) and called 𝓔_c a set fixed by r_n. 𝓔(r_n) is defined in §3e(3.8), as the bond set 𝓔_c of the row c of the traversal n (V4 L506).
- Round 5 (narrow) was clean. Round 6 (full) found R7: #T12.32-6 took μ_x from #T12.19-6, but no row defined μ_x or μ_H. The row now gives μ_x := μ_H/20 (IT-1 §3j(5)) and V4's μ_H := γ/(h_+ρ_L) (V4 Lemma c5-1-1).
- Round 7 (narrow) and round 8 (full) are clean, so the rows are done.
- During rounds 6–8, IT-1 went caac168e83ce → 16534f9a2c96 → b4c7a72a3c0f → 11398a3e19ce, all changes in §3i–§3j. Every anchor of the batch was re-found in its cited item in 11398a3e19ce, map cb9d46678f56 and D26 9282fc1d22fe. #T12.32-6 has 624 characters, within the 660 limit for list rows.
- (4) then repaired both reported items. IT-1 9c77825b2a82 orders K′ as ϱ_*, H_*, K_*, C_C, then ϑ_*, then C^a_k and C_p, and #T12.32-4 holds as written. D26 4dfb36e15797 writes ϑ_V in 6.4 *Tilt* and on l.379 and l.381.
- So #T12.19-6's C_sh′ and #T12.19-8-1's C_h now write ϑ_V, and #T12.19-4-1's "write it ϑ" list keeps only IT-1 §3e and §3f. IT-1's §3i consolidation leaves every §3i anchor of #T12.4-1-2 and #T12.19-9 in its item.
- Round 9 (narrow) found R8: #T12.19-4-1's list of ϑ_V's users omitted #T12.32-6. Round 10 (full, with #T12.19-6 and #T12.19-8-1 read whole against D26) found R9: #T12.19-6 cited §6.3 for W_III, which D26 defines in 6.4 (l.335). Rounds 11 (narrow) and 12 (full) are clean.
- Table 99c0d18618f6 → 9dacb63576d1 → 494562303302 → 6e6acccc4ce6 → f4f089dd4cbc → 6a9a392e6060 → 7a0f3334905e. LABELS 7a980dfeec7b → 18538c3369a5 → fd7beb743955 → 899e7e91e276 → 9bbc0e4a13bf → b44c959564b7 → c6814d4faaee. defcheck on LF, on the general-loops note and on the pair note: "-- 0 lines" each; dmarks2 16; deadcheck and prefcheck known hits only; columns 10×5, 74×6, 267×7.

## NL e2ca5b9e7a82 and General Loops ebaefc789f80: #T1.3-1, #T12.31, #T12.33 to #T12.33-4-1 (Table)

Input: ⑂ (3)'s NL messages (rows from e2ca5b9e7a82, with ℋ(D) renamed 𝒯(D) and K₂ set in #NL9.6-4b only) and BETA's general-loops message (§6–§7 settled, the multi-loop factor 2Λ̄(𝒞) for every N_C).
- NL rows: #T1.3-1 states that L₀^×, u_𝔏 and #NL12.1's conditions are N_C-free. #T12.31-11 loses its u_𝔏^{(N)} and L₀^{(N)} clauses. New #T12.33 (δ, N_i, admissible pieces, Σ(𝒫)), #T12.33-1 (tube hulls), #T12.33-2 ((H1′), 𝒯(D)), #T12.33-3 (H^i_γ, A_s^{(N)}), #T12.33-4 (K₁, K₂, φ_c, Φ_c) and #T12.33-4-1 (C^src, the response constant).
- General-loop rows: #T12.31-1 (s_k(C), δ_k(C) ≥ L²MR_k), #T12.31-2 (Λ_N deleted), #T12.31-4 (A_s^{(N)}(𝒞), η(𝒞)), #T12.31-9 (c_off), #T12.31-10 (C_win^×(𝒞)), #T12.31-11 (u_𝔏(𝒞), L₀(𝒞), the transport condition, the locals).
- Re-derived: 1000·9Λ̄(𝒞)/(1 200 000Λ̄(𝒞)) = 3/400 < 1/128 = ϖ/8. With D₀ := 14Λ̄(𝒞)u and a := c_w/D₀, Σ_{d≥0}e^{−c_w(d/D₀ − 1)₊} ≤ D₀ + 1 + 1/a, as θ + e^{−aθ}/(1 − e^{−a}) ≤ 1 + 1/a on (0, 1]. So C_win^×(𝒞) ≤ 116Λ̄(𝒞)u/c_w for c_w ≤ 1, Λ̄ ≥ 2, u ≥ 1.
- Also re-derived: 2(M + 1)/M ≤ 5/2 for M ≥ 4 gives c_off = (7/2)ν_r + (3/8)ν_e ≤ 4ν. A coarse bond is L^{j−q(C)+K′−k} ≥ L^{q̄(j)+K′−k} step-k bonds, since j ≥ Q + q̄(j). L₀(𝒞) = 4Λ̄(𝒞)²L₀^× is 2Λ̄(𝒞) from u_𝔏(𝒞) times 2Λ̄(𝒞) from the coefficients, L₀^× being linear in u_𝔏.
- Round 1 (full) found N1–N7:
  - N1: #T1.3-1 gave the one-loop count (#NL1.3-5) as the reason for every u_𝔏 claim; it is the reason for #NL6B.1-1 only.
  - N2: #T12.33-2's u_D is two-loops' factor of *Units with a factor* (#510, #570), not #NL6A.6's u.
  - N3: #T12.33-2 cited #518 for ℐ(D), which defines ℐ(D) only for an 𝐑-made D.
  - N4: #T12.33-3 made 1000ηA_s^{(N)} < ϖ/8 a hypothesis of the hull bound; it is the condition of V4's lem:c4-8-2(c) with A_s^{(N)}.
  - N5: #T12.33-4 left φ_c and Φ_c undefined. Φ_c is V4's constant bound 4(2R_0′ + 1)(1 + 1/c) + 8/c² of (c5-7-boundary-marks), not a single-square part.
  - N6: #T12.33-3 cited #T12.12 for A_h, η and ϖ, which are #T12.13's. N7: #T12.33-4 used ℓ_Σ without #T4.51.
- Then NL e2ca5b9e7a82 and the general-loops rows were entered. Round 2 (full) found N8–N10:
  - N8: #T1.3-1 said N_C enters only the scale conditions, but N_C also enters the bounds (#NL.1.2).
  - N9: #T12.33-2's ℐ(D) pointer listed some species only; it is two-loops' arc set (#394, #574-1).
  - N10: #T12.31-11's "for #T1.3-1's 4096M" was ambiguous.
- Round 3 (narrow) found N11 and N12. N11: #T1.3-1 called u_𝔏 a unit, not the units factor, and its two clauses on conditions read as contradictory. N12: #T12.31-1 had a double "and".
- Round 4 (narrow) and round 5 (full, with the unchanged #T12.31 rows' §3, §6 and §8 anchors re-read in ebaefc789f80) are clean, so the rows are done.
- Table 7a0f3334905e → 6002edcf2457 → a13230452afd → 0aa0a9313e4b → 4da161f7f9f4 → 5c94a0d5dd14 → db7ae55b6e5a → ff88007cace7. LABELS c6814d4faaee → b7f8d8374c5d → 9495906b1bc0 → 4ee3cc98399f → 5bf9a254d0d8 → e384dc944732. defcheck on LF, on the general-loops note and on the pair note: "-- 0 lines" each; dmarks2 16; deadcheck and prefcheck known hits only; columns 10×5, 74×6, 267×7.

## IT-1 d3aef750d7a9, O4 952a1687d5c4 and D26 45edbc7927d4: #T12.19-2, #T12.19-4-1 to #T12.19-8-1, #T12.32-6, #T12.32-8, #T12.32-10 to #T12.32-12-1, #T12.34 and #T12.34-1 (Table)

Input: (4)'s message on IT-1 §3j and §3e(3.12), O4 and D26, sent at IT-1 c334172e64a1 and D26 d592a6c7431d. The rows follow the files on disk, IT-1 d3aef750d7a9 and D26 45edbc7927d4.
- New rows: #T12.32-10 and #T12.32-10-1 (§3j(1)–(3): ε_s, σ_H(T), q_s, ℓ_s, m̃, δ_N, m̂, λ, R_N, c_ℓ, ε_N, δ̂, C_sh), #T12.32-11 (§3j(4): s_p, τ̂_N, ω̂_t, ω̄̂, Ĉ^δ_bd, the raised C_bd), #T12.32-12 and #T12.32-12-1 (§3j(5)–(6): N₀, 𝔖̂₁, 𝔖̂₂, μ̂′, C_F = A_E, C_τ, C₀′, C_ph with C₀′, N(g₀), R_t, n_t, a_lab), #T12.34 and #T12.34-1 (O4: ρ_ω, C_ω, ω̃′_t, ω̄̃′, C^δ_bd).
- Edited rows: #T12.19-2 (ρ_ω to #T12.34), #T12.19-4-1 (ϑ_V wherever written; c_h in §3j and D26 §6.4), #T12.19-5, #T12.19-7 and #T12.19-8-1 (pointers; ρ₁ → ϱ₁), #T12.19-6 (C_m's formula; m̂, λ, δ̂ and C_sh′ to #T12.32-10 and #T12.32-10-1), #T12.32-6 (the old C^δ_bd deleted; τ̄ not #T12.14's τ̄²), #T12.32-8 (δ̂).
- Re-derived: 4c_G′(C_w′/2 + 4C_{c₀} + 8C_odL) = 2c_G′(C_w′ + 8C_{c₀} + 16C_odL); with α_{1,1} = Lϱ₁, 8m_L(2ρ_L+1)⁴ρ_ωe^{μ_xρ_L} = C_ωC_δϱ₁ϑ_Vr; with ϑ_V = γ/(4c_hm_LN_lat(μ_H)), 4c_hc_ℓϑ_Vγ^{−1}N_lat(μ_H) = 4(2ρ_L+1)⁴; (5/4)(1 + ω̄̂)e^{ω̄̂} ≤ (5/2)e for ω̄̂ ≤ 1 gives Ĉ^δ_bd.
- Round 1 (full) found I1–I4:
  - I1: #T12.19-5, #T12.19-6 and #T12.32-8 sent c_ℓ, δ̂ and C_sh to #T12.32-10; they are #T12.32-10-1's.
  - I2: #T12.19-8-1 sent C^δ_bd to #T12.34; it is #T12.34-1's.
  - I3: #T12.32-12 and #T12.32-12-1 cited Lemma c5-5-8(b) for C_F and A_E; V4 sets C_F := A_E, the envelope constant of lem:c4-6-env.
  - I4: #T12.19-2 left ω₀,₀ unnamed, and #T12.32-11 left B_h unqualified.
- Round 2 (narrow) is clean. Round 3 (full) found I5: #T12.32-11 cited (c) for ω̂_t, which §3j(4) defines in the bullet after *Host bound*.
- Rounds 4 (narrow) and 5 (full) are clean, so the rows are done.
- Table ff88007cace7 → 0a9d08071c16 → 5e325c9e5904 → 37e1056450c0. LABELS e384dc944732 → 8a5651829f1d → a3dced12f772 → 3e685cf2133e. defcheck on LF and on the pair note: "-- 0 lines" each. On general-loops note 6be701a1022e it prints lines in the new §9 only (#GL9.2 to #GL9.8-2), whose rows BETA has not sent. dmarks2 16; deadcheck and prefcheck known hits only; columns 10×5, 74×6, 267×7.

## SHAs

Table: d71e239470ea → eb5a6a505303 → b168c70703ab → 9f6ebf47c805 → 0fa578b35726 → ef03c153b6ad → cc3949e005fb → 77c1b5ec9928 → 18cbd119fc8f → 05cbd40be4db → 7b51b1177ee9 → bb2bbb3fbd08 → 99c0d18618f6 → 7a0f3334905e → ff88007cace7 → 37e1056450c0. LABELS: 2d2801629f41 → 146c7b49d22b → d444e40b4233 → 1f2b3fa09b9d → 740b198d7a9d → 58050f8936d3 → 0e94a6174742 → 4c2c66efb348 → 734a37930def → c59773513fd1 → be350896ce4a → 9eeed3a7792e → 7a980dfeec7b → c6814d4faaee → e384dc944732 → 3e685cf2133e. Background note: 249ae1a46a2a → 8510ab0aebd7 → 7bb5f99918ab → 3047b31464c3 → 22a230556c65 → c7612b0d6f3b → df792ffa33f3.

## Status

Background note: rounds 6–16 found F1–F12, all repaired. Rounds 17 (narrow) and 18 (full) are clean, so the note is done at df792ffa33f3, against the coarse-chain note d02ba134814f and map d3dc46ddacc5.

Table: the repoints needed no round. The K rows follow D26 2dce56a49737, #T12.13 follows COMPLEX_COVARIANCE f1cbf76fb687, #T3.36 follows O6 908c956d462e, #T12.30-9 follows the coarse-chain note d02ba134814f, #T12.17 and #T12.13-1 follow map d3dc46ddacc5, and #T1.3-1 and #T4.51 follow NL 204c1c20c891.

The new #T12.31 rows and #T4.53's C_w follow the general-loops note 1d61bc4589e2. Rounds 1–6 found G1–G14, all repaired, and rounds 7 (narrow) and 8 (full) are clean, so they are done at table 7b51b1177ee9.

The rows #T12.4-1-1 to #T12.4-1-3, #T12.31-0 and #T12.31-11-1 to #T12.31-15 follow general-loops note 6919e16b2fdd and pair note 9b4918036466. Rounds 1–4 found H1–H8, all repaired. Rounds 5 and 6 (both full) are clean, so the rows are done at table bb2bbb3fbd08.

The rows #T4.44, #T12.19-4-1, #T12.19-6, #T12.19-8-1, #T12.19-9-1 and #T12.32 to #T12.32-9 follow IT-1 9c77825b2a82, map cb9d46678f56 and D26 4dfb36e15797. Rounds 1–10 found R1–R9, all repaired. Rounds 11 (narrow) and 12 (full) are clean, so the rows are done at table 7a0f3334905e. The C_box item is closed by map #MD2.4.12.7-1-5 (C_box ≥ 38).

The rows #T1.3-1, #T12.31-1, #T12.31-2, #T12.31-4, #T12.31-9 to #T12.31-11 and #T12.33 to #T12.33-4-1 follow NL e2ca5b9e7a82, general-loops note ebaefc789f80 and two-loops cea1a21316cc. Rounds 1–3 found N1–N12, all repaired. Rounds 4 (narrow) and 5 (full) are clean, so the rows are done at table ff88007cace7. At general-loops notes 11df5d85a367 (𝒯(D) for ℋ(D), new #GL6.2-0-1 and #GL6.2-0-2, no new symbols) and b4b6a5cc0dfe (#GL6.1-4-2 cites #T12.33–#T12.33-1) every #GL tag the table cites is present with its anchor unchanged, and defcheck prints 0 lines.

The rows #T12.19-2, #T12.19-4-1 to #T12.19-8-1, #T12.32-6, #T12.32-8, #T12.32-10 to #T12.32-12-1, #T12.34 and #T12.34-1 follow IT-1 d3aef750d7a9, O4 952a1687d5c4 and D26 45edbc7927d4. Rounds 1–3 found I1–I5, all repaired. Rounds 4 (narrow) and 5 (full) are clean, so the rows are done at table 37e1056450c0.
