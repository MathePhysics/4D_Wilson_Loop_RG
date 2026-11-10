# Consolidation of the D2.6 Closure, 10 Nov 2026

## Rules

- Read every line of WILSON_IT1_D26_CLOSURE_2026_10_24.md and verify it.
- Remove status remarks, review history, roadmaps, hedging, and dead routes.
- Split lines over ~650 characters at sentence boundaries; repair in place.
- Before deleting §0 (register) and §8 (status), put every mathematical item of §8 where it is used.

## §8 Relocation Checklist

- **Conditions** (§8 *Conditions*): confirm each is stated in the section named in its parenthesis; the map cites "D2.6 closure §8 *Conditions*" for R_t + 4L + 2 ≤ ℓ (map l.602).
- **Accepted from Bałaban:** LFR II (1.83), (1.89), and p.387 in §7.2; p.387 for j ≥ 2; CRE p.277's support bound in §2.3; §2.2's source bound at real data.
- **Inputs inherited from the map:** CRE p.277's 𝐇-decay and margin, RG2 p.6's B′-range, LFR I p.177 (ii), q₀ = q₁ > p₀, CRE (2.6)–(2.7), (RZ), §9.3's layer bound, CRE p.261's boundary potentials, §9.1's gluing, route (a), §6.1's row-domain bound.
- **Map amendments marked "to be amended":** D2.2(6)(e) *The radii* (r_{ω,j} := g_j^{1/2}); #MD2.2.6.30 slot convention at j = 0, D(1)(iii), #MD2.2.6.150; D2.1(4) *Constants* (ε_H ≤ C₁^{VAR}ε̄₁/(2c_V)); #MD2.0.3.19 (subset expansion of f_ξ). Check whether the map has them.
- **O-note summaries** (O1, O2, O2′, O4, O5, O6): keep only the statement used, at the place used, citing the O-note.
- **External citers of §0 and §8:** map #MD2.0.4.6-7 (§8 *Conditions*, R_t + 4L + 2 ≤ ℓ), map #MD2.0.4.6 and #MD2.0.4.6-9 (§0, §8's amendment list), D27 l.26 and l.606 (D26 §0), D27 l.678 (D26 §8's joint expansion), D27 l.824 (§0, §8), continuum l.175 (§0, §8), and the background note §5.3 *(iv-c)* (D26 §8, for "D2.4(4) *Scope* and D2.3 … given for the fine chain"; owned by the table fork, which re-points it when told where the item lands).

## Peer Reports to Act On

- Table fork, 10 Nov (corrected): COARSE_CHAIN_INTERFACES l.41's exponent exp(c_π(b_d^cL)^kΔ_0(c)) needs the factor 1.04, since ‖π(V)‖ ≤ exp(c_π‖log V‖) and ‖log V‖ ≤ −log(1 − ‖V − 1‖) ≤ 1.04Δ_k; so (C7) 1.08 → 1.12 and (C9) 1.06 → 1.11, in §2.2 and *Constants and Conditions*. To apply when that note is consolidated.
- Table fork, 10 Nov: the table #T12.14 restates N_j(x) at rate η_V/C_F; the map's (ii′-b) now has c_*′ (#MD2.0.3.43). To be messaged with the final consolidation hash.

## Progress

- §1 done. §2.0–§2.1 rewritten; the species rule now stands in map #MD2.0.3.21–#MD2.0.3.25-1, and D26's *Rule changes* list is deleted. "M ≥ n_C + 2" removed from map #MD2.4.13.19 (redundant under M ≥ 100; n_C clashed with #T2.26).
- §2.2: the measure, the source bound, and *Complex σ_k* rewritten; O6's content cited by map #MD2.2.6.170-*; the radius users cited by map #MD2.2.6.168-3, #MD2.2.6.177, #MD2.2.6.193. Repair: the KP weight step counted m(X) as RG2's m; RG2 p.3 l.30–31 defines m by the cubes meeting ∪X̃_j^5, and C's block gives m(X) ≤ 3^dm(ω), so the constants are e^{16(3^d+1)a} and δ₁M ≥ (3^d+1)a (D26 2.2 (2), map #MD2.2.6.168-1).
- Map D(k)(ii) collar term and (ii′-b)'s N_j now at c_*′ (#MD2.0.3.29, #MD2.0.3.29-1, #MD2.0.3.39-2, #MD2.0.3.43).
- §3 rewritten. §4 rewritten: c_π → c_π′ at complex data in 4.2(i)–(ii) and 4.4 (map #MD2.1.4.27, #MD2.4.8.1); 4.3's "c_*′ ≤ ν_e/4" corrected to ν_e/8; the unused parity remark deleted; the boundary-type definition moved to 2.1(iii); |log w| at C_w′ (map #MD2.2.6.175-2) in 4.5 and ρ_ω, removing the clash with §3's C_w. Map #MD2.2.6.168-3's *Propagation* pointer corrected to #MD2.2.6.175–#MD2.2.6.179-2.
- §5 rewritten: 5.4 at c_π′; 5.5's merged-bridge display had −(5/8)(ν_e/L)Σσ(D″) where the payment e^{−(5/4)(ν_e/L)σ(D″)} is what closes the step: corrected; 5.2's pointer to the map's (ii′-a) corrected to #MD2.0.3.42-1–#MD2.0.3.48-2.
- Peer fixes: map #MOMGD.2 and continuum #ND.5.5 now quote (iv-e)'s bounds (2|κ_f^{(K)}| resp. |κ_f^{(K′)}| times exp(4Cℓ_C(ρε + τ²) + r^R)δ_LF); map (h) #MD2.0.5.41 gains r^R_K for the 𝐑-steps' constants.
- Coarse chain (table fork, corrected 10 Nov): c_π is right; l.41's exponent needs the factor 1.04 (‖log V‖ ≤ 1.04Δ_k), so (C7) 1.08 → 1.12 and (C9) 1.06 → 1.11. To apply when that note is consolidated.

## Files of This Run (updated as each is finished)

- Done on 10 Nov: W-δ, continuum, Cauchy, the D2 map, D2.7, the LF (before 14:00); D26, O4, O2 (afternoon); O2′ redundant with D26, to archive once RC_PAYMENT_PASS no longer cites it (two-loops' citers re-pointed, 17:30).
- Done 18:07: D26 7.2 *Linear size and cubes* (d′ + 1 ≤ d·#cubes, C_d′ := d(3(126)^d + 64^d + 2^d), ℓ₀^{box}; 30cd68b6dc51); SW rewritten (1eeaeff9e212); map 796d26f6e193 (#MD2.4.4.5, -8-3, -10, -12-1, -20, -21-1, #MD2.3.9.9-1); D27 15.6(e) (9b3902e3545b). Table fork and two-loops told.
- Done 18:30: K₁ takes d^{−1} (direct route; trees of the enlargements need not lie in Z), K_{j+1} keeps 2(14)^d; D26 2dce56a49737 (with 4.2(iii) class (3)'s ω-freeness induction and §1's "contained in"), O2 1c529b0ff9ad, IT-1 62907f757621, map #MD2.0.5.36. O2′ archived to archive/ (README there).
- Done 18:43: COMPLEX_COVARIANCE consolidated, f1cbf76fb687 (slot cocycle and (K4) deleted, δ̄₀ := min(δ̄, μ), Lemma 1 on the gauge-invariant 𝒟_W, path-point curvature closed via L^{−m} ≤ μ/(4M), T₁ from CRE p.268, c_π′, K₁ ≤ 3, L ≥ 12(1+β₀)²); map 656eed60159c (#MOMGD.5, -4 deleted; #MD2.4.13.19-1; RTR's X₀ in #MOMGD.23-1); SW 2be3106d4b2f (c_π′, printed R₁M₁). Table fork and two-loops told.
- Done 18:57: O6 consolidated, 908c956d462e (RG2 (1.18)'s factor 4 in the deformed shift, margin (7/16)min(β,1)α_{1,k}; S_H ≤ g^{3/2}/40 and slot moves 10S_H/g_j per #MD2.2.6.193; (C1), (C4) deleted; q₁ = p₀ alternatives removed); map 4393221aa40a. Table fork did #T3.36 (table cc3949e005fb); two-loops told, coarse-chain 1.04 point forwarded.
- To do, non-BP, LF: LINE_DEFECT (IT-1), LF_PACKET_PLAN, READINGS_INVENTORY.
- Delegated to two-loops (17:5x, user's request): RMJ, RW1, COARSE_CHAIN_INTERFACES (with the 1.04 factor), RTR_PROOF_PASS (CRE (2.32)), RC_PAYMENT_PASS (O2′ → D26), RC_PROOF_PASS, READINGS_RECHECK.
- Map follow-ups: the remaining V3/V4 line pins.
- Last, after everything above, the LF-owned BP files: BP_COUPLING_PROFILES, BP_VAR_PROP4_KERNEL, BP_COMPLEX_BASE_GAUGE, BP_CMP98_ADJOINT_AVERAGING, BP_LFR2_CHI_K_LAMBDA, BP_LFR2_LOOP_LOCALISATION.
- D26 §9 renumbered §8 (17:24); map, D27, SW citers re-pointed; table fork told (BACKGROUND_ITERATION).
- 20:11: IT-1 §2–§3d consolidated: V3 pins → V4 labels, with every quote checked in V4; review tags and status blocks deleted; lines ≤ 650. Repairs: §3c(2)(a)(ii′)'s |f_c| ≤ 2C+1 is now derived via uniform continuity of log w on a convex neighbourhood, and the radius ρ_L, which clashed with V4's ρ_L = 4L, is now unnamed; §3d(5) is at N⁺_ret with the 𝒬⁺ mark inequality (103ℓ+1), with |Γ_C| ≤ C_Ln_C from the proof of (c3-7-3); the exposed-segment cost is pointed to D26 §7.4. IT-1 fb73993e112b.
- 20:11: two-loops' COARSE_CHAIN_INTERFACES consolidated (d02ba134814f). Its map finding at #MD2.4.11.5-2 (the dropped +1) was re-derived and applied: e^{(ν_r/16)(σ_k(W)+1)} under 20c_π′M‖a′‖_∞ ≤ ν_r/16, with e^{ν_r/16} per touched W a per-piece constant (#MD2.4.12.27-6); also #MD2.4.11.5-3, #MD2.4.12.27-2 and #MD2.4.13.19-3. Map 45da9228179b. D27 l.115 → #CC.1.1-2 (515f6d31c942). Two-loops told.
