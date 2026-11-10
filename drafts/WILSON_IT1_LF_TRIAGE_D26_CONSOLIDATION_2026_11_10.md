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
