# Triage: The Torus-Size Condition of the Pair Notes (11 November 2026)

Two-loops session. Finding from the BETA session (messages of 00:54 and its addendum; GL triage WILSON_IT1_GENERAL_LOOPS_TRIAGE_2026_11_10.md). User's instruction: "Implement the T_{ph}/3 repair".

## Finding

The pair notes cited TL #290 but kept only its consequence N_s ≥ 2max(ℓ₁, ℓ₂), and stated their families with sides up to T_ph/2. V4 assumes, for each square, coarse periods K_μ ≥ 3(n_i + 2), n_iL fine bonds being the side (V4 sec:extent-weights, sec:two-loops-setting, eq:c5-7-T(iii)). Sides in (T_ph/3, T_ph/2] violate it at every K.

## Re-derivation

- At ε_K = uL^{−K}: LK_μ = (T_ph/u)L^K and n_iL = (ℓ_i^{ph}/u)L^K, so K_μ ≥ 3(n_i + 2) reads T_ph − 3ℓ_i^{ph} ≥ 6uL^{1−K}.
- If 3ℓ_i^{ph} < T_ph: T_ph ∈ uℤ (#NWTOA.1) and ℓ_i^{ph} ∈ uL^{−q_i}ℤ, so T_ph − 3ℓ_i^{ph} ≥ uL^{−q_i} ≥ 6uL^{1−K} once K ≥ q_i + 2 and L ≥ 6. Every K of the construction has K ≥ j ≥ q_i + q̄(j) ≥ q_i + 3 (#307; q̄(j) ≥ 3 because the argument of the logarithm in map #MOMGD.30 is at least L³ for g_min ≤ e^{−1/2}).
- If 3ℓ_i^{ph} ≥ T_ph, the left side is ≤ 0 < 6uL^{1−K} at every K.
- The hypothesis gives N_s = (T_ph/u)L^j > 3ℓ_i ≥ 2ℓ_i, the bound the span bound of (6B) uses.

## Repairs (in place, no tags renumbered)

- TL #290: states V4's hypothesis, its fixed-torus form and the consequence N_s ≥ 2max(ℓ₁, ℓ₂); V4 line pins L1565, L3560 replaced by sec:extent-weights, sec:two-loops-setting. New #290-1: on the fixed torus the hypothesis holds at every K if and only if 3ℓ_i^{ph} < T_ph.
- TL #917: the (8.2) hypothesis list names V4's torus hypothesis (#290) instead of its consequence.
- PC #PC2.3: N_s ≥ 2max(ℓ₁, ℓ₂) is now cited as a consequence of the hypothesis (#290). PC #PC7.2: sides below T_ph/3 (#290-1), instead of sides up to half the period.
- NL #NL10.2, #NL10.7, #NL12.1: the same.
- RP #RP.6, #RP.6-3, #RP.10-2: sides below T_ph/3 (#290-1).
- NV #NV.9: sides below T_ph/3. NV #NV.5-2: the hypothesis replaces its consequence. NV #NV.11-2: 8h ≤ T_ph is assumed, so the starting square is a configuration (h < T_ph/3) and the doubling count is ≥ 0.
- PF: no change. #PF4.4-4's ℓ_i ≤ N_s/2 (#290) still holds, and PF's pair family is #PC7.2's.

## Stale N_C Conditions in NV (Found in the Same Pass)

- NV #NV.3 and #NV.3-4 required L ≥ L₀^{(N)}, but NL's L condition is now L ≥ L₀^× (#NL6A.9). Repaired.
- NV #NV.11-3 still quoted L ≥ (n/2)²L₀^×, ν ≤ 1/(500n) and 1000ηA_s < ϖ/(4n), which NL #NL12.1 no longer has. It now says what remains n-dependent: #NV.5's coupling threshold, through ḡ_W (#NV.3-4-2) and the family's E* and A^× (#NV.5-2.1).

## Table Fork's Readings (Its Message of 11 November)

- #NL6B.2's E^{R×}_k equals E^R_k(⊔_iC_i; ℓ₀) − Σ_iE^R_k(C_i; ℓ₀) with #T12.20-4's E^R_k = log(Ξ^c/Ξ): confirmed by expanding, since −log Ξ + N_C·log Ξ = (N_C − 1)log Ξ.
- #NL6A.5-3's A_M is the map's S_M (#MD2.4.12.22-3): confirmed, because both unions run over the members Y of M's slot groups (#MD2.4.12.22-1). NL's wording "components Y" is now "members Y", and the line cites the map's S_M.

## Pre-check

- Every changed line was re-read. No line under the repair exceeds 600 characters. labels_two_loops.py (1445 tags) and labels_pair_cauchy.py (347 tags) pass the cross-reference checks.
- A grep of all top-level notes finds no remaining "half the torus period" or "≤ T_ph/2" side condition. GL (BETA's) already uses 3diam_ph(C) < T_ph.
- Not mine, and already forwarded by the table fork: the continuum note's #ND.8.5 family (session (4)).

## SHAs

TL b94da3099515 (LABELS_TWO_LOOPS e9023cc9fb4c), PC 5b345629598c (LABELS_PAIR_CAUCHY dfe71a7404c6), NL de703f746b46, RP a780d9fe3ef9, NV 0c3236ada5f9.

## PF and Theorem D in the N_s Form

User's decision: "Sure use the N_s form". The torus-scale terms are stated with ℓ₁ℓ₂/N_s² and are not converted by D ≤ N_s/2.

- Re-derivation. #PF4.4-4 gives ‖ξ_i‖₂ ≤ 2ε_{K′}ℓ_i/N_s, so |Cov_{𝐏_{ℓ₀}}(O₁, O₂)| ≤ 4|e^{E^{(1)}_{const,K′}+E^{(2)}_{const,K′}}|ε_{K′}²ℓ₁ℓ₂/N_s² ≤ 4|e^{…}|ρ_cv²ℓ₁ℓ₂/N_s², as 0 ≤ ε_{K′} ≤ ρ_cv. ℓ_i = (ℓ_i^{ph}/u)L^j and N_s = (T_ph/u)L^j (#290) give ℓ_i/N_s = ℓ_i^{ph}/T_ph. In the decay plan, (T)'s bound ‖F_i − 𝐄F_i‖₂ ≤ Cgs_i^{(K)}, s_i^{(K)} = ℓ_i(T_ph/u)/N_s, gives |Cov(F₁, F₂)| ≤ C²g²(T_ph/u)²ℓ₁ℓ₂/N_s² = C²g²ℓ₁^{ph}ℓ₂^{ph}/u².
- The wraps. #PF3.2-8f's step e^{−c_wN_s/M} ≤ e^{−2c_wD/M} was the same kind of conversion, and is deleted. #PF3.2-9b and #PF0.5-3 now say that the wraps decay exponentially in N_s. No bound changes.
- Edits. PF #PF.1, #PF0.2, #PF0.4, #PF0.5-1, #PF0.5-2, #PF0.5-3, #PF3.2-8f, #PF3.2-9b, #PF4.4-1, #PF4.4-4, #PF4.6-1. Decay plan #DP.2 (split; new #DP.2-1 for the remainders, absorbed by ℓ_i ≥ 1 and N_s² ≤ C_q^{1/2}(log ḡ^{−2})^{2r}, Cauchy #C11c.7-2) and #DP.9 (split; new #DP.9-0).
- Consumers. TL #941 ("does not decrease in D") is still true. NL #NL11.1 cites #PF0.5-1 only as a pair bound. NV #NV.4-3 uses only ρ_cv's definition. Table rows #T12.4-1, #T12.4-1-2 and #T4.52 quote unchanged text. GL #GL8.2, #GL8.5-3-1, #GL8.6-5-1 and #GL8.7-2 (BETA's) still hold, since D ≤ N_s/2; BETA has been messaged with the matching changes, and the table fork with the SHAs.
- Pre-check. Every changed line was re-read. PF's changed lines are at most 390 characters; the decay plan's are at most 478 (#DP.9-1, not edited, is 615).
- SHAs: PF a0ac855ab471, decay plan f4ae4eb0322a.

## RW1 Consolidation

User's instruction: "Continue with RW1, when consolidating check for "not used" phrases".

- §5 is rewritten in full on V4 (no V3): domain and local gauges (#RW1.5-1 … -7), (a) the Hessian, (b) selected integrals, (b′) the payment at complex data (#RW1.5bp … -14), (c) potentials, (d) activities, (e) clusters and the determinant, (f) tails, (g) second derivatives at B = 0 via VAR Prop. 9 and (190), and (h) the outer prefactor. Every constant was re-derived before writing.
- #RW1.4-2 uses the convex domain 𝒫(U₁) (#RW1.5-1) in place of the polydisc argument. #RW1.4-11/-12 use C_w^∨ := max(C_w, C_w^c). #RW1.4-13 is split, with new #RW1.4-14 holding the volume factors.
- "Not used" asides deleted: "each object used below" (#RW1.5-2, reworded), and "𝗐_ξ is not a factor of Y_W, c_W or φ₁" (#RW1.4-10). No bound changes.
- Clashes found by grepping the table and renamed: ε_H → ε_ℂ, β′ → β_ℂ, q′ → q_ℂ, 𝖠′ → 𝖠_ℂ, k̄ → k^⋆, Φ̄ → Φ^⋆, r_χ → ϱ_χ, c_V → c_𝒱. h_ℂ now cites #T12.32 and bch cites #T12.24-0, instead of restating them. μ̂ is V4's (lem:regular-bounds).
- Repairs found on read-back: #RW1.5-6's range-R vanishing now goes through real-point uniqueness; (190)'s factors (L^jη)^{−1}, (L^{j′}η)^{−d} equal 1 at j = j′ = 1 and η = η₁ (#RW1.5g-4); exp(−g₀^{−2}S) is entire via the bond inverses (#RW1.5h); the threshold list includes g₀(1 + ϱ_χ)³ → 0 (#RW1.5bp-14).
- Flagged to LF and to the table fork: the M condition at 4δ_M (#RW1.5bp-2) and the use of q₁ > p₀ (#RW1.5g-2), which is provisional under (R-m′). Question to LF: who bounds the T–T′ difference of the embedding terms' B-derivatives through VAR's 𝓗 (#MD2.3.4.37-7)?
- Pre-check. All 63 V4 labels and all #MD, #MOMGD, #T and #RW1 references resolve (script check). Lines are ≤ 621 characters. No "not used", "not needed", "V3" or "polydisc" (except the σ and z polydiscs) remains.
- SHA: RW1 AA66652F0D6A (115 lines, 36.6k chars).

## NV #NV.4-3 (Peer Finding, 11 November)

- Finding (session ⑂ ⑂ (2)): B_E = O((log ḡ^{−2})^{5r}), not O((log ḡ^{−2})^r).
- Re-derivation: A^R_E = 16e^{−2}C^R_EL²(R^E)³/(c^R_E)² with R^E = MR̄(j(C)) ≤ 2LM(log(ḡ^{−2} + bj(C)))^r (#CP.13). S_E ≤ e^{−a_E}(1 + 6/a_E) with 1/a_E ≤ max(1/a^T_E, 2LR^E/c^R_E) (#C7.6-7-1), and ℓ_C = O((log ḡ^{−2})^r). Confirmed.
- Repair: #NV.4-3 now states the 5r order, and new #NV.4-4 uses #T10.2's p₀ > (d + 5)r + ⌈r⌉ + 2 > max(5r, 4r + 1). #NV.5-2's range is now "#NV.4-2–#NV.4-4". The family part is unchanged (E* → 0, #NV.5-2.1).
- SHA: NV A23C5C204987 (was 0c3236ada5f9).

## "For Every K" on the Fixed Torus (BETA's Request, #290-2)

- #PC7.2 said "the squares for which V4's torus hypothesis holds at every K (#290-1)". By #290-1 only the square/torus condition holds at every K; (H3)'s other conditions need K ≥ max_iK_tor(C_i) (#290-2). Repair: #PC1.1 now states that every statement of the note is for K ≥ max(K_tor(C₁), K_tor(C₂)), which is all the limit uses, and #PC7.2 keeps "sides below T_ph/3 (#290-1)".
- #NL12.1: V4's torus hypothesis for each loop now reads "sides below T_ph/3 and K ≥ K_tor(C_i), #290-1, #290-2". #NL10.7 is a limit statement ("as in #PC7.2") and is unchanged.
- No change needed: #RP.6 and #NV.9 are definitions. #RP.10-2 is a limit. #RP.10-3 and #NV.10 ("for every K") are fixed-ε identities of the lattice measure with κ^{(K′)} an explicit exponential (#ND.6.1), so they need no torus threshold. #NV.11-3's "do not involve n" stays true, as K_tor depends on the loop only through its side (#NWTOA.1-7), which takes finitely many values at fixed q.
- Pre-check: labels_pair_cauchy.py passes (347 tags, LABELS unchanged at dfe71a7404c6). NL #NL12.1 is 500 characters.
- SHAs: PC bbed461c87b5, NL 19fc310faab8.
