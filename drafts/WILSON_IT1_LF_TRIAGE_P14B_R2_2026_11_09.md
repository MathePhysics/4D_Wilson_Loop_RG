# Packet 14b (Cauchy §10.3), round 2, 9 Nov 2026

## Pre-check of cauchy-p14b-20261109-r2 (full)

- **Whole part read** (#C10.3.1–#C10.3.51-1) on 9 Nov 2026, after packet 14 r1's repairs and the contour-variable repairs, with its context: Cauchy #C10.1.4–#C10.1.6-1, #C9.2.1–#C9.2.3-2, #C9.3.3–#C9.3.3-1, #C9.4.3–#C9.4.3-5, #C9.7.1, and #C9.7.1-15–#C9.7.1-16.
- **Earlier repairs:** packet 14 r1's S1 and M1–M8 are in the text (WILSON_IT1_LF_TRIAGE_P14_R1_2026_11_09.md). So are the 𝐆^{(2)} kernel bound on contour variables (#C10.3.3-11–#C10.3.3-11-4, 14a pre-check of 05:19), the contour variables of (105) (#C10.3.34-2), the BCH bound for the group average (#C10.3.34-7, -7-1, -8), and its conditions in #C10.3.36.
- **Re-derived:**
  - #C10.3.3-11-1 and -2:
    - Two contours of 𝐆(y, x) make a loop of ≤ dL bonds, and the real part needs ≤ Σ_{α<β}|n_α||n_β| ≤ dL² moves.
    - The plaquettes of W₀ are ≤ O(1)Mα₀L^{2m}η²/a_j² = O(1)Mα₀/L², since L^mη = a_j/L in both runs (run A: m = j − 1 and η = ε; run B: m = j and η = ε/L). So δ′ ≤ O(1)dMα₀ + O(1)dLα₁.
    - |g_Γ − 1| ≤ 2δ′e^{2δ′}e^{|Ā|} + |Ā|e^{|Ā|} ≤ 4.3δ′ ≤ 6δ′ at δ′ ≤ 1/66.
  - #C10.3.3-11-3:
    - Differentiating Σ_Γ(1/i)log(W(Γ)W(y, x)^{−1}) = 0 gives d g_Γ g_Γ^{−1} = i(X_Γ − Ad(g_Γ)B̃′).
    - 𝒜 = n(1 + E) with |E| ≤ 2e + e² ≤ 3e, so Σ|T_Γ| ≤ (1 + e)/(1 − 3e) = (12/11)/(8/11) = 3/2 at e = 1/11.
    - The coefficient is ℓ(3/2)(4/3) = 2ℓ.
  - #C10.3.3-11-4: with the inner product ℓ^dΣ_b, the kernel is ℓ^{−2d} times the coefficient products, so 4ℓ²ℓ^{−2d} = 4ℓ^{−2}ℓ^{−d} at d = 4. There are L^d terms, at distances ≤ dL.
  - #C10.3.8 and #C10.3.11:
    - Differentiating A_ε(MW) = A_{ε/L}(W) + b(W) along ℒX, with Q₁^{pl}ℒX = X, gives (10.3a).
    - 𝒬H₀ = 1 − D_VΘ_jH₀ by (B1), so the multipliers are read off by divergence-freeness.
  - #C10.3.14-1 to -4:
    - (12/5)C₀ε₁ ≤ (12/25)α₁ ≤ α₁/2.
    - BCH three times: Σ_{steps} ≤ c_B·2Σ_{i<j}|Z_i||Z_j| ≤ c_Bs² ≤ 2c_Bs², with the intermediate exponents ≤ 2s ≤ r_B.
    - |Y_p| ≤ (9/8)α₁ε²/a_j² ≤ 9/64, so e^{|Y_p|} ≤ 1.16 ≤ 6/5 and (9/8)(6/5) = 1.35 ≤ 3/2.
  - #C10.3.14-8: |f_y| ≤ c_WΣ_pε^{d−2}·2α₁(ε²/a_j²)·3B₀a_j^{−1}e^{−½δ₁d}·a_j^{−d} ≤ 6c_Wc_eB₀α₁a_j^{−3}. The Schwarz lemma on the disc of radius α₁/(8ρ_j) ≥ 1 gives the factor 2·8ρ_j/α₁ = 16ρ_j/α₁.
  - #C10.3.16: x_λ = Nc_eB₀(96c_W + 4C_rC_ℒ) and B_λ = Nc_eB₀(6c_WC₀ + 4C_rC_ℒ), using ε/a_j ≤ 1.
  - #C10.3.25-4: Σ_{i<n}L^{2(i−n)} ≤ (9/8)L^{−2} ≤ (4/3)L^{−2}, and exp((16/3)c_QL^{d−1}C₀ε₁) ≤ e^{2/3} ≤ 2 under (AQ).
  - #C10.3.31 to #C10.3.32:
    - The transport mismatch of D* is 2d bonds × 2c_vL^{i+1}η sup|A| divided by L^{i+1}η, which is 4dc_v sup|A|.
    - Σ_{i<n}L^{i+1}η ≤ (3/2)a_j ≤ 2a_j, so C′_Q = 2·2·2(c_D + 4d)c_vL^{d−1}.
  - #C10.3.34-6: Σ_{i<j}L²·4C₀ε₁L^{2(i−j)} ≤ 4.5C₀ε₁ ≤ (16/3)C₀ε₁, and exp(1/3 + 1/4) ≤ 1.8 ≤ 2. This gives θ_i ≤ 8L^{i−j}ρ_j.
  - #C10.3.34-7:
    - The contours have ≤ dL bonds, so |A_Γ| ≤ dLθ_i ≤ 8dρ_j ≤ r_B/2.
    - (0.10) with BCH gives n|Z| ≤ Σ|A_Γ| + c_BΣ|A_Γ||Z|, so |Z| ≤ a_i/(1 − c_Ba_i) ≤ (4/3)a_i under c_Ba_i ≤ 8c_Bdρ_j ≤ 1/4. Then (4/3)a_i ≤ (32/3)dρ_j ≤ (2/3)r_B.
    - The continuity argument excludes |Z| reaching r_B.
  - #C10.3.34-7-1 and -8:
    - Σ_{i<j}Lθ_i ≤ 8ρ_jL/(L − 1) ≤ 12ρ_j for L ≥ 3, which gives 16dρ_j and 32dρ_j.
    - Both are below r_inj by c_wρ_j < r_inj.
  - #C10.3.40: x_J = 2(x_λ + c_brc_wB_λ) + (4C′_Q + 2c_brc_w)B_λ ≤ 2x_λ + (4C′_Q + 4c_brc_w)B_λ, using ε₁ ≤ 1.
  - #C10.3.42-2: 2B_λε₁ + ¼α_J < α_J when 4B_λε₁ ≤ α_J.
  - (10.3): 2S/R_𝒟 ≤ [16ρ_j/α₁ + 8x_J(ρ_j + (ε/a_j)ε₁)/α_J]S.
- **Repairs made in this pre-check:**
  - #C10.3.36-1 said that Ad(w) "is orthogonal on 𝔤, so |Ad(w) − 1| ≤ |ad_Y|". Orthogonality gives that bound in the operator norm of the trace form, whereas the norm here is #T6.23's. The line now reads: "every Ad(e^{isY}) is an isometry of the norm of #T6.23 (#C10.3.34-3), so |Ad(w) − 1| ≤ ∫₀¹|ad_Y Ad(e^{isY})|ds ≤ |ad_Y| ≤ c_brc_wρ_j". I grepped for the same shortcut in my notes and found none; the two hits elsewhere use orthogonality only for adjoints.
  - #C10.3.3-10 (616 characters) was split at its sentence boundary into new #C10.3.3-10-1 (the block field, C̃^{(2)}, h, and 𝐆^{(2)}). #C10.3.3-11's citation for |W′ − 1| < O(1)α₁ now reads #C10.3.3-10-1. This is bookkeeping, with no change to the mathematics.
- **Definition check:** 0 conflicts (13 allowed). New entries: W, W₀, g_Γ, e, and 𝒜 (local to #C10.3.3-11–#C10.3.3-11-4), and a_i (local to #C10.3.34-7).
- **Table:** the fork's #T12.7-24-1 marks c_B and r_B (#C10.3.14-3) apart from the map's c_B and from VAR's and BC's r_B. No table row lists Cauchy smallness conditions.
- **Size:** reviewed block 22.1k characters (under 25k). The longest line is 602, at #C10.3.3-11-2. CR is 0, and there are no trailing spaces or duplicate tags.
- **After 14a r2 (06:15):** #C10.3.34-5 now cites "CMP 98 Proposition 3 ((122)–(123)) and (126) (#C10.1.4-1-1-1)" and bounds "the linear part of (122)", in place of "(122)–(126)" and "(124)". (124)'s explicit form is CMP 98's own average, and the bound (126) is what the line uses. The spec's background adds RG I p.253 l.42–43 and p.254 l.7–8.
- **After 14bp r2 (06:27):** #C10.3.1-5 now states the site pairing Σ_xη^d⟨·, ·⟩ beside the bond pairing (14bp r2 m3). (i) at #C10.3.18 and R* = (a_j/η)^d1 at #C10.3.4-1 use it, and both hold with it. The BP file (f03186fe900e, permitted background here) has the m1–m4 rewordings, which change no bound.
- **Spec:** specs\spec_p14b_r2.json (Cauchy 3802c8fb4ced, LF b142ee965e51). Built at 06:29: 0 conflicts (13 allowed); reviewed block 22.18k (under 25k); table a59d81743856, labels 160897034a78.
- **Order:** after 14a r2 and 14bp r2.

Written 2026-11-09 06:04.

## Verdict of cauchy-p14b-20261109-r2

One serious finding (S1) and minor findings M1, M2, M4–M8, plus cosmetics; no fatal finding. Not clean. All are repaired below; the Cauchy note is now a0b36ebcf1d0.

| Finding | Repair |
|---|---|
| S1, #C10.3.3-10: the inverses, H, H₁, and H₀ at complex pairs at PBG's rates | #C10.3.3-4 now says the series build G and G₁ only, and H, H₁ come from them and the inverses by (3.126), (3.129). #C10.3.3-10 cites BP_PBG_COMPLEX.md (#BX.1-2–#BX.1-3, #BX.7–#BX.8-2) at the scale ℓ with α_JL^{−3} for its γ, under M ≥ M₃ and Mα₀ + α₁ + α_JL^{−3} ≤ a_cx: (3.132) with the new {#D.B₀^{cx}} and δ₁′ (table #T10.50), and (3.133) with B₀^{cx} and ½δ₁′. #C10.3.10-2 does the same for H₀ at 𝐉 = 0 |
| S1, callers | δ₂ := δ₁′ at #C10.1.3-3. #C10.3.3-11-4, #C10.3.42-3, and (10.3) run at δ₁′. #C10.4.122 notes that (A2)'s rate ½δ₁ exceeds δ₂. #C10.5.1-1 and #CK.1-24 now read δ₂ = δ₁′. c_e (#C10.3.14-6) is defined at ½δ₁′ for any spacing pair η ≤ a. #C10.3.14-5 and -8 use B₀^{cx}, and x_λ := Nc_e(96c_WB₀^{cx} + 4C_rC_ℒB₀) |
| M1, #C10.3.3-11: the other terms bounded by B₀ | #C10.3.3-11 now gives the principal part B₀^{cx} and the a-term aℓ^{−2}ℓ^{−d}. New #C10.3.3-11-5–#C10.3.3-11-8-1 derive the J-term: the H₁-sum ≤ e^{δ₁′d}c_eB₀^{cx}α_JL^{−3}ℓ^{−3} by (3.133); C̃^{(2)}'s bilinear coefficients ≤ 2C₂^{(135)}Lℓ by CMP 98 Proposition 4 at k = 1, (135), uniform at complex W by Proposition 7, and Cauchy's estimate in two variables; abs(h(c)) ≤ (8/3)L^d from (124); the support in B(c₋) ∪ B(c₊). This gives {#D.C_𝐉} C_𝐉 := (256/3)NdC₂^{(135)}c_eB₀^{cx}α_JL^{d−2}e^{δ₁′(2d+1)L} and the total (B₀^{cx} + a + C_𝐉 + C_𝐆) |
| M1, consumers | (10.3), #C10.3.42-3, and the factor in #C10.4.122 and C(ε₀, γ_H) of #C10.4.123 now carry (B₀^{cx} + a + C_𝐉 + C_𝐆)/B₀ |
| M2, #C10.3.3-11-2: abs(Ā) ≤ 2δ′ + c_{GM}δ′² unsupported | New #C10.3.3-11-2-1: (0.10) with the BCH bound, and the continuity argument of #C10.3.34-7, give abs(Ā) ≤ (8/3)δ′ under 8c_Bδ′ ≤ 1 and 4δ′ ≤ r_B. Then abs(Z_Γ) ≤ (16/3)δ′ and abs(g_Γ − 1) ≤ 6δ′ for δ′ ≤ 1/46, which c_{GM}δ′ ≤ 1/66 gives. c_{GM} keeps only its dlog and Ad roles |
| M4, #C10.3.4 | 𝒬(U^A) = Q_j^{pl}(U^A) is onto by #C10.1.6-1 with n = j, and the line separates the invariance of A_ε from the covariance of M^j (CMP 98 (11)) |
| M5, #C10.3.51, -0 | #C10.3.29-2's entry states 4ρ_j below the α₁ of CMP 98 (158). New #C10.3.51-0-1 lists: PBG's a₁ of Theorem 3.4 (not VAR's a₁); M_P ≥ M₃ and M_Pα₀ + α₁ + α_JL^{−3} ≤ a_cx; 8c_Bδ′ ≤ 1 and 4δ′ ≤ r_B; the thresholds of CMP 98 Propositions 6 and 7; and O(1)L^d(Mα₀ + α₁) ≤ ½ for h. #C10.3.51-0 classifies δ₁ ≤ δ_Q^{pl} as a choice of PBG's rate, and #C10.3.15-1 says so |
| M6, #C10.3.14-2 | Two of the four transports differ from the covariant differences' by Ad(∂Ũ(p)), within 4C₀ε₁ε²/a_j² of 1. The correction is ≤ 8C₀ε₁(ε/a_j)α₁ε²/a_j² ≤ (1/15)α₁ε²/a_j², by ε/a_j ≤ 1/3 and 40C₀ε₁ ≤ 1. #C10.3.14-3 then has abs(Y_p) ≤ (16/15 + 8c_Bα₁)α₁ε²/a_j², and #C10.3.14-4's bounds hold: 1.192/8 ≤ 0.149, e^{0.149} ≤ 1.161 ≤ 6/5, 1.192·1.161 ≤ 1.39 ≤ 3/2 |
| M7, #C10.3.31-2, -3: c_D asserted | Derived. The weights are fixed, of total ≤ (2d + 2)L^{d−1}. Each term is one transport along ≤ (2d + 1)L bonds and ≤ 4 near-identity operators of norm ≤ 9/8. With v := c_vL^iη sup abs(A), the transports change by ≤ 2(2d + 1)Lv, h by ≤ (2d + 1)Lv, and every factor by ≤ k_G²(2d + 1)Lv, with the new {#D.k_G} (Lipschitz constants of log, dlog, dexp, Ad(e^{iY}), and their adjoints). So c_D := 9(2d + 1)(2d + 2)k_G², since 5(9/8)⁴ ≤ 9. c_D stays untagged, as the LF's {#D.c_D} is another object |
| M8, #C10.3.34-1 | Now cites (88), (92), and (97) for M^jU^A = (M^jU^A_ax)^{v_j} |
| Cosmetic, #C10.3.13 | Heading: "bounded by the plaquette curvatures" |
| Cosmetic, #C10.3.15-2 | The γ remarks are deleted. B₀(γ) is PBG's constant at γ = γ_H |
| Cosmetic, #C10.3.34-3 | "bi-invariant Finsler distance of this norm" |

- **Re-derived:**
  - J-term: 2·2d·(8/3)·2 = 64/3, times 4N gives 256/3. The exponent δ₁′d + δ₁′(d + 1)L ≤ δ₁′(2d + 1)L. Two adjacent blocks have ℓ¹ diameter ≤ (d − 1)(L − 1) + 2L − 1 ≤ (d + 1)L.
  - Cauchy in (s, s′): |F| ≤ C₂^{(135)}(2r_P/3)², and the ss′-coefficient is ≤ |F|(3Lℓ/r_P)² = 4C₂^{(135)}(Lℓ)², twice the bilinear part.
  - In (124) only the first, third, and fifth terms contain b₀(c): the contours stay in the blocks. On the line of c, the contour from c₋ to x is the straight segment, so every transport to b₀(c) reduces to the segment of c from c₋.
  - Pins: CMP 98 p.036 l.31–33 (the non-main terms are O(L²α₀)), p.043 l.15–17 (O(L²α₀ + Lα₁) at V′V₀, so Proposition 3 holds uniformly), Proposition 4 statement p.038–039 (C₂ depends on d), RG I p.267 l.18–23 (h).
- **Table (fork):** the rows #T3.27 and #T12.7-23 (δ₂), #T12.7-24 (C_𝐆 at δ₁′, and c_{GM} without the angle bound), #T12.7-25 (c_e at ½δ₁′), and the x_λ entry (line 588) need updating. New symbols: B₀^{cx}, C_𝐉, C₂^{(135)}, r_P, k_G, and the local T_c, e_c, α₀^W. The table fork was messaged at 07:18 with these and the new smallness conditions (table c9661181fd5a). It reports them done: table 75715b244ad6, labels ff427ec1b000, with new rows #T12.7-24-2 (B₀^{cx}, C₂^{(135)}, r_P, C_𝐉) and #T12.7-24-3 (k_G, c_D), and δ₂ = δ₁′ also in the map row #T12.15.
- **BX:** the repair rests on BP_PBG_COMPLEX.md (172709784d81), owned by another session. Its own review is the owner's.
- **Hygiene:** CR is 0; there are no trailing spaces or duplicate tags. All edited lines are ≤ 600 characters: #C10.3.3-11-2 and #C10.3.51-0 were split at sentences into #C10.3.3-11-2-1 and #C10.3.51-0-1.

Written 2026-11-09 07:18.

- **Missed consumer of M2 (07:29):** #C10.4.9-1-1-1 (packet 15) still used abs(Ā) ≤ 2δ′ + c_{GM}δ′². It now uses #C10.3.3-11-2-1, abs(Ā) ≤ (8/3)dε²abs(F), with 24c_BdC₀ε₁ ≤ 1 and 12dC₀ε₁ ≤ r_B added to its condition and to #C10.4.124. Cauchy is now 7a007794e060 (WILSON_IT1_LF_TRIAGE_P14A_R3_2026_11_09.md).
- **Split (07:36):** §10.3 is 27.45k with these repairs, so it is split into 14b1 (#C10.3.1–#C10.3.16) and 14b2 (#C10.3.17–#C10.3.51-1). 14b1's pre-check removes the local name α₀^W (it is table #T3.10's) from #C10.3.3-11-7-1. Cauchy is now ab50fa4809fd.
