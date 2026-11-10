# Packet 14b2 (Cauchy #C10.3.17–#C10.3.51-1), round 3, 9 Nov 2026

## Pre-check of cauchy-p14b2-20261109-r3 (full)

- **Split:** see WILSON_IT1_LF_TRIAGE_P14B1_R3_2026_11_09.md. 14b2 is #C10.3.17–#C10.3.51-1, 10.36k.
- **Whole part re-read** (#C10.3.17–#C10.3.51-1), with BP_CMP98_ADJOINT_AVERAGING.md #C10.3.21–#C10.3.24-4 and the table rows #T1.3, #T10.43, and #T12.7-24-3.
- **Re-derived:**
  - #C10.3.25-4: Σ_{i<n}L^{2(i−n)} ≤ (9/8)L^{−2} ≤ (4/3)L^{−2}, so the product is ≤ exp((16/3)c_QL^{d−1}C₀ε₁) ≤ e^{2/3} ≤ 2 under (AQ). (ii)'s condition holds at every level: 4c_{av}C₀ε₁ ≤ 1/(20(d + 1)L^{d−1}) by c_Q = 10(d + 1)c_{av}.
  - #C10.3.31: the 2d transports of D* on T_{L^{i+1}η} change by ≤ 2c_vL^{i+1}η sup abs(A) each, divided by the spacing, which gives 4dc_v sup abs(A).
  - #C10.3.31-2–#C10.3.31-3: a product of five factors of norm ≤ 9/8, each changing by ≤ k_G²(2d + 1)Lv, changes by ≤ 5(9/8)⁴k_G²(2d + 1)Lv ≤ 9k_G²(2d + 1)Lv. k_G ≥ 2 covers the transports' 2(2d + 1)Lv, and k_G² covers the compositions through Y_c. With the weights ≤ (2d + 2)L^{d−1}, this gives c_D.
  - #C10.3.32: the per-level defect is (c_D + 4d)c_vL^{d−1}L^{i+1}η sup abs(A)·2 sup abs(μ). Summed with Σ_{i<n}L^{i+1}η ≤ (3/2)a_j ≤ 2a_j and multiplied by the product ≤ 2, it gives C′_Q = 8(c_D + 4d)c_vL^{d−1}.
  - #C10.3.34-6: Σ_{i<j}L²α₀^{(i)} ≤ (9/2)C₀ε₁ ≤ (16/3)C₀ε₁, and exp(1/3 + 1/4) ≤ 2.
  - #C10.3.34-7–#C10.3.34-8: c_Ba_i ≤ 8c_Bdρ_j ≤ ¼ gives abs(Z) ≤ (4/3)a_i ≤ (32/3)dρ_j ≤ (2/3)r_B. Then Σ_{i<j}Lθ_i ≤ 12ρ_j for L ≥ 3, so the sums are 16dρ_j and 32dρ_j.
  - #C10.3.40: 2(x_λ + c_brc_wB_λ) + (4C′_Q + 2c_brc_w)B_λ = 2x_λ + (4C′_Q + 4c_brc_w)B_λ.
  - #C10.3.42-2: abs(𝐉(t)) ≤ (2B_λε₁ + ¼α_J)a_j^{−3} ≤ ¾α_Ja_j^{−3}.
  - (10.3): with R_𝒟 ≥ 2, abs(f(1) − f(0)) ≤ 2 sup abs(f)/R_𝒟 ≤ [16ρ_j/α₁ + 8x_J(ρ_j + (ε/a_j)ε₁)/α_J]sup abs(f).
  - #C10.3.51–#C10.3.51-0-1 list every condition of #C10.3.1–#C10.3.42-2. Those of #C10.3.14-2 (40C₀ε₁ ≤ 1, from 5C₀ε₁ ≤ α₁ ≤ 1/8) and #C10.3.14-8 (16ρ_j ≤ α₁, inside R_𝒟 ≥ 2) follow from listed ones.
- **No repair needed** in this part. 14b r2's M5, M7, and M8 repairs are re-read above.
- **Definition check:** 0 conflicts (7 allowed): Y, c_w, δ𝐉, and a_i as in 14b r2, and k_G, c_D, and v (the local abbreviation of #C10.3.31-2).
- **Size:** reviewed block 10.36k characters (25k cap). CR is 0, and there are no trailing spaces or duplicate tags.
- **Spec:** specs\spec_p14b2_r3.json (Cauchy ab50fa4809fd, LF 56d172c27cf2). 14b1's #C10.3.1–#C10.3.1-6, #C10.3.3–#C10.3.3-1, #C10.3.3-10, #C10.3.3-11-8-1, #C10.3.4–#C10.3.6, #C10.3.14–#C10.3.14-4, and #C10.3.16 are context.
- **Order:** after 14b1 r3.

Written 2026-11-09 07:36.

## Pre-check update (08:56)

- **No line of the part changed** since this pre-check: #C10.3.17 to the end of §10.3 is identical in Cauchy ab50fa4809fd (snapshot of cauchy-p14a-20261109-r3) and 14ee33c357e1, by a line diff.
- **Context changes:** 14a r3 and r4 rewrote #C10.1.6-1 (its hypotheses per case) and added #C10.3.4-0-1 (the onto-ness of 𝒬(U^B)), both inside this packet's context extracts. #C10.3.3-12 is deleted; the part, the spec, and the context do not cite it. BP_CMP98_ADJOINT_AVERAGING (0c5dc5ff8bfd) has 14bp r3's and r4's rewordings of #C10.3.21-2–#C10.3.23-4 (the signs, the transports to b₋, P_{b,Γ} as Ad of a transport). The bound (ii) and the column weights that #C10.3.31-2 uses are unchanged.
- **Table:** 3f73b58833dd (LABELS c7ac77a7f926). The part cites #T6.23 and #T10.43, neither touched by the fork's changes since 07:36 (#T12.12(a), #T12.22, #T12.24-1-2-1, #T10.36-4).
- **Spec:** Cauchy 14ee33c357e1, LF 6ac728004094. Definition check: 0 conflicts (7 allowed). Size unchanged at 10.36k.

## Pre-check update after 14b1 r3's repairs (09:24)

- **No line of the part changed.** 14b1 r3's repairs (WILSON_IT1_LF_TRIAGE_P14B1_R3_2026_11_09.md) touch the context lines #C10.3.3 (∇_{U₀}), #C10.3.3-1 ((3.35) at the scale ℓ), #C10.3.3-10 (BX's conclusions and the real case from Theorem 3.12), #C10.3.4 (t = 1 in #C10.3.14's disc), and #C10.3.14 (∇_Ũ). The part uses #C10.3.3-10 only for B₀^{cx} and δ₁′, and #C10.3.14 only for (3.37) along U(t), both unchanged in substance.
- **Other files:** table a63138631eb6 (LABELS 33ee63b855ee) after the fork's #T10.36-4 change, which the part does not cite. BP_PBG_COMPLEX f7ccda5b3de6 changes only its header line; #BX.1-2–#BX.1-3 are unchanged.
- **Spec:** Cauchy f92f946e4b55, LF 6ac728004094. Definition check: 0 conflicts (7 allowed). Size 10.36k.
- **Order:** next, after 14b1 r3's triage.
- **Built** at 09:25 (Cauchy f92f946e4b55, LF 6ac728004094, table a63138631eb6, LABELS 33ee63b855ee). Definition check: 0 conflicts (7 allowed). The argument field, context included, is 24.1k characters, of which the reviewed block is 10.36k. Launched at 09:25.

## Verdict of cauchy-p14b2-20261109-r3 (full)

No fatal or serious finding, and five minor findings, M1–M5. So the round is not clean. The referee also gave two nits that are not findings. The review was read in full.

| Finding | Repair | Lines |
|---|---|---|
| M1: c_v is called "the O(1) of (162)–(163)", but it is 3c_{(163)} + 2. The (52) hypothesis of §E is not stated. | #C10.3.29-2 rewritten in place: for real A the factors of (159) are unitary, so the bound is 2abs(v_i − 1) + abs(Ū̄′^i − 1) by (161), (163), and Σ_{i′<i}L^{i′+1} ≤ (3/2)L^i. It defines {#D.c_v} c_v := 3c_{(163)} + 2 and adds the hypothesis that U satisfies (52) with α₀ = 2C₀ε₁ below §E's threshold (p.042 l.16–17, p.043 l.10). LF #4.53-1 now cites the constant instead of restating it. | #C10.3.29-2, LF #4.53-1 |
| M1′: #C10.3.51 omits §E's α₀ condition. | Added to #C10.3.51's entry for #C10.3.29-2: "and 2C₀ε₁ below §E's threshold for α₀". | #C10.3.51 |
| M2: #C10.3.36 omits some of #C10.3.35's hypotheses. | #C10.3.36 now lists 2C₀ε₁ ≤ c₂ (for α₀^{(i)}, #C10.3.25-1), c₁₂₄C₀ε₁ ≤ 1/16, and C₁^{(123)}ρ_j ≤ 1/64. | #C10.3.36 |
| M3: c₁₂₄ is used before it is defined. | Defined at its first use, {#D.c₁₂₄} in new #C10.3.34-5-1 (the O(1) of (126), with (109)'s α₀). #C10.4.9-6 now cites it. The table fork was asked for a row. | #C10.3.34-5, #C10.3.34-5-1, #C10.4.9-6 |
| M4: r_inj is not defined for the operator-norm distance, and the subadditivity is asserted. | #C10.3.34-3 proves the bound for a sum < π. New #C10.3.34-3-1 shows the logarithm lies in i𝔤. r_inj is replaced by π in #C10.3.36 and removed from #CK.1-28. | #C10.3.34-3, #C10.3.34-3-1, #C10.3.36, #CK.1-28 |
| M5: "each term is a product" does not describe BP #C10.3.21-4's term. | #C10.3.31-2 describes that term and bounds its norm by 5/8. #C10.3.31-3 defines k_G before its first use (it was used one line early) and gives v. New #C10.3.31-3-1 bounds that term's change and defines c_D. | #C10.3.31-2, #C10.3.31-3, #C10.3.31-3-1 |
| Nit: #C10.3.39 uses ε₁ ≤ 1 before #C10.3.39-1 states it. | #C10.3.39 ends "by ε₁ ≤ 1". | #C10.3.39 |
| Nit: #C10.3.31's 4dc_v could be 2dc_v. | Kept. It is a valid upper bound, and C′_Q is defined with it. | none |

- **Queued re-pointings** from 14b1 r3's re-cut are now applied to #C10.3.51-0-1 (WILSON_IT1_LF_TRIAGE_P14B1_R4_2026_11_09.md): Theorem 3.4 now cites #C10.3.3-8, BX's conditions #C10.3.3-9, and Proposition 7's threshold #C10.3.3-11-6-0. The referee read the old pointers as correct, since the content sits in that range.
- **Re-derived:**
  - **M1.** In T_{a_j} units, U′ = e^{iη_CMP A″} with A″ = a_jA and η_CMP = η/a_j. (163) at level i gives abs(v_i − 1) < c_{(163)}α₁Σ_{i′<i}L^{i′+1}η_CMP ≤ (3/2)c_{(163)}α₁L^iη_CMP, and (161) gives abs(Ū̄′^i − 1) ≤ abs(log Ū̄′^i) < 2α₁L^iη_CMP. The sum is (3c_{(163)} + 2)α₁L^iη_CMP = c_vL^iη sup|A| at α₁ = a_j sup|A|. Ũ's plaquettes are ≤ 2C₀ε₁ε²/a_j² (#C9.3.3-1), which is (52) with α₀ = 2C₀ε₁.
  - **M4.** For normal u the numerical range is the convex hull of the eigenvalues, so φ(u) ≤ θ < π iff Re⟨v, uv⟩ ≥ cos θ for every unit v. The real angle ∠(a, b) = arccos Re⟨a, b⟩ on the unit sphere of ℂ^N = ℝ^{2N} satisfies the triangle inequality. ∠(g*v, v) ≤ φ(g) and ∠(v, hv) ≤ φ(h), so Re⟨v, ghv⟩ = Re⟨g*v, hv⟩ ≥ cos(φ(g) + φ(h)), and induction gives m factors. For the logarithm in i𝔤: along s ↦ ∏e^{s log g_k}, φ ≤ sΣ < π, so the principal logarithm is continuous. exp on 𝔤 is a local diffeomorphism at X when the eigenvalues of ad X, differences of eigenvalues of X, avoid 2πiℤ∖{0}, which holds for abs(X) < π.
  - **M5.** BP #C10.3.24-1 puts each factor within x ≤ 1/8 of the identity, so the bracket of BP #C10.3.21-4 has norm ≤ x + (1 + x)³ − 1 ≤ 0.55 ≤ 5/8. Its change is ≤ (1 + 3(9/8)²)k_G²(2d + 1)Lv ≈ 4.80k_G²(2d + 1)Lv, plus the transport's 2(2d + 1)Lv times 5/8, which is ≤ 0.32k_G²(2d + 1)Lv by k_G ≥ 2. The total is ≤ 5.11k_G²(2d + 1)Lv ≤ 5(9/8)⁴k_G²(2d + 1)Lv ≈ 8.01k_G²(2d + 1)Lv.
  - **15c check.** #C10.4.113-6's "L²α₀ = ε²|F|" is correct: α₀ is (109)'s plaquette bound, as #C10.4.9-6 states.
- **Size:** 14b2 is now 11.61k characters (10.36k before). The growth is the proofs of M1, M4, and M5 and the completed lists. Lines are ≤ 602 characters, CR is 0, and there are no trailing spaces or duplicate tags.
- **SHAs after repair:** Cauchy 5e2918ba9bcf, LF 8d84c228e098. The table fork was messaged about c_v (#T12.9), c₁₂₄ (a new row), c_D's tag (#T12.7-24-3), and r_inj. It confirmed the changes at table 48ed6504f348 (LABELS 44bfa18fd4a2): c_v at #T12.9 citing #C10.3.29-2, c₁₂₄ at #T12.7-24-3 ("a constant of d and G"), c_D citing #C10.3.31-3-1, and no row naming r_inj. These were re-checked against the repaired lines.
- **Next:** r4, narrow, on #C10.3.29-2, #C10.3.31-2–#C10.3.31-3-1, #C10.3.34-3–#C10.3.34-3-1, #C10.3.34-5–#C10.3.34-5-1, #C10.3.36, #C10.3.39, #C10.3.51, and #C10.3.51-0-1, with their consumers. Then r5, full.

Written 2026-11-09 09:47.
