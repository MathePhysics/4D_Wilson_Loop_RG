# Packet 14b1 (Cauchy #C10.3.1–#C10.3.16), round 3, 9 Nov 2026

## Pre-check of cauchy-p14b1-20261109-r3 (full)

- **Split:** with 14b r2's repairs (WILSON_IT1_LF_TRIAGE_P14B_R2_2026_11_09.md), §10.3 measures 27.45k, over the 25k cap. It is split at the heading *The Adjoint Averaging.* into 14b1 (#C10.3.1–#C10.3.16, 17.05k) and 14b2 (#C10.3.17–#C10.3.51-1, 10.36k). The rounds continue 14b's count, as for 13b1 and 13b2. The packet plan has the two rows.
- **Whole part re-read** (#C10.3.1–#C10.3.16), with BP_PBG_COMPLEX.md #BX.1–#BX.1-4 (172709784d81) and the table rows #T1.3, #T3.10, #T10.50, and #T12.7-24-2.
- **Re-derived:**
  - #C10.3.3-10: BX's hypothesis is abs(𝐉) < γ(L^jη)^{−3} at its scale. At the scale ℓ, abs(𝐉) < α_Ja_j^{−3} = α_JL^{−3}ℓ^{−3}, so γ = α_JL^{−3}. 𝒟_j has α₁/L at the scale ℓ (#C10.3.3-1), and Mα₀ + α₁ + α_JL^{−3} ≤ a_cx covers it. BX's constants depend on d, L, and G, its rates are δ₁′ and ½δ₁′, and its averages are the chain's dressed average.
  - #C10.3.3-11: each of the ≤ dL factors of a contour has norm ≤ (1 + O(1)α₁)², so the product is ≤ e^{2O(1)dLα₁} ≤ 4/3.
  - #C10.3.3-11-2-1: avg(A_Γ − Ā + E_Γ) = 0 with abs(E_Γ) ≤ 2c_Bδ′abs(Ā) ≤ ¼abs(Ā), so abs(Ā) ≤ (8/3)δ′. Then abs(Z_Γ) ≤ (14/3)δ′ + (16/3)c_Bδ′² ≤ (16/3)δ′, and (16/3)e^{16/138} ≤ 5.99 ≤ 6.
  - #C10.3.3-11-3: abs(𝒜 − 1) ≤ 3e, so (1 + e)/(1 − 3e) ≤ (12/11)/(8/11) = 3/2.
  - #C10.3.3-11-5–#C10.3.3-11-8-1: the J-term is 2ℓ^dΣ_c⟨h(c)C̃^{(2)}(B)(c), (H₁*𝐉)(b₀(c))⟩. So K = 2ℓ^{−d}Σ_c(…), with ≤ 2d sets per pair, and C_𝐉 = 2·2d·(8/3)·2·4N = 256Nd/3. The factor e^{δ₁′d} over-counts the e^{½δ₁′d} that d(x, y′) ≤ d(y, y′) + d needs, which is harmless.
  - #C10.3.14-1: (12/5)C₀ε₁ ≤ (12/25)α₁ ≤ ½α₁.
  - #C10.3.14-2: two terms carry the extra Ad(∂Ũ(p)) − 1, each of size ≤ α₁ε/(2a_j), so the correction is ≤ (8/3)C₀ε₁α₁ε²/a_j² ≤ (1/15)α₁ε²/a_j².
  - #C10.3.14-3: the three BCH steps keep every partial logarithm ≤ 2S ≤ 4α₁ ≤ r_B, with S := Σ_kabs(Z_k), under 4c_Bα₁ ≤ 1, and the error is ≤ 2c_BS².
  - #C10.3.14-8: with R := α₁/(8ρ_j) ≥ 2, abs(f(1) − f(0)) ≤ sup abs(f)/(R − 1) ≤ (16ρ_j/α₁)sup abs(f).
  - #C10.3.16: x_λ and B_λ follow from #C10.3.11, #C10.3.14-8, -9, and #C10.3.15-3 with the factor N.
- **Repairs made in this pre-check:**
  - #C10.3.3-11-7-1 named the plaquette bound of W₀ α₀^W, which is table #T3.10's W-δ class parameter. The line now states the bound inline: the plaquettes of W₀ are within O(1)Mα₀/L² of 1 (#C10.3.3-11-1), so the operators are O(1)(Mα₀ + Lα₁), O(L²) times that bound by p.036 l.31–33. The mathematics is unchanged.
  - #C10.3.14-2 cites #T1.3 for L ≥ 3.
- **Definition check:** 0 conflicts (9 allowed). 14b r2's allowed W, W₀, g_Γ, e, and 𝒜 are kept, with g_Γ now at #C10.3.3-11-2-1.
- **Size:** reviewed block 17.05k characters (25k cap). CR is 0, and there are no trailing spaces or duplicate tags. The longest edited line is #C10.3.3-11-8 (under 600).
- **Spec:** specs\spec_p14b1_r3.json (Cauchy ab50fa4809fd, LF 56d172c27cf2). BP_PBG_COMPLEX.md is permitted background: the reviewed lines rest on its statement #BX.1-2–#BX.1-3, and its own review is its owner's.
- **Order:** after 14a r3 and 14bp r3.

Written 2026-11-09 07:36.

## Pre-check update after 14a r3's repairs (08:15)

- **Changed line in the part:** #C10.3.4, as a consumer of #C10.1.6-1. 14a r3's M1 made #C10.1.6-1's hypotheses explicit. Its uses here, at n = j and the scale a_j, needed a case of their own (WILSON_IT1_LF_TRIAGE_P14A_R3_2026_11_09.md, update 08:12).
  - #C10.3.4: U^A satisfies 𝒟_j's condition on 𝐔 by #C10.3.14 at t = 1, as 8ρ_j ≤ α₁ under #C10.3.14-8's 16ρ_j ≤ α₁. #C10.1.6-1's third case, with the current 0, then gives onto-ness. #C10.3.14 uses no multiplier, so the argument is not circular. #C10.3.42, whose current bound uses B_λ, is not cited.
  - New #C10.3.4-0-1 (the old "likewise" for U^B): by the chain rule 𝒬(U^B) = d(M^j)(Ũ)dM(U^B), up to the positive unit factors of #C10.3.1-4. Q₁^{pl}(U^B) is onto since T^{pl}(U^B) = Q₁^{pl}Q₁^{pl}*(U^B) ≥ m_Q^{pl}/2 (#C9.4.3-4, #C9.4.5-2). d(M^j)(Ũ) is onto by #C10.1.6-1's third case, Ũ satisfying 𝒟_j's condition by #C10.3.14 at t = 0. A composite of onto maps is onto.
- **Spec:** Cauchy d901e7a1b941, LF 6ac728004094. The context now runs to #C10.1.6-1-1 and adds #C9.4.5–#C9.4.5-2. Claim (c) states both cases. Definition check: 0 conflicts (9 allowed).
- **Size:** reviewed block 17.43k characters (25k cap). The growth over 17.05k is the U^B argument. CR is 0, and there are no trailing spaces, duplicate tags, or lines over 600 among the edited lines.

## Pre-check update after 14a r4's repairs (08:50)

- **Changed line in the part:** #C10.3.3-12 is deleted. 14a r4's M1 moved the positivity of G₁^{−1} at the real pairs of 𝒟_j into #C10.2.1-0–#C10.2.1-0-1 (packet 14a), proved there by continuity from U₀ (WILSON_IT1_LF_TRIAGE_P14A_R4_2026_11_09.md). No line of the Cauchy note, the LF, or balaban_proofs/ cites #C10.3.3-12, and no line of 14b1 uses PBG Theorem 3.11.
- **Consumers of 14a r4's other changes:** #C10.3.4 and #C10.3.4-0-1 use #C10.1.6-1's third case with the current 0. Its new wording (the current 0 lying strictly inside #BX.1-3's bound) changes no condition used here.
- **Table:** 8b8f7c1733bc (LABELS 6dd1919a39c2). #T12.24-1-2-1's W is now N_Q, #T12.22's split moves c₀, □^{(n)}, X_□, F₂, and γ_ℓ to #T12.22-0-1, and #T10.36-4 reads Bałaban's σ as σ_H/σ_H(0). 14b1 cites none of these rows (it cites #T12.24 only).
- **Spec:** Cauchy 045261827913, LF 6ac728004094. Claim (b) drops the clause on Theorem 3.11, and claim (b) and question 2 end at #C10.3.3-11-8-1. Definition check: 0 conflicts (9 allowed).
- **Size:** reviewed block 17.29k characters (25k cap), down from 17.43k by the deleted line. CR is 0, and there are no trailing spaces or duplicate tags.
- **Order:** after 14bp r4.
- **Built** at 08:55 (Cauchy 14ee33c357e1, whose 14a pre-check edits in #C10.2.1–#C10.2.1-0 lie outside this packet's extracts, LF 6ac728004094, table 3f73b58833dd, LABELS c7ac77a7f926, BP_CMP98_ADJOINT_AVERAGING 0c5dc5ff8bfd after 14bp r4's rewordings, BP_PBG_COMPLEX 782efe167a1d). Definition check: 0 conflicts (9 allowed). The argument field, context included, is 30.4k characters, of which the reviewed block is 17.29k. Launched at 08:55, after 14bp r4's triage.

## Verdict of cauchy-p14b1-20261109-r3 (full)

No fatal or serious finding; seven minor findings, m1–m7. The referee's verdict: the claim is correct as stated, conditional on BP_PBG_COMPLEX #BX.1-2–#BX.1-3 and the §10.1 readings. Not clean.

| Finding | Repair |
|---|---|
| m1, #C10.3.3-8–#C10.3.3-9: G₁'s series (3.138) uses H, hence (QGQ*)^{−1}, before BX supplies them | #C10.3.3-8 now concludes for (3.130) and G only. #C10.3.3-9 says (3.138) contains Δ^{(2)}_π, hence H and (QGQ*)^{−1}, and needs (3.133) for H, and cites BX for the inverses and with them H, G₁, and H₁. #C10.3.3-10 states BX's conclusions |
| m2, #C10.3.3-10 last sentence and #C10.3.10-2: PBG's B₀ and δ₁ at real pairs read, not printed | #C10.3.3-6 now pins where PBG uses (3.36), only for the size of the current (p.419 l.11–12, p.422 l.50). #C10.3.3-10 derives the real case from Theorem 3.12, which states (3.133) for H and H₁ (p.423 l.33–36) through (3.132) for both inverses (p.422 l.15–21), with #C10.3.3-6. #C10.3.10-2 cites Theorem 3.12 at 𝐉 = 0 with #C10.3.3-6 |
| m3, #C10.3.3-11-6–#C10.3.3-11-7: h and C̃^{(2)} taken with the double bar, RG I's Q̃ being plain | #C10.3.3-11-6 states that C̃^{(2)} is taken with the double bar of PBG's (3.155), #C10.1.3-0's reading, inferred, not printed. #C10.3.3-11-7 shows that h is RG I's operator: by (B1) at n = 1 the plain and double-bar linear parts differ by D̄Θ₁, and Θ₁B(y) involves B only on the contours in B(y) (CMP 98 (97), v₁(x) the transported average of U₁ over B(x)), while b₀(c) joins two blocks. The (124) computation moved to #C10.3.3-11-7-0 |
| m4, #C10.3.4-0-1: "up to positive factors of the units" | Replaced by the exact chain rule 𝒬(U^B) = 𝒬(Ũ)Q₁^{pl}(U^B) (#C10.3.1-6) |
| m5, #C10.3.4: t = 1 needs 16ρ_j ≤ α₁, stated only at #C10.3.14-8 | #C10.3.4 says t = 1 lies in #C10.3.14's disc since 16ρ_j ≤ α₁ (#C10.3.51) |
| m6, #C10.3.3-10-1 and #C10.3.3-11-6: thresholds of CMP 98 Propositions 6 and 7 implicit | #C10.3.3-10-1: Proposition 6 with ℓ as its unit, U₀ satisfying its (52) with O(1)Mα₀/L² and abs(A′) < α₁/L in its units. New #C10.3.3-11-6-0: Proposition 7 with Lℓ as its unit, W₀ satisfying its (52) with O(1)Mα₀ (#C10.3.3-11-1) and W′ = e^{iA′/L}, abs(A′) ≤ O(1)Lα₁ < r_P. Both are below the thresholds for α₀ and Lα₁ small |
| m7, #C10.3.3, #C10.3.3-1, #C10.3.14: ∇ for ∇_{U₀}; (3.35) at a_j implies (3.35) at ℓ not stated | ∇_{U₀} in #C10.3.3, ∇_Ũ in #C10.3.14 and #C10.3.14-2. #C10.3.3-1 states that U₀ satisfies (3.35) at the scale ℓ by #C10.2.1-0-1's cube argument |

- **Re-derived:**
  - (52) is abs(U(∂p) − 1) < α₀η² with the coarse lattice as unit (CMP 98 p.026 l.14). With ℓ as unit, η = ε/ℓ, and U₀'s plaquettes within O(1)Mα₀ε²/a_j² = O(1)Mα₀L^{−2}η². ℓabs(A) < α₁/L.
  - With Lℓ as unit, η = 1/L and W₀'s plaquettes within O(1)Mα₀/L² = O(1)Mα₀η². abs(log W′) ≤ O(1)α₁ gives abs(A′) ≤ O(1)Lα₁.
  - Theorem 3.12 (p.423 l.33–36) asserts (3.133) for H and H₁, which p.422 l.21–25 derives from (3.132) for both inverses. (3.36) enters PBG's argument only at p.419 l.11–12 (the smallness of J) and p.422 l.50 (the bound on H*J).
- **Consumers grepped:** #C10.3.51-0-1 cites #C10.3.3-8 for the series of (3.130), unchanged. #C10.2.1 cites #C10.3.3-1 and #C10.3.3-10, whose conclusions are unchanged. No other line cites #C10.3.3-9 or #C10.3.3-11-7.
- **Size:** 14b1 is 18.54k (25k cap), up from 17.29k by the derivations of m2, m3, and m6. Lines ≤ 581, no duplicate tags.
- **Repaired SHA:** Cauchy f92f946e4b55 (with the 15a and 15b pre-check repairs of the same pass, outside this part).
- **Next:** r4, narrow, on the changed lines and their consumers; then r5, full.

Written 2026-11-09 09:22.
