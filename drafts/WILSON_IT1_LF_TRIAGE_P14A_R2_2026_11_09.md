# Packet 14a (Cauchy §10.1–§10.2), round 2, 9 Nov 2026

## Pre-check of cauchy-p14a-20261109-r2 (full)

- **Whole part read** (#C10.1.1–#C10.2.3) on 9 Nov 2026, after packet 14 r1's repairs, with its context: Cauchy #C9.8.1–#C9.8.1-2, #C10.3.3–#C10.3.3-11, #C10.3.4–#C10.3.4-1, #C10.3.25-1, and #C10.3.39.
- **Citations checked against the corrected transcriptions:**
  - RG I:
    - p.252 l.22–32: (0.3), the blocks B^k(y) = Δ(y) ∩ T, with Δ(y) the cube centred at y; the families 𝐆(y, x) of shortest contours.
    - (0.4) on p.253: the weights |𝐆(c₋, x)|^{−1}|𝐆(c₊, x′)|^{−1}, the loop Γ ∪ [x, x′] ∪ (−Γ′) ∪ (−c), and the outer factor U(c).
    - (0.5)–(0.11) on p.253: the axioms of the group average, Federbush's equation (0.10), and the contour variables (0.11).
    - (0.12) and l.7–10 on p.254 ("both definitions are equally good for our purposes"); p.254 l.26–30 (the gauge fixing through U(y, x) of (0.11)); (2.4)–(2.5) on p.266 l.4–15.
  - PRT1 (1.7) on p.18: the axial contour runs through the coordinates d, d − 1, …, 1.
  - CMP 98 (14) on p.019: Γ_{c₋,x} is taken from paper [2], which is PRT1.
- **Repair made in this pre-check:**
  - #C10.1.3-0-1 said that W(y, x) is "the product of W along the axial-gauge contour from y to x". RG I's gauge fixing uses the contour variables U(y, x) of (0.11), the group averages (0.10) over 𝐆(y, x) (p.253 l.12–13, "rather than to use one contour variable U(Γ_{y,x})"; p.254 l.26–30; p.255 l.43). The line now reads: "W(y, x) is RG I's contour variable (0.11), the group average (0.10) of the transports W(Γ) along the family 𝐆(y, x) of #C10.1.4-0-1 in the block B(y) of T_{Lℓ}".
  - Consumer #C10.3.3-11 (packet 14b) bounded B̃′(y, x) as a single contour sum, so it is re-derived for the average in #C10.3.3-11–#C10.3.3-11-4:
    - W = W′W₀, with W₀ = M^mU₀ real and |W′ − 1| < O(1)α₁.
    - The spread δ′ of the W(Γ) is at most O(1)dMα₀ + O(1)dLα₁. The real loop needs ≤ dL² plaquette moves, and the plaquettes of W₀ are ≤ O(1)Mα₀/L², by (3.35) with the Baker–Campbell–Hausdorff formula and CMP 98 Proposition 2 applied m times, as at #C10.3.25-1.
    - (0.6) and (0.8) give |g_Γ − 1| ≤ 6δ′. Differentiating (0.10) gives B̃′ = Σ_ΓT_ΓX_Γ with Σ|T_Γ| ≤ (1 + e)/(1 − 3e) ≤ 3/2 for e = 6c_{GM}δ′ ≤ 1/11. The transports have norm ≤ 4/3 under 2O(1)dLα₁ ≤ log(4/3), which was log 2 before.
    - So the coefficient is ≤ 2ℓ as before, and C_𝐆 := 4L^de^{δ₁dL} is unchanged.
    - c_{GM} is named apart from W-δ's c_G (#T4.10) and Cauchy #C11b.2-8's c_G.
  - Consumer #C10.4.1-4 (packet 15): "its blocks and axial contours" now reads "its blocks and contour families". This is bookkeeping, since 𝐆^{(2)} still depends on the background only through the block field.
- **Re-derived:**
  - (B1): Q_n^{pl} = Q_n − D̄^nΘ_n, from Ũ = Ū̄^{v_n} and A^λ = A − Dλ (PBG (3.116)).
  - (B2): onto-ness, since Q_n^{pl}(X₀ + D_Uω) = Q_nX₀ − D̄^nΘ_nX₀ + D̄^n(ω restricted) = B.
  - (B5):
    - Ū̄(U₁^u) = Ū̄(U₁)^{w_u}, with w_u = v₁(U₁^u)^{−1}u|v₁(U₁) for U^{gh} = (U^h)^g.
    - The λY terms of both sides, Q_nc(λ, Y) − 2C^{(2)}[Dλ, Y] = −D̄^nq_n(λ, Y) + c̄(Q′_nλ, Q_nY), give #C10.1.10.
    - The λ-only terms give Q_nD = D̄^nQ′_n.
  - #C10.1.4-3: for i < n, L^{2i}η² ≤ a_j²/L⁴ in both runs, so 4C₀ε₁L^{2i}η²/a_j² ≤ C₀ε₁.
  - §10.2:
    - G₁^{−1}H₁B = Q_m*(Q_mG₁Q_m*)^{−1}B, so the cross terms vanish, and the minimum is at A₀ = 0.
    - The polarised identity: ⟨A′, (Δ₁ + DRD*)H₁B⟩ = ⟨A′, Q_m*((Q_mG₁Q_m*)^{−1} − a)B⟩ = ⟨B′, P_UB⟩.
- **Earlier repairs:** packet 14 r1's S1 and M1–M8 are in the text (WILSON_IT1_LF_TRIAGE_P14_R1_2026_11_09.md). No 14a line holds a known weak point.
- **Definition check:** 0 conflicts (4 allowed): U₁, X, and ℓ (local, as in packet 14 r1), and Y_c (LF #5.21 instantiates it at U^B).
- **Size:** 8.9k before the pre-check and 8.98k after. The longest 14a line is 517 characters. CR is 0, and there are no trailing spaces.
- **Spec:** specs\spec_p14a_r2.json (Cauchy 61852ee2de80, LF 31538d03f6ab).
- **Order:** launch after 12b-bp r1 reports (one referee at a time). 14bp r2 follows.

Written 2026-11-09 05:19.

## Pre-check redone after the contour-variable double bar

- **Repairs since the 05:19 pre-check:**
  - #C10.1.4-1: (89) builds the double bar from the plain relative average M and the gauge averages (78)–(80). CMP 98 builds both with the axial contour Γ_{y,x} (CMP 98 (78), p.030 l.19, R(V₀(Γ_{y,x})); the notation at p.019 l.38–42). This pre-check moved the pin from p.019 alone to (78).
  - #C10.1.4-1-1: with M = (0.4), the gauge averages use RG I's contour variables U(y, x) of (0.11) in place of U(Γ_{y,x}), as table #T10.23 does for the chain's dressed average. Re-read against RG I:
    - (0.6) gives u(y)U(y, x)u(x)^{−1}, (0.9) membership in G, and (0.8) the linear part (p.253);
    - the replacement in the gauge fixing is at p.253 l.12–13 and p.254 l.25–26. This pre-check corrected the pin from l.26–27: l.25 is the block axial gauge and l.26 is "have to use other expressions than the contour variables U(Γ_{y,x}). We use the variables U(y,x)"; BETA #B9.40-3b pins the same lines.
  - #C10.1.4-1-1-1: CMP 98's (60)–(108) hold for these averages by BP_REG_DRESSED.md #BR.4–#BR.4-1 (permitted background in the spec).
  - #C10.1.8-3: at U = 1 the contour terms of (0.4), L^{−(d+1)}Σ_x(A(Γ̄_{c₋,x}) − A(Γ̄_{c₊,x′})) (#C9.8.1), and the linear parts of the gauge averages at c₋ and c₊ are the same family means, and they cancel in (89).
- **Re-derived for #C10.1.8-3:**
  - By (0.8) the linear part of U(y, x) at U = 1 is A(Γ̄_{y,x}).
  - The gauge average at y has the linear part L^{−d}Σ_xA(Γ̄_{y,x}) on T_η, that is L^{−(d+1)}Σ_xA(Γ̄_{y,x}) in the units of T_{Lη}.
  - In (89) the factors at c₋ and c₊ enter with opposite signs, so they remove the two Γ̄-sums of #C9.8.1 exactly as CMP 98's axial sums cancel. This leaves L^{−(d+1)}Σ_xA([x, x′]), CMP 98 (125).
- **Other queued repairs applied before launch:** Cauchy §10.3 (#C10.3.34-2, #C10.3.34-7 through -8, #C10.3.36), §10.4 (#C10.4.9-1-1 through #C10.4.113-7), #C9.4.4-4, #C7.4-7-5-2, and #C7.8-1-3; LF #4.135 through #0.1.39-4; BP_LFR2_CHI_K_LAMBDA.md (a2ed044a6797).
- **Claim and background:** the spec's claim (b) now states the contour-variable double bar; permitted_background adds BP_REG_DRESSED.md #BR.4–#BR.4-1 and table #T10.23.
- **Definition check:** 0 conflicts (4 allowed: Y_c, U₁, X, ℓ).
- **Size:** reviewed block 10.02k (8.98k at 05:19); argument with context 13.00k. The longest 14a line is 570 characters. CR is 0, and there are no trailing spaces or duplicate tags.
- **Spec:** specs\spec_p14a_r2.json (Cauchy 054141083507, LF b142ee965e51, table f44f990130f3, labels 5bc2ff823179).

Written 2026-11-09 05:53.

## Launch and messages

- Launched cauchy-p14a-20261109-r2 (full) on 9 Nov 2026 after 05:53.
- Table fork: sent the SHAs (Cauchy 054141083507, LF b142ee965e51, BP_LFR2_CHI_K_LAMBDA a2ed044a6797) and these points:
  - the relabel of the 13 new LF tags;
  - C_ε̂ := e^{2c_sh+2}C_pc for #T12.7;
  - K₁ ≤ K̄₁, period-free, for #T12.7-4;
  - the conditions of #C10.3.36 and #C10.4.9-1-1-1;
  - the contour-variable rows #T10.14, #T10.23, and Q′₁ of #C10.4.67.
- Two-loops: sent the Cauchy SHA, the #C7.4-7-5-2 wording, C_ε̂, and the §10 contour-variable change.
- Two-loops replied that none of its files quotes §10's double bar, Q′₁, Q̄₁, or Γ_{y,x}, and that its C^{ε̂} (#T4.55) is a different symbol from C_ε̂.
- The table fork replied (table 6af3278b159c, LABELS 064cb91459fe):
  - the relabel is done;
  - #T12.7, #T12.7-4 (with K̄₁), #T12.7-27 (Q′₁), and #T12.7-7 through -7-2 are updated;
  - c_B and r_B (#C10.3.14-3) are marked apart in #T12.7-24-1.
- The fork asked whether a line uses U(y, x) = 1 in #C9.8.14's axial gauge. None does:
  - #C9.8.14-1 bounds every in-block bond;
  - #C9.8.14-2 bounds every path of the families by its length (d + 1)L.
  I replied, and kept the names c_B and r_B.

## Verdict of cauchy-p14a-20261109-r2

- No fatal and no serious finding; two minor findings (m1, m2) and six cosmetic ones. The round is not clean.
- I re-derived both minor findings and agree with them.
  - **m1.** PBG's (3.16) at the single scale ℓ is aℓ^{d−2}Σ_b|(Q_mA)(b)|². Against ℓ^dΣ_b this is aℓ^{−2}⟨Q_mA, Q_mA⟩, so PBG's Q*aQ is aℓ^{−2}Q_m*Q_m. Read with a alone, the mass term would be off by ℓ², and #C10.1.3-3 would not follow from (3.132).
  - **m2.** BP_REG_DRESSED #BR.4-1 covers CMP 98 (60)–(108). (109), Proposition 3, (121)–(123), and (126) are taken for the dressed average on RG I p.254 l.7–8, which makes all results of [12] valid for (0.12), the average built on the contour variables (0.11), and on p.253 l.42–43. (124)'s explicit form is CMP 98's own.

## Repairs

| Finding | Line | Repair |
|---|---|---|
| m1 | #C10.1.2, #C10.2.2 | (10.1) and (10.2) have − aℓ^{−2}⟨B, B⟩. |
| m1 | new #C10.1.2-1 | The inner products η^dΣ_b and ℓ^dΣ_b, and PBG's (3.16) at the single scale ℓ, which gives Q*aQ = aℓ^{−2}Q_m*Q_m. |
| m1 | #C10.1.3, #C10.2.1-1, #C10.2.3 | G₁ = (Δ₁ + DRD* + aℓ^{−2}Q_m*Q_m)^{−1}; aℓ^{−2}⟨B, B⟩; G₁^{−1}H₁B − aℓ^{−2}Q_m*B. |
| m1, consumers | #C10.4.1-5, #C10.4.5-2 (packet 15) | aℓ^{−2}⟨B′, B⟩ and aℓ^{−2}⟨QX, QE⟩. |
| m2 | #C10.1.4-1-1-1, new #C10.1.4-1-1-1-1 | (60)–(108) by #BR.4–#BR.4-1. (109), Proposition 3 with (121)–(123), and (126) rest on RG I p.254 l.7–8 and p.253 l.42–43, both quoted. (124)'s explicit form is CMP 98's own, its contour terms here run over the families with #C10.4.9-1-1-1's weights, and #C10.1.8-3 derives the U = 1 linear part. |
| m2 | #C10.1.4-0-3 | Adds p.253 l.42, "do not depend on any particular averaging operation used". |
| m2 | #C10.1.8 | Q̄₁(U) is Q(U) of CMP 98 (121)–(122). |
| m2, consumer | #C10.3.34-5 (packet 14b) | "Proposition 3 ((122)–(123)) and (126) (#C10.1.4-1-1-1)"; "the linear part of (122)" in place of "(124)". |
| m2 | #C10.1.8-3, new #C10.1.8-3-1 | The U = 1 cancellation is derived for the contour-variable gauge averages: λ_y := L^{−(d+1)}Σ_xX(Γ̄_{y,x}) by (0.8); (89) composes −λ_{c₋}, the linear part of M, and +λ_{c₊}; x ↦ x′ maps B(c₋) onto B(c₊). |
| cosmetic | #C10.1.4-1 | (89)–(92). |
| cosmetic | #C10.1.3-3 | r_j is the least number with the bound. |
| cosmetic | #C10.1.8-2 | The n-fold double bar of the fluctuation e^{iηX} about U. |
| cosmetic | #C10.1.8-1 | C̄₁^{(2)} is in the normalisation of #C10.1.8-2. |
| cosmetic | #C10.1.9-2, #C10.1.9-4 | The n-fold transformation is w_u^{(n)}, the composite of the one-step ones along the levels. |
| cosmetic | #C10.1.3 | Q_m is PBG's linearised m-fold averaging built on the double bar of #C10.1.4-1, with PBG's operators and bounds taken for it as #C10.1.4-1-1-1 states. |

- Grep of all uses: Q*aQ in #C5.69–#C5.70 is PBG's own notation at U = 1, and aQ*Q in #C9.4.1-2 is VAR's form at VAR p.293. Neither uses the note's inner products, so neither changes. "(124)" remains only in §10.4 (packet 15) for the non-main terms, which #C10.1.4-1-1-1-1 now covers.
- Hygiene: CR is 0, there are no trailing spaces or duplicate tags, and no §10.1 line is over 600 characters.
- **Repaired SHA:** Cauchy 00e33ad08351.
- **Next round:** 14a r3, full, after 14bp r2, 14b r2, and 12b-bp r2.
- **Table fork, sent:** #T12.7-23's P_U needs − aℓ^{−2}⟨B, B⟩ (m1, with the derivation); w_u^{(n)} is new local notation; the new tags are #C10.1.2-1, #C10.1.4-1-1-1-1, #C10.1.8-3-1, and #C10.3.3-10-1. #T12.24-1-0-1 (BX Step 7, on the unit lattice L^kη = 1) needs no change. I also suggested that #T6.5-2 point to #C10.1.4-1-1-1 for the scope of Proposition 3 at the dressed average.
- **Table fork, reply (checked in the table):** #T12.7-23 reads "P_U(B) := ⟨B, (Q_mG₁Q_m*)^{−1}B⟩ − aℓ^{−2}⟨B, B⟩, aℓ^{−2}Q_m*Q_m being PBG's Q*aQ at scale ℓ (#C10.2.2, #C10.1.2-1)" and lists w_u^{(n)}. #T6.5-2 ends "For the chain's dressed average: Cauchy #C10.1.4-1-1-1." The relabel is done. Table 541c27303c76, LABELS 63082681d0d8.

Written 2026-11-09 06:15.
