# Consolidation of the Open Packets, 8 Nov 2026

The user asked (8 Nov 2026) to go through every remaining packet, read the text itself rather than the citation graph, consolidate it, and add citations where a step uses something without one; packets are not split. Each packet below records what was read, what was merged or deleted, the citations added, and its size before and after. A fact argued in several places is kept once, at the place that first needs it, and cited from the others; a restated table row is replaced by the row's citation; roadmaps and asides are deleted.

## Order

13b2 (in review), then the LF packets in the plan's order (16, 17, 33–47, 50–53, with 12b), then the Cauchy packets (14, 15, 30–32, 48–49), then the W-δ packets (18–29), then the closed-readings packets (54–59).

## 13b2 (LF #4.517–#4.517-2, #4.561–#4.565-1, #4.567–#4.568)

Read in full, with #4.472–#4.472-0-1, #4.559–#4.560-0, and the Cauchy note's #C8.6.5–#C8.6.7 (14:41–14:50). LF 16ba68a9c7f3 → d57736f994e7.

| Finding | Change | Lines |
|---|---|---|
| abs(X − 1) ≤ abs(Y)abs(U^r(∂p) − 1) + abs(Y − 1) ≤ 4C₀^{ms}ε₁′ + 3ε₂ for the moved plaquette X = YU^r(∂p) was computed three times | stated once in #4.563-2.1-1 at the spacing a_j of the run's own layer; #4.563-2.2 and #4.563-3-0 cite it | #4.563-2.1-1, #4.563-2.2, #4.563-3-0 |
| #4.564 was a roadmap; its one fact, that Lemma (Two Constants) is applied at z = i, was missing from the lines that use it | #4.564 kept as a heading only; #4.565-1 and #4.566 now name the Lemma (#4.557) at z = i (#4.559); "absorbed as the real ones are" moved into #4.567-1 | #4.564, #4.565-1, #4.566, #4.567-1 |
| #4.561.1-3 restated #4.508 (ι's C₁ and ε₂^ι, with M_c of #4.504) and the M-dependence visible in C_{V′} and stated in #4.562-1.1; cited nowhere | deleted | #4.561.1-3 |
| #4.561-1.1 restated table rows #T3.32-1, #T3.32-2, #T1.4, #T4.23 | reduced to the claim and the rows | #4.561-1.1 |
| #4.563-2-1 restated #T11.19-1, #T11.20-1, #T11.37-1 (the covariant differences and the norm of (19)); cited nowhere | deleted; the rows cited at the end of #4.563-2 | #4.563-2, #4.563-2-1 |

Re-derivations. c_pl: in run A's indexing run B's plaquette field strength is ≤ 2·2C₀^{ms}ε₁′/a_j² + 3L²ε₂/a_j² = (4C₀^{ms} + 3L²B₅^c)ε₁′/a_j² = c_plC₀^{ms}ε₁′/a_j². abs(X^{−1}) ≤ 2 from abs(X − 1) ≤ ½ by the Neumann series. Lemma (Two Constants) at 𝔳 = 24, 𝔳₁ = 25 gives 𝔨^{15/16}𝔎^{1/16} at z = i, and (1/3)(15/16) = 5/16, the exponent of #4.565-1 and #4.566; the real bound holds on (−24, 24) (#4.560) and the disc bound on abs(z) < 25 (#4.563).

Not merged, with reasons: the restatements of abs(B^e(z)) ≤ 2c_avε′_k and ε₁′ ≥ ε′_k are one-clause uses with their citations; (T-c) is stated in #4.561 and #4.561-1.2 because the second half needs C_{V′} and ε₂, defined in between.

## Across §4: the Absorption Lemma and the Layer Widths

LF d57736f994e7 → 8221d0a3d3a2 and on (14:50–15:10). Each of these lines had re-argued the bound of k, of log g_k^{−2}, or of R_k, or the absorption of polynomial factors by a power L^{−sn}. They now cite the absorption lemma #4.55-0.1–#4.55-1-1, which states k ≤ K < 8n + j(C), log g_k^{−2} ≤ log(ḡ^{−2} + 8b′n + b′j(C) + C_W) (BETA Lemma 2.1(i)), R_k ≤ 2^{r+1}L(log g_k^{−2})^r, and L^{−s(1−ε₀)n} ≤ θ̃^nL^{−(s−¼)(1−ε₀)n} for s > ¼.

| Finding | Change | Lines |
|---|---|---|
| the bound of R_k and of log g_k^{−2} and the absorption at s = ⅓ re-argued | cite #4.55-0.1–#4.55-1-1 | #4.166, #4.189-1, #4.208 |
| k < 8n + j(C) and the bound of log g_k^{−2} re-argued in (iv)'s result and its thresholds | cite #4.55-0.1 | #4.459-0.0, #4.459-0.1 |
| the ratio's k-bound and g_k-bound re-argued at complex and at real points | cite #4.55-0.1 and #4.55-1 | #4.553, #4.553-1, #4.554-0.2, #4.554-1 |
| R_k and (k − m + 1)^{1/2} re-argued for the radii of 13-part points | cite #4.55-1–#4.55-1-1 at s = 5/16 with m for n | #4.598 |
| ε_k/ε_m and k < 8n + j(C) re-argued in the configuration part, with an aside on CRE (2.8) | cite #4.554 and #4.55-0.1; aside deleted | #4.456-1-1 |
| the layer widths argued in #4.63 and again in #4.80, the M case without a source for M > 5L + 1 | stated once in #4.63-1, with M ≥ 2(d + 1)L²M₁ ≥ 10L² (W-δ #W8.19-1), M₁ = KM′ ≥ M′ ≥ 6L (#T2.9, #W8.18), and RM ≥ 12L (#4.98); #4.80 cites #4.63-1 | #4.63, #4.63-1, #4.80 |

Re-derivations. #4.553-1: 15kε₀/16 < 15(8n + j(C))ε₀/16, and 5(1 − ε₀)/16 − 15ε₀/2 = 5(1 − 25ε₀)/16; with θ̃ ≥ L^{−(1−ε₀)/4}, 5(1 − 25ε₀)/16 − 4(1 − ε₀)/16 = (1 − 121ε₀)/16. #4.554-0.2: (1 − ε₀)/3 − 8ε₀ = (1 − 25ε₀)/3, and (1 − 25ε₀)/3 − (1 − ε₀)/4 = (1 − 97ε₀)/12. #4.456-1-2: θ_V(1 − 25ε₀)/3 − θ_V/8 = 5θ_V(1 − 40ε₀)/24, and k − m + 1 ≤ k + 1 < 8n + j(C) + 1 ≤ (1 + j(C))(8n + 1). #4.63-1: S_j lies within a_j of Ω_j^c and the next interface reads within (d + 1)a_{j+1} = (d + 1)La_j of Ω_{j+1}, so the width needed is (d + 1)L + 1 = 5L + 1 in the units a_j; 10L², 6L, and 12L all exceed it for L ≥ 2.

Lines over 600 characters that these edits touched are split at sentences into tagged sub-lines: #4.63-1, #4.189-1, #4.189-2, #4.208-1, #4.456-1-1, #4.456-1-2, #4.459-0.0, #4.459-0.1, #4.459-0.2, #4.553-1, #4.553-2, #4.553-3, #4.554-0.1, and #4.554-0.2 are new.

## Packet 16 (LF #4.60–#4.138)

Read in full. Little internal duplication: #4.100–#4.105 and #4.131 already cite the Cauchy note's arguments. Repaired (LF → b94c97a111f5):
- #4.118 combined the twist bound with the second-order chain rule for β_f. The chain rule is now its own item, #4.118-1 (*The chain rule for β_f.*), with #4.118-2 and #4.118-3.
- The commutator bound appeared as abs([X, Y]) ≤ 2abs(X)abs(Y) in the operator norm (#4.62) and as c_Gabs(X)abs(Y) (#4.135), with c_G W-δ's constant (#T4.10) and the LF's abs(·) the operator norm (l.536). #4.135-1 now uses 2, and states the path sum's norm ≤ dLη sup abs(A) = dε sup abs(A). So c_q := 4d, where it was 4dc_G; the table fork was asked to change the row. Re-derivation: each ½[X, Y] term is ≤ ½·2 sup abs(λ)·dε sup abs(A), so the four terms give ≤ 4dε. A first version set 8d without showing the factor; the fork's check caught it, and the sharp 4d with the count written out replaced it. #4.135 is split (#4.135-0.1, #4.135-1, #4.135-2).
- The product-of-exponentials bound (abs(E) ≤ e^s − 1, abs(log(1 + E)) ≤ 2s) recurs in #4.62-1, #4.115, #4.517-2, and #4.561.1-1.3-2 as one-clause uses; not merged.

## Packet 17 (LF #4.139–#4.208)

Read in full (15:00–15:20).

| Finding | Change | Lines |
|---|---|---|
| #4.170 had a roadmap of the comparison and its decay budget, restated by #4.177 (rate δ₀/16) and #4.183 (u^{1/3}v^{2/3}, rate δ₀/24, (2.58)–(2.59) at α = 1/24); nothing cites the roadmap | deleted; #4.170 split into #4.170-0.1, #4.170-1, #4.170-2 | #4.170 |
| #4.171 cited CRE (2.24) twice for φ_m, and stated "F_K does not depend on the choice" before its reason | one sentence with the source; the claim joined to its reason by a colon | #4.171-1, #4.171-2 |
| #4.172 said twice that three printed statements force (RZ), and twice that it is Bałaban's convention | each said once | #4.172, #4.172-0.1, #4.172-0.2 |
| #4.189 used w̄ ≤ (1 + O(1)k)g_k^{−2} and ε̂ ≤ 2ε₁ without their sources | cites #4.170-2 (with g_k ≤ 1) and #4.177 | #4.189 |
| #4.190 cited p.364 l.35–36 again for w̄ | cites #4.170-2 | #4.190 |
| #4.195: "C_wcε̂² ≤ 1 since ε̂ ≤ 2ε₁" lacked a source; "D_l ≤ D^♭_l since β′ > 1/3" was not enough, since it needs L^{−β′} ≤ q = L^{−1/3}e^{−1/12} | cites #4.177; "since L^{−β′} ≤ q: β′ ≥ 19/40 (#T3.6), and (19/40 − 1/3)ln L ≥ 1/12 for L ≥ 2" (0.1417 × 0.693 = 0.098 ≥ 0.083) | #4.195, #4.195-1, #4.195-2 |
| #4.199: ε̂′ ≤ 2ε₁′ lacked a source; "The absorption" cited by name | δ′_k = g_kA₁p₁(g_k) ≤ g_kb_k ≤ ε′_k/25 ≤ ε₁′ (#4.177, #D.b_k, #D.ε′_k, #4.560.1-1); cites #4.568 | #4.199 |
| #4.201 ended with a roadmap sentence | deleted; the line split into #4.201-1–#4.201-3 | #4.201 |
| **Dead blocks.** #4.202 (the small form of (1.20): the identity with λ″, Δ′(ζ), and its bound), #4.203 (V(ζ, ·), V(ζ₀, ·) not bounded separately), #4.204–#4.207 (the linear term of (1.2): 𝒜_z, c_z, ψ_J, f := J^A(1 − ζ₀), C_ℓ(M)), and #4.208-1 (Bałaban's bounds of the parts not compared). #4.155, #4.167, and §0 (l.139) state that these parts enter the main proof only through d and 𝐂_k, compared as wholes. The semantic check found two consumers: #4.179's lift bound "as for 𝒜_z", and the Cauchy note's #CP.6-7, which said the linear term of (1.2) is derived in §4(d) | removed. #4.179 now cites the lift bound's own source, (3.133) and PBG Theorem 3.12 (#4.54-0.0–#4.54-0.0-1). #CP.6-7 now says that V(ζ₀, ·) and the linear term of (1.2) enter only through d (#4.155, #4.167). #4.208 says once that these parts are not compared separately (#4.155, #4.167). #4.167 drops "of the type of C_ℓ(M)". The table fork was asked to remove the rows of Δ′(ζ), C_ℓ(M), 𝒜_z, c_z, ψ_J, and #D.f.2 | #4.202–#4.207, #4.208-1 (removed); #4.167, #4.179, #4.208, Cauchy #CP.6-7 |

The (1.21) comparison does not depend on the removed blocks: §4(d) treats the forms of (1.2) and (1.21) together through the lifts H₁B̃ (#4.57–#4.60), and #4.160 reads (1.21) through #4.201. Lines split: #4.179-1–#4.179-3, #4.190-1, #4.201-1–#4.201-3.

Re-derivations. #4.183: u_y^{1/3}v_y^{2/3} = C_e^{1/3}(8C_L(2 + C_𝐇)C_𝐇)^{2/3}w̄ε₁^{2/3}ε̂^{4/3}(ε/a_{j(y)})^{(1−ε₀)/3}e^{−(δ₀/24)d(y,Λ)} ≤ C′w̄ε̂²(…). The count: dividing ⅛δ₀RM ≥ 4log L + 1 by 12 gives (1/96)δ₀RM ≥ (1/3)log L + 1/12; a layer m steps finer contributes 6c₀^dL^{m/3}e^{−((1/3)log L + 1/12)(m−1)} = 6c₀^dL^{1/3}e^{−(m−1)/12}; (1 − e^{−1/12})^{−1} ≈ 12.5 < 13; the total is 6c₀^d(1 + 13 + 13L^{1/3}) = c‴. #4.189: w̄ε̂² ≤ (1 + O(1)k)g_k^{−2}·4C(M)²R_k²g_k²p₀(g_k)². #4.195: C_wc = 4C_L(2 + C_𝐇)C_𝐇c₀^d(1/48)·(2·6·27 + 2·78) = 1920C_L(2 + C_𝐇)C_𝐇c₀^d(1/48), the near layers giving 2·6(1 + 2·13) and the far ones 2·6·13.

## Packet 50 (LF #4.151–#4.169)

Read in full (first pass 14:50, second 15:20).

| Finding | Change | Lines |
|---|---|---|
| #4.160 said twice that the bound is carried to the class by *The complex class.* under (T-c); its constant 11d was not itemised | said once; "(8 from the four actions, ½ from the form, 2 from φ_d, #4.155)" added; line split into #4.160-0.1, #4.160-1, #4.160-2 | #4.160 |
| #4.169 stated item (iii) twice ("The decoupled propagators, which need (W-δ)" and "(iii) is the relative walk-term bound"), with (ii)'s inputs between them | (ii) and (iii) each stated once, in #4.169-2 and #4.169-3; (i) split into #4.169-0.1 and #4.169-0.2 | #4.169, #4.169-1–#4.169-3 |
| #4.164's ≤ 4Cg_k²abs(δ_k)/κ_s used κ_s ≤ 1 without its source | "by min(t^A, t^B) ≥ ½t^A and 2(1 + κ_s) ≤ 4 (κ_s = 1/240, #T3.34-1)" | #4.164 |

Checked without change: #4.152 (C(M) ≥ 8(1 + κ_s)max(M₀, C_𝔛(M)) gives the moves ≤ ε₁/8, as R_k ≥ 1), #4.155 ((e^φ − 1)e^{c(M)} ≤ ½ gives abs(log d^B − log d^A) ≤ 2(e^φ − 1)e^{c(M)} ≤ 4e^{c(M)}φ for φ ≤ 1; D(1) factors out of both integrals), #4.159–#4.159-1, and #4.161–#4.168-1. #4.155 and #4.167 are the two statements that the parts other than (1.21) enter only through d and 𝐂_k. They are not merged, since #4.155 gives d's reason (the parts enter only through the action A(ζ₀, U_{k,Z}(V′V_Λ))) and #4.167 gives 𝐂_k's.

## Packet 33 (LF #4.209–#4.255, #4.465–#4.502)

Read in full, together with the neighbours #4.212, #4.216, #4.218, #4.219, #4.224, #4.228, #4.230 and #4.233–#4.244 that the packet's lines cite or repeat (15:23).

| Finding | Change | Lines |
|---|---|---|
| #4.215 and #4.216 both stated (iv) = [renB(U^B) − renB(ι_YU^A)] + r_z with the geometric-mean bound of (5.1v), and both said that the completions of p.377 l.22–26 at U_k are covered | the formula stays in #4.215; #4.216-1.1 cites it ("bounded with it as in #4.215") and is the one place for the completions (with #4.225) | #4.215, #4.216–#4.216-2 |
| #4.231 ("The decoupled configurations of (iii) are not minimisers") was a stray sentence inside the U_{1,2} list, with no citer; its content is #4.233-2.1's "W is neither a member of 𝒞 nor a composite" | removed; the fork has to drop its LABELS row | #4.231 |
| #4.232 quoted p.371 l.26–27 again, after #4.228 had quoted it for the same conclusion | it cites #4.228; #4.229's summary of where U_2 enters cites #4.232 | #4.228, #4.229, #4.232 |
| #4.230 stated twice that the strip data at the cut are 1, from W-δ §12 and (RZ) | stated once, with the status (derived, not reviewed) attached to the first statement | #4.230–#4.230-3 |
| #4.235 explained the section numbering of RG II again after #4.209 | it cites #4.209-0.1 | #4.235 |
| #4.226 had an overlap remark (∂Y_1 and ∂Y_2 can share parts), which no bound uses, and gave the reason why the boundary case is separate only after the side remarks | remark removed; the reason now follows the case | #4.226, #4.226-1 |
| #4.233-2.1 and #4.245 cited "§8.4" bare, but the LF has §§1–5 only | both say "the Cauchy note's §8.4"; #P.2 now states that a bare §6–§11 is the Cauchy note's unless the line names another note (checked: every such use in the LF matches the Cauchy note's headings, apart from l.1008, which names the walk note) | #P.2, #4.233-2.1, #4.245 |
| #4.467 restated RG I's p.278 l.46 and l.64 restrictions, which #4.476 lists | it cites #4.476 | #4.467 |
| #4.472-2 restated the far-domain bound of #4.233 | it cites #4.233-0.2 and #4.233-1 | #4.472-2 |
| #4.496 restated the value of C_{Q*} | it cites #4.244-2 (#D.C_Q) | #4.496 |

Lines over ~700 characters were split at sentence boundaries, keeping each sentence whole. The new sub-tags are #4.209-0.1, #4.209-0.2, #4.209-2, #4.216-1, #4.216-1.1, #4.216-2, #4.217-0.1, #4.217-1, #4.217-2, #4.218-1, #4.219-1, #4.226-1, #4.227-1, #4.229-1, #4.229-2, #4.230-1–#4.230-3, #4.232-1, #4.233-0.1, #4.233-0.2, #4.233-1.1, #4.233-1.2, #4.233-2.1, #4.234-0.1, #4.234-1, #4.235-0.1, #4.235-0.2, #4.235-1.1, #4.235-2, #4.472-1.1, #4.472-1.2, #4.472-2.1, #4.473-0.1, #4.473-1, #4.474-0.0, #4.474-0.1 and #4.480-1.

Checked without change:
- #4.466 at β = 1/8: 21/8 ≤ 45/16, ¾ < 7/8, and 7/4 ≥ 11/8.
- #4.467 at β_I ≤ ¼ and L = 2: 11/16 and ¾.
- #4.480: q₁ ≥ q₀ is forced, because α₀/α₁ = (C₀/C₁)(log g^{−2})^{q₀−q₁} has to stay below 1/(2B₃²O(1)M).
- #4.497: every one of the ten values μ is at most an entry of λ_Q, using B₃ ≥ 1 for μ_mem ≤ 2 ≤ 4B₃.
- #4.249–#4.255: the fluctuation fields are the same variables in both runs.

No duplicate tag occurs in the file after these edits.

## Packet 34 (LF #4.219, #4.256–#4.286.2)

Read in full (15:33).

| Finding | Change | Lines |
|---|---|---|
| #4.284.1 re-derived #4.280's envelope identity and defined Δ(W) a second time (#D.Δ(W).2) | it cites #4.280: J^B(ι_XW) = Q₁^{pl}(ι_XW)*(J(W) + ∇_WΔ(W)), so δJ = −Q₁^{pl}(ι_XW)*∇_WΔ(W); #D.Δ(W).2 removed | #4.284.1 |
| #4.284.1's bound abs(K) ≤ O(1)(ε/a_j)C₀^{ms}ε₁a_j^{−2} at the chain's real minimisers is used nowhere in (δ): at W, which is not a minimiser, #4.281-1 and #4.286.1 bound K through the oscillation | the line states the divergence form (W-δ #W11.86) and points to #4.281–#4.281-1 | #4.284.1-1 |
| α₂ was defined twice: := c₂α_{0,j} (#4.275.3) and := c₂min(α₀, α₁) (#4.485, #D.α₂.2); the two agree only through α₁ ≥ α₀, which was not stated | #4.485 cites #4.275.3 and gives the reason, C₁ = λ_RC₀ with λ_R = K_RLM + 1 ≥ 1 and q₁ = q₀ (#4.480, W-δ #W12.183-2); #D.α₂.2 removed | #4.485 |
| C_□′ := max(C_H⁰, C_□) was defined in #4.284.17 and again in #4.284.18 (#D.C_□′.2), which also called *The weighted rerun.* "below", though it is above | #4.284.18 cites #4.284.17; #D.C_□′.2 removed | #4.284.18 |
| #4.284.15's C_{Δ2} was defined nowhere, and "the bound of §11's multiplier" pointed to no item: the walk note's §11 has no multiplier, and its *The term G̃Δ^{(2)}H₀B.* bounds H*∇b₁ only at real points (#W11.86-13) | derived in place: H* applied to −∇b₁ = ℒ*J^B − J^A at the base ι_Yc^A is a first-kind pairing of *Where the current enters.*. Real bound O(1)B₀C_δ′(ε/a)^{β_o}a^{−3}; disc bound O(1)C_ℒ^gLř_j(a/ε)a^{−3}; the two-constants theorem gives O(1)B₀(C_ℒ^g)^{1/3}C_J‴(ε/a)^{(2β_o−1)/3}a^{−3}. With C_J‴ ≤ K_J (#4.290) and (2β_o − 1)/3 ≥ 1/6 > γ_H − 2β′, this is ≤ ϑ_H/C_Hw, so {#D.C_Δ2} C_{Δ2} := O(1)(C_ℒ^g)^{1/3}K_J/C_Hw | #4.284.15-1, #4.284.15-2 |
| #4.284.7 and #4.284.16 cited "§11's composition" bare, and #4.284.15 and #4.433 cited a bare "§11", all meaning the walk note's §11 (*The composition of the averagings.*) | named explicitly, so the convention of #P.2 holds without exception | #4.284.7, #4.284.15, #4.284.16, #4.433 |
| #4.234 repeated #4.275.2's description of 𝐇_j's entries (VAR Proposition 9 and (190)) | it cites #4.275.2 | #4.234 |

Lines over ~1300 characters were split at sentence boundaries. Three lines of 1100–1200 characters (#4.278, #4.281-1 and #4.284.19) are each a single sentence and were left whole. New sub-tags: #4.262-1, #4.275.1-1, #4.275.1-2, #4.275.2-1, #4.275.2-2, #4.275.3-1, #4.275.3-2, #4.275.4-1, #4.275.4-1.1, #4.275.4-2, #4.275.5-1, #4.275.5-2, #4.276-0.1, #4.276-1.1, #4.278-1, #4.281-0.1, #4.281-2, #4.282-1, #4.284.1-1, #4.284.1-2, #4.284.2-1, #4.284.3-1, #4.284.3-2, #4.284.4-1, #4.284.5-1, #4.284.6-1, #4.284.7-1, #4.284.7-2, #4.284.8-1, #4.284.8-2, #4.284.10-1, #4.284.14-1, #4.284.14-2, #4.284.15-0.1, #4.284.15-0.2, #4.284.15-1–#4.284.15-3, #4.284.16-1, #4.284.17-1, #4.284.17-2, #4.284.18-1, #4.284.19-1, #4.284.19-2, #4.286.1-1, #4.286.2-0.1, #4.286.2-1.1 and #4.286.2-2.1.

Checked without change:
- #4.275.4's ŝ_j: S_j ≤ C_fac(N₀ + 1)^{1/2}(1 + β₀)2^{p₀}g_jA₀(log g_j^{−2})^{p₀}, against r_{0,j} ≥ C₀g_j(log g_j^{−2})^{q₀}/(8B₃).
- #4.278: r_{0,m}a_m^{−3} ≤ r_{0,j}L^{m−j}L^{−3(m−j)}a_j^{−3} ≤ r_{0,j}a_j^{−3}.
- #4.284.6: γ_H < 2β_o/3, by the two comparisons β/2 < 2β/3 and (1 − ε₀)/6 < 2(1 − 2ε₀)/3 for ε₀ < 3/7.
- #4.286.2-1: (2(β_o − β″) − 1)/3 ≥ 2/15 at β_o ≥ 3/4 and β″ ≤ 1/20.

## Packet 35 (LF #4.285–#4.312)

Read in full (15:57). From this packet on, dead-route mentions, review-status remarks ("derived, not reviewed", "with the status given there"), roadmaps and hedges are deleted as the text is read; OPEN markers stay.

| Finding | Change | Lines |
|---|---|---|
| #4.286.1 restated the three kinds of *Where Bałaban puts 𝐉.* without its pins | the three kinds are cited with their PBG pins: (3.136) p.422 l.47–51; (3.117) p.419 l.5–7 with l.11–12; (3.119)–(3.120) p.419 l.24–36 | #4.286.1 |
| #4.292 and #4.286.2-2.1 bounded α_{0,m} by α_{0,j} without the argument | both cite #4.290, where g ↦ g(log g^{−2})^{q₀} is increasing and g_m ≤ (1 + β₀)g_j | #4.292, #4.286.2-2.1 |
| #4.298 listed three routes that fail; #4.299 and #4.300 had no citers | #4.298 removed with them | #4.298, #4.299, #4.300 |
| #4.285 described two estimates that fail | removed; the line states the divergence form it uses | #4.285 |
| #4.293.5 closed with what is not used | removed | #4.293.5 |
| #4.302 discussed the patch of U_1 and U_2 as an alternative entry, and announced "four steps, and its current in a fifth" | both removed | #4.302 |
| #4.307 stated that a pointwise bound fails on the band | the line states why the divergence form is taken: U_{1,2} is critical only on each side of the cut and J_S has no factor ε/a_h | #4.307 |
| #4.313 announced the order of its two lifts | removed | #4.313 |
| #4.286.2-2 opened with what is not needed | removed | #4.286.2-2 |
| #4.301-1 bounded J_S without the factor L³B₃ that #4.305 has | L³B₃ added, and P includes it | #4.301-1, #4.301-1.2 |
| #4.305 wrote the response with the kernel's full rate δ₀ and abs(J_S) unsummed over the edge S | sup J_S, rate ½δ₀, C including the sum over the (d − 1)-dimensional S, as in #4.301-1.2 | #4.305 |
| C_r had three meanings: the Cauchy note's (9.5) constant (#4.304, #4.8), #4.301-2's response constant, and #4.620's local constant | #4.301-2's renamed {#D.C_resp} C_resp, #4.620's {#D.C_rF} C_{rF}; C_r keeps the Cauchy note's meaning | #4.301-2, #4.620 |
| μ_mem was defined four times | one definition at #4.473-0.1, cited by #4.528, #4.532, #4.540.3 | #4.528, #4.532, #4.540.3 |
| status remarks in #4.287, #4.295, #4.297, #4.301, #4.301-1, #4.302, #4.307, #4.313 | removed | as listed |

Lines over ~700 characters were split at sentence boundaries; #4.289.2-2–#4.289.2-3 rephrase the list "PBG's …; VAR's …; RG I's and CRE's …" as sentences. New sub-tags: #4.286.1-0.1, #4.286.2-0.0, #4.286.2-1.0, #4.286.2-2.2, #4.286.2-4, #4.288-0.1, #4.288-0.2, #4.288-1.1, #4.288-1.2, #4.288-2.1, #4.288-2.2, #4.288-3.1, #4.288-3.2, #4.289.1-1, #4.289.1-2, #4.289.2-1–#4.289.2-3, #4.289.3-1, #4.289.3-1.1, #4.289.3-2, #4.289.4-1, #4.289.5-1, #4.289.5-2, #4.290-0.1, #4.290-1.1, #4.290-3, #4.291-1, #4.291-2, #4.292-0.1, #4.292-2, #4.293.1-1, #4.293.3-1, #4.293.3-2, #4.293.4-1–#4.293.4-3, #4.294-1, #4.301-0.1, #4.301-0.2, #4.301-1.1, #4.301-1.2, #4.301-2.1, #4.301-2.2, #4.302-1, #4.303-1, #4.304-1, #4.304-2, #4.312-0.1 and #4.312-1. New definitions: #D.C_resp, #D.C_rF. Removed: #4.298, #4.299, #4.300, #D.C_r (LF), #D.μ_mem.2, #D.μ_mem.3, #D.μ_mem.4.

Checked without change:
- #4.305: a_h|resp| ≤ CL³B₃ε₁(ε/a_h)² and a_h²|∇resp| ≤ CL³B₃ε₁(ε/a_h) from ε|resp| + ε²|∇resp| ≤ Cε³L³B₃ε₁a_h^{−3}.
- #4.306: (ε/a_h)^{1−ε₀} ≤ (ε/a_h)^{(1−ε₀)/3} ≤ (ε/a_n)^{(1−ε₀)/3}, since ε/a_h ≤ 1 and a_n ≤ a_h.
- #4.312: abs(t)σ_{1,2} ≤ (c_ρα_h/d̄)C(ε/a_h)^{1−ε₀}ε₁ ≤ (C/C_U(M))c_ρα_h(ε/a_h)^{2(1−ε₀)/3}, with d̄ ≥ C_U(M)(ε/a_h)^{(1−ε₀)/3}ε₁; 2(1 − ε₀)/3 > ½ ≥ β″.

Follow-up for the table fork: #4.620's C_{rF} was a name without a formula, so labels_rebuild.py stopped. It is now C_{rF} := (4C_mv/β)C_c′2^{j(C)}sup_{k_s≥0}max_{k≤k_s+j(C)}P(k)2^{−k_s}. It cites #4.619 and the Cauchy note's #CP.14 (log g_k^{−2} ≤ 2log(ḡ^{−2} + b(K − k))). #4.621's remaining C_r is now C_{rF}.

## Packet 36 (LF #4.367–#4.415)

Read in full (16:04).

| Finding | Change | Lines |
|---|---|---|
| #4.369 announced "two inputs", #4.370 listed its inputs, and #4.402 named "the other input" | the announcements are removed; #4.402 is removed (no citers) | #4.369, #4.370, #4.402 |
| #4.382 described a Cauchy estimate in one direction that fails, and the axial gauge that (190) does not cover | both removed; the line keeps the reason for taking each variable in turn | #4.382 |
| #4.390 opened with a Hölder bound of 𝐒_c that fails | replaced by what is used: f is bounded on the disc and r(Y) supplies the smallness, so the Hölder norm enters only where RG I uses it (#4.391) | #4.390 |
| #4.406 said what VAR (9)–(10) would not give | removed | #4.406 |
| #4.375 closed a step with "So no non-minimiser defect arises" | removed | #4.375 |
| #4.376 gave "the status of (α)" | it is bounded as (α) | #4.376 |
| #4.401's heading made the result conditional on the localisation that #4.379–#4.386 prove | heading "The result." | #4.401 |
| #4.394.3 left Δ(X) with a status remark, but #4.394.4 bounds it | cites #4.394.4 | #4.394.3 |
| #4.394.4 pointed to "one corner of an 𝐑-operation below" | cites #4.394.6 | #4.394.4 |
| status remarks in #4.367, #4.368, #4.369, #4.370, #4.375, #4.379, #4.383, #4.387, #4.388, #4.391, #4.394.1, #4.394.4, #4.394.5, #4.394.6, #4.394.7-1, #4.395, #4.400, #4.403, #4.406, #4.409, #4.411 | removed | as listed |

Lines over ~760 characters were split at sentence boundaries. New sub-tags: #4.373-1, #4.375-0.1, #4.375-1, #4.382-1, #4.382-2, #4.385-1, #4.385-2, #4.386-1, #4.388-0.1, #4.388-1, #4.391-1, #4.393-1, #4.394.1-0.1, #4.394.1-1, #4.394.2-1–#4.394.2-3, #4.394.3-0.1, #4.394.3-1, #4.394.4-0.1, #4.394.4-0.2, #4.394.4-1, #4.394.5-0.1, #4.394.5-1, #4.394.6-1–#4.394.6-3, #4.394.7-0.1, #4.394.7-2, #4.394.8-1, #4.394.8-2, #4.395-1, #4.397-0.0, #4.397-0.1, #4.397-1.1, #4.397-2.1, #4.398-0.1, #4.398-0.2, #4.398-1.1, #4.399-1, #4.399-2, #4.400-0.1, #4.400-1.1, #4.400-1.2, #4.401-1, #4.401-2, #4.406-1, #4.407-1, #4.407-2, #4.410-1, #4.410-2 and #4.413-1. Removed: #4.402.

Checked without change:
- #4.382: the geometric mean (K/ρ)e^{−(δ₀/16)(d(x,y′)+d(x,y″))}, summed over y″ and over y′ ∈ R at half the rate, gives C(d̄/ρ)sup abs(Δd)e^{−(δ₀/32)d(x,R)}.
- #4.394.4: R_j ≥ 2(log ḡ^{−2})^r ≥ L ≥ 3 gives the margin MR_ja_j ≥ 3Ma_j at m = j.
- #4.400-1: (1 − 2β)L ≥ 1 + 3β at L ≥ 2 is 1 ≥ 7β, so it holds at β = 1/8.
- #4.401: g_j ≤ (1 + β₀)g_m gives log g_m^{−2} ≤ 2log g_j^{−2} for g small. So α̃_{0,m} ≤ 2^{q₀}(1 + β₀)(m − j + 1)^{1/2}α̃_{0,j}, three ratios give 8^{q₀}(1 + β₀)³(m − j + 1)^{3/2}, and Σ_{j≤m}(m − j + 1)^{3/2} ≤ (m + 1)^{5/2} ≤ C k^{5/2}.
- #4.413: 8R_k > 6d and 6MR_k ≥ 6dM for R_k ≥ L > d.

## Packets 37 and 38 (LF #4.74, #4.313–#4.366; the rest of their lists is in packets 33–36)

Read in full (16:09). The other tags on rows 37 and 38 (#4.212, #4.228, #4.230, #4.234–#4.244, #4.290, #4.301, #4.306, #4.312, #4.401, #4.410) were read in packets 33–36.

| Finding | Change | Lines |
|---|---|---|
| #4.363 put the background entry's current J_{1,2} into the pointwise minimum T_J(Y) "near the cut". #4.307 shows that on the band there is no pointwise bound Ĉ_Jd̄, and the move is handled in divergence form | J_{1,2} enters T_J(Y) off the band only; on the band, *The disc.* keeps it in 𝒟_R (#4.311–#4.312) | #4.363 |
| #4.74 closed with "the factor c_wL^{1/3}", but c_w is #4.122's current constant; the walk constant of the line is c_ω | c_ω, citing #4.91 for the display of c_al | #4.74 |
| #4.323-3 explained why a bound through ε₁ would fail | removed | #4.323-3 |
| #4.328-1 closed with "so no relation between k and j is needed" | removed | #4.328-1 |
| status remarks and "accepted" in #4.74, #4.323, #4.323-1, #4.324, #4.328-2, #4.329, #4.335, #4.363, #4.365 | removed; #4.323 cites #4.323-2 for the class bound of the tail | as listed |

New sub-tags: #4.74-1, #4.314-1, #4.315-1, #4.316-1, #4.320-1, #4.320-2, #4.321-1, #4.323-0.1, #4.323-1.1, #4.323-1.2, #4.323-2.1, #4.323-2.2, #4.324-1, #4.324-2, #4.328-0.1, #4.328-1.1, #4.328-1.2, #4.329-1, #4.331-1, #4.333-1, #4.343-1–#4.343-3, #4.349-1, #4.349-2, #4.363-1–#4.363-3, #4.364-1 and #4.365-1.

Checked without change:
- #4.323-2: a_j²abs(F) ≤ 2(1 + β₀)²L^{3j}r_{0,j}. For ℓ′ ≥ j, L^{−2(ℓ′−j)}(ℓ′ − j + 1)^{1/2} ≤ 1; for ℓ′ < j, L^{2(j−ℓ′)}(j − ℓ′)^{β₀} ≤ L^{3j}. Also x³e^{−cx} ≤ (3/(ec))³ at c = ½δ₀M₁, τ(M₁) ≤ 1/32 is equivalent to M₁ ≥ M₁^τ, and ½τr_{0,j}/(2B₃) = 4(C_ι/C_F)(1 + β₀)²(6/(eδ₀M₁))³r_{0,j}.
- #4.331: dist/ε ≥ M₁L^k − (R_ι/L + 2)M₁ for M₁ ≥ 2, and x²e^{−cx} ≤ (2/(ec))² at x = L^k, c = ½δ₀M₁.

## Sweep of packets 33–34 (LF #4.209–#4.284) under the new rule

| Finding | Change | Lines |
|---|---|---|
| status remarks in #4.218-1, #4.226-1, #4.227 (heading), #4.229, #4.229-2, #4.230, #4.230-1, #4.233-0.2, #4.255, #4.258, #4.261, #4.273, #4.274, #4.284.8-2 | removed. #4.229 cites *The lift of U_1.* and #4.216-1.1; #4.255 cites §4(e); #4.284.8-2 cites #4.284.17 | as listed |
| #4.240-1 said that the power 15/16 "would not be affordable"; #4.267 said "the other order fails" | removed | #4.240-1, #4.267 |
| #4.258 said "the link-image rule does not force this choice" | the line states that both choices agree at run B's chain | #4.258 |

## Packet 39 (LF #4.416–#4.432, #4.434–#4.434.10, #4.243, #4.275.3, #4.278, #4.282, #4.284.3, #4.284.14), with #4.433 of packet 40

Read in full (16:17). The status remarks left in #4.224–#4.284.7 were removed in the same pass.

| Finding | Change | Lines |
|---|---|---|
| #4.421 joined two sentences with a comma ("BCMα_{0,j}, For U_{k,Λ}") | full stop; the second sentence is #4.421-1 | #4.421 |
| #4.434.3 explained that the Landau-gauge condition is not used; #4.427 said that the alignment of (b) does not apply; #4.279 described the one-step bound through VAR (10) that loses (a_j/ε)²; #4.275.5-2 said that R₁ is not matched against the kernel part; #4.238 described the differences at two arguments, which no bound uses | removed; #4.427 states the walk form of the decoupled propagators, #4.279 states that the own current is bounded through the constraint | #4.434.3, #4.427, #4.279, #4.275.5-2, #4.238 |
| hedges: #4.417-1 ("no gain in L^{−(k−m)}"), #4.420-1 ("which q₀ > p₀ alone does not pay", "a search of the transcriptions"), #4.431 ("which no factor bound supplies"), #4.432 ("PBG gives no bound per factor"), #4.433 (analyticity in the operators; no Hölder bound of Δ_𝐇), #4.434.6 (no second differences), #4.434.6-2 (no transport), #4.434.8 ("no further threshold"), #4.434.10 ("is not bounded along the segment"), #4.240-1 (the Lemma (Two Constants)), #4.284.14 ("cannot have the rate") | removed or stated positively | as listed |
| status remarks in #4.224, #4.226, #4.230-3, #4.233, #4.234, #4.236, #4.246, #4.248, #4.256, #4.275.5-2, #4.276, #4.277, #4.278, #4.279, #4.284.1, #4.284.1-2, #4.284.7, #4.417, #4.420-1, #4.421-1, #4.427, #4.431, #4.433, #4.434.6, #4.434.8, #4.437; #4.278's "derived, not printed" | removed; #4.278's parenthesis states why the product form holds | as listed |
| #4.278 listed the Laplace-type entries as a "plus" after the bound of 𝐅 | they are the third part D_U*D_U𝐀^A of the RG I (3.11) current, #4.278-0.1; ř_j of #4.278-1 is unchanged | #4.278 |

New sub-tags: #4.243-1, #4.278-0.1, #4.282-0.1, #4.416-1, #4.417-0.1–#4.417-0.3, #4.417-2, #4.420-0.1, #4.420-0.2, #4.420-1.1, #4.420-2, #4.421-0.1, #4.421-0.2, #4.421-1, #4.423-1, #4.423-2, #4.431-1, #4.432-0.1, #4.432-1.1, #4.432-1.2, #4.433-0.1, #4.433-1.1, #4.433-1.2, #4.434.1-1, #4.434.3-0.0, #4.434.3-0.1, #4.434.3-2, #4.434.4-1–#4.434.4-3, #4.434.5-1, #4.434.5-2, #4.434.5-2.1, #4.434.5-3, #4.434.5-4, #4.434.6-1, #4.434.6-2, #4.434.7-1–#4.434.7-3, #4.434.8-1, #4.434.9-1, #4.434.9-2, #4.434.10-0.1 and #4.434.10-1. #4.434.6 now heads *The divergence part.*

Checked without change:
- #4.419: k − m + 1 = N₀ + (k₀ + 1 − m), so (k − m + 1)^{1/2} ≤ (N₀ + 1)^{1/2}(1 + (k₀ + 1 − m)^{1/2}), and e^{−δ_Vt}(1 + t^{1/2}) ≤ c_V.
- #4.420: U_1 at 2(2c_U + C_W(N₀ + 1)^{1/2}) + C_W(N₀ + 1)^{1/2}; the prefactors are ≥ 1 − β(3 + 1) ≥ ½ for β ≤ 1/8.
- #4.420-1: j − m ≤ k − k₀ − 1 = N₀ − 1, so (L/L₀)^{2(j−m)} ≤ L^{2(N₀−1)}.
- #4.432: (abs(ω) + 1)e^{N_cmax_cδ_c(abs(ω)+1)} ≤ 2(4/3)^{abs(ω)}(3/2)^{abs(ω)+1} = 3·2^{abs(ω)}, and n + 1 ≤ 2(4/3)^n for n ≥ 0. In #4.432-1, N_cmax_cδ_c > 2/5 gives c_Q + c_s ≤ (5/2)(c_Q + c_s)N_cmax_cδ_c ≤ C_telN_cmax_cδ_c.

## Packet 40 (LF #4.73, #4.224, #4.233, #4.275.2, #4.275.4, #4.284.5, #4.284.7, #4.284.18; #4.311 and #4.363 in packets 35 and 37–38, #4.433–#4.434.9 in packet 39)

Read in full (16:20), with #4.227–#4.232 and #4.284.4–#4.284.19 around them.

| Finding | Change | Lines |
|---|---|---|
| #4.284.13 (*Without the factor ϑ_H.*) described the geometric-mean bound and why it gives the wrong rate | removed; no line cites it; plan row 34's range ends at #4.284.12 | #4.284.13 |
| #4.233-1 explained that d_j is not used; #4.233-2.1 said "not through (3.48)" and listed the two items that do not cover W | removed; #4.233-1 closes with W ∈ 𝒫_j(X; r) alone, #4.233-2.1 points to *The lift half at W.* | #4.233-1, #4.233-2.1 |
| #4.227-1 ("Neither is needed"), #4.229-1 ((5.1c) not evaluated at the patch), #4.229-2 ("not removed from (ii)"), #4.284.10-1 (§11's sup-norm bounds), #4.284.17-1 ("no constant is defined through itself", "Neither second differences … enter"), #4.284.18 ("no entry … beyond") | removed or stated positively; #4.227-1 cites #4.228, #4.284.11 points to #4.284.14 | as listed |

New sub-tags: #4.73-1, #4.275.2-0.1, #4.275.2-3, #4.275.4-0.1, #4.275.4-1.2, #4.284.5-2, #4.284.7-0.1 and #4.284.18-2. Removed: #4.284.13.

Checked without change:
- #4.284.6: β/(1 + β) < ½ for β < 1; β/2 < 2β/3; (1 − ε₀)/6 < 2(1 − 2ε₀)/3 is 7ε₀ < 3.
- #4.284.18-2: with C_segϑ̂_H ≤ 1/6 the v-disc has radius ρ ≥ 2, the τ-derivative at 0 is at most twice the bound over r̄, and the v-difference over distance 1 costs 1/(ρ − 1) ≤ 2/ρ = 6C_segϑ̂_H, so 12C_segϑ̂_H.
- #4.284.19: Cauchy in σ on radius r̄_w/(3C_{αs}C_segϑ̂_H) with F at most twice the bound gives 6C_{αs}C_segϑ̂_H/r̄_w, and 1/r̄_w = 3N′α₂^{−1}e^{−E_w}.

## Packet 41 (LF #4.216, #4.434.10–#4.449)

Read in full (16:28). #4.434.10 was done in packet 39. The fork's request about #4.323-2.1 is done: it now cites #T1.3 and #T1.5 instead of "rows 12 and 14".

| Finding | Change | Lines |
|---|---|---|
| #4.446.2 explained why the own quantities are not bounded through the class (8) or RG I (3.27); #4.439-3 described the resolvent identity that "doesn't work"; #4.216-2 listed obstacles that "do not arise" | removed | #4.446.2, #4.439-3, #4.216-2 |
| #4.446.5 had a fragment ("so for n ≥ n₀′.") | joined to the preceding clause | #4.446.5 |
| status remarks and "accepted" in #4.216, #4.216-1.1, #4.438, #4.438-2, #4.439, #4.439-3, #4.440 (heading), #4.443, #4.443-0.1, #4.443-1, #4.444, #4.446.2-1, #4.446.3, #4.446.4, #4.447.1, #4.447.1-1, #4.447.4, #4.447.5, #4.448, #4.449 | removed; #4.443 lists the inputs of (5.1v) it uses; #4.439-3 keeps the pointer to Open Gaps (7) | as listed |
| hedges and roadmaps: #4.436 ("treated at the end of this bullet"), #4.437 (n ≤ 1), #4.439-1 ("not its background part"), #4.442 ("no standalone r_z arises", "no age bound at its second value"), #4.447.5 ("needs no transfer"), #4.449-2 ("the next bullet") | removed or stated positively; #4.449-2 cites #4.450 | as listed |

New sub-tags: #4.435-0.1–#4.435-0.3, #4.435-1.1–#4.435-1.3, #4.436-1–#4.436-3, #4.437-0.1, #4.437-1–#4.437-3, #4.438-0.1, #4.438-0.2, #4.438-1.1, #4.438-1.2, #4.438-3.1, #4.438-3.2, #4.438-4.1, #4.438-4.2, #4.439-0.1, #4.439-0.2, #4.439-1.1, #4.439-2.1–#4.439-2.3, #4.441-1, #4.442-0.1, #4.442-0.2, #4.442-1, #4.443-0.1, #4.443-0.2, #4.443-2, #4.444-0.1–#4.444-0.3, #4.444-1, #4.445.1-1, #4.445.1-2, #4.445.2-1–#4.445.2-3, #4.445.3-1–#4.445.3-3, #4.445.4-1, #4.445.5-1–#4.445.5-3, #4.445.6-1, #4.445.6-2, #4.446.1-0.1, #4.446.1-1, #4.446.1-2, #4.446.2-1, #4.446.2-2, #4.446.3-1, #4.446.3-1.1, #4.446.3-2, #4.446.4-1, #4.446.4-2, #4.446.5-0.1, #4.446.5-2, #4.447.1-0.1, #4.447.1-1.1, #4.447.2-1, #4.447.3-1, #4.447.3-2, #4.447.4-1, #4.447.4-2, #4.447.5-1, #4.447.5-2, #4.448-1, #4.448-2, #4.449-0.1, #4.449-0.2, #4.449-1.1 and #4.449-1.2. C_𝔡 is defined at #4.437-1; N′ stays at #4.435-1.

Checked without change:
- #4.436: Schwarz's lemma for f − f(1) on the disc of radius R about 1 gives abs(f(0) − f(1)) ≤ 2r·sup abs(f − c), so 12C_{Δ𝐇}ϑ̂_H with sup abs(f) at most twice the bound; with R₂ = 1/(2C_{Δ𝐇}ϑ_H) ≥ 3, 2·2 sup abs(f)/R₂ = 4C_{Δ𝐇}ϑ_H sup abs(f).
- #4.437: L^{β′k} ≤ L^{2β′}L^{2β′j_min} from k ≤ 2j_min + 2, and 1 − 2β′ ≥ γ_H − 4β′.
- #4.439-1: θ_V/8 ≤ (1/2)/(16·4.5) = 1/144 and (γ_H − 4β′)/2 ≥ (1/12 − 1/15)/2 = 1/120.
- #4.439-2.1: 12 + 6(2 + C_F′k^{5/2}) + 4 = 28 + 6C_F′k^{5/2}.
- #4.445.3-2: L^{3j}L^{−8(j−3)^+} ≤ L^{24}L^{−j}, since 4j ≤ 24 + 8(j − 3)^+.
- #4.446.4 and #4.446.5: (1 − ε₀)/3 − 16ε₀ = (1 − 49ε₀)/3 and (15/16)(1 − ε₀)/3 − 15ε₀ = 5(1 − 49ε₀)/16.

## Packet 42 (LF #4.387, #4.388, #4.517, #4.533–#4.546)

Read in full (17:08). The open item of #4.536-2 (CMP98 (106) at a complex base) is repaired by balaban_proofs/BP_COMPLEX_BASE_GAUGE.md (#4.536.1–#4.536.10).

| Finding | Change | Lines |
|---|---|---|
| #4.536-2 bounded u_{k,Λ}, u_1, u″_k by run B's real-base count, while the bases 𝐔, U_{k,Λ}, U^0_k are complex | CMP98 (106) at e^{iηA′}U reduced to two gauges at U (BP file, #4.536.5); abs(log u) ≤ 72d(ε_A + ε_X) (#4.536.10); u_1 through the covariance #4.536.4, at the base W_{X} := e^{iη𝐇_k(X)}𝐔 (renamed from W₁, which is #T4.31's loop) | #4.536-2, #4.536-2-0, #4.536-2-0.1; table #T11.14 to be updated |
| #4.535's C_Y clashed with the LF's own #D.C_Y (#5.22, #T4.36) and cited a section, not a bound; its C_Λ clashed with #T4.30's | the W-δ quantities get δ-marked LF symbols, since the LF's C_s (#4.445.2-3), w and w_y are other objects: C_Λ^δ, w^δ, X^δ_s, C_I^δ, C_s^δ, each defined by its W-δ tag; abs(Y) ≤ C_{Z″}(α̃_{0,k} + α̃_{1,k}), C_{Z″} := 4C_s^δ, derived from #W12.153-13, #W12.176-3, #W12.175 and C_I^δ ≤ C_s^δ (#W12.176-4); δ^c and (D-Λ) carry C_Λ^δ and C_{Z″} | #4.535, #4.535-0.1, #4.535-1, #4.536, #4.538, #4.539 |
| #4.539 restated C_Λ and λ_R; #4.537 restated δ_H | cited #W12.172, #T12.6-20, #T2.24, #T12.9 | #4.537-0.3, #4.539 |
| #4.384 restated the data-angle bounds of #4.535 | cites #4.535 | #4.384 |
| #4.388 restated the bound of #4.386–#4.386-1 and #4.387's smallness; #4.388-1 restated #4.387-1 | cited | #4.388, #4.388-1 |
| the orbit-representative reason was given for U″_k alone in #4.540.4; #4.540.3 restated #4.536's representative of U″_k | stated once for all three members in #4.536-0.2; #4.540.4 cites #4.536-1.2 and #4.536-0.2 | #4.536-0.2, #4.540.3-3, #4.540.4, #4.540.4-1 |
| #4.543 gave the general-U₀ form of VAR (111) without the current | A₁ = −𝔊(J + (δV/δA′)(A₁ + H₁B)) | #4.543 |
| the current's two entries (Δ₁ and V) and the regularity of the base at (𝐔, 𝐉) were argued in #4.534, #4.543, and #4.546 | stated once in #4.534-1–#4.534-3 and cited | #4.534-1–#4.534-3, #4.543-1, #4.546 |
| c_D's content was restated at #4.540.1, #4.540.3, #4.545 | cite (D-Λ) only | as listed |
| #4.541-1 ended with a roadmap to #4.542; status remarks and hedges in #4.517 and #4.533–#4.542 | removed | as listed |
| lines over 600 characters | split at sentence boundaries | below |

New sub-tags: #4.387-1, #4.533-1, #4.534-1–#4.534-3, #4.535-0.1, #4.535-1, #4.536-0.1–#4.536-0.3, #4.536-1.1, #4.536-1.2, #4.536-2-0, #4.536-2-0.1, #4.537-0.1–#4.537-0.3, #4.537-1.1, #4.537-1.2, #4.540.1-1–#4.540.1-3, #4.540.2-1, #4.540.2-2, #4.540.3-1–#4.540.3-3, #4.540.4-1, #4.540.4-2, #4.541-0.1, #4.541-0.2, #4.541-1.1, #4.543-1, #4.544-1, #4.545-1–#4.545-3 and #4.546-1–#4.546-3. 𝐇′ is defined at #4.536-1.2, u, u.2 and u.3 at #4.536-0.2; δ^c stays at #4.536 and now reads max(C_Λ, C_{Z″})(r_{0,k} + r_{1,k}); C_{Z″} is defined at #4.535-0.1.

Checked without change:
- (D-Λ): 4608 = 9·512, and 4608·(8/3) = 12288 = 12·1024, which puts the lift entries' 12C_δ(ε₀)L^{7/3} below 2^{−10}.
- #4.540.1: (1 + 2^{−9})² + 2^{−9} + (1 + 2^{−9})²2^{−9} ≤ 1 + 5·2^{−9} ≤ 1 + 2^{−6}.
- #4.535-0.1: 2C_I^δ + C_s^δ ≤ 3C_s^δ, and the Baker–Campbell–Hausdorff factor is ≤ 4/3 for γ small.
- BP file: the recursion constant 4C₁ and the bootstrap ρ ≤ C₂d²ε² ≤ dε on s ≤ 65dε (#4.536.9-3, #4.536.9-4); (33/32)(32dε_A + dε + 32dε_W) = (33/32)·33dε ≤ 35dε with ε = ε_A + ε_W ≤ (2ε_A + ε_X)(1 + O(ε_A + ε_X)), so ≤ 72d(ε_A + ε_X) (#4.536.6-2, #4.536.10).
- VAR (79)–(80), (111)–(112), (170)–(175), (190), p.308 l.49 – p.309 l.4; PBG (3.35)–(3.38), (3.134)–(3.136), p.422 l.47–51; LFR II p.371–375; RG I p.261 l.35–42: re-read against the lines citing them.

## Packet 43 (LF #4.450–#4.452, #4.454.1, #4.454.2, #4.454.4–#4.454.6, #4.454.8–#4.454.11, #4.454.15–#4.454.17, #4.454.22)

Read in full (17:23). #4.438 is done in packet 41.

| Finding | Change | Lines |
|---|---|---|
| the w of At D(s) was used at #4.454.22 before its definition at #4.454.35, untagged, and it clashed with the LF's #D.w (#4.41, w := ζ₁/(g″)²) | renamed w_□, {#D.w_□} at #4.454.35; #4.454.22-1 cites it | #4.454.22-1, #4.454.35, #4.454.36 |
| C_* was defined without a tag | {#D.C_*} added (row #T4.29) | #4.454.10-1 |
| #4.454.15 restated #4.536-1.2 (W^u in 𝒮⁺_z with g = ū·u^{−1}) | cites #4.536-1.2 | #4.454.15-1 |
| #4.454.2 redefined h of #4.450 and restated β_H ≥ 19/20; #4.454.1 restated β_E | cite #4.450, #T3.6, #T3.7 | #4.454.1, #4.454.2-2 |
| #4.454.11 "not shown at r (below)" and "This is admissible." | cites #4.540.3-2 and #4.540.4-1; filler removed | #4.454.11, #4.454.11-1 |
| #4.454.9 restated c̃'s definition of #4.454.8-4 | removed | #4.454.9-2 |
| #4.454.6 "This is not circular." (the order is #4.454.7's) | removed | #4.454.6-3 |
| #4.450's "not shown" hedges and its roadmap "The bound has four parts." | stated positively: the comparison of #4.454.2 does not use 𝒮_z at c^A | #4.450-1 |
| status remarks in #4.450, #4.454.1, #4.454.2, #4.454.16 | removed | as listed |
| lines over 600 characters | split at sentence boundaries | below |

New sub-tags: #4.450-0.1, #4.450-1, #4.451-1, #4.451-2, #4.452-0.1, #4.452-1, #4.452-2, #4.454.1-1, #4.454.1-2, #4.454.2-1, #4.454.2-2, #4.454.4-1–#4.454.4-3, #4.454.5-1–#4.454.5-3, #4.454.6-1–#4.454.6-3, #4.454.8-1–#4.454.8-4, #4.454.9-1–#4.454.9-3, #4.454.10-1–#4.454.10-3, #4.454.11-1–#4.454.11-3, #4.454.15-1, #4.454.15-2, #4.454.16-1–#4.454.16-4, #4.454.17-1–#4.454.17-3 and #4.454.22-1–#4.454.22-4.

Checked without change:
- #4.454.9-3: 2d^{1/2}R_* + 1 + 4d^{1/2} ≤ 7d^{1/2}R_* for R_* ≥ 1, and 7·4 = 28.
- #4.454.10: 2C_𝔟(Υ_z + 28d^{1/2}R_*C_LipΔ_z) with Δ_z ≤ (1 + B₀C_𝔟)Υ_z, times B₀C_Lip, is C_*Υ_z.
- #4.454.15-2: (65/64)(8/9) + (1 + 2^{−9})/36 < 0.931 ≤ 15/16, the move 𝔱_m/32 being 1/36 of an r⁺-threshold.
- #4.454.16: (9/8)·0.35 + 2^{−8} + 2^{−5}(1 + 2^{−9}) < 0.43 < 9/8; 16 + 10/8 ≤ 18.
- #4.454.17-2: 2^{13}B₃²L³/(8B₃) = 2^{10}B₃L³ ≥ 8192; 18/8192 ≤ 18/256, and 2(1 + ⅛)/8 = 9/32.
- #4.454.22-4: R_kε_m/α_{0,m} ≤ 2^{r+1}L(A₀/C₀)2^{q₀−p₀}(log g_k^{−2})^{r+p₀−q₀}, using log g_m^{−2} ≥ ½log g_k^{−2} and p₀ < q₀.

## Packet 44 (LF #4.394.6, #4.454.3, #4.454.7, #4.454.13, #4.454.18, #4.454.19, #4.454.21, #4.454.23, #4.454.25, #4.454.27–#4.454.38, #4.454.40, #4.454.41)

Read in full (18:00). The tag #4.454.22-4 no longer exists: #4.454.22-3 cites #4.454.18–#4.454.18-3, whose bound carries R_k^{3/2}, under q₀ > p₀ + 3r.

| Finding | Change | Lines |
|---|---|---|
| C_L named three constants: the undefined constant of #4.182–#4.200, the Cauchy note's path-length constant (#C9.8.14-2), and the undefined "constant of L" of #4.537-1 | #4.182–#4.200 use C_bd of #4.48.0 at ε_r = 2ε₁ with #4.48.0-3; {#D.C_L^ι} at #4.323-0.1; #4.537-1.0 proves N₀ + 1 ≤ 7(1 + log R_k) | #4.182, #4.183, #4.191, #4.195, #4.198-1, #4.199, #4.200, #4.323-0.1, #4.330, #4.454.25-1, #4.454.25-1.2, #4.512, #4.537-1–#4.537-1.1 |
| #4.48.0 bounds the change by abs(ℋ)_y, a maximum over the neighbouring blocks, while #4.177 bounds 𝐇 only on Δ(y) | #4.177-1: d(y, Λ) ≤ d(y′, Λ) + √d, {#D.C_𝐇^nb} C_𝐇^nb := e^{δ₀√d/16}C_𝐇 | #4.177-1 and the lines of row 1 |
| #4.323-0.1 had C_ι/C_F = O(1)LC_L, against the Cauchy note's C_ι := O(1)L²C_LC_F | O(1)L²C_L^ι (#C9.8.15-3) | #4.323-0.1 |
| "N₀ = O(log R_k/log L)" was used without a source | cites N₀ + 1 ≤ 7(1 + log R_k) (#4.537-1.0); #4.420-1 cites #4.537-1 instead of restating LFR I p.192 | #4.244-1, #4.275.4-0.1, #4.420-0.2, #4.420-1, #4.536-2-0.1, #4.454.18-1 |
| #4.454.18-3 had C(M) once, but the moves carry C(M)ε₁ with ε₁ = C(M)R_kε_k | C(M)² | #4.454.18-3 |
| C_D named W-δ's constant (in B_T, #4.435-0.1), the age-factor constant, and a constant of C_X, L, d (#4.578) | the age-factor constant is {#D.C_irr} C_irr := c_□^{−1}L^{4+β′}max(C, 2C_{ε′}) | #4.454.40-1, #4.454.40-2, #D.E_o |
| C_cm, C_D, n_A, j₀, 𝔥_z and C_{ε′} were introduced in words | D-tags; C_cm := max(1, B₀c″_K)C_comC_cf with {#D.C_com} and {#D.C_cf}; C_{ε′} := C sup_{p≥−1}(p + 2)L^{−ε′p} | #4.454.27-1, #4.454.28-1, #4.454.31-2, #4.454.31-4, #4.454.34-2, #4.454.34-3, #4.454.40-2 |
| m′ ∈ {m − 1, m} had no reason | cites #4.446.1-2 at z's layer m | #4.454.2-2 |
| #4.454.31 restated r_{0,m} ≤ (1 + β₀)²(m − j + 1)^{1/2}r_{0,j} of #4.323-2 | cites #4.323-2 and #4.454.6-3–#4.454.7 | #4.454.31, #4.454.38-1 |
| #4.454.32 justified the case m′ − j < j₀ by "j − m′ ≤ 1" | by m′ − j < j₀, which is what the factor L^{β_Hj₀} needs | #4.454.32-1 |
| "d := d(y, y′)" would have redefined the dimension d | written d(y, y′) | #4.454.25-0.1, #4.454.25-1.2 |
| W₀ in #4.454.35 was defined only in Appendix A (W₀ := W there) | c = W + δ𝐇(s) + w_□, as c − W in #4.454.23 | #4.454.35-3 |
| citations by heading or step number: "(1)", "(2)", "(3)", "(4)", At D(s), At the lifted data, The coarse side, Mixed radii, The lift gauges, The Ratio, At real points the ratio is small, Small n, The old generations, The 𝐑-terms' variation group | cite #4.454.3, #4.454.5-2, #4.454.6, #4.454.6-3, #4.454.18, #4.454.24–#4.454.27, #4.454.31, #4.454.32-3, #4.454.33, #4.304, #C5.28, #C5.47-2, #4.365-1, #4.554, #4.520, #4.455.2, #C5.100 | as listed |
| status remarks in #4.454.29, #4.454.30, #4.454.35, #4.454.40, #4.454.41 | removed | as listed |
| #4.560.1's {#D.c_rp} had no := | c_{rp} := the constant of CMP98 (54), taken ≥ 1 | #4.560.1 |
| lines over 600 characters | split at sentence boundaries | below |

New sub-tags: #4.177-1, #4.537-1.0, #4.454.18-0.1, #4.454.25-0.1, #4.454.25-0.2, #4.454.25-1.1, #4.454.25-1.2, #4.454.27-1, #4.454.27-2, #4.454.28-1, #4.454.28-2, #4.454.29-1–#4.454.29-4, #4.454.30-1, #4.454.30-2, #4.454.31-1–#4.454.31-4, #4.454.32-1–#4.454.32-3, #4.454.33-1–#4.454.33-3, #4.454.34-1–#4.454.34-4, #4.454.35-1–#4.454.35-3, #4.454.36-1, #4.454.36-1.1, #4.454.36-2, #4.454.37-1–#4.454.37-3, #4.454.38-0.1, #4.454.38-1, #4.454.38-1.1, #4.454.38-2, #4.454.40-1–#4.454.40-3 and #4.454.41-1 (with #4.454.3-1–-3, #4.454.7-1–-3 and #4.454.13-1–-3 of the earlier part of this packet).

Checked without change:
- #4.537-1.0: log y ≤ y/e, 1/e < log 2; ((N₀ + 1)/2 − 2)log L ≤ log(L + 1) + log R_k; 2log 9/log 8 = 2.113, 2/log 8 = 0.962, 4 + 2.12 ≤ 7.
- #4.454.27: LC_*C_rsC_clα_{0,m}L^{3−β_Hm′} ≤ α_{0,m}/(2^{13}B₃²L³C_{Q*}) if β_Hm′ ≥ 7 + log_L(2^{13}B₃²C_{Q*}C_*C_rsC_cl), which is m_r's bracket.
- #4.454.27-1: 2L²C(ε₀)d̄ times LC_* is 2L³C_*C(ε₀)d̄; at complex data 4L³C_*C(ε₀)^{15/16}d̄′^{15/16}.
- #4.454.29-4: entries ≤ 2max(B₃, B₅)O(1)c_𝒫r_{0,j} = r_{0,j}/2.
- #4.454.30: c_ℰr_{0,j} ≤ 0.8c₂α_{0,j} if c_ℰ ≤ 6.4c₂B₃ = 32c₂B₃/5.
- #4.454.30-2 and #4.454.31-1: ‖δ‖²/r² is at most θ_z^{β_H} times the order of ‖δ‖‖𝐀_c̃‖/r², since R_XL^{j−m′} < θ_z.
- #4.454.31-3: d_j(X) ≥ θ_zL^p/(2M) for p ≥ j₀; C_out's exponent 5 ≥ 4 + β_H.
- #4.454.36-2: Σ_il_i^{β_H} ≤ N_p^{1−β_H}l_p^{β_H}; (x + y)^{1−β_H} ≤ x^{1−β_H} + y^{1−β_H}; Σ_{p≤h}a_p^{1−β_H} ≤ (1 − L^{−(1−β_H)})^{−1}a_h^{1−β_H}.
- #4.454.38-1.1: L^{−4(abs(m′ − p) − 1)}L^{3abs(m′ − p)} = L⁴L^{−abs(m′ − p)}; δ₀M′/16 ≥ 4 log L.
- #4.454.40: 4 + β_H − ε′ = 4 + β′ at ε′ = β_H − β′.

Left for its packet: the C_D of #4.578 ("a constant of C_X, L, and d") is defined only in words; C_Ψ and C_𝐇 of #4.177 (packet 17) have no D-tags.

## Packet 45 (LF #4.218, #4.323, #4.324, #4.446–#4.446.3, #4.447, #4.453, #4.454.20, #4.454.24, #4.454.26, #4.454.39, #4.455.3, #4.455.4, #4.455.6, #4.456, #4.459–#4.464)

Read in full; recorded 18:32.

| Finding | Change | Lines |
|---|---|---|
| the history's birth scale was written n_b, which also names the W-δ shell index, the count of #A.11.4-1 and the MD2 n_b | n_h := the birth scale of the history, the n of #4.314 and #4.455.1 | #4.446.1-1, #4.446.4-1, #4.449-1.1, #4.456-0.1 |
| c^A, c^B named both the members of #4.441 and the composites | convention: members c^A_Y, c^B_Y with ι_Yc^A_Y = e^{i(ε/L)𝐒_c}c^B_Y on Y (#4.321); c^A, c^B the composites | #4.444-0.4, #4.444-1, #4.445.2, #4.445.2-1, #4.446.2-1 |
| n₀″ and n₀‴ were described in words | defined as least integers ≥ n₀ with the stated bound; existence from the counts of #4.553 and #4.554 | #4.446.4-0.1, #4.447.3-1.1, #4.520 |
| the generic constant of the response at ∂Y_i was an unnamed C | C_{J_S} := O(1)B₀c₀(1)^d with the O(1) of abs(J_S); C_S was rejected (Cauchy note §8.7 clash) | #4.453, #4.453-2 |
| C_irr used "C the constant of (5.1c)" | C_α⁺ := the C_α of (5.1c) at the radii r⁺ (#C5.15-4); C_irr := c_□^{−1}L^{4+β′}max(2C_α⁺, 2C_{ε′}) | #4.454.39-3, #4.454.40-2 |
| the t_□-part bound of (A‴) omitted the factor C_ι′ of #4.454.21-3 | added there and to c_□'s second bound | #4.454.20-1, #4.454.21-1 |
| the size parameter of Δ was written d, the dimension | d_j, the norm of Δ on ℰ_j(X; r) (#C5.8-1); d⁺ := max(d_j, 2) | #4.454.11-2, #4.454.12, #4.454.39-3, #4.454.40, #4.454.40-1, #4.455.5 |
| distances written d | d(y, b), d(y, y′) | #4.446.3-2, #4.454.6 |
| □₀ and d̄_j were each defined twice | D.□₀.2 and D.d̄_j.2 removed; #4.447.1 cites #0.9-2 and #C5.4, #4.456-0.1 cites #4.446.2 | #4.447.1, #4.456-0.1 |
| #4.447.1-1 read "the generation j = m of the layer m" | j = n of the layer n of z | #4.447.1-1 |
| #4.456 read "the member's layer n − 1" | m − 1 | #4.456-0.1 |
| #4.454.24 cited #4.301 for ι_Y | #4.321 | #4.454.24 |
| road map and status lines #4.459-2, #4.459-3 (cited only in LABELS) | deleted | #4.459 |
| status remarks: "(not reviewed)", the status title of #4.460, the road-map sentence of #4.446.2 | removed | #4.446.2, #4.455.4-1, #4.460 |
| citations by heading | cite #4.68, #4.315, #4.321, #4.328-1, #4.329, #4.330–#4.331, #4.335, #4.352, #4.403, #4.465, #4.472, #4.473, #4.520, #4.532, #4.553, #4.554, #4.557, #3.70, #C5.61, #CK.1-3 | as listed |
| run B's per-point term, and the age factor of #4.226 (packet 33), carried an underived factor L⁴: (5.1c) and (5.1c𝐀) give (L^{j−m})^{4+β′} per scale-j point z ∈ Λ_j⁰ (#C5.4, #C8.2.4-2), the finer-layer factor L^{4+β′} being inside C_α (#C5.28-4, #C5.35-4), and a point of the layer m holds L^{4(m−j)} scale-j points | ≤ 6⁵C_αE₀L^{−β′(m−j)} and ≤ d_jE₁(α)L^{−β′(m−j)} per point of the layer m, with the count written out; E_o := max(E₁, 6⁵C_αE₀, C_irr(1 + d_j)(E₀ + E₁), C_far) | #4.226, #4.455.4-2, #4.455.5 |
| lines over 600 characters | split at sentence boundaries | below |

New sub-tags: #4.218-2, #4.323-0.2, #4.323-0.3, #4.323-1.3, #4.323-2-1, #4.323-2-2, #4.324-0.1, #4.444-0.4, #4.446.4-0.1, #4.446.5-1.1, #4.447.3-1.1, #4.453-0.1, #4.453-1, #4.453-2, #4.454.20-1, #4.454.20-2, #4.454.20-2.1, #4.454.20-3, #4.454.26-1, #4.454.26-2, #4.454.39-1–#4.454.39-3, #4.455.3-1, #4.455.3-2, #4.455.4-1, #4.455.4-1.1, #4.455.4-2, #4.455.6-1, #4.455.6-2, #4.456-0.1, #4.459-1.1, #4.460-0.1, #4.460-1.1, #4.460-1.2, #4.460-2.1, #4.460-2.1.1 and #4.460-2.2, and #4.226-0.1 and #4.226-0.2 (packet 33's line, split after the repair). Removed: #4.459-2, #4.459-3, D.□₀.2, D.d̄_j.2. New D-tags: D.n_h, D.n₀″, D.n₀‴, D.C_J_S, D.C_α⁺; D.c^A and D.c^B moved to #4.444-0.4.

Checked without change:
- #4.446.2: where j(x′) = j − 1, L^{j−j(x′)}d̄(x′) ≤ L·L^{1/3}d̄_j = L^{4/3}d̄_j.
- #4.454.6: x e^{−δ₀x/32} ≤ 32/(eδ₀), so (1 + x)e^{−δ₀x/16} ≤ (1 + 32/(eδ₀))e^{−δ₀x/32}.
- #4.454.12: 1 + d⁺ ≤ 3 + d_j ≤ 3(1 + d_j); #4.454.39-3: d⁺ ≤ 2 + d_j ≤ 2(1 + d_j).
- #4.454.20-1: with c_□ ≤ (2⁷B₃(1 + 2C_cm)C_ι′L³C_*)^{−1} the t_□-part is ≤ c₂α_{0,m}/(2⁷B₃) = c₂r_{0,m}/16, since r_{0,m} = α_{0,m}/(8B₃) (#C5.43-11).

Left for their packets: the d_j of the norm against d_j(X) and d_j(x); W-δ's C_D and δ_D against the LF's (#4.578, #4.537-0.3).

## Packet 46 (LF #4.364, #4.366, #4.443, #4.454.12, #4.454.14, #4.455–#4.455.2, #4.455.5, #4.457, #4.458, #4.503, #4.504)

Read in full; recorded 18:55.

| Finding | Change | Lines |
|---|---|---|
| ϖ, the prefactor of LFR I (1.64)–(1.68), was defined only in words, and ϖ already names other constants in the W-δ note, the D2 map and the table | λ_β := 1 − βΣ_{i=h+1}^j2^{−abs(l−i)} − βΣ_{q=l+1}^k2^{−(q−l)}, l = m or j as printed (LFR I pp.190–191); λ_β ≥ 1 − 4β | #4.460-1.2, #4.244, #4.363-1, #4.365, #4.503-1, #4.521 |
| #4.504 used x both for the lattice point and for the real parameter of the disc | the real points are z, abs(z) < 25; the line is #4.559's, with (𝐔(i), 𝐉(i)) = (𝐔, 𝐉) | #4.504, #4.504-1 |
| #4.454.12 concluded "C(1 + d⁺)E₁" with C undefined, restating #4.454.40-1's remark that the factor d_j comes from #0.1 | sentence deleted; #4.472-1.2 now cites #4.454.40-1 | #4.454.12, #4.472-1.2 |
| #4.454.14 restated the Cauchy note's derivation of Lemma 4's condition (iv) | pointer to #C5.12-4–#C5.12-6, #C5.22–#C5.34 and #C5.33 | #4.454.14 |
| the tail part read e^{−cδ₀M₁L^j} with c undefined | c = ½, the tail of #4.456 | #4.458 |
| #4.364's real bound cited "the bound above" at 2ε₁′ without the hypothesis ε₁ ≤ 1 of #4.361 | #4.362 at 2ε₁′ ≤ 1; the Lemma written with 𝔨 = 2Ĉ_Jd̄′(x), 𝔎 = 𝔐_J, at z = i | #4.364, #4.364-2 |
| #4.455.2's move bound skipped σ_c ≤ C(ε₀)d̄(x′); d̄_n was a second form of d̄_j | the step written with #4.321 and #4.314-1; d̄_n stated as #4.446.2's d̄_j at j ≥ n_h = n | #4.455.2-1 |
| #4.455.5's L^{−β′m/2} ≤ θ̃^nL^{−(4β′−θ_V)n/8} skipped its step | L^{−β′n/2} = L^{−θ_Vn/8}L^{−(4β′−θ_V)n/8} written, #C8.7.1-1 cited | #4.455.5-1 |
| #4.443-1 cited "The inputs at the composites" for the Two Constants step, and #4.443-2 a "below" heading that is #4.449 | #4.446.4–#4.446.5; #4.449, #4.453 | #4.443-1, #4.443-2 |
| #4.455.1 cited the stopping-scale count and the generation split by section | #C5.99-1, #0.6.1, #0.8, #C8.6.27; n = n_h | #4.455.1, #4.455.1-1 |
| #4.457 cited the Cauchy note's §5 for C_Π(j)ε₁² ≤ max(1, k − j) and for the moment defect | #C5.74-9, #C5.96 | #4.457 |
| citations by heading, among them a quoted heading ("Run A's half of that is Bałaban's") | cite #4.50-1, #4.351, #C10.4.116, #4.444, #4.445.1, #4.445.5, #4.22, #4.23, #4.505, #4.550, #4.557, #4.503, #4.448, #4.403, #4.450, #4.454, #4.323, #4.261, #4.233, #4.234, #4.235, #4.275.2-2, #4.329, #4.393, #4.397, #4.397-0.1, #4.456-1-1, #4.536, #4.540, #4.514, #C5.36, #C5.37 | as listed |
| status remarks: "(derived given the inputs of (iv))", "derived (not reviewed)", "(derived, not reviewed)" | removed | #4.454.12, #4.455.1, #4.455.2, #4.455.5, #4.458-1, #4.503 |
| abs(·) in a note | written as absolute value bars | #4.454.12-2 |
| titles in packet-41 and packet-44 lines met on the way | #4.321, #4.446.2; #4.533–#4.546 | #4.447.3, #4.454.13-2 |
| lines over 600 characters | split at sentence boundaries | below |

New sub-tags: #4.364-2, #4.454.12-1–#4.454.12-3, #4.454.14-1, #4.454.14-2, #4.455.1-1, #4.455.2-1, #4.455.2-2, #4.455.5-1–#4.455.5-3, #4.457-1, #4.458-0.1, #4.458-1.1, #4.458-2.1, #4.458-2.2, #4.503-1 and #4.504-1–#4.504-3. New D-tag: D.λ_β.

Checked without change:
- #4.458-2.1: CRE (2.6) prints g_n ≤ (1 + β₀)(n − m)^{1/2}g_m for n > m (p.255), and (2.7) the log factor within 1 + β₀, so α_{0,m}/α_{0,j} ≤ (1 + β₀)²max(1, m − j)^{1/2}; #4.323-2's (m − j + 1)^{1/2} is weaker and also holds.
- #4.458-3: (α/α₃)(s_j/α₃) and (α₁/α₃)²(s_j/α₃) are at most C(M) max(1, m − j)^{3/2} times the ratio, and Σ_{m/2<j≤m}max(1, m − j)^{3/2} ≤ C m^{5/2}.
- #4.457-1 and #4.458: L^j − L^{m/2} ≥ L^{j−m/2} − 1 ≥ (j − m/2)log L gives Σ_{m/2<j≤m}e^{−aL^j} ≤ e^{−aL^{m/2}}(1 − L^{−a})^{−1}.
- #4.458-1.1: min(a + x, s) ≤ min(a, s) + x ≤ a^{1−θ_V}s^{θ_V} + x.
- #4.455.1-1: θ_V = (19/40)/(2·4.475) = 0.0531; (4 + β′)(1 − θ_V) = 4 + β′/2.
- #4.364-2 and #4.504-3: (2y)^{15/16} ≤ 2y^{15/16}; 𝔐_J^{1/16} ≤ 1; the case 𝔨 > 𝔎 is #4.558-1.1.
- #4.455.2-1: L^{j−m+1}L^{1/3} = L^{j−m}L^{4/3}; d̄(x′) ≤ L^{(1−ε₀)/3}d̄_n one layer below n (#4.314-1).
- #4.460-1.2: Σ_{i∈ℤ}2^{−abs(l−i)} = 3, Σ_{q>l}2^{−(q−l)} = 1, so λ_β ≥ 1 − 4β = ½ at β = 1/8.

Left for their packets: C_p of #4.462 is described as "a constant of B₀, c_K, …"; #4.448 defines 𝔣_J again after #4.364's 𝔣_J(z); the status titles of #4.473 and #4.505; #4.334's local "c = 1".

On the way, at two-loops' report through the table fork: #4.493's gloss on CRE (3.43)'s C₁p₁(g_k) is removed, and it now cites #4.595's radius 2r^χ_k. #4.600 quotes the printed space (3.43) and is unchanged.

## Packet 47 (LF #4.365, #4.472, #4.505–#4.516, #4.518–#4.532, #4.547–#4.555)

Read in full; recorded 19:22. LF 938987135236.

| Finding | Change | Lines |
|---|---|---|
| n₀ and n₀′ had no definition; their conditions were spread over #4.323-1.2, #4.520, #4.521.1, #4.521.5, #4.553-2 and #4.554-2, with two dependency lists | D.n₀ := least n′ ≥ max(3, n_A, n_H, n_R) with the three conditions of #4.554-1.1; D.n₀′ := least n′ ≥ max(n₀″, n₀‴) + 1 with the three conditions of #4.520; one dependency list each | #4.554-1.1, #4.554-1.2, #4.520, #4.520-1 |
| gap: at real data with n₀ ≤ n < n_H or n < n_R, (iii) and (δ) used C_{Δ𝐇}ϑ_H ≤ 1/6 and R ≥ 2, and only n₀′ was taken ≥ n_H, n_R | n₀ ≥ max(n_H, n_R); #4.290-3 and #4.437-3 cite #4.554-1.1, #4.554-2, #4.520-2 | #4.554-1.1, #4.290-3, #4.437-3 |
| open item: #4.523 took CRE (2.34)–(2.39) at r from "the norm class", whose literal points (R1) carry only (2.34), (2.36), (2.38), (2.39) at r⁺ (#C5.8-6) | #4.521.6: Proposition 9 with Cauchy's estimate bounds the composites and 𝐉_{p,X} of (2.35), (2.37) at (R1) as #4.521.4 bounds the members, so (R1) points lie in Ũ^c_k(Y₄, α̃′/2); #4.523 reads at points of that class; #4.472-0's OPEN sentence replaced | #4.521.6, #4.521.6-1, #4.523, #4.472-0 |
| 𝔰(x).2 clashed with 𝔰(x) of #4.100 and 𝔰 of #4.131 | D.σ_c^ℂ(x) := 8σ_c′(x)^{15/16} | #4.513-1, #4.514, #4.520, #4.521.1, #4.521.4-1, #4.521.5, #4.553 |
| #4.553-1 and #4.554-0.2 wrote the factor 1 + C_F′k^{5/2}/α, C_F′ ∝ 1/α (#4.438-4) divided by α twice; #4.401-2's constant was named C_F, the field-strength constant of #4.328 | D.C_ex := 3^{5/2}8^{q₀}(1 + β₀)³C(M, β, κ)E₀ with Σ_{j=0}^m(m − j + 1)^{3/2} ≤ (m + 2)^{5/2} ≤ 3^{5/2}k^{5/2}; the factor is 1 + C_exk^{5/2}/α | #4.401-2, #4.553-1, #4.554-0.2, #4.554-1.2 |
| E_pt defined in words twice | D.E_pt := Bałaban's bound of V(Y) per point (LFR II p.375 l.29–35) | #4.554-2, #4.520-2 |
| #4.520 wrote c^B(i) = U^0_k(𝐔)^u; #4.518-1 relates them by a product of two gauges | c^B(i) a G^c-gauge transform of U^0_k(𝐔) (#4.518-1), carried by #4.519 | #4.520-2 |
| #4.521.1 cited #4.244 and #4.520 for the transport factor | #4.503-1, #4.519; C^c_t = 2C_tC^c_F/C_F (#4.512) | #4.521.1, #4.521.1-1 |
| #4.554-3 used θ̃^m ≤ θ̃^{k_s/8} without m > k_s/8 | cites #4.426 | #4.554-3 |
| #4.548 restated #4.532's route about (𝐔, 𝐉) | #4.548 removed; #4.532 states it, U″_k separated from X ⊂ Z^c | #4.532, #4.532-1 |
| dead-route sentences | removed: #4.522's ϰ_cC_𝐇ε̂′ bound, #4.524's single-constant Theorem 1, #4.547's plaquette remark, #4.548's c₀ route, #4.551's reason, #4.472-3's "unprinted claim" | as listed |
| status remarks and road mapping | removed: "(derived, not reviewed)" in #4.520–#4.524, #4.529, #4.532, #4.549, #4.550, #4.552, #4.553-3, #4.554-2, #4.554-3, #4.472, #4.472-2.1, #4.472-3; #4.472-0-1's and #4.554-3's road-map sentences | as listed |
| citations by heading | cite #4.323, #4.370, #4.403, #4.409, #4.411, #4.423-1–#4.423-2, #4.444, #4.450, #4.454, #4.460, #4.503, #4.503-1, #4.505, #4.506, #4.507–#4.513, #4.511, #4.512, #4.514, #4.517, #4.519, #4.520-2, #4.522–#4.546, #4.523, #4.524–#4.529, #4.532, #4.533–#4.546, #4.536-0.3, #4.540–#4.542, #4.551, #4.553, #4.554, #4.560-0, #4.580, #4.599, #C5.47-2 | as listed |
| #4.514's input list unverified | #4.515 (with #4.516–#4.519), #4.520, and #4.521 | #4.514 |
| lines over 620 characters | split at sentence boundaries; #4.521.4-0.1's semicolon made a full stop | below |

New sub-tags: #4.365-0.1, #4.401-2.1, #4.507-1, #4.507-2, #4.511-0.1, #4.511-0.2, #4.511-1.1, #4.511-2.1, #4.511-2.2, #4.512-1, #4.512-2, #4.513-1, #4.513-1.1, #4.513-2, #4.514-1, #4.519-1, #4.520-1, #4.520-2, #4.521.1-0.1, #4.521.1-1, #4.521.1-2, #4.521.2-1–#4.521.2-3, #4.521.4-0.1, #4.521.4-0.2, #4.521.4-1.1, #4.521.5-1, #4.521.6, #4.521.6-1, #4.521.6-2, #4.523-1, #4.523-2, #4.526-1, #4.526-2, #4.527-1, #4.529-1–#4.529-3, #4.530-0.1, #4.530-0.2, #4.531-1, #4.532-1, #4.547-1, #4.550-0.1, #4.550-1, #4.550-2, #4.554-1.1 and #4.554-1.2. Removed tag: #4.548. New D-tags: D.n₀, D.n₀′, D.E_pt, D.C_ex, D.σ_c^ℂ(x) (replacing D.𝔰(x).2).

Checked without change:
- #4.553: 8σ_c′^{15/16} with σ_c′ ≤ C(ε₀)(a_k/ε)^{ε₀}d̄′ gives the printed right side; 5(1 − ε₀)/16 − 15ε₀/2 = 5(1 − 25ε₀)/16; θ̃^nL^{−(1−121ε₀)n/16} ≥ L^{−5(1−25ε₀)n/16} for θ̃ ≥ L^{−(1−ε₀)/4}.
- #4.554-0.2 and #4.554-1: (1 − ε₀)/3 − 8ε₀ = (1 − 25ε₀)/3; (1 − ε₀)/4 + (1 − 97ε₀)/12 = (1 − 25ε₀)/3.
- #4.521.1: σ_c^ℂ/r_{0,m} ≤ 2σ_c^ℂ/ϱ ≤ 2r(Y) ≤ 1/32 as ϱ ≤ 2r; r(Y)α̃′ ≤ r/32; (1 + o(1))r + r/32 < (9/8)r.
- #4.521.5: 2B₃σ_c^ℂ(x)/r_{0,m} ≤ 2B₃·8B₃(1 + β₀)/(512B₃²(1 + β₀)) = 1/32; 4σ_c^ℂ(y) ≤ α_ℓ/(8B₃(1 + β₀)) ≤ r_{0,ℓ}.
- #4.521.6-1: e^{2^{−7}}(½ + 2^{−9}) < 0.51 < ¾; CRE p.261 prints β = ¼, so the prefactor 1 − β(1 − 2^{−(j−n)}) ≥ ¾.
- #4.529: L^x ≥ x for L ≥ 2 gives D ≥ k₀ + 1 − m.
- #4.365-1: a_k ≥ ε, so #4.553's right side ≥ 8C(ε₀)^{15/16}d̄′(x)^{15/16}/α_m.

Left for their packets: #4.388-0.1 uses n ≥ n₀′ for "the enlargement of r(Y) ≤ ½ r(Y)'s bound", which is not among #4.520's conditions; #4.621 redefines n₀ locally (l.2260); D.ϱ := ϑ_gf (#4.284.5-2) clashes with the room ϱ(x) of #4.301-3, which has no D-tag; D.𝔰(x) (#4.100) and D.𝔰 (#4.131) share a symbol; #C5.8-6 can cite #4.521.6-1 for (2.35), (2.37) at r; #4.546-2's (2.35) from the class now rests on #4.521.6 at (R1). Kept at 632–648 characters as one sentence or close: #4.511-1, #4.521.5-1, #4.530.

## LF #0.0: σ on 𝒟^c (2026-11-08 20:33)

LF 938987135236 → 943491fdba44. #0.0: OPEN → derived, not reviewed; #0.0-1 deleted (no longer cited anywhere).

What changed:
- #4.291-2, #4.292-0.1, #4.292-1, #4.292-2 (with the new #4.292-2-1): σ = σ^B + σ^δ (D.σ^B, D.σ^δ); the base (𝐔, 𝐉₀) lies at the radii α/(8B₃) (#4.472, #4.503, #4.521.6-1), so σ^B has Bałaban's printed bounds; the OPEN marker of #4.292-0.1 is gone.
- #4.293.2–#4.293.2-2: minimiser form only (current as a function of the data, LFR I p.190 l.18–19, CRE (2.37); old terms at that pair, p.373 l.14–15); 𝐉 enters the data only through the first datum on Y₁ ∖ Y₁⁰, via 𝐇″_k, u_k⁰, and M^·(U₁). The second form and the OPEN tail of #4.293.2-2 are deleted.
- (a), #4.293.3–#4.293.5-1: the room 8B₃ (#4.473); prefactors λ_β ≥ ½ at the LF's β = 1/8 (#4.460-1.2, #4.465); the disc |z| ≤ R and Schwarz's lemma; K_Σ, C_KU (#4.540.2, #4.235-0.1–#4.235-1); gauges Lipschitz with C_u (#4.385-1), C_BU; d(y, Λ) ≥ max(k − q − 1, 4MR_k/M₁) on the boundary layer (Z^c by #4.537-0.1–#4.537-0.2; Z by ∂Z₀ ⊂ Λ_k cubes, y ∈ Ω_{k−1}, crossing Ω_{k₀+1} ∖ Ω_{k₀+2}); ϵ_z; Proposition 9 at the complex base by the identity theorem; W^δ_z, 𝐇^δ_z with #4.530's layer conversion; entries as in #4.536, #4.545, #4.546; frozen layers paid by c_Z, the prefactor by λ_β^{−1} ≤ 2; C_δU; R^U = R/(2C_δU); membership (3/2)/(8B₃) + ½ < 1; the term at W^δ_z is the continuation of the term at U^δ_z (Landau gauge v_z, v₀ = 1, VAR p.307 l.2–4).
- (b), #4.294–#4.294-0.2: |Q| ≤ O(1)B₃²A₁²p₁²(g_k)|𝐁₀| (p.360 l.42, p.361 l.12, row sums as at p.379 l.31); |V| ≤ 𝔈_V := Σ_P‖P‖ (p.375 l.38–p.376 l.2); sup|σ^δ| ≤ (8cθ̂C_δU/r)(O(1)B₃²A₁²p₁²(g_k)|𝐁₀| + 𝔈_V) → 0 with γ; σ^B uniform in k′ ≤ k.

Re-derivation checks:
- Prefactor: both sums are at most 3 and 1, so λ_β ≥ 1 − 4β = ½ at β = 1/8 (#4.460-1.2).
- Decay split: δ_H d ≥ δ_D(max(k − q − 1, 0) + 4MR_k/M₁) from d ≥ max(a, b) ≥ ½(a + b) and δ_D ≤ ½δ_H.
- k = k₀ + 2: (8MR_k − 2M₁)a_k ≥ 6MR_ka_k since M ≥ M₁ and R_k ≥ 1.
- Membership: (1 + ½)/(8B₃) + ½ < 1 for B₃ ≥ 1 at |z| ≤ R^U.
- Schwarz factor: 2/R^U = 4C_δU/R = 8cθ̂C_δU/r.

Weak points, labelled or cited in the text: X meets each component of Z in a cube or a wall (#4.293.4-3, inferred, not printed); the kernel row sums O(1)B₃² of the form, as at p.379 l.31 (#4.294); 𝔈_V as Bałaban's resummation sum (#4.294-0.1).

Correction (20:54): the first version, LF 943491fdba44, bounded the prefactors below by P_β := 2^{−(R_k+1)}, taking Bałaban's β ≤ ¼, and paid P_β^{−1} with a new condition (D-P) δ_DM ≥ M₁ log 2. The LF fixes β = 1/8 (#D.β, #4.460-1.2, checked in #4.465), which gives λ_β ≥ ½. So #4.293.3-0.1, D.P_β and (D-P) are deleted, and #4.293.3 and #4.293.4-10 cite #4.460-1.2.

New sub-tags: #4.292-2-1, #4.293.4-1–#4.293.4-10, #4.293.5-1, #4.294-0.1, #4.294-0.2. Removed tags: #0.0-1, #4.293.3-0.1. New D-tags: D.σ^B, D.σ^δ, D.U^δ_z, D.D^δ_z, D.B^δ_z, D.K_Σ(y), D.C_KU, D.C_BU, D.ϵ_z, D.W^δ_z, D.𝐇^δ_z, D.C_δU, D.R^U, D.𝔈_V. Readings inventory: the σ row moved from Open to Awaiting review.

## The local links of the kernel form (2026-11-08 20:44)

LF 943491fdba44 → b78d00e57470; BP_VAR_PROP4_KERNEL.md 48eb8f5cf7b7 → be58db4b4e09.

Gap: #4.36-1-1 bounds the product of the link decays by e^{−(δ_ch−δ₀/128)Σd_i} with Σd_i ≥ d(y,y″), which needs a rate on every link. The local links Q, Q*, a^V and the vertices of (i) had none.

Repair:
- #4.36-0-3 and #4.36-0-4 give the supports:
  - Q_j and Q_j* join c₋ to the blocks of the bonds with an endpoint in B^j(c₋) ∪ B^j(c₊) (PBG p.414 l.15, checked in the transcript).
  - So does C_j(·, c), the nonlinear part of Q_j(ηA)(c) (VAR (48)), since each average of CMP98 (15) reads only the two blocks of its bond, and the blocks nest.
  - a^V joins a block to itself. A plaquette vertex joins blocks whose corners lie within η of each other.
- Lemma D (BP_VAR_189.md #BV.3-1b, #BV.3-1h) gives d ≤ 3dL for each local link, so a kernel ≤ κ is ≤ κe^{¾dLδ₀}e^{−¼δ₀d}. #4.36-1 lists the local links at the rate ¼δ₀, and #4.36 points to #4.36-0-3 in place of "supported within one block and its neighbours".
- #4.33 adds the hypothesis RM ≥ 4dL, allowed because VAR's results hold for every R ≥ R₁ (VAR (1), p.277 l.14–17, checked).
- Where the hypothesis is met:
  - #4.444-0.1-1 (new): R′M′ ≥ (L(12d + 1) − 1)L, by #T2.15 and #T2.5.
  - #4.314: LM₁ ≥ 4dL at the joins, as M₁ = K_{M′}M′ ≥ (12d + 1)L.
  - #4.656 and §0's #0.20.1-1 list the condition.
- #4.447.5's "M′ for RM" contradicted #4.444-0.1 and is corrected to RM = R′M′. The counts at α = ¼ stay at M′ (#4.445.3-1).

Lemma D re-derived line by line before citing it (BETA's file, read only):
- the blocks C, with |x − y|_∞ < 2a_{j+1} on C;
- the sites within 2a_j of Δ(y), which lie in B^j(Z) with Z ∈ y + a_j{−2,…,2}^d and B^j(Z) ⊂ C, by 2a_j ≤ a_{j+1};
- Case I: 3da_j = 3dLa_{j−1} ≤ RMa_{j−1} puts the blocks outside Ω_j into Ω_{j−1};
- Case II: 4dLa_j ≤ RMa_j and 2da_{j+1} ≤ RMa_{j+1} give C ⊂ Ω_j ∖ Ω_{j+2};
- admissibility under both counts;
- the weights: 2dL + d(L − 1) + 2d/L = 3dL − d + 2d/L ≤ 3dL, and 2d(L − 1) + dL + d/L = 3dL − 2d + d/L ≤ 3dL.

New sub-tags: #4.36-0-3, #4.36-0-4 and #4.444-0.1-1. No new symbols. The table fork was told (RM ≥ 4dL for #T1.5), with the SHAs.

Correction: #4.444-0.1 first took #4.33's two other conditions at the composites from R_thr, which covers printed thresholds only. It now takes them from R′M′ ≥ ½LM₁ and (J-W) at the width R′M′, which M₁ ≥ 2M_J(d, L) gives (balaban_proofs/BP_JOINS_BLOCK_SIZE.md #4.24, #4.29; #T2.9), with δ_* ≤ δ₀ (#T12.21-1).

## Packet 51 (LF #4.571–#4.622)

Read in full; recorded 20:59. LF 1e6de3b6974e → 16874c04b589.

| Finding | Change | Lines |
|---|---|---|
| status remarks in the headings of (e), the exceptional constituents, the completions, and #4.595–#4.599 | removed | #4.571, #4.584, #4.588, #4.595–#4.599 |
| δ_i of the boundary terms defined in words | cites #C1.1-4, δ_i := (g^B_{j+1})^{−2} − (g^A_j)^{−2} | #4.572-1 |
| #4.578 used e^{−(j−i)} for the L^{d(j−i)} points without L^{j−1−i} ≥ j − i | added, with e^{−(j−i)} ≤ L^de^{−(j−1−i)}; δ of #4.652; σ and (⋆) of #4.654–#4.655 | #4.578-1 |
| #4.578 summed X at the rate κ − 1 − δκ by C_X without comparing rates | (β/16)κ ≤ ½(κ − 1) ≤ κ − 1 − δκ for β ≤ ¼, δ ≤ ¼, κ ≥ 2 | #4.578-3 |
| k̄ and Ē₀ defined in words | D.k̄, D.Ē₀ | #4.578-2 |
| #4.579 and #4.579-1 cited the Cauchy note's §8.6 by heading | #C8.6.24-1–#C8.6.24-2 | #4.579, #4.579-1 |
| the crossing's units, the conditions (κ-½) and σ_V ≥ 1, and the step map's references cited by heading | #4.582-1, #4.582-1.1, #4.583, #4.588, #4.654 | #4.581-1, #4.582-2, #4.583-2, #4.585, #4.586, #4.589, #4.591-3 |
| #4.592's parenthesis cited the complex-background argument in words | #4.599–#4.621, under (L-V) | #4.592 |
| #4.596–#4.615 cited the real-background items by heading | #4.335, #4.46, #4.460, #4.504, #4.505, #4.553, #4.554, #4.557, #4.559, #4.560, #4.596-1, #4.596-1-2, #4.597, #4.597-1, #4.598 | #4.596-0-1, #4.596-1-2, #4.597-1, #4.597-2, #4.598, #4.605, #4.608–#4.612, #4.615 |
| the threshold of r^F(X) ≤ ½ was unnamed, and #4.621 redefined n₀ locally | D.n_F := the least k_s from which #4.598 gives r^F(X) ≤ ½ at every non-deep X; D.n_F^c := the larger of n_F and the least k_s with C_{rF}θ̃^{k_s/8} ≤ ½; #4.622's order of choice lists n_F, n_F^c | #4.598-1, #4.621, #4.622 |
| lines over 620 characters | split at sentence boundaries | below |

Re-derivation checks:
- #4.578-1: (i − k_s/8) + (j − i) = j − k_s/8 > k_s/8 for j > k_s/4, so i − k_s/8 > k_s/16 or j − i > k_s/16; then 2^{−(i−1−k_s/8)} ≤ 2·2^{−k_s/16} or e^{−(j−i)} ≤ 2^{−k_s/16}, both ≤ L^de²2^{−k_s/16}.
- #4.582-1.2: t₁ + t₂ + t₃ > RM gives (t₁/M − 1)½βκ + t₂¼δ + (t₃/M)¼(κ₁ − 1) ≥ c_V(t₁ + t₂ + t₃)/M − ½βκ > c_VR − ½βκ = σ_V.
- #4.583-2: N ≥ k_s/8 − 2 and σ_V ≥ 1 give e^{−σ_V max(N, 0)} ≤ e²e^{−k_s/8} ≤ e²2^{−k_s/16}.
- #4.586: ½βκ(R − 1) = ½βκR − ½βκ ≥ c_VR − ½βκ = σ_V, since c_V ≤ ½βκ.

New sub-tags: #4.572-1, #4.572-2, #4.573-0.1, #4.573-0.2, #4.573-1.1, #4.573-1.2, #4.578-1–#4.578-3, #4.579-1, #4.580-1, #4.581-1, #4.582-0.1–#4.582-0.3, #4.582-1.1, #4.582-1.2, #4.583-0.1, #4.583-1, #4.583-2, #4.588-1, #4.588-2, #4.589-1, #4.590-0.1, #4.590-1, #4.591-1–#4.591-3, #4.592-1 and #4.596-0.1. Relabelled since LF 1e6de3b6974e: the old #4.573-0.1 is #4.573-0.2, the old #4.582-0.1 and #4.582-0.2 are #4.582-0.2 and #4.582-0.3; no file but LABELS_LF_AND_TABLE.md cited them. New D-tags: D.k̄, D.Ē₀, D.n_F, D.n_F^c.

Later in packet 51: #4.596-1-1 read "With β ≤ 1/8, as in (d)(ii)"; it now reads "With β = 1/8 (#4.460-1.2)". During packet 52, #4.621 was split at "So the variation is ≤ C_hθ̃^{k_s/8}…", which is now #4.621-1, and Ē₀ (#4.578-2) gained C₀^𝔹.

## Packet 52 (LF #4.623–#4.671)

Read in full; recorded 21:26 at LF 655cd900e6b3, revised 21:44 at LF 410b1ad53094 and Cauchy 6bd89bc214ff → 563cdd5a5b01. LF 16874c04b589 → 410b1ad53094.

| Finding | Change | Lines |
|---|---|---|
| status remark in the heading of the creation difference | removed | #4.623 |
| h, N, and Bałaban's C₀ used without definition; C₀ clashes with #T4.4 | h = k_R − N (LFR I p.178 l.9), D.N.5 N := N̄(K − k_R) of #CP.13, D.C₀^𝔹 := C₀ of LFR I (1.70) (p.192 l.11) | #4.623, #4.625, #4.629, #4.649, #4.650 |
| #4.624 took every integration scale above k_s/8 without proof | D.n_N from #CP.14 and K − k_R < 3k_s/4 + j(C) (#C8.2.1-3); for k_s < n_N, c_ν ≤ 2 ≤ C_hθ̃^{k_s/8} once C_h ≥ 2θ̃^{−n_N/8}; n_N enters #4.622's order of choice | #4.622, #4.624, #4.624-0.1, #4.624-1 |
| deep 𝔹-terms cited by heading | #4.577–#4.579, #4.578-2, #C8.6.24-2 | #4.624-2 |
| generation of the created terms not stated; #4.650 put the count N₀ of overlapping created terms into the per-term norm b | each ℂ^{(i)}_k(X) is carried as its own boundary term of the generation k_R, since d_m(X) ≥ d_{k_R}(X) for m ≤ k_R (#4.582-0.3–#4.582-1), with class norm ≤ (C₀^𝔹/B₀)c_ν ≤ C_ℂ′(𝒟^∗_{k_R} + C_hθ̃^{k_s/8}), D.C_ℂ′ := 2C_ℂC₀^𝔹/B₀; the count C_cN₀ enters only per-point sums | #4.650, #4.650-1 |
| N₀ not bounded where the room and the recursion over ν use it | D.N₀^+(i) := 1 + 2(log(32L(L + 1)) + 2 log log g_i^{−2})/log L ≥ N₀, from LFR I p.192 l.18–20 with β₀ = 1/7 (#T1.2) and R_k ≤ 8L(log g_k^{−2})² (#T2.23) | #4.638, #4.643-1, #4.649-1 |
| the propagation sum of #4.659 omitted the multiplicity of the created terms at a point | the source D.s^♯_i := (C_B + C_ℂ′)(𝒟^∗_i + C_hθ̃^{k_s/8}) is nondecreasing; #4.659 holds with 2C_cN₀^+(i)b_i for b_i; N₀^+(i) ≤ μ_N(k − i)N₀^+(k) with D.μ_N(a), D.c_μN, D.W^♯; threshold 4C_cη_kN₀^+(k)W^♯ ≤ 1 in (T1); b_i ≤ 2s^♯_i | #4.660–#4.660-4, #4.670 |
| the quotients' per-point sums omitted the same multiplicity | the factor 2C_cN₀^+(i) ≤ 2C_cμ_N(j − i)N₀^+(j), μ_N(j − i) ≤ μ_N(P_j(Z)) via j − m + 1 ≤ P_j(Z) (#C8.6.11-4); D.C_w^♯; φ gains C^B_n(𝒟^∗_j + C_hθ̃^{k_s/8})P_j(Z)² with C^B_n of #C8.6.11-10 | #4.662, #4.662-1, #4.663, #4.668-1 |
| #4.654's C_W clashed with #4.420's D.C_W and the Cauchy note's window constant C_W | D.C_wr | #4.653-2, #4.654, #4.656, #4.660-2 |
| w_K, C_μ, and the bound lθ̃^l ≤ C_μ(k_s + 1)θ̃^{k_s/8} restated from #C8.7.1-5 and #C8.7.3-7–#C8.7.3-10 | cited | #4.669 |
| references by heading, by section letter, or "as there" | #4.31, #4.33, #4.36-0-1, #4.36-0-4, #4.459-0.2, #4.574–#4.589, #4.592, #4.595–#4.598, #4.615, #4.637, #4.645, #4.653-2, #4.655, #0.1.8, #0.1.10, #C8.2.1-2, #C8.2.1-4, #C8.2.1-5, #C8.7.3-2, #CS8.5 | #4.625–#4.669 |
| unsupported "h ≥ k_R/2 − 1", "collar comparison below", and a road-map sentence | removed; the comparison is #4.642 | #4.643, #4.644 |
| lines over 620 characters | split at sentence boundaries | below |

Re-derivation checks:
- #4.638: N₀ + 1 ≤ 4·2^{(N₀−1)/2} for N₀ ≥ 1, so (N₀ − 1)log L ≤ log(L + 1) + (1/7)(½(N₀ − 1)log 2 + log 4) + log(8L) + 2 log log g_k^{−2}; with log L − (log 2)/14 ≥ ½log L for L ≥ 2 and log(8L(L + 1)) + (log 4)/7 ≤ log(32L(L + 1)), N₀ ≤ N₀^+(k).
- #4.660-1: with a := k − i and log g_k^{−2} ≥ 1, log log g_i^{−2} ≤ log(log g_k^{−2} + 2β₀ + log(a + 1)) ≤ log log g_k^{−2} + 2β₀ + log(a + 1), so N₀^+(i) ≤ N₀^+(k) + μ_N(a) − 1 ≤ μ_N(a)N₀^+(k).
- #4.660-2: W^♯ ≤ C_{wr}L^dc_{μN}Σ_{s≥0}(s + 2)(eL)^{−s} and (2 − x)/(1 − x)² ≤ 2.8 for x ≤ (2e)^{−1}.
- #4.660-4: with μ_N(k − i) ≤ μ_N(k + 1 − i) and s^♯_i ≤ s^♯_{k+1}, η_kΣ_iw_{k+1−i}L^{d(k+1−i)}·2C_cN₀^+(i)·2s^♯_i ≤ 4C_cη_kN₀^+(k)W^♯s^♯_{k+1}.
- #4.662-1: 2B₁·2C_c·2 + C_XB₀C_w^♯·2C_c·2 = 4C_c(2B₁ + C_XB₀C_w^♯), times N₀^+(j)μ_N(P_j(Z))s^♯_j.
- #4.663: (1 + L^d)P·4C_c(2B₁ + C_XB₀C_w^♯)N₀^+(j)μ_N(P)(C_B + C_ℂ′) ≤ C^B_nP², since Pμ_N(P) ≤ c_{μN}(P + 1)P ≤ 2c_{μN}P² for P ≥ 1; max_{P≥1}P²e^{−2P} = e^{−2}.
- #C8.7.3-11: N₀^+(j) ≤ C_N′K at j ≤ K/2 turns the fine-scale term C(bK/2)^{−κ₀/2}ℓ_K into ≤ CC_N′K^{1−κ₀/2}ℓ_K ≤ CC_N′μ_K.

New sub-tags: #4.621-1, #4.624-0.1, #4.624-1, #4.624-2, #4.626-1, #4.626-2, #4.629-1, #4.633-1, #4.636-1, #4.636-2, #4.637-1, #4.642-1, #4.643-0.1, #4.643-1.1, #4.643-1.2, #4.643-2.1–#4.643-2.3, #4.645-0.1–#4.645-0.3, #4.645-1.1–#4.645-1.3, #4.646-0.1, #4.646-1, #4.649-1, #4.650-1, #4.652-1, #4.653-1, #4.653-2, #4.660-0.1, #4.660-1–#4.660-4, #4.662-1 and #4.668-1. Relabelled: the old #4.643-0.1 is #4.643-0.2. New D-tags: D.N.5, D.C₀^𝔹, D.n_N, D.N₀^+(i), D.s^♯_i, D.μ_N(a), D.c_μN, D.W^♯, D.C_w^♯, D.C_ℂ′, D.C_wr. Removed D-tags: D.w_K and D.C_μ at #4.669.

Cauchy note, consequent changes (the LF session edits it): #C8.6.2-8 and #C8.6.11-10 take the per-point bound of LF #4.662-1, with C^B_n := 8c_{μN}(1 + L^d)C_c(2B₁ + C_XB₀C_w^♯)(C_B + C_ℂ′)N₀^+(j) and P_j(Z)² for P_j(Z); #C8.6.17-1 uses P²e^{−C_PP} ≤ 1; #C8.6.21-1-1 measures the 𝐁-terms of the V(Y) per term, C^B_V := 2(C_B + C_ℂ′ + C_ℂ), with no factor N₀; #C8.6.29 writes C^B_R = C^B_{R,1}N₀^+(j); #C8.7.3-11–#C8.7.3-11-1 absorb N₀^+(j) (C^N_Σ, C^N_m, C^N_μ, C_N′), carried into #C8.7.3-14, #C8.7.3-16 and #C8.7.5; #C8.4.5 lists N₀^+(j); #C8.6.2-10's Ē₀ gains C₀^𝔹; #CP.22-3-1–#CP.22-3-2 state the threshold 4C_cε^{*B}(g)N₀^+(g)W^♯ ≤ 1; #CK.1-1 and #CK.1-16 list the constants, with #CK.1-1's stale σ := min(3δκR, ⅛δ₀RM) and C_w ≤ 1/(eL − 1) corrected to #4.654's and #4.657's. New Cauchy sub-tags: #CP.22-3-1, #CP.22-3-2, #C8.6.21-1-1, #C8.7.3-11-1.

Revision of 22:04 (reported by the table fork). The C_c of #4.629-1, "the constant of Bałaban's count", had no definition: Bałaban prints only "There are at most N₀ such terms" for the regions that contain the common domain (LFR I p.191 l.48–49). It also clashed with #4.560's D.C_c := 60 and with Bałaban's C_c in α_{c,m}. The count is now derived, and the symbol is D.C_ov := 2.

| Finding | Change | Lines |
|---|---|---|
| overlap count C_c undefined and clashing | generations with h + i > k₀: at most k_R − k₀ = N₀ (h + N = k_R, LFR I (1.11)); for h + 1 ≤ j < j′ ≤ k₀ the regions Z_j ∖ Z″_j are pairwise disjoint; so ≤ N₀ + 1 ≤ C_ovN₀, D.C_ov := 2 | #4.629-1–#4.629-1-3 |
| C_c in the uses | C_ov | #4.648, #4.650, #4.660-0.1, #4.660-3, #4.660-4, #4.662, #4.662-1, #4.670; Cauchy #CP.22-3-1, #CP.22-3-2, #C8.6.2-8, #C8.6.11-10, #CK.1-1 |

Re-derivation check, #4.629-1-1–#4.629-1-2: Z″_l = (Ω_l^{∼5})^c ∩ Z for h + 1 ≤ l ≤ k₀ (LFR I (1.11)), so Z_j ∖ Z″_j ⊂ Z_j and Z_{j′} ∖ Z″_{j′} ⊂ Ω_{j′}^{∼5}. The points of Ω_l^{∼5} lie within ℓ∞-distance 5MR_la_l of Ω_l (five layers of the cubes of Ω_l, LFR I p.179 l.7–8). BP_LAYER_WIDTHS #4.18-1 gives the ℓ∞-distance ≥ 8MR_{l+1}a_{l+1} from Ω_{l+1} to Z_l = Λ_l^c ⊆ Z′_l and to Ω_l^c, on Z. For j′ ≥ j + 2, Ω_{j′}^{∼5} ⊂ Ω_{j′−1} ⊂ Ω_{j+1}, and Ω_{j+1}^{∼5} ∩ Z_j = ∅, as 5 < 8.

## Packet 53 (LF #5.1–#5.68)

Read in full; recorded 22:04. LF 410b1ad53094 → b3f44b51cb9c (this includes the revision above), Cauchy 563cdd5a5b01 → c9b62136d9c5.

| Finding | Change | Lines |
|---|---|---|
| status remarks in the section heading and the headings (a)–(f) | removed; the dependence on the points (3), (6), (7), and (10) of (LF-A) is stated at #5.50 and #5.68 with the pointer (Open Gaps) | #S5, #5.2, #5.9, #5.17, #5.29, #5.44, #5.51 |
| references by section letter, heading, or "Lemma 2.1(i)" | tags: #4.7-2, #4.38, #4.89, #4.91, #4.170, #4.458-0.1, #5.3, #5.4, #5.9–#5.50, #5.17–#5.43, #5.49, #5.53, #C6.1, #C8.2.1-5, #C8.5.1, #C8.5.1-4–#C8.5.1-5, #C8.6.18-2, #C8.6.18-3, #C8.6.23, #C8.7.3-10, #C11c.5, #CP.14 | #5.1, #5.3, #5.4, #5.6, #5.8, #5.18-0.1, #5.30, #5.34, #5.37, #5.38-1, #5.39-3-2, #5.42, #5.45, #5.47, #5.48-2, #5.49, #5.50, #5.54, #5.59, #5.63, #5.66-2, #5.67, #5.68 |
| restated definitions | cited; D.J′.2, D.δ𝐉.2 (#4.89), D.m_i, D.w_K.2 (#C8.7.1-5), and D.ω(X).2 (#5.4) removed | #5.30, #5.38-2, #5.59 |
| the constant of 𝒟^B_{i+1} ≤ Cm_i unnamed, its D-tag without := | D.C_𝒟B := the constant of #4.669's bound (not #C8.7.3-2's C_m) | #5.38-2 |
| #5.33's D.c_W clashed with the Cauchy note's c_W (#C10.3.13-1), which §4 uses at #4.71–#4.72 and #4.349–#4.353 without a pointer, and with D2.6's species constant c_W in c^σ_n | D.c_RW; #4.71 points to #C10.3.13-1; #5.39-3-1-0.1 cites D2.6 closure 5.0 (D2.7 closure 15.8-1(5-1)) | #4.71, #5.33, #5.36, #5.39-3-1-0.1 |
| b̄^{𝐓′}_K ignored the factor N₀^+(j) of C^B_n (packet 52) | factor N₀^+(g_K^*), D.g_K^* := (ḡ^{−2} + b′K + C)^{−1/2}, since g_j^{−2} ≤ ḡ^{−2} + b′(K − j) + C (#CP.14) and N₀^+(g) increases with g^{−2}; a log log K factor, which #5.66-2 absorbs | #5.67-1 |
| lines over 620 characters | split at sentence boundaries | below |

Re-derivation check, #5.67-1: N₀^+(g_K^*) ≤ 1 + 2(log(32L(L + 1)) + 2 log log(ḡ^{−2} + b′K + C))/log L ≤ C log K for K ≥ 3. Then (k + 1)θ̃^{7k/8}, θ̃^{k_s/8}, and 2^{−k_s/16} stay geometric in K (k = k_s = K − j(C), #5.64, #4.646-0.1), and Kw_K ≤ kKw_K stays summable after multiplication by a power of log K (#5.66-2).

New sub-tags: #5.1-1, #5.3-0.1, #5.16-1, #5.18-0.1, #5.21-0.1, #5.39-3-1-0.1, #5.40-0.1, #5.41.3-0.1, #5.41.4-1, #5.42-1, #5.45-1, #5.54-1; from the revision, #4.629-1-1–#4.629-1-3. New D-tags: D.C_𝒟B, D.c_RW (replaces D.c_W), D.g_K^*, D.C_ov. Removed D-tags: D.J′.2, D.δ𝐉.2, D.m_i, D.w_K.2, D.ω(X).2, D.c_W.

22:09 (reported by the table fork): #4.349's second-variation constant c′_W, used in D.x₁, gets the tag D.c′_W := the constant of that bound, a constant of G. LF b3f44b51cb9c → 9c2e58ac7bd3. 22:10: the Cauchy note's D.RΔ^c-T at #C5.35-4 takes ":=" ("(RΔ^c-T) := the statement of #C5.33–#C5.35-3"); Cauchy c9b62136d9c5 → 72cad2341c28. 22:25: LF #4.71 (about 1,900 characters) is split at sentence boundaries into #4.71 and the new #4.71-1–#4.71-3, with no other change; LF 9c2e58ac7bd3 → bd880a3e0982.

## Packet 12b (LF #3.63–#3.100)

Read in full; recorded 22:34. LF bd880a3e0982 → b6aff2179f62. Packet 13's row is closed, since its parts 13a1, 13a2, 13b1, and 13b2 are done.

| Finding | Change | Lines |
|---|---|---|
| status remarks "derived" in the headings of §1–§4, of §3(a) and (d), of the appendix, and in #3.76 | removed | #S1, #S2, #S3, #3.1, #3.16, #S4, #SA, #3.76 |
| pointers "above", "below", "checked above", "(c)", "§4(c)", "(b)", and "the Cauchy note's §8.6" | #3.61, #3.74–#3.79, #3.89, #4.45-1 (κ_Λ, Bałaban's (1.9)), #4.43-1.2 (C(M)), #4.152 (the polydisc), #3.45, #3.100.1, #C8.6.5–#C8.6.8-1 | #3.69, #3.82, #3.83, #3.94, #3.94-1, #3.95, #3.96-1, #3.96-1-1, #3.100, #3.100.1 |

Checked without change: #3.94's lower bound (κ_Λ/2)‖B′‖² follows from #4.45-1, since g_k^{−2}(2κ_Λ − O(1)(M⁶R_kε_k + e^{−R_k}))‖Y‖₂² = (2κ_Λ − O(1)(M⁶R_kε_k + e^{−R_k}))‖B′‖² at Y = g_kB′, which is ≥ (κ_Λ/2)‖B′‖² for γ small. No line of the packet exceeds 620 characters. Packet 12b's narrow and full rounds wait until the remaining consolidation is applied (workflow §4: all queued repairs before a launch).

## Second pass over LF §4: heading pointers and restatements (#4.295 onward)

In progress; recorded 23:49. LF → fb8554088cbd. Every pointer by heading or letter was looked up at its target and replaced by the target's tags.

| Finding | Change | Lines |
|---|---|---|
| c_ρ := one value, which met neither #4.377's condition nor #4.312-1's | c_ρ := min(1/(4(1 + β₀)C_p), 2B₃c₂/(1 + β₀)², c_𝔯M/(2C_{K₂})); the case j < m is the new #4.377-1 (the move is smaller by L^{j−m}, and L^{j−m}α′_{0,m} ≤ (1 + β₀)²α′_{0,j} by #4.323-2); C_{K₂} and c_𝔯 defined at #4.312-0.1 | #4.464, #4.377, #4.377-1, #4.312-0.1, #4.312-1 |
| c_U used and never defined | c_U := 3(1 + 2κ_s), from the soft support's margin and (1.24)'s coefficients < 3 (#3.70-2, #3.70-4) | #4.420 |
| wrong or dangling pointers | #4.323 → #4.330–#4.331; #4.323-1.2 → #4.460-3; #4.301's "as for U^B" deleted (no such identity anywhere); #4.336 → #4.79 at ℓ = 0 and #4.70–#4.71; #4.343-1 → #4.48.0-0; #4.420-0.2 → #T1.2; #4.420-2 → #C5.59-5 | as listed |
| #4.296 restated #4.217–#4.217-2 | cites it | #4.296 |
| #4.432-0.1–#4.432-2 restated the W-δ note's #W7.23–#W7.25-9 and #T4.13 (the telescoping, C_tel, the absorption, (1.11), the composites) | #4.432-0.1 and #4.432-2 cite them; #4.432-1, #4.432-1.1, #4.432-1.2, and D.C_tel deleted; the per-group factor of (J) is #W7.24-3 | #4.432–#4.432-2 |
| #4.444-0.1 defined R′ again (D.R′.2) | cites BP_JOINS_BLOCK_SIZE #4.24 | #4.444-0.1 |
| R₁M₁ under two conventions (the table fork, 23:2x): "R₁ = 1" (block size M′) and "R₁ raised to M′/M₁^{VAR}" (block size M₁^{VAR}) | one convention, the second: VAR (1)'s R is counted in M₁^{VAR}-blocks, R = R′R₁ at the joins and R = R_ιM₁/M₁^{VAR} at the lift; the condition R > 4dLR₁ of #W12.237-3 reads R′ > 4dL and R_ιM₁ > 4dLM′ | BP_JOINS_BLOCK_SIZE #4.22, #4.23–#4.24-2; LF #0.6.2, #4.329, #4.444-0.2, #4.447.4, #4.447.5-1, #A.11.1.1; W-δ #WOG.9-11, #W8.11-6, #W8.16–#W8.16-1, #W11.148-11, #W12.27-2–#W12.27-7 (#W12.27-3 and #W12.27-5 deleted), #W12.43, #W12.105-3, #W12.237-6, #W12.257-3, #W12.264-6; Cauchy #C9.1-4, #C9.8.6-1–#C9.8.6-3, #C9.8.17–#C9.8.17-3 (R written R_ι) |
| status remarks | removed | #A.11.1.1; W-δ #WOG.9-11, #W8.11-6, #W11.148-11, #W12.264-6 |

Re-derivation, the lift: VAR's Sect. F cube of parameter R₁M₁ = M′ reaches d(2M′ + 2M′)L^jη beyond Ω_j (#W12.237-3); the lift's layer is R_ιM₁L^{j−1}η wide, M₁ = K_{M′}M′, so the reach stays inside for R_ιK_{M′} > 4dL, met by R_ι = 4dL + 1; in M₁^{VAR}-blocks R = R_ιK_{M′}R₁ ≥ R₁, VAR's R ≥ R₁ (p.277 l.17). New sub-tag #4.377-1; new D-tags D.c_U, D.C_K₂, D.c_𝔯; deleted D.C_tel, D.R′.2. Table rows reported stale to the table fork: #T2.20, #T2.22, #T7.1 ("R₁ = 1"), #T4.7 (the Cauchy note's R is now R_ι), #T4.13 (cites the deleted #4.432-1).

### Continuation, #4.445 to the end of §4 and Appendix A

Recorded 2026-11-09 00:27. LF → 31ed33edb813 (CR 0, no trailing spaces, dchk.py 0 lines). The heading-pointer list (hp2.py) went from 103 to 5, all inline headings (#A.4, #A.4-1) or other files' sections (#2.6, #2.10); dangle.py lists only tags defined in balaban_proofs/ (#4.7-1-x, #4.11–#4.36, #4.41-1-x, #4.536.x), as before.

| Finding | Change | Lines |
|---|---|---|
| #4.454.17 and #4.454.17-3: "2(1 + ⅛) times the base's", but the added terms of #4.545-3 are absolute, not relative | at most (1 + 2^{−9})² times the base's plus 2^{−7} of (a)'s current bound (each step multiplies by ≤ 1 + 2^{−9} and adds ≤ 2^{−9} of that bound, #4.545-2–#4.546); the margin (1 + 2^{−9})²/8 + 2^{−7} < 9/32 | #4.454.17, #4.454.17-3 |
| #4.523-1 cited LFR I (1.75) for the integration variables, and omitted B and V″ | V′: LFR II (1.1), M₀ε_k (#4.416); B: g_k abs(B) < δ′_k = g_kA₁p₁(g_k) ≤ (A₁/A₀)ε_k (#4.57, p₁ < p₀ of #T3.40); V″ on Λ ∖ Ω″^{∼2}_{h+1}: C(ε_q + ϑ_q) ≤ o(1)r_{0,q} (#4.1, #1.3–#1.6, q₀ > p₀); V″ on Λ^c and V_k on Z ∩ Λ^c are averages of U in D₀ (LFR II p.370 l.7–8) | #4.523-1, new #4.523-1.1 |
| #4.523-2 said R_k comes from Sect. F's field "not from the plaquettes"; it comes from the bound ε_P of the data V_k on Z ∩ Λ^c (#4.43-1.1), which 𝔸_Z inherits | rewritten; in D₀ those data are averages of U, so no R_k | #4.523-2, #4.529-1 |
| wrong pointers | #W8.16 → #W8.19-1 (#4.445.4-1); #4.304 → #4.452 (#4.454.37); "as in that item" → #4.409 (#4.529-2) | as listed |
| clashes and duplicate D-tags | D.c_R (#4.290-2) → D.c_rad; D.c_R.2 → D.c_R (#4.445.5-3); D.M_c.2 → D.M_c; D.α′ (#4.508-0) → D.α^ι; D.ε₁.3 (#4.525) → D.ε₁^D; D.Δ_𝐇.3 deleted (#4.454.40-3 cites #4.433) | as listed |
| heading, letter, and § pointers | replaced by the targets' tags | #4.445–#4.546, #4.289.5-2, #4.291-2, #A.10, #A.11.3, #A.11.12, #A.13, #A.14, #A.16, #A.9.1 |
| #4.447.5-2 restated (RΔ^c-T); #4.449-2 and #4.454.7 carried roadmaps; #4.452-0.1 restated π′ | deleted, cited | as listed |
| status remarks outside §0 | removed | #4.7-1-0, #4.10-1, #4.10-2, #4.33-1, #4.41-1-1-1, #A.10, #A.11.1, #A.11.1.4.1–#A.11.1.6.1, #A.11.17, #A.11.24, #K0.g6 |

Re-derivation, #4.523: D = D′D₀ with D₀ the datum at the real U. Its data are averages of U (plaquettes ≤ O(1)r_{0,q} by CRE (2.34)) or integration variables: V′_k on Λ^{(k)} (≤ M₀ε_k), exp(ig_kB) on 𝐁₀ ⊂ Λ (≤ max(A₁/A₀, M₀)ε_k), and V″ on Λ ∖ Ω″^{∼2}_{h+1} (≤ C(ε_q + ϑ_q), and (ε_q + ϑ_q)/r_{0,q} = O((log g_q^{−2})^{p₀−q₀})). So p_q ≤ O(1)r_{0,q} + O(ε_k) with the O(ε_k) part on Λ only, which is what #4.525–#4.529-2 consume.

## §0 Dissolved (2026-11-09 01:06)

| item | action | tags |
|---|---|---|
| Open Gaps heading and summaries #0.2–#0.19 | deleted; every body pointer to them repointed to the body tag that carries the content | #4.160-2, #4.407-2, #4.439-3, #5.50, #5.68 |
| #0.1 | moved verbatim to the new section (LF-2) at the Members of the Quotients {#S0} before {#SA}; status words removed; checked by cmp01 against the saved original | #0.1.1–#0.1.42-1 |
| "Open Gaps (3)" and "(10)" pointers in §4 | repointed to #4.450–#4.454.41-1 and #4.623–#4.650 | #4.216-2, #4.226-1, #4.255, #4.262-1 |
| #4.226-1 and #4.262-1 said c^A (or the member) is not the local minimiser at ∂Y_i | repaired in place: only at the decoupled data do the collar's fine data keep c^A outside 𝒮_z; at a member's data c^A ∈ 𝒮_z (#4.450-0.1, #C5.13-6) | #4.226-1, #4.262-1 |
| roadmap sentence; heading marks (derived); P.2 section count | removed; P.2 now says the note numbers only §§1–5 | #0.1.12, #3.25, #3.26-1, #3.26-4, #3.28, #3.43, #4.561.1-1.3-1.0, #P.2 |
| external pointers to deleted tags | Cauchy #CP.2-3, #CP.6-12, #C5.8-12, #C5.8-13, #C5.28-13, #CK.1-2; W-δ #W8.13-1, #W8.13-2, #W10.5.108-2, #W12.187-2 | as listed |

Re-derivation, #4.226-1: 𝒮_z (#C5.13) asks that c^A on □₀ be the local minimiser of its own block data at the scale of the layer. A member minimises with the full 𝐁″_k, whose layers on □₀ are ≥ n − 1 (#C5.31-3); the collar constraints of (1.61) are its own finer averages, so they change nothing, and c^A ∈ 𝒮_z. At D(s) the collar data are replaced (p.373 l.31–34), c^A is critical only for the variations that keep them (#4.450-1), and the direct comparison of #4.454 is used instead.

Remaining after this step: table rows 11, 212, 215, 455, 598 sent to the table fork; D2_STEP_MAP l.566 not owned; the packet plan cites the old §0 and is re-cut with packets 54–59; 46 LF lines cite BP_LAYER_WIDTHS, BP_VAR_COVERING, and BP_JOINS_BLOCK_SIZE tags without naming the file.

## Cauchy Status Summaries Removed (2026-11-09 01:16)

| item | action | tags |
|---|---|---|
| preamble status: (LF) status lines, the "Derived, awaiting review" items, the Status paragraph, the summaries of §6.2, §9, §10, Review status | deleted; each fact checked present in the body (#C3.9-2, #C3.10-2, #C5.31-3, #C5.33-2, #C5.37-4, #C5.37-18, #C5.65, #C5.72-3, #C5.75-2, #C9.8.6, #C10.5.6–#C10.5.7; δ^s_j at LF #3.32) | #CP.2-3, #CP.2-4, #CP.5–#CP.11-3, #CP.21-1–#CP.21-20, #CP.23–#CP.25-2, #CP.30 |
| where (LF) is derived | one line | #CP.2-2 |
| conditions block | old #CP.21-21 under the base tag, headed The conditions and the result | #CP.21 |
| pointers to the Status paragraph | (G′), (G″) named in place; #C9.6.5 restated (9.10) and is deleted, #C9.6.5-1 → #C9.6.5 | #C8.5 (G′ line), #C8.6.29, #C9.6.5 |
| §7 title What Remains, Collected; status in section and item titles | §7 → The Assembly of the Estimate; marks removed | §§2–4, 6, 8.1–8.7, 9, 10.2, 10.4, 11; #C5.21, #C5.28, #C5.28-12, #C5.30, #C5.36, #C5.43-11, #C5.47, #C5.47-2, #C5.61, #C5.68, #C5.76, #C5.81, #C5.85, #C5.91, #C5.100, #C7.5–#C7.9, #C8.6.19, #C9.8.5, #C9.8.18-5, #C10.5.3, #C10.5.4 |
| inline status words | removed | #C2 (c_N line), #C5.63-3, #C5.64-1, #C5.67, #C5.75-11, #C5.79-3, #C6.2.12, #C7.1, #C8.2 lines, #C8.5.2-18, #C8.6.10-4, #C8.6.21-5, #CP.23 text, #CP.29-1, #CP.29-3 |
| dead routes in the sources | Lemma SH → LF §3(d) soft tests; V4 lem:c5-5-5 dropped; the continuum note's derived and open lists dropped | #CR.1-11–#CR.1-13 |
| #C7.1 | inputs named: (LF) (#CP.2–#CP.2-2) under (T1), (T2), (T-Λ), (T-c) | #C7.1 |

Table rows 561, 562, 565 sent to the table fork. Cauchy 21f829a454ae; CR 0, trailing spaces 0, no duplicate tags, no dangling Cauchy tag in any live note.

## W-δ Open Gaps, Status Summaries, and the d^B Bound Removed (2026-11-09 01:52)

| item | action | tags |
|---|---|---|
| Open Gaps section | (Wδ-1)–(Wδ-4) statements moved into the body; the rest deleted | #WOG.1–#WOG.3-1 after #W5.1-1; #WOG.4–#WOG.4-3, #WOG.4-14 at 10.5; #WOG.5–#WOG.5-2 at §11; #WOG.6–#WOG.7-1 after #W12.95 |
| status summaries of §9, §10.6, §11, §12 | deleted; §9 gone; §10.6 is Dependencies and Rates | #W10.6.17–#W10.6.17-5, #W10.6.19 |
| d^B: bounded although no term reads it (#W12.224-6, #W12.248-4) | the bound deleted; #W12.248 (run B's terms read only RHS(1.55)) moved under #W12.224-6 | deleted #W12.226-6–#W12.236, #W12.238–#W12.247, #W12.248-3–5, #W12.249–#W12.249-2, #W12.249-10–19 |
| the current difference at the pair | kept as *The current difference.*: (dι_Y)*J^B − J^A = −κ; the gauge term drops by D_B*∇_Wb = 0; κ enters as §11's ∇b₁ (#W11.86-12–14) | #W12.226–#W12.226-5, #W12.249-3–9, #W12.249-20, #W12.250-2 |
| consumers of the d^B bound | C_w^{(11–12)} loses O(1)B₀²C₀ε₁ (#W8.9 deleted; the current term at the pairs is #W8.6-1's); the M*e_c condition on M₁ dropped from #W8.18-3; #W8.7 → #W12.254-6; #WOG.6-8, #W12.96-1, #W12.140-7 reworded | #W8.5, #W8.7, #W8.18-3 |
| C_F ≤ O(1)L²B₃C₀ and C_ι/C₀ ≤ O(1)L⁴C_LB₃ (were #W12.243-2–5) | moved to where C_F is introduced | Cauchy #C9.8.14-3, #C9.8.14-3-1 |
| ℒ_ι defined twice: dι_Y (§3(c), #WOG.4-3) and H₁𝔡 (10.5, §11); #W3.7-1's Q₁ℒ_ι = id holds only for H₁𝔡 | defined once at #W3.5 as the Landau part, gauge term removed by #W10.5.100–101; restatements replaced; LF's local linearised lift at W^A renamed ℒ_ι^W | #W3.5, #W3.7-1, #W5.16, #WOG.4-3, #W10.1.23, #W10.5.8-2, #W10.5.9-1, #W11.10, #W11.14, #W11.14-2; LF #4.280, #4.284.1-1, #4.295, #4.439, #4.454.25–#4.454.25-1.2 |
| remarks and dead measures | deleted | #W11.99-2, #W12.146-4 |
| long line | split | #W11.110-2-1 |

W-δ 9a0edc9aaf6d, LF 4a0a7b474895, Cauchy c62b3fe408fd; CR 0 and trailing spaces 0 in all three; no duplicate tags; no dangling W-δ tag outside the table. Table rows 23, 39, 83, 127, 128, 141, 540, 544, 550, 552, 558, 563, and #T12.6's ℒ_ι, plus the new {#D.ℒ_ι^W}, sent to the table fork.

## B₃⁺ Stated Once, D2.7 15.8(c), and the Packet Plan Re-cut (2026-11-09 02:10)

| item | action | tags |
|---|---|---|
| B₃⁺ := max(B₃, 2B_J) stated in the Cauchy note, W-δ §8 and the LF | stated once; the others cite it | Cauchy #C5.37-18, #CK.1-10; W-δ #W8.20, #W12.185; LF #4.485 |
| D2.7 15.8(c): the χ_k^c(Y_i^{∼−6}) derivation restated, and #819.1 cited in the wrong file | the restatement replaced by the print's pins (p.383 l.44, p.378 l.22–24) and a pointer to balaban_proofs/BP_TL_SECOND_CLASS.md #819.1–#819.1-2; the leading word's transports at the transport-form points paid by e^{A_k} ≤ e (D(k)(iii); two-loops #820-1) | D2.7 line 191 |
| packet plan: Open Gaps framing and the #0.2–#0.19 pointers (that section is deleted) | title and header re-cut; the pointers and the old Open Gaps numbering dropped from rows 11, 11a, 16, 17, 33–53 | plan rows 11–53 |
| packet plan: consolidation details and round histories in status cells | reduced to the status and the triage or consolidation file | rows 10, 12b, 13b2, 33–47 |
| packet 59 (Cauchy B_J) | dissolved: its blocks are reviewed in packets 30–32 (#C5.37-7–#C5.37-18), 18–29 (#W8.20) and 33 (#4.485) | plan, closed readings |
| packets 54–58: line pins and old reading names | re-pinned by section and tag; contents named as in the inventory's Closed list | IT-1 §3c(2), §6 (f3); D2.6 §2.2–§2.4, §4.2, §6.1, §9.1–§9.3; map #MD2.1.2.1, #MOMGD.11, #MD2.2.6.190, #MOMST.55; SW §5(2), §5(5); O6 §5, §5a(i) |
| stale sizes | W-δ §§7–8, 10–12 measured at 530k, Cauchy §§2–3, 5 at 120k | rows 18–29, 30–32 |

Cauchy ebb50f60d77e, W-δ 7e4b3ee27105, D2.7 ab2af6b0f234, packet plan 7b3552198b90. The plan's tables have consistent pipe counts; it has no CR and no trailing spaces.

## p₁ Stated Once, C_ι Split, the V Identity, and the Wraps' t-Step (2026-11-09 02:52)

| item | action | tags |
|---|---|---|
| CRE (3.43)/p₁ remark stated three times | stated once at the table; the notes cite it | #T11.12-2, #T11.12-2-1; Cauchy #C5.12-8, #C8.2.2-74, #C8.2.2-78, #C8.2.2-80, #C8.5.1-7-1, #C8.5.2-2 (#C5.36-4 deleted); LF #4.493, #4.600 (#4.501 no longer lists (3.43)); W-δ #W12.193-2 |
| C_ι used for both PBG (3.133)'s O(1) and the Cauchy tail constant | (3.133)'s constant renamed B_ι (d and L only), ℒ_ι's C^{1,β} constant C_{ℒ,β}; C_ι is the tail constant only | W-δ #W10.5.32, #W10.5.83-1, #W10.5.87-1, #W12.56-3, #W12.63-2, #W12.76; #W8.11-9's first sentence deleted |
| an extra (3.133) factor in the gauge bound | removed: sup abs(γ) ≤ (O(1) + 2d)ε sup abs(ℒ_ιv) | W-δ #W10.5.105-5; LF #4.277, #4.283 |
| V identity: (1 + c) of Δ^A = D_A*(1 + c)D_A + 𝒦 missing, constants out of step with #W11.157-1 | rewritten | W-δ #W11.144-2, #W11.158-1–3, #W11.159-2 |
| κ at ι_Y(U_{1,2}): §11's K bound misquoted, power β for β_o | κ = ∇_A*K_ι + s_ι with abs(K_ι) ≤ O(1)(ε/a_j)^{β_o}C₀′ε₁a_j^{−2} (#W12.56–#W12.56-1); γ_w ≤ β_o (#W12.56-2) | W-δ #W12.249-3, -4, -7, -8, -9, #W12.250-1–3 |
| c_κ(C₀′ε₁)² ≤ 1 placed at the wrong stage | moved to the data parameter (stage 6); the LF ε₁″ condition stated | W-δ #W8.22-2-1, #W8.23-2, new #W8.23-2-1 |
| sixteen W-δ "Sects." mis-splits | merged into their lines | W-δ (none cited anywhere) |
| wraps' t-step at the per-step terms: "every constituent at most twice its bound" does not give (T′)'s amplitude; the 𝐑-clause vacuous (two-loops report) | the 𝐑-steps do not depend on t; c^t_W linear (a group with a wrap member is a wrap, map #MD2.4.11.5-10); root sum raised by μ^{pt}; bound A^{TZ}_E(𝔞̄ + μ^{pt}/C_S′); Cauchy on the disc R_E = μ₀/Ȳ; ε̂ thresholds tightened to ν_r/(10368M) | Cauchy #CP.22-5, #C7.8-9-4, #C7.8-9-9–#C7.8-9-9-1-2, #C7.6-7, #C7.6-7-2-1 |

| R_E := μ₀/Ȳ without the case Ȳ = 0 (two-loops check) | R_E := ∞ if Ȳ = 0; the line split | Cauchy #C7.8-9-9, new #C7.8-9-9-0 |
| §11 bridge, source side: the constant O(1)B₀(C_Q′ + B_ι)(1 + r_I²) dropped the C_tr background and the Mα₀ Δ′ terms, and the C̃₁ bound lacked B₀ | explicit constant B₀ + (C_Q′ + B_ι)(r_I² + C_trMα₀) + Mα₀, entered in C_br; the gradient term of G₁^{−1}C̃₁ named | W-δ #W11.20, #W11.21-7, #W11.21-8, #W11.21-10 |

Cauchy 6f7444fc6b1a, W-δ 84e3a749b1dd, LF 8b6390bc65b9; CR 0 and trailing spaces 0 in all three; no dangling W-δ tag and no citation of #C5.36-4 in any live note or the table. #T4.38's Δ^E_K and the new A^{TZ}_E sent to the table fork.
