# Triage of LF Packet 9, Seventeenth Review (lf-p9-20261105-r17)

The review is verification\isolated_reviewer\reviews\lf-p9-20261105-r17\review.md. It finds no fatal issue, one serious, three minor, and five trivial items.

The review resolves the sixteenth review's findings. It confirms the following at every real base: ν_a ∈ N(Q′(U)), a_L in the Landau gauge with Q(U)a_L = Q(U)a, e_a ∈ N(Q(U)) ∩ N(R(U)D_U^*), and A_N = A_N(U)B + 𝒫_Uξ_ω + Π_Ue_a.

The repairs below change #A.11.1.4.4.4.1, #A.11.1.4.4.4.2.1–#A.11.1.4.4.4.2.3, #A.11.1.4.3.4, #A.11.1.4.3's first sentence, #A.11.1.6.1's last sentence, and one clause of #0.1.11. They add #A.11.1.4.4.4.2.2.1, #A.11.1.4.3.4.1, and #A.11.1.4.3.4.2. These go to r18.

The LF is now e7a665a5e187, with labels 71f16c0a44af (102 multiply defined, CR 0). The table is 310cb2e6096c, after the fork's bookkeeping edit to {#T4.32} (C_u also covers w_m's 4dC_G, cited to two-loops cc01cac1c22c).

| Finding | Verdict | Disposition |
|---|---|---|
| S1: the absorption bounding e_a, and the ν_a bound, use derivative norms of D_Uν_a that PBG does not print (∇∇G′∇*) | Accepted | The absorption now closes in a_L alone, with B₁ = Q(U)a_L and a_L = H₁B₁ + e_a (#A.11.1.4.4.4.1). The term 𝒬̃(D_Uν_a, t′) vanishes identically (#A.11.1.4.4.4.2.3). The gauge transforms of U by e^{isλ} are constrained minimisers at the transformed data, and differentiating their Lagrange condition gives 𝒬̃(D_Uλ, t) = 0 for t ∈ N(Q̃(U)). N(a), the sup and first-derivative norms that (3.44) uses, is bounded independently by (190) and p.307 l.17–18, Bałaban's, accepted, through a = φ(ad iη𝓗)d𝓗 (#A.11.1.4.4.4.2.2.1). The ν_a bound then needs only sup norms, through (3.42)–(3.44). |
| M2: #A.11.1.4.3.4 omits the crossing shift on bonds with b₋ ∈ Λ₀ | Accepted | #A.11.1.4.3.4 now states B′_U = B + KU′_ax(b₋) + E(U)U′_ax on those bonds. #A.11.1.4.3.4.1 keeps only the one-sided bound θ_{B′_U} ≤ 2(1 + C(d)L)θ_B, which uses neither #A.11.1.4.3.3 nor ν_a. #A.11.1.4.3's first sentence names the crossing shift. |
| M3: the conversion per level between A_N's data and RG I's data | Accepted | #A.11.1.4.3.4.2: the conversion is the flat one (#0.1.4, #0.1.12) with the factor 1 + C(L)α₀. C_HC(L)α₀ is covered by δ_U's second term, so the factor per level keeps the form (C_H + δ_U). |
| M4: the analyticity threshold is PBG's a₁(d, L), not c(d) | Accepted | #A.11.1.4.4.4.2.2 uses abs(s)B₅ε₁ ≤ a₁ (table #T1.4). #A.11.1.6.1 lists B₅ε₁ ≤ a₁/2. |
| Trivial: R(U(s)) at complex s; #0.1.11's "H₁ at U₀"; Q(U)U′_ax = B₁ uncited; the real-base corrections to the bond determination | Accepted | R(U(s)) is the analytic extension at complex s (Theorem 3.4). #0.1.11 says "at the base (U₀ in VAR's (174), U in #A.11.1.4.1)". Q(U)U′_ax = B₁ is cited to #A.9, PBG p.394 l.1–2, and (3.115). The C(L)α₀ corrections are stated in #A.11.1.4.3.4.1. |
| t1–t4 | Noted | Deferred until after the second clean pass. |
