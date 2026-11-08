# Triage of LF Packet 9, Nineteenth Review (lf-p9-20261105-r19)

The review is verification\isolated_reviewer\reviews\lf-p9-20261105-r19\review.md. It finds no fatal and no serious issue, one minor, and six trivial items. With the eighteenth review, this gives packet 9 two consecutive clean passes.

The review confirms the following:
- the crossing term S_b at every interface, as REG p.81 l.36–44's factor, absent from ξ_ω(b₋);
- its non-circular bound through the data of the layer j − 1;
- θ_{B′_U} ≤ 2(1 + C(d)L)θ_B;
- the right inverse H̃ with S² = 0, and the bound of H̃^*J.

The review notes that transferring REG's crossing factor to RG I's contour families rests on the pairing accepted in #A.11.1.4.4.1, and that the same term also follows from the note's own linear algebra.

The repairs below are made after the second clean pass. They change #A.11.1.4.4.4.1 (the right inverse, λ_t and t′, and the third comparison term), #A.11.1.4.3.4.1, #A.11.1.4.3.4.2, #A.11.1.4.3.2's first clause, #A.11.1.4.4.3's first sentence, #A.11.1.4.4.4.2.2.1, #A.11.1.5.3.1, #A.11.1.6, #A.11.1.6.1, and one clause of #0.1.4. They go to a narrow confirming twentieth review.

The LF is now d627954548d0, with labels ecec1388a8a1 (102 multiply defined, CR 0). The table is 72d1793479e7, after the fork's hash update in {#T4.32} (two-loops f66b126b4b1d).

| Finding | Verdict | Disposition |
|---|---|---|
| M1: at j ≥ 2 the crossing term reads the E-defects of the layer j − 1's data, so Q̃(U)(H₁X + D_Uλ_X) = (I + S)(I + E″)X and Q̃(U)(t + D_Uλ_t) = (I + S)E(U)t | Accepted | #A.11.1.4.4.4.1 states Q̃(U)(H₁X + D_Uλ_X) = (I + S)(I + E″)X, with E″ the total remainder. It also states Q̃(U)(t + D_Uλ_t) = (I + S)E(U)t and t′ := t + D_Uλ_t − H̃(I + S)E(U)t ∈ N(Q̃(U)). The third comparison term reads 𝒬̃(a_L, H̃(I + S)E(U)t). abs(S) ≤ C(d)L, so the bounds are unchanged. |
| T1: the bond determination omits the crossing term on the fine bonds near crossing bonds | Accepted | #A.11.1.4.3.4.1 adds it, ≤ C(d)Lθ_{B′_U}, at the cost of another C(L). |
| T2: #0.1.4 and #A.11.1.4.4.3 do not use S_b | Accepted | Both now name S_b, with −KU′_ax(b₋) as its j = 1 case. |
| T3: the flat crossing shift at a real base is exact only up to S(E(U)U′_ax) | Accepted | #A.11.1.4.3.4.2 states this term, ≤ C(d)LC(L)α₀θ_{B′_U}, which the factor 1 + C(L)α₀ covers. |
| T4: "C(d)" in C(d)C₁ε₁ ≤ ½ is a constant of G | Accepted | It now reads C(G)C₁ε₁ ≤ ½, with C(G) the bound of ad on 𝔤^c. |
| T5: the conversion term is (C_H + δ_U)C(L)α₀ | Accepted | #A.11.1.4.3.4.2 and #A.11.1.5.3.1 now say so. |
| t1, t2, t4 (deferred until the second clean pass) | Accepted | t1: #A.11.1.6 says "K denoting the covariant maps' (P2) constant". t2: #A.11.1.6 lists the (P3) constants K₃, each a C(L, M′), at the choice of M′. t4: #A.11.1.4.3.2 now also covers the real regular pairs (U^{u^{−1}}, U_□) of #A.11.1.2. t3 was already resolved (#A.11.1.5.3.1, M = M′). |
