# Triage of LF Packet 9, Sixteenth Review (lf-p9-20261105-r16)

The review is verification\isolated_reviewer\reviews\lf-p9-20261105-r16\review.md. It finds no fatal issue, one serious, three minor, and four trivial items.

The review resolves the fifteenth review's serious finding. It confirms the following at the Landau base U₀ = U_k(V₀): the first-order Lagrange identity in RG I's pairing (μ₀ = H̃^*J, the factor 2, t′, the three error terms, and e_a ≤ C(L, M′)ε₁θ_{B₁}), the non-circular θ_ξ bound through 𝒞_U, and the order of the constants.

The repairs below change #A.11.1.4.4.4, #A.11.1.4.4.4.1, #A.11.1.4.1, #A.11.1.4.3, #A.11.1.4.3.3, #A.11.1.4.4.1, #A.11.1.4.4.3, #A.11.1.6, #A.11.1.6.1, #A.9's first sentence, one sentence of #0.1.11, and the first two sentences of #0.1.12. They add #A.11.1.4.4.4.2 (with .1–.3) and #A.11.1.4.3.4. These go to r17.

The LF is now c60169974ab9, with labels c7b67d68d453 (102 multiply defined, CR 0). The table is ff7d58652e3b, with {#T4.32} added (bookkeeping, the fork's two-loops constants).

| Finding | Verdict | Disposition |
|---|---|---|
| S1: (21) is posed relative to U₀ = U_k(V₀) (VAR p.305 l.36–37), so R(U)D_U^*a = 0 fails at the base u_R(Re B)^{g₀^{−1}} | Accepted | #A.11.1.4.4.4 defines ν_a := G′(U)R(U)D_U^*a and a_L := a − D_Uν_a, with R(U)D_U^*a_L = 0 ((3.118)–(3.119)) and Q(U)a_L = Q(U)a. It sets e_a := a_L − â, which stays in N(Q(U)) ∩ N(R(U)D_U^*), so a = â + e_a + D_Uν_a. #A.11.1.4.4.4.1 runs the comparison for a_L, adding the term −𝒬̃(D_Uν_a, t′). #A.11.1.4.4.4.2 bounds ν_a. It writes ν_a = T₁(a − d𝓗) + (T₁ − T₀)d𝓗 along U(s) = e^{iηs𝓗(Re B)}U₀, uses (19) with ε₂ = B₅ε₁ (table #T10.5), and applies Cauchy's bound in s. This gives D_Uν_a ≤ C(L)B₅ε₁ times the norms of a. The new term carries J and so is bounded as the first two terms, and it vanishes at U = 1. #A.11.1.4.1 uses only Π_U, which annihilates D_Uν_a, and #A.11.1.4.3.3 adds D_UD_Uν_a, of size ε₁². #0.1.11 names the base explicitly. #A.11.1.6.1 adds C(L)B₅ε₁ to its ε₁ conditions. |
| M2: B = Q(U)A_N equals RG I's datum only up to −E(U)U′_ax | Accepted | #A.11.1.4.3.4 derives B = B′_U − E(U)U′_ax, with B′_U := Q̃(U)U′_ax. It bounds abs(E(U)U′_ax) ≤ C(L)α₀(θ_{B′_U} + θ_B), so the two suprema agree within a factor 2 for C(L)α₀ ≤ ¼. #A.11.1.4.3, #0.1.11, and #0.1.12 state the difference. |
| M3: (0.4) contains no group average M; the CRE layered transfer is p.276 l.2–16; the propagator bounds are an inference | Accepted | Checked against RG I p.253. (0.4) is exp[i·(mean of (1/i)log of loop holonomies based at c₋)]𝐔(c), and (0.5)–(0.10) axiomatise the separate average M of (0.11). The covariance now follows from log's conjugation covariance (#A.11.1.4.4.1), and E(U) from the analyticity of log near 1 (#A.11.1.4.4.4). The CRE citation is now p.276 l.2–16 for the transfer and l.18–20 for the localisation. The propagator bounds in RG I's pairing are stated as part of Bałaban's "By the results of Sect. G [15]" of RG II (1.2), accepted. |
| M4: #A.11.1.4.4.3's wording | Accepted | The text now says "B is shifted by −KU′_ax(b₋) (#0.1.4)". |
| Trivial: #A.11.1.6 does not list #A.11.1.6.1; #0.1.12's 2dL remark; #A.9's "VAR's data (3)" | Accepted | #A.11.1.6 lists the upper bounds of #A.11.1.6.1. The 2dL clause is removed. #A.9 says "RG I's data (0.4), like VAR's (3)". |
| t1–t4 | Noted | Deferred until after the second clean pass. |
