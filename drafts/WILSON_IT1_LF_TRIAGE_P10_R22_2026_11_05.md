# Triage of Packet 10, Twenty-Second Review (lf-p10-20261105-r22)

The review is verification/isolated_reviewer/reviews/lf-p10-20261105-r22/review.md (Cauchy note c51e09e31f9c, LF fc2901265e71, table 22ebc8f3b014, labels d8b5e8218fcc, W-δ 2b1e11a74d59). It was a full confirming round. It found no fatal or serious finding, three minor findings, and five cosmetic findings. All eight are repaired in the Cauchy note fa0b9ce829e5 (970 lines, every edit within its line), the LF de1068e2ec77, the table 21dbcec72dca, and the labels index e446703f429f. The W-δ note is unchanged.

| Finding | Kind | Verdict | Repair |
|---|---|---|---|
| 1. l.305–307: with the triangle split, the dev insertions of the second term add B_Ws_K to the numerators, so b^{(M)}_K carries 5s_K, not 4s_K | minor | correct | l.307: the numerators get B_W(2s_K + s^{W,tot}_K) (B_Ws_K from the densities, B_Ws_K from the dev insertions, and B_Ws^{W,tot}_K from the dressings); l.305: the remaining young pairs change F by ≤ B_Wδ_LF(3s_K + s^{W,tot}_K), all young pairs by ≤ B_Wδ_LF(5s_K + s^{W,tot}_K), and b^{(M)}_K := 3e^{−C_P⌊k/2⌋} + 5s_K + s^{W,tot}_K; the glossary l.966 and LF #5.3 and #5.63 follow, and #5.3 now cites #5.62 for the dev part (its old pointer #3.70 named an unrelated item) |
| 2. l.293: k_* also depends on ḡ (and b) through ℓ_K, and on j(C) through ℓ_K's argument | minor | correct | l.293 reads "k ≥ k_*(j(C), ḡ), a threshold that depends on j(C) and ḡ through C_a, C_h, ℓ_K = (log(bK + ḡ^{−2}))^{rd+2p₀} (with K = k + j(C)), and the part (K + 1)θ̃^{k_s/8} of w_K" |
| 3. l.516: "𝔊_BJ(U^B) = 0 by the criticality of U^B" omits the multiplier step on VAR's constraint space | minor | correct | l.516 states it: 𝔊_B acts on the derivative of the action in the directions X with Q₁X = 0, and J(U^B) = Q₁^{pl}*λ₁ with (D̄¹)*λ₁ = 0 (§10.3, at n = 1) and Q₁^{pl}X = −D̄¹Θ₁X ((B2) at n = 1) give ⟨J(U^B), X⟩ = 0, as at l.488 |
| 4. (9.0) does not display the threshold "ε₁ ≤ a₁ at M_P" of l.440 | cosmetic | correct | (9.0) carries a₁^{(M_P)}; l.440 defines it as VAR's a₁ taken at M_P; the glossary and table #T3.31 list it |
| 5. "1/16 of the rate of (190)" is ambiguous | cosmetic | correct | l.541 and the glossary read "1/16 of the rate ⅛δ₀^{VAR} printed in (190)", δ₀^{VAR} VAR's δ₀ |
| 6. The ε₁ of (T-Λ) at l.38 and §9's ε₁ share one symbol | cosmetic | correct | l.38 reads "ε₁ = C(M)R_kε_k (VAR's parameter at U₀, not §9's ε₁ := 2C₀ε_V)" |
| 7. l.546 cites CRE p.259 l.43–44 for the spaces being unions of G^c-orbits | cosmetic | correct | l.546 cites CRE's (iii), p.259 l.43–44, for the invariance and RG I p.262 l.4–14 for the orbits |
| 8. l.45 cites RG I Theorem 2, printed for SU(2) | cosmetic | correct | l.45 reads "RG I Theorem 2, printed for SU(2), and for compact simple G BETA_FUNCTION_WILSON_LOOPS.md Corollary 8.2" |

The table also records, at the fork's request, the δ of the two-loops note's (6B) and (6C) in #T4.30 (two-loops #728.1). That edit is bookkeeping and outside packet 10.
