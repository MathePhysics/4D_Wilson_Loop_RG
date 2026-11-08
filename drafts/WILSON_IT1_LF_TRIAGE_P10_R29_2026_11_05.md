# Triage of Packet 10, Twenty-Ninth Review (lf-p10-20261105-r29)

The review is verification/isolated_reviewer/reviews/lf-p10-20261105-r29/review.md, a full round, at the Cauchy note d9e84b07bfca, the LF a52e10df2b5e, the table 9ef4d092dd77, and W-δ 39d82fbef86e.

It found:

- no fatal finding;
- two serious findings, S-1′ and S-2;
- two minor findings, m-1 and m-2;
- seven cosmetic findings, c-a to c-g.

Every finding is repaired, as listed below. The repairs are in the following files:

- the Cauchy note bce4b66ad4d3;
- the LF 4354f71a5bdb (#5.38 to #5.41.6, #5.53, #5.54, #5.65.1, #5.67);
- the table b32fb0a22afe (#T4.35, #T4.38, #T4.40, and #T4.41 changed; 208 rows);
- the labels index f00fa0cc5a5b.

| Finding | Kind | Verdict | Repair |
|---|---|---|---|
| S-1′. The R-gas constituents include the components' operations 𝐓′_i(X)1, whose run-dependence is §6.2's (α)–(γ) per point of the history, not r^E_i | serious | correct | The constituents are listed (#C7.6-6-1-1) and paired through R̄ (#C7.6-6-2). A young component's 𝐓′_i(X)1 differs by at most 3s_Kb̄(X): §6.2's three-piece split with (LF-1) gives s_Kω(X)M̄(X) per piece, and (11.2) at the scale i gives ω(X)M(X) ≤ b(X), the spare factor e^{−C_PP} paying ω (#C7.6-6-2-2, #C7.6-6-2-3; #CP.2-1 adds this use of (LF-1)). Old components, born at n(X) ≤ k − ⌊k/2⌋, have P_i(X) ≥ k/4 and are removed by Cauchy's estimate in z on the disc of radius e^{C_Pk/4}, at most 2e^{−C_Pk/4}A_EL^me^{−a_EL^m} per run (#C7.6-6-2-6, #C7.6-6-3). The interpolation radius is 1/(2ρ^E_K), with ρ^E_K := max(r̄^E_K, 3(1 + C_MN^{pt}/κ_I)s_K) (#C7.6-6-4 to #C7.6-6-4-3) |
| S-2. The T-part of the per-step term at R-steps is not compared | serious | correct | At an R-step the term is E°^T_i + E°^R_i (map #MD2.3.5.5-2; #C7.6-6-1). The T-part's polymer activities differ by at most 3C_Ms′_Kn(X)e^{C_Ms′_Kn(X)} times their bounds, with n(X) ≤ N^{pt}(1 + d_i(X)) and N^{pt} := 2·3^dM^d (#C7.6-6-2-4, #C7.6-6-2-5). At the radius 1/(2ρ^E_K) they stay within 2e^{κ_I}e^{κ_Id_i(X)} times their bounds (#C7.6-6-4-2), so the decay is lowered to κ − κ_I, κ_I := κ/6, a free-constant threshold of the map's kind (#C7.6-6-6). The bound at the enlarged amplitudes is A^{E,2}L^me^{−a^{E,2}L^m} (#C7.6-6-7), and Cauchy's estimate gives 4ρ^E_K times it (#C7.6-6-8). Δ^E_K := 4ρ^E_KA^{E,2}S^{(2)}_E + 4e^{−C_Pk/4}A_ES_E is summable (#C7.6-7, #C7.6-7-2). The wraps' births use the same scheme (#C7.8-4 to #C7.8-4-3) |
| m-1. #C7.4-7-3 covers only m^E_K | minor | correct | #C7.4-7-3 uses max(m^E_{K′}, m^w_{K′}). K₁ also asks max(m^E_{K′}, m^w_{K′}) ≤ ⌊k′/4⌋, ρ^E_{K′} ≤ ¼, and k′ ≥ k_*(j(C), ḡ) (#C7.4-7-1, #C7.4-7-2, #C7.4-7-4, #C7.4-7-5) |
| m-2. #T4.41's dependence column omits C_h and C_ν | minor | correct | "as #T4.39's C_a, C_h and C_ν included through C_s and C_S″" |
| c-a. The #C7.8-6 tags are out of order, and r̄^w_K is used before its definition | cosmetic | correct | r̄^w_K is replaced by ρ^E_K, defined in #C7.6-6-4. The tags are now #C7.8-6, #C7.8-6-1, #C7.8-6-2 |
| c-b. #C7.5-6 cites map #MD2.0.3.6 for the covariance | cosmetic | correct | It cites D2.7 15.5(ii)(γ) |
| c-c. #C7.6-6-3 cites #C1.1 and #C7.6 for the same partitions | cosmetic | correct | #C7.6-6-2 cites R̄ (#CP.21-19) |
| c-d. The packet's #CK.1 extract omits #CK.1-30-1 | cosmetic | correct | The line is now #CK.1-32, which the builder includes, and it lists the new symbols |
| c-e. The factor e^{ΔE_K} of #C7.6-10 is redundant | cosmetic | correct | Removed from #C7.6-9, #C7.6-10, #C7.7, #C7.7-1, and #CP.29 |
| c-f. LF #5.38-2's g_{i+1} and ḡ_K clash with the couplings | cosmetic | correct | Renamed η^{gen}_K (#D.η^gen_K); the radius is now ρ^{LF}_K := max(η^{gen}_K, ρ^E_K) |
| c-g. #T4.35's dependence column is incomplete | cosmetic | correct | Adds M through C(M), j(C) and ḡ through R(g_a), A₁/A₀, and β₀ |

Further repairs found while checking:

- The leak term 4τ^w_K of the old wraps into the young ones is removed. By the D2.6 closure 2.1 *Merged groups*, a group that contains an old wrap takes the first inherited species in step order, so on the all-small-field pair it is old (#C7.8-6-1).
- On the large-field pairs such a group can instead be an attached descendant of an earlier member. There the old wraps pass at most 6τ^w_K per step to D (LF #5.40-2), so (D) gains 24(m_W + 1)τ^w_K, which enters s^{W,0}_K (LF #5.41, #5.53, #5.54, #5.65.1).
- The LF's generated part (#5.38-3 to #5.38.2) uses the same constituent bounds and radius 1/(2ρ^{LF}_K), with the generated difference at most 8ρ^{LF}_K times the bound at the enlarged amplitudes, so c̄^W_K := 4(m_W + 1)(r̄_K + 8ρ^{LF}_K). D^{w,LF}_K := (m^w_K + 1)(2L)^{m^w_K}[r̄_KA_wS_w + 12ρ^{LF}_KA^{w,2}S^{(2)}_w + 4e^{−C_Pk/4}A_wS_w].
- LF #5.67-1 (fork point): b̄_K ≤ C[(k + 1)θ̃^{7k/8} + Kw_K + θ̃^{k_s/8} + 2^{−k_s/16}], summable since Kw_K is.
- #C8.7.7-3 cites #C7.6-6-2-1.

The result is now #C7.7 and #CP.29:

a_K := [3x_K + λ_K + x^w_K + b^{(S)}_K + δ_LF(a^{(U)}_K + b^{(M)}_K)]B_W + (e^{ΔE_K} − 1)B_W,

summable in K (#C7.7-1).

The next round, r30, is a full round over the whole packet. It asks about the repairs listed above.
