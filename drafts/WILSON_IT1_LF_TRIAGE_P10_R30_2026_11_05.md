# Triage of Packet 10, Thirtieth Review (lf-p10-20261105-r30)

The review is verification/isolated_reviewer/reviews/lf-p10-20261105-r30/review.md, a full round, at the Cauchy note bce4b66ad4d3, the LF 4354f71a5bdb, the table b32fb0a22afe, and W-δ 39d82fbef86e.

It found:

- no fatal finding;
- two serious findings, F-1 and F-2;
- two minor findings, m-1 and m-2;
- five cosmetic findings, c-1 to c-5.

It confirmed the r29 repairs, except the V-terms (now F-2) and a residual of S-2 (now m-2).

Every finding is repaired, as listed below. The repairs are in the following files:

- the Cauchy note 1d705cf8b0be;
- the LF 42b9c81ac626 (#5.38-3, #5.40-1, #5.40-2);
- the table 726abc1fa186 (#T4.38 and #T4.40 changed; 208 rows);
- the labels index ae3c4f4e96b6.

| Finding | Kind | Verdict | Repair |
|---|---|---|---|
| F-1. m_Wτ^w_K is of order log K/K, so the term 24(m_W + 1)τ^w_K of the LF's (D) is not summable, and neither are s^{W,tot}_K, b^{(M)}_K, and a_K | serious | correct | m^w_K is the least m ≥ 1 with a_wL^m ≥ 3log(K + 2), so τ^w_K := 2A_wmax(L, 3Llog(K + 2)/a_w)(K + 2)^{−3} and m_Wτ^w_K is summable (#C7.8-3). r̄^E_K uses 3Llog(K + 2)/a_{Ew} (#C7.6-6-4), and #C7.8-7 and #C7.6-7 use the new threshold. Table #T4.40 |
| F-2. The R-gas constituents omit the V-factors 1 + t(Y)V(Y) and exp t(Y)V(Y) of LFR II (1.91) | serious | correct | The constituents list the V-factors with the bound (1.68) (#C7.6-6-1-1). They differ by at most r^V_K := sup_{i>k−⌊k/4⌋}[4C_hθ̃^{k_s/8} + 4e²(C_V + C_E + C_C)2^{−k_s/16} + 2𝒟^V_i] times their bounds, by §8.6's #C8.6.21 to #C8.6.22-2, with (W-δ) and (LF) as inputs (#C7.6-6-2-1-1). Every point of their Y lies at a layer > k_s/8 − 1, and with C_θ := sup_{m≥0}(m + 1)θ̃^{m/2} each term of r^V_K is a constant times θ̃^{k_s/16−3/2}, θ̃^{k_s/8}, 2^{−k_s/16}, or w_K, so r^V_K times any power of log(K + 2) is summable (#C7.6-6-2-1-2). ρ^E_K := max(r̄^E_K, r^V_K, 3(1 + C_MN^{pt}/κ_I)s_K) (#C7.6-6-4, #C7.6-6-4-1, #C7.6-7-2, #C7.4-7-5). LF #5.38-3 adds the V-factors. Table #T4.38 |
| m-1. The lists of where (LF) enters omit the young R-steps | minor | correct | #C7.1-1 and #CP.29-1 name the young components' operations and the V-factors at the young R-steps of §7.6 and §7.8, and (W-δ) through the V-factors |
| m-2. The T-gas's convergence at the enlarged amplitudes is asserted, and map #MD2.4.1.20-5 also needs L ≥ 3 | minor | correct | #C7.6-6-6 cites LFR II p.377 l.14 for the R-part, and map #MD2.4.1.17-1 with the prefactors α₆ (map #MD2.4.10.5) and ε₂ (map #MD2.4.10.32-2), each taken 2e^{κ_I} times smaller, for the T-part. #C7.6-6-6-1: κ is free with thresholds (map #MD2.4.1.20-5) at L ≥ 3, the map's standing condition, which the note inherits; the decay is 5κ/6 once κ ≥ 6/5 times the thresholds |
| c-1. #C7.6-6 states the R-step range only with m^E_K | cosmetic | correct | The range is i ≥ k + 1 − max(m^E_K, m^w_K) (#C7.6-6); #C7.8-4 uses i ≥ k + 2 − m^w_K |
| c-2. #C7.6-6-2 cites #C6.2.1-4 for the change of p₀(g_i) | cosmetic | correct | The change is derived in place: log g^{−2} changes by at most 2g²abs(δ), so p₀ changes by at most 2A₀p₀(log g^{−2})^{p₀−1}g²abs(δ) ≤ abs(δ) |
| c-3. "𝐓′_i(X)1" stands for the operation | cosmetic | correct | The operation 𝐓′_i(X) is compared in total variation, its total mass 𝐓′_i(X)1 bounded by b(X) (#C7.6-6-1-1, #C7.6-6-2-2, #C7.6-6-2-3, #C7.6-6-3, #CP.2-1; LF #5.38-3) |
| c-4. #CK.1's tags are out of order, and M̄(X) and ĉ₁ are missing | cosmetic | correct | #CK.1-18 to #CK.1-32 run in order. #CK.1-32 adds ĉ₁, M̄(X), r^V_K, and C_θ, and states ρ^E_K with r^V_K |
| c-5. LF #5.40-1 bounds Π(1 + 2δ_i) by the per-step δ_i ≤ log 2 | cosmetic | correct | It cites the D2.6 closure's Σ_mδ_m = C_δc̄S_R ≤ log 2 (its 5.0), so Π_i(1 + 2δ_i) ≤ e^{2Σ_iδ_i} ≤ 4. #5.40-2 uses δ_i ≤ Σ_mδ_m ≤ log 2 |

The result is still #C7.7 and #CP.29:

a_K := [3x_K + λ_K + x^w_K + b^{(S)}_K + δ_LF(a^{(U)}_K + b^{(M)}_K)]B_W + (e^{ΔE_K} − 1)B_W,

summable in K (#C7.7-1), now with m_Wτ^w_K summable.

The next round, r31, is a full round over the whole packet. It asks about the repairs listed above.
