# Triage of Packet 10, Thirty-First Review (lf-p10-20261105-r31)

The review is verification/isolated_reviewer/reviews/lf-p10-20261105-r31/review.md, a full round, at the Cauchy note 1d705cf8b0be, the LF 42b9c81ac626, the table 726abc1fa186, and W-δ 39d82fbef86e.

It found:

- no fatal finding;
- one serious finding, S-1;
- three minor findings, m-2 to m-4;
- three cosmetic findings, c-1 to c-3.

It confirmed the r30 repairs F-1, F-2, m-1, m-2 (in part), and c-1 to c-5.

Every finding is repaired, as listed below. The repairs are in the following files:

- the Cauchy note 392f7288bff1;
- the LF 08e7dc0cf6df (#5.38.1, #5.38.1-1, #5.38-3, #5.66 to #5.66-2);
- the table 7cdbea43205b (#T4.38 and #T4.40 changed; 208 rows);
- the labels index 9bc1ae65731b.

| Finding | Kind | Verdict | Repair |
|---|---|---|---|
| S-1. c̄^W_K = 4(m_W + 1)(r̄_K + 8ρ^{LF}_K) carries (m_W + 1)·3s_K, and s_K's 10sup abs(δ_i) is of order Kw_K, so c̄^W_K is of order K^{4−κ₀/2}ℓ_K, not summable at κ₀ = 9; LF #5.66's bound is false | serious | correct | κ₀ ≥ 11, which CRE p.260 allows after (2.31) ("κ₀ can be chosen arbitrarily large"). LF #5.66 to #5.66-2 derive c̄^W_K ≤ C[kγ_K + kKw_K], γ_K geometric in k up to powers of log(K + 2), and kKw_K ≤ K²w_K summable for κ₀ > 10, also times any power of log K. The Cauchy note takes κ₀ ≥ 11 at #CP.11-3, #CP.29-1, #C6.2.17-1, #C6.2.17-2, #C7.6-7-2, #C8.7.7-1, #C10.5.8-3, and #CK.1. Table #T4.40 records c̄^W_K |
| m-2. LFR II (1.91)'s V-factor is V(Y), not 1 + t(Y)V(Y) | minor | correct | The print (p.388) has Π_{Y∈𝐃}V(Y) and exp Σ_{Y∈𝐃}t(Y)V(Y), integrated over t(Y) ∈ [0, 1]. The constituents are the V-terms V(Y), with the bound (1.68), abs(V(Y)) ≤ αexp(−(1 + 2β)κd_{k,Z}(Y)) (#C7.6-6-1-1, #C7.6-6-2-1-1, #C7.6-6-4-1, #C7.1-1, #CP.29-1; LF #5.38-3; #T4.38). §8.6's 1 + t(Y)V(Y) (#C8.6.21-4) is the derivative of V e^{tV} in V and stays |
| m-3. The reason for the layer condition is the one #C8.6.19-1 rejects | minor | correct | §8.6's bracket covers every V(Y) of a polymer all of whose components are young: a non-deep one has its points at layers > k_s/8 (#C8.6.20-1), and a deep one is bounded by #C8.6.19-2. On the all-small-field term ℓ₀ every component is first-class (D2.7 15.4(iii)), with c_g := 0 for groups meeting a second-class or unchanged component (15.4(i)); the old components are removed (#C7.6-6-2-1-2) |
| m-4. "α₆ and ε₂ taken 2e^{κ_I} times smaller" ignores ε₂ = 2E₀ε₁C₁α₄^{−1}α₆^{−1}M^qe^{C₂κ₁} | minor | correct | The amplitudes are now enlarged by 2 only: with ρ^E_K := max(r̄^E_K, r^V_K, 3(1 + eC_MN^{pt})s_K) and κ ≥ 12, the T-part activities stay within 2e^{κ_Id_i(X)} of run A's bound, using σ ≤ 1/(12e) and 1 + d ≤ e^d (#C7.6-6-4-2). The prefactors α₆ and 2(L+2)⁴O₃ε₂ at twice their size are met with α₆ halved (a choice, map #MD2.4.10.5) and ε₂ halved, that is, RG II's ε₁ taken four times smaller (#C7.6-6-6-1, #C7.6-6-6-1-1). ε₁ is chosen after κ, κ₁, M, α₄, and α₆ (p.20's assumption, map #MD2.4.1.7). Its lower-type conditions are relative to the coupling (map #MD2.4.10.7, #MD2.4.10.17-5, #MD2.1.4.31), met for γ small (#C7.6-6-6-1-2). κ ≥ 12 joins #C7.6-6-6-2's thresholds. Table #T4.38. LF #5.38.1-1 |
| c-1. (LF) also enters §8.6 through 𝒟^∗ and C_h; (W-δ) also enters §7.8's births and LF #5.38-3 | cosmetic | correct | #C7.1-1 and #CP.29-1 list them |
| c-2. r^V_K's range i > k − ⌊k/4⌋ misses LF #5.38-3's step k − m_W − 1 for k ≤ 11 | cosmetic | correct | r^V_K := sup_{i≥k−⌊k/4⌋−1}[…], which covers both ranges since max(m^E_K, m^w_K) ≤ ⌊k/4⌋ and m_W ≤ ⌊k/4⌋ (#C7.6-6-2-1-1; LF #5.38-3; #T4.38) |
| c-3. The interpolation parameter t clashes with Bałaban's t(Y) | cosmetic | correct | Renamed ζ, x^ζ (#C7.6-6-4 to #C7.6-6-8, #C7.8-4-1, #CK.1-32; LF #5.38.1, #5.38.1-1; #T4.38) |

The tags #C7.6-6-6-1 to #C7.6-6-6-1-2 are new, and the former #C7.6-6-6-1 is now #C7.6-6-6-2.

The result is still #C7.7 and #CP.29, summable in K for κ₀ ≥ 11.

The next round, r32, is a full round over the whole packet. It asks about the repairs listed above.
