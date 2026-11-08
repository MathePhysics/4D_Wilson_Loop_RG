# Triage of Packet 10, Twenty-Eighth Review (lf-p10-20261105-r28)

The review is verification/isolated_reviewer/reviews/lf-p10-20261105-r28/review.md, a full round, at the Cauchy note 60f7c65716ed, the LF 50ca3aa719db, the table 9dbe70b6a8d0, and W-δ 39d82fbef86e.

It found:

- one serious finding, S-1;
- three minor findings, M-1 to M-3;
- eight cosmetic findings, c-1 to c-8.

The fork, working on the pair Cauchy note, reported three further gaps in the single-loop comparison, F3 to F5 below.

Every finding is repaired, as listed below. The repairs are in the following files:

- the Cauchy note d9e84b07bfca;
- the LF a52e10df2b5e (#5.38 to #5.41.6, #5.53, #5.54, #5.65.1);
- the continuum note fa10b42999e3 (#ND.5.4-1, #ND.5.4-2, #ND.5.7, #ND.6.8, #ND.8.1);
- the table 9ef4d092dd77 (#T4.35, #T4.37, and #T4.38 changed; #T4.40 and #T4.41 added; 208 rows);
- the labels index a422c1e04888.

| Finding | Kind | Verdict | Repair |
|---|---|---|---|
| S-1. The young per-step terms of the loop constant are compared by analogy with the species-blind recursion (#C7.6-6) | serious | correct | Derived (#C7.6-6 to #C7.6-6-7). For K ≥ K₁ the young steps are R-steps of both runs, and the term is the corner and torus remainder of D2.7 15.4's log(Ξ^c/Ξ). Its constituents, Bałaban's activities and the loop's marked activities, differ by at most r^E_i times their bounds. C^E_r now covers the marked activities through C^*_{ins}. The interpolation x^t := x^A + t(x^B − x^A), with abs(t) ≤ 1/r^E_i, keeps each constituent within twice its bound. The doubled amplitudes keep 15.3–15.4's convergence for g small with the rate unchanged, which gives the constant C^{R,2}_E. Cauchy's estimate then gives 2r^E_iA^{E,2}L^me^{−a_EL^m}. Δ^E_K is restated (#C7.6-7), and the sum lemma is derived inline (#C7.6-7-1). The marked activities' recursion is written out (#C8.3.3-4-1, #C8.3.3-4-2) and solved (#C8.7.7-2 to #C8.7.7-3) |
| M-1. The LF's ε₁ and §9's ε₁ are conflated in σ̂^Λ and C_{ε₁} | minor | correct | ε₁^{LF} is named and defined (#C6.2.18-6), and c^{LF}_{ε₁} is bounded uniformly in K (#C6.2.18-7-1). #C7.4 and #C7.4-1 use them, and so do the glossary (#CK.1-30-1) and the table (#T4.35) |
| M-2. The admission at n > k/2 needs k ≥ 2n₀ | minor | correct | #C6.2.18-4 and #C6.2.19 now require k_* ≥ 2n₀ (LF #4.621) |
| M-3. "Uniformly in the volume" should say lattice volume at a fixed physical torus | minor | correct | The r29 claim says "uniformly in the lattice volume at a fixed physical torus" |
| c-1, c-2. Wording of σ̂^Λ's scope and of the larger constant | cosmetic | correct | #C7.4, #C6.2.18-3, #C6.2.18-5 |
| c-3. B_W is used as a bound on e^{E^A_const} times a loop without saying why | cosmetic | correct | #C7.4-4-1: B_W ≥ e^{C^E_Σ𝔞̄}exp(Σ_nν_n) (#C7.5-7) |
| c-4. The smooth w is not CRE (2.24)'s | cosmetic | correct | #C6.2.18-5 cites CRE (2.24)'s smooth w |
| c-5. #T4.37's dependence column is incomplete | cosmetic | correct | M, ν, A_d, C_S′, C_rel^{(1)}, and C⁎ (map #MD2.3.7.8) added |
| c-6. #CP.29-2 is unclear | cosmetic | correct | Reworded, with τ^w_K added to the parts without (LF) |
| c-7. (9.0) omits 4d(3d + 1)L²C₀ε₁ ≤ ½ | cosmetic | correct | Added at #C9.3 (#C7.5-2) |
| c-8. The non-trivial layers are not located | cosmetic | correct | #C6.2.18-1: n ≥ j₀ − 1 ≥ k/2, by CRE (2.2) |
| F3 (fork). The wrap insertions on ℓ₀ are not compared | gap | correct | *The wrap insertions.* (#C7.8 to #C7.8-8-1). The wraps of age m have total weighted mass at most A_wL^me^{−a_wL^m} (map #MD2.0.3.34-4, #MD2.3.4.16-6). The old wraps, m ≥ m^w_K, are not compared, at most 2τ^w_K. The young wraps are compared at birth by interpolation and Cauchy's estimate, with the doubled-amplitude constant C^{w,2}_M. They are then carried by the LF's (V), with differences growing by at most 2L per step, plus the old wraps' differences passed to young descendants, at most 4τ^w_K per step. This gives D^w_K. In product form the wraps change the loop by at most x^w_KB_W, x^w_K := e^{2τ^w_K + D^w_K} − 1, which is added to a_K (#C7.7, #CP.29). K₁ also asks max(m^E_K, m^w_K) ≤ k′ + 1, m^w_K ≤ ⌊k′/8⌋, and the r ≤ ½ condition at a = a_w (#C7.4-7) |
| F4 (fork). The transports of the words are not compared | gap | correct | #C7.5-6 to #C7.5-7-1: the transports change the dressed loop by at most λ_KB_W (LF #5.11, #5.25; map #MD2.0.3.5, #MD2.0.3.6; continuum #ND.5.4, #ND.8.1) |
| F5 (fork). An object of n activities picks up a factor n·r_i, both in #C7.6-6 and in LF #5.38, and LF #5.40 must start at step 1 for the wraps | gap | correct | No constituent count is used. #C7.6-6 and the young wraps use interpolation at doubled amplitudes. LF #5.38.1 and #5.38.2 do the same for the generated part: at most 4g_{i+1} times the bound at the doubled amplitudes, with Ȳ_X and ε̄_A taken at those amplitudes (#5.39). The wraps are taken out of the carry (#5.40, (D) with c̄^W_K := 4(m_W + 1)(r̄_K + 4ḡ_K)) and treated from step 1 by (D^w) (#5.41.1 to #5.41.6), which enters s^{W,0}_K (#5.53). k_W includes K ≥ K₁ (#5.54) |

Further repairs found while checking:

- The continuum note's wrap sum in (5.3), (5.6), (6.3), and (8.1) lacked the factor 4ℓ_C, since the map's wrap term is per traversal. The exponent is now 4ℓ_C[O(C_χρ_{K′}) + 2C sup_jρ̂_je^{−c′(T_ph/u)L^{j(C)}/M}].
- LF #5.53 had C_Q in s^{W,0}_K. It now has C_Q^W, the Q-part constant.

The result is now #C7.7 and #CP.29:

a_K := e^{ΔE_K}[3x_K + λ_K + x^w_K + b^{(S)}_K + δ_LF(a^{(U)}_K + b^{(M)}_K)]B_W + (e^{ΔE_K} − 1)e^{ΔE_K}B_W,

summable in K (#C7.7-1).

The next round, r29, is a full round over the whole packet. It adds the new blocks, §7.8, #C8.3.3-4-1 and #C8.3.3-4-2, and #C8.7.7-2 and #C8.7.7-3, and asks about the LF and continuum repairs listed above.
