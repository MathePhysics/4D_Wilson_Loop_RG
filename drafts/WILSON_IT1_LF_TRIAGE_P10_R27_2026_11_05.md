# Triage of Packet 10, Twenty-Seventh Review (lf-p10-20261105-r27)

The review is verification/isolated_reviewer/reviews/lf-p10-20261105-r27/review.md, a full round, at the Cauchy note 8b680db237a0, the LF 50ca3aa719db, the table 30d086997182, and W-δ 4ba9f44bb9d6.

It confirmed the r26 repairs except one premise. It found:

- no fatal or serious finding;
- one minor finding, M-a;
- four cosmetic findings, C-a to C-d.

The fork, working on the pair Cauchy note, reported two further gaps in the single-loop comparison, F1 and F2 below.

Every finding is repaired, as listed below. The repairs are in the following files:

- the Cauchy note 60f7c65716ed;
- the table 9dbe70b6a8d0 (rows #T4.35 to #T4.39 added; #T1.13 and #T4.9 changed);
- W-δ 39d82fbef86e (the C_ι change, and #W10.6.17-2, #W10.6.17-3 restated with #W10.6.17-6 removed);
- the labels index e74695324ca8.

The LF is unchanged at 50ca3aa719db.

| Finding | Kind | Verdict | Repair |
|---|---|---|---|
| M-a. The young pairs' small-field exponent on Λ_k is asserted to be at most X_K at their large-field backgrounds, but §4.1 and §9 are derived only in the all-small-field geometry | minor | correct | Derived group by group (#C6.2.18-1 to #C6.2.18-7). The extra generation and the old tail: CRE (2.43)–(2.44) hold at the multiscale U_k(V) with E₁ and R₁ independent of the domains (CRE p.263 l.5–13), and on Λ_k only the layer Γ_k meets the domain (CRE p.255 l.15–16), so X^{dir}_K holds as before. The coupling term: (9.2) on the stopping layer (LF #4.7). The frozen differences: (8.6), whose class contains the multiscale minimisers. The classical group: the LF's multiscale classical depth (its #4.40–#4.42) gives N_s⁴C_w(ε₀)(g_a^{−2} + β′k)L^{−(1−ε₀)k/2}ε₁², added to X^{cl}_K. The variation groups: the pair line's distance is the LF's σ_c ≤ C^{LF}(ε₀)d̄ (its #4.321), so σ̂ becomes σ̂^Λ := σ̂ + C_{yd}L^{−(1−ε₀)k/6}ε₁ in X^{var}_K and X^{𝐑}_K (#C7.4). Summability of the added parts is #C7.4-1. #C7.4-6 now cites this derivation |
| C-a. On the collar the fine differences 2L·abs(T)/ε exceed the gradient bound unless C_ι carries L² | cosmetic | correct | C_ι := O(1)L²C_LC_F with O(1) ≥ 2 (#C9.8.15-3), and #C9.8.15-4 shows the collar's fine differences ≤ 2L²C_LC_Fε₁/a² inside the gradient bound. The ratio C_ι/C₀ becomes ≤ O(1)L⁴C_LB₃, still independent of M′. Carried to the table (#T1.13, #T4.9) and W-δ (#W8.11-9, #W8.18-3, #W11.133-22, #W12.243-1, #W12.243-5) |
| C-b. (LF) is said to enter every term of a_K except §4's direct bounds | cosmetic | correct | #CP.29-2 lists the exceptions: §4's direct bounds, λ_K, a^{(U)}_K, the old-pair term of b^{(M)}_K, the old part τ^E_K of ΔE_K, and the branches b^{(M)}_K := 4 and a_K := 2B_W |
| C-c. The factor ℓ_K in C_aℓ_K[…] is not in (8.6) | cosmetic | correct | Removed from #C6.2.5, #C6.2.8-1, s′_K (#C6.2.9-1), #C6.2.9-3, #C6.2.17, #C7.1-4, (7.1), and #CP.29. #C6.2.5 now states why C_a covers D_i + S_i + e_i, and #C8.7.7 writes C_a explicitly. The covariance terms keep ℓ_K, which bounds p₀(g_i)² there |
| C-d. VAR's B₀ is cited from (49) and not identified with PBG's | cosmetic | correct | #CK.1-21: VAR's B₀ is introduced at (46) from PBG Theorem 3.12 (p.285 l.25–27), so it is PBG's B₀ (PBG p.423 l.39–40), the one §9.5 and (10.6) use |
| F1 (fork). The leading words of the two runs are read at different fine backgrounds and are not compared | gap | correct | *The leading word.* (#C7.5 to #C7.5-5): abs(f^B_{k+1} − f^A_k) ≤ λ_K := 4ℓ_C‖dπ‖(4C_G(ε₀) + C_Y)ε₁L^{−(1−ε₀)k}, by (9.8) and CMP 98 (15), the LF's (T) with every bond at the stopping scale. #C1.2-3 defines f^A_k. #C7.4-4 and #C7.4-5 carry λ_K, with run A's constant e^{E^A_const} ≤ B_W. The young pairs' leading words are inside s^{W,tot}_K (#C7.4-6) |
| F2 (fork). The loop constants E^A_const and E^B_const multiply the whole numerators and are not compared | gap | correct | *The loop constant.* (#C7.6 to #C7.6-10). The per-step terms are ≤ A_EL^me^{−a_EL^m} by the map's T-step bounds and D2.7 15.4(ii). The old part, m ≥ m^E_K, is bounded per run by τ^E_K. The young part is compared by the species-blind recursion, at most Δ^E_K. So abs(E^B_const − E^A_const) ≤ ΔE_K := min(2τ^E_K + Δ^E_K, 2C^E_Σ𝔞̄). §§3–7 compare the runs with run A's constant, and the restoring factor adds (e^{ΔE_K} − 1)e^{ΔE_K}B_W. K₁ also asks m^E_K ≤ k + 1 (#C7.4-7, #C7.6-4-1). The young step (#C7.6-6) is derived, not reviewed |

The result is now #C7.7 and #CP.29:

a_K := e^{ΔE_K}[3x_K + λ_K + b^{(S)}_K + δ_LF(a^{(U)}_K + b^{(M)}_K)]B_W + (e^{ΔE_K} − 1)e^{ΔE_K}B_W,

summable in K (#C7.7-1).

The self-check before the next round also repaired the following:

- New constants that clashed with existing ones are renamed:
  - the map's C_E, c_E become C^T_E, c^T_E;
  - D2.7's C_R, c_R become C^R_E, c^R_E;
  - D2.3(7)'s C_Σ becomes C^E_Σ;
  - the young factor becomes r^E_i, C^E_r.
  The table records each one.
- #CP.29 and the glossary's long lines are split into tagged continuation lines.

The next round, r28, is a full round over the whole packet. It adds the new §7 blocks and their context extracts.
