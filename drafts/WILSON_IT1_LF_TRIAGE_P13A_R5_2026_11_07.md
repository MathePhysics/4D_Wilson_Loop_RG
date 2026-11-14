# Packet 13a r4 Result and r5 Repairs (7 Nov 2026)

lf-p13a-20261107-r4 (LF 0e0a28f49094, table cd814aac5ad0, labels 48aa1d1831b3) found no fatal and no serious findings, three minor findings (m1–m3), and three trivial ones (t1–t3). It confirmed that r3's m1, t1 and t2 are repaired. The round is not clean, so 13a's clean count stays 0. All six findings are re-derived and repaired in place. The same misreading of R_k as r3's m1 was then found outside 13a and swept. r5 is a full round of 13a, #4.43–#4.55-1, with r4's review as its prior.

## Open

None.

## Repairs in 13a (in place)

| Item | Line | Repair |
|---|---|---|
| m1 | #4.50-1.1, new #4.50-1.1.0 | Proposition 1's "ε sufficiently small" now stands at the regularity ε < 2L(L + 1)R_kε_k ≤ ε₁ of the data on Z ∩ Λ^c, as #4.43-1.1 uses it (LFR I p.193 l.21–23; C(M) ≥ 2L(L + 1)max(1, B₅M⁵), #4.43-1.2). The rest of the line moved to #4.50-1.1.0 for length. |
| m2 | new #4.50-1.2; #4.50-1.1.0 | (T-Λ) now contains (b)'s (T-π) (#4.38-1) at the value ε₁ = C(M)R_kε_k of (c), which *The comparison.* and *The data difference.* use. Each condition has the form C·ε₁ ≤ c, and ε₁ ≤ C(M)2^{2r+1}LA₀g_k(log g_k^{−2})^{p₀+r} (#4.50-1.1.1-1), so it holds for γ small depending on M. #4.50-1.1.0 adds PBG Theorem 3.13's "α₀ sufficiently small" (p.426) at 2ε₁, for #4.46-2, beside Theorem 3.12's. |
| m3 | #4.51-1, new #4.51-1.1 | The quadratic term C_qρ̄_u² (#4.40-0) is added. With ρ̄_u ≤ 4C_G(ε₀)c_Kε₁ (#4.9-3, ε/a_n ≤ 1), the difference is ≤ (C + 4C_qC_G(ε₀)c_K)ε₁ρ̄_u, so C_σ := 4C_G(ε₀)c_K(C + 4C_qC_G(ε₀)c_K) + CC_b. C_Δ(M) keeps its formula in C_σ. The second half of the line moved to #4.51-1.1. |
| t1 | #4.50-1.1.1 | "for ḡ and γ small depending on M". |
| t2 | #4.54-0.1, new #4.54-0.1.1 | The decay is split as #4.9-2-2 uses it. e^{−(3/8)δ₀d} absorbs (1 + β₀)²(i + 1): for i ≥ 1, ⅛δ₀RM ≥ 1 gives (i + 1)e^{−3(i−1)} ≤ 2. The remaining e^{−(5/8)δ₀d} = e^{−½δ₀d}e^{−⅛δ₀d} is what the count c_K uses. For x coarser than the data, p.422's spacing ratio a_{j(x)}/a_j = L^{j(x)−j} ≤ L^{3(j(x)−j)}, which is K_ρ's factor (#4.9-2-1) that the count covers. |
| t3 | #4.48-1 | C_Φ(M)'s dependence now lists the block-density constant C of #4.48 and c′_Λ. |

## The R_k sweep (outside 13a, in place)

R_k is R̄(K − k) (the Cauchy note's #CP.13), not CRE (2.5)'s value. The facts the note uses hold for R̄:
- R̄ ≥ 2(log ḡ^{−2})^r (#CP.13).
- R̄ ≥ (log g_k^{−2})^r for ḡ small (#CP.14).
- R̄ is a power of L, nonincreasing in j, and drops by at most the factor L per step (#CP.13, #CP.14-1).
- R_k ≤ 2^{r+1}L(log g_k^{−2})^r (#3.29-1).

Every LF citation of CRE (2.5) for R_k now cites one of these:

| Line | Was | Now |
|---|---|---|
| #4.562-1.1 (13b) | "R_k is a function of g_k (CRE (2.5))" | the first threshold of #4.50-1.1 at O(1)ε′_k, with its C_{1−ζ₀} term, bounded as in #4.50-1.1.1–#4.50-1.1.1-1, for ḡ and γ small depending on M |
| #4.166, #4.420, #4.434.7, #4.454.22, #4.554, #4.598 | R_k ≤ L(log g_k^{−2})^r (CRE (2.5)) | R_k ≤ 2^{r+1}L(log g_k^{−2})^r (#3.29-1), with the factor carried |
| #4.208 | "up to the factor L in R_k (CRE (2.5))" | 2^{r+1}L (#3.29-1) |
| #5.43 | "R_k is a power of log g_k^{−2} (CRE (2.5))" | R_k ≤ 2^{r+1}L(log g_k^{−2})^r (#3.29-1) |
| #5.65 | "(R_k, CRE (2.5), …)" | "(R_k, #3.29-1, …)" |
| #4.412 | R_k as CRE's least power of L, "R_k ≥ L for γ small" | R_k = R̄(K − k) ≥ 2(log ḡ^{−2})^r (#CP.13), R_k ≥ L for ḡ small |
| #4.582-2 | "the widths MR_k grow with k (CRE (2.5))" | "vary with k (#CP.13)", since R̄(K − k) is nonincreasing in k |
| #3.76, #4.294, #4.394.4, #4.394.5, #4.474, #4.480, #4.530-1, #4.656 | "(2.5)" for R_j a power of L, R_j ≥ L, the drop per step, L^{−R_j} small, R_j decreasing in j, R_l ≥ (log g_l^{−2})^r | #CP.13, #CP.14, #CP.14-1 or #3.29-1, as applies |

After the sweep, the only LF occurrence of "(2.5)" is #4.50-1.1.1's "not CRE (2.5)'s value". The four table rows that describe R_k as CRE (2.5)'s (#T2.23 and three others) were sent to the table fork for its judgement, since the facts they use hold for R̄.

## Checked

- PBG p.426, Theorem 3.13: "for α₀ sufficiently small", the same form as Theorem 3.12 (p.423).
- LF #4.9-2-1 (K_ρ := L^{3(j−j′)_+}e^{−δ₀d}), #4.9-2-2 (c_K's count uses e^{−½δ₀d}, through c₀^d(¼), and e^{−⅛δ₀RM(i−1)} ≤ e^{−⅛δ₀d}), #4.9-3 (ρ̄_u), #4.38-1 ((T-π)), #4.40-0 (C_q), #4.43-1.1–#4.43-1.2.
- The Cauchy note's #CP.13–#CP.14-1, and LF #4.560-0 (ε′_k).

## Definition audit and repairs (after r4, before r5)

The user asked for a check that every object in the packet has a proper definition. Each object is now defined where it is first used. Every defect found while doing this was repaired in place.

| Item | Line | Repair |
|---|---|---|
| off-Λ data | #4.43-1.1, #4.44, #4.44-1, #4.46, #4.46-1, #4.51 | LFR II (1.1)'s V_Λ is Bałaban's full data, with V′ a deviation (p.378 l.12). The note's off-Λ data is now V_{Λ^c} := V_k⌈_{Z∩Λ^c}, and LFR II's U_{k,Z}(V′V_Λ) is U_{k,Z}(V′V′₀V_{Λ^c}). ε_P := 2L(L + 1)R_kε_k names the regularity on Z ∩ Λ^c |
| 𝔸_Z, ξ | #4.43-1 | U_0 = exp iη𝔸_Z, VAR's U_1 = e^{iηA} (p.301 l.51), which LFR II writes exp iξA₀. 𝔸_Z is not the A₀ of p₀(g) |
| H_{1,k}, J_0, Δ₁ | #4.45 | defined at first use (LFR II p.356 l.31–p.357 l.8, p.357 l.24; RG I p.266 l.37) |
| Y, 𝔛, norms | new #4.44-2 | ‖·‖_∞ and ‖·‖₂ on the bonds of Λ^{(k)} ∖ G₀. 𝔛 := (1/i)log(V′^B₀(V′^A₀)^{−1}), Bałaban's logarithm (#T11.26), replaces the undefined X |
| C_𝔛(M) | #4.50, new #4.50-0 | πO(1)B₅M⁶, from LFR I (1.83) and #T11.26 (24)–(25). It replaces C_X(M) |
| ε₃ | #4.47, new #4.47-0 | ε₃ := max(1, B₀(3B₃ + 2dL))C₁′ε₁ bounds 𝒜₁ + H₁Y (Proposition 6's ε₄ plus #4.46-0) and the J-terms |
| a_y, the block norm, N_bl | #4.48 | a_y is the sum over plaquettes with initial point in y. abs(ℋ)_y is the maximum over adjacent blocks. N_bl := 3^d(2 + L^d) ≥ 3^d + 2^d + (L + 2)^d |
| per-block action bound | new #4.48.0–#4.48.0-2 | C_bd := max(48L²C₀^{ms}, 2C_hes^wL⁶), derived to first order from #C9.3.5-1 and to second order from #4.41-3. At complex points the transports have norm ≤ 2^{1/8}, which gives the factor 2 |
| C_Φ, C_{1−ζ₀} | #4.48-1, new #4.48-1.1, #4.48-3.0.2–#4.48-3.1 | the factor N_bl from the block count. Cauchy's estimate for the quadratic form is stated (#4.48-1.1) |
| δΦ, the averaging M, a_y^B, d_y, b_y | #4.51, new #4.51-0 | D is renamed δΦ. M is CMP 98 (15)'s averaging (#C9.3.1-1), not the cube parameter. The cells are those of #C9.3.3-6 |
| A′* bound (defect) | #4.51-1, #4.53-1.1 | ρ̄_u bounds A₁* only. U^A − MU^B involves A′*, whose bound is #4.38's 2C_G(ε₀)c″_K, larger for L > 2. So c_{A′} := 2C_G(ε₀)c″_K and C_σ := c_{A′}C_bd(1 + c_{A′}) + C_b |
| segment derivative | #4.51-1.1, #4.51-2, new #4.51-2.1 | ∂_tU^X = H₁𝔛, since 𝒜₁ and HD are of second order. K̃_Λ, C_{dΛ} := 8C_bdB₀, and the factor N_bl in C_Δ(M) |
| data difference | #4.53, #4.53-1, new #4.53-1.1, #4.53-1.2 | CMP 98 (159)–(163) with c_v (#C10.3.29-2). C′_Δ(M) := (1 + (π/2)c_vdB₀c_tot(1/128))C_Δ(M) + c_vc_{A′}, and c_{δD} |
| propagation (defect) | #4.54–#4.54-0.1.2 | The old "≤ C abs(δD)² at second order" had no derivation. It is now a mean-value step along D″_t := e^{itδD}D″^A, regular with ε_{D″} := (2 + 2πLc_{δD})ε₁. The 2 is because D″^A carries exp(ig_kB), abs(g_kB) < δ′_k, and 4Lδ′_k ≤ ε_k (new threshold #4.50-1.1.0-1). The weights obey w ≤ (1 + b₂ḡ²)g_{j(y)}^{−2} (#4.41-1-1), where the old text lacked the factor. C_pr := 6(2 + 2πLc_{δD})(1 + b₂ḡ²)(1 + β₀)²N_blB₀C_bd |
| run-A change of A(ζ₀, U_0) | #4.54-1 | bounded by the same propagation along V′_t, with weight g_k^{−2}ζ₀ (LFR II (1.10) carries g_k^{−2}). Each bond contributes ≤ C_prc_Kg_k^{−2}ε₁Δ. The Schwarz step and C_{ζ₀} are deleted (#4.54-1.1 removed) |
| C_A(M) | #4.55 | C_A(M) := C_prc_K((π/2)C′_Δ(M) + C_Δ(M)) |
| C_W | #4.55-0.1, new #4.55-0.1.1 | BETA Lemma 2.1(i)'s constant, as in #C5.7-7 |
| (T-Λ) | #4.50-1, #4.50-1.1, #4.50-1.1.0, new #4.50-1.1.0-1, #4.50-1.1.1-1, #4.50-1.2 | #4.48.0's conditions at the field A′* and at the propagation's regularity. CMP 98 (158). 4Lδ′_k ≤ ε_k, since δ′_k/ε_k = (A₁/A₀)(log g_k^{−2})^{p₁−p₀}. p₀(g) is named |

## Consumers outside 13a (in place)

| Line | Repair |
|---|---|
| #3.96-1-1 | V′ is the deviation from V′^X₀ (#4.152, LFR II p.378 l.12). So Y = (1/i)log V′ and ‖Y‖_∞ < ε₁/8. The old Y := (1/i)log(V′(V′^X₀)^{−1}) read V′ as absolute data |
| #4.116, #4.153, #4.157, #4.160, #4.563-1.1 | V_{Λ^c} in place of the off-Λ V_Λ. #4.563-1.1 names V_{Λ^c}(z) |
| #4.152 | V_{Λ^c}, 𝔛, e^{it𝔛}, and C(M) ≥ 8(1 + κ_s)max(M₀, C_𝔛(M)) |
| #4.154 | the bound rests on the regular data path V′e^{it𝔛}V′^A₀V_{Λ^c} and ‖𝔛‖_∞ ≤ Δ. The old "≤ C abs(δD)² at second order" is gone |
| #4.179, #4.189 | The U″_k path is regular with ε_{D″}, not 2ε₁, and its difference in the log coordinate is abs(δD) ≤ (π/2)C′_Δ. So C_E(M) := 2(2 + 2πLc_{δD})dB₀c_Kc_w(C_Δ(M) + (π/2)C′_Δ(M)) + c‴C′ |
| #4.560-1.1.2 | ‖𝔛‖_∞ ≤ C_𝔛(M)O(1)ε′_k, and C(M) ≥ 4C_𝔛(M) times that O(1) gives ≤ ε₁′/4 |

Unchanged and consistent: #4.162 (s_n, via ‖𝔛‖_∞ ≤ Δ), #4.260 (C_U ≥ C′_Δ), #4.562-1.1, and #4.177. The remaining V_Λ's (#3.80-1, #4.57, #4.111, #4.152's first, #4.155, #4.178, #4.559-1) are Bałaban's.

Pending approval: the Cauchy note's #CP.27 restates the old "C₁ := max(1, C_X(M)C_Φ(M)/κ_Λ)" as VAR's constant of (172), which is C₁′ (#4.46-0). The edit was refused by the session's permission classifier. #CP.27 is permitted background for 13a, not under review.

## The split

Rebuilt at LF 49628896d858, the packet came to 28,615 characters, over the 25k limit. The growth is from the definitions and the repairs above, not from restatement. It is split at *The comparison.* into two parts, each with its own clean count:
- **13a1**, #4.43–#4.50-2, 18,104 characters (rev lf-p13a1-20261107-r5);
- **13a2**, #4.51–#4.55-1, 10,792 characters (rev lf-p13a2-20261107-r5).

Each part names the other as permitted background. Both are built at table c6beb03f3952 and labels f93fef03e92d (verified), with 0 definition conflicts. spec_p13a_r5.json is superseded by spec_p13a1_r5.json and spec_p13a2_r5.json. They launch one at a time, on the user's go.

## Pre-check, lf-p13a1-20261107-r5

The pre-check below covers both parts.

## Pre-check, lf-p13a2-20261107-r5

- Changed in 13a: every line listed above, each re-derived (the derivations are in the table). The whole of #4.43–#4.55-1 was re-read line by line after the edits, including each inequality: the N_bl count, the Cauchy and Schwarz constants, the min(u, v) ≤ (uv)^{1/2} step, and the factors of C_pr and C_A.
- Sources re-read: LFR II p.357 l.24–48, p.358 (1.10), p.378 l.8–16; RG I p.266 (2.7)–(2.8); VAR p.300–p.301 (Sect. F, U_1 = e^{iηA}); LFR I p.183 l.2, p.184 l.18; #T3.40.
- Linear order: no forward tag citation in 13a (scripted list). Later sections are named by section (*The sum 𝐂_k.*, *The a priori location.*, *The comparison.*, *The propagation.*). #4.54-0.1's old "(#4.157)" and "(#4.158)" are replaced by a section name.
- Definitions: build_packet --check gives 0 conflicts (8 allowed: C_c, C₁, ε₃, V′_t, ε₁, ε₂, w_y, 𝔯). The new #D.w_y duplicated #4.346's tag and is now #D.w_y.c. D and C_ζ₀ are gone.
- Line lengths: 13a lines are ≤ 600 characters, except #4.43-1.1 at 608. #4.54-0 (763) was split into #4.54-0.0.
- The table rows (#T12.9, #T12.12, #T3.34, #T3.34-1, #T4.29) were sent to the table fork with derivations. The fork re-derived and entered them (table 87b4d88d2560 → 26584851201e, hash verified).
- The labeller requires "x :=" after each {#D.x}. So #D.𝔸_Z, #D.a_y(U), #D.ℋ_y and #D.a_y^B(W) now read ":= …", ε_r has its own defining clause, and #D.H_{1,k} is now #D.H_1,k. These are wording only. LF 4b36ac5dab04 → 2d368e9814ac, relabelled by the fork (LABELS 6852a49efcea, table ee0afaedcd0e, both verified). The labeller cuts tags at the first "}", so five older D-tags were renamed without braces: C_1−ζ₀(M), C₀^ms, S^in_j, ω_♮^im, and ‖·‖_Y,j′. LF → 49628896d858. The fork updated #T12.9 and #T12.11 and relabelled: LABELS f93fef03e92d, table c6beb03f3952, both verified. No label row has a nested brace.

## SHAs

- LF 0e0a28f49094 → c574de3787de.

## Status

The fork re-derived and entered C_σ (#T12.9), updated #T2.23, #T7.7 and #T8.5 for R̄, and relabelled: table 87b4d88d2560, labels 5eaa220c2f08. It noted that CC_b could be C_b. CC_b is kept, since C ≥ 1 there and it is an upper bound. spec_p13a_r5.json is built at LF c574de3787de: 21,110 argument characters, 0 definition conflicts. r5 is launched only on the user's go. 13b's r2 findings wait until 13a is done; its #4.562-1.1 is repaired above.
