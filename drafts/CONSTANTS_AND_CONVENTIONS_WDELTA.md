# Constants and Conventions of the Wilson-Loop Notes

Scope: the walk-factor note (W-δ, WILSON_IT1_WALK_FACTOR_DIFFERENCE_2026_10_28.md), the large-field note (LF, WILSON_IT1_LARGE_FIELD_DEPTH_2026_10_27.md), and the Cauchy note (WILSON_IT1_CAUCHY_ESTIMATE_2026_10_27.md). Line numbers are W-δ lines unless marked LF or Cauchy; they hold at W-δ d0c05a54a692 and LF c59222f58b91 and must be regrepped after edits. Every entry states the convention the notes use; a use that disagrees with this file is a defect of the note, not of the file. The note's own collected list of conditions is W-δ §8, *The conditions on the constants.* (l.178–188); 10.6 and §12 point to it. Absolute values are written abs(·) so that no cell contains a vertical bar.

## 1. Order of Choices

Each constant is fixed in one stage and may depend only on constants of earlier stages. A condition is legal only if it is a lower bound on a quantity of its own stage in terms of earlier ones, or an upper bound on a quantity of a later stage.

| Stage | Fixed here | Kind of condition allowed |
|---|---|---|
| 0 | d, G, and the exponents ε₀, β, β₂, β′, β″ | ranges: 0 < ε₀ < 1/125, β ∈ [3/4, 1), β₂ = (1 + β)/2, 0 < β′ ≤ min(1/60, β_o − γ_w), LF's β″ ∈ (0, 1/20] (so β_o − β″ > ½, LF (δ)); CRE's q₁ = q₀ > p₀ + 3r, q₀ an integer, within the LF note's q₁ ≥ q₀ > p₀ + 3r (LF l.15, l.700; CRE (2.28)) |
| 1 | L | lower bounds in d and G: L ≥ 4, L > 5 (so L ≥ 6), L > 2d, L ≥ 8d + 4, L ≥ 12d + 6, L² > 9d, (1 + β₀)² ≤ L with CRE's β₀ |
| 2 | Bałaban's constants that depend on d, L, G (δ₀, δ₁, B₀–B₅, PBG's a₀ and a₁, VAR's a₃, O(1) of VAR, REG, PBG, PRT2, CRE) and the derived rates and constants (δ₀′, δ_c, δ_gf′, δ_D′, δ_ι, δ_min, δ_g, δ_br, δ_br^c, κ₁, c_u, c_G, r_G, r_υ, c_d), and RG I's β_I and c₂ ((1 + 8β_I)L^{−2} ≤ 1, RG I (3.52), p.280 l.18, which covers (1 + 7β_I)L^{−2} ≤ 1 of p.279 l.28; c₂ ≤ min(1, c_*) and within the rooms of RG I's (3.13); §8, stage 2) | none; computed |
| 3 | R₀M₀, M′ = R₁M₁, K (PBG's and CRE's), M₁ = KM′ (CRE's), R, R_ι, RG II's M, λ_R | lower bounds in stages 0–2 and the sizes before it, in the order R with CRE's K, then R₀M₀, then PBG's K (hence M′ = KR₀M₀; the lower bounds on M′ are met by K large), then RG II's M (W-δ §8, stage 3; e.g. M′ ≥ R₀M₀, M ≥ 4KM′, (D2) with C_ι(M′), and Bałaban's own lower bounds on M: RG I's M ≥ M(κ), RG II's δ₀M ≥ κ and δ₁M ≥ κ₁, CRE's p.245 l.34, LFR I's δ(M/M₁) ≥ 2 at p.186 l.35 and p.200 l.14–21; δ_ιM₁ ≥ 1 for §12's tail of ι_Y; M ≥ 2dM₁ for the LF note's strip response, LF l.663 and l.667; M ≥ 2(d + 1)L²M₁ for the strip of misaligned layers, LF l.663 and l.667) |
| 3′ | VAR's a₀, a₁, a₅, and M(ε₁), which depend on R₁M₁ = M′ (VAR (166), p.304 l.21–26, l.52–54) | none; computed after stage 3 |
| 4 | PBG's α₀ (with α_J := Mα₀, LF l.237), then PBG's α₁ (RG I's α's are not here; see their row) | upper bounds in stages 0–3′ (§8, stage 4); never in terms of ε₁ |
| 5 | VAR's ε₃ first, then ε₁ (VAR's, and 10.5's fixed value), ε₁^{(1)} (O(1)C_ℒ^gB₅ε₁ ≤ ε₃/2 bounds ε₁ by ε₃) | upper bounds in stages 0–4 (§8, stage 5) |
| 6 | γ (hence ḡ, ε_k, the data parameters, ε_U^{(i)}, ϱ, ϱ̄, α_c, d̄(ω), ε₂, α₀^W, ε₄) | γ small (§8, stage 6) |

Rule 1: no condition bounds α₀ or α₁ above by ε₁, by ε_k, or by ϱ.
Rule 2: VAR's upper bound M_V ≤ M(ε₁) = R₁M₁a₁/ε₁ is read as an upper bound on ε₁ (stage 5), never as an upper bound on a stage-3 size.
Rule 3: an O(1) belongs to the stage of the result it comes from; an O(1) that depends on L is written with its L-power whenever a condition compares two L-powers (c_u = O(1)L³, the L⁵ at the index j + 1, the L⁴ of the axial-gauge input, the L⁷ of the gradient at l.553).
Rule 4: a constant that may grow with a size (C₀ and C_F carry R₁M₁ = M′; C_ι = O(1)LC_LC_F) never enters a lower bound on that size alone; either the condition is an upper bound on ε₁ (for example LC_ιε₁ ≤ O(1)M₁α₀), or the growing constants enter as a ratio bounded independently of the size (C_ι/C₀ ≤ O(1)L³C_LB₃ at l.1153, from VAR (8), whose space 𝔘_k(B₃ε₁) carries no cube factor; VAR (9)'s B₃M does, and is not used for the ratio).
Rule 5: every condition the note uses on its constants is entered in W-δ §8's list when it is written, with its source; a condition stated only where it is derived is a defect. Bałaban's own conditions that the notes rely on (lower bounds on M, the RG I and RG II smallness conditions) are entered as well.

## 2. Sizes and Integers

| Symbol | Meaning in the notes | Source | Stage | Clashes and where they occur |
|---|---|---|---|---|
| d | dimension (4 for the application; the notes keep d) | — | 0 | none |
| L | block-spin factor | RG I, CRE | 1 | none |
| a_j, a_n | L^jε, the lattice spacing of the scale j | CRE | — | a_{j(x)} is the scale of the global layer of x |
| η, ε | finest spacing; ε in the notes, η in PBG and VAR | PBG, VAR | — | L^jη of PBG = a_j of the notes |
| M′ | PBG's block size at the joins (LF reading); M′ ≥ max(M₁^{PBG}, R₀M₀, R₁M₁^{VAR}), a power of L; also the RM of the composites' layers (LF l.662–663, δ_minM′ ≥ 6c_d log L) | LF l.197 | 3 | written M in W-δ §§7–8 and 10, M₁ in §§11–12 |
| R₀M₀ | PBG's local-sequence size | PBG p.408 | 3 | R₀ a power of L, R₀ > 5dL |
| R₁M₁ | VAR's and REG's product (VAR p.277 l.12, R ≥ R₁ at l.17); equals M′ in the LF reading (R₁ = 1) | VAR, LF *R₁ = 1* | 3 | also in C₀ and M(ε₁); never ≥ CRE's M₁ |
| M₁ (default) | PBG's block size M′ | W-δ §8 l.176 | 3 | see next row |
| M₁ (CRE) | CRE's block size KM′ ≥ M′ | CRE, LF l.197 | 3 | in M₁ = KM′, §11's collar passage (from "The collar lies within 2M₁a_h", l.823), §12's collar widths, M ≥ 4M₁, M ≥ 2dM₁ and M ≥ 2(d + 1)L²M₁ (LF l.663 and l.667, §8 stage 3), and the distance M₁a_k from Y to (Y^∼)^c (l.526, l.681, l.961, l.1126–1130; LF l.542) |
| M (§§7–8, 10) | PBG's block size KR₀M₀ = M′ | PBG p.408 l.28 | 3 | written M₁ in §§11–12 |
| M (§§11–12) | RG II's cube size; also in C_U(M), (W-M), and §12's ε₁ bounds with M⁵, M⁶ | RG II | 3 | not VAR's M_V; not PBG's M |
| M_V | VAR's cube parameter (VAR writes M), a multiple of R₁M₁ with M_V ≤ M(ε₁), chosen per cube, a union of big blocks | VAR p.279 l.2, l.17, l.28 | per cube | values used: R₁M₁ and 3LR₁M₁ (§11 axial gauge), 7M′ (§12, l.1003 and l.1010), R₁M₁ (l.1051) |
| M′_V | VAR's own M′ := M/(R₁M₁) | VAR p.300 l.30, p.304 | — | LF only; not the block size M′ |
| K (PBG) | integer in PBG's M = KR₀M₀, a power of L, K ≥ 4 | PBG, W-δ §§7–8 | 3 | collar cells as well |
| K (CRE) | integer in CRE's M₁ = KM′, a power of L, K ≥ 12d + 1 | LF l.197, W-δ l.930 (the block size), l.932 (the contraction) | 3 | §12's band regularity (block size, contraction, chains) |
| K (VAR) | the notes' name for the coefficient of VAR's (165), K := B₀(C₄ + 4C₂)(36dL²B₁)², printed with the factor (R₁M₁)²(M′ε₀)², VAR's M′ = 1 for the cubes of size R₁M₁ | VAR p.304 l.17–19, W-δ l.176, l.931 | 2 | in θ and in 4KM′²B₃ε_U^{(i)} ≤ ½L^{−3} (stage 6); not CRE's or PBG's K |
| K_T | max{1, (2/(eδ′M₁))²}, δ′ := min(δ_ι, ⅛δ₁); the tail of ι_Y against ι away from X | W-δ §12, the W_0 bullet of *§11's oscillation at U_{1,2}* (l.945) | 3 | a constant of L and δ₁ under δ_ιM₁ ≥ 1 and (F-ι); K_ℬ ≥ O(L)K_T |
| K (LF scale) | the final scale k_s + j(C) | LF | — | only where named so |
| K_ℬ | constant of §12's bootstrap, depending on d, L, δ₁, and δ_ι, K_ℬ ≥ O(L)K_T ≥ 1 | W-δ l.176, l.980, l.984 | 3 | not PBG's, CRE's, or VAR's K |
| R | walk-problem separation of PRT2 (2.2); R ≥ 12dL | PRT2, W-δ §7 | 3 | covers R ≥ 8dL and R ≥ (2d + 1)L; REG's R > 4dLR₁ at R₁ = 1 holds by it for the walk problems and by R_ι = 4dL + 1 for the lift |
| R′ | LK − 1, the global layers' width in units of M′ | LF l.197 | 3 | R ≥ 12dL at the joins reads R′ ≥ 12dL, i.e. K ≥ 12d + 1 |
| R_ι, R₁ (lift) | R_ι = 4dL + 1 and R₁ = 1 for the lift's one-step problem | VAR p.300, REG p.098 | 3 | not the R of the walk problems; used in M₁(L − 1 − R_ι/L) > 3 (l.526) and M₁(L/3 − 1 − R_ι/L) > 3 (l.961) |
| R_k | CRE's R_k = least power of L with R_k ≥ (log g_k^{−2})^r, so R_k ≥ L for small g | CRE (2.5), p.255 l.36–39 | 6 | the collar cells' fit uses R_{h+1} ≥ L (l.1010) |
| λ_R | K_RM + 1, K_R ≥ 4B₃²O(1) (RG I p.277 l.54) and K_R ≥ O(1)(1 + B₃O(1)) with the largest O(1) of RG I p.285 l.17, p.285 l.23, and p.280 l.44 | W-δ *Analyticity and bounds.*, l.1092 | 3 | C₁ = λ_RC₀ of CRE (2.28) |
| h₀ | least integer with L^{h₀} > max(2M₁/M, L(d + 1)) | W-δ l.171 | 3 | — |

## 3. Exponents and Small Parameters

| Symbol | Meaning | Source | Stage | Clashes and where they occur |
|---|---|---|---|---|
| ε₀ (exponent) | exponent in γ_w, C(ε₀), δ^f_j, and the LF note's d̄; 0 < ε₀ < 1/125 | W-δ §8 (stage 0 of the list, and the paragraph on the consumer's exponent), LF l.643, l.674, l.775–776 | 0 | VAR's ε₀ = α₀ in §11's comparison with VAR; VAR's bound (2) in §12's *The band regularity of U_{1,2}.*; VAR's 𝔘-parameter of (19) is written ε₀^𝔘 in *10.5's premise at 𝐇″_k.* and §12's field bound (W-δ l.176); CRE's ε₀ and δ₀ = (A₁/A₀)ε₀ (CRE p.247 l.50) are quoted in §12's *No loop through M* (W-δ l.1105); VAR's ε₀ = α₀ also at W-δ l.1168; the LF note's (ii) and its threshold n₀′ need ε₀ < 1/125; γ_w > 1/4 and the consumer's exponent need ε₀ < 1/4; §12 needs only ε₀ < 2/5 |
| β | Hölder exponent of (Wδ-1); β ∈ [3/4, 1) | W-δ §8, l.986 | 0 | §12's bootstrap needs β > (1 − ε₀)/3; the consumer needs β ≥ 1/2; LF (δ)'s complex-point current bounds need β_o − β″ > ½ |
| β″ (LF) | crude lattice Hölder exponent of the second differences in LF (δ), β″ ∈ (0, 1/20] | LF (δ), *Where the current enters.* | 0 | LF (δ)'s exponent c_J := (2(β_o − β″) − 1)/3 ≥ 2/15 (not W-δ l.126's constant c_J of the pair path); β″ is not §11's β′ nor the W-δ l.618 β″ |
| β₂ | (1 + β)/2, the exponent of (3.43) for G^A | W-δ 10.5, 10.6 | 0 | — |
| β′ (§11) | 0 < β′ ≤ min(1/60, β_o − γ_w), β_o := min(β, 1 − 2ε₀) | W-δ l.179, l.986 | 0 | not the Cauchy note's β′ (19/40) |
| β′ (Cauchy, LF) | the age exponent, β′ := ½min(β_H, 1 − β_E) ≥ 19/40, β_H ≥ 19/20 the Hölder index of the class bound (5.1c); β′ ≤ ½ | Cauchy l.106, l.966; LF l.672–677 | 0 | not W-δ §11's β′ (≤ 1/60); the LF note's (iii) and the consumer write γ_H − 4β′ with W-δ's β′ |
| β_E | the small positive exponent of CRE (3.67) and of the irrelevant terms O((L^jL^{−n})^{5−β_E}) (CRE p.281 l.44–45, "where β is a positive number"; p.283 l.31), fixed ≤ 1/20; CRE Theorem 2's (2.43) exponent is 1 − β_E ("for β<1", p.263 l.19–21, E₁ depending on it) | Cauchy l.106; LF l.672 | 0 | CRE writes it β; not the Hölder β of (Wδ-1), not RG I's β_I, not CRE's β = 1/8 of the κ row; β_E ≤ 1 − β′ holds |
| θ_V, θ̃ | θ_V := β′/(2(4 + β′)) (≈ 0.053 at β′ = 19/40), θ_V < β′/8; θ̃ := max((1 + θ)/2, L^{−γ_H}, L^{−(1−2ε₀)/3}, L^{−(1−ε₀)/4}, L^{−θ_V/8}) | Cauchy l.257, l.966; LF l.673–677 | 0 (θ̃ after L) | the composites' configuration sum carries (1 − L^{−(β′/2−4θ_V/3)})^{−1} (LF l.674) |
| α₀ | PBG's regularity parameter of (3.35)–(3.36) | PBG p.396 | 4 | VAR's ε₀ = α₀ (VAR p.280 l.51–52); §12's bootstrap places W_s in the one-step class at its own α₀^W (its row), not at this α₀; PBG's smallness of Mα₀ (p.396 l.32; used in Theorem 3.12, p.423 l.34, and at p.428 l.28) read at 2Mα₀ for the terms on LF's 𝒟^c (stage 4, l.186) |
| α₀^W | §12 bootstrap's class parameter, α₀^W := O(1)d²L²C₀′ε₁, γ-dependent | W-δ §12 *The bootstrap.* (*The class.*) | 6 | O(1)L⁵M′α₀^W ≤ a₁/2, and α₀^W below the absolute constant of PBG Theorem 3.12's "α₀ sufficiently small" ((3.138), p.423 l.29–30, l.34), both at stage 6 |
| ω | §12 bootstrap's weight, ω(c) := min{(a_{j(c)}/ε)², e^{⅛δ₁d_ε(c,Y)}}, 1 ≤ ω ≤ (a_{j(c)}/ε)², ω ≤ e^{δ₁/4} within 2ε of Y | W-δ §12 *The bootstrap.* (*The weight.*) | — | not a parameter; the rate ⅛δ₁ is one of the three parts of 10.5's kernel rate ½δ₁ (*The layers.*) |
| α₁ (PBG) | PBG's complex-domain parameter of (3.37); PBG has no α₂ | PBG (3.37), p.396 l.38 | 4 | α₁ at complex backgrounds in O(1)C_D(L⁵M₁α₀ + α₁) ≤ ½ |
| α₀, α₁, α₂, α₃ (RG I) | in §12's ratio of (D2): CRE's α̃_{0,k} = g_kC₀(log g_k^{−2})^{q₀} and α̃_{1,k} = λ_Rα̃_{0,k} (q₁ = q₀, an integer > max(1, p₀ + 3r)), with CRE's C₀, C₁; α₂ := c₂α̃_{0,k}, the radius of (3.14) (rooms ½α₀, ½α₁, (1 − L^{−3})α₀ of (3.13)); α₃ := β_IL^{−2}α̃_{0,k}/(2B₃) of Lemma 4 (B₃α₃ < ½α₁, 2B₃α₃ ≤ β_IL^{−2}α₀, p.280 l.6, l.16); O(1)α₂ ≤ α₃ by c₂ ≤ c_* (p.279 l.44–49); c₂ ≤ (43B₃(4C_δ(ε₀)L^{7/3} + C_{Q*}(1 + 3C_φ)))^{−1} for the t_□ part of the decoupled scale-j field, whose entries on the circle (3.15) are ⅓α₂ (p.273 l.9–11), and its part C_φα₂ of the gauge-fixing addition D_Aφ_A (C_φ = O(1)(1 + B₀)B₀, LF (δ)), α₂ = c₂α_{0,j} for a term of index j (LF (δ), the lift half's *The conditions.*; W-δ §8, stage 2); the same definitions as the Cauchy note's (its l.161, l.163, l.966) | CRE (2.28) p.259 l.45–50, RG I p.262 l.37, p.272 l.27–41, p.279 l.44–49, p.280 l.6, l.16, W-δ l.1092 | values at 6; c₂ at 2; λ_R at 3 | not PBG's α₀, α₁; CRE's C₀, C₁ are not the Cauchy note's C₀ or VAR's C₁; β_I is RG I's class parameter β, not the Hölder β; a term of index j < k has CRE's α_{i,j}, and the ratio α̃_{i,k}/α̃_{i,j} ≤ (1 + β₀)²(k − j)^{1/2} is paid by the factor L^{j−k} kept in the comparison ((3.51) drops it; l.1092), under (1 + β₀)² ≤ L |
| γ₀ | RG I's bound on 𝐉 in U_j^c (γ₀ = α₀, RG I p.263 l.2–3); LFR II's constant of (1.7) and (1.9) (p.358 l.4, l.20) | RG I, LFR II | — | two meanings; W-δ l.1080 and §8 use LFR II's; l.1093 uses RG I's |
| α_J, α_*′ | α_J := Mα₀, the pair class's current bound (LF l.237), fixed with α₀; α_*′ := min(α₁, α_J/c_J) | W-δ l.126, LF l.237 | 4 | its conditions 2B̄_Jε₁ ≤ α_J are upper bounds on ε₁ (stage 5) |
| α₁^A | 4L²(C_L + 1)(c_uMα₀ + α₁), run A's complex-domain size | W-δ 10.1 | 4 | not the amplitude of the B″ chain (that is α_c) |
| ϱ, ϱ̄ | ϱ = c_ρα_m, the size of the joint line's moves; ϱ̄ := sup over Y^∼ | LF *The joint line.*, W-δ l.551 | 6 | ϱ ≤ O(1)α₁^A/L kept |
| α_c | C_cϱ̄, the size of B′ at the points c(t) | W-δ l.551, l.639 | 6 | amplitude of the B″ chain |
| ε₁ (VAR) | VAR Theorem 1's data parameter of (7), abs((∂V)(p′) − 1) < ε₁ on 𝔅_k; the minimiser lies in 𝔘_k({Ω_j}, B₃ε₁) of (8); ε₁ ≤ a₁ (VAR's a₁) | VAR p.278 l.35–38, p.279 l.11–15 | 5 | the a₁ here is VAR's |
| ε₁ (10.5) | a fixed admissible value between the data parameter and a₁ | W-δ l.605 | 5 | monotone admissibility in VAR Theorem 1 |
| ε₁^{(1)} | the ε₁ of 10.5's one-step problem at 𝐇″_k, also serving VAR (9) for V₀ | W-δ §12 *10.5's premise at 𝐇″_k.* | 5 | fixed after α₀, M′, and K, before γ |
| ε_U^{(i)} | the data bounds of U_i's problems (𝐁₁, 𝐁₂), ε_U^{(i)} ≤ O(1)B₃²B₅M⁶ε_k; γ-dependent; REG membership of U_{1,2} at L³B₃ε_U^{(i)} | W-δ §12 *The band regularity of U_{1,2}.* | 6 | 4KM′²B₃ε_U^{(i)} ≤ ½L^{−3} and ε_U^{(i)} ≤ ε₁^{(1)} for γ small (stage 6), the latter so that stage 5's O(1)L³B₃ε₁^{(1)} ≤ α₀ covers the collar's (3.35) for U_{1,2}; not 10.5's fixed ε₁^{(1)} |
| ε₃ | VAR's parameter of (50)–(51) and (186)–(190) | VAR, W-δ §11 | 5 | — |
| ε₄, C_♯ | VAR's ball parameter of (115), 2B₀C₁B₃ε₁ ≤ ε₄ ≤ a₄, taken as ε₄ := 3B₀C₁B₃ε₁, the value VAR's Proposition 6 prints, at the data parameter of (9.2); C_♯ ≥ 1 the constant of L and d that contains the enlargement of (3.47) for 𝔊 in §12's shifted norm and the O(1) of the single-argument bound | VAR p.294 l.59–60, p.295 l.2, l.20, l.42, l.45; W-δ §12 *The base at the layer j.* | 6 | 4C_♯B₀C₄ε₄ ≤ ½ and ε₄ ≤ a₄ (stage 6); for run B's terms of (1.60) along LF (iii)'s k-field segment, 2B_T′C₁B₃ε₁ ≤ a₄ at B_T′ := (3/2)B_T (stage 6, l.188) |
| data parameters | O(1)B₃²B₅M⁶ε_k (*The background pairs.*), B₅M⁵ε_k (*The collar of 𝐁₁.*), and the LF alignment's max of these and C(M)R_kε_k | W-δ §8 l.176 | 6 | written "the ε₁ of §12" in §8 l.176; each is at most the fixed ε₁ for γ small |
| ε₂ | second band parameter; ε₂ ≤ B₁(O(1)B₃³B₅M⁶ε_k + C₁ε₁) | W-δ §12 | 6 | RG II's ε₂ of (1.13)–(1.14) is a different parameter |
| ε_k | g_kp₀(g_k) = A₀g_k(log g_k^{−2})^{p₀} ≤ Cḡp₀(ḡ) | CRE (2.4), (2.6) | 6 | k-independent through ḡ |
| a₀ (PBG) | PBG Theorem 3.1's threshold, Mα₀ ≤ a₀ | PBG p.397, Cauchy l.440 | 2 | not VAR's a₀ |
| a₀ (VAR) | VAR's threshold; α₀ ≤ a₀ at α₀ = ε₀ | VAR p.279 | 3′ | not PBG's a₀ |
| a₁ (PBG) | threshold of PBG Corollary 3.5 and Theorem 3.4; in O(1)L⁵Mα₀ ≤ a₁/2 (Corollary 3.6 at the real U₀, halved so that 10.5's O(1)L⁵M(α₀ + O(1)LB₅ε₁) ≤ a₁ follows with O(1)L⁶MB₅ε₁ ≤ a₁/2, l.575), α₁^A ≤ a₁/2 (l.209), B₅ε₁ ≤ a₁/2, B₅ε₁^{(1)} ≤ a₁/2; the last three halved for 10.5's Cauchy polydisc of radius (a₁/2)(L^jη)^{−1} about the real points (l.575; analyticity on (3.37) by PBG p.406 l.21–22) | PBG | 2 | not VAR's a₁ |
| a₁ (VAR) | threshold of VAR Theorem 1; in ε₁ ≤ a₁/7, ε₁ ≤ a₁/(3L), M(ε₁) | VAR p.279, p.304 | 3′ | not PBG's a₁ |
| a₃ (VAR) | threshold of VAR Proposition 4, ε₃ ≤ a₃; a constant of d and L; in 2ε₃ ≤ a₃ (the Cauchy estimate of (186)) and RG II's ε₂ ≤ a₃ | VAR p.292 l.50, RG II p.5 l.40, W-δ l.187–188 | 2 | the radius r_V of (D1) includes VAR's radius of Propositions 4 and 6 |
| γ, ḡ | the coupling-side small parameter and CRE's bound on g_k | CRE | 6 | — |
| κ (Bałaban) | the decay rate of the inductive bounds, large at fixed β, Bałaban's order (CRE p.260 l.27–28, stated for κ₀ "similarly as κ"); also ½βκ > c_dom, c_dom the growth rate of the number of domains X ∋ z in d_k(X), for the remainder e^{−½βκd_k(X)} of the counterterm pieces at j = k | CRE, LF l.617 | — | CRE's β = 1/8 here (LF *The choice β = 1/8, checked.*), not stage 0's β |

## 4. Derived Constants

| Symbol | Definition | Source | Depends on |
|---|---|---|---|
| c_u | O(1)L³, the constant of (3.35) on □̃⁵ at the index j (O(1)L⁵ at the index j + 1) | W-δ l.211, §7 l.139 | d, L |
| c_π | the constant of Δ′_π in (3.131) (PBG prints O(1)Mα₀), containing M₁ and c_u | W-δ l.574, l.812 | d, L, M₁ |
| C₃ | constant of the Δ^{(2)} factors, O(1)C₃Mα₀, containing c_u | PBG p.422 l.50–52, W-δ l.789 | d, L |
| C₀ | 4R₁M₁(B₃ + B₄(1)); grows with M′ (CRE's C₀ of (2.28) in l.1092 is a different constant) | Cauchy (9.2) l.452 | stage 2, R₁M₁ |
| C₀′ | C₀′ε₁ := K_ℬ(C₀ + C(ε₀))ε₁ + C_ℬC(β₂)ε₂; for the base at the real points of LF's class at the full radii, C₀^c, the same with the target's and the base's parameters both at most O(1)ε₁″, ε₁″ = C(M)ε′_k the parameter of VAR's classes there, a constant of M and the stages (LF l.493, l.502, l.782) | W-δ l.169, l.980 | as listed; O(1)C₀^cε₁″ ≤ 1 at stage 6 |
| C₁ | five distinct constants under one letter: VAR (14)'s absolute C₁ (C₁ = L³ near the cut); CRE (2.28)'s C₁ = λ_RC₀ with CRE's C₀; CRE (3.43)'s C₁ of the fluctuation domain abs(A) < C₁p₁(g_k) (p.276 l.29–31), which the print does not tie to (2.28) and which l.1102 treats through the margin α₃ for γ small; RG II's absolute C₁ (p.6 l.54–57, p.7 l.9; l.1102 and §8, stage 6); 10.1's first-order Taylor constant in abs(𝔡v − QIv) ≤ C₁ε abs(∇_Av) + … (l.517); 10.5's one-step constant is written C₁^{(1)} | W-δ l.18, l.517, l.853, l.1102 | L (VAR's); M (CRE's) |
| C(ε₀) | the Cauchy note's constant of §9.7–9.8; it absorbs C_ιe^{δ_ι(R_ι/L + 2)M₁} (the Cauchy note writes the tail rate δ₀ and R), so it grows with M₁ and enters no lower bound on M₁ (rule 4); C(ε₀, δ_ιM₁) := 2C(ε₀)/(eδ_ιM₁) ≤ C(ε₀) under δ_ιM₁ ≥ 1 | Cauchy l.541, l.544, W-δ l.943, l.946, l.959 | ε₀, d, L, M₁, R_ι, and M′ through C_ι |
| C_F | the one-step lift's curvature constant, abs(F) ≤ C_Fε₁/a² on X^∼; C_F ≤ O(1)L²B₃C₀ by VAR (8) and p.278 l.5 | Cauchy l.540, W-δ l.1153 | d, L, C₀ |
| C_ι | two uses (l.176): O(1) of PBG (3.133) (l.510); O(1)LC_LC_F of the Cauchy note's §9.8 (l.541) in the tail bounds of T, C_ιε₁ ≤ min(α₁, Mα₀), and the bridge; C_ι/C₀ ≤ O(1)L³C_LB₃, independent of M′ (l.1153, VAR (8)) | W-δ l.510, l.835, l.1153; Cauchy l.540–541 | stage 2 and C₀, hence M′; the ratio C_ι/C₀ only d, L |
| c_G, r_G | Lie-algebra constant and the radius of the BCH and logarithm series | W-δ l.211, l.231 | G, L |
| c_F | c_F ≥ 8L³(c_u + 1)/r_G | W-δ 10.4 | G, L |
| C_c | the larger O(1) of the two bounds on B′ | W-δ l.551 | stage 2 |
| C_tel | max(3, (5/2)(c₁ + c₂)), c₁ the total weight of Q₁ and c₂ the constant of the slot map; the LF note writes them c_Q and c_s | W-δ l.153, LF l.651 | d, L, lift constants |
| C_ℬ, C_ℒ, C_ℒ′, C_ℒ″ | C_ℬ := O(1)L^{3+β₂}C_ℒ″(1 + C(β₂)), §12 bootstrap's own constant, depending on M′ through C_ℒ″ ⊃ C_ι; C_ℒ: block-sum bound of the lift; C_ℒ′: 10.1's constant; C_ℒ″ ≥ 1: the constant of §12's *The terms.*, containing O(1)L⁴ and C_ι of *The normalisation.*, K_M := e^{δ₁/2}max{1, (72/(eδ₁M₁))³} of *The collar.* (a constant of L and δ₁ by (F-ι)), the constant of the sum over c in *The layers.* and that of the crude part's sum at the rate ¼δ₁ in *The collar.*, and the factor L² between the units of F and of the first differences | W-δ §5, 10.1, l.980 | C_ℬ is not 10.1's C_ℒ′ |
| δ_g | min(δ₁, δ₁′), RG II's geometric constant | W-δ l.824 | not PBG's rate δ₁ of (3.132) |
| δ_min | min(δ_π/4, δ₀′/(54L), δ_gf′/(6L), δ_D′/(12L)) | W-δ l.820 | stage 2, L |
| δ_br, δ_br^c | the bridge's rates at the real and the complex chain configurations | W-δ §11, l.681, l.696 | stage 2 |
| δ₀′, δ_c, δ_gf′ | δ₀′ = min(δ₀, ¼δ_Q, ¼δ₁, ¼δ_c); δ_c := (1/16)min(δ_V, δ₀, δ₁); δ_gf′ = min(δ₀/486, δ₀′) | W-δ 10.6 l.650 | stage 2 |
| κ_V, κ_ℋ | κ_V = O(1)B₀C₄C_ℒ^g(B₅ + B₀C₁B₃)ε₁ (§11's contraction); κ_ℋ := O(1)c_G(1 + C_ℋ)ϱ̄ (§11's bridge) | W-δ §11 | ε₁; ϱ̄ |
| c_d | 2d(3^d + 1) | W-δ §8 l.184 | d |
| γ_w, γ_H | γ_w := min(β, (1 − ε₀)/3); γ_H := βγ_w/(1 + β); γ_H − 2β′ for the fixed points; γ_H − 4β′ in the LF note's (iii), with ϑ̂_H := L^{β′k}ϑ_H, and the consumer's condition (γ_H − 4β′)/2 > θ_V/8 | W-δ §8, l.18, l.179, l.190; LF l.652, l.655, l.657 | β, ε₀, β′ |
| C_w | the constant of δ_w(ω) ≤ C_w(ε/a_{m(ω)})^{γ_w}, l.161 plus C_w^{(11–12)} of l.167 | W-δ §8 | stages 0–5 at k-independent bounds |
| c₀(α), c_tot(α) | c₀(α) := Σ_{z∈ℤ}e^{−αδ₀abs(z)} < 4/(αδ₀); PRT2's count (2.58) at α gives 6c₀^d(½α), so c₀(⅛)^d at α = ¼ and c₀(¼)^d at α = ½; c_tot(α) := 26c₀^d(½α) | LF l.184, l.663 | δ₀, d |
| d̄, d̄_j | d̄(x) := C_U(M)(ε/a_{min(j(x),n)})^{(1−ε₀)/3}ε₁, n the birth scale; at the composites of the generation j, d̄_j with j(x) = j, in the units a_j | LF l.236, l.526, l.674 | C_U(M), ε₀, ε₁ |
| C_U(M) | 4C_G(ε₀)c″_K + 2B₀c_KC′_Δ(M) + C_T; enters only upper bounds C_U(M)ε₁ ≤ const (stage 6) and divisors (x₃, x₄, C″, c_∂, C″_∂) | LF l.236 | ε₀, M, stage 2, C_T |
| C_s, C_T | C_s := C_ℒL⁹B₃ + dL⁵(C_F + L²B₃), the strip sources' size by VAR's class (8) up to ∂□₀; C_T := O(1)B₀c₀(⅛)^dL^{24}C_s, the strip constant | LF l.663 | d, L, B₀, B₃, C_ℒ, C_F (hence M′) |
| C_TJ, x₄ | C_TJ := O(1)B₀C_ℒ′c_λc₀(⅛)^dL^{33}B₃, the bound of the term (IV); x₄ := C_TJ/C_U(M), added to x̂_ν at the composites; Ĉ_J′ the members' Ĉ_J with x̂_ν + x₄ | LF l.663, l.666 | d, L, B₀, B₃, C_ℒ′ |
| C_r′, C″ | C_r′ := O(1)sup_{x≥1}P(Lx)e^{−δ₀Mx}; C″ := C_r′sup_{n≥0}L^{(n+1)/3}e^{−δ₀ML^n}/C_U(M), the strip response at the composites and the representation configurations | LF l.663, l.667 | d, L, M, δ₀, C_U(M) |
| c_∂, C″_∂ | c_∂ := 2(C + C_T)/C_U(M), the coarse bound on the collar of 𝐁(Y_i); C″_∂ := max(1, c_∂)C(ε₀) + CL³B₃/C_U(M), the run difference at the near domains at ∂Y_i | LF l.670–671 | C(ε₀), C_T, C_U(M), L, B₃ |

## 5. Conditions

The full list, by stage and with its sources, is W-δ §8, *The conditions on the constants.* (l.178–188). It is not copied here, so that it exists once. When a derivation adds or changes a condition, the condition is entered there in its stage, and the derivation states it where it arises (rule 5).

## 6. Conventions

- Distances: ℓ∞ unless stated; an ℓ¹ separation s gives an ℓ∞ separation ≥ s/d, and the factor d is absorbed by R ≥ 12dL.
- Layers: run A's layer j is run B's layer j + 1; a_{j(x)} is the scale of the global layer of x; on run A's shell n, a_{j(x)} ≥ L^nε except on the innermost local shell (factors L and L²).
- Units: F and its first differences carry ε^{−2} times the dimensionless differences of the link variables; B′ and ε₂(ε/a_j)² are dimensionless.
- Cubes: □̃^k is □ enlarged by k layers of blocks of its own size; a cube of side 2M′ has □̃⁵ of side 12M′; VAR's class cube of parameter M_V has side 2M_Va_j, is a union of big blocks (aligned to the grid), and its test cube adds 2R₁M₁a_j on each side (side (2M_V + 4R₁M₁)a_j). Aligning a cube to the grid costs at most one block per side.
- CMP98 (15): the block average is an average over the L^d contours Γ_{c,x} of the logarithms of the closed-contour factors; each contour has at most L + d(L − 1) ≤ (d + 1)L fine bonds.
- Citations: transcription line numbers count the \pagemark line as l.1; in *_corrected.tex, file line = print line. REG (CMP 99) has no *_corrected files, and its pages open with a "%" line before the \pagemark, so a REG pin is the file line minus 1 (REG p.077 l.31 for "the following spaces of regular field configurations", file line 32). Bałaban by page and line (verification/BALABAN_LINE_PINS.md). Quotations of Bałaban's smallness are his words (p.396 l.32: "O(1)Mα₀ is still a sufficiently small number"), not glosses such as "absolute threshold". PBG p.422: the series quote at l.12–13, the (QGQ*)^{−1} remark at l.15, (3.132) at l.17–21, the Δ^{(2)} bound at l.50–52.
- PBG's printed O(1)Mα₀ is read as c_uMα₀ at the index j and O(1)L⁵Mα₀ at the index j + 1 wherever it comes through (3.35); the current bounds O(1)Mα₀a^{−3} are harmless since §11's O(1)L⁴C₀ε₁a^{−3} ≤ α₀a^{−3} implies them.
- c^A: the complex coarse point Mc(t) from l.551's "write c^A = V′V₀" to the end of the B″ bullets; its value at t = 1 is the real member V₀ = Mι_Y(V₀), where B′ = 0.

## 7. Implications Between Conditions

- R ≥ 12dL implies R ≥ 8dL, R ≥ (2d + 1)L, and, for the walk problems, REG's R > 4dL at R₁ = 1 (for the lift, R_ι = 4dL + 1 meets it by its choice); at the joins it is K ≥ 12d + 1, which implies the reach's K ≥ 10d + 1 and the lift's K ≥ 4d + 1.
- L ≥ 12d + 6 implies L ≥ 8d + 4; with M₁ ≥ 4 it gives M₁(L/3 − 1 − R_ι/L) > 3 (l.961) and M₁(L − 1 − R_ι/L) > 3 (l.526).
- M ≥ 4M₁ with CRE's M₁ = KM′ implies VAR's M ≥ 4R₁M₁, since R₁M₁ = M′ ≤ KM′.
- ε₁ ≤ a₁/7 makes M_V = 7M′ admissible (M(ε₁) = M′a₁/ε₁ ≥ 7M′); ε₁ ≤ a₁/(3L) makes M_V = 3LR₁M₁ admissible and, for L ≥ 3, implies ε₁ ≤ a₁/7 wherever the same ε₁ is meant.
- O(1)L⁴C₀ε₁ ≤ α₀ implies the current bounds O(1)Mα₀a^{−3} wherever PBG prints them, and, at α₀ = ε₀, VAR's B₃ε₁ ≤ ε₀ since C₀ ≥ 4R₁M₁B₃ ≥ B₃.
- The conditions of 10.3 and 10.4 on R₀M₀ imply those of the compositions (Comp).
- L > 5 with R_{h+1} ≥ 1 gives 4LR_{h+1} ≥ 24; with R_{h+1} ≥ L (CRE (2.5), small g) it gives 4LR_{h+1} ≥ 144.

## 8. Cube-Fit Budgets on the Collar

Distances in units of a_h from the cut; M₁ is CRE's KM′; the band's boundaries are at ≥ MR_{h+1}a_{h+1} ≥ 4LR_{h+1}M₁a_h ≥ 24M₁a_h under M ≥ 4M₁ and L > 5.

| Fit | Object and side | Reach from the cut | Margin to the band's boundary | Where |
|---|---|---|---|---|
| collar cell | Q̃² inside Q̃⁵, side ≤ 20M₁a_{j′} | ≤ 22M₁ | ≥ 2M₁ | l.823 |
| PBG cube | □̃⁵, side 12M′a_{n′} | ≤ 10M₁ | ≥ 14M₁ | l.1003 |
| VAR cube for □̃⁵ | M_V = 7M′ (grid-aligned, beyond □ by ≤ 8M′a_h), test cube adds 2M′ per side | ≤ 14M₁ | ≥ 10M₁ | l.1003 |
| VAR cube for Q̃² | M_V = 7M′ (contains Q̃² by the scale-j_Q alignment), test cube side 18M′ | ≤ 40M₁ | ≥ 104M₁, using R_{h+1} ≥ L (CRE (2.5)) and L ≥ 6 | l.1010 |
| REG's Sect. F margin | 18M₁a_h + 2R₁M₁a_h ≤ 20KM′a_h | ≤ 20KM′ | ≥ 4KM′ | l.924 |
| VAR cubes in Λ | M_V = R₁M₁, test cube in the ℓ∞-ball of radius 4R₁M₁a_k | ≤ 4R₁M₁ from x | ≥ (M − 4R₁M₁)a_k from Λ^c | l.1051 |

## 9. Checks Before Each Packet

- Grep for the canonical strings of Sections 2–4 and for their known stale variants: "4R₁M₁" (only VAR's own M ≥ 4R₁M₁ at l.1051 and its implication in §8), "M_V ≥ 6M₁", "a₁/15", "R ≥ 8dL" (allowed only as covered by 12dL), "K ≥ 10d + 1" (only the reach), "α₁^A" in the B″ chain, "O(1)Mα₀" through (3.35), "B₄(1)M_V", "absolute threshold", "lower bound on M" next to C_ι, "R/L" without R_ι, and pointers to lists other than §8's ("listed with §12", "listed at the end of §12", "listed in 10.6", "collected in 10.6", "as in 10.6", "listed among §12's conditions", "§12's own list"), "leaves free" for an exponent §8 fixes, "uniformly in M′" next to VAR (9), "B₅ε₁ ≤ a₁" or "B₅ε₁^{(1)} ≤ a₁" without the halving, "min(α₂", "α₂^{RG I}", "R₁M₁ for RM" and "RM = R₁M₁" at the composites (M′), "c₀(¼)^d" in a count at α = ¼, "VAR (10)" or "VAR (9)" next to ∂□₀ or ∂Y_i (the class (8) there), "5−β)" for the irrelevant terms (β_E), "C″d̄" at the near domains at ∂Y_i (C″_∂), and "for M large" (RG I's α₂ and α₃ are the Cauchy note's, and the lower bound on M is (D2)), and "≪" in place of a stated condition.
- Sweep the note for conditions not in §8's list: grep "under ", "log L", "lower bound", "upper bound", "for γ small", "for α₀ small", "≤ ½", "≤ 1", "≪", "halving", and "sufficiently small" outside l.178–188 and check each hit against the list (rule 5); conditions named collectively in the list ("the conditions on ϱ̄ of §11") are spelled out there one by one.
- For each reason given for a bound, check that the cited display states it (a source that bounds a constant is quoted with its page and line, not described).
- For each symbol taken from a cited paper (α₀, α₁, α₂, ε₁, C₀, C₁, M, K), check which paper's object it is at that place and whether it is fixed or γ-dependent; a relation between γ-dependent thresholds is homogeneous and is not entered as an upper bound of stage 4. Any suspected clash is settled against the source before launch, never left for the referee.
- Run every check of this section on the final hash immediately before the packet is built.
- For each new or changed inequality, record its stage and kind (Section 1), check rules 1–5, and enter it in W-δ §8's list.
- For each new constant, add a row here before using it in a note; for each new use of M, M₁, K, ε₁, ε₀, a₀, a₁, C_ι, R, or c^A, check its meaning against the rows above.
- For each new cube fit, add a row to Section 8 with the side, the reach, and the margin.
