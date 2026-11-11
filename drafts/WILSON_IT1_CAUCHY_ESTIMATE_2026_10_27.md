# The Cauchy Estimate Across Cutoffs: Matched Terms, Age Decay, and the One-Step Inequality

{#CP.1} For a loop C on the fixed torus, the renormalised Wilson-loop expectation F_K(C) at cutoff K (#C1.2) satisfies |F_{K+1}(C) − F_K(C)| ≤ a_K with Σ_Ka_K < ∞ (#C7.1), so F_K(C) converges along the full sequence of cutoffs (`WILSON_IT1_CONTINUUM_LIMIT_CLOSURE_2026_10_26.md` (8.4)).
{#CP.1-1} The two runs are compared at the stopping lattice, term by term of Bałaban's representation CRE (2.18), through one one-step inequality (G) (§8), the lattice-artifact estimates (§§9–10), and the relative weight of the large-field terms (§11).

{#CP.2} **The input (LF) (§6.2, §8.6).** For a history born at a scale n > k/8, so that its scales m are all ≥ n, the run-dependence of the ingredients (β) and (γ) below is to change a term by at most (exp(Σ_XΣ_mC_Ms^{LF}_{n(X)}L^d|Z_m ∩ X|_m) − 1) times its majorant, |Z_m ∩ X|_m the number of scale-m points of the component's history at the scale m, n(X) the birth scale of the component X, and s^{LF}_n ≤ C_hθ̃^n: one bound per point of the history, at its birth scale.
{#CP.2-1} It is asked in two forms: (LF-1), for the young matched pairs of §6.2, against the majorant of (11.1) built from Bałaban's bound (1.79), run A's M^A_τ on the common support and run B's M^B_{τ⁺} for run B's own-support shells, and for the young components' operations 𝐓′_i(X), compared in total variation, at the young 𝐑-steps of §7.6 against their bounds (1.79) (#C7.6-6-2-2); (LF-2), for the renormalisation quotients of §8.6 at complex V in the inductive class, against Bałaban's majorants n̄ of their numerators and |d| of their denominators.
{#CP.2-2} (LF) is derived in `WILSON_IT1_LARGE_FIELD_DEPTH_2026_10_27.md`: (β) in its §3(d), through the soft tests (#C3.10-2), the coupling shells of the radial tests (1.5), (1.9), and χ^{(j−1)c}(R_j) in its §2(b), and (γ) in its §4 and §5, with the walk-factor difference (W-δ) of `WILSON_IT1_WALK_FACTOR_DIFFERENCE_2026_10_28.md`.
{#CP.2-2-1} (LF-2) at complex V is needed linear in d_j at the literal points of ℰ (#C8.2.6). That note derives it directly for the 𝐄-terms of its frozen difference (i) at arguments of the kind (R1). It derives it through its #0.1 for the old 𝐑-terms of its quotients, read at its members, and for arguments of the kinds (R2), (N), and (R3), read through the merged generations j ≤ k₁.

- {#CP.3} (β) The shells of the plaquette and reference-configuration tests: LFR I (1.3), (1.4), (1.7), and (1.8) (p.178), CRE (2.17) (p.257), the small-field functions χ_k, χ_{k,Λ}, and χ_{h,1/2} of LFR II (1.70), the large-field functions χ^c_j(P_j) and χ′^c_j(Q_j) of LFR II p.380 l.31–46, and the factors of ζ(Ω^c_j) of CRE p.255 l.4–9 built from them.
  {#CP.3-1} These test minimisers computed on the run's fine lattice, and at equal data the two runs' tested quantities differ by C(ε/a_j)^{1−2ε₀}ε_j; the thresholds ε_j and 2ϑ_j differ through the coupling by ≤ Ctg_j²|δ_j| at the threshold t.
  {#CP.3-2} The tests of the scale j that are not equal to 1 on the support of the term's other characteristic functions lie in the term's large-field region or its collar (CRE (3.6)–(3.9) and (3.19)–(3.21); `WILSON_IT1_LARGE_FIELD_DEPTH_2026_10_27.md` §3(a)), so for a young pair the shells lie on the history's cubes, at scales ≥ k/2 − 1, and on the stopping-scale cubes of Ω_k.
- {#CP.4} (γ) The large-field integrands: the action and the form of LFR II (1.70), the minimiser U₀ and the operators H_{1,k} and Δ₁(ζ₀) of the renormalisation denominators LFR II (1.1)–(1.2), the factors V(Y) of LFR II (1.91), the boundary terms 𝐁 generated at the steps at which a large-field region existed, and the large-field dressings of the loop at the 𝐑-operations with the loop.

{#CP.12} **The cube sizes at a crossing (§2).** CRE (2.5) (p.255 l.36–40) defines R_j as the smallest power of L with R_j ≥ (log g_j^{−2})^r, from each run's own coupling.
{#CP.12-1} The admissibility conditions of §2's bijection (CRE pp.255–256), the condition (i) of LFR I p.177, the cubes of the domains, and the localisation sets all depend on R_j, so they agree at the shared scale j only if R^A_j = R^B_{j+1}.
{#CP.12-2} That fails where a power of L lies between (log(g^A_j)^{−2})^r and (log(g^B_{j+1})^{−2})^r.
- {#CP.13} *The choice.* Each run is the tube construction for its target, run A for (K, ḡ) and run B for (K + 1, ḡ) (BETA_FUNCTION_WILSON_LOOPS.md #B2.2.171–#B2.2.180, with the soft tests and Λ of #B2.2.174-1): every parameter that CRE, LFR I, and LFR II define from a coupling g_j is taken at ĝ_j := u_j^{−1/2}, u_j := ḡ^{−2} + b′(K − j) + C_W, with the tube's b′ and C = C_W (#B2.2.165–#B2.2.167; #C5.7-6). So R_j := R^T_j, the least power of L with R_j ≥ (log ĝ_j^{−2})^r, and the 𝐑-operation at the scale j has the depth N^T_j of #B2.2.174.
  {#CP.13-1} u_j depends on K − j alone, so run B's scale j + 1 has the same ĝ, hence the same R, depth, thresholds, and domain radii, as run A's scale j.
  {#CP.13-2} At a fixed bare coupling F_K does not depend on R, which only parametrises the decompositions of unity (§1); the bare couplings are the tube's (#C1.1-2).
- {#CP.14} *Its properties.* Each run's history lies in the tube H_K (Proposition 2.13, #B2.2.823), so Lemma 2.10 (#B2.2.267–#B2.2.271) gives: ĝ_j ≤ g_j ≤ ρ_γ^{1/2}ĝ_j with ρ_γ → 1 as γ → 0; CRE (2.6) with b′ + C_W for its β′, hence (2.7) ("They imply the following inequalities", CRE p.255, before (2.7)); (log g_j^{−2})^r ≤ R_j ≤ 2L(log g_j^{−2})^r, which is (2.5) as a lower bound and with 2L for L as an upper bound; and the conditions of LFR I and LFR II on the depth, with L^{−N_j} ≤ (log g_j^{−2})^{−ν_L}, L^{N_j} ≤ 16L⁴(L+1)²(log g_j^{−2})^{ν_L}, N_j ≤ R_j, and N_j nonincreasing in j (Lemma 2.10(d); BP_TL_NSTEP_FRAME #3.2.1.1-2).
  {#CP.14-1} R_j is nonincreasing in j with R_j/R_{j+1} ∈ {1, L}, and R_m ≤ (L + 1)(n − m)^{β₀}R_n for n > m, which is CRE (2.9) (Lemma 2.10(c)).
  {#CP.14-2} Since the ratio is a power of L, (2.9) also gives R_m/R_n ≤ L^{(n−m)/2} for n − m ≥ 2.
- {#CP.15} *The uses, checked.* Bałaban's proofs use R_j only through these properties.
  - {#CP.16} CRE §§1–3 (pp.245–285): partitions into MR_j-, LM₂R_j-, and LMR_{k+1}-cubes compatible with the earlier ones, which needs R a power of L with R_{j+1} ∈ {R_j, R_j/L} (p.246 l.24–29, p.257 l.28–43, p.264 l.53–56); (2.9) (p.256 l.12–17); e^{−δ2M₂R_k} ≤ e^{−R_k} and e^{−δLM₂R_{k+1}} ≤ e^{−R_k} through R_k ≤ LR_{k+1} (p.266 l.18–19, p.268 l.41–51, p.269 l.44); and k₁ by L^{−(k−k₁)}MR ≤ L (p.270 l.49–50).
    {#CP.16-1} The R₁ of (2.44) (p.263) is a constant, not a cube size.
  - {#CP.17} LFR I pp.177–201: components in 100MR_k-cubes, with R_k decreasing by the factor L at some steps (p.177 l.19–26); N₀ with L^{−N₀+1}MR_{k−N₀+1} = M (p.179 l.8–9); R_{j−N+1} ≤ (L+1)N^{β₀}R_j (p.192 l.17–20); and e^{−R} small (pp.184–188, p.198, p.199 l.38–39, p.200 l.16–18 and l.33), with 10δMR_{j+1} ≥ R_j at p.188 l.22–23.
  - {#CP.18} LFR II pp.356–390: the covers of the operation S and the scaling d′_n(Z^{(n−j)}) ≤ L^{−(n−j)/2}d′_j(Z), which need R_j/R_n ≤ L^{(n−j)/2} for n − j ≥ 2 (p.384 l.7–8 and l.35–36); R_{j−N+1} ≤ (L+1)N^{β₀}R_j (p.382 l.4); N = R_j (p.384 l.17); and the powers R^{d+1}, R^{d+2}, R^7, and R^{−8} inside a strict polylogarithmic dominance by p₀ or p₁ ((1.47), (1.79)–(1.88), p.383 l.28, p.389 l.15–18).
  - {#CP.19} RG I and RG II use only a fixed R = R₁ (RG I p.262 l.42, p.273 l.41; RG II p.3 l.27–28), not R_j.
- {#CP.20} R^T satisfies each of these, with 2L for L in the polylogarithmic bounds, the same in both runs (#CP.14–#CP.14-2); LFR II's N = R_j counts steps only, and every such count holds with the depth N^T_j ≤ R_j (BP_TL_NSTEP_FRAME #3.2.1.2).

{#CP.21} **The conditions and the result.** The conditions are thresholds of Bałaban's kind on g_a := g^A_k, run A's coupling at the stopping scale (#C3.1-2; run B's is g^B_{k+1}, the two inverse squares differing by δ_k, and each run's shared-scale couplings up to the stopping scale are ≤ (1+β₀) times its stopping coupling by CRE (2.6)), on γ := sup_Kg_K, and on ḡ, each on its own line. §11 treats each run at its own stopping coupling, and (T2) is imposed at g_a and at g^B_{k+1} (#C11c.6-1):

- {#CP.22} (T1) The contraction and the feedbacks (§8.3, §8.4, §8.7): for every g ≤ (1+β₀)γ, (ε^*(g) + ε^Q(g))C_τ ≤ 1/2 and 4ε̂^*(g)N′(g/(1+β₀)) ≤ 1, ε̂^*(g) := sup_{g′≤2g}ε^*(g′), which cover every shared scale i ≤ K at its own coupling g_i ≤ (1+β₀)g_K;
  {#CP.22-1} here ε^*(g) := C_XC_ptC_KPL⁴C^𝐀_α[C_Tμ(g) + 4a(g)] bounds the constant ε_k^* of (8.2)–(8.3) at g = g_k (#C8.3.3-2), μ(g) := (‖C‖_∞ϑ(g)/m(g))² ≤ 4‖C‖_∞²(A₁/c_m)²(log g^{−2})^{−2(min(q₀,q₁)−p₀)} the square of the cutoff's sup bound ‖C‖_∞ϑ(g), ϑ(g) := A₁g(log g^{−2})^{p₀}, over the analyticity margin m(g) := ½c_mg(log g^{−2})^{q₀} of the frozen terms, the fluctuation radius of their composites at the radii r of the norm class (§8.2), a(g) := gP_a(log g^{−2}) the bound of the interaction's activities on Bałaban's complex fluctuation domain (#C8.2.2-84),
  {#CP.22-2} N′(g) := log_L(MR(g)) + 3 the bound of the memory length of the recent 𝐑-terms (§8.4), and C_τ a constant of L, b, ḡ, and Bałaban's constants (§8.7);
  {#CP.22-3} ε^*(g) → 0 as g → 0 as a negative power of log g^{−2} and N′(g) grows as a double logarithm, so both conditions hold for γ small, uniformly in K.
    {#CP.22-3-1} The boundary-term recursion of `WILSON_IT1_LARGE_FIELD_DEPTH_2026_10_27.md` §4(e) adds 4C_ovε^{*B}(g)N₀^+(g)W^♯ ≤ 1 for every g ≤ (1+β₀)γ (that note's #4.660-3 at g = ĝ_k, #4.660-4).
    {#CP.22-3-2} Here ε^{*B}(g) := 2C_ptC_XC_KPC_εε(g), C_ε Bałaban's constant in the factor O(ε_k) of CRE p.277 l.7–9, N₀^+(g) := 1 + 2(log(32L(L + 1)) + 2 log log g^{−2})/log L (its #4.638), C_ov := 2 its count of the generations of created terms at a point (its #4.629-1), and W^♯ ≤ 4c_{μN}C_{wr}L^d that note's weighted sum of its #4.660-2 (not this note's configurations W), finite under its condition (⋆) σ ≥ (d + 1)log L + 1 on Bałaban's R and M (its #4.655); ε(g) := gp₀(g) → 0 and N₀^+(g) grows as a double logarithm, so this holds for γ small in the same way.
  {#CP.22-4} ε^Q(g) is the old vertices' coefficient of #C8.3.3-4-3-2-1, g² times a power of log g^{−2}, so it → 0 faster than ε^*(g); the first condition implies ε^*(g)C_τ ≤ 1/2, which is how §8.3, §8.4, and §8.7 use it, and the sum enters only #C8.7.7-2-1 and #C8.7.7-4-1.
  {#CP.22-5} (T1-w) The wraps (#C7.8-9): the reference gases of both runs and of the hybrids of #C7.8-9-4 and #C7.8-9-9 have ε̂ ≤ ν_r/(10368M); μ^{pt} ≤ ν_r/(20736M); G_w ≤ ½; and 4K_ΔC″c″μ^{pt}/(1 − θ_Q) ≤ 1/8. Each holds for γ small, uniformly in K. ε̂ is within the runs' c-versions, which are small with the couplings (map #MD2.4.12.38-3).
    {#CP.22-5-1} μ^{pt} and G_w are proportional to ρ̂^w_γ, which tends to 0 with γ. The torus condition (T_ph/u)L^{j(C)} ≥ CM (map #MD2.3.4.16-6) gives a_w, a^{w,2} ≥ a₀ := min(c^w_M, c^{w,2}_M)c^w_NC/L, so T_w(a_w), T_w(a^{w,2}) ≤ T_w(a₀) (#C7.8-9-2). C_pos, c″, K_Δ, C″, C^w_M, C^{w,2}_M, and 1/(1 − θ_Q) ≤ 2/(1 − L^{−β′}) (#C8.7.7-4-1) do not depend on γ.
- {#CP.26} (T2) The large-field weight (§11): (T2-i) ĉ₀ := c₀M^dR_{k+1}^{d+1}(3·2^{d−1})^{−1}(2L²)^{−d} ≥ log C_d + 2; (T2-ii) p₀(g_a)/4 ≥ (log C_d + 1)100^d + 1; (H) 3·2^{d−1}L^d(C_ℰ + C_P) ≤ R_n and 2^dL^dM^dR_n^d(c_n + C_P) ≤ ⅛γ₀A₁²p₀²(g_n) at every scale n ≤ k, c_n := C_ℰ + C_λ(1 + log g_n^{−2}) (the history volume and cost, (11.2)), C_P := max(2, 2C_M); Bałaban's three conditions for (1.80) with the gain halved and the cost raised by λ_n := 1 + 3·2^{d−1}L^dC_λ(1 + log g_n^{−2}) (§11(d)); and β₀ ≤ 1/7.
  {#CP.26-1} All hold for ḡ small, uniformly in the loop, with p₀ > r(d + 2) + 1, Bałaban's "p₀ large" (LFR II p.385 l.37, p.387 l.28), a choice that CRE p.246 l.14's p₀ ≥ 5r allows: R_n ≥ (log g_n^{−2})^r and p₀(g) = A₀(log g^{−2})^{p₀} (CRE (2.4)–(2.5)).
  {#CP.26-2} It is compatible with Bałaban's other conditions on the exponents: p₁ < p₀ (LFR I p.183 l.2), ½ν ≤ p₀ − p₁ − 1 with a positive integer ν (LFR I p.198 l.55–56), and 2p₁ − (d+5)r₀ > p₀ (LFR II p.383 l.28) admit an integer p₁ once p₀ ≥ (d+5)r₀ + ν + 4, since ν and r₀ do not depend on p₀; and T₀ ≥ 2 of §8.2 holds with the integers q₀, q₁ > p₀ of CRE (2.28), which are bounded below only.
  {#CP.26-3} They give the relative weight δ_LF := e^{2C_K}(e^s − 1) of (11.3), C_K := C_fsN_s⁴(1 + log g_a^{−1}) the final-scale constant of (11.1), bounded uniformly in K, with w_{ℓ₀} ≥ (1 + δ_LF)^{−1}; the Cauchy estimate uses only this.
  {#CP.26-4} The smallness δ_LF ≤ ½ needs in addition (T2-v) 8e^{2C_K}N_s⁴(MR_k)^{−4}e^{−(3/2)p₀(g_a)} ≤ 1; it depends on the loop through N_s and holds for ḡ ≤ ḡ₀(q, T_ph/u) when p₀ > 4r + 1 (§11(c)).
- {#CP.27} (T-Λ) The depth of U₀ (`WILSON_IT1_LARGE_FIELD_DEPTH_2026_10_27.md` §4(c)), used through (LF): C(M)R_kε_k ≤ ε₁^{LF} (LF #4.43-1; VAR's parameter at U₀), with ε₁^{LF} the large-field note's ε₁ (its #D.ε₁, #1.6-1), named apart from §9's ε₁ := 2C₀ε_V, below the smallness that VAR Sect. G needs for its constant C₁ of VAR (172), which plays (14)'s role in Sect. G's repetition of §§A–E (not the C₁ = 2C₀/B₃ chosen at #C9.4), taken in the LF note as C₁′ (LF #4.46-0, with #4.50-0's C₁), which depends only on M and Bałaban's constants;
  {#CP.27-1} VAR assumes this C₁ absolute, "hence B₅ is such a constant also" (p.305 l.44), and a constant of M serves, with VAR's B₅ of (173) then a constant of M too, since M is fixed before ε₁ and γ (the LF note's #4.22.2), and the smallness conditions on ε₁ of the alignment of that note's §4(d), listed there.
  {#CP.27-2} It holds for γ small, uniformly in K.
- {#CP.28} (T-c) The complex class (`WILSON_IT1_LARGE_FIELD_DEPTH_2026_10_27.md` §4(d), *The complex class.*): the conditions of (T-Λ) with 26ε₁′ in place of ε₁, where ε₁′ := C(M)R_k(ε_k + 60(α̂₀ + α̂₁) + 25g_kb_k) and α̂_i := max_{m≤k}α_{i,m}, and 1560(α̂₀ + α̂₁) ≤ min(α₁, α_J).
  {#CP.28-1} It holds for γ small, uniformly in K.
- {#CP.29} Result (§7): |F_{K+1}(C) − F_K(C)| ≤ a_K with a_K := [3x_K + λ_K + x^w_K + x^Q_K + b^{(S)}_K + δ_LF(a^{(U)}_K + b^{(M)}_K)]B_W + (e^{ΔE_K} − 1)B_W (#C7.7).
  {#CP.29-5} Here x_K := e^{X_K} − 1 with X_K the bound (7.1) on the groups of (3.1) of the all-small-field pair and of the young pairs on Λ_k (the direct bounds of §4.1–4.2, N_s⁴C_a[(K+1)θ̃^{K−j(C)} + (j(C)+2)w_K], and the variation, 𝐑-variation, and classical groups), λ_K the leading-word bound (#C7.5), x^w_K the wrap bound (#C7.8-8-1), x^Q_K the bound of the final interaction weights (#C7.9), ΔE_K the loop-constant bound (#C7.6), and b^{(S)}_K the stopping-scale shell bound of §3 (soft tests).
  {#CP.29-6} Further, ℓ_K := (log(bK + ḡ^{−2}))^{rd+2p₀} is the polylogarithm collecting the cube counts (100MR_j)^d, the shells' p₀(ĝ_j)², and c_j (#CK.1-14) at the shared scales (#C8.7.1-5), μ_K := K^{2−κ₀/2}ℓ_K, w_K := (K + 1)(θ̃^{k_s/8} + 2^{−k_s/16}) + μ_K with the stopping scale k_s := K − j(C) of §8, b^{(M)}_K is the bound of §6.2 on the change of F by the matched large-field pairs, and a^{(U)}_K := 2e^{−C_P(K−j(C))} is the bound (6.1) of §6.1 on the unmatched set (#C6.1.2).
  {#CP.29-1} a_K is summable in K since κ₀ ≥ 11 (CRE p.263 l.50 has κ₀ ≥ 7, and p.260 lets κ₀ be chosen arbitrarily large, after (2.31)), the large-field note's c̄^W_K needing κ₀ > 10 (its #5.66). The inputs (LF), (W-δ), the lift condition, and the 𝐑 version of (5.1c) enter as listed in #C7.1-1–#C7.1-2.
  {#CP.29-2} Through §8.7's recursion, (LF) enters x_K except its part §4's direct bounds X^{dir}_K, and every other term of a_K except λ_K, a^{(U)}_K, the old-pair term of b^{(M)}_K, the old parts τ^E_K of ΔE_K and τ^w_K of x^w_K, and the branches b^{(M)}_K := 4 and a_K := 2B_W.
  {#CP.29-3} The deep-V(Y) part of ν_j at fine scales (§8.6) is derived in the large-field note's §4(e).
  {#CP.29-4} This a_K is for K ≥ K₁ of §7; for the finitely many K < K₁, a_K := 2B_W (*The smaller K.*, #C7.4-7).

## 1. Setting {#CS1}

{#C1.1} Run A: lattice spacing ε = uL^{−K}, bare coupling g^A_0 = g_0(ε, ḡ), k := K − j(C) steps to the stopping lattice T_a, a = uL^{−j(C)}, with N_s⁴ points.
{#C1.1-1} Run B: spacing ε/L, g^B_0 = g_0(ε/L, ḡ), k + 1 steps to the same T_a.
{#C1.1-2} Both are pinned at the unit scale, g^A_K = g^B_{K+1} = ḡ, by BETA_FUNCTION_WILSON_LOOPS.md Proposition 2.13 for the tube construction of each run's target (#CP.13), for compact simple G, SU(2) included, with ḡ ≤ γ′; along each run's flow (i) and (ii) of its Lemma 2.1 hold with the tube's b, b′, C (#B2.2.823), and these are the "Lemma 2.1(i)" cited below. RG I states the matching as its Theorem 2 for SU(2) and defers the proof to a separate paper (p.259 l.38).
{#C1.1-3} Run B's step j + 1 acts on the same pair of lattices as run A's step j, j = 1, …, k; the shared scale index is j, and run B's step 1 is the extra step.
{#C1.1-4} Couplings at the shared scale j: g^A_j and g^B_{j+1}, with δ_j := (g^B_{j+1})^{−2} − (g^A_j)^{−2}, δ_K = 0.

{#C1.2} F_K(C) = N_K/(κ_K Z_K) with κ_K = κ^{(k)} the run's own product of per-step perimeter and corner coefficients (map #MD2.0.3.4), so that at the stopping scale F_K is e^{E^A_const} times the expectation of the normalised dressed loop 𝒲^A_k = f^A_k + (dev insertions), leading coefficient 1, against the stopping-scale density ρ^A_k, plus the remainder r_K, which carries the same factor (the continuum note's identity (2), #ND.2.6, with κ^{(K′)} of its (6.1)).
{#C1.2-1} The same for run B with 𝒲^B_{k+1}, ρ^B_{k+1}, and E^B_const.
{#C1.2-2} The comparison is made at T_a with each run's κ divided out; no product of per-step coefficients is compared across runs.
{#C1.2-3} The leading word f^A_k := dim(π)^{−1}tr π(Hol_C(U^A_k(V))) is read at run A's fine background (map #MD2.0.3.5), so f^B_{k+1} and f^A_k are different functions of V (*The leading word.*, #C7.5).
{#C1.2-4} The loop constant E^A_const := E_const,k = Σ_{j≤k}E°^A_j is a number of the contour and the torus, a factor of the whole numerator and not of Z (map #MD2.0.3.8; the continuum note's #ND.2.3, #ND.5.3: abs(E_const) ≤ B_E, its T-part C^E_Σ𝔞̄ with C^E_Σ the C_Σ of D2.3(7) there, renamed apart from §8's C_Σ); it is compared in *The loop constant.* (#C7.6).
{#C1.2-5} §§3–6 and #C7.1–#C7.5 compare the two runs with run A's constant e^{E^A_const} on both, and #C7.6 restores run B's.

## 2. The Matched Decomposition {#CS2}

{#C2.1} Both stopping-scale densities have the form CRE (2.18): ρ = Σ_{{Ω_j},{Λ_j}} χ(Ω_last) 𝐓 exp A, summed over admissible sequences of domains, one domain pair per step.
{#C2.1-1} Run B's sequences have k + 1 entries, run A's k.
{#C2.1-2} The 𝐑-operation acts on a component Z′ of the large-field region by replacing ρ(Z, V) with ρ(Z″, V) times a quotient of integrals (LFR I (0.3)), ρ(Z″, V) being the term of the same sum with Z′ removed from the sequence, the quotient entering as an 𝐑-term (LFR I (0.5)–(0.6)); a component is renormalised once it satisfies LFR I p.177's conditions (i) (contained in a cube of size 100MR_k) and (ii) (no new large field inside during the preceding N steps).
{#C2.1-3} So every term of run B's stopping-scale representation is one of two kinds:

- {#C2.2} (M) its step-1 pair is (T, T) (no large-field region alive from run B's extra step; its renormalised step-1 regions survive only as 𝐑-terms); dropping the step-1 entry gives an admissible run-A sequence, and this is a bijection between (M) and run A's terms, since the admissibility conditions (CRE pp.255–256) are the same at the shared scales, with R_j := R^T_j in both runs, so that R^A_j = R^B_{j+1} (#CP.13-1) (the paragraph on the cube sizes at a crossing);
- {#C2.3} (U) its step-1 pair is not (T, T): a component born at run B's step 1 is alive at the stopping scale.

{#C2.4} So ρ^B_{k+1} − ρ^A_k = Σ_{τ} (ρ^B[τ⁺] − ρ^A[τ]) + Σ_{(U)} ρ^B[·], and the same for the numerators with the dressed loops.

## 3. A Matched Pair at the Stopping Scale {#CS3}

{#C3.1} Fix a matched pair τ⁺, τ, and the all-small-field term first (every Ω_j = Λ_j = T).
{#C3.1-1} On the last domain the position-dependent coupling of CRE (2.24) is constant, and (2.23) with (2.25), (2.30) gives the exponent of each run as −g^{−2}_{stop}A_fine(U(V)) + Σ_j irr_j(U(V)) + Σ_j[𝐑^{(j)}(U) − 𝐑^{(j)}(1)] − E, where irr_j := 𝐄^{(j)}(U) − 𝐄^{(j)}(1) − β_j A(φ_j, U) is the quantity bounded by CRE (2.43) and the coupling renormalisations β_j have been absorbed into g_stop by (2.24).
{#C3.1-2} For run A, g_stop = g^A_k, A_fine = A_ε, U = U^A_k(V), the minimiser of CRE (2.12) on T_ε with M^kU = V; for run B, g_stop = g^B_{k+1}, A_fine = A_{ε/L}, U = U^B_{k+1}(V) on T_{ε/L} with M^{k+1}U = V.

{#C3.2} *The lift.* For a field U on T_ε regular at scale k let ι(U) be the one-step minimiser of A_{ε/L} with block data U (CRE (2.12) at one step; existence, regularity, analyticity in U, and gauge covariance from VAR Theorem 1 and RG I p.262 (iv), p.263 (1.17)); M ι(U) = U exactly, so M^{k+1}ι(U^A_k(V)) = V. For a localisation domain X let ι_X be the localised one-step minimiser of #C9.8.6, a function of U on X^∼ with Mι_XU = U on X^∼ and ι_X1 = 1.
{#C3.2-1} Let Q₁^{pl}(W) := dM(W) be the plain linearised one-step averaging at a configuration W on T_{ε/L} (#C10.3.17).
{#C3.2-2} The pair lift of a pair (𝐔, 𝐉) on X^∼, 𝐉 a current variable as in RG I (1.14), is (ι_X𝐔, Q₁^{pl}(ι_X𝐔)*𝐉).

{#C3.3} The difference of the two exponents at the same V is then exactly

{#C3.4} (3.1) D_τ(V) = −δ_k A_{ε/L}(U^B_{k+1}) − (g^A_k)^{−2}[A_{ε/L}(U^B_{k+1}) − A_ε(U^A_k)] + irr^B_1(U^B_{k+1}) + Σ_{j=1}^{k} irr(Δ_j)(U^A_k) + Σ_{j=1}^{k}[irr^B_{j+1}(U^B_{k+1}) − irr^G(U^A_k)] + (the same three groups for the 𝐑-terms) − (E^B − E^A),

{#C3.5} with Δ_j(X, ·, z) := G(X, ·, z) − 𝐄^{A,(j)}(X, ·, z) and G(X, (𝐔, 𝐉), z) := 𝐄^{B,(j+1)}(X, (ι_X𝐔, Q₁^{pl}(ι_X𝐔)*𝐉), z), run B's term at the pair lift.
{#C3.5-1} Both are evaluated at the diagonal 𝐉 = J(U), J(W) the current (I.1.8) of the configuration W, so Δ_j is a functional of fields on T_ε.
{#C3.5-2} It is written here through its irrelevant part irr(Δ_j) := Δ_j(U) − Δ_j(1) − Π^Δ_{22,11}A(h_z, U) − N_j(U), with Δ_j's own coefficient Π^Δ_{22,11} = Π^G_{22,11} − β^A_j and N_j the plane-resolved part of G's moment (*The plane-resolved moment.* below).
{#C3.5-3} The coefficient differs from Δβ_j := β^B_{j+1} − β^A_j by at most C_Π(j)E₀e^{−δ₀M₁L^j}, C_Π(j) := C′_Π(8B₃/α_{2,j})² (§5, *The moment of the lifted term.*).
{#C3.5-4} The vacuum constants E^B − E^A are pure numbers for this term and cancel in F.

{#C3.6} In the variation group, irr^G(U^A_k) := G(Λ_j, U^A_k, z) − G(Λ_j, 1, z) − Π^G_{22,11}A_ε(h_z, U^A_k) − N_j(U^A_k), with G at the diagonal and the Wilson action of T_ε at U^A_k.
{#C3.6-1} Since ι_X1 = 1 and J(1) = 0, G(Λ_j, 1, z) = 𝐄^{B,(j+1)}(Λ_j, 1, z).
{#C3.6-2} So the telescoping is exact: irr(Δ_j)(U^A_k) = irr^G(U^A_k) − irr^A_j(U^A_k), and the group adds irr^B_{j+1}(U^B_{k+1}) − irr^G(U^A_k), where irr^B_{j+1}(U^B_{k+1}) carries A_{ε/L}(h_z, U^B_{k+1}).
{#C3.6-3} The sum of the two is the same for every coefficient in place of Π^G_{22,11} and every N_j; G's own marginal part makes each piece the irrelevant part of one term.

{#C3.7} *The plane-resolved moment.* For the coordinate planes P = (κ, μ), κ < μ, and P′ = (λ, ν), λ < ν, let Φ_P(x) := (1/iε²)log U(∂p_P(x)) be the plaquette field of the plaquette p_P(x) with the corner x spanned by e_κ and e_μ, and let A_{PP′}(h_z, U) := ½Σ_{x∈T_ε}ε⁴h_z(x)tr Φ_P(x)Φ_{P′}(x), the plane-pair action with the weights of A_ε(h_z, ·).
{#C3.7-1} It is gauge invariant, since both loops start at x, and holomorphic where the plaquettes are small; at real configurations Φ_P and Φ_{P′} are Hermitian, so the trace is real.
{#C3.7-2} Let Π^G_{μν,κλ}(z) be the tensor of CRE (3.57) for G at the point z, the sum over X extended to the localisation domains of the infinite lattice as there.
{#C3.7-3} It is taken at each z, so the translation invariance by which CRE drops z (p.281 l.59) is not used, and every subtraction below is at that z.
{#C3.7-4} Then

{#C3.8} N_j(U) := Σ_{κ<μ, λ<ν}(Π^G_{μν,κλ} − Π^G_{22,11}δ_{μν}δ_{κλ})A_{(κμ)(λν)}(h_z, U),

{#C3.9} the part of G's marginal term off its isotropic coefficient.
{#C3.9-1} G's tensor is taken at the z of the term, so Π^G_{μν,κλ} = Π^G_{μν,κλ}(z) and Π^G_{22,11} = Π^G_{22,11}(z) depend on z, and so do the coefficients of N_j.
{#C3.9-2} For a family with the Euclidean covariance (2.29), CRE (3.60)–(3.61) give N = 0.
{#C3.9-3} (2.29) holds for the sum over X at one configuration (CRE p.260 l.2–4), while G evaluates each X at its own ι_X𝐔, so (3.60)–(3.61) are not applied to G.
{#C3.9-4} N_j is kept, and its coefficients are boundary terms of the localised lift (§5, *The moment of the lifted term.*).
{#C3.9-5} The functions h_z are CRE's tents on T_{L^{−j}}, h(t) = max{1 − |t|, 0} (CRE p.283 l.12–15), the same for both runs since both use the blocks T^{(j)}, with Σ_zh_z = 1 on each fine lattice.

{#C3.10} The two all-small-field terms also differ in their supports.
{#C3.10-1} Each carries the stopping-scale test χ_k(T) of (2.18), built on its own fine lattice, and the fluctuation cutoffs (3.16), whose shells are §8.2(b); its other plaquette, axial, and reference tests are equal to 1 on the support of its other characteristic functions (`WILSON_IT1_LARGE_FIELD_DEPTH_2026_10_27.md` §3(a)).
{#C3.10-2} With the plaquette and reference tests soft at every K and in both runs (that note's §3(d)), the shells of χ_k(T) change F_{K+1} − F_K by at most b^{(S)}_KB_W, with b^{(S)}_K of that note's #3.42, by (RS) of its §3(d); the tests' thresholds are the same in both runs, and their coupling parts enter s′_K (its #3.40-1). b^{(S)}_K is summable in K, being a constant times (ε/a)^{1−2ε₀} = L^{−(1−2ε₀)(K−j(C))}.

{#C3.11} The five groups are of four kinds.
{#C3.11-1} (a) The coupling difference δ_k times the action, with |A_{ε/L}(U^B_{k+1}(V))| ≤ C ε_k² N_s⁴ for V regular at scale k, and δ_k = Σ_{k<m≤K}(β^B_{m+1} − β^A_m): (2.24) on the last domain, g_m^{−2} = g_{m−1}^{−2} − β_m(g_{m−1}), gives δ_m − δ_{m−1} = β^A_m − β^B_{m+1} for δ_m := (g^B_{m+1})^{−2} − (g^A_m)^{−2}, and the pin g^A_K = g^B_{K+1} = ḡ (#C1.1-2) gives δ_K = 0.
{#C3.11-2} (b) The difference of the two constrained minima, a one-step artifact plus the gap between two configurations of run A's problem: MU^B_{k+1} satisfies run A's constraint (§9.1), and

{#C3.12} (3.2) A_{ε/L}(U^B_{k+1}) − A_ε(U^A_k) = [A_ε(MU^B_{k+1}) − A_ε(U^A_k)] − b(U^B_{k+1}), b(W) := A_ε(MW) − A_{ε/L}(W),

{#C3.13} which is (9.1).
{#C3.13-1} The artifact b is bounded in §9.3, (9.4), and the gap in §9.6, (9.9), so the difference Δ is bounded in §9, (9.10), for fields regular at scale k (CRE (3.12), VAR's B₃).
{#C3.13-2} (c) The extra generation irr^B_1 and 𝐑^{B,(1)}: §4.1.
{#C3.13-3} (d) The same-generation differences, split as the frozen difference Δ_j at run A's own configuration plus the variation of run B's frozen term between the two configurations U^B_{k+1}(V) and ι_X(U^A_k(V)): §5, the variation at #C5.77–#C5.98 with the minimiser distance of §9.7.

{#C3.14} For matched terms with large-field regions the same split applies to the small-field exponent on the last domain; in addition the characteristic functions χ_k (CRE (2.17)), the operations 𝐓_k (CRE (2.19)–(2.21)), the boundary terms 𝐁 (CRE (2.40)–(2.42)), and the relative constants E are each run's own, built on its fine lattice.
{#C3.14-1} Their differences are sorted in §6.2: the old pairs are measured against each run's own Z_{ℓ₀}, and for the young pairs the small-field ingredients are (α), the shells of the tests that are not identically 1 are (β), and the large-field integrands and 𝐁 are (γ).

## 4. The Direct Bounds {#CS4}

### 4.1 The Extra Generation {#CS4.1}

{#C4.1.1} On the all-small-field term, Γ_{k+1} = T_a in run B's indexing.
{#C4.1.1-1} CRE (2.43) at j = 1 with Ω = T_a gives |irr^B_1(U^B_{k+1}(V))| ≤ E₁ L^{−βk} N_s⁴, as the sum Σ_{n=1}^{k+1}(L^{1−n})^β|Γ_n ∩ Ω| has the single term n = k + 1.
{#C4.1.1-2} CRE (2.44) at j = 1 gives |𝐑^{B,(1)}(U) − 𝐑^{B,(1)}(1)| ≤ R₁ (g^B_1)^{κ₀} N_s⁴, and (g^B_1)^{−2} ≥ ḡ^{−2} + bK − C by BETA_FUNCTION_WILSON_LOOPS.md Lemma 2.1(i) at the shared scale 1 (K steps below the pin), so this is ≤ R₁ N_s⁴ (bK − C)^{−κ₀/2}, summable for κ₀ ≥ 3 (CRE p.263 l.50 has κ₀ ≥ 7).
{#C4.1.1-3} On terms with large-field regions, run B's step-1 boundary terms 𝐁^{(1)} are localised at Z_1^∼ (CRE (2.41)), which is empty for (M) after the 𝐑-operations, so there are none.
{#C4.1.1-4} The extra generation's direct contribution to D_τ is therefore ≤ (E₁L^{−βk} + R₁(bK − C)^{−κ₀/2}) N_s⁴, summable in K.

### 4.2 The Old Tail {#CS4.2}

{#C4.2.1} For the same-generation differences of ages k − j ≥ m, the triangle inequality with CRE (2.43), (2.44), (2.46) and Lemma 2.1(i) gives Σ_{j ≤ k−m}|irr^B_{j+1} − irr^A_j| ≤ 2E₁N_s⁴L^{−βm}/(1 − L^{−β}) and Σ_{j ≤ k−m}|Δ𝐑_j| ≤ C N_s⁴(1 + m)^{1−κ₀/2}: each run's step-j 𝐑-term is at most R₁g_j^{κ₀}N_s⁴ on T_a ((2.44), (2.46)), g_j^{−2} ≥ g_k^{−2} + b(k − j) − C (Lemma 2.1(i)) gives g_j^{κ₀} ≤ C(1 + k − j)^{−κ₀/2} for ḡ small, and Σ_{i≥m}(1 + i)^{−κ₀/2} ≤ C(1 + m)^{1−κ₀/2} as κ₀ ≥ 7.
{#C4.2.1-1} At m = m_K := ⌊√K⌋ this is summable in K, since (1 + m_K)^{1−κ₀/2} ≤ K^{1/2−κ₀/4} with κ₀ ≥ 7; it uses no information on d_j.

## 5. Theorem 2 for a Difference (RΔ, Bałaban's Proof Applied to Δ_j) {#CS5}

{#C5.1} *Statement.* Let 𝐄^A and 𝐄^B be two families of generation-j terms on the same lattices, each with CRE p.259's properties (i)–(iv) (localisation in X, analyticity on U^c_j(X, α₀, α₁), gauge invariance, the bound RG I (1.18) with E₀) and, for 𝐄^A, the Euclidean covariance (2.29).
{#C5.1-1} For the pair-lift term G of §3 covariance is not used: CRE (3.57) holds for G with its own tensor Π^G_{μν,κλ}, and the part off its isotropic coefficient is the N_j of §3 (*The plane-resolved moment.*).
{#C5.1-2} For G, (i) holds with X^∼ in place of X, and (ii) holds on the common polydisc 𝒫_j(X; α′) of *Complex domain.* below.
{#C5.1-3} Let their difference Δ satisfy |Δ(X, (𝐔, J(𝐔)), z)| ≤ d E₀ exp(−κd_j(X)) on the evaluation set ℰ_j(X; r) of the norm class 𝒫_j(X; r) (*Complex domain.*).
{#C5.1-4} Then for z ∈ Λ_j⁰ ∩ (Ω_n ∖ Ω_{n+1}) and U_k regular,

{#C5.2} (5.1) |Δ(Λ_j, U_k, z) − Δ(Λ_j, 1, z) − Δβ A(h_z, U_k) − N(U_k)| ≤ d · E₁′ (L^jL^{−n})^{5−β}, Δβ := Π^Δ_{22,11} (Δ's own coefficient, not the Δβ_j = β^B_{j+1} − β^A_j of §3),

{#C5.3} with N := N_j for the frozen difference and N := 0 for two covariant families, E₁′ the constant of CRE (3.67) for one term with the 36 plane pairs of N included, and summing over z, the bound (2.43) with E₁ replaced by d E₁, in its per-z form, since Π^G_{22,11}(z) and N_j depend on z.
{#C5.3-1} Here β is the small positive exponent of (3.67) (p.283 l.31: "with 1−β, β>0, instead of β<1"), written β_E where it meets other exponents; (2.43)'s β is the complementary number.
{#C5.3-2} The age exponent of this note is β′ := ½min(β_H, 1 − β_E), β_H the Hölder index of the class bound (5.1c) below.
{#C5.3-3} The two indices are fixed with β_H ≥ 19/20 and β_E ≤ 1/20, so β′ ≥ 19/40: RG I states its Hölder bounds for 0 ≤ β ≤ β^H_0 < 1, β^H_0 RG I's β₀ there (p.276 l.42, p.285 l.23), on VAR (9), which holds up to β = 1 (§9.2), and (3.67) holds for every β > 0.
{#C5.3-4} Since 4 + β′ < 5 − β_E and L^{j−n} ≤ 1, (5.1) holds with the exponent 4 + β′ in place of 5 − β.

{#C5.4} *Complex domain (RΔ^c).* For z ∈ Λ_j⁰ ∩ (Ω_n ∖ Ω_{n+1}) let □ ∈ π_n be the cube containing z, and let the near domain of z be □₀ := □̃⁵, of the side 11M in the L^{−n}-scale, 11MLⁿη in the units of T_η (RG I p.257 l.7, p.273 l.40).
{#C5.4-1} In the first case of CRE p.280 l.14–22, the localisation domains X ⊂ □̃² of p.279 l.45–48, RG I's analysis uses the configuration on □₀ only: the gauges v and u_{k+1} of (I.3.26)–(I.3.27) and the localisation of p.280 l.44–47 live there, the background bounds (I.3.27) hold on □̃⁴, and the gauge transformations are "explicitly given analytic functions of 𝐔, depending on 𝐔 restricted to the cube □₀" (RG I p.276 l.14–15).
{#C5.4-2} Let irr(Δ)(U) := Δ(Λ_j, U, z) − Δ(Λ_j, 1, z) − Δβ A(h_z, U) − N(U).
{#C5.4-3} The radii are reduced: α′_{i,m} := α_{i,m}/(4B₃) on the layer m, i = 0, 1, and r_{i,m} := ½α′_{i,m}.

{#C5.5} The common polydisc of X at radii s ≤ α′ is the set 𝒫_j(X; s) of pairs (𝐔, 𝐉) on X^∼, 𝐉 a current variable as in RG I (1.14), whose orbit under the G^c-valued gauge transformations (I.1.10) on X^∼ contains a representative (𝐔₀, 𝐉₀) with two properties.
{#C5.5-1} Its restriction to X satisfies the conditions (i)–(iii) of run A's U^c_j(X, s_{0,j}, s_{1,j}) (RG I p.262 l.15–40), with |𝐉₀| ≤ s_{0,j}/C_{Q*}.
{#C5.5-2} The G^c-orbit of the lifted configuration ι_X𝐔₀ contains a configuration (ι_X𝐔₀)^ṽ, ṽ a G^c-valued gauge transformation on the lattice of ι_X with ‖Ad(ṽ(x)^{±1})‖ ≤ e^{2β_I} at every point, that satisfies, on X, the configuration conditions (i), (ii), and the plaquette bound of (iii) of run B's U^c_{j+1}(X, s_{0,j}, s_{1,j}).
{#C5.5-3} This is orbit-wise as Bałaban states his conditions (RG I p.277 l.54–55: "the orbit of the configuration … contains the configuration exp iξ𝐇_j(…) satisfying the conditions (i), (ii)"), with a gauge near the identity as his are (|u_j − 1| < B₃²O(1)Mα₀ in (3.37), p.277 l.50; the bound of R((v ū_{k+1}v_ju_j)^{−1}) in (3.41), p.278 l.39–41); the gauges ṽ at the points used are listed in *The lift gauges.* (#C5.47).
{#C5.5-4} The lift half is used only through the lifted pair's membership in run B's space, a union of G^c-orbits (#C5.6).
{#C5.5-5} The condition (iv) is not imposed: it follows.
{#C5.5-6} By (1.17) (RG I p.263 l.7–17), the conditions (i)–(iii) at α′₀ give the bounds (1.16) at 2B₃α′₀ through Proposition 9 [15], for 𝐔₀ and, at the real data M^·(U₀), for its real part U₀, which satisfies (1.11).
{#C5.5-7} Since s_{0,j} ≤ α′_{0,j} = α_{0,j}/(4B₃), this gives (iv) at 2B₃s_{0,j} ≤ ½α_{0,j}.
{#C5.5-8} So the representative lies in run A's U^c_j(X, ½α_{0,j}, ½α_{1,j}), and with it the whole orbit, since that space is a union of G^c-orbits (p.262 l.12–13).
{#C5.5-9} The lift is covariant, ι_X(𝐔^v) = (ι_X𝐔)^{ṽ_b} for G^c-valued v (#C9.8.18-3, #C9.8.18-5), so the lifts of the orbit form one orbit, and it lies in run B's U^c_{j+1}(X, e^{2β_I}·½α_{0,j}, e^{2β_I}·½α_{1,j}) in the same way (#C5.6), with e^{2β_I}·½α_{i,j} ≤ α^B_{i,j+1} (#C5.7).
{#C5.5-10} Hence 𝒫_j(X; s) is a union of G^c-orbits, on which Δ(X, ·) is invariant (#C9.8.18-5).

{#C5.6} The lifted pair (ι_X𝐔₀, Q₁^{pl}(ι_X𝐔₀)*𝐉₀) of the representative then lies in run B's space.
{#C5.6-1} Its transform by ṽ under (1.10) is (W_ṽ, Ad(ṽ)Q₁^{pl}(ι_X𝐔₀)*𝐉₀), W_ṽ := (ι_X𝐔₀)^ṽ, and by the covariance of Q₁^{pl}* (§9.4, #C9.8.18), with v := ṽ| on run A's lattice, Ad(ṽ)Q₁^{pl}(ι_X𝐔₀)*𝐉₀ = Q₁^{pl}(W_ṽ)*Ad(v)𝐉₀, where |Ad(v)𝐉₀| ≤ e^{2β_I}|𝐉₀| ≤ e^{2β_I}s_{0,j}/C_{Q*}.
{#C5.6-2} W_ṽ satisfies, on X, run B's (i), (ii), and plaquette bound at s, so it is a configuration 𝒱 of the class below, and the bound below gives |Q₁^{pl}(W_ṽ)*Ad(v)𝐉₀| ≤ e^{2β_I}s_{0,j}.
{#C5.6-3} So the transformed pair satisfies, on X, the conditions (i)–(iii) of run B's U^c_{j+1}(X, e^{2β_I}s_{0,j}, e^{2β_I}s_{1,j}), its current included.
{#C5.6-4} A column of Q₁^{pl}(𝒱)* has L straight terms and at most 2dL^d contour terms of weight L^{−1}, and the term of weight L^{d−1} (§10.3, *The Adjoint Averaging.*), with transports along at most (2d + 1)L bonds.
{#C5.6-5} So |Q₁^{pl}(𝒱)*𝐉| ≤ C_{Q*}|𝐉|, C_{Q*} := 2(1 + (2d + 1)L^{d−1}).
{#C5.6-6} The factor 2 is the room for the transports and for the operators dlog, dexp, Ad(e^{iY_c}), and Ad(h_{c,x}^{Γ,Γ′}) of that paragraph at the configurations 𝒱 of the class, which are within O(s_{1,j}L^{−j}) of real ones on each bond, for γ small.
{#C5.6-7} Each transport is a product of at most (2d + 1)L bond factors, and each of the four operators is analytic in the logarithms of such products near their real values, so at 𝒱 each is within the factor exp(O((2d + 1)Ls_{1,j}L^{−j})) of its value at a real configuration, and that factor is at most 2 for γ small.

{#C5.7} Δ(X, ·, z) is analytic on 𝒫_j(X; α′).
{#C5.7-1} For 𝐄^A(X, ·) this holds since α′ < α.
{#C5.7-2} For G(X, ·) it holds since ι_X is analytic in 𝐔 (#C9.8.10), Q₁^{pl}(W)* is analytic in W, and e^{2β_I}α′_{i,j} ≤ e^{2β_I}·½α_{i,j} < α_{i,j} = α^B_{i,j+1}, as e^{2β_I} = e^{1/64} < 1.6 (β_I = 2^{−7}, #CK.1-11) and run B's thresholds at the scale j are run A's (#CP.13-1).
{#C5.7-3} Where |δ_j| ≤ ½(g^A_j)^{−2}, (g^B_{j+1})^{−2} = (g^A_j)^{−2} + δ_j lies in [½(g^A_j)^{−2}, (3/2)(g^A_j)^{−2}], and so does every x between (g^A_j)^{−2} and (g^B_{j+1})^{−2}.
{#C5.7-4} The bound |δ_j| ≤ ½(g^A_j)^{−2} is a priori, run by run, and uses no norm d_i.
{#C5.7-5} Both runs have their couplings in ]0, (1+β₀)γ] (#CP.21) and the same unit coupling g ≤ γ (δ_K = 0, §8.3).
{#C5.7-6} In the tube construction each step's coefficient β^T_{k+1} is within δ′ := C_ΛC₃γp₀(γ) + C_Rγ^{κ₀−4} of the zero-coupling coefficient on the histories of H_k (`BETA_FUNCTION_WILSON_LOOPS.md` #B2.2.165, #B2.2.842: Propositions 2.4 and 2.11 with Lemma 2.10), so the window (W) holds with b = 2c ln L − δ′, b′ = 2c ln L + δ′, and the window constant C_W := C₀ of its Remark 2.3 (#B2.2.167), for compact simple G.
{#C5.7-7} Summed from the unit scale (its Lemma 2.1(i), which holds along each run's flow, #B2.2.823), it puts both (g^A_j)^{−2} and (g^B_{j+1})^{−2} in [ḡ^{−2} + b(K − j) − C_W, ḡ^{−2} + b′(K − j) + C_W].
{#C5.7-8} So |δ_j| ≤ 2C_rem(1+β₀)²γ²(K − j) + 2C_W ≤ ε_γ(g^A_j)^{−2} with ε_γ := 2C_rem(1+β₀)²γ²/b + 2C_Wγ²/(1 − C_Wγ²), since (g^A_j)^{−2} ≥ b(K − j) and (g^A_j)^{−2} ≥ γ^{−2} − C_W; ε_γ → 0 as γ → 0, and ε_γ ≤ ½ for γ small.
{#C5.7-9} (8.6) gives the sharper bound used in §8.

{#C5.8} The norm class is 𝒫_j(X; r).
{#C5.8-1} §8.2 takes the norm d_j on its evaluation set ℰ_j(X; r), the union of the G^c-orbits on X^∼, within 𝒫_j(X; r), of the literal points of four kinds.
{#C5.8-2} Δ(X, ·) is constant on these orbits: 𝐄^A by CRE's (iii) (p.259 l.43–44) on RG I's spaces, unions of G^c-orbits (RG I p.262 l.4–14), the terms of Δ_j being the localised terms of CRE (2.1) with X ⊂ Λ_j (p.254 l.47–50, p.259 l.39), not the boundary terms; and G by #C9.8.18-5. So d_j is the supremum over the literal points whose orbits lie in 𝒫_j(X; r), and every bound with d_j is derived there.
{#C5.8-3} The literal points are the following.
{#C5.8-4} (R1) A pair (𝐔, J(𝐔)) that equals, in a G^c-valued gauge w on X^∼, a minimiser of one of the following three kinds, with the top index p ≥ j and its constraints on X^∼ of the scales ≥ j, and that satisfies on X^∼ the bounds of #C5.8-6.
- {#C5.8-4-1} A single-scale minimiser U_p(𝐕), at real data of the integration support of data parameter ε₁ ≤ C(M)R_kε_k (#C5.59), or at complex data 𝐕 = V′V₀ of the fluctuation integral, V₀ such real data and V′ the exponential of the complexified integration variables (CRE (3.15) with the margin m_k, §8.2; #C5.62).
- {#C5.8-5} A real member U″_k, U^0_k, U_{k,Λ}, U_1, or U_k of the large-field note's multiscale minimisers (CRE's multiscale U_k among them, its #4.219) at the real data of a young history with n ≥ n₀.
- {#C5.8-5-1} A member U_k, U^0_k, U″_k, U_{k,Λ}, or U_1 at the callers' complex data with n ≥ n₀′ on the margin ball sup_b abs(g_kCA(b)) ≤ m_k of #C8.2.2: U_k at the data V′V^{(k)} (its #4.521.2), the others at the averages of U_k(V′V^{(k)}) and the real integration variables. Bałaban's representation (for U_k) and Proposition 9 [15] (for the others, within 2^{−8} of the lift radius by c₂ ≤ c_N) put both runs' members within the bounds of #C5.8-6 on X^∼ (its #4.521.3 and #4.521.4).

{#C5.8-6} The bounds are (2.34), (2.36), (2.38), and (2.39) of CRE's class (p.261) at the radii r⁺ := (9/8)r of its layers, with the current at most r⁺_{0,m}/C_{Q*} in the normalisation of (2.36).
{#C5.8-7} These are the minimisers themselves (w = 1).
{#C5.8-8} The kinds are restricted to these data because the lift condition is derived at every scale j ≤ p exactly there.
{#C5.8-9} At the single-scale minimisers it is derived at real data by #C5.52–#C5.59 and at data V′V₀ by #C5.61–#C5.66, both uniformly in k. At the multiscale ones it is derived at every generation j ≤ m of a point of the layer m by that note's #4.328 and #4.521, with the tail of ι_X bounded through the class on the collar of X^∼ (its #4.323, under L ≥ 8d + 6 and its (T-M₁)).
{#C5.8-10} In the histories with n < n₀ at real data, or n < n₀′ at complex data, that note bounds the run difference as a whole (at real data its #4.554, at complex data *Small n.*, its #4.520), and their multiscale minimisers are not literal points.
{#C5.8-11} At real data whose plaquettes are of the order of the class radii, or at V′ of another form, #C5.52–#C5.66 give no lift condition, and such points are not literal points.
{#C5.8-12} The large-field note's members at its other complex points, U^0_k (the minimiser of LFR II's determining set 𝐁″_k, its #4.516), U″_k, U_{k,Λ}, U_1, and U_k at general points of its class and at the data of the arguments of the kinds (R2), (N), and (R3) below, are not literal points either; its #0.1 bounds their complex parts by a contraction along the chains; the representatives W^u of U″_k, U_{k,Λ}, and U_1 lie in the orbits of the members, on which Δ is constant.
{#C5.8-13} That note forms their ι_X lift only at the generations m/2 < j ≤ m of a point of the layer m (its #4.219-1, #4.472, and #4.521.4), and it reads RΔ at them on 𝒫_j(X; r⁺) with the size parameter d⁺ := max(d, 2) of the plain class bound, not d_j (its #4.472).
{#C5.8-14} Its member U_k at the callers' data V′V^{(k)} is the minimiser at the data of the fluctuation integral, of the kind (R1) (its #4.521.2) on the margin ball of #C8.2.2, the ball on which §8.2 reads the age factor, where Bałaban's representation puts both runs' minimisers within the bounds on X^∼ (its #4.521.3).
{#C5.8-15} Its class Ũ^c_k(Y₄, ·) imposes them on Y₄ only, and X^∼ exceeds X by one layer of M₁-cubes of the scale j, so at the other callers' data that note reads U_k as its members at general points of its class, with d⁺ (its #4.521.4, #4.454.12).
{#C5.8-16} (R2) The same with a local minimiser U_p(□′₀, 𝐕) at data of the kinds of (R1) in place of the minimiser, □′₀ := (□′)^{∼5} the near domain of a cube □′ of a scale n ≥ p, U_p(□′₀, ·) being built on the sequence □′₀ ⊃ □′₁ ⊃ ⋯ ⊃ □′_n of that cube (RG I p.273 l.39–42), with X^∼ ⊂ (□′)^{∼4}, where the constraints are those of the scale p ((□′)^{∼4} ⊂ □′_n ⊂ □′_p, p.273 l.41).
{#C5.8-17} These are the composites and Lemma 4's configurations, whose literal points are their transforms exp iξ𝐇, with real part 1, by the gauge u_j of (I.3.37) and the gauges v_j, v, and ū_{k+1} of (I.3.39) (RG I p.278 l.14–25), within the bounds by *Mixed radii.* and *The outputs in the norm class.* (#C5.28; RG I p.277 l.54–55), the current bound being Bałaban's at the reduced thresholds (#C5.12).
{#C5.8-18} (N) A pair (exp iξ𝐀, 𝐅(𝐀)) of the function (I.3.13) at 𝐔 = 1, 𝐉 = 0, with 𝐀 on (I.4.4) at α_{2,j} (RG I p.281 l.36–41), here α_{2,j} = c₂α_{0,j} at Bałaban's thresholds, which is above its value at the radii r, so the inclusion checks below are conservative; this kind (N) of point is not the near-domain condition (N) of #C5.23, which is always said of a near domain ("satisfies (N)").
{#C5.8-19} (R3) A pair (exp iη𝐀𝐔′, 𝐉′ + 𝐉_𝐀) over a base (𝐔′, 𝐉′) of one of two kinds: a literal point of the kind (R1) or (R2) of a top index p > j for a domain containing X^∼, whose constraints on X^∼ have the scales > j; or a member of the large-field note of the kind (R1) at a generation j ≤ m of a point of its layer m, whose entries on X^∼ are at most 0.26 of the thresholds of the scale j and whose lift is within 7/16 of them (that note's #4.324, #4.328, and #4.521). The room below uses only these bounds on the scales of the constraints.
{#C5.8-20} Here a ≤ 0.8, 𝐀 has |𝐀| and |∇𝐀| at most aα_{2,j} in the L^{−j}-scale, ∇ covariant at 𝐔′, and the current increment 𝐉_𝐀 is at most C₁₃aα_{2,j} in the normalisation of (I.1.14).
{#C5.8-21} These are the configurations at which §8.2 reads the far domains, and the current variable is moved as in (I.3.11)–(I.3.13) (RG I p.272 l.14–33).
{#C5.8-22} Every evaluation of a term against its norm is at a point of ℰ.
{#C5.8-23} RΔ and RΔ^c read the term at Lemma 4's configurations (R2), at the configuration itself on the near and far domains ((R1), the callers' configurations, the composites of their own data being equal to them on □₀, #C5.26), at U = 1, and at the points (N) of the Taylor coefficients (I.4.3), which also give Δβ in §8.3.
{#C5.8-24} The large-field note reads it against d_j at its real members with n ≥ n₀ (its #4.226), at its members at the callers' complex data on the margin ball of #C8.2.2, of the kind (R1), at the composites over them, of the kind (R2), and at its comparison configurations c̃ at the near domains at ∂Y_i over these members, points (R3) (its #4.472, #4.454, #4.521); at its members at other complex points, the callers' U_k at the other data among them, it uses d⁺ on the variant class 𝒞⁺_k (above, #C5.15).
{#C5.8-25} The other evaluations use only the plain class bound |Δ(X, ·)| ≤ 2E₀exp(−κd_j(X)) on 𝒫_j(X; α′), not d_j: G and 𝐄^A satisfy (I.1.18) on their classes, which the lift reaches (#C5.6–#C5.7), run B's generation j + 1 on run A's lattices of generation j (#C1.1).
{#C5.8-26} These evaluations are the far domains at the large-field note's decoupled configuration W = e^{iξ𝐀^A}c^A (its #4.233) and run B's term on the polydiscs of the large-field note's *The age factor.*; for Δ those polydiscs read d_j, their points being points (R3) over (1, 0) (its #4.454).
{#C5.8-27} The points (N) and (R3) lie in 𝒫_j(X; r) for c₂ ≤ c_N := (128B₃²C₁₃C_{Q*}O(1))^{−1}.
{#C5.8-28} Here C₁₃ ≥ 1 is the constant of the moves of (I.3.13) (§8.2), and the O(1) of c_N is at least max(1, B₅/B₃) times the constant of the data moves below, B₅ the constant of VAR (173) (p.305 l.39–42).
{#C5.8-29} Each point is its own representative in the definition of 𝒫_j.
{#C5.8-30} At (N) the real part is 1 and A′ = 𝐀.
{#C5.8-31} So (i)–(ii) hold with |𝐀|, |∇𝐀| ≤ α_{2,j} ≤ r_{1,j}/8, since α_{2,j} = c₂α_{0,j} and r_{0,j} ≤ r_{1,j}.
{#C5.8-32} The plaquettes are at most O(1)α_{2,j}, and the current 𝐅(𝐀) is at most C₁₃α_{2,j}.
{#C5.8-33} The lift ι_X(exp iξ𝐀) is the one-step minimiser of the data exp iξ𝐀 on X^∼ (#C9.8.6).
{#C5.8-34} By Proposition 9 [15] (VAR p.309 l.8–16) at the real data V₀ = 1, its orbit contains exp iη𝓗, reached by a gauge with ‖Ad(ṽ^{±1})‖ ≤ e^{β_I} (*The lift gauges.*, #C5.47), with real part 1 and A′ = 𝓗, and 𝓗 satisfies VAR (19)–(21) with ε₂ = B₅ε₁ (p.305 l.39–42, p.281 l.6–17), ε₁ the size of the data.
{#C5.8-35} So |𝓗| and |∇𝓗| in the units of the layer, and the plaquettes and the current as in (1.17), are at most 2max(B₃, B₅)O(1)α_{2,j} ≤ r_{0,j}/(8C₁₃C_{Q*}).
{#C5.8-36} At (R3), exp iη𝐀𝐔′ has the real part of 𝐔′, and its complex factor is exp iηA″ with A″ = 𝐀 + A′ + commutators (Baker–Campbell–Hausdorff).
{#C5.8-37} So its conditions (i)–(iii) are those of 𝐔′ moved by at most C₁₃aα_{2,j}(1 + O(α_{0,j})) ≤ ¼r_{0,j}/C_{Q*}, the commutators being paid by the slack between C₁₃aα_{2,j} ≤ α_{0,j}/(160B₃C_{Q*}) (c₂ ≤ c_N with a ≤ 0.8, B₃ ≥ 1, and the O(1) of c_N ≥ 1) and ¼r_{0,j}/C_{Q*} = α_{0,j}/(32B₃C_{Q*}), for γ small: the plaquettes move by the covariant curl of 𝐀 plus commutators, A″ and ∇A″ by |𝐀| and |∇𝐀| plus commutators, and the current by 𝐉_𝐀.
{#C5.8-38} Those of 𝐔′, a literal point of a top index p > j at the radii r⁺, read at the scale j, are at most (9/8)(1+β₀)²(n−j)^{1/2}L^{−(n−j)} ≤ (9/8)·0.66 < 0.745 times the thresholds of the scale j at a point of the layer n, j < n ≤ p (#C5.27).
{#C5.8-39} The cube condition of the real part is included, its gauge field and gradient carrying L^{j−p} and L^{2(j−p)}.
{#C5.8-40} So they are at most 0.745 + 0.25 < 1 times the thresholds of the scale j.
{#C5.8-41} The data of ι_X(exp iη𝐀𝐔′) differ from those of ι_X𝐔′ by at most O(1)aα_{2,j}, since M^·(Q₁^{s*}·) is a product of bond variables along contours.
{#C5.8-42} So by Proposition 9 [15] and Cauchy's estimate in the data on half its polydisc, the orbit of ι_X(exp iη𝐀𝐔′) contains the representative of the orbit of ι_X𝐔′ shifted by a complex factor exp iη𝓗.
{#C5.8-43} The field 𝓗 has |𝓗| and |∇𝓗|, and its moves of the plaquettes and the current as in (1.17), at most 4max(B₃, B₅)O(1)aα_{2,j} ≤ α_{0,j}/(40B₃C₁₃C_{Q*}) for c₂ ≤ c_N, a ≤ 0.8, below ¼r_{0,j}/C_{Q*} = α_{0,j}/(32B₃C_{Q*}) with the slack that pays the commutators below, for γ small.
{#C5.8-44} The real part, and with it the cube condition, is unchanged, and A′ moves by 𝓗 plus commutators.
{#C5.8-45} This is below the room of the lift condition at 𝐔′ at the scale j.
{#C5.8-46} At the kinds (R1) and (R2) that condition is derived at every scale j ≤ p (#C5.52–#C5.66, #C5.63–#C5.64, and the large-field note's #4.328, #4.521, and #4.540). The lift is run B's configuration of the same kind moved by 𝔰_{p,j}, and at the multiscale points also by the tail of ι_X. The move 𝔰_{p,j} is o(α_{0,j}) at this note's minimisers (#C5.57, #C5.64) and at most 1/64 of the r-thresholds at the large-field note's multiscale points, n₀ and n₀′ being taken so large there (its #4.554 and #4.521). The tail is at most r_{0,j}/32 (that note's #4.323 at real points and #4.521 at complex points).
{#C5.8-47} Run B's quantities, read at the scale j from its layers n > j, are at most (9/8)·0.66 < 0.745 of run B's thresholds as run A's are of run A's (#C5.27), and run B's thresholds are at most 1 + o(1) times run A's by |δ| ≤ ε_γg^{−2} (#C5.7) and CRE (2.28). So the room is at least 0.255 − 1/32 − 1/64 − o(1) > 0.205, above the move's 4max(B₃, B₅)O(1)aα_{2,j}/r_{0,j} ≤ 1/(5C₁₃C_{Q*}) ≤ 0.2 of the thresholds.
{#C5.8-48} At a member base of the large-field note the entries are at most 0.26 < 0.745 of the thresholds and the lift, the move and the tail of ι_X included, is within 7/16 of them, so the room is at least 9/16.
{#C5.8-49} The orbit of the lift is reached from ι_X(exp iη𝐀𝐔′) by the gauge of 𝐔′ times that of Proposition 9 for the data move, at most e^{β_I}·e^{β_I} = e^{2β_I} (*The lift gauges.*, #C5.47).
{#C5.8-50} The callers' points are of these kinds: §8.2's backgrounds are points of ℰ_{k+1} (#C8.2.2), the callers' configurations are minimisers at the support's real data or at the data of the fluctuation integral, the minimisers U_k(exp i[g_kCA − hD̃(g_kCA)]V^{(k)}) at the complexified integration variables A about the support's data V^{(k)}, at which the large-field note's callers read the age factor (its #4.454), and Lemma 4's composites and outputs over them (#C5.48–#C5.50).
{#C5.8-51} The large-field note forms its lift at complex points only for n ≥ n₀′ (its #4.514) and at real points only for n ≥ n₀ (its #4.226 and #4.554), bounding the run difference below these as a whole by Bałaban's bounds per point (*Small n.*, its #4.520, and its #4.554), with no evaluation against d_j.
{#C5.8-52} At general points of 𝒫_j(X; r) no bound with the age factor is derived or used (#C5.16).
{#C5.8-53} Δ depends on 𝐔 on X^∼, not on X alone.
{#C5.8-54} The proof below uses the localisation only to split the domains into the near ones, X ⊂ □̃², and the far ones.
{#C5.8-55} A near X has X^∼ ⊂ □̃³: X^∼ exceeds X by one layer of M₁-cubes of the scale j (CRE (2.13), p.257 l.9–11), M₁ < M (CRE p.245 l.35–37), and the layers of □̃³ have the width ML^n ≥ ML^j.
{#C5.8-56} RG I's output conditions hold on □̃³ (p.277 l.55), "hence on X".

{#C5.9} The class of (5.1c) is the set 𝒞_k of pairs (𝐔, J(𝐔)) on T_η with two properties.
- {#C5.10} (a) For every localisation domain X ∈ 𝐃_j of the sum Δ(Λ_j, ·, z), the restriction to X^∼ lies in the evaluation set ℰ_j(X; r) of the norm class 𝒫_j(X; r).
  {#C5.10-1} The near part irr_□ of *The composites over 𝒮_z.* reads only the near domains X ⊂ □̃², so for (5.1c𝐀) (a) is required on them only.
- {#C5.11} (b) A configuration 𝐔₀ = 𝐔^{h^{−1}} of the G^c-orbit of the pair on □₀ satisfies the bounds (2.34), (2.36), (2.38), and (2.39) of Bałaban's multiscale complex class (CRE p.261), not its (2.35) and (2.37), which the analysis on □₀ does not use (#C5.27), with the top index k as in (3.43), on the cube □₀ of z (RG I's proof uses the conditions on □₀ only, *The near domain*, #C5.21), with r_{0,m} in place of α_{0,m} and r_{1,m} in place of α_{1,m}.
  {#C5.11-1} The near domains at a finer layer are read at the scale n − 1 (*The near domains at a finer layer.*).
  {#C5.11-2} RG I's analysis on □₀ is run at 𝐔₀: its input space U′^c_{k+1}(□₀, …) is a union of G^c-orbits (RG I p.262 l.12–13), and the bounds below are derived at 𝐔₀.
  {#C5.11-3} They transfer to 𝐔 through c(𝐔, 𝐀) = c(𝐔₀, 𝐀^h)^{h̄} and the G^c-invariance of Δ (#C9.8.18-5), with 𝐀^h := Ad(h^{−1})𝐀 pointwise (*The composites over 𝒮_z.*).

{#C5.12} Condition (a) is the domain of every term of the sum, and (b) is what RG I's analysis on □₀ uses.
{#C5.12-1} The radii in (b) are of the form (2.28) with C_i divided by 8B₃, and the current bound r_{0,j}/C_{Q*} of (a) is of that form with C₀ divided by 8B₃C_{Q*}.
{#C5.12-2} So Bałaban's statements hold at them, by `WILSON_IT1_LARGE_FIELD_DEPTH_2026_10_27.md` §4(d), *Bałaban's Statements at the Reduced Thresholds*, once C₀ and C₁ are at least λ_Q := max{1, 4B₃, 8B₃, 2^{13}B₃²L³, 64B₃C_{Q*}, C_mem} times his lower bounds, C_mem the constant of that note's *The conditions.*
{#C5.12-3} Run A's part of (a) and (b) at the callers' configurations is then Bałaban's. At real minimisers it follows from his statements at his own thresholds and the current bound of *The lift condition.* At complex points the callers place the configurations in CRE's class at the radii r (the large-field note's §4(d), *The age factor.*), whose bounds are (b).
{#C5.12-4} Lemma 4 at radius r needs the restriction to □₀ in U′^c_{k+1}(□₀, (1+2β_I)r_{0,n}, (1+2β_I)r_{1,n}, r_{0,n}), whose condition (iv) is (1.16) on the maximal sequence of □₀ (RG I p.262 l.41–55, p.275 l.19–21).
{#C5.12-5} Bałaban does not print that his class lies in it: CRE p.276 l.2–16 states that the formulas and bounds of Sects. 3–4 [I] hold with η replaced by L^{−n}, "the difference shows up in bounds only", and RG I p.275 l.19–21 states analyticity on U′^c(□₀, …); his class carries (2.35) and (2.37) on the determining sets 𝐁_p(X), and (1.17) gives (iv) only at the cost 2B₃ (p.263 l.7–22).
{#C5.12-6} The inclusion is derived below for the configurations at which RΔ^c is used: the proof of Lemma 4 uses (iv) only through (3.40) (#C5.22), and on 𝒮_z (3.40) is the configuration's own (iii) up to the adjoint action of a gauge g with ‖Ad(g)‖ ≤ e^{β_I} (#C5.26).
{#C5.12-7} The inclusion is derived only at the points of 𝒮_z that satisfy (b) at radii at most r⁺ = (9/8)r, and it is used only there: by RΔ^c at the callers' configurations (the large-field note's §4(d), *The age factor.*), and in §8.2 at the backgrounds 𝐔̂_z of the points of ℰ_{k+1} (#C5.8, #C8.2.2), whose fluctuation enters through the composites of (5.1c𝐀) (#C5.43), not at general points of RG I's class or of CRE's (3.43).
{#C5.12-8} He evaluates the terms at U_k on every X (CRE p.259 l.40–44) and at the configuration of (3.15) (p.279 l.43–44). For the terms whose domains are not contained in Λ_{k+1}, which go into 𝐁^{(k+1)} (table #T11.12-2), §8.2 uses only the bound a_k of the activities on the cutoff ball, which is p.277's bound on the support (O6 closure §5a(i)).
{#C5.12-9} The lift part of (a) is *The lift condition* below.
{#C5.12-10} Below, α_{·,m} stands for r_{·,m}, and Lemma 4 is run at these radii.

{#C5.13} *The regular subclass.* 𝒮_z is the set of pairs (𝐔, J(𝐔)) of the class, J(𝐔) the current of 𝐔, whose restriction to □₀, in a G^c-valued gauge on □₀, is the local minimiser of its own block data at the scale of the layer, 𝐔 = U_n(□₀, M^·(𝐔)), or, where □₀ meets the layer n − 1, at the scale n − 1, 𝐔 = U_{n−1}(□₀, M^·(𝐔)) (*The near domains at a finer layer.*).
{#C5.13-1} Here U_n(□₀, ·) is RG I's local function U_j(□₀) of p.273 l.39–42 built at the scale n: a sequence of cubes □₀ ⊃ □₁ ⊃ ⋯ ⊃ □_n satisfying (1.3)–(1.6) [14] in the L^{−n}-scale, with the averages M^p(𝐔) of the scales p ≤ n as data, extended as equal to 𝐔 outside □₀ (RG I p.275 l.4–7).
{#C5.13-2} This is CRE's layer form of RG I's construction, as CRE prints it: U_k "restricted to Ω_n∖Ω_{n+1} coincides with a U_n-type configuration", and (I.3.18)–(I.3.28) are applied with η replaced by L^{−n} (CRE p.280 l.14–20, p.276 l.9–14) and with η𝐇_k in place of L^{−1}η𝐇_{k+1} (p.280 l.17–19).
{#C5.13-3} Bałaban writes the same representation at the scale j in his second proof of Theorem 2, U_k = U_{j,□₀}(M^·(U_k)) (p.283 l.47–48).
{#C5.13-4} On □₀ ∩ Ω_{n+1} the data of the scale n determine the configuration's own data of the scale n + 1, since M^{n+1} = M∘M^n, so they are finer constraints there.
{#C5.13-5} The scale is that of the layer, not k: for k ≫ n the cube sequence of U_k(□₀, ·) does not fit in □₀.
{#C5.13-6} These are the configurations at which RG I's Lemma 4 evaluates a term in CRE's layer form, with 𝐀 = 0 in (I.3.30): the composite is then the configuration itself, and its C^{1,β_H} regularity is (I.3.27), at a fixed Hölder index 0 < β_H < 1 not above RG I's Hölder limit there, written β^H_0 here (RG I's β₀ of (I.3.27) and (I.4.18), not CRE's β₀ of (2.6)–(2.7)).
{#C5.13-7} 𝒮_z contains the pairs (U_k(𝐕), J(U_k(𝐕))) of the class at complex data 𝐕. At real data a minimiser is the local minimiser of its own block data, as in (I.3.18) (RG I p.273 l.44–46), which CRE applies at the layer n (p.280 l.14–16). At complex data the identity holds by analytic continuation, both sides being analytic in the data.
{#C5.13-8} A family t ↦ U_n(□₀, 𝐕(t)), extended as equal to a fixed configuration of the class outside □₀, at holomorphic complex data stays in 𝒮_z as long as its pairs stay in the class, since M^·U_n(□₀, 𝐕) = 𝐕 on the constrained bonds.
{#C5.13-9} The class bound RΔ^c, derived below, is

{#C5.14} (5.1c) |irr(Δ)(U)| ≤ d · E₁(α) (L^{j−n})^{4+β′}, E₁(α) := C_αE₀,

{#C5.15} for every U in 𝒮_z whose near domain □₀ satisfies the condition (N) below.
{#C5.15-1} The constant C_α is that of *The constant.* below, uniform in j, n, k, K, and the volume.
{#C5.15-2} The composites of the scale j at the data exp iQ(η𝐀)M^·(U), U in 𝒮_z and 𝐀 in the class (I.3.31), satisfy the same bound on the near domains with 6⁵C_α ((5.1c𝐀), *The composites over 𝒮_z.* below).
{#C5.15-3} The variant class 𝒞⁺_k is defined by (b) at the radii r⁺ := (9/8)r and by (a⁺): for every X of (a), the restriction to X^∼ lies in the norm class 𝒫_j(X; r⁺), its lift half included, in place of ℰ_j(X; r). 𝒮⁺_z is defined from 𝒞⁺_k as 𝒮_z is from 𝒞_k.
{#C5.15-4} On 𝒮⁺_z, (5.1c) and (5.1c𝐀) hold with the size parameter d⁺ := max(d, 2) in place of d and with C_α at the radii r⁺, Lemma 4 being run at the input radii ρ = r⁺ with α₂ and α₃, and with them the composites' field 𝐀 of (I.3.31), kept at their values at the radii r (#C5.28), derived in the large-field note's #4.454: there Δ satisfies the hypothesis of RΔ on 𝒫_j(X; r⁺) ⊂ 𝒫_j(X; α′) with d⁺ by its analyticity there (#C5.7) and its plain class bound (#C5.8).
{#C5.15-5} That note reads its points that are not literal points of ℰ_j (#C5.8) in 𝒞⁺_k (its #4.454, #4.472, and #4.540).

{#C5.16} (5.1c) is stated on 𝒮_z and not on the whole class: the class bounds the configuration's first derivatives and its current, not a Hölder norm of ∇A, and the power beyond (L^{j−n})⁴ comes from the C^{1,β_H} regularity of the background ((I.3.27), (I.3.32), (I.4.18)); Bałaban states Theorem 2, (2.43), "for β<1, and sufficiently regular configurations U_k=U_k(V)" (CRE p.263 l.19).

{#C5.18} *Bałaban's analysis on complex configurations.* RG I Lemma 4 (p.280 l.24–32) takes 𝐔 ∈ U′^c_{k+1}(□₀, (1+2β_I)α₀, (1+2β_I)α₁), the space of p.277 l.34 (there with the fourth argument α₀), together with a 𝔤^c-valued 𝐀 satisfying (I.3.31) and a complex B′ with |B′| < α₃.
{#C5.18-1} It states (I.3.53) and "The functions in (3.53) are analytic on the above spaces".
{#C5.18-2} Here β_I is RG I's class parameter, not the exponent β of (3.67).
{#C5.18-3} RG I p.281 l.3–4 states that the remaining terms are irrelevant, "i.e. they satisfy bounds of the form (0.29) on their domains of analyticity".

{#C5.19} In CRE's proof of Theorem 2, 𝐀 = 0 in (I.3.30), and L^{−1}η𝐇_{k+1} is replaced by η𝐇_k (p.280 l.17–19).
{#C5.19-1} The background is therefore the field A of (I.3.30), built from U_k: "The function L^nηA, where A is defined by (I.3.30), satisfies the bound (I.3.32), but in the L^{−n}-scale instead of the η-scale" (p.280 l.19–20).
{#C5.19-2} That bound is stated with the class parameters, the background obeying the bounds of (I.3.31) "with α₂ replaced by B₃O(1)Mα₀, and □₀ by □̃⁴" (RG I p.276 l.42–43).
{#C5.19-3} So the real proof already measures the background's amplitude in the units of the class; its Hölder regularity is a property of the composite minimiser, which is why the bound is stated on 𝒮_z.

{#C5.20} The field U_k "may depend on the fluctuation field, as in the exponential in (3.15)" (CRE p.279 l.43–44).
{#C5.20-1} The expressions needed in the fluctuation integral come from the derivative in t_□ (p.283 l.23–25), the parameter multiplying the fluctuation field inside the configuration (RG I (3.28)).
{#C5.20-2} RG I p.280 l.47–49 bounds that derivative by "a factor O(1)α₂^{−1}ε₁".

{#C5.21} *The near domain.* The bounds below use that the restriction of U to □₀ satisfies, in the L^{−n}-scale, the conditions of RG I's space U′^c_{k+1}(□₀, (1+2β_I)α_{0,n}, (1+2β_I)α_{1,n}, α_{0,n}) on □₀, with α = r the radii of the norm class.
{#C5.21-1} That space asks (i)–(iii) "on the whole lattice T_η" (RG I p.275 l.20–21).
{#C5.21-2} The global conditions enter RG I's proof only through the objects that depend on the configuration on the whole lattice, "The function 𝐇_k and the averaging operations Q_j in the definition of B̃_□" (RG I p.275 l.3), which enter (I.3.24)–(I.3.25) only through B̃_□ of (I.3.22), the field 𝐇_k(B′) of (I.3.25) and its averages, so they vanish with 𝐇_k(B′). 𝐇_k(B′) is built from the propagators of the whole lattice: its operators are those of VAR (179)–(180), with 𝐔, 𝐉 in place of U_{k+1}, J_{k+1} (RG I p.273 l.2–3).
{#C5.21-3} In CRE's layer form 𝐇_k(B′) = 0 (p.280 l.17–18).
{#C5.21-4} The remaining objects of (I.3.25)–(I.3.32) are functions of 𝐔 restricted to □₀: the averages M^·(𝐔) with their axial gauge v of (I.3.26) and the gauge u_{k+1} of (I.3.27) ("explicitly given analytic functions of 𝐔, depending on 𝐔 restricted to the cube □₀", p.276 l.14–15), and the local minimiser's field 𝐇(□₀, ·) of (I.3.27) and the composite of (I.3.30) at 𝐀 = 0.
{#C5.21-5} The proof states its input bounds on □₀ and □̃⁴ ((I.3.26)–(I.3.27)) and its output conditions on □̃³ (p.277 l.55).
{#C5.21-6} So its bounds hold for configurations that satisfy (i)–(iv) on □₀, and no extension outside □₀ is used.

{#C5.22} The proof does not use the cube condition (I.1.12).
{#C5.22-1} Its inputs on □₀ are the averages M^·(𝐔) with the axial gauge v of (I.3.26), the gauge u_{k+1} and the field 𝐇(□₀, ·) of (I.3.27), and the composite of (I.3.30).
{#C5.22-2} (I.3.26) repeats VAR Sect. F (RG I p.275 l.21–26), and VAR derives its axial-gauge bounds from the plaquette condition and Proposition 2 of [4] (VAR p.300 l.38–40), so it uses (I.1.11) for U, (I.1.14) for 𝐔, and |A′| < α₁ of (ii).
{#C5.22-3} VAR Sect. F concerns real minimal configurations, but RG I states (I.3.26) for 𝐔 in the complex space U′^c_{k+1}(□₀, (1+2β_I)α₀, (1+2β_I)α₁, α₀), on which it proves the analyticity of (3.25) (p.275 l.19–26): the bound |v − 1| < O(1)Mα₁ carries the parameter α₁ of the complex factor, and V is given by the contour variables, V(b) = Ū^{k+1}(Γ_{y₀,b₋} ∪ b ∪ Γ_{b₊,y₀}) (p.275 l.27–28), products of bond variables that are defined at G^c-valued bonds.
{#C5.22-4} So the complex version is Bałaban's statement.
{#C5.22-5} The VAR minimiser and (I.3.27) need only |V(b) − 1| < O(1)Mα₀ on the bonds of the averages.
{#C5.22-7} The outputs come from (I.3.37) and (I.3.50) for (i)–(ii), from (I.3.41)–(I.3.47) and (I.3.51)–(I.3.52) for (iii), and from the identity (I.3.38) for (iv) (p.277 l.55, p.278 l.12–13, p.280 l.6 and l.21); the output's real factor is 1, so its (I.1.12) holds with A = 0.
{#C5.22-8} The statement of p.275 l.6–7 that "all necessary theorems are valid for operations with this configuration" concerns those global operations, 𝐇_k and Q_j of p.275 l.3, which enter only through B̃_□, 0 at 𝐇_k(B′) = 0.
{#C5.22-9} So the membership needed is that of (I.1.11), (I.1.13), (I.1.14), and (iv) on □₀, and CRE's cube condition (2.38) is not among the inputs.
{#C5.22-10} The input's (iv) enters only through (3.40) (p.278 l.26–34): the bounds |∂U_{k+1}(□₀, M^·(𝐔)) − 1| < (1+2β_I)α₀(L^{−1}η)² and |J_{k+1}(□₀, M^·(𝐔))| < (1+2β_I)α₀ on □̃³, which feed (3.41)–(3.42) through (3.39).
{#C5.22-11} The gauges v, u_{k+1} and the field 𝐇_{k+1}(□₀, ·) of (3.26)–(3.27) are bounded from (i)–(iii) and the data M^·(𝐔) (p.275 l.21–39), the output's (iv) comes from its (iii) by (3.38) (p.278 l.12–13, p.280 l.21–22), and the words "(iv)" and "(1.16)" occur in pp.275–280 only in the definition of the space (p.275 l.20) and for the output (p.278 l.2, "all the conditions (i)–(iv)" of the output configuration; p.278 l.13, "the condition (iv) is a consequence of the condition (iii)" for it; p.279 l.49; p.280 l.21).
{#C5.22-12} So the real part's (iv) and (iv) off □̃³ are not used.

{#C5.23} The condition (N) is that □₀ lies in Ω_n, so that it meets no finer layer.
{#C5.23-1} Under (N) the membership follows from the condition (b) of the class:
- {#C5.24} On the layer n the radii are those of the layer, and the factor 1 − β_C(1 − 2^{−(k−n)}) ≤ 1 of (2.34)–(2.39) leaves the room 1 + 2β_I.
  {#C5.24-1} Here β_C is CRE's class constant ("e.g., we can take β=1/4", p.261 l.42), taken as β_C = 1/8; CRE's uses of its β are counted against 1/8 in `WILSON_IT1_LARGE_FIELD_DEPTH_2026_10_27.md` §4(d), *The choice β = 1/8, checked.*, and nothing below depends on the choice.
- {#C5.25} (2.34) gives the plaquettes of (I.1.11) and (I.1.14) at α_{0,n}.
  {#C5.25-1} (2.36) gives the 𝐉-bound of (I.1.14) with γ₀ = α_{0,n}, and (2.39) gives (ii) at α_{1,n}.
  {#C5.25-2} The normalisations agree: (2.34) is α_{0,n}ξ²(L^nξ)^{−2}, which is (I.1.11) in the L^{−n}-scale, and (2.37) at p ≥ n is (2.36) at the spacing L^{−p} (CRE p.261 l.10–22).
- {#C5.26} The condition (iv) on □₀, in the form (3.40) in which the proof uses it, follows on 𝒮_z from (iii).
  {#C5.26-1} By the definition of 𝒮_z, 𝐔^w = U_n(□₀, M^·(𝐔^w)) on □₀ for a G^c-valued gauge w on □₀.
  {#C5.26-2} The function U_n(□₀, ·) is covariant, U_n(□₀, M^·(𝐔^u)) = U_n(□₀, M^·(𝐔))^{ū} with ū constant on the blocks of the function and equal to u at their centres (RG I p.278 l.3–12, printed for his u_j); for G-valued u this is VAR's covariance, and for G^c-valued u it is VAR's (181), proved by analyticity near the G-valued u and taken as the definition on the rest of each orbit (VAR p.307 l.11–15; #C9.8.18), M^·(𝐔^u) depending on u only through its values at the centres.
  {#C5.26-3} With u = w^{−1} this gives U_n(□₀, M^·(𝐔)) = 𝐔^g, g := (w^{−1})‾·w, with the convention (𝐔^a)^b = 𝐔^{ba}, and g = 1 at the block centres.
  {#C5.26-4} On □̃⁴ ⊂ □_n (RG I p.273 l.41) the constraints are those of the scale n, on blocks of side L^nξ.
  {#C5.26-5} For x ∈ □̃³ let Γ be a contour of at most dL^n bonds in its block from the centre c to x, so that g(x) = 𝐔^g(Γ)^{−1}𝐔(Γ).
  {#C5.26-6} By (2.39) each bond factor of 𝐔(Γ) is U′(b)U(b) with U(b) ∈ G and |ξA′(b)| < α_{1,n}L^{−n}, so ‖Ad(𝐔(Γ))‖ ≤ exp(O(1)dα_{1,n}).
  {#C5.26-7} By (3.26)–(3.27) in the L^{−n}-scale, which use (i)–(iii) only, M^·(𝐔) = V^v and U_n(□₀, M^·(𝐔)) = (exp iξ𝐇)^h, h := v̄·u_n, with L^nξ|𝐇| < B₃O(1)Mα_{0,n} on □̃⁴, |v − 1| < O(1)Mα_{1,n}, and |u_n − 1| < B₃O(1)Mα_{0,n} on □₀, so ‖Ad(𝐔^g(Γ)^{−1})‖ ≤ ‖Ad(h(c))‖‖Ad(h(x))‖exp(O(1)dB₃Mα_{0,n}).
  {#C5.26-8} With B₃²O(1)Mα_{0,n} < ½α_{1,n} (RG I p.277 l.54), ‖Ad(g(x))‖ and ‖Ad(g(x)^{−1})‖ are ≤ exp(O(1)Mα_{1,n}) ≤ e^{β_I}, the same contour bound holding for g(x)^{−1} = 𝐔(Γ)^{−1}𝐔^g(Γ), under O(1)Mα₁ ≤ β_I (p.278 l.46), its O(1) taken at least that of this bound.
  {#C5.26-9} The identities ∂(𝐔^g) − 1 = Ad(g)(∂𝐔 − 1) and J(𝐔^g) = Ad(g)J(𝐔) are algebraic and hold at G^c-valued g: a gauge transformation conjugates each plaquette product, and the current, the derivative of an action that is a sum of traces of plaquette products, transforms by Ad(g).
  {#C5.26-10} So (2.34) and (2.36) give |∂U_n(□₀, M^·(𝐔)) − 1| < e^{β_I}α_{0,n}ξ²(L^nξ)^{−2} and |J_n(□₀, M^·(𝐔))| < e^{β_I}α_{0,n}(L^nξ)^{−3} on □̃³, and e^{β_I} ≤ 1 + 2β_I for β_I ≤ 1.
  {#C5.26-11} This is (3.40) in the L^{−n}-scale at the radius of the space.
  {#C5.26-12} For the minimisers U_k(𝐕) the identity (I.3.18) holds with w = 1, and so it does for the composites of their own data on □₀ (#C5.13, and the large-field note's W, c̃, and c^□), so g = 1 there, and (3.40) is (2.34) and (2.36) themselves.
  {#C5.26-13} At the large-field note's representatives W^u, c̃^u, and (c^□)^u (its #4.454), whose transforms by u^{−1} are the members, g = ū·u^{−1}, with ū the block-constant transformation given by u at the block centres (VAR (181), p.307 l.7 and l.11–15; the large-field note's #4.518), and Ad(g) is within (1 + 2^{−9})² ≤ e^{2^{−8}} ≤ e^{β_I} of isometric (its #4.454 and #4.536), β_I := 2^{−7} being fixed, a choice that RG I allows, its conditions on β_I being the lower bounds O(1)Mα₁ ≤ β_I and (4B₃²O(1)M)²α₀ ≤ β_I that γ small gives (#C5.28), so there (3.40) follows from (2.34) and (2.36) as above.
- {#C5.27} On the layers n + p, p ≥ 1, the bounds of (2.34), (2.36), and (2.39), rescaled to the L^{−n}-scale, are ≤ (1+β₀)²p^{1/2}L^{−p} ≤ 1 times those of the layer n, compared directly with the room at the layer n, by CRE (2.6)–(2.7) at the distance p, for L ≥ 2 and β₀ ≤ 1/7: at p = 1 it is (64/49)·½ < 0.66, and p^{1/2}L^{−p} decreases in p. The power L^{−p} is the worst over the conditions (L^{−2p} in (2.34), L^{−3p} in (2.36), L^{−p} and L^{−2p} in (2.39)).
  {#C5.27-1} (2.35) and (2.37) are not used, since (3.40) comes from (iii) on 𝒮_z.

{#C5.28} *Mixed radii.* Lemma 4 maps its space at the radii (α₀, α₁) into U^c_j(X, α₀, α₁) at the same radii, while here the input carries the layer-n radii and the term is analytic at the scale-j radii (CRE p.259 l.41–42).
{#C5.28-1} At n = j Lemma 4 does not apply: its margin (1 + 7β_I)L^{−2} ≤ 1 rests on L^{j−1}η ≤ L^{−1} (RG I p.279 l.28), and the replacement factor is L⁰ = 1, so (I.3.47) gives (1 + 7β_I)α_{0,j}ξ² > α_{0,j}ξ².
{#C5.28-2} There (L^{j−n})^{4+β′} = 1, and irr(Δ) is bounded directly.
{#C5.28-3} Σ_X|Δ(X, U, z)| ≤ O(1)dE₀, since by the condition (a) of the class U lies in the evaluation set ℰ_j(X; r) of every X. The same holds at U = 1, where ι_X1 = 1, and |Δβ A(h_z, U)| ≤ O(1)dE₀c₂^{−2}, and the same holds for N(U), a sum of 36 plane-pair actions with coefficients at most 2 sup|Π^Δ|, so (5.1c) holds at n = j with C_α ≥ O(1)(2 + c₂^{−2}), the O(1) counting these 36 pieces.
{#C5.28-4} At a □₀ that meets the layer n − 1 the same direct bound covers j = n − 1 and j = n, where (L^{j−n})^{4+β′} ≥ L^{−(4+β′)}, so (5.1c) holds there with C_α ≥ O(1)(2 + c₂^{−2})L^{4+β′}.
{#C5.28-5} For n > j, α_{i,n} ≤ (1+β₀)²(n−j)^{1/2}α_{i,j} (*The constant.*), and in CRE's layer form the inequalities (I.3.37)–(I.3.52) carry a factor at most L^{j−n} in place of RG I's L^{j−1}η, squared in (I.3.41) and (I.3.43)–(I.3.47) and cubed in (I.3.42).
{#C5.28-6} Since (1+β₀)²m^{1/2}L^{−m} ≤ 1 and (1 + 7β_I)(1+β₀)²m^{1/2}L^{−2m} ≤ 1 for m ≥ 1, L ≥ 2, β₀ ≤ 1/7, and β_I ≤ 1/4, each conclusion of the proof holds with the scale-j radii on its right-hand side.
{#C5.28-7} The steps (I.3.51)–(I.3.52), with the factors 1 + 6β_I and 1 + 8β_I and 2B₃⁺α_{3,j} = β_IL^{−2}α_{0,j}/C_{Q*} ≤ β_IL^{−2}α_{0,j} (#C5.37), hold the same way.
{#C5.28-8} The α₃-term 2B₃⁺α_{3,j} ≤ β_IL^{−2}α_{0,j} is fixed at the scale j and carries no factor m^{1/2}L^{−2m}, so the bound is (1 + 7β_I)(1+β₀)²m^{1/2}L^{−2m} + β_IL^{−2} ≤ (11/4)(64/49)/4 + 1/16 < 0.97 at m = 1, L = 2, and it decreases in m.
{#C5.28-9} In particular |𝐇_j| < B₃²O(1)Mα_{0,j} in (I.3.37), which with B₃²O(1)Mα_{0,j} < ½α_{1,j} gives (i)–(ii) at the scale j, and the bound (1 + 7β_I)α_{0,j} of (I.3.47) holds.
{#C5.28-10} The smallness conditions O(1)Mα₁ ≤ β_I and (4B₃²O(1)M)²α₀ ≤ β_I (RG I p.278 l.46 and l.64) are taken at the radii of the layer n, and the restrictions on α₃ of (I.3.51) at the scale j.
{#C5.28-11} At a □₀ that meets the layer n − 1 all of this holds with n − 1 in place of n, m = n − 1 − j ≥ 1, and LM in place of M (*The near domains at a finer layer.*).
{#C5.28-12} *The outputs in the norm class.* The current bound at general τ ∈ [0, 1] and in its B′-part is Bałaban's bound B_J (#C5.37-9). §8.2 reads d_j at Lemma 4's outputs from inputs whose condition (b) holds at radii ρ ≤ r⁺ = (9/8)r: the kinds (R1) and (R2) at r⁺, and (R3) at at most 1.01r (#C8.2.2). d_j is taken on ℰ_j(X; r) ⊂ 𝒫_j(X; r) (#C5.8), so the outputs must satisfy the conditions at the radii r, not only at the radii ρ that the factors above give.
{#C5.28-13} For n > j Lemma 4 is run at the input radii ρ, taken in [r, r⁺] (an input with (b) at radii below r satisfies it at r), with α₂ and α₃ those of the run of RΔ^c at the radii r (#C8.2.2), below their values at ρ and so admissible (Bałaban's α₂ and α₃ are only "sufficiently small", p.279 l.47–49, p.280 l.31); the large-field note's run of RΔ at (9/8)r (its #4.454.11-1, #4.473) is the case ρ = r⁺.
{#C5.28-14} The sharper factors then give the inclusion.
{#C5.28-15} For (i)–(ii), |𝐇_j| < (1+β₀)²m^{1/2}L^{−m}B₃²O(1)Mρ_{0,j} ≤ 0.66·½ρ_{1,j} in (I.3.37), and |𝐀₂| ≤ B₃α_{3,j} ≤ B₃⁺α_{3,j} ≤ ½β_IL^{−2}ρ_{0,j}/C_{Q*} ≤ 2^{−10}ρ_{1,j}, so (i)–(ii) hold at (0.33 + 2^{−10})ρ_{1,j}.
{#C5.28-16} For the plaquettes of (iii), (I.3.51)–(I.3.52) at β_I = 2^{−7} (#C5.26), not at β_I ≤ ¼, give ((1 + 8β_I)(1+β₀)²m^{1/2}L^{−2m} + β_IL^{−2})ρ_{0,j} ≤ ((17/16)(64/49)/4 + 2^{−9})ρ_{0,j} < 0.35ρ_{0,j}.
{#C5.28-17} For the current, whose threshold in the norm class is the reduced one, ρ_{0,j}/C_{Q*} (#C5.5), the second inequality of (iii) is "obtained in the same way" (RG I p.279 l.29) and "proved in the same way" (p.280 l.21), with two parts.
{#C5.28-18} The τ-part is the input's current carried through the identity (I.3.42) with (I.3.39)–(I.3.40), and the input's current is at most ρ_{0,n}/C_{Q*} at the kinds (R1), (R2), and (R3), so this part is at most (17/16)(64/49)/8 < 0.174 of the reduced threshold, L^{−3m} in place of L^{−2m}.
{#C5.28-19} The B′-part is at most 2B₃⁺α_{3,j} ≤ β_IL^{−2}ρ_{0,j}/C_{Q*} (#C5.37), which is 2^{−9} of the reduced threshold, the factor 1/C_{Q*} of α_{3,j} being chosen for this.
{#C5.28-20} So the current is below 0.18 of its threshold.
{#C5.28-21} These are the values at m = 1, L = 2, and β₀ = 1/7, and each decreases in m.
{#C5.28-22} Since ρ ≤ (9/8)r, each output condition is at most (9/8)·0.35 < 0.4 of its threshold at the radii r.
{#C5.28-23} The output's real factor is 1, so its cube condition holds with A = 0 (#C5.22).
{#C5.28-24} The lift condition at these outputs, the composites of #C5.50, is #C5.63–#C5.64: the lifted output is e^{i(ε/L)𝐒}U^B_{j+1}(□₀, ·), whose moves 𝔰_{k,j} = o(α_{0,j}) are uniform in ρ ≤ r⁺.
{#C5.28-25} So Lemma 4's outputs from these inputs, the composites among them, lie in 𝒫_j(X; r) through their representatives exp iξ𝐇_j with real part 1 (U_j(□₀, ·) = (exp iξ𝐇_j)^{u_j}, (I.3.37)), at which these bounds are stated, and they are points (R2) of ℰ_j(X; r).
{#C5.28-26} At a □₀ that meets the layer n − 1 the same holds with n − 1 in place of n.
{#C5.28-27} At n = j Lemma 4 is not used (above), and §8.2 bounds that case directly within the room 0.92 (#C8.2.2).

{#C5.29} This is the derivation for run A's term.
{#C5.29-1} For Δ, Lemma 4's output must also lie in run B's space through the pair lift, which is the lift condition at the composites (*The lift condition at complex configurations*).

{#C5.30} *The near domains at a finer layer.* At n = j the direct bound of *Mixed radii.* above covers every □₀.
{#C5.30-1} Let n > j, and let □₀ meet a finer layer m < n.
- {#C5.31} Only the layer n − 1 is met.
  {#C5.31-1} In the step n − 1 → n, CRE builds Ω_n inside the complement of Z′^{∼8}_{n−1}, Z_{n−1} = Λ_{n−1}^c: P¹_n has B^n(P¹_n) ⊂ (Z′^{∼5}_{n−1})^c (p.265 l.19–20), and (3.5) takes three more layers of LMR_n-cubes off it (p.265 l.40–45).
  {#C5.31-2} By (3.20) Λ_{n−1} ⊂ Ω_{n−1}.
  {#C5.31-3} So the distance from Ω_n to Ω_{n−1}^c is at least eight LMR_n-cubes of the step n − 1, that is 8R_n of the M-cubes of the scale n. □₀ is a cube of 11 such M-cubes containing z ∈ Ω_n, so it lies in Ω_{n−1} once 8R_n > 11d^{1/2}, which holds by (2.5) for g small.
  {#C5.31-4} So □₀ meets the layers n − 1, n, and the coarser ones only.
- {#C5.32} No point meets Ω₁^c.
  {#C5.32-1} Since j ≥ 1 is the index of a renormalisation step, n > j gives n ≥ 2, so □₀ ⊂ Ω_{n−1} ⊂ Ω₁, and the class (b) bounds every bond of □₀.
- {#C5.33} The scale. □₀ is evaluated at the scale n − 1 of the finest layer it meets.
  {#C5.33-1} On the layer n the bounds (2.34), (2.36), and (2.39), rescaled to the L^{−(n−1)}-scale, are those of the layer n − 1 times L^{−2} in (2.34), L^{−3} in (2.36), and L^{−1} for |A′| and L^{−2} for |∇A′| in (2.39), each times α_{·,n}/α_{·,n−1} ≤ (1+β₀)² ≤ 64/49 by CRE (2.6)–(2.7) at the distance 1.
  {#C5.33-2} So each is at most (64/49)L^{−1} < 0.66 times the radius of (b) at the layer n − 1, and the layers n + p, p ≥ 1, are below it by the last bullet under (N) with n − 1 in place of n.
- {#C5.34} The membership.
  {#C5.34-1} So (b) gives on □₀ the bounds of the first three bullets under (N) with n − 1 in place of n.
  {#C5.34-2} The identity of 𝒮_z is 𝐔 = U_{n−1}(□₀, M^·(𝐔)): a member's constraints on □₀ have the scales ≥ n − 1, so it is critical for the variations that preserve its data of U_{n−1}(□₀, ·), as in (I.3.18).
  {#C5.34-3} (3.40) follows from (iii) as in the fourth bullet under (N), at the scale n − 1: on □̃⁴ the blocks are those of the scale n − 1, and the bond factors of the contour satisfy |ξA′(b)| < α_{1,n−1}L^{−(n−1)} on the layers n − 1 and n by the scale bullet.
  {#C5.34-4} In the L^{−(n−1)}-scale the M-cubes of the scale n that make up □₀ have the side LM, so RG I's analysis runs with LM in place of M: the axial-gauge bounds (I.3.26)–(I.3.27) and the bounds of Sects. 3–4 [I] built on them carry O(1)LM in place of O(1)M, and so do the smallness conditions O(1)Mα₁ ≤ β_I and (4B₃²O(1)M)²α₀ ≤ β_I and the ratio conditions B₃²O(1)Mα₀ < ½α₁ and O(1)(α₂ + B₃O(1)Mα₀) < α₁, taken at the radii of the layer n − 1.
  {#C5.34-5} The expansion uses the identity as 𝐔 = U_j(□₀, M^·(𝐔)) for the generations j < n − 1, which follows in the same way, and the generations j = n − 1 and j = n are bounded directly (*Mixed radii.*).
- {#C5.35} The cost.
  {#C5.35-1} The evaluation at the scale n − 1 puts LM in place of M in C_r and ρ̄ (#C5.37, #C5.40), in C_WT, through δ₁ = O((LM)^{−1}), and in C_loc, all constants of L and M and in the ratio λ_R = K_RLM + 1 of C₁ to C₀ (`WILSON_IT1_WALK_FACTOR_DIFFERENCE_2026_10_28.md` #W8.19), which then gives the ratio conditions with LM.
  {#C5.35-2} The bound it yields carries (L^{j−(n−1)})^{4+β′} = L^{4+β′}(L^{j−n})^{4+β′}, and the factor L^{4+β′} is in C_α (*The constant.*).
  {#C5.35-3} The smallness conditions with LM hold for g small, as those with M do.
  {#C5.35-4} {#D.RΔ^c-T} (RΔ^c-T) := the statement of #C5.33–#C5.35-3: RΔ^c at a near domain □₀ that meets the layer n − 1, run at the scale n − 1 with LM in place of M, with the bound carrying the factor L^{4+β′} that C_α contains.

{#C5.36} *The constant.* The radii come first.
{#C5.36-1} With α_{i,m} = ĝ_mC_i(log ĝ_m^{−2})^{q_i} (CRE (2.28) at ĝ_m, #CP.13), CRE (2.6)–(2.7) (p.255) for ĝ (`WILSON_IT1_LARGE_FIELD_DEPTH_2026_10_27.md` #P.1-3-1) give α_{i,n}/α_{i,j} ≤ (1+β₀)²(n−j)^{1/2} for n > j.
{#C5.36-2} RG I requires B₃²O(1)Mα₀ < ½α₁ (p.277 l.54).
{#C5.36-3} CRE takes q₀ and q₁ "integers greater than 1" and C₀ and C₁ "sufficiently large" (p.259 l.50), with no other condition on them in CRE; within that freedom this note fixes q₀ ≤ q₁ and C₁ > 2B₃²O(1)MC₀, so that B₃²O(1)Mα_{0,m} < ½α_{1,m} at every m.
{#C5.36-8} The radius α₂ of (I.3.14) and (I.4.4) depends "on α₀ and on some absolute constants" (RG I p.272 l.38–39).
{#C5.36-9} It is fixed by the room between the space U^c_j(X, ½α₀, ½α₁, α₀) of (3.13) and the domain U^c_j(X, α₀, α₁) of the term.
{#C5.36-10} The substitution (3.13) moves the conditions (i)–(ii) by O(1)max(|𝐀|, |∇𝐀|) and the current by O(1)max(|𝐀|, |P₁𝐀|, |∇𝐀|, |Δ𝐀|), since F₁ is a local operator in 𝐔, ∂𝐔, 𝐀, and ∇𝐀 that vanishes at 𝐀 = 0 (p.272 l.19–22).
{#C5.36-11} The rooms are ½α₀, ½α₁, and (1 − L^{−3})α₀, so α_{2,m} := c₂min(α_{0,m}, α_{1,m}) = c₂α_{0,m}, with c₂ depending at most on d, L, and B₃ for these rooms, is admissible.
{#C5.36-12} The further bounds on c₂ of the walk-factor note's §8 are c₂ ≤ c_N and the large-field note's bound at stage 2 (its #W8.15-1–#W8.15-2), and c₂ ≤ c_* := β_IL^{−2}/(2B₃⁺C_{Q*}O(1)), used in *The composites over 𝒮_z.* below, at stage 3′ after M, as B₃⁺ is fixed after M (its #W8.20-1, #C5.37-10); through them c₂ depends also on β_I, B₃⁺, C_{Q*}, C₁₃, B₅, C_δ(ε₀), and C_φ.
{#C5.36-13} The norm class does not impose (iv) (#C5.5), so the shift exp iξ𝐀 needs no room in (iv); the B₃ is that of the lift moves through Proposition 9 (#C5.8).

{#C5.37} The fifth-order term of (I.3.34) is bounded by (I.3.54) (RG I p.280 l.35–42).
{#C5.37-1} This is a Cauchy integral over |σ| = r of 𝐄 itself, ≤ E₀α₃^{−5}|B|⁵exp(−κd_j(X)), and the print continues "|B|<O(1)L^jη, e.g. |B|<α₁L^jη" (p.280 l.44).
{#C5.37-2} CRE replaces η by L^{−n} (p.280 l.20–22).
{#C5.37-3} On 𝒮_z the background bound (I.3.27) at the layer n then gives |B| ≤ O(1)B₃Mα_{0,n}L^{j−n}, α_{0,n} here at the radii ρ ∈ [r, r⁺] of the run and α_{3,j} below at the radii r (#C5.28), so the ratio is at most 9/8 times its value at equal radii, a factor that the O(1) of C_r below, and that of ρ̄ (#C5.40), includes.
{#C5.37-4} RG I requires B₃α₃ < ½α₁ and 2B₃α₃ ≤ β_IL^{−2}α₀ (p.280 l.6 and l.16), so α_{3,j} := β_IL^{−2}α_{0,j}/(2B₃⁺C_{Q*}) is admissible, C_{Q*} ≥ 1 (#C5.6), Bałaban's α₃ being only "sufficiently small" (p.279 l.49, p.280 l.31).
{#C5.37-5} The factor 1/C_{Q*} is for the current.
{#C5.37-6} The second inequality of (iii) is "obtained in the same way" (p.279 l.29) and "proved in the same way" (p.280 l.21), that is, from (3.42) and the bounds (1.43)–(1.54) of [14], a bound of the type (3.44) for the second-order operator ∂^{ξ*}∂^ξ (p.279 l.29–31).
{#C5.37-7} Its B′-part, the current of 𝐀₂, has the form of (3.45)–(3.46) (p.279 l.7–20): by (174) of [15] (p.279 l.7–8) its linear term is ∂^{ξ*}∂^ξH_{1,j}B′, at most B_J|B′| with B_J the second-order operator bound of H_{1,j} in the normalisation of (3.42).
{#C5.37-8} Its terms of second order, ∂^{ξ*}∂^ξ applied to the functions 𝐀_{1,j} and H_jD_j(…) of (174), whose first differences (3.45) bounds by B₃(B₃O(1)Mα₀)² at |B| of the order of B₃O(1)Mα₀, have B′-part at most B_J·B₃O(1)Mα₀|B′|, below B_J|B′| for γ small.
{#C5.37-9} These two bounds, with B_J uniform in j, are Bałaban's: the second inequality of (iii) "is proved in the same way" (p.280 l.21) as the first, whose B′-part is bounded by |∇^ξ𝐀₂| ≤ B₃|B′| (p.280 l.3–4).
{#C5.37-10} B_J may depend on M, since H_{1,j} acts on the cube □₀ = □̃⁵ (p.273 l.40), so B₃⁺ below is fixed after M (the walk-factor note's §8, stage 3′).
{#C5.37-11} RG I does not print B_J's value, and it obtains second-order bounds of 𝐇_j only through the Landau-gauge representation of VAR (174)–(180): "For 𝐀 = 𝐇_j we have bounds for this second order operator, but only if we use the second representation for 𝐇_j connected with the Eq. (180) [15]", and "for terms in this expansion we will have good bounds, including bounds for the covariant Laplace operator. Such bounds do not hold for the operator D*D" (p.272 l.20–24).
{#C5.37-14} The printed counterparts are VAR's, for the operator H of its Landau gauge. |Δ_πHB|_{(−3)}, |ΔHB|_{(−3)}, |D*DHB|_{(−3)}, and |Δ_{U₀}HB|_{(−3)} are at most O(1)|B| (VAR (137)–(140), p.298 l.49–p.299 l.23), and the second-order term |D*DHD(A₁′)|_{(−3)} is at most O(1)4C₂|A₁′|²_{(−1)} (p.299 l.16).
{#C5.37-15} The print calls the O(1) of ε₂ = O(1)C₁B₃ε₁, assembled from these bounds, "an absolute constant depending on d and L only" (p.299 l.25–26). Pointwise, the second-order quantities are printed with explicit constants: |HB|, |∇^ηHB|, |∂^{η*}∂^ηHB|, |Δ^ηHB| ≤ B₀Σ_{c∈ℭ_k}e^{−δ₀d(y₁,c₋)}(L^{j(c)}η)^{−1}|B(c)| ((161), p.303 l.26), B₃ is defined from this bound ((162), p.303 l.36–39), and B₃ "depends on d and L only" (p.303 l.41).
{#C5.37-16} H_{1,j} is the operator of Δ₁ (VAR p.290 l.19, p.293 l.24).
{#C5.37-17} Bałaban's B₃ is not changed, and his statements are applied with it.
{#C5.37-18} The notes use B₃⁺ := max(B₃, 2B_J), fixed after M, in α_{3,j} and in the constants derived from it (c_*, C_r, α₁/α₃, α₂/α₃, r_{0,m}/α_{3,j}), so the B′-part of the output's current is at most 2B₃⁺α_{3,j} = β_IL^{−2}α_{0,j}/C_{Q*}, and RG I's conditions B₃α₃ < ½α₁ and 2B₃α₃ ≤ β_IL^{−2}α₀ hold a fortiori since B₃ ≤ B₃⁺.
{#C5.37-19} At the radii r this is β_IL^{−2} = 2^{−9} of the norm class's current threshold r_{0,j}/C_{Q*} (#C5.5, #C5.28).
{#C5.37-20} So the remainder is ≤ E₀C_r⁵max(1, n−j)^{5/2}(L^{j−n})⁵exp(−κd_j(X)), with C_r := O(1)B₃B₃⁺LML²β_I^{−1}(1+β₀)²C_{Q*}, the factor L covering LM in place of M at a finer layer (*The near domains at a finer layer.*).
{#C5.37-21} It holds on □̃⁴.
{#C5.37-22} The localisation of the inner product in □̃⁴ and its complement is Bałaban's statement.
{#C5.37-23} The parts with at least one factor localised in (□̃⁴)^c "can be estimated by an arbitrary power of L^jη using the exponential decay properties", by considerations "similar to those done on several occasions, e.g. (3.6), (3.21)", which he does not repeat (RG I p.280 l.45–47).
{#C5.37-24} In CRE's layer form this is a bound C_loc E₀(L^{j−n})⁵exp(−κd_j(X)) at the power 5.
{#C5.37-25} C_loc is the constant of that statement, an equal-scale constant of Bałaban's like those in C_{WT}.
{#C5.37-26} The transfer to the mixed radii, a background of the layer n and a term of the scale j, is also Bałaban's: "The last term in it satisfies the bound (I.3.54), the right-hand side of which can be further bounded by (I.3.35), again with η replaced by L^{−n}" (CRE p.280 l.20–22), (I.3.35) being O(1)exp(−κd_j(X))(O(1)L^jη)⁵ (RG I p.277 l.26–30), the form RG I's "required bound" with the localisation reaches (p.280 l.34 and l.44–47).
{#C5.37-27} So the localised parts are ≤ C_loc E₀(L^{j−n})⁵exp(−κd_j(X)) by Bałaban's statement, and the part on □̃⁴ is the explicit bound above, with its factor max(1, n−j)^{5/2}.

{#C5.38} The terms n = 2, 3, and 4 of (I.3.34) are n-linear in B. Their coefficients are the Taylor coefficients at U = 1, which (I.4.3) writes as Cauchy integrals of 𝐄^{(j)}(X, exp iξ𝐀) on the domain (I.4.4).
{#C5.38-1} This gives the bound (I.4.5), (2n²B₃/α₂)ⁿE₀exp(−κd_j(X)) times the product of the sup norms of the arguments (RG I p.282 l.10–17), with the radius α_{2,j} of the term.
{#C5.38-2} After the Ward–Takahashi identities the irrelevant parts carry derivatives of B. The bounds on these are (I.4.17), |∂B| < O(1)(α₂ + B₃O(1)Mα₀)(L^jη)², and (I.4.18), |∂∂B| < α₁(L^jη)^{2+β} for 0 ≤ β ≤ β^H_0 < 1, which comes from the Hölder norms of (I.3.32) (RG I p.285 l.14–24).
{#C5.38-3} The α₂ of (4.17) comes from the field 𝐀 of (I.3.31)–(I.3.32), and 𝐀 = 0 in CRE's layer form, so it is absent here; at the composites over 𝒮_z below it is present.
{#C5.38-4} In CRE's layer form every factor B, ∂B, and ∂∂B then carries the amplitude O(1)B₃Mα_{0,n} of (I.3.27) at the layer n, times L^{j−n}, (L^{j−n})², and (L^{j−n})^{2+β_H} respectively.
{#C5.38-5} An irrelevant part has the power (L^{j−n})^{4+β_H} or a higher one, the least power belonging to the parts with one factor ∂∂B; this is (3.67)'s 5 − β at β = 1 − β_H.
{#C5.38-6} The parts with a factor |Γ_{x,x₃}| are summed with the exponential decay as for (I.4.22) (p.286 l.2–21).
{#C5.38-7} (4.22) itself is stated after the differentiation in t_□ (p.282 l.24–25) and is used here only for that summation.
{#C5.38-8} A part of order r is r-linear in B. The commutator terms produced by the Ward–Takahashi identities carry fewer factors α_{2,j}^{−1} than factors B, and α_{2,j} ≤ 1, so the bound of a part of order r is at most the r-th power of the ratio ρ := O(1)B₃²Mα_{0,n}/α_{2,j} times

{#C5.39} C_{WT}(L^{j−n})^{4+β_H}exp(−⅓κd_j(X))E₀.

{#C5.40} Here C_{WT} collects Bałaban's equal-scale constants of RG I Sect. 4: the factors 2n², c₀(δ₁)c₁(δ₁) with δ₁ = O(M^{−1}), and the like, as in (4.22).
{#C5.40-1} The two factors B₃ of ρ are the 2n²B₃/α₂ of (I.4.5) per order and the amplitude B₃ of each factor B. Since α_{0,n}/α_{2,j} ≤ c₂^{−1}(1+β₀)²max(1, n−j)^{1/2}, times 9/8 when α_{0,n} is at input radii up to r⁺ and α_{2,j} at r (#C5.37), ρ ≤ ρ̄max(1, n−j)^{1/2} with ρ̄ := O(1)B₃²LM(1+β₀)²/c₂, the factor L covering LM in place of M at a finer layer.

{#C5.41} (I.4.14)–(I.4.15) (RG I p.284 l.13–37) are identities for the Taylor coefficients at B = 0, "for an arbitrary gauge function λ, and arbitrary gauge fields B₁, B₂, B₃" (p.284 l.37).
{#C5.41-1} They are multilinear, so they hold for complex B with no continuation, and they hold for Δ because they hold for each term.

{#C5.42} The far domains are bounded by (3.48).
{#C5.42-1} It holds on the class, since the condition (a) places U in the evaluation set ℰ_j(X; r) of every X, where Δ has the bound of the *Statement*, and their sum is ≤ O(1)exp(−κL^{n−j}) ≤ O(1)(L^{j−n})⁵ (p.280 l.4–8).

{#C5.43} Every factor max(1, n−j)^{1/2} enters at most to the fifth power, and (L^{j−n})⁵ ≤ (L^{j−n})^{4+β_H}.
{#C5.43-1} Let C_{β′} := sup_{m≥0}max(1, m)^{5/2}L^{−β′m}, which is finite.
{#C5.43-2} Since β_H − β′ ≥ β′, max(1, n−j)^{5/2}(L^{j−n})^{4+β_H} ≤ C_{β′}(L^{j−n})^{4+β′}.
{#C5.43-3} Two further pieces enter.
{#C5.43-4} The irrelevant part of Δβ A(h_z, U) + N(U), by (3.66) for A(h_z, ·) and for each of the 36 plane-pair actions of N, ≤ O(1)E₀c₂^{−2}ρ²(L^{j−n})^{4+β_H} with the O(1) counting these pieces, has the form of the parts of orders 2 to 4 and is counted with C_{WT} + c₂^{−2} in place of C_{WT}.
{#C5.43-5} The localisation remainder outside □̃⁴ is Bałaban's bound C_locE₀(L^{j−n})⁵exp(−κd_j(X)) above.
{#C5.43-6} With ρ^r ≤ (1+ρ̄)⁴max(1, n−j)² for r ≤ 4, and with the sum of exp(−⅓κd_j(X)) over the domains X ∋ z bounded by O(1), (5.1c) holds with C_α := O(1)L^{4+β′}C_{β′}[C_r⁵ + C_loc + (C_{WT} + c₂^{−2})(1+ρ̄)⁴ + 1], the O(1) that sum, the 1 the far domains, and L^{4+β′} the cost of the evaluation at the scale n − 1 at a finer layer (*The near domains at a finer layer.*).
{#C5.43-7} Since C_{β′} ≥ 1, this is at least the values O(1)(2 + c₂^{−2}) and O(1)(2 + c₂^{−2})L^{4+β′} of *Mixed radii.*, for the O(1) large enough.
{#C5.43-8} C_α depends on d, L, M, B₃, B₃⁺, β_I, β₀, β_H, and c₂ and on Bałaban's equal-scale constants.
{#C5.43-9} It does not depend on j, n, k, K, the volume, or the regularity ε_n of real configurations.
{#C5.43-10} For a difference every step is linear in the term, and E₀ is replaced by dE₀.
{#C5.43-11} *The composites over 𝒮_z.* Let 𝐔 lie in 𝒮_z at a point z whose near domain satisfies (N), with (b) at 𝐔₀ = 𝐔^{h^{−1}}, and let 𝐀 be a 𝔤^c-valued field on □₀ such that L^nη𝐀^h, 𝐀^h := Ad(h^{−1})𝐀 pointwise, satisfies (I.3.31) in the L^{−n}-scale at 𝐔₀ with α_{2,n} := c₂α_{0,n} in place of α₂, the Hölder norm included, its derivatives covariant.
{#C5.43-12} The composite over 𝐔 is c(𝐔, 𝐀) := U_j(□₀, exp iQ(η𝐀)M^·(𝐔)) = U_j(□₀, M^·(exp iη𝐀𝐔)) (RG I (3.3), p.270 l.27–28), RG I's local function at the term's scale j, with 𝐀 transformed together with 𝐔 as B is in (I.3.29) (p.276 l.11–19).
{#C5.43-13} The composite is covariant.
{#C5.43-14} Bond by bond, exp iη𝐀𝐔 = (exp iη𝐀^h𝐔₀)^h, with 𝐀^h(b) = Ad(h(b₋)^{−1})𝐀(b).
{#C5.43-15} The averages satisfy M^·(Y^h) = M^·(Y)^h at the points of each scale (CMP 98 (11), an identity of holomorphic functional calculus at conjugated holonomies, valid at G^c-valued h, #C9.8.18), and U_j(□₀, V^h) = U_j(□₀, V)^{h̄} with h̄ constant on the blocks of the function (RG I p.278 l.3–12; VAR (181), p.307 l.7–15, by analyticity near the G-valued h and as VAR's definition on the rest of the orbit).
{#C5.43-16} So c(𝐔, 𝐀) = c(𝐔₀, 𝐀^h)^{h̄}, and irr_□(Δ)(c(𝐔, 𝐀)) = irr_□(Δ)(c(𝐔₀, 𝐀^h)) by the G^c-invariance of Δ (#C9.8.18-5) and of the actions A(h_z, ·) and N, which are traces of plaquette products.
{#C5.43-17} The bounds below are derived at 𝐔₀.
{#C5.43-18} These are the configurations of RG I (3.28) with (tζ̃_□ + t_□ζ_□)𝐇_k(B′) replaced by 𝐀 (p.276 l.26–36), in CRE's layer form: since 𝐔 = U_n(□₀, M^·(𝐔)) on □₀, the replacement of p.275 l.4–7 leaves 𝐔 unchanged, and after the gauges v and u_{k+1} of (I.3.26)–(I.3.27) the data are exp iB, B = Q(ηA) with A of (I.3.30).
{#C5.43-19} At 𝐀 = 0 the composite is U_n(□₀, M^·(𝐔)) on □₀, which is 𝐔^g with ‖Ad(g)‖ ≤ e^{β_I} (#C5.26), and 𝐔 itself where 𝐔 = U_n(□₀, M^·(𝐔)): the level-j constraints imply the level-n ones (M^n = M^{n−j}∘M^j), and U_n(□₀, M^·(𝐔)) minimises under the level-n ones and satisfies the level-j ones.
{#C5.43-20} Let irr_□(Δ)(c) be irr(Δ)(c) with the sum over the domains restricted to the near domains X ∋ z, X ⊂ □̃², which read c on □̃³ only (*Complex domain.*), the coefficients Δβ and N being kept whole.
{#C5.43-21} Then for n > j, (5.1c𝐀) |irr_□(Δ)(c(𝐔, 𝐀))| ≤ d · C^𝐀_αE₀(L^{j−n})^{4+β′}, C^𝐀_α := 6⁵C_α, and at n = j the same holds wherever c(𝐔, 𝐀), a point (R2), lies in the norm class 𝒫_j(X; r) of each near domain X, by the direct bound of *Mixed radii.* The proof above reads 𝐀 at three places.
{#C5.43-22} The Ward–Takahashi identities, the coefficients (I.4.3) at U = 1, and Bałaban's localisation outside □̃⁴ do not involve 𝐀.
{#C5.43-23} *Lemma 4.* Its proof reads 𝐀 only through (I.3.48)–(I.3.49), |Q′| ≤ O(1)L^jη|𝐀| with Q′ analytic in 𝐀, after which τQ′ is replaced by B′ with |B′| < α₃ (RG I p.279 l.33–p.280 l.22); neither |∇^η𝐀| nor ‖𝐀‖_{1,β} enters it.
{#C5.43-24} In the L^{−n}-scale |Q′| ≤ O(1)L^{j−n}α_{2,n} ≤ O(1)(1+β₀)²(n−j)^{1/2}L^{j−n}c₂α_{0,j} ≤ 0.66·O(1)c₂α_{0,j} for n > j, by *The constant.* and the factor (1+β₀)²p^{1/2}L^{−p} < 0.66 at p ≥ 1 of the bullets under (N).
{#C5.43-25} Under c₂ ≤ c_* := β_IL^{−2}/(2B₃⁺C_{Q*}O(1)), with the O(1) of (I.3.49), the condition O(1)α₂ ≤ α₃ of the walk-factor note's §8, stage 2 (RG I's "for α₂ sufficiently small", p.279 l.47), O(1)c₂α_{0,j} ≤ α_{3,j} = β_IL^{−2}α_{0,j}/(2B₃⁺C_{Q*}), so |Q′| ≤ 0.66α_{3,j}.
{#C5.43-26} Both sides are at the radii r: the field 𝐀 is at c₂r_{0,n} also when Lemma 4 is run at input radii in [r, r⁺] (#C5.28), since this budget 0.66α_{3,j} + ⅓α_{3,j} has no room for a factor 9/8.
{#C5.43-27} So Lemma 4's conclusions hold at c(𝐔, 𝐀) with a third of α_{3,j} left for its B′.
{#C5.43-28} *The amplitude.* (I.3.32) bounds A by 2(α₂ + B₃O(1)Mα₀) on □̃⁴ (p.277 l.2–5), and (I.4.17)–(I.4.18) bound ∂B and ∂∂B through (I.3.32) and Proposition 5 of [7] (RG I p.285 l.14–24), (I.4.18) through the Hölder norms, the one place where the Hölder part of (I.3.31) enters.
{#C5.43-29} In the L^{−n}-scale the amplitude is 2(α_{2,n} + B₃O(1)Mα_{0,n}) ≤ 4B₃O(1)Mα_{0,n}, since c₂ ≤ 1 ≤ B₃O(1)M.
{#C5.43-30} So each factor B, ∂B, and ∂∂B carries at most twice the amplitude of *The constant.*, and ρ, ρ̄, and C_r are replaced by 2ρ, 2ρ̄, and 2C_r.
{#C5.43-31} *The fifth-order term.* Q′ is part of B and uses at most 0.66α_{3,j}, so the Cauchy integral of (I.3.54) is taken at |σ||B| = ⅓α_{3,j}, the B′ of Lemma 4 then being below 0.99α_{3,j}, which costs the factor 3⁵.
{#C5.43-32} So the constant of *The constant.* becomes O(1)C_{β′}[(6C_r)⁵ + C_loc + (C_{WT} + c₂^{−2})(1 + 2ρ̄)⁴ + 1] ≤ 6⁵C_α.
{#C5.43-33} The far domains are not read at c(𝐔, 𝐀).
{#C5.43-34} In irr_□(Δ) the parts of Δβ and N that come from the far domains multiply A(h_z, c) and the 36 plane-pair actions of c, which Lemma 4's output bounds on □̃³ as at the class, so these parts are at most O(1)dE₀c₂^{−2}exp(−κL^{n−j}) ≤ O(1)dE₀c₂^{−2}(L^{j−n})⁵, by the decay of the far domains above, and the term c₂^{−2} of C_α covers them.
{#C5.43-35} Along a holomorphic family 𝐀(t), |t| < R, that satisfies these hypotheses at every t, t ↦ irr_□(Δ)(c(𝐔, 𝐀(t))) is analytic, and the derivative version below holds with C^𝐀_α in place of C_α.
{#C5.43-36} A field 𝐀 with the bounds of (I.3.31) but no Hölder bound gives Lemma 4 and (I.4.17) as above, but not (I.4.18); that case is the split and the excess of `WILSON_IT1_LARGE_FIELD_DEPTH_2026_10_27.md` §4(d), (F-H).

{#C5.44} *Derivative version (derived from RΔ^c).* Let t ↦ U(t), |t| < R, be a holomorphic family of pairs of the class that lie in 𝒮_z, at a point z whose near domain satisfies (N).
{#C5.44-1} Two kinds occur.
{#C5.44-2} One is the local minimisers U(t) = U_n(□₀, 𝐕(t)) of complex block data 𝐕(t) holomorphic in t, extended outside □₀ as in *The regular subclass.*.
{#C5.44-3} The other is the minimisers U_k(𝐕(t)) at holomorphic complex data, which vary outside □₀ and lie in 𝒮_z pointwise in t (*The regular subclass.*); the §8.2 family U_k(exp i[g_kCtA − hD̃(g_kCtA)]V^{(k)}) is of this kind.
{#C5.44-4} Then t ↦ irr(Δ)(U(t)) is analytic on |t| < R and bounded there by (5.1c), and Cauchy's estimate on the circles |t| = R′ < R, as R′ → R, gives

{#C5.45} the derivative bound |∂_t irr(Δ)(U(t))|_{t=0}| ≤ R^{−1}·d·E₁(α)(L^{j−n})^{4+β′}.

{#C5.46} This is Bałaban's mechanism for the derivative in t_□ (p.283 l.23–25, RG I p.280 l.47–49): the configuration is a holomorphic function of t_□ through its data, and the factor O(1)α₂^{−1}ε₁ is the size ε₁ of the direction over the radius α₂.
{#C5.46-1} §8.2 uses it along the fluctuation, with R the ratio of the margin m_k to the size of the fluctuation.
{#C5.46-3} Along a family that leaves the local minimisers, (5.1c) is not available.

{#C5.47} *The lift condition.* Condition (a) contains, through ℰ_j(X; r) ⊂ 𝒫_j(X; r) and the lift half of 𝒫_j, besides run A's membership with the current at most r_{0,j}/C_{Q*}, the condition that the G^c-orbit of the lifted configuration ι_X𝐔 contain a configuration (ι_X𝐔)^ṽ with ‖Ad(ṽ^{±1})‖ ≤ e^{2β_I} that satisfies on X the configuration conditions of run B's U^c_{j+1}(X, r_{0,j}, r_{1,j}) (#C5.5).
{#C5.47-1} The lifted pair then lies in run B's space, its current bounded at the transformed pair (*Complex domain.*, #C5.6).
{#C5.47-2} *The lift gauges.* At the points used, ṽ is the following.
{#C5.47-3} At the real minimisers ṽ = 1: ι_X(U^A) satisfies the conditions itself, with the cube gauges of (I.1.12), which are G-valued and part of the conditions (#C5.52–#C5.59).
{#C5.47-4} At the minimisers at the data of the fluctuation integral on the margin ball of #C8.2.2, the large-field note's callers' U_k among them, ṽ is Bałaban's gauge h_B of the representation, the axial gauge followed by u_k, with ‖Ad(h_B^{±1})‖ ≤ 1 + O_L(m_k) ≤ e^{β_I} for γ small (#C5.64; that note's #4.521).
{#C5.47-5} At the large-field note's other members, ṽ is the gauge u of run B's member, given by CMP98 (106), |log u| ≤ 32dε₂, so that Ad(u^{±1}) is within 1 + 2^{−9} of isometric for γ small (that note's #4.517-0–#4.517-2, #4.536, and *The representative.*, #4.244), and ‖Ad(ṽ^{±1})‖ ≤ e^{β_I}.
{#C5.47-6} At that note's representatives W^u of U″_k, U_{k,Λ}, and U_1, ṽ is that of their base, U^0_k or U_k (its #4.540.1).
{#C5.47-7} At the composites and Lemma 4's outputs, ṽ is the inverse of the block-constant lift of run A's gauge h_A := v ū_{k+1}v_ju_j of (I.3.37)–(I.3.39) (#C9.8.18) times run B's gauge h_B of the same construction.
{#C5.47-8} By (3.26), (3.27), (3.37), and (3.41) (RG I p.275 l.24 and l.35, p.277 l.50, p.278 l.39–41) each of h_A^{±1} and h_B^{±1} has ‖R(·)‖ ≤ exp(B₃²O(1)Mα₀ + 2B₃O(1)Mα₀ + O(1)Mα₁) ≤ exp(O(1)Mα_{1,j}), by B₃²O(1)Mα₀ < ½α₁ (p.277 l.54), so ‖Ad(ṽ^{±1})‖ ≤ exp(O(1)Mα_{1,j}) ≤ e^{β_I} for γ small, α_{1,j} tending to 0 uniformly by CRE (2.28).
{#C5.47-9} At the points (N), on the large-field note's polydiscs of c_𝒫 (its #4.454), and at its decoupled configurations (its #4.244), ṽ is the gauge of Proposition 9 [15] at V₀ = 1, or the u of that note's *The representative.*, given by CMP98 (106) as in its #4.517-0–#4.517-2, so ‖Ad(ṽ^{±1})‖ ≤ exp(O(1)dB₅ε₁), ε₁ the size of the data move, at most of the order of the class radii α_{0,j} + α_{1,j}, hence ≤ e^{β_I} for γ small, as for h at #C8.2.2.
{#C5.47-10} At the points (R3), ṽ is that of 𝐔′ times the gauge of Proposition 9 for the data move (#C5.8), so ‖Ad(ṽ^{±1})‖ ≤ e^{2β_I}.
{#C5.47-11} Wherever a gauge that is not smooth (u, h_B, or the g of #C8.2.2) moves a bound of (ii), the gradient transported is the covariant derivative at the full configuration, the continuation of the real covariant derivative, which transforms pointwise, ∇_{W^u}(Ad(u)S) = Ad(u)∇_WS (the large-field note's #4.517-3).
{#C5.47-12} The A′-gradient of (ii), covariant at the real part, differs from it by the commutator with the A′ of the configuration before the gauge, so the transported bound carries a factor 1 + O(α_{1,j}) besides ‖Ad‖ (#C5.63, #C8.2.2, and the large-field note's #4.540), which the margins there absorb for γ small.
{#C5.47-13} The proof of (5.1c) and its callers need this at three kinds of configurations:
- {#C5.48} the minimisers U^A_k(V) at real data V;
- {#C5.49} the minimisers at the complex data of the fluctuation integral (§8.2, CRE (3.15));
- {#C5.50} for the near domains, the composites U_j(□₀, exp i(τB + B′)) of Lemma 4 at complex τ and B′.

{#C5.52} At the real minimisers the conditions are derived, with the localised lift of #C9.8.6–#C9.8.17.
{#C5.52-1} Let U^A := U^A_k(V), U^B := U^B_{k+1}(V), a := εL^k, and a_j := εL^j, the unit of the scale j. The unit of the scale k is written a, since a_k denotes the activity bound g_kP_a(log g_k^{−2}) of #C5.12-8 (#CK.1-9).
- {#C5.53} §9.7 gives ι(U^A) = e^{i(ε/L)𝐒}U^B, with 𝐒 := ℒA′* + A″ up to the BCH term O((ε/L)|A″||ℒA′*|) of the composition e^{i(ε/L)A″}e^{i(ε/L)ℒA′*}, sup|𝐒| ≤ σ_k/a, and sup|∇𝐒| ≤ σ_k/a².
  {#C5.53-1} In the units of a_j the two bounds are σ_kL^{j−k} and σ_kL^{2(j−k)}.
- {#C5.54} By #C9.8.17-2–#C9.8.17-3, ι_XU^A = e^{i(ε/L)𝐒_X}U^B on X, with 𝐒_X − 𝐒 at most C(ε₀)ε₁e^{−δ₀M₁L^j}/a and its gradient at the one-step scale ε.
  {#C5.54-1} In the units of a_j the tail moves the cube-gauge field by C(ε₀)ε₁e^{−δ₀M₁L^j}L^{j−k} and its gradient by at most C(ε₀, δ₀M₁)ε₁e^{−δ₀M₁L^j/2}L^{j−k}.
  {#C5.54-2} So in these units 𝐒_X and its gradient are at most σ̂_{k,j}L^{j−k}, with σ̂_{k,j} := σ_k + C(ε₀)ρ_k + C(ε₀, δ₀M₁)ε₁e^{−δ₀M₁L^j/2}.
- {#C5.55} U^B is real.
  {#C5.55-1} By VAR Theorem 1 at k + 1 steps (§9.2, (9.2)) its plaquettes lie within C₀ε₁L^{2(j−k)}ξ² in the units of a_j.
  {#C5.55-2} By VAR (9) on the cubes of side 2M′a, M′ := O(1)LM/2 ≤ M(ε₁) taken a multiple of R₁M₁ as VAR Theorem 1 asks (VAR p.279 l.3), it has on the cubes of (I.1.12) a gauge with |A|, |∇A| ≤ O(1)LMB₃ε₁L^{j−k} in these units.
- {#C5.56} The move by e^{i(ε/L)𝐒_X} changes the plaquettes by O(1)σ̂_{k,j}L^{j−k}ξ² and the cube-gauge field by at most σ̂_{k,j}L^{j−k} with its gradient.
- {#C5.57} So ι_X(U^A) satisfies (i), (ii) (with U′ = 1), and the plaquette half of (iii) on X at radii ≤ r_{·,j}/(2B₃), for γ small.
  {#C5.57-1} Here ε₁ ≤ C_{ε₁}ε_k, σ_k ≤ C(ε₀)ε₁, and ε_kL^{j−k}/α_{0,j} ≤ (ε_k/α_{0,k})(1+β₀)²(k−j)^{1/2}L^{j−k} → 0 uniformly, since q₀ > p₀, a choice of this note (CRE p.259 l.50 asks only "integers greater than 1").
- {#C5.58} (iv) follows by RG I (1.17), which uses only the plaquettes of the configuration and of its real part.
- {#C5.59} The current.
  {#C5.59-1} By §10.3 at the scale k, J(U^A) = J′ + δ𝐉 with a³|J′| ≤ 2B_λε₁ and a³|δ𝐉| ≤ x_J(ρ_k + (ε/a)ε₁) ≤ x_J(C_G(ε₀) + 1)ε₁.
  {#C5.59-2} So in the units of a_j, |J(U^A)| ≤ B′_λε₁L^{3(j−k)} < r_{0,j}/C_{Q*} for γ small, B′_λ := 2B_λ + x_J(C_G(ε₀) + 1), since r_{0,j} ≥ r_{0,k}L^{j−k} and ε₁/r_{0,k} ≤ C_{ε₁}ε_k/r_{0,k} → 0 (q₀ > p₀).
  {#C5.59-3} The lifted current Q₁^{pl}(ι_XU^A)*J(U^A) is then at most C_{Q*}|J(U^A)| < r_{0,j}.
  {#C5.59-4} These limits, and C_Π(j)ε₁² ≤ max(1, k − j) and r_{0,k}ε₁ ≤ 1 below, use ε₁ ≤ C_{ε₁}ε_k with the constant C_{ε₁} := 2C₀C_{(3.12)} of §9, C_{(3.12)} that of CRE (3.12).
  {#C5.59-5} At (T-Λ)'s parameter ε₁^{LF} ≤ (1 + β₀)C(M)R_kε_k (LF #1.6-3 at its step k = k_s, LF #D.k_s) they need q₀ > p₀ + r, since R_k ≤ C(log g_k^{−2})^r.
  {#C5.59-6} CRE p.259 l.50 asks only that q₀ be an integer greater than 1, and CRE, LFR I, and LFR II print no upper bound on q₀, so this is a choice of q₀, as q₀ > p₀ is.

{#C5.61} *The lift condition at complex configurations.* The configuration conditions of the lifted configuration are needed at the complex data of the fluctuation integral and at the composites of Lemma 4; its current then follows by *Complex domain.*, run A's current bound r_{0,j}/C_{Q*} being Bałaban's at the reduced thresholds (*The class*, #C5.12).
{#C5.61-1} Both cases are instances of the large-field note's *The Fine Side at Complex Points.* (`WILSON_IT1_LARGE_FIELD_DEPTH_2026_10_27.md` §4(d)), which runs §9.5–9.7 at complex data with the operator bounds of PBG and VAR at complex configurations (PBG Theorem 3.4, VAR p.309 l.1–4 and Proposition 9, RG I p.273 l.1–3).
- {#C5.62} The fluctuation integral.
  {#C5.62-1} Its complex data are 𝐕 = V′V₀ with V₀ real and V′ the exponential of the complex fluctuation of the class (§8.2, CRE (3.15)), so |V′ − 1| is below the class radii, and the minimisers U^A_k(𝐕) and U^B_{k+1}(𝐕) are that note's member U_k at these data, on its norm class, where ε₁′ contains C_c(α̂₀ + α̂₁).
  {#C5.62-2} Under its conditions (T-c) and (T-ι), *The members.*, *The complex class of ι's problem.*, *The lifted backgrounds in the class.*, *The flow.*, *The tail at complex points.*, and *The bound.* give ι_X(U^A_k(𝐕)) = e^{i(ε/L)𝐒_X(𝐕)}U^B_{k+1}(𝐕) on X, with 𝐒_X analytic in the data.
  {#C5.62-3} On the disc of that note ‖𝐒_X‖ ≤ 𝔐_S := 𝔯 + 4C^c_tε₁′, a fixed multiple C_S(M) of ε₁′, and at its real points the real bound σ̂_{k,j}L^{j−k} of *The lift condition* above holds in the units of a_j.
  {#C5.62-4} The Lemma (Two Constants), with 𝔪 = σ̂_{k,j}L^{j−k} and 𝔐 = 𝔐_S, gives a_j|𝐒_X| and a_j²|∇𝐒_X| ≤ 𝔰_{k,j} := (σ̂_{k,j}L^{j−k})^{15/16}𝔐_S^{1/16} in these units.
- {#C5.63} The composites.
  {#C5.63-1} U_j(□₀, exp i(τB + B′)) at complex τ and B′ is a local minimiser of a VAR determining-set problem on □₀ at data V′V₀ with V₀ real, and run B's U^B_{j+1}(□₀, ·) is the minimiser of the same problem at the same data.
  {#C5.63-2} That note's *The composites and the representation configurations* runs the same construction with the local problem's layers, which gives ι(U^A_j(□₀, ·)) = e^{i(ε/L)𝐒}U^B_{j+1}(□₀, ·) with the same bound; Lemma 4 for run B holds at its local minimiser of that data (RG I p.279 l.47–49).
  {#C5.63-3} At the outputs of #C5.28, run B's input is run B's minimiser at the input's data, a configuration of #C5.48–#C5.50 for run B. Its run-B conditions are those from which the lift condition above is derived, not consequences of it. At real data they are VAR Theorem 1's (#C5.55), far below the thresholds. At the complex data of the fluctuation integral they are those of the large-field note's member on its norm class at the radii r (#C5.62).
  {#C5.63-4} At the composites they are those of run B's Lemma 4 outputs from inputs of these kinds, which by the bound below are again below 0.4 of the r-thresholds; this is an induction on the number of composite steps.
  {#C5.63-5} So run B's input satisfies run B's (i), (ii), and plaquettes on □₀ at radii at most r⁺, at the gauges of its kind (*The lift gauges.*, #C5.47).
  {#C5.63-6} Its current, run B's J of the input as in (3.40), is below run B's (iii) at those radii by the same three cases: at real data by (9.2) (#C5.82), at the data of the fluctuation integral by the current condition of the large-field note's member on its norm class (its #4.503 and #4.540), and at the composites by run B's Lemma 4 outputs, (3.42), in the induction.
  {#C5.63-7} The inequalities (3.40), through which alone Lemma 4's proof uses the input's (iv) (#C5.22), are its own (iii) up to the gauge g of #C5.26 with g = 1, since run B's input is a minimiser or composite of its own data and so lies in run B's 𝒮_z (#C5.13, #C5.43); RG I p.278 l.26–33 states (3.40) as a consequence of the input's membership, and (iv) is not used otherwise.
  {#C5.63-8} The factors of *The outputs in the norm class.* (#C5.28) then give run B's outputs (i), (ii), and plaquettes at most (9/8)·0.35 + o(1) of the r-thresholds. The move by e^{i(ε/L)𝐒} adds 𝔰_{k,j} = o(α_{0,j}) (#C5.64), at most (1 + O(α_{1,j}))e^{β_I}𝔰_{k,j} after the conjugation by Ad(h_B) (*The lift gauges.*).
  {#C5.63-9} Run B's output moved by e^{i(ε/L)𝐒} lies in the G^c-orbit of the output's lift by the identity above and the covariance of the lift (#C9.8.18-3, #C9.8.18-5), reached from it by the gauge ṽ of the composites in *The lift gauges.* (#C5.47), with ‖Ad(ṽ^{±1})‖ ≤ e^{β_I}. So the lift half of 𝒫_j(X; r), stated orbit-wise (#C5.5), holds at the outputs below 0.4 of its thresholds for γ small.
- {#C5.64} The conditions.
  {#C5.64-1} The base U^B_{k+1}(𝐕) is not real, and its bound on the large-field note's norm class (below ϖ times the radii r there, ϖ < 1) leaves no room at the radii r; its own bound comes from the margin ball.
  {#C5.64-2} The data of the fluctuation integral lie on the ball sup_b abs(g_kCA(b)) ≤ m_k of #C8.2.2, on which U^B_{k+1}(𝐕) lies in the G^c-orbit of Bałaban's representative exp iη𝐇^B(B′_A)U^B_{k+1}(V₀) about run B's real minimiser at V₀ (RG I p.265 l.37–41, Sect. G [15], with his continuation in B′_A, at run B's problem as #C8.2.2 uses it at run A's), with 𝐇^B(B′_A) within (I.3.31) at c₂r_{0,k}/(4C₁₃C_{Q*}) (#C8.2.2, through the bound 4B₀e^{16κ₁}abs(B′) of RG II p.6 l.41, a constant of d, L, and κ₁ for each run).
  {#C5.64-3} So at that representative, at which the lift half is read orbit-wise (#C5.5, *The lift gauges.*, #C5.47), its plaquettes, cube-gauge field, and current exceed those of the real U^B_{k+1}(V₀) of #C5.55 and #C5.59 by at most the moves c₂r_{0,k}/(4C_{Q*}) of (I.3.13), at most 2^{−10} of the radius r_{·,j}/(2B₃) at every scale j ≤ k since c₂ ≤ c_N, C_{Q*} ≥ 2, and B₃ ≥ 1.
  {#C5.64-4} The gauge h_B from U^B_{k+1}(𝐕) to that representative is Bałaban's axial gauge followed by u_k, with ‖Ad(h_B^{±1})‖ ≤ 1 + O_L(m_k) = 1 + o(1) on the ball (the large-field note's #4.521), so the moves below are conjugated by Ad(h_B) at a factor 1 + o(1).
  {#C5.64-5} The moves by e^{i(ε/L)𝐒_X} then change the plaquettes and the cube-gauge field as in *The lift condition* above, with 𝔰_{k,j} for σ̂_{k,j}L^{j−k}.
  {#C5.64-6} Every limit used there holds with this replacement: 𝔰_{k,j}/α_{0,j} = (σ̂_{k,j}L^{j−k}/α_{0,j})^{15/16}(𝔐_S/α_{0,j})^{1/16}, where the first factor is at most C(log g_k^{−2})^{−(15/16)(q₀−p₀−r)}((1+β₀)²(k−j)^{1/2}L^{j−k})^{15/16} as in the real case, and the second is at most (C(M)R_k(α̂₀ + α̂₁)/α_{0,j})^{1/16} ≤ C(M)(log g_k^{−2})^{r/16}((1+β₀)²(k−j)^{1/2})^{1/16} by CRE (2.28) with q₁ = q₀ and (2.6).
  {#C5.64-7} So 𝔰_{k,j}/α_{0,j} → 0 uniformly in k and j under
  {#C5.65} (q-c) 15(q₀ − p₀ − r) > r,
  {#C5.66} a choice of q₀ of the kind of q₀ > p₀ + r (CRE p.259 l.50 asks only that q₀ be an integer greater than 1, and no upper bound on q₀ is printed).
  {#C5.66-1} The smallness comes from ε₁/α_{0,j}, uniformly in k.

{#C5.67} So (5.1c) for the lifted term G, and so for Δ, holds where its proof evaluates the lift, at the composites of the near domains and at the far domains.
{#C5.67-1} For one term on its own run it is Bałaban's (3.67).

{#C5.68} *The moment of the lifted term.* For the global lift ι the whole tensor is isotropic, with Π^Δ_{22,11} = Δβ_j = β^B_{j+1} − β^A_j of §3 and N_j = 0; for the localised lift both differ by the boundary term below.
{#C5.68-1} By (3.57)–(3.64) and RG I (1.20)–(1.22), the coefficient of a generation-j term 𝐄 along a lift ℓ (a map from the block fields exp iB on T^{(j)} to fine fields with M^{(j)}∘ℓ = id) is β = −∂²_{p_μp_ν}Π̂_{μν}(0), Π the kernel of the quadratic part of B ↦ 𝐄(ℓ(exp iB)) at B = 0 (RG I (1.20), "the vacuum polarization tensor").
{#C5.68-2} The first variation of 𝐄 at the trivial configuration is zero: it is invariant under the constant gauge transformations (RG I p.264 l.9–10; the vanishing is also (I.4.14), p.284 l.19–25), so each of its values is an Ad-invariant vector of 𝔤, which is zero since the gauge group is compact and simple, as for ∂_J𝐄 below.
{#C5.68-3} So Π = (dℓ)*H(dℓ) with H the Hessian of 𝐄 in the fine field at 1, and in Fourier variables Π̂(p) = Σ_n d̂ℓ_n(p)*Ĥ(p + 2πn/a_j)d̂ℓ_n(p), the sum over the aliases n of the block lattice.
{#C5.68-4} The Ward identity (I.4.15) with the covariance (3.58)–(3.60) gives Ĥ(q) = O(q²) at q → 0 and Ĥ(0) = ∂Ĥ(0) = 0, and a lift that reproduces affine block fields has d̂ℓ_0(0) = 1, d̂ℓ_0(p) = 1 + O(p), and d̂ℓ_n(p) = O(p²) for n ≠ 0; so Π̂(p) = Ĥ(p) + O(p³) and β = −∂²Ĥ(0), the same for every such lift.
{#C5.68-5} The Fourier form uses the block-translation covariance of the global lift; the next paragraph identifies the tensor without it.
{#C5.68-6} U^B_{j+1} is a linearised Landau-gauge minimiser of the Wilson form under block constraints, with an exponentially decaying kernel, and ι∘U^A_j is the composition of two such lifts; each reproduces affine fields, so the composition does too.
{#C5.68-7} An affine fine field A_aff has constant curl and averages to an affine block field.
{#C5.68-8} For every φ of compact support Σ_{p′}(Dφ)(p′) = 0 for each orientation, so ⟨DA_aff, Dφ⟩ = 0, and ΔA_aff = 0 for the form Δ of the action at 1.
{#C5.68-9} D*A_aff is constant, and R annihilates constants: at U = 1 the operators G′, Q′, and Q′* of PBG (3.25) map constants to constants, so (3.25) gives Rc = c − c = 0.
{#C5.68-10} So RD*A_aff = 0, and A_aff is in the lift's gauge.
- {#C5.69} *The constrained inverse.* At U = 1 the current J vanishes, so the propagator G₁ of PBG (3.128) is the G of (3.126), with G^{−1} = (I − DRG′D*)Δ(I − DG′RD*) + DRD* + Q*aQ, and the linearised lift is ℓ₁ := GQ*(QGQ*)^{−1}, the operator H of (3.126) up to the normalisation of p.422 l.32–33 (written ℓ₁ here, since H is the Hessian).
  {#C5.69-1} The covariance 𝔊 of (3.148), with the hard constraints δ(QA)δ_R(RD*A), satisfies 𝔊Q* = 0, since ⟨A, Q*λ⟩ = ⟨QA, λ⟩ vanishes on its support, and 𝔊 = G − GDRD*G − ℓ₁QG by (3.153) (p.426 l.22).
  {#C5.69-2} Hence 𝔊G^{−1} = I − GDRD* − ℓ₁Q.
  {#C5.69-3} The kernels of G, 𝔊, and ℓ₁ decay exponentially (PBG Theorems 3.3 and 3.13, (3.133)), and so does that of R, through (3.25) and G′.
  {#C5.69-4} So the identity, which holds on fields of compact support, extends to fields of polynomial growth by cutting off and dominated convergence.
- {#C5.70} *The affine fields.* G^{−1}A_aff = Q*aQA_aff, since (I − DG′RD*)A_aff = A_aff, ΔA_aff = 0, and RD*A_aff = 0.
  {#C5.70-1} So 𝔊G^{−1}A_aff = 𝔊Q*(aQA_aff) = 0, and ℓ₁QA_aff = A_aff − GDR(D*A_aff) = A_aff: the lift of the block field of A_aff is A_aff itself, and no multiplier enters.
  {#C5.70-2} The argument is local, as β is defined in infinite volume: "Now we take a limit of these functions as T^{(j+1)} ↗ Z^d. This limit exists by the localized representation (1.7)" (RG I p.264 l.21–22).
  {#C5.70-2-0} The infinite-volume kernels of the identity are the limits of the finite-volume ones in the same way: they have localised representations, sums over random walks ω with terms localised in the walks' domains (RG II p.3 l.29–32), whose bounds B₀e^{−δ₀d(·,·)} (VAR (161), p.303 l.26) have constants of d and L, not of the volume, so the walk sums converge uniformly and each term is independent of the volume once the volume contains its domain.

{#C5.71} Hence Π^{B∘ι}_{22,11} = β^B_{j+1} for the global lift ι.

{#C5.72} The affine fields give the whole tensor.
{#C5.72-1} The tensor Π_{μν,κλ}(z) of (3.57) is the second-order term at z of the affine field B_μ(x) = Σ_κa_{μκ}(x_κ − z_κ), and by (3.55) it depends on a only through the curl.
{#C5.72-2} The lift of an affine block field is A_aff modulo gauge, the first variation of 𝐄^B at 1 is zero, and H annihilates the gauge differences, so B ↦ 𝐄^B(ι(exp iB), z) has run B's own tensor, Π^{B∘ι}_{μν,κλ} = Π^{B,(j+1)}_{μν,κλ}.
{#C5.72-3} CRE (3.60)–(3.61) for run B's sum reduce it to β^B_{j+1}δ_{μν}δ_{κλ} for κ < μ, λ < ν.
{#C5.72-4} The covariance used is (2.29) for run B's sum at one configuration, as CRE p.260 l.2–4 states it.
{#C5.72-5} No covariance of ι, of Q₁^{pl}, or of G enters.

{#C5.73} The pair lift does not change the moment.
{#C5.73-1} Its current slot carries Q₁^{pl}(ι𝐔)*J(𝐔) in place of the lifted configuration's own current.
{#C5.73-2} Both are O(p²)B̂(p) at the block momentum p, on every alias, since the linearised current D*D vanishes on affine fields and Q₁^{pl}(1)* is bounded.
{#C5.73-3} The mixed Hessian Ĥ_{AJ}(q) of 𝐄 in the configuration and the current at the trivial pair (1, 0) is O(q).
{#C5.73-4} The gauge invariance (iii) at (1, 0), in the direction of a gauge parameter ω and a current j, gives H_{AJ}(Dω, j) + ∂_J𝐄(1, 0)[[ω, j]] = 0.
{#C5.73-5} The first variation ∂_J𝐄(1, 0) is invariant under the constant gauge transformations, so it vanishes: the gauge group is compact and simple, so 𝔤 has no nonzero Ad-invariant vectors.
{#C5.73-6} So q_μĤ_{AJ,μν}(q) = 0 for every q, and Ĥ_{AJ}(0) = 0 by the continuity that the exponential decay gives.
{#C5.73-7} The current slot therefore changes Π̂ by O(p)·O(p²) = O(p³) on the alias n = 0 and by O(p⁴) on the others, and β = −∂²Ĥ(0) also at the pair lift.
{#C5.73-8} At an affine field the linearised current vanishes, so the current slot adds nothing to the second-order term there, and the whole tensor is unchanged.

{#C5.74} For the localised lift the coefficient differs by a boundary term.
{#C5.74-1} On the support of the term Π^G − Π^{B∘ι} = (dι_X)*H dι_X − (dι)*H dι, and the moment tests it on affine block fields.
{#C5.74-2} The linearisations of ι and ι_X at 1 agree on constant block fields.
{#C5.74-3} On an affine block field their difference is sourced near the boundary of X^∼ by its constant curl, not by the field itself, so the unboundedness of affine fields enters only through the term's weight exp(−κd_j(X)).
{#C5.74-4} By the decay of the localised lift's linearisation at 1 (#C9.8.16), the difference on X is at most C″_Πe^{−δ₀M₁L^j} times the curl.
{#C5.74-5} RG I (4.5) at order 2 bounds the Hessian by (8B₃/α_{2,j})²E₀exp(−κd_j(X)).
{#C5.74-6} The argument tests the quadratic form in the curl and never uses the plane, so for all κ < μ, λ < ν, |Π^G_{μν,κλ} − β^B_{j+1}δ_{μν}δ_{κλ}| ≤ C_Π(j)E₀e^{−δ₀M₁L^j}, C_Π(j) := C′_Π(8B₃/α_{2,j})², C′_Π := O(1)C″_Π, the weights of the moment absorbed by exp(−κd_j(X)) and the polarisation by the O(1).
{#C5.74-7} So the coefficients of N_j are at most 2C_Π(j)E₀e^{−δ₀M₁L^j}.
{#C5.74-8} C_Π(j) is not uniform in j, since α_{2,j} = c₂α_{0,j} carries g_j.
{#C5.74-9} It enters only through C_Π(j)ε₁², and α_{0,j} ≥ α_{0,k}(1+β₀)^{−2}max(1, k−j)^{−1/2} with ε₁ ≤ C_{ε₁}ε_k gives C_Π(j)ε₁² ≤ C′_Π(8B₃)²C_{ε₁}²c₂^{−2}(1+β₀)⁴max(1, k−j)(ε_k/α_{0,k})² ≤ max(1, k − j) for γ small.
{#C5.74-10} G is gauge invariant (#C9.8.18–#C9.8.18-4), so the Ward identities hold for G and for Δ exactly.
{#C5.74-11} The frozen difference and the variation group are therefore renormalised with G's own coefficient.
{#C5.74-12} Their sum, the two runs' difference at the generation j, is the same for every coefficient.
{#C5.74-13} With Π^G_{22,11} and N_j the frozen difference is irr(Δ_j) of §3, with Δ's own coefficient Π^Δ_{22,11} = Π^G_{22,11} − β^A_j.
{#C5.74-14} Its marginal part is removed in full, since Δ_j's tensor is Π^G_{μν,κλ} − β^A_jδ_{μν}δ_{κλ}, run A's tensor being isotropic by (3.61); so (5.1) bounds it.
{#C5.74-15} The marginal parts of the two runs are their own coefficients, which §3 absorbed into the couplings, and the defect (Π^G_{22,11} − β^B_{j+1})A_ε(h_z, U^A_k) + N_j(U^A_k) enters only the second bound (5.1v) of the group.

{#C5.75} *Evidence.* CRE pp.279 l.43–283 l.34.
{#C5.75-1} Every step of the proof is linear in the term: the far-domain bound (3.48) is RG I (1.18) with half the decay rate, exp(−½κd_j(X)) (p.280 l.4); the near-domain analysis applies the expansion (I.3.34) with remainder (I.3.54), a Taylor expansion on the analyticity domain whose remainder is a Cauchy estimate proportional to the sup bound (p.280 l.14–22), and whose terms of orders 2 to 4 are bounded through (I.4.17)–(I.4.18) and (I.4.3), proportional to E₀. The Ward–Takahashi identities (I.4.14)–(I.4.15) are consequences of the gauge invariance (iii), which holds for both terms and hence for Δ.
{#C5.75-2} (3.49)–(3.56) are identities linear in the term, which use the gauge invariance and not the covariance.
{#C5.75-3} RG I removes the first-moment terms of (I.4.34) by the Euclidean symmetries (p.290 l.13–15), but in CRE's version all factors are B, moved to z (p.280 l.22–25), so each first-moment term has a slot at the constant B(z).
{#C5.75-4} The Ward identity at the linear gauge parameter λ = cx_κ, c ∈ 𝔤, with the first variation at 1 zero ((I.4.14), RG I p.284 l.19–25), gives Σ_x𝐄^{(2)}_{κν}(X, x, y, z) = 0 for every κ, ν, and y, the sums taken after their extension to the whole lattice (RG I p.290 l.25–26), so these terms vanish, as RG I's own first-moment terms do at (4.23)–(4.25) (p.286 l.31–36, p.287 l.21), by the symmetry of (3.50) also where the constant slot is the second.
{#C5.75-5} (3.57) holds for each term with its own tensor at each z, whose z-independence uses the translation invariance (p.281 l.59), so for G the tensor is taken at each z; (3.58)–(3.61) use the covariance (2.29) to reduce that tensor to Π_{22,11}, which is Bałaban's for 𝐄^A, while for G the part off Π^G_{22,11}(z) is subtracted as N_j; (3.62)–(3.64), which also use the translation invariance (p.282 l.44), identify the quadratic coefficient Π_{22,11} for 𝐄^A, and for G the coefficient is identified at each z through the lift (*The moment of the lifted term.*).
{#C5.75-6} (3.65)–(3.66) concern A(h_z, U_k), and the same analysis gives (3.66) for each plane-pair action A_{PP′}(h_z, U_k), with the elementary tensor ½tr F_PF_{P′}(z) in the normalisation of (3.66), computed at the affine fields, where every fine plaquette of the plane P carries the curl F_P. Here A_{PP′}(h_z, ·) is gauge invariant and analytic where the plaquettes are small, and (3.66) uses the covariance of A(h_z, ·) only to identify its tensor.
{#C5.75-7} For A_{PP′}(h_z, U^A_j(exp iB)) that tensor is computed at the affine block fields through the affine reproduction of run A's lift (*The moment of the lifted term.*), with the normalisation of the weights h_z, which A_{PP′}(h_z, ·) shares with A(h_z, ·). (3.67) collects constants proportional to E₀.
{#C5.75-8} The derivative version is the mechanism of p.283 l.23–25 ("we differentiate these terms with respect to the parameter t_□ multiplying the fluctuation field"), applied along a holomorphic family of local minimisers in 𝒮_z.
{#C5.75-9} The common polydisc 𝒫_j(X; α′) is by definition the set where run A's domain conditions and run B's conditions for the lifted pair both hold, so both terms are analytic on it and bounded there by E₀ (*Complex domain.*).
{#C5.75-10} Condition (a) puts every pair of the class in the evaluation set ℰ_j(X; r) of every X, and the proof runs there with E₀ the bound on the larger polydisc.
{#C5.75-11} At the configurations where the proof evaluates the lift, condition (a) is *The lift condition.*, and at complex configurations *The lift condition at complex configurations*.
{#C5.75-12} Every radius of the proof is a fixed multiple of the common radius α_{0,·}: α_{1,·} by the choice of C₁, α_{2,·} = c₂α_{0,·}, α_{3,j} = β_IL^{−2}α_{0,j}/(2B₃⁺C_{Q*}), and the background amplitude O(1)B₃Mα_{0,n}.
{#C5.75-13} So the ratios ρ, C_r, and α_{0,n}/α_{2,j} are unchanged by the reduction, the smallness conditions O(1)Mα₁ ≤ β_I and (4B₃²O(1)M)²α₀ ≤ β_I are weaker at the reduced radii, and C_α is unchanged.

{#C5.76} *What it gives.* The frozen difference Δ_j of a matched pair, renormalised with Π^Δ_{22,11} = Π^G_{22,11} − β^A_j and N_j (*The moment of the lifted term.*) and carried from its generation j to the stopping scale, is evaluated at run A's minimiser U^A_k, a configuration of 𝒮_z on T_ε.
{#C5.76-1} It contributes ≤ d_j E₁(α) L^{−β′(k−j)} N_s⁴ to D_τ, where d_j is the analytic norm of the difference at its generation.

{#C5.77} The variation group of (3.1) compares irr^B_{j+1}(U^B_{k+1}) with irr^G(U^A_k) := G(U^A_k) − G(1) − Π^G_{22,11}A_ε(h_z, U^A_k) − N_j(U^A_k), G run B's term at the pair lift on T_ε (§3), whose configuration ι_XU^A_k is not a local minimiser of run B. Each of the two values has the age bound of (5.1c) for one term, with d = 1 and the other term zero:
- {#C5.78} irr^B_{j+1}(U^B_{k+1}) on T_{ε/L}, where U^B_{k+1} is in run B's 𝒮_z;
- {#C5.79} irr^G(U^A_k) on T_ε, where U^A_k is in 𝒮_z, and (5.1c) for G bounds G(U) − G(1) − Π^G_{22,11}A_ε(h_z, U) − N_j(U).
  {#C5.79-1} G depends on U on X^∼, where the condition (a) of the class places the lifted pair (*Complex domain.*).
  {#C5.79-2} At U^A_k that is the lift condition, derived there.
  {#C5.79-3} The proof of (5.1c) for G also evaluates G at the composites of Lemma 4 at complex τ and B′, through (I.3.34), (I.3.54), and (I.4.3), and at the far domains, where the lift condition is *The lift condition at complex configurations*.
  {#C5.79-4} It holds at the near domains satisfying (N), and the others are (RΔ^c-T).

{#C5.80} So the group is ≤ 2E₁(α)(L^{j−k})^{4+β′} per scale-(j+1) point.

{#C5.81} *The pair line.* Let a := εL^k.
{#C5.81-1} By §9.7 and #C9.8.17-2, ι_XU^A_k = e^{i(ε/L)𝐒_X}U^B_{k+1} on X and within 2L fine spacings of it, with sup|𝐒_X| ≤ σ̂_{k,j}/a, and in the units of a_j 𝐒_X and its gradient are at most σ̂_{k,j}L^{j−k}, σ̂_{k,j} := σ_k + C(ε₀)ρ_k + C(ε₀, δ₀M₁)ε₁e^{−δ₀M₁L^j/2} (*The lift condition.*).
{#C5.81-2} The localisation enters the distance, not an additive tail.
{#C5.81-3} The terms are functions of pairs (𝐔, 𝐉) with the current 𝐉 an independent variable (RG I p.262, (1.14)), and the condition (iv) involves only the currents of the averages of 𝐔, which are functions of 𝐔 (RG I (1.15)–(1.16)).
{#C5.81-4} So the difference is split with the current frozen.
{#C5.81-5} Let W(s) := e^{is(ε/L)𝐒_X}U^B_{k+1}, ΔJ := Q₁^{pl}(ι_XU^A_k)*J(U^A_k) − J(U^B_{k+1}), the difference of the two current slots, and F(s, u) := 𝐄^B(W(s), J(U^B_{k+1}) + uΔJ; z) for s, u ∈ ℂ.
{#C5.81-6} Then G(U^A_k; z) − 𝐄^B(U^B_{k+1}; z) = [F(1, 0) − F(0, 0)] + [F(1, 1) − F(1, 0)].
{#C5.81-7} The bounds below are per localisation domain X, with E₀ standing for E₀exp(−κd_j(X)); per point they carry the domain sum C_X of §8.2.
- {#C5.82} *The configuration part.* In the units of a_j the line s ↦ W(s) moves the plaquettes by at most 4|s|σ̂_{k,j}L^{j−k}ξ², the cube-gauge field and its gradient by at most |s|σ̂_{k,j}L^{j−k}, and the data of (iv) through (1.17).
  {#C5.82-1} These are measured against r_{0,j}, the smallest room, and r_{0,j} ≥ r_{0,k}(1+β₀)^{−2}(k−j)^{−1/2} ≥ r_{0,k}L^{j−k} (*The constant.*).
  {#C5.82-2} So for |s| ≤ T := r_{0,k}/(16σ̂_{k,j}) they stay within ¼r_{0,j} of U^B_{k+1}, whose own plaquettes and cube-gauge field are within O(1)LMB₃C₀ε₁L^{j−k} ≤ ¼r_{0,j} for γ small (§9.2, *The lift condition.*).
  {#C5.82-3} The current stays at J(U^B_{k+1}), and |J(U^B_{k+1})| ≤ O(1)C₀ε₁L^{3(j−k)} ≤ ¼r_{0,j} by (9.2), for γ small.
  {#C5.82-4} So the disc lies in the domain of 𝐄^B, since 2B₃·½r_{0,j} < α^B_{0,j+1}.
- {#C5.83} *Its bound.* For T ≥ 2 Cauchy's estimate on the disc |s| ≤ T gives |F(1, 0) − F(0, 0)| ≤ 2 sup|F|/T ≤ 32(σ̂_{k,j}/r_{0,k})E₀.
  {#C5.83-1} For T < 2 both endpoints lie in the domain, the endpoint s = 1 by the configuration conditions of *The lift condition.*, and |F(1, 0) − F(0, 0)| ≤ 2E₀ < 64(σ̂_{k,j}/r_{0,k})E₀.
  {#C5.83-2} So the configuration part is ≤ C_σ(σ̂_{k,j}/r_{0,k})E₀ at every k, C_σ := 64, and no bound on the current enters it.
- {#C5.84} *The current part.* At the fixed configuration W(1) = ι_XU^A_k, which satisfies the configuration conditions (*The lift condition.*), the line u ↦ J(U^B_{k+1}) + uΔJ moves only the current.
  {#C5.84-1} For |u| ≤ T_J := r_{0,j}/(4 sup|ΔJ|) the current stays within ½r_{0,j}.
  {#C5.84-2} With the endpoint u = 1 in the domain by the lift condition, the same two cases give |F(1, 1) − F(1, 0)| ≤ 16(sup|ΔJ|/r_{0,j})E₀.

{#C5.85} *The current along the pair line.* At every age, sup_X|ΔJ| ≤ C_Jσ̂_{k,j}L^{3(j−k)} in the units of a_j, C_J := 2x_J + 1, under (16dc_br + 2c_Dc_v)L^{d−1}B_λε₁ ≤ 1.

{#C5.86} The averagings compose, M^{k+1} = M^k∘M, so 𝒬(U^B_{k+1}) = 𝒬(Ũ)Q₁^{pl}(U^B_{k+1}) with Ũ := MU^B_{k+1}.
{#C5.86-1} Hence J(U^B_{k+1}) = 𝒬(U^B_{k+1})*λ^B = Q₁^{pl}(U^B_{k+1})*J′, with J′ := 𝒬(Ũ)*λ^B the intermediate current of §10.3 at the scale k (*The Multipliers.*, *The Intermediate Current.*).
{#C5.86-2} With δ𝐉 := J(U^A_k) − J′,

{#C5.87} ΔJ = Q₁^{pl}(ι_XU^A_k)*δ𝐉 + [Q₁^{pl}(ι_XU^A_k) − Q₁^{pl}(U^B_{k+1})]*J′.

- {#C5.88} *The first term.* By §10.3 at the scale k, a³|δ𝐉| ≤ x_J(ρ_k + (ε/a)ε₁) and a³|J′| ≤ 2B_λε₁.
  {#C5.88-1} On X^∼, Mι_XU^A_k = U^A_k, so *The Adjoint Averaging.* (ii) applies at W := ι_XU^A_k with W̄ = U^A_k, and c_QL^{d+1}κ_W ≤ 1 for γ small by the plaquette bound of *The lift condition.*.
  {#C5.88-2} Its divergence term is small.
  {#C5.88-3} D*_{U^A_k}J(U^A_k) = 0 (PBG (3.117)) and D*_ŨJ′ = 0 by D_V*λ^B = 0 (*The Multipliers.*), so D*_{U^A_k}δ𝐉 = −(D*_{U^A_k} − D*_Ũ)J′.
  {#C5.88-4} U^A_k = e^{iεA′*}Ũ with sup|A′*| ≤ 4ρ_k/a (§9.7), so the transports of the 2d bonds at a point differ in Ad by at most c_brε·4ρ_k/a, and ε sup|D*_{U^A_k}δ𝐉| ≤ 8dc_br(ε/a)ρ_k sup|J′|.
  {#C5.88-5} So a³ sup_X|Q₁^{pl}(W)*δ𝐉| ≤ 2x_J(ρ_k + (ε/a)ε₁) + 16dc_brL^{d−1}B_λε₁(ε/a)ρ_k.
- {#C5.89} *The second term.* On X and within 2L fine spacings of it, ι_XU^A_k = e^{iη𝐒_X}U^B_{k+1}, η := ε/L.
  {#C5.89-1} The columns of Q₁^{pl}(·)* at the bonds of X use the transports along paths of at most (2d + 1)L bonds there.
  {#C5.89-2} These change by at most c_vη sup|𝐒_X| per bond, and with them the three operators and Ad(h_{c,x}) of *The Adjoint Averaging.*.
  {#C5.89-3} As in *(b) The Difference.* of §10.3 at the level i = 0, the second term is at most c_DL^{d−1}c_vε sup|𝐒_X| sup|J′|, and a³ times it is at most 2c_Dc_vL^{d−1}B_λε₁(ε/a)σ̂_{k,j}.

{#C5.90} With ρ_k + (ε/a)ε₁ ≤ σ̂_{k,j}, ρ_k ≤ σ̂_{k,j}, and ε/a ≤ 1, a³ sup_X|ΔJ| ≤ [2x_J + (16dc_br + 2c_Dc_v)L^{d−1}B_λε₁]σ̂_{k,j} ≤ C_Jσ̂_{k,j}, and a_j³ = L^{3(j−k)}a³ gives the statement.
{#C5.90-1} So the current part is ≤ 16C_J(σ̂_{k,j}/r_{0,k})L^{2(j−k)}E₀ ≤ 16C_J(σ̂_{k,j}/r_{0,k})E₀ at every age, since r_{0,j} ≥ r_{0,k}L^{j−k}.
{#C5.90-2} No second differences of the displacement enter: at both minimisers the current is the lift of a multiplier, J = 𝒬*λ, so the current slot moves through the multipliers and, in the configuration, only through the transports of Q₁^{pl}*.

{#C5.91} *The action part.* The group's action part is −β^B_{j+1}[A_{ε/L}(h_z, U^B_{k+1}) − A_ε(h_z, U^A_k)], at two real regular configurations, so no lift enters it.
{#C5.91-1} It splits through MU^B_{k+1}, and the support of h_z has the volume (2a_j)⁴.
- {#C5.92} U^A_k = e^{iεA′*}MU^B_{k+1} with sup|A′*| ≤ 4ρ_k/a and sup|∇A′*| ≤ 4ρ_k/a² (§9.7), and both plaquette fields are at most 2C₀ε₁/a² ((9.2)–(9.3)).
  {#C5.92-1} So |A_ε(h_z, U^A_k) − A_ε(h_z, MU^B_{k+1})| ≤ C_Aρ_kε₁L^{4(j−k)}.
- {#C5.93} The localised blocking artifact A_ε(h_z, MU^B_{k+1}) − A_{ε/L}(h_z, U^B_{k+1}) is (9.3)–(9.4) with the weight h_z.
  {#C5.93-1} The terms of (9.4) give 16C_b(ε/a)ε₁²L^{4(j−k)}.
  {#C5.93-2} The weight changes by at most 4ε/a_j between a coarse plaquette and the fine plaquettes of its cell, whatever point of a plaquette h_z is evaluated at, since h_z is Lipschitz in ℓ¹ with the constant 1/a_j and the ε-cube of the coarse plaquette, which contains these fine plaquettes, has ℓ¹-diameter 4ε.
  {#C5.93-3} The fine action on the support of h_z is at most 192C₀²ε₁²L^{4(j−k)}, so this adds at most 768C₀²(ε/a)ε₁²L^{3(j−k)}.
- {#C5.94} β̄ := sup_j|β^B_j| is finite.
  {#C5.94-1} The hypothesis (W) of BETA_FUNCTION_WILSON_LOOPS.md (§2), which holds for the tube construction on the histories of H_k (#B2.2.842; #C5.7-6), each run's history lying in H_K (#C1.1-2), gives b − C ≤ β_{m+1} ≤ b′ + C at every step (n = m + 1), so β̄ ≤ b′ + C. RG I p.264 l.32 gives the bound on [0, γ] at each j, not uniformly in j.
- {#C5.95} With (ε/a)ε₁ ≤ σ_k and ρ_k ≤ σ̂_{k,j}, the action part is at most C_A′β̄σ̂_{k,j}ε₁ per point, C_A′ := C_A + 16C_b + 768C₀².
- {#C5.96} The moment defect (Π^G_{22,11} − β^B_{j+1})A_ε(h_z, U^A_k) + N_j(U^A_k) is at most 2496C_XC₀²E₀C_Π(j)ε₁²e^{−δ₀M₁L^j} per point (*The moment of the lifted term.*).
  {#C5.96-1} A_ε(h_z, U^A_k) ≤ 192C₀²ε₁²L^{4(j−k)} by the plaquette bound of the first bullet.
  {#C5.96-2} Each plane-pair action is at most ½(2C₀ε₁/a²)²ε⁴(2a_j/ε)⁴ = 32C₀²ε₁²L^{4(j−k)}, by the same bound, and the 36 coefficients of N_j are at most 2C_Π(j)E₀e^{−δ₀M₁L^j}, which adds 2304C₀².

{#C5.97} So the group has the second bound (σ̂_{k,j}/r_{0,k})(C_X(C_σ + 16C_J)E₀ + C_A′β̄) + 2496C_XC₀²E₀C_Π(j)ε₁²e^{−δ₀M₁L^j} per point, since r_{0,k}ε₁ ≤ 1, with no age factor: the configuration and current parts of the pair line, the action part, and the moment defect.
{#C5.97-1} The smaller of two bounds is at most their geometric mean with the weights 1 − θ_V and θ_V, θ_V := β′/(2(4+β′)), and (x + y)^θ ≤ x^θ + y^θ.
{#C5.97-2} Since (4+β′)(1−θ_V) = 4 + β′/2, per scale-(j+1) point

{#C5.98} (5.1v) |irr^B_{j+1}(U^B_{k+1}) − irr^G(U^A_k)| ≤ E_V[(σ̂_{k,j}/r_{0,k})^{θ_V} + (C_Π(j)ε₁²e^{−δ₀M₁L^j})^{θ_V}](L^{j−k})^{4+β′/2}, E_V := (2E₁(α))^{1−θ_V}(C_X(C_σ + 16C_J + 2496C₀²)E₀ + C_A′β̄)^{θ_V}.

{#C5.99-1} Counting the L^{4(k−j)} scale-(j+1) points per stopping-scale point, the group contributes ≤ E_V[(σ̂_{k,j}/r_{0,k})^{θ_V} + (C_Π(j)ε₁²e^{−δ₀M₁L^j})^{θ_V}]L^{−(β′/2)(k−j)}N_s⁴ per generation.
{#C5.99-2} Since r_{0,k} ≥ ε_k, C_Π(j)ε₁² ≤ max(1, k − j) (*The moment of the lifted term.*), and e^{−δ₀M₁L^j} ≤ e^{−δ₀M₁L^j/2}, the sum over j is ≤ E_VN_s⁴[((σ_k + C(ε₀)ρ_k)/ε_k)^{θ_V}/(1 − L^{−β′/2}) + ((C(ε₀, δ₀M₁)ε₁/ε_k)^{θ_V} + 1)Σ_{j≤k}max(1, k−j)^{θ_V}e^{−θ_Vδ₀M₁L^j/2}L^{−(β′/2)(k−j)}].
{#C5.99-3} With C′_{β′} := sup_{m≥0}max(1, m)L^{−β′m/4}, the last sum is ≤ C′_{β′}(L^{−β′k/8} + e^{−θ_Vδ₀M₁L^{k/2}/2})/(1 − L^{−β′/4}), split at j = k/2.
{#C5.99-4} With σ_k + C(ε₀)ρ_k ≤ C(ε₀)(1 + C_G(ε₀))L^{−(1−2ε₀)k}ε₁ and ε₁ ≤ C_{ε₁}ε_k every part is summable in K.

{#C5.100} *The 𝐑-terms' variation group.* The group Σ_j[𝐑^{B,(j+1)}(U^B_{k+1}) − 𝐑^{B,(j+1)}(pair lift of U^A_k)] of (3.1) has no age factor.
{#C5.100-1} At a regular configuration each term is O(1)(L^jL^{−k})⁴g_j^{κ₀}exp(−κd_j(X)) (CRE p.283 l.34–38), which offsets the L^{4(k−j)} points and no more.
{#C5.100-2} The group is split at the age m_K := ⌊√K⌋ of §4.2.
- {#C5.101} At the ages k − j < m_K, the 𝐑-terms have the properties (i)–(iii) of the 𝐄-terms and the bound (2.31), g_j^{κ₀}exp(−κd_j(X)), on the class (CRE p.260 l.18–25).
  {#C5.101-1} So the frozen-current split of the pair line above gives ≤ (C_σ + 16C_J)(σ̂_{k,j}/r_{0,k})(g^B_{j+1})^{κ₀}exp(−κd_{j+1}(X)) per localisation domain, by the lift condition, as for the 𝐄-terms; the 𝐑-terms carry no coupling coefficient, so no moment enters.
  {#C5.101-2} At these ages j > k − m_K, so e^{−δ₀M₁L^j/2} ≤ L^{−(1−2ε₀)k} and σ̂_{k,j} ≤ C_σ̂L^{−(1−2ε₀)k}ε₁, C_σ̂ := C(ε₀)(1 + C_G(ε₀)) + C(ε₀, δ₀M₁), for K ≥ K₀(L, δ₀M₁, j(C)), finitely many K excepted.
  {#C5.101-3} With the domain count C_X of §8.2 and the L^{4(k−j)} points, these ages contribute ≤ C_X(C_σ + 16C_J)(sup_{k−j<m_K}σ̂_{k,j}/ε_k)L^{4m_K}N_s⁴/(1 − L^{−4}).
  {#C5.101-4} With ε₁ ≤ C_{ε₁}ε_k and k = K − j(C), this is ≤ C_σ̂C_{ε₁}C_X(C_σ + 16C_J)L^{(1−2ε₀)j(C)}L^{4√K−(1−2ε₀)K}N_s⁴/(1 − L^{−4}), summable in K.
- {#C5.102} At the ages k − j ≥ m_K the group is not split.
  {#C5.102-1} With the frozen 𝐑-differences of these ages it is the same-generation difference 𝐑^{B,(j+1)}(U^B_{k+1}) − 𝐑^{A,(j)}(U^A_k), each run at its own minimiser, and §4.2 bounds the sum of these by CN_s⁴(1 + m_K)^{1−κ₀/2}, summable in K for κ₀ ≥ 7.

{#C5.103} So the 𝐑-terms of (3.1) are bounded by the extra generation (§4.1), the frozen 𝐑-differences of the ages < m_K, which S_k bounds, the young part of the group above, and §4.2's tail.
{#C5.103-1} The fluctuation-dependent version is in §10.5.

{#C5.104} So the carried differences contract geometrically in age, and the two-run comparison reduces to the size at birth d_{k+1} of the generation created by one step from inputs differing by d_1, …, d_k. §8 bounds it by (8.3), with the small constant ε_k^* and the contraction θ of #C8.3.3-2.

## 6. The Large-Field Terms: The Unmatched Set and the Matched Pairs {#CS6}

### 6.1 The Unmatched Set {#CS6.1}

{#C6.1.1} A term of (U) has a component Z alive at the stopping scale with first large field at run B's step 1, j(Z) = 1.
{#C6.1.1-1} The large-field regions grow and merge until renormalised ((1.84); LFR I (0.3)), so Z's history meets the large-field region at every scale n = 1, …, k + 1 of run B, and its history volume P(Z) of §11(c), the number of points of its history counted at their own scales, is ≥ k + 1.
{#C6.1.1-2} The sum (11.3) for run B admits the weight ω(Z) := exp(C_PP(Z)) ≥ e^{C_P(k+1)} on that component and ω = 1 on the others, so

{#C6.1.2} (6.1) Σ_{(U)}Z^B_ℓ ≤ Σ_{(U)}M^B_ℓ ≤ e^{−C_P(k+1)}δ_LFZ^B_{ℓ₀} ≤ ½a^{(U)}_Kδ_LFZ^B_{ℓ₀}, a^{(U)}_K := 2e^{−C_P(K−j(C))},

{#C6.1.3} measured against run B's own all-small-field term.
{#C6.1.3-1} Since |𝒲^B| ≤ B_W pointwise in V (the continuum note's (8.1) is assembled from pointwise bounds of the loop's terms, its (6.3), (5.6), and the B_LF of (4.4), #ND.4.9) and Z^B ≥ Z^B_{ℓ₀}, removing the (U) terms from F_{K+1} = N^B/Z^B changes it by at most 2B_WΣ_{(U)}Z^B_ℓ/Z^B ≤ δ_LFa^{(U)}_KB_W, summable in K; no comparison of Z^B_{ℓ₀} with Z^A_{ℓ₀} is used. δ_LF is the bound (11.3) of §11.
{#C6.1.3-2} The entropy of the alive components is inside (11.3).

### 6.2 The Matched Pairs with Large-Field Regions {#CS6.2}

{#C6.2.1} A matched pair τ⁺, τ with large-field components has the same sequence of domains at the shared scales, and its two terms are the same operations applied to run-dependent ingredients.
{#C6.2.1-1} By CRE (2.20)–(2.21) the large-field operation 𝐓 is an ordered product of one-step operations, each an integral over the block variables V_i on Ω^c_{i+1} with the constraint δ(V̄_iV_{i+1}^{−1}) and the large-field functions ζ, and over the fluctuation variables A_i on Z_{i+1} ∩ Ω_{i+1} with the functions χ and the Gaussian form of Δ^{(i)}.
{#C6.2.1-2} The integration variables and the constraint are the same in both runs. The fine lattice enters through the step covariance Δ^{(i)} (§10: relative difference r_i, and the same for the Gaussian normalisations z^{(i)}), and through the characteristic functions built on the local minimisers U_{i,□}(V_i) (LFR I (1.3)–(1.4), CRE (2.17)), which differ on threshold shells.
{#C6.2.1-3} The functions (1.5)–(1.7) of LFR I p.178 depend on the run's coupling. (1.6), (1/z)exp[−g_i^{−2}[1 − Re tr V_i(y,x)]], differs relatively by at most e^{4|δ_i|} − 1 ≤ 10|δ_i| per variable, for |δ_i| ≤ 1/20 (#C6.2.19-3). Indeed 0 ≤ 1 − Re tr V ≤ 2 for the normalised trace, so the exponential changes by a factor in [e^{−2|δ_i|}, e^{2|δ_i|}], and so does z = ∫du χ(|u − 1| < ε_i)e^{−g_i^{−2}(1 − Re tr u)} (CRE (1.5)), whose cutoff ε_i is the same in both runs (#CP.13).
{#C6.2.1-4} So the ratio of (1.6) lies in [e^{−4|δ_i|}, e^{4|δ_i|}]. (1.5) acts on the shared V_i at the threshold ε_i, the same in both runs, and has no shell (`WILSON_IT1_LARGE_FIELD_DEPTH_2026_10_27.md` #2.4). (1.7) tests minimisers on the run's fine lattice at the threshold 2ϑ_i, the same in both runs (ϑ_i := (A₁/A₀)ε_i is Bałaban's δ_i, renamed here to keep δ_i for the coupling difference), and differs on the plaquette shells of (β) (that note's #2.17).
{#C6.2.1-5} The run also enters through the large-field operations' own integrands, the fine-lattice action A(1/(g″_i)²ζ₁, U″(exp ig_iB, V″)) and the form ⟨DH″B, ζDH″B⟩ of LFR II (1.70), and through the effective action on the small-field regions, whose exponent difference is (3.1) layer by layer: on Ω_n ∖ Ω_{n+1} the frozen terms have age n − j and their differences are bounded per scale-n point by D_n + S_n, with the coupling term Cε_n²|δ_n|, and the depth terms e_n.
{#C6.2.1-6} The boundary terms 𝐁 generated at the steps at which a large-field region existed are outputs of those steps' large-field operations, and their two-run differences belong to (γ).
{#C6.2.1-7} Let j₀ be the least i at which a run's term of the pair has a non-empty large-field region Z_i = Λ_i^c. After each 𝐑-operation the term has the post-R domains, in which the removed components leave no large-field region (#C6.2.1-7-1), so every non-empty Z_i belongs to the history of an alive component, and j₀ is the birth scale of the pair's oldest alive component (#CP.2). So Λ_i = T, hence Ω_i = T (Ω_i ⊃ Λ_i, CRE (2.1)), for i < j₀.
{#C6.2.1-7-1} The post-R domains: the first-class components keep only small-field functions and enter the R′-terms (LFR II p.378 l.14–27), whose domains contain a large-field region of a 𝐓′_k-operation (p.390 l.10); the new large-field region is Z_k ∪ ⋃_iY_i (p.390 l.34–35), Z_k there being the large-field region off Z, as the 𝐑-operation renames it (LFR I p.201 l.11: "We denote Z_k∖Z by Z_k"; LFR II's Z_k of p.364 l.29 still contains Z), to which the components with the large-field function are joined in the new large-field region (p.378 l.8, (1.72) at p.379 l.13–20).
{#C6.2.1-7-2} The ingredients at the scales i < j₀ − 1 are those of the all-small-field pair. The step at the scale j₀ − 1 creates Λ_{j₀}, through Ω_{j₀} or R_{j₀} (CRE (3.2)–(3.5), (3.16), (3.20)), so its tests carry run-dependent thresholds (CRE (3.3) at 2ϑ_{j₀−1}, (3.2) at ε_{j₀}, (3.16) at ϑ_{j₀−1}), and its layer Γ_{j₀−1} = T ∖ Ω_{j₀} may be non-trivial (#C6.2.18-1).
{#C6.2.1-8} Two cases, with m := ⌊k/2⌋.

{#C6.2.2} If k − j₀ ≥ m, the oldest component X meets the large-field region at every scale from j₀ to k, so its history volume is P(X) ≥ m + 1, as in §6.1.
{#C6.2.2-1} The sum (11.3) with the weight ω(X) := exp(C_PP(X)) on it bounds each run's terms of this kind by e^{−C_P(m+1)}δ_LF times that run's own Z_{ℓ₀}, and removing them from each run's F changes it by at most 2B_We^{−C_P(m+1)}δ_LF, as in §6.1; for the two runs together this is ≤ 3e^{−C_Pm}δ_LFB_W, since 4e^{−C_P} < 3.

{#C6.2.3} If k − j₀ < m and k ≥ k_*(j(C), ḡ) (*The threshold.*, #C6.2.19), every component of the pair was born at a scale > k − m ≥ k/2, so j₀ − 1 ≥ k − m, the ingredients at the scales i < j₀ − 1 are the all-small-field pair's, and at the scales i ≥ j₀ − 1 ≥ k − m the two terms differ in three ways.

- {#C6.2.4} (α) On the common support of the two runs' characteristic functions the small-field ingredients differ as follows.
  - {#C6.2.5} The frozen exponents and the depth terms differ per point by D_i + S_i + e_i ≤ C_a[(i+1)θ̃^i + w_K], by (8.6) and the depth sources e_i ≤ C_eθ̃^i (§8.7), since C_a ≥ 2C_s(1 − L^{−β′}/θ̃)^{−1} + C_S″ + C_e (#C8.7.7).
    {#C6.2.5-1} The coupling term differs by Cε_i²|δ_i| ≤ |δ_i|, since ε_i = A₀ĝ_i(log ĝ_i^{−2})^{p₀} (CRE (2.4), #CP.13) gives Cε_i² ≤ 1 for γ small.
  - {#C6.2.6} The function (1.6) differs relatively by at most 10|δ_i| per variable (#C6.2.1-3).
  - {#C6.2.7} The covariance differs by r_i ≤ C(ε₀, γ_H)[L^{−γ_H(i−1)} + ε₁L^{−(1−ε₀)i}/α_*] ≤ C_δΔ[L^{−γ_H(i−1)} + L^{−(1−ε₀)i}], by (10.6), with C_δΔ := C(ε₀, γ_H)max(1, ε₁/α_*), so the Gaussian form changes by ≤ Cr_i|A_i(b)|² per variable, and the normalisations z^{(i)} relatively by r_i per variable (§10).
    {#C6.2.7-1} On the fluctuation cutoff, |A_i| < r^χ_i ≤ (A₁/A₀)p₀(ĝ_i) (#C8.2.1-6), this is ≤ Cr_ip₀(ĝ_i)² per variable, with p₀(ĝ_i)² ≤ ℓ_K (§8.7).
    {#C6.2.7-2} Where a large-field function χ^c leaves A_i unbounded, the factor e^{Cr_i|A_i|²} is absorbed by the form (C^{(i)})^{−1} ≥ C_cov^{−1} (C_cov the bound of the rescaled covariance C^{(k)} = (C*Δ^{(k)}C)^{−1} of A_k, RG I p.268 l.3, bounded by its random-walk expansion in [13] (RG II p.13 l.19, [13] = PBG), used in §8.2(b)).
    {#C6.2.7-3} This changes Bałaban's positivity bound of the A_i-integral, the gain of χ^c included, by at most the factor exp(2CC_covr_i(1 + p₀(ĝ_i)²)) per variable.
  - {#C6.2.8} The history-localised constants differ per point in two parts.
    {#C6.2.8-1} The vacuum-energy counterterms are subtractions of one-step small-field vacuum energies (CRE p.262 l.16–20), so they differ by the class norm d_i of their step, ≤ C_a[(i+1)θ̃^i + w_K] by (8.6).
    {#C6.2.8-2} The normalisation constants (−½d(𝐠)log g_i^{−2} + log σ₀) per variable (LFR II (1.70), p.380 l.24–28) differ by ½d(𝐠)|log(1 + g_i²δ_i)| ≤ d(𝐠)g_i²|δ_i| ≤ |δ_i|.
  - {#C6.2.18} The small-field exponent on the last domain Λ_k, outside the components, differs by the groups of (3.1) restricted to Λ_k, its vacuum constants cancelling in F as for the all-small-field pair (#C3.5-4).
    {#C6.2.18-1} At the young pairs' backgrounds, multiscale VAR minimisers whose non-trivial layers are Γ_n, n ≥ j₀ − 1 ≥ k/2 (CRE (2.2), p.255 l.15–16: Γ_{j₀−1} = T ∖ Ω_{j₀}), the groups are bounded on Λ_k one by one, and Λ_k has at most N_s⁴ points; the sum is at most X_K of (7.1) at every point of the integration (#C7.3), whose variation and classical parts cover both geometries (#C7.4).
    {#C6.2.18-2} The extra generation and the old tail (§4.1–4.2). CRE (2.43)–(2.44) hold at the multiscale U_k(V) for every domain Ω of 𝐃_k in B^j(Λ_j^0), with E₁ and R₁ independent of j, k, Ω, {Ω_j}, and {Λ_j} (CRE p.263 l.5–13). For Ω ⊂ Λ_k ⊂ Ω_k only the layer Γ_k = Ω_k (CRE p.255 l.15–16; Γ_{k+1} in run B's indexing) meets Ω, so the sums of (2.43)–(2.44) have the single term of §4.1 and §4.2, and X^{dir}_K holds as for the all-small-field pair.
    {#C6.2.18-3} The coupling term (a). (9.2) holds on the cubes of the stopping layer, the layer k, with the spacing a itself (the large-field note's #4.7), so abs(A_{ε/L}(U^B_{k+1}(V))) restricted to Λ_k is ≤ Cε_k²N_s⁴ as in #C3.11-1. There the large-field note's ε₁ (its #D.ε₁) enters (9.2), so C is the larger of #C3.11-1's constant and the one (9.2) gives with that ε₁; it is the C of the coupling term in C_a (#C8.7.7).
    {#C6.2.18-4} The frozen differences. D_k + S_k per point is (8.6): the class norms are suprema over the class 𝒞_k, which contains the young pairs' multiscale minimisers (#C5.8-5, at the young histories' n > k/2 ≥ n₀ for k ≥ k_*, #C6.2.19), and the depth sources of (8.6) include these backgrounds through h_i and C′_e (#C8.7.1-1).
    {#C6.2.18-5} The classical group (b). The large-field note's §4(b) runs §9 for the multiscale problem point by point (its #4.8, #4.40–#4.41). In #4.41 the weight is w := ζ₁/(g″)², ζ₁ LFR II's cutoff, 0 ≤ ζ₁ ≤ 1, and 1/(g″)² CRE (2.24)'s smooth coupling function, 1/g_{j−1}²(x) = 1/g_j²(x) + β_j(g_{j−1})φ_j(x) (p.259 l.17–21), whose value at x lies between g_{j(x)}^{−2} and g_{j(x)−1}^{−2} (its #4.41-1-1), and w satisfies the bound on abs(w) + a·abs(∇w) that #4.41 needs.
    {#C6.2.18-5-0} This gives the per-point bound C_w(ε₀)g_{j(x)}^{−2}(ε/a_n)^{1−ε₀}(ε₁^{LF})² with a_n the spacing of the history's finest layer (its #4.42). On Λ_k, with g_{j(x)}^{−2} ≤ g_a^{−2} + b₂k (CRE (2.6), b₂ of #CK.1-14; g_k = g_a) and a_n ≥ εL^{k/2}, the group is ≤ N_s⁴C_w(ε₀)(g_a^{−2} + b₂k)L^{−(1−ε₀)k/2}(ε₁^{LF})².
    {#C6.2.18-6} The variation groups ((5.1v) and #C5.101). At the points of Λ_k the pair line's distance is the large-field note's σ_c ≤ C^{LF}(ε₀)d̄(x) (its #4.321, C^{LF}(ε₀) its #D.C(ε₀)), with d̄(x) = C_U(M)(ε/a_n)^{(1−ε₀)/3}ε₁^{LF} at the stopping layer (its #4.314), plus the tail of ι_X (#C9.8.13–#C9.8.17, #C5.8-9). Here ε₁^{LF} is the large-field note's ε₁ (#CP.27).
    {#C6.2.18-7} So σ̂_{k,j} is replaced by σ̂^Λ_{k,j} := σ̂_{k,j} + C_{yd}L^{−(1−ε₀)k/6}ε₁^{LF}, C_{yd} := C^{LF}(ε₀)C_U(M), in (5.1v) and #C5.101-1, both increasing in σ̂.
    {#C6.2.18-7-1} c^{LF}_{ε₁} := sup_Kε₁^{LF}/ε_k ≤ C(M)R_{k_s} is finite and uniform in K: this is LF #1.6-3 at its step k = k_s (LF #D.k_s), where m_s = 1, and R_{k_s} = R^T_{k_s} depends only on ĝ_{k_s}^{−2} = ḡ^{−2} + b′j(C) + C_W (#CP.13).

  {#C6.2.9} Each of these but the last enters per point of the component's history at its own scale: the layers Γ_i, the block variables on Ω^c_{i+1}, and the fluctuation variables on Z_{i+1} ∩ Ω_{i+1}, all inside Z_{i+1}.
  {#C6.2.9-1} So on the common support the two integrands, measured by Bałaban's bounds, differ relatively by at most exp(X_K + Σ_Xφ′_X) − 1, φ′_X := C_Ms′_KP(X), with C_M the number of the per-point ingredients per point (a constant of d, L, and G) and s′_K := 2C_a[(k+1)θ̃^{k−m} + w_K] + 4C(1 + C_cov)C_δΔℓ_K[L^{−γ_H(k−m−1)} + L^{−(1−ε₀)(k−m)}] + 10sup_{i≥k−m}|δ_i|.
  {#C6.2.9-2} Here C ≥ 1 is the constant of the covariance item (p₀(ĝ_i)² ≤ ℓ_K and ℓ_K ≥ 1).
  {#C6.2.9-3} At fixed j(C) and ḡ, s′_K → 0 as k → ∞: (k + 1)θ̃^{k−m} → 0 since k − m ≥ k/2, w_K → 0 (#C6.2.17), the covariance terms decay geometrically against the polylogarithm ℓ_K, and for i ≥ k − m ≥ k/2 (8.6) gives |δ_i| ≤ C[kθ̃^{k/2} + Kw_K], since (i + 1)θ̃^{i+1} ≤ (k + 1)θ̃^{k/2} and K + 1 − i ≤ 2K, and this tends to 0, since Kμ_K = K^{3−κ₀/2}ℓ_K → 0 for κ₀ > 6.
- {#C6.2.10} The threshold shells of the characteristic functions, where one run's function is 1 and the other's 0.
  {#C6.2.10-1} The shells of the radial tests (1.5), (1.9), and χ^{(j−1)c}(R_j) are bounded in `WILSON_IT1_LARGE_FIELD_DEPTH_2026_10_27.md` §2(b); the shells of the plaquette and reference-configuration tests are (β) of the (LF) line.
- {#C6.2.11} The large-field integrands, the boundary terms 𝐁 of the steps with large-field regions, and the large-field dressings of the dressed loop: (γ) of the (LF) line; the dressings are bounded in `WILSON_IT1_LARGE_FIELD_DEPTH_2026_10_27.md` §5, those at the 𝐑-operations with the loop in its §5(e).

{#C6.2.12} (β) and (γ) are the input (LF) (#CP.2–#CP.2-2).
{#C6.2.12-1} In the form (LF-1) it asks that, for a history born at a scale > k/8, their run-dependence change the term by at most (exp(Σ_XΣ_iC_Ms^{LF}_{n(X)}L^d|Z_i ∩ X|_i) − 1) times run A's majorant M^A_τ of (11.1) on the common support (run B's own-support shells: run B's majorant M^B_{τ⁺}, below), with s^{LF}_n ≤ C_hθ̃^n.
{#C6.2.12-2} Since Σ_i|Z_i ∩ X|_i ≤ P(X) by the definition of the history volume (§11(c)) and every component of a young pair is born at a scale n(X) > k − m ≥ k/2, this exponent is ≤ C_Ms^{LF}_KL^dP(X) with s^{LF}_K := C_hθ̃^{k/2}.
{#C6.2.12-3} Let s_K := s′_K + L^ds^{LF}_K and φ_X := C_Ms_KP(X).

{#C6.2.19} *The threshold.* Let k_*(j(C), ḡ) be the least integer such that k_* ≥ 2n₀ and, for every k ≥ k_*, s′_K ≤ ½ and L^dC_hθ̃^{k/2} ≤ ½. Here n₀ is the large-field note's threshold of its #4.621, so that the young histories, n > k/2 ≥ n₀, are admitted to 𝒞_k (#C5.8-5).
{#C6.2.19-1} It exists, since s′_K → 0 (#C6.2.9-3) and θ̃ < 1.
{#C6.2.19-2} It depends on j(C) and ḡ through C_a, C_h, θ̃, ℓ_K = (log(bK + ḡ^{−2}))^{rd+2p₀} (with K = k + j(C)), w_K (its parts (K + 1)θ̃^{k_s/8}, (K + 1)2^{−k_s/16}, and μ_K), and the factor K + 1 − i of (8.6)'s bound on |δ_i|, besides the constants.
{#C6.2.19-3} For k ≥ k_*, s_K ≤ 1, since L^ds^{LF}_K = L^dC_hθ̃^{k/2} ≤ ½, and |δ_i| ≤ s′_K/10 ≤ 1/20 at the scales i ≥ k − m, which the bound of (1.6) uses (#C6.2.1-3).
{#C6.2.19-4} The young pairs are compared below for k ≥ k_*; for the finitely many k < k_* the matched pairs with large-field regions are bounded at once (*The smaller k.*, #C6.2.21).

{#C6.2.20} The three-piece split of `WILSON_IT1_LARGE_FIELD_DEPTH_2026_10_27.md` §2(b), ρ^B − ρ^A = Π_AΠ_B(ρ_B − ρ_A) + Π_B(1 − Π_A)ρ_B − Π_A(1 − Π_B)ρ_A, puts each shell term on one run's own support.
{#C6.2.20-1} Run B's piece Π_B(1 − Π_A)ρ_B is at most the shell mass times Bałaban's bound of run B's term (that note's #2.9, #2.16, #4.165), that is, it is measured against run B's majorant M^B_{τ⁺} of (11.1), and it is removed from run B first, after (6.3).
{#C6.2.20-2} For the rest, ρ^{B′}[τ⁺] := Π_AΠ_Bρ_B against ρ^A[τ], (LF-1) is measured against run A's majorant M^A_τ: on the common support the LF note compares the two runs' factors by the differences of their logarithms (e.g. its #4.155), relative to run A's term.
{#C6.2.20-2-1} *The shells in s′_K.* Per point of a history at a scale i ≥ k − m, relative to Bałaban's bound, two ingredients enter: the sharp-cutoff shells (LF §2(b) and below) and the soft tests' coupling parts. A variable carries the sharp cutoffs of at most s_T(i) steps (LF #3.38-1), at most 8s_T(i) of them (LF #3.21's eight, each at most once per step), each shell ≤ Cp₀(ĝ_i)^{d_G}g_i²|δ_i| (LF #2.10–#2.15, and for LFR I (1.55) #C6.2.20-2-2); since s_T(i) ≤ 2 + log_L(16L⁴(L + 1)²) + ν_L log_L log g_i^{−2} (LF #3.40-1, #CP.14), they sum to ≤ |δ_i| for γ small.
{#C6.2.20-2-2} LFR I (1.55) tests the two runs' common B_j (LF #3.28) under a form analogous to CRE (3.15) (LFR I p.188 l.1–2), so #C8.6.9-3's density bound applies with LF #2.12's per-bond precision. Its threshold on the scaled B_j is g_j^{−1}δ′_j ≤ A₁p₁(ĝ_j), δ′_j = ĝ_jA₁p₁(ĝ_j) (LFR I p.183 l.2; LFR II p.383 l.21; #CP.13), (1.55) printing δ′_j, a slip; the shell bound holds at both, since A₁ < A₀ (CRE p.248 l.11) and p₁ < p₀. The coupling parts of all the soft tests at a cube, the cascade tests with their factor N + 1 included, sum to ≤ |δ_i| (LF #3.40-1). So C_M counts ingredients per point, not tests.
{#C6.2.20-3} The triangle inequality, (α) on the common support (where the difference is ≤ (e^{X_K + Σφ′_X} − 1) times Bałaban's bound of ρ^A, the densities being positive on the real integration region, LFR I p.176 l.20), the radial shells and the coupling parts of the soft tests (per point, inside the term 10sup_{i≥k−m}|δ_i| of s′_K, #C6.2.20-2-1–#C6.2.20-2-2), and (LF) on the rest give, integrating over V,

{#C6.2.13} (6.2) ∫|ρ^{B′}[τ⁺] − ρ^A[τ]| dV ≤ (s_K + x_K)Π_{X⊂Z(τ)}ω^s(X)·M^A_τ, ∫Π_B(1 − Π_A)ρ_B[τ⁺] dV ≤ s_KΠ_{X⊂Z(τ⁺)}ω^s(X)·M^B_{τ⁺}, ω^s(X) := (1 + C_MP(X))e^{C_Ms_KP(X)} ≤ e^{C_PP(X)}, a weight of (11.3) below #C6.2.2-1's ω(X),

{#C6.2.14} since Z^A_τ ≤ M^A_τ, (e^a − 1) + (e^b − 1) ≤ e^{a+b} − 1 for a, b ≥ 0, e^{X_K + Σφ_X} − 1 = x_Ke^{Σφ_X} + (e^{Σφ_X} − 1) with x_K := e^{X_K} − 1 and e^{Σφ_X} = Π_Xe^{φ_X} ≤ Π_Xω^s(X), e^{Σφ_X} − 1 ≤ (Σ_Xφ_X)e^{Σφ_X}, Σ_XC_MP(X) ≤ Π_X(1 + C_MP(X)), and C_P ≥ 2C_M with s_K ≤ 1.
{#C6.2.14-1} The own-support piece is run B's own term against its own majorant, so the small-field exponent on Λ_k is not compared there.
{#C6.2.14-2} Hence, by (11.3) for each run with these weights, for the young pairs,

{#C6.2.15} (6.3) Σ_{(M), young}∫|ρ^{B′}[τ⁺] − ρ^A[τ]| dV ≤ δ_LF(s_K + x_K)Z^A_{ℓ₀}, Σ_{(M), young}∫Π_B(1 − Π_A)ρ_B[τ⁺] dV ≤ δ_LFs_KZ^B_{ℓ₀}.

{#C6.2.16} Removing run B's own-support pieces, of total mass m_B and total n_B against the dressed loop, |n_B| ≤ B_Wm_B, changes run B's F = N^B/Z^B by |(n_B − F^Bm_B)/(Z^B − m_B)| ≤ 2B_Wm_B/Z^B_{ℓ₀} ≤ 2B_Ws_Kδ_LF, since |F^B| ≤ B_W and Z^B − m_B ≥ Z^B_{ℓ₀}, the removed pieces being parts of young large-field terms and the densities being positive.

{#C6.2.22} The callers integrate against the dressed loop: ∫|𝒲^Bρ^{B′} − 𝒲^Aρ^A| ≤ B_W∫|ρ^{B′} − ρ^A| + ∫|𝒲^B − 𝒲^A|ρ^A.
{#C6.2.22-1} The second term is bounded in the same way: the small-field dev insertions at the points of the components' histories by the recursion of §8.3, inside s′_K; those on Λ_k as for the all-small-field pair, by B_WX_K ≤ B_Wx_K (#C7.2); and the large-field dressings by `WILSON_IT1_LARGE_FIELD_DEPTH_2026_10_27.md` §5, (5.1)–(5.2), with s^{W,tot}_K of that note's §5(f).
{#C6.2.22-2} So the first sum of (6.3) holds for the young pairs' numerators with B_W(2s_K + 2x_K + s^{W,tot}_K) in place of s_K + x_K: B_W(s_K + x_K) from the densities, B_W(s_K + x_K) from the dev insertions, and B_Ws^{W,tot}_K from the dressings.
{#C6.2.22-3} Then N^{B′}/Z^{B′} − N^A/Z^A = (ΔN − F^{B′}ΔZ)/Z^A with |F^{B′}| ≤ B_W, and since Z^A ≥ Z^A_{ℓ₀}, the remaining young pairs change F by ≤ B_Wδ_LF(2s_K + 2x_K + s^{W,tot}_K) through the numerators and by ≤ B_Wδ_LF(s_K + x_K) through the normalisation.
{#C6.2.22-4} With run B's own-support pieces, the young pairs change F by ≤ B_Wδ_LF(5s_K + 3x_K + s^{W,tot}_K) in all.
{#C6.2.22-5} The old pairs are not compared: they change each run's F by the amount computed above, ≤ 3e^{−C_P⌊k/2⌋}δ_LFB_W for the two runs.
{#C6.2.22-6} So, for k ≥ k_*(j(C), ḡ), the matched pairs with large-field regions change F_{K+1} − F_K by at most δ_LFb^{(M)}_KB_W, b^{(M)}_K := 3e^{−C_P⌊k/2⌋} + 5s_K + 3x_K + s^{W,tot}_K.

{#C6.2.17} b^{(M)}_K is summable in K. Its first term is geometric.
{#C6.2.17-1} In s_K the terms w_K and Kw_K are summable, Kw_K entering through |δ_i| ≤ C[kθ̃^{k/2} + Kw_K] for i ≥ k − m by (8.6) (#C6.2.9-3). Their parts μ_K = K^{2−κ₀/2}ℓ_K and Kμ_K = K^{3−κ₀/2}ℓ_K are summable for κ₀ > 8 (κ₀ ≥ 11), ℓ_K being a power of log(bK + ḡ^{−2}), and the rest, at most K(K + 1)(θ̃^{k_s/8} + 2^{−k_s/16}) with k_s = K − j(C), decays exponentially in K at fixed j(C).
{#C6.2.17-2} The other terms of s_K are geometric in k up to polynomial factors in k, the covariance terms up to the polylogarithm ℓ_K, and s^{LF}_K = C_hθ̃^{k/2} is geometric. s^{W,tot}_K is summable by that note's §5(f), for κ₀ > 10 (its #5.66), and x_K is summable (#C7.4-1).

{#C6.2.21} *The smaller k.* For the finitely many k < k_*(j(C), ḡ), (11.3) with ω = 1 bounds each run's matched pairs with large-field regions, old and young, by δ_LF times its own Z_{ℓ₀}.
{#C6.2.21-1} Removing them changes each run's F by at most 2B_Wδ_LF, as in §6.1, so they change F_{K+1} − F_K by at most δ_LFb^{(M)}_KB_W with b^{(M)}_K := 4.

## 7. The Assembly of the Estimate {#CS7}

{#C7.1} The Cauchy estimate |F_{K+1} − F_K| ≤ a_K follows from (3.1)–(3.2), §4, §5, §6, §8, §9, §10, and §11, and from the input (LF) (#CP.2–#CP.2-2) under the conditions (T1), (T2), (T-Λ), and (T-c) (#CP.22, #CP.26–#CP.28).
{#C7.1-1} (LF) enters only through the young matched pairs of §6.2, through h_n in the 𝒟_{[j]} of §8.4 and §8.6 and through §8.6's 𝒟^∗_j and C_h, and through the young components' operations and the V-terms at the young 𝐑-steps of §7.6 and §7.8 (#C7.6-6-2-1-1, #C7.6-6-2-2), in all through its ingredient (γ). (W-δ) enters through the V-terms (#C8.6.21-5), at the young 𝐑-steps of the loop constant and the wraps' births (#C7.6-6-2-1-1, #C7.8-4) and at the large-field note's generated part and 𝐑-operations with the loop (its #5.38-3, #5.48-1).
{#C7.1-2} The lift condition enters through (5.1c) and (5.1v) of §5, and the 𝐑 version of (5.1c) through §10.5.
{#C7.1-3} The groups of (3.1): the carried frozen differences of the all-small-field matched pairs are D_k + S_k per stopping-scale point, the coupling term is ≤ Cε_k²|δ_k|, the variation group is ≤ the sum over j of (5.1v), summable in K ((5.1v) of §5, §10.5), its 𝐑-terms' group is split at the age ⌊√K⌋ (§5, *The 𝐑-terms' variation group*, with §4.2's tail), and the classical group (b) is (9.10), with (3.2) reducing it to one-step statements about regular fields.
{#C7.1-4} By (8.6) of §8.7, D_k + S_k + Cε_k²|δ_k| ≤ C_a[(K+1)θ̃^{K−j(C)} + (j(C)+2)w_K] (#C8.7.6), with w_K = (K + 1)(θ̃^{k_s/8} + 2^{−k_s/16}) + μ_K, μ_K = K^{2−κ₀/2}ℓ_K, and ℓ_K = (log(bK + ḡ^{−2}))^{rd+2p₀}; this is summable in K. (8.6) uses the birth-scale form s^{LF}_n ≤ C_hθ̃^n of (LF).
{#C7.1-5} The supports of the all-small-field pair differ by the shells of the stopping-scale test, which change F_{K+1} − F_K by ≤ b^{(S)}_KB_W (§3), by (RS), summable (#C3.10-2).
{#C7.1-6} The matched pairs with large-field regions change F_{K+1} − F_K by ≤ δ_LFb^{(M)}_KB_W (§6.2: the old pairs each run against its own Z_{ℓ₀}, the young pairs by (6.3)), summable (#C6.2.17).
{#C7.1-7} (8.3) also covers the dev insertions of the dressed loops (the project's class D(k) at equal leading words) and the per-step coefficients β_{k+1}, hence δ_k through |Δβ_{k+1}| ≤ C_βd_{k+1} (§8.3); the matched large-field pairs are §6.2; the unmatched set is §6.1 with the δ_LF of §11.

{#C7.2} *The all-small-field pair in F.* On the common support of the two all-small-field terms the groups of (3.1), that is D_τ(V) + E^B − E^A, are bounded at every V by the sum of the bounds collected above (#C7.1-3, #C7.1-4):

{#C7.3} (7.1) |D_τ(V) + E^B − E^A| ≤ X_K := X^{dir}_K + N_s⁴C_a[(K+1)θ̃^{K−j(C)} + (j(C)+2)w_K] + X^{var}_K + X^{𝐑}_K + X^{cl}_K, x_K := e^{X_K} − 1,

{#C7.4} with X^{dir}_K the direct bounds of §4.1–4.2; X^{var}_K the sum over j of (5.1v) (§5, §10.5) and X^{𝐑}_K the bound of the young part of the 𝐑-terms' variation group (#C5.101) and of its old part (#C5.102), the young part with σ̂^Λ_{k,j} of #C6.2.18-7 in place of σ̂_{k,j} (the old part's bound contains no σ̂); and X^{cl}_K := X^{cl,0}_K + N_s⁴C_w(ε₀)(g_a^{−2} + b₂k)L^{−(1−ε₀)k/2}(ε₁^{LF})², with X^{cl,0}_K the bound of the classical group (b) by (3.2) and (9.10) and the second term its bound at the young pairs (#C6.2.18-5).
{#C7.4-1} Each of them is summable in K. The parts that σ̂^Λ_{k,j} − σ̂_{k,j} = C_{yd}L^{−(1−ε₀)k/6}ε₁^{LF} adds are, with ε₁^{LF} ≤ c^{LF}_{ε₁}ε_k (#C6.2.18-7-1), at most E_VN_s⁴(C_{yd}c^{LF}_{ε₁})^{θ_V}L^{−θ_V(1−ε₀)k/6}/(1 − L^{−β′/2}) in X^{var}_K (#C5.99-2) and at most C_{yd}c^{LF}_{ε₁}C_X(C_σ + 16C_J)L^{4√K−(1−ε₀)k/6}N_s⁴/(1 − L^{−4}) in X^{𝐑}_K (#C5.101-3). The second term of X^{cl}_K is geometric times linear in k, since (ε₁^{LF})² ≤ (c^{LF}_{ε₁})²ε_k². So X_K is summable and bounded in K, and x_K ≤ X_Ke^{X_K} is summable.
{#C7.4-2} There, the dev insertions of the two dressed loops differ by at most B_WX_K, by §8.3's recursion for them (#C8.3.3-4). The transports of their words, the leading word among them, change the dressed loop by at most λ_KB_W (#C7.5, #C7.5-6, #C7.5-7). The wrap insertions change it by at most x^w_KB_W (#C7.8).
{#C7.4-2-1} The final interaction weights Q_{K′}(𝔅) of the two runs change it by at most x^Q_KB_W (#C7.9).
{#C7.4-3} The vacuum constants are pure numbers and cancel in F (#C3.5-4), so on the common support run B's term is e^{D_τ + E^B − E^A} times run A's for the purpose of F.
{#C7.4-4} Hence, with run A's constant on both runs (#C1.2-5), ∫|e^{E^A_const}(𝒲^Bρ^B_{ℓ₀} − 𝒲^Aρ^A_{ℓ₀})| ≤ B_W(x_K + X_K + λ_K + x^w_K + x^Q_K)Z^A_{ℓ₀} and ∫|ρ^B_{ℓ₀} − ρ^A_{ℓ₀}| ≤ x_KZ^A_{ℓ₀} there.
{#C7.4-4-1} Here B_W bounds e^{E^A_const} times either run's dressed loop on ℓ₀ pointwise, run B's included: abs(E^A_const) ≤ B_E (#C1.2-4), and B_W ≥ e^{B_E}exp(Σ_nν_n) for each run's insertion masses ν_n (#C7.5-7).
{#C7.4-5} As in §6.2, N′/Z′ − N/Z = (ΔN − F′ΔZ)/Z with |F′| ≤ B_W (#C7.4-4-1) and Z ≥ Z^A_{ℓ₀}. So the pair changes F_{K+1} − F_K by at most B_W(2x_K + X_K + λ_K + x^w_K + x^Q_K) ≤ (3x_K + λ_K + x^w_K + x^Q_K)B_W on its common support, since X_K ≤ x_K, besides the shells b^{(S)}_KB_W of §3.
{#C7.4-6} The young matched pairs carry the same bound X_K on their small-field exponents on Λ_k (§6.2, #C6.2.18), and their leading words are compared by the large-field note's (T) (its #5.23–#5.24, #5.28), inside s^{W,tot}_K (its #5.63; #C6.2.22-1).
{#C7.4-7} *The smaller K.* The bounds of #C7.1–#C7.8 are derived for K ≥ K₁. K₁ is the least K such that every K′ ≥ K, with k′ := K′ − j(C), has the following properties.
{#C7.4-7-1} k′ ≥ k₀(ε₀) (§9.6), k′ ≥ k_*(j(C), ḡ) (#C6.2.19), and K′ ≥ K₀(L, δ₀M₁, j(C)) (#C5.101-2).
{#C7.4-7-2} max(m^E_{K′}, m^w_{K′}) ≤ ⌊k′/4⌋ (#C7.6-4, #C7.6-6-2-6, #C7.8-3), and m^w_{K′} ≤ ⌊k′/8⌋, the large-field note's m_W (#C7.8-5).
{#C7.4-7-3} Every scale i ≥ k′ + 1 − max(m^E_{K′}, m^w_{K′}) is an 𝐑-step of both runs, i > N_i (#C7.6-6, #C7.8-4).
{#C7.4-7-4} ρ^E_{K′} ≤ ¼, so that the discs of #C7.6-6-8 and #C7.8-4-2 have radius ≥ 2.
  {#C7.4-7-4-1} ρ^E_{K′,0} ≤ 1/8 and 2K_ΔC″c″x^*_{K′}/(1 − θ_Q) ≤ 1/8. These give -4 (#C7.6-6-4-4), and with #CP.22-5 and X_w ≤ 2μ^{pt} (#C7.8-9-3) they give ρ̃ ≤ ¼ (#C7.8-9-5).
{#C7.4-7-5} K₁ exists: m^E_K and m^w_K grow as log log K; N_i at the scales of -3 is O((log log log K)^ν) by #C7.6-6; and ρ^E_K tends to 0, since r̄^E_K does (#C8.7.7-1), r^V_K does (#C7.6-6-2-1-2), and s_K does (#C6.2.9-3, θ̃ < 1).
  {#C7.4-7-5-1} ρ^E_{K,0}, x^*_K, and y^*_K tend to 0 as well (#C7.8-9-8-2), and μ₀ does not depend on K, so -4-1 and -6 hold for K large.
  {#C7.4-7-5-2} The torus period T_ph/u enters these conditions only through a_w and a^{w,2}, by decreasing functions: L^{m^w_K} ≤ max(L, 3Llog(K + 2)/a_w), τ^w_K, a_{Ew} in r̄^E_K, and T_w. Since a_w, a^{w,2} ≥ a₀ (#CP.22-5-1) and μ₀ is taken at a₀ (#C7.8-9-3), each condition holds whenever its version with a₀ in place of a_w and a^{w,2} holds. So K₁ ≤ K̄₁, the least K such that every K′ ≥ K has the a₀-versions of the properties, which exists by -5 and -5-1 and does not depend on T_ph/u.
{#C7.4-7-6} y^*_{K′} ≤ μ₀/2, so that the disc of #C7.8-9-9 has radius R_E ≥ 2.
{#C7.4-8} For the finitely many K < K₁, |F_{K+1} − F_K| ≤ 2B_W, since F_K = N_K/(κ_KZ_K) is the renormalised expectation W_ren(ε_K) and abs(W_ren(ε_K)) ≤ B_W for every K (the continuum note's (8.1), #ND.8.1), so a_K := 2B_W there.

{#C7.5} *The leading word.* On the common support of the all-small-field pair, abs(f^B_{k+1} − f^A_k) ≤ λ_K := 4ℓ_C‖dπ‖(4C_G(ε₀) + C_Y)ε₁L^{−(1−ε₀)k}, geometric in K.
{#C7.5-1} By #C9.7.1, U^A = e^{iεA′*}MU^B in the Landau gauge relative to MU^B, with sup|A′*| ≤ 4ρ/a and ρ = C_G(ε₀)(ε/a)^{1−ε₀}ε₁, so ε|A′*(c)| ≤ 4C_G(ε₀)(ε/a)^{2−ε₀}ε₁ on every bond c of T_ε.
{#C7.5-2} RG I (0.4) gives MU^B(c) = e^{iY_c}W(c) (#C10.1.4-0-2), W(c) the transport of U^B along the L fine bonds of c, with |Y_c| ≤ C_Y(ε/a)²ε₁ (the large-field note's (Y), #5.21–#5.22, with its C_Y and under its condition).
{#C7.5-3} So Hol_C(U^B) = Π_cW(c) and Hol_C(U^A) = Π_ce^{iεA′*(c)}e^{iY_c}W(c) up to a gauge transformation, which leaves the closed trace unchanged, the products over the bonds c of C in T_ε in order.
{#C7.5-4} Telescoping inside the normalised trace, with π unitary and ‖π(e^{iX}) − 1‖_op ≤ ‖dπ‖|X|, gives abs(f^B − f^A) ≤ Σ_c‖dπ‖(ε|A′*(c)| + |Y_c|). C has side ℓ_C in bonds of T_a (the continuum note's #ND.1.1), so 4ℓ_CL^k bonds of T_ε, and 4ℓ_CL^k(ε/a)^{2−ε₀} = 4ℓ_CL^{−(1−ε₀)k}, so the sum is ≤ λ_K.
{#C7.5-5} This is the large-field note's (T) (its #5.23–#5.24, #5.28) with every bond at the stopping scale and (9.8) for its (P′); it holds where (9.8) does, k ≥ k₀(ε₀) (§9.6), that is, for K ≥ K₁.
{#C7.5-6} *The transports of the words with insertions.* A word w(𝔅) of the dressed loop with insertions 𝔅 ≠ ∅ is the normalised trace of the ordered product along C of the insertions' operators and the transports between them, read on the run's background (the large-field note's #5.11; map #MD2.0.3.5). The insertions transform covariantly at their slots (D2.7 15.5(ii)(γ): each transforms by π(u) at the end sites of its arc), so the gauge transformation of #C7.5-3 leaves w(𝔅) unchanged when it transforms the insertions too.
{#C7.5-6-1} With the insertions held fixed, the telescoping of #C7.5-4 over the bonds of the transports gives abs(w^B(𝔅) − w^A(𝔅)) ≤ λ_KΠ_{b∈𝔅}‖Y_b‖, as the large-field note's #5.25 has on the matched pairs.
{#C7.5-7} Summed over 𝔅 with the leading word (𝔅 = ∅), the transports change the dressed loop at fixed insertions by at most λ_KΠ_b(1 + ‖Y_b‖) ≤ λ_Kexp(Σ_nν_n). Here ν_n is the insertions' weighted mass on the traversal n of a step-K′ bond, each insertion counted at its first traversal (the continuum note's (5.3), #ND.5.4), and ‖Y_b‖ is at most its weighted mass.
{#C7.5-7-1} The exponent of the continuum note's (8.1) bounds Σ_nν_n (#ND.5.4-2), so e^{B_E}exp(Σ_nν_n) ≤ B_W (#ND.8.1). With run A's constant the transports therefore change e^{E^A_const}𝒲 by at most λ_KB_W.

{#C7.6} *The loop constant.* E^A_const = Σ_{j≤k}E°^A_j and E^B_const = Σ_{j≤k+1}E°^B_j (#C1.2-4). Index the per-step terms by m := k + 1 − j in run A and m := k + 2 − j in run B, the map's index of #MD2.3.7.2, so that run B's step j + 1 and run A's step j, the shared scale, carry the same m ≥ 1, and run B's extra step 1 has m = k + 1.
{#C7.6-1} Each per-step term is at most A_EL^{m/2}e^{−a_EL^{m/2}} (#C7.6-2–#C7.6-3-2), with a_E := min(a^T_E, b^R_E/2), a^T_E := min(c^T_E, c^Z)/L, b^R_E := c^R_E/(LR^E), R^E := MR_{K−j(C)}, R at the stopping scale, a function of j(C) alone (#CP.13-1), A_E := A^{TZ}_E𝔞̄/(ea^T_E) + ℓ_CA^R_E, {#D.A^{TZ}_E} A^{TZ}_E := ℓ_C(2C^T_E + 12C̄_Z), A^R_E := 16e^{−2}C^R_ER^E(b^R_E)^{−2}, and ℓ_C ≥ 1. C^T_E, c^T_E, C̄_Z, and c^Z are the map's C_E, c_E, C̄_Z, and c^Z (#MD2.3.7.3), and C^R_E, c^R_E are the C and c of D2.7 15.4(ii).
{#C7.6-2} At the T-steps the corner and torus parts are at most 2C^T_E𝔞̄ℓ_CL^me^{−c^T_Eℓ_CL^m} + 12C̄_Z𝔞̄ℓ_CL^me^{−c^Zι_{T,j}} (map #MD2.3.7.3, for the admissible sides of #MD2.3.7.4), with ι_{T,j} = L^{m−1}ι_T^{stop} ≥ L^{m−1}, ι_T^{stop} ≥ 1 the run's ι_T at its stopping scale (map #MD2.0.5.40, and (TC), #MD2.3.4.43).
{#C7.6-2-1} So the T-part is at most A^{TZ}_E𝔞̄L^me^{−a^T_EL^m} ≤ (ea^T_E)^{−1}A^{TZ}_E𝔞̄L^{m/2}e^{−a^T_EL^{m/2}}: with y := L^{m/2} ≥ 2, y² ≥ 2y and ye^{−a^T_Ey} ≤ (ea^T_E)^{−1}.
{#C7.6-3} At the 𝐑-steps D2.7 15.4(ii) bounds the corner and torus remainder by C^R_EMR_je^{−p₀(g_j)/4}[(s + 1)e^{−c^R_Es/(MR_j)} + se^{−c^R_Eι_{T,j}/(MR_j)}], its c being in MR_j-cube units, with s = ℓ_CL^{m−1} the side of C in step-j units. Since ℓ_C ≥ 1 and ι_{T,j} ≥ L^{m−1} (#C7.6-2), both exponentials are at most e^{−c^R_EL^{m−1}/(MR_j)}, and 2s + 1 ≤ 3ℓ_CL^{m−1}.
{#C7.6-3-1} MR_k = R^E at the stopping scale k (#C7.6-1), and R changes by at most the factor L per step and by at most L^{(m−1)/2} over m − 1 ≥ 2 steps (#CP.14-1, #CP.14-2), so MR_j ≤ R^EL^{m/2}. With e^{−p₀(g_j)/4} ≤ 1 and 3L^{m−1} ≤ L^m (L ≥ 3), the remainder is at most ℓ_CC^R_ER^EL^{3m/2}e^{−b^R_EL^{m/2}}.
{#C7.6-3-2} With y := L^{m/2}, y²e^{−b^R_Ey/2} ≤ 16e^{−2}(b^R_E)^{−2}, its maximum, at y = 4/b^R_E. So the remainder is at most ℓ_CA^R_EL^{m/2}e^{−(b^R_E/2)L^{m/2}}, uniformly in K, since R^E does not depend on K. Run B's step j + 1 has the same R_j and R^E (#CP.13-1).
{#C7.6-4} *The old part (m ≥ m^E_K): not compared.* Let m^E_K be the least integer m ≥ 1 with a_EL^{m/2} ≥ 2log(K + 2). For m ≥ m^E_K the ratio of consecutive terms is L^{1/2}e^{−a_E(L^{1/2}−1)L^{m/2}} ≤ L^{1/2}4^{−(L^{1/2}−1)} ≤ ½ (L ≥ 4), so each run's old part is at most 2A_EL^{m^E_K/2}e^{−a_EL^{m^E_K/2}} ≤ τ^E_K := 2A_Emax(L^{1/2}, 2L^{1/2}log(K + 2)/a_E)(K + 2)^{−2}, summable in K.
{#C7.6-4-1} For K ≥ K₁, m^E_K ≤ k + 1 (#C7.4-7), so run B's extra step, m = k + 1, lies in the old part, and every young term has a partner at the same m.
{#C7.6-5} *The young part (1 ≤ m < m^E_K): compared.* Each per-step term is the constant part of the cluster expansion of the step's marked gas, the corner and torus remainders after the perimeter part is moved into κ (map #MD2.3.7.11).
{#C7.6-6} *The young steps are 𝐑-steps.* For K ≥ K₁ every young step of #C7.6 and #C7.8 is an 𝐑-step of both runs (#C7.4-7): at the shared scales i ≥ k + 1 − max(m^E_K, m^w_K), i > N_i, since N_i ≤ O(1)(log g_i^{−2})^ν (map #MD2.3.4.16-1), g_i ≥ g_k/((1 + β₀)max(m^E_K, m^w_K)^{1/2}) (CRE (2.6)), and g_k = g_a lies in the K-independent window (#C11c.6-2).
{#C7.6-6-1} *The term at an 𝐑-step.* At an 𝐑-step the per-step term is E°^T_i + E°^R_i (map #MD2.3.5.5-2). The T-part E°^T_i is the corner and torus remainder of the step's cluster series 𝒲° at flat trivial-label data (map #MD2.3.6.1, #MD2.3.6.2). The 𝐑-part E°^R_i is the corner and torus remainder of E^R_i(C) = log(Ξ^c/Ξ) of D2.7 15.4(i), after 15.4(ii) moves the perimeter part into κ. #C7.6-2 and #C7.6-3 bound them.
{#C7.6-6-1-1} *The constituents.* Ξ^c is the cluster series of a gas whose group activities c_gΠ_{P∈g}F(P) are bounded by (ĉ₁)^{#components}e^{−κ(size)} (15.4(i)). F(P) is built from Bałaban's 𝐄- and 𝐑-activities, the first-class components' operations 𝐓′_i(X) at the flat reference, the V-terms V(Y), and the loop's marked activities in the slots (15.3).
{#C7.6-6-1-1-0} 𝐓′_i(X) is a measure on the component's variables that (1.91) applies to the V-terms and the slots, compared in total variation, with total mass 𝐓′_i(X)1 bounded by its factor b(X) := exp(−2(1 + β₀)^{−1}p₀(ĝ_i) + 1) in (1.92), at ĝ_i (#CP.13). The V-terms enter (1.91) through Π_{Y∈𝐃}V(Y) and exp Σ_{Y∈𝐃}t(Y)V(Y), integrated over Bałaban's t(Y) ∈ [0, 1]. They are re-summed by Bałaban's operators from the old 𝐑-terms and boundary terms (LFR II p.377), with the bound (1.68), abs(V(Y)) ≤ αexp(−(1 + 2β)κd_{k,Z}(Y)).
{#C7.6-6-1-2} 𝒲° is the cluster series of the step's loop gas at flat trivial-label data (map D2.3(4)–(6)). It is built from the step's polymer activities at trivial labels and from the loop's marked activities in the slots. A polymer activity is an integral over the step's variables in a connected union X of M-cubes, bounded with Bałaban's decay e^{−κd_i(X)}, d_i(X) the length of a shortest tree graph meeting the cubes (RG I p.257 l.14–16).
{#C7.6-6-2} *The pairing.* The two runs' steps at a shared scale have the same lattice, cubes, and loop, and the same partitions through the shared R (#CP.13-1), so the constituents pair by shape and position. Each run's bound of a constituent is Bałaban's function of the parameters of #CP.13 at the scale i, its amplitude carrying p₀(ĝ_i), so the two runs' bounds coincide; b̄ denotes this common bound, against which the pairs differ as follows.
{#C7.6-6-2-1} Bałaban's activities and the marked activities differ by at most r^E_i := C^E_r(iθ̃^i + w_K) times b̄. Here C^E_r := max(2C_s(1 − L^{−β′}/θ̃)^{−1} + C_S″, 4C_s, 4C^*_{ins}(1 − L^{−β′}/θ̃)^{−1}). Bałaban's activities are covered by D_i + S_i (S_i ≥ d^R_i, #C8.4.1) and d_{i+1} ≤ 2C_s(i + 1)θ̃^{i+1} + 2C_sw_K ≤ 4C_s(iθ̃^i + w_K) ((8.6), #C8.7.4). The loop's marked activities are covered by D^{ins}_i and d^{ins}_{i+1} (#C8.7.7-3).
{#C7.6-6-2-1-1} The V-terms V(Y) differ by at most r^V_K times their bounds (1.68), r^V_K := sup_{i≥k−⌊k/4⌋−1}[4C_hθ̃^{k_s/8} + 4e²(C_{rD} + C_{rE} + C_{rC})2^{−k_s/16} + 2𝒟^V_i], by #C8.6.21–#C8.6.22-2. The range covers the young 𝐑-steps of §7.6 and §7.8 (#C7.6-6) and the large-field note's steps i ≥ k − m_W − 1 (its #5.38-3), since max(m^E_K, m^w_K, m_W) ≤ ⌊k/4⌋. These include the old terms' own differences (𝒟^V_i of #C8.6.21-1), the re-summing operators' difference through the input (W-δ) (#C8.6.21-5), and (LF) through C_h and 𝒟^∗_i. The domain count is absorbed by eα (#C8.6.22-1).
{#C7.6-6-2-1-2} §8.6's bracket covers every V(Y) of a polymer all of whose components are young: a non-deep V(Y) has every point of Y at a layer > k_s/8 (#C8.6.20-1), as #C8.6.20 and #C8.6.21-2 need, and a deep one is bounded by #C8.6.19-2. Here every component is young and first-class. The loop constant is the series on the all-small-field term ℓ₀, whose gas has every component of the old large-field region first-class (D2.7 15.4(iii)), so it has no second-class or unchanged components, and a group meeting one would have c_g := 0 (15.4(i)).
{#C7.6-6-2-1-2-0} The old components are removed (#C7.6-6-3), and the others were born at scales > k − ⌊k/2⌋. r^V_K times any power of log(K + 2) is summable. D_m + S_{m−1} and 𝒟^∗_i are at most a constant times (m + 1)θ̃^{m−1} + w_K (#C7.6-6-2-1; the large-field note's #4.669), at layers m > k_s/8 − 1. There (m + 1)θ̃^{m−1} ≤ C_θθ̃^{k_s/16−3/2}, C_θ := sup_{m≥0}(m + 1)θ̃^{m/2}, so each term of r^V_K is a constant times θ̃^{k_s/16−3/2}, θ̃^{k_s/8}, 2^{−k_s/16}, or w_K.
{#C7.6-6-2-1-3} The marked activities' differences also carry the wraps' source s^w (#C8.3.3-4-4), which adds at most 2s^w/(1 − θ_Q) ≤ 2K_ΔC″c″x^*_K/(1 − θ_Q) to r^E_i (#C8.7.7-4, #C7.8-9-8-1). ρ^E_K covers it (#C7.6-6-4-4).
{#C7.6-6-2-2} A component X born at n(X) > k − ⌊k/2⌋, as the young pairs' components of #C6.2.3, has §6.2's run-dependence per point of its history at the scales ≥ n(X): (α), the shells (β), and (γ) through (LF) (#C6.2.1 to #C6.2.11). As in (6.2) for one component and without Λ_k, each of the three pieces of #C6.2.20 is at most s_Kω^s(X)M̄(X). Here M̄(X) is the larger of the two runs' bounds (1.79) of the total mass 𝐓′_i(X)1. The pieces are total-variation masses of 𝐓′^B_i(X) − 𝐓′^A_i(X), which (6.2)'s ∫abs(ρ^B − ρ^A) supplies, and (LF) enters in the form (LF-1) for 𝐓′_i(X) against M̄(X) (#CP.2-1).
{#C7.6-6-2-3} For every component, (11.2) at the scale i (#C11c.3) gives, for each run's own bounds, ω^s(X)M(X) ≤ e^{C_PP_i(X)}M(X) ≤ e·exp(−κ̂_i(X) − ½G_i(X) − 2p₀(ĝ_{j(X)})) ≤ b(X), as in #C11c.3-2. Here P^c_i(X), κ̂_i(X), and G_i(X) are ≥ 0, and p₀(ĝ_{j(X)}) ≥ p₀(ĝ_i), since ĝ_{j(X)} ≤ ĝ_i for j(X) ≤ i (#CP.13). So each run's 𝐓′_i(X)1 is at most e^{−C_PP_i(X)}b(X), and the pair of -2-2 differs by at most 3s_Kb̄(X) in total variation: the spare factor e^{−C_PP_i(X)} of #C11c.3-7 pays ω^s(X).
{#C7.6-6-2-4} A T-part polymer activity on X has at trivial labels only (α) per point and the radial shells as its run-dependence (#C6.2.5 to #C6.2.8, #C6.2.20-3). So #C6.2.9-1 and the three-piece split give at most 3C_Ms′_Kn(X)e^{C_Ms′_Kn(X)} times b̄ for the pair, with n(X) its number of points.
{#C7.6-6-2-5} n(X) ≤ M^d#cubes(X) ≤ N^{pt}(1 + d_i(X)), with N^{pt} := 2·3^dM^d. Indeed, a tour of a shortest tree graph has length 2d_i(X), so it is covered by at most 2d_i(X) + 1 sets of diameter ≤ 1 in M-cube units, and each of these meets at most 3^d M-cubes.
{#C7.6-6-2-6} *The old components.* A component born at n(X) ≤ k − ⌊k/2⌋ is not compared. At a young step of #C7.6 or #C7.8, i ≥ k + 1 − max(m^E_K, m^w_K) with max(m^E_K, m^w_K) ≤ ⌊k/4⌋ (#C7.4-7-2), it meets the large-field region at every scale from n(X) to i, so P_i(X) ≥ i − n(X) + 1 ≥ k/4, as in #C6.2.2. By -2-3 each run's 𝐓′_i(X)1 is then at most e^{−C_Pk/4}b(X).
{#C7.6-6-3} *The old components removed.* For each run and 𝔷 ∈ ℂ with abs(𝔷) ≤ e^{C_Pk/4}, multiply the operation 𝐓′_i(X) of every old component by 𝔷. Each stays within its bound b(X) (-2-6), so the gas converges as at 𝔷 = 1, and E°^R_i(𝔷) is analytic in 𝔷 with #C7.6-3's bound. E°^R_i(0) is the step's 𝐑-part without old components. By Cauchy's estimate on the disc of radius e^{C_Pk/4} ≥ 2, abs(E°^R_i(1) − E°^R_i(0)) ≤ 2e^{−C_Pk/4}A_EL^{m/2}e^{−a_EL^{m/2}} for each run.
{#C7.6-6-4} *The interpolation.* Let {#D.ρ^E_{K,0}} ρ^E_{K,0} := max(r̄^E_K, r^V_K, 3(1 + eC_MN^{pt})s_K) and ρ^E_K as in #C7.6-6-4-4, with s_K of #C6.2.12-3, and r̄^E_K := C^E_r[kθ̃^kmax(L, 3Llog(K + 2)/a_{Ew})^{2/3} + w_K], a_{Ew} := min(a_E, a_w) (#C7.8-2); r̄^E_K ≥ r^E_i at the young steps of #C7.6 and #C7.8 (#C7.6-7). For ς ∈ ℂ with abs(ς) ≤ 1/(2ρ^E_K) put x^ς := x^A + ς(x^B − x^A) for every constituent x of the step without old components, on its domain.
{#C7.6-6-4-0} The parameter ς is not Bałaban's t(Y) of (1.91), which stays in its integral, nor one of his large-field functions ζ, ζ₁ inside the operations (#C6.2.1-1).
{#C7.6-6-4-1} Then abs(x^ς) ≤ abs(x^A) + abs(ς)abs(x^B − x^A) ≤ (3/2)b^A(x) ≤ 2b^A(x), b^A = b̄ run A's bound, for Bałaban's activities, the marked activities, the V-terms, and the young components' operations, the last in total variation (-2-1, -2-1-1, -2-3; ρ^E_K ≥ r^E_i, r^V_K, 3s_K).
{#C7.6-6-4-2} For a T-part polymer activity put σ := C_MN^{pt}s′_K and κ_I := κ/6, with κ ≥ 12, so that κ_I ≥ 2. Since ρ^E_K ≥ 3eσ (s′_K ≤ s_K) and ρ^E_K ≤ ¼, σ ≤ 1/(12e) < 1. With d := d_i(X) and 1 + d ≤ e^d, abs(ς)·3C_Ms′_Kn(X)e^{C_Ms′_Kn(X)} ≤ (3σ/(2ρ^E_K))(1 + d)e^{σ(1 + d)} ≤ (1/(2e))(1 + d)e·e^{σd} ≤ ½e^{(1 + σ)d} ≤ ½e^{κ_Id}. So abs(x^ς) ≤ (1 + ½e^{κ_Id})b^A(x) ≤ 2e^{κ_Id_i(X)}b^A(x).
{#C7.6-6-4-3} The gas built from the x^ς by the formulas of D2.7 15.3–15.4 and map D2.3(4)–(6) is run A's at ς = 0 and run B's at ς = 1 except for the wraps (#C7.6-6-4-5), both without old components.
{#C7.6-6-4-4} {#D.ρ^E_K} ρ^E_K := ρ^E_{K,0} + 2K_ΔC″c″x^*_K/(1 − θ_Q), with x^*_K of #C7.8-9-8 and θ_Q of #C8.7.7-4. The second term covers the wraps' part of the marked activities' differences (#C7.8-9-7-1), so ρ^E_K bounds the relative differences of the constituents (#C7.8-9-8-1). It is defined from ρ^E_{K,0}, and x^*_K is defined without ρ^E_K, so the definition is not circular.
{#C7.6-6-4-5} The wraps are not among the interpolated constituents. They are held at run A's, so at ς = 1 the gas is run B's with run A's wraps, and the t-step of #C7.8-9-9 moves them.
{#C7.6-6-5} At the flat reference the group factors c_g are numbers fixed by the shapes and positions (15.4(i)), the same for both runs, so the term depends on the run only through the constituents. In the bounds of 15.3–15.4 (Bałaban's (1.92)–(1.97) with the changes of 15.3) and of map D2.3(5)–(6) each constituent enters through its bound, an amplitude times decay factors that do not involve the amplitudes.
{#C7.6-6-6} At the x^ς the amplitudes are multiplied by at most 2, and for the T-part's polymer activities the decay κ is lowered to κ − κ_I. The convergence conditions are smallness conditions on the amplitudes. For the 𝐑-part, α "can be chosen arbitrarily small for γ small enough" (LFR II p.377 l.14), so the conditions hold at 2α for γ small, and b(X) carries e^{−2(1+β₀)^{−1}p₀(ĝ_i)}; its decay is unchanged.
{#C7.6-6-6-1} For the T-part, the map's derivation covers any prefactor α with αe^{20.25}O_{(1.26)} ≤ 1/8 (map #MD2.4.1.17-1), and its prefactors are α₆ and 2(L+2)⁴O₃ε₂. At twice their size they meet it once α₆ and ε₂ are taken half as large. α₆ is a choice made as small as wanted (map #MD2.4.10.5: α₆ ≤ a small number times L^{−4}). It enters the A of the map's (10) (#MD2.4.10.5), and so its κ-condition 324A ≤ δλ_Lκ (map #MD2.4.10.7), which halving it only relaxes; the A of map #MD2.4.1.20-5 contains no α₆.
  {#C7.6-6-6-1-1} ε₂ is not free: ε₂ = 2E₀ε₁C₁α₄^{−1}α₆^{−1}M^qe^{C₂κ₁} (RG II p.19, map #MD2.4.1.6), with RG II's own C₁, C₂, and q (#CK.1-32). So ε₂ halves when RG II's ε₁ is taken four times smaller. p.20's assumption 2(L+2)⁴O(1)ε₂e^{5κ} ≤ 1 (map #MD2.4.1.7) is met by taking ε₁ small after κ, κ₁, M, α₄, and α₆, so a smaller ε₁ is of the same kind.
  {#C7.6-6-6-1-2} RG II's conditions (1/20)γ₂ε₁²/γ² ≥ 18κ and e^{−γ₂ε₁²/(20γ²)} ≤ ε₂ (RG II p.19) are read in the map with t_k² := (δ_k/g_k)² in place of ε₁²/γ², as smallness conditions on g_K (map #MD2.4.10.2, #MD2.4.10.32-2), so they do not involve ε₁, and the second holds at the halved ε₂ for g_K small. The upper bound ε₂e^{max(5, 3λ_L)κ} ≤ 1 (map #MD2.4.10.7) only improves. The one lower bound on ε₁, O(1)ε_k < ε₁ (map #MD2.1.4.31), is a smallness condition on g_K and holds at the smaller ε₁ for γ small.
{#C7.6-6-6-2} For the T-part's decay, κ is a free large constant of the construction with lower thresholds, such as map #MD2.4.1.20-5's κ ≥ max(κ_vac, 3240A/(L − 2)) at L ≥ 3, the map's standing condition, which this note inherits. So the cluster bounds of map D2.3(4)–(6) hold at the decay κ − κ_I = 5κ/6 once κ is at least 6/5 times those thresholds and κ ≥ 12 (#C7.6-6-4-2), conditions of the same kind, with positive rates. Both series then converge uniformly in abs(ς) ≤ 1/(2ρ^E_K) and are analytic in ς there.
{#C7.6-6-7} The subtractions (15.4(ii); map #MD2.3.5.5 and #MD2.3.5.9) use only the translation covariance, which the x^ς inherit from both runs. So #C7.6-2's and #C7.6-3's bounds hold at every such ς with constants C^{T,2}_E, C̄^{(2)}_Z, C^{R,2}_E and rates c^{T,2}_E, c^{Z,2}, c^R_E, their values at the enlarged amplitudes and the lowered decay: abs(E°_i(ς)) ≤ A^{E,2}L^{m/2}e^{−a^{E,2}L^{m/2}}, with A^{E,2} and a^{E,2} #C7.6-1's A_E and a_E at these constants and rates.
{#C7.6-6-8} *Cauchy's estimate.* ρ^E_K ≤ ¼ (#C7.4-7-4). On the disc of radius R := 1/(2ρ^E_K) ≥ 2, abs(E°_i(1) − E°_i(0)) ≤ sup_{abs(ς)=R}abs(E°_i(ς))/(R − 1) ≤ 4ρ^E_KA^{E,2}L^{m/2}e^{−a^{E,2}L^{m/2}}, for the step's terms without old components.
{#C7.6-7} At i = k + 1 − m with m < m^E_K, iθ̃^i ≤ kθ̃^kθ̃^{1−m} ≤ kθ̃^kL^{m^E_K/3} ≤ kθ̃^kmax(L^{1/2}, 2L^{1/2}log(K + 2)/a_E)^{2/3}, since θ̃ ≥ L^{−1/3} and L^{m^E_K/2} ≤ max(L^{1/2}, 2L^{1/2}log(K + 2)/a_E). For m < m^w_K the same gives kθ̃^kmax(L, 3Llog(K + 2)/a_w)^{1/3} (#C7.4-7-5-2). Both are at most r̄^E_K's first term, so r^E_i ≤ r̄^E_K.
{#C7.6-7-0} With #C7.6-6-3 for the old components, the young parts differ by at most Δ^E_K := 4ρ^E_KA^{E,2}S^{(2)}_E + 4e^{−C_Pk/4}A_ES_E + 2(ea^T_E)^{−1}A^{TZ}_E(𝔞̄y^*_K/μ₀ + x^*_K/C_S′)S_E, the last term the wraps' (#C7.8-9-9–#C7.8-9-9-2), with S_E := Σ_{m≥1}L^{m/2}e^{−a_EL^{m/2}} and S^{(2)}_E the same sum at a^{E,2}.
{#C7.6-7-1} *The sum lemma.* For a > 0 and a real base Λ ≥ 2, Σ_{m≥1}Λ^me^{−aΛ^m} ≤ e^{−a}(1 + 6/a). For m ≥ 2, Λ^m − Λ^{m−1} ≥ Λ^m/2, so Λ^me^{−aΛ^m} ≤ 2∫_{Λ^{m−1}}^{Λ^m}e^{−ax}dx and Σ_{m≥2} ≤ 2e^{−aΛ}/a ≤ 2e^{−a}/a. The m = 1 term is e^{−a}Λe^{−a(Λ−1)} ≤ e^{−a}max(1, 1/a), the maximum over Λ ≥ 2 being at Λ = 1/a or at Λ = 2, where 2e^{−a} ≤ max(1, 1/a) since 2ae^{−a} ≤ 2/e. At Λ = L^{1/2} ≥ 2, S_E ≤ e^{−a_E}(1 + 6/a_E) and S^{(2)}_E ≤ e^{−a^{E,2}}(1 + 6/a^{E,2}).
{#C7.6-7-2} Δ^E_K, and ρ^E_K times any power of log(K + 2), are summable in K. So are w_K and kθ̃^k times such a power (#C8.7.7-1), r^V_K times it (#C7.6-6-2-1-2), and s_K times it (#C6.2.17-1, #C6.2.17-2), whose term Kw_K carries Kμ_K = K^{3−κ₀/2}ℓ_K with κ₀ ≥ 11; e^{−C_Pk/4} is geometric.
  {#C7.6-7-2-1} This is ρ^E_{K,0}'s part. The wraps' parts, x^*_K in ρ^E_K and y^*_K/μ₀ and x^*_K in Δ^E_K, are summable with any power of log(K + 2) by #C7.8-9-8-2 and #C7.8-9-9-2, whose summands are ρ^E_{K,0}, τ^{pt}_K, e^{−C_Pk/4}, and r̄_K.
{#C7.6-8} So abs(E^B_const − E^A_const) ≤ ΔE_K := min(2τ^E_K + Δ^E_K, 2B_E), the second bound by #C1.2-4; ΔE_K is summable and at most 2B_E.
{#C7.6-9} Let F^{B,A} := e^{E^A_const − E^B_const}F_{K+1}, run B's expectation with run A's constant. Then F_{K+1} − F_K = (F^{B,A} − F_K) + (e^{E^B_const − E^A_const} − 1)F^{B,A}, and abs(F^{B,A}) ≤ B_W, since B_W bounds run B's dressed loop with run A's constant pointwise (#C7.4-4-1). So the second term is at most (e^{ΔE_K} − 1)B_W.
{#C7.6-10} §§3–6, #C7.1–#C7.5, and #C7.8 bound F^{B,A} − F_K (#C1.2-5), with B_W as the pointwise bound of both runs' dressed loops with run A's constant (#C7.4-4-1).

{#C7.7} *The result.* For K ≥ K₁, abs(F_{K+1} − F_K) ≤ a_K := [3x_K + λ_K + x^w_K + x^Q_K + b^{(S)}_K + δ_LF(a^{(U)}_K + b^{(M)}_K)]B_W + (e^{ΔE_K} − 1)B_W, by #C7.4-5, #C7.6-9, #C7.6-10, §3, §6.1, and §6.2.
{#C7.7-1} a_K is summable in K: e^{ΔE_K} − 1 ≤ ΔE_Ke^{2B_E}, and the terms in the bracket are summable (#C7.4-1, #C7.5, #C7.8-8, #C7.9-4, #C3.10-2, #C6.1.3-1, #C6.2.17).

{#C7.8} *The wrap insertions.* On the all-small-field pair the dressed loops carry, besides the dev insertions, the wrap insertions wrap(j), j ≤ K′, of D(K′)(ii) (map #MD2.0.3.29). They have no deviation bound, #C8.3.3-4's recursion does not contract them, and each grows by at most L per step (map #MD2.0.3.34-4).
{#C7.8-1} Their masses are weighted by {#D.w^w} w(W) := e^{θ(W)+ν_rσ(W)+(5/8+1/L)ν_e·ext(W)} ≥ 1, with σ, θ, and ext in production units (map #MD2.4.13.13; map D2.0(3) *Units of carried groups*). Per traversal of a step-i bond, the scale-j wraps have weighted mass Σw(W)‖Y_W‖ at most C^w_ML^{i−j}ρ̂^w_je^{−c^w_MN^{(j)}_min/M} (#C7.8-1-1, #C7.8-1-2), with {#D.C^w_M} C^w_M := e^{ν_e}, {#D.c^w_M} c^w_M := ν_e/8, and {#D.ρ̂^w_j} ρ̂^w_j := max(C_S′ρ̂_j, C_S″b_j)·pl_j (map #MD2.0.3.34-4, #MD2.0.5.40-6).
  {#C7.8-1-0} Here N^{(j)}_min ≥ c^w_N(T_ph/u)L^{K′−j+j(C)} in step-j units (map #MD2.3.4.16-6, #MD2.0.3.35-1, c^w_N the lower constant of its ≍), and the loop has 4ℓ_C step-K′ bonds (the continuum note's #ND.1.1).
  {#C7.8-1-1} *Production.* A wrap group made at the step j has ext_j ≥ N^{(j)}_min/(2M) − 1 in π_j-sides, N^{(j)}_min being in step-j bonds (the D2.6 closure 2.1(e) and its *Precedence and units*). (S-w) with its c-version bounds Σ_{𝒢∋n, wrap}e^{θ+ν_rσ+ν_e·ext}‖Y_𝒢‖ by ρ̂^w_j per traversal n (closure 2.1(e); map #MD2.4.12.12-2). Against that weight w(W) is smaller by e^{−(3/8−1/L)ν_e·ext} ≤ e^{ν_e}e^{−(ν_e/8)N^{(j)}_min/M}, since (3/8 − 1/L)/2 ≥ 1/8 for L ≥ 8. This is #C7.8-1 at i = j.
  {#C7.8-1-2} *Carry.* The weight of a carried wrap is fixed, and each wrap grows by at most L per traversal and step (map #MD2.0.3.34-4), which gives L^{i−j}. Its reference activity c_𝒢 = Y_𝒢(1, 0) is a number fixed at production, bounded there by (S-w)'s c-version (map #MD2.4.12.12-2), and the carry leaves it unchanged, since the block averages of the flat configuration are flat. So #C7.8-1 holds for Σw(W)|c_W| as well, and every bound of #C7.8 below holds for the c_W, their differences being fixed at birth.
  {#C7.8-1-3} *The ε̂ weight.* The Kotecký–Preiss check of a step's gas weighs a group by e^{s(W)+(ν_r/16)σ(W)}, s := sh + b + (3/16)ν_rσ + log C_pc′ (map #MD2.4.12.38–#MD2.4.12.38-1). By map #MD2.4.12.23-2 and #MD2.4.12.27-3, s + (ν_r/16)σ ≤ (3/4)ν_rσ + (3/8 + 1/L)ν_e·ext + 2c_sh + log C_pc′ + c_πα_{1,k+1}|win|.
    {#C7.8-1-3-1} Map #MD2.4.12.27 gives c_πα_{1,k+1}|win| ≤ (ν_r/16)σ + 40c_πα_{1,k+1}, and 40c_πα_{1,k+1} ≤ 1 by 4c_πMα_{1,k+1} ≤ 1 (map #MD2.4.8.1-2), which also gives log C_pc′ ≤ 1 + log C_pc for C_pc′ = C_pce^{40c_πα_{1,k+1}} (map #MD2.4.12.28). Hence e^{s+(ν_r/16)σ} ≤ C_ε̂e^{−(ν_e/4)ext}w(W), with {#D.C_ε̂} C_ε̂ := e^{2c_sh+2}C_pc, free of the step, since θ ≥ 0, 13/16 ≤ 1, and 3/8 + 1/4 = 5/8.
  {#C7.8-1-4} *Positions.* The positions of map #MD2.4.12.38-1 are the traversals of a group's arc and the cubes incompatible with its set. At a traversal p, Σ_{W at p}e^{s+(ν_r/16)σ}x_W ≤ C_ε̂Σ_{W∋p}w(W)x_W for any x_W ≥ 0. A cube Δ incompatible with X_W lies within one cube of a cube of X_W, so within ext(W) + 2 of every traversal of W (map #MD2.4.12.30), distances at the step i being at most those in production units.
    {#C7.8-1-4-1} Counting W at one of its traversals n with dist(n, Δ) ≤ R + 3, R := ⌊ext(W)⌋, gives, as in the map's box reduction, Σ_{W at Δ}e^{s+(ν_r/16)σ}x_W ≤ C_ε̂Σ_{R≥0}8M(2R + 7)e^{−(ν_e/4)R}sup_nΣ_{W∋n}w(W)x_W. Since 1 − e^{−a} ≥ ae^{−a/2}, Σ_{R≥0}(2R + 7)e^{−aR} ≤ 2/a² + 14/a ≤ 16/a² for a ≤ 1, and a = ν_e/4 ≤ 1 (ν_e ≤ ν/8, map #MD2.0.3.32). So every position sum at the ε̂ weight is at most C_possup_nΣ_{W∋n}w(W)x_W, with {#D.C_pos} C_pos := 2048C_ε̂M/ν_e².
{#C7.8-2} A wrap of scale j grows by at most L per traversal and step while the traversals shrink by L, so the total over C does not grow. With the index m := K′ + 1 − j of #C7.6, which is the same for run B's j + 1 and run A's j, the wraps of age m have total weighted mass at most A_wL^me^{−a_wL^m} at every step. Here A_w := 4ℓ_CC^w_Msup_jρ̂^w_j/L and a_w := c^w_Mc^w_N(T_ph/u)L^{j(C)−1}/M.
{#C7.8-3} *The old wraps (m ≥ m^w_K): not compared.* Let m^w_K be the least integer m ≥ 1 with a_wL^m ≥ 3log(K + 2). As in #C7.6-4, each run's old wraps have total weighted mass at most τ^w_K := 2A_wmax(L, 3Llog(K + 2)/a_w)(K + 2)^{−3}. The exponent 3 makes m_Wτ^w_K summable, which the large-field note's (D) needs (its #5.41, #5.65.1). Since ‖Y_W‖ ≤ w(W), the two runs' old wraps differ in total, unweighted, by at most 2τ^w_K, an absent wrap counting as 0. For K ≥ K₁, m^w_K ≤ k + 1 (#C7.4-7-2), so run B's step-1 wraps are old.
{#C7.8-4} *The young wraps (m < m^w_K): compared at birth.* A young wrap is made at a shared step i ≥ k + 2 − m^w_K, an 𝐑-step (#C7.4-7-3), by the step's T-part or 𝐑-part (#C7.6-6-1), as a localisation piece of a loop-linked activity of the step's gas (D2.7 15.3, 15.5(ii)). At aligned arguments it is a function of the step's constituents (#C7.6-6-1-1, #C7.6-6-1-2) and of the occurrences merged into it at birth (#C7.8-4-0), paired and compared as in #C7.6-6-2 to #C7.6-6-2-6.
{#C7.8-4-00} A carried wrap in one of its slots is held at run A's here, and its difference passes to the new wrap as to a descendant (#C7.8-5-1). The evaluation at each run's own background is the carry of #C7.8-5.
{#C7.8-4-0} *The merged occurrences.* At the step i the interaction weights Q_{i−1} of the old insertions are expanded in occurrences, and each occurrence joins one group as a vertex whose factor, a cluster activity φ_{i−1}(Γ) of the step-(i − 1) reference gas, enters the group's activity as a number (map #MD2.3.3.4–#MD2.3.3.5-4, #MD2.4.12.17). The φ_{i−1}(Γ) are functions of the reference activities of the step i − 1's groups, so of that step's constituents.
  {#C7.8-4-0-1} The step i − 1 ≥ k + 1 − m^w_K is an 𝐑-step of both runs (#C7.4-7-3), and r^E_{i−1} ≤ r̄^E_K by #C7.6-7's bound at m = m^w_K: θ̃^{1−m} ≤ L^{(m−1)/3} ≤ L^{m^w_K/3}, with L^{m^w_K} ≤ max(L, 3Llog(K + 2)/a_w) (#C7.8-7).
{#C7.8-4-1} Remove the old components as in #C7.6-6-3 and interpolate the other constituents as in #C7.6-6-4. The wraps made from the x^ς are analytic in ς, run A's at ς = 0 and run B's at ς = 1. Map #MD2.0.3.34-4's bound holds for them with a rate c^{w,2}_M and a constant C^{w,2}_M ≥ C^w_M, its values at the enlarged amplitudes and the lowered decay (#C7.6-6-5 to #C7.6-6-6-2).
  {#C7.8-4-1-1} This is done at the steps i − 1 and i with the same ς and the same 𝔷. At the step i − 1 the reference activities are then analytic in ς and at most twice their bounds (#C7.6-6-6). The gas's Kotecký–Preiss condition (map #MD2.4.12.38-2, ε̂ ≤ ν_r/(1296M)) holds at twice the activities for γ small, its left side being proportional to them. So the φ^ς_{i−1}(Γ) are analytic in ς, and the map's count, with the occurrences as vertices (map #MD2.4.12.24, #MD2.4.12.38), runs at the enlarged amplitudes; C^{w,2}_M and c^{w,2}_M are its values there.
  {#C7.8-4-1-2} A merged occurrence through an old component of the step i − 1 makes the wrap one through old components (#C7.8-4-2).
  {#C7.8-4-1-3} The wraps are not among the interpolated constituents. At the steps i − 1 and i the two runs' wraps, old and young, are held at run A's here, and the t-step of #C7.8-9-4 moves them (#C7.8-9-5).
{#C7.8-4-2} By Cauchy's estimate on the disc of radius 1/(2ρ^E_K) ≥ 2 (#C7.6-6-8), the two runs' wraps born at step i without old components, paired by shape and position, differ by at most 4ρ^E_K times that bound. The wraps through old components are, for each run, at most 2e^{−C_Pk/4} times map #MD2.0.3.34-4's bound, by the disc in z of #C7.6-6-3.
{#C7.8-4-3} So the birth differences at age m total at most (4ρ^E_K + c″x^*_K)A^{w,2}L^me^{−a^{w,2}L^m} + 4e^{−C_Pk/4}A_wL^me^{−a_wL^m}, weighted, the term c″x^*_K from the wraps of the step i − 1 (#C7.8-9-5–#C7.8-9-5-1), with A^{w,2} := 4ℓ_CC^{w,2}_Msup_jρ̂^w_j/L and a^{w,2} := c^{w,2}_Mc^w_N(T_ph/u)L^{j(C)−1}/M.
{#C7.8-5} *The young wraps: carried.* At each later step the runs evaluate their wraps at their aligned backgrounds. This moves a wrap by at most r̄_K times its bound: the large-field note's (V) (its #5.33–#5.37), on the all-small-field pair with the path of §10.4, (9.8) in place of (P′), and the steps i ≥ k − m_W, m^w_K ≤ m_W (#C7.4-7-2).
{#C7.8-5-1} The difference of a carried wrap grows by at most 2L per step: L as the wrap does (map #MD2.0.3.34-4), doubled for a descendant of several parents, since the difference of a product replaces one parent at a time (the large-field note's #5.40).
{#C7.8-6} The young wraps live at most m^w_K steps, and their total weighted mass is at most A_wS_w at every step, S_w := Σ_{m≥1}L^me^{−a_wL^m} ≤ e^{−a_w}(1 + 6/a_w) (#C7.6-7-1). Each step adds at most r̄_KA_wS_w by the carry and one age's birth difference, whose total over the steps is at most (4ρ^E_K + c″x^*_K)A^{w,2}S^{(2)}_w + 4e^{−C_Pk/4}A_wS_w (#C7.8-4-3), with S^{(2)}_w the same sum at a^{w,2}.
{#C7.8-6-1} *Merged groups.* No difference of an old wrap passes to a young one. On the all-small-field pair the only inherited attached members are wraps (#C7.8). By the D2.6 closure 2.1 *Merged groups*, a group with an inherited attached member takes the first inherited species in step order, so a group that contains an old wrap is the wrap of that step or an earlier one, with its bound and the growth L per later step. It is therefore old and counted in #C7.8-3.
{#C7.8-6-2} In total and unweighted the young wraps therefore differ by at most D^w_K := (m^w_K + 1)(2L)^{m^w_K}[r̄_KA_wS_w + (4ρ^E_K + c″x^*_K)A^{w,2}S^{(2)}_w + 4e^{−C_Pk/4}A_wS_w].
{#C7.8-7} D^w_K is summable in K. (m^w_K + 1)(2L)^{m^w_K} ≤ 2m^w_KL^{2m^w_K} is at most a power of log(K + 2), since L^{m^w_K} ≤ max(L, 3Llog(K + 2)/a_w). ρ^E_K times such a power is summable (#C7.6-7-2), e^{−C_Pk/4} is geometric, and r̄_K ≤ C′_eθ̃^k for ε₀ < 2/5 (the large-field note's #5.43).
  {#C7.8-7-1} x^*_K times any power of log(K + 2) is summable (#C7.8-9-8-2).
{#C7.8-8} *The product form.* The words are multilinear in the insertions (the D2.6 closure 5.2 (T0)). Pair the two runs' wraps by shape and position, an absent wrap being 0, and let δ_b be the difference of the pair b. Then changing the wraps changes the dressed loop at the other insertions fixed by at most Π_b(1 + ‖Y_b‖ + δ_b) − Π_b(1 + ‖Y_b‖) ≤ (e^{Σ_bδ_b} − 1)exp(Σ_nν_n).
{#C7.8-8-1} The exponent of the continuum note's (8.1) bounds Σ_nν_n also for one run's dev insertions with the other run's wraps, since its dev and wrap parts are bounds that do not depend on the run (#ND.5.4-2). With Σ_bδ_b ≤ 2τ^w_K + D^w_K and #C7.5-7-1, the wraps change e^{E^A_const}𝒲 by at most x^w_KB_W, x^w_K := e^{2τ^w_K + D^w_K + r^w_Klog B_W} − 1, which is summable in K; the term r^w_Klog B_W is their part through the dev insertions (#C7.8-9-10).

{#C7.8-9} *The wraps in the step gases.* The wrap groups belong to every step's reference gas, with c_𝒢 = Y_𝒢(1, 0) (map #MD2.3.3.2, #MD2.3.3.10-1); only the dev parts vanish at the reference point (map #MD2.3.3.10-3, #MD2.4.12.48-3). So the two runs' wraps also differ inside the occurrences merged at the births of young wraps (#C7.8-4-0) and of dev insertions (#C8.3.3-4-3), inside the per-step terms E°_i, whose activities contain the carried insertions as factors (map #MD2.3.4.45), and inside the final Q_{K′} (#C7.9). #C7.8-9-1 to #C7.8-9-10 bound these parts.
  {#C7.8-9-1} *Per traversal.* At a shared step i let Δ_i := sup_nΣ w(W)max(‖Y^B_W − Y^A_W‖, |c^B_W − c^A_W|) over the pairs of young wraps through the traversal n, paired by shape and position at aligned arguments, an absent wrap being 0. Let τ^{pt}_i be the larger of the two runs' sup_nΣ_{old W∋n}w(W)max(‖Y_W‖, |c_W|), and {#D.Ȳ} Ȳ := max_i(2τ^{pt}_i + Δ_i) over the shared steps, a finite maximum.
  {#C7.8-9-1-1} Let δε̂^w_i := sup_pΣ_{wrap 𝒢 at p}|c^B_𝒢 − c^A_𝒢|e^{s+(ν_r/16)σ}, the position sum of map #MD2.4.12.38-1 over the wrap groups of the step i's gas. The old wraps are not paired, so they enter with |c^B| + |c^A|, and #C7.8-1-4 gives δε̂^w_i ≤ {#D.X_w} X_w := C_posȲ.
  {#C7.8-9-2} *Sum lemma 2.* For a > 0 and L ≥ 2, {#D.T_w} T_w(a) := Σ_{n≥0}(2L)^ne^{−aL^{n+1}} ≤ 16/(e²a²L²(e^{aL/2} − 1)), and T_w decreases in a. Indeed (2L)^n ≤ L^{2(n+1)}/L² and y²e^{−ay/2} ≤ (4/(ea))², so T_w(a) ≤ (16/(e²a²L²))Σ_{m≥1}e^{−aL^m/2}, and L^m ≥ mL gives Σ_{m≥1}e^{−aL^m/2} ≤ 1/(e^{aL/2} − 1).
  {#C7.8-9-3} *A priori bounds.* Let {#D.ρ̂^w_γ} ρ̂^w_γ := sup_{g≤(1+β₀)γ}max(C_S′ρ̂(g), C_S″b(g))pl(g), so ρ̂^w_j ≤ ρ̂^w_γ at every scale (#C8.3.3-2). By #C7.8-1 and #C7.8-1-2 either run's wraps at the step i have per-traversal weighted mass at most Σ_{j≤i}C^w_ML^{i−j}ρ̂^w_je^{−a_wL^{K′+1−j}} ≤ C^w_Mρ̂^w_γT_w(a_w) ≤ {#D.μ₀} μ₀ := C^w_Mρ̂^w_γT_w(a₀), with n := i − j and K′ + 1 − j ≥ n + 1, T_w decreasing, and a_w ≥ a₀ (#CP.22-5-1). So 2τ^{pt}_i + Δ_i ≤ 2μ₀ and X_w ≤ 2μ^{pt}, {#D.μ^{pt}} μ^{pt} := C_posμ₀.
  {#C7.8-9-3-1} The old wraps at any step have per-traversal weighted mass at most τ^{pt}_K := τ^w_K/(4ℓ_C), the tail of #C7.8-3 without the count of traversals, since a scale-j old wrap at the step i ≤ K′ has L^{i−j} ≤ L^{m−1}, m := K′ + 1 − j ≥ m^w_K. So τ^{pt}_i ≤ τ^{pt}_K.
  {#C7.8-9-4} *The t-step.* Put R_w := ν_r/(5184MX_w), R_w := ∞ if X_w = 0. For t ∈ ℂ with |t| ≤ R_w move the wraps linearly, Y^t_W := Y^A_W + t(Y^B_W − Y^A_W) over the aligned pairs, an absent wrap being 0, so c^t_W as well, with the other constituents at run B's. The gases of both runs and of this hybrid have ε̂ ≤ ν_r/(10368M) (#CP.22-5), since each part is within its run's c-version. So ε̂(t) ≤ ν_r/(10368M) + |t|X_w ≤ ν_r/(2592M), the threshold of (5.11), below that of (5.10) (map #MD2.4.12.38-2–#MD2.4.12.38-3).
    {#C7.8-9-4-1} The φ^t(Γ) are therefore analytic in t on the disc, with Σ_{Γ hits W}|φ^t(Γ)|e^{Σs} ≤ 81Mσ(W)ε̂(t) ≤ (ν_r/32)σ(W), and the map's count with the occurrences as vertices runs there with the constants of #C7.8-4-1-1. R_w ≥ 2, since X_w ≤ 2μ^{pt} ≤ ν_r/(10368M) (#CP.22-5). So Cauchy's estimate gives |f(1) − f(0)| ≤ sup_{|t|=R_w}|f|/(R_w − 1) ≤ c″X_w·sup_{|t|=R_w}|f|, {#D.c″} c″ := 10368M/ν_r.
  {#C7.8-9-5} *Births.* A young wrap born at the step i depends on the wraps of the step i − 1 through the occurrences φ_{i−1} (#C7.8-4-0); its members are held at run A's (#C7.8-4). Split run B's minus run A's into the t-step at ς = 1 and the ς-step at t = 0, with the 𝔷-removal of #C7.6-6-3 in the second. At t = 0 the wraps of the step i − 1 are run A's (#C7.8-4-1-3), and the ς-step of #C7.8-4-1–#C7.8-4-2 runs on the disc of radius 1/(2ρ̃), {#D.ρ̃} ρ̃ := ρ^E_{K,0} + 2K_ΔC″c″X_w/(1 − θ_Q).
    {#C7.8-9-5-1} ρ̃ bounds the relative differences of the interpolated constituents (#C7.8-9-7), and ρ̃ ≤ ¼ (#C7.4-7-4-1, #CP.22-5). The t-step gives c″X_w times the bound on its disc, which is map #MD2.0.3.34-4's at the enlarged amplitudes (#C7.8-9-4-1). So per traversal a wrap born at the step i′ has a birth difference, its c-version included, at most (4ρ̃ + c″X_w)C^{w,2}_Mρ̂^w_{i′}e^{−a^{w,2}L^{K′+1−i′}} + 4e^{−C_Pk/4}C^w_Mρ̂^w_{i′}e^{−a_wL^{K′+1−i′}}.
  {#C7.8-9-6} *The recursion.* After birth each young wrap is moved by at most r̄_K times its bound (#C7.8-5), and the difference grows by at most 2L per step (#C7.8-5-1). Sum over the birth steps i′ ≤ i, with n := i − i′ and K′ + 1 − i′ ≥ n + 1, and for the carry over the scales j ≤ i′, with Σ_{i′=j}^{i}(2L)^{i−i′}L^{i′−j} ≤ 2(2L)^{i−j}. This gives Δ_i ≤ (4ρ̃ + c″X_w)C^{w,2}_Mρ̂^w_γT_w(a^{w,2}) + (4e^{−C_Pk/4} + 2r̄_K)C^w_Mρ̂^w_γT_w(a_w), uniformly in i, K, ℓ_C, and m^w_K.
  {#C7.8-9-7} *The dev source.* The dev groups born at the step i + 1 carry occurrences of φ_i, whose clusters can contain wrap groups of the step i, the species of a group coming from its W-vertices (map #MD2.3.3.5, #MD2.0.3.26-1). #C8.3.3-4-3-2 compares them at run A's wraps, and the rest is the t-step at the step i. By #C7.8-9-4-1, Σ_{Γ hits W}|φ^{t=1}_i(Γ) − φ^{t=0}_i(Γ)|e^{Σs} ≤ c″X_w(ν_r/32)σ(W) ≤ (c″X_w/2)·b(W)/2 (map #MD2.4.12.38-4), a mark of the form of map #MD2.4.13.8-4 with c″X_w/2 in place of ε̄^{diff}/ε_*.
    {#C7.8-9-7-1} By map #MD2.4.13.12, with the factor 2 of map #MD2.4.13.15-5, this adds at most s^w := K_ΔC″c″X_w to d^{ins}_{i+1}, relative to C_S′ρ_{i+1}pl_{i+1} (#C8.3.3-4-4). Solved apart (#C8.7.7-4), it adds at most 2s^w/(1 − θ_Q) to r^E_i (#C7.6-6-2-1). Since max(a + b, c, d) ≤ max(a, c, d) + b, the relative differences of the interpolated constituents are at most ρ̃.
  {#C7.8-9-8} *The bootstrap.* Put {#D.Δ̄₀₀} Δ̄₀₀ := 4ρ^E_{K,0}C^{w,2}_Mρ̂^w_γT_w(a^{w,2}) + (4e^{−C_Pk/4} + 2r̄_K)C^w_Mρ̂^w_γT_w(a_w), {#D.G_w} G_w := C_posc″(1 + 8K_ΔC″/(1 − θ_Q))C^{w,2}_Mρ̂^w_γT_w(a^{w,2}), {#D.y^*_K} y^*_K := (2τ^{pt}_K + Δ̄₀₀)/(1 − G_w), and {#D.x^*_K} x^*_K := C_posy^*_K.
    {#C7.8-9-8-1} By #C7.8-9-6 and #C7.8-9-3-1, with 4ρ̃ = 4ρ^E_{K,0} + 8K_ΔC″c″X_w/(1 − θ_Q) and X_w = C_posȲ, every 2τ^{pt}_i + Δ_i is at most 2τ^{pt}_K + Δ̄₀₀ + G_wȲ, so Ȳ ≤ 2τ^{pt}_K + Δ̄₀₀ + G_wȲ. Ȳ is finite and G_w ≤ ½ (#CP.22-5), so Ȳ ≤ y^*_K and X_w ≤ x^*_K. Hence ρ̃ ≤ ρ^E_K (#C7.6-6-4-4), and the Cauchy estimates at ρ^E_K of #C7.8-4-2, #C7.6-6-8, and #C7.9-2-1 hold.
    {#C7.8-9-8-2} x^*_K ≤ 2C_pos(2τ^{pt}_K + Δ̄₀₀), and τ^{pt}_K, ρ^E_{K,0}, e^{−C_Pk/4}, and r̄_K times any power of log(K + 2) are summable (#C7.8-3, #C7.6-7-2, #C7.8-7). So x^*_K is, with any power of log(K + 2).
  {#C7.8-9-9} *The per-step terms.* E°_i sees the wraps of the step i, and #C7.6-6-4 holds them at run A's (#C7.6-6-4-5). Move them by the t-step on the disc |t| ≤ R_E := μ₀/Ȳ (R_E := ∞ if Ȳ = 0, when nothing moves), with the other constituents at run B's; R_E ≥ 2 by Ȳ ≤ y^*_K ≤ μ₀/2 (#C7.4-7-6).
    {#C7.8-9-9-0} At an 𝐑-step E°_i does not depend on t, since its groups' slots hold no insertion (D2.7 15.8-1(2-2-1), 15.4(i)). At a T-step it depends on t only through the wraps' activities c^t_W = Y^t_W(1, 0) (#C7.8-9), linear in t: a group with a wrap member is a wrap (map #MD2.4.11.5-10), and the occurrences φ_{i−1} in the other groups stay run B's.
    {#C7.8-9-9-1} On the disc ε̂(t) ≤ ν_r/(10368M) + R_EX_w = ν_r/(10368M) + μ^{pt} ≤ ν_r/(5184M) (#CP.22-5), so the Kotecký–Preiss condition at a°/2 of map #MD2.4.12.51-4 holds. The root sum Σ_{𝒢∋b}|c^t_𝒢|e^{2a°(𝒢)} of (T′) (map #MD2.3.5.3-1) exceeds its value at t = 0 by at most |t|δε̂^w_i ≤ μ^{pt}: the traversals of a group's arc are among its positions (map #MD2.4.12.38-1), 2a°(𝒢) = (ν/16)σ ≤ s + (ν_r/16)σ since ν_r = ν (map #MD2.4.12.6) and s ≥ 0, and δε̂^w_i ≤ X_w (#C7.8-9-1-1).
    {#C7.8-9-9-1-1} So (T′) and (Z) hold on the disc (map #MD2.3.5.1, #MD2.3.5.3-17) with the root-sum amplitude raised by μ^{pt}, and #C7.6-2's bounds, linear in 𝔞̄ (map #MD2.3.7.1-2, #MD2.3.7.3), hold with 𝔞̄ + μ^{pt}/C_S′ in place of 𝔞̄ (τ̄² depends on the coupling only, map #MD2.3.7.1): at a T-step abs(E°_i(t)) ≤ (ea^T_E)^{−1}A^{TZ}_E(𝔞̄ + μ^{pt}/C_S′)L^{m/2}e^{−a_EL^{m/2}} (#C7.6-2-1), with A^{TZ}_E, a^T_E, and a_E of #C7.6-1.
    {#C7.8-9-9-1-2} Cauchy's estimate, with 1/(R_E − 1) ≤ 2Ȳ/μ₀ and R_EX_w = μ^{pt}, gives |E°_i(1) − E°_i(0)| ≤ 2(ea^T_E)^{−1}A^{TZ}_E(𝔞̄y^*_K/μ₀ + x^*_K/C_S′)L^{m/2}e^{−a_EL^{m/2}}, and Δ^E_K gains 2(ea^T_E)^{−1}A^{TZ}_E(𝔞̄y^*_K/μ₀ + x^*_K/C_S′)S_E (#C7.6-7-0).
    {#C7.8-9-9-2} y^*_K/μ₀ ≤ 2(2τ^{pt}_K + Δ̄₀₀)/μ₀ is summable in K: τ^{pt}_K/μ₀ ≤ 2max(1, 3log(K + 2)/a₀)(K + 2)^{−3}/T_w(a₀), and Δ̄₀₀/μ₀ ≤ 4ρ^E_{K,0}C^{w,2}_M/C^w_M + 4e^{−C_Pk/4} + 2r̄_K, by a_w, a^{w,2} ≥ a₀ (#CP.22-5-1).
  {#C7.8-9-10} *Through the dev insertions.* The source s^w changes the dev insertions at the stopping scale by at most r^w_K := 2K_ΔC″c″x^*_K/(1 − θ_Q) times the bounds of (S-w) relative to which d^{ins} is measured (#C8.7.7-4, #C8.3.3-4-1). These are the dev terms of D(K′)(ii), whose per-traversal sum the exponent of (8.1) bounds (#ND.5.4), so these changes add at most r^w_Klog B_W to Σ_bδ_b in #C7.8-8.

{#C7.9} *The final interaction weights.* Each term of the dressed loop with insertions 𝔅 carries the factor Q_{K′}(𝔅) = exp(−Σ_{Γ hits 𝔅}φ_{K′}(Γ)) of D(K′) (map #MD2.0.3.7), a number given the labels (map #MD2.0.3.64), with Σ_{Γ hits W}|φ_{K′}(Γ)| ≤ θ(W) ≤ νσ(W)/16 (map #MD2.0.3.7, #MD2.0.3.50). The φ_{K′}(Γ) are the cluster activities of the final step's reference gas, which each run computes from its own groups; the comparisons of #C7.4-2 do not contain them.
{#C7.9-1} *Mean value.* For a := Σ_{Γ hits 𝔅}φ^A_{K′}(Γ) and b := Σ_{Γ hits 𝔅}φ^B_{K′}(Γ), |a + t(b − a)| ≤ Σ_{W∈𝔅}θ(W) for 0 ≤ t ≤ 1, so |e^{−b} − e^{−a}| ≤ |b − a|∏_{W∈𝔅}e^{θ(W)}, with no condition on |b − a|.
{#C7.9-2} *The difference of the activities.* The final step is the shared index m = 1, a young 𝐑-step (#C7.4-7-3), with r^E ≤ r̄^E_K (#C7.6-7). Remove its old components with 𝔷 (#C7.6-6-3) and interpolate its constituents with ς (#C7.6-6-4), and those of the step before with the same ς and 𝔷 (#C7.8-4-1-1).
  {#C7.9-2-0} The reference activities are then analytic and at most twice their bounds, and the gas's Kotecký–Preiss condition holds at twice the activities for γ small (#C7.8-4-1-1), so Σ_{Γ hits W}|φ^ς_{K′}(Γ)| ≤ 2θ(W) on the disc by FV Lemma 5.6, (5.17), the weight a(W) of map #MD2.4.12.38-1 being linear in the activities (map #MD2.4.12.38-3).
  {#C7.9-2-1} By Cauchy's estimate on the disc of radius 1/(2ρ^E_K) ≥ 2 (#C7.4-7-4), the part without old components differs by at most 4ρ^E_K·2θ(W) summed over the Γ hitting W. The part through old components is, for each run, at most 2e^{−C_Pk/4}θ(W) by the disc in 𝔷. So Σ_{Γ hits W}|φ^{B,A}_{K′}(Γ) − φ^A_{K′}(Γ)| ≤ q^Q_Kθ(W), {#D.q^Q_K} q^Q_K := 8ρ^E_K + 4e^{−C_Pk/4}, with φ^{B,A}_{K′} the clusters of run B's gas with run A's wraps (#C7.6-6-4-5).
  {#C7.9-2-2} The t-step of #C7.8-9-4 at the final step moves the wraps to run B's: Σ_{Γ hits W}|φ^B_{K′}(Γ) − φ^{B,A}_{K′}(Γ)| ≤ c″X_w(ν_r/32)σ(W) ≤ (c″x^*_K/32)ν_rσ(W) (#C7.8-9-4-1, #C7.8-9-8-1).
{#C7.9-3} *Per member.* With θ(W) ≤ νσ(W)/16, ν_r = ν (map #MD2.4.12.6), and σ ≤ e^{ν_rσ}/(eν_r), (q^Q_Kθ(W) + (c″x^*_K/32)ν_rσ(W))e^{θ(W)}‖Y_W‖ ≤ (q^Q_K/(16e) + c″x^*_K/(32e))e^{ν_rσ(W)}e^{θ(W)}‖Y_W‖ ≤ q̄^Q_Kw̄(W), {#D.q̄^Q_K} q̄^Q_K := q^Q_K/(16e) + c″x^*_K/(32e) (#C7.9-2-1, #C7.9-2-2). Here w̄(W) is W's summand in the per-traversal clause that bounds it, which contains e^{θ(W) + ν_rσ(W)}‖Y_W‖: (ii-w) for the dev insertions (map #MD2.4.12.4-4–#MD2.4.12.5) and w(W)‖Y_W‖ of #C7.8-1 for the wraps.
  {#C7.9-3-1} So |ΔQ_{K′}(𝔅)|∏_{b∈𝔅}‖Y_b‖ ≤ q̄^Q_KΣ_{W∈𝔅}∏_{b∈𝔅}w̄(b), the other members keeping e^{θ(b)}‖Y_b‖ ≤ w̄(b). Summed over 𝔅, Σ_𝔅Σ_{W∈𝔅}∏_{b∈𝔅}w̄(b) ≤ Σ_Ww̄(W)·∏_b(1 + w̄(b)) ≤ (Σ_nν̄_n)exp(Σ_nν̄_n), ν̄_n := Σ_{W∋n}w̄(W), each insertion counted at its first traversal (#C7.5-7). The continuum note bounds the dev part of ν_n by the right side of (ii-w) (its #ND.5.4), so the same bound holds for the dev part of ν̄_n.
  {#C7.9-3-2} The wrap part of ν̄_n is #C7.8-1's at i = K′: Σ_{j≤K′}C^w_ML^{K′−j}ρ̂^w_je^{−c^w_MN^{(j)}_min/M} ≤ C^w_Msup_jρ̂^w_j(2 + 6/b^{wr})e^{−b^{wr}}, {#D.b^{wr}} b^{wr} := c^w_Mc^w_N(T_ph/u)L^{j(C)}/M, by the sum lemma #C7.6-7-1 and N^{(j)}_min ≥ c^w_N(T_ph/u)L^{K′−j+j(C)}. So e^{B_E}exp(Σ_nν̄_n) ≤ B̄_W, {#D.B̄_W} B̄_W := B_W·exp(4ℓ_CC^w_Msup_jρ̂^w_j(2 + 6/b^{wr})e^{−b^{wr}}), with B_W ≥ e^{B_E}exp(dev part) (#C7.4-4-1). B̄_W is bounded uniformly in K, since ρ̂^w_j ≤ ρ̂^w_γ.
{#C7.9-4} With run A's constant, e^{B_E}exp(Σ_nν̄_n) ≤ B̄_W and Σ_nν̄_n ≤ log B̄_W (#C7.9-3-2, #C7.5-7-1), so the final interaction weights change e^{E^A_const}𝒲 by at most x^Q_KB_W, {#D.x^Q_K} x^Q_K := q̄^Q_Klog(B̄_W)B̄_W/B_W. It is summable in K: ρ^E_K and x^*_K are (#C7.6-7-2, #C7.6-7-2-1), e^{−C_Pk/4} is geometric, and B̄_W/B_W and B̄_W are bounded uniformly in K (#C7.9-3-2, the continuum note's #ND.8.1).

## 8. The Generated Difference of One Fluctuation Integral {#CS8}

### 8.1 The Interpolation Identity {#CS8.1}

{#C8.1.1} At the shared scale k the two runs apply the same step CRE (3.1)–(3.15) to inputs on the same lattice T_{εL^{k−1}} with the same block data, and the fluctuation field A_k of (3.11) is the same variable in both runs; the characteristic functions χ^{(k)} of (3.16) cut the fluctuation at Bałaban's δ_k = (A₁/A₀)ε_k, written ϑ_k in this note since δ_k is the coupling difference of §1, a function of the run's coupling at the shared scale, so they differ on a threshold shell, treated in §8.2(b).
{#C8.1.1-1} The background U_{k+1}(V) of (3.10) is the fine-lattice minimiser, on T_ε in run A and on T_{ε/L} in run B (§9.7 bounds their distance), and the Gaussian form −½⟨A_k, C*Δ^{(k)}CA_k⟩ is RG I (1.5) built from the fine-lattice propagators in that background, so it differs between the runs; §10 bounds the difference δΔ^{(k)} := Δ^{(k+1)}_B − Δ^{(k)}_A by r_k times the form's own bound ((10.6)).
{#C8.1.1-2} The runs differ further in the interaction 𝐏^{(k)} of (3.15): the curly bracket collects, for every frozen term, its fluctuation part 𝐄^{(j)}(U_k(exp i[g_kCA_k − hD̃(g_kCA_k)]V^{(k)})) − 𝐄^{(j)}(U_{k+1}), and the same for 𝐑 and 𝐁, and in the fluctuation parts of the fine actions g_k^{−2}A_ε(U^A_k(…)) and g_k^{−2}A_{ε/L}(U^B_{k+1}(…)), whose difference at the fluctuation-dependent configuration is the classical depth of §9 at that configuration (the same (9.1)–(9.10) with V replaced by the fluctuated block field, which is regular by (3.14)).
{#C8.1.1-3} Put 𝐏_t := 𝐏^A + t(𝐏^B − 𝐏^A) and Δ_t := Δ^{(k)}_A + tδΔ^{(k)}, t ∈ [0, 1], Z_t := ∫dA_k χ^{A,(k)} exp[−½⟨A, C*Δ_tCA⟩ + 𝐏_t], with run A's cutoff in both; run B's own integral is Z_1 plus the shell term of §8.2(b).
{#C8.1.1-4} Then, exactly,

{#C8.1.2} (8.1) log Z_1 − log Z_0 = ∫₀¹ [⟨𝐏^B − 𝐏^A⟩_t − ½⟨⟨A, C*δΔ^{(k)}CA⟩⟩_t] dt,

{#C8.1.3} the left side being the whole logarithm of the step's output (𝐄_0^{(k+1)} of (3.37) together with the R″, B, and constant parts of (3.26), (3.38)); the second term is the expectation of a quadratic insertion whose kernel is bounded by (10.6), of the class the marked expansion of §8.5 treats, and

{#C8.1.4} ⟨·⟩_t the expectation of the fluctuation measure with interaction 𝐏_t, which for every t is a measure of the kind Bałaban integrates, since 𝐏_t is a convex combination of two admissible interactions and the inductive bounds (RG I (1.18), CRE (2.31), (2.42)) define convex sets.
{#C8.1.4-1} The localised terms of (3.47) for the difference are the localised terms of the right side of (8.1): the marked expansion with one marked activity, the piece of 𝐏^B − 𝐏^A on Y. The marked-cluster bound (G′) of §8.5 is the statement that this marked expansion is bounded by the marked activity times C_KP, with Bałaban's decay in d_{k+1}(X), and by the marked activity's Gaussian mean where it is connected to no activity of 𝐏_t.

### 8.2 The Interaction Difference {#CS8.2}

{#C8.2.1} Δ𝐏 := 𝐏^B − 𝐏^A has four parts, and the step's output differs further by the threshold shell.
{#C8.2.1-1} (a) *The frozen differences' fluctuation parts.* For each shared generation j ≤ k, [irr(Δ_j)(U_k(…A…)) − irr(Δ_j)(U_{k+1})] + Δβ_j[A(h_z, U_k(…A…)) − A(h_z, U_{k+1})], and the same for the frozen 𝐑-differences ΔR_j of §8.4 (𝐑_k′ of (3.26) is included into 𝐄_k, and 𝐑_k″ enters by the s-interpolation of (3.26), p.271 l.3–30, whose measure is of the kind §8.5 expands).
{#C8.2.1-2} The frozen boundary-term differences enter the same way, as marked activities of the t-interpolation of (3.26) and of its measure (3.27), and their output goes into 𝐁^{(k+1)} only (p.271 l.29–31, p.279 l.16); they are carried by `WILSON_IT1_LARGE_FIELD_DEPTH_2026_10_27.md` §4(e) and enter (8.3) only through §8.6.
{#C8.2.1-3} Let k_s := K − j(C) denote the stopping scale in the thresholds of §§8.2–8.7, where k is the generic step.
{#C8.2.1-4} At the steps > k_s/8 the norms d_j, D, S, and those of the boundary terms are taken over the terms that are not deep in the sense of that section: a non-deep output has non-deep inputs only, and the deep terms are bounded in §8.6 and §6.2 (that section's "Deep terms").
{#C8.2.1-5} (b) *The coupling and the cutoff.* The coupling enters 𝐏 through g_kCA_k in the backgrounds and through the coefficients g_k^{n−2} of the action's terms of order n ≥ 3 in the fluctuation (the quadratic part is the g-free Gaussian form of (3.15)); the two runs' values g^A_k and g^B_{k+1} differ relatively by τ_k := g^B_{k+1}/g^A_k − 1, |τ_k| ≤ g_k²|δ_k|, and the marginal parts Σ_jΔβ_jA(h_z, ·) of (a) are absorbed in δ_k by (2.24) and §3.
{#C8.2.1-6} The cutoff (3.16) cuts the rescaled Gaussian variable A_k of (3.15) on the bonds (□′^{∼2})^{(k)*} at r^χ_k := ϑ_k/g_k = (A₁/A₀)p₀(ĝ_k)ĝ_k/g_k, so ρ_γ^{−1/2}(A₁/A₀)p₀(ĝ_k) ≤ r^χ_k ≤ (A₁/A₀)p₀(ĝ_k) (#CP.14). Here A_k′ = g_kA_k is the scaling of p.267 l.42, and A_k has the covariance C^{(k)} = (C*Δ^{(k)}C)^{−1} (RG I p.268 l.3, the form of (1.4)–(1.5)), bounded by its random-walk expansion in [13] (RG II p.13 l.19, [13] = PBG).
{#C8.2.1-6-0} ϑ_k = ĝ_k(A₁/A₀)p₀(ĝ_k) is Bałaban's δ_k = g_k(A₁/A₀)p₀(g_k) (p.265 l.39) at ĝ_k (#CP.13), with p₀(g) = A₀(log g^{−2})^{p₀} and ε = gp₀(g) (p.246 l.14). So ϑ_k = (A₁/A₀)ε_k is a threshold in configuration units, that of the configuration test (3.3); this corrects the print of (3.16) (#C8.2.1-7–#C8.2.1-13).
{#C8.2.1-7} (3.16) prints the threshold as δ_k (p.268 l.15–21).
{#C8.2.1-8} Its step-0 counterpart (1.18) (p.250 l.28–36) prints g₀^{−1}δ₀ for the same scaled variable, which enters the configuration as exp ig₀A in (1.19) (p.250 l.40–43), after the scaling A = g₀A′ (p.249 l.19).
{#C8.2.1-9} The argument after (1.19) (p.250 l.44–50), that the configuration test is then implied, is the one that p.268 l.28–30 repeats for (3.3) with (3.17)–(3.19) ("much smaller than δ_k", ≤ 44d²B₃²(1+β₀)e^{−R_k}ε_k), and p.267 l.40–44 states that the step's operations are those of step 0.
{#C8.2.1-10} RG II cuts the scaled fluctuation in the same way, at ε₁/g_k ((2.3), p.12 l.15–21), the radius of its domain (1.34) (p.9), and LFR II cuts its scaled B at g_k^{−1}δ′_k (p.360 l.42, the χ′ of (1.18) and (1.70); p.383 l.21, g_j^{−1}δ′_j = A₁p₁(g_j) as printed, A₁p₁(ĝ_j)ĝ_j/g_j in the tube, #CP.13).
{#C8.2.1-11} So the δ_k of (3.16) is the step-0 threshold g_k^{−1}δ_k with the factor g_k^{−1} dropped.
{#C8.2.1-12} At the literal δ_k the scaled variable of covariance O(1) would be confined to a radius that tends to 0, and the small-field set would not be the typical one.
{#C8.2.1-13} Bałaban's own large-field threshold is gp₀(g) in configuration units, with the factor exp(−½p₀²) (p.244 l.20–26), which the literal δ_k would lose.
{#C8.2.1-14} C fills the gauge-fixed bonds b₀(c) by a local linear map of the variables on the bonds of B(c_−) ∪ B(c_+) (CRE p.249 l.20–24; RG I p.268 l.2–3, with b₀(c) at p.267 l.19–20), so sup_b|g_kCA_k(b)| ≤ ‖C‖_∞ϑ_k on the cutoff ball, with ‖C‖_∞ a constant of L and d.
{#C8.2.1-15} The two runs share ϑ_k, so r^{χ,B}_k/r^{χ,A}_k = g^A_k/g^B_{k+1}, and (g^A_k/g^B_{k+1})² = 1 + δ_k(g^A_k)² gives a relative difference ≤ |δ_k|g_k². So χ^{B,(k)} − χ^{A,(k)} is supported on the shell between the two radii in the sup over a cube's bonds, a set of Gaussian measure ≤ #bonds(□)·C|δ_k|g_k²r^χ_ke^{−(r^χ_k)²/(2C_cov)} ≤ C|δ_k|g_k²e^{−c(A₁/A₀)²p₀(ĝ_k)²}, since (r^χ_k)² ≥ ½(A₁/A₀)²p₀(ĝ_k)² for γ small (#C8.2.1-6).
{#C8.2.1-15-1} The shell's contribution to the step's output per scale-(k+1) point is at most this measure times e^{O(1)} (the activities on the cube are bounded by a_k on the cutoff ball, #C5.12-8): a term ≤ C|δ_k|g_k²e^{−cp₀(ĝ_k)²}, absorbed in the coupling term of (8.3).
{#C8.2.1-16} The device is V4's lem:c5-5R-2(b), the marked difference of two cutoffs paid by the large-field reserve.
{#C8.2.1-17} (c) *The 𝐑-differences' fluctuation parts,* in (a) and §8.4.
{#C8.2.1-18} (d) *The extra generation,* run B's generation-1 terms, which run A lacks: an input difference d_1 ≤ E₀ + R₁g_1^{κ₀} ≤ 2E₀ per scale-1 point at the shared scale 1, carried by (8.3) like every other.

{#C8.2.2} Three facts bound the part (a) of #C8.2.1, the frozen differences' fluctuation parts; they are V4's three mechanisms (α)–(γ) of sec:c5-5R and its Lemmas lem:c5-5R-1(b) and lem:c5-5R-2(a), (c), restated for Bałaban's step.
{#C8.2.2-1} The norm throughout is the class norm of RΔ: d_j is the smallest number with |Δ_j(X)| ≤ d_jE₀exp(−κd_j(X)) on the evaluation set ℰ_j(X; r) of the norm class 𝒫_j(X; r) of §5 (*Complex domain.*), r_{i,j} = α_{i,j}/(8B₃) with α_{i,j} the radii of the inductive complex class of CRE (2.28) (p.259 l.40–50).
{#C8.2.2-2} C₀ and C₁ are at least λ_Q (#C5.12) times Bałaban's lower bounds, so that his statements and inclusions hold at the reduced thresholds (`WILSON_IT1_LARGE_FIELD_DEPTH_2026_10_27.md` §4(d), *The room at complex points.*, *Bałaban's Statements at the Reduced Thresholds*).
{#C8.2.2-3} RΔ^c is run at the radii r (§5), and the radii α₂ and α₃ and the margin m_k below are those of that run.
{#C8.2.2-4} The real backgrounds of the support lie in the class 𝒞_k of §5, its condition (a) containing the lift condition through 𝒫_j's lift half, with its current (*The lift condition*).
{#C8.2.2-5} This is the hypothesis of RΔ (§5) and the quantity the step's output is measured in: the output difference is analytic on the class of the next scale with the better decay (1+4β)κ (p.262 l.26–30) and satisfies the inductive assumption (CRE p.279 l.23–24), so d_{k+1} is defined with the same E₀.
{#C8.2.2-6} First, the age factor: RΔ^c (§5) applies at the fluctuation-dependent configuration through its composites over 𝒮_z (CRE p.279 l.43–44, "The field U_k may depend on the fluctuation field, as in the exponential in (3.15)"; p.280 l.15–17).
{#C8.2.2-7} The configuration of (3.15) is U_k(V′V^{(k)}) with V′ := exp iB′_A, B′_A := g_kCA − hD̃(g_kCA), and V^{(k)} = M^k(U_{k+1}) ((I.2.3)).
{#C8.2.2-8} Bałaban writes U_k(V′V^{(k)}) = U′_k(V′)U_{k+1} and transforms U′_k(V′) by the axial gauge and the gauge u_k into exp iη𝐇_k(B′), "regular and of the same order as B′" (RG I p.265 l.33–41), and he expands the action at exp iη𝐇_k(B′)U_{k+1} by its gauge invariance (p.266 l.18–21).
{#C8.2.2-9} The old terms are analytic on RG I's spaces U^c_j(X, α_{0,j}, α_{1,j}) (p.259 l.41–42), which are unions of orbits of the G^c-valued gauge transformations (I.1.10) (RG I p.262 l.4–14), and invariant under them (p.259 (iii)); the invariance under G-valued gauges printed at p.261 l.42–43 concerns the boundary terms' spaces Ũ^c_j.
{#C8.2.2-10} Here only the G-invariance is used, so at real A they take the same values at U_k(V′V^{(k)}) and at exp iη𝐀_AU_{k+1}, 𝐀_A := 𝐇_k(B′_A), which is analytic in A on the ball below.
{#C8.2.2-11} The term at exp iη𝐀_AU_{k+1} is therefore the analytic extension in A of the integrand of (3.15), the integration being over real A, and no value at U_k(V′V^{(k)}) at complex A is used.
{#C8.2.2-12} The terms on the near domains read exp iη𝐀_AU_{k+1} through RG I's composite U_j(□₀, M^·(·)) ((I.3.28), p.276 l.1–9).
{#C8.2.2-13} The output is a function of the background on the class, and d_{k+1} is taken on ℰ_{k+1}(X; r).
{#C8.2.2-14} The output difference is G^c-invariant, run A's output by CRE's (iii) at the step k + 1 and G by #C9.8.18-5.
{#C8.2.2-15} So d_{k+1} is the supremum over the literal points of ℰ_{k+1}(X; r) (#C5.8), and the steps below are run at a literal point 𝐔.
{#C8.2.2-16} The output's domain X lies in Λ_{k+1} (CRE (2.1)), where the constraints of the kinds have the scales ≥ k + 1 (#C5.8), and it contains □₀ (below).
{#C8.2.2-17} So □₀ meets no layer finer than k + 1, and the finer-layer case of 𝒮_z does not occur at these backgrounds.
{#C8.2.2-18} Bałaban continues the output to a complex background by putting the local minimiser 𝐔̂_z := U_{k+1}(□₀, M^·(𝐔)), extended as equal to 𝐔 outside □₀, in place of U_{k+1} in 𝐇_k and in the averages (RG I p.275 l.2–7, (3.24)–(3.25); CRE p.280 l.14–20), so the operators of 𝐇_k are taken at 𝐔̂_z, extended as 𝐔 outside □₀ (RG I p.275 l.3–6, "in order to get better properties with respect to gauge transformations", in place of 𝐔 of p.273 l.2–3), where "all necessary theorems are valid" (p.275 l.6–7, Bałaban's statement).
{#C8.2.2-19} The term of Y₀ depends on 𝐔 on Y₀ ∪ □₀ only (RG II p.5 l.2–3), so □₀ lies in the output's domain X. So at 𝐔 the near part of the frozen term of the point z is F^{nr}_j(A) := irr_□(Δ_j)(c(𝐔̂_z, 𝐀_A)), 𝐀_A := 𝐇_k(B′_A) at 𝐔̂_z, and at real minimisers 𝐔̂_z = U_{k+1}. 𝐔̂_z is a point of 𝒮_z: it is the local minimiser of its own data, since M^·(𝐔̂_z) = M^·(𝐔) on the constrained bonds (#C5.13).
{#C8.2.2-20} A configuration 𝐔₀ = 𝐔̂_z^{h^{−1}} of its orbit, with ‖Ad(h)‖ ≤ e^{2β_I}, satisfies (b) at radii at most r⁺ (#C5.11).
{#C8.2.2-21} On the near domains 𝐔̂_z lies in the orbit of a literal point (R2), which is (a) there (#C5.10).
{#C8.2.2-22} At the points (R1) and (R2), 𝐔 = W^{w^{−1}} on X^∼ with W of the kind, and W = U_{k+1}(□₀, M^·(W)) on □₀: on □₀ ⊂ X ⊂ □′^{∼4} the constraints of W have scales at least that of the layer of z (RG I p.273 l.42–44, □̃⁴ ⊂ □_{k+1}; CRE p.280 l.15–17 for (R1)), the data of a scale determine those of the coarser ones (M^{n+1} = M∘M^n), so every variation that preserves the data of U_{k+1}(□₀, ·) preserves those of W, W is critical for the problem of U_{k+1}(□₀, ·), and the identity is that of (I.3.18) (RG I p.273 l.44–46).
{#C8.2.2-23} So 𝐔 lies in 𝒮_z, and by #C5.26 𝐔̂_z = 𝐔^{g′} on □₀ with ‖Ad(g′)‖ ≤ e^{β_I}.
{#C8.2.2-24} Then 𝐔₀ = 𝐔, a literal point at the radii r⁺, and h = g′.
{#C8.2.2-25} The plaquettes and the current of 𝐔̂_z are at most e^{β_I} times those of 𝐔.
{#C8.2.2-26} Its A′ and cube entries are not used, since (b) is imposed on 𝐔₀.
{#C8.2.2-27} At the points (N), 𝐔̂_z is the local minimiser of the data of exp iξ𝐀.
{#C8.2.2-28} By Proposition 9 [15] at V₀ = 1 (#C5.8), its orbit contains 𝐔₀ := exp iη𝓗, with real part 1 and A′ = 𝓗.
{#C8.2.2-29} Here |𝓗|, |∇𝓗|, the plaquettes, and the current are at most 2max(B₃, B₅)O(1)α_{2,k+1} ≤ r_{0,k+1}/(8C₁₃C_{Q*}) for c₂ ≤ c_N.
{#C8.2.2-30} The gauge h is that of the axial representation, given at the base 1 by CMP98 (106) as in the large-field note's #4.517-0–#4.517-2, with these bounds of 𝓗 for ε₂, so |log h| ≤ 32d times them and ‖Ad(h)‖ ≤ exp(O(1)dB₅c₂α_{0,k+1}) ≤ e^{β_I}.
{#C8.2.2-31} At the points (R3), 𝐔 = exp iη𝐀′𝐔′ with 𝐔′ a literal point (R1) or (R2) of a top index p > k+1, and 𝐀′ and its current increment are at most a′α_{2,k+1} and C₁₃a′α_{2,k+1}, a′ ≤ 0.8. 𝐔̂_z is the local minimiser of the data of 𝐔, which differ from those of 𝐔′ by at most O(1)a′α_{2,k+1}, and U_{k+1}(□₀, M^·(𝐔′)) = 𝐔′^{g′} with ‖Ad(g′)‖ ≤ e^{β_I} (above).
{#C8.2.2-32} So by Proposition 9 [15] and Cauchy's estimate in the data (#C5.8), the orbit of 𝐔̂_z contains exp iη𝓗𝐔′^{g′}, and with it 𝐔₀ := exp iη𝓗^{g′}𝐔′, 𝓗^{g′} := Ad(g′^{−1})𝓗 pointwise.
{#C8.2.2-33} Here |𝓗|, |∇𝓗|, and the moves of the plaquettes and the current are at most 4max(B₃, B₅)O(1)a′c₂α_{0,k+1} ≤ ¼r_{0,k+1}/C_{Q*} for c₂ ≤ c_N.
{#C8.2.2-34} The gauge h is g′ times that of the axial representation, so ‖Ad(h)‖ ≤ e^{2β_I} as at (N). 𝐔₀ has the real part of 𝐔′, so its cube condition is that of 𝐔′.
{#C8.2.2-35} Its quantities are those of 𝐔′, at most (9/8)·0.66 < 0.745 of the thresholds of the scale k + 1 (#C5.8, #C5.27), moved by at most e^{β_I}·¼ < 0.26 of them.
{#C8.2.2-36} That is at most 1.01 ≤ 9/8, which is (b) at radii at most r⁺.
{#C8.2.2-37} In each case the lift of 𝐔̂_z satisfies the lift half of the class condition (a) by #C5.62–#C5.63, at the complex data V′V₀ of its local problem, V₀ real.
{#C8.2.2-38} So F^{nr}_j(A) is the term at a composite over 𝒮_z of §5 (*The composites over 𝒮_z.*), read at 𝐔₀ with the field 𝐀_A^h.
{#C8.2.2-39} The entries of 𝐀_A^h, covariant at 𝐔₀, are at most e^{2β_I} times those of 𝐀_A, inside the margin below. 𝐀_A is the fluctuation field 𝐇_k(B′) of the configuration at which RG I expands the action and evaluates the old terms, whose decoupled form (tζ̃_□ + t_□ζ_□)𝐇_k(B′) Bałaban places in (I.3.31) "for ε₁ sufficiently small" (RG I p.276 l.42; RG II p.7 l.3–11).
{#C8.2.2-40} In CRE's layer form, |𝐀_A|, |∇𝐀_A|, ‖𝐀_A‖_{1,β}, |P₁𝐀_A|, and |Δ𝐀_A| (the last two in the normalisation of (I.3.14)) are at most C_flsup_b|B′_A(b)| in the L^{−k}-scale, covariant at 𝐔̂_z (p.275 l.6–7), and so are those of 𝐀^f_A, covariant at 𝐔, with C_fl := 4B_Te^{2·6^dκ₁}: RG II bounds 𝐇_k(s(Y₀), B′) by 4B₀e^{16κ₁}|B′| (p.6 l.41), "and the same for all admissible norms" ((1.21), p.7 l.3–8, which restates the bound as 4B₀C₁e^{16κ₁}g_k|B| through |B′| ≤ C₁g_k|B|, p.6 l.54), if e^{32κ₁}ε₁ is smaller than an absolute constant.
{#C8.2.2-41} These norms are those of Theorems 3.1–3.10 [13] (p.5 l.16), among them the second-order entry Δ_UG′ of PBG (3.42) (the large-field note's #4.235), and P₁ is a bounded local average. Its products with tζ̃_□ and ζ_□ have the norms of (I.3.31) within the same bound (p.7 l.8–10), read with B_T ≥ B₀ and 2·6^d ≥ 16 as in LFR II (`WILSON_IT1_LARGE_FIELD_DEPTH_2026_10_27.md` #4.435, #4.447; the walk-factor note's #W8.22).
{#C8.2.2-42} The margin is m_k := c₂r_{0,k}/(8C_flC₁₃C_{Q*}), with C₁₃ ≥ 1 the O(1) of the moves of the substitution (I.3.13) (#C5.36), the lower-order terms of the true current (below) included.
{#C8.2.2-43} On the ball sup_b|g_kCA(b)| ≤ m_k, sup_b|B′_A(b)| ≤ 2m_k for γ small, since hD̃ is of second order, so 𝐀_A satisfies (I.3.31) with c₂r_{0,k}/(4C₁₃C_{Q*}) in place of α₂, below the run's α₂ = c₂r_{0,k} at the radii r (elsewhere in this paragraph α_{2,n} is Bałaban's c₂α_{0,n}, as in (N) and (R3), #C5.8).
{#C8.2.2-44} The far domains X ⊄ □̃² of z enter through Bałaban's simpler representation 𝐄^{(j)}(X, exp iη𝐀^f_A𝐔, z), with the background replaced by the complex variable 𝐔 (CRE p.280 l.10–12), so 𝐀^f_A := 𝐇_k(B′_A) with its operators at 𝐔 (RG I's rule for the functions 𝐇_j, 𝐇_k: "we replace the configurations U_{k+1}, J_{k+1} occurring in operators there by the configurations 𝐔, 𝐉", p.273 l.2–4; the near part takes them at 𝐔̂_z instead, "in a slightly different way", RG I p.275 l.3–6), which has the bounds of 𝐀_A at the literal point 𝐔.
{#C8.2.2-45} F_j is taken with them: F_j(A) := F^{nr}_j(A) + Σ_{X ⊄ □̃²}Δ_j(X, exp iη𝐀^f_A𝐔, z), the far sum being ≤ O(1)d_jE₀(L^{j−k})⁵ by (3.48) (p.280 l.2–8) where exp iη𝐀^f_A𝐔 lies in ℰ_j(X; r) of each far X, and it does at each kind of 𝐔.
{#C8.2.2-46} The far X lies in the output's domain (RG II p.5 l.2–3), so its X^∼, whose layer has the width M₁L^j ≤ M₁L^{k+1}, lies in that of the output.
{#C8.2.2-47} In the L^{−j}-scale, |𝐀| and |∇𝐀| of a field of the scale n ≥ j are at most L^{j−n} and L^{2(j−n)} times their values in the L^{−n}-scale (the dimensionless entries carrying (L^nη)^{1+m} for m derivatives, as CRE p.280 l.19–20 reads L^nηA in the L^{−n}-scale), and a current of the scale n is at most L^{3(j−n)} times itself at the scale j ((I.3.12)).
{#C8.2.2-48} With α_{2,n} ≤ (1+β₀)²(n−j)^{1/2}α_{2,j} (CRE (2.6), p.255 l.41–60) and (1+β₀)²p^{1/2}L^{−p} < 0.66 for p ≥ 1 (#C5.27), a field of the scale n > j at most aα_{2,n}, with a current increment at most C₁₃aα_{2,n}, is at most 0.66aα_{2,j}, with an increment at most 0.66C₁₃aα_{2,j}, at the scale j. 𝐀^f_A is at most α_{2,k}/(32B₃C₁₃C_{Q*}) ≤ α_{2,k}/32 at the scale k (B₃, C_{Q*} ≥ 1 being upper-bound constants, C₁₃ ≥ 1), so at most α_{2,j}/32 at the scale j.
{#C8.2.2-49} Its current increment, Δ_𝐔𝐀^f_A − P₁𝐀^f_A + 𝐅₁(𝐔, 𝐀^f_A) of (I.3.13), is at most C₁₃ times the entries of (I.3.14) of 𝐀^f_A at its own scale k, so at most C₁₃α_{2,k}/32, and at most C₁₃α_{2,j}/32 at the scale j.
{#C8.2.2-50} Here P₁ is read only at the field's own scale. 𝐀^f_A = 𝐇_k(B′_A) satisfies the Landau condition RD*𝐇_k = 0 of VAR (21) at its background (RG I p.272 l.20–22), so D*D𝐀^f_A = Δ𝐀^f_A − P₁𝐀^f_A + lower-order terms, and the true current (I.3.11) moves by the same increment up to those terms, which C₁₃ includes.
{#C8.2.2-51} At (R1) and (R2) the configuration is a point (R3) of the scale j with 𝐔′ = 𝐔, a literal point of a top index ≥ k+1 > j, and a = 1/32, the entries of 𝐀^f_A being covariant at 𝐔.
{#C8.2.2-52} At (R3), 𝐔 = exp iη𝐀′𝐔′ with 𝐀′ at most a′α_{2,k+1}, a′ ≤ 0.8, and 𝐔′ of a top index p > k+1, and exp iη𝐀^f_A exp iη𝐀′ = exp iη𝐀″ bond by bond. |𝐀″| and |∇𝐀″|, covariant at 𝐔′, are at most (1 + O(α_{0,j}))(0.66a′ + 1/32)α_{2,j} ≤ 0.8α_{2,j} at the scale j: the commutator terms of the product, and the change of the covariant derivative from 𝐔 to 𝐔′, carry a factor of the size of the fields.
{#C8.2.2-53} The current increments add, the increment of 𝐀′ at 𝐔′ and that of 𝐀^f_A at 𝐔, to at most C₁₃(1 + O(α_{0,j}))(0.66a′ + 1/32)α_{2,j}.
{#C8.2.2-54} So it is a point (R3) of the scale j with the same 𝐔′.
{#C8.2.2-55} At (N) it is a point (R3) of the scale j with (𝐔′, 𝐉′) = (1, 0), the minimiser at the data 1, a literal point (R1) of every top index, and with a ≤ (1 + O(α_{0,j}))(0.66 + 1/32) ≤ 0.8: the field of (N) has |𝐀|, |∇𝐀| < α_{2,k+1} and the current increment 𝐅(𝐀) at most C₁₃α_{2,k+1}.
{#C8.2.2-56} So the far evaluation maps ℰ_{k+1} into ℰ_j with no loss: the background 𝐔′ keeps its own scale and is read with the factor 0.66 of #C5.27, and the fields and current increments of the successive steps add with the factor 0.66 per gap of scales, since a ↦ (1 + O(α_{0,j}))(0.66a + 1/32) maps [0, 0.8] into itself.
{#C8.2.2-57} The composites are Lemma 4's outputs at the scale j from the input 𝐔̂_z of the scale n = k + 1, RG I's factor L^{j−1}η being L^{j−n} at η = L^{−k} (RG I p.279 l.28).
{#C8.2.2-58} So the factor of (5.1c𝐀) is L^{−(4+β′)(k+1−j)} ≤ L^{−(4+β′)(k−j)}, and the exponent k − j below is the weaker one.
{#C8.2.2-59} Lemma 4 is run at 𝐔₀, which satisfies (b) at radii at most r⁺, so its outputs, the composites among them, lie in ℰ_j(X; r) by *The outputs in the norm class.* (#C5.28), where d_j applies.
{#C8.2.2-60} So for j < k (5.1c𝐀), with the far sum inside the term 1 of C_α (*The constant.*), gives |F_j(A)| ≤ b^c_j := d_jE^𝐀_1(α)L^{−(4+β′)(k−j)} per point z of the layer on that ball, where □₀ satisfies (N). The same holds at a □₀ that meets a finer layer, through the evaluation at the scale n − 1 (*The near domains at a finer layer.*, with the factor L^{4+β′} in C_α; the large-field note's (RΔ^c-T), its #4.472).
{#C8.2.2-61} Here E^𝐀_1(α) := C^𝐀_αE₀, C^𝐀_α = 6⁵C_α and C_α of §5 (*The constant.*), uniform in j and k (Theorem 2's real constant E₁ carries the smaller factor (ε/α₃)^{5−β} instead), since Δ_j/d_j satisfies the hypothesis (I.1.18) with E₀.
{#C8.2.2-62} At j = k the note does not use Lemma 4's factor L^{−(4+β′)} but the direct bound of the case n = j of *Mixed radii.* (#C5.28), the weaker one, and the same bound holds where the composite lies in the evaluation set ℰ_k(X; r), and it does on the ball: it lies in 𝒫_k(X; r), shown below, and it is a point (R2) with p = k on the cube of the scale k + 1 (#C5.8).
{#C8.2.2-63} The composite lies in the orbit of the composite at 𝐔₀ with the field 𝐀_A^h (*The composites over 𝒮_z.*), and 𝒫_k(X; r) is a union of orbits (#C5.5), so the representative 𝐔₀ is read.
{#C8.2.2-64} Read at the scale k, it meets each configuration condition and the current bound r_{0,k}/C_{Q*} at most at 0.92 of its threshold.
{#C8.2.2-65} At (R1) and (R2), 𝐔₀ = 𝐔 is a literal point of a top index ≥ k+1 at the radii r⁺, whose quantities are at most (9/8)·0.66 < 0.745 of the thresholds of the scale k (#C5.27).
{#C8.2.2-66} At (R3), 𝐔₀ = exp iη𝓗^{g′}𝐔′ has the quantities of 𝐔′, at most 0.745 of them, moved by at most e^{β_I}·¼r_{0,k+1}/C_{Q*} (above), which is at most 0.66·0.26 of them at the scale k, so at most 0.745 + 0.172 < 0.92.
{#C8.2.2-67} At (N) they are at most 0.66·⅛ (above).
{#C8.2.2-69} At j = k the composite at 𝐔₀ is the local minimiser U_k(□₀, ·) of the data of exp iη𝐀_A^h𝐔₀.
{#C8.2.2-70} These data differ from those of 𝐔₀ by at most O(1) times the entries of 𝐀_A^h, which are at most e^{2β_I}c₂r_{0,k}/(4C₁₃C_{Q*}).
{#C8.2.2-71} So by Proposition 9 [15] and Cauchy's estimate in the data (#C5.8), the composite moves the conditions (i)–(iii) and the current of U_k(□₀, M^·(𝐔₀)) = 𝐔₀^{g} (#C5.26) by at most 4max(B₃, B₅)O(1)e^{2β_I}c₂r_{0,k}/(4C₁₃C_{Q*}) ≤ r_{0,k}/(128C_{Q*}) for c₂ ≤ c_N, by e^{2β_I} < 2 ≤ C_{Q*} ≤ B₃C₁₃²C_{Q*} (B₃, C₁₃ ≥ 1).
{#C8.2.2-72} This move is measured from 𝐔₀^g; transformed back by g^{−1}, with ‖Ad(g^{−1})‖ ≤ e^{β_I} (#C5.26), it is at most e^{β_I}r_{0,k}/(128C_{Q*}) for the quantities covariant at the full configuration, and at most (1 + O(α_{1,k}))e^{β_I}r_{0,k}/(128C_{Q*}) for the A′-gradient of (ii), which is covariant at the real part, the transport adding the commutator with A′; 0.92 + (1 + O(α_{1,k}))e^{β_I}/128 < 1 for γ small, so it is inside the room 0.08 of each threshold, since r_{0,k} ≤ r_{1,k}.
{#C8.2.2-73} The lift condition at the composite is that of *The lift condition at complex configurations* (#C5.61) at the complex data of the fluctuation integral.
{#C8.2.2-74} The fluctuation enters only as 𝐀_A, the role of 𝐀 in (I.3.28), at the background 𝐔̂_z of a point of ℰ_{k+1} (#C5.12-7).
{#C8.2.2-75} Lemma 4's slot B′ (|B′| < α₃, RG I p.280 l.25–26) carries the field τQ′ generated by 𝐀_A and the Cauchy room of (I.3.54) inside the proof of (5.1c𝐀) (#C5.43); it is not the Gaussian variable A. With α_{0,k} = ĝ_kC₀(log ĝ_k^{−2})^{q₀} ((2.28), p.259 l.47–48, at ĝ_k by #CP.13) and r_{0,k} = α_{0,k}/(8B₃), m_k = ½c_mĝ_k(log ĝ_k^{−2})^{q₀} with c_m := c₂C₀/(32B₃C_flC₁₃C_{Q*}).
{#C8.2.2-76} With ϑ_k = (A₁/A₀)ε_k and ε_k = ĝ_kA₀(log ĝ_k^{−2})^{p₀} (CRE (2.4) at ĝ_k, #CP.13), ϑ_k = A₁ĝ_k(log ĝ_k^{−2})^{p₀} and 2m_k/(‖C‖_∞ϑ_k) = (c_m/(‖C‖_∞A₁))(log ĝ_k^{−2})^{q₀−p₀} ≥ 4 for γ small, since q₀ > p₀, a choice that (2.28) allows ("integers greater than 1", p.259 l.48–50), and q₀ = min(q₀, q₁) (#C5.36).
{#C8.2.2-77} So the cutoff ball of (3.16), on which sup_b|g_kCA_k(b)| ≤ ‖C‖_∞ϑ_k, lies inside the ball of radius m_k with the ratio T₀ := m_k/(‖C‖_∞ϑ_k) ≥ 2.
{#C8.2.2-78} Bałaban's expansion uses bounds on the integration region only: RG II cuts at the radius ε₁/g_k of its domain (1.34) ((2.3), p.12 l.15–21), and CRE's (3.43) (table #T11.12-2) is the space of the terms whose domains are not in Λ_{k+1}, those in Λ_{k+1} keeping RG I's (I.6.34).
{#C8.2.2-79} So every sup bound below is taken on the cutoff ball, and the analyticity beyond it gives the margin T₀.
{#C8.2.2-80} This is Bałaban's inclusion of the fluctuation cutoff in his analyticity domain, which his expansion and his Cauchy estimate (3.54) (p.280) use (for the terms with domains not in Λ_{k+1}, table #T11.12-2-1), and in CRE's parameters it is a threshold of Bałaban's kind on A₁/A₀ (p.266 l.42, "for A₁/A₀ sufficiently small") and on the exponents q₀, q₁ against p₀ (of the kind LFR II p.383 l.28).
{#C8.2.2-81} Second, the split and the evenness (lem:c5-5R-1(b), lem:c5-5R-2(a)): F_j(A) − F_j(0) = L_j(A) + R_{2,j}(A) with L_j(A) := DF_j(0)A linear (the term hD̃ is of second order and belongs to R_{2,j}) and R_{2,j} the two-term Taylor remainder.
{#C8.2.2-82} The Gaussian measure of (3.15) with the symmetric cutoff (3.16), after the removal of the gauge-fixing δ-functions by C (p.267 l.41, the form at p.267 l.52), is even in A_k, and L_j is odd, so in the expansion of §8.5 the cluster consisting of L_j alone vanishes, and L_j enters only through clusters in which it is connected to at least one activity of 𝐏_t (the interaction is not even: the cubic vertices of the action and the odd parts of 𝐄_k(U_k(…)) − 𝐄_k(U_{k+1}) are in it, (3.28)).
{#C8.2.2-83} Each such cluster carries the activity's small factor a_k, the bound of 𝐏_t's activities on the cutoff ball (#C5.12-8). The action's vertices of order n ≥ 3 are ≤ g_kO(p₀(ĝ_k)³) there (|A| ≤ r^χ_k ≤ (A₁/A₀)p₀(ĝ_k), #C8.2.1-6, #T3.27).
{#C8.2.2-83-0} The frozen terms' fluctuation parts are bounded there by the terms' own class bounds, which are the outputs of the earlier steps, ≤ g_{j−1}O(p₀³(ĝ_{j−1})) in the form of (2.42) for the generation j (p.278 l.32–35: the terms of (3.47) "satisfy the bounds (2.42), with the constant B₀ replaced by O(p₀³(g_k))", and "the multiplication by g_k yields small bounds"), times L^{−β′(k−j)} per scale-k point by Theorem 2.
{#C8.2.2-84} So a_k ≤ g_kP_a(log g_k^{−2}) for a polynomial P_a, since g_{j−1} ≤ (1 + β₀)g_k (CRE (2.6)), log ĝ_{j−1}^{−2} ≤ log ĝ_k^{−2} + log((1 + β₀)²(k − j + 1)) against the factor L^{−β′(k−j)}, and log ĝ_k^{−2} ≤ log g_k^{−2} + log ρ_γ (#CP.14).
{#C8.2.2-85} This is V4's mechanism (β) and lem:c5-5R-2(c), the Cauchy parameter on the activities: with every activity multiplied by 𝔷 ∈ ℂ (as at #C7.6-6-3; #CK.1-32), the terms with at least one activity vanish at 𝔷 = 0, and the expansion converges for abs(𝔷) up to the ratio of the Kotecký–Preiss bound ā it tolerates to a_k, so each such term carries a_k/ā.
{#C8.2.2-86} Third, the second-order part and the Gaussian mean (mechanism (γ)): for A in the cutoff ball, with f(t) := F_j(tA) analytic for |t| ≤ T := m_k/sup_b|g_kCA(b)| ≥ T₀ and bounded by b^c_j there, the remainder is bounded by its Taylor tail,

{#C8.2.3} R_{2,j}(A) = f(1) − f(0) − f′(0), |R_{2,j}(A)| ≤ Σ_{n≥2}T^{−n} sup_{|t|=T}|f(t)| ≤ C_Tb^c_j(sup_b|g_kCA(b)|/m_k)², C_T := (1 − 1/T₀)^{−1},

{#C8.2.4} and on the cutoff ball, where T ≥ T₀, |R_{2,j}(A)| ≤ C_Tb^c_jμ_k, μ_k := (‖C‖_∞ϑ_k/m_k)² = T₀^{−2} ≤ 4‖C‖_∞²(A₁/c_m)²(log g_k^{−2})^{−2(min(q₀,q₁)−p₀)}, a fraction of the age-decayed class bound that is a negative power of log g_k^{−2}.
{#C8.2.4-1} So by RMark (§8.5), with this bound of the insertion on the cutoff ball, the cluster consisting of R_{2,j} alone is ≤ C_Tμ_kb^c_j; the clusters connecting R_{2,j} or L_j to activities are ≤ C_KP·4b^c_j·a_k by the bound a_k on the cutoff ball (|L_j(A)| = |f′(0)| ≤ b^c_j/T ≤ b^c_j by Cauchy, so |L_j|, |R_{2,j}| ≤ 3b^c_j there).
{#C8.2.4-2} Counting the L^{4(k+1−j)} scale-j points per scale-(k+1) point, L^{4(k+1−j)}L^{−(4+β′)(k−j)} = L⁴L^{−β′(k−j)}, and dividing by E₀, the generated difference from (a) per scale-(k+1) point in the class norm is

{#C8.2.5} (8.2) d^{(a)}_{k+1} ≤ ε_k^*(D_k + S_k), D_k := Σ_{j≤k}L^{−β′(k−j)}d_j, S_k := Σ_{j≤k}d^R_j, ε_k^* := C_XC_ptC_KPL⁴C^𝐀_α[C_Tμ_k + 4a_k],

{#C8.2.6} with S_k the carried 𝐑-differences of §8.4, whose norms d^R_j are taken on the same evaluation sets ℰ_j, since this step generates them at its points (no age factor, so the normalisation 1 in place of L^{−β′(k−j)} and the same ε_k^*, the 𝐑-terms' class bounds R₁g^{κ₀} of (2.31) in place of E₀ being the smaller), and ε_k^* → 0 as g_k → 0: μ_k is a negative power of log ĝ_k^{−2} ≥ log g_k^{−2} (#CK.1-9, #CP.14), and a_k = g_kP_a(log g_k^{−2}).
{#C8.2.6-1} Every step is taken at a point of ℰ_{k+1}(X; r), and every term it reads is read at a point of ℰ_j of its own domain, so the bound holds in the norm d_{k+1} on ℰ_{k+1} that RΔ assumes, with no conversion between real sizes and class radii.

{#C8.2.7} The coupling part (b): at g^B the frozen terms' fluctuation parts are F_j((1+τ_k)A) in place of F_j(A), and G_j(A) := F_j((1+τ_k)A) − F_j(A) = Σ_{n≥1}a_n[(1+τ_k)^n − 1] with f(t) = Σ_na_nt^n and |a_n| ≤ b^c_jT^{−n} by Cauchy has G_j(0) = 0, the odd linear part τ_ka_1 = τ_kDF_j(0)A, and the remainder Σ_{n≥2}, bounded by |τ_k|b^c_jΣ_{n≥2}n(1+|τ_k|)^{n−1}T^{−n} ≤ |τ_k|C_T′b^c_j(sup_b|g_kCA(b)|/m_k)² with C_T′ := (9/2)(1 − 3/(2T₀))^{−2} (|τ_k| ≤ 1/2 and Σ_{n≥2}nx^n ≤ 2x²(1 − x)^{−2}).
{#C8.2.7-1} The action's own terms of order n ≥ 3 change by |τ_k| times their bounds on the cutoff ball, which are among the activities bounded by a_k: the odd cubic part enters connected clusters only (a_k²), and the quartic part, alone, by its sup bound ≤ a_k on the cutoff ball (RMark's ι_G ≤ ι), both below the bracket of ε_k^*.
{#C8.2.7-2} With the frozen terms' own class bounds C^𝐀_αL^{−(4+β′)(k−j)} in place of b^c_j/E₀ and Σ_jL^{−β′(k−j)} ≤ (1 − L^{−β′})^{−1}, the coupling part is ≤ C_gε_k^*g_k²|δ_k| with C_g := (1 − L^{−β′})^{−1}max(C_T′/(2C_T), 1), and the shell term of (b) is smaller still.

### 8.3 The Recursion {#CS8.3}

{#C8.3.1} With (8.1), (8.2), the coupling and shell parts of §8.2(b), and the marked-cluster bound of §8.5, the generated difference per scale-(k+1) point in the class norm is

{#C8.3.2} (8.3) d_{k+1} ≤ ε_k^*(D_k + S_k) + C_gε_k^*g_k²|δ_k| + e_{k+1},

{#C8.3.3} with ε_k^* and C_g of (8.2) and §8.2(b), and e_{k+1} the depth terms: the classical ones are (9.10) at the fluctuated block field (§8.1), and the Gaussian and configuration ones are bounded in §10.5.
{#C8.3.3-0} The per-step coefficient β_i is the marginal part of the step's output, so its two-run difference Δβ_i is the marginal part of the generated difference, and its own dependence on the coupling is inside d_i through §8.2(b). Cauchy's estimate on the quadratic coefficient Π^Δ_{22,11} of (3.61)–(3.64) gives |Δβ_{k+1}| ≤ C_βd_{k+1}. From the pinned value δ_K = 0 the coupling difference is δ_j = Σ_{i=j+1}^{K}Δβ_i, so |δ_j| ≤ C_βΣ_{i>j}d_i.
{#C8.3.3-1} For the carried sum this gives D_{k+1} ≤ θ_kD_k + ε_k^*S_k + C_gε_k^*g_k²|δ_k| + e_{k+1} with θ_k := L^{−β′} + ε_k^*.
{#C8.3.3-2} C_α, C^𝐀_α, C_T, C_X, C_cov, and C_KP are independent of j and k: Theorem 2's E₁ is independent of j and k, and C_KP depends on the activity bounds, which are uniform in k. At every shared scale ε_i^* ≤ ε^*(g_i), since μ_i = μ(ĝ_i) ≤ μ(g_i), μ being a negative power of log g^{−2} (#CP.22-1) and ĝ_i ≤ g_i (#CP.14), and a_i = a(g_i); and g_i ≤ (1+β₀)g_K ≤ (1+β₀)γ by CRE (2.6), so ε^*(g_i) ≤ ε^* := ε^*_γ := sup_{g≤(1+β₀)γ}ε^*(g). Hence θ_k ≤ θ := L^{−β′} + ε^* < 1 under (T1).
{#C8.3.3-3} The delay before the age decay sets in is absorbed in E₁, which is uniform in j and so does not depend on R_j.
{#C8.3.3-4} The same recursion holds for the dev insertions of the dressed loops, which form the class D(k), and for the perimeter coefficients, which are the marginal parts of the loop's generated terms. The per-step map of D(k) is the same fluctuation integral with the loop's words as additional marked activities, which have the same localisation and analyticity. Their two-run difference is the frozen difference of the dev insertions, so (8.2)–(8.3) hold for them with the dev insertions' class norms in place of d_j.
{#C8.3.3-4-1} Precisely: the class norm d^{ins}_j of the marked activities of generation j is relative to the bounds with which they enter (S-w) (map #MD2.4.11.21, #MD2.4.12.11), as d_j is relative to E₀exp(−κd_j(X)) (#C8.2.2-1), and D^{ins}_i := Σ_{j≤i}L^{−β′(i−j)}d^{ins}_j.
{#C8.3.3-4-1-1} The class norm d^{ins}_j contains the reference activities c_𝒢 = Y_𝒢(1, 0) of generation j's groups, whose bounds (S-w) contains as its c-version (map #MD2.4.12.12-2), relative to the same bound C_S′ρ_jpl_j of (S-w).
{#C8.3.3-4-2} The inputs of their generated difference are the frozen differences of the old marked activities and of Bałaban's terms, so (8.3) reads d^{ins}_{i+1} ≤ (ε^* + ε^Q_i)D^{ins}_i + ε^*(D_i + S_i) + C_gε^*g_i²|δ_i| + e_{i+1}, with d^{ins}_1 ≤ 2 and e_{i+1} the depth sources of §8.7 with C′_e included (#C8.7.1-1), and ε^Q_iD^{ins}_i the part of the old vertices (#C8.3.3-4-3).
{#C8.3.3-4-3} *The old vertices.* A group born at the step i + 1 has, besides its marked polymers, old vertices (map #MD2.4.12.16–#MD2.4.12.17): the untouched old insertions merged into it, and the occurrences of the step-i reference gas from the expansion of Q_i (map #MD2.3.3.4–#MD2.3.3.5-4). Their activities enter Y_𝒢 as numbers, outside the fluctuation integral, so their frozen differences carry no factor ε^*.
  {#C8.3.3-4-3-1} The map's telescoped difference count, #MD2.4.13.11–#MD2.4.13.14, applies with the two runs in place of T and T′. It uses only that the two families have the same polymers, compatibilities, and Ursell coefficients (map #MD2.4.13.16), which the runs share, and its vacuum-tail part δ_vac is absent, the lattice being the same. Each term has one marked old vertex, and a term with an M-vertex is counted with the mark of (S-w) as well (map #MD2.4.13.11-2).
  {#C8.3.3-4-3-2} The marks are the old insertions' frozen differences and, through the cluster level (map #MD2.4.13.16, #MD2.4.13.8-3), the step-i groups' Δc_𝒢. In the normalisation of #C8.3.3-4-1, in which the old marked activities' frozen differences are ≤ D^{ins}_i (#C8.3.3-4-2) and the step-i groups' Δc_𝒢 are ≤ d^{ins}_i ≤ D^{ins}_i (#C8.3.3-4-1-1), the mark sums of map #MD2.4.13.8 are ≤ D^{ins}_i times the step-i sums, so ε^{diff}_i ≤ D^{ins}_iC″C_S′ρ_ipl_i (map #MD2.4.13.13-2).
  {#C8.3.3-4-3-2-1} By map #MD2.4.13.12, δ_{i+1} ≤ K_ΔC″C_S′ρ_{i+1}pl_{i+1}ε̄^{diff}_i/ε_* with ε̄^{diff}_i = L⁴C(M/ν_e²)K₀ε^{diff}_i, and the factor 2 of the doubled unmarked factors (map #MD2.4.13.15-5). Relative to C_S′ρ_{i+1}pl_{i+1}, the old vertices' part of d^{ins}_{i+1} is then ≤ ε^Q_iD^{ins}_i, with ε^Q_i := ε^Q(g_i) and {#D.ε^Q} ε^Q(g) := 2L⁴C(M/ν_e²)K₀K_Δ(C″)²C_S′ρ(g)pl(g)/ε_*, the map's constants, ρ(g) := C_ρg²(1 + A₁(log g^{−2})^{p₀})⁴, and pl(g) := 1 + (log g^{−2})^{(q₁−q₀)₊}.
  {#C8.3.3-4-3-3} ε^Q(g) → 0 as g → 0, as g² times a power of log g^{−2}, and it enters (T1) (#CP.22).
{#C8.3.3-4-4} *The wrap marks.* On the all-small-field pair the step-i gas also has wrap groups, whose Δc_𝒢 are not in d^{ins}_i. #C8.3.3-4-3-2 is the count with run A's wraps in both runs, so its Δc_𝒢 are the dev groups'. Moving the wraps from run A's to run B's adds the source s^w ≤ K_ΔC″c″x^*_K to the display of #C8.3.3-4-2 at every step (#C7.8-9-7–#C7.8-9-8-1). It is a source, not a growth.
{#C8.3.3-6} *The first steps.* §9 bounds the depth only at the steps k ≥ k₀(ε₀) (§9.6, #C9.6.6).
{#C8.3.3-7} At the finitely many steps k < k₀(ε₀), (8.3) is used with e_{k+1} := 2: both runs' generated terms satisfy (I.1.18) on their classes, which contain the evaluation sets (#C5.8-25, #C8.2.6-1), so d_{k+1} ≤ 2. The same holds for the dev insertions and perimeter coefficients of #C8.3.3-4, since each run's value satisfies its own class bound.
{#C8.3.3-8} Since θ̃ ≥ L^{−(1−2ε₀)/3} > L^{−1} (§8.7), 2 ≤ 2L^{k₀(ε₀)}θ̃^{k+1} for k + 1 ≤ k₀(ε₀), so the depth sources satisfy e_i ≤ C_eθ̃^i at every i once C_e ≥ 2L^{k₀(ε₀)}.

### 8.4 The 𝐑-Sector {#CS8.4}

{#C8.4.1} The 𝐑-terms have no age decay beyond the volume factor (CRE p.283 l.35–39: O(1)(L^jL^{−n})⁴g_j^{κ₀}exp(−κd_j(X)) per scale-j point), so their differences enter (8.3) as S_k = Σ_{j≤k}d^R_j without the factor L^{−β′(k−j)} of (8.2).
{#C8.4.1-2} A term of the generation k+1 has two sources.
{#C8.4.1-3} (i) The renormalisation of the large-field components at the step k+1, as the logarithm of the quotient LFR I (0.5), with the bound (2.31), g_{k+1}^{κ₀}exp(−κd_{k+1}(X)). By (8.4) of §8.6 its two-run difference is ≤ c_{k+1}𝒟_{[k+1]} + c^B_{k+1}𝒟^∗_{k+1} + c^V_{k+1}𝒟^V_{k+1} + ν_{k+1}.
{#C8.4.1-3-1} Here c_j := C_R(100MR_j)^dg_j^{κ₀}, c^B_j := C^B_R(100MR_j)^dg_j^{κ₀}, and c^V_j := C^V_R(100MR_j)^dg_j^{κ₀}. 𝒟^∗ is the boundary terms' source of `WILSON_IT1_LARGE_FIELD_DEPTH_2026_10_27.md` §4(e), 𝒟^V is the old terms' own differences in the V(Y) (§8.6, *The Own Differences of the V(Y).*), and ν_j are the fine-scale and old-history bounds of §8.6, with Σ_{j≤K}ν_j ≤ C_νw_K.
{#C8.4.1-4} 𝒟_{[j]} := max_{k_s/8−1<m≤j}e^{−½C_P(j−m)}𝒟_m is the memory-weighted maximum over the component's history, with 𝒟_m := D^♭_m + S_{m−1} + C|δ_m| + e_m + h_m, h_m := C_hθ̃^m, D^♭_m := Σ_{i≤m}q^{m−i}d_i, and q := L^{−1/3}e^{−1/12}. §8.7's sums treat 𝒟_{[j]} as a scale-j quantity: in the weighted norm there max_{m≤j}e^{−½C_P(j−m)}m_m ≤ m_j, since e^{−½C_P} ≤ e^{−1} < ½ ≤ θ̃, and S_{m−1} ≤ S_{j−1}.
{#C8.4.1-5} The first four terms of 𝒟_m bound the relative difference of the two runs' integrands per point of the history at the scale m. D^♭_m bounds the frozen small-field exponents through D_m ≤ D^♭_m, which holds since L^{−β′} ≤ q, that is (β′ − 1/3)log L ≥ 1/12; this is true for β′ ≥ 19/40 (§5) and L ≥ 2. D^♭_m also carries the coupling part of the exterior part W_ext of 𝐂_j (§8.6). S_{m−1} bounds the carried 𝐑-differences.
{#C8.4.1-6} C|δ_m| bounds the coupling, which enters the action as Cε_m²|δ_m|, the function (1.6) of LFR I as 10|δ_m| per variable (§6.2, #C6.2.6), and the normalisation constants, the radial shells, the coupling part of the plaquette shells, and the denominators of §8.6 as ≤ C|δ_m| per point. e_m bounds the depth terms.
{#C8.4.1-7} The input (LF) bounds the rest, the threshold shells and the large-field integrands, by h_n per point at every scale of a history born at the scale n > k_s/8, and §8.6 carries it through the term m = n of 𝒟_{[j]}.
{#C8.4.1-8} (ii) The fluctuation integral's own 𝐑-output. By (3.26) the frozen 𝐑-terms of the recent generations, 𝐑″_k = Σ_{j=k₁+1}^{k}𝐑^{(j)}, are not merged into 𝐄_k but carried through the step by the s-interpolation (p.271 l.1–30), and the step's output contains 𝐑″^{(k+1)}, their integrated fluctuation parts (p.279 l.17–20). Here k₁ is the largest integer with L^{−(k−k₁)}MR_j ≤ L (p.270 l.49–50), read with j = k₁.
{#C8.4.1-9} The inequality fails at k₁ + 1, so the memory N′_k := k − k₁ satisfies N′_k < log_L(MR_{k₁+1}). For m ≤ n the tube's R satisfies CRE (2.9) (p.256 l.12–17) in the form R_m ≤ L(1 + x)^{β₀}R_n, x := ĝ_n²b′(n − m): R_m < L(log u_m)^r and R_n ≥ (log u_n)^r (#CP.13), and u_m = (1 + x)u_n, so R_m/R_n < L(1 + log(1 + x)/log u_n)^r ≤ L(1 + x)^{r/log u_n} ≤ L(1 + x)^{β₀}, as log u_n ≥ log γ^{−2} ≥ r/β₀ for γ small.
{#C8.4.1-9-1} With m = k₁ + 1, n = k, and log_L(1 + x) ≤ x/log L for x ≥ 0, this gives N′_k < 1 + log_L(MR_k) + β₀b′ĝ_k²N′_k/log L. For γ small β₀b′ĝ_k²/log L ≤ ½, so N′_k < 2 + 2log_L(MR_k). Since R_k < L(log ĝ_k^{−2})^r, ĝ_k²N′_k is then small for γ small, and so is g_k²N′_k ≤ ρ_γĝ_k²N′_k (#CP.14); so (1 + ĝ_k²b′N′_k)^{β₀} ≤ 2 and R_{k₁+1} ≤ 2LR_k.
{#C8.4.1-10} Hence N′_k < log_L(2LMR_k) ≤ log_L(MR_k) + 2 ≤ N′(ĝ_k), with N′(g) := log_L(MR(g)) + 3 and R(g) the least power of L with R(g) ≥ (log g^{−2})^r, so that R_k = R(ĝ_k) (#CP.13); N′(g) is a double logarithm of g^{−1} and decreases in g.
{#C8.4.1-11} The two-run difference of 𝐑″^{(k+1)} has two parts. The first is the generated difference of §8.2 with the frozen 𝐑-differences of the window as the marked activities, bounded by (8.2) with the window sum in place of D_k + S_k. The second is the measure difference Δ𝐏 acting on run A's 𝐑″_k, whose fluctuation parts are activities of size ≤ 2R₁N′_kg_k^{κ₀}/E₀ connected to the marked activity. So d^{R,(ii)}_{k+1} ≤ 2ε_k^*Σ_{j=k−N′_k+1}^{k}d^R_j + C_KP(2R₁/E₀)N′_kg_k^{κ₀}ε_k^*(D_k + S_k).
{#C8.4.1-12} The 𝐑-differences of the generations j ≤ k₁ are merged into 𝐄_k and carried with the weight 1 inside S_k.
{#C8.4.1-13} Together,

{#C8.4.2} d^R_{k+1} ≤ c_{k+1}𝒟_{[k+1]} + c^B_{k+1}𝒟^∗_{k+1} + c^V_{k+1}𝒟^V_{k+1} + ν_{k+1} + 2ε_k^*Σ_{j=k−N′_k+1}^{k}d^R_j + c′_{k+1}(D_k + S_k), c′_{k+1} := C_KP(2R₁/E₀)N′_kg_k^{κ₀}ε_k^*, ε_k^* that of (8.2), ≤ ε^*(g_k) (#C8.3.3-2),

{#C8.4.3} *The window lemma.* If u_j := 0 for j ≤ 0, u_{i+1} ≤ s_{i+1} + η_iΣ_{j=i−N′_i+1}^{i}u_j for all i ≥ 0, and Σ_{i: i−N′_i<j≤i}η_i ≤ 1/2 for every j, then Σ_{j≤k}u_j ≤ 2Σ_{j≤k}s_j. Indeed, summing over i gives Σ_{i≤k}u_i ≤ Σ_{i≤k}s_i + Σ_{j≤k}u_jΣ_{i: i−N′_i<j≤i}η_i ≤ Σ_{i≤k}s_i + ½Σ_{j≤k}u_j.
{#C8.4.3-1} It is applied with u_j = d^R_j and η_i = 2ε_i^*. The i with i − N′_i < j ≤ i satisfy 0 ≤ i − j < N′_i. So, by CRE (2.6), g_i ≥ g_j/(1+β₀) and g_i ≤ (1 + g_i²b₂N′_i)^{1/2}g_j, which is ≤ 2g_j since g_i²N′_i is small (#C8.4.1-9-1).
{#C8.4.3-2} Each such i has N′_i ≤ N′(ĝ_i) ≤ N′(ĝ_j) ≤ N′(g_j/(1+β₀)) (#C8.4.1-10), as ĝ_i ≥ ĝ_j ≥ ρ_γ^{−1/2}g_j ≥ g_j/(1+β₀) for γ small (#CP.14). So there are at most N′(g_j/(1+β₀)) such i, each with η_i ≤ 2ε^*(g_i) ≤ 2ε̂^*(g_j) (#C8.3.3-2).
{#C8.4.3-3} The condition of the lemma therefore holds if 4ε̂^*(g_j)N′(g_j/(1+β₀)) ≤ 1, which is part of (T1). Then S_k ≤ 2Σ_{j≤k}[c_j𝒟_{[j]} + c^B_j𝒟^∗_j + c^V_j𝒟^V_j + ν_j + c′_j(D_{j−1} + S_{j−1})].
{#C8.4.3-4} The terms S_{m−1} inside 𝒟_{[j]}, 𝒟^∗_j, and 𝒟^V_j, and S_{j−1} in the last term, feed S back into itself. Since S_{m−1} ≤ S_{j−1} for m ≤ j, S_k ≤ Σ_{j≤k}c^S_jS_{j−1} + B_k with c^S_j := 2c_j + 2c^B_j + 2c^V_j + 2c′_j and B_k := Σ_{j≤k}[2c_j𝒟′_{[j]} + 2c^B_j𝒟^{∗′}_j + 2c^V_j𝒟^{V′}_j + 2c′_jD_{j−1}] + 2C_νw_K. Here 𝒟′_m := D^♭_m + C|δ_m| + e_m + h_m, and 𝒟^{∗′}_j and 𝒟^{V′}_j are the maxima 𝒟^∗_j and 𝒟^V_j with the terms S omitted.
{#C8.4.3-5} Further 2c′_jD_{j−1} ≤ 2c_jD_{j−1}, since c′_j/c_j = (2/E₀)(C_KPR₁/C_R)N′_{j−1}ε^*_{j−1}(g_{j−1}/g_j)^{κ₀}(100MR_j)^{−d} ≤ 1 for γ small: ε^*_{j−1} ≤ ε^*_γ is small (§8.7), N′_{j−1} ≤ (100MR_j)^d, and g_{j−1}/g_j ≤ 1 + β₀ by CRE (2.6).
{#C8.4.3-6} B_k is nondecreasing in k and S_0 = 0, so induction on k gives S_k ≤ B_kΠ_{j≤k}(1 + c^S_j) ≤ B_kexp(Σ_{j≤k}c^S_j). Hence

{#C8.4.4} (8.5) S_k ≤ C_S[Σ_{j≤k}c_j(𝒟′_{[j]} + D_{j−1}) + Σ_{j≤k}c^B_j𝒟^{∗′}_j + Σ_{j≤k}c^V_j𝒟^{V′}_j + C_νw_K], C_S := 2exp(2C_Σ), C_Σ := sup_KΣ_{j≤K}(c_j + c^B_j + c^V_j + c′_j),

{#C8.4.5} C_Σ is finite and uniform in K: (100MR_j)^d is a power of log g_j^{−2}, N′_j and the factor N₀^+(j) of C^B_R (#C8.6.29) are double logarithms, and g_j^{κ₀} ≤ (ḡ^{−2} + b(K − j) − C)^{−κ₀/2} by Lemma 2.1(i), which is summable over j for κ₀ > 2.
{#C8.4.5-1} S feeds back into (8.3) through ε^*S_k, and (8.5) feeds D back into S with the weights c_j, which at the fine scales are ≤ (bK/2)^{−κ₀/2} times a polylogarithm. Together with the fine-scale part of the 𝐑-sector source Σ_jν_j ≤ C_νw_K of §8.6, a sum over at most K fine scales, this gives the part K^{1−κ₀/2}ℓ_K of the term μ_K = K^{2−κ₀/2}ℓ_K in the weight w_K of §8.7. The rest of μ_K covers the 𝐑-terms' old ages of §10.5.

### 8.5 The Marked-Cluster Bound (RMark, Bałaban's Construction Applied to the Insertion Δ𝐏) {#CS8.5}

{#C8.5.1} *Statement.* For the step-(k+1) fluctuation integral with an admissible interaction 𝐏_t and localised insertions I(Y), Y ∈ 𝐃_k, analytic on the fluctuation domain of Bałaban's terms of the same kind, which contains the cutoff ball of (3.16) with the margin T₀ (§8.2), and with |I(Y)| ≤ ι(Y)exp(−κd_k(Y)) on the cutoff ball, ⟨Σ_YI(Y)⟩_t has the localised expansion (3.47), Σ_{X∈𝐃_{k+1}}𝐈(X), with |𝐈(X)| ≤ C_ptC_XC_KPsup_{Y∩X≠∅}[ι_G(Y) + a_kι(Y)]exp(−κ′d_{k+1}(X)), κ′ := (1 + 7β/2)κ, for β ≤ 1/4.
{#C8.5.1-1} Here ι_G(Y) bounds the terms in which the insertion is connected to no activity of 𝐏_t, Bałaban's Gaussian part, and a_kι(Y) bounds every term in which it is connected to at least one activity, with a_k the Cauchy parameter on the activities (#C8.2.2-85).
{#C8.5.1-2} Always ι_G(Y) ≤ ι(Y), and ι_G(Y) = 0 for an insertion odd in A, the cutoff measure being even.
{#C8.5.1-3} For I(Y) = c + ⟨A, KA⟩, with c a constant and K supported in Y × Y, ι_G(Y) ≤ C_G″(|c| + |Y|‖K‖_Y), ‖K‖_Y := max(sup_yΣ_{y′}|K(y, y′)|, sup_{y′}Σ_y|K(y, y′)|), the larger of the row and column sums.
{#C8.5.1-4} C_KP and C_G″ are Bałaban's constants for his own insertion and its Gaussian part, independent of k.
{#C8.5.1-5} C_X := sup_xΣ_{Y∋x}exp(−(β/16)κd_k(Y)) is finite for κ large at fixed β, and C_pt(M, L, β, κ) absorbs the number of scale-k points of X and the factors |Y| of the quadratic insertions, which are polynomial in d_{k+1}(X) and in d_k(Y).
{#C8.5.1-6} The output 𝐈(X) is analytic on the class U^c_{k+1} of the next scale, as Bałaban's output is (p.262 l.26–28, p.279 l.22–23).
{#C8.5.1-7} For an insertion from the boundary terms the same holds with the fluctuation domain replaced by Ũ^c_{k+1}(Y, α̃₀, α̃₁) × {A : supp A ⊂ Y ∩ Λ^{(k)*}_{k+1}, |A| < 2r^χ_k}, where 2r^χ_k is the large-field note's A-radius (its #4.595), twice the cutoff radius (#T3.27). The output is then analytic on Ũ^c_{k+1}(X, α̃₀, α̃₁), the class of 𝐁^{(k+1)} in (2.41)–(2.42).
{#C8.5.1-7-1} By O6 closure §3 the boundary terms are analytic on Ũ^c_{k+1}(Y, (1 + β)α̃₀, (1 + β)α̃₁) × 𝒫_k^{3/4}|_Y (#T4.50), which contains this space at O6 §4's points. There g_k sup|B| ≤ ε_k^♯ (#T3.36), and the A-part contributes at most ϑ_k ≤ c₃ε_k/2 ≤ ε_k^♯/2 to it (#T3.27). So on the ball |A| < 2r^χ_k = 2ϑ_k/g_k, which doubles the A-part, g_k sup|B| ≤ (3/2)ε_k^♯.
{#C8.5.1-7-2} Then |B′| ≤ C₁^{RG2}g_k sup|B| (RG II (1.20)) < 3r_{α,k}/4 by O6's (C3), C₁^{RG2}ε_k^♯ < r_{α,k}/2, which is a smallness condition on g_K under q₁ > p₀ (#T6.17). Since r_{α,k}/C₁^{RG2} < ε₁ (O6 §3), these points lie in 𝒫_k^{3/4}.
{#C8.5.1-8} The output's class is the input's class, without the factor (1 + β). The expansion evaluates the insertion only at the background where the output is taken. The print treats the boundary terms by (3.6)–(3.7) of [I] and a localisation, with no renormalisation step (p.276 l.42–46); the step "not needed here" at p.276 l.39–41 concerns 𝐑_k.
{#C8.5.1-8-1} The only derivative there is the t_□-derivative of (3.7) [I] (RG I p.271 l.23–31). It is written as the Cauchy integral (3.15) [I] over a circle in t_□ whose room is the field bound (3.14) [I] at the radius α₂, at a fixed configuration (RG I p.272 l.36–44, p.273 l.4–13). The localisation only restricts the domains, so no derivative estimate uses an enlargement of the class.

{#C8.5.2} *Proof.* By CRE (3.37), p.274, 𝐄_0^{(k+1)}(Λ, U, b) is defined through ∫₀¹dt ⟨tr 𝐕′_k(tg_k, A, b)(CA)(b)⟩_t, an interpolation in the coupling of the interaction with the localised insertion tr𝐕′(CA)(b) under the interacting measure ⟨·⟩_t.
{#C8.5.2-0} P.277 l.22–44 and p.278 l.1–15 expand "the last expectation value in (3.37)" (p.277 l.23–24): the nominator is (3.44) with one factor H′(Z₀) "given by an integral with the integrand including, as one of the factors, a localized term from the expansion of the integrated function", and "Although different, it satisfies the same bound as the other factors" (p.277 l.44–p.278 l.2).
{#C8.5.2-1} (3.45)–(3.47) exponentiate and resum into terms 𝐄_0^{(k+1)}(Λ, X, b) which "satisfy the bounds (2.42), with the constant B₀ replaced by O(p₀³(g_k))", the insertion's own size, "and the multiplication by g_k yields small bounds".
{#C8.5.2-2} The only properties of the insertion used are its localisation, its analyticity on the fluctuation domain, and its bound, and the bound enters linearly. The domain is RG I's (I.6.34) for the domains in Λ_{k+1}, as for Bałaban's terms of the same kind, and #C8.5.1-7's domain for the others. So the output bound is the insertion's bound times a constant of the expansion.
{#C8.5.2-3} For the insertion Δ𝐏(Y) of §8.2, localisation and analyticity hold because both runs' frozen terms have them (§5), and the bound is (8.2).
{#C8.5.2-4} The measure ⟨·⟩_t with 𝐏_t = 𝐏^A + tΔ𝐏 is of the kind expanded on p.277, since 𝐏_t satisfies the inductive bounds (§8.1).
{#C8.5.2-6} The split into ι_G and a_kι separates the terms of H′(Z₀) whose integrand carries no activity of 𝐏_t, the Gaussian expectation of the insertion, from those with at least one. Each activity of 𝐏_t carries the factor a_k of §8.2: the action's vertices of order n ≥ 3 are at most g_kO(p₀(ĝ_k)³) on the cutoff ball (#C8.2.2-83), and the frozen terms' fluctuation parts are at most their class bounds in the form of (2.42), "with the constant B₀ replaced by O(p₀³(g_k))" (p.278 l.32–35).
{#C8.5.2-7} *The rate.* Bałaban's construction is applied with the input rate (1 − β/8)κ. This is allowed since κ may be chosen large there (p.260 l.27: "κ₀ can be chosen arbitrarily large, similarly as κ"), and (1 − β/8)κ is large for κ large.
{#C8.5.2-8} Its output carries the rate (1+4β)(1 − β/8)κ ≥ (1 + 15β/4)κ for β ≤ 1/4. P.262 l.25–28 states the rate (1+4β)κ for the newly created expressions ("for example, by (1+4β)κ"), and the insertion's terms satisfy it by the sentence of p.277 l.44–p.278 l.2 quoted in #C8.5.2.
{#C8.5.2-9} The factor exp(−(β/8)κd_k(Y)) left over is split into two factors exp(−(β/16)κd_k(Y)). The first pays the factors |Y| at the cost C_pt. The second pays the sum over the Y meeting X, which is ≤ n_k(X)C_X, as Bałaban uses the factor exp(−(κ − 1)d_j(X)) to control the sum over X (p.263 l.51–52).
{#C8.5.2-9-1} Here n_k(X), the number of scale-k points of X, is polynomial in d_{k+1}(X) with coefficients depending on M, L, and d, so n_k(X) ≤ C_ptexp((β/4)κd_{k+1}(X)). This leaves κ′ = (1 + 7β/2)κ, which is enough for the extraction (1+3β)κ with ½βκ left (the large-field note's #4.399).
{#C8.5.2-10} *The Gaussian part.* The terms in which the insertion is connected to no activity of 𝐏_t are expectations under the Gaussian measure with the cutoff, with the insertion as the integrand.
{#C8.5.2-11} Bałaban treats an expectation of this kind, the second integral of (3.37), whose integrand is the cutoff's derivative ∂_tχ^{(k)}(tA(b)) (p.274 l.19–20), at p.278 l.37–42: the expansion (I.7.3) with Y₀ = ∅ for the denominator and Y₀ = □ for the nominator, the steps (I.7.3)–(I.7.13) (= RG II (2.3)–(2.13)), and (3.44)–(3.47), with terms satisfying (I.1.18).
{#C8.5.2-12} These steps use of the integrand only its localisation and its bound on the integration region, so with I(Y) in place of ∂_tχ^{(k)}(tA(b)) and Y₀ ⊃ Y they give ι_G ≤ ι, and ι_G = 0 for an odd insertion, the cutoff measure being even.
{#C8.5.2-13} Let I(Y) = c + ⟨A, KA⟩. By Schur's test |⟨A, KA⟩| ≤ ‖K‖_YΣ_{b∈Y}|A(b)|²: |A(y)||A(y′)| ≤ ½(|A(y)|² + |A(y′)|²), the row sums pay the first term, and the column sums the second. The quadratic part is written by the Cauchy formula in a parameter τ, ⟨A, KA⟩ = (2πi)^{−1}∮exp(τ⟨A, KA⟩)τ^{−2}dτ over |τ| = α₄^G/(‖K‖_Y|Y|), as RG II writes its potentials through the parameters τ(Y) of (2.14) (p.15 l.10–18), with 1/|τ(Y)| fixed in (2.18) (p.16 l.16–19).
{#C8.5.2-14} On this circle |τ⟨A, KA⟩| ≤ α₄^G|Y|^{−1}Σ_{b∈Y}|A(b)|² ≤ α₄^GΣ_{b⊂Y₀}|A(b)|², A being RG II's scaled variable B. RG II bounds (2.14) on the complex class by (2.15) (p.15 l.27–36), through the real parts of the forms, the positive measure of the covariance (Re C^{(k)}(Z₀, σ(Z))^{−1})^{−1}, and the quotient of determinants.
{#C8.5.2-15} It compares the operators with those at (U, 0) through the forms R₁, R₂, and R₃ of (2.16), and the determinants by (2.17) (p.15 l.38–p.16 l.12). After the multiplication by |τ(Y)| it bounds its potentials by the form ½O(1)α₄Σ_{b⊂Y₀}|B(b)|² of (2.20) (p.16 l.27–35). With (2.21) and (2.22) (p.16 l.35–45) it absorbs these forms into the Gaussian integral (2.23) at α₅ = O(1)e^{−δ₀M/3} + O(α₀ + α₁) + O(1)α₄ + γ₂, with the factors exp(O(α₅)|Z₀|) of (2.24) and exp(O(α₅)|Z|) of (2.25) (p.17 l.3–24).
{#C8.5.2-16} On the circle exp(τ⟨A, KA⟩) is bounded by the exponential of a form of the same kind, so the same steps apply with α₅ + O(1)α₄^G in place of α₅, for α₄^G small, and the factors are absorbed in the decay of the terms as there.
{#C8.5.2-17} The Cauchy formula costs the factor 1/|τ| = ‖K‖_Y|Y|/α₄^G.
{#C8.5.2-18} So ι_G(Y) ≤ C_G″(|c| + |Y|‖K‖_Y), with C_G″ := (1 + 1/α₄^G) times the constant of Bałaban's bound of these terms, independent of k.

{#C8.5.3} *Application.* By RMark applied to the first term of (8.1), 𝐄_0^{B,(k+2)} − 𝐄_0^{A,(k+1)} = Σ_Y ∫₀¹⟨Δ𝐏(Y)⟩_t dt has localised terms analytic on the class and bounded by C_ptC_XC_KPsup_{Y∩X≠∅}[ι_G(Y) + a_kι(Y)]exp(−κ′d_{k+1}(X)), with ι(Y) the bound of Δ𝐏(Y) on the cutoff ball and ι_G(Y) its Gaussian part. This is the marked-cluster bound (G′).
{#C8.5.3-1} With the three facts of §8.2 this is (8.2), and with the coupling and shell parts (8.3).

### 8.6 The Renormalisation Quotient {#CS8.6}

{#C8.6.1} *Lemma (real backgrounds).* Let f^A, f^B be positive functions on a compact group power with |log(f^B/f^A)| ≤ φ_* pointwise.
{#C8.6.1-1} Then ∫f^B/∫f^A ∈ [e^{−φ_*}, e^{φ_*}].
{#C8.6.1-2} For quotients q^{A/B} := ∫f^{A/B}_1/∫f^{A/B}_2 of two such pairs, |log q^B − log q^A| ≤ 2φ_* and |q^B − q^A| ≤ (e^{2φ_*} − 1)q^A ≤ 4φ_*q^A for φ_* ≤ 1/2.
{#C8.6.1-3} *Proof.* By the pointwise bound, ∫f^B = ∫f^Ae^{log(f^B/f^A)} lies between e^{−φ_*}∫f^A and e^{φ_*}∫f^A. Dividing gives the bound on the quotients, and |q^B − q^A| = |e^{log q^B − log q^A} − 1|q^A; e^{2φ} − 1 ≤ 2(e − 1)φ ≤ 4φ for 0 ≤ φ ≤ 1/2 by convexity.
{#C8.6.1-4} At real backgrounds the densities are positive (LFR I p.176 l.19–20). The complex version below uses absolute integration in place of positivity.

{#C8.6.2} *Application (the complex class).* Bałaban bounds the renormalised terms by uniform bounds on the integrands followed by integration over the real variables. He does this on the complex spaces Ũ^{(n)c}_k of pp.190–191, built "to gain a larger domain of analyticity for the effective action, in order to perform the basic step in the 𝐑-operation" (p.190 l.2–4), with the result (1.70) (p.192), |ℂ^{(n)}_k(X, (𝕌, 𝕁))| ≤ C₀exp(−(1+3β)κd_m(X)), analytic on the space.
{#C8.6.2-1} LFR I p.191 l.49–52 reads: "They are easily obtained estimating the integral (1.60), after the renormalization and the localization. All the expressions in the exponential in this integral can be uniformly bounded in the usual way, except possibly expressions connected with 𝔹_k^{(n)}". The cumulation of those boundary expressions is controlled on p.191 l.52–p.192 l.6 by their factors g_j.
{#C8.6.2-2} The renormalisation of a component Z′ at step j replaces ρ(Z, V) by ρ(Z″, V) times the quotient q(V) := ∫dV|_{Z′}ρ(Z, V)/∫dV|_{Z′}ρ(Z″, V) (LFR I (0.3)–(0.5), p.177 l.1–5). Its numerator n is the large-field integral over the component. Its denominator d is the small-field expression localised near Z′, whose logarithm is given by the convergent small-field expansion that produces the step's small-field output, analytic on the class.
{#C8.6.2-3} At the same complex V the two runs' numerators n^A, n^B are the same operation applied to run-dependent ingredients of the three kinds of §6.2. (α) The small-field ingredients of the component's history, which on the common support of the characteristic functions give integrands I^B = I^Ae^{D}, together with the function (1.6), the localised constants, and the radial shells (§6.2). The two runs' measures of (1.6) differ by ≤ e^{5|δ_m|} − 1 ≤ 10|δ_m| per variable relative to the measure itself (§6.2, #C6.2.6).
{#C8.6.2-4} (β) The shells of the plaquette and reference-configuration tests. (γ) The large-field integrands, among them the term V(X^∼) of LFR II (1.71) for the component X, the terms localised in its component of Z^∼ (p.379 l.24–25), and the boundary terms 𝐁.
{#C8.6.2-5} The factors V(Y) of (1.91), with Y ∖ Z^∼ ≠ ∅, lie outside the quotients and are compared in *From the quotients to the 𝐑-terms* below.
{#C8.6.2-6} (β) and (γ) are the items (β) and (γ) of the (LF) line, so the input (LF) in the form (LF-2) bounds them, with h_n = C_hθ̃^n per point of the history at every scale, n its birth scale.
{#C8.6.2-7} The boundary terms 𝐁 enter instead through `WILSON_IT1_LARGE_FIELD_DEPTH_2026_10_27.md` §4(e).
{#C8.6.2-8} The differences of those that are not deep are ≤ 4C_ov(2B₁ + C_XB₀C_w^♯)N₀^+(j)μ_N(P_j(Z))s^♯_j per point of a layer of the history (that note's #4.662-1), with no age factor.
{#C8.6.2-9} The deep ones that meet the component when its history lies at the layers > k_s/8 are ≤ 2C_Dk̄Ē₀2^{−k_s/16} per point of the component at the scale j.
{#C8.6.2-10} Here Ē₀ := max(E₀, B₀, C₀^𝔹, R₁) (`WILSON_IT1_LARGE_FIELD_DEPTH_2026_10_27.md` #4.578-2), since the deep terms are frozen 𝐄-, 𝐑-, and 𝐁-terms and the created terms of that note's #4.623; C₀^𝔹 is Bałaban's C₀ of LFR I (1.70). k̄ := max(k_s, j) ≤ K bounds the number of generations summed at the step j, which exceeds k_s at the steps beyond the stopping scale.
{#C8.6.2-11} The other deep terms are those of "Fine scales and old histories" below.
{#C8.6.2-12} So |n^B − n^A| ≤ (e^φ − 1)n̄, with φ the total exponent difference below and n̄ the majorant of ∫|I^A| that Bałaban's uniform bound controls.
{#C8.6.2-13} The denominators' logarithms differ by ψ := |log d^B − log d^A|.
{#C8.6.2-14} The denominator is LFR II (1.1)–(1.2) at the step j of the renormalisation (Bałaban's k), d = ∫dV′|_Λ δ_{G₀}(V′)χ exp[−g_j^{−2}A(ζ₀, U_{j,Z}(V′V_Λ))] over a parallelepiped Λ inside a cube of side 100M.
{#C8.6.2-15} By (1.10) (p.358), log d = −g_j^{−2}A(ζ₀, U₀) − I(U₀) + E_j(Λ), with E_j(Λ) = (−½d(𝐠)log g_j^{−2} + log σ₀)|Λ^{(j)}∖G₀| and −I(U₀) the logarithm of the B′-integral of (1.2).
{#C8.6.2-16} These are analytic for 𝐔 in U^c_j(Z, α_{0,j}, α_{1,j}), with ε_j replaced by O(α_{0,j} + α_{1,j}) in the bounds (p.358 l.27–33). This space contains the restrictions to Z of the points of the class, and run B's space contains those of their lifts (`WILSON_IT1_LARGE_FIELD_DEPTH_2026_10_27.md` #4.567-3).
{#C8.6.2-17} With x := g_j^{−2} and |x^B − x^A| = |δ_j|, the run-dependence is the following.
- {#C8.6.3} E_j(Λ) changes by ½d(𝐠)|log(1 + g_j²δ_j)| ≤ d(𝐠)g_j²|δ_j| per bond of Λ^{(j)}.
- {#C8.6.4} The coupling of the action changes it by |δ_j||A(ζ₀, U₀)| ≤ 3|δ_j| per plaquette of Λ^{(j)}, since 0 ≤ ζ₀ ≤ 1 and |1 − Re tr U₀(∂p)| ≤ 3 on the class.
- {#C8.6.5} The coupling inside −I + E_j(Λ) is the third dependence; it counts #C8.6.3 again, which is an overcount. It is read at fixed fine-lattice objects of one run: U₀ at the data of the point, V_Λ, Λ, ζ₀, and G₀ (LFR I (1.100)–(1.101), p.201 l.28–31; (1.2)–(1.3)). None of them involves the coupling; they are built at the run's step with the run-uniform R_j of #CP.13 and are fixed along the path of x from x^A to x^B.
  {#C8.6.5-0} The cutoff does not depend on x: per bond it is the soft test χ̄(|(1/i)log V′(b)|/(M₀ε_j)), the soft form of the cutoff |B′| < M₀g^{−1}ε_j of p.356 l.37 written in V′ = exp igB′ (p.356 l.31), and its threshold M₀ε_j is the same in both runs (#CP.13; `WILSON_IT1_LARGE_FIELD_DEPTH_2026_10_27.md` #3.92, #3.96).
    {#C8.6.5-1} So, with g := x^{−1/2}, every point of the path is Bałaban's denominator (1.1)–(1.2) at the coupling g, with the tube's cutoff, thresholds, and R at the scale j (#CP.13-1), soft through `WILSON_IT1_LARGE_FIELD_DEPTH_2026_10_27.md` #3.92–#3.95, at the point's configuration, which for run B is its lift. g lies between g^A_j and g^B_{j+1}, so ĝ_j ≤ g ≤ ρ_γ^{1/2}ĝ_j (#CP.13-1, #CP.14), and the lift lies in the run's space U^c(Z, α_{0,j}, α_{1,j}) (that note's #4.567-3), so his bounds of pp.357–358 hold there (that note's #P.1-3-0). g enters through the exponent only.
  - {#C8.6.6} For the exponent, the x-derivative of log d + xA(ζ₀, U₀) through exp[−xA] is minus the average of A(ζ₀, U_{j,Z}(V′V_Λ)) − A(ζ₀, U₀) under d's integrand.
    {#C8.6.6-1} On the support of χ̄, x times this difference is the exponent of (1.2) at g, with |B′(b)| < (1 + κ_s)M₀g^{−1}ε_j ≤ (1 + κ_s)M₀p₀(ĝ_j), as g ≥ ĝ_j: the form, bounded per bond by the boundedness of the quadratic form (p.358 l.25); the linear term, linear in B′, by (1 + κ_s) times (1.6); and V by O(g^{1−β})|Λ| (p.357 l.9–10) at the constant (1 + κ_s)M₀, M₀ not being fixed on pp.356–358 (p.378 l.13–14).
    {#C8.6.6-2} So the difference is ≤ C(M)g²p₀(ĝ_j)² per bond, with C(M) containing (1 + κ_s)²M₀². On the path ½g_j^{−2} ≤ x ≤ (3/2)g_j^{−2} (#C5.7-3, whose proviso |δ_j| ≤ ½(g^A_j)^{−2} holds a priori by #C5.7-4–#C5.7-8), so g² ≤ 2g_j², and the difference is ≤ 2C(M)g_j²p₀(ĝ_j)² per bond.
    {#C8.6.6-3} The average is taken against d's integrand, and |d| is ≥ exp(−O(1)log M|Λ|) times the integral of the integrand's modulus. This is (1.10)–(1.11) at g (the lower bound of p.358 l.25–26 with (1.11)) for the sharp cutoff and `WILSON_IT1_LARGE_FIELD_DEPTH_2026_10_27.md` #3.94–#3.94-1 for the soft one, with the upper bound from (1.9). Since |Λ| ≤ O(M⁴), this part of the x-derivative is ≤ C(M)g_j²p₀(ĝ_j)² per bond, and its change along the path is ≤ C(M)g_j²p₀(ĝ_j)²|δ_j| per bond.
  - {#C8.6.7} The test χ̄ of LFR I (1.101) (`WILSON_IT1_LARGE_FIELD_DEPTH_2026_10_27.md` §3(d)) reads the integration variable V′ at the threshold M₀ε_j, which does not depend on x (#C8.6.5-0), so it contributes nothing to the x-derivative and is the same in both runs.
- {#C8.6.8} The rest is the fine-lattice objects: U₀ (the minimiser of (1.3) on the run's fine lattice), H_{1,j}, Δ₁(ζ₀), Im∂U₀, and the argument of V. They enter d only through the action A(ζ₀, U_{j,Z}(V′V_Λ)) of its integrand.
  {#C8.6.8-1} At equal couplings `WILSON_IT1_LARGE_FIELD_DEPTH_2026_10_27.md` §4(d), *The denominator.*, compares d as a whole by the Lemma above: |log d^B − log d^A| ≤ φ_d, where φ_d ≤ h_n per point of the layers of the component's history plus h_n per bond of Λ^{(j)}, n the history's birth scale.
  {#C8.6.8-2} This is (γ) of the (LF) line, in the form (LF-2), derived at real configurations.
  {#C8.6.8-3} On the complex class that note's same bullet gives |log d^B − log d^A| ≤ |D(1)| + 4e^{c(M)}C_d(M)C_hθ̃^n. Here D(1) is the two runs' difference of the exponents at V′ = 1, bounded by the comparisons of that note's §4(b)–(c) on the class (its *The complex class.*), and e^{−c(M)} = exp(−O(1)log M|Λ|) is the lower bound of #C8.6.6-3. The factor 4e^{c(M)}C_d(M) depends on M only, and Λ has at least one point at the scale j, so the last term is ≤ C_ψh_n with C_ψ ≥ 4e^{c(M)}C_d(M) in #C8.6.9.

{#C8.6.9} So ψ ≤ C_ψΣ_{points of Λ at the scale j}(|δ_j| + h_n) + Σ_{points of the history}h_n, with C_ψ a constant of d, L, G, and M; Λ lies in the component's history at the scale j.
{#C8.6.9-1} Hence |d^B| ≥ e^{−ψ}|d^A| and |1/d^B − 1/d^A| ≤ (e^ψ − 1)/|d^A|.
{#C8.6.9-2} The numerators' cutoff χ′ = χ({|B(b)| < g_j^{−1}δ′_j}) of LFR II (1.70), with δ′_j = ĝ_jA₁p₁(ĝ_j) the same in both runs (LFR I p.183 l.2 at ĝ_j, #CP.13), is LFR I's sharp (1.82). Its radii t := δ′_j/g^A_j and t′ := δ′_j/g^B_{j+1} are ≤ A₁p₁(ĝ_j) (#CP.13-1, #CP.14), and |t′ − t| ≤ g_j²|δ_j|t, since (g^A_j/g^B_{j+1})² = 1 + δ_j(g^A_j)² and |(1 + y)^{1/2} − 1| ≤ |y|. A density bound controls its shell relative to Bałaban's positivity bound of the B-integral (LFR II p.383 l.30–34).
{#C8.6.9-3} The shell between the radii lies in the union over bonds b of {t ≤ |B(b)| < t′}. Let Q be the form of the integrand, which is positive and bounded; the marginal variance of B(b) under it is ≥ (Q_{bb})^{−1}. With the other factors bounded, each such set therefore has mass ≤ C|t′ − t|t′^{d_G−1}(‖Q_{bb}‖/2π)^{d_G/2} under the modulus of the integrand.
{#C8.6.9-4} Its form ⟨DH″_{1,j,Z}B, ζDH″_{1,j,Z}B⟩ is bounded per bond, since H″_{1,j,Z} has the random-walk expansion of PBG (3.107) with the kernel bounds (3.108) in the norms of PBG (3.42)–(3.47) (LFR II p.362 l.42–48, PBG p.416).
{#C8.6.9-5} The action term contributes the factor exp(−A) ≤ 1, and the V(Y) are bounded by (1.68)–(1.69).
{#C8.6.9-6} So the shell is ≤ Cp₁(ĝ_j)^{d_G}g_j²|δ_j| per bond relative to that bound.
{#C8.6.9-7} Hence |q^B − q^A| ≤ |n^B − n^A|/|d^B| + |n^A||1/d^B − 1/d^A| ≤ [e^ψ(e^φ − 1) + (e^ψ − 1)]q̄ ≤ 2(e+1)(φ + ψ)q̄ for φ, ψ ≤ 1. Here q̄ = q̄^A := n̄^A/|d^A| is Bałaban's majorant of run A's quotient, the 𝐓′-bound of the component's factor that his derivation (1.92)–(1.97) uses (LFR II p.389 l.13–16), and q̄^B is run B's. Otherwise φ + ψ > 1, and the triangle inequality gives |q^B − q^A| ≤ q̄^A + q̄^B ≤ (φ + ψ)(q̄^A + q̄^B).

{#C8.6.10} *The Representation of d.* In Bałaban's representation d is no separate factor after (1.49).
{#C8.6.10-1} There −log d is part of 𝐂_k, through I(U₀) "from the denominator" (LFR II p.369 l.7), and 𝐂_k is localised with the old terms into the V(Y) of (1.68), among them V(X^∼) of (1.71) (p.373 l.10–17, p.377 l.2–17).
{#C8.6.10-2} Since (1.49) is an equality for (1.1), the transformed integral of a component equals its quotient n/d, and the comparison above is that of the whole. φ is the exponent difference of the integrand with the pieces of −log d left out, and ψ is that of −log d as a whole. So d is counted once, and the bound is that of e^{φ+ψ} − 1 = e^ψ(e^φ − 1) + (e^ψ − 1) for the combined exponent.
{#C8.6.10-3} The expansion (1.92)–(1.97) needs the difference per localised piece, since the pieces of −log d in a V(Y) with Y ∖ Z^∼ ≠ ∅ lie outside the component's quotient.
{#C8.6.10-4} That comparison is `WILSON_IT1_LARGE_FIELD_DEPTH_2026_10_27.md` §4(d), *The Localised Pieces of 𝐂_k.*: the piece of −log d is the single term I(U₀) of LFR II (1.10), localised through the representation of its background, and compared at each configuration of the class as d is.

{#C8.6.11} *The exponent differences φ, ψ on the component.* Its points are those of its history: the layers Ω_m ∖ Ω_{m+1} and the large-field variables at the scales m ≤ j, with p_m(Z) scale-m points at the scale m, where p_m(Z) ≤ L^d|Z_{m+1} ∩ Z|_{m+1} for m < j and p_j(Z) ≤ L^{2d}|Z_j ∩ Z|_j.
{#C8.6.11-1} Here p_m(Z) ≥ 1 at every scale m from n − 1 up to j, where n is the birth scale of the oldest region merged into Z, whose finest layer lies at the scale n − 1 (`WILSON_IT1_LARGE_FIELD_DEPTH_2026_10_27.md` §1; §11(c), Γ_{n−1} ⊂ Z_n). With P_j(Z) the history volume of §11(c) at the scale j, Σ_mp_m(Z) ≤ (1 + L^d)P_j(Z), the term m = j alone being ≤ L^dP_j(Z).
{#C8.6.11-2} At each of these points the exponent difference is ≤ 𝒟_m + h_n in the class norm, with 𝒟_m of §8.4. The frozen terms of the layer have age m − i for the generation i and are evaluated at U_m-type configurations (CRE p.280 l.15–17), so RΔ^c gives D_m ≤ D^♭_m. The other terms are the carried 𝐑-differences S_{m−1}, the coupling with (1.6), the depth terms, and (LF), which is ≤ h_n.
{#C8.6.11-3} At the points of Λ, at the scale j, the coupling part of the exterior part W_ext of 𝐂_j adds ≤ max_{n−1≤l≤j}|δ_l| + C_βD^♭_{n−1} (`WILSON_IT1_LARGE_FIELD_DEPTH_2026_10_27.md` §4(d), *The couplings of W_ext.*, with C_wcε̂² ≤ 1). This is ≤ (1 + C_β)max_{n−1≤m≤j}𝒟_m, since |δ_l| ≤ 𝒟_l for C ≥ 1 and D^♭_{n−1} ≤ 𝒟_{n−1}.
{#C8.6.11-4} So φ + ψ ≤ (3 + C_ψ)Σ_{m=n−1}^{j}p_m(Z)(𝒟_m + h_n) + (1 + C_β)p_j(Z)max_{n−1≤m≤j}𝒟_m, with the collar points of #C8.6.16 counted at m = j. For the histories where (LF) enters n > k_s/8 (#C8.6.24–#C8.6.24-2), so 𝒟_m ≤ e^{½C_P(j−m)}𝒟_{[j]} and h_n ≤ 𝒟_n ≤ e^{½C_P(j−n)}𝒟_{[j]}. Since j − m + 1 ≤ P_j(Z) for n − 1 ≤ m ≤ j, φ + ψ ≤ C_nP_j(Z)²e^{½C_PP_j(Z)}𝒟_{[j]} with C_n := 2(1 + L^d + 3^d)(4 + C_ψ + C_β).
{#C8.6.11-5} The factor is paid by the component's weight.
{#C8.6.11-6} By (11.4) and (11.2) at the scale j, κ^tr_j(Z) ≥ κ̂_j(Z) + P^c_j(Z) + C_PP_j(Z) + ½G_j(Z), so the component's factor exp(−κ^tr_j(Z) − 2p₀(ĝ_{j(Z)})) in (1.79) is ≤ exp(−C_PP_j(Z))·exp(−κ̂_j(Z) − P^c_j(Z) − 2p₀(ĝ_{j(Z)})).
{#C8.6.11-7} In the last factor κ̂_j(Z) ≥ 0 satisfies (1.80), and P^c_j(Z) pays the integrand's history cost as in §11(c).
{#C8.6.11-8} Bałaban's derivation of the quotient bound (2.31) from (1.89) (LFR II (1.89)–(1.97)) uses of κ only κ ≥ 0, which is (1.89) (p.387 l.30–33), and (1.80).
{#C8.6.11-9} So for either run q̄ improves to e^{−C_PP_j(Z)}q̄, and |q^B − q^A| ≤ 2(e + 1)(φ + ψ)e^{−C_PP_j(Z)}q̄ ≤ 2(e + 1)C_n𝒟_{[j]}q̄, because P²e^{−½C_PP} ≤ (4/(eC_P))² ≤ 1 for C_P ≥ 2.
{#C8.6.11-10} The boundary terms add ≤ C^B_n(𝒟^∗_j + C_hθ̃^{k_s/8})P_j(Z)² to φ (`WILSON_IT1_LARGE_FIELD_DEPTH_2026_10_27.md` #4.662–#4.663), C^B_n := 8c_{μN}(1 + L^d)C_ov(2B₁ + C_XB₀C_w^♯)(C_B + C_ℂ′)N₀^+(j), with c_{μN}, C_w^♯, C_ℂ′, N₀^+(j), and C_ov := 2 of that note's #4.660-2, #4.662-1, #4.650-1, #4.638, and #4.629-1. C^B_n depends on j only through N₀^+(j).
{#C8.6.11-11} The variation of the term V(Z^∼) (Bałaban's V(X^∼) of (1.71) for X = Z) at the points of its collar Z^∼ ∖ Z, which lie outside the history, adds ≤ C_VC_hθ̃^{k_s/8}P_j(Z), for the following reasons.
- {#C8.6.12} On the class V(Z^∼) is bounded by (1.69), O(1)Σ_l|Γ^0_l ∩ Z^∼|.
- {#C8.6.13} Cauchy's estimate on the disc of `WILSON_IT1_LARGE_FIELD_DEPTH_2026_10_27.md` (its #4.301-2.2) bounds the variation by 2r times this bound, with r the supremum of d̄/ρ over the collar.
  {#C8.6.13-1} The collar lies in Λ_j, at the layer j > k_s/8: Z^∼ is a component of the neighbourhood of the large-field region Λ_j^c, and each component of Λ_j^c has its own (p.379 l.24–25 with (1.71)), so the collar meets no other component.
  {#C8.6.13-2} Hence r ≤ C_hθ̃^{k_s/8} by that note's §4(e), "Into the quotients".
- {#C8.6.14} The points of the old determining set in Z^∼ are those of the history, ≤ (1 + L^d)P_j(Z), and those of the collar.
  {#C8.6.14-1} The collar is one layer of the cubes of which the large-field region is a union (CRE p.245 l.41–43), so each of its cubes touches a cube of Z, and |Z^∼ ∖ Z|_j ≤ (3^d − 1)|Z_j ∩ Z|_j ≤ (3^d − 1)L^{−d}P_j(Z) (§11(c)).
- {#C8.6.15} So C_V := 2O(1)(1 + L^d + 3^d), with O(1) the constant of (1.69).
- {#C8.6.16} The old terms at the collar points also carry their own two-run differences, part (i) of that note's §4(d), *The functions of the configurations.*, which is ≤ 𝒟_j per point, since the collar lies in Ω_j at the scale j.
  {#C8.6.16-1} These points enter φ with the history points at m = j, and their number ≤ (3^d − 1)L^{−d}P_j(Z) ≤ 3^dP_j(Z) is the 3^d in C_n.

{#C8.6.17} The deep terms meeting a young component add ≤ 2L^dC_Dk̄Ē₀2^{−k_s/16}P_j(Z).
{#C8.6.17-1} With Pe^{−C_PP} ≤ P²e^{−C_PP} ≤ 1 for P ≥ 1 and C_P ≥ 2, |q^B − q^A| gains 2(e + 1)[C^B_n𝒟^∗_j + C^θ_nθ̃^{k_s/8} + 2L^dC_Dk̄Ē₀2^{−k_s/16}]q̄, C^θ_n := (C^B_n + C_V)C_h.

{#C8.6.18} *From the quotients to the 𝐑-terms.* The terms 𝐑(X, V) of LFR I (0.5)–(0.6) are built from the quotients by Bałaban's expansion (1.92)–(1.97) of LFR II.
{#C8.6.18-1} There the 𝐓′-bound of each renormalised component X_{j_h}, times the weight exp((1 + β + β/(3·2^d))κM^{−d}|X_{j_h}|) of (1.93), is ≤ exp(−(3/2)p₀(ĝ_k)) under the condition of p.389 l.16, at ĝ_k in the tube (#CP.13): "The product over h there is estimated by ∏_{h=1}^q exp2κ(100R_k)^d" (p.389 l.13–14). The sum over the families of components converges by (1.96).
{#C8.6.18-2} Each renormalised component's operation is interpolated, 𝐓′_ς := 𝐓′^A + ς(𝐓′^B − 𝐓′^A) with ς ∈ [0, 1], named apart from Bałaban's t(Y) and his large-field functions ζ, ζ₁. Every interpolated factor obeys the bound that both runs' factors obey. The derivative in ς is the same sum with one factor replaced by the two-run difference, which is ≤ 2(e + 1)[C_n𝒟_{[j]} + C^B_n𝒟^∗_j + C^θ_nθ̃^{k_s/8} + 2L^dC_Dk̄Ē₀2^{−k_s/16}] times that factor's bound.
{#C8.6.18-3} The factors V(Y) of (1.91) are interpolated alongside, V_ς(Y) := V^A(Y) + ς(V^B(Y) − V^A(Y)).
{#C8.6.18-4} These obey (1.68)–(1.69) whenever both runs' V(Y) do, since those bounds are bounds of the modulus and so hold for convex combinations.
{#C8.6.18-5} The derivative with respect to them replaces one factor V(Y) of (1.91) by V^B(Y) − V^A(Y), or one exponent t(Y)V(Y) by t(Y)(V^B(Y) − V^A(Y)) with t(Y) ∈ [0, 1]. V^B(Y) − V^A(Y) is (γ) of the (LF) line.
{#C8.6.18-6} The comparison holds for 𝐓′ applied to the integrand F = ΠV(Y)exp Σt(Y)V(Y) of (1.91), not only to 𝐓′1: the V(Y) depend on B and V″ localised in Y (p.377 l.7–8), and the sum of (1.71) acts on the last exponential of (1.72) (p.379 l.23–24).
{#C8.6.18-7} At fixed V_ς(Y), F is common to both runs' integrands, so the exponent comparison above holds with the integrands multiplied by F and gives the same relative bound with the factor sup|F|, which is the bound of F(X′) that (1.92) uses.
- {#C8.6.19} *The deep V(Y) in a young polymer.* Let every component of Bałaban's Z in the polymer X′ be young: the X_{j_h} and the second-class components Y_i that X′ contains (p.389 l.27–28).
  {#C8.6.19-1} A factor V(Y) of X′ can still be deep, through a point of Y at a layer ≤ k_s/8 that lies in Λ_j^c but outside Z, in a component of Λ_j^c that is not one of those making up Z (LFR I p.177 l.33).
  {#C8.6.19-2} Its constituents are bounded in `WILSON_IT1_LARGE_FIELD_DEPTH_2026_10_27.md` §4(e), *Deep V(Y) in a Young Polymer*, through the weights of LFR II (1.66) and the crossing of their domain X, with the run difference ≤ r_D + r_E + r_C = 2e²(C_{rD} + C_{rE} + C_{rC})2^{−k_s/16} times the factor's bound, under σ_V ≥ 1 on Bałaban's R. With the factor and the exponent of one Y this adds 4e²(C_{rD} + C_{rE} + C_{rC})2^{−k_s/16} to the bracket below.
  {#C8.6.19-3} The polymers with an old component are those of "Fine scales and old histories" below, or, for an old second-class component, are carried on with it as deep terms (that note's §4(e), "Deep terms").
- {#C8.6.20} *The non-deep V(Y).* By Cauchy's estimate on the disc of that note's #4.301-2.2, the variation of V(Y) at the two runs' configurations is ≤ 2r(Y) times the factor's bound in (1.92), with r(Y) of its #4.301-3.
  {#C8.6.20-1} Every point of Y lies at a layer > k_s/8, so r(Y) ≤ C_hθ̃^{k_s/8} by that note's §4(e), "Into the quotients".
  {#C8.6.20-2} The bound is per factor, through the supremum r(Y), so no count of the domains at a point enters.
- {#C8.6.21} *The Own Differences of the V(Y).* The V(Y) also differ by the old terms' own two-run differences, part (i) of that note's §4(d), *The functions of the configurations.* The re-summation is linear in the old terms, and each of its terms is bounded through the bound of its one old term (RG II (1.24)–(1.29), as that bullet reads them). So the re-summation of the differences, with one run's re-summing operator, is ≤ 𝒟^V_j times the factor's bound in (1.68).
  {#C8.6.21-1} Here 𝒟^V_j := max_{k_s/8−1<m≤j}(D_m + S_{m−1}) + C^B_V(𝒟^∗_j + C_hθ̃^{k_s/8}), with C^B_V := 2(C_B + C_ℂ′ + C_ℂ), bounds the old terms' differences relative to their bounds. D_m bounds the frozen 𝐄-terms at the points of Y of the layer m, with their age factors, and the carried 𝐑-differences S_{m−1} bound the old 𝐑-terms (§8.4).
    {#C8.6.21-1-1} The 𝐁-terms, each relative to its own bound, are bounded by b_i ≤ 2s^♯_i ≤ 2s^♯_j (that note's #4.660, #4.660-3), and the created terms of its #4.650 by (C₀^𝔹/B₀)c_ν ≤ s^♯_j in the units B₀ or by c_ν ≤ 2C_ℂ(𝒟^∗_j + C_hθ̃^{k_s/8}) relative to LFR I (1.70) (its #4.649-1, #4.650-1).
  {#C8.6.21-2} Every point of Y lies at a layer > k_s/8 − 1, so the indices are those that §8.7 controls.
  {#C8.6.21-3} The differences are evaluated at run A's own pair of the chain, and on the complex class the 𝐄-part rests on the class bound (5.1c) there (§5), with the near domains at a finer layer of §5 where (N) fails.
  {#C8.6.21-4} The factor and the exponent of one Y contribute ≤ 2𝒟^V_j times the bound of F(X′): the factor V(Y) changes by ≤ 𝒟^V_j times its bound (1.68), and the exponent t(Y)V(Y) by ≤ 𝒟^V_jα ≤ 𝒟^V_j, since t(Y) ∈ [0, 1] and α ≤ 1. 𝒟^V_j is an unweighted maximum, of the type of 𝒟^∗_j, and §8.7 absorbs it in the same way.
  {#C8.6.21-5} The difference of the two runs' re-summing operators is part (iii) of that bullet; it uses the walk-factor inequality (W-δ) stated there, derived in `WILSON_IT1_WALK_FACTOR_DIFFERENCE_2026_10_28.md`.
- {#C8.6.22} *The count of the factors.* With |t(Y)V(Y)| ≤ α ≤ 1, the factor and the exponent of one Y contribute ≤ 4r(Y) times the bound of F(X′).
  {#C8.6.22-1} The number of domains, |𝐃| ≤ e^{|𝐃|}, is absorbed by eα in place of α in (1.92)–(1.93), which the smallness of α allows (α "can be chosen arbitrarily small for γ small enough", p.377 l.14; p.388 l.34).
  {#C8.6.22-2} So the factors V(Y) add 4C_hθ̃^{k_s/8} + 4e²(C_{rD} + C_{rE} + C_{rC})2^{−k_s/16} + 2𝒟^V_j to the bracket, the middle term from the deep ones.

{#C8.6.23} The number q of factors is absorbed by q ≤ e^q, which changes the condition of p.389 l.16 to −2(1 + β₀)^{−1}p₀(ĝ_j) + 2 + 2κ(100R_j)^d ≤ −(3/2)p₀(ĝ_j), true for ḡ small, as R_j < L(log ĝ_j^{−2})^r (#CP.13) and p₀ > rd.
{#C8.6.23-1} So |𝐑^B(X) − 𝐑^A(X)| ≤ {2(e + 1)[C_n𝒟_{[j]} + C^B_n𝒟^∗_j + C^θ_nθ̃^{k_s/8} + 2L^dC_Dk̄Ē₀2^{−k_s/16}] + 4C_hθ̃^{k_s/8} + 4e²(C_{rD} + C_{rE} + C_{rC})2^{−k_s/16} + 2𝒟^V_j}R₁′g_j^{κ₀}exp(−κd_j(X)), with R₁′ the constant of (2.31) given by Bałaban's derivation under this condition and with eα for α, uniform in j.

{#C8.6.24} *Fine scales and old histories.* (LF) enters only at coarse scales.
{#C8.6.24-1} For a component renormalised at a step j ≤ k_s/4 the triangle inequality with the inductive bound (2.31) (CRE p.260 l.24), |𝐑^{(j)}(X, (𝐔, 𝐉))| ≤ g_j^{κ₀}exp(−κd_j(X)), gives |𝐑^B(X) − 𝐑^A(X)| ≤ 2R₁g_j^{κ₀}exp(−κd_j(X)), with R₁ ≥ 1, which p.263 l.29–30 allows. Here g_j^{κ₀} ≤ (3bK/4 − C)^{−κ₀/2} by Lemma 2.1(i), since K − j ≥ K − k_s/4 ≥ 3K/4.
{#C8.6.24-2} For a component renormalised at j > k_s/4 whose history reaches a scale ≤ k_s/8, P_j(Z) ≥ j − k_s/8 ≥ k_s/8, and the improved bound e^{−C_PP_j(Z)}q̄ of each run, carried through the expansion as above, gives ≤ 2e^{−C_Pk_s/8}R₁′g_j^{κ₀}exp(−κd_j(X)).
{#C8.6.24-3} Let ν_j be these bounds per point of the generation j, together with L⁴R₁′[2(e + 1)(C^θ_nθ̃^{k_s/8} + 2L^dC_Dk̄Ē₀2^{−k_s/16}) + 4C_hθ̃^{k_s/8}](100MR_j)^dg_j^{κ₀} from the boundary terms and the factors V(Y) of the remaining components below. ν_j also contains 4e²(C_{rD} + C_{rE} + C_{rC})L⁴R₁′2^{−k_s/16}(100MR_j)^dg_j^{κ₀} from the deep V(Y) in the young polymers (*The deep V(Y) in a young polymer.* above), and C″_RK^{1−κ₀/2} from the 𝐑-terms' variation group at the old ages of the step j − 1 (§10.5).
{#C8.6.24-4} Then Σ_{j≤K}ν_j ≤ C_νw_K, with
- {#C8.6.25} w_K := (K + 1)(θ̃^{k_s/8} + 2^{−k_s/16}) + μ_K and μ_K := K^{2−κ₀/2}ℓ_K;
- {#C8.6.26} C_ν a constant of R₁, R₁′, b, C_P, C^θ_n, C_h, C_D, Ē₀, C_{rD} + C_{rE} + C_{rC}, C″_R, and Σ_g := sup_KΣ_{j≤K}(100MR_j)^dg_j^{κ₀}, which is finite (§8.4).
  {#C8.6.26-1} C_ν = C_ν(j(C)) depends on j(C) through C_h, which `WILSON_IT1_LARGE_FIELD_DEPTH_2026_10_27.md` §4(b)–(c), "The result", states as a constant of j(C), both directly and through C^θ_n.
  {#C8.6.26-2} The dependence is at most L^{Cε₀j(C)} times a polynomial in j(C), with C a constant of the exponents: the exponential factor comes from the factor (εL^k/ε)^{ε₀} = L^{kε₀} ≤ L^{j(C)ε₀}L^{8nε₀} of the layers k < 8n + j(C) in the fine side of the large-field note's §4(d) (*The rate of (iv) and (α) in the layer.* and the ratios of (ii)), and the polynomial one from the absorption of the steps beyond the stopping scale below.
  {#C8.6.26-3} At fixed j(C) the summability in K is unaffected.

{#C8.6.27} There are ≤ K generations of the first kind, each ≤ 2R₁(3bK/4 − C)^{−κ₀/2}, which together are ≤ Cμ_K.
{#C8.6.27-1} The old-age 𝐑 sources sum to ≤ C″_RK^{2−κ₀/2} ≤ C″_Rμ_K.
{#C8.6.27-2} The second kind sums to ≤ 2R₁′Σ_ge^{−C_Pk_s/8} ≤ 2R₁′Σ_g2^{−k_s/16}, since C_P ≥ 2 and e^{−1/4} < 2^{−1/16}.
{#C8.6.27-3} The boundary terms and the factors V(Y), the deep ones included, sum to ≤ C(K + 1)(θ̃^{k_s/8} + 2^{−k_s/16}), since k̄ ≤ K. The remaining components, renormalised at j > k_s/4 with the whole history at the scales > k_s/8, satisfy #C8.6.23-1, and only there does (LF) enter, through h_n in 𝒟_{[j]}.
{#C8.6.27-4} At the steps j ∈ (k_s, K] the births still satisfy n > k_s/8, but j < 8n can fail, and only j ≤ K = k_s + j(C) < 8n + j(C) holds.
{#C8.6.27-5} The factors polynomial in the step that `WILSON_IT1_LARGE_FIELD_DEPTH_2026_10_27.md` §4(b)–(d) absorbs with j < 8n obey j^p ≤ (8n + j(C))^p ≤ (1 + j(C))^p(8n)^p, so the absorption holds there with C_h multiplied by (1 + j(C))^p, p the largest power absorbed, and the polylogarithms in K obey the same bound with K < 8n + j(C).
{#C8.6.27-6} Hence, for a component renormalised at step j,

{#C8.6.28} (8.4) |𝐑^{B}(X) − 𝐑^{A}(X)| ≤ [C_R(100MR_j)^d𝒟_{[j]}g_j^{κ₀} + C^B_R(100MR_j)^d𝒟^∗_jg_j^{κ₀} + C^V_R(100MR_j)^d𝒟^V_jg_j^{κ₀} + ν_j]exp(−κd_j(X)), with 𝒟_{[j]} of #C8.4.1-4.

{#C8.6.29} This is the inequality (G″), with C_R := 2(e+1)C_nL⁴R₁′, C^B_R := 2(e+1)C^B_nL⁴R₁′ = C^B_{R,1}N₀^+(j), where C^B_{R,1} := C^B_R/N₀^+(j) is independent of j (#C8.6.11-10), and C^V_R := 2L⁴R₁′. 𝒟^V_j is that of #C8.6.21-1, and 𝒟^∗_j is the boundary terms' source of `WILSON_IT1_LARGE_FIELD_DEPTH_2026_10_27.md` §4(e), the running maximum over k_s/8 < i ≤ j of D_{i−1} + S_{i−1} + g_{i−1}²|δ_{i−1}| + e_i + max_{k_s/8<l<i}d_l.
{#C8.6.29-1} The factor (100MR_j)^d is at most (200ML)^d(log g_j^{−2})^{rd} (#CP.14), kept as slack, and is beaten in §8.4's sums by g_j^{κ₀}.

### 8.7 The Solution of the Recursion {#CS8.7}

{#C8.7.1} The unknowns are the class norms d_i (i = 1, …, K, with d_1 ≤ 2 from §8.2(d)), the 𝐑-differences d^R_i, and the coupling differences δ_i, on all shared scales up to the unit scale K, the stopping scale k_s = K − j(C) among them. The coupling differences δ_i = Σ_{l>i}Δβ_l run to K, and the steps beyond k, which both runs perform for the coupling prescription, obey (8.3) and (8.5) in the same way.
{#C8.7.1-1} The inequalities are (8.3), (8.5), |δ_i| ≤ C_βΣ_{l>i}d_l (δ_K = 0, §8.3), the depth sources e_i ≤ C_eθ̃^i, and h_i = C_hθ̃^i, through which the input (LF) enters (§8.4). The depth sources are bounded in §9, §10.5, and, at the large-field backgrounds of the young pairs, `WILSON_IT1_LARGE_FIELD_DEPTH_2026_10_27.md` §5(d), whose source C′_e is relative to the class norm of the dev insertions, so C_e is enlarged by C′_e times that norm's bound. Here θ̃ := max((1+θ)/2, L^{−γ_H}, L^{−(1−2ε₀)/3}, L^{−(1−ε₀)/4}, L^{−θ_V/8}) < 1, with θ_V := β′/(2(4+β′)) of §5.
{#C8.7.1-2} The term L^{−θ_V/8} puts the variation groups (iv) and (α) of `WILSON_IT1_LARGE_FIELD_DEPTH_2026_10_27.md` (its #4.443, #4.443-2) into the form of h_n (its #4.455.1).
{#C8.7.1-3} This note and that one use θ̃ only through lower bounds on it and through θ̃ < 1, so its size changes only constants: C_τ, C_s, C_μ, C_∗, C″_μ, C_m, C′_m, C_S″, C_a, the threshold k_*(j(C), ḡ) of §6.2 (*The threshold.*, #C6.2.19), and the constants of the absorptions by the slack.
{#C8.7.1-4} The constants are continuous in θ̃ on a compact range of θ̃ that excludes 1, L^{−β′}, and L^{−1/3}, so they stay bounded uniformly in K and in γ small. Every term of the maximum stays below a fixed number less than 1: (1+θ)/2 ≤ (3 + L^{−β′})/4 once ε^* ≤ (1 − L^{−β′})/2. (T1) implies this, since C_τ ≥ θ̃^{−1}(1 − L^{−β′}/θ̃)^{−1} = (θ̃ − L^{−β′})^{−1} > (1 − L^{−β′})^{−1}, so ε^* ≤ 1/(2C_τ) < (1 − L^{−β′})/2. Below, θ̃ ≥ (1 + L^{−β′})/2 exceeds L^{−β′} by (1 − L^{−β′})/2, and θ̃ ≥ L^{−(1−2ε₀)/3} exceeds L^{−1/3} by the factor L^{2ε₀/3}.
{#C8.7.1-5} Put ℓ_K := (log(bK + ḡ^{−2}))^{rd+2p₀} and m_i := iθ̃^i + w_K, with μ_K and w_K of #C8.6.25. For ḡ small, ℓ_K bounds (100MR_j)^d, p₀(ĝ_j)², and c_j at every shared scale: ĝ_j^{−2} ≤ ḡ^{−2} + b′K + C_W ≤ (3/2)(bK + ḡ^{−2}) ≤ (bK + ḡ^{−2})² (#CP.13; b′ ≤ ρ_γb ≤ (3/2)b, BETA_FUNCTION_WILSON_LOOPS.md #B2.2.155-1; C_W ≤ ½ḡ^{−2}), so log ĝ_j^{−2} ≤ 2log(bK + ḡ^{−2}), while R_j < L(log ĝ_j^{−2})^r (#CP.13), g_j ≤ 1, and log(bK + ḡ^{−2}) ≥ log ḡ^{−2}.
{#C8.7.1-6} Substituting (8.5) and the coupling bound into (8.3) gives d ≤ 𝒯d + s with the positive, monotone, and positively homogeneous operator

{#C8.7.2} (𝒯u)_{i+1} := ε^*[D_i[u] + C_SΣ_{j≤i}c_j(𝒟′_{[j]}[u] + D_{j−1}[u]) + C_SΣ_{j≤i}c^B_j𝒟^{∗′}_j[u] + C_SΣ_{j≤i}c^V_j𝒟^{V′}_j[u]] + C_gε^*g_i²C_βΣ_{l>i}u_l, D_i[u] := Σ_{j≤i}L^{−β′(i−j)}u_j, D^♭_m[u] := Σ_{j≤m}q^{m−j}u_j, 𝒟′_{[j]}[u] := max_{k_s/8−1<m≤j}e^{−½C_P(j−m)}(D^♭_m[u] + CC_βΣ_{l>m}u_l), 𝒟^{∗′}_j[u] := max_{k_s/8<m≤j}(D_{m−1}[u] + g_{m−1}²C_βΣ_{l≥m}u_l + max_{k_s/8<l<m}u_l), 𝒟^{V′}_j[u] := max_{k_s/8−1<m≤j}D_m[u] + C^B_V𝒟^{∗′}_j[u],

{#C8.7.3} and the source s_{i+1} := e_{i+1} + ε^*C_S[Σ_{j≤i}c_jmax_{k_s/8−1<m≤j}e^{−½C_P(j−m)}(e_m + h_m) + Σ_{j≤i}c^B_jmax_{k_s/8<m≤j}e_m + Σ_{j≤i}c^V_jC^B_V(max_{k_s/8<m≤j}e_m + C_hθ̃^{k_s/8}) + C_νw_K], s_1 := 2.
{#C8.7.3-1} In the weighted norm ‖u‖_m := sup_iu_i/m_i the operator is small. Since θ̃ > L^{−β′}, Σ_{j≤i}L^{−β′(i−j)}m_j ≤ (1 − L^{−β′}/θ̃)^{−1}m_i. In the same way Σ_{j≤i}q^{i−j}m_j ≤ (1 − L^{−1/3}/θ̃)^{−1}m_i, since q < L^{−1/3} < L^{−(1−ε₀)/4} ≤ θ̃, so D^♭_m[u] ≤ (1 − L^{−1/3}/θ̃)^{−1}‖u‖_mm_m. The contraction of §8.3 is that of D at the rate L^{−β′}, in the first term of 𝒯; D^♭ enters only through 𝒟′, as a linear functional bounded in the weighted norm.
{#C8.7.3-2} Since Σ_{l>i}lθ̃^l ≤ 2(1−θ̃)^{−2}(i+1)θ̃^{i+1}, g_i²(K − i) ≤ b^{−1} by Lemma 2.1(i), and g_i² ≤ 1, g_i²Σ_{l>i}m_l ≤ g_i²[2(1−θ̃)^{−2}(i+1)θ̃^{i+1} + (K − i)w_K] ≤ (2(1−θ̃)^{−2} + b^{−1})m_{i+1}. Next Σ_{j≤i}c_jm_j ≤ C_Σw_K + Σ_{j≤K/2}c_jjθ̃^j + Σ_{j>K/2}c_jjθ̃^j ≤ C_Σw_K + C(bK/2)^{−κ₀/2}ℓ_K + C_ΣKθ̃^{K/2}: the fine scales pay with c_j ≤ C_Rℓ_K(ḡ^{−2} + bK/2 − C)^{−κ₀/2}, and the coarse scales with θ̃^j.
{#C8.7.3-2-1} The last two terms are ≤ C″_μμ_K ≤ C″_μw_K, with C″_μ a constant of C_Σ, b, θ̃, and κ₀, so Σ_{j≤i}c_jm_j ≤ C_mw_K ≤ C_mm_{i+1} with C_m := C_Σ + C″_μ. For the coupling term of 𝒟′, Σ_{l>m}m_l ≤ 2(1−θ̃)^{−2}(m+1)θ̃^{m+1} + (K − m)w_K.
{#C8.7.3-3} With the weight, e^{−½C_P(j−m)}(K − m) ≤ (K − j) + 1 and e^{−½C_P(j−m)}(m+1)θ̃^{m+1} ≤ (j+1)θ̃^{j+1}.
{#C8.7.3-4} So Σ_{j≤i}c_jmax_{k_s/8−1<m≤j}e^{−½C_P(j−m)}Σ_{l>m}m_l ≤ 2(1−θ̃)^{−2}C_mw_K + w_KΣ_{j≤K}c_j(K − j + 1) ≤ C′_mw_K.
{#C8.7.3-5} The last sum is finite and uniform in K: c_j(K − j + 1) ≤ C_R(100MR_j)^dg_j^{κ₀−2}(g_j²(K − j) + g_j²) ≤ C_R(100MR_j)^dg_j^{κ₀−2}(b^{−1} + 1) by Lemma 2.1(i), and g_j^{κ₀−2} times a power of log g_j^{−2} is summable over j for κ₀ > 4.
{#C8.7.3-6} The maxima in 𝒟′_{[j]}[u] are bounded in the weighted norm by their scale-j values: e^{−½C_P(j−m)}m_m ≤ m_j for m ≤ j (#C8.4.1-4), since (e^{−½C_P}/θ̃)^{j−m} ≤ 1.
{#C8.7.3-7} The unweighted maxima in 𝒟^{∗′}_j[u] are ≤ (1 + C_μ)C_∗‖u‖_mm_j, with C_∗ := (1 − L^{−β′}/θ̃)^{−1} + 2C_β(2(1−θ̃)^{−2} + b^{−1} + 1) + 1 and C_μ := θ̃^{−1}max(1, c(θ̃)), c(θ̃) := sup_{x≥0}xθ̃^x = 1/(e log(1/θ̃)), a constant of θ̃ alone.
{#C8.7.3-8} Each part at m > k_s/8 is ≤ C_∗‖u‖_m max_{k_s/8−1≤l≤m}m_l by the bounds above. The coupling part is ≤ C_β(2(1−θ̃)^{−2} + b^{−1} + 1)‖u‖_mm_m, through Σ_{l≥m}lθ̃^l ≤ 2(1−θ̃)^{−2}mθ̃^m and g_{m−1}²(K − m + 1) ≤ b^{−1} + g_{m−1}².
{#C8.7.3-9} For such l put x₀ := max(k_s/8 − 1, 0) and l = x₀ + t, t ≥ 0.
{#C8.7.3-10} Then lθ̃^l ≤ θ̃^{x₀}(x₀ + tθ̃^t) ≤ θ̃^{x₀}(x₀ + c(θ̃)) ≤ θ̃^{−1}θ̃^{k_s/8}(k_s/8 + c(θ̃)) ≤ C_μ(k_s + 1)θ̃^{k_s/8} ≤ C_μw_K, and so max_{k_s/8−1≤l≤j}m_l ≤ (1 + C_μ)w_K ≤ (1 + C_μ)m_j.
{#C8.7.3-11} c^B_j = (C^B_{R,1}/C_R)N₀^+(j)c_j (#C8.6.29). Σ_jN₀^+(j)c_j ≤ C^N_Σ, finite and uniform in K as in #C8.4.5, N₀^+(j) being a double logarithm of g_j^{−2}. At the fine scales j ≤ K/2, log g_j^{−2} ≤ 2log(ḡ^{−2} + bK) (#CP.14) gives N₀^+(j) ≤ 1 + 2(log(32L(L + 1)) + 2log(2log(ḡ^{−2} + bK)))/log L ≤ C_N′K, with C_N′ a constant of L, b, and ḡ.
{#C8.7.3-11-1} So the proof of #C8.7.3-2 with N₀^+(j)c_j for c_j gives Σ_{j≤i}N₀^+(j)c_jm_j ≤ C^N_mm_{i+1}, C^N_m := C^N_Σ + C^N_μ, the fine scales' term C_N′K·C(bK/2)^{−κ₀/2}ℓ_K and the coarse scales' C^N_ΣKθ̃^{K/2} being ≤ C^N_μμ_K, with C^N_μ a constant of C^N_Σ, C_N′, b, θ̃, and κ₀. Hence Σ_{j≤i}c^B_jm_j ≤ (C^B_{R,1}/C_R)C^N_mm_{i+1} and Σ_jc^B_j ≤ (C^B_{R,1}/C_R)C^N_Σ.
{#C8.7.3-12} In the same way D_m[u] ≤ C_∗‖u‖_mm_m, and the maximum over k_s/8 − 1 < m ≤ j gives 𝒟^{V′}_j[u] ≤ (1 + C^B_V)(1 + C_μ)C_∗‖u‖_mm_j; with c^V_j = (C^V_R/C_R)c_j, Σ_{j≤i}c^V_j𝒟^{V′}_j[u] ≤ (1 + C^B_V)(1 + C_μ)C_∗(C^V_R/C_R)C_m‖u‖_mm_{i+1}.
{#C8.7.3-13} Every component of 𝒯u at i+1 is bounded by quantities of size m_i ≤ θ̃^{−1}m_{i+1}, since m_{i+1} ≥ θ̃m_i.
{#C8.7.3-14} Hence ‖𝒯‖_m ≤ ε^*C_τ with C_τ := θ̃^{−1}[(1 − L^{−β′}/θ̃)^{−1}(1 + C_SC_m) + (1 − L^{−1/3}/θ̃)^{−1}C_SC_m + CC_βC_SC′_m + C_SC_∗(1 + C_μ)(C^B_{R,1}/C_R)C^N_m + C_SC_∗(1 + C^B_V)(1 + C_μ)(C^V_R/C_R)C_m + C_gC_β(2(1−θ̃)^{−2} + b^{−1})]. The first two terms count D_i[u] and the two D-terms of the c_j-sum, D_{j−1}[u] at the rate L^{−β′} and D^♭_m[u] at the rate q.
{#C8.7.3-14-1} Here ε^* = ε^*_γ (#C8.3.3-2) does not depend on K and is a constant of L, b, ḡ, and Bałaban's constants. Under (T1) ‖𝒯‖_m ≤ 1/2.
{#C8.7.3-15} The system is finite, so ‖d‖_m < ∞, and d ≤ ‖d‖_mm. Since 𝒯 is monotone and positively homogeneous, ‖d‖_m ≤ ‖𝒯‖_m‖d‖_m + ‖s‖_m, hence ‖d‖_m ≤ 2‖s‖_m.
{#C8.7.3-16} The source satisfies ‖s‖_m ≤ C_s := max(2/θ̃, C_e + ε^*C_S((C_e + C_h)C_m + C_e(C^B_{R,1}/C_R)C^N_Σ + C^B_V(C_e + C_h)(C^V_R/C_R)C_Σ + C_ν)). The first entry covers s_1 = 2 ≤ (2/θ̃)m_1. The second follows by the same sums, with max_{m>k_s/8}e_m ≤ C_eθ̃^{k_s/8} ≤ C_ew_K, Σ_jc_j ≤ C_Σ, and w_K ≤ m_{i+1} for the 𝐑-sector source.
{#C8.7.3-17} Therefore, for every shared scale i,

{#C8.7.4} (8.6) d_i ≤ 2C_s(iθ̃^i + w_K), D_i ≤ 2C_s(1 − L^{−β′}/θ̃)^{−1}(iθ̃^i + w_K), D^♭_i ≤ 2C_s(1 − L^{−1/3}/θ̃)^{−1}(iθ̃^i + w_K), S_i ≤ C_S″w_K, |δ_i| ≤ 2C_sC_β[2(1−θ̃)^{−2}(i+1)θ̃^{i+1} + (K + 1 − i)w_K],

{#C8.7.5} with C_S″ := C_S[2C_s((1 − L^{−1/3}/θ̃)^{−1} + (1 − L^{−β′}/θ̃)^{−1}θ̃^{−1})C_m + 2C_sCC_βC′_m + (C_e + C_h)C_m + (C^B_{R,1}/C_R)(2(1 + C_μ)C_∗C_sC^N_m + C_eC^N_Σ) + (C^V_R/C_R)(2(1 + C^B_V)(1 + C_μ)C_∗C_sC_m + C^B_V(C_e + C_h)C_Σ) + C_ν] from (8.5). The first term is the D^♭-part of 𝒟′_{[j]} and D_{j−1}, with m_{j−1} ≤ θ̃^{−1}m_j, the second the coupling part of 𝒟′_{[j]}, the third its e- and h-parts, and the terms with C^B_{R,1}/C_R and C^V_R/C_R the sectors Σ_jc^B_j𝒟^{∗′}_j and Σ_jc^V_j𝒟^{V′}_j with their sources.
{#C8.7.5-1} At the stopping scale k_s = K − j(C), with ε_{k_s}²|δ_{k_s}| ≤ sup_{g≤(1+β₀)γ}g²p₀(g)²|δ_{k_s}| and (K + 1 − k_s) = j(C) + 1,

{#C8.7.6} D_{k_s} + S_{k_s} + Cε_{k_s}²|δ_{k_s}| + e_{k_s} ≤ C_a[(K+1)θ̃^{K−j(C)} + (j(C) + 2)w_K],

{#C8.7.7} with C_a := 2C_s(1 − L^{−β′}/θ̃)^{−1} + C_S″ + C_e + 4C_sC_β(1 − θ̃)^{−2}C sup_{g≤(1+β₀)γ}g²p₀(g)², where C is the constant of the coupling term. The four parts bound D_{k_s}, S_{k_s}, e_{k_s}, and Cε_{k_s}²|δ_{k_s}| by (8.6), with k_sθ̃^{k_s} ≤ (K+1)θ̃^{K−j(C)} and (K + 1 − k_s)w_K = (j(C) + 1)w_K. C_a does not depend on K; it depends on j(C) through C_h and C_ν (§8.6), at most as L^{Cε₀j(C)} times a polynomial.
{#C8.7.7-1} This is the bound §7 uses, summable in K: at fixed j(C) the part (j(C) + 2)(K + 1)(θ̃^{k_s/8} + 2^{−k_s/16}) of (j(C) + 2)w_K decays exponentially in K, and μ_K = K^{2−κ₀/2}ℓ_K with κ₀ ≥ 11 (the exponent κ₀ of (2.31) is Bałaban's, κ₀ ≥ 7 at CRE p.263 l.50, and "κ₀ can be chosen arbitrarily large" at p.260 after (2.31); κ₀ > 6 suffices for the summability of Σ_K(j(C) + 2)μ_K, κ₀ > 8 for the Kμ_K in §6.2's s_K and in |δ_i|, and κ₀ > 10 for the K²μ_K in the large-field note's c̄^W_K, its #5.66).
{#C8.7.7-2} *The marked activities.* By (8.6), g_i² ≤ 1, g_i²(K − i) ≤ b^{−1} (#C8.7.3-2), (i + 1)θ̃^{i+1} ≤ m_{i+1}, w_K ≤ m_{i+1}, and m_i ≤ θ̃^{−1}m_{i+1} (#C8.7.3-13), the sources of #C8.3.3-4-2 other than D^{ins}_i are at most C_{ins}m_{i+1}. Here C_{ins} := ε^*[2C_sθ̃^{−1}(1 − L^{−β′}/θ̃)^{−1} + C_S″ + 2C_gC_sC_β(2(1 − θ̃)^{−2} + b^{−1} + 1)] + C_e.
{#C8.7.7-2-1} Also (ε^* + ε^Q_i)D^{ins}_i ≤ (ε^* + ε^Q_i)θ̃^{−1}(1 − L^{−β′}/θ̃)^{−1}‖d^{ins}‖_mm_{i+1} ≤ ½‖d^{ins}‖_mm_{i+1}, since C_τ ≥ θ̃^{−1}(1 − L^{−β′}/θ̃)^{−1} and (ε^* + ε^Q_i)C_τ ≤ ½ under (T1) (#C8.7.3-14, #CP.22).
{#C8.7.7-3} The system is finite, d^{ins}_1 ≤ 2 ≤ (2/θ̃)m_1, and the first steps are #C8.3.3-7's with C_e ≥ 2L^{k₀(ε₀)}. So ‖d^{ins}‖_m ≤ ½‖d^{ins}‖_m + C^*_{ins} with C^*_{ins} := max(C_{ins}, 2/θ̃), hence d^{ins}_i ≤ 2C^*_{ins}m_i and D^{ins}_i ≤ 2C^*_{ins}(1 − L^{−β′}/θ̃)^{−1}m_i. Since m_{i+1} ≤ 2m_i, d^{ins}_{i+1} ≤ 4C^*_{ins}m_i, the bound #C7.6-6-2-1 uses.
{#C8.7.7-4} *The wrap source, solved apart.* The bounds are linear, so d^{ins}_i ≤ u_i + v_i by induction, with u the solution of #C8.7.7-2–#C8.7.7-3 and v that of v_{i+1} = (ε^* + ε^Q_i)V_i + s^w, V_i := Σ_{j≤i}L^{−β′(i−j)}v_j, v_1 := 0. Put {#D.θ_Q} θ_Q := L^{−β′} + sup_i(ε^* + ε^Q_i). Then V_{i+1} ≤ θ_QV_i + s^w, so V_i ≤ s^w/(1 − θ_Q), and v_{i+1} ≤ s^w(1 − L^{−β′})/(1 − θ_Q) ≤ s^w/(1 − θ_Q).
  {#C8.7.7-4-1} θ_Q ≤ (1 + L^{−β′})/2: C_τ ≥ θ̃^{−1}(1 − L^{−β′}/θ̃)^{−1} > (1 − L^{−β′})^{−1} (#C8.7.7-2-1, θ̃ < 1), so (T1) gives ε^* + ε^Q_i ≤ 1/(2C_τ) < (1 − L^{−β′})/2. Hence 1/(1 − θ_Q) ≤ 2/(1 − L^{−β′}). C^*_{ins} and C^E_r are unchanged, and r^E_i gains at most 2s^w/(1 − θ_Q), whether #C7.6-6-2-1 takes D^{ins}_i and d^{ins}_{i+1} by their maximum or by their sum.

## 9. Classical Depth {#CS9}

{#C9.1} Throughout, V is regular at the stopping scale in the sense of VAR (7): |V(∂p′) − 1| < ε_V on T_a. Here ε_V ≤ C_{(3.12)}ε_k by the restrictions on the fields V_k, V_{k+1} on Ω̃_{k+1} from which CRE derives (3.12) (p.267 l.5), with C_{(3.12)} the constant of these restrictions. Put ε₁ := 2C₀ε_V, so that ε₁ ≤ C_{ε₁}ε_k with C_{ε₁} := 2C₀C_{(3.12)}.
{#C9.1-1} VAR (7) at ε_V gives (7) at every parameter in [ε_V, a₁] (#T3.19-1). Since C₀ ≥ 60 (#T4.4, with c₁₁ ≥ 15, R₁M₁ ≥ 1, and B₃ ≥ 1), ε_V ≤ ε₁, and ε₁ ≤ a₁ for γ small. So V satisfies (7) at ε₁ too, with the same minimal orbit (BP_DERIVED_CONFIGS #BC.1-4-3), and (9.2) holds with ε_V as well as with ε₁ in its bounds.
  {#C9.1-1-1} The stopping lattice has N_s > 24M_P points per side, with M_P dividing N_s. Here M_P ≥ R₁M₁ is the block size of #C9.8.4-1, a power of L. It exists since VAR fixes R₁, M₁ as numbers for which the results of its references [3, 5, 6] hold (VAR p.277 l.17), adding only the lower bound (163) (p.304 l.2–4); [6] is REG (VAR's reference list, p.309 l.26).
{#C9.1-2} So REG's theorems hold at VAR's R₁, M₁, and REG's smallest integers R₁, M₁ (REG p.098 l.7) are replaced here by VAR's. These theorems need only lower bounds on these numbers (the LF note's #4.23–#4.24), so VAR's R₁, M₁ are taken as powers of L by choice; PBG's R₀, M₀ are powers of L by PBG's text (p.408 l.26–27).
{#C9.1-2-1} N_s > 24M_P and M_P | N_s hold for γ small: N_s ≥ ℓ_C ≥ MR_k (#C11c.4) with MR_k → ∞ as γ → 0, and the MR_k-cubes tile T_a (#C11c.4), with M_P ≤ MR_k both powers of L. So the cubes of VAR Theorem 1 and of REG Proposition 6 fit in T_a.
{#C9.1-3} U^A := U_k(V) on T_ε and U^B := U_{k+1}(V) on T_{ε/L} are the two minimisers of VAR Theorem 1, Ũ := MU^B on T_ε, and Δ := A_{ε/L}(U^B) − A_ε(U^A).
{#C9.1-3-1} All constants depend only on d, L, G, and the constants of VAR, REG, CMP 98, PRT2, and PBG, with these exceptions. C_{ε₁} also depends on CRE's C_{(3.12)}. The constant absorbed at #C9.8.17 also depends on R_ι = 4dL + 1 of #C9.8.6-1 (VAR p.277 l.14–17, p.300 l.33–37; REG p.098 l.17–18) and on CRE's M₁. Where marked, constants depend on the Hölder exponent ε₀ of §9.5 (B₀′(ε₀), C_G(ε₀), C_gap(ε₀), k₀(ε₀), C(ε₀), C(ε₀, δ₀M₁)), which is not VAR's regularity parameter ε₀ of #C9.4 (#C9.3.3).
{#C9.1-4} The lattice field strength of W = e^{iηA} is F_p := (1/iη²)log W(∂p), and ∇ is its covariant lattice difference.

{#C9.2} The smallness conditions of §9 on ε₁ are

{#C9.3} (9.0) ε₁ ≤ min(1, a₁, a₁^{(M_P)}, a₁′(2C₀/B₃), R₁M₁a₁/M_P), C₀ε₁ ≤ 1, 2C₀ε₁ ≤ min(c₂, c₃), 14dL²B₁^{REG}M_PC₀ε₁ ≤ a₀, 280dL²M_PC₀ε₁ ≤ c₁^{REG}, C_ax^{pl}·d(R_Q^{pl} + 3)C₀ε₁ ≤ m_Q^{pl}/4, 4d(3d + 1)L²C₀ε₁ ≤ ½ (#C7.5-2).

{#C9.4} Here a₁ is VAR's threshold in (7). R₁M₁a₁/M_P is the condition M_P ≤ M(ε₁) = R₁M₁(a₁/ε₁) of VAR Theorem 1 (p.279 l.28) for the lift's cubes at the cube parameter M_P (#C9.8.6), in VAR's parametrisation; VAR Theorem 1 applies to cubes whose parameter is any multiple of R₁M₁ (#4.23 of `balaban_proofs\BP_JOINS_BLOCK_SIZE.md`, which continues the LF note's numbering).
{#C9.4-0} a₁^{(M_P)} is VAR's a₁ taken at the product M_P, which covers the thresholds of VAR that contain R₁M₁ when its constructions are run at the cube parameter M_P (#C9.4-3). a₁′ is VAR's threshold for its §§A–E at the given C₁, used in §9.4 at VAR's C₁ = 2C₀/B₃: the condition ε₀ + C₁ε₁ ≤ c₁ of p.281 l.2 and the restrictions on ε₃ and ε₄ collected at (113)–(121) and Proposition 6, with ε₃ = 4B₁(ε₀ + C₁ε₁) of (114) and ε₄ = 3B₀C₁B₃ε₁.
{#C9.4-1} c₂ is that of CMP 98 Proposition 2, used in §9.7 for the data at scale j. c₃ is that of CMP 98 Proposition 3 (p.036), which the logarithms of (B1)–(B2) of §10.1, used in §9.4, need at the plaquettes of U^B and Ũ (§10.1, *The Plain and the Double-Bar Averagings.*). a₀ is that of PBG Theorems 3.1–3.13, not VAR Theorem 1's a₀, used in #C9.8.4-4: Theorem 3.1 (p.397 l.38) needs M_Pα₀^P ≤ a₀ with α₀^P = 14dL²B₁^{REG}C₀ε₁ (#C9.8.4-3). c₁^{REG} is that of REG Proposition 6 (p.099 l.42) at the cube sizes ≤ 20M_P of #C9.8.4-2.
{#C9.4-2} The last condition is that of *The lower bound at U^B.* in §9.4, with m_Q^{pl}, R_Q^{pl}, and C_ax^{pl} constants of L and d.
{#C9.4-3} The thresholds are constants of d, L, G, VAR, REG, CMP 98, PRT2 (through M_P, C₀, and VAR's thresholds that contain R₁M₁, such as a₅ of VAR (166), p.304 l.24, taken also at the lift's cube parameter M_P), and PBG, so (9.0) holds at every scale j with the same ε₁, uniformly in j, k, K, and ε.

### 9.1 Two Identities {#CS9.1}

{#C9.1.1} (9.1) Δ = [A_ε(Ũ) − A_ε(U^A)] − b(U^B), b(W) := A_ε(MW) − A_{ε/L}(W),

{#C9.1.2} since A_{ε/L}(U^B) = A_ε(Ũ) − b(U^B). Ũ satisfies the constraint M^kŨ = M^{k+1}U^B = V, and §9.6 bounds the bracket in absolute value.
{#C9.1.2-1} Also ℓ(U) := A_{ε/L}(ι(U)) − A_ε(U) = −b(ι(U)), since Mι = id. By (9.1), |Δ| ≤ |b(U^B)| + |A_ε(Ũ) − A_ε(U^A)|.

### 9.2 Regularity of U^B (VAR Theorem 1 at k + 1 Steps) {#CS9.2}

{#C9.2.1} VAR Theorem 1 for the (k+1)-step problem, fine lattice η = ε/L, all-small-field domains (Ω_j the whole lattice, Λ_{k+1} = T_a, L^{k+1}η = a): on every cube ◻ of side 2Ma, R₁M₁ ≤ M ≤ M(ε₁), there is a gauge u with U^{B,u⁻¹} = e^{iηA}, |A| < B₃Mε₁/a, |∇A| < B₃Mε₁/a², ‖A‖_{1,β} < B₄(β₀)Mε₁a^{−2−β} for 0 ≤ β ≤ β₀ = 1 (VAR (9)), and |∂*∂A|, |ΔA| < B₃Mε₁/a³ (VAR (10)).
{#C9.2.1-1} With M = R₁M₁ and β = 1 (the C^{1,1} bound controls every second difference of A):

{#C9.2.2} (9.2) |F| ≤ C₀ε₁/a², |∇F| ≤ C₀ε₁/a³, |A| ≤ C₀ε₁/a on ◻ in the gauge u, C₀ := c₁₁C₀^{VAR}, C₀^{VAR} := 4R₁M₁(B₃ + B₄(1)), c₁₁ := 3(1 + 4c_9),

{#C9.2.3} for ε₁ ≤ a₁, which (9.0) includes. The F-bounds are gauge invariant.
{#C9.2.3-1} VAR's bounds give these with C₀^{VAR}; the factor c₁₁, with c_9 ≥ 1 the constant of (9.4), is the room that §9.3 uses for MW.
{#C9.2.3-2} VAR §F (p.300 l.24–25) proves (9)–(10) from criticality and membership in the regular space (6) alone, and CRE (3.12) is the same application of Theorem 1 to U_{k+1}.

### 9.3 The Blocking Artifact at a Regular Field (Taylor, First Order in ε/a) {#CS9.3}

{#C9.3.1} Let W on T_{ε/L} satisfy (9.2) with C₀^{VAR} in place of C₀, as U^B does (#C9.2.3).
{#C9.3.1-1} The average M = RG I (0.4) (#C10.1.4–#C10.1.4-0-2) multiplies the straight-line transport W(c) along the coarse bond c by the exponential of a convex combination of the logarithms of the holonomies h_{c,x}^{Γ,Γ′} around the closed loops γ_{c,x}^{Γ,Γ′} ∪ (−c), each in B(c₋) ∪ B(c₊) and spanned by at most dL² fine plaquettes (BP_CMP98_ADJOINT_AVERAGING #C10.3.21-6).
{#C9.3.1-2} By the lattice Stokes identity with transports, (1/i)log of such a holonomy is the transported sum of (ε/L)²F over a spanning surface, up to commutators of two fluxes, O(ε⁴|F|²).
{#C9.3.1-3} For the coarse plaquette p = ⟨y, y + εe_μ, y + εe_μ + εe_ν, y + εe_ν⟩, the four bond corrections pair off: the correction of c₁ = ⟨y, y + εe_μ⟩ and that of its opposite c₃ (reversed) are the same convex combinations of fluxes through surfaces that are translates by εe_ν of one another (#C10.1.4-0-1), so their difference is at most Σ_{surface}(ε/L)²·ε|∇F| ≤ Cε³|∇F|, and likewise for c₂, c₄.
{#C9.3.1-4} Hence

{#C9.3.2} (9.3) (1/iε²)log (MW)(∂p) = F̄_p + O(ε|∇F| + ε²|F|²), F̄_p := L^{−2}Σ_{p′ tiling p}F_{p′} (transported),

{#C9.3.3} and MW satisfies VAR (2) on T_ε with VAR's regularity parameter (its ε₀, not the Hölder exponent ε₀ of §9.5) equal to 2C₀ε₁.
{#C9.3.3-1} By (9.3) with VAR's bounds C₀^{VAR} for F, the plaquettes are within (1 + 2c_9)C₀^{VAR}ε₁ε²/a² ≤ 2C₀ε₁ε²/a².
{#C9.3.3-2} D*∂(MW) is a sum of d − 1 = 3 differences of (9.3)'s right side per bond, transported, with a transport factor ≤ 2. The factor 2 covers the holonomy corrections O(ε|F|²) of the covariant differences, which are smaller than the bound C₀^{VAR}ε₁/a³ of ∇F by the factor (ε/a)C₀^{VAR}ε₁ ≤ 1.
{#C9.3.3-3} A difference quotient of F̄ is ≤ C₀^{VAR}ε₁/a³. The C^{1,1} bound of (9.2) does not control ∇∇F, so a difference quotient of the remainder is bounded by twice its size over ε: ≤ (2/ε)c_9(ε|∇F| + ε²|F|²) ≤ 4c_9C₀^{VAR}ε₁/a³.
{#C9.3.3-4} So |D*∂(MW)| ≤ 6(1 + 4c_9)C₀^{VAR}ε₁ε²/a³ = 2C₀ε₁ε²/a³.
{#C9.3.3-5} Also M^kMW = M^{k+1}W (the device of V4's sec:c3-9-1, the blocking artifact at a regular field, and of BalabanAVG Proposition 1 (51)).
{#C9.3.3-6} Now A_ε(MW) = Σ_{p⊂T_ε}ε⁴[½|F̄_p|² + O(ε|F||∇F| + ε²|F|³ + ε⁴|F|⁴)] and A_{ε/L}(W) = Σ_{p⊂T_ε}ε⁴L^{−4}Σ_{p′∈cell(p)}[½|F_{p′}|² + O(ε⁴|F|⁴)], cell(p) the L⁴ fine plaquettes parallel to p in the 4-cell of p (each fine plaquette lies in exactly one cell).
{#C9.3.3-7} All F-values entering one coarse term lie within 2ε of each other, so ||F̄_p|² − L^{−4}Σ|F_{p′}|²| ≤ 4|F|·ε|∇F|·(1 + O(ε|A|)), and with 6(a/ε)⁴N_s⁴ coarse plaquettes and (9.2):

{#C9.3.4} (9.4) |b(W)| ≤ C_b (ε/a) ε₁² N_s⁴ = C_b L^{−k} ε₁² N_s⁴, C_b := 48c_9²C₀², with c_9 ≥ 1 a constant of L and d that bounds the O-terms of (9.3), the factor 1 + O(ε|A|) (ε|A| ≤ C₀ε₁ε/a ≤ 1), and the quartic remainders of the two actions.
{#C9.3.4-1} Per coarse plaquette, with Y := (ε/a)C₀²ε₁²a^{−4} and C₀ε₁ ≤ 1, ε/a ≤ 1, the four parts are: the quadratic mismatch ≤ 2c_9Y, the cross term ⟨F̄_p, (9.3)'s remainder⟩ ≤ 2c_9Y, half the remainder's square ≤ 2c_9²Y, and the quartic terms ≤ 2Y.
{#C9.3.4-2} Their sum is ≤ 8c_9²Y, and the 6(a/ε)⁴N_s⁴ coarse plaquettes, each with weight ε⁴, give the factor 6a⁴N_s⁴.

{#C9.3.5} The same expansion gives the first variation of b at W in the direction δW = e^{i(ε/L)δ𝒜}W, δ𝒜 a Lie-algebra field on the fine bonds, in weak form.
{#C9.3.5-1} The fine side is exact: δA_{ε/L}(W)[δ𝒜] = Σ_{p′}(ε/L)⁴⟨F_{p′}, (Dδ𝒜)(p′)⟩(1 + O((ε/L)⁴|F|²)), D the covariant lattice curl. The term ⟨θ, [θ, δ𝒜]⟩ of the commutator correction vanishes identically (tr X[X, Y] = 0).
{#C9.3.5-2} The coarse side is Σ_pε⁴⟨F̄_p + O(ε|∇F|), (D̄δĀ)(p)⟩, with δĀ := dM(W)δ𝒜 the linearised average (#C9.8.1) of δ𝒜 with transports in W. D̄δĀ is a weighted average of the fine curls (Dδ𝒜)(p′) over the fine plaquettes of the same orientation within 2ε of p, with weights w_{p,p′} ≥ 0, Σ_{p′}w_{p,p′} = 1, Σ_pw_{p,p′} = L^{−4}, computed in #C9.8.1–#C9.8.3, plus a transport correction: δĀ = (the untransported path average) + X with |X| ≤ Cε|A||δ𝒜|.
{#C9.3.5-3} Here ⟨F̂, D̄X⟩ = ⟨D̄*F̂, X⟩ with D̄*F̂ = O(|∇F|), where F̂ := F̄ + the remainder of (9.3). This term and the commutator mismatch [Ā, ·] against [A, ·], which is O(ε|∇A||F||δ𝒜|), are both of the form Σ_bε⁴⟨O(ε|∇F||A| + ε|∇A||F|), δ𝒜⟩.
{#C9.3.5-4} Put F̃_{p′} := Σ_pL⁴w_{p,p′}F̄_p. The plaquettes averaged into F̃_{p′} lie within ℓ¹ distance 6ε of p′, so |F̃_{p′} − F_{p′}| ≤ 6ε|∇F|(1 + O(ε|A|)). Collecting,

{#C9.3.6} (9.5) δb(W)[δ𝒜] = Σ_{p′⊂T_{ε/L}}(ε/L)⁴⟨r₁(p′), (Dδ𝒜)(p′)⟩ + Σ_{b′⊂T_{ε/L}}(ε/L)⁴⟨r₀(b′), δ𝒜(b′)⟩, |r₁| ≤ C_rεε₁/a³, |r₀| ≤ C_rεε₁²/a⁴,

{#C9.3.7} C_r := 8c_9C₀(1 + C₀), with c_9 enlarged to bound also the O-terms of this paragraph: the transport corrections, the commutator mismatch, and the factor 1 + O((ε/L)⁴|F|²). Indeed |r₁| ≤ 6c_9ε|∇F| + c_9(ε|∇F| + ε²|F|²) ≤ 8c_9C₀εε₁a^{−3}, where 6c_9ε|∇F| comes from F̃ − F and the rest from (9.3)'s remainder (C₀ε₁ ≤ 1, ε/a ≤ 1). Further |r₀| ≤ c_9ε(|∇F||A| + |∇A||F|) ≤ 2c_9C₀²εε₁²a^{−4}, since |∇A| ≤ B₃Mε₁/a² ≤ C₀ε₁/a². In VAR's weighted norms |r₁|_{(−2)} ≤ C_r(ε/a)ε₁ and |r₀|_{(−3)} ≤ C_r(ε/a)ε₁².
{#C9.3.7-1} Only ∇F enters: the comparison is of the two quadratic forms at nearby points, not of the two currents.

### 9.4 The Tangential Current of Ũ Is the First Variation of b {#CS9.4}

{#C9.4.1} For run A's problem (VAR (5)–(6), k steps, η = ε, Λ_k = T_a) take VAR's reference configuration U₀ := Ũ.
{#C9.4.1-1} By §9.3, Ũ satisfies VAR (2) at 2C₀ε₁ = C₁B₃ε₁, so it satisfies VAR (14) with C₁ there equal to 2C₀/B₃, at the cost of the smaller threshold a₁′(2C₀/B₃) on ε₁ in VAR (113)–(121), which (9.0) includes. Moreover Ū₀^k = V exactly, so VAR's block datum B vanishes and 𝔄 = H₁B = 0.
{#C9.4.1-1-1} By VAR Proposition 5 the minimiser is U^A = e^{iεA′*}Ũ, A′* = A₁* − HD(A₁*), QA₁* = 0, RD*A₁* = 0, with A₁* the unique fixed point in the ball (115) of T(A₁) := −𝔊J − 𝔊(δV/δA′)(A₁) (VAR (116) with B = 0). Here J is the current of Ũ, ⟨δA, J⟩ := dA_ε(Ũ)[δA] (VAR (81): the linear term of 𝔉), and 𝔊 = G₁𝔓* = 𝔓G₁ (PBG (3.153)).
{#C9.4.1-2} 𝔓 is the projection onto 𝒯 := {QA = 0, RD*A = 0} orthogonal for the form ⟨A, (Δ₁ + DRD* + aQ*Q)A′⟩ (VAR p.293 l.24–26). VAR prints Δ₁ + D^*RD + aQ^*Q there; the operator is DRD*, as p.294 l.4–5 and l.18 and PBG (3.153) print it. R acts on site functions, as in RD*δA′ = 0 of (100) (p.293 l.21), so DRD* maps bond fields to bond fields, while D*RD would apply R to the plaquette field DA′, on which it is not defined.
{#C9.4.1-3} T is a contraction with constant ≤ ½ on the ball in the norm ‖·‖ := max{|·|_{(−1)}, |∇·|_{(−2)}} (VAR (120)–(121)).
{#C9.4.1-4} Hence

{#C9.4.2} (9.6) ‖A₁*‖ ≤ ‖T(0)‖ + ‖T(A₁*) − T(0)‖ ≤ ‖𝔊J‖ + ½‖A₁*‖, so ‖A₁*‖ ≤ 2‖𝔊J‖.

{#C9.4.3} Let Q₁^{pl} := dM(U^B) be the plain linearised one-step averaging at U^B (§10.4 uses Q₁ for the double-bar one) and ℒ a linear right inverse, Q₁^{pl}ℒ = id, built as ℒg := Ig + Q₁^{pl}*(Q₁^{pl}Q₁^{pl}*)^{−1}(g − Q₁^{pl}Ig) with I the componentwise multilinear interpolation of a coarse bond field to the midpoints of the fine bonds in the cube gauge.
{#C9.4.3-1} Q₁^{pl}I reproduces the affine pure-gauge fields g = ∇̄Λ, Λ quadratic, since then Ig = ∇Λ exactly and the plain average is gauge covariant.
{#C9.4.3-2} It does not reproduce an affine field of constant curl: the paths γ_{c,x}^{Γ,Γ′} of #C10.1.4-0-2 enclose with c a flux of order ε²|D̄g|.
{#C9.4.3-3} So, up to transport corrections, g − Q₁^{pl}Ig = 𝒦_ΓD̄g + O(ε²|∇∇g| + ε|A||g|), with 𝒦_Γ a translation-invariant local operator of norm at most Cε.
{#C9.4.3-4} The inverse of T^{pl} := Q₁^{pl}Q₁^{pl}* is bounded uniformly in the volume through a right inverse of Q₁^{pl} bounded uniformly in the volume.
{#C9.4.3-5} The norms are those of the inner products Σ_cε^d on T_ε and Σ_b(ε/L)^d on T_{ε/L}.

- {#C9.4.4} *The lower bound at U = 1.* Let ν be a coarse bond field, Q^{str} the straight-tube average of (ii) of *Identities.* in §10.4, and T(1) := Q^{str}Q^{str}*.
  {#C9.4.4-1} By the tents of *Regularity of the Lifts.* (§10.4), T(1) acts along each coordinate column as a convolution with spectrum in [1/3, 1], so ‖T(1)^{−1}‖ ≤ 3 and ‖Q^{str}*ν‖² = ⟨ν, T(1)ν⟩ ≤ ‖ν‖².
  {#C9.4.4-2} So X₀ := Q^{str}*T(1)^{−1}ν has Q^{str}X₀ = ν and ‖X₀‖ ≤ 3‖ν‖.
  {#C9.4.4-3} At U = 1, Q^{str} is the linear part Q̄₁ of the one-step double bar ((B4) of §10.1), so by (B1)–(B2) at n = 1 the field X := X₀ + Dω̃, with ω̃ equal to Θ₁X₀(y) on the block B(y), satisfies Q₁^{pl}X = ν.
  {#C9.4.4-4} Θ₁X(y) is the block average over x ∈ B(y) of the means over 𝐆(y, x) of the sums of (ε/L)X along its contours (the linear part of v₁ = (R_{0,y}U₁)‾ of CMP 98 (97), (105), taken with the contour variables of #C10.1.4-1-1, by (0.8)), each contour of at most dL bonds inside B(y), so, the means being convex combinations, ‖Θ₁X₀‖ ≤ dL^{d/2+1}(ε/L)‖X₀‖.
  {#C9.4.4-5} Since ω̃ is constant on the blocks, each of L^d sites of weight (ε/L)^d, its norm on T_{ε/L} equals the coarse norm of Θ₁X₀.
  {#C9.4.4-6} Dω̃ lives on the L^{d−1} fine bonds crossing each block face, so ‖Dω̃‖ ≤ 2d^{1/2}L^{−1/2}(ε/L)^{−1}‖Θ₁X₀‖.
  {#C9.4.4-7} Hence ‖X‖ ≤ C_{pl}‖ν‖ with C_{pl} := 3(1 + 2d^{3/2}L^{(d+1)/2}), and ‖ν‖² = ⟨Q₁^{pl}X, ν⟩ = ⟨X, Q₁^{pl}*ν⟩ ≤ C_{pl}‖ν‖‖Q₁^{pl}*ν‖.
  {#C9.4.4-8} So T^{pl}(1) ≥ m_Q^{pl} := C_{pl}^{−2} in every volume.
- {#C9.4.5} *The lower bound at U^B.* T^{pl} has finite range r_T^{pl}, a constant of d, since the paths γ_{c,x}^{Γ,Γ′} of #C10.1.4-0-2 stay in B(c₋) ∪ B(c₊), and norm at most a constant M̃_Q^{pl} of L and d.
  {#C9.4.5-1} It is gauge covariant, T^{pl}(U^u) = Ad(u)T^{pl}(U)Ad(u)^{−1} with u restricted to T_ε, by the covariance of the plain average (CMP 98 (11)), which gives Q₁^{pl}(U^u) = Ad(u|)Q₁^{pl}(U)Ad(u)^{−1}.
  {#C9.4.5-2} So the localisation and the axial-gauge comparison of *Regularity of the Lifts.* apply with m_Q^{pl} in place of m_Q: with R_Q^{pl} fixed by C_E^{pl}/(R_Q^{pl})² ≤ m_Q^{pl}/4 and under C_ax^{pl}·d(R_Q^{pl} + 3)C₀ε₁ ≤ m_Q^{pl}/4, the spectrum of T^{pl}(U^B) lies in [m_Q^{pl}/2, M̃_Q^{pl}], with C_E^{pl} and C_ax^{pl} constants of L and d.
- {#C9.4.6} *The decay.* With q^{pl} := 1 − m_Q^{pl}/(2M̃_Q^{pl}), the Neumann series (T^{pl})^{−1} = (M̃_Q^{pl})^{−1}Σ_{n≥0}(1 − T^{pl}/M̃_Q^{pl})^n, whose n-th term has norm at most (q^{pl})^n and range nr_T^{pl}, gives |(T^{pl})^{−1}(c, c′)| ≤ (2/m_Q^{pl})e^{−δ_Q^{pl}d_ε(c,c′)}, δ_Q^{pl} := (r_T^{pl})^{−1}log(1/q^{pl}), in every volume.

{#C9.4.7} The correction Q₁^{pl}*(T^{pl})^{−1}(g − Q₁^{pl}Ig) is therefore exponentially localised about the support of g − Q₁^{pl}Ig, with fine gradient ≤ C(L|D̄g| + ε|∇∇g| + (ε₁/a)|g|) and fine curl 𝒦_LD̄g + O(ε|∇∇g| + (ε₁/a)|g|), where 𝒦_L := DQ₁^{pl}*(T^{pl})^{−1}𝒦_Γ at U = 1 is a translation-invariant, exponentially localised operator of norm at most a constant C_𝒦 of L and d.
{#C9.4.7-1} Since ε|∇∇g| ≤ 4d|∇g| and ε|D̄g| ≤ 4|g| on T_ε, sup|ℒg| ≤ C_ℒsup|g| and sup|D(ℒg)| ≤ C_ℒ(sup|∇g| + (ε₁/a)sup|g|), with C_ℒ a constant of L, d, G, and C₀ (C₀ through the commutator part, |A| ≤ C₀ε₁/a; taken large enough for #C10.3.15 as well).
{#C9.4.7-2} Let I_{pl} be the componentwise multilinear interpolation of a coarse plaquette field to the fine plaquettes, in the same gauge as I. Then D(Ig) = I_{pl}(D̄g) + O(ε|∇∇g| + (ε₁/a)|g|), by Taylor expansion of g along the paths, the last term being the commutator part of the covariant fine curl at U^B.
{#C9.4.7-3} For every δA ∈ ker Q_A (Q_A the linearised k-step averaging at Ũ), δ𝒜 := ℒδA lies in ker Q_B = ker(Q_A Q₁^{pl}) (chain rule for M^{k+1} = M^k∘M), the tangent space at U^B of {M^{k+1}W = V}, on which dA_{ε/L}(U^B) vanishes by criticality (the gauge directions included, A being gauge invariant).
{#C9.4.7-4} Therefore

{#C9.4.8} (9.7) ⟨δA, J⟩ = dA_ε(MU^B)[Q₁^{pl}ℒδA] = d(A_ε∘M)(U^B)[ℒδA] = db(U^B)[ℒδA] = ⟨δA, ℒ*(D*r₁ + r₀)⟩ for all δA ∈ ker Q_A + 𝒯.

{#C9.4.9} For δA ∈ 𝒯 the vanishing of dA_{ε/L}(U^B)[ℒδA] is checked separately, since 𝒯 is defined by VAR's constraint, the linear part of the double bar (§10.1).
{#C9.4.9-1} By the construction of ℒ, Q₁^{pl}ℒ = id, and the chain rule, Q_BℒδA = Q_AQ₁^{pl}ℒδA = Q_AδA for every δA, and by (B2) of §10.1, Q_AδA = −D_VΘ_kδA for δA ∈ 𝒯.
{#C9.4.9-2} With J(U^B) = Q_B*λ^B and D_V*λ^B = 0 (§10.3, *The Multipliers.*, at the scale of this section), dA_{ε/L}(U^B)[ℒδA] = ⟨Q_AδA, λ^B⟩ = −⟨Θ_kδA, D_V*λ^B⟩ = 0.

{#C9.4.10} So J − ℒ*(D*r₁ + r₀) is annihilated by 𝔓* and 𝔊J = 𝔊ℒ*(D*r₁ + r₀): the residual of the fixed-point equation at Ũ is the propagator applied to the first variation of the blocking artifact.

### 9.5 The Residual (PBG (3.42), (3.44) for 𝔊) {#CS9.5}

{#C9.5.1} PBG Theorem 3.13 (p.426 l.29–32) transfers Theorems 3.3, 3.10, 3.11 to 𝔊 "with the exception of the inequality in (3.42) involving the covariant Laplace operator", so (3.42) without its fourth entry and (3.43)–(3.47) hold for 𝔊, for backgrounds satisfying (3.35)–(3.36), which Ũ does by #C9.8.4–#C9.8.4-4.
{#C9.5.1-1} Writing 𝔊_x := 𝔊(x, ·) and summing by parts on T_{ε/L}, (𝔊ℒ*D*r₁)(x) = Σ_{p′}(ε/L)⁴⟨D(ℒ𝔊_x)(p′), r₁(p′)⟩ with D(ℒ𝔊_x) = (I_{pl} + 𝒦_L)D̄𝔊_x + O(ε|∇∇𝔊_x| + (ε₁/a)|𝔊_x|) by §9.4.
{#C9.5.1-2} (3.42) bounds 𝔊 from sup norms to sup norms: |(𝔊∇*_Uλ)(x)| ≤ B₀a e^{−δ₀d(y,y′)}|λ| and |(𝔊λ)(x)| ≤ B₀a²e^{−δ₀d(y,y′)}|λ| for supp λ ⊂ Δ(y′), x ∈ Δ(y) (its entries G′∇_U^*λ and G′λ, with the norm |λ| = sup|λ|, PBG p.397 l.42–44). Splitting a field f into its restrictions to the cubes Δ(y′) and summing gives |(𝔊∇*_Uf)(x)| ≤ c_δB₀a sup|f| and |(𝔊f)(x)| ≤ c_δB₀a² sup|f|, with {#D.c_δ} c_δ := sup_yΣ_{y′}e^{−δ₀d(y,y′)}.
{#C9.5.1-2-1} Each term of #C9.5.1-1 is of one of these forms. The main term pairs D̄𝔊_x with (I_{pl} + 𝒦_L)*r₁, so it is (𝔊∇*_Uλ)(x) with λ := (I_{pl} + 𝒦_L)*r₁. The term (ε₁/a)O(|𝔊_x|) is 𝔊 applied to a local field of size (ε₁/a)O(|r₁|). The second-difference term enters only multiplied by ε, and summing by parts moves one difference onto r₁: ε⟨∇∇𝔊_x, r₁⟩ = ⟨∇𝔊_x, ε∇*r₁⟩, with |ε∇*r₁| ≤ 4d sup|r₁| by |∇f| ≤ (2/ε)sup|f| on T_ε. So it is at most 4dc_δB₀a sup|r₁|.
{#C9.5.1-3} Let c_𝒦 ≥ 2 be a constant of L, d, and G collecting c_δ, 4d, the factor 1 + C_𝒦 of 𝒦_L, and the constants of the O-terms of §9.4, whose C₀ enters only with a factor ε₁ and is absorbed through C₀ε₁ ≤ 1 of (9.0); PBG's B₀ is left unchanged. Then

{#C9.5.2} sup|𝔊ℒ*D*r₁| ≤ c_𝒦B₀a·sup|r₁| ≤ c_𝒦B₀C_rεε₁/a², sup|𝔊ℒ*r₀| ≤ c_𝒦B₀a²sup|r₀| ≤ c_𝒦B₀C_rεε₁²/a²,

{#C9.5.3} that is, |𝔊J|_{(−1)} ≤ 2c_𝒦B₀C_r(ε/a)ε₁.
{#C9.5.3-1} For the gradient, (3.44) gives |∇𝔊∇*λ| ≤ B₀′(ε₀)Σ_{y′}e^{−δ₀d(y,y′)}(‖λ_{y′}‖^{ξ′}_{ε₀} + |λ_{y′}|) for every 0 < ε₀ ≤ 1, with λ := (I_{pl} + 𝒦_L)*r₁, a coarse plaquette field with |λ| ≤ (1 + C_𝒦)sup|r₁|. The Hölder seminorm of exponent ε₀ at the scale ξ′ = ε/a of a bounded function is at most 2(a/ε)^{ε₀} times its supremum, since its increments are over distances ≥ ξ′.
{#C9.5.3-2} The terms from ℒ's correction and from D(Ig) − I_{pl}D̄g have the form ∇*(a field of size O(|r₁|)) plus (ε₁/a)O(|r₁|). The former is bounded by (3.44) again, with the same Hölder factor, and the latter by (3.42)'s entry ∇_UG′λ, within the B₀ part of C_G(ε₀).
{#C9.5.3-3} The factor 1 + C_𝒦 of λ multiplies B₀′(ε₀), and c_𝒦 is taken to bound it together with c_δ.
{#C9.5.3-4} The gradient of 𝔊ℒ*r₀ is bounded by (3.42)'s entry ∇_UG′λ: sup|∇𝔊ℒ*r₀| ≤ c_𝒦B₀a·sup|r₀| ≤ c_𝒦B₀C_rεε₁²/a³.
{#C9.5.3-5} Hence

{#C9.5.4} (9.8) ‖𝔊J‖ ≤ ρ := C_G(ε₀)(ε/a)^{1−ε₀}ε₁, C_G(ε₀) := 4c_𝒦C_r(B₀ + B₀′(ε₀)), and ‖A₁*‖ ≤ 2ρ by (9.6).

### 9.6 The Gap and the Classical Depth {#CS9.6}

{#C9.6.1} By VAR (81) in VAR's variable A′, which equals A₁* here (B = 0), A_ε(Ũ) − A_ε(U^A) = 𝔉(0) − 𝔉(A₁*) = −⟨A₁*, J⟩ − ½⟨A₁*, Δ₁A₁*⟩ − V(A₁*). The terms below bound this and, with A′* = A₁* − HD(A₁*), the equivalent form VAR (74).
{#C9.6.1-1} The bounds used are sup|A₁*| ≤ 2ρ/a, sup|∇A₁*| ≤ 2ρ/a², |HD(A₁*)| ≤ 4B₀C₂(2ρ)²/a, and |∇HD(A₁*)| ≤ 4B₀C₂(2ρ)²/a² (VAR (57) and (58), p.286 l.42 and p.287 l.4, at VAR's ε₃ := 3ρ). So sup|A′*| ≤ 4ρ/a and sup|∇A′*| ≤ 4ρ/a² once ρ ≤ 1, 54C₂B₀ρ ≤ 1 (VAR's ε₃ ≤ (18C₂B₀)^{−1}, p.286 l.20, which also gives 8B₀C₂ρ ≤ 1), 6ρ ≤ c₄ (VAR p.287 l.7, c₄ that of Proposition 4 of VAR's reference [4]), and 4ρ ≤ a₃ (VAR Proposition 4, p.292 l.50, for V below). These hold for k ≥ k₀(ε₀), since ρ ≤ C_G(ε₀)L^{−(1−ε₀)k}.
{#C9.6.1-2} With 6 plaquettes and 4 bonds per site, a sum with the weights ε⁴ (or (ε/L)⁴ on T_{ε/L}) of a product over the plaquettes or the bonds is at most 6 or 4 times N_s⁴a⁴ times the product of the suprema. By (9.7) ⟨A₁*, J⟩ = db(U^B)[ℒA₁*], so through (9.5) and #C9.4.7-1 it is ≤ N_s⁴a⁴[6C_rεε₁a^{−3}·C_ℒ·4ρa^{−2} + 4C_rεε₁²a^{−4}·C_ℒ·2ρa^{−1}] ≤ 32C_rC_ℒN_s⁴(ε/a)ε₁ρ.
{#C9.6.1-2-1} The current satisfies |J| ≤ 8C₀ε₁a^{−3}, since J is ε^{−2}D*∂Ũ up to terms of higher order in ε²F, with |D*∂Ũ| ≤ 2C₀ε₁ε²/a³ by §9.3 and C₀ε₁ ≤ 1. So |⟨HD(A₁*), J⟩| ≤ 4N_s⁴a⁴·16B₀C₂ρ²a^{−1}·8C₀ε₁a^{−3} = 512B₀C₂C₀N_s⁴ε₁ρ².
{#C9.6.1-3} By VAR (79), ½⟨A₁*, Δ₁A₁*⟩ = ½⟨A₁*, Δ_πA₁*⟩ − ⟨HC^{(2)}(A₁*), J⟩, where |⟨A₁*, Δ_πA₁*⟩| ≤ N_s⁴a⁴·C(4ρ/a²)² ≤ CN_s⁴ρ². Here Δ_π = Δ − Δ′_π of VAR p.284 l.37–38 and p.299 l.2, with ⟨A, Δ_πA⟩ = ⟨A − DG′RD*A, Δ(A − DG′RD*A)⟩ by PBG (3.119) (p.419 l.23), so ⟨A₁*, Δ_πA₁*⟩ = ⟨A₁*, ΔA₁*⟩ since RD*A₁* = 0.
{#C9.6.1-4} Δ is the second variation of the Wilson action at Ũ (PBG's Δ, not the Δ of (9.1)); PBG prints (3.10) for U(N), and the form uses only a faithful unitary representation of G. It is a second-order lattice operator whose coefficients are polynomials in the transports of Ũ and in the plaquette variables Ũ(∂p) − 1 = O(ε²|F|), bounded by (9.2) and (9.3). So |⟨A, ΔA⟩| ≤ Σ_pε⁴((1 + Cε²|F|)|DA(p)|² + C|F||A|²), with ε²|F| ≤ C₀ε₁ ≤ 1.
{#C9.6.1-5} The term ⟨HC^{(2)}(A₁*), J⟩, non-local through H, is at most the bound 512B₀C₂C₀N_s⁴ε₁ρ² of ⟨HD(A₁*), J⟩, since |C^{(2)}(A₁*)| ≤ C₂(2ρ)² (VAR (44), its quadratic part by the Cauchy estimate in t ↦ C_k(taA₁*), |aA₁*| ≤ 2ρ); it replaces that term in the form (81). Finally |V(A₁*)| ≤ Σ_bε⁴|A₁*|sup_t|δV/δA′(tA₁*)| ≤ 4N_s⁴a⁴(4ρ/a)C₄(4ρ)²a^{−3} = 256C₄N_s⁴ρ³ (VAR Proposition 4, (97)).
{#C9.6.1-6} Hence, with (9.8),

{#C9.6.2} (9.9) |A_ε(Ũ) − A_ε(U^A)| ≤ C_gap(ε₀) (ε/a)^{2−2ε₀} ε₁² N_s⁴, C_gap(ε₀) := 32C_rC_ℒC_G(ε₀) + (512B₀C₂C₀ + C + 256C₄)C_G(ε₀)², for k ≥ k₀(ε₀) (ρ ≤ 1, ε₁ ≤ 1, ε/a ≤ 1).

{#C9.6.3} Take k₀(ε₀) so large that also C_gap(ε₀)L^{−(1−2ε₀)k} ≤ C_b and the conditions of §9.7 hold: 8ρ ≤ C₀ε₁, C_{U′}ρ ≤ C₀ε₁, 16C₂^{pl}C_ℒ²ρ² < 3C₁C₀ε₁, 4C_ℒρL^{−k−1} ≤ r^{pl}/2, and 4dC₀L^{−2k} ≤ 1, which gives 3C₀L^{−2k} ≤ 1 (ρ/ε₁ = C_G(ε₀)L^{−(1−ε₀)k}). Then by (9.1), (9.4), and (9.9), for every 0 < ε₀ < ½ and k ≥ k₀(ε₀),

{#C9.6.4} (9.10) |A_{ε/L}(U^B_{k+1}(V)) − A_ε(U^A_k(V))| ≤ 2C_b L^{−k} ε₁² N_s⁴.

{#C9.6.5} With the coupling, the term (g^A_k)^{−2}[A_{ε/L}(U^B) − A_ε(U^A)] of (3.1) is at most 2C_b g_k^{−2}L^{−k}ε₁²N_s⁴, summable in K at fixed stopping lattice since k = K − j(C).

{#C9.6.6} *The smaller k.* §9 asserts (9.8)–(9.10) and the bounds of §9.7 only for k ≥ k₀(ε₀).
{#C9.6.6-1} The steps k < k₀(ε₀) of the recursion are bounded without them, by the plain class bound (§8.3, *The first steps.*, #C8.3.3-6).
{#C9.6.6-2} The finitely many K with K − j(C) < k₀(ε₀) are bounded without them as well (§7, *The smaller K.*, #C7.4-7).

### 9.7 The Minimiser Distance (Configuration Depth, Minimiser Half) {#CS9.7}

{#C9.7.1} (9.8) is also the coarse-side configuration depth: U^A = e^{iεA′*}MU^B with sup|A′*| ≤ 4ρ/a, sup|∇A′*| ≤ 4ρ/a², ρ = C_G(ε₀)(ε/a)^{1−ε₀}ε₁, in the Landau gauge VAR (21) relative to Ũ (the axial representative of Proposition 2 differs by a gauge transformation, immaterial for the gauge-invariant frozen terms).
{#C9.7.1-1} For the fine side, U^B is the minimiser of the one-step problem on T_{ε/L} with the block data Ũ at the spacing ε (it is critical for it, since {MW = Ũ} ⊂ {M^{k+1}W = V}, and VAR Theorem 1's critical orbit is unique), and ι(U^A) is that with the data U^A.
{#C9.7.1-2} VAR Proposition 5 for this one-step problem works at its own scale L^1(ε/L) = ε: VAR's norm is max{ε|·|, ε²|∇·|}, the bounds (3.42), (3.44) for its propagator 𝔊_B carry ε in place of a, and the Hölder scale is ξ′ = 1/L.
{#C9.7.1-3} Its data U^A are regular at the parameter ε₁^{(1)} := 3C₀ε₁(ε/a)²: the plaquettes of Ũ are within 2C₀ε₁ε²/a² by §9.3, and e^{iεA′*} moves them by ≤ 8ρε²/a² ≤ C₀ε₁ε²/a² once 8ρ ≤ C₀ε₁. Since ε₁^{(1)} ≤ ε₁ for k ≥ k₀(ε₀), (9.0) holds for this problem.
{#C9.7.1-4} Put U₀′ := e^{i(ε/L)X}U^B with X := ℒA′*, so |X| ≤ 4C_ℒρ/a and |DX| ≤ 8C_ℒρ/a² (§9.4, ε₁ ≤ 1). In the one-step units of VAR (2) its plaquettes are within (C₀ε₁ + 16C_ℒρ)(ε/a)²: U^B's are within C₀ε₁(ε/a)² by (9.2), and the field strength changes by f below, with |f| ≤ 16C_ℒρ/a².
{#C9.7.1-4-1} Its current is within (C₀ε₁ + C_{U′}ρ)(ε/a)², C_{U′} := (32(d − 1)L + 4C)C_ℒ. U^B's current is within C₀ε₁(ε/a)² by (9.2) with C₀^{VAR}, |D*F| ≤ 2(d − 1)|∇F|, and c₁₁ ≥ 15. The change is ≤ (ε/L)²(2(d − 1)(L/ε)|f| + |s|), with s below, since |D*f| ≤ 2(d − 1)(L/ε)sup|f| on T_{ε/L}.
{#C9.7.1-5} Both are ≤ 2C₀ε₁(ε/a)² ≤ ε₁^{(1)} once C_{U′}ρ ≤ C₀ε₁, since C_{U′} ≥ 16C_ℒ, so U₀′ lies in its space (14). #C9.8.4-2's REG argument at the one-step scale (REG's class at a parameter ≤ 2C₀ε₁, under (9.0)) gives U₀′ the cube-gauge regularity (3.35)–(3.36) that PBG Theorem 3.13 needs for 𝔊_B (and VAR p.280 l.52 for U₀).
{#C9.7.1-6} Since Q₁^{pl}ℒ = id, MU₀′ = e^{i(εA′* + B^{pl})}Ũ exactly, with B^{pl} the remainder of second and higher order of the plain averaging. By Cauchy's estimate in t ↦ (1/i)log(M(e^{it(ε/L)X}U^B)Ũ^{−1}) on |t| ≤ r^{pl}/((ε/L)|X|), |B^{pl}| ≤ C₂^{pl}ε²|X|² ≤ 16C₂^{pl}C_ℒ²(ε/a)²ρ², with C₂^{pl} a constant of d, L, and G (VAR (44)'s C₂ is that of CMP 98's double-bar functions, p.038 l.27). Here r^{pl} = r^{pl}(d, L, G) is a radius on which the complexified holonomies of the average stay in the domain of the principal logarithm (the table's #T11.26), given (9.2).
{#C9.7.1-7} By (9.2) the holonomies of U^B over the plaquettes and the averaging paths are within 2dC₀ε₁L^{−2k} ≤ ½ of 1: there are at most dL² fine plaquettes per averaging loop (BP_CMP98_ADJOINT_AVERAGING #C10.3.21-6), each within C₀ε₁L^{−2k−2}, and 4dC₀L^{−2k} ≤ 1 by #C9.6.3 (ε₁ ≤ 1). The radius condition is (ε/L)|X| ≤ 4C_ℒρL^{−k−1} ≤ r^{pl}/2. Since ‖e^{i(Y+Z)} − e^{iY}‖ ≤ ‖Z‖ for Hermitian Y, Z, VAR (14)'s second condition holds: |MU₀′ − U^A| ≤ |B^{pl}| < C₁ε₁^{(1)}, C₁ = 2C₀/B₃ (#C9.4), once 16C₂^{pl}C_ℒ²ρ² < 3C₁C₀ε₁.
{#C9.7.1-8} VAR's datum B of (20), with e^{iB} = U^A(MU₀′)^{−1} by REG (1.31) (p.082 l.3, l.6), satisfies |B| ≤ (π/2)|e^{iB} − 1| ≤ 2|B^{pl}| (the table's #T11.26) ≤ 32C₂^{pl}C_ℒ²(ε/a)²ρ². This is within VAR's allowance |B| < 2dLC₁ε₁^{(1)} (p.281 l.14), and |H₁B| ≤ B₀|B|/ε ≤ 32B₀C₂^{pl}C_ℒ²(ε/a)ρ²/a. The fixed-point source also contains −𝔊_B(δV/δA′)(H₁B), at most B₀C₄(B₀|B|)² in VAR's units by (117) at A₁ = 0, of order ρ⁴ and absorbed in C(ε₀) below.
{#C9.7.1-9} The current of U₀′ is J(U₀′) = J(U^B) + D*f + s in weak form, where f = DX + O((ε/L)|X||DX|) is the change of the field strength, |f| ≤ 2|DX| ≤ 16C_ℒρ/a² (ε|X| ≤ 1), and s, the change of the transports in D*, satisfies |s| ≤ C|F||X| ≤ 4CC_ℒC₀ε₁ρ/a³.
{#C9.7.1-10} Moreover 𝔊_BJ(U^B) = 0, up to the background-change term of #C9.7.1-14. 𝔊_B acts on the derivative of the action in the directions X of VAR's constraint, the linear part of the double bar (Q₁X = 0, §10.1). As at #C9.4.9, J(U^B) = Q₁^{pl}*λ₁ with (D̄¹)*λ₁ = 0 (§10.3, *The Multipliers.*, at n = 1) and Q₁^{pl}X = −D̄¹Θ₁X ((B2) of §10.1 at n = 1) give ⟨J(U^B), X⟩ = ⟨λ₁, Q₁^{pl}X⟩ = −⟨Θ₁X, (D̄¹)*λ₁⟩ = 0.
{#C9.7.1-11} By (3.42) at the scale ε (the entries G′∇_U^*λ, G′λ, and ∇_UG′λ), sup|𝔊_B(D*f + s)| ≤ c_δB₀(ε|f| + ε²|s|) ≤ C(ε/a)ρ/a, and by (3.44) with the Hölder factor 2L^{ε₀}, sup|∇𝔊_BD*f| ≤ c_δB₀′(ε₀)(1 + 2L^{ε₀})|f| ≤ C(ε₀)ρ/a², while sup|∇𝔊_Bs| ≤ c_δB₀ε|s| ≤ C(ε/a)ρ/a².
{#C9.7.1-12} So VAR Proposition 5 gives ι(U^A) = e^{i(ε/L)A″}U₀′, A″ the sum of H₁B, its fixed point, and the correction HD of VAR (57)–(58) at the one-step scale, with sup|A″| ≤ C(ε₀)(ε/a)ρ/a and sup|∇A″| ≤ C(ε₀)ρ/a², that is, ‖A″‖ ≤ C(ε₀)ρ.
{#C9.7.1-13} Hence the stopping-scale configurations of the two runs on the common fine lattice T_{ε/L} differ by the field (ε/L)(ℒA′* + A″), with ‖ℒA′* + A″‖ ≤ C(ε₀)(ε/a)^{1−2ε₀}ε₁ in VAR's norm, that is, supremum ≤ C(ε₀)(ε/a)^{1−2ε₀}ε₁/a and gradient ≤ C(ε₀)(ε/a)^{1−2ε₀}ε₁/a²: this is σ_k for the minimisers, with σ = 1 − 2ε₀.
{#C9.7.1-14} The one-step fixed point for ι(U^A) uses 𝔊 and 𝔓 at U₀′ rather than at U^B. The background-change term 𝔓*_{U₀′}J(U^B) is bounded by the Cauchy estimate of §10.3 with the distance (ε/L)ℒA′*, relatively O(ρ(ε/a)²ε₁), and is absorbed in C(ε₀); §10.3 uses only (9.2), §9.3, and (9.8).
{#C9.7.1-15} The same argument gives (9.8) with a replaced by a_j := εL^j for the backgrounds of the step at scale j: the j-step minimiser on T_ε against the (j+1)-step minimiser on T_{ε/L} with the same block data at scale a_j, the data V of §10.3. These data satisfy VAR (7) on T_{a_j} with the same ε₁. They are averages of a stopping-scale minimiser, M^jU^A or M^{j+1}U^B, whose plaquettes are within C₀ε_Vη²/a² (η = ε or ε/L) by (9.2) at the data parameter ε_V. So by CMP 98 Proposition 2 ((52), (54)), applied to the j- or (j+1)-fold average under 2C₀ε₁ ≤ c₂, the plaquettes of V are within 2C₀ε_VL^{2(j−k)} ≤ ε₁.
{#C9.7.1-16} Hence (9.0) holds at every scale with this ε₁, with ρ_j := C_G(ε₀)L^{−(1−ε₀)j}ε₁, and for j ≥ k₀(ε₀), where §9.7's conditions hold with ρ_j in place of ρ, σ_j := C(ε₀)L^{−(1−2ε₀)j}ε₁. The note uses only σ_k.

### 9.8 Three Premises Supplied {#CS9.8}

{#C9.8.1} *The Weights of the Linearised Averaging.* At W = 1, (1/i)log h_{c,x}^{Γ,Γ′} is linear in A to first order, and the linearisation of (0.4) (#C10.1.4-0-2) is Ā_c = L^{−(d+1)}Σ_{x∈B(c₋)}A(γ̄_{c,x}) (Ā in the units of T_{Lη}, A in those of T_η, whence L^{−d}·L^{−1}), with the 1-chains γ̄_{c,x} := Γ̄_{c₋,x} + [x, x′] − Γ̄_{c₊,x′} and Γ̄_{y,x} := |𝐆(y, x)|^{−1}Σ_{Γ∈𝐆(y,x)}Γ, A(·) being linear on 1-chains. By #C10.1.4-0-1, Γ̄_{y+z,x+z} = Γ̄_{y,x} + z.
{#C9.8.1-1} Let p be the coarse plaquette with corner y = c₋ in the (μ, ν)-plane, with the bonds c₁ = ⟨y, y + Le_μ⟩, c₂ = ⟨y + Le_μ, y + Le_μ + Le_ν⟩, c₃ = ⟨y + Le_ν, y + Le_ν + Le_μ⟩, and c₄ = ⟨y, y + Le_ν⟩, and fix x ∈ B(y). The four chains γ̄_{c₁,x}, γ̄_{c₂,x+Le_μ}, γ̄_{c₃,x+Le_ν}, γ̄_{c₄,x} combine in the curl Ā_{c₁} + Ā_{c₂} − Ā_{c₃} − Ā_{c₄} into the closed chain γ̄_{c₁,x} + γ̄_{c₂,x+Le_μ} − γ̄_{c₃,x+Le_ν} − γ̄_{c₄,x}.
{#C9.8.1-2} In it every Γ̄-piece appears twice with opposite signs: Γ̄_{y,x} from c₁ and c₄, Γ̄_{y+Le_μ,x+Le_μ} from c₁ reversed and c₂, Γ̄_{y+Le_ν,x+Le_ν} from c₃ and c₄ reversed, and Γ̄_{y+Le_μ+Le_ν,x+Le_μ+Le_ν} from c₂ reversed and c₃. What remains is ∂S_x, the boundary of the L × L square S_x in the (μ, ν)-plane with corner x.
{#C9.8.1-3} Hence, by the abelian Stokes formula,

{#C9.8.2} (9.11) (D̄Ā)(p) = L^{−2}L^{−d}Σ_{x∈B(y)}Σ_{p′⊂S_x}(DA)(p′) = Σ_{p′}w_{p,p′}(DA)(p′), w_{p,p′} := L^{−2−d}·#{x ∈ B(y) : p′ ⊂ S_x} ≥ 0,

{#C9.8.3} so Σ_{p′}w_{p,p′} = L^{−2−d}·L^d·L² = 1, since each S_x has L² plaquettes. Fix a fine (μ, ν)-plaquette p′. The pairs (p, x ∈ B(p₋)) with p of orientation (μ, ν) are in bijection with the fine points x, since x determines its block point y = p₋. So Σ_pw_{p,p′} = L^{−2−d}·#{x ∈ T_{ε/L} : p′ ⊂ S_x} = L^{−2−d}·L² = L^{−d}.
{#C9.8.3-1} The weights are translation invariant by construction and vanish unless p′ ⊂ S_x for some x ∈ B(y), that is, unless p′ lies within the 2L × 2L square at y in the (μ, ν)-plane and within L fine spacings of y in each of the d − 2 transverse directions (x ranges over B(y)).
{#C9.8.3-2} In the non-abelian case the same identity holds for the transported curls, the transports along the cancelling Γ-pieces being the transport corrections X of §9.3.

{#C9.8.4} *The Cube-Gauge Regularity (3.35)–(3.36) of Ũ = MU^B.* By §9.3, Ũ satisfies VAR (2) on T_ε with the parameter α₀^R := 2C₀ε₁, which in the all-small-field geometry (Ω_j the whole lattice, L^kε = a) is REG's class (1.8)–(1.9) (p.077 l.36–38) at the parameter α₀^R: |Ũ(∂p) − 1| < α₀^Rε²/a² and |D*∂Ũ| < α₀^RL^{−2k}a^{−1}.
{#C9.8.4-1} PBG is applied at the block size M_P, the LF note's M′ (#4.22; the table's #T2.5; not the local M′ := O(1)LM/2 of #C5.55), a power of L and a constant of d and L that is at least PBG's M₁ of Theorem 3.1 (p.397 l.38) and a multiple of VAR's R₁M₁ (VAR p.279 l.3), of REG's R₁M₁ (p.098 l.8), and of PBG's R₀M₀ (p.408 l.28). Its class cubes are here unions of M_P-blocks of T_a, and those its theorems use are □̃ⁿ with n ≤ 9, of side at most 20M_Pa (the LF note's #4.25).
{#C9.8.4-2} Let □ be such a cube, of side Ma with M a multiple of REG's R₁M₁ and M ≤ 20M_P. The construction of REG Proposition 6 (p.099 l.42–58) uses the cube □̃ of side (M + 4R₁M₁)a ≤ 24M_Pa (p.098 l.12–18), which T_a contains as a genuine cube since N_s > 24M_P. Under 7dL²Mα₀^R ≤ c₁^{REG} the proposition gives a gauge u on □ with Ũ^{u⁻¹} = e^{iεA} and a|A|, a²|∇A|, a³|∂*∂A|, a³|ΔA| < 7dL²B₁^{REG}Mα₀^R on □ ((1.136) at j = k), where c₁^{REG} and B₁^{REG} are REG's c₁ and B₁ of Proposition 6.
{#C9.8.4-3} These are (3.35)–(3.36) with PBG's M equal to M_P and its α₀ equal to α₀^P := 7dL²B₁^{REG}α₀^R = 14dL²B₁^{REG}C₀ε₁, the size of □ in T_a being M. The bounds are proportional to the cube size, as (3.35) asks, so VAR's cube class need not be matched with PBG's.
{#C9.8.4-4} PBG Theorem 3.1 needs M_Pα₀^P ≤ a₀, and REG needs 7dL²·20M_P·α₀^R = 280dL²M_PC₀ε₁ ≤ c₁^{REG}. Both are in (9.0), and the plaquette bounds of (9.3) hold as well.

{#C9.8.5} *The Localised Lift.* For a localisation domain X the frozen difference Δ_j of (3.1) needs a lift ι_X with three properties.
{#C9.8.5-1} It is a function of U on X^∼ only, so that Δ_j depends on U on X^∼. CRE p.259 (i) has X, and the enlargement to X^∼ is the lift's.
{#C9.8.5-2} It satisfies Mι_XU = U on the coarse bonds of X^∼, and ι_X1 = 1.
{#C9.8.5-3} It is the minimal configuration of a one-step problem whose block data on X agree with those of ι, so that ι_XU^A_k is close to U^B_{k+1} on X.

{#C9.8.6} *The definition.* ι_XU := U(𝐁_1(X^∼), M^·(Q_1^{s*}U)), Bałaban's construction of the local minimisers (CRE (1.2)–(1.3), and (2.16) at k-blocks), with (Q_1^{s*}U)(b) = 1 for b ⊂ B(y) and U(c) for b ∈ B(c).
{#C9.8.6-1} Here Ω₀ := X^∼, and Ω₁ is the union of the big blocks of size M₁ε of X^∼ at distance > R_ιM₁ε/L from its complement, with R_ι = 4dL + 1 (the LF note's #D.R_ι; table #T2.22). VAR's Sect. F cubes are run at VAR's product R₁M₁ = M_P, with its block size M₁^{VAR} kept and its R₁ raised to M_P/M₁^{VAR} (#T2.7-1; BP_JOINS_BLOCK_SIZE #4.23–#4.23-0). So VAR (1)'s R is R := R_ιM₁/M₁^{VAR} blocks of M₁^{VAR}, and M_P ≤ CRE's M₁ (CRE's M₁ = KM′ with K ≥ 12d + 1, the LF note's #D.M₁; table #T2.15).
{#C9.8.6-2} Hence R_ιM₁ε/L > 4dM₁ε ≥ 4dM_Pε, the ℓ¹ reach of □̃ beyond Ω₁ (□ of side 2M_Pε, □̃ adding 2M_Pε). This suffices for □̃ ⊂ Ω₀ (VAR's Sect. F, p.300 l.33–37, whose source REG p.098 l.17–18 assumes RM bigger than R₁M₁, "for example L^{−1}RM > 2dR₁M₁", to this end; VAR's thresholds at this cube parameter are among those of (9.0), #C9.4). Also R ≥ R₁ since R_ιM₁ ≥ M_P, which is all that VAR (1) asks of R (p.277 l.17), so VAR (1) holds at j = 0 with η = ε/L.
{#C9.8.6-3} REG's condition "a power of L" (p.077 l.16) enters none of REG's steps. They read R only in (1.4), at p.098 l.18, and in p.077 l.16's lower bound on RM₁. That bound is met here, since VAR fixes R₁, M₁ so that REG's results hold (p.277 l.17), and R_ιM₁ = R_ιKM′ ≥ M_P = R₁M₁, with CRE's M₁ on the left and VAR's product on the right.
{#C9.8.6-4} The block data are U on Ω₁.
{#C9.8.6-5} The collar data are the fine field Q_1^{s*}U on the bonds of Λ₀, those without an endpoint in Ω₁.
- {#C9.8.7} Q_1^{s*} is an exact local right inverse of the averaging.
  {#C9.8.7-1} M(Q_1^{s*}U) = U is #C11b.2-4 at k = j = 1, every coarse bond joining two 1-blocks.
- {#C9.8.8} Q_1^{s*} is covariant, Q_1^{s*}(U^v) = (Q_1^{s*}U)^{ṽ_b} with ṽ_b := v(y) on B(y), and polynomial in U, with Q_1^{s*}1 = 1.
- {#C9.8.9} ι_XU depends on U on X^∼ only (CRE p.246 l.46).
- {#C9.8.10} VAR Theorem 1 and Proposition 9 give the minimal orbit, its uniqueness, its regularity, and its analyticity in U in the axial gauge, since Q_1^{s*} is analytic. ι_X1 = 1.
- {#C9.8.11} Mι_XU = U on the coarse bonds of X^∼.
  {#C9.8.11-1} On those with an endpoint in Ω₁ this is the constraint, since VAR identifies Ω₁ with the bonds having an endpoint in it (p.277 l.18).
  {#C9.8.11-2} On the others, the averaging contours run on bonds of Λ₀, which carry Q_1^{s*}U.

{#C9.8.13} *The tail.* As in CRE (3.6), ιU^A_k is the minimiser of the X^∼-problem at its own data M^·(ιU^A_k).
{#C9.8.13-1} The constraints of 𝐁_1(X^∼) fix the block averages of ι's problem on X^∼, so a competitor extended by ιU^A_k is admissible for ι's problem, with the same change of the action, and the minimal orbit is unique.
{#C9.8.13-2} So ι_XU^A_k = exp(i(ε/L)T)ιU^A_k, with T := ℋ(B), ℋ the solution map of VAR (179)–(181) at the background ιU^A_k, and B := (1/i)log[Q_1^{s*}U^A_k(ιU^A_k)^{−1}] on Λ₀, B = 0 on Ω₁.
- {#C9.8.14} *The collar mismatch.* Take ιU^A_k in the block-axial gauge: ιU^A_k = 1 on the axial contours Γ_{y,x} of each block (#C10.1.4-1), a representative of its orbit with u(y) = 1, which leaves U^A_k and Q_1^{s*}U^A_k unchanged.
  {#C9.8.14-1} An in-block bond b closes a loop with the contours of area ≤ dε²/L, so |ιU^A_k(b) − 1| ≤ dε(ε/L)|F|, with F the field strength of ιU^A_k.
  {#C9.8.14-2} A crossing bond b ∈ B(c) differs from U^A_k(c) = M(ιU^A_k)(c) by the in-block parts of the contours and the strips between them, by ≤ C_Lε²|F|. Here C_L is the path-length constant of the averaging, a constant of L and d: each path γ_{c,x}^{Γ,Γ′} of #C10.1.4-0-2 has at most (d + 1)L fine bonds and stays in B(c₋) ∪ B(c₊).
  {#C9.8.14-3} The data parameter of ι's problem is the coarse plaquette deviation of U^A_k ≈ MU^B, which is at most O(1)C₀ε₁(ε/a)² by (9.2)–(9.3). VAR Theorem 1 places the minimiser in the space 𝔘_k({Ω_j}, B₃ε₁) of its (8), with VAR's ε₁ equal to that data parameter (p.279 l.11–15). That space bounds |∂U(p) − 1| by B₃ε₁L^{−2j} on Ω_j (VAR p.278 l.5), with no cube factor. The constant B₃M of VAR (9) carries the cube factor, so (9) is not used.
    {#C9.8.14-3-1} At one step, η = ε/L and j = 0, 1, this gives |F| ≤ C_Fε₁/a² on X^∼ with C_F := O(1)L²B₃C₀, a the finest scale on X^∼, since VAR's ε₁ is a supremum over 𝔅_k (VAR (7)); so C_ι/C₀ ≤ O(1)L⁴C_LB₃ (#C9.8.15-3), independent of M′. B, dimensionless as VAR's B = (1/i)log V′, is at most C_LC_Fε²ε₁/a² per fine bond.
  {#C9.8.14-4} VAR's solution map carries the factor (L^jη)^{−1} ≤ L/ε of (190) at the fine lattice, so B enters T as a source of size ≤ LC_LC_F(ε/a)ε₁/a.
- {#C9.8.15} *The decay.* The derivative δℋ/δB decays as in VAR (190).
  {#C9.8.15-1} Integrated along tB, t ∈ [0, 1], as in CRE (3.7), it gives |T| ≤ C_ι(ε/a)(ε₁/a)e^{−δ₀dist(·, Ω₁^c)/ε} and |∇T| ≤ C_ι(ε/a)(ε₁/(aε))e^{−δ₀dist(·, Ω₁^c)/ε}.
  {#C9.8.15-2} The gradient entry of (190) carries one more factor (L^jη)^{−1} = ε^{−1} at j = 1.
  {#C9.8.15-3} Here δ₀ is at most 1/16 of the rate ⅛δ₀^{VAR} printed in (190) (δ₀^{VAR} being VAR's δ₀), half of it paying the sum over the collar, and C_ι := O(1)L²C_LC_F with O(1) ≥ 2.
  {#C9.8.15-4} On the collar T is the mismatch itself, |T| ≤ LC_LC_F(ε/a)ε₁/a (#C9.8.14-4), with fine differences ≤ 2L|T|/ε ≤ 2L²C_LC_Fε₁/a², inside the gradient bound of #C9.8.15-1 since C_ι ≥ 2L²C_LC_F.
- {#C9.8.16} *The linearisation at 1.* At U = exp(ih) with h an affine block field and t → 0, the same computation bounds d(ι_X − ι)(1)h on X by C_ιe^{−δ₀dist(·, Ω₁^c)/ε} times the constant curl of h, since the mismatch dB(1)h is sourced by the curl.
  {#C9.8.16-1} This is the input C″_Π of the moment (§5, *The moment of the lifted term*).

{#C9.8.17} *The consequences.* Let dist_∞ be the ℓ^∞ distance. It exceeds the distance dist in which VAR's decay is stated by at most the block-point rounding of PRT2 (2.46) (p.231 l.14–15), which is less than ε, so dist(·, Ω₁^c) + ε ≥ dist_∞(·, Ω₁^c).
{#C9.8.17-0} Since X^∼ exceeds X by M₁-cubes of the scale a_j = εL^j (CRE p.256 l.62–63), every point of X is at ℓ^∞ distance ≥ M₁εL^j from the complement of X^∼. Every point of Ω₁^c ∩ X^∼ lies in a big block at distance ≤ R_ιM₁ε/L from that complement (#C9.8.6-1), and a big block has ℓ^∞ diameter ≤ M₁ε. Hence, on X and within 2L fine spacings of it, where the frozen term and its current slot live, dist_∞(·, Ω₁^c) ≥ M₁εL^j − R_ιM₁ε/L − M₁ε − 2ε. Since M₁ ≥ 3, δ₀(R_ιM₁/L + M₁ + 3) ≤ δ₀(R_ι/L + 2)M₁.
{#C9.8.17-1} So e^{−δ₀dist/ε} ≤ e^{δ₀(R_ι/L + 2)M₁}e^{−δ₀M₁L^j}, which also covers the scales with L^j ≤ R_ι/L + 2, where X can meet the collar.
{#C9.8.17-2} By the Baker–Campbell–Hausdorff formula, ι_XU^A_k = e^{i(ε/L)𝐒_X}U^B_{k+1} there, with 𝐒_X − 𝐒 = T + O((ε/L)|𝐒||T|).
{#C9.8.17-3} So 𝐒_X − 𝐒 is at most C(ε₀)ε₁e^{−δ₀M₁L^j}/a in sup and C(ε₀)ε₁e^{−δ₀M₁L^j}/a² in gradient, by ε/a ≤ 1, with C_ιe^{δ₀(R_ι/L + 2)M₁} absorbed into C(ε₀).
{#C9.8.17-4} In the units of a_j these are C(ε₀)ε₁e^{−δ₀M₁L^j}L^{j−k} and C(ε₀)ε₁e^{−δ₀M₁L^j}L^{2(j−k)}, both ≤ C(ε₀, δ₀M₁)ε₁e^{−δ₀M₁L^j/2}L^{j−k} with C(ε₀, δ₀M₁) := 2C(ε₀)/(eδ₀M₁). Indeed L^{j−k} ≤ 1, and xe^{−x/2} ≤ 2/e gives e^{−δ₀M₁L^j/2} ≤ 2/(eδ₀M₁L^j) ≤ 2/(eδ₀M₁).
{#C9.8.17-5} So σ̂_{k,j} := σ_k + C(ε₀)ρ_k + C(ε₀, δ₀M₁)ε₁e^{−δ₀M₁L^j/2} bounds the distance of §5's pair line on X and within 2L fine spacings of it.

{#C9.8.18} The pair-lift term G of §3 is gauge invariant.
{#C9.8.18-1} Let v be a gauge transformation on T_ε and ṽ_b := v(y) on B(y).
{#C9.8.18-2} The collar data transform as Q_1^{s*}(U^v) = (Q_1^{s*}U)^{ṽ_b}, and the block data as M(W^{ṽ_b}) = M(W)^v (CMP 98 (11)).
{#C9.8.18-3} So the X^∼-problems at U and at U^v correspond under ṽ_b, and the uniqueness of the minimal orbit (VAR Theorem 1) gives ι_X(U^v) = (ι_XU)^{ṽ} with ṽ := ṽ_bu, where u is a gauge transformation equal to 1 at the block points. So ṽ(y) = v(y) at every block point y.
{#C9.8.18-4} With J(U^v) = Ad(v)J(U) and the covariance Q₁^{pl}(W^ṽ)* = Ad(ṽ)Q₁^{pl}(W)*Ad(v)^{−1} of §9.4, Q₁^{pl}(ι_X(U^v))*J(U^v) = Ad(ṽ)Q₁^{pl}(ι_XU)*J(U). 𝐄^B is invariant under (W, 𝐉) ↦ (W^ṽ, Ad(ṽ)𝐉) (RG I (1.19), p.263 l.34–37, under the gauge action (1.10); CRE p.259 (iii)), so G(U^v) = G(U).
{#C9.8.18-5} *The G^c-invariance of G.* The same holds for G^c-valued v on X^∼ wherever 𝐔 and 𝐔^v lie in 𝒫_j(X; α′), with the current variable 𝐉 transformed by Ad(v) as in (1.10).
{#C9.8.18-6} The collar identity Q_1^{s*}(𝐔^v) = (Q_1^{s*}𝐔)^{ṽ_b} is an identity of polynomials in 𝐔 and v.
{#C9.8.18-7} The identities M(W^{ṽ_b}) = M(W)^v and Q₁^{pl}(W^{ṽ})* = Ad(ṽ)Q₁^{pl}(W)*Ad(v)^{−1} hold for G^c-valued v wherever both sides are defined, with no continuation.
{#C9.8.18-7-0} M (#C10.1.4-0-2) and Q₁^{pl}* (BP_CMP98_ADJOINT_AVERAGING #C10.3.21–#C10.3.21-4) are built from transports, which are products of bond variables, and from log, dlog, dexp, and Ad(e^{iY}) evaluated at the loop holonomies h_{c,x}^{Γ,Γ′}. A gauge transformation conjugates these holonomies, h ↦ ṽ(c₋)hṽ(c₋)^{−1}. Conjugation preserves the spectrum of h, and f(ghg^{−1}) = gf(h)g^{−1} for every invertible g and every f holomorphic near that spectrum.
{#C9.8.18-8} In the axial gauge of the X^∼-problem, ι_X(𝐔^v) = (ι_X𝐔)^{ṽ_b}.
{#C9.8.18-9} This is VAR (181) for the local problem, with the transformation constant on the blocks B(y) and equal to v(y).
{#C9.8.18-10} VAR proves (181) by analyticity for complex data and for G^c-valued v in a small neighbourhood of the G-valued ones, and extends it to all G^c-valued v "treating the equality as a definition for the remaining υ", so that U_k is defined and analytic on the union of the orbits (p.307 l.11–15; Proposition 9, p.309 l.9–10).
{#C9.8.18-11} ι_X on 𝒫_j(X; α′) is that extended function, as the large-field note's #4.519 applies it to V^B(Y). 𝐄^B is invariant under the G^c-valued gauges (1.10) (CRE's (iii), p.259 l.43–44) on run B's spaces, which are unions of G^c-orbits (RG I p.262 l.4–14), and the lifted pairs of 𝐔 and 𝐔^v lie in one orbit there (#C5.5).
{#C9.8.18-12} So G(𝐔^v) = G(𝐔), and with CRE's (iii) for 𝐄^A, Δ(X, 𝐔^v) = Δ(X, 𝐔) on 𝒫_j(X; α′).

## 10. Gaussian Depth (Configuration Depth, Covariance Half) {#CS10}

### 10.1 The Two Forms {#CS10.1}

{#C10.1.1} At the step whose fluctuation field B lives on T_ℓ, ℓ := εL^{j−1} (run A's step j, run B's step j + 1), the Gaussian form of CRE (3.15) is −½⟨A_k, C*ΔCA_k⟩ with Δ = Δ^{(j)}(U) of RG I (1.4)–(1.5) on {Q̃B = 0}, whose last term is the quadratic part 𝐆^{(2)} of the exponential axial gauge fixing (RG I (2.5), (2.11)). By RG I p.267 l.38–39 ("The quadratic form in B′ above is equal to −1/2⟨B′,Δ^{(k)}B′⟩, see the definition (3.156) [13] with the δ-function gauge fixing term replaced by the exponential one") the other terms are those of PBG (3.155)–(3.156), so

{#C10.1.2} (10.1) Δ_U[B] = ⟨B, (Q_mG₁Q_m*)^{−1}B⟩ − aℓ^{−2}⟨B, B⟩ − 2⟨H₁hC̃^{(2)}(B), J⟩ + 𝐆^{(2)}_{M^mU}(B),

{#C10.1.2-1} with the inner products η^dΣ_b on T_η and ℓ^dΣ_b on T_ℓ, for which Q_m* is the adjoint. In them PBG's form (3.16) at the single scale ℓ is aℓ^{d−2}Σ_b|(Q_mA)(b)|² = aℓ^{−2}⟨Q_mA, Q_mA⟩, so PBG's Q*aQ is aℓ^{−2}Q_m*Q_m and the a-term of (3.156) is aℓ^{−2}⟨B, B⟩.
{#C10.1.3} G₁ = (Δ₁ + DRD* + aℓ^{−2}Q_m*Q_m)^{−1} on the fine lattice T_η is PBG's G₁ of (3.128): Δ₁ = Δ_π − Δ_π^{(2)}, VAR (79)'s (table #T11.25), is the operator of its first two terms ⟨A, Δ_πA⟩ − 2⟨HC_π^{(2)}(A), J⟩ (PBG (3.134) and p.422 l.40), and ‖RD*A‖² = ⟨A, DRD*A⟩ since R is an orthogonal projection. Q_m = Q_m(U) is the linear part of the m-fold double bar of #C10.1.4-1, PBG's linearised m-fold averaging built on it, with PBG's operators and bounds taken for it as #C10.1.4-1-1-1 states, and H₁ = G₁Q_m*(Q_mG₁Q_m*)^{−1} (PBG (3.129)).
{#C10.1.3-0} J is the current of U, R = R(U) the orthogonal projection onto Δ_UN(Q′_m), Q′_m the linear part of the averaged gauge transformation (Ru)‾^m (Q′_m and R: PBG p.393 l.46–p.394 l.2 and l.9–11; CMP 98 (78)–(80)), C̃^{(2)} the quadratic term of the one-step nonlinear averaging Q̃ of B at the block field M^mU, and h the operator of RG I p.267 l.18–23. PBG (3.155) writes the current term with D̃^{(2)}, a quadratic polynomial restricted to unit blocks (p.427 l.37–38). RG I (2.11) (p.267 l.35) writes it as ⟨H₁hC̃^{(2)}(B′), J⟩, and l.38–39 identify RG I's form with (3.156). (10.1) uses RG I's term.
  {#C10.1.3-0-1} 𝐆^{(2)}_W is RG I's 𝐆^{(2)} (table #T10.14) at the block field W = M^mU in the units of (10.1), where RG I's unit-lattice variable is B′ = ℓB (d = 4): 𝐆^{(2)}_W(B) = Σ_yΣ_{x∈B(y), x≠y}|B̃′(y, x)|², with B̃′(y, x) the linear part of (e^{iℓB}W)(y, x)W(y, x)^{−1}. Here W(y, x) is RG I's contour variable (0.11), the group average (0.10) of the transports W(Γ) along the family 𝐆(y, x) of #C10.1.4-0-1 in the block B(y) of T_{Lℓ} (RG I p.253, p.254 l.26–30, p.266 l.8–15).
{#C10.1.3-1} Run A: η = ε, m = j − 1, U = U^A_j(V); run B: η = ε/L, m = j, U = U^B_{j+1}(V).
{#C10.1.3-2} Both are forms on fields on T_ℓ. Put δΔ_j := Δ^B − Δ^A.
{#C10.1.3-3} The principal part's kernel obeys PBG (3.132), |(Q_mG₁Q_m*)^{−1}(y, y′)| ≤ B₀ℓ^{−2}ℓ^{−d}e^{−δ₁d(y,y′)} at the single scale ℓ. Let r_j be the least number with |δΔ_j(y, y′)| ≤ r_jB₀ℓ^{−2}ℓ^{−d}e^{−δ₂d(y,y′)}, δ₂ := min(δ₁′, ½δ₁), with δ₁′ the rate of (3.132) at complex data (table #T10.50; #C10.3.3-10) and δ₁ as fixed in §10.4 (#C10.4.124).

{#C10.1.4} *The Plain and the Double-Bar Averagings.* The block fields are plain averages: M is the chain's average RG I (0.4) (p.253; CRE p.243 l.23–25), which extends CMP 98 (15) to families of contours so that it is symmetric under the lattice Euclidean transformations (RG I p.252 l.34–40).
  {#C10.1.4-0-1} For a coarse bond c = ⟨c₋, c₊⟩ in direction μ and x ∈ B(c₋) put x′ := x + Le_μ (fine units). B(y) is the set of fine points of the cube of side L centred at y (RG I (0.3)), and L is odd (RG I p.251 l.14, table #T10.43). So the blocks have L^d points each and partition the fine lattice, and x − y = Σ_νn_νe_ν with |n_ν| ≤ (L − 1)/2 for x ∈ B(y). 𝐆(y, x) is the family of the shortest contours from y to x, one for each order of the directions ν with n_ν ≠ 0 (p.252 l.27–32). So 𝐆(y + z, x + z) = 𝐆(y, x) + z, and |𝐆(c₊, x′)| = |𝐆(c₋, x)|.
  {#C10.1.4-0-2} For Γ ∈ 𝐆(c₋, x) and Γ′ ∈ 𝐆(c₊, x′) put γ_{c,x}^{Γ,Γ′} := Γ ∪ [x, x′] ∪ (−Γ′) and h_{c,x}^{Γ,Γ′} := W(γ_{c,x}^{Γ,Γ′})W(c)^{−1}, the holonomy at c₋ of the closed loop γ_{c,x}^{Γ,Γ′} ∪ (−c), with W(c) the transport along the L fine bonds of c. Then (0.4) reads MW(c) = e^{iY_c}W(c) with Y_c := L^{−d}Σ_{x∈B(c₋)}|𝐆(c₋, x)|^{−2}Σ_{Γ,Γ′}(1/i)log h_{c,x}^{Γ,Γ′}, a convex combination of the logarithms.
  {#C10.1.4-0-3} A gauge transformation u conjugates every h_{c,x}^{Γ,Γ′} by u(c₋), so M(W^u) = M(W)^{u|}, u| the restriction of u to the coarse lattice. RG I applies the results of CMP 98 ([12] there) to its averages (Proposition 2 at p.260 l.36 and p.265 l.17, (97) at p.270 l.32). It states that they hold for (0.12), that (0.4) and (0.12) "are equally good for our purposes" (p.254 l.7–10), and that the results of RG I and of the previous papers "do not depend on any particular averaging operation used" (p.253 l.42). The note cites CMP 98's results for M in the same way.
{#C10.1.4-1} PBG's linear objects belong to the double bar Ū̄ of CMP 98 (89)–(92), which PBG uses throughout (p.392 l.44–52). CMP 98 (89) builds it from the plain relative average, here M, and the gauge averages of CMP 98 (78)–(80). CMP 98 builds these with one contour for each x ∈ B(y), the axial contour Γ_{y,x} of PRT1 (1.7) (CMP 98 (78), p.030 l.19; the notation at p.019 l.38–42), the member of 𝐆(y, x) that runs through the directions in the order d, d − 1, …, 1.
  {#C10.1.4-1-1} With M = (0.4) they are taken, as in the chain's dressed average of table #T10.23, with RG I's contour variables U(y, x) of (0.11), Federbush's group averages (0.10) of the U(Γ), Γ ∈ 𝐆(y, x), in place of U(Γ_{y,x}). RG I makes the same replacement in its axial gauge fixing (p.253 l.12–13, p.254 l.25–26). By (0.6) U(y, x) transforms as U(Γ_{y,x}) does, to u(y)U(y, x)u(x)^{−1}. By (0.9) it lies in G for real U, and by (0.8) its linear part at U = 1 is the mean of the contour sums over 𝐆(y, x).
  {#C10.1.4-1-1-1} CMP 98's (60)–(108) hold for these averages (balaban_proofs/BP_REG_DRESSED.md #BR.4–#BR.4-1). Its other results used here, (109), Proposition 3 with (121)–(124), Proposition 4 with (134)–(135), Propositions 6 and 7, and the bound (126) of the linear part, are taken for them by RG I p.254 l.7–10 (#C10.1.4-0-3). PBG's results used for Q_m (PBG is RG I's [13]) are taken for them by RG I's assertion, printed without proof, that the results of RG I and of the previous papers "are valid universally for all averages satisfying the above properties" (0.5)–(0.9) (p.253 l.42–43).
    {#C10.1.4-1-1-1-1} The explicit form (124) of the linear part is printed for CMP 98's own average; for these its contour terms run over the families 𝐆(y, x) with the weights of #C10.4.9-1-1-1, and #C10.1.8-3 derives the linear part at U = 1 directly.
  {#C10.1.4-1-2} Q_n(U) and C_n^{(2)}(U) are the linear and quadratic parts of the n-fold double bar of a fluctuation U₁ = e^{iηA} about U, normalised as in #C10.1.8-2.
{#C10.1.4-2} For a configuration U on T_η put Q_n^{pl}(U) := d(M^n)(U) in the same units.
{#C10.1.4-3} The logarithms below are taken at backgrounds regular in the sense of CMP 98 (109), |V₀(∂p) − 1| < α₀ with α₀ ≤ c₃ of CMP 98 Proposition 3 (p.036). Here C₀ is the note's constant of (9.2), not CMP 98's C₀ of Proposition 1. The plaquettes of U^A_j, U^B, and Ũ_j are within 2C₀ε₁η²/a_j² of 1 (#C10.3.39), and those of their averages M^iU, i < n, within 4C₀ε₁L^{2i}η²/a_j² ≤ C₀ε₁ (#C10.3.25-1). So all these backgrounds are regular under 2C₀ε₁ ≤ c₃.

- {#C10.1.5} (B1) By CMP 98 (97), the relative plain average Ũ₁^n of U₁ is the double bar Ū̄₁^n transformed by the gauge transformation v_n of the lattice of spacing L^nη given there, a product of means of transported averages of U₁ and of its double bars Ū̄₁^i, 1 ≤ i ≤ n − 1, with v_n = 1 at U₁ = 1.
  {#C10.1.5-1} Linearising at U₁ = 1, with the gauge action of PBG (3.116), Q_n^{pl}(U) = Q_n(U) − D̄^nΘ_n, where Θ_n := d((1/i)log v_n) is linear and D̄^n is the covariant difference at the block field M^nU (PBG (3.115)).
- {#C10.1.6} (B2) Hence Q_n^{pl}(U)*ν = Q_n(U)*ν for every ν with (D̄^n)*ν = 0, and Q_nX = 0 implies Q_n^{pl}X = −D̄^nΘ_nX.
  {#C10.1.6-1} Q_n^{pl} is onto wherever Q_n is (#C10.1.6-1-1). Q_n is onto wherever Q_nG₁Q_n* is invertible, since the range of Q_nG₁Q_n* lies in that of Q_n. Q_nG₁Q_n* is invertible in the following three cases.
    {#C10.1.6-1-0} At real U under the hypotheses of PBG Theorem 3.12 at the scale L^nη, or under their variant with the current bound in the place of (3.36) (#C10.2.1 at ℓ), by Theorem 3.12 and (3.132), with #C10.3.3-6 for the variant.
    {#C10.1.6-1-0-1} On 𝒟_j at the scale ℓ, by #C10.3.3-10.
    {#C10.1.6-1-0-2} At the configurations satisfying 𝒟_j's condition on 𝐔 (#C10.3.3) at its scale a_j, with the current 0, where G₁ = G₀, by balaban_proofs/BP_PBG_COMPLEX.md #BX.1-3 under M ≥ M₃ and Mα₀ + α₁ + α_JL^{−3} ≤ a_cx (#C10.3.3-9). The current 0 lies strictly inside its bound.
    {#C10.1.6-1-1} If Q_nX₀ = B, then X := X₀ + D_Uω, with ω equal to Θ_nX₀ on the coarse lattice, satisfies Q_n^{pl}X = B, by the covariance Q_n^{pl}(U)D_Uω = D̄^n(ω restricted to the coarse lattice) (#C10.3.4-1).
- {#C10.1.7} (B3) For W near U put M̄_U(W) := Ū̄₁·MU, the one-step double bar of U₁ := WU^{−1} times the coarse background (CMP 98 (89)–(90)).
  {#C10.1.7-1} By (B1) at n = 1, M(W) is the gauge transform of M̄_U(W) by v₁, so A_{Lη}(M̄_U(W)) = A_{Lη}(M(W)), and M̄_U(U) = MU.
- {#C10.1.8} (B4) By CMP 98 (90)–(91), the n-fold double bar about U is the (n − 1)-fold one about MU applied to the one-step double bar about U. Linearising, Q_n(U) = Q_{n−1}(MU)Q̄₁(U), with Q̄₁(U) the linear part of the one-step double bar, Q(U) of CMP 98 (121)–(122).
  {#C10.1.8-1} At second order, C_n^{(2)}(U)[X, X] = C_{n−1}^{(2)}(MU)[Q̄₁X, Q̄₁X] + Q_{n−1}(MU)C̄₁^{(2)}[X, X], with C̄₁^{(2)} the quadratic part of CMP 98 (122) in the normalisation of #C10.1.8-2.
  {#C10.1.8-2} Here C_n^{(2)}(U)[X, X] is the quadratic part of (1/(L^nη))C_n(U, L^nηX) in PBG (3.14), that is, L^nη times the quadratic part of PBG's C_n(U, ·), which is PBG's second normalisation on p.421 l.12–14, C^{(2)}(A) = L^jηC_j^{(2)}(A) on Λ_j, the one that goes with H of (3.126). So the n-fold double bar of the fluctuation e^{iηX} about U is exp(iL^nη(Q_nX + C_n^{(2)}(U)[X, X] + O(X³))).
  {#C10.1.8-3} At U = 1, Q̄₁X(c) = L^{−(d+1)}Σ_{x∈B(c₋)}X([x, x′]), the average over the L^d straight fine paths of the tube of c divided by L, which is CMP 98's (125) in the normalisation of #C10.1.8-2. Indeed, CMP 98's gauge average at y, of the transports along the contours from y to x (CMP 98 (85)), has with the contour variables the linear part λ_y := L^{−(d+1)}Σ_{x∈B(y)}X(Γ̄_{y,x}) in the units of T_{Lη}, by (0.8) (#C10.1.4-1-1), and the linear part of M is L^{−(d+1)}Σ_x(X(Γ̄_{c₋,x}) + X([x, x′]) − X(Γ̄_{c₊,x′})) (#C9.8.1).
    {#C10.1.8-3-1} (89) composes them as −λ_{c₋} + (linear part of M) + λ_{c₊}, and x ↦ x′ maps B(c₋) onto B(c₊), so the Γ̄-terms cancel.
- {#C10.1.9} (B5) Covariance.
  {#C10.1.9-1} PBG p.418 computes, at U₁ = 1, that the double bar of the gauge transform of U₁ by u = e^{iλ} is the coarse gauge transform of the trivial configuration by ū = (Ru)‾, which gives (3.114)–(3.115), Q_nD = D̄^nQ′_n.
  {#C10.1.9-2} For general U₁, (B1) at n = 1 and the plain covariance give Ū̄(U₁^u) = Ū̄(U₁)^{w_u} with w_u := v₁(U₁^u)^{−1}·u|·v₁(U₁), u| the restriction of u to the coarse lattice, a coarse gauge transformation. By (B4) the same holds for the n-fold double bar, with w_u^{(n)} the composite of these one-step transformations along the levels.
  {#C10.1.9-3} PBG (3.116) reads A^λ = A − Dλ + c(λ, A) + O(λ²) + O(λA²), with c(λ, A)(b) := ½i[λ(b₋), A(b)] − ½i[A(b), R_bλ(b₊)], and c̄ for the same term on the coarse lattice.
  {#C10.1.9-4} With (1/i)log w_u^{(n)} = Q′_nλ + q_n(λ, A) + O(λ²) + O(λA²), q_n bilinear, the terms of first order in λ and in A of the covariance give

{#C10.1.10} 2C_n^{(2)}[Dλ, Y] = Q_nc(λ, Y) + D̄^nq_n(λ, Y) − c̄(Q′_nλ, Q_nY).

{#C10.1.11} The identity is used only paired with a bond field ν with (D̄^n)*ν = 0, where the term D̄^nq_n drops out, so no bound on q_n is needed.

### 10.2 The Penalty Form and the Galerkin Identity {#CS10.2}

{#C10.2.1} Let U be real and satisfy, at the scale ℓ, the variant of the hypotheses of PBG Theorem 3.12 (p.423 l.33–36) with the current bound in the place of (3.36) (#C10.3.3-6): (3.35) with M large and α₀ small, and a real current J with |J| ≤ α_Jℓ^{−3}. Or let (U, J) be a real pair of 𝒟_j, U and J real, where PBG's bounds at the scale ℓ hold (#C10.3.3-1, #C10.3.3-10). Then G₁^{−1} is positive definite and Q_m is onto.
  {#C10.2.1-0} In the first case the positivity is PBG Theorem 3.11 for G₁, through Theorem 3.12. In the second, U = e^{iεA}U₀ (#C10.3.3), where εA, of norm < εα₁/a_j, is the small logarithm of UU₀^{−1} ∈ G. So εA lies in 𝔤 and A is real. Hence the (e^{itεA}U₀, J), t ∈ [0, 1], are real pairs of 𝒟_j, at which G₁(t)^{−1} is symmetric, invertible by the convergent series (3.138) (#C10.3.3-9), and continuous in t (#C10.3.3-10). At t = 0 the first case applies, so no eigenvalue of G₁(t)^{−1} crosses 0, and G₁^{−1} is positive definite at t = 1. In both cases Q_m is onto by #C10.1.6-1.
    {#C10.2.1-0-1} The first case applies at t = 0, since |J| < α_Ja_j^{−3} ≤ α_Jℓ^{−3} and U₀ satisfies (3.35) at the scale ℓ. Indeed, a cube of PBG's class at the scale ℓ (p.396 l.14–17), of side κℓ with κ ≥ 10M, lies in a cube of the class at the scale a_j = Lℓ of side κ′a_j with κ′ ≤ max(10M, κ/L + 2M) ≤ Lκ, since 2M ≤ κ/5. The gauge u of the larger cube, U₀^u = e^{iεA₀}, gives on it |A₀| < κ′α₀a_j^{−1} ≤ κα₀ℓ^{−1} and |∇A₀| < κ′α₀a_j^{−2} ≤ κα₀ℓ^{−2}.
{#C10.2.1-1} For Q_mA = B write A = H₁B + A₀ with Q_mA₀ = 0. Since G₁^{−1}H₁B = Q_m*(Q_mG₁Q_m*)^{−1}B is orthogonal to ker Q_m, ⟨A, G₁^{−1}A⟩ = ⟨B, (Q_mG₁Q_m*)^{−1}B⟩ + ⟨A₀, G₁^{−1}A₀⟩, and ⟨A, aℓ^{−2}Q_m*Q_mA⟩ = aℓ^{−2}⟨B, B⟩ on the constraint set.
{#C10.2.1-2} Hence

{#C10.2.2} (10.2) P_U(B) := ⟨B, (Q_mG₁Q_m*)^{−1}B⟩ − aℓ^{−2}⟨B, B⟩ = min{⟨A, (Δ₁ + DRD*)A⟩ : Q_mA = B}, attained at A = H₁B,

{#C10.2.3} and, polarised, ⟨B′, P_UB⟩ = ⟨A′, (Δ₁ + DRD*)H₁B⟩ for every A′ with Q_mA′ = B′, because (Δ₁ + DRD*)H₁B = G₁^{−1}H₁B − aℓ^{−2}Q_m*B is orthogonal to ker Q_m. This identity uses only Q_mH₁B = B and the inverses of G₁ and Q_mG₁Q_m*, so it holds on 𝒟_j as well (#C10.3.3-10). There ⟨·, ·⟩ is extended bilinearly, Q_m* is its transpose, and "orthogonal" means annihilated in that pairing. The minimum in (10.2) is for real U only.

### 10.3 Alignment of the Backgrounds (Cauchy) {#CS10.3}

{#C10.3.1} By (9.8) at scale j (#C9.7.1, #C9.7.1-15), under #C9.6.1's conditions with ρ_j (ρ_j ≤ 1, 54C₂B₀ρ_j ≤ 1, 6ρ_j ≤ c₄, and 4ρ_j ≤ a₃), U^A_j = e^{iεA′*_j}Ũ_j with Ũ_j := MU^B_{j+1}, sup|A′*_j| ≤ 4ρ_j/a_j, sup|∇A′*_j| ≤ 4ρ_j/a_j², a_j = εL^j, in the Landau gauge VAR (21) relative to Ũ_j.
{#C10.3.1-1} In this subsection U^A, U^B, and Ũ stand for U^A_j, U^B_{j+1}, and Ũ_j, and V = M^jŨ = M^{j+1}U^B is the common block field on T_{a_j}.
{#C10.3.1-2} The block field of U^A is V^w, not V. VAR p.281 l.2–4 reaches the Landau representative from the axial one, U^A_ax with M^jU^A_ax = V, through the gauge transformation u with (R₀u)‾^j = 1, U^A = (U^A_ax)^{u^{−1}}. This condition makes the averaged transformation trivial, not the restriction of u to T_{a_j}.
{#C10.3.1-3} So M^jU^A = V^w with w := u^{−1} restricted to T_{a_j}, by the covariance CMP 98 (11), and #C10.3.35 gives |(1/i)log u| ≤ c_wρ_j at every point.
{#C10.3.1-4} For a configuration U on T_η with block field V_U := M^nU (n = j for η = ε, n = j + 1 for η = ε/L) let 𝒬(U) := d(M^n)(U), normalised by M^n(e^{iηX}U) = e^{ia_j(𝒬(U)X + O(X²))}V_U.
{#C10.3.1-5} The inner products on a lattice of spacing η are Σ_bη^d⟨·, ·⟩ on the bonds and Σ_xη^d⟨·, ·⟩ on the sites, and the current J(U) is defined by ⟨X, J(U)⟩ := dA_η(U)[X].
{#C10.3.1-6} The chain rule gives 𝒬(U^B) = 𝒬(Ũ)Q₁^{pl}, with Q₁^{pl} = dM(U^B) of #C9.4.3, and 𝒬(U) = 𝒬′Q_m^{pl}(U), with Q_m^{pl} the plain linearised averaging to T_ℓ (#C10.1.4-2) and 𝒬′ := dM(M^mU) the last step, a field averaging, written 𝒬′ to keep Q′ for PBG's averaging of gauge parameters. 𝒬′ is the same operator for Ũ (m = j − 1) and for U^B (m = j), since M^{j−1}Ũ = M^jU^B.

{#C10.3.3} *The Pair Class.* Let 𝒟_j be the set of pairs (𝐔, 𝐉) where 𝐔 is a G^c-valued configuration on T_ε satisfying PBG (3.37) at scale j, and 𝐉 is a 𝔤^c-valued bond field on T_ε with |𝐉| < α_Ja_j^{−3}, α_J = Mα₀ (table #T3.15). Condition (3.37) means 𝐔 = e^{iεA}U₀ with U₀ real satisfying (3.35) at the scale a_j, with PBG's M and α₀, |A| < α₁/a_j, and |∇_{U₀}A| < α₁/a_j², where ∇_{U₀} is the covariant gradient of (3.37).
{#C10.3.3-1} 𝒟_j is imposed at the scale a_j of the common block field V, which the multipliers below need, while run A's form lives at the scale ℓ = a_j/L. At the scale ℓ the conditions of 𝒟_j are (3.37) with α₁/L in place of α₁, U₀ satisfying (3.35) at the scale ℓ too (the cube argument of #C10.2.1-0-1), and the current bound with α_JL^{−3}. So PBG's bounds at the scale ℓ hold on 𝒟_j.
{#C10.3.3-2} Define the form Δ_{(𝐔,𝐉)} by writing 𝐉 for J in (3.120), in the first line of (3.128), in Δ_π := Δ − Δ′_π[𝐉], in (3.134), and in the J-term of (10.1), with the block field M^m𝐔 in hC̃^{(2)} and 𝐆^{(2)}. On the diagonal 𝐉 = J(𝐔) it is Bałaban's form.
{#C10.3.3-3} The second printed line of (3.128) differs from the first at a pair by ⟨A, Δ′_π[J(𝐔) − 𝐉]A⟩. The first line is the one used, and β_π ≡ 0 (#C10.4.98) holds for it.
{#C10.3.3-4} PBG builds G and G₁ from G₀ = (Δ + DRD* + Q*aQ)^{−1} (p.421) by the series (3.130) and (3.138) (pp.421–423), and H and H₁ from them and the inverses (QGQ*)^{−1} and (QG₁Q*)^{−1} by (3.126) and (3.129). G₀ does not involve the current and satisfies Theorem 3.3 under (3.35).
{#C10.3.3-5} The current enters these series through Δ′_π, which is linear in 𝐉, and through Δ^{(2)} = 2⟨HC^{(2)}, 𝐉⟩, in which H itself depends on 𝐉 through the series.
{#C10.3.3-6} PBG uses (3.36), which (3.38) asks of U₀ and Theorem 3.12 of the external field, only for the size of the current (p.419 l.11–12, p.422 l.50). The current enters (3.131), as printed with the factor O(1)Mα₀, through |𝐉| ≤ α_Jℓ^{−3}, and (3.137) through |H*𝐉| ≤ O(1)α_Jℓ^{−3}, which (3.133) gives (p.422 l.50). So PBG's bounds, and Theorem 3.12 (p.423, stated under (3.35) and (3.36)), hold with the current bound in place of (3.36).
{#C10.3.3-8} So (3.130) converges on 𝒟_j for α₀ small, uniformly on 𝒟_j. Its terms are built from G₀ and, through Δ′_π, from G′ and R. They are analytic there, since the complex extensions of G′, R, and G₀ (Theorem 3.4's G, p.421 l.33) are given by Theorem 3.4 with the inequalities of Theorems 3.1–3.3 (p.400 l.7–10, proved on pp.400–407). A uniformly convergent series of analytic functions is analytic, as PBG argues for G′ and G (p.402 l.56, p.407 l.36), so G is analytic on 𝒟_j.
{#C10.3.3-9} (3.138) contains Δ^{(2)}_π, hence H and (QGQ*)^{−1}, which are not terms of (3.130). Its convergence needs (3.133) for H at the pair, which BP_PBG_COMPLEX.md gives at complex pairs (#BX.1-3, #BX.8-1). balaban_proofs/BP_PBG_COMPLEX.md extends the inverses (QGQ*)^{−1} and (QG₁Q*)^{−1}, and with them H, G₁, and H₁, at the single scale ℓ, with α_JL^{−3} for its current bound γ, for M ≥ M₃ and Mα₀ + α₁ + α_JL^{−3} ≤ a_cx (#BX.1-2–#BX.1-3, #BX.7–#BX.8-2; table #T12.24).
{#C10.3.3-10} They are analytic in (A, 𝐉) on 𝒟_j. The inverses satisfy (3.132) with a constant {#D.B₀^{cx}} B₀^{cx} ≥ B₀ of d, L, and G and the rate δ₁′ of table #T10.50 for δ₁, and H and H₁ satisfy (3.133) with B₀^{cx} and ½δ₁′. At real pairs PBG's B₀ and δ₁ hold, by Theorem 3.12 with #C10.3.3-6 for the external field 𝐔 (#C10.3.3-10-0). Theorem 3.12 states (3.133) for H and H₁ (p.423 l.33–36), through (3.132) for both inverses (p.422 l.15–21).
  {#C10.3.3-10-0} At a real pair 𝐔 = e^{iεA}U₀ satisfies (3.35) at the scale ℓ with 2(α₀ + α₁/(ML)) for α₀. In the gauge u of U₀ on a class cube, U₀^u = e^{iεA₀} with A₀ bounded by (3.35), and 𝐔^u = e^{iεA^u}e^{iεA₀}, A^u(b) := Ad(u(b₋))A(b), |A^u| = |A| < (α₁/L)ℓ^{−1} (#C10.3.3-1). Writing ∇_{U₀}A in this gauge, the transports e^{iεA₀} add at most 4|A₀||A|, so |∇A^u| ≤ (α₁/L)ℓ^{−2} + 4|A₀||A| ≤ 2(α₁/L)ℓ^{−2} under 4O(1)Mα₀ ≤ 1.
    {#C10.3.3-10-0-1} With Φ(X, Y) := (1/i)log(e^{iX}e^{iY}) − X − Y, |Φ| ≤ c_B|X||Y| for |X|, |Y| ≤ r_{BCH} (#C10.3.14-3), and Cauchy's estimate gives |∂_XΦ| ≤ 2c_B|Y| and |∂_YΦ| ≤ 2c_B|X| for |X|, |Y| ≤ r_{BCH}/2. So 𝐔^u = e^{iεA_tot}, A_tot := A^u + A₀ + ε^{−1}Φ(εA^u, εA₀), has |A_tot| ≤ (α₁/L + (1 + c_Bα₁)O(1)Mα₀)ℓ^{−1} and |∇A_tot| ≤ (3/2)(|∇A^u| + |∇A₀|), under 4c_BO(1)Mα₀ ≤ 1, 4c_Bα₁ ≤ 1, and O(1)Mα₀ ≤ r_{BCH}/2.
    {#C10.3.3-10-0-2} Since PBG's O(1) is ≥ 10 (p.396 l.16), 3α₁/L ≤ 2O(1)M·α₁/(ML) and (3/2)O(1)Mα₀ ≤ 2O(1)Mα₀. So both bounds are within those of (3.35) with 2(α₀ + α₁/(ML)) for α₀, and Theorem 3.12 needs 2(α₀ + α₁/(ML)) below its threshold for α₀.
  {#C10.3.3-10-1} The block field M^m𝐔 is analytic on 𝒟_j with |M^m𝐔(M^mU₀)^{−1} − 1| < O(1)α₁, by CMP 98 Proposition 6 ((164), p.043) with ℓ as its unit. Its hypotheses hold for α₀ and α₁ small, since U₀ satisfies its (52) with O(1)Mα₀/L² by (3.35), and |A′| < α₁/L in its units. So C̃^{(2)} (CMP 98 Proposition 6, p.043, at the parameters of #C10.3.3-11-6-0), h, and 𝐆^{(2)}_{M^m𝐔} are analytic on 𝒟_j, and so is Δ_{(𝐔,𝐉)}. Here h is the inverse of a coefficient of the linear part that is analytic in W and invertible (#C10.3.3-11-7).
{#C10.3.3-11} On 𝒟_j the principal part of Δ_{(𝐔,𝐉)} has kernel bounded by B₀^{cx}ℓ^{−2}ℓ^{−d}e^{−δ₁′d(y,y′)} (#C10.3.3-10), and the a-term by aℓ^{−2}ℓ^{−d} on the diagonal, the identity having kernel ℓ^{−d}δ_{yy′} for the inner product ℓ^dΣ. For 𝐆^{(2)} write W := M^m𝐔 = W′W₀ bondwise, with W₀ := M^mU₀ real and |W′ − 1| < O(1)α₁ (#C10.3.3-10-1). On 𝒟_j each factor Ad(W(b)) of a contour has norm ≤ (1 + O(1)α₁)², so under 2O(1)dLα₁ ≤ log(4/3) the transports in X_Γ := ℓΣ_{b∈Γ}Ad(W(Γ up to b))B(b), the linear part of (e^{iℓB}W)(Γ)W(Γ)^{−1}, have norm ≤ 4/3.
  {#C10.3.3-11-1} For Γ, Γ″ ∈ 𝐆(y, x), W(Γ)W(Γ″)^{−1} is the holonomy of a loop of at most dL bonds. Its real part W₀(Γ)W₀(Γ″)^{−1} is reached from 1 by at most Σ_{α<β}|n_α||n_β| ≤ dL² plaquette moves, one per pair of steps taken in opposite orders (BP #C10.3.21-6). The plaquettes of U₀ are within O(1)Mα₀η²/a_j² of 1, by (3.35) and the Baker–Campbell–Hausdorff formula, and CMP 98 Proposition 2 ((52), (54); #C10.1.4-0-3), applied m times as at #C10.3.25-1 under O(1)Mα₀ ≤ c₂, puts those of W₀ within O(1)Mα₀L^{2m}η²/a_j² = O(1)Mα₀/L² (L^mη = ℓ = a_j/L).
  {#C10.3.3-11-2} The factors W′ change the loop by a product of at most dL unitary conjugates of W′(b)^{±1}. So δ′ := max_{Γ,Γ″}|W(Γ)W(Γ″)^{−1} − 1| ≤ O(1)dMα₀ + O(1)dLα₁. By (0.6), W(y, x) = M({W(Γ)W(Γ₀)^{−1}})W(Γ₀) for a fixed Γ₀, with W(Γ)W(Γ₀)^{−1} = e^{iA_Γ} and |A_Γ| ≤ 2δ′.
    {#C10.3.3-11-2-1} Their average e^{iĀ} satisfies (0.10), Σ_Γ(1/i)log(e^{iA_Γ}e^{−iĀ}) = 0, so the BCH bound of #C10.3.14-3 and the continuity argument of #C10.3.34-7 give |Ā| ≤ (4/3)·2δ′ under 8c_Bδ′ ≤ 1 and 4δ′ ≤ r_{BCH}. So g_Γ := W(Γ)W(y, x)^{−1} = e^{iA_Γ}e^{−iĀ} = e^{iZ_Γ} with |Z_Γ| ≤ 2δ′ + (8/3)δ′ + c_B(16/3)δ′² ≤ (16/3)δ′, and |g_Γ − 1| ≤ |Z_Γ|e^{|Z_Γ|} ≤ 6δ′ for δ′ ≤ 1/46. Let c_{GM} ≥ 1 be a constant of d and G with |dlog_g − 1| and |Ad(g) − 1| at most c_{GM}|g − 1| for |g − 1| ≤ 1/10. Then c_{GM}δ′ ≤ 1/66 gives δ′ ≤ 1/46 and |g_Γ − 1| ≤ 1/11, and these conditions hold for α₀ and Lα₁ small.
  {#C10.3.3-11-3} Differentiating (0.10), Σ_Γ(1/i)log g_Γ = 0, along e^{iℓB}W gives Σ_Γdlog_{g_Γ}(X_Γ − Ad(g_Γ)B̃′(y, x)) = 0. So B̃′(y, x) = Σ_ΓT_ΓX_Γ, with T_Γ := 𝒜^{−1}dlog_{g_Γ} and 𝒜 := Σ_Γdlog_{g_Γ}Ad(g_Γ). With dlog_g and Ad(g) within e := 6c_{GM}δ′ ≤ 1/11 of the identity, Σ_Γ|T_Γ| ≤ (1 + e)/(1 − 3e) ≤ 3/2. So the coefficient of each B(b) in B̃′(y, x) has norm ≤ ℓ·(3/2)(4/3) = 2ℓ.
  {#C10.3.3-11-4} So 𝐆^{(2)}'s kernel is supported on pairs of bonds in one block of T_{Lℓ}, which lie at distance ≤ dL. Against the inner product Σℓ^d it is a sum of at most L^d terms, one per x, each of norm ≤ 4ℓ²ℓ^{−2d} = 4ℓ^{−2}ℓ^{−d} (d = 4). So it is bounded by {#D.C_𝐆} C_𝐆ℓ^{−2}ℓ^{−d}e^{−δ₁′d(y,y′)}, C_𝐆 := 4L^de^{δ₁′dL}, a constant of d and L.
  {#C10.3.3-11-5} In the J-term −2⟨H₁hC̃^{(2)}(B), 𝐉⟩, hC̃^{(2)}(B) vanishes off the bonds b₀(c), c a bond of T_{Lℓ}, b₀(c) the bond of c joining B(c₋) to B(c₊), and equals h(c)C̃^{(2)}(B)(c) at b₀(c) (RG I p.267 l.18–23). For x ∈ Δ(y), (3.133) gives |H₁(x, y′)| ≤ B₀^{cx}ℓ^{−d}e^{−½δ₁′d(y,y′)} (#C10.3.3-10) and d(x, y′) ≤ d(y, y′) + d. So η^dΣ_x|H₁(x, y′)||𝐉(x)| ≤ e^{δ₁′d}c_eB₀^{cx}α_JL^{−3}ℓ^{−3}, with c_e of #C10.3.14-6 at the scale ℓ.
  {#C10.3.3-11-6} In the units of #C10.1.8-2, C̃^{(2)}(B)(c) is the quadratic part of (Lℓ)^{−1}F_c(B), F_c(B) := (1/i)log[M(e^{iℓB}W)(c)M(W)(c)^{−1}]. With RG I's unit-lattice variable B′ = ℓB (#C10.1.3-0-1), F_c is RG I's Q̃(B′)(c) of (2.4) (p.266 l.6) at the block field W, and RG I defines C̃ from it at p.267 l.26.
    {#C10.3.3-11-6-0} By (0.4) (#C10.1.4-0-2), F_c reads B only on c, the paths [x, x′], and the contours of 𝐆(c₋, x) and 𝐆(c₊, x′), all bonds of B(c₋) ∪ B(c₊). With Lℓ as the unit, e^{iℓB}W = U″W₀, with W₀ real satisfying CMP 98 (52) with O(1)Mα₀ (#C10.3.3-11-1), U″ := e^{iℓB}W′ = e^{iA″/L}, and W′ = e^{iA′/L}, |A′| ≤ O(1)Lα₁ (#C10.3.3-10-1). Let r_P, a constant of d, L, and G, be an α₁ of CMP 98 Proposition 6 with r_P ≤ r_{BCH}, c_Br_P ≤ 1, and O(1)r_P ≤ 1/8 for the O(1) of (164).
      {#C10.3.3-11-6-0-1} For Lℓ sup|B| ≤ r_P/2 and O(1)Lα₁ ≤ r_P/3 the BCH bound of #C10.3.14-3 gives |A″| ≤ r_P/2 + r_P/3 + c_Br_P²/(6L) < r_P. So by Proposition 6 ((164), p.043; #C10.1.4-1-1-1) both factors of M(e^{iℓB}W)(c)M(W)(c)^{−1} = [M(U″W₀)(c)M(W₀)(c)^{−1}][M(W′W₀)(c)M(W₀)(c)^{−1}]^{−1} are analytic in B and within 1/8 of 1. The product is then within (1/8)(8/7) + 1/7 = 2/7 of 1, and F_c is analytic with |F_c| ≤ −log(1 − 2/7) < 1/2.
    {#C10.3.3-11-6-1} For unit X, Y ∈ 𝔤 and bonds b, b′, Cauchy's estimate in (s, s′) for B = sX1_b + s′Y1_{b′}, |s|, |s′| ≤ r_P/(4Lℓ), so that Lℓ sup|B| ≤ r_P/2, bounds the coefficient of ss′ in F_c, 2Lℓ·C̃^{(2)}(X1_b, Y1_{b′})(c), by ½(4Lℓ/r_P)² = 8(Lℓ)²/r_P². So |C̃^{(2)}(X1_b, Y1_{b′})(c)| ≤ 4Lℓ/r_P².
  {#C10.3.3-11-7} h(c) inverts the coefficient of B(b₀(c)) in (Q̄₁(W)B)(c), so that Q̄₁(W)h = I, as b₀(c′) for c′ ≠ c is no bond of B(c₋) ∪ B(c₊). It is RG I's h (p.267 l.21–23, LQ̃h = I in the units of #C10.1.8-2), whose Q̃ is the plain linear part. By (B1) at n = 1 (#C10.1.5–#C10.1.5-1) the two linear parts differ by D̄Θ₁, and Θ₁B(y) involves B only on the contours in B(y) (CMP 98 (97)). Since b₀(c) joins B(c₋) to B(c₊), it lies on none of these contours, so the coefficient of B(b₀(c)) is the same.
    {#C10.3.3-11-7-0} In (124), b₀(c) lies on [x, x′] for the L points x of B(c₋) on the line of c and on no contour, and for these x the transports to c₋ reduce to T_c, the transport along c from c₋ to b₀(c), as their contours run along that line. So the coefficient is L^{−d}(1 + e_c)T_c, with e_c from the third and fifth terms of (124).
    {#C10.3.3-11-7-1} The plaquettes of W₀ are within O(1)Mα₀/L² of 1 (#C10.3.3-11-1), so the operators of those terms are O(1)(Mα₀ + Lα₁): O(L²) times that plaquette bound (p.036 l.31–33), with Proposition 7's change (p.043 l.15–17). So |e_c| ≤ O(1)L^{d−1}(Mα₀ + Lα₁) ≤ ½ for O(1)L^d(Mα₀ + α₁) ≤ ½, and |T_c^{−1}| ≤ 4/3 as for the transports of #C10.3.3-11, so |h(c)| ≤ (8/3)L^d.
  {#C10.3.3-11-8} Hence the J-term is ℓ^{2d}Σ_{b,b′}⟨B(b), K(b, b′)B(b′)⟩, with K supported on the pairs in one B(c₋) ∪ B(c₊), at distance ≤ (d + 1)L, each pair lying in at most 2d of these sets. For unit X, Y ∈ 𝔤, |⟨X, K(b, b′)Y⟩| ≤ 2ℓ^{−d}·2d·e^{δ₁′d}c_eB₀^{cx}α_JL^{−3}ℓ^{−3}·(8/3)L^d·4Lℓ/r_P², and on 𝔤^c the norm is at most 4N times this, by trace duality (#C10.3.15-4) and Y = Re Y + i Im Y.
    {#C10.3.3-11-8-1} So |K(b, b′)| ≤ C_𝐉ℓ^{−2}ℓ^{−d}e^{−δ₁′d(b,b′)}, {#D.C_𝐉} C_𝐉 := (512/3)Ndr_P^{−2}c_eB₀^{cx}α_JL^{d−2}e^{δ₁′(2d+1)L}, a constant of d, L, and G times α_J, and |Δ_{(𝐔,𝐉)}(y, y′)| ≤ (B₀^{cx} + a + C_𝐉 + C_𝐆)ℓ^{−2}ℓ^{−d}e^{−δ₁′d(y,y′)}.
{#C10.3.4} *The Multipliers.* U^A_ax minimises A_ε on {M^jU = V}. Since A_ε is gauge invariant and M^j is gauge covariant (CMP 98 (11)), U^A minimises A_ε on {M^jU = V^w}. U^A satisfies 𝒟_j's condition on 𝐔 by #C10.3.14 at t = 1, which lies in its disc since 16ρ_j ≤ α₁ (#C10.3.51). So 𝒬(U^A) = Q_j^{pl}(U^A) is onto by #C10.1.6-1 with n = j. Hence J(U^A) annihilates ker 𝒬(U^A), and J(U^A) = 𝒬(U^A)*λ^A for a unique bond field λ^A on T_{a_j}.
  {#C10.3.4-0-1} Likewise J(U^B) = 𝒬(U^B)*λ^B. By the chain rule 𝒬(U^B) = 𝒬(Ũ)Q₁^{pl}(U^B) (#C10.3.1-6), and both factors are onto. Q₁^{pl}(U^B) = dM(U^B) is onto since T^{pl}(U^B) has spectrum in [m_Q^{pl}/2, M̃_Q^{pl}] (#C9.4.3-4, #C9.4.5-2). 𝒬(Ũ) is onto by #C10.1.6-1 with n = j, since Ũ satisfies 𝒟_j's condition on 𝐔 by #C10.3.14 at t = 0.
{#C10.3.4-1} Differentiating the gauge covariance of the averaging (CMP 98 (11)) gives 𝒬(U)D_Uω = D_{V_U}(ω restricted to T_{a_j}) for every gauge parameter ω, with D_U the covariant difference. So D_U*𝒬(U)*λ = (a_j/η)^d1_{T_{a_j}}D_{V_U}*λ.
{#C10.3.4-2} With D_U*J(U) = 0 (PBG (3.117), the gauge invariance of the action), both multipliers are covariantly divergence-free, each at its own block field:

{#C10.3.5} D_{V^w}*λ^A = D_V*λ^B = 0.

{#C10.3.6} Ad(w)λ^B denotes the gauge transform of λ^B by w, (Ad(w)λ^B)(c) := Ad(w(c₋))λ^B(c), which satisfies D_{V^w}*Ad(w)λ^B = 0 by the same covariance.

{#C10.3.7} For ν_λ := 𝒬′*λ^B on T_ℓ (not the exponent ν of LFR I p.198) the same covariance of the last step gives D̄*ν_λ = 0, D̄ the covariant difference at the common block field M^{j−1}Ũ = M^jU^B on T_ℓ.
{#C10.3.7-1} So by (B2) (#C10.1.6), Q_m^{pl}*ν_λ = Q_m*ν_λ in both runs: J(U^B) = Q^B_j*ν_λ, and the intermediate current J′_j below is Q^A_{j−1}*ν_λ, with PBG's Q_m.

{#C10.3.8} Every field X on T_ε satisfies X = Q₁^{pl}ℒX, with ℒ the plain lift of #C9.4.3, so by the chain rule dA_ε(Ũ)[X] = dA_{ε/L}(U^B)[ℒX] + db(U^B)[ℒX] = ⟨𝒬(Ũ)X, λ^B⟩ + db(U^B)[ℒX].
{#C10.3.8-1} With (9.5) at scale j this is the exact current identity, which extends (9.7) from ker 𝒬(Ũ) to all fields:

{#C10.3.9} (10.3a) J(Ũ) = 𝒬(Ũ)*λ^B + ℒ*(D*r₁ + r₀).

{#C10.3.10} Let H₀(U) := G₀Q_j(U)*(Q_j(U)G₀Q_j(U)*)^{−1}, with G₀ the operator of PBG p.421 for the j-step problem and Q_j(U) PBG's j-step double-bar averaging (#C10.1.4-1).
{#C10.3.10-1} It is PBG's H of (3.126) at 𝐉 = 0, since G = G₀ there by (3.130).
{#C10.3.10-2} So H₀ satisfies (3.133) and (Q_jG₀Q_j*)^{−1} satisfies (3.132) at real U satisfying (3.35) at scale j, by Theorem 3.12 at 𝐉 = 0 with #C10.3.3-6 (#C10.3.3-10). At the 𝐔 of (3.37) at scale j they satisfy these bounds with B₀^{cx}, δ₁′, and ½δ₁′ (BP_PBG_COMPLEX.md #BX.1-3 at 𝐉 = 0, under the conditions of #C10.3.3-9).
{#C10.3.10-3} For a bond y of T_{a_j}, an element e of the Lie algebra with |e| = 1, and e_y the field equal to e at y and 0 elsewhere, |H₀e_y| ≤ B₀e^{−½δ₁d(·,y)} and |∇H₀e_y| ≤ B₀a_j^{−1}e^{−½δ₁d(·,y)}, with d in units of a_j.
{#C10.3.10-4} By (B1) at n = j (#C10.1.5-1), 𝒬(U)H₀ = 1 − D_{V_U}Θ_jH₀, so for every λ with D_{V_U}*λ = 0, ⟨𝒬H₀e_y, λ⟩ = ⟨e_y, λ⟩ − ⟨Θ_jH₀e_y, D_{V_U}*λ⟩ = ⟨e_y, λ⟩. λ^A is divergence-free at V^w = V_{U^A} and λ^B at V = V_Ũ, so

{#C10.3.11} ⟨e, λ^A(y)⟩ = f_y(U^A), ⟨e, λ^B(y)⟩ = f_y(Ũ) − a_j^{−d}db(U^B)[ℒH₀(Ũ)e_y], f_y(U) := a_j^{−d}dA_ε(U)[H₀(U)e_y],

{#C10.3.12} the second by (10.3a).

{#C10.3.13} The first variation of the action is bounded by the plaquette curvatures.
{#C10.3.13-1} For 𝐔 satisfying (3.37) and a field X, |dA_η(𝐔)[X]| ≤ c_WΣ_pη^{d−2}|∂𝐔(p) − 1||(D_𝐔X)(p)|, with c_W a constant of G. Indeed, the derivative of the plaquette term ½tr(2 − 𝐔(∂p) − 𝐔(∂p)^{−1}) in the direction X is −½i tr[η²(D_𝐔X)(p)(𝐔(∂p) − 𝐔(∂p)^{−1})], which vanishes at 𝐔(∂p) = 1.

{#C10.3.14} Along U(t) := e^{itεA′*}Ũ with |t| ≤ α₁/(8ρ_j), U(t) satisfies (3.37) at scale j. Indeed, under α₀^P ≤ α₀, Ũ satisfies (3.35) at the scale a_j with PBG's M = M_P and α₀, by #C9.8.4–#C9.8.4-4 with a_j in place of a, since #C9.7.1-15 runs §9 at the scale a_j. Also |tA′*| ≤ α₁/(2a_j) and |∇_Ũ(tA′*)| ≤ α₁/(2a_j²).
{#C10.3.14-1} Its plaquettes satisfy |∂U(t)(p) − 1| ≤ (6/5)·2C₀ε₁ε²/a_j² + (3/2)α₁ε²/a_j² ≤ 2α₁ε²/a_j² when 5C₀ε₁ ≤ α₁ (#C9.3.3-1 for Ũ).
{#C10.3.14-2} Indeed, moving the four factors Ũ(b) of ∂U(t)(p) to the right writes it as e^{iZ₁}⋯e^{iZ₄}∂Ũ(p), with Z_k the transported values of tεA′*, Σ_k|Z_k| ≤ 2α₁ε/a_j. On two of the four terms these transports differ from those of the covariant differences by Ad(∂Ũ(p)), within 2|∂Ũ(p) − 1| ≤ 4C₀ε₁ε²/a_j² of the identity. So Σ_kZ_k is the covariant curl, at most 2ε²sup|∇_Ũ(tA′*)| ≤ α₁ε²/a_j², plus at most 4C₀ε₁(ε²/a_j²)·2α₁ε/a_j ≤ (1/15)α₁ε²/a_j², by ε/a_j ≤ 1/3 (j ≥ 1, L ≥ 3 by #T1.3) and 40C₀ε₁ ≤ 1 (5C₀ε₁ ≤ α₁ ≤ 1/8).
{#C10.3.14-3} With c_B the constant of the BCH bound |(1/i)log(e^{iX}e^{iY}) − X − Y| ≤ c_B|X||Y| for |X|, |Y| ≤ r_{BCH} (complex X, Y, c_B and r_{BCH} constants of G), applied three times, e^{iZ₁}⋯e^{iZ₄} = e^{iY_p} with |Y_p − Σ_kZ_k| ≤ 2c_B(Σ_k|Z_k|)², so |Y_p| ≤ (16/15 + 8c_Bα₁)α₁ε²/a_j², when 4α₁ ≤ r_{BCH} and 4c_Bα₁ ≤ 1.
{#C10.3.14-4} Under 64c_Bα₁ ≤ 1 and 8α₁ ≤ 1, e^{|Y_p|} ≤ 6/5 and |Y_p|e^{|Y_p|} ≤ (3/2)α₁ε²/a_j², and |e^{iY_p}h − 1| ≤ e^{|Y_p|}|h − 1| + |Y_p|e^{|Y_p|} for h = ∂Ũ(p) gives the bound.
{#C10.3.14-5} Also |D_{U(t)}H₀(U(t))e_y| ≤ 3B₀^{cx}a_j^{−1}e^{−½δ₁′d(·,y)} (#C10.3.10-2; two differences and the transports).
{#C10.3.14-6} Let c_e := sup a^{−d}max(Σ_pη^de^{−½δ₁′d(p,y)}, Σ_bη^de^{−½δ₁′d(b,y)}), where the sums run over the plaquettes and over the bonds of T_η, d is in units of a, and the sup runs over the spacings η ≤ a and the bonds y of T_a. It is a constant of d and δ₁′, used at a = a_j here and at a = ℓ in #C10.3.3-11-5.
{#C10.3.14-8} Then the analytic function t ↦ f_y(U(t)) is bounded by 6c_Wc_eB₀^{cx}α₁a_j^{−3} on the disc, and Cauchy's estimate, for 16ρ_j ≤ α₁, gives |f_y(U^A) − f_y(Ũ)| ≤ (16ρ_j/α₁)·6c_Wc_eB₀^{cx}α₁a_j^{−3} = 96c_Wc_eB₀^{cx}ρ_ja_j^{−3}.
{#C10.3.14-9} At t = 0, with |∂Ũ − 1| ≤ 2C₀ε₁ε²/a_j², the same computation gives |f_y(Ũ)| ≤ 6c_Wc_eC₀B₀ε₁a_j^{−3}.

{#C10.3.15} For the artifact term, ℒ is the plain lift of #C9.4.3, built from Q₁^{pl}.
{#C10.3.15-1} Its correction is exponentially localised at the rate δ_Q^{pl} of (Q₁^{pl}Q₁^{pl}*)^{−1} at U^B (#C9.4.5-2, #C9.4.7), and PBG's rate δ₁ is taken ≤ δ_Q^{pl}, as a smaller rate only weakens (3.132)–(3.133). With #C9.4.7-1's sup and gradient bounds at the scale a_j this gives |ℒH₀(Ũ)e_y| ≤ C_ℒB₀e^{−½δ₁d(·,y)} and |DℒH₀(Ũ)e_y| ≤ 3C_ℒB₀a_j^{−1}e^{−½δ₁d(·,y)}.
{#C10.3.15-2} #C9.4.7-1's C_ℒ, a constant of L, d, G, and C₀, covers the sum over the intermediate point and the ratio B₀(γ)/B₀, with B₀(γ) PBG's constant of d and L at the Hölder exponent γ = γ_H of (10.6) (#C10.4.116), printed β in (3.133). All are uniform in k, K, ε, and the volume.
{#C10.3.15-3} So (9.5) at scale j gives a_j^{−d}|db(U^B)[ℒH₀(Ũ)e_y]| ≤ 4c_eC_rC_ℒB₀(ε/a_j)ε₁a_j^{−3}.
{#C10.3.15-4} For the normalised trace pairing and X ∈ 𝔤, |X| ≤ N sup_{|e|≤1}|⟨e, X⟩|, with N the matrix size of table #T6.23's G ⊂ U(N) (trace duality: take e = X/|X| and use tr(X*X) ≥ |X|²). Since e is arbitrary with |e| = 1, this gives

{#C10.3.16} a_j³|λ^A − λ^B| ≤ x_λ(ρ_j + (ε/a_j)ε₁), a_j³|λ^B| ≤ B_λε₁, x_λ := Nc_e(96c_WB₀^{cx} + 4C_rC_ℒB₀), B_λ := Nc_eB₀(6c_WC₀ + 4C_rC_ℒ).

{#C10.3.17} *The Adjoint Averaging.* For a real configuration W on T_η put κ_W := sup_p|∂W(p) − 1|, W̄ := MW on T_{Lη}, and Q₁^{pl}(W) = dM(W) (#C3.2-1).
{#C10.3.17-1} For every bond field ν on T_{Lη}:

- {#C10.3.18} (i) D_W*Q₁^{pl}(W)*ν = L^d1_{T_{Lη}}D_{W̄}*ν;
- {#C10.3.19} (ii) if c_{av}L²κ_W ≤ 1/8, with c_{av} a constant of d and G, then sup|Q₁^{pl}(W)*ν| ≤ (1 + c_QL^{d+1}κ_W)sup|ν| + L^{d−1}·Lη sup|D_{W̄}*ν|, with c_Q := 10(d + 1)c_{av}.

{#C10.3.20} (i) is the one-step case of #C10.3.4-1's identity. (ii) is derived from RG I (0.4) (#C10.1.4-0-2) in balaban_proofs/BP_CMP98_ADJOINT_AVERAGING.md (#C10.3.21–#C10.3.24-3). Its condition holds at the averages of (a) (#C10.3.24-4).

{#C10.3.25} *(a) The Composite.* Let U be a real configuration on T_η with block field V_U = M^nU, a_j = L^nη, and κ_U ≤ 2C₀ε₁η²/a_j², and put W_i := M^iU on T_{L^iη}.
{#C10.3.25-1} CMP 98 Proposition 2 ((52), (54)), applied to the i-fold averages, gives κ_{W_i} ≤ 4C₀ε₁L^{2i}η²/a_j² when 2C₀ε₁ ≤ c₂.
{#C10.3.25-2} For μ on T_{a_j} with D_{V_U}*μ = 0 put μ_n := μ and μ_i := Q₁^{pl}(W_i)*μ_{i+1}, so that 𝒬(U)*μ = μ_0 by the chain rule.
{#C10.3.25-3} By (i) every μ_i is divergence-free, and by (ii) sup|μ_i| ≤ (1 + 4c_QL^{d+1}C₀ε₁L^{2i}η²/a_j²)sup|μ_{i+1}|.
{#C10.3.25-4} Since Σ_{i<n}L^{2i}η²/a_j² ≤ (4/3)L^{−2}, the product of these factors is at most exp((16/3)c_QL^{d−1}C₀ε₁) ≤ 2 under

{#C10.3.26} (AQ) 8c_QL^{d−1}C₀ε₁ ≤ 1,

{#C10.3.27} and

{#C10.3.28} sup|𝒬(U)*μ| ≤ 2 sup|μ| for D_{V_U}*μ = 0, with sup|μ_i| ≤ 2 sup|μ| at every level.

{#C10.3.29} *(b) The Difference.* Let U and U′ = e^{iηA}U both satisfy the hypotheses of (a), with block fields V_U and V_{U′} = V_U^w for a gauge transformation w on T_{a_j}, and put W′_i := M^iU′.
{#C10.3.29-1} For μ with D_{V_U}*μ = 0 put μ′_n := Ad(w)μ, which is divergence-free at V_{U′}, and μ′_i := Q₁^{pl}(W′_i)*μ′_{i+1}, so that 𝒬(U′)*Ad(w)μ = μ′_0.
{#C10.3.29-2} Apply CMP 98 (159)–(163) (p.042) in the units of T_{a_j} to the i-fold averages, i ≤ n, with A real. (159) writes W′_i(b)W_i(b)^{−1} as a product of unitary factors, so |W′_i(b)W_i(b)^{−1} − 1| ≤ 2|v_i − 1| + |Ū̄′^i_b − 1| ≤ c_vL^iη sup|A| on every bond of T_{L^iη}, by (161), (163), and Σ_{i′<i}L^{i′+1} ≤ (3/2)L^i. Here {#D.c_v} c_v := 3c_{(163)} + 2, where c_{(163)}, the O(1) of (163), is a constant of d. This holds when U satisfies (52) with α₀ = 2C₀ε₁ (the hypotheses of (a)) below §E's threshold for α₀ (p.042 l.16–17, p.043 l.10) and a_j sup|A| is below the α₁ of (158).
{#C10.3.29-3} Let δ^μ_i := sup|μ′_i − μ_i|, so that δ^μ_n ≤ sup|Ad(w) − 1| sup|μ| and

{#C10.3.30} μ′_i − μ_i = Q₁^{pl}(W′_i)*(μ′_{i+1} − μ_{i+1}) + [Q₁^{pl}(W′_i) − Q₁^{pl}(W_i)]*μ_{i+1}.

{#C10.3.31} The divergence of the difference field is the transport mismatch alone, D*_{W′_{i+1}}(μ′_{i+1} − μ_{i+1}) = −(D*_{W′_{i+1}} − D*_{W_{i+1}})μ_{i+1}, at most 4dc_v sup|A| sup|μ_{i+1}|.
{#C10.3.31-1} So by (ii) the first term is at most (1 + c_QL^{d+1}κ_{W′_i})δ^μ_{i+1} + 4dc_vL^{d−1}L^{i+1}η sup|A| sup|μ_{i+1}|, and the defect does not accumulate over the levels.
{#C10.3.31-2} In the second term the weights of the column of BP #C10.3.21–#C10.3.24 are fixed, of total at most 1 + 2dL^{d−1} + L^{d−1} ≤ (2d + 2)L^{d−1} (BP #C10.3.24-1, #C10.3.21-5). Each path term is a product of one transport along at most (2d + 1)L bonds (Ad(W(c))P_{b,Γ′} being one, BP #C10.3.21-3) and at most four of dlog_h, dexp_{Y_c}, Ad(h), and Ad(e^{iY_c}) or their adjoints, each of norm ≤ 9/8 at W_i and W′_i (BP #C10.3.24). BP #C10.3.21-4's term is a transport along c times Ad(e^{iY_c}) minus an average of products of three of them, a difference of norm ≤ 1/8 + (9/8)³ − 1 ≤ 5/8.
{#C10.3.31-3} Let {#D.k_G} k_G ≥ 2 be a constant of G bounding the Lipschitz constants of log, dlog, dexp, and Y ↦ Ad(e^{iY}), and of their adjoints, on the matrix balls |g − 1| ≤ 1/16 and |Y| ≤ 1/8, where they are analytic. With v := c_vL^iη sup|A|, the transports and the holonomies h change by at most 2(2d + 1)Lv and (2d + 1)Lv, so Y_c by at most k_G(2d + 1)Lv and each factor by at most k_G²(2d + 1)Lv.
  {#C10.3.31-3-1} So each path term changes by at most (9/8)⁴(2 + 4k_G²)(2d + 1)Lv ≤ 5(9/8)⁴k_G²(2d + 1)Lv, as k_G ≥ 2. The term of BP #C10.3.21-4 changes by at most (1 + 3(9/8)²)k_G²(2d + 1)Lv + (5/8)·2(2d + 1)Lv, which is less. So the second term is at most c_DL^{d−1}c_vL^{i+1}η sup|A| sup|μ_{i+1}| with c_D := 9(2d + 1)(2d + 2)k_G². With sup|μ_{i+1}| ≤ 2 sup|μ|, the product of the factors at most 2, and Σ_{i<n}L^{i+1}η ≤ (3/2)a_j ≤ 2a_j,

{#C10.3.32} sup|𝒬(U′)*Ad(w)μ − 𝒬(U)*μ| ≤ (C′_Qa_j sup|A| + 2 sup|Ad(w) − 1|)sup|μ| for D_{V_U}*μ = 0, C′_Q := 8(c_D + 4d)c_vL^{d−1}.

{#C10.3.33} For w = 1, the case M^nU′ = M^nU, the last term is absent.

{#C10.3.34} *The Size of w.* Write U^A = U₁Ũ bondwise, U₁(b) = e^{iεA′*(b)}, as in CMP 98 §C with U₀ = Ũ.
{#C10.3.34-1} By CMP 98 (86)–(87) and (99), the axial transformation u has u(y) = v_j(y)^{−1} at the points y of T_{a_j}, with v_j(y) = ∏_{i=0}^{j−1}(\overline{\bar R^i_{0,y}\bar{\bar U}^i_1}) of (97). By (88), (92), and (97), M^jU^A = (M^jU^A_ax)^{v_j}, so w = v_j.
{#C10.3.34-2} By (105) each factor is the exponential of the block mean over x ∈ B(y) of (1/i)log(\bar R^i_{0,y}\bar{\bar U}^i_1)(y, x), the contour variable (0.11) of the i-fold double-bar average (#C10.1.4-1-1), the group average of its transports along the contours of 𝐆(y, x), each of at most dL bonds of T_{L^iε}.
{#C10.3.34-3} The norm on 𝔤, the operator norm of table #T6.23, is Ad-invariant, so the conjugations R are isometric, and |(1/i)log(g₁⋯g_m)| ≤ Σ_k|(1/i)log g_k| whenever the right side is < π. For unitary u let φ(u) be the largest modulus of its eigenvalue angles, so |(1/i)log u| = φ(u), and φ(u) ≤ θ < π if and only if Re⟨v, uv⟩ ≥ cos θ for every unit vector v. The angle between g*v and hv is at most the angle between g*v and v plus that between v and hv, so φ(gh) ≤ φ(g) + φ(h) while the sum is < π.
  {#C10.3.34-3-1} The logarithm of the product lies in i𝔤 by the open-closed argument of BP #C10.3.21-7-2 along s ↦ ∏_ke^{s log g_k}, which holds for |X| < π, since then |ad X| ≤ 2|X| < 2π.
{#C10.3.34-4} Let θ_i := sup_b|(1/i)log(\bar{\bar U}^i_1)_b|, so θ_0 = ε sup|A′*| ≤ 4L^{−j}ρ_j.
{#C10.3.34-5} CMP 98 Proposition 3 ((122)–(123)) and (126) (#C10.1.4-1-1-1) for the step from i to i + 1, with V₀ = M^iŨ, whose plaquettes are at most α₀^{(i)} := 4C₀ε₁L^{2(i−j)} by (a), gives θ_{i+1} ≤ Lθ_i(1 + c₁₂₄L²α₀^{(i)} + C₁^{(123)}Lθ_i) when α₀^{(i)} ≤ c₃ and θ_i ≤ c₃.
  {#C10.3.34-5-1} Here α₀^{(i)} is the α₀ of (109), and the linear part of (122) is at most (1 + c₁₂₄L²α₀^{(i)})θ_i by (126), with {#D.c₁₂₄} c₁₂₄ the O(1) of (126), a constant of d and G. The quadratic part (123) is at most C₁^{(123)}L²θ_i², with C₁^{(123)} the constant of CMP 98 (123) (not VAR's C₁ of #C9.4), and the logarithm is L times the linear part plus the quadratic part by (122).
{#C10.3.34-6} Since Σ_{i<j}L²α₀^{(i)} ≤ (16/3)C₀ε₁ and, inductively, Σ_{i<j}Lθ_i ≤ 16ρ_j, the product of the factors is at most exp((16/3)c₁₂₄C₀ε₁ + 16C₁^{(123)}ρ_j) ≤ 2 under c₁₂₄C₀ε₁ ≤ 1/16 and C₁^{(123)}ρ_j ≤ 1/64, and θ_i ≤ 8L^{i−j}ρ_j.
{#C10.3.34-7} By #C10.3.34-3 the transports e^{iA_Γ} along the contours of 𝐆(y, x) have |A_Γ| ≤ s_i := dLθ_i ≤ 8dρ_j. Their group average e^{iZ} satisfies (0.10), Σ_Γ(1/i)log(e^{iA_Γ}e^{−iZ}) = 0. So the BCH bound of #C10.3.14-3 gives |Z| ≤ s_i + c_Bs_i|Z| while |Z| ≤ r_{BCH}, hence |Z| ≤ (4/3)s_i ≤ (2/3)r_{BCH} under 32c_Bdρ_j ≤ 1 and 16dρ_j ≤ r_{BCH}. Along the averages of e^{itA_Γ}, t ∈ [0, 1], |Z| is continuous and starts at 0, so it never reaches r_{BCH}, and |Z| ≤ (4/3)s_i at t = 1.
{#C10.3.34-7-1} So each factor of v_j has |(1/i)log| ≤ (4/3)dLθ_i. Since L is odd (#T10.43), L ≥ 3 and Σ_{i<j}Lθ_i ≤ 8ρ_jΣ_{i<j}L^{i−j+1} ≤ 12ρ_j, so |(1/i)log w| ≤ (4/3)·12dρ_j = 16dρ_j.
{#C10.3.34-8} By (106), u(x) at a point x of T_ε is a product over i < j of conjugated brackets, with x_i the points of CMP 98 (101) (x_0 = x). Each bracket is the inverse of the i-th factor of (97) at x_{i+1} times the contour variable of \bar{\bar U}^i_1 from x_{i+1} to x_i, so it has |(1/i)log| ≤ (8/3)dLθ_i. The sum of these bounds is at most (8/3)·12dρ_j = 32dρ_j.
{#C10.3.34-9} Hence

{#C10.3.35} sup_{T_ε}|(1/i)log u| ≤ c_wρ_j, sup_{T_{a_j}}|(1/i)log w| ≤ c_wρ_j, c_w := 32d,

{#C10.3.36} under 2C₀ε₁ ≤ c₂ (for α₀^{(i)}, #C10.3.25-1), 4C₀ε₁ ≤ c₃, 8ρ_j ≤ c₃, c₁₂₄C₀ε₁ ≤ 1/16, C₁^{(123)}ρ_j ≤ 1/64, c_wρ_j < π, 32c_Bdρ_j ≤ 1, and 16dρ_j ≤ r_{BCH}.
{#C10.3.36-1} Ad(w) = e^{i ad_Y}, Y := (1/i)log w, and every Ad(e^{isY}) is an isometry of the norm of #T6.23 (#C10.3.34-3), so |Ad(w) − 1| ≤ ∫₀¹|ad_Y Ad(e^{isY})|ds ≤ |ad_Y| ≤ c_brc_wρ_j, with c_br := sup|[X, X′]|/(|X||X′|).

{#C10.3.37} *The Intermediate Current.* Let J′ = J′_j := 𝒬(Ũ)*λ^B and

{#C10.3.38} δ𝐉 := J(U^A) − J′ = 𝒬(U^A)*(λ^A − Ad(w)λ^B) + [𝒬(U^A)*Ad(w)λ^B − 𝒬(Ũ)*λ^B].

{#C10.3.39} Ũ satisfies the hypotheses of (a) by #C9.3.3-1, U^A and U^B by (9.2) at scale j (#C9.7.1-15), and U^A = e^{iεA′*}Ũ with a_j sup|A′*| ≤ 4ρ_j. λ^A − Ad(w)λ^B is divergence-free at V^w and λ^B at V, and a_j³|λ^A − Ad(w)λ^B| ≤ a_j³|λ^A − λ^B| + |Ad(w) − 1|a_j³|λ^B| ≤ (x_λ + c_brc_wB_λ)(ρ_j + (ε/a_j)ε₁), by ε₁ ≤ 1.
{#C10.3.39-1} So (a) at U^A, (b) with U = Ũ and U′ = U^A, and the multiplier bounds give, with ε₁ ≤ 1,

{#C10.3.40} a_j³|δ𝐉| ≤ x_J(ρ_j + (ε/a_j)ε₁), x_J := 2x_λ + (4C′_Q + 4c_brc_w)B_λ, a_j³|J′| ≤ 2B_λε₁, a_j³|J(U^B)| ≤ 2B_λε₁.

{#C10.3.41} J′ is real, and it differs from J(Ũ) by the artifact term of (10.3a).

{#C10.3.42} *The Alignment Estimate.* The path (𝐔(t), 𝐉(t)) := (e^{itεA′*}Ũ, J′ + tδ𝐉), t ∈ ℂ, joins the pair (Ũ, J′) at t = 0 to the diagonal point (U^A, J(U^A)) at t = 1.
{#C10.3.42-1} Let R_𝒟 := min(α₁/(8ρ_j), α_J/(4x_J(ρ_j + (ε/a_j)ε₁))).
{#C10.3.42-2} For |t| ≤ R_𝒟, 𝐔(t) satisfies (3.37) at scale j as in #C10.3.14, and |𝐉(t)| ≤ (2B_λε₁ + ¼α_J)a_j^{−3} < α_Ja_j^{−3} when 4B_λε₁ ≤ α_J.
{#C10.3.42-3} So the path stays in 𝒟_j, and t ↦ Δ_{(𝐔(t),𝐉(t))}(y, y′) is analytic and bounded by (B₀^{cx} + a + C_𝐉 + C_𝐆)ℓ^{−2}ℓ^{−d}e^{−δ₁′d(y,y′)} (#C10.3.3-10–#C10.3.3-11-8-1).
{#C10.3.42-4} Cauchy's estimate with R_𝒟 ≥ 2 gives

{#C10.3.43} (10.3) |Δ^A_{U^A_j}(y, y′) − Δ^A_{(Ũ_j, J′_j)}(y, y′)| ≤ [16ρ_j/α₁ + 8x_J(ρ_j + (ε/a_j)ε₁)/α_J]·(B₀^{cx} + a + C_𝐉 + C_𝐆)ℓ^{−2}ℓ^{−d}e^{−δ₁′d(y,y′)},

{#C10.3.44} where both forms are run A's (fine lattice T_ε, m = j − 1), and the left one is on the diagonal.
{#C10.3.51} R_𝒟 ≥ 2 is 16ρ_j ≤ α₁ and 8x_J(ρ_j + (ε/a_j)ε₁) ≤ α_J. With it, the conditions of this subsection are those at #C10.3.1, #C10.3.14-1, #C10.3.14-3–#C10.3.14-4, #C10.3.15-1 (#C9.4.5-2's), #C10.3.25-1, (AQ), #C10.3.29-2 (4ρ_j below the α₁ of CMP 98 (158), as a_j sup|A′*| ≤ 4ρ_j, and 2C₀ε₁ below §E's threshold for α₀), #C10.3.34-6, #C10.3.36, #C10.3.39-1 (ε₁ ≤ 1), and #C10.3.42-2, 2C₀ε₁ ≤ c₃ of #C10.1.4-3, and α₀^P ≤ α₀ with #C9.8.4-4's conditions at the scale a_j (#C10.3.14).
  {#C10.3.51-0} Apart from δ₁ ≤ δ_Q^{pl} (#C10.3.15-1), which is a choice of PBG's rate, all are smallness conditions on ε₁, since ρ_j ≤ C_G(ε₀)ε₁. Their threshold depends on ε₀, which is fixed before γ, and is uniform in j.
    {#C10.3.51-0-1} Besides them are conditions on PBG's fixed M = M_P, α₀, and α₁: O(1)M_Pα₀ small for the series (p.396 l.32; #C10.3.3-8), α₁ below PBG's a₁ of Theorem 3.4 (p.400, not VAR's a₁; #C10.3.3-8), M_P ≥ M₃ and M_Pα₀ + α₁ + α_JL^{−3} ≤ a_cx (#C10.3.3-9), 64c_Bα₁ ≤ 1, 8α₁ ≤ 1, 4α₁ ≤ r_{BCH}, and 2O(1)dLα₁ ≤ log(4/3) (#C10.3.3-11, #C10.3.14-3–#C10.3.14-4).
    {#C10.3.51-0-2} They also include O(1)Mα₀ ≤ c₂, 8c_Bδ′ ≤ 1, 4δ′ ≤ r_{BCH}, and c_{GM}δ′ ≤ 1/66 (#C10.3.3-11-1–#C10.3.3-11-2-1), O(1)Mα₀ and O(1)Lα₁ below the thresholds of CMP 98 Propositions 6 and 7 and O(1)Lα₁ ≤ r_P/3 (#C10.3.3-10-1, #C10.3.3-11-6-0–#C10.3.3-11-6-0-1), O(1)L^d(Mα₀ + α₁) ≤ ½ (#C10.3.3-11-7-1), and 4O(1)Mα₀ ≤ 1, 4c_BO(1)Mα₀ ≤ 1, O(1)Mα₀ ≤ r_{BCH}/2, and 2(α₀ + α₁/(ML)) below Theorem 3.12's threshold for α₀ (#C10.3.3-10-0–#C10.3.3-10-0-2).
{#C10.3.51-1} For an analytic functional of the background alone the path 𝐔(t) suffices, with the factor 16ρ_j/α₁.

### 10.4 The Aligned Comparison: Chain Rule, Bilinear Defect, Oscillation {#CS10.4}

{#C10.4.1} Compare Δ^A at the pair (Ũ_j, J′_j) of §10.3 (T_ε, m = j − 1) with Δ^B at U^B := U^B_{j+1} on its diagonal (T_{ε/L}, m = j).
{#C10.4.1-1} (Ũ_j, J′_j) is a real pair of 𝒟_j (#C10.3.41, and #C10.3.42-2 at t = 0). Run B's pair (U^B, J^B(U^B)) on T_{ε/L} is in the first case of #C10.2.1 at the same ℓ. Indeed, U^B satisfies VAR (2) on T_{ε/L} at 2C₀ε₁ by (9.2), as MW does at #C9.3.3-1–#C9.3.3-2 without the averaging. So #C9.8.4–#C9.8.4-4 at the scale a_j (as at #C10.3.14) and #C10.2.1-0-1 give it (3.35) at the scale ℓ. Also |J^B(U^B)| ≤ 2B_λε₁a_j^{−3} < α_Jℓ^{−3} (#C10.3.40, #C10.3.42-2).
  {#C10.4.1-1-1} So §10.2 holds in both runs (#C10.2.1), with G₁ and H₁ built as on PBG p.421 l.12–17, from the form (3.127) through (3.128)–(3.129), with the run's current written for J.
{#C10.4.1-2} By (B4) of §10.1, Q^B_j = Q^A_{j−1}Q₁ exactly, where from here on Q₁ := Q̄₁(U^B) is the linear part of the one-step double bar at U^B, in place of the plain Q₁^{pl} = dM(U^B) of §9.4 and §10.3. ℒ is the lift built from this Q₁ as §9.4's lift is built from Q₁^{pl}: ℒg := Ig + Q₁*(Q₁Q₁*)^{−1}(g − Q₁Ig), with the interpolation I of *Regularity of the Lifts.* after (10.5′), where ℒ is bounded. Then Q₁ℒg = g.
{#C10.4.1-3} So Q₁ maps {Q^B_j𝒜 = B} into {Q^A_{j−1}A = B} and ℒ maps back.
{#C10.4.1-4} The plain Q₁^{pl} enters below only through the artifact current δJ := J^A(Ũ_j) − J′_j of (10.3a), and δJ only through the crude bound of *The Constraint Part of β.* After alignment the block fields M^{j−1}Ũ_j = M^jU^B coincide on the common lattice T_ℓ with its blocks and contour families, so hC̃^{(2)} and 𝐆^{(2)}, which depend on the background only through the block field (#C10.1.3-0–#C10.1.3-0-1), are the same polynomials in both runs.
{#C10.4.1-5} Let G_A^{−1} := Δ₁^A + D_AR_AD_A* on T_ε, with Δ₁^A := Δ₁ of VAR (79) at (Ũ_j, J′_j), and G_B^{−1} := Δ₁^B + D_BR_BD_B* on T_{ε/L}, with Δ₁^B at (U^B, J^B(U^B)). The a-terms contribute aℓ^{−2}⟨B′, B⟩ to both forms and cancel. Define the bilinear defect

{#C10.4.2} (10.4) β(𝒜′, 𝒜) := ⟨Q₁𝒜′, G_A^{−1}Q₁𝒜⟩ − ⟨𝒜′, G_B^{−1}𝒜⟩ for fields 𝒜, 𝒜′ on T_{ε/L}.

{#C10.4.3} With 𝒜^B := H₁^BB, 𝒜′^B := H₁^BB′, 𝒜^A := H₁^AB, 𝒜′^A := H₁^AB′, the polarised identity of §10.2 gives ⟨B′, P_AB⟩ = ⟨Q₁𝒜′^B, G_A^{−1}𝒜^A⟩, since Q₁𝒜′^B is admissible for run A, and ⟨B′, P_BB⟩ = ⟨𝒜′^B, G_B^{−1}𝒜^B⟩. Adding and subtracting ⟨Q₁𝒜′^B, G_A^{−1}Q₁𝒜^B⟩, and using ⟨𝒜′^A, G_A^{−1}E⟩ = 0 for E ∈ ker Q^A_{j−1}, gives

{#C10.4.4} (10.5) ⟨B′, (P_B − P_A)B⟩ = −β(𝒜′^B, 𝒜^B) + ⟨E′, G_A^{−1}E⟩, E := Q₁𝒜^B − 𝒜^A ∈ ker Q^A_{j−1}, E′ := Q₁𝒜′^B − 𝒜′^A.

{#C10.4.5} E is characterised by ⟨Q₁ℱ, G_A^{−1}E⟩ = β(ℱ, 𝒜^B) for every ℱ ∈ ker Q^B_j (both ⟨Q₁ℱ, G_A^{−1}𝒜^A⟩ and ⟨ℱ, G_B^{−1}𝒜^B⟩ vanish).
{#C10.4.5-1} Let Q := Q^A_{j−1}, G₁ := G₁^A, and H₁ := H₁^A at run A's pair, and let ℒ*β(·, 𝒜^B) be the field on T_ε that represents X ↦ β(ℒX, 𝒜^B).
{#C10.4.5-2} Every X ∈ ker Q is Q₁ℒX with ℒX ∈ ker Q^B_j, since Q^B_jℒ = QQ₁ℒ = Q. For X ∈ ker Q, ⟨X, G₁^{−1}E⟩ = ⟨X, G_A^{−1}E⟩, since the term aℓ^{−2}⟨QX, QE⟩ vanishes.
{#C10.4.5-3} So G₁^{−1}E − ℒ*β(·, 𝒜^B) = Q*κ for a field κ on T_ℓ, and QE = 0 gives κ = −(QG₁Q*)^{−1}QG₁ℒ*β(·, 𝒜^B).
{#C10.4.5-4} Hence

{#C10.4.6} E = G₁^Qℒ*β(·, 𝒜^B), G₁^Q := G₁ − G₁Q*(QG₁Q*)^{−1}QG₁ = (I − H₁Q)G₁,

{#C10.4.7} the Green operator on ker Q at run A's pair.
{#C10.4.7-3} The bounds of G₁^Q come from those at the pair (§10.3, *The Pair Class.*): G₁ obeys (3.42) without its Laplacian entry (Theorem 3.3 for G₁, through Theorem 3.12), (QG₁Q*)^{−1} obeys (3.132) with G₁, and H₁ obeys (3.133).
{#C10.4.7-4} Q is local: its kernel Q(z, ·) vanishes outside B^{j−1}(z₋) ∪ B^{j−1}(z₊) (CMP 98 p.031, after (91)), whose points w have d(z, w) ≤ 1 + d/2. Its sup norm is at most 2, by CMP 98 (126) at each of the j − 1 steps under 16c₁₂₄C₀ε₁ ≤ 1.
{#C10.4.7-5} G₁ decays at PBG's rate δ₀ of (3.42), and δ₁ ≤ δ₀ (#C10.4.66-3). So |(QG₁)(z, y′)| ≤ 2e^{(1+d/2)δ₀} times G₁'s bound at (z, y′), and e^{−½δ₁d(x,z)}e^{−δ₀d(z,y′)} ≤ e^{−½δ₁d(x,y′)}e^{−½δ₀d(z,y′)}. Hence H₁QG₁ obeys the bounds of (3.42) for G₁, entry by entry, with the decay rate ½δ₁ and with B₀ replaced by 2c_δ′B₀², where {#D.c_δ′} c_δ′ := e^{(1+d/2)δ₀}sup_xΣ_ze^{−½δ₀d(x,z)}. So G₁^Q = G₁ − H₁QG₁ obeys them with B₀ + 2c_δ′B₀².
{#C10.4.7-7} On the diagonal B′ = B the second term of (10.5) is ⟨E, G_A^{−1}E⟩ = ⟨E, G₁^{−1}E⟩ ≥ 0 (#C10.4.5-2), G₁^{−1} being positive definite at the pair (#C10.2.1).

{#C10.4.8} *Regularity of H₁.* PBG Theorem 3.12 (p.423 l.33–36) gives (3.133) and Theorem 3.10 for H₁ on both lattices: for B supported at y′ with |B(y′)| = 1, 𝒜 = H₁B satisfies |𝒜(x)| ≤ B₀e^{−½δ₁d(x,y′)}, |∇𝒜(x)| ≤ B₀ℓ^{−1}e^{−½δ₁d(x,y′)}, and ‖ζ∇𝒜‖_{γ_H} ≤ B₀(γ_H)ℓ^{−1−γ_H}e^{−½δ₁d(y,y′)} for ζ ∈ C₀^∞(Δ̃(y)), 0 < γ_H < 1 (the Hölder exponent γ_H, not table #T3.33's γ). So the oscillation of ∇𝒜 over any fine 4-cell of side 4ε, in the ℓ^∞ distance, is at most 𝔬(x) := 4^{γ_H}B₀(γ_H)(ε/ℓ)^{γ_H}ℓ^{−1}e^{−½δ₁d(x,y′)}.
{#C10.4.8-1} The curl D𝒜 and the divergence D*𝒜 are sums of 2 and of d differences, so their oscillations are at most 2𝔬(x) and d𝔬(x).
{#C10.4.8-2} If 6ε ≤ ℓ/2, a cell of side at most 6ε lies in the cube of side (3/2)ℓ about some y ∈ T_ℓ, on which a fixed cutoff ζ ∈ C₀^∞(Δ̃(y)) equals 1, where Δ̃(y) is the cube of side 2ℓ about y (PBG p.397 l.30–31). On that cube e^{−½δ₁d(y,y′)} ≤ e^{1/16}e^{−½δ₁d(x,y′)} for δ₁ ≤ 1/(10d).
  {#C10.4.8-2-1} If 6ε > ℓ/2, that is L^{j−1} < 12 (j = 1 among them), the oscillation over a cell of side at most 6ε is at most twice the sup of |∇𝒜| over it. The cell has ℓ¹ diameter at most 6dε ≤ 6dℓ, so this is at most 2e^{3/10}𝔰(x) ≤ 3𝔰(x), with 𝔰 of #C10.4.8-5. This is at most 𝔬(x), since 4^{γ_H}(ε/ℓ)^{γ_H} > 3^{−γ_H} ≥ ⅓, once B₀(γ_H) ≥ 9B₀. B₀(γ_H) is taken to satisfy this and to cover e^{1/16} and the norm of ζ in (3.133), which changes only B₀(γ_H).
{#C10.4.8-3} The distance in the Hölder quotients is PBG's |x − x′| of (3.40), with the transports along a shortest contour Γ_{x,x′}.
{#C10.4.8-4} The oscillations below are taken over sets of Euclidean diameter at most ε(d + 6)^{1/2}, so the factor 4^{γ_H} holds whether that distance is the ℓ^∞ or the Euclidean one, since (d + 6)^{1/2} ≤ 4 for d ≤ 10, which covers d = 4.
{#C10.4.8-5} For such 𝒜 let 𝔰(x) := B₀ℓ^{−1}e^{−½δ₁d(x,y′)}, so that |𝒜| ≤ ℓ𝔰, |∇𝒜| ≤ 𝔰, and 𝔬 = h_H(ε/ℓ)^{γ_H}𝔰 with h_H := 4^{γ_H}B₀(γ_H)/B₀.

{#C10.4.9} *Transports.* A gauge-covariant identity at a coarse point y is evaluated in the axial gauge of U^B about y.
{#C10.4.9-1} There every fine bond b within ℓ¹-distance 4dε of y has |U^B(b) − 1| ≤ 4dε(ε/L)|F|: b closes a lattice loop bounding at most 4dL fine plaquettes, each within (ε/L)²|F| of 1, and the holonomy of a loop is an ordered product of conjugated plaquette holonomies.
{#C10.4.9-1-1} Two contours of 𝐆(y, x) differ by a loop of at most dL² plaquette moves (#C10.3.3-11-1), so the U^B(Γ), Γ ∈ 𝐆(y, x), have spread at most dL²(ε/L)²|F| = dε²|F|, and the sets {e^{iH_Γ}U^B(Γ)} with |H_Γ| ≤ dε²|F| have spread δ′ ≤ 3dε²|F| ≤ 3dC₀ε₁, using ε²|F| ≤ C₀ε₁ (9.2).
  {#C10.4.9-1-1-1} Under 198c_{GM}dC₀ε₁ ≤ 1, 24c_BdC₀ε₁ ≤ 1, and 12dC₀ε₁ ≤ r_{BCH}, #C10.3.3-11-2–#C10.3.3-11-3, which use only the spread, apply to their averages, among them the contour variable U^B(y, x) of #C10.1.4-1-1. It is e^{iĀ}U^B(Γ₀) for any Γ₀ ∈ 𝐆(y, x), with |Ā| ≤ (8/3)dε²|F| ≤ 3dε²|F| (#C10.3.3-11-2-1 at the spread dε²|F|), and its linear part in left variations X_Γ of the U^B(Γ) is Σ_ΓT_ΓX_Γ with Σ_Γ|T_Γ| ≤ 3/2.
{#C10.4.9-2} A transport in Q₁ is the contour variable U^B(c₋, x) followed by a straight path of the tube, that is, at most dL + L fine bonds and a factor within 3dε²|F| of 1. The transports in Q′₁ are the contour variables U^B(y, x). So all of them are within (4d² + 7d)ε²|F| of 1. The transports along the paths γ_{c,x}^{Γ,Γ′} of #C10.1.4-0-2, of at most (d + 1)L fine bonds, are within 4d(d + 1)ε²|F| of 1.
  {#C10.4.9-2-1} The loops γ_{c,x}^{Γ,Γ′} ∪ (−c) have at most (d + 2)L fine bonds, so |h_{c,x}^{Γ,Γ′} − 1| ≤ 4d(d + 2)ε²|F|, |Y_c| ≤ 2πd(d + 2)ε²|F| by (π/2) of #T11.26, and the coarse links e^{iY_c}U^B(c) of Ũ_j are within (2πd(d + 2) + 4d)ε²|F| of 1. Since |Ad(g) − 1| ≤ 2|g − 1| for g ∈ G, all these transports have adjoint action within δ_T := 32d²ε²|F| of 1 (d ≥ 2).
{#C10.4.9-3} In a fine divergence summed over a block (Q′₁D_B*), summation by parts leaves each interior fine bond b = ⟨x, x + (ε/L)e_μ⟩ with h_b := U^B(y, x)U^B(b)U^B(y, x + (ε/L)e_μ)^{−1}. Index both averages by the larger of the families 𝐆(y, x) and 𝐆(y, x + (ε/L)e_μ), each contour of the smaller one repeated once for every contour of the larger one that gives it by deleting one μ-step. By #C10.1.4-0-1 each is repeated equally often, which leaves the average (0.10) unchanged.
  {#C10.4.9-3-1} Paired contours Γ, Γ′ differ by the thin loop Γ·b·Γ′^{−1}, which bounds at most dL plaquettes, so h_Γ := U^B(Γ)U^B(b)U^B(Γ′)^{−1} = e^{iH_Γ} with |H_Γ| ≤ (1 + dε²|F|)dε(ε/L)|F|. Moving each U^B(Γ′) to e^{itH_Γ}U^B(Γ′), t ∈ [0, 1], #C10.4.9-1-1-1 gives |h_b − 1| ≤ (3/2)max_Γ|H_Γ|, so the adjoint action of h_b is within 4dε(ε/L)|F| of 1. The face bonds carry transports of the first kind.
{#C10.4.9-4} Besides the transports, Q₁ = Q̄₁(U^B) contains the non-main terms of CMP 98 (124).
{#C10.4.9-5} Their operators, g(−i ad_Y)g^{−1}(−i ad_{Y_x}) − 1 (in the second and third terms), g(−i ad_Y)g^{−1}(i ad_{Y_x})e^{−i ad_Y} − 1, and e^{i ad_Y} − g(−i ad_Y)Σ_xL^{−d}g^{−1}(i ad_{Y_x}), vanish at Y = Y_x = 0 and are O(L²α₀) (CMP 98 p.036, after (124)).
{#C10.4.9-6} Here α₀ is the fine plaquette bound (ε/L)²|F|, so L²α₀ = ε²|F|, and by (126) these terms change Q₁𝒜 by at most c₁₂₄ε²|F| sup|𝒜| over the paths, with c₁₂₄ of #C10.3.34-5-1. An identity exact at U^B = 1 is built from the following pieces:

- {#C10.4.10} at most two averages, each with sup norm at most 3d times that of the field;
- {#C10.4.11} coarse differences, 2d terms at spacing ε, each with transports within δ_T of 1, contributing in all at most 2dδ_T/ε = 64d³ε|F| per unit of the field differenced;
- {#C10.4.12} at most one block divergence, contributing at most (4d² + 32d³)ε|F| per unit. The holonomies h_b of the interior bonds give 4d². Only the entering faces deviate from the convention of (iii) (#C10.4.70), since at the exiting faces the field is carried by U^B(y, b₋) as in Q′₁. Their dL^{d−1} bonds, of weight L^{−d}(L/ε) each and with transports within δ_T of 1, give dδ_T/ε = 32d³ε|F|;
- {#C10.4.13} the non-main terms of (124), contributing at most 2dc₁₂₄ε|F| per unit once differenced.

{#C10.4.14} The worst case is a coarse divergence of an average, as in e_f below. The averaged field's transports give 3d·64d³ = 192d⁴, the average's own transports and its non-main terms, differenced, give 64d³ + 2dc₁₂₄, and the block divergence gives 4d² + 32d³. In all this is at most 192d⁴ + 64d³ + 32d³ + 4d² + 2dc₁₂₄ ≤ 300d⁴ + 2dc₁₂₄ per unit, and every other combination of at most these pieces is smaller.
{#C10.4.14-1} Each identity therefore holds up to a correction bounded by C_trε|F| times the sup over the cell of the field it acts on and of ε times its gradient, with C_tr := 1000d⁴ + 2dc₁₂₄.
{#C10.4.14-2} Let ν_F := εℓ sup|F| ≤ C₀ε₁(ε/ℓ)L^{−2}, by |F| ≤ C₀ε₁/a_j² ((9.2) at scale j) and a_j = Lℓ.
{#C10.4.14-3} The oscillations of *Regularity of H₁.* and #C10.4.66-1 are those of the Hölder quotients, with transports along shortest contours (#C10.4.8-3). In a cell of side at most 4ε within ℓ¹-distance 4dε of y such a contour stays in the cell, with at most 4dL fine bonds, each within 4dε(ε/L)|F| of 1 in the axial gauge about y (#C10.4.9-1), so its adjoint action is within δ_T of 1. So two values of a field g on the cell, carried to y by transports whose adjoint actions are within 2δ_T of 1, differ by at most the oscillation of g over the cell plus 5δ_T sup|g|, and so do two averages of such values.

{#C10.4.15} *The Parts of β.* By VAR (79), Δ₁ = Δ_π − Δ^{(2)}_π.
{#C10.4.15-1} By PBG (3.120), (3.128), and (3.134), for fields A′, A at a pair (𝐔, 𝐉),

{#C10.4.16} ⟨A′, Δ₁A⟩ = ⟨A′, ΔA⟩ − 2⟨HC^{(2)}[A′, A], 𝐉⟩ − π(A′, A).

{#C10.4.17} Here Δ is the plain second variation of the action (PBG (3.12), (3.109)), and C^{(2)} is the second-order term of the m-fold averaging in the units of Q_mA (PBG p.421, after (3.127)), polarised.
{#C10.4.17-1} The remainder π(A′, A) := ⟨A′, Δ′_π[𝐉]A⟩ + 2⟨H(C^{(2)}_π − C^{(2)})[A′, A], 𝐉⟩, with Δ′_π[𝐉] the form of (3.120) with 𝐉 written for J and C^{(2)}_π(A) := C^{(2)}(A − DG′RD*A), collects the terms containing G′RD*A′ or G′RD*A. π_X denotes it in run X. Correspondingly β = β_act + β_con + β_π + β_gf. Here β_act is the defect of the plain second variations, β_con that of the terms 2⟨HC^{(2)}, 𝐉⟩, β_π := π_B(𝒜′, 𝒜) − π_A(Q₁𝒜′, Q₁𝒜), and β_gf is defined below.
{#C10.4.17-2} By *The π-Part of β.*, β_π ≡ 0, so β = β_act + β_con + β_gf.

{#C10.4.18} *The Action Part of β.* By (B3) of §10.1, A_ε∘M̄ = A_ε∘M with M̄ := M̄_{U^B}, so the blocking artifact is b = A_ε∘M̄ − A_{ε/L}.
{#C10.4.18-1} Differentiating A_ε(M̄(e^{i(ε/L)(s𝒜′+t𝒜)}U^B)) in s and t at 0 gives the following identity.
{#C10.4.18-2} It uses dM̄(U^B) = Q₁ and d²M̄ = 2C₁^{(2)} with C₁^{(2)} := C̄₁^{(2)} of (B4). By VAR (44) at j = 1, |C₁^{(2)}(𝒜)| ≤ C₂ε|𝒜|². (CMP 98 (122)–(123), p.036, bound the whole nonlinear part, |C| ≤ C₁^{(123)}L²|A|², in that paper's units.) So polarisation in the sup norm gives |C₁^{(2)}[𝒜′, 𝒜]| ≤ 2C₂ε|𝒜′||𝒜|, with the sups taken over the paths of the averaging:

{#C10.4.19} β_act(𝒜′, 𝒜) := ⟨Q₁𝒜′, Δ^A(Ũ_j)Q₁𝒜⟩ − ⟨𝒜′, Δ^B(U^B)𝒜⟩ = d²b(U^B)[𝒜′, 𝒜] − 2⟨J^A(Ũ_j), C₁^{(2)}[𝒜′, 𝒜]⟩.

{#C10.4.20} *The Constraint Part of β.* In both runs the current is the lift of λ^B through the averagings (§10.3): J′_j = Q^A_{j−1}*𝒬′*λ^B and J^B(U^B) = Q^B_j*𝒬′*λ^B, with 𝒬′ the last step at the common block field and PBG's Q_m, by (B2) of §10.1 and D̄*𝒬′*λ^B = 0 (§10.3).
{#C10.4.20-1} Since Q_mH = 1, ⟨HC^{(2)}[A′, A], Q_m*𝒬′*λ^B⟩ = ⟨C^{(2)}[A′, A], 𝒬′*λ^B⟩ in each run.
{#C10.4.20-2} The second-order part of (B4) is C_B^{(2)}(𝒜) = C_A^{(2)}(Q₁𝒜) + Q^A_{j−1}C₁^{(2)}(𝒜).
{#C10.4.20-3} Hence

{#C10.4.21} β_con(𝒜′, 𝒜) := −2⟨C_A^{(2)}[Q₁𝒜′, Q₁𝒜], 𝒬′*λ^B⟩ + 2⟨C_B^{(2)}[𝒜′, 𝒜], 𝒬′*λ^B⟩ = 2⟨C₁^{(2)}[𝒜′, 𝒜], J′_j⟩,

{#C10.4.22} and β_act + β_con = d²b(U^B)[𝒜′, 𝒜] − 2⟨J^A(Ũ_j) − J′_j, C₁^{(2)}[𝒜′, 𝒜]⟩.
{#C10.4.22-1} Here J^A(Ũ_j) − J′_j = δJ is the artifact current of (10.3a), and only its size enters.
{#C10.4.22-2} J^A(Ũ_j) = D*F̂(Ũ_j), where F̂ = F + O(ε⁴|F|³) is the plaquette field of the first variation of the Wilson action. At each bond it is a sum of d − 1 covariant differences of F̂(Ũ_j), each at most 2C₀ε₁a_j^{−3} by VAR (2) for Ũ_j (§9.3). A factor 2 covers the transports and the higher terms of F̂.
{#C10.4.22-3} With a_j³|J′_j| ≤ 2B_λε₁ (§10.3, *The Intermediate Current.*),

{#C10.4.23} the artifact current satisfies |δJ| ≤ |J^A(Ũ_j)| + |J′_j| ≤ (4dC₀ + 2B_λ)ε₁a_j^{−3}.

{#C10.4.24} *The Remainder of the Coarse Curvature.* Let p be a coarse plaquette of T_ε with corner y_p.
{#C10.4.24-1} The computation is in the axial gauge of U^B about y_p (*Transports.*), with η := ε/L.
{#C10.4.24-2} The cell of p is the set of fine bonds within ℓ¹-distance 4dε of y_p.
{#C10.4.24-3} It contains every fine bond on which (MW)(∂p) depends, the fine plaquettes p′ with w_{p,p′} > 0 in (9.11), and the paths γ_{p′} from y_p to their corners along the contours Γ.
{#C10.4.24-4} For W on the cell let

{#C10.4.25} Φ_p(W) := (1/iε²)log (MW)(∂p), F^w_p(W) := Σ_{p′}w_{p,p′}Ad(W(γ_{p′}))F_{p′}(W), εr_p(W) := Φ_p(W) − F^w_p(W),

{#C10.4.26} with F_{p′}(W) := (1/iη²)log W(∂p′), the weights of (9.11), and the logarithms of the holonomies based at the corners.
{#C10.4.26-1} So r_p is the remainder of (9.3) with the (9.11) average in place of the tiling average.
{#C10.4.26-2} Derivatives are taken along W ↦ e^{iηZ}W: d(εr_p)(W)[Z] := ∂_tεr_p(e^{iηtZ}W) and d²(εr_p)(W)[Z′, Z] := ∂_s∂_tεr_p(e^{iη(sZ′+tZ)}W) at s = t = 0, and |Z| is the sup of |Z(b)| over the cell.

{#C10.4.27} *Analyticity.* Let 𝒫 be the set of complex configurations W(b) = e^{iζ(b)} on the cell with ζ(b) ∈ 𝔤_ℂ and |ζ(b)| ≤ 2r_G.
{#C10.4.27-1} Here r_G is a constant of d, L, and G, small enough for three properties: every holonomy entering Φ_p, F^w_p, and the F_{p′} on 𝒫 lies in the ball about 1 where log is analytic; |dlog_h| ≤ 2 there; and e^{iZ}e^{iζ} = e^{iζ′} with |ζ′| ≤ |ζ| + 2|Z| for |ζ|, |Z| ≤ r_G.
{#C10.4.27-2} The functions η²Φ_p = L^{−2}(1/i)log (MW)(∂p), η²F^w_p, and η²F_{p′} depend on the variables ζ(b) alone and are analytic on 𝒫.
{#C10.4.27-3} Let m_G be the sup over 𝒫 of η²(|Φ_p| + |F^w_p| + max_{p′}|F_{p′}|), a constant of d, L, and G. In the axial gauge, U^B = e^{iη𝔞} on the cell with |𝔞| ≤ 8dε|F|, since |U^B(b) − 1| ≤ 4dε(ε/L)|F| and |log u| ≤ (π/2)|u − 1| for unitary u. So η|𝔞| ≤ 8dε²|F| ≤ 8dC₀ε₁ ≤ r_G/2 under 16dC₀ε₁ ≤ r_G.

{#C10.4.28} *Cauchy Estimates.* For W = e^{iζ} with |ζ| ≤ r_G, the function (s, t) ↦ εr_p(e^{iη(sZ′+tZ)}W) is analytic for |s| ≤ r_G/(4η|Z′|) and |t| ≤ r_G/(4η|Z|) and bounded there by m_Gη^{−2}.
{#C10.4.28-1} Cauchy's estimate gives

{#C10.4.29} for all Z′ and Z, |d²(εr_p)(W)[Z′, Z]| ≤ k₂|Z′||Z|, k₂ := 16m_G/r_G²,

{#C10.4.30} and the same bound for d²Φ_p, d²F^w_p, and d²F_{p′}.
{#C10.4.30-1} Along W_τ := e^{iητ𝔞}, the functions are analytic also in τ, for |τ − τ₀| ≤ r_G/(2η|𝔞|) about every τ₀ ∈ [0, 1], where |ητ𝔞| ≤ r_G.
{#C10.4.30-2} Cauchy's estimate in (τ, t), with the t-radius r_G/(2η|Z|), admissible for a single direction since |ηtZ| ≤ r_G/2, and in (τ, s, t), with the radii r_G/(4η|Z′|) and r_G/(4η|Z|), gives

{#C10.4.31} for τ ∈ [0, 1], |∂_τ d(εr_p)(W_τ)[Z]| ≤ 4m_Gr_G^{−2}|𝔞||Z|, |∂_τ d²(εr_p)(W_τ)[Z′, Z]| ≤ 32m_Gr_G^{−3}η|𝔞||Z′||Z|.

{#C10.4.32} *Vanishing at the Identity.* Three facts hold at W = 1:

- {#C10.4.33} εr_p(1) = 0, both curvatures vanishing.
- {#C10.4.34} d(εr_p)(1)[Z] = 0 for every Z. At W = 1, dΦ_p(1)[Z] = (D̄Q₁^{pl}Z)(p), the coarse curl of the untransported path average, and dF^w_p(1)[Z] = Σ_{p′}w_{p,p′}(DZ)(p′), the variations of the transports dropping out because F(1) = 0.
  {#C10.4.34-1} (9.11) is the identity of the two.
- {#C10.4.35} d²(εr_p)(1)[Z′_c, Z_c] = 0 for fields Z′_c, Z_c constant on the cell, Z_c(b) = Z_μ on the bonds of direction μ.
  {#C10.4.35-1} Let Y := sZ′_c + tZ_c.
  {#C10.4.35-2} For W = e^{iηY} each fine plaquette logarithm is i[Y_μ, Y_ν] + O(η|Y|³) by the Baker–Campbell–Hausdorff formula, and the transports of F^w_p do not enter the second derivative at 0: the terms with two variations of a transport vanish since F(1) = 0, and the cross terms (dAd)(dF) vanish since dF_{p′}(1)[Z_c] = (DZ_c)(p′) = 0 for the constant fields.
  {#C10.4.35-3} The plain average of this configuration is invariant under the translations of T_ε, since the blocks and the contour families 𝐆 are translates of one another (#C10.1.4-0-1).
  {#C10.4.35-4} So its coarse links are e^{iεȲ_μ}, with Ȳ_μ = Y_μ + O(ε|Y|²) from the loop holonomies of (0.4), and the coarse plaquette logarithm is i[Ȳ_μ, Ȳ_ν] + O(ε|Y|³) = i[Y_μ, Y_ν] + O(ε|Y|³).
  {#C10.4.35-5} The weights sum to 1, so the second derivatives at s = t = 0 agree.

{#C10.4.36} *The Variations of r_p.* For a field 𝒜 with the bounds of *Regularity of H₁.*, let 𝒜_c be the constant field on the cell with the axial-gauge values of 𝒜 on the bonds from y_p.
{#C10.4.36-1} A path of at most 4dε/η fine bonds joins every bond of the cell to one of these, and each step changes the axial-gauge value by at most η|∇𝒜| + 2|U^B(b) − 1||𝒜|, so |𝒜 − 𝒜_c| ≤ 4dε|∇𝒜| + δ_T|𝒜|.
{#C10.4.36-2} At W = 1 bilinearity and the third fact give d²(εr_p)(1)[𝒜′, 𝒜] = d²(εr_p)(1)[𝒜′ − 𝒜′_c, 𝒜] + d²(εr_p)(1)[𝒜′_c, 𝒜 − 𝒜_c].
{#C10.4.36-3} Integrating the Cauchy estimates over τ ∈ [0, 1] from these values gives, at W = U^B:

- {#C10.4.37} |εr_p(U^B)| ≤ ½k₂|𝔞|² ≤ 32d²k₂ε²|F|², by Taylor's formula along W_τ with the first two facts;
- {#C10.4.38} |d(εr_p)[𝒜]| ≤ c_{r1}ε|F||𝒜|, c_{r1} := 32dm_G/r_G², by the second fact;
- {#C10.4.39} |d²(εr_p)[𝒜′, 𝒜]| ≤ k₂(|𝒜′ − 𝒜′_c||𝒜| + |𝒜′||𝒜 − 𝒜_c|) + c_{r3}ε²|F||𝒜′||𝒜|, c_{r3} := 256dm_G/(Lr_G³).

{#C10.4.41} *The Second Variation of b.* The Wilson density at spacing η is ½|X|² + κ_η(X) in the plaquette logarithm X, with |d^iκ_η(X)| ≤ c_κη⁴|X|^{4−i}, i = 0, 1, 2, for η²|X| ≤ 1, c_κ a constant of G. By the column-sum property Σ_pw_{p,p′} = L^{−d} of (9.11), which at d = 4 is L^{−4} = η⁴/ε⁴, as an identity in W,

{#C10.4.42} b(W) = Σ_pε⁴[½|Φ_p(W)|² − ½Σ_{p′}w_{p,p′}|F_{p′}(W)|²] + Σ_pε⁴κ_ε(Φ_p(W)) − Σ_{p′}η⁴κ_η(F_{p′}(W)).

{#C10.4.43} At U^B let f := dF_{p′}[𝒜], f′ := dF_{p′}[𝒜′], f″ := d²F_{p′}[𝒜′, 𝒜], and T := Ad(U^B(γ_{p′})). a and a′ denote the right-trivialised variations of W(γ_{p′}) in the directions 𝒜 and 𝒜′ (below), and ρ, ρ_t, ρ_s, ρ_{st} denote εr_p(U^B) and its variations in the directions 𝒜, 𝒜′, and (𝒜′, 𝒜).
{#C10.4.43-1} Then Φ_p = F^w_p + ρ, dF^w_p[𝒜] = Σ_{p′}w_{p,p′}(Tf + i[a, TF]), and |F_{p′}| = |TF_{p′}| for real W. So the second variation of the first sum is, at each p,

{#C10.4.44} ⟨dΦ_p[𝒜′], dΦ_p[𝒜]⟩ + ⟨Φ_p, d²Φ_p[𝒜′, 𝒜]⟩ − Σ_{p′}w_{p,p′}(⟨f′, f⟩ + ⟨F, f″⟩) = −Cov_p(Tf′, Tf) − Cov_p(TF, Tf″) + X_tr + X_r,

{#C10.4.45} with Cov_p(X, Y) := Σ_{p′}w_{p,p′}⟨X_{p′}, Y_{p′}⟩ − ⟨Σ_{p′}w_{p,p′}X_{p′}, Σ_{p′}w_{p,p′}Y_{p′}⟩ the covariance under the probability weights w_{p,·}, X_tr the terms containing a or a′, and X_r the terms containing ρ, ρ_t, ρ_s, or ρ_{st}. |Cov_p(X, Y)| ≤ osc_pX·osc_pY, the oscillations taken over the fine plaquettes p′ with w_{p,p′} > 0.
{#C10.4.45-1} By (9.11) these lie in the box at y_p of side 2ε in the plane of p and of side ε in the other d − 2 directions, of Euclidean diameter at most ε(d + 6)^{1/2}.

{#C10.4.46} *The Bounds.* Let 𝒜 = H₁^Be_{y′} and 𝒜′ = H₁^Be_y.
{#C10.4.46-1} On the cell of p, |𝒜| ≤ ℓ𝔰, |∇𝒜| ≤ 𝔰, and |D𝒜| ≤ 2𝔰, and likewise for 𝒜′ with 𝔰′.
{#C10.4.46-2} The weights are taken at their sup over the cell, which exceeds their value at y_p by at most e^{1/3} when δ₁ ≤ 1/(6d).
{#C10.4.46-3} By (9.2) at scale j, |F| ≤ C₀ε₁a_j^{−2} and |∇F| ≤ C₀ε₁a_j^{−3}, and ε²|F| ≤ ν_F ≤ C₀ε₁ ≤ 1; ε²|Φ_p| ≤ 1 by VAR (2) for MU^B (§9.3).
{#C10.4.46-4} The ingredients are as follows.

- {#C10.4.47} f = dlog_h[(D𝒜)(p′)] at the plaquette holonomy h, so |f| ≤ 4𝔰 and |f − D𝒜| ≤ 2k_lν_F𝔰, with k_l the constant of |dlog_h − 1| ≤ k_l|log h|, a constant of G, and |log h| = η²|F| ≤ ν_F; here k_lν_F ≤ k_lL^{−2} ≤ 1 by #C10.4.14-2 for L² ≥ k_l.
- {#C10.4.48} The path γ_{p′} has at most 4dL fine bonds.
  {#C10.4.48-1} With a taken as the right-trivialised variation, i a = (dW(γ_{p′})[𝒜])W(γ_{p′})^{−1}, so that dT[𝒜] = i ad_aT with no dlog factor, a is a sum of at most 4dL transported values η𝒜(b), so |a| ≤ 4dε|𝒜| ≤ 4dεℓ𝔰, and |i[a, TF]| ≤ c_{br}|a||F| ≤ 4dc_{br}ν_F𝔰 with c_{br} of #C10.3.36-1, a constant of G. The second variation of T is i ad_{a″}T + (i ad_a)(i ad_{a′})T, with a″ the variation of a in the direction 𝒜′, a sum of commutators of the transported values over pairs of bonds of γ_{p′}, so |a″| ≤ ½c_{br}(4dε)²|𝒜′||𝒜|,
  {#C10.4.48-2} and its norm is at most c_{br}|a″| + c_{br}²|a′||a| ≤ 24d²c_{br}²ε²|𝒜′||𝒜|.
- {#C10.4.49} osc_p(Tf) ≤ 2𝔬 + k_oν_F𝔰, k_o := 256d² + 4k_l.
  {#C10.4.49-1} The oscillation of the curl D𝒜 over these plaquettes is at most 2𝔬 (*Regularity of H₁.*).
  {#C10.4.49-2} In the axial gauge the transports along the paths γ_{p′} and along the contours of the Hölder quotient are within δ_T ≤ 32d²ν_F of 1, which adds at most 4δ_T|D𝒜| ≤ 256d²ν_F𝔰, and f − D𝒜 adds 4k_lν_F𝔰.
- {#C10.4.50} osc_p(TF) ≤ 4dε|∇F| + 4δ_T|F| ≤ 4d(1 + 32d)C₀ε₁εa_j^{−3}, the axial-gauge values changing along a path as those of 𝒜 in #C10.4.36-1, and 4δ_T|F| = 128d²ε²|F|² ≤ 128d²C₀ε₁εa_j^{−3} by ε ≤ a_j and C₀ε₁ ≤ 1.
- {#C10.4.51} |f″| ≤ k₂ℓ²𝔰′𝔰, so osc_p(Tf″) ≤ 2k₂ℓ²𝔰′𝔰, and |d²F^w_p| ≤ (k₂ + 32dc_{br} + 24d²c_{br}²)ℓ²𝔰′𝔰, the terms i[a′, Tf] + i[a, Tf′] and the second variation of T adding 32dc_{br}εℓ and 24d²c_{br}²ε²ℓ²|F|.
- {#C10.4.52} By *The Variations of r_p.*, |ρ| ≤ 32d²k₂ε²|F|² ≤ 32d²k₂|F|, so |Φ_p| ≤ k_F|F| with k_F := 1 + 32d²k₂; |ρ_t| ≤ c_{r1}ν_F𝔰 and |ρ_s| ≤ c_{r1}ν_F𝔰′; and |ρ_{st}| ≤ [2k₂(4dεℓ + δ_Tℓ²) + c_{r3}ε²ℓ²|F|]𝔰′𝔰, so |F||ρ_{st}| ≤ (8dk₂ + 64d²k₂ + c_{r3})ν_F𝔰′𝔰, by εℓ|F| = ν_F and ν_F ≤ 1.

{#C10.4.53} With these, at each p and in units of 𝔰′𝔰:

- {#C10.4.54} |Cov_p(Tf′, Tf)| ≤ (2h_H(ε/ℓ)^{γ_H} + k_oν_F)² ≤ 4(h_H + k_o)²(ε/ℓ)^{γ_H}, by 𝔬 = h_H(ε/ℓ)^{γ_H}𝔰 and ν_F ≤ (ε/ℓ)^{γ_H};
- {#C10.4.55} |Cov_p(TF, Tf″)| ≤ 8d(1 + 32d)k₂C₀ε₁(ε/ℓ)L^{−3}, since εℓ²a_j^{−3} = (ε/ℓ)L^{−3};
- {#C10.4.56} |X_tr| ≤ (64dc_{br} + 40d²c_{br}²)ν_F: the cross terms of ⟨dF^w_p[𝒜′], dF^w_p[𝒜]⟩ give at most 32dc_{br}ν_F + 16d²c_{br}²ν_F², and ⟨F^w_p, ·⟩ of the transport terms of d²F^w_p at most 32dc_{br}ν_F + 24d²c_{br}²ν_F²;
- {#C10.4.57} |X_r| ≤ [2(4 + 4dc_{br})c_{r1} + c_{r1}² + 32d²k₂(k₂ + 32dc_{br} + 24d²c_{br}²) + k_F(8dk₂ + 64d²k₂ + c_{r3})]ν_F, from ⟨dF^w_p[𝒜′], ρ_t⟩ + ⟨ρ_s, dF^w_p[𝒜]⟩ with |dF^w_p| ≤ (4 + 4dc_{br})𝔰, from ⟨ρ_s, ρ_t⟩, from ⟨ρ, d²F^w_p⟩, and from ⟨Φ_p, ρ_{st}⟩;
- {#C10.4.58} the quartic terms are at most 2c_κ(k_F²k_Φ² + k_F³k_Φ″)ν_F, with k_Φ := 4 + 4dc_{br} + c_{r1} and k_Φ″ := k₂ + 32dc_{br} + 24d²c_{br}² + 8dk₂ + 64d²k₂ + c_{r3} bounding |dΦ_p| ≤ k_Φ𝔰 and |d²Φ_p| ≤ k_Φ″ℓ²𝔰′𝔰, since ε⁴|F|² ≤ ν_F² and ε⁴|F|³ℓ² ≤ ν_F², the fine side being bounded in the same way through Σ_{p′}w_{p,p′} = 1.

{#C10.4.59} The current term is at most 2Σ_bε^d|δJ|·2C₂ε|𝒜′||𝒜| ≤ 4C₂(4dC₀ + 2B_λ)ε₁(ε/ℓ)L^{−3} in the same units, summed over the coarse bonds.
{#C10.4.59-1} Over the coarse plaquettes the weights sum to Σ_pε^d𝔰′𝔰 ≤ 2C_δB₀²ℓ^{−2}ℓ^de^{−¼δ₁d(y,y′)} by the triangle inequality, and over the coarse bonds to the same bound, with C_δ depending on δ₁ and d and taken to bound both sums; the factor 2 ≥ e^{2/3} covers the sup over the cell.
{#C10.4.59-2} With ν_F ≤ (ε/ℓ)^{γ_H}, every term of β_act + β_con at (𝒜′^B, 𝒜^B) is therefore bounded by

{#C10.4.60} (10.6a) |(β_act + β_con)(H₁^Be_y, H₁^Be_{y′})| ≤ C_β(γ_H)[(ε/ℓ)^{γ_H} + ε₁(ε/ℓ)L^{−3}]·B₀ℓ^{−2}ℓ^de^{−¼δ₁d(y,y′)},

{#C10.4.61} C_β(γ_H) := 2C_δB₀[4(h_H + k_o)² + k_ν + 8d(1 + 32d)k₂C₀ + 4C₂(4dC₀ + 2B_λ)], k_ν := 64dc_{br} + 40d²c_{br}² + 2(4 + 4dc_{br})c_{r1} + c_{r1}² + 32d²k₂(k₂ + 32dc_{br} + 24d²c_{br}²) + k_F(8dk₂ + 64d²k₂ + c_{r3}) + 2c_κ(k_F²k_Φ² + k_F³k_Φ″),

{#C10.4.62} with h_H of #C10.4.8-5, so that C_β is increasing in B₀(γ_H).
{#C10.4.62-1} The bound is for the bilinear form at the unit fields e_y and e_{y′}: since ⟨e_y, Ke_{y′}⟩ = ℓ^{2d}K(y, y′) for a kernel K on T_ℓ, it is a kernel bound C_β(γ_H)[(ε/ℓ)^{γ_H} + ε₁(ε/ℓ)L^{−3}]·B₀ℓ^{−2}ℓ^{−d}e^{−¼δ₁d(y,y′)}, of the form of the principal part's kernel bound (3.132), and (ε/ℓ)^{γ_H} = L^{−γ_H(j−1)}.
{#C10.4.63} *The Gauge-Fixing Part of β.* Since R is an orthogonal projection,

{#C10.4.64} β_gf(𝒜′, 𝒜) := ⟨Q₁𝒜′, D_AR_AD_A*Q₁𝒜⟩ − ⟨𝒜′, D_BR_BD_B*𝒜⟩ = ⟨r′_A, r_A⟩ − ⟨r′_B, r_B⟩,

{#C10.4.65} with r_A := R_Af_A, f_A := D_A*Q₁𝒜 on T_ε, r_B := R_Bf_B, f_B := D_B*𝒜 on T_{ε/L}, and r′_A, r′_B the same for 𝒜′.
{#C10.4.65-1} By PBG (3.20)–(3.25) (p.394), R_X = 1 − G′_XQ′_X*K_X^{−1}Q′_XG′_X for X = A, B. Here Q′_X is the linearised averaging of gauge parameters to the scale ℓ, G′_X := (Δ_X + a_Xℓ^{−2}Q′_X*Q′_X)^{−1} with Δ_X the covariant Laplacian on gauge parameters, and K_X := Q′_XG′_X²Q′_X*.
{#C10.4.65-2} The coefficient a_X is â_m for the run's m, where â_m denotes PBG's number a_m at a = 1 (LF #4.101-1). PBG p.394 l.29 prints â₁ = â₀ = 1 together with the recursion â_{m+1} = â_m/(L^{−2} + â_m), which is therefore the recursion for m ≥ 1. The map a ↦ a/(L^{−2} + a) fixes a_* := 1 − L^{−2}, and for a ≥ a_* its value minus a_* is (a − a_*)L^{−2}/(L^{−2} + a) ∈ [0, L^{−2}(a − a_*)]. Starting from â₁ − a_* = L^{−2}, this gives 0 ≤ â_m − a_* ≤ L^{−2m} for m ≥ 1. Run A has index j − 1 and run B index j, so |a_A − a_B| ≤ L^{−2(j−1)} ≤ 2L^{−j} for j ≥ 2, and a_A = a_B = 1 at j = 1.
{#C10.4.65-3} Hence r_X = f_X − φ_X(μ_X), with φ_X(μ) := G′_XQ′_X*μ and μ_X := K_X^{−1}Q′_XG′_Xf_X, and Q′_XG′_Xr_X = 0.

{#C10.4.66} *Inputs.* Both runs' configurations satisfy (3.35) at the scale ℓ (#C10.4.1-1), so PBG Theorems 3.1 and 3.2, at a = 1 and with the single layer of the run in (3.24), hold on both lattices with constants of d and L, uniformly in PBG's spacing η, which is ε for run A and ε/L for run B at the same ℓ = L^mη.
{#C10.4.66-1} For λ supported in Δ(y′), (3.42) gives |G′λ|, |∇G′λ|, |G′∇*λ| ≤ B₀(ℓ², ℓ, ℓ)e^{−δ₀d(y,y′)}|λ| on Δ(y), and (3.43) bounds the Hölder constant of exponent γ of ζ∇G′λ by B₀(γ)ℓ^{1−γ}e^{−δ₀d(y,y′)}|λ| for the cutoffs ζ of #C10.4.8-2, and the two cases of #C10.4.8-2–#C10.4.8-2-1 then bound the oscillation of ∇G′λ over a cell of side at most 6ε.
{#C10.4.66-2} (3.48) gives |K^{−1}(y, y′)| ≤ B₀ℓ^{−4}ℓ^{−d}e^{−δ₀d(y,y′)}.
{#C10.4.66-3} B₀ and B₀(γ) are taken large enough to cover these constants, and δ₁ ≤ δ₀ (decreasing δ₁ if necessary).
{#C10.4.66-4} Applied to a source bounded by a multiple of e^{−½δ₁d(·,y′)}, these operators then return the same decay times c_δ′ (#C10.4.7-5), since −δ₀ + ½δ₁ ≤ −½δ₀.
{#C10.4.66-5} Let B_G := c_δ′B₀ and B_G(γ_H) := c_δ′4^{γ_H}B₀(γ_H).

{#C10.4.67} *Identities.* Let Q′₁λ(y) := L^{−d}Σ_{x∈B(y)}Ad(U^B(y, x))λ(x) be the one-step average of gauge parameters (CMP 98 (78)–(79), with the contour variables U^B(y, x) ∈ G of #C10.1.4-1-1).

- {#C10.4.68} (i) Q′_B = Q′_AQ′₁ (CMP 98 (80)) and Q′₁Q′₁* = 1, both exact.
- {#C10.4.69} (ii) Q₁𝒜 = Q^{str}𝒜, where Q^{str}𝒜 is the average over the L^d straight fine paths of the tube of a coarse bond of the sum of 𝒜 along the path, divided by L: this is the main term (125) of CMP 98 (124) ((B4) of §10.1).
  {#C10.4.69-1} The plain dM(U^B) differs from Q^{str} by the coarse difference of θ_𝒜(y) := −(ε/L)L^{−d}Σ_{x∈B(y)}𝒜(Γ̄_{y,x}), into which the Γ̄-pieces of the chains γ̄_{c,x} of #C9.8.1 telescope, as (B1) requires.
- {#C10.4.70} (iii) D_AQ′₁φ = Q^{str}D_Bφ, a coarse difference of block averages being the tube average of fine differences, and Q′₁D_B*g = D_A*Q̂_fg, summing a fine divergence over a block leaving the fluxes through its faces; Q̂_f is the average over the L^{d−1} fine bonds crossing a face.
  {#C10.4.70-1} For a coarse bond c, Q̂_fg(c) is based at c₋: the value on a crossing bond b is carried to c₋ by the contour variable U^B(c₋, b₋), b₋ ∈ B(c₋) being the endpoint of b in B(c₋).
  {#C10.4.70-2} At the entering face of B(y), crossed by c′ = ⟨y − εe_μ, y⟩, D_A* then carries Q̂_fg(c′) from c′₋ to y by the coarse link Ũ_j(c′); the convention based at y differs from this one by a loop holonomy within δ_T of 1, which the count of *Transports.* covers.

{#C10.4.71} (ii) and (iii) are exact at U^B = 1.
{#C10.4.71-1} In general they hold up to the corrections of *Transports.*, which include the non-main terms of CMP 98 (124) in Q₁.
{#C10.4.71-2} The transports in them are: in Q′₁ the contour variables U^B(y, x); in Q^{str} U^B(y, x) followed by the straight path to the bond; and in Q̂_f U^B(c₋, b₋), to the endpoint of the crossing bond in B(c₋).
{#C10.4.71-3} Their bonds lie within ℓ¹-distance 4dε of y, so each transport is within δ_T of 1 (#C10.4.9-2-1), and the corrections are those of *Transports.*

{#C10.4.72} *Sizes.* For 𝒜 = H₁^Be_{y′} put τ̂ := (ε/ℓ)^{γ_H} + ν_F.
{#C10.4.72-1} Then |f_B| ≤ d𝔰, |Q′_BG′_Bf_B| ≤ dB_Gℓ²𝔰, |μ_B| ≤ dB_G²ℓ^{−2}𝔰, |φ_B(μ_B)| ≤ dB_G³𝔰, and |∇φ_B(μ_B)| ≤ dB_G³ℓ^{−1}𝔰, so

{#C10.4.73} (G1) |r_B| ≤ c_{g2}𝔰, c_{g2} := d(1 + B_G³), and osc_{B(y)}r_B ≤ c_{g1}τ̂𝔰, c_{g1} := d(h_H + dB_G³) + C_trc_{g2}.

{#C10.4.74} The oscillation is that of the values transported to y over the block B(y) of side ε.
{#C10.4.74-1} For f_B it comes from *Regularity of H₁.*, with at most 5δ_T|f_B| from the transports (#C10.4.14-3), and for φ_B from dε|∇φ_B| with ε/ℓ ≤ (ε/ℓ)^{γ_H}, along a path of at most dL fine bonds whose thin loops (#C10.4.9-3-1) add at most 4d²ε²|F||φ_B| ≤ δ_T|φ_B|; in all the transports add at most 5δ_T(|f_B| + |φ_B(μ_B)|) ≤ C_trc_{g2}ν_F𝔰.

{#C10.4.75} *The Commutator.* For a fine source ρ bounded by a multiple |ρ| of e^{−½δ₁d(·,y′)}, let 𝔠(ρ) := G′_AQ′₁ρ − Q′₁G′_Bρ and ψ := G′_Bρ.
{#C10.4.75-1} Applying Q′₁ to (Δ_B + a_Bℓ^{−2}Q′_B*Q′_B)ψ = ρ and using (i) and (iii),

{#C10.4.76} (Δ_A + a_Aℓ^{−2}Q′_A*Q′_A)Q′₁ψ = Q′₁ρ + D_A*[(Q^{str} − Q̂_f)D_Bψ + X] − Y + (a_A − a_B)ℓ^{−2}Q′_A*Q′_Bψ,

{#C10.4.77} with |X| ≤ (300d⁴ + 2dc₁₂₄)ε|F|(sup|ψ| + ε sup|∇ψ|) and |Y| ≤ C_trε|F|sup|∇ψ| (#C10.4.14), so

{#C10.4.78} 𝔠(ρ) = −G′_A{D_A*[(Q^{str} − Q̂_f)D_Bψ + X] − Y + (a_A − a_B)ℓ^{−2}Q′_A*Q′_Bψ}.

{#C10.4.79} (Q^{str} − Q̂_f)D_Bψ is a difference of two averages of ∇ψ over the tube of a coarse bond, a cell of side 2ε, with transports within δ_T of 1 (#C10.4.71-3), so by #C10.4.66-1 and #C10.4.14-3 it is at most B_G(γ_H)(ε/ℓ)^{γ_H}ℓ|ρ| + 5δ_T sup|∇ψ|. Since 5δ_T = 160d²ε²|F| and 300d⁴ + 2dc₁₂₄ + 160d² ≤ C_tr, X and the second part are together at most C_trε|F|(sup|ψ| + ε sup|∇ψ|). And |a_A − a_B| ≤ 2L^{−j} ≤ 2(ε/ℓ)^{γ_H}.
{#C10.4.79-1} With (3.42) for G′_A and G′_AD_A*,

{#C10.4.80} (G2) |𝔠(ρ)| ≤ c_𝔠B_Gτ̂ℓ²|ρ|, c_𝔠 := dB_G(γ_H) + 2B_G + (2d + 1)C_trB_G,

{#C10.4.81} since the first part of #C10.4.79 gives dB_GB_G(γ_H)(ε/ℓ)^{γ_H}ℓ²|ρ| through G′_AD_A*, the X-term, X with the second part, carries the factor d of the d components of G′_AD_A* and is at most dB_Gℓ·C_trε|F|(B_Gℓ² + εB_Gℓ)|ρ| ≤ 2dC_trB_G²ν_Fℓ²|ρ|, the Y-term gives C_trB_G²ν_Fℓ²|ρ|, and the a-term gives 2B_G²L^{−j}ℓ²|ρ| ≤ 2B_G²(ε/ℓ)^{γ_H}ℓ²|ρ|.

{#C10.4.82} *The Defects.* Let e_f := f_A − Q′₁f_B, e_φ(μ) := φ_A(μ) − Q′₁φ_B(μ), and e_*(r) := Q′_AG′_AQ′₁r − Q′_BG′_Br.
{#C10.4.82-1} By (i), φ_A(μ) = G′_AQ′₁Q′_B*μ, so e_φ(μ) = 𝔠(Q′_B*μ) and e_*(r) = Q′_A𝔠(r).
{#C10.4.82-2} By (ii) and (iii), e_f = D_A*(Q^{str} − Q̂_f)𝒜 + X_f with |X_f| ≤ 2(300d⁴ + 2dc₁₂₄)ν_F𝔰, by the count of #C10.4.14 and sup|𝒜| + ε sup|∇𝒜| ≤ 2ℓ𝔰.
{#C10.4.82-3} By #C10.4.95-1–#C10.4.95-1-2 at ℱ = 𝒜, (Q^{str} − Q̂_f)𝒜(c) = (ε/L)Σ_iW^{tent}_i𝔡_i(c) + 𝔣(𝒜)(c), with (1/L)Σ_i|W^{tent}_i| = (L² − 1)/(3L²) < 1. The 𝔡_i at the two coarse bonds of a coarse difference are translates of each other, so the difference, divided by ε, is a combination of total weight less than 1 of differences of transported values of ∇𝒜 within a 4-cell, plus that of 𝔣(𝒜), at most 4δ_T sup|𝒜|/ε. By #C10.4.14-3 the divergence is therefore at most d𝔬 + 5dδ_T𝔰 + 4dδ_Tℓ𝔰/ε ≤ d𝔬 + 288d³ν_F𝔰.
{#C10.4.82-4} Hence, with 2(300d⁴ + 2dc₁₂₄) + 288d³ ≤ 2C_tr,

{#C10.4.83} (G3) |e_f| ≤ c_fτ̂𝔰, c_f := dh_H + 2C_tr; |e_φ(μ_B)| ≤ c_{g3}τ̂𝔰, c_{g3} := dB_G³c_𝔠; |e_*(r_B)| ≤ c_{g4}τ̂ℓ²𝔰, c_{g4} := B_Gc_𝔠c_{g2}.

{#C10.4.84} Since Q′_XG′_Xr_X = 0 in both runs and f_A = Q′₁r_B + φ_A(μ_B) − e_φ(μ_B) + e_f, applying Q′_AG′_A (with Q′_AG′_Aφ_A(μ) = K_Aμ) gives

{#C10.4.85} K_A(μ_A − μ_B) = e_*(r_B) + Q′_AG′_A(e_f − e_φ(μ_B)), δr := r_A − Q′₁r_B = e_f − e_φ(μ_B) − φ_A(μ_A − μ_B),

{#C10.4.86} so |μ_A − μ_B| ≤ B_Gc_{g5}τ̂ℓ^{−2}𝔰 with c_{g5} := c_{g4} + B_G(c_f + c_{g3}), and |δr| ≤ c_{g6}τ̂𝔰 with c_{g6} := c_f + c_{g3} + B_G²c_{g5}.

{#C10.4.87} *The Bound.* With δr of *The Defects.* (#C10.4.85), r_A = Q′₁r_B + δr.
{#C10.4.87-1} Then ⟨Q′₁r′_B, Q′₁r_B⟩_ε − ⟨r′_B, r_B⟩_{ε/L} = −Σ_yε^dCov_{B(y)}(r′_B, r_B), the covariance of the values transported to y under the uniform distribution on B(y), Ad being isometric.
{#C10.4.87-2} So

{#C10.4.88} β_gf(𝒜′, 𝒜) = −Σ_yε^dCov_{B(y)}(r′_B, r_B) + ⟨δr′, Q′₁r_B⟩ + ⟨Q′₁r′_B, δr⟩ + ⟨δr′, δr⟩.

{#C10.4.89} For 𝒜′ = H₁^Be_y and 𝒜 = H₁^Be_{y′}, |Cov| ≤ osc·osc, τ̂ ≤ 2 when C₀ε₁ ≤ 1, and Σ_xε^d𝔰′(x)𝔰(x) ≤ C_δB₀²ℓ^{−2}ℓ^de^{−¼δ₁d(y,y′)}, 𝔰′ being the weight of 𝒜′, the weights taken at their sup over B(x), and C_δ taken to bound this sum as well (#C10.4.59-1).
{#C10.4.89-1} Therefore

{#C10.4.90} (10.6b) |β_gf(H₁^Be_y, H₁^Be_{y′})| ≤ C_gf(γ_H)[(ε/ℓ)^{γ_H} + C₀ε₁(ε/ℓ)L^{−2}]·B₀ℓ^{−2}ℓ^de^{−¼δ₁d(y,y′)}, C_gf(γ_H) := 2C_δB₀(c_{g1}² + c_{g2}c_{g6} + c_{g6}²).

{#C10.4.91} For the two fields, (10.6a) and (10.6b) use only the sup, gradient, and 4-cell oscillation bounds of *Regularity of H₁.*

{#C10.4.92} *Functional Form.* For a general fine field ℱ, R_X being self-adjoint with R_Xr_X = r_X, β_gf(ℱ, 𝒜) = ⟨D_A*Q₁ℱ, r_A⟩_ε − ⟨D_B*ℱ, r_B⟩_{ε/L}, and D_A*Q₁ℱ = Q′₁D_B*ℱ + e_f(ℱ) with e_f(ℱ) = D_A*(Q^{str} − Q̂_f)ℱ + X_f(ℱ).
{#C10.4.92-1} Summing by parts once,

{#C10.4.93} (10.6c) β_gf(ℱ, 𝒜) = ⟨D_B*ℱ, s₂⟩ + ⟨∇ℱ, s₁⟩ + ⟨ℱ, s₀⟩ (inner products of T_{ε/L}),

- {#C10.4.94} s₂ := Q′₁*r_A − r_B = Q′₁*δr − (1 − Q′₁*Q′₁)r_B, so |s₂| ≤ (c_{g1} + c_{g6})τ̂𝔰;
- {#C10.4.95} s₁ collects ⟨(Q^{str} − Q̂_f)ℱ − 𝔣(ℱ), D_Ar_A⟩, with 𝔣(ℱ) of #C10.4.95-1-1.
  {#C10.4.95-1} Number the slices of fine bonds of the tube of c transverse to c by i = 0, …, 2L − 2 from c₋, the face slice being i = L − 1, so that Q^{str} weighs slice i by L^{−2}min(i + 1, 2L − 1 − i), a tent. On each straight path of Q^{str}, the path's average minus its value at the face bond is the sum of its consecutive differences, the difference between its bonds m and m + 1 having the weight −(m + 1)/L before the face bond and (L − 1 − m)/L from it on, and each difference is ε/L times a covariant longitudinal difference quotient of ℱ carried by the path's transport.
  {#C10.4.95-1-1} Averaging over the paths, (Q^{str} − Q̂_f)ℱ(c) = (ε/L)Σ_iW^{tent}_i𝔡_i(c) + 𝔣(ℱ)(c). Here 𝔡_i(c) is an average of these transported difference quotients between the slices i and i + 1, since the weights of the paths there have one sign, and 𝔣(ℱ)(c), the average of the face values with the transports of Q^{str} minus Q̂_fℱ(c), is at most 2δ_T times the sup of |ℱ| on the face (#C10.4.71-3).
  {#C10.4.95-1-2} The weights are W^{tent}_i := −L^{−2}Σ_{i′≤i}(i′ + 1) for i ≤ L − 2 and W^{tent}_i := L^{−2}Σ_{i′>i}(2L − 1 − i′) for i ≥ L − 1, so |W^{tent}_i| ≤ L^{−2}Σ_{i′≤L−2}(i′ + 1) < ½.
  {#C10.4.95-2} Written in the inner product of T_{ε/L}, such a difference quotient gets a weight of norm at most ε|W^{tent}_i||D_Ar_A(c)|, and a fine bond lies in the tubes of at most two coarse bonds, so this part of s₁ is at most sup_{cell}ε|D_Ar_A| ≤ C_ld sup_{cell}ε|D_Ar_A|, C_ld := 2 + 4dL^{d−1}.
  {#C10.4.95-3} The ε∇ℱ-part of X_f(ℱ) adds a part of s₁, bounded below with s₀;
- {#C10.4.96} s₀ comes from X_f(ℱ) and from 𝔣(ℱ), through ⟨𝔣(ℱ), D_Ar_A⟩ = ⟨D_A*𝔣(ℱ), r_A⟩.
  {#C10.4.96-1} The Transports count is term by term, so it bounds the absolute row sums of X_f(ℱ) by (300d⁴ + 2dc₁₂₄)ε|F|, and D_A*𝔣(ℱ), d coarse differences of 𝔣(ℱ) divided by ε, adds at most 4dδ_T/ε = 128d³ε|F|: X_f(ℱ)(y) + (D_A*𝔣(ℱ))(y) = Σ_b[k₀(y, b)ℱ(b) + k₁(y, b)ε∇ℱ(b)], with Σ_b|k₀(y, b)| + Σ_b|k₁(y, b)| ≤ C_trε|F|.
  {#C10.4.96-2} The kernels vanish unless the fine bond b is within ℓ^∞-distance 2ε of y, so each b meets at most 5^d coarse points, and the change from ε^d to (ε/L)^d costs L^d.
  {#C10.4.96-3} So the column sums are at most C_{5L}C_trε|F|, with C_{5L} := (5L)^d, and |s₀| ≤ C_{5L}C_trε|F||r_A|, while the part of s₁ from k₁ is at most C_{5L}C_trε²|F||r_A|.

{#C10.4.97} Here |r_A| ≤ (c_{g2} + 2c_{g6})𝔰, since r_A = Q′₁r_B + δr and τ̂ ≤ 2, and ε|D_Ar_A| ≤ c_{g7}τ̂𝔰 with c_{g7} := dh_H + 4C_tr + 32d²(c_{g2} + 2c_{g6}) + B_G²(dB_G + 2c_{g5}).
{#C10.4.97-1} The coarse differences of f_A are d differences of averages of ∇𝒜 within a 4-cell, each exceeding the oscillation by at most 5δ_T𝔰 (#C10.4.14-3), with the transport corrections of two identities, at most 4(300d⁴ + 2dc₁₂₄)ν_F𝔰 (#C10.4.14); with 5dδ_T𝔰 ≤ 160d³ν_F𝔰, the corrections are at most 4C_trν_F𝔰.
{#C10.4.97-2} The coarse difference of r_A along a link carries the link's transport, within δ_T = 32d²ε²|F| of 1, which adds at most δ_T|r_A| ≤ 32d²(c_{g2} + 2c_{g6})ν_F𝔰, since ε²|F| ≤ ν_F.
{#C10.4.97-3} And ε|D_Aφ_A(μ_A)| ≤ (ε/ℓ)B_Gℓ²(|μ_B| + |μ_A − μ_B|).
{#C10.4.97-4} So |s₁| ≤ [C_ldc_{g7} + C_{5L}C_tr(c_{g2} + 2c_{g6})]τ̂𝔰 and |s₀| ≤ C_{5L}C_tr(c_{g2} + 2c_{g6})ν_Fℓ^{−1}𝔰, all with the decay of 𝔰 about y′.

{#C10.4.98} *The π-Part of β.* At a pair (𝐔, 𝐉) of run X ∈ {A, B} the remainder π_X of *The Parts of β.* is the polarisation of its quadratic form, and that form vanishes when 𝐉 = Q_X*ν_λ, with ν_λ of #C10.3.7.
{#C10.4.98-1} For a field A of run X let σ_A := G′_XR_XD_X*A and P_XA := A − D_Xσ_A.
{#C10.4.98-2} Then Q′_Xσ_A = 0, since Q′_XG′_XR_X = 0 by PBG (3.25), and π_X(A, A) = ⟨A, Δ′_π[𝐉]A⟩ + 2⟨H(C_X^{(2)}(P_XA) − C_X^{(2)}(A)), 𝐉⟩, since C^{(2)}_π(A) = C^{(2)}(P_XA) by definition.

- {#C10.4.99} The bracket of (3.120).
  {#C10.4.99-1} PBG (3.116) gives (D_Xλ)(b) = η^{−1}(R_bλ(b₊) − λ(b₋)), so i[λ(b₋), (D_Xλ)(b)] = c_X(λ, D_Xλ)(b) pointwise, with c_X the bracket c of (B5) of §10.1 in run X. The bracket of (3.117) is therefore 2c_X(λ, Y) − c_X(λ, D_Xλ), and at λ = σ_A and Y = A it is c_X(σ_A, A) + c_X(σ_A, P_XA) as a bond field.
  {#C10.4.99-2} (3.120) is (3.117) at λ = σ_A, so ⟨A, Δ′_π[𝐉]A⟩ = ⟨𝐉, c_X(σ_A, A) + c_X(σ_A, P_XA)⟩ for every 𝐉.
- {#C10.4.100} The C^{(2)}-terms.
  {#C10.4.100-1} By bilinearity, C_X^{(2)}(P_XA) − C_X^{(2)}(A) = −C_X^{(2)}[D_Xσ_A, A] − C_X^{(2)}[D_Xσ_A, P_XA].
  {#C10.4.100-2} (B5) with Q′_Xσ_A = 0 gives 2C_X^{(2)}[D_Xσ_A, Y] = Q_Xc_X(σ_A, Y) + D̄q_X(σ_A, Y), and D̄*ν_λ = 0 (§10.3, *The Multipliers.*), so 2⟨C_X^{(2)}(P_XA) − C_X^{(2)}(A), ν_λ⟩ = −⟨Q_X*ν_λ, c_X(σ_A, A) + c_X(σ_A, P_XA)⟩.
- {#C10.4.101} The cancellation.
  {#C10.4.101-1} At 𝐉 = Q_X*ν_λ, Q_mH = 1 gives ⟨H(C_X^{(2)}(P_XA) − C_X^{(2)}(A)), 𝐉⟩ = ⟨C_X^{(2)}(P_XA) − C_X^{(2)}(A), ν_λ⟩, so the two bullets give π_X(A, A) = ⟨Q_X*ν_λ, c_X(σ_A, A) + c_X(σ_A, P_XA)⟩ − ⟨Q_X*ν_λ, c_X(σ_A, A) + c_X(σ_A, P_XA)⟩ = 0.
  {#C10.4.101-2} The current is Q_X*ν_λ in both runs: J^B(U^B) = Q^B_j*ν_λ at U^B, and J′_j = Q^A_{j−1}*ν_λ at run A's pair (§10.3, *The Multipliers.*). π_A and π_B are symmetric bilinear forms with vanishing quadratic forms.
  {#C10.4.101-3} Hence π_X ≡ 0 in both runs, so β_π ≡ 0.

{#C10.4.103} *The J-Term of (10.1).* hC̃^{(2)}, PBG's D̃^{(2)} as read in #C10.1.3-0, is common to both runs (#C10.4.1-4).
{#C10.4.103-1} By §10.3, J′_j = Q^A_{j−1}*𝒬′*λ^B and J^B(U^B) = Q^B_j*𝒬′*λ^B with the same 𝒬′, and Q_mH₁ = 1 in both runs.
{#C10.4.103-2} So

{#C10.4.104} ⟨H₁^AhC̃^{(2)}(B), J′_j⟩ = ⟨hC̃^{(2)}(B), 𝒬′*λ^B⟩ = ⟨H₁^BhC̃^{(2)}(B), J^B(U^B)⟩,

{#C10.4.105} and the J-terms of the two forms are equal, at the pair (Ũ_j, J′_j) and at U^B.

{#C10.4.106} *Assembly.* The lower bound below is (10.5) with ⟨E, G_A^{−1}E⟩ ≥ 0.
{#C10.4.106-1} The upper bound is the minimality in (10.2) for run B applied to ℒ𝒜^A, which is admissible because Q^B_jℒ = Q^A_{j−1}Q₁ℒ = Q^A_{j−1}; since Q₁ℒ = 1, ⟨ℒ𝒜^A, G_B^{−1}ℒ𝒜^A⟩ = ⟨𝒜^A, G_A^{−1}𝒜^A⟩ − β(ℒ𝒜^A, ℒ𝒜^A).
{#C10.4.106-2} Hence

{#C10.4.107} (10.5′) −β(𝒜^B, 𝒜^B) ≤ ⟨B, (P_B − P_A)B⟩ ≤ −β(ℒ𝒜^A, ℒ𝒜^A).

{#C10.4.108} *Regularity of the Lifts.* Here ℒ is the lift of the first paragraph of §10.4, built from Q₁ = Q̄₁(U^B), and I is gauge covariant: the multilinear interpolation with the coarse values carried to the fine bonds by the transports of U^B along coordinate paths.
{#C10.4.108-1} The node of the μ-component of a coarse bond c is the centroid of its tube in Q^{str}, the midpoint of the bond joining the centres of B(c₋) and B(c₊), which for the centred blocks of RG I (0.3) (#C10.1.4-0-1) is the midpoint of c.
{#C10.4.108-2} With these nodes Q^{str}I reproduces affine fields at U^B = 1, which the Taylor bound below needs.
{#C10.4.108-3} Q₁ℒ = 1 holds for every I by the construction of ℒ.
{#C10.4.108-4} Let g := H₁^Ae_y, so g has the sup, gradient, and 4-cell oscillation bounds of *Regularity of H₁.* with the weight 𝔰′ := B₀ℓ^{−1}e^{−½δ₁d(·,y)}.

- {#C10.4.109} In the axial gauge about a coarse point, Ig is a convex combination of transported coarse values.
  {#C10.4.109-1} So |Ig| ≤ sup|g|; its fine differences are interpolated coarse differences of g up to (2d + 128d²)ν_F𝔰′ ≤ 2C_trν_F𝔰′.
  {#C10.4.109-2} Two terms make this up.
  {#C10.4.109-3} The coordinate paths that carry the coarse values to the two ends of a fine bond b, together with b, enclose a strip of at most dL fine plaquettes, so the two transports differ by at most 2dε(ε/L)|F|, which after division by ε/L is 2dε|F||g| ≤ 2dν_F𝔰′ by |g| ≤ ℓ𝔰′.
  {#C10.4.109-4} The differences of the interpolation weights, of total at most 2/ε after division by ε/L, act on values carried along different node paths, which in the axial gauge are within 2δ_T of each other, so they add at most (2/ε)·2δ_T|g| = 128d²ε|F||g| ≤ 128d²ν_F𝔰′.
  {#C10.4.109-5} And their oscillation over a fine 4-cell of side 4ε is at most that of ∇g over a coarse cell of side 6ε, (3/2)^{γ_H}𝔬, plus 4C_trν_F𝔰′: twice the error above, and the passage from the transports of the interpolation, within δ_T of 1, to those of the Hölder quotients, along a fine contour within δ_T of 1 and a coarse one of at most 6d links of Ũ_j, each within δ_T of 1 (#C10.4.9-2-1), at most (6d + 3)δ_T sup|∇g| ≤ 288d³ν_F𝔰′ as in #C10.4.14-3, with 4d + 256d² + 288d³ ≤ 4C_tr.
- {#C10.4.110} In the same gauge Q^{str}I reproduces affine fields, by the choice of the nodes, so Taylor's formula about the node of each coarse bond gives |g − Q₁Ig| ≤ max(C, 1)(ε²|∇∇g| + C_trε²|F||g|), with C a constant of d bounding the total weight of the second differences in the remainder. And ε²|∇∇g| ≤ ε𝔬 on the lattice, ε times a covariant second difference being a difference of ∇g along one coarse link.
  {#C10.4.110-0} The second term collects the transports of Q^{str} and I (2δ_T), those of the second differences, taken in the axial gauge and within 4δ_T|g| of the covariant ones, and the non-main terms of CMP 98 (124) (c₁₂₄ε²|F|, #C10.4.9-6): 4Cδ_T + 2δ_T + c₁₂₄ε²|F| ≤ max(C, 1)C_trε²|F|.
  {#C10.4.110-1} The correction is Q₁*T_Q^{−1}(g − Q₁Ig), with T_Q := Q₁Q₁* on the coarse bond fields, and T_Q^{−1} is bounded at U^B as follows.
  - {#C10.4.111} T_Q has finite range, T_Q(c, c′) = 0 unless d_ε(c, c′) ≤ r_T, with r_T a constant of d, since the paths of Q₁ stay within 2L fine spacings.
    {#C10.4.111-1} Its norm is at most a constant M̃_Q of L and d, since Ad is isometric.
    {#C10.4.111-2} At U^B = 1 its spectrum is bounded below by m_Q := 1/3.
    {#C10.4.111-3} There T_Q acts along each coordinate column as a convolution with the overlaps of the tents of (ii): its diagonal entry (2L³ + L)/(3L³) exceeds the sum (L³ − L)/(3L³) of the others by (L³ + 2L)/(3L³) ≥ 1/3.
  - {#C10.4.112} The lower bound at U^B.
    {#C10.4.112-1} Let χ_i be functions supported in boxes of side R_Qε, with Σ_iχ_i² = 1 and |χ_i(c) − χ_i(c′)| ≤ C_χd_ε(c, c′)/R_Q, C_χ a constant of d.
    {#C10.4.112-2} Then T_Q = Σ_iχ_iT_Qχ_i + ½Σ_i(χ_i(c) − χ_i(c′))²T_Q(c, c′), and the second sum has norm at most C_E/R_Q², with C_E a constant of L and d, since T_Q has range r_T and each point lies in at most 2^d boxes.
    {#C10.4.112-3} T_Q is gauge covariant: differentiating CMP 98 (11) gives Q₁^{pl}(U^u)Ad(u) = Ad(u|)Q₁^{pl}(U), with u| the restriction to the coarse points, and Θ₁ is covariant in the same way, since v₁(y) = (R_{0,y}U₁)‾ (CMP 98 (97), (105)) is conjugated by u(y), so by (B1) Q̄₁(U^u)Ad(u) = Ad(u|)Q̄₁(U) and T_Q(U^u) = Ad(u|)T_Q(U)Ad(u|)^{−1}.
    {#C10.4.112-4} Ad is isometric, so χ_iT_Qχ_i is unitarily equivalent to its form in the axial gauge of its box.
    {#C10.4.112-5} There the bonds of the box and of the paths of Q₁ that start in it have |U^B(b) − 1| ≤ d(R_Q + 3)ε(ε/L)|F|, so on the fields supported in the box T_Q(U^B) − T_Q(1) has norm at most C_ax·d(R_Q + 3)ε²|F|, with C_ax a constant of L, d, and G (through c₁₂₄ for the non-main terms), and |⟨χ_iν, (T_Q(U^B) − T_Q(1))χ_iν⟩| ≤ C_ax·d(R_Q + 3)ε²|F|‖χ_iν‖².
    {#C10.4.112-6} R_Q is fixed by C_E/R_Q² ≤ m_Q/4.
    {#C10.4.112-7} Under C_ax·d(R_Q + 3)C₀ε₁ ≤ m_Q/4, since ε²|F| ≤ C₀ε₁ by (9.2) and ⟨χ_iν, T_Q(1)χ_iν⟩ ≥ m_Q‖χ_iν‖², Σ_i⟨χ_iν, T_Qχ_iν⟩ ≥ (3/4)m_QΣ_i‖χ_iν‖² = (3/4)m_Q‖ν‖², so with #C10.4.112-2 and #C10.4.112-6 the spectrum of T_Q lies in [m_Q/2, M̃_Q].
  - {#C10.4.113} The decay.
    {#C10.4.113-1} With q_T := 1 − m_Q/(2M̃_Q), the Neumann series T_Q^{−1} = M̃_Q^{−1}Σ_{n≥0}(1 − T_Q/M̃_Q)^n, whose n-th term has norm at most q_T^n and range nr_T, gives |T_Q^{−1}(c, c′)| ≤ (2/m_Q)e^{−δ_Qd_ε(c,c′)}, δ_Q := r_T^{−1}log(1/q_T).
    {#C10.4.113-2} For δ₁ ≤ δ_Q, T_Q^{−1} maps a source bounded by a multiple of e^{−½δ₁d(·,y)} to at most C_Q times the same multiple, C_Q := (2/m_Q)sup_cΣ_{c′}e^{−½δ_Qd_ε(c,c′)}, by the triangle inequality.
    {#C10.4.113-3} Also sup|Q₁*ν| ≤ 2(1 + 2dL^{d−1})sup|ν|.
    {#C10.4.113-4} The main term (125) of CMP 98 (124) has column sums 1.
    {#C10.4.113-5} The third term of (124), the non-main operator on the straight paths [x, x′], has column weight 1, the Γ-terms, taken over the families with weights of total at most 3/2 for each x (#C10.4.9-1-1-1), have column weight at most 3dL^{d−1}, and the last term at most L^{d−1}.
    {#C10.4.113-6} The operator factors of these non-main terms are at most c₁₂₄L²α₀ (CMP 98 p.036, after (124), and (126)), with L²α₀ = ε²|F| ≤ C₀ε₁, so at most ½ under c₁₂₄C₀ε₁ ≤ ½, and Proposition 3 applies under 2C₀ε₁ ≤ c₃.
    {#C10.4.113-7} The total is at most 1 + ½(1 + 3dL^{d−1} + L^{d−1}) ≤ 2(1 + 2dL^{d−1}).
  - {#C10.4.114} With δ₁ ≤ min(δ_Q, 1/(10d)), the weight 𝔰′ changes by at most the factor e^{1/4} < 4/3 over the ℓ¹ distance 5dε, which covers the sup and Taylor stencils (3dε) and the points of the 6ε-cell of the oscillation bullet (5ε per coordinate).
    {#C10.4.114-1} The factor (3/2)^{γ_H} of the first bullet is the ratio of the cube sides for the ℓ^∞ distance, and at most 3^{γ_H} for the Euclidean distance (the side-6ε cell has Euclidean diameter 6ε√d = 12ε at d = 4).
    {#C10.4.114-2} So the bounds of this paragraph hold with the weight taken at the point, the first bullet's (3/2)^{γ_H}𝔬 becoming at most 4𝔬, since 3^γ·4/3 < 4 for every exponent γ < 1, in particular at γ_H and at 2γ_H. This holds for the ℓ^∞ and for the Euclidean distance; PBG (3.40) writes |x′ − x| without naming the norm. The factor 4 of C_ℒ′ below covers this.

  {#C10.4.115} The correction therefore has sup at most C_I(ε𝔬 + C_trεν_F𝔰′), with C_I := 2(1 + 2dL^{d−1})C_Q·max(C, 1).
  {#C10.4.115-1} Its fine differences are at most 2(L/ε) times its sup, 2LC_I(𝔬 + C_trν_F𝔰′).

{#C10.4.116} With ν_F ≤ (ε/ℓ)^{γ_H} (C₀ε₁ ≤ 1), ℒH₁^Ae_y satisfies the sup, gradient, and 4-cell oscillation bounds of *Regularity of H₁.* with B₀ replaced by C_ℒ′B₀ and B₀(γ_H) by C_ℒ′(B₀(γ_H) + B₀), where C_ℒ′ := 4(1 + 2C_tr)(1 + 2LC_I(1 + h_H)).
{#C10.4.116-1} The bounds above are for fine differences; the curl and divergence, sums of 2 and of d fine differences, carry the factors 2 and d in their oscillations, as in *Regularity of H₁.* The derivation holds at every Hölder exponent γ of (3.133) in place of γ_H, with h_H(γ) := 4^γB₀(γ)/B₀ in C_ℒ′; at the exponent 2γ_H of *Polarisation.*, h_H(2γ_H) = 16^{γ_H}B₀(2γ_H)/B₀ and B₀(2γ_H) + B₀ replaces B₀(2γ_H).

{#C10.4.117} *Polarisation.* 𝒜^B = Σ_yH₁^B(e_y ⊗ B(y)) expands over the points y, and ℒ𝒜^A likewise.
{#C10.4.117-1} Since β_π ≡ 0, β = β_act + β_con + β_gf.
{#C10.4.117-2} (10.6a) and (10.6b) apply at the exponent 2γ_H, which is admissible in (3.133) and (3.43) for 0 < γ_H < ½, to H₁^Be_y and to C_ℒ′(2γ_H)^{−1}ℒH₁^Ae_y.
{#C10.4.117-3} C_β^ℒ and C_gf^ℒ denote C_β and C_gf at the exponent 2γ_H (increasing in B₀(2γ_H)) with B₀(2γ_H) + B₀ in place of B₀(2γ_H).
{#C10.4.117-4} With ε/ℓ ≤ (ε/ℓ)^{2γ_H}, ε₁ ≤ 1, and C₀ε₁ ≤ 1, (10.5′) gives

{#C10.4.118} (A1) |⟨B, (P_B − P_A)B⟩| ≤ r_βΣ_{y,y′}|B(y)||B(y′)|B₀ℓ^{−2}ℓ^de^{−¼δ₁d(y,y′)}, r_β := 2C_ℒ′(2γ_H)²[C_β^ℒ(2γ_H) + C_gf^ℒ(2γ_H)](ε/ℓ)^{2γ_H}.

{#C10.4.119} P_B − P_A is symmetric.
{#C10.4.119-1} Polarisation, ⟨u, Tv⟩ = ¼[⟨u + v, T(u + v)⟩ − ⟨u − v, T(u − v)⟩] for a symmetric T, at T = P_B − P_A, u = e_y ⊗ X, and v = e_{y′} ⊗ X′ with |X| = |X′| = 1, gives |(P_B − P_A)(y, y′)| ≤ 2r_βB₀ℓ^{−2}ℓ^{−d}, without decay.

{#C10.4.120} *Interpolation.* P_B − P_A is also the difference of the two runs' (Q_mG₁Q_m*)^{−1}, the a-terms cancelling, so (3.132) gives |(P_B − P_A)(y, y′)| ≤ 2B₀ℓ^{−2}ℓ^{−d}e^{−δ₁d(y,y′)}.
{#C10.4.120-1} With min(u, v) ≤ (uv)^{1/2},

{#C10.4.121} (A2) |(P_B − P_A)(y, y′)| ≤ 2r_β^{1/2}B₀ℓ^{−2}ℓ^{−d}e^{−½δ₁d(y,y′)} ≤ 3C_ℒ′(2γ_H)[C_β^ℒ(2γ_H) + C_gf^ℒ(2γ_H)]^{1/2}L^{−γ_H(j−1)}B₀ℓ^{−2}ℓ^{−d}e^{−½δ₁d(y,y′)}.

{#C10.4.122} δΔ_j is this difference, the J-terms and the 𝐆^{(2)}-terms being equal (#C10.4.105, #C10.4.1-4), plus the alignment (10.3), whose factor relative to B₀ is at most [16C_G(ε₀) + 8x_J(C_G(ε₀) + 1)]((B₀^{cx} + a + C_𝐉 + C_𝐆)/B₀)ε₁L^{−(1−ε₀)j}/α_* by ρ_j = C_G(ε₀)L^{−(1−ε₀)j}ε₁ and ε/a_j = L^{−j}, at the rate δ₁′ ≥ δ₂, and (A2)'s rate is ½δ₁ ≥ δ₂ (#C10.1.3-3).
{#C10.4.122-1} Hence

{#C10.4.123} (10.6) |δΔ_j(y, y′)| ≤ r_jB₀ℓ^{−2}ℓ^{−d}e^{−δ₂d(y,y′)}, r_j ≤ C(ε₀, γ_H)[L^{−γ_H(j−1)} + ε₁L^{−(1−ε₀)j}/α_*] with α_* := min(α₁, α_J) and C(ε₀, γ_H) := 3C_ℒ′(2γ_H)[C_β^ℒ(2γ_H) + C_gf^ℒ(2γ_H)]^{1/2} + [16C_G(ε₀) + 8x_J(C_G(ε₀) + 1)](B₀^{cx} + a + C_𝐉 + C_𝐆)/B₀,

{#C10.4.124} for j ≥ 1, 0 < γ_H < ½, 0 < ε₀ < ½, under the conditions of #C10.3.51–#C10.3.51-0-2 (those on ε₁ for all j, by ρ_j ≤ C_G(ε₀)ε₁), for C₀ε₁ ≤ 1, for 16dC₀ε₁ ≤ r_G (*Analyticity.*), for 198c_{GM}dC₀ε₁ ≤ 1, 24c_BdC₀ε₁ ≤ 1, and 12dC₀ε₁ ≤ r_{BCH} (#C10.4.9-1-1-1), for 16c₁₂₄C₀ε₁ ≤ 1 (the non-main terms of CMP 98 (124) in *Transports.*, *Regularity of the Lifts.*, and the identification of E, and *The Size of w.*), and for C_ax·d(R_Q + 3)C₀ε₁ ≤ m_Q/4 (*Regularity of the Lifts.*), with δ₁ ≤ min(δ₀, δ_Q, 1/(10d)) (#C10.4.66-3, #C10.4.114) and B₀(γ_H), B₀(2γ_H) ≥ 9B₀ (#C10.4.8-2-1, #C10.4.116-1).
{#C10.4.124-1} The constants depend on d, L, G, γ_H, ε₀, and the constants of VAR, PBG, and CMP 98 only, and not on j, k, K, ε, or the volume.

### 10.5 The Parts of the Depth Source and the 𝐑-Terms' Group {#CS10.5}

{#C10.5.1} In (8.1) the quadratic insertion −½⟨A, C*δΔ^{(k)}CA⟩ on a localisation domain Y is a marked activity of §8.5's kind: it is ⟨A, KA⟩ with K := −½C*δΔ^{(k)}C. The kernel bound r_kB₀e^{−δ₂d(y,y′)} of (10.6) is symmetric in y and y′, so in scale-ℓ units both sup_yΣ_{y′}|δΔ_k(y,y′)| and the column sums of δΔ_k are at most c_{δ₂}r_kB₀. The row sums of C* are the column sums of C, and its column sums are the row sums of C. So the row and the column sums of K are at most ½‖C‖_∞‖C‖_1c_{δ₂}r_kB₀, which bounds ‖K‖_Y.
{#C10.5.1-1} Here c_{δ₂} := sup_yΣ_{y′}e^{−δ₂d(y,y′)} at the rate δ₂ = min(δ₁′, ½δ₁) of (10.6), and ‖C‖_1, the column-sum norm of C, is a constant of L and d, as ‖C‖_∞ is. So the Gaussian part of the insertion is ι_G(Y) ≤ ½C_G″‖C‖_∞‖C‖_1|Y|c_{δ₂}r_kB₀ by RMark, and its bound on the cutoff ball, where sup_b|CA_k(b)| ≤ ‖C‖_∞r^χ_k, is ι(Y) ≤ |Y|c_{δ₂}r_kB₀‖C‖_∞²(r^χ_k)².
{#C10.5.1-2} So by the two-part bound of §8.5, with the factors |Y| absorbed in C_pt, its contribution to the generated difference per scale-(k+1) point is ≤ C_ptC_KPC_Xc_{δ₂}B₀[½C_G″‖C‖_∞‖C‖_1 + a_k‖C‖_∞²(r^χ_k)²]r_k ≤ C_e′r_k, uniformly in k, since a_k(r^χ_k)² ≤ (A₁/A₀)²g_kP_a(log g_k^{−2})p₀(ĝ_k)² → 0 (#C8.2.1-6, #C8.2.2-84). It is geometric in k by (10.6).
{#C10.5.1-4} This is the Gaussian part of the depth source e_{k+1} of (8.3), which together with the classical part gives e_{k+1} ≤ C_eθ̃^{k+1}, and Σ_k of it is finite.
{#C10.5.1-5} The classical part of e_{k+1} is (9.10) at the fluctuated block field (§8.1).
{#C10.5.1-6} The configuration part, the variation group of (3.1) and its fluctuation-dependent version in §8.2, is the change of a frozen term under the scale-a smooth background change of §9.7, |𝒜| ≤ σ_k/a, |∇𝒜| ≤ σ_k/a². It is bounded with an age factor.
{#C10.5.1-7} The age factor comes from (5.1v) of §5 (*What it gives*).
{#C10.5.1-8} Each of the group's two values has the age bound of (5.1c) for one term, at a local minimiser of its own lattice, and the geometric mean of that bound with the Cauchy bound along the pair line of §5 gives E_V[(σ̂_{k,j}/r_{0,k})^{θ_V} + (C_Π(j)ε₁²e^{−δ₀M₁L^j})^{θ_V}](L^{j−k})^{4+β′/2} per scale-(j+1) point, θ_V = β′/(2(4+β′)), σ̂_{k,j} = σ_k + C(ε₀)ρ_k + C(ε₀, δ₀M₁)ε₁e^{−δ₀M₁L^j/2}.
{#C10.5.1-9} At the stopping scale this carries L^{−(β′/2)(k−j)}N_s⁴, and the sum over j is summable in K (§5).
{#C10.5.1-10} It uses the lift condition of §5.
{#C10.5.1-11} At the fluctuation-dependent configurations the two bounds hold on the complex lines t ↦ tA of §8.2: the age bound on the whole disc, where both configurations are local minimisers of complex data, and the Cauchy bound on its real diameter, where the block field is real and regular by (3.14) and §9.7 applies.
{#C10.5.1-12} On that diameter the block field carries the fluctuation up to the margin m_k, so the ε₁ of §9.7 is the plaquette bound at that level, at most O(1)α_{0,k}, and σ̂_{k,j}/r_{0,k} ≤ O(1)B₃C_σ̂(L^{−(1−2ε₀)k} + e^{−δ₀M₁L^j/2}), with the same sum over j as in §5.
{#C10.5.1-13} The harmonic measure of the circle at the points of the disc of a quarter of the radius, relative to the disc cut along the diameter, is ≤ (4/π)arctan(1/4) < 1/3.
{#C10.5.1-14} So by the two-constants theorem the group is ≤ (E_V[(σ̂_{k,j}/r_{0,k})^{θ_V} + (C_Π(j)ε₁²e^{−δ₀M₁L^j})^{θ_V}])^{2/3}(2E₁(α))^{1/3}(L^{j−k})^{4+2β′/3} on that smaller disc, and §8.2's argument uses it with T₀ ≥ 8, a threshold of the same kind as T₀ ≥ 2 there.

{#C10.5.2} The 𝐑-terms' group (§5, *The 𝐑-terms' variation group*) has a fluctuation-dependent version at each step k, split at the age m(k) := ⌊(1 − 2ε₀)k/12⌋.
- {#C10.5.3} At the ages k − j < m(k).
  {#C10.5.3-1} The two bounds are (2.31) on the whole disc, 2g_j^{κ₀}exp(−κd_j(X)) per domain for the two values, and C′_σ(σ̂_{k,j}/r_{0,k})g_j^{κ₀}exp(−κd_j(X)) on its real diameter, C′_σ := C_σ + 16C_J, by the frozen-current split of §5.
  {#C10.5.3-2} So the two-constants theorem gives ≤ 2^{1/3}(C′_σσ̂_{k,j}/r_{0,k})^{2/3}g_j^{κ₀}exp(−κd_j(X)) per domain on the smaller disc.
  {#C10.5.3-3} At these ages e^{−δ₀M₁L^j/2} ≤ L^{−(1−2ε₀)k} except at finitely many k, so σ̂_{k,j} ≤ C_σ̂L^{−(1−2ε₀)k}ε₁, and C′_R absorbs the finitely many k.
  {#C10.5.3-4} With C_X and the L^{4(k−j)} points this is ≤ 2^{1/3}C_XC′_σ^{2/3}(sup_{k−j<m(k)}σ̂_{k,j}/r_{0,k})^{2/3}L^{4m(k)}/(1 − L^{−4}) ≤ C′_RL^{−(1−2ε₀)k/3} per scale-(k+1) point.
  {#C10.5.3-5} It is a part of e_{k+1}, since θ̃ ≥ L^{−(1−2ε₀)/3} (§8.7).
- {#C10.5.4} At the ages k − j ≥ m(k).
  {#C10.5.4-1} Each run's term at its own fluctuation-dependent configuration, a U_k-type configuration (p.279 l.43–44), has p.283's bound O(1)(L^jL^{−k})⁴g_j^{κ₀}exp(−κd_j(X)) on the disc.
  {#C10.5.4-2} This is the 𝐑 version of (5.1c) at complex configurations.
  {#C10.5.4-3} The configurations on the disc are local minimisers of complex data, so they lie in 𝒮_z, and the bound there is §5's RΔ^c for one term (d = 1, the other term zero), run for 𝐑^{(j)} and stopped at (3.49).
  - {#C10.5.5} The terms.
    {#C10.5.5-1} By CRE p.260, after (2.30), the terms 𝐑^{(j)}(X, ·) have the properties (i)–(iii) of p.259: localisation, analyticity on U^c_j(X, α₀, α₁), and gauge invariance.
    {#C10.5.5-2} In place of (iv) they have (2.31), the bound g_j^{κ₀}exp(−κd_j(X)) in place of E₀exp(−κd_j(X)).
  - {#C10.5.6} The steps.
    {#C10.5.6-1} Bałaban proves (2.44) by the analysis of (2.43) stopped at (3.49), with 𝐑^{(2)}(X, x, y) for 𝐄^{(2)}(X, x, y, z) and z any point of X (p.283 l.36–40).
    {#C10.5.6-2} Up to (3.49) that analysis is the far-domain bound (3.48), RG I's (3.3) and (3.18)–(3.28) at the scale n, the expansion (I.3.34) with the remainder (I.3.54), and RG I §4 with the Ward–Takahashi identities (I.4.14)–(I.4.15) (p.280 l.4–37).
    {#C10.5.6-3} §5's *Evidence.* checks each of these steps: each is linear in the term, proportional to the term's sup bound on its analyticity domain, and uses the gauge invariance (iii), not the covariance.
    {#C10.5.6-4} §5's RΔ^c runs them at the complex points of 𝒮_z (*Complex domain (RΔ^c).*, *Bałaban's analysis on complex configurations.*), at the near domains that meet a finer layer through (RΔ^c-T), with the uniform constant C_α.
    {#C10.5.6-5} No lift enters, since each run's term is evaluated on its own run.
  - {#C10.5.7} The right side of (3.49).
    {#C10.5.7-1} For 𝐑 the marginal term is bounded, not subtracted.
    {#C10.5.7-2} Its coefficient Σ_{x,y}𝐑^{(2)}_{μν}(X, x, y)(x_κ − z_κ)(y_λ − z_λ) is a second derivative at B = 0, bounded by the Cauchy estimate on the polydisc of the radius α_{2,j}, with diam(X)² absorbed by half of exp(−κd_j(X)).
    {#C10.5.7-3} Each of the two curvature factors at z is ≤ O(1)L^{2(j−n)} in the units of the scale j at every point of 𝒮_z, since the background there has the amplitude O(1)B₃Mα_{0,n} in the L^{−n}-scale with its first differences, as at real points (*Complex domain (RΔ^c).*).
    {#C10.5.7-4} The irrelevant terms satisfy bounds of the form (0.29) on their domains of analyticity (RG I p.281 l.3–4), proportional to the sup bound.
    {#C10.5.7-5} So |𝐑^{(j)}(X, U) − 𝐑^{(j)}(X, 1)| ≤ C_αO(1)(L^jL^{−n})⁴g_j^{κ₀}exp(−κd_j(X)) at the points of 𝒮_z, with §5's constant C_α.
  - {#C10.5.8} The sum.
    {#C10.5.8-1} With it, g_j^{−2} ≥ ḡ^{−2} + b(K − j) − C with K − j ≥ K − k + m(k) ≥ (1 − 2ε₀)K/12 − 1 by Lemma 2.1(i), so these ages give ≤ C″_RK^{1−κ₀/2} per scale-(k+1) point at each step.
    {#C10.5.8-2} This source is a part of ν_{k+1} of §8.6, which enters the 𝐑-differences d^R_{k+1} and so S_K = Σ_{j≤K}d^R_j without contraction; it adds ≤ C″_RK^{2−κ₀/2} to Σ_{j≤K}ν_j.
    {#C10.5.8-3} The weight μ_K := K^{2−κ₀/2}ℓ_K of §8.6–8.7 covers it, and w_K, Kw_K, and K²w_K are summable for κ₀ ≥ 11, a choice that CRE p.260 allows after (2.31) ("κ₀ can be chosen arbitrarily large").

## 11. The Relative Weight of the Large-Field Terms {#CS11}

{#C11.1} The relative weight of the large-field terms is bounded by comparing whole integrals on the stopping lattice T_a, which is fixed and finite, with N_s⁴ points.
{#C11.1-1} The whole all-small-field integral is bounded below by the Haar volume of a ball of configurations, and every large-field term's integral is bounded above by the supremum of its small-field exponent, each at the price of a constant exponential in N_s⁴ and independent of K. The relative weight is then bounded uniformly in K at every loop, and it is small for ḡ small at a fixed loop and torus.
{#C11.1-3} The one cost that this comparison does not bound by N_s⁴ is the small-field action on the inner layers of a component's history, which CRE's Theorem 2 counts at their own scales.
{#C11.1-4} It is paid in (c)–(d) from the costs and half of the gains of (1.79), which also leave a spare factor exponential in the history volume for §6 and §8.6.

### 11(a) The Terms at the Stopping Scale {#CS11a}

{#C11a.1} By CRE (2.18) the stopping-scale density is ρ_k(V) = Σ_ℓρ_ℓ(V), the sum over the labelled terms ℓ (the sequences {Ω_j}, {Λ_j} and the 𝐑-operation labels), each ρ_ℓ(V) = χ_k(Ω_k)𝐓_k(ℓ)[exp A_k(1/g_k², U_k)] a function of the stopping-scale field V on the bonds of T_a, nonnegative on the real integration region, with the effective action (2.23), A_k = −A(1/g_k², U_k) + 𝐄_k + 𝐑_k + 𝐁_k − E_k.
{#C11a.1-1} The weights are Z_ℓ := ∫ρ_ℓ(V) dV with the normalised Haar measure on G^{bonds(T_a)}, w_ℓ := Z_ℓ/Σ_{ℓ′}Z_{ℓ′}, and 1 − w_{ℓ₀} = Σ_{ℓ≠ℓ₀}Z_ℓ/Σ_{ℓ′}Z_{ℓ′} ≤ Σ_{ℓ≠ℓ₀}Z_ℓ/Z_{ℓ₀}, as every Z_ℓ ≥ 0.

{#C11a.2} Every term is written in the completed form of LFR II p.377 l.22–29 for its kept components, and in the factorised form with the normalised operations of (1.79) for its surviving components, (1.79) holding for an arbitrary large-field region (p.387 l.36–39), with the constants of the latter accounted outside 𝐓 in E^ℓ.
{#C11a.2-1} Bałaban adds the terms of the effective action whose localisations meet the large-field domain "to complete the effective action, and we subtract them from the remaining expression".
{#C11a.2-2} The term is then χ_k·Π_{X⊂Z(ℓ)}𝐓′_k(X)·exp A′_k, with A′_k "the whole new action connected with the new determining set 𝐁_k" (p.377 l.22–28).
{#C11a.2-3} The subtracted constants, E_k(X) + (−½d(𝐠)log g_k^{−2} + log σ₀)|(𝐁₀∖T₀) ∩ X| − E_k(Λ ∩ X), stand inside the integration of 𝐓′_k(X) ((1.70); E_k(Z) is "the sum of normalization terms and vacuum energy terms with localizations intersecting the large field domain Z", p.378 l.2).
{#C11a.2-4} LFR II p.387 l.36–39 states that (1.79) holds for the 𝐓-operation connected with an arbitrary large-field region and that (1.80) holds for such regions; CRE p.264 l.17–23 is the resulting estimate of ∫dV_kρ_k "by a sum of terms".
{#C11a.2-5} The normalisation used below divides every term by e^{−E^{ℓ₀}}, the constant of the all-small-field term ℓ₀, one number for all terms.
{#C11a.2-6} Then, for every term ℓ,

{#C11a.3} Z_ℓ ≤ Π_{X⊂Z(ℓ)}[e·sup 𝐓′_k(X)1]·sup exp(𝒜_ℓ), the second supremum over the term's integration region, with the following ingredients.

- {#C11a.4} 𝐓′_k(X) is the operation of the component X, normalised as in (1.79) and bounded by (1.79)'s right side (p.383 l.46–p.384 l.1).
  {#C11a.4-1} For a kept component it is the operation of LFR I p.177's renormalisation class after the completion of LFR II pp.377–378.
  {#C11a.4-2} For a surviving component it is CRE (2.20)–(2.21)'s operation, which the 𝐑-operation leaves unchanged (LFR I p.177 l.42–43).
- {#C11a.5} Inside 𝐓′_k(X) are the subtracted constants of (1.70), the normalisation constants of the large-field integrations with their logarithms (LFR II p.380 l.24–27, p.383 l.29–31), and the inner-layer action V(X^∼) of (1.69).
- {#C11a.6} The gauge-fixing δ-functions of a kept component (LFR II (1.72), p.378 l.21–22) are integrated first against the normalised Haar measure, so the bound holds for Z_ℓ and not pointwise in V. Removing the δ-functions of a first-class component gives a density that is "equivalent, but not equal" (p.378 l.18–20), with the same Z_ℓ.
- {#C11a.7} The factor e per component is from (1.92) (e^{|σ|} ≤ e by (1.73)); the supremum is over the integrated variables and the exterior field ((1.79), uniform in both).
- {#C11a.8} 𝒜_ℓ is the term's completed exponent less the common constant: −A(1/g_k²(·), U_k) + 𝐄_k + 𝐑_k + 𝐁_k + (E^{ℓ₀} − E^ℓ), with, for a kept component, the exterior couplings V(Y) of (1.68) and 𝐑′ of (1.99).
  {#C11a.8-1} Here E^ℓ is the constant of A′_k.
- {#C11a.9} The normalisation and vacuum-energy terms of E^ℓ are localised.
  {#C11a.9-1} Those whose localisation meets no layer and no large-field region of a component's history are the terms of ℓ₀, since the determining sets of ℓ and ℓ₀ coincide there and the expansions that produce the terms are local.
  {#C11a.9-2} The sources are CRE p.262 l.16–18, where E_k "is obtained by subtracting one-step vacuum energy expressions, generated in small field regions, from the initial constant E"; LFR II p.378 l.2, where E_k(Z) "denotes the sum of normalization terms and vacuum energy terms with localizations intersecting the large field domain Z"; and LFR II p.380 l.24–26, where the vacuum energy counterterms and normalisation constants obey the bounds of V(X^∼), with "the corresponding constant O(log g_j^{−2}) instead of O(1)" for the latter.
  {#C11a.9-3} C_λ absorbs the O(1)-layer enlargement of these localisations and their exponential tails.
  {#C11a.9-4} The renormalised components are removed from the sequence (LFR I (0.3)).
  {#C11a.9-5} So E^{ℓ₀} − E^ℓ is a sum over the histories.
  {#C11a.9-6} A normalisation constant is at most ½d(𝐠)log g_n^{−2} + |log σ₀| per integration variable ((1.70)), and the vacuum energies are at most E₂ per point (CRE p.264 l.14–15).
  {#C11a.9-7} Counting the constants of both terms, |E^{ℓ₀} − E^ℓ| ≤ Σ_{X⊂Z(ℓ)}Σ_{n≤k}C_λ(1 + log g_n^{−2})L^d|Z_n ∩ X|_n, with C_λ a constant of d, G, σ₀, and E₂.
  {#C11a.9-8} This is part of the history cost, paid in (c).

{#C11a.10} For ℓ₀ the same normalisation gives the identity ρ_{ℓ₀} = χ_k(T)exp(𝒜_{ℓ₀}), 𝒜_{ℓ₀} = −A(U_k(V))/g_a² + 𝐄_k(U_k(V)) + 𝐑_k(U_k(V)), since its 𝐓-operation is trivial.
{#C11a.10-1} Here U_k(V) is the minimiser of VAR Theorem 1 on the whole torus; 𝐑_k carries the renormalised components of the history (LFR I (0.6)), and 𝐁_k = 0 without large-field regions (CRE (2.41)).

### 11(b) The Final-Scale Comparison {#CS11b}

{#C11b.1} *Upper Bound.* The action is nonnegative, A(1/g², U) = Σ_p g^{−2}(x_p)η^{d−4}[1 − Re tr U(∂p)] ≥ 0 with the normalised trace (VAR (5); PBG p.392 l.2), so −A(1/g_k²(·), U_k) ≤ 0 everywhere.
{#C11b.1-1} On the term's integration region, which the characteristic functions of (2.18) and of the large-field operations restrict (CRE p.256 l.27–29: V_{j−1} is regular on Γ_{j−1}), Theorem 2 gives |𝐄_k| ≤ E₁(1 − L^{−β})^{−1}Σ_n|Γ_n| ((2.45)), |𝐑_k| ≤ Σ_n|Γ_n| ((2.46), κ₀ ≥ 7), |𝐁_k| ≤ 2B_∂Σ_n|Γ_n| ((2.48), B_∂ the constant printed B₁ in (2.47)), |Γ_n| the number of points of the layer Γ_n of the term's determining set in the scale-n lattice T_1^{(n)} (p.263 l.21–23); this is (2.49) without its constants, which (a) treats.
{#C11b.1-2} The exterior couplings of a kept component are its terms V(Y) of (1.68) with Y ⊄ Z^∼, at most αe^{−(1+2β)κd_{k,Z}(Y)} with α arbitrarily small for γ small (p.377 l.11–14), and its terms 𝐑′ of (1.99) meeting the kept components, at most O(1)α^{1/3}e^{−(1+½β)κd_{k,∪Y_i}(X′)} (p.390 l.2, l.15). Summed over the polymers meeting a given MR_k-cube, these are at most C_∂ := C(α + α^{1/3}) ≤ 1 for γ small and κ large, so they contribute ≤ C_∂N_s⁴ over the at most N_s⁴ cubes of T_a.
{#C11b.1-3} So, with C_ℰ := E₁(1 − L^{−β})^{−1} + 1 + 2B_∂, −A ≤ 0, and the bound of (a) on E^{ℓ₀} − E^ℓ, 𝒜_ℓ ≤ C_ℰΣ_{n≤k}|Γ_n(ℓ)|_n + C_∂N_s⁴ + |E^{ℓ₀} − E^ℓ| ≤ (C_ℰ + C_∂)N_s⁴ + Σ_{X⊂Z(ℓ)}P^c(X), P^c(X) := Σ_{n≤k}c_nL^d|Z_n ∩ X|_n, c_n := C_ℰ + C_λ(1 + log g_n^{−2}), since Σ_{n<k}|Γ_n ∩ X|_n ≤ Σ_{n≤k}L^d|Z_n ∩ X|_n by the inclusion below.
{#C11b.1-5} The last layer Γ_k lies in T_a, and every earlier layer Γ_n ⊂ Ω_{n+1}^c ⊂ Z_{n+1} lies inside a component of the stopping-scale region: the large-field regions grow and merge by (1.84) until renormalised, and a renormalised component is no longer in Z(ℓ), since the renormalised term is ρ(Z″, V) with that component removed (LFR I (0.3)); and |Γ_n ∩ X|_n ≤ L^d|Z_{n+1} ∩ X|_{n+1}.
{#C11b.1-6} P^c(X) is the history cost of X, paid in (c).

{#C11b.2} *Lower Bound.* Let 𝔅 := {V : |V_b − 1| < r_𝔅 for every bond b of T_a}, r_𝔅 := g_a/(8B₃C_av), with C_av a Lipschitz bound on 𝔅 for the averaged extension M^·(Q_k^{s*}V) of (2.16).
{#C11b.2-1} C_av = 1.
{#C11b.2-2} The entries of Q^{s*}V are 1 on the bonds inside the blocks and V(c) on the bond b ∈ B(c) (CRE (1.3)).
{#C11b.2-3} The averaging is RG I (0.4) (#C10.1.4–#C10.1.4-0-2), and the blocks of each level are unions of blocks of the finer levels (RG I (0.3)).
{#C11b.2-4} So M^j(Q_k^{s*}V) is 1 on the level-j bonds inside k-blocks and V(c) on those joining the k-blocks of a bond c, by induction on j. For a level-(j + 1) bond b′, the contours Γ, Γ′ of every path γ_{b′,x}^{Γ,Γ′} lie in the blocks of b′₋ and b′₊, inside k-blocks, and carry 1. The segment [x, x′] and the straight path of b′ each cross the face between the k-blocks of b′₋ and b′₊ once if these differ, on a bond carrying V(c), and otherwise carry 1. So every h_{b′,x}^{Γ,Γ′} is 1, and the average on b′ is 1 or V(c).
{#C11b.2-5} Hence the data plaquettes are 1 or plaquettes V(∂p) of the stopping-scale field, and |M^·(Q_k^{s*}V)(b) − 1| ≤ max_{b′}|V_{b′} − 1|.
{#C11b.2-6} On 𝔅 the block data has plaquettes within ε_a := g_a/(2B₃) of 1 (VAR (7) with ε_a for VAR's ε₁, not §9's ε₁), ε_a ≤ a₁ for g_a small, so VAR Theorem 1 applies to the local minimisers U_{k,□}(V) of (2.16) and to the global minimiser U_k(V): both lie in the space (8) with ε₀ = B₃ε_a = g_a/2, i.e. |U(∂p) − 1| < (g_a/2)η² for every plaquette of T_η ((2) with j = k, Ω_k = T).
{#C11b.2-7} Hence every test of (2.17) passes (g_a/2 < ε_k = ĝ_kp₀(ĝ_k), as ĝ_k ≥ ρ_γ^{−1/2}g_a with ρ_γ < 4 for γ small and p₀(ĝ_k) ≥ 1, #CP.13, #CP.14, (2.4)), χ_k(T) = 1 on 𝔅; and 1 − Re tr U(∂p) = ½‖1 − U(∂p)‖²_{HS} ≤ ½|U(∂p) − 1|² gives A(U_k(V)) ≤ 6N_s⁴η^{−4}·½(g_a/2)²η⁴ = (3/4)g_a²N_s⁴, so −A(U_k(V))/g_a² ≥ −(3/4)N_s⁴ on 𝔅; and 𝐄_k + 𝐑_k ≥ −C_ℰN_s⁴ by (2.45) and (2.46), with Σ_n|Γ_n| = |Γ_k| = N_s⁴.
{#C11b.2-8} The normalised Haar measure of the ball of radius r ≤ 1 about 1 in G is ≥ (c_Gr)^{dim G} (exponential coordinates), so Haar(𝔅) ≥ (c_Gr_𝔅)^{4N_s⁴dim G}.
{#C11b.2-9} Together, in the normalisation of (a) and for g_a ≤ 1,

{#C11b.3} (11.1) Z_{ℓ₀} ≥ e^{−C_K}, Z_ℓ ≤ M_ℓ := e^{C_K}Π_{X⊂Z(ℓ)}[e·sup 𝐓′_k(X)1·exp(P^c(X))], C_K := C_fsN_s⁴(1 + log g_a^{−1}), C_fs := 1 + C_∂ + C_ℰ + 4 dim G·(1 + log₊(8B₃C_av/c_G)),

{#C11b.4} C_fs a constant of d, L, G, and the constants of CRE's Theorems 1–2, independent of K: the price of comparing whole integrals is exponential in the fixed volume N_s⁴ and in nothing else.
{#C11b.4-1} M_ℓ is the term's majorant.

### 11(c) The Sum over Patterns {#CS11c}

{#C11c.1} *Component Factors.* Let X be a component of Z(ℓ), Z′ the new large-field regions merged into it during its history (the Z_{j′}^{(i)} of (1.79), with birth scales j′ ≤ k), and Z″ the components of Z_n inside X at the scales n ≤ k.
{#C11c.1-1} Its history volume is P(X) := Σ_{n≤k}L^d|Z_n ∩ X|_n, which counts at their own scales the layers Γ_{n−1} ⊂ Z_n and the large-field variables of the steps n − 1 → n.
{#C11c.1-2} By (11.4) of (d), κ^tr_k(X) = κ̂_k(X) + G_k(X) + H_k(X), with κ^tr_k(X) the exact exponent of X's factor in (1.79), G_k(X) := ¼γ₀A₁²Σ_{Z′}p₀²(ĝ_{j′})(d′_{j′}(Z′) + 1), H_k(X) := Σ_{n≤k}λ_nΣ_{Z″}M^dR_n^{d+1}d′_n(Z″), λ_n := 1 + 3·2^{d−1}L^dC_λ(1 + log g_n^{−2}), and κ̂_k(X) ≥ 0 satisfying (1.80) with O(1) + λ_n in place of O(1).
{#C11c.1-3} The history volume and the history cost are bounded by H_k(X) and half of G_k(X).
{#C11c.1-4} First, |Z_n ∩ X|_n = (MR_n)^dΣ_{Z″}#cubes_n(Z″), and #cubes_n(Z″) ≤ 3·2^{d−1}d′_n(Z″) when d′_n(Z″) ≠ 0 (LFR II p.384 l.31–32), so the points of Z″ cost (c_n + C_P)L^d|Z″|_n ≤ 3·2^{d−1}L^d(c_n + C_P)M^dR_n^dd′_n(Z″) ≤ λ_nM^dR_n^{d+1}d′_n(Z″) under the first condition of (H), since λ_nR_n ≥ R_n + 3·2^{d−1}L^dC_λ(1 + log g_n^{−2}).
{#C11c.1-5} Second, a component with d′_n(Z″) = 0 has at most 2^d cubes with a common vertex: the linear size is the length of a shortest tree graph in continuous space meeting all the cubes (RG I p.257 l.14–16), and LFR II p.385 l.18 carries the corresponding 2^d.
{#C11c.1-6} Such a component contains no S-image (S adds ten layers, p.384 l.7–8), so by (1.84) it consists of new large-field regions born at the scale n, each with its own gain in (1.79), used here once, at its birth.
{#C11c.1-7} So

{#C11c.2} (11.2) P^c(X) + C_PP(X) ≤ H_k(X) + ½G_k(X) under (H): 3·2^{d−1}L^d(C_ℰ + C_P) ≤ R_n and 2^dL^dM^dR_n^d(c_n + C_P) ≤ ⅛γ₀A₁²p₀²(g_n) for every n ≤ k,

{#C11c.3} with C_P := max(2, 2C_M), C_M the count of §6.2, and the same at every scale j ≤ k for a component Z of Z_j, with P_j(Z), P^c_j(Z), H_j(Z), G_j(Z).
{#C11c.3-1} Both thresholds are of Bałaban's kind ((log g_n^{−2})^r ≤ R_n ≤ 2L(log g_n^{−2})^r by #CP.14, p₀²(g_n) = A₀²(log g_n^{−2})^{2p₀} by (2.4) against R_n^d(1 + log g_n^{−2}), with 2p₀ > rd + 1), and (H) at g_n gives the same at the gain's ĝ_n, as p₀(ĝ_n) ≥ p₀(g_n) (#CP.14).
{#C11c.3-2} Hence, by (1.79) in the form of p.384 l.4–6 with κ^tr, e·sup 𝐓′_k(X)1·exp(P^c(X)) ≤ e·exp(−κ̂_k(X) − C_PP(X) − ½G_k(X) − 2p₀(ĝ_{j(X)})), with 2p₀(ĝ_{j(X)}) ≥ 2p₀(g_a) ≥ (7/4)p₀(g_a), since ĝ_{j(X)} ≤ ĝ_k ≤ g_a for j(X) ≤ k (#CP.13-1, #CP.14; `WILSON_IT1_LARGE_FIELD_DEPTH_2026_10_27.md` #P.1-3-1).
{#C11c.3-3} A surviving component, one failing (i) or (ii) at the stopping scale, has κ̂_k(X) ≥ c₀M^dR_{k+1}^{d+1}d′_{k+1}(S(X)) ≥ ĉ₀#cubes_k(X), the first inequality being the first term of (1.80) for κ̂. The K of (1.80), which is not the cutoff index, is "the smallest positive integer" of p.384 l.15–17, so K ≥ 1 for the components failing (i) or (ii); the domain X of the definition (1.71), the component the 𝐑-operation renormalises, satisfies the assumption of (1.80) "with K=0" (p.387 l.30).
{#C11c.3-4} The constants are c₀ := O(1) + 1 ≤ O(1) + λ_{k+1} and ĉ₀ := c₀M^dR_{k+1}^{d+1}(3·2^{d−1})^{−1}(2L²)^{−d}.
{#C11c.3-4-1} Indeed, S(X) ⊃ X is the cover of X by LMR_{k+1}-cubes of the scale-k lattice, which are the MR_{k+1}-cubes of the scale k + 1, with ten added layers of them (p.384 l.7–8). So it has at least 21^d > 2^d of them, d′_{k+1}(S(X)) ≠ 0 by #C11c.1-5, and p.384 l.31–32 gives #cubes_{k+1}(S(X)) ≤ 3·2^{d−1}d′_{k+1}(S(X)). Such a cube is LMR_{k+1} ≤ L²MR_k scale-k units across (R_{k+1} ≤ LR_k, CRE (2.9), p.256 l.14), so #cubes_{k+1}(S(X)) ≥ L^{−2d}#cubes_k(X) ≥ (2L²)^{−d}#cubes_k(X).
{#C11c.3-5} Under (T2-i) ĉ₀ ≥ log C_d + 2, C_d the constant with at most C_d^n connected unions of n MR-cubes containing a given cube, its factor is ≤ exp(−(3/2)p₀(g_a) − (log C_d + 1)#cubes_k(X))·exp(−C_PP(X) − ½G_k(X)).
{#C11c.3-6} A kept component, one satisfying (i) and (ii) ((1.89)), has #cubes_k(Y) ≤ 100^d and κ̂_k(Y) ≥ 0, and under (T2-ii) p₀(g_a)/4 ≥ (log C_d + 1)100^d + 1 its factor obeys the same bound.
{#C11c.3-7} The spare factors exp(−C_PP(X)) and exp(−½G_k(X)) stay in the summands.

{#C11c.4} *The Sum.* The components of Z(ℓ) are disjoint connected unions of MR_k-cubes of T_a, N_s⁴(MR_k)^{−4} cubes in all (N_s ≥ ℓ_C ≥ MR_k by the prescription of j(C), the continuum note #NWTOA.1 with #CP.14, #CP.14-1), each component in one of the two classes, and the sum over the labels ℓ with a given region and class assignment (the sequences and the 𝐑-labels) is inside (1.79)'s first exponential, hence inside κ̂ (p.383 l.33–34; for the surviving components, p.387 l.36–39).
{#C11c.4-1} (1.79) bounds a supremum over the admissible sequences of a per-sequence expression with the entropy of the sequences inside its O(1); the history factor of a sequence and the weights below are inserted in that expression before the sum.
{#C11c.4-2} So, by (11.1) and the component factors, for every choice of weights 1 ≤ ω(X) ≤ exp(C_PP(X) + ½G_k(X)),

{#C11c.5} (11.3) Σ_{ℓ≠ℓ₀}M_ℓ·Π_{X⊂Z(ℓ)}ω(X) ≤ e^{2C_K}Σ_{m≥1}(s^m/m!)·Z_{ℓ₀} = δ_LF·Z_{ℓ₀}, δ_LF := e^{2C_K}(e^s − 1), s := 2N_s⁴(MR_k)^{−4}e^{−(3/2)p₀(g_a)}Σ_{n≥1}C_d^ne^{−(log C_d + 1)n} ≤ 2N_s⁴(MR_k)^{−4}e^{−(3/2)p₀(g_a)},

{#C11c.6} and in particular, since Z_ℓ ≤ M_ℓ, Σ_{ℓ≠ℓ₀}Z_ℓ ≤ δ_LFZ_{ℓ₀}, so 1 − w_{ℓ₀} ≤ δ_LF and w_{ℓ₀} ≥ (1 + δ_LF)^{−1}.
{#C11c.6-1} §11 is written for run A. The same holds for run B with its stopping coupling g^B_{k+1} in place of g_a (#C3.1-2), and δ_LF denotes the larger of the two values.
{#C11c.6-2} It is bounded uniformly in K, since N_s is fixed and g_a and g^B_{k+1} lie in K-independent windows: the continuum note's #ND.1.2 applies CRE (2.6) between the stopping scale and the pinned last scale, and the two runs have the same distance j(C) between them.

{#C11c.7} *Smallness.* Under (T2-v) 8e^{2C_K}N_s⁴(MR_k)^{−4}e^{−(3/2)p₀(g_a)} ≤ 1, s ≤ ¼e^{−2C_K} ≤ 1 and δ_LF ≤ 2e^{2C_K}s ≤ ½.
{#C11c.7-1} (T2-v) depends on the loop through N_s.
{#C11c.7-2} The prescription of j(C) gives L^{j(C)} ≤ 2^{β₀}L^{q+4}M(log ḡ^{−2})^r for ḡ small, q the continuum note's loop parameter, not §8.4's q (the continuum note #NWTOA.1, with g_min = γ = ḡ under the pin), so N_s⁴ ≤ C_q(log ḡ^{−2})^{4r}, C_q := 2^{4β₀}(T_ph/u)⁴L^{4q+16}M⁴.
{#C11c.7-3} With log g_a^{−1} ≤ log ḡ^{−1} + 1 and log g_a^{−2} ≥ log ḡ^{−2} − 2 log(1 + β₀) (CRE (2.6), the continuum note #ND.1.2), 2C_K ≤ 2C_fsC_q(log ḡ^{−2})^{4r}(2 + log ḡ^{−1}) against (3/2)p₀(g_a) of order (log ḡ^{−2})^{p₀}, so (T2-v) holds for ḡ ≤ ḡ₀(q, T_ph/u) when p₀ > 4r + 1.
{#C11c.7-4} At a fixed ḡ it covers the loops with q ≤ Q(ḡ), Q(ḡ) = ((p₀ − 4r − 1)/4)log_L log ḡ^{−2} − O(1).

### 11(d) The Entropy Condition and Its Half-Rate Version {#CS11d}

{#C11d.1} Bałaban's κ_j(Z) is defined by (1.83) and (1.85) from the factors of (1.79). Each new large-field region Z′ = Z_{j′}^{(i)} brings the gain ½γ₀A₁²p₀²(ĝ_{j′})(d′_{j′}(Z′) + 1) of (1.79)'s second line, at ĝ_{j′} in the tube (#CP.13); (1.85) prints γ₀ where (1.79) has ½γ₀, and the gain available is (1.79)'s.
{#C11d.1-1} Each step n charges the cost O(1)M^dR_n^{d+1}d′_n(Z″) for every component Z″ of Z_n. This is (1.79)'s first exponential, which includes the sum over the admissible sequences (p.383 l.33–34) and the volume factors exp O(1)|Z_j ∩ Ω_j| of the fluctuation integrals (p.383 l.32–33). The terms 2p₀ are rearranged with a nonnegative remainder (p.386 l.40–46).
{#C11d.1-2} In one case Bałaban's definition is not the exponent of the factor: for Z = S(Z₀) with Z₀ satisfying (i), (ii) and a new large field in the preparatory operations, he puts κ_{j+1}(Z) := p₀(ĝ_j) − O(1)M^dR_{j+1}^{d+1}d′_{j+1}(Z), discarding κ_j(Z₀) ≥ 0 (p.385 l.44–47, p.386 l.1–3).
{#C11d.1-3} Let κ^tr_j(Z) be the exact exponent of Z's factor (p.384 l.4–6), given by the same recursion with κ_j(Z₀) kept in that case.
{#C11d.1-4} (1.79) holds with κ^tr in place of κ, since κ^tr is the exact exponent of the product of (1.79)'s factors; κ^tr_j(Z) ≥ κ_j(Z) is what makes Bałaban's form of (1.79) true, with (1.85) read with (1.79)'s ½γ₀.
{#C11d.1-5} The recursion for κ^tr is affine in the gain and the cost constants.
{#C11d.1-6} Let κ̂_j(Z) be defined by the same recursion, κ̂_j(Z₀) kept in the preparatory case, with the gain ¼γ₀A₁²p₀²(ĝ_{j′})(d′_{j′}(Z′) + 1) and the cost (O(1) + λ_n)M^dR_n^{d+1}d′_n(Z″), λ_n of (c).
{#C11d.1-7} Then, for every j ≤ k and every component Z of Z_j,

{#C11d.2} (11.4) κ^tr_j(Z) = κ̂_j(Z) + G_j(Z) + H_j(Z), κ̂_j(Z) ≥ Σ_{n=j+1}^{j+K}(O(1) + λ_n)M^dR_n^{d+1}d′_n(S^{n−j}(Z)) ≥ 0, K as in (1.80),

{#C11d.3} with G_j, H_j as in (c) at the scale j, both summed over Z's whole history.
{#C11d.3-1} The equality is the affine structure: the 2p₀ terms and the preparatory factors p₀(ĝ_j) enter κ^tr and κ̂ alike and cancel in the difference.
{#C11d.3-2} The inequality is Bałaban's proof of (1.80) (pp.384–387) read with the modified constants, by induction on j.
{#C11d.3-3} In the preparatory case κ̂_{j+1}(Z) = κ̂_j(Z₀) + p₀(ĝ_j) − (O(1) + λ_{j+1})M^dR_{j+1}^{d+1}d′_{j+1}(Z) ≥ p₀(ĝ_j) − (O(1) + λ_{j+1})M^dR_{j+1}^{d+1}d′_{j+1}(Z), since κ̂_j(Z₀) ≥ 0 by the induction, and the right side is Bałaban's value with the cost raised by λ_{j+1}.
{#C11d.3-4} The sizes of the gain and of the cost enter only through the condition at p.385 l.33–36 for a new region (there at j = 1; the same inequality at the scale of every new region, with ⅛γ₀ in place of ¼γ₀ and the cost (O(1) + λ_n)M^dR^{d+1} added to its right side), through the small-domain case p.385 l.44–47 and p.386 l.1–3 (p₀(ĝ_j) against (O(1) + λ_{j+1})M^dR_{j+1}^{d+2} times a constant of d, over the R_{j+1} steps of K), and through the last inequality of (1.88) (2(1 + β₀)^{−1}p₀(ĝ_{j+1}) against (O(1) + λ_{j+1})3(100M)^dR_{j+1}^{d+2}).
{#C11d.3-5} The cost constant also enters (1.81), (1.83), (1.87), and the middle step of (1.88), on both sides alike, and the slack goes into the last inequality of (1.88).
{#C11d.3-6} All three conditions hold for ḡ small with p₀ > r(d + 2) + 1, a form of Bałaban's "p₀ large" (p.385 l.37, p.387 l.28), the extra 1 for the logarithm in λ_n: p₀(ĝ_n) ≥ p₀(g_n) = A₀(log g_n^{−2})^{p₀} (#CP.14), against λ_nR_n^{d+2} ≤ C(log g_n^{−2})^{r(d+2)+1} (CRE (2.4); R_n ≤ 2L(log g_n^{−2})^r, #CP.14).
{#C11d.3-7} At j = k, H_k(X) and half of G_k(X) pay the history volume (11.2), the stopping-scale reserve κ̂_k(X) ≥ c₀M^dR_{k+1}^{d+1}d′_{k+1}(S(X)) of a surviving component pays the shape entropy, and ½G_k(X) stays spare ((c)).

## Constants {#CSK}

{#CK.1} E₁, β < 1 (CRE (2.43), Theorem 2); R₁, κ₀ ≥ 11 (CRE (2.44), p.263 l.50 with κ₀ ≥ 7, raised as p.260 allows after (2.31); §10.5, #CP.29-1); E₂ (CRE p.264 l.14–15, the non-logarithmic part of E_k), B_∂ (CRE (2.47), the boundary terms);
{#CK.1-1} the boundary terms' constants of `WILSON_IT1_LARGE_FIELD_DEPTH_2026_10_27.md` §4(e): B₀, B₁ (CRE (2.42), (2.47); not VAR's B₀, B₁ of §9), C_ε (the O(ε_k) of CRE p.277 l.7–9), ε^{*B}_k := 2C_ptC_XC_KPC_εε_k, σ := min(½δκR, (1/16)δ₀RM) (#4.654) with the condition (⋆) σ ≥ (d + 1)log L + 1, C_{wr}, W ≤ 2C_{wr}L^d, W^♯ ≤ 4c_{μN}C_{wr}L^d, C_w ≤ 2L^d, C_w^♯ ≤ 4c_{μN}L^d, μ_N, c_{μN}, N₀^+, C_ov, C_B, C_ℂ, C_ℂ′, C_D (that note's #4.578, #4.592, #4.629-1, #4.638, #4.648–#4.663),
{#CK.1-1-1} C^B_n, C^θ_n := (C^B_n + C_V)C_h, C^B_R, C^B_{R,1} (§8.6), C^N_Σ, C^N_m, C^N_μ, C_N′ (#C8.7.3-11), C_∗ and C_μ := θ̃^{−1}max(1, 1/(e log(1/θ̃))), a constant of θ̃ alone (§8.7); E₀, κ (RG I (1.18));
{#CK.1-2} α_{0,j}, α_{1,j} (CRE (2.28), the class U^c_j, with the integers q₁ ≥ q₀ > p₀ + 3r, bounded below only, the large-field note's choice (its #4.420-1.1 and #4.480), which contains the q₀ > p₀ + r used at the ε₁ of (T-Λ), §5); α′_{i,j} := α_{i,j}/(4B₃) (the common polydisc 𝒫_j(X; α′) of §5) and r_{i,j} := α′_{i,j}/2 (the norm class 𝒫_j(X; r) and the class 𝒞_k of §5 and §8.2), with CRE's C₀ and C₁ of (2.28) at least λ_Q := max{1, 4B₃, 8B₃, 2^{13}B₃²L³, 64B₃C_{Q*}, C_mem} (C_mem of the LF note's *The conditions.*, a constant of d and L) times Bałaban's lower bounds;
{#CK.1-3} C_{Q*} := 2(1 + (2d + 1)L^{d−1}) (the bound of the lifted current, §5 *Complex domain*); σ̂_{k,j} := σ_k + C(ε₀)ρ_k + C(ε₀, δ₀M₁)ε₁e^{−δ₀M₁L^j/2}, C(ε₀, δ₀M₁) := 2C(ε₀)/(eδ₀M₁), C_σ̂ := C(ε₀)(1 + C_G(ε₀)) + C(ε₀, δ₀M₁) (the distance of the pair line, §5 and #C9.8.17-5); C_J := 2x_J + 1 under (16dc_br + 2c_Dc_v)L^{d−1}B_λε₁ ≤ 1, and B′_λ := 2B_λ + x_J(C_G(ε₀) + 1) (the current along the pair line and the lift's current, §5);
{#CK.1-4} C_Π(j) := C′_Π(8B₃/α_{2,j})², C′_Π := O(1)C″_Π, C″_Π (the moment defect of the localised lift, with C_Π(j)ε₁² ≤ max(1, k − j), §5), C′_{β′} := sup_{m≥0}max(1, m)L^{−β′m/4} (the j-sum of (5.1v)); β_C := 1/8 (CRE's class constant of (2.34)–(2.39), p.261 l.42); α₂, α₃ (RG I (3.31), p.280: B₃α₃ < ½α₁, 2B₃α₃ ≤ βL^{−2}α₀, at the radii r; α_{3,j} below, with 2B₃⁺α_{3,j} ≤ β_IL^{−2}α_{0,j}/C_{Q*});
{#CK.1-5} C_fl := 4B_Te^{2·6^dκ₁} (RG II p.6 l.41, the bound 4B₀e^{16κ₁}|B′| of the fluctuation part 𝐇_k(s(Y₀), B′) of (I.3.28), the same in all admissible norms by (1.21), p.7 l.3–11, these being the norms of Theorems 3.1–3.10 [13], p.5 l.16, read with B_T and 2·6^d, §8.2), c_N := (128B₃²C₁₃C_{Q*}O(1))^{−1} (the bound on c₂ under which the points (N) and (R3) lie in the norm class, #C5.8),
{#CK.1-6} ℰ_j(X; r) (the evaluation set of the norm d_j, the union of the G^c-orbits of its literal points of the kinds (R1) and (R2), literal class configurations at the radii r⁺ that are minimisers or local minimisers in a G^c-valued gauge, (N), and (R3), the shifts exp iη𝐀𝐔′ of the former with a current increment, #C5.8; Δ is constant on the orbits, #C9.8.18-5; §8.2 maps ℰ_{k+1} into ℰ_j),
{#CK.1-7} C₁₃ ≥ 1 (the O(1) of the moves of (I.3.13), the lower-order terms of the true current included, #C5.36, §8.2), B₅ (VAR (173), p.305 l.39–42, the constant of Proposition 9's bounds (19)–(21) on the minimiser's move, #C5.8), c_m := c₂C₀/(32B₃C_flC₁₃C_{Q*}), C₀ of CRE (2.28); ϑ_k := (A₁/A₀)ε_k (Bałaban's threshold δ_k, CRE p.265 l.39, renamed to keep δ_k for the coupling difference);
{#CK.1-8} m_k := c₂r_{0,k}/(8C_flC₁₃C_{Q*}) = ½c_mĝ_k(log ĝ_k^{−2})^{q₀} (the margin of §8.2), T₀ := m_k/(‖C‖_∞ϑ_k) ≥ 2 (the cutoff ball (3.16) inside the margin), C_T := (1 − 1/T₀)^{−1}, C_T′ := (9/2)(1 − 3/(2T₀))^{−2}, C_X := sup_xΣ_{Y∋x}exp(−(β/16)κd_k(Y)) (the domain count of §8.5 at a point), C_pt(M, L, β, κ) (§8.5, the points of X and the factors abs(Y)), C_G″ := (1 + 1/α₄^G) times the constant of Bałaban's bound of the Gaussian terms (the Gaussian part of §8.5), α₄^G (§8.5, the radius parameter of the Cauchy circle, RG II's α₄ of (2.18) in this role, small against α₅'s condition of RG II (2.24)),
{#CK.1-9} C_cov (the covariance bound of §6.2 and §8.2(b), not C_G(ε₀) of (9.8)), r^χ_k := ϑ_k/g_k = (A₁/A₀)p₀(ĝ_k)ĝ_k/g_k (the cutoff radius of (3.16)), ‖C‖_∞ and ‖C‖_1 (the row-sum and column-sum norms of C, §8.2 and §10.5), μ_k := (‖C‖_∞ϑ_k/m_k)² ≤ 4‖C‖_∞²(A₁/c_m)²(log ĝ_k^{−2})^{−2(min(q₀,q₁)−p₀)}, a_k := g_kP_a(log g_k^{−2}) (CRE p.278 l.32–35, the fluctuation-domain weight), E₁(α) := C_αE₀ and E^𝐀_1(α) := C^𝐀_αE₀, C^𝐀_α := 6⁵C_α ((5.1c𝐀), the constant of §8.2's b^c_j), C_α := O(1)L^{4+β′}C_{β′}[C_r⁵ + C_loc + (C_{WT} + c₂^{−2})(1+ρ̄)⁴ + 1],
{#CK.1-10} C_loc (the localisation remainder, §5 *The constant.*), C_r := O(1)B₃B₃⁺LML²β_I^{−1}(1+β₀)²C_{Q*}, C_{β′} := sup_{m≥0}max(1, m)^{5/2}L^{−β′m}, ρ̄ := O(1)B₃²LM(1+β₀)²/c₂, α_{2,m} := c₂α_{0,m}, α_{3,j} := β_IL^{−2}α_{0,j}/(2B₃⁺C_{Q*}) (the factor 1/C_{Q*} for the reduced current threshold; B₃⁺ of #C5.37-18),
{#CK.1-11} C_{WT} Bałaban's equal-scale constants of RG I Sect. 4, β_I := 2^{−7} RG I's class parameter (#C5.26), β_H ≥ 19/20 the Hölder index and β_E ≤ 1/20 the exponent of (3.67), θ_V := β′/(2(4+β′)), E_V := (2E₁(α))^{1−θ_V}(C_X(C_σ + 16C_J + 2496C₀²)E₀ + C_A′β̄)^{θ_V}, C_σ absolute, C_A, C_A′ := C_A + 16C_b + 768C₀² (the action part of the variation group, §5), β̄ := sup_j|β^B_j| ≤ b′ + C (BETA_FUNCTION_WILSON_LOOPS.md (W) at n = m + 1, §2), m(k) := ⌊(1 − 2ε₀)k/12⌋, C′_R and C″_R (the 𝐑-terms' variation at the young and the old ages of a step, §10.5),
{#CK.1-12} q₀ ≤ q₁ and CRE's C₁ > 2B₃²O(1)MC₀ (CRE's C₀; #C5.36; the class bound (5.1c) of RΔ^c on 𝒮_z and the variation-group bound (5.1v), §5 *The constant.*, used in §8.2 and §10.5); C_KP, κ′, C_G″ (RMark, §8.5: Bałaban's constants for the expansion of the insertion (3.37), and the complex-background Gaussian mean);
{#CK.1-13} ε_k^* := C_XC_ptC_KPL⁴C^𝐀_α[C_Tμ_k + 4a_k], ε^*(g), its bound at the coupling g (#CP.22-1, #C8.3.3-2), ε^* := ε^*_γ := sup_{g≤(1+β₀)γ}ε^*(g), ε̂^*(g) := sup_{g′≤2g}ε^*(g′), γ := sup_Kg_K ((T1)), β′ := ½min(β_H, 1 − β_E) ≥ 19/40 (§5), θ := L^{−β′} + ε^*, θ̃ := max((1 + θ)/2, L^{−γ_H}, L^{−(1−2ε₀)/3}, L^{−(1−ε₀)/4}, L^{−θ_V/8}), C_g := (1 − L^{−β′})^{−1}max(C_T′/(2C_T), 1), C_β (§8.2–8.3);
{#CK.1-14} N′_k := k − k₁ ≤ N′(ĝ_k), N′(g) := log_L(MR(g)) + 3 (the memory of 𝐑″, R(g) of #C8.4.1-10), b₂ := b′ + C_W (Bałaban's coefficient β′ of CRE (2.6) in the tube, #CP.14, renamed since β′ is the age exponent of §5), c_j := C_R(100MR_j)^dg_j^{κ₀}, c′_j := C_KP(2R₁/E₀)N′_jg_j^{κ₀}ε_j^*, c^B_j := C^B_R(100MR_j)^dg_j^{κ₀}, c^V_j := C^V_R(100MR_j)^dg_j^{κ₀}, 𝒟^∗_j (the boundary terms' source of `WILSON_IT1_LARGE_FIELD_DEPTH_2026_10_27.md` §4(e)), 𝒟^{∗′}_j[u] (§8.7),
{#CK.1-14-1} c^S_j := 2c_j + 2c^B_j + 2c^V_j + 2c′_j (#C8.4.3-4), C_Σ := sup_KΣ_{j≤K}(c_j + c^B_j + c^V_j + c′_j), C_S := 2exp(2C_Σ), C_S″, 𝒟_m := D^♭_m + S_{m−1} + C|δ_m| + e_m + h_m, D^♭_m := Σ_{i≤m}q^{m−i}d_i ≥ D_m, q := L^{−1/3}e^{−1/12}, D^♭_m[u] (§8.7),
{#CK.1-15} h_m := C_hθ̃^m (the input (LF) bounds its ingredients by h_n per point of a history born at the scale n > k_s/8), 𝒟′_{[j]} (§8.4, (8.5)); p_m(Z), C_ψ (the per-point constant of the denominators' run-dependence, from LFR II (1.6), (1.9)–(1.11), p.357 l.9–10, p.358 l.23–33), e^{−c(M)} and C_d(M) (the complex version of the denominator's comparison, `WILSON_IT1_LARGE_FIELD_DEPTH_2026_10_27.md` #4.155-1–#4.155-2), C_n := 2(1 + L^d + 3^d)(4 + C_ψ + C_β) (with the collar points and the coupling part of W_ext), q̄^A, q̄^B (Bałaban's majorants of the two runs' quotients, LFR II p.389 l.13–16),
{#CK.1-16} R₁′ (the constant of (2.31) under the modified condition of p.389 l.16), C_R := 2(e + 1)C_nL⁴R₁′, ν_j, C_ν (the fine-scale and old-history 𝐑-bounds, Σ_{j≤K}ν_j ≤ C_νw_K, C_ν = C_ν(j(C)) at most L^{Cε₀j(C)} times a polynomial in j(C), through C_h), Σ_g := sup_KΣ_{j≤K}(100MR_j)^dg_j^{κ₀}, k̄ := max(k_s, j), Ē₀ := max(E₀, B₀, C₀^𝔹, R₁) (the deep terms, #C8.6.2-10), C_V := 2O(1)(1 + L^d + 3^d) (the collar count of V(Z^∼), LFR II (1.69)), 𝒟^V_j, C^B_V := 2(C_B + C_ℂ′ + C_ℂ), C^V_R := 2L⁴R₁′ (the old terms' own differences in the V(Y)), 𝒟_{[j]} := max_{k_s/8−1<m≤j}e^{−½C_P(j−m)}𝒟_m (§8.6, (8.4));
{#CK.1-17} 𝒟^{V′}_j, 𝒟^{V′}_j[u] (§8.4, §8.7); C_e, C_e′ (§10.5, the depth source; C_e ≥ 2L^{k₀(ε₀)} for the first steps, #C8.3.3-8); ℓ_K := (log(bK + ḡ^{−2}))^{rd+2p₀}, μ_K := K^{2−κ₀/2}ℓ_K, k_s := K − j(C), w_K := (K + 1)(θ̃^{k_s/8} + 2^{−k_s/16}) + μ_K, m_i := iθ̃^i + w_K, 𝒯, D_i[u], 𝒟′_{[j]}[u], C_m := C_Σ + C″_μ, C″_μ, C′_m, C_τ, C_s, C_a (§8.7; C_a depends on j(C) at most as L^{Cε₀j(C)} times a polynomial); b, C (BETA_FUNCTION_WILSON_LOOPS.md Lemma 2.1(i)); a^{(U)}_K := 2e^{−C_P(K−j(C))} (§6.1), K₀(L, δ₀M₁, j(C)) (§5, #C5.101-2), K₁ (§7, #C7.4-7);
{#CK.1-18} C_M (the count of run-dependent ingredients per point of a history), C_δΔ := C(ε₀, γ_H)max(1, ε₁/α_*) (the covariance item), s′_K, s^{LF}_K := C_hθ̃^{k/2} (the input (LF) at the young scales), s_K := s′_K + L^ds^{LF}_K, φ′_X, φ_X, ω(X) and ω^s(X) (the weights of (11.3), #C6.2.2-1, #C6.2.13), M^A_τ, s^{W,tot}_K (the large-field dressings of the loop, the LF note's §5(f)),
{#CK.1-18-1} k_*(j(C), ḡ) (the threshold of §6.2, #C6.2.19), X_K and x_K := e^{X_K} − 1 (the bound (7.1), #C7.3, of the all-small-field pair and of the young pairs on Λ_k), σ̂^Λ_{k,j}, C_{yd} := C^{LF}(ε₀)C_U(M) with C^{LF}(ε₀) the large-field note's #D.C(ε₀) (#C6.2.18-7), X^{cl,0}_K and C_w(ε₀) (the large-field note's #4.42; #C7.4);
{#CK.1-19} 𝒜_ℓ, Z_ℓ, w_ℓ, E^ℓ, C_λ (the localised logarithmic constants, at most C_λ(1 + log g_n^{−2}) per scale-n point of a history, CRE p.262 l.16–18, LFR II p.378 l.2, p.380 l.24–26), C_∂ ≤ 1 (the exterior couplings, #C11b.1-2) (§11(a)); C_ℰ := E₁(1 − L^{−β})^{−1} + 1 + 2B_∂, c_n := C_ℰ + C_λ(1 + log g_n^{−2}), P^c(X) (the history cost), C_av = 1, c_G, r_𝔅 := g_a/(8B₃C_av), 𝔅, C_fs := 1 + C_∂ + C_ℰ + 4 dim G·(1 + log₊(8B₃C_av/c_G)), C_K := C_fsN_s⁴(1 + log g_a^{−1}), M_ℓ (the term's majorant (11.1)) (§11(b), (11.1)); γ₀, A₀, A₁, p₀ > r(d + 2) + 1 (LFR II (1.79), (1.82), p.385 l.37; CRE p.246 l.14),
{#CK.1-20} p₁, ν, r₀ (LFR I p.183 l.2, p.198 l.55–56, LFR II p.383 l.28; p₀ ≥ (d+5)r₀ + ν + 4), δ′_j := ĝ_jA₁p₁(ĝ_j) (LFR I p.183 l.2 at ĝ_j, #CP.13), λ_n := 1 + 3·2^{d−1}L^dC_λ(1 + log g_n^{−2}), c₀ := O(1) + 1 (the constant of (1.80) for κ̂), κ^tr_j, κ̂_j, G_j, H_j (§11(d), (11.4)); P(X), P_j(Z) (the history volume), C_P := max(2, 2C_M) (§11(c), (11.2));
{#CK.1-21} ĉ₀ := c₀M^dR_{k+1}^{d+1}(3·2^{d−1})^{−1}(2L²)^{−d}, C_d, s (the pattern sum of (11.3), ≤ 2N_s⁴(MR_k)^{−4}e^{−(3/2)p₀(g_a)}), δ_LF := e^{2C_K}(e^s − 1), the larger of the two runs' values, C_q := 2^{4β₀}(T_ph/u)⁴L^{4q+16}M⁴, ḡ₀(q, T_ph/u), Q(ḡ) (§11(c), (11.3)); B_W (continuum note (8.1)); N = N^T_k, R_j = R^T_j (#CP.13–#CP.14); N_s⁴ = |T_a|; ε_k := ĝ_kp₀(ĝ_k) ≤ g_kp₀(g_k) (CRE (2.4) at ĝ_k; #B2.2.271); ε_V ≤ C_{(3.12)}ε_k (CRE (3.12)), ε₁ := 2C₀ε_V ≤ C_{ε₁}ε_k, C_{ε₁} := 2C₀C_{(3.12)} (§9), a₁, a₁^{(M_P)} (a₁ taken at M_P, §9), B₃, B₄(β₀), R₁M₁, M(ε₁) (VAR Theorem 1 and (7));
{#CK.1-22} B₀′(ε₀), δ₀ (the smaller of the rate of PBG (3.42), (3.44) and 1/16 of the rate ⅛δ₀^{VAR} of VAR (190), #C9.8.15-3; a smaller δ₀ only weakens each e^{−δ₀d} bound, and the conditions on M that contain it are met by M large); C₀ := c₁₁C₀^{VAR}, C₀^{VAR} := 4R₁M₁(B₃ + B₄(1)), c₁₁ := 3(1 + 4c_9) (§9's field constant, (9.2), used in 32C₀², 192C₀², 768C₀², and 2496C₀² of §5; not the C₀ of CRE (2.28)), C_b := 48c_9²C₀², C_r := 8c_9C₀(1 + C₀) (§9's, (9.4) and (9.5); not the C_r of §5),
{#CK.1-23} C₁ := 2C₀/B₃ (VAR's C₁ of (14) for §9.4, #C9.4), VAR's C₁ of (172) (Sect. G's, #CP.27), C₁^{(123)} (the constant of CMP 98 (123), #C10.3.34), C_ℒ, 𝒦_Γ, 𝒦_L, C_𝒦 (the curl terms of the plain lift, §9.4), C_{pl} := 3(1 + 2d^{3/2}L^{(d+1)/2}), m_Q^{pl} := C_{pl}^{−2}, T^{pl} := Q₁^{pl}Q₁^{pl}*, r_T^{pl}, M̃_Q^{pl}, R_Q^{pl}, C_E^{pl}, C_ax^{pl}, q^{pl} := 1 − m_Q^{pl}/(2M̃_Q^{pl}), δ_Q^{pl} := (r_T^{pl})^{−1}log(1/q^{pl}) (the plain lift's Gram operator, §9.4), c_𝒦 (§9.5), C_G(ε₀) := 4c_𝒦C_r(B₀ + B₀′(ε₀)), ρ, C_gap(ε₀), k₀(ε₀) (§9);
{#CK.1-24} c_δ := sup_yΣ_{y′}e^{−δ₀d(y,y′)}, c_{δ₂} := sup_yΣ_{y′}e^{−δ₂d(y,y′)} (§10.5, the rate δ₂ = min(δ₁′, ½δ₁) of (10.6)), C_L (#C9.8.14-2, the path-length constant of the averaging), C_F, C_ι := O(1)L²C_LC_F (#C9.8.14-3-1, #C9.8.15-3, the field strength of ι and the localised lift's tail), a := εL^k and a_j := εL^j (#C5.52-1; the scale-k unit is written a, a_k being #CK.1-9's), ρ_j, σ_j (§9.7);
{#CK.1-25} δ₁, δ₂, γ_H (the Hölder exponent of PBG (3.133) and (3.43), any 0 < γ_H < 1 in (10.6a) and (10.6b), 0 < γ_H < ½ in (10.6)), B₀(γ_H), C_δ, C_β(γ_H), 𝔰, h_H(γ), h_H, C_tr, c₁₂₄ (the O(1) of CMP 98 (126), for the non-main terms of (124)), δ_T, ν_F, c_δ′, B_G, B_G(γ_H), τ̂, c_𝔠, c_f, c_{g1}–c_{g7}, C_gf(γ_H), C_ld (the bond load of (10.6c)), C_{5L} (§10.4, (10.6c));
{#CK.1-26} Φ_p, F^w_p, r_p (the remainder of the coarse curvature), η = ε/L, r_G, 𝒫, m_G (the polydisc of *Analyticity.* and the sup of the curvatures on it), 𝔞 (the axial-gauge field, U^B = e^{iη𝔞}), the condition 16dC₀ε₁ ≤ r_G, k₂, c_{r1}, c_{r3}, c_κ (the quartic part of the Wilson density), k_l (the constant of |dlog_h − 1| ≤ k_l|log h|), c_{br}, k_o, k_F, k_Φ, k_Φ″, k_ν (*The Bounds.*, (10.6a));
{#CK.1-27} Q^{str} (the main term (125) of CMP 98 (124)), Q₁^{pl} (the plain averaging), T_Q and r_T (the Gram operator Q₁Q₁* and its range), M̃_Q, C_χ, R_Q (fixed by C_E/R_Q² ≤ m_Q/4), C_E, C_ax, q_T, δ_Q, C_Q, the conditions C_ax·d(R_Q + 3)C₀ε₁ ≤ m_Q/4 and δ₁ ≤ min(δ_Q, 1/(10d)), C_I, C_ℒ′(γ), C_ℒ′ (*Regularity of the Lifts.*), C_β^ℒ, C_gf^ℒ, m_Q (the lower spectral bound of Q₁Q₁* at U^B = 1), r_β, C(ε₀, γ_H), r_j (§10);
{#CK.1-28} Q_n^{pl}, v_n, Θ_n, M̄_U, Q̄₁, C̄₁^{(2)}, c, c̄, q_n (§10.1, the bridge (B1)–(B5) between the plain and the double-bar averagings); 𝒬, 𝒬′ (the last-step field averaging), V_U, w, V^w, U^A_ax, c_w, θ_i, c_B, r_{BCH} (the BCH bound), 𝒟_j, α_J, δ₁′, B₀^{cx}, M₃, a_cx (BP_PBG_COMPLEX.md), C_𝐆, c_{GM}, r_P, T_c, e_c, C_𝐉, c_W, c_e, x_λ, B_λ, κ_W, c_{av}, c_Q, c_v, k_G, c_D, C′_Q, x_J, J′_j, R_𝒟 (§10.3); α_* (§10.4); G₁^Q (§10.4, the Green operator on ker Q at run A's pair);
{#CK.1-29} κ_s := β/30 = 1/240 (the width of the soft tests, at LFR I's test constant β = 1/8), δ^s_j, b^{(S)}_K (`WILSON_IT1_LARGE_FIELD_DEPTH_2026_10_27.md` §3(d), the soft tests);
{#CK.1-30} f^A_k and E^A_const (#C1.2-3, #C1.2-4), λ_K and C_Y (#C7.5), C^E_Σ and B_E (#C1.2-4), a_E, A_E, a^T_E, b^R_E, R^E, A^{TZ}_E, A^R_E, C^T_E, c^T_E, C̄_Z, c^Z, C^R_E, c^R_E, ι_T^{stop}, m^E_K, τ^E_K, r^E_i, C^E_r, Δ^E_K, S_E, ΔE_K, F^{B,A} (#C7.6), b^{(M)}_K := 3e^{−C_P⌊k/2⌋} + 5s_K + 3x_K + s^{W,tot}_K for k ≥ k_*(j(C), ḡ) and 4 below (§6.2);
{#CK.1-31} C₂, C₄, B₀, B₁, a₃, a₄ (VAR (46), (49), (97), (117)–(121); VAR's B₀ is introduced at (46) from "the Theorem 3.12 from [5]" (p.285 l.25–27), so it is PBG's B₀, the common constant of PBG's operators (PBG p.423 l.39–40), the one that §9.5 and (10.6) use; this B₀, B₁ not CRE's of the boundary terms above);
{#CK.1-32} E°^T_i, E°^R_i, ĉ₁ (D2.7 15.4(i)), b(X), b̄, M̄(X), n(X), N^{pt} := 2·3^dM^d, r^V_K, C_θ, κ_I := κ/6, a_{Ew} := min(a_E, a_w), r̄^E_K, ρ^E_{K,0} := max(r̄^E_K, r^V_K, 3(1 + eC_MN^{pt})s_K), ρ^E_K (#C7.6-6-4-4), ς and x^ς (the interpolation, not Bałaban's t(Y) or his large-field functions ζ, ζ₁, and not the large-field note's local ς₁, ς₂), 𝔷 (the Cauchy parameter on the activities, #C7.6-6-3 and #C8.2.2-85, not Bałaban's normalisation z of LFR I (1.6), the point z of 𝐄(X, ·, z) and 𝒮_z, or Bałaban's large-field functions ζ);
{#CK.1-32-1} RG II's α₆, ε₁, and ε₂ = 2E₀ε₁C₁α₄^{−1}α₆^{−1}M^qe^{C₂κ₁} (RG II p.19, with RG II's own C₁, C₂, and q, not #CK.1-23's C₁, #CK.1-31's C₂, or the note's q; α₆ halved and this ε₁, not those of VAR, §9 (#C9.1), or the large-field note, quartered, #C7.6-6-6-1 to #C7.6-6-6-1-2), C^{T,2}_E, C̄^{(2)}_Z, C^{R,2}_E, c^{T,2}_E, c^{Z,2}, A^{E,2}, a^{E,2}, S^{(2)}_E (the young part of the loop constant, #C7.6-6-1 to #C7.6-7-2);
{#CK.1-32-2} C^w_M, c^w_M, c^w_N, A_w, a_w, m^w_K, τ^w_K, S_w, C^{w,2}_M, c^{w,2}_M, A^{w,2}, a^{w,2}, S^{(2)}_w, D^w_K, x^w_K (the wrap insertions, #C7.8, #C7.8-8-1); q^Q_K, q̄^Q_K, b^{wr}, B̄_W, x^Q_K (the final interaction weights, #C7.9); d^{ins}_i, D^{ins}_i (the marked activities, #C8.3.3-4-1), C_{ins}, C^*_{ins} := max(C_{ins}, 2/θ̃) (#C8.7.7-2); ε^Q(g), ε^Q_i (the old vertices' coefficient, #C8.3.3-4-3-2-1); ε₁^{LF} (the large-field note's ε₁, not §9's ε₁, #CP.27) and c^{LF}_{ε₁} (#C6.2.18-7-1).
{#CK.1-33} The wraps in the step gases (#C7.8-1–#C7.8-1-4-1, #C7.8-9–#C7.8-9-10): w(W), ρ̂^w_j, C_ε̂, C_pos, Δ_i, τ^{pt}_i, τ^{pt}_K, Ȳ, δε̂^w_i, X_w, T_w(a), ρ̂^w_γ, μ₀, μ^{pt}, the t-step and its radii R_w and R_E, c″ := 10368M/ν_r, ρ̃, s^w, Δ̄₀₀, G_w, y^*_K, x^*_K, r^w_K, a₀ (#CP.22-5-1), and θ_Q (#C8.7.7-4). The t of the t-step is not §8.1's interpolation t of #C8.1.1-3.

## Sources Read {#CSR}

{#CR.1} CRE (CMP 119): p.246 l.8–20 (p₀ ≥ 5r with A₀ large), l.40–44 ((1.3)); pp.255–264 ((2.1)–(2.50), Theorems 1–2, Corollary 3; in particular p.255 l.31–60 ((2.4)–(2.7)), p.256 l.1–40 ((2.8)–(2.10)), p.257 l.20–47 ((2.16)–(2.18)), p.258 ((2.19)–(2.23)), p.255 l.1–12 (ζ and χ of the general domains), p.259 l.1–50 ((2.24)–(2.28)), p.262 l.14–36 (l.16–18, the constant E_k), p.263 (Theorem 2, (2.43)–(2.46); l.50, κ₀ ≥ 7), p.264 l.1–33 ((2.47)–(2.50), the proof of Corollary 3)); pp.265–269 ((3.1)–(3.22); p.267 l.44–52, p.268 l.1–8); pp.266–268 ((3.9)–(3.16), the display (3.15) with its Gaussian form);
{#CR.1-1} p.270 l.22–51, p.271 l.1–30 ((3.26), the memory of 𝐑″); pp.274–276 ((3.36)–(3.43), the definition (3.37) of 𝐄_0^{(k+1)} by t-interpolated insertions and the measures (3.27), (3.29); p.276 l.18–40); pp.277–283 ((3.44)–(3.67), the proof of Theorem 2; p.279 l.8–26; p.280 l.1–20, (3.48)).
{#CR.1-2} RG I (CMP 109): p.257 l.12–18 (the linear size), pp.260–264 ((1.1)–(1.22), the Definition of U^c_j), p.267 l.22–40 ((2.11), the identification of the step's quadratic form with PBG (3.156)); the transcription pages 276 ((3.28)–(3.31)), 278 ((3.38)–(3.43), the space U′^c_{k+1}(□₀, (1 + 2β)α₀, (1 + 2β)α₁)), and 280 (the restrictions on α₃, (3.51)–(3.52), Lemma 4 (3.53), (3.54)); p.281 l.1–3, pp.283–284 ((4.13)–(4.15)).
{#CR.1-3} VAR (CMP 102): pp.277–281 ((2)–(17); the spaces (2), (6)–(8), the regularity (7), Theorem 1 with (9)–(10), §A, Proposition 2), pp.285–287 ((46)–(49), the bounds on D and HD), pp.290–296 ((81)–(84), Proposition 4, (99)–(121), Propositions 5–6; p.293 l.22–26), p.299 (Proposition 7), p.300 (§F, l.22–50), p.309 (references).
{#CR.1-4} PBG (CMP 99): p.392 l.2 (the normalised trace), p.393 l.46–p.394 l.2 and p.394 l.9–11 (Q′ and R), pp.396–399 ((3.35), (3.36), (3.42)–(3.47), Theorem 3.3), pp.400–407 (Theorem 3.4 and its proof), pp.415–416 (Theorems 3.10, 3.11), p.418 ((3.113)–(3.116)), pp.421–423 ((3.129), (3.132), (3.133), Theorem 3.12, (3.139)–(3.140)), pp.425–428 ((3.148), (3.153), Theorems 3.13, 3.14, (3.155)–(3.158)), p.416 ((3.107)–(3.108), the walk expansion of the Green operator).
{#CR.1-5} CMP 98: pp.17–20 ((1)–(17), the averaging (14), (15)).
{#CR.1-6} PRT1: pp.18–19 ((1.6)–(1.14), the contours Γ_{y,x} and the averaging (1.8)).
{#CR.1-7} LFR I (CMP 122): pp.176–178 ((0.2)–(0.6), conditions (i)–(ii), (1.1); p.176 l.14–30, p.177, p.178 l.1–40), p.185 l.11–20, p.188 l.27–37, p.189 l.29–49, pp.190–191 (the spaces Ũ^{(n)c}_k, (1.65)–(1.69), p.191 l.37–52, p.192 l.1–13 ((1.70), the exception for 𝔹_k^{(n)} and its cumulation), p.182 l.53 and p.183 l.2 (χ′_j, δ′_j, p₁ < p₀), p.196 l.40 (χ′), p.198 l.48–60 ((1.94), ν).
{#CR.1-8} LFR II (CMP 122): pp.356–359 ((1.1)–(1.12), the renormalisation denominator, the bound of V on p.357 l.9–10, the positivity (1.9), the boundedness of the form on p.358 l.23–24, (1.10)–(1.11)), p.360 l.36–50 ((1.18)–(1.19), the cutoff χ′), p.362 l.40–60 and p.363 l.1–25 ((1.26)–(1.29), the walk expansion of H″), pp.368–370 ((1.46)–(1.54), the configurations U″_{h+2} and U″_k = U_{𝐁″_k}), p.377 ((1.68)–(1.70), the completion), p.378 (the decompositions of unity after (1.70), the new 𝐓′_k), p.389 l.13–16 (the product over h).
{#CR.1-9} LFR II, continued: p.380 l.15–47 (the constants inside 𝐓′, the large-field functions χ^c_j(P_j), χ′^c_j(Q_j), χ^{(j−1)c}(R_j)), p.381 l.6, p.392 (references [13], [15]), pp.383–389 ((1.77)–(1.97); p.383 l.24–48 ((1.79)), p.384 ((1.80), the operation S, d′ and the covers), p.385 ((1.81)–(1.83), l.15–20, the preparatory case l.44–47), p.386 ((1.84)–(1.86), l.1–3), p.387 ((1.87)–(1.89), l.24–42)).
{#CR.1-10} BETA_FUNCTION_WILSON_LOOPS.md §2 (Lemma 2.1 and its hypothesis (W); the tube construction, #B2.2.165–#B2.2.180; Lemma 2.10; Propositions 2.11–2.13).
{#CR.1-11} WILSON_IT1_LARGE_FIELD_DEPTH_2026_10_27.md (§1, VAR's (7) on every term; §2(b), the radial shells and the three-piece split; §3(d), the soft tests).
{#CR.1-12} WILSON_IT1_CONTINUUM_LIMIT_CLOSURE_2026_10_26.md #NWTOA.1, #ND.1.1, and #ND.1.2 (the prescription of j(C), the coupling window), and (7.1)–(7.4), (8.2)–(9.4), and Constants.
{#CR.1-13} V4 sec:c5-5R (lem:c5-5R-1, lem:c5-5R-2), and sec:c3-9-1 (prop:c3-9-1, eq:c3-9-4).
{#CR.1-14} Map #MWTCI.8, #MD2.0.3.4, #MD2.3.4.18, and #MD2.4.6.14.
