# LIP-1 repair (a): RG1's fixed constants with CRE's fluctuation cutoff

Written 21 Oct 2026, from 18:37 (user: "Continue with Lip 1(a)"). Companion to `WILSON_CAUCHY_LIPSCHITZ_2026_10_21.md` (the Lipschitz note, §5) and `V3_RG1_FIXED_CONSTANTS_CHECK_2026_10_21.md` (the check note). Bałaban is cited by printed page and equation, checked on the transcriptions in `Balaban\tex\<paper>\parts`. Bałaban-project files are cited by name and are not edited.

## OPEN MATHEMATICAL GAPS

- **H-2b: (B1)(iii) at the hybrid thresholds.** "U₁ lies in the domain of integration" (CRE p.248) is CRE's statement at CRE's thresholds.
  - *What is missing.* With Lemma H-2a it reduces to at least three statements (§4.3):
    - (f) at the boundary cubes □' ⊂ Ω₁ \ Ω₁^{∼−1}: |U₁U_{1,□'}⁻¹ − 1| < 2δ₀ on (□'^{∼2})^* ∩ Ω₁. This is a sup-norm contraction for the boundary response of (1.12). CRE does not prove it and keeps these tests as cutoffs on A (p.250);
    - H-2b(loc): definedness at U₁, through a localised VAR problem near Ω₁ and the identification of its minimiser with CRE's U₁ by (B1)'s uniqueness clause;
    - H-2b(ζ): the χ₀′ tests of cubes of Ω₁^c whose carriers reach into Ω₁, unless they are shown not to be booked in ζ(Ω₁^c).
  - *What closes it.* Proofs of the three; or, for (f), the weaker (f′), ≤ C_bδ₀, from VAR Proposition 9 and (190), which needs a common VAR problem, a localisation and a gauge conversion (§4.3), together with a V3 change at its six uses of U₁ ∈ D^{(11)} (V3 L269, L300, L309, L313, L3740, L4291/L4388).
  - *What waits on it.* (B1)(iii), and through it (B2), (B4)(i)–(iii) (§4.2). These are reduced to H-2b, not passed.
- **Join to RG1's domains (part of R-S1(d) and R-N4).**
  - V3's coarse test (CRE (1.4)) bounds fine plaquettes of the local minima U_{1,□'}.
  - RG1's domain U₁(ε₀) (RG1 (1.2), p.260) bounds the plaquettes and J of the global minimum U₁(V).
  - V3's output must be stated on RG1's domains. This is R-S1(d), open in either setting.
- **R-terms.** RG1's small-field model has none. In the compared model the (R) row of D9 comes only from the join of the fixed-threshold small-field model to CRE's large-field analysis (Lipschitz note §5(a), costs). Not done.
- **Unchanged:** LIP-2 (N4 transfer), LIP-3 (class-wide readings), the loop system R-S1, R-S2, (P-Y).
- **Closed here:**
  - H-1(i): the coupling dependence (§2);
  - H-1(ii): the imports RG1_Thm2_REP, D1, D2, D5, D6a, D6b, D6 with δ_k (§3);
  - the order of the constants for V3's items 5 and 6 at a fixed ε₀ (§4.1);
  - H-2a, (B3)(i) at the hybrid thresholds (§4.3, Lemma H-2a). The designated bonds satisfy |W(b₀) − 1| ≤ C_*L^dδ₀ on the support of the retained tests, so χ₀ and χ_Ax localized in Ω₁^∼ equal 1. Conditions: ε₀ ≤ cL^{2−2d} (fixed, after L) and g₀ small. Readings: R1 in weak form (the determining set of (1.2) contains the coarse bonds whose blocks lie near the cube □' of R3), R2 (U_{1,□'}(y,x) = 1 for the mean of (0.11), from CRE p.247 line 37 and p.248 line 37; load-bearing), R3 (the geometry of CRE p.248 lines 9–11, derived from (1.10)), and V3's definedness convention for δ(ŪV⁻¹) on rows of Ω₁ (on rows of Ω₁^c it is derived). The path families G(y,x) are from RG1 p.252, lines 29–33. The same proof gives CRE's own p.248 claim with A₀/A₁ ≥ C′L^d.

**Status (19:29, revised 22:14):** H-2a is proved in §4.3. H-2b is open: (f) at the boundary cubes, H-2b(loc) and H-2b(ζ). The proposed repair (f′) for (f) needs further work and a V3 change.

**Review (21 Oct):** §4 opening, §4.1 and §4.2 reviewed in packet lip-a-order-20261021-r1. Verdict: claim (1), the order of the constants, correct; claim (2) not sufficient as worded; no fatal issues.
- S1 repaired: §4.2 now separates pass, pass given H-2a, and reduced to H-2b.
- S2 repaired from VAR: (172)–(173), p.305, and Prop. 9, p.309, give a coupling-free domain. The condition 44d²B₃ε₀ ≤ C₁ε₁^V is added to step 4.
- S3 repaired: V3's item 2 consists of two upper bounds on ε₀ by constants of L and the group (§4.1).
- The minor findings were repaired.

§4.3 (Lemma H-2a and H-2b) reviewed in packet lip-b-h2-20261021-r1. Verdict: Lemma H-2a essentially correct and sufficient for (B3)(i) as V3 consumes it; the H-2b reduction not established as stated; no fatal issues. Repaired by 22:14:
- S1: the consumers of U₁ ∈ D^{(11)} are six, not three (Lemma boundary-bijection at L313, the measurability paragraph at L300, L269 added).
- S2, S3: definedness at U₁ (H-2b(loc)) and the cross-boundary ζ(Ω₁^c) tests (H-2b(ζ)) are now open items beside (f).
- M1–M12: definedness on rows of Ω₁^c derived; R1 in weak form; the □'^∼ layer size; G(y,x) from RG1 p.252; the off-axis wording; the two-point uniqueness bound; "≤" in CRE's setting; the (190) prefactor; the "ratio 1" sentence deleted; the radius r_M′; "near" defined; L355 cited.
- R2 recorded as load-bearing.

## 1. The setting adopted

The compared small-field model is RG1's small-field model (RG1 (0.17)–(0.20), Theorem 3, p.264), with these constants:
- fixed: RG1's plaquette threshold ε₀, domains α₀, α₁, cube size M, decay κ, coupling bound γ;
- step-dependent: CRE's fluctuation cutoff δ_k := g_k r(g_k), r(g) = A₁(log g⁻²)^{p₀}, p₀ ≥ 1, in place of RG1's ε₁ in RG1 (2.9) (p.266).

Each theory uses its own couplings g_k in δ_k.
- The pair-dependence of Lipschitz note §2.4 does not arise for δ_k: the difference of two theories' cutoffs at the same level is a coupling difference, which D6a's cutoff part estimates (§3).
- The plaquette threshold and the domains do not depend on the level. So §2.4 stays void for them.
- The localisation scale R₁ of CRE enters only V3's first step, through (B3)(ii) and the period conditions (§4.2). N6 is not triggered by the compared model.

## 2. H-1(i): the dependence on the coupling

**What RG1 states.**
- RG1 p.263 (lines 25–27): E^{(j)} "is a C^∞-function of g_{j−1} ∈ [0,γ], (or analytic)".
- RG1 p.264 (line 33): β_{j+1} "is a smooth function defined on the interval [0,γ], (or analytic), uniformly bounded on this interval together with all derivatives".
- Both are inductive assumptions. Theorem 3 asserts them, but no proof is given for them (`ONE_LOOP_PROOFS.md` line 131; `P2C_WORK.md` A).

**What RG1 and RG2 use.** Text check of every page:
- RG1 pp.249–301 and RG2 pp.1–22: the transcriptions are complete (53 and 22 pages).
- Every derivative in them is a derivative in the field or the momentum: p.270 (smooth partition of unity), pp.271–274 (in t_□ and δ/δB), pp.280–298 (functional and momentum derivatives); RG2 pp.4, 7, 10 (in s and t_□).
- No step differentiates in a coupling. So the C^∞ clause is not an input of RG1's proof. In the hybrid it is not claimed.

**What the imports use instead.** They replace the clause by three properties: continuity (C), the coupling Lipschitz bound D6a, and the bound (P2). Each passes with δ_k.
- *(C), Proposition 2.6.* The couplings enter through the potentials (continuous) and through the indicators {|B(b)| < δ_k/g_k} = {|B(b)| < r(g_k)}. r is continuous on (0,γ]. So the indicators are constant near g_k⁰ off the Gaussian-null set {|B(b)| = r(g_k⁰)}, and dominated convergence applies as in step 3 of the proof.
- *D6a (`DIFFERENCES_PROOFS.md` §2.1), coupling part.* On the support of the cutoff the unscaled field is |zCB| ≤ |z|r(g) < Rδ(g)/2 for |z| < Rg/2. RG2's estimates apply once Rδ(γ)/2 ≤ ε₁*, the largest admissible fluctuation size. The bound becomes M = O(1)C₃Rδ(g), and Schwarz gives 8·O(1)C₃δ(g)|g′ − g|/g.
- *D6a, cutoff part.* The thresholds are t = r(g) < t′ = r(g′) for g′ < g ≤ 2g′, since r decreases. From r′(g) = −2p₀A₁(log g⁻²)^{p₀−1}/g,

  t′ − t ≤ (4p₀/log g′⁻²) t′ |g − g′|/g,

  which is better than the ε₁ case (t′ − t ≤ 2t|g − g′|/g) by the factor 2p₀/log g′⁻². The shell factor is τ := sup_{u ≥ r(γ)} uⁿe^{−½γ₂u²}. It is smaller than any power of γ, because r(γ) ≥ A₁(log γ⁻²) for p₀ ≥ 1. The check against RG2 (2.22)–(2.25) is unchanged: the shell bond is a P-bond at threshold t ≥ r(γ).
- *D6a, large changes.* The trivial bound is 2·O(1)C₃δ(γ).
- *D6a, result.* η_E = C(C₃δ(γ)/E₀)γ² and η = C_ΛE₀η_E, with δ(γ) = γr(γ) in place of ε₁.

## 3. H-1(ii): the Bałaban-project imports with δ_k

Each item was read for every use of the fluctuation cutoff (`ONE_LOOP_PROOFS.md` §§2, 8; `DIFFERENCES_PLAN.md` §1; `DIFFERENCES_PROOFS.md` §§1–3; `P2C_WORK.md` B′, C, D).

| Import | Use of the cutoff | With δ_k |
|---|---|---|
| Lemma 2.1 (flow lemma) | none: hypotheses (W), (C) | unchanged |
| Remark 2.3 | b_{k+1} = Λ(log Z^{(k)}), the Gaussian term | unchanged; the cutoff enters only β − b |
| Prop. 2.4 (P2) | RG2 (2.41): O(1)C₃ε₁; conditions on ε₁ all upper bounds (RG2 pp.7, 18, 20, 21; RG1 pp.269, 273, 276, 280) | O(1)C₃δ_k, so (P2) holds with C_ΛC₃γr(γ) → 0; the γ-conditions become per step, as in check note §4 |
| Lemma 2.5 (C_Λ) | Cauchy radius from α₀, α₁ | fixed, since α₀, α₁ are RG1's; this is the point of (a) |
| Prop. 2.6 (C) | threshold ε₁/g_k | threshold r(g_k), continuous (§2) |
| Thm 8.1 | zero-coupling coefficients, no cutoff | unchanged |
| Cor. 8.2 | Lemma 2.1, Rem. 2.3, Thm 8.1, Props 2.4, 2.6 | holds; δ = C_ΛC₃γr(γ) |
| D1 | none (Schwarz) | unchanged |
| D2 | room ε₁ ≤ ε₁*/R; B = CC₃ε₁/E₀ | room R ≤ ε₁*/δ_k → ∞; B_k = CC₃δ_k/E₀ ≤ CC₃γr(γ)/E₀ |
| D5 (depth) | VAR's regularity parameter of the backgrounds (VAR (9), (10)) | the plaquette threshold, fixed in (a) and in RG1; unchanged |
| D6a, D6b, D6 | §2 above | η, b ∝ γ³r(γ) |
| D_HOLO, D7 | CRE's model (threshold ε_j, domains of CRE (2.34)–(2.39)) | not used by the compared small-field model; the large-field side enters only through the join (gaps block) |
| D9 | constants B, η, b, A | B, η smaller; b = C_ΛE₀O(B) with fixed C_Λ; A from the join |

Consequences for the Lipschitz note:
- *Lemma T.* τ = δ/b̄ + Cg² with δ = C_ΛC₃γr(γ). It tends to 0 with g alone; ε₁ is no longer decreased first.
- *ω (Lipschitz note §3.2).* ω_k = 4C′(1+ϑ₀)δ_k/ϑ₀ = O(g_kr(g_k)). The Lipschitz note's "ω improves to O(g)" should read O(g r(g)).
- *The young-level classical source (Lipschitz note §5(a), costs).* It is set by the plaquette threshold: c_cl ε₀²x_ℓ per point with RG1's fixed ε₀. The note writes ε₁ there; the constant is the plaquette threshold.

## 4. H-2: V3's inputs (B1)–(B4) at a fixed plaquette threshold

In the hybrid, V3's fine threshold ε₀ = g₀A₀(log g₀⁻²)^{p₀} and coarse threshold ε₁ = g₁p₀(g₁) become fixed constants. V3's δ₀ = g₀r(g₀) is kept.
- Take the coarse threshold ε₁ᴴ := ε₀ for the fixed ε₀.
- CRE's coarse test (1.4) (p.246) is then "fine plaquettes of U_{1,□'} below ε₀L⁻²". This is RG1's plaquette condition for U₁(ε₀) (RG1 (1.2), η = L⁻¹), stated for the local minima.

### 4.1 The order of the constants: items 5 and 6 (closed)

**In V3.**
- *Order.* V3 fixes its constants before the coupling, in the order of app:thresholds (V3 L3968): L, the group constants, τ_L (with m_L, c_L, γ_L), R_loc, R_p, s_𝔓, R_c, C_{L,R_c}, n_ℰ, …, ϑ_*, …, V3's κ, …, M₁, M₂, M, the collar constants. The coupling is chosen after them.
- *Why items 5 and 6 hold now.* For item 6, L3977 says so explicitly: "because ε₀=g₀A₀(log g₀⁻²)^{p₀}→0". For the ε₀ parts of item 5 the reason is implicit ("All hold for small g₀").
- *At a fixed ε₀, item 2* (eq:convex-background-thresholds, V3 L3632–3635; the hypotheses of Lemma regular-bounds, L434, restated in the standing conditions, L259) becomes two upper bounds on ε₀ by constants of L and the group:
  - μ̂ = C_{L,R_c}ε₀ < τ_L/2;
  - max(1,c_L)μ̂ < γ_L/4.

  V3 L3636 derives 6c_h s_𝔓 ε₁ < r_G from the first of these, using τ_L ≤ 2c_Gr_G.
- *At a fixed ε₀, item 6* becomes two upper bounds on ε₀ by constants that are fixed before the coupling:
  - 3c_Gc_h s_𝔓 ε₀ ≤ τ_L/2;
  - n_ℰ^{1/2}c_Gc_h·2O(L²)ε₀ ≤ ϑ_*/4.

  O(L²) is independent of the coupling by the reading of (B1).
- *The ε₀ parts of item 5* are the same kind of bound:
  - VAR Theorem 1's threshold;
  - 2O(L²)ε₀ and O(1)L²ε₀ below ϱ_G, r_G/√N and the small-diameter radius.
- *The pure-smallness uses of check note §3(b)* are also of this kind: the smallness of μ̂ = C_{L,R_c}ε₁ᴴ (item 2 above), 6c_h s_𝔓 ε₁ᴴ ≤ r_G (implied by item 2), K_αε₀ ≤ a₁ and B₃K_αε₀ ≤ a₀.

**In RG1 and RG2.**
- *Where ε₀ occurs.* Pages 254, 255, 259, 260, 263, 264 and 265 of RG1 (20 occurrences), and nowhere in RG2. This was found by a text search of the complete transcriptions (RG1 pp.249–301, RG2 pp.1–22; §2).
- *How it occurs.* Each occurrence is one of:
  - a definition;
  - "ε₀ sufficiently small" (p.254 line 22 of the transcription file, p.259 line 13, p.260 line 38, p.263 line 23);
  - an assertion linear in ε₀ (p.255 "|U−U₀|<O(1)ε₀"; p.260 "|V(∂p')−1|<2ε₀ … with 2ε₀ replaced by B₃⁻¹ε₀"; p.265 "|W(∂p')−1|<2ε₀");
  - Theorem 3's existence statement (p.264).
- *Order in RG1.* Theorem 3 (p.264): "if κ≥κ₀, M≥M(κ)"; ε₀, ε₁, α₀, α₁ "depend on M and satisfy numerous restrictions, which will become clear in the proof"; γ depends on all the other constants.
- *Two relations tie ε₀ to other constants:*
  - the inclusion U_k(ε₀) ⊂ U^c_j(X, α₀, α₁) needs ε₀ small given α₀, α₁ (p.263, lines 19–23). This is an upper bound on ε₀;
  - the integration region of the step must keep U_k(V) ∈ U_k(ε₀) (p.265, lines 17–20). This bounds the fluctuation cutoff given ε₀, i.e. it bounds ε₀ from below in terms of δ_k. A smaller cutoff gives a smaller region, so it suffices that δ_k is at most RG1's admissible ε₁, which is a condition on γ (step 5).

**Order of choice.** Choose, in this order:
1. L;
2. V3's pre-coupling constants in the order of L3968, which fixes V3's κ before M₁. RG1's κ ≥ κ₀ and then RG1's M ≥ M(κ) (Theorem 3) are chosen where V3 chooses M₁. RG1's κ is not V3's κ. RG1's M is played by M₁: V3 identifies its M₁ with CRE's M₁ of p.245, "the size of cubes for which the theorems of the previous papers … are valid" (V3 L252);
3. α₀, α₁;
4. ε₀, below the minimum of:
   - RG1's bounds;
   - V3's items 2, 5 and 6 and the pure-smallness list;
   - ε₀ ≤ cL^{2−2d} (Lemma H-2a, §4.3);
   - the H-domain condition 44d²B₃ε₀ ≤ C₁ε₁^V of §4.2;
5. γ, and V3's threshold on g₀.

No condition bounds ε₀ from below by a quantity fixed before the coupling. Every lower bound has the form ε₀ > Cδ_k, with C fixed before ε₀: p.265 above, and Lemma H-2a's (8 + C_*L^d)δ₀ < ε₀(1 − L⁻²) and 2CdLδ₀ < ε₀. Step 5 meets them. This settles the question of the summary of 21 Oct ("is ε₀ chosen after L?"): it is, through its dependence on M.

### 4.2 The inputs: what passes and what reduces to H-2b

Status (repaired after review lip-a-order-20261021-r1, S1):
- **Pass:** (B1)(ii) and (iv); (B3)(ii) and (iii); the bound on H_{1,Ax}.
- **Pass given Lemma H-2a:** (B1)(i), and the hierarchy item of (B3)(i). H-2a is in review packet lip-b-h2-20261021-r1.
- **Open through H-2b:** (B1)(iii), and every input that uses it: (B2) (through Lemma fibre-smallness(i)), (B4)(i) and (iii) (Lemma fibre-smallness), and (B4)(ii) ("the membership U₁ ∈ D^{(11)}"). These are reduced to H-2b, not passed.

- **(B1).** Each of its sources is a fixed-threshold statement with constants independent of the coupling:
  - VAR Theorem 1, "for ε₀ sufficiently small" (CRE p.248);
  - REG Lemma 1, whose bound 4d²α₀ + α₁ is linear in its thresholds (REG pp.79–80);
  - AVG pp.24–25, "for L²α₀ sufficiently small".

  (B1)(i) rests on (B3)(i), and (B1)(iii) is H-2b (§4.3).
- **(B2).** Proved in V3 (the Remark under (B2)), except its reading of the rows with one block off Ω₁, which is threshold-free. It uses the threshold only through Lemma two-block's τ_L, the first condition of item 6 (§4.1), and the first assertion of Lemma fibre-smallness(i), which uses (B1)(i), (iii) and (iv). Through (B1)(iii) it inherits H-2b.
- **(B3)(ii), (B3)(iii) and the bound on H_{1,Ax} behind (B4)(ii).**
  - *CRE's statements.* |U₁U_{1,□'}⁻¹ − 1| < O(1)B₃e^{−δLM₂R₁}ε₁ (p.250), and |H_{1,Ax}| < O(1)B₃e^{−δMR₁}ε₁ (p.251).
  - *CRE's printed mechanism.* It is given at the general step, CRE (3.17)–(3.19), p.268:
    - the regularity |∂U_{k+1} − 1| < 2B₃ε_{k+1}(L⁻¹η)² bounds the argument of H by 44d²B₃ε_{k+1};
    - H is then bounded by B₃e^{−δLM₂R}·44d²B₃ε_{k+1}, which is linear in the regularity size;
    - this is compared with δ_k through ε_k = (A₀/A₁)δ_k.
  - *In the hybrid.* The regularity size is the fixed ε₁ᴴ = ε₀, and the comparison needs O(1)B₃²e^{−δLM₂R₁}ε₀ ≪ δ₀ = g₀r(g₀).
  - *Why it holds.* R₁ ≥ (log g₁⁻²)^𝔯 with 𝔯 ≥ 2 (CRE pp.245–246). So e^{−δLM₂R₁} ≤ (g₁²)^{δLM₂(log g₁⁻²)^{𝔯−1}}, which is smaller than any power of g₁. This beats δ₀/ε₀ ≍ g₀(log g₀⁻²)^{p₀}/ε₀ once g₁ ≤ Cg₀. That bound follows from RG1 (0.18), p.255, 1/g₁² = 1/g₀² − β₁, and the uniform bound |β₁| ≤ B on [0,γ] (RG1 p.264 line 33): g₁² ≤ g₀²/(1 − Bg₀²) ≤ 2g₀² for Bg₀² ≤ ½. (In CRE's setting, CRE (2.6) as quoted at V3 L3977 gives g₁ ≤ (1+β₀)g₀.) The same argument covers item 5's "MR₁ large" and "M₂R₁ large".
  - *Reading used.* V3's reading (B3)(iii) (B₃, δ and O(1) independent of the coupling and of the branch, named in (H4)), with the regularity size set to ε₀ in place of CRE's ε₁. The linear form is printed in (3.17)–(3.19) for H_{k+1,□'}. For H_{1,Ax} (p.251) it holds for the same reason, since both rest on VAR (190). If V3 is re-sourced, this reading is to be added to (H4).
  - *The domain at fixed ε₀ (review S2; VAR quoted and checked, the integration step derived).* CRE's family has the regularity size tend to 0 with R₁⁻¹. The pair (ε₀ fixed, R₁ → ∞) lies outside it, so the domain on which the bound on H is linear has to come from VAR:
    - VAR's extension is on V′ = e^{iB′} with |V′ − 1| < C₁ε₁, |B′| < 2C₁ε₁ ((172), p.305), "for ε₁ sufficiently small".
    - "We assume that C₁ is an absolute constant, hence B₅ is such a constant also" (p.305, after (173)), with ε₂ = B₅ε₁.
    - Proposition 9 (p.309): 𝓗 is analytic on that domain, and its functional derivative satisfies (190) there.
    - VAR contains no coupling. So the radius is coupling-free. Write ε₁^V for VAR's admissible ε₁.
    - 𝓗(0) = 0, since B = 0 gives V′ = 1. So integrating (190) along tB, t ∈ [0,1], gives a bound linear in sup|B|, with the decay of (190), on the whole domain. CRE's (3.17)–(3.19) is this estimate for a B supported at distance of order LM₂R from the point.
    - The condition is 44d²B₃ε₀ ≤ C₁ε₁^V, an upper bound on ε₀ by a coupling-free constant. It is now listed in step 4 of §4.1. The external field must also satisfy VAR's regularity conditions, (3.35)–(3.38) of [5] or (1.7)–(1.9) of [6], cited on p.309. At fixed ε₀ these are smallness conditions of the same kind (p.281: "ε₀+C₁ε₁≤c₁"). [5] and [6] are not transcribed here.
- **(B3)(i)'s hierarchy condition.** "A₀ sufficiently larger than A₁" becomes ε₀/δ₀ → ∞, which holds for small g₀. The removal itself is Lemma H-2a (§4.3, proved).
- **(B4)(i) and (iii).** These are Lemma fibre-smallness. The threshold enters only through items 5 and 6 (§4.1), through (B1), and through (B2), which reduces to the same items. Through (B1)(iii) they inherit H-2b.
- **(B4)(ii).** Lemma boundary-bijection, from the H_{1,Ax} bound above at tolerance δ₀/40, and from (B1). Through "the membership U₁ ∈ D^{(11)}", which is (B1)(iii), it inherits H-2b.

### 4.3 What does not pass as stated

**H-2a: (B3)(i).**
- *The tests.*
  - Removed: χ₀ (CRE (1.1)), fine plaquettes below ε₀; and χ_Ax (CRE (1.5)), |U^u(y,x) − 1| < ε₀.
  - Retained: χ₁ ((1.4)), fine plaquettes of U_{1,□'} below ε₁L⁻²; χ₀′ ((1.8)), free bonds within 2δ₀ of U_{1,□'}; and the constraint Ū = V.
- *Why CRE's statement does not transfer.*
  - The removal claim compares thresholds through their ratios. The hybrid's ratios are at least as favourable as CRE's: ε₁ᴴL⁻²/ε₀ = L⁻² against (1+β₀)L⁻², and δ₀/ε₀ → 0 against A₁/A₀.
  - But CRE gives no proof ("it is easy to see", p.248), and its claim is made at thresholds that tend to 0 together. At the same g₀ the hybrid's retained set is larger, so the claim does not follow from CRE's by inclusion.
- *Why a lemma is needed.* b₀(c) enters every closed contour of RG1 (0.4) (p.253, through −c) and the final factor U(c), so the constraint fixes it only implicitly. V3 controls it in Lemma fibre-smallness(iii) on D^{(11)}, after (B1)(i), which rests on (B3)(i); that proof cannot be reused here without a circle. The lemma below uses only the retained tests.

**Lemma H-2a (designated bonds; proved 19:21).** Let ε₀ ≤ cL^{2−2d} and let g₀ be small (conditions below). On the support of the retained factors of (1.6), every designated bond b₀(c) in a plaquette tested by a χ₀ localized in Ω₁^∼ satisfies |U(b₀)U_{1,□'}(b₀)⁻¹ − 1| ≤ C_*L^dδ₀, and χ₀, χ_Ax localized in Ω₁^∼ equal 1. C_*, c depend on d and N only.

*Conventions.*
- |·| is the norm of CRE's tests, bi-invariant, so |XY − 1| ≤ |X − 1| + |Y − 1|. Along a path, |U(Γ) − U′(Γ)| ≤ Σ_{b∈Γ}|U(b)U′(b)⁻¹ − 1|. For a closed contour spanned by a lattice surface S (lasso decomposition), |U(∂S) − 1| ≤ Σ_{p∈S}|U(∂p) − 1|.
- h is V3's chart norm (normalised Hilbert–Schmidt, V3 L252). Log is the principal logarithm on the chart ball h < ϱ_G = π/√N, where ‖·‖_op ≤ √N h. On this ball |e^{iA} − 1| and h(A) are equivalent with constants depending on N. C, c, K below depend only on d and N.
- Write U(b) = W(b)U_□(b), with U_□ := U_{1,□'}.

*Readings.*
- **R1 (weak form).** "B₁(□'^{∼4}) is the minimal determining set based on □'^{∼4}" (CRE p.246, line 36) is read as: its coarse bonds include every coarse bond c whose two blocks lie in the fine 2dL-neighbourhood of the cube □' of R3. Only these rows are used. They lie at depth at least three L²M₂R₁-layers inside □'^{∼4}, which exceeds the width 2LM₁ of the fine layer of B₁(·) (V3 L4388), since M₁ < M₂ (V3 L255). The definition of minimal determining sets (CRE p.256) is not re-read here, so R1 is a reading. Every contour of (0.4) for Q₁^{s*}V of (1.3) has holonomy V(c)V(c)⁻¹ = 1, so M(Q₁^{s*}V, c) = V(c). The constraint of (1.2) then gives M(U_□, c) = V(c) for these c.
- **R2.** U_{1,□'} "is taken in the axial gauge" (CRE p.247, line 37), and the axial gauge conditions are U(y,x) = 1 for x ∈ B(y), x ≠ y (p.248, line 37). This is read as U_□(y,x) = 1 on every block B(y) ⊂ □'^{∼4} ∩ B(P₁^1), with U(y,x) the mean of (0.11) (the mean axial gauge, as V3 (B1) adopts). The reading is load-bearing: under the contour-axial alternative that p.247 also mentions, only |U_□(y,x) − 1| ≤ O(d²)ε₀ follows, and the removal of χ_Ax below fails. If V3 is re-sourced, R2 is to be recorded in (H4).
- **R3 (geometry).** CRE p.248, lines 9–11: "On the set Ω₁^∼ we have only the small field characteristic functions", with Ω₁ at distance at least 2LMR₁ from the large-field regions. This is read as follows.
  - Every plaquette p tested by χ₀ and every block B(y) tested by χ_Ax, localized in Ω₁^∼, lies in an L²M₂R₁-cube □' (p.246, line 30) whose χ₁(□') and χ₀′(□') are retained factors.
  - The fine 2dL-neighbourhood of p, resp. of B(y), lies in □'^∼ ∩ B(P₁^1). □'^∼ adds a layer of L²M₂R₁-cubes (V3 L252), and L²M₂R₁ ≥ 2dL.
  - The geometric content follows from CRE (1.10) (p.248), Ω₁ = (Q₁'^{∼2})ᶜ ∩ B(P₁^1)^{∼−3}: hence Ω₁^∼ ⊂ B(P₁^1)^{∼−2} ∩ (Q₁'^∼)ᶜ, so each L²M₂R₁-cube in Ω₁^∼ carries retained χ₁ and χ₀′ factors.
  - The reading does not involve the thresholds.
- **Definedness.** The integrand is supported where the averages (0.4) and the means (0.11) are defined in the chart. This is V3's reading of the support of δ(ŪV⁻¹) (D^{(11)}, V3 L269).
  - In (1.6) as printed, χ₀ ensures it, so the reading does not change (1.6).
  - After χ₀ and χ_Ax are dropped, the two integrands agree. Where the averages are defined, the lemma gives χ₀ = χ_Ax = 1 on the support of the retained factors. Where they are not defined, both integrands vanish.
  - V3 L269 imposes definedness only on rows of Ω₁; on rows of Ω₁ᶜ, V3 L252 sets M to the straight transport off 𝒪_c, and some such rows lie in Ω₁^∼. There definedness is a consequence, not a reading. The straight-transport constraint gives U(c) = V(c), hence Z = T⁻¹ in the notation below. Then, with the bounds from the retained tests below, |P − 1| = |YT⁻¹ − 1| ≤ η for every off-axis contour, and the on-axis contours equal 1. So U ∈ 𝒪_c once η is below the chart radius.

*Structure of (0.4) at b₀(c).* Fix a coarse bond c in direction μ. L > 11 is odd (V3 L3968).
- *The contours.* For x ∈ B(c₋), each contour Γ ∪ [x,x′] ∪ (−Γ′) ∪ (−c) lies in B(c₋) ∪ B(c₊).
  - Γ and Γ′ consist of bonds inside one block.
  - [x,x′] crosses the interface once, at the bond b_x at the transverse position of x; −c crosses it at b₀ = b₀(c).
  - b_x = b₀ exactly for the L points x on the centre line. So for off-axis x, b₀ occurs in the contour only through −c.
  - Every other bond is non-designated. Off the axis, b_x lies in the corridor B(c) off the centre line, and no designated bond lies inside a block (V3 L355: "paths Φ inside the blocks, which contain no designated bond"; it also holds by definition).
- *The path families.* G(y,x) (RG1 p.252, lines 29–33) is the family of shortest contours from y to x generated by all permutations of the directions μ with n_μ ≠ 0, where x − y = Σδn_μe_μ ("|n_μ| ≤ L−1/2" as printed; for odd L and x in the block B(y) centred at y, |n_μ| ≤ (L−1)/2). So every contour of G(y,x) has Σ|n_μ| < dL/2 bonds, and for collinear y, x the family is the straight path alone.
- *On-axis contours.* For x = c₋ + te_μ, G(c₋,x) and G(c₊,x′) contain only the straight paths, by the collinear case. The contour runs along the centre line and back, so its holonomy is exactly 1 (in the convention U(Γ₁∪Γ₂) = U(Γ₁)U(Γ₂)). These L contours carry total weight L·L^{−d} = L^{1−d}. The off-axis weight is λ := 1 − L^{1−d}.
- *Off-axis contours.* Let k := U(c⁻), the transport along c from c₋ to the initial point of b₀. Let Ũ be U with U(b₀) replaced by U_□(b₀). Then:
  - U(c) = Z⁻¹Ũ(c), with Z := kW(b₀)⁻¹k⁻¹;
  - every off-axis contour has holonomy P = YZ, with Y := Ũ(contour);
  - Z is the same for all off-axis contours.
- *The average.* M(U,c) = e^{iā}Z⁻¹Ũ(c), with ā := λ⟨Log P⟩. Here ⟨·⟩ is the normalised average over the off-axis contours, a convex combination.
- *Consistency with V3.* The group-level coefficient of A(b₀) is 1 − λ = L^{1−d}. V3's α_c(id) = L⁻⁴id (L349) is this divided by L, because V3 normalises (Q₁a)(c) = L⁻⁵Σ_x a([x,x′]) (L356, d = 4). The coefficient "1/n" of the earlier sketch was wrong: there are L trivial contours, not one.

*Bounds from the retained tests.* Take p (or B(y)) and □' as in R3, and c with b₀(c) ∈ p.
- *Free bonds.* χ₀′ gives |W(b) − 1| < 2δ₀ on (□'^{∼2})^*, which contains every bond of the contours except b₀.
- *Background contours.* Each contour of U_□ spans a surface of at most 2d(d+2)L² plaquettes in B(c₋) ∪ B(c₊) ⊂ □'^∼. Each of these plaquettes is below ε₀L⁻² (χ₁ at ε₁ᴴ = ε₀). So |U_□(contour) − 1| ≤ 2d(d+2)ε₀.
- *The target.* By R1, V(c) = M(U_□,c) = e^{iΦ^□}U_□(c), with Φ^□ := λ⟨Log P^□⟩ and P^□ := U_□(contour).
- *The free part of c.* Write U_□(c)Ũ(c)⁻¹ =: e^{−iF}. c has L − 1 free bonds, so |e^{−iF} − 1| ≤ 2(L−1)δ₀.
- *The constraint.* Put T := V(c)Ũ(c)⁻¹ = e^{iΦ^□}e^{−iF}. Then M(U,c) = V(c) reads Z = T⁻¹e^{iā}.
- *The contours against T.* YT⁻¹ = Ũ(Γ ∪ [x,x′] ∪ (−Γ′))V(c)⁻¹, and the open path has at most (d+1)L free bonds. So |YT⁻¹ − 1| and |Y − 1| are at most η := C(ε₀ + Lδ₀).

*Step 1: every admissible solution is small.*
- By definedness each Log P lies in the chart ball, which is convex. So h(ā) < λϱ_G, and ‖ā‖_op < π(1 − L^{1−d}).
- *Each contour near the average.* Write P = (YT⁻¹)e^{iā} = e^{iη′}e^{iā}, with h(η′) ≤ η.
  - Along s ↦ e^{isη′}e^{iā} the eigenphases move by at most (π/2)√Nη (spectral perturbation of normal matrices). So they stay in [−θ, θ], θ := π(1 − L^{1−d}/2), when √Nη ≤ L^{1−d}.
  - There the inverse differential of exp has h-norm at most θ/sin θ ≤ πL^{d−1}. (ad is normal for the h inner product, and u/sin u is increasing on [0, θ].)
  - So h(Log P − ā) ≤ πL^{d−1}η.
- *The average is small.* From ā = λ⟨Log P⟩ we get (1 − λ)ā = λ⟨Log P − ā⟩, so h(ā) ≤ L^{d−1}·πL^{d−1}η = πL^{2d−2}η.
- *Conclusion.* ζ := Log Z satisfies h(ζ) ≤ CL^{2d−2}η ≤ r₀ once η ≤ cL^{2−2d}. Here r₀ ≤ ϱ_G/8 is a fixed radius depending on N.

*Step 2: the refined bound.*
- *The map.* Set Φ(Y,ζ) := Log[exp(iλ⟨Log(Ye^{iζ})⟩)e^{−iζ}]. It is analytic for max h(Log Y) ≤ r₀ and h(ζ) ≤ r₀. The constraint is Φ(Y,ζ) = Log T, and Φ(P^□,0) = Φ^□.
- *Its derivative.* Φ(1,ζ) = Log e^{−i(1−λ)ζ} = −L^{1−d}ζ exactly.
  - D_ζΦ(Y,ζ) − D_ζΦ(1,ζ) vanishes at Y = 1, and Φ depends on Y only through an average of functions of single contours.
  - So ‖D_ζΦ(Y,ζ) + L^{1−d}‖ ≤ K max h(Log Y) ≤ Kη, with K = K(N, r₀) uniform in L and λ.
- *Lower bound.* If Kη ≤ L^{1−d}/2, then h(Φ(Y,ζ) − Φ(Y,0)) ≥ (L^{1−d}/2)h(ζ) on h(ζ) ≤ r₀.
- *Upper bound.* Φ(Y,0) = λ⟨Log Y⟩, and |Y − P^□| ≤ 2(d+2)Lδ₀. So h(Log T − Φ(Y,0)) ≤ h(Log T − Φ^□) + h(Φ(P^□,0) − Φ(Y,0)) ≤ CLδ₀.
- *Conclusion.* h(ζ) ≤ 2CL^dδ₀, so |W(b₀) − 1| = |Z⁻¹ − 1| ≤ C_*L^dδ₀.
- *By-product: uniqueness.* The same derivative bound, integrated along the segment between two points of the convex ball h(ζ) ≤ r₀, gives h(Φ(Y,ζ₁) − Φ(Y,ζ₂)) ≥ (L^{1−d}/2)h(ζ₁ − ζ₂). By Step 1 every solution lies in that ball, so the admissible U(b₀) is unique given the free bonds. The constraints of different c involve different designated bonds, since the contours of c contain only b₀(c).

*Removal of χ₀.*
- A plaquette contains at most one designated bond. Parallel designated bonds are at least L apart. A designated bond in direction μ has its ν-coordinate at a block centre, while one in direction ν crosses a ν-interface.
- By R3 and χ₁: |U(∂p) − 1| ≤ |U_□(∂p) − 1| + Σ_{b∈∂p}|W(b) − 1| < ε₀L⁻² + 8δ₀ + C_*L^dδ₀ < ε₀ for small g₀.

*Removal of χ_Ax.* Take x ∈ B(y), with B(y) as in R3.
- The contours of G(y,x) lie in B(y). They contain no designated bond and have fewer than dL/2 bonds each (the path families above), so |U(Γ)U_□(Γ)⁻¹ − 1| < dLδ₀.
- Two contours of G(y,x) bound O(d²L²) plaquettes in B(y). So the family {U_□(Γ)} has spread O(d²ε₀).
- RG1's mean (0.8)–(0.11) is equivariant. On families of spread at most r_M′ it is Lipschitz with constant 2, by the implicit function theorem on (0.10), uniformly in the family size; r_M′ = r_M′(N) is chosen so that the implicit-function constant 1 + O(r_M′) is at most 2. The spread O(d²ε₀) is below r_M′ once ε₀ is small, which is an upper bound on ε₀ by a constant of d and N.
- With U_□(y,x) = 1 (R2): |U(y,x) − 1| ≤ 2CdLδ₀ < ε₀ for small g₀.

*Conditions.*
- *On ε₀:* ε₀ ≤ cL^{2−2d}. This is an upper bound by a constant fixed after L, so it joins step 4 of the order in §4.1.
- *On g₀:* Lδ₀ ≤ cL^{2−2d}, (8 + C_*L^d)δ₀ < ε₀(1 − L⁻²) and 2CdLδ₀ < ε₀. They hold for small g₀, since δ₀ = g₀r(g₀) → 0 at fixed ε₀.
- *No circle.* The proof uses χ₁, χ₀′, the constraint, definedness, R1–R3 and RG1 (0.4), (0.8)–(0.11). It uses neither (B1) nor V3's Lemma fibre-smallness, which come after it.

*In CRE's own setting.* Here χ₁ is at ε₁L⁻² with ε₁L⁻²/ε₀ ≤ (1+β₀)L⁻² ≤ 1/2 (CRE (2.8) as quoted at V3 L3977), and δ₀ = (A₁/A₀)ε₀. The last uses the transcriber's correction at CRE p.247, whose footnote records that it was not checked against the print.
- The same proof applies with η = C(ε₁ + Lδ₀).
- It proves CRE's p.248 claim once A₀/A₁ ≥ C′L^d and g₀ is small. C′ = C′(d,N) covers both margins: (8 + C_*L^d)δ₀ < ε₀/2 and 2CdLδ₀ < ε₀. This quantifies "A₀ sufficiently larger than A₁".

**H-2b: (B1)(iii).**
- *The statement.* CRE p.248: U₁ is "in the domain of integration" of (1.11). V3 reads this as the support of every characteristic factor (H4).
- *Interior cubes.* Here it follows from the comparison (B3)(iii) and the χ₁ bound on U_{1,□'}.
- *Cubes of Ω₁ \ Ω₁^{∼−1}.* The comparison does not reach them.
- *What V3 uses (re-checked 22:14 after review lip-b-h2).* The membership U₁ ∈ D^{(11)}(V,V₀) is used in at least six places:
  - L309, (B1)(iii): to apply (ii) to U₁, giving |U₁U_{1,□'}⁻¹ − 1| < O(L²)ε₀ on □'^{∼2};
  - L3740: the plaquettes of U₁ are below ε₀ on 𝔓_c;
  - L4291 and L4388: the characteristic factors of (1.11) are nonzero at U₁ itself;
  - (B4)(ii), L313: Lemma boundary-bijection is proved "from the membership U₁ ∈ D^{(11)}(V,V₀) of (B1), that is the cutoff χ₀′(Ω₁) at U₁ (CRE p.248)". This is (f) itself, used exactly near the boundary cubes;
  - the measurability paragraph, L300: the fibre D^{(11)}(V,V₀) contains exactly one point of Crit, namely U₁(V,V₀); the Borel property of U₁ rests on this;
  - L269: "(B1) provides the background U₁ ∈ D^{(11)}(V,V₀) for every admissible pair".
- *Reduction.* Split the membership into:
  - (r): definedness and the small-field conditions at U₁ on Ω₁^∼;
  - (f): χ₀′(□')(U₁) = 1 for every □' ⊂ Ω₁.

  - χ₁ is a condition on V, so it holds at U₁.
  - ζ(Ω₁^c): CRE says only that it collects the factors "localized in Ω₁^c". The χ₀′(□') factors of good cubes □' ⊂ Ω₁^c adjacent to ∂Ω₁ test (□'^{∼2})^*, which reaches two L²M₂R₁-layers into Ω₁. Unless CRE or V3 shows that these cross-boundary tests are not booked in ζ, they are tests of U₁ on bonds of Ω₁ and join (f). **Open (H-2b(ζ)).**
  - Definedness at U₁ is not yet derived. VAR Theorem 1 (p.279) needs data satisfying its (7) on the whole determining set, while V₀ is arbitrary in the large-field parts of Ω₁^c; and the plaquette bound C_Lε₀ (B₃ = B₃(d,L)) can hold only on Ω₁ and a collar. The repair: define U₁ as the VAR minimiser of (1.12) localised to a neighbourhood of Ω₁ inside Ω₁ ∪ Ω₁^∼, where V₀ is regular (plaquettes below ε₀, by Lemma H-2a applied to any U ∈ D^{(11)}(V,V₀), since U = V₀ off Ω₁); take the C_Lε₀ bounds on that region only; and identify this minimiser with CRE's U₁ (the critical point in the domain, p.248) through (B1)'s uniqueness clause, not through V3 L4388, which uses the membership being proved. Whether that uniqueness clause holds at the hybrid thresholds (all of D^{(11)} in VAR's class (6), divergence bound included) is not checked. **Open (H-2b(loc)).**
  - Given (f) and definedness, Lemma H-2a applied to U₁ (which satisfies the constraint and the retained factors) gives (r). For plaquettes of Ω₁^∼ \ Ω₁, R3 must pick □' ⊂ Ω₁, or the lemma is applied to an admissible U, which equals U₁ = V₀ there; otherwise the χ₀′ tests needed at U₁ are not covered by (f).
  - For interior cubes, (f) holds by (B3)(iii) at fixed ε₀ (§4.2).
  - So H-2b is at least (f) at the boundary cubes, plus H-2b(loc) and H-2b(ζ).
- *What is open: (f) at the boundary cubes.* For □' ⊂ Ω₁ \ Ω₁^{∼−1}, it requires |U₁U_{1,□'}⁻¹ − 1| < 2δ₀ on (□'^{∼2})^* ∩ Ω₁. The data side is known: V₀ is within 2δ₀ of U_{1,□'} on (□'^{∼2})^* \ Ω₁.
  - *What it asks.* The minimiser of (1.12) must not amplify its boundary deviation. Linearised, this is a sup-norm bound below 1 for the map from boundary data to interior values of the constrained axial-gauge problem. No maximum principle is available for that problem, and CRE gives no proof.
  - *CRE's own treatment.* CRE p.250 (lines 51–53) keeps these tests as cutoffs on A for □' ⊂ Ω₁ \ Ω₁^{∼−1}, so it does not assert their value at A = 0. V3's reading (H4) of p.248 does.
  - *Why it does not transfer from CRE.* The fluctuation tests coincide, since δ₀ = g₀r(g₀) = g₀A₁(log g₀⁻²)^{p₀} in both. But the hybrid's backgrounds have curvature up to the fixed ε₀, and CRE's claim covers only curvature below ε₀(g₀).
- *Proposed repair (not done).* Replace (f) at the boundary cubes by (f′): |U₁U_{1,□'}⁻¹ − 1| ≤ C_bδ₀ on (□'^{∼2})^* ∩ Ω₁, with C_b = C_b(d,L,N).
  - *Source for (f′).* VAR Proposition 9 (p.309) gives the analytic dependence U_k(V′V₀)U_k(V₀)⁻¹ = exp iη𝓗(B), B = (1/i)log V′. VAR (190) (p.308) bounds |δ𝓗_μ(B,x)/δB_ν(y′)| by O(1)(L^jη)^{−1}(L^{j′}η)^{−d}exp(−δ₀^{VAR}d(y,y′)/8). Apply this to (1.12), with reference data U_{1,□'} on the outer part. Summing the kernel, with the prefactor, gives C_b. The gauge must then be converted from VAR's Landau gauge to the axial gauge (VAR Proposition 2, not re-read here).
  - *What (f′) still needs (not done).*
    1. A common VAR problem containing both U₁ and a reference agreeing with U_{1,□'} near □' up to e^{−cR₁}. U_{1,□'} lives on B₁(□'^{∼4}) with straight-extension data, U₁ on Ω₁ with fine data V₀, so their determining sets differ near the boundary cubes.
    2. Smallness of V′ on the whole data set: Prop. 9 is for "small configurations V′". This fails where the region reaches Q₁ or large-field data, so "data far from □' contribute terms exponentially small in R₁" itself needs a localisation of the type of CRE (3.17)–(3.19).
    3. The Landau-to-axial conversion with bondwise sup control.
    4. Independence of C_b from the coupling and the branch.
  - *Then (r).* It follows from Lemma H-2a with 2δ₀ replaced by C_bδ₀ on the free bonds; only the constants change.
  - *What it needs in V3.* Each of the six uses above must be re-proved from (r) and (f′), with the boundary tests kept as cutoffs on A as at CRE p.250: in particular Lemma boundary-bijection with tolerance C_bδ₀, and a characterisation of U₁ for the Borel argument in a domain it provably belongs to (under (f′) with C_b > 2, U₁ may lie outside D^{(11)}). This is a V3 change, not to be made before the user agrees.
