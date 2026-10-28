# Large-Field and Cauchy Notes: Triage of the Fifth Review Round (28 October 2026)

Eleven reviews were launched at about 00:31 on 28 October, on the LF note at SHA256 86547ec89d91 (474 lines) and the Cauchy note at SHA256 7210b11ea338 (752 lines). The repair agent edits the Cauchy note outside §8 during the round, so the reviewers saw the Cauchy note at 7c9c630b0266. Edits to the LF note and to the Cauchy note's §8 are held until the reviews that read them have reported. The closure draft of the point (3) of (LF-A), the room at complex points, is held in the integrator's scratchpad for the same reason.

## Dispositions, Review cauchy-s87-20261028-r2 (§8.4 and §8.7)

Verdict: §8.4 correct; §8.7 correct in substance. The repairs of the previous round (w_K with the stopping scale k_s, the lemma lθ̃^l ≤ C_μw_K, the bound (1 + C_μ)m_j, and the closing of 𝒯) hold. Nothing is fatal or serious. The minor points and their repairs (held until cauchy-s86-20261028-r2 reports):

- (m1) C_τ has two D-type sums with the weight c_j, the D_m in 𝒟′_{[j]}[u] and D_{j−1}[u]. Repair: (1 + 2C_SC_m) in place of (1 + C_SC_m); (T1) is read with this C_τ.
- (m2) The displayed C_S″ has the coupling coefficient CC_βC_m and an undefined "·O(1)". Repair: C_S″ := C_S[2C_s(1 − L^{−β′}/θ̃)^{−1}(1 + θ̃^{−1})C_m + 2C_sCC_βC′_m + (C_e + C_h)C_m + (C^B_R/C_R)(2(1 + C_μ)C_∗C_sC_m + C_eC_Σ) + C_ν].
- (m3) g_i²Σ_{l>i}m_l ≤ (2(1−θ̃)^{−2} + b^{−1})m_i fails at small i. Repair: m_{i+1} in place of m_i.
- (m4) (8.5) replaces c′_jD_{j−1} by c_jD_{j−1} without a sentence. Repair: c′_j ≤ c_j for γ small, since ε^*_j ≤ ε^*_γ and N′_j ≤ (100MR_j)^d.
- (m5) θ̃ depends on K through ε^* := sup_{i≤K}ε^*(g_i). Repair: θ̃ is defined with ε^*_γ := sup_{g≤(1+β₀)γ}ε^*(g), and C_a with sup_{g≤(1+β₀)γ}g²p₀(g)².
- (m6) N′_k ≤ log_L(MR_k) + 1 needs R_{k₁} in place of R_k. Repair: N′_k ≤ N′(g_k) := log_L(MR(g_k)) + 3 through CRE (2.9), with the page read before the edit.
- (m7) Notation: β′ is both 1 − β and the coefficient of CRE (2.6); C_m has no explicit formula and is not in the Constants list; §8.4 writes L^{−β′(k+1−j)} where (8.2) has (k − j). Repair: rename the (2.6) coefficient, define C_m and list it, and use (k − j).
- (m8) The depth source C′_e of LF §5(d) is relative to the class norm of the dev insertions. Repair: C_e is enlarged by C′_e times that norm's bound.
- (m9) Outside scope: LF §5(d) l.435 writes ḡ_K without the part (K + 1)(θ̃^{k_s/8} + 2^{−k_s/16}) of the new w_K, and its C_m clashes with §8.7's. Repair: ḡ_K with w_K, and a new name for the LF constant.
- The hash change is the repair agent's edit outside §8, which the packet announced.

## Dispositions, Review lf-wext-20261028-r1 (the Exterior Part W_ext)

Verdict: the weight, the chain, run B's chain at run A's data, the data part, the equal-data part, the result, and the application of the Lemma (Two Constants) are correct. Two serious points, both accepted:

- (S1) The disc bound 𝔐 uses the 𝐇-maps of VAR Sects. D–E with arguments up to 26C_Ψε̂′ and plaquettes up to 52C₀ε₁′, outside the class of (1.65). *The disc.* covers VAR Sect. G and the pair class 𝒟̄ only, and (T-c) lists no threshold of Sects. D–E. Repair: (T-c) gains the condition that these are below the thresholds of VAR Sects. D–E, with the weighted contraction of *The chain.* closing there, after the thresholds are read on the VAR pages. It is a smallness of ε₁′, which is g_k times a power of log g_k^{−2}.
- (S2) *The couplings of W_ext.* takes sup|w^B_e − w^A_e| over supp w_e, which contains the fine layers of old components, possibly deep, where the coupling differences are not small. Repair: |Δw(y)| stays inside the v-sum, and the per-layer decay of (2.58) separates the layers near Λ, which give the history's coupling differences in the form of the couplings item of *The sum 𝐂_k.*, from the far and deep layers, which give an exponentially small tail of the kind of §4(e) *Deep terms.*
- Minor, accepted: "the determining sets and data differ only on Λ" (by (1.33)); the absorption display states the case of ε₁ as the larger of the constants of §1 and (c); the count 12 states its convention (a bond of Λ^{(k)} as a point, multiplicity ≤ d + 1, in C_h); the disc wording gives 26² as computed; C_L of (c) is renamed; θ₁'s support is stated as a choice; c_w is doubled on the 2ε₁-regular segment; the φ_m structure of the weights is cited to CRE (2.24).

## Dispositions, Review lf-profile-20261027-r1 (§4(b), the Profile)

Verdict: the norm |·|_π, the identity for ρ, the ratio π(y′)/π(y), and the count for the kernel K are correct. Three serious points, all accepted:

- (S7) The propagator acts on plain sources, whose kernel carries (a_j/a_{j′})³ (PBG (3.42)), not the L^{2(j−j′)} of K, so the π-weighted row sums need ⅛δ₀RM ≥ 4 log L + 1. Repair: the source norm |f|_{π,(−3)} := sup_xπ(x)^{−1}a_{j(x)}³|f(x)|, the bound |𝔊f|_π ≤ 2B₀c⁽⁴⁾|f|_{π,(−3)} with c⁽⁴⁾ := 6c₀^d(¼)(3 + 2L⁴), and the condition ⅛δ₀RM ≥ 4 log L + 1, implied by (⋆) of §4(e) at d ≥ 3. The same holds for the r₀-part of the residual bullet (Observation 1), whose c_K becomes 6c₀^d(¼)(3 + 2L³) under the same condition. The Status line and §4(e)'s sentence on (⋆) read 4 log L + 1.
- (S8) VAR's δV/δA′ is not local ((80), (85)–(90)), so |N(A)|_π ≤ C|A|_∞|A|_π is unsupported and the closing in |·|_π is unsupported. Repair (the integrator's): an a priori pointwise inequality for u(x) := a_{j(x)}|A₁*(x)| + a_{j(x)}²|∇A₁*(x)|, from VAR's kernel representations of the terms of δV/δA′, with one factor of A₁* kept at its point and the others at VAR's sup bound. The π-weighted row sums of the kernels follow from PRT2 (2.60), which gives π(y′)/π(y) ≤ L^{1−ε₀}exp((1−ε₀)(log L/RM)d(y,y′)) and so spends at most δ₀/32 of the decay. Since u is finite on the finite lattice, |u|_π ≤ 2|ρ|_π follows without a weighted contraction.
- (S12) The configuration difference A′* = A₁* − HD(A₁*) needs the profile of HD(A₁*). Repair: the same inequality for HD(A₁*), and the statement restricted to the coarse-side comparison U^A against MU^B in VAR's gauge.
- The cross-referenced claim of §4(c), *The remainder.*, "|(δV/δA′)(A)|_w ≤ C|A|_∞|A|_w by locality" with w = e^{(δ₀/2)d(·,Λ)}, has the same defect: that weight cancels the whole e^{−½δ₀d} decay of the 𝔇₂-factor of VAR (86). Repair: the same inequality, with a weight of smaller rate if the kernel sums need it.
- Minor, accepted: |·|_∞ and the source norm are defined; "for any multiscale determining set" reads "satisfying PRT2 (2.1)–(2.2)"; the propagator constant is 2B₀; the interface layer follows PBG (3.41); the form of (2.58) is stated as a consequence of the printed intermediate line; §4(c) does not use the profile.

## Dispositions, Review lf-rs-20261027-r1 ((R-s), §3(d))

Verdict: (R-s) holds on CRE §1, CRE §3, and LFR II §1, and on LFR I §1 except at one step. One serious point, accepted:

- (F1) The removal of the cascade tests χ_k^{(n)} of LFR I (1.22)–(1.24) through (1.48)–(1.50) (p.186 l.44–p.187 l.13) has the relative slack β2^{−(j−i)}(¼ − 2α), zero at Bałaban's α = 1/8, so it fails with a k-independent width. Repair (route fixed by the integrator): (1.48)–(1.50) are homogeneous under a common rescaling of the thresholds by 1 + τ, τ ≥ 0, since the additive term of (1.48) is unchanged and (1 + τ)T ≥ T. So the cascade tests are made soft with nested plateaus: the test χ̄_k^{(n)} has the plateau f ≤ (1 + κ_c)^{N−n}T_n and the width κ_c := κ_s/(N + 1), T_n Bałaban's threshold. On the support of χ̄_k^{(n+1)}, f^{(n+1)} < (1 + κ_c)^{N−n}T_{n+1}, and (1.48)–(1.50) at the rescaled thresholds put f^{(n)} on the plateau of χ̄_k^{(n)}. The same holds for (1.51)–(1.52), which have room. Every threshold stays within the factor (1 + κ_c)^{N+1} ≤ 1 + 2κ_s, and the margin of LFR I (1.31) allows 2κ_s = β/15, since (1 + β/15)(1 − 7β/90) < 1. The shell factor of a cascade test is (N + 1)/κ_s times that of §3(d). By LFR I p.198 l.55, N ≤ O(1)(log g_k^{−2})^ν, so the first part is absorbed into C_hθ̃^j through the strict gap θ̃ ≥ L^{−(1−ε₀)/4} > L^{−(1−2ε₀)} (ε₀ < 3/7) in a young pair, and the second part is (N + 1)g_j²|δ_j| ≤ |δ_j| for γ small, since g_k ≥ g_j. The tests of the disjoint case j ≤ k₀ are treated in the same way.
- Minor, accepted: LFR I (1.5) joins the sharp list; "overlapping tests" reads "tests on disjoint cube sets"; the reason for (1.59) is the plateau argument of p.269; "CRE §2 only defines the tests" is corrected (p.256 l.29–30, p.263 l.19–20, (2.50)); the l.112 wording on (3.23); the removals at LFR II p.378 l.10 and LFR I p.198 l.16 are listed; the citation slips; the Status line on §4(e). The hypothesis q_i > p₀ is the provisional reading (R-m′); no printed upper bound on q_i was reported.

## Dispositions, Review cauchy-s86-20261028-r2 (§8.6 and LF *Deep Terms.*)

Nothing is fatal. Accepted:

- (S1, serious) "No deep V(Y) in a young polymer" misidentifies Bałaban's Z (LFR I p.177 l.33): the deep V(Y) produced by re-expanding old terms on the layers of the surviving components of Λ_j^c ∖ Z (LFR II p.369 l.28–31, p.377 l.5–8) are neither excluded nor bounded. Repair: a crossing bound through 𝐇″ or through the weights of the constituent terms, adding to ν_j.
- (S2, serious) The two-run differences of the V(Y) factors themselves (LF §4(d)(ii)(i)) are absent from the final display of |𝐑^B − 𝐑^A|. Repair: a 𝒟^∗-type unweighted term, with §8.7 replayed.
- (S3, serious) C_ν depends on j(C) through C_h, and LF §4(d) still takes the R-step at most the stopping scale (k < 8n, n ≥ k/2 − 1), while §8.6 uses steps j up to K with births n > k_s/8. Repair: the absorption is redone for j > k_s with a j(C)-dependent constant, and the uniformity statements say j(C).
- Minor, accepted: the index shift between the birth n and the finest layer n − 1 (the threshold ⌊k_s/8⌋, the sum Σ_{m=n}^{j}, and the range of 𝒟_{[j]}); the citations (2.31) (CRE p.260 l.24) and LFR II p.377 l.14; "components of Z"; the quotient comparison stated for 𝐓′F; the collar count; the Open Gaps' "k/8"; the edge case k_s < 8.

## Dispositions, Review lf-forms-20261027-r2 (the Forms, §4(d))

Nothing is fatal. Accepted:

- (S1, serious) The single-scale (B1), (B2), and (B5) need multipliers divergence-free on each layer, which fails where two layers meet. So β_π ≡ 0 for multiscale data, "𝐐(Ũ)H^A = 1" in the constraint term, and the use of PBG's double-bar C^{(2)} in the (1.2) split are unsupported. Repair (the integrator's): one consistent multiscale averaging with PBG's bounds for its lift, or a multiscale (B1)–(B2) and (B5) with a depth-size bound on the interface terms in both runs.
- Minor, accepted: the per-point-of-𝐁₀ conversion through σ(y); the factors of 2 (the polarisation in c_f, x_E, the second-order part, the normalisation of (1.21)); the two uses of c_f; the column sums are (9.11); (2.59) restated; the 𝔰 normalisation; c_br ≤ 2 stated.

## Dispositions, Review lf-align-20261027-r1 (the Alignment, §4(d))

Nothing is fatal. Accepted:

- (S1, serious) The multiplier representation ⟨e, λ_{j′}(y)⟩ = f_y needs D_V*λ = 0 on each layer; the multiscale condition is only the weighted sum, and the interface sum with (Θ_j − Θ_{j+1})H₀e_y is generically nonzero. So x̄_λ, B̄_λ, x̄_J, B̄_J, the current part of R̄, and c_al are unsupported near the interfaces; 4d̄/α₁ is unaffected. This is the mechanism of forms S1. Repair (the integrator's): λ through an exact right inverse of the plain multiscale 𝐐, or through (𝐐𝐐*)^{−1}𝐐J, with decay bounds on 𝒟̄.
- Minor, accepted: C_U(M) := 4C_G(ε₀)c″_K + 2B₀c_KC′_Δ(M); (3.131) uses |J| (PBG p.421 l.38–42); the conditions 2C₀ε₁ ≤ c₃ and ε₁ ≤ 1 and §4(b)'s conditions on R and M are listed; C_ℒ; the convention for ε₁; 𝒟̄ carries PBG's thresholds α₁ and α_J = Mα₀, not CRE's.

## Dispositions, Review lf-complex-20261028-r1 (the Complex Class, §4(d))

Nothing is fatal. Accepted:

- (S1, serious) *The lift difference as a Taylor coefficient.*: the real-t bound on A(t) identifies VAR Sect. G's Landau representatives with the alignment representative, whose first-order mismatch is the content of (10.6c). Repair: the paragraph uses (10.6c) (the main line through r̄_n and (10.6c) is unaffected), or the step is removed.
- (S2, serious) The data parametrisation of the line is not stated. Repair: both runs are evaluated at D(z) = M^·(𝐔(z)) (LFR II p.358 l.27–29), with the role of 𝐉(z) stated.
- Minor, accepted: the count of averages in C_c; the citations for the disc and the data disc; 52C₀ in C_act; the membership of the complex minimisers in 𝒟̄; the attribution of real points outside Bałaban's class; the analytic gauge choice; the factor 2 in 2|t|g_kσ_k; the clash of C_av with the Cauchy note.

## Dispositions, Review lf-cweights-20261027-r1 (the Complementary-Weight Parts, §4(d))

Nothing is fatal. Accepted:

- (S1, serious) "Need no comparison of their own" is unsupported: 𝐂_k enters the main proof through its localisation (LFR II p.373 l.10–17, (1.59)–(1.64)) and its re-summation into V(Y), including Y ∖ Z^∼ ≠ ∅ (pp.376–377, (1.68)), compared per Y, and an aggregate bound supplies neither the Y-localisation nor the values at the decoupled configurations. Repair: the per-Y comparison of the localised 𝐂_k, with the V(Y) repair of vfun S2.
- (S2, serious, unclear) d enters 𝐂_k through I(U₀) (p.369 l.7) and 𝐂_k contains −log d, while the Cauchy note divides by d and puts V(X^∼) in the numerator. Repair: one representation is fixed, and the comparison follows it.
- Minor, accepted: the stale W_ext sentence at l.245; the data of U″_{h+2}; the count 11 and its convention; the complex version of the Lemma with (e^{φ_d} − 1)e^{c(M)} ≤ ½ and the Cauchy note's "(LF-A)(3)" label; the shared variable V_k against V′_k and the run-dependence of χ(Λ)(V′_k); the citations; the couplings through the background data.

## Dispositions, Review lf-vfun-20261028-r1 (the Functions of the Configurations, §4(d))

Nothing is fatal. Accepted:

- (S1, serious) a³|J(Ũ) − J′| ≤ C_jr(ε/a_n)ε₁ is false pointwise; the size is O(ε₁). So the room at real points and c_ρ do not follow as written. Repair: the reviewer's V22–V23.
- (S2, serious) The per-Y reduction is unsupported: the run-dependent re-summation, with its decoupled configurations, is not covered by d̄ (V2). Repair: with cweights S1.
- (S3, serious) The class bound behind the per-point count for 𝐑 is unsupported, and the 𝐄 bound rests on the unreviewed reading R-Δ^c (V13, V5). Repair: the class bound derived, and R-Δ^c reviewed or replaced.
- Minor, accepted: the age factor L^{−β′(m−j)} and the 𝐄 generation-sum constant; E₁(α); the pairing of (i) and (ii); the citations; β ≤ 1/8 against "not too small"; n₀'s dependence on j(C); r̂ over the non-deep domains and the nonlocal room.
- The closure draft for the room at complex points (the integrator's scratchpad) inherits S1–S3 and the profile's S8 and S12 and is not applied until they are repaired.

## Dispositions, Review lf-boundary-20261027-r2 (the Carried Boundary Terms, §4(e))

Nothing is fatal. The opening, the objects, the deep terms, (i) of the step map, the weights of the ages under (⋆), the algebra of the recursion, and the counts of *Into the quotients.* are correct. Accepted:

- (S1, serious) The variation part of (ii) of the step map and of *Into the quotients.* uses the room of §4(d)(ii), which is derived for the R-operation's chain in LFR I's spaces, not for the CRE fluctuation step, where CRE p.277 l.1–7 describes a shrinking margin; on the complex class the room is the point (3) of (LF-A). Repair: the room at the CRE fluctuation step at real points, derived from CRE's own spaces, and the complex points with the closure of (LF-A)(3). Until then "(derived)" in §4(e), the Status, and the Cauchy note's "the boundary terms leave (γ)" are replaced by the open status.
- (S2, serious) The R-operation's own boundary terms 𝔹_k^{(n)} of LFR I (1.60)–(1.63) meet the component (the first part of LFR II (1.49), p.369 l.28–30, or attached to it, LFR I p.191 l.44–47); their creation difference comes from a large-field preliminary integral, with the bound C₀exp(−(1 + 3β)κd_m) on Ũ^{(n)c}_k. Repair: their two-run comparison derived, or they stay in (γ).
- Minor, accepted: the inward weight e^{−σ(m−1−i)} with C_w ≤ 2L^d; the layer widths after R-operations from PRT2 (2.2), with the constant in (⋆); the reserved fractions of the decay of 𝐇_k and of δκ against CRE p.276 l.13–16 and RG I p.272 l.2–4; R-mark with two insertions; the citations (RG I p.257 l.7–9; the H-decomposition at CRE p.276 l.42–46; RG I p.272; "k/8"); the class of b_i; the case k_s/8 < j ≤ k_s/4; second-class components; C_B's dependence on W.

## Assignment of the Repairs

- The integrator: the profile (S7, S8, S12, and §4(c) *The remainder.*) in §4(b)–(c), and the interface multipliers (forms S1, align S1) in §4(d) *The alignment.* through *The terms in E.* and *The result for the forms.*
- Repair agent R (LF §3(d), §4(d) from *The exterior part W_ext* through *The lift difference*, and §5(d)): F1 with the route above, wext S1–S2, complex S1–S2, and the minor points of rs, wext, complex, and cweights, and s87 (m9).
- Repair agent V (LF §4(d) *The complementary-weight parts.* outside W_ext, *The functions of the configurations.*, and the Cauchy note's §8): vfun S1–S3, cweights S1–S2, s86 S2–S3 and its minor points, s87 (m1)–(m8), the half-class edit of §8.2, and the room at complex points from the integrator's draft once S1–S3 are repaired.
- Repair agent B (LF §4(e)): boundary S1–S2 and its minor points, and s86 S1 (the deep V(Y)), whose addition to ν_j goes to agent V for §8.6.
