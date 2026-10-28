# Large-Field and Cauchy Notes: Triage of the Fourth Review Round (27–28 October 2026)

Reviews of the Cauchy note at SHA256 30010adde8f1 (701 lines) were launched at 23:25–23:40 on 27 October. The state before them is in `WILSON_IT1_LF_TRIAGE_R3_2026_10_27.md`, section *Integrator Repairs and Launches*. Edits to the Cauchy note are held until all five reviews have reported, since the reviewers read the file live.

## Dispositions, Review cauchy-bridge-20261027-r1

The hash matched. Verdict: (B1)–(B5), the display after (B5), and the three applications (§9.4, §10.3, §10.4) are all CORRECT. Nothing is fatal or serious. The minor points and their repairs (held):

- (m1) "means of transported averages of U₁": the factors of index i ≥ 1 average Ū̄₁^i. Repair: (B1) reads "a product of means of transported averages of U₁ and of its double bars Ū̄₁^i, i ≥ 1".
- (m2) The background regularity, CMP 98 (109) with α₀ ≤ c₃ (Proposition 3), is unstated. Repair: one sentence before the bullets saying that the logarithms are taken at backgrounds regular in the sense of CMP 98 (109) with α₀ ≤ c₃, which holds at U^B and Ũ_j by §9.2 and §10.3.
- (m3) The surjectivity of Q_n has no pointer. Repair: cite PBG Theorem 3.12, (3.132), in (B2).
- (m4) The normalisation of C^{(2)} is implicit. Repair: (B4) states that C^{(2)} is the quadratic Taylor coefficient in the units of PBG (3.14), so the second-order part of the double bar is C^{(2)}[X, X].
- (m5) q_n is defined only implicitly. It is used only paired with a divergence-free ν, where it drops out. Repair: (B5) says so.
- (m6) In §9.4, Q_BℒδA = Q_AδA follows from the construction of ℒ (the plain chain rule), not from (B2). Repair: reword the sentence of the 𝒯 paragraph.
- (m7) Q₁ names both the plain and the double-bar one-step linearisations, separated only by "from here on". Repair: §9.4 writes Q₁^{pl} for the plain one, and §10.4's "from here on" sentence names the change.
- (m8) In (10.1), the source for Q′_m is PBG p.394 l.1–2; l.9–11 is R. Repair: cite p.394 l.1–2 and l.9–11.

## Dispositions, Review cauchy-pi-20261027-r1

The hash matched. Verdicts: the gauge identities (b), the formula (c) for π_X, the second bullet of (e), (10.6d′), the split and bounds of (f), (10.6e), and (A1) are CORRECT; (a), (d), and the first bullet of (e) turn on a definition conflict (S1). Nothing is fatal.

- (S1, serious) Accepted. §10.3 defines the form at a pair (𝐔, 𝐉) by writing 𝐉 into PBG (3.120), (3.128), and (3.134) (reading D2). The π-part of §10.4 used (3.119), the P-conjugate, which equals (3.120) only at the background's own current (reading D1). Disposition: D2, the reading §10.3 needs, since D1 would need J(𝐔(t)) on the complex path (PBG (3.38)). Under D2 the π-part vanishes identically in both runs:
  - PBG (3.116) gives (Dλ)(b) = η^{−1}(R_bλ(b₊) − λ(b₋)). So i[λ(b₋), (Dλ)(b)] = ½c(λ, Dλ)(b) pointwise, with c(λ, Y) := i[λ(b₋), Y(b)] − i[Y(b), R_bλ(b₊)] the Y-linear bracket of (3.117). In the note's normalisation c_X = ½c, the bracket of (3.120) at λ = μ_A is c_X(μ_A, A) + c_X(μ_A, P_XA) as a bond field. So ⟨A, Δ′_π[𝐉]A⟩ = ⟨𝐉, c_X(μ_A, A) + c_X(μ_A, P_XA)⟩ for every 𝐉, not only for the background's current.
  - (B5) with Q′_Xμ_A = 0 and D̄*ν = 0 gives 2⟨C^{(2)}(P_XA) − C^{(2)}(A), ν⟩ = −⟨Q_X*ν, c_X(μ_A, A) + c_X(μ_A, P_XA)⟩.
  - So the quadratic form of π_X is A ↦ ⟨𝐉 − Q_X*ν, c_X(μ_A, A) + c_X(μ_A, P_XA)⟩. It vanishes at 𝐉 = Q_X*ν, that is, at U^B (J^B(U^B) = Q^B_j*ν) and at the pair (J′_j = Q^A_{j−1}*ν). π_X is symmetric, so π_X ≡ 0 in both runs, and β_π ≡ 0.
  - Under D2 the Landau property R_AD_A*H₁^A = 0 at J′_j fails at order δJ. In the Cauchy note it is used only in the first bullet of *The bound at the two pairs of arguments.* and in the parenthetical of *Polarisation.*, both about β_π. (10.2), (10.5), the positivity of G_A^{−1} on ker Q^A_{j−1}, and the regularity of H₁^A use only H₁ = G₁Q_m*(Q_mG₁Q_m*)^{−1} and the series bounds, which hold at the pair.
  - Repairs (held). The π-part paragraph is replaced by the derivation above, ending in β_π ≡ 0. *The bound at the two pairs of arguments.* and *Functional form of the π-part.*, with (10.6d), (10.6d′), and (10.6e), are deleted. *Polarisation.*, (A1), (A2), and C(ε₀, γ_H) drop C_π^ℒ. *The parts of β.* reads β = β_act + β_con + β_gf. The first paragraph of §10.4 drops ℒ_pl, since δJ enters only through the crude bound of the constraint part. The Status lines and the Constants drop c_R, C^{pl}_ℒ, c_{br}, c_{π2}, C_π, and C_π^ℒ.
  - The LF note's uses of (10.6d)–(10.6e) become β_π ≡ 0 (the Cauchy note's §10.4), after the LF agents finish: the Open Gaps (l.11), the Status (l.14), §4(d) (l.241, l.258, l.262, l.268, l.310), and §5(e) (l.422).
- (M1) Moot: ℒ_pl and C^{pl}_ℒ entered only T₁, which is deleted.
- (M2) and (M3) Moot: both are in the deleted displays.
- (M4) Accepted in part. C_X := (5L)^d in (10.6c) is renamed C_{5L} and entered in the Constants; §8's cluster constant keeps C_X. C_X^{(2)}, D_A, and D_B carry the run index X ∈ {A, B} and stay.
- (M5) Accepted. The first paragraph of §10.4 cites PBG p.421 l.12–17 for the construction of G₁ and H₁.

## Dispositions, Review cauchy-align-20261027-r1

The hash matched. Verdicts: the opening of §10.3, the pair class (one misquotation), the adjoint averaging, the intermediate current, the alignment estimate with (10.3), the parts of β, the action-part identity, and the J-term are CORRECT; the multipliers need a one-line repair; the bound (10.6a) is UNSUPPORTED as derived. Nothing is fatal.

- (S1, serious) Accepted, with the reviewer's repair. H₀ := G₀Q_j*(Q_jG₀Q_j*)^{−1}, with Q_j PBG's j-step double-bar averaging, is PBG's H of (3.126) at 𝐉 = 0. For λ with D_V*λ = 0, (B1) of §10.1 gives ⟨𝒬(U)X, λ⟩ = ⟨Q_j(U)X, λ⟩, so ⟨𝒬H₀e_y, λ^X⟩ = ⟨e_y, λ^X⟩ for X = A, B, and the formulas for λ^A and λ^B, the bounds x_λ and B_λ, and the rest of §10.3 stand.
- (S2, serious) Accepted. The first and second variations of r_p in the action part are asserted, the first omits a transport term of order ε|F||𝒜| (relative size ν_F ≤ τ̂), several "-type" terms are not computed, and C_β omits their constants and a factor 2. Repair (repair agent): derive d(εr_p)[𝒜] and d²(εr_p)[𝒜′, 𝒜] from the definition of r_p in (9.11), with the transport term; compute every term of β_act + β_con at (H₁^Be_y, H₁^Be_{y′}); and state C_β with all constants.
- (m1) Accepted. The pair-class paragraph quotes (3.131) with |J| as printed, and says that H depends on 𝐉 through the series.
- (m2) Accepted. Where §10.3 uses the plain lift ℒ of §9.4, its constant is §9.4's, not C_ℒ′.
- (m3) Accepted. The polarised bound is |C₁^{(2)}[𝒜′, 𝒜]| ≤ 2C₂ε|𝒜′||𝒜|; C_β inherits the factor.
- (m4) Accepted. The operator count in (ii) is made consistent.
- (m5) Accepted. |J(Ũ_j)| carries the factor of order 2d from the bond count.
- (m6) Accepted. The variance identity names the (9.11) weights of F̄_p, "d r_p" becomes d(εr_p), and "relative to (3.132)" states the conversion from ℓ^d to the kernel normalisation ℓ^{−d}.
- (m7) RG I p.262 is checked against the transcription by the repair agent; the remark is not load-bearing.
- (m8) Accepted. The pair class states that 𝒟_j is imposed at the scale a_j while the form lives at the scale ℓ.

## Dispositions, Review cauchy-gf-20261027-r2

The hash matched. Verdicts: *Transports.*, the gauge-fixing part, *Inputs.*, *Identities.*, *Sizes.*, *The commutator.*, *The defects.*, *The bound.*, the functional form (10.6c), and the T^{−1} analysis of the lifts are CORRECT. Nothing is fatal.

- (1, serious) Accepted. The multilinear interpolation I places the coarse value of a bond at the centroid of its tube in Q^{str}: the midpoint of the bond joining the centres of B(c₋) and B(c₊), shifted by ((L − 1)/2)(ε/L) per coordinate from c under PRT1 (1.6). Then Q₁I reproduces affine fields, and the Taylor bound and C_ℒ′ stand.
- (2) Accepted. In (G2) the X-term coefficient is (2d + 1)C_tr; c_𝔠, c_{g3}–c_{g7}, and C_gf inherit it.
- (3) Accepted. *Transports.* itemises the non-transport terms of CMP 98 (124) and combines the contributions into C_tr.
- (4) Accepted. The fine-difference transport bound 2C_trν_F𝔰′ uses the thin-loop argument.
- (5) Accepted. The conditions C_ax·d(R_Q + 3)C₀ε₁ ≤ m_Q/4 and δ₁ ≤ min(δ_Q, 1/(6d)) join the conditions of (10.6) and the Constants; R_Q, C_ax, C_E, C_χ, r_T, M̃_Q, q, δ_Q, and C_Q are listed; the dependence of C_ℒ′ on the exponent is shown.
- (6) Accepted. The bound on sup|Q₁*ν| states that the operator factors of CMP 98 (124) are ≤ ½ by the smallness of CMP 98 Proposition 3.
- (7) Accepted. At 2γ_H the weight factor is (3/2)·(4/3) = 2; (ii)'s transport corrections include the (124) terms; the base point of Q̂_f on the entering face is fixed; the Hölder convention follows PBG's metric.

## Dispositions, Review cauchy-s8b-20261027-r1

The hash matched. Verdicts: §8.2(a), §8.4 with (8.5), the boundary gain, the deep-term bound for frozen terms, the R-term transfer, ν_j, and the sums of §8.7 are CORRECT; the deep V(Y) case is UNSUPPORTED; C_τ depends on j(C). Nothing is fatal.

- (S1, serious) Accepted. C_μ ≥ c(θ̃)j(C)^{κ₀/2−1}/ℓ_{j(C)}, so C_τ and (T1) depend on j(C), against the stated dependence. Repair (integrator): §8.7's weight m_i gains a term in the stopping scale k_s := K − j(C), as the reviewer suggests, so that the maxima over the layers above k_s/8 are bounded by a constant of θ̃ alone; or (T1) is stated with the dependence on j(C).
- (S2, serious) Accepted. A deep Y of V(Y) meeting a young component is not covered. Repair (integrator): a crossing bound for V(Y) from the decay of LFR II (1.68) in d_{k,Z}, with at least one cube per layer (CRE p.264 l.1–3), or a reduction of deep V(Y) to deep frozen constituents.
- (M1) Accepted (integrator). The stopping scale is written k_s in every threshold of §§8.2, 8.4, 8.6, and 8.7.
- (M2) Accepted. The Constants list gains c^B_j, 𝒟^∗, 𝒟^B, 𝒟^{∗′}, s^B, b_i, w_r, and η_k, corrects C_Σ, and states the dependences of C_μ.
- (M3) Accepted (integrator). C_S″ gains the c^B contribution.
- (M4) Accepted (integrator, with S2). The count for V(Y)'s domains is a constant C_V from (1.68), with the cube-to-point factor.
- (M5) Accepted (integrator). E₀ becomes max(E₀, B₀, R₁), and the generation factor max(k, j).
- (M6) Accepted (integrator). C_μ is defined with m ≥ k_s/8 − 1, agreeing with the LF note, and max e_m ≤ C_eC_μμ_K gains θ̃^{−1}.
- (M7) Accepted. l.12 is updated to the LF note's current points (3) and (5), and the status sentence on 𝐁 excludes §6.2.

Repairs applied by the integrator in §8 (Cauchy note hash 5aea6452423b before W6; W6 applied after):
- S1. w_K := (K + 1)(θ̃^{k_s/8} + 2^{−k_s/16}) + μ_K replaces μ_K in m_i, (8.4)–(8.6), the sums of §8.7, and the stopping-scale bound. C_μ := θ̃^{−1}max(1, c(θ̃)), c(θ̃) = 1/(e log(1/θ̃)). For l ≥ x₀ := max(k_s/8 − 1, 0) and l = x₀ + t this gives lθ̃^l ≤ θ̃^{x₀}(x₀ + c(θ̃)) ≤ C_μ(k_s + 1)θ̃^{k_s/8}. So C_μ, C_τ, (T1), C_ν, and C_a do not depend on j(C). The factor K + 1 rather than k_s + 1 absorbs M5's generation factor k̄ ≤ K. The second kind of ν_j uses e^{−C_Pk_s/8} ≤ 2^{−k_s/16} for C_P ≥ 2.
- S2. This was closed by structure, not by a crossing bound. By LFR II p.377 l.5–7, every V-domain Y meets Z^∼ in whole components of Z^∼. A deep point of Y therefore brings its whole component of Λ_j^c into the polymer X′: as one of the X_{j_h} (p.387 l.41–43, p.388 l.2–3), or as a second-class Y_i contained in X′ (p.389 l.27–28). That component is old. So a polymer whose components are all young has no deep V(Y). The polymers with an old component are "Fine scales and old histories", or deep carried terms (LF §4(e)). The crossing-bound route was not used: d_{k,Z′} in (1.67) is measured in scale-k M-cubes, and the finer layers are thin in those units.
- M4. The structure differs from the reviewer's reading. The quotient 𝐓′_k(X) contains only V(X^∼) (LFR II (1.71), p.379 l.24–25). The factors V(Y), Y ∖ Z^∼ ≠ ∅, are outside it, in (1.91).
  - V(X^∼). Its collar variation is ≤ C_VC_hθ̃^{k_s/8}P_j(Z), by Cauchy's estimate against (1.69). The collar is one layer of the region's cubes (CRE p.245 l.41–43), so |collar|_j ≤ (3^d − 1)|Z_j ∩ Z|_j. Hence C_V := 2O(1)(1 + L^d + 3^d).
  - The factors V(Y). Cauchy's estimate is per factor, with the supremum r(Y) ≤ C_hθ̃^{k_s/8}, so no count of domains at a point enters. Each factor and its exponent give 4r(Y). |𝐃| ≤ e^{|𝐃|} is absorbed by eα. The bracket gains 4C_hθ̃^{k_s/8}.
- M1 (k_s in §§8.2, 8.4, 8.6, 8.7), M3 (C_S″ with (C^B_R/C_R)(2(1 + C_μ)C_∗C_sC_m + C_eC_Σ)), and M5 (Ē₀ := max(E₀, B₀, R₁), k̄ := max(k_s, j)) are applied as accepted.
- M6. The index range l ≥ k_s/8 − 1 is applied. The θ̃^{−1} in max e_m is moot, since w_K contains θ̃^{k_s/8} itself: max_{m>k_s/8}e_m ≤ C_ew_K.
- W6 is applied in §8.7.
- The consumer edits outside §8 (Status l.32, §6.2, §7, and the Constants entries of §8) went to the repair agent before 00:16. The repair agent reports them applied at 00:20, with W1–W5, W7, C1, C2, and M7.
- The LF note had the same S1 conflation. §4(e) used k/8 and k/4 with k the fluctuation step. It now uses the stopping scale k_s, defined at the head of (e). The deep-term bound is C_Dk̄Ē₀2^{−k_s/16} as in §8.6. *What changes in the Cauchy note.* now carries w_K and the x₀ lemma in place of the old C_μ := sup_Ksup_{m>k/8}mθ̃^m/μ_K. *Into the quotients.* points to *No deep V(Y) in a young polymer.* The §4(d) lines on non-deep domains use k_s/8. §5(e)'s b̄_K takes the repaired bracket with 4C_hθ̃^{k_s/8}.
- LF note Status and Open Gaps: β_π ≡ 0 replaces (10.6d)–(10.6e). (LF-A)(5) W_ext is derived (ad166, *The complex class of W_ext.*) and unreviewed. The (LF-W) line and the §5 headings reduce to the point (3) of (LF-A).

## Proposals of the LF Agents for the Cauchy Note

The (LF-W) agent appended §5 to the LF note (l.325–421 at its hash 228c6700b119). The (LF-A)(3) agent derived *The complex class.* and *The lift difference as a Taylor coefficient.* in §4(d) (hash 540fc40bccd0, 446 lines, with concurrent edits). Their proposals for the Cauchy note, accepted for the repair agent except where §8 is named:

- (W1) l.8: the ending "…, and the large-field dressings of the loop." becomes "…, and the large-field dressings of the loop at the R-operations with the loop."
- (W2) l.12: "Also missing are the large-field dressings of the loop." becomes "The large-field dressings of the loop are derived in that note's §5 except at the R-operations with the loop, which use these points through §8.6."
- (W3) l.128: "…(the continuum note's (9.3)): (γ) of the Open line." becomes "…(the continuum note's (9.3)): (γ) of the Open line; the dressings are derived in `WILSON_IT1_LARGE_FIELD_DEPTH_2026_10_27.md` §5 except at the R-operations with the loop."
- (W4) l.138: "the young pairs change F by ≤ 2B_Wδ_LFs_K through the numerators and the normalisation together" becomes "the young pairs change F by ≤ B_Wδ_LF(2s_K + s^{W,tot}_K) through the numerators and the normalisation together, with s^{W,tot}_K of `WILSON_IT1_LARGE_FIELD_DEPTH_2026_10_27.md` §5(f)"; "b^{(M)}_K := 3e^{−C_P⌊k/2⌋} + 2s_K," becomes "b^{(M)}_K := 3e^{−C_P⌊k/2⌋} + 2s_K + s^{W,tot}_K,".
- (W5) l.140: after "and s^{LF}_K = C_hθ̃^{k/2} is geometric, given (LF)" insert ", and s^{W,tot}_K is summable by that note's §5(f)"; "the large-field dressings by (LF), so (6.3) holds for the young pairs' numerators with B_Ws_K in place of s_K, which is the numerator part of the change 2B_Wδ_LFs_K above." becomes "the large-field dressings by `WILSON_IT1_LARGE_FIELD_DEPTH_2026_10_27.md` §5, (5.1)–(5.2), so (6.3) holds for the young pairs' numerators with B_W(s_K + s^{W,tot}_K) in place of s_K, which is the numerator part of the change B_Wδ_LF(2s_K + s^{W,tot}_K) above."
- (W6, §8, integrator) l.228: "the depth sources e_i ≤ C_eθ̃^i (§9 and §10.5)" becomes "the depth sources e_i ≤ C_eθ̃^i (§9, §10.5, and, at the large-field backgrounds of the young pairs, `WILSON_IT1_LARGE_FIELD_DEPTH_2026_10_27.md` §5(d), which enlarges C_e by C′_e)".
- (W7) l.697: "b^{(M)}_K := 3e^{−C_P⌊k/2⌋} + 2s_K (§6.2);" becomes "s^{W,tot}_K (the large-field dressings of the loop, the LF note's §5(f)), b^{(M)}_K := 3e^{−C_P⌊k/2⌋} + 2s_K + s^{W,tot}_K (§6.2);".
- (C1) After l.31, (T-Λ): add "- (T-c) The complex class (`WILSON_IT1_LARGE_FIELD_DEPTH_2026_10_27.md` §4(d), *The complex class.*): the conditions of (T-Λ) with 26ε₁′ in place of ε₁, where ε₁′ := C(M)R_k(ε_k + 60(α̂₀ + α̂₁) + 25g_kb_k) and α̂_i := max_{m≤k}α_{i,m}, and 1560(α̂₀ + α̂₁) ≤ min(α₁, α_J). It holds for γ small, uniformly in K."
- (C2) l.12: "What is missing is the points (2)–(5) of that note's (LF-A), all in its §4(d): the multiscale (10.6c); complex V for (LF-2); the nonlinear parts of the remainders V(ζ, ·) and V(ζ₀, ·); and the small form of (1.20)." becomes "What is missing is the points (3) and (5) of that note's (LF-A), both in its §4(d): the variation of the old terms V(Y) at the complex points of the class, the forms, the actions, d, and 𝐂_k − W_ext being derived on the class under (T-c); and the exterior part W_ext of 𝐂_k." The W_ext agent is still running; its result may change the second item.

## Ownership of the Repairs

- The repair agent applies every accepted repair outside §8 of the Cauchy note, the held edits of TRIAGE_R3's *Integrator Repairs and Launches*, and the proposals of the (LF-W) and (LF-A)(3) agents for the Cauchy note outside §8. It then prepares review packets for the repaired paragraphs.
- The integrator repairs §8 (s8b S1, S2, M1, M3–M6) and the LF note (after the W_ext agent finishes).
