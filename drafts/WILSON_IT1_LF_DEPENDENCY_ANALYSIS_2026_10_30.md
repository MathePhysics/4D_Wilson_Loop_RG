# The Input (LF): Dependency Graph and What the Main Proof Needs

Own working note. It analyses the large-field input (LF) of `WILSON_IT1_CAUCHY_ESTIMATE_2026_10_27.md` as the LF note (`WILSON_IT1_LARGE_FIELD_DEPTH_2026_10_27.md`) states it, and the repair sections §§40–72 of `WILSON_IT1_LF_GAMMA_REPAIR_ATTEMPTS_2026_10_28.md`. "Needed" means that the main proof uses the content, traced from the consumer down; it is not decided by label searches. Bałaban is cited by printed page and line on the transcriptions in `Balaban\tex\LFR2\parts`.

## Open Gaps That Gate Everything Below

- **(W-δ), the walk-factor difference** (`WILSON_IT1_WALK_FACTOR_DIFFERENCE_2026_10_28.md`): (Wδ-1), the per-shell bilinear defect of PBG's local operators G′_□, C_□, and G_□ on two fine lattices, whose coarse side that note's §10 derives (not yet reviewed in its current form); (Wδ-2), the fine side at the decoupled field, whose lift regularity at the real and the complex chain configurations §10.5 derives, with the Hölder bound, the inclusion in Ω₁(Y^∼), exact (S) at the aligned pair (ι_Yc^A, c^A), the data derivative through CMP 99 (1.30)–(1.31), and the removal of the gauge term, which leaves the value of (δ) unchanged and, written at the transformed pair lift, puts into (δ) a commutator with the pair-lift current defect, a second-order rotation of B, and the second-order part of the gauge factor (the complex step, through a cut-off complex axial gauge on the scale R₀M₀L^{n−1}ε about each coarse site, one covariant Hölder quotient, and PBG's (3.130)–(3.133) and proof of Theorem 3.12 rerun at the complex background for G, H, G₁, and H₁, repaired after two reviews and not yet re-reviewed); and (Wδ-3), the two runs' fixed points D and 𝐀₀ of RG II (1.3)–(1.4), for which that note's §11 derives, through the global lift of the Cauchy note's §10.4, exact identities. The D difference is the one-step remainder. The linear coordinates differ by a propagator term and a quadratic kernel term R₁, which, like the D difference, carries the factor L^{−j(x)} ≤ L^{1−k/2} of the layer on the young histories. 𝐀₀'s difference satisfies a contraction. The identity V = T₃𝔉 holds on all of VAR's set (77), with 𝔉 the action itself, since RG II (1.4) uses VAR's (80) with Δ in place of Δ_π (VAR p.297); so σ has no Landau parts. The global sets of the two runs are aligned. §11's global lift is bridged to the consumer's ℒ_ι := dι_Y. Both are right inverses of the same Q₁ that reproduce affine fields, so their difference carries (ε/a_j)^{β₂}. The term G̃Δ^{(2)}H₀B of VAR (180) is bounded through an exact identity. The E-terms of σ carry the small factor δ_w + ϑ_ℒ + C₂L²L^{1−k/2}. The gradient of the term G̃DRD*E follows from PBG (3.44) with a crude lattice Hölder bound, at the exponent less an arbitrary β′ > 0. The blocking artifact beyond second order is a sum of cell covariances with one oscillation factor each, so it carries (ε/a_j)^{β_H}. So (Wδ-3), and with it (W-δ), is derived, not reviewed in its current form. It gates the piece (iii) of point (3) (the LF note's l.557 and l.580), all of point (7) (l.25–26), and point (10), which waits for §3(d) and (3) (l.29). Of §§40–72, only 72.3 touches it, through the far-term current part of (δ).
- **The propagators of the localisation expansions (1.61)–(1.64)** (the LF note's (β) of l.17; not the threshold shells of §1 below): the W-δ note's §12 reduces them to §§3–11 on the layers at shared scales ≥ 1 (derived, not reviewed). 𝐇_k is VAR's Sect. G function with (179)–(180). 𝐇″_k is VAR's Sects. D–E function (111)–(112) about the non-critical U_{1,2}, with 𝔊 of PBG (3.148), H₁, and the current J_{1,2}, and 𝐇_{𝐁₁} is taken in the (111) form as well (a choice of representation; Bałaban prints none); §11's *The Sects. D–E form (111).* covers both. The gauge transformations differ by a scale-0 factor of size (ε/a_j)|𝐇^B|. Bałaban's regularity of U_{1,2} near the cut (p.370 l.35–38) is used as he states it; it is the open U_{1,2} item of §2.4. **Open:** the collar 𝐁_h(Ω″^∼_{h+1}) of 𝐁₁ has layers down to the finest scale near the cut (CRE p.256 l.57–62; the LF note's l.196), so the runs' problems are not aligned there and the young-history factor is lost; the collar also enters 𝐇″_k through the source 𝐆″_k(1 − θ)Q*_{𝐁₁}θ₁H*_{𝐁₁}J₁ of LFR II (1.55); the sets 𝐁(Y_i) of the boundary layers are CRE's 𝐁(Ω) (CRE p.257 l.22–26) and have finest-scale strips with no run-A counterpart; PBG Corollary 3.6 needs the width of 𝐁″_k's middle layers.
- **Point (6)**: the π-part of β for multiscale data and the twist term 2⟨B̃₂, ν₀⟩ at interface blocks; untouched by §§40–72.
- **Point (10)**: the creation difference of the R-operation's boundary terms 𝔹_k^{(n)}; it waits for (3) and for the marked expansion of the Cauchy note's (8.1).

These four are the hard core of (LF). If (W-δ) fails, points (3), (7), and (10) fail with it.

## 1. The Top of the Graph

The main proof consumes (LF) in two places, both through one per-point rate s^{LF}_n ≤ C_hθ̃^n at the birth scale n of a large-field component:
- (LF-1): the young matched pairs of the Cauchy note's §6.2, components born at a scale > k/2 (the old ones are removed in each run at the cost e^{−C_P⌊k/2⌋}δ_LF, summable in K);
- (LF-2): the renormalisation quotients of the Cauchy note's §8.6 at the coarse histories.

The comparison cannot be replaced by the triangle inequality: a young component is born at a coarse scale, where the coupling is the fixed physical one, so its large-field suppression does not decay in K. A young component that persists for N₀ steps meets an R-operation, so the R-operation's ingredients (U_{𝐁″}, U₀, V(Y), and the boundary terms 𝐁) are needed.

(LF) splits into the threshold shells (derived, LF note §3(d)) and the integrands. The integrands are derived except the points (3), (6), (7), and (10) of (LF-A), and (11), which §46 treats (not reviewed).

## 2. Point (3): The Variation of V(Y)

Point (3) is the variation of V(Y) between the runs. The LF note splits it, through the intermediate V^B(Y)[ι_Yc^A], into the variation (ii) along the joint line, which is run B's function only, and the frozen and comparison pieces (i), (iii), (iv), (α), (β), and (δ). §§44–72 work almost entirely inside this point, on the conditions of LFR I (1.64)–(1.69) at the configurations that the terms read (the LF note's l.18–20 and l.536–543) and on the near-domain age bound (5.1c).

### 2.1 What Bałaban States, and What It Covers

- LFR II (1.65) (p.375 l.16–22), with l.24–35: the extended function U^0_k is analytic on Ũ^c_k(Y₄, α̃₀, α̃₁) with values in Ũ″^c_k(Y₁, α̃₀, α̃₁); that space "is contained in the analyticity domain of the term 𝐄(X) we consider, hence in the analyticity domains of all terms in the obtained effective action". It concerns the one composite U^0_k(𝐔, 𝐉) at points of Ũ^c_k(Y₄), as the LF note's l.20 says. It says nothing about U_{k,Λ}, U_1, U_2, or U_{1,2} as backgrounds of the terms, and no complex domain of the localisation parameters s is printed.
- LFR II p.375 l.1–15: the regularity of U_{k,Λ} and U_1 is "almost the same" as at the corresponding minimisers. Bałaban marks this as qualitative: "A precise description of the regularity properties is given by the following statement" (l.14), namely (1.65).
- LFR II p.370 l.35–38: U_{1,2} "is regular, and satisfies the regularity conditions typical for an h-order configuration" on the band (Ω″_{h+1})^c ∩ Ω″^{∼2}_{h+1}. It gives no room, no current bound, nothing for U_2 off the band or at the junction, and nothing for case (ii) of LFR I (1.66)–(1.67).
- LFR II p.373 l.2–3: the second set of expressions depends "analytically on the background field U_{1,2}". It states no condition at U_{1,2} or U_2.

So these passages are quoted inputs only for U^0_k at points of its class. They do not replace the conditions that §§49, 59–61 derive at U_{k,Λ}, U_1, U_2, and U_{1,2}.

### 2.2 The Configurations the Terms Read

The terms of V(Y) are evaluated at three kinds of configuration:
- Bałaban's composite U^0_k(𝐔, 𝐉) at a point of its class, covered by (1.65);
- the other members of the chain (U″_k, U_{1,2}, U_{k,Λ}, U_1, and U_k) as backgrounds of the terms, which LFR II re-expands around U_1 and U_{k,Λ} (p.373 l.3–6), and their lifts ι into run B's spaces;
- the interior and complex points of the joint line, c(t) = (e^{it(ε/L)𝐒_c}c^B)_{c∈𝒞} (the LF note's l.459), which moves each member separately, and the configurations U(𝐁(Y_i), D(t, s)) built from them (54.1, 68.2). These are not of the form U^0_k(𝐔, 𝐉) for any (𝐔, 𝐉).

Only the first kind is covered by Bałaban's statement. The second needs §§49, 53, 59–61 (with §50 and 56.4 at U_{1,2}); the third needs §§54, 65, 67, and 68.

The near-domain bound (5.1c) under R-data (55.1): a near term at 𝐔 reads only P_n𝐔 = U_n(□₀, M^·(𝐔)), so where □₀ lies relative to the boundary of a minimisation domain plays no role. The inputs of 64.2 at 𝐔 itself on □₀ remain: (I.1.11), the plaquette part of (I.1.14) with the room of the class, (ii), (iv) by (1.17), and condition (a) at 𝐔, with its current, for the far terms. They are derived at real points (64.2); the complex points rest on 68.4. At configurations that are not local minimisers on □₀, the identity irr(Δ)(𝐔) = D_Ŵ is the definition by R-data and the clause of 62.3, justified by 66.1's total and resting on the per-domain pieces of 47.3, whose term properties are open.

### 2.3 Sections Not Needed

- §48 and 57.2: 64.5 shows that the glued member's membership in 𝒮_z and the current condition of 57.2 are not inputs of 44.6. Both are in `WILSON_IT1_LF_GAMMA_ARCHIVE_2026_10_30.md`. The facts of 48.1 that other sections cite (the outer-shell data, Lemma 4's membership on X only, and the difference from the global minimiser) are in 57.1, and 57.1, 57.3, and 57.4 stay.
- §53 stays. The member identities are printed (LFR II p.373 l.20 and l.39, p.374 l.16), but 53.2 adds the support on Y_i and the gauge transformations of VAR (4), which 64.3, §65 (the endpoint data D(0)), and §67 use.

### 2.4 Sections That Are Needed

Every other section of §§44–72 is used by the main proof's chain. In particular:
- the conditions at the members: §49 (49.2–49.5), §53's conditions part, §59, §60, and 61.2–61.6, through 62.2, 64.3, 66.1, 66.3, and 68.2 (66.5 lists them as inputs of 66.1);
- condition (a) and the lift condition at U_{1,2}: §50 and 56.4, through 62.2, 62.4, and 66.1;
- the line's interior and complex points: §54, 65.2–65.3, §67, and 68.2–68.4, through the analyticity of f(t) = V^B(Y)[c(t)] on |t| < 1/r(Y), 66.1's sums over z, 66.4, and 72.2;
- R-data, the clause, and 66.1: 55.1, 62.2–62.4, 64.2–64.5, 66.1, §44 (44.2 and 44.7), 52.1, and Lemmas A and B of §51;
- (5.1c) for the difference: §63 with §46, 66.2, and §71;
- the lift: §69 and (δ) (§72);
- the variation groups (§70) and the counterterm of a point (§45, §47).

The open items of these sections are gaps of the main proof, including the case (ii) of (1.66)–(1.67) at U_2 when h > k₀ (§60), the collar points near Λ (49.4, which 64.3 relies on), 65.4, 67.5, and the conditions at U_{1,2} near the cut (§62).

§§40–43 serve the marked mixed-integral estimate behind point (10) and stay needed with it.

## 3. Recommendation

- No referee waves on the archived §48 and 57.2.
- Keep the other sections of §§44–72. Their referee waves continue at the rate of one wave per usage window, after the work on the gating items.
- Put the main work on (W-δ): the review of the W-δ note's §10 (the coarse side of (Wδ-1)), then (Wδ-2) and (Wδ-3); then the propagators of (1.61)–(1.64) and point (6). Without them points (3), (7), and (10) stay open, whatever happens to the configuration items.

## 4. What This Analysis Does Not Settle

- It does not trace the claim that a young component which persists N₀ steps meets an R-operation.
- §46 is cited as treating point (11) and is not reviewed.
