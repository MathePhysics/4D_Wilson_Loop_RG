# Triage R9: Third Referee Round of 28 October 2026

Reviews of the R8 repairs, launched by `run_app_review_cli.ps1` on claude-opus-5-5: lf-shell-beta-20261028-r2, cauchy-nd-20261028-r1, cauchy-lift-20261028-r4, and var-20261028-r4. All four have landed, and every report was read in full. The reviewers report the hashes 3b38676698e0… (LF note) and 8f7a3e6cc5c7… (Cauchy note), which match the packets. All dispositions below are applied. After the repairs the Cauchy note (`WILSON_IT1_CAUCHY_ESTIMATE_2026_10_27.md`) has SHA256 7a57630460b2… (932 lines) and the LF note (`WILSON_IT1_LARGE_FIELD_DEPTH_2026_10_27.md`) has SHA256 00d0bace3acd… (611 lines).

## cauchy-lift-20261028-r4 (Cauchy §5, the Lift, the Pair Line, and the Moment)

Verdict: no fatal point; four serious points (D5, B2, E1, C1/E3) and eight minor ones.

- D5, the closure of (J-δ): accepted. Separate C^{1,1} bounds for ℒA′* and A″ are false because of ℒ's fine pattern. Repair: the pair lift. G is evaluated at (ι_X𝐔, Q₁^{pl}(ι_X𝐔)*𝐉) with Q₁^{pl}(W) := dM, at the diagonal 𝐉 = J(U). The chain rule J(U^B) = Q₁^{pl}(U^B)*J′ with J′ := 𝒬(Ũ)*λ^B gives ΔJ = Q₁^{pl}(ι_XU^A)*δ𝐉 + [Q₁^{pl}(ι_XU^A) − Q₁^{pl}(U^B)]*J′, and sup_X|ΔJ| ≤ C_Jσ̂_{k,j}L^{3(j−k)} at every age, C_J := 2x_J + 1, under (16dc_br + 2c_Dc_v)L^{d−1}B_λε₁ ≤ 1. No second differences of the displacement enter. (J-δ) is closed given the localised lift. The current slot is O(p²) and Ĥ_{AJ}(q) = O(q), so the moment of the lifted term is unchanged. The lifted current obeys |Q₁^{pl}(W)*𝐉| ≤ C_{Q*}|𝐉|, C_{Q*} := 2(1 + (2d + 1)L^{d−1}), and the polydisc and class (a) take run A's current at r_{0,j}/C_{Q*}. Applied in §3, §5, §9.8, §10.5, the header, the Status, and the constants.
- B2, the localised moment: accepted. C_Π(j) := C′_Π(8B₃/α_{2,j})² is carried, with C_Π(j)ε₁² ≤ max(1, k − j), and E_V and the j-sum of (5.1v) carry it through C′_{β′}. The boundary-layer derivation rests on §9.8. Applied.
- E1 and C1/E3, the definition and tail of ι_X: accepted. The free-boundary object is outside VAR Theorem 1, whose setting needs dist(Ω_j^c, Ω_{j+1}) > RM₁L^jη (VAR (1), p.277). §9.8 is rewritten as **Open (the localised lift)**, with the closure route Ω₀ = X^∼, an inner Ω₁ at distance RM₁ε, collar data from a gauge-covariant local right inverse of the averaging, then VAR Theorem 1 and Proposition 9, and the tail through VAR (116) with PBG (3.42) at block scale ε. The rate is δ₀/2 and the gradient is in the scale of a_j: σ̂_{k,j} := σ_k + C(ε₀)ρ_k + C(ε₀, δ₀M₁)ε₁e^{−δ₀M₁L^j/2}. The header's open line names the localised lift in place of (J-δ). Applied.
- A3: the tail carries ε₁. Applied.
- C4/C5/G1: C_X added to the per-point bounds; E_V in the constants synchronised with (5.1v). Applied.
- B1: "equals Δβ_j" replaced by the moment defect. Applied.
- D3: obsolete under the pair lift.
- D4: obsolete; the factor of the replaced (J-δ) bound no longer appears.
- E2/E4: the citations of the M₁ layer and of CMP 98 (11) corrected. Applied.
- F3, the constant 96: rechecked. The weight changes by at most 2ε/a_j between a coarse plaquette and the fine plaquettes of its cell, and the fine action on the support of h_z is at most 192C₀²ε₁²L^{4(j−k)}, so the weight-change part is at most 384C₀²(ε/a)ε₁²L^{3(j−k)}. C_A′ := C_A + 16C_b + 384C₀² in §5 and in the constants. Applied.
- Further, found in the stale-string check: the covariance and the analyticity sentences of the Statement and the open line of (5.1c) now name the pair-lift term G instead of 𝐄^B∘ι_X. Applied.

## cauchy-nd-20261028-r1 (Cauchy §5, the Near Domain and the Constant)

Verdict: no fatal or serious point; ten minor ones.

- 1–2, the open set (R-Δ^c-T): accepted. The points with n = j are closed by *Mixed radii* and are removed from the open set; the case m = 0, □₀ meeting Ω₁^c, is added to it (no class bound there, and the count via |Γ_m| of (2.43) does not apply). Applied in l.14, l.128, and l.140.
- 3: the complex version of (I.3.26), which RG I does not prove separately, is labelled a reading; "(I.1.11) for U, (I.1.14) for 𝐔". Applied.
- 4: the output citations (I.3.37)/(I.3.50), (I.3.41)–(I.3.52), and (I.3.38). Applied.
- 5: β_C = 1/8 set against CRE's "not too small" through the same check as β = 1/8 of the LF note. Applied.
- 6: the m-monotonicity at (I.3.51)–(I.3.52) restated, the α₃-term being m-independent. Applied.
- 7: C_loc's transfer goes through α_{0,n}/α_{2,j} ≤ c₂^{−1}(1 + β₀)²max(1, n − j)^{1/2}, absorbed by C_{β′}. Applied.
- 8: the factor g_k in α_{3,k}. Applied.
- 9: the stale constants entry C := 11 removed. Applied.
- 10, an observation for the callers: Lemma 4's output must also lie in run B's space through the pair lift, which is the lift condition at the composites (open). A paragraph after *Mixed radii* says so. Applied.

## lf-shell-beta-20261028-r2 (LF §3(d), the Soft χ̄ Shell, and β = 1/8)

Verdict: no fatal or serious point; six minor ones. The dispositions were applied in the R8 working round of the LF note's §3 and §2(b): the stale l.164 and the sharp label of the soft (1.27) at l.139 corrected; the p.378 ½-inference kept open as "p.378 at the soft thresholds"; the §2(b) pointer to the numerator factor's shell; the dependence list of C_χ; the soft-support wording at l.329.

## var-20261028-r4 (LF §4(d), the Functions of the Configurations)

Verdict: no fatal point; five serious points (S1–S5) and ten minor ones.

- S1, the domain of the lifts: accepted. ι_X carries run A's data only on X^∼, while the re-summed terms read □₀ and Y_4. Repair: one lift for all terms of V(Y), ι_Y, the localised lift of the Cauchy note's §9.8 with Y^∼ in place of X^∼ (open with §9.8). The regions □₀ and Y_4 lie in Y, since V(Y) is a function of the configuration on Y ((1.68)–(1.69) on Ũ^c_k(Y, α̃₀, α̃₁), p.377 l.8–19). So D = M^·(ι_Yc^A) = M^·(c^A) on □₀, and the joint line moves one field 𝐒_c per member. The lift change ℓ_X between ι_Y and ι_X on X is added to r_z. Applied in (i), (ii), (iii), (iv), and *The Fine Side at Complex Points*.
- S2, r_z at the members of 𝒞: accepted as open. There the partner of renG(X, c^A) is run B's term at ι_Yc^A, which is not a local minimiser of run B, so the device of (5.1v) does not apply. The moment defect summed over the generations is a fixed multiple of E₀ε₁² per point, and the lift change is worse by the count. Check of the reviewer's claim that the blocking artifact is fine: it is small only after the sum over z at one configuration, Σ_zb_{h_z} = b_1, since its weight-change part is 384C₀²(ε/a_j)ε₁² per point per generation; this is stated. **Open: r_z at the members of 𝒞 read inside V(Y)**, with the closure: an age bound of run B's renormalised terms at the lifted chain, or a localised lift whose moment defect and tail decay in the layer of z. At the composites and the representation configurations r_z is inside the groups (iv) and (α); for the completions at U_k the grouping is the Cauchy note's variation group itself. Applied.
- S3, (iv): accepted. (iv) := renB(X, U^B_{j+1}(□₀, D)) − renG(X, U^A_j(□₀, D)) is the Cauchy group and contains r_z at the composites; the age is (L^{j−n})^{4+β′/2} per scale-j point at z ∈ Ω_n ∖ Ω_{n+1}, with r_{0,n}. Status: derived given the localised lift, the lift condition at the composites, (R-Δ^c-T), and the multiscale fine side. Applied.
- S4, completeness: accepted. The evaluation list of (i) adds the representation configurations of (1.61)–(1.63) and the later-stage configurations for X ⊂ Z^c (p.373 l.2–6, p.372 l.27–33, p.373 l.10–11, checked against the transcription). V^B(Y)[c] has one entry per member; terms that read a member as such read the entry, with their counterterms, and every other configuration is a link image, run B's map or local minimisation at the entries. The piece list adds (α), the variation group at the representation configurations, (β), the propagators of the localisation expansions, and (δ), the nonlinearity of the lift at the decoupled configurations of (1.60), all open; "four pieces" is replaced by the list. Applied.
- S5, the transfer map: accepted. The two runs' propagators act into T_ε and T_{ε/L} (RG II p.5 l.6–7). For (1.59) the comparison is at the composites' coarse data Q(η𝐇″_k); for (1.60) it carries the nonlinearity (δ). (W-δ) is restated through the transfers of `WILSON_IT1_WALK_FACTOR_DIFFERENCE_2026_10_28.md`, and the resolvent-identity closure is replaced by that note's reduction to (Wδ-1)–(Wδ-3), with the one plain line that the resolvent identity with a kernel bound of δ𝒪 doesn't work. "(i) at the decoupled configurations is part of (iii)" is withdrawn; (i) there is a separate open item. Applied.
- Minors:
  - L_0² ≤ L/3 (LFR I p.191 l.35, checked) replaces L_0 < L/2. Applied.
  - p.372 l.12–13 for the quote and p.372 l.15–19 for the expansion (checked). Applied.
  - "common lattice" replaced by "scale-k objects (RG II p.3 l.14–17 and l.27–33)", checked; the s-factor citation is p.3 l.30–32. Applied.
  - Analyticity in the operators: RG II p.3 l.2–3 gives D and 𝐀₀ as functionals of the operators, and p.6 l.44–45 analyticity in (𝐔, 𝐉) only (checked); analyticity in the operators is now part of the open (iii). Applied.
  - "by *The Room*" restricted to U^0_k and U_k in run A's half of the norm class. Applied.
  - 𝔪 = 2d̄′: the real points of the disc are regular with 2ε₁′, so 𝔪 = 2d̄′ and 𝔡 := 4d̄′^{15/16}; the same correction for 𝐒_c gives 𝔰 := 4σ_c′^{15/16}, and the prefactor of *The Ratio* is 4. Applied.
  - The layer of (1.66): (1.66) imposes the scale-j thresholds on the determining-set configurations U_{p,X}(M^·(𝕌)) as well (p.190 l.18, l.38–48, checked). Applied.
  - "And and"; U″_k and U_2 no longer called intermediate configurations; "almost the same" attributed to the extended functions (1.63) and (1.62) (p.375 l.1–13, checked). Applied.
  - The fourth open input gets a closure route: a check of the steps of the proof of (1.65), that of (1.89) [IV], at the halved thresholds, which pass through these configurations; the check at U″_k, U_1, U_2, and U_{k,Λ} is unchecked. Applied.
  - supp h_z ⊂ X^∼ ⊂ Y^∼ and the single counterterm configuration are stated. Applied.
- Also applied: the current of the line uses the frozen-current split with the pair-lift currents, derived at the single-scale real minimisers given the localised lift and open at the other members; the room at real points moves the configurations with the currents frozen; the lift condition of (i) is derived at the single-scale real minimisers given the localised lift, the pair lift's current included; Open Gaps item (3) lists ι_Y, r_z, (iv) with (α), (β) with (δ), and the closure of the conditions at the other configurations.

## Pending

- The walk-factor note (`WILSON_IT1_WALK_FACTOR_DIFFERENCE_2026_10_28.md`) now takes ℒ_ι := dι_Y in (Wδ-2), its fine form (c), and its §4(b), with the regularity of dι_Y resting on the Cauchy note's §9.8, and it says that the piece (δ) is not covered by (W-δ). Applied after the launch of the reviews.
- New reviews: the Cauchy pair lift and current (§3, §5), the Cauchy §9.8, and the LF §4(d) items (i)–(iv).
