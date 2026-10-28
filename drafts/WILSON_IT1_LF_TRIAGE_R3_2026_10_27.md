# Large-Field Note: Triage of the Third Review Round (27 October 2026)

Notes: `WILSON_IT1_LARGE_FIELD_DEPTH_2026_10_27.md` (the LF note) and `WILSON_IT1_CAUCHY_ESTIMATE_2026_10_27.md` (the Cauchy note). Reviewed at 209 lines (LF note, SHA256 beginning 3f159c6bca92) and 550 lines (Cauchy note, SHA256 beginning adf73889dc5b). At this triage, 21:54, the notes have 302 lines (LF note, LF endings, SHA256 beginning 93320f3c6852) and 659 lines (Cauchy note, LF endings, SHA256 beginning 542a8dc7ea9e). These revisions include the integrator's concurrent edits: the alignment, the Open Gaps list, the multiscale gauge-fixing bullet, and §4(e) of the LF note, and §10.3 and most of §10.4 of the Cauchy note.

Reviews (headless `claude -p`, `verification\isolated_reviewer\run_app_review_cli.ps1`):
- `lf-forms-20261027-r1`: LF §4(d). No fatal finding, five serious findings (S1–S5), and ten minor items.
- `lf-boundary-20261027-r1`: LF §4(e). No fatal finding, three serious findings (S1–S3), and nine minor items (M1–M9).
- `cauchy-gf-20261027-r1`: the gauge-fixing part of the Cauchy note's §10.4. No fatal or serious finding, and eight minor items (M1–M8).
- `cauchy-assembly-20261027-r1`: the J-term paragraph and the Assembly of the Cauchy note's §10.4. No fatal or serious finding, and seven minor items.

## Outcome

- The (1.2)-form is split exactly. The form of (1.2) is the second-order part of g_k^{−2}A(ζ₀, U_{k,Z}(V′V_Λ)), so it equals f(𝒜₁) − 2⟨𝒜₂, J(1 − ζ₀)⟩. The bulk form f is the action and constraint parts of the Cauchy note's §10.4 with the weight ζ₀; its multiscale defect β_f is derived through the chain rule layer by layer at the pair (Ũ, J′), J′ := 𝐐(Ũ)*λ^B. The part carried by the weight 1 − ζ₀ is open, as (LF-A)(5).
- The small form of (1.20) has the same split, with the weight ζ, the set 𝐁″_k(Z), and its multiplier λ″. Its first two terms are derived; the third, carried by 1 − ζ, is (LF-A)(5).
- The linear term of (1.2) is bounded directly. In each run it is (1/g_k)⟨𝒜₁, J(1 − ζ₀)⟩. At the pair its difference is a blocking-artifact term and a term in E, plus the alignment, with the per-point constant C_ℓ(M).
- The remainders V(ζ, ·) and V(ζ₀, ·) are reduced to a bound of the action difference D(B) on a complex B-ball, which is open, as (LF-A)(4). The claimed relative size C(ε/a_n) is withdrawn.
- V(Y)(ii) uses the layer's α_{1,m}, the age of the point's layer, and the room ρ(x) of the class. The room is open, as part of (LF-A)(3).
- A new gap is found in the terms in E. E's characterisation needs β(ℱ, 𝒜^B) for every ℱ ∈ ker Q^B. The π-part β_π then carries terms in G′RD*ℱ, which vanish only for Landau ℱ, and (10.6d) is stated at the two diagonal argument pairs only. The functional form of β_π is open even at a single scale, as (LF-A)(2). The integrator is deriving it after (10.6d).
- In the Cauchy note, the lifts paragraph gets the bound of (Q₁Q₁*)^{−1} at U^B by localisation and a Neumann series, with the decay rate δ_Q. §9 gets the standing conditions (9.0). The gauge-fixing constants are corrected (M1, M2, M7), and the transports of the identities are specified (M6, first half).

## Dispositions, Review lf-forms-20261027-r1

- **S1 (the alignment disc).** Holds. Addressed by the integrator's rewrite of the alignment: the class 𝒟̄ with the multiscale multipliers, the path in (U, J), and the factor c_al(ε/a_n)^{(1−ε₀)/3}ε₁. The former (LF-A)(1) is deleted. Under review in `lf-align-20261027-r1` and `cauchy-align-20261027-r1`.
- **S2 (the multiscale (10.6c)).** Holds. Addressed by the integrator's bullet "The multiscale gauge-fixing defect" in LF §4(d). The review of that bullet is in `lf-forms-20261027-r2`. The new gap in the functional form of β_π is (LF-A)(2).
- **S3 (complex V).** Holds. Open, as (LF-A)(3).
- **S4 (the remainders).** Holds. The claim C(ε/a_n) is withdrawn. The remainder is the third-order Taylor remainder of D(B) := Φ^A(B) − Φ^B(B), and a bound of D on a complex B-ball is open, as (LF-A)(4).
- **S5 (the 𝐑- and 𝐁-terms of older generations).** Holds. Addressed by the integrator's §4(e): "Deep terms", the norms over the non-deep terms, and the inward weight e^{−σ(m−i)}. In V(Y)(ii) the 𝐑- and 𝐁-counts are per point of the layer Γ_m.
- **The small form.** Holds. Repaired: the split of the small form, with the first two terms derived and the third open, as (LF-A)(5).
- **The linear term.** Holds. Repaired by the direct bound: the alignment through the divergence form, the artifact piece by (9.5) with the weight 1 − ζ₀ and the first variation of the weight-gradient sum, and the E-piece with |J^A(1 − ζ₀)| ≤ c_wε₁a_j^{−3}. The column sums of K are bounded by c_K.
- **The radius α_{1,k} and the age in (ii).** Holds. Repaired: α_{1,m} of (2.28), the allowance of (2.39), the age L^{−(5−β)(m−j)} of (3.67), and ε_k ≤ 2^{p₀}(1 + β₀)(k − m + 1)^{1/2}ε_m by (2.6). The room of the class is open, as part of (LF-A)(3).
- **N_k's normalisation.** Holds. Repaired earlier in the N_k bullet: the data measure a_{j′}^d cancels the a_{j′}^{−d} of (3.133).
- **The (1.2)-form defect omitted the weighted curvature and current pieces.** Holds. Repaired: the curvature piece of the weight-gradient sum and the current term, with c_w and B̄_J, in C_d.
- **The small-form misquote.** Holds. Repaired: O(1)B₃⁵B₅M⁵A₁²p₁²(g_k)ε_k|𝐁₀| (LFR II p.361 l.20). "Radius of (3.35)" no longer occurs.
- **C_F(M) and the complex-disc O(1).** Holds. Repaired: C_F(M) := C_d(2 + C_ζ) + (1 + c_f)(2x_E + x_E²) + c_4c_alε₁. The k-dependent ε₁ enters only through ε₁ ≤ 1 and (T-Λ), and c_4 bounds the forms on the disc.
- **x_E's C_r, "within 2ε", and the ζ-gradient choice.** Holds. Repaired earlier: max(C_r, 1), "within 4ε", the choice with h + 1 ≥ n stated.
- **The overloaded k.** Holds. Repaired earlier in the heading and intro of (d).
- **The per-Y form and the common t_□ contour.** Holds. Repaired: the statement holds for each V(Y), and the circle of RG II (1.22) depends on g_k|B| only. Where the runs' g_k differ, the smaller radius serves both.
- **The (LF-A) line "§4(d) derives the per-layer form of (10.6)".** Holds. Assigned to the integrator (Open Gaps list).

## Dispositions, Review lf-boundary-20261027-r1

All items are addressed by the integrator's rewrite of LF §4(e), and the rewrite is under review in `lf-boundary-20261027-r2`.
- **S1 (the age weight).** Holds. The weight is geometric, w_r ≤ C_We^{−σ(r−1)}, σ := min(3δκR, ⅛δ₀RM), under (⋆) σ ≥ (d + 1)log L + 1.
- **S2 (the scalar recursion).** Holds. The norms are taken over the non-deep terms, whose source is one number at each step.
- **S3 (the delimitation).** Holds. "Deep terms" delimits the open case: the deep terms are bounded at every generation or belong to an older component's integrand.
- **M1 (the measure (3.27)).** Holds. Repaired: 𝐁_k enters through the integrand and, multiplied by t, through (3.27); the step map uses R-mark.
- **M2 (evenness).** Holds. The claim no longer occurs.
- **M3 (the count L^{d(k+1−i)}).** Holds. Repaired: it stands in the recursion and is paid by W.
- **M4 (the coupling term and V^{(k)}(S_{k+1})).** Holds. Repaired: both are itemised, the coupling term through (2.24) and the window bound (W).
- **M5 (the widths and c_w).** Holds. Repaired in "The weights of the ages" (a).
- **M6 (C_w).** Holds. Repaired: C_w := Σ_r(L^de^{−σ})^r, with the inward generations on Γ_m.
- **M7 (the initial data).** Holds. Repaired: no initial data is needed, by "Deep terms".
- **M8 (citations).** Holds. Repaired: p.373 l.5–6, and LFR I (1.63) for the boundary terms of the preliminary integrations. At this triage the range "for some m ≥ j + 1" of LFR I (1.63) (p.189) is added.
- **M9 (C_T for old layers).** Holds. The constant no longer occurs: (i) uses Bałaban's O(ε_k) of p.277 l.7–9, ε_k^{*B} := 2C_XC_KPC_εε_k.

## Dispositions, Review cauchy-gf-20261027-r1

- **M1 (|r_A|).** Holds. Repaired: |r_A| ≤ (c_{g2} + 2c_{g6})𝔰, since r_A = Q′₁r_B + δr and τ̂ ≤ 2, propagated into s₁ and s₀.
- **M2 (c_{g7}).** Holds. Repaired: c_{g7} := d(1 + 2d)h_H + 4C_tr + 32d²(c_{g2} + 2c_{g6}) + B_G²(dB_G + 2c_{g5}). The term 4C_tr is the transport correction of two identities, and 32d² the link transport δ_T|r_A|, with ε²|F| ≤ ν_F.
- **M3 (the count of C_tr; the face term).** Holds. Assigned to the integrator (Transports paragraph): the face coefficient is 32d³, and the count of C_tr is to be written out.
- **M4 (the scales j ≤ 2).** Holds. Assigned to the integrator (the regularity paragraph before Transports): at j ≤ 2 the trivial bound osc ≤ 2 sup|∇𝒜| with ε/ℓ ≥ L^{−1}.
- **M5 (the d log correction).** Holds. Assigned to the integrator (Transports paragraph).
- **M6 (the transports of the identities; the axial tree).** Holds. The paths of Q′₁, θ, Q^{str}, and Q̂_f are specified in the Identities, with at most (d + 1)L ≤ 3dL fine bonds within ℓ¹-distance 4dε of y. The axial tree outside B(y) is assigned to the integrator (Transports paragraph).
- **M7 (the column sums).** Holds. Repaired: the kernels k₀, k₁ of X_f(ℱ) have absolute row sums ≤ C_trε|F|, vanish beyond ℓ^∞-distance 2ε, and so have column sums ≤ C_XC_trε|F|, C_X := (5L)^d. Hence |s₁| ≤ [C_ldc_{g7} + C_XC_tr(c_{g2} + 2c_{g6})]τ̂𝔰 and |s₀| ≤ C_XC_tr(c_{g2} + 2c_{g6})ν_Fℓ^{−1}𝔰.
- **M8 (R independent of a).** A remark. No change.

## Dispositions, Review cauchy-assembly-20261027-r1

- **(1) The lifts.** Holds. Repaired in the lifts paragraph after (10.5′). T := Q₁Q₁* has range r₀ and norm ≤ M̃_Q. By localisation in boxes of side R_Qε, the axial gauge in each box, and C_E/R_Q² ≤ m_Q/4, its spectrum lies in [m_Q/2, M̃_Q] under C_ax·d(R_Q + 3)C₀ε₁ ≤ m_Q/4. The Neumann series gives |T^{−1}(c, c′)| ≤ (2/m_Q)e^{−δ_Qd_ε(c,c′)}, and the weighted bound holds for δ₁ ≤ min(δ_Q, 1/(6d)), with C_Q and C_I := 2(1 + 2dL^{d−1})C_Q·max(C, 1). The change of the weight over 3dε is at most 4/3, covered by the factor 2 of C_ℒ′.
- **(2) §9's standing conditions.** Holds. Repaired: (9.0) ε₁ ≤ min(1, a₁, a₁′(2C₀/B₃)), C₀ε₁ ≤ 1, C_LC₀ε₁ ≤ a₀, with references in §9.2, §9.4, and §9.8; Mα₀ = C_LC₀ε₁ at M = R₁M₁ (PBG Theorem 3.1, p.397). The condition sentence of (10.6) is assigned to the integrator.
- **(3) The exponent 2γ_H.** Holds. Repaired in the lifts paragraph: h_H(γ) := 4^γB₀(γ)/B₀, so h_H(2γ_H) = 16^{γ_H}B₀(2γ_H)/B₀, with B₀(2γ_H) + B₀. The Polarisation paragraph is assigned to the integrator.
- **(4) "The three bounds".** Holds. Repaired: "the sup, gradient, and 4-cell oscillation bounds", in the sentence after (10.6b) and in the lifts paragraph.
- **(5)–(6) The J-term.** Superseded by the rewrite of the J-term paragraph (integrator).
- **(7) §10.3.** Holds. Addressed by the integrator's rewrite of §10.3; under review in `cauchy-align-20261027-r1`.

## Steps That Fail in Multiscale Form

- β_act^{ζ₀} + β_con: no failure. The chain rule C_B^{(2)}(𝒜) = C_A^{(2)}(Q₁𝒜) + Q^AC₁^{(2)}(𝒜) holds layer by layer, and the current term is bounded crudely with c_w and B̄_J.
- β_gf: no failure, given the integrator's multiscale gauge-fixing bullet.
- β_π: at run B's Landau lifts π_B vanishes, and (10.6d) carries δr, whose multiscale bound follows with the multiscale (G1)–(G3). E's characterisation needs β_π(ℱ, 𝒜^B) for every ℱ ∈ ker Q^B, which is not derived even at a single scale: (LF-A)(2).
- The weight: the part carried by 1 − ζ₀ (and 1 − ζ) fails because of the weight, not the multiscale form, since J(1 − ζ₀) need not annihilate ker Q and E₂ is not bounded: (LF-A)(5).

## Open Points

- (LF-A)(2): the functional form of β_π, which the terms in E need. What closes it: the sources of β_π(ℱ, 𝒜^B) through G′RD*ℱ, written as in (10.6c), by (G2) and (G3) applied to G′R.
- (LF-A)(3): complex V; and the room ρ(x) ≥ c_ρα_{1,m} of the chain's real configurations in the class (2.39), since LFR II (1.65) gives membership only. What closes it: §4(b)–(c) on the complex class, and the room from the bounds in the proof of (1.65).
- (LF-A)(4): a bound of D(B) on a complex B-ball of radius 2b_k, of relative size (ε/a_n)^{(1−ε₀)/3}.
- (LF-A)(5): the parts −2⟨𝒜₂, J(1 − ζ₀)⟩ and −2⟨𝒜₂, J(1 − ζ)⟩. What closes it: the sup and gradient bounds of 𝒜₂^B and a bound of E₂ := Q₁𝒜₂^B + C₁^{(2)}[𝒜^B, 𝒜^B] − 𝒜₂^A of the relative size of E.
- To check: the linear term g_k⟨DH″_{1,k,Z}B, ζη^{−2}Im∂U^0_{k,Z}⟩ of LFR II (1.20) (p.360) is not among the objects treated in LF §4(d).

## Notation Clashes

- C_L: l.248 of the Cauchy note uses C_L for the constant of CRE (3.12) (ε₁ ≤ C_Lε_k), and §9.8 for the constant of the linear average. (9.0) names the latter explicitly. A rename of one of them is proposed to the integrator.
- β′: the sum over the generations in V(Y)(ii) used 1/(1 − L^{−β′}), with β′ also the coefficient in log(ḡ^{−2} + β′k). It now reads 1/(1 − L^{−(5−β)}).
- m: in V(Y)(ii), m is the layer of the point, as in (e).

## Unreviewed Parts

- LF §4(d): the alignment (integrator), the multiscale gauge-fixing bullet (integrator), the (1.2)-form split, β_f, the current term, the terms in E for f^A with c_f, the result for the forms with c_4 and C_F(M), the small-form split, the linear term with C_ℓ(M), V(Y) with the common contour, and (ii) with α_{1,m} and the room.
- LF §4(e): the integrator's rewrite.
- Cauchy §10.3 and the β paragraphs (integrator), the functional form of β_π (integrator, in progress), the gauge-fixing repairs, the lifts paragraph, and (9.0).

## Next Reviews

Prepared, not launched, in `verification\isolated_reviewer\reviews\`:
- `lf-boundary-20261027-r2`: LF §4(e).
- `lf-profile-20261027-r1`: the profile by layers in LF §4(b).
- `lf-forms-20261027-r2`: LF §4(d) without the alignment.
- `cauchy-s8b-20261027-r1`: the boundary-term additions to the Cauchy note's §8.2(a), §8.4, §8.6, and §8.7, and the constants line.
- `cauchy-gf-20261027-r2`: the gauge-fixing part of §10.4 after the repairs, and the lifts paragraph.
- `lf-rs-20261027-r1`: the checks of (R-s) in LF §3(d), §4(d), and §4(e).
- `lf-align-20261027-r1`: the LF alignment bullet.
- `cauchy-align-20261027-r1`: the Cauchy note's §10.3 and the β paragraphs.

The packets are best launched after the integrator's functional form of β_π is in; `lf-forms-20261027-r2` and `cauchy-align-20261027-r1` depend on it.

## Integrator Repairs and Launches (27 October 2026, 22:40–23:45)

**Cauchy note: the double-bar repair.**
- §10.1 gains the bridge (B1)–(B5) between the plain M and PBG's double bar, from CMP 98 (89)–(100) and (121)–(126) and PBG pp.418–419.
- §9.4 gains the 𝒯 paragraph. §10.3 gains the ν paragraph. From §10.4 on, Q₁ := Q̄₁(U^B).
- The π-part is exact, (10.6d). The bound at the H₁^B pair is (10.6d′), and β_π = 0 at the ℒ-lifts. The functional form is (10.6e), of relative size τ̂ε₁L^{−3}.
- m_Q := 1/3 at U^B = 1 comes from the tent overlaps.
- Cauchy §8.6 now uses the LF note's whole-d comparison: ψ gains Σ_history h_n, and C_n := 2(1 + L^d)(3 + C_ψ).
- Renames: C′_ℒ → C^{pl}_ℒ, and ε₁ ≤ C_{ε₁}ε_k (the C_L clash).
- Hash at the launches: 30010adde8f1, 701 lines.

**LF note.**
- (LF-A)(2) is closed by Cauchy (10.6d)–(10.6e), at l.243 and in the four "uses (LF-A)(2)" places.
- aab7's *The complementary-weight parts.* bullet was verified line by line against LFR II pp.356–360, 364–370, and 377, and LFR I pp.195, 197, and 201. Two citation fixes: the w_e identity is Bałaban's (p.364 l.36–45, p.365 l.29–34), and p.358 l.24–30.
- Open Gaps now lists (3), the complex class, and (5), W_ext. (4) and the old (5) are covered by the comparison of d and 𝐂_k as wholes. The small-form and V sub-bullets of *The result for the forms.* are rewritten accordingly.
- The "≤ 3|δ_j| per plaquette" in Cauchy §8.6 is correct with the normalised trace.
- Hash: 1b054e434362, 317 lines.

**Reviews launched at 23:25–23:40**, all on the Cauchy note at 30010adde8f1:
- cauchy-bridge-20261027-r1 (new);
- cauchy-pi-20261027-r1 (new);
- cauchy-gf-20261027-r2 (refreshed for the double bar and m_Q);
- cauchy-align-20261027-r1 (the π-part removed, now Q1–Q6);
- cauchy-s8b-20261027-r1 (hashes refreshed).

**Held** until the LF agents finish: lf-boundary-r2, lf-profile-r1, lf-forms-r2, lf-rs-r1, and lf-align-r1. Also a new packet still to write: LF *The complementary-weight parts.* together with Cauchy §8.6's d-bullet.

**Agents running:**
- af3a: (LF-A)(3), the complex class. It was told about the double bar and the plain-E caveat for its Cauchy-in-t argument.
- a9be: (LF-W) §5. Its 23:4x report: the young-pair split moves to ⌊k/8⌋; the variation runs on the coarse side along §4(d)'s alignment path at equal data; the middle pairs use the triangle inequality; the R-operations reduce to (LF-A)(3)–(5).
- ad16: (LF-A)(5), W_ext, by the fundamental theorem of calculus on the common determining set 𝐁″_k. Deadline 01:15.

**Cauchy edits held** while the reviews read the file:
- C_X is used both for the domain count (l.166 and the constants list) and for (5L)^d (l.554, (10.6c), (10.6e)). Rename the latter C_{5L}.
- r₀ is used three ways: the LFR constant, the range of T (l.612–613), and the source of δJ. Rename the range r_T.
- Add to the constants list: M̃_Q, R_Q, C_E, C_ax, δ_Q, C_Q, and Q^{str}.
- Still to integrate, from the first agent's earlier proposals: the (3) wording, the (10.6) conditions sentence, §9.4 l.286, M3–M6, and the LF constants.

**If this session is lost:**
- Triage each `reviews\<rev>\review.md` above into a new LF_TRIAGE_R4 file.
- Verify the three agents' final messages against the files.
- Then apply the held edits and launch the held LF packets.
