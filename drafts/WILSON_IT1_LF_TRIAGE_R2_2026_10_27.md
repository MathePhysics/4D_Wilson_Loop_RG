# Large-Field Note: Triage of the Second Review Round (27 October 2026)

Notes: `WILSON_IT1_LARGE_FIELD_DEPTH_2026_10_27.md` (the LF note) and `WILSON_IT1_CAUCHY_ESTIMATE_2026_10_27.md` (the Cauchy note). Reviewed at 114 lines (LF note, SHA256 beginning aea5e91fc1eb) and 451 lines (Cauchy note, SHA256 beginning a74e3321cd96). Repaired at 209 lines (LF note, LF endings, SHA256 beginning 3f159c6bca92) and 550 lines (Cauchy note, LF endings, SHA256 beginning adf73889dc5b) (18:09).

Reviews (headless `claude -p`, `verification\isolated_reviewer\run_app_review_cli.ps1`):
- `lf-thresholds-20261027-r2a`: LF §3(b)–(d) (then the averaged thresholds and the reading (R-τ)) and the Cauchy note's uses. No fatal finding; ranked findings F1–F12, with N1–N3 among the step verdicts.
- `lf-depth-u0-20261027-r2b`: LF §4(b) (kernel sums) and §4(c) (the depth of U₀). No fatal finding, three serious findings ((b6), (c7), (c12)), and the minor items of its §4.

## Outcome

- The averaged thresholds and the reading (R-τ) are replaced by soft tests of width κ_s := β/30 and the reading (R-s), checked on every page where a test stands: CRE §§1 and 3, LFR I §1, and LFR II §1 (LF §3(d)).- §4(b) is now a multiscale bound with a pointwise profile, and §4(c) uses it. The result of §4(c) is per data point at its own scale, with C_h independent of K.
- Repairs beyond the two reviews: the gauge-fixing part of the Cauchy note's §10.4 ((10.6b) and its functional form (10.6c)), the Assembly of (10.6) through the two-sided bound (10.5′), and the J-term. They are not yet reviewed.
- Open: the boundary terms whose sources border holes older than the component (LF §4(e)), and (LF-W), the large-field dressings of the loop.

## Dispositions, Review r2a

- **F1 ((R-τ)(a) as worded).** Holds for the averaged device. The device is withdrawn. Its replacement, the soft tests of LF §3(d), needs no factorisation of the integrand through the tests. Clause (a) of (R-s) concerns only the removal of redundant tests on the plateau.
- **F2 (M₀).** Holds. Repaired in LF §3(d), LFR II p.378 l.10–14: M₀ := (1 + κ_s)O(1)B₅M⁶, the same in both runs. The denominator bounds of the Cauchy note's §8.6 hold for any fixed M₀.
- **F3 (δ′ omitted for the young pairs).** Holds. With the soft tests the per-test factor is δ^s_j/κ_s, stated in LF §3(d) "The result", and it contributes 2C/κ_s to C_h.
- **F4 (the dressed loop 𝒲).** Holds. Checked in LF §3(d): |𝒲| ≤ B_W uses the background's regularity, whose constants scale by 1 + κ_s.
- **F5 (the CRE §3 check unsupported).** Holds. Repaired: LF §3(d) checks CRE §3 page by page, including p.264 l.50–51, (3.9), (3.12)–(3.19), and p.269 l.45–50.
- **F6 (which tests carry factors).** Holds. Repaired: the device lists the soft tests by equation, and the radial, fluctuation, and gauge-fixing cutoffs that stay sharp.
- **F7 (the identity needs (b)).** Holds for the averaged device. For the soft tests every decomposition of unity is exact for any functions with values in [0, 1], so no redundancy is used.
- **F8 (the (3.19) misquote and the (3.7) boundary layer).** Holds. Repaired: the O(1) of (3.17)–(3.19) is restored, and the boundary-layer term 30d²L²B₃(1 + β₀)ε_k of (3.7) is treated.
- **F9 (the closeness at the enlarged support).** Holds. Repaired: LF §3(d) states the factor 1 + κ_s on C.
- **F10 (the wording of §3(b)'s negative result).** Holds. Repaired: "Lemma SH with a radial family does not work here."
- **F11 (the (LF) proviso for the summability of g_a²|δ_k|).** Holds. At the triage the Cauchy note's §3 and §7 still called b^{(S)}_K summable by (R-s) alone. Repaired: b^{(S)}_K is summable given the birth-scale form of (LF), its coupling part through (8.6). LF §3(d) states the same.
- **F12 (the cube sizes at a crossing).** Holds. Repaired in the Cauchy note's paragraph "The cube sizes at a crossing": both runs use R_j := R̄(K − j), R̄(n) the smallest power of L with R̄(n) ≥ 2(log(ḡ^{−2} + bn))^r. Every use of R_j in CRE §§1–3, LFR I pp.177–201, and LFR II pp.356–390 is checked against the properties of R̄. RG I and RG II use only the fixed R₁.
- **N3 (V4 cited through LF §3(b)–(c)).** Holds. Repaired: the Cauchy note's (β) paragraph attributes only Lemma SH to LF §3(b)–(c), and cites V4's lem:c5-5-5 directly. That lemma bounds the shell of one coordinate b under the conditional Gaussian (V4 l.2927–2937).
- **The step verdicts D1–D5, S1–S5, R1–R6, and T1–T9.** Their findings are F1–F11. The device they check is withdrawn, and its replacement is checked in full in LF §3(d).

## Dispositions, Review r2b

- **(b6) (the pointwise use of K for A₁*).** Holds. Repaired in LF §4(b): the residual is bounded pointwise, with the profile ρ(x) := C_G(ε₀)Σ_{y′}K(y, y′)(ε/a_{j′})^{1−ε₀}ε₁, the source's weight being ≤ 2(a_{j′}/ε)^{ε₀} times its supremum, as in the Cauchy note's §9.5. The decay across layers uses PRT2 (2.2) (p.224 l.10–13).
- **(c7) ("(b) applies with one layer").** Holds. Repaired: §4(c) uses the multiscale version of §4(b).
- **(c12) (a factor polylogarithmic in K put into C_h).** Holds. Repaired: the factor is polylogarithmic times linear in n, independent of K, and absorbed since θ̃ ≥ L^{−(1−ε₀)/4}.
- **(c3) (the polydisc radius; C_ℋ and C₁).** Holds. Repaired: P := {‖Y‖_∞ < 2C₁ε₁} with C₁′ := 4C₁ in VAR's hypothesis, and C_ℋ is independent of C₁.
- **(c11) (per component versus per point).** Holds. Repaired: each data point contributes at its own scale, summed with the decay by the count of §4(b). The data derivative is the H₁-type operator of (1.54).
- **(c10) (the intermediate scales).** Holds. Repaired: the data difference is bounded at every scale m of 𝐁″_k(Z) between h and k.
- **(b4) (PRT2 (2.2)).** Holds. Repaired: cited at p.224 l.10–13, with CRE p.256 l.21–24 for CRE's domains.
- **(c1) (LFR I Proposition 1, the V_Λ clash, and G₀).** Holds. Repaired: LFR I Proposition 1 (p.194 l.37–48) is cited, LFR I's V_Λ is identified with V′₀V_Λ, and LFR I's axial gauge in Λ^{(k)} with LFR II's G₀.
- **(c5) (constants on the segment).** Holds. Repaired: ε_k is the larger of the two runs' values, and C(M) ≥ 4C_X(M).
- **(c12) (the γ clash).** Holds. Repaired: the Hölder exponent is γ_H, and γ := sup_Kg_K.
- **The status lines.** Hold. Repaired: §4(b)–(c) are marked reviewed, repaired, and the repairs unreviewed.

## Notation Clashes Repaired

- κ: the soft width is κ_s. Bałaban's κ is his decay constant (LFR II pp.376–377, pp.388–389).
- γ: γ_H is the Hölder exponent of PBG (3.133) and (3.43).
- δ: δ_j is the coupling difference. Bałaban's threshold δ_k is ϑ_k (CRE p.265 l.39).
- C_T: the transport constant of the Cauchy note's §10.4 is C_tr := 1000d⁴. C_T := (1 − 1/T₀)^{−1} of §3 keeps its name.
- C_s: the bond load of (10.6c) is C_ld := 2 + 4dL^{d−1}. C_s of §8.7 keeps its name.
- The display labels of §10.4 and the Assembly are (G1), (G2), (G3), (A1), and (A2). A first choice, (Q), clashed with Bałaban's quotient.
- Bałaban's "[I]" in LFR II: "Sects. 6, 7 [I]" is RG II §§1–2, since RG I has §§0–5 only (LF §4(d), LFR II p.372 l.16–19, p.376 l.42).

## The Cauchy Note's §10.4 and the Assembly (Unreviewed)

- The earlier outline of the gauge-fixing part had three errors. It gave G′ as Δ_U^{−1}, against PBG (3.20)–(3.25). It claimed an exact Γ-cancellation for the divergence. It compared Q̂ against a restriction, although Q′ is an average. All three are replaced by the identities (i)–(iii), the transports, the commutator 𝔠, and (10.6b).
- The second-order claim on the E-term of (10.5) was not proved. It is replaced by the two-sided bound (10.5′), which uses only the sign ⟨E, G_A^{−1}E⟩ ≥ 0 on the diagonal. The E-characterisation after (10.5) is kept, since LF §4(d) uses it with (10.6c).
- The cube-gauge lift of §9.4 gives transport errors of order ε₁L^{−1}, which do not decay. The Assembly uses the lift with a gauge-covariant I, which keeps Q₁ℒ = 1, with the constant C_ℒ′.
- The J-term's projection step was not justified (E_b − 𝔓E_b need not be a gauge direction). It is replaced by (9.7) at scale j and (9.5) at scale a_j.
- The first transport count, 2048d³, omitted the weights L/ε of Q′₁D_B*. The count was redone by summation by parts and gives C_tr := 1000d⁴.
- (10.6c), the functional form of the gauge-fixing defect for a general ℱ, is new. LF §4(d) uses it layer by layer.
- Weak points for the review: the count C_tr; the load C_ld; the transfer of (10.6c) to the layer form in LF §4(d); the claims on the covariant lift (Q₁ℒ = 1, the regularity constant C_ℒ′, and B₀(γ_H) + B₀).

## Next Reviews

- Cauchy §10.4: (10.6b) and (10.6c).
- Cauchy §10.4: the Assembly with (10.5′), the lifts, and the J-term.
- LF §3(d): the soft tests and (R-s).
- LF §4(b)–(c): the repairs.
- LF §4(d), with the layer transfer of (10.6c).
- LF §4(e).
- The Cauchy note's cube-size paragraph (F12) and the uses of (LF).
