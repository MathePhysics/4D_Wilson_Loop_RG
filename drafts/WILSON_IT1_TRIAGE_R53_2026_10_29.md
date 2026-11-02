# Triage R53: Re-Reviews of Everything Not Re-Reviewed (29 October 2026)

User: "Run rereviews on everything"; "Ignore the LF \gamma work that is being done by a different agent".

Packets: verification\isolated_reviewer\build_round53_rereview_packets_20261029.py, 48 folders reviews\<rev>\ (rev ending -20261029-rN). Referee: claude-opus-5-5, effort high, through run_app_review_cli.ps1. Each section below is written when its review lands: verdict, findings by rank, and the disposition of each (repaired where, or why not).

## Waves

- Wave 1, launched 00:36: it1-o4-20261029-r3, it1-d27-20261029-r4, it1-cont-20261029-r3, it1-d27-early-20261029-r2, it1-coarse-20261029-r2, it1-bg-20261029-r2, it1-o6-20261029-r2, it1-class-20261029-r2.
- Wave B, launched 01:05 and relaunched at 01:33 after a session restart: it1-d2-r45-20261029-r2, it1-o2-20261029-r2, it1-o2prime-20261029-r2, it1-d2-rep-20261029-r6. The packets were built before the D27, continuum, and map edits of 01:07–01:49.
- At 02:13 the 36 unlaunched packets were rebuilt after the edits of 01:07–02:12 to the map and the D27, continuum, O6, O4, O2, O2′, and D2.6 notes.
- Wave C, launched 02:13: it1-rc-p6f-20261029-r7, it1-rh-20261029-r6, it1-d24-12-20261029-r1, it1-d24-13-20261029-r1, it1-sw-20261029-r1, it1-d22-6c-20261029-r1. All six exited with 1 at 02:17–02:18 without a review: cli.stdout reads "You've hit your session limit · resets 2:30am (Europe/London)". To be relaunched after the reset with the same packets.
- Wave C relaunched at 02:31:55 with the same packets; all six reviews landed 02:41–02:50. The user then asked for fewer waves per 5-hour window, so the next wave (D) waits for the next window, with its packets rebuilt first.

## it1-class-20261029-r2 (landed 00:48, triaged 00:48–00:53)

Verdict: no fatal finding, one serious, eight minor. Class (i) is closed by the split route. Class (ii) rested on the Premise, which read CRE p.254's "coincides" as an identity of functions.

- *Serious (P1).* Accepted. The cutoffs and covariances differ: CRE (1.18) on p.250 uses cube tests with threshold g₀^{−1}δ₀, RG1 (2.9) on p.266 uses a single-bond ε₁, and CRE uses the restricted C^{(0)}(Λ₁). So the sentence is no longer used as an identity. Repaired by deriving the width that the step needs. At step 1 there is no earlier 𝐄 (CRE (1.26), p.253), so RG2 Lemma 1 and its α₂-condition do not act. The 𝐏-terms are analytic on absolute widths α₀′ and α₁′ (RG2 p.10, read). C^{(0)}(Λ₁) is a restricted covariance of the kind C^{(k)}(Z₀) that RG2 already uses (pp.12–13, read). The cube tests act on the integration variable only. They enter through (2.22), with a per-cube bond count, and through Lemma 3's condition, which becomes (1/20)γ₂r₀² ≥ 18κ + log|(□′^{∼2})*| with r₀ = (A₁/A₀)(log g₀^{−2})^{p₀} (CRE p.247, p.265). Accepted input: Bałaban's treatment of the exterior coupling (CRE pp.253–254, the k = 0 instance of R-I7, already accepted in the map). Changed: Premise l.5–9, header l.3, b1, Constant Conditions, Sources, and the lists of what is Bałaban's and what is derived; map l.113 and l.166.
- *Minors.* All applied.
  - "p.280, Theorem" is replaced by RG1 p.263 l.24–25 and Theorem 3 (p.264).
  - RG2 p.7 is cited through (I.3.31).
  - "verified from the print" is removed for CRE p.276.
  - The 𝐑₁ absence is now marked as D2.7's open check in the header, b1, and the map.
  - a8 is marked as not independent evidence.
  - "in A" replaces "in the scaled field" in b5(1) and the map.
  - The Premise's pages are added to Sources Read.
  - The obsolete 𝐑₁ input is removed from the list of what is Bałaban's.
- Packet note: the map's l.199 under `argument` was a wrong locator in the packet. Nothing in the note or map needs changing for it.
- Hashes at 00:53: class note 99 lines, 7aa296747dee; map 1614 lines, 94110c006f29.

## it1-bg-20261029-r2 (landed 00:49, triaged 00:53–00:57)

Verdict: no fatal finding, two serious, eight minor. The reorganisation is sound. Two claims are not: (iv-b)'s w_K and the k = K order of the crude R_bad bound.

- *Serious 1 ((iv-b) w_K).* Accepted.
  - CRE (2.6) gives the opposite inequality. The lower bound on the running is ONE_LOOP_PROOFS Lemma 2.1(i) (read): g_k^{−2} ≥ g_K^{−2} + b(K−k) − C.
  - The j-sum was re-derived. Split at bx = G′ and use convexity, log(1+t) ≥ t/2, and the tail with s = 2p₀(log G′)^{p₀−1} ≥ 2. Result: Σ ≤ (5/4 + 2G′/(p₀b(log G′)^{p₀−1}))e^{−2(log G′)^{p₀}}, which agrees with the review's order and still tends to 0 uniformly in K.
  - The creation-position count under a scale-K cube is now stated as open, with what closes it. It was not Bałaban's: (1.80) pays future sums only, and its K is a component's lifetime.
  - Changed in (iv-b), §3.4, header l.3, and map l.161 and l.165.
- *Serious 2 (R_bad's order at k = K).* Accepted. 1/κ_f^{(K)} carries the unbounded perimeter self-energy. *The complement* now says that the crude bound is never of the right order for the fine part. §3.4 gives the ℒ_K bound κ_f^{(K)}N_tube(C·w_K^f + e^{Re E^f_{const,K}}w_K^{(0)}). §3.4's label is now "derived given (iv-b) for the fine chain and the fine D(K) form on ℒ_K". Map l.165 says the same.
- *Minors.* All applied.
  - l.11 now names R_bad and 𝔏_good.
  - There is one coarse-loop definition, §1.6's block-field function, in l.9 and in §3.4's g_K^{(K)}.
  - §3.3's nesting is corrected (scale-k₁ blocks contain the scale-k₀ blocks), and its display now carries both R_bad's and 𝔏_good restrictions.
  - §1.6 now states its range (k ≤ N; beyond N, D2.7's), labels the reality of A_k a reading, and drops the restriction to real 𝒲.
  - l.3 says that the identities hold at k = 1 and k = K with ε_H fixed at k = 1.
  - §3.2 adds the alternative with (iv-a) (|β| ≤ 2 on ℒ_k, paid by (iv-b)).
  - Map l.165 adds R_bad and 𝔏_good.
  - (iv-b) separates Bałaban's lifetime K from the final step. The log_𝔤 notation replaces (1/i)log, and the ∏ of (3.16) is cited from the corrected transcription.
- Not changed: map l.141's "derived" for (iii-a)/(iii-c) in the coarse note. That status is settled by it1-coarse-20261029-r2 below.
- Hashes at 00:57: background note 144 lines, ba980044e428; map dbf4160615d2.

## it1-coarse-20261029-r2 (landed 00:51, triaged 00:57–01:05)

Verdict: no fatal finding, one serious (S-A), S-B between minor and serious, J1, and minors m1–m10. S1 of round 48 is closed; (iii-c) is closed for the composed words; (iii-a) was not closed while S-A stood.

- *Serious (S-A, the share budget with X^g_W in σ).* Accepted and repaired by the review's second option, a sharper count. X^g_W together with the cubes meeting the tube of I(W) is a closed connected set of at most 8σ_k(W) + 120 π_k-cubes, so #_{k+1}(X^g_W) ≤ 16 + 15360/L + 1024σ_k(W)/L. The coefficient 1024/L is the map's (l.1549, l.1551), so the share inequality holds at L₀ = 5000 with the constant c_sh^g := c_sh + 10240ν_f/L, a factor e^{10240ν_f/L} ≤ e^{2.05ν_f} per old group. Changed: §4.1's σ paragraph, §7's (β) weight and product (e^{ν_e + 10240ν_f/L}), §8's wording, header l.3, and map l.141.
- *S-B (§6 a1).* Applied: the scaling identity's quadratic-form clause corrected, and the A(1/g²(·) − 1/g², ·) terms assigned to D2.6. The p.268 citation of the ρ_j formula is gone.
- *J1 (j = k).* Applied: l.9 separates j ≥ k+1 from j = k, and §2.4 treats j = k by the direct bound.
- *Minors.*
  - m1: 6561 restored as the earlier constant in l.3.
  - m3: the t_Y = 0 field is e^{iηa′}U_{j+1} (l.35).
  - m4: the inter-arc transport is the M^k(e^{iηa′}U_{j+1})-transport (l.12).
  - m5: l.3 carries (C4)'s (b_d^c)^{k−1} and ε_H's dependence on the largest k; l.14 now says the k-dependence is (b_d^c)^{2k} at fixed ε_H.
  - m6: §4.2 says that its entries are read with §7's factors (81e^{ν_e + 10240ν_f/L} in (β) and the recursion term, 2099601e^{ν_e} where positions and ℓ_{X^g} enter) and still tend to 0 for g_K small at fixed k. §4.3 adds the disc inclusion: for |z| < R_X the point is in D(j+1)(iii)'s domain (SW closure §6(6a)–(6b), read), where the phase per fine bond is < α_{1,j+1}L^{−(j+1)} ≤ (1+β₀)α_{1,K}L^{−(j+1)}, the a′-part of (C4).
  - m7: §7's KP line states the further factor ≤ 81 if incompatibility is decided by X^g; the smallness condition is now ν/(64·81²M) in §4.2, §7, and Constants.
  - m8: ‖a′‖_∞ without the extra L (l.44).
  - m9: RG1 (0.4) in place of (0.6)/(0.9); RG2 (1.19) on p.6; (1.21) as a size bound; CRE (3.15)/(3.16).
  - m10: C_χ^g = 2099601e^{ν_e}… (l.91, Constants).
  - M2 (carried from round 48): §1 now opens with a list of the β and θ symbols and their roles.
- Status: map l.141 now records the round-53 review of the coarse and background notes, with the creation-position count open.
- Hashes at 01:05: coarse note 186 lines, fde3f284b852; map c6ee7d744035.

## it1-d27-early-20261029-r2 (landed 00:51) and it1-d27-20261029-r4 (landed 00:53), triaged together 01:07–01:49

Both reviews cover WILSON_IT1_D27_CLOSURE_2026_10_26.md: d27-early covers items 3–5, 13, the constants, and the continuum note's (4.3)–(4.5); d27-r4 covers item 15. Verdicts: no fatal finding in either. d27-early has four serious findings and nine minors; d27-r4 has two serious findings and fifteen minors, and finds item 15 not closed as stated.

- *Status (d27-early S1, d27-r4 S2).* Accepted. One status everywhere: derived given the reading R-far″ and the unreviewed project inputs (R-eval), (R-round), and (R-att-ext), with one OPEN check (15.8's link comparison, below). Stale "OPEN"/"Neither a bound nor analyticity" sentences are removed. Changed: D27 l.3, l.5, item 5 Corrections (b), 15.9(a); continuum l.3, l.5, l.129, l.156; map l.156, l.342.
- *Item 13 (d27-early S2).* Accepted. The later-step 𝐑^{(j)} form rests on LFR II Theorem 1 and on 15.8; map l.976 and l.1353 do not extend the step lemmas, and the text no longer says they do.
- *Continuum (4.4) (d27-early S3).* Accepted. The dressing depends on Z through the attached species and through the leading word, i.e. 15.5(i)'s background-localisation pieces with the 𝐇-decay. Δ_Z includes both: |Δ_Z| ≤ C_attℓ_C(e^{−cD/M}(…) + e^{−δ′D}), with rate min(c/M, δ′).
- *ΣA (d27-early S4).* Accepted, second route. e^{2ΣA} is paid from κ in D26 7.2's enlarged induction, with no smallness condition. A polymer with a slot has q ≥ 1 in (1.95) and extracts e^{−p₀} in both of c₁'s cases. New amplitude ĉ₁ := e^{3+a_k}e^{−p₀(g_k)}; the condition is p₀/2 ≥ 3 + a_k. Changed: item 5 (a), 15.3, 15.4(ii), 15.6, Constants.
- *Covariance of the localisation pieces (d27-r4 S1).* Accepted, partly derived and partly read. The minimiser part is derived: by CRE (2.11)–(2.12), p.256, U_k(V) lies in the unique minimal orbit and M_𝔹 is covariant, so U_k(V^v) = U_k(V)^{u′} with u′⌈ = v. The covariance of the interpolated 𝐇(s)-functions (LFR II p.374 l.42) is a reading, extending p.378's "the effective action is gauge invariant". It is added to R-far″ as clause (γ), with constant conjugation (for c_g) and non-constant u (for 15.6(a)) stated separately. Changed: 15.5 (γ), 15.6(a), map l.342.
- *Item 3 (d27-early M1–M3).* Accepted. Item 3 is rewritten as two operations, R′ and p.378's δ-removal ("equivalent, but not equal", p.378 l.17–20). Gauge invariance enters at three places inside (1.76). Cov(k) (map l.620–623) is cited, with the minimiser-covariance derivation. The identity is E[W(C)] = ∫RN/∫Rρ.
- *Item 5 (M4) and M6.* The superseded body bounds are rewritten; ‖Y_X‖ ≤ e^{4+2ΣA}; item 6 uses e^{4+2ΣA}; LFR II (1.51), p.370.
- *M5 (c₁ = α^{1/3} near ∪Y_i).* Accepted. 15.6 now takes e^{−p₀/2} there from the absorbed components' e^{−(3/2)p₀}.
- *Continuum M7–M9.* (4.3) and (4.5) now make no age bound (p.384 l.15); the (4.4) shell count is "set out and not derived"; B_LF := sup over every ℓ ≠ ℓ₀.
- *Incidental (map l.165).* The k = K bound needs 8a_dc_hB₃ℓ_Cε_K ≤ 1/10; it is stated with a parenthesis.
- *d27-r4 minors.* All applied:
  - map l.342: Ξ is the whole gas and Ξ_{¬C}(𝔉) the gas compatible with 𝔉;
  - N4's "first-class component" in 15.5(i) and the map;
  - the R-far″ title;
  - E^{R,∂}_k(ℓ) subtracts ℓ₀'s collar clusters, with a factor 2 in m_k^R;
  - μ_k^R := −(4LΠ^R_k)^{−1}Σ_vκ^R_v, per unit length, and map l.1146 states it;
  - |E°_k^R| ≤ C·MR_ke^{−p₀/2};
  - a_k(X) := 4(100MR_k + 2Mw_k + 2Mδ^{−1})δ^{−1}e^{−δw_k};
  - e^{|Ψ_g|} ≤ exp(O(1)e^{−p₀/2}n_g), absorbed by O(1)e^{−p₀/2} ≤ κ/6;
  - the e^{2s} reason via (1.73) on the unnormalised operation;
  - S_R over m ≤ K−1 and g_* over m ≤ K;
  - λ_R in 15.7;
  - the merge rule and F(P) in 15.3;
  - citations: p.374 l.8–35 for the construction; (1.67)'s "of Y∖Z"; CRE (2.12) at p.256; the Ω_k quotation at p.379 l.22; c₁ = α^{1/3} only near ∪Y_i; (3.43)'s radius is for the fluctuation field A, with r^{an}_k its value for g_kA (15.7).
- *The link condition (d27-r4 minor, "(1.94)'s volume cost").* Not repaired, made OPEN. D26 l.150's per-cube comparison of the link decay ν/64 with (1.94)'s O(1)α^{1/3} per M-cube is not derived. 15.8 and 15.9(c) now state it as OPEN, with a route: (1.94)'s first form is a surface term on the components' boundaries.
- Hashes at 01:49: D27 note 236 lines, 4b15c2cd1cfa.

## it1-cont-20261029-r3 (landed 00:56, triaged 01:40–01:49)

Verdict: no fatal finding, two serious, about fifteen minor. r2's three serious findings are closed as to the reading. (7.2)'s new justification reopened r2's point on surviving components.

- *Serious 1 (surviving components).* Accepted. (1.70) is the result of LFR II §1's operations for components satisfying (i) and (ii), not a multiplication and division. A surviving component appears as 𝐓″_{K′}(X) acting on the exponential ((1.72), (1.104)), so Q_ℓ is undefined there. Repaired: (7.2) restricts the factorisation to kept components. For surviving components it bounds |𝐓″F| ≤ (𝐓″1)·sup|F| by positivity, with (1.79)–(1.80) at arbitrary regions, and defines the residual Q″_ℓ. Its bound (Q″) is a second open premise. Changed: (7)'s title, (7.2), (7.3)'s surviving-component line, (7.4), header l.3 and l.19, Not derived (l.156); map l.16, l.1096(c), l.1213.
- *Serious 2 (S not well posed).* Accepted. The two runs' sharp characteristic functions have coupling-dependent thresholds (ε_k = g_kp₀(g_k), CRE p.246 l.14) and partitions (R_k, p.245 l.33–34), so δ_k ≠ 0 gives different supports and possibly different partitions. (9.4)(e) now states this and poses S under one of two conventions: (α) common thresholds and partitions from one coupling sequence, with the check that Bałaban's bounds hold for run B; or (β) a norm on the normalised expectations of local functions. Bałaban's second choice (p.246 l.15–17) is recorded as removing the coupling from p₀ and R but not from ε_0. The threshold mismatch is taken out of s_k. Changed: (9.4)(e), (9.3), header l.3, Not derived, map l.16, l.1213.
- *Minors.* All applied:
  - (7.1) is labelled derived given the support inclusion, which is part of (Q); the mixed tests are named;
  - the "at no place" sentence is replaced by the corrected reading (LFR II (1.1)'s localised denominator);
  - p.378 l.15–20's δ-removal applies to first-class components only, and the kept components' δ_{G_i} stay in S_ℓ;
  - (7.3)(b) states the proviso that U(V) lies in (1.3)'s admissible class (p.357 l.14);
  - the cube count uses R_{K′+1} ≤ LR_{K′} (CRE (2.9) first line), giving L^{−2d};
  - (Q) and (Q″) enter through c_Q, in ĉ and in (C-LF)'s second condition (l.3, (7.4));
  - (9.2) quotes (2.43) as the field-dependent part, after the U = 1 value and β_jA are removed, and (2.44) as 𝐑(U) − 𝐑(1);
  - (9.4)(e): θ′ := θ + 2C²g⁴/(1−θ) for C²g⁴ ≤ (1−θ)²/4, a bootstrap on the largest ratio, and K-uniformity only with the running couplings and Σg_m⁴ < ∞ (RG I (0.31), Cor. 8.2);
  - (4.5): term-by-term convergence needs a K-independent label set and dominated summation, not set up, so only r_K as a whole is used;
  - the coupling matching is Bałaban's statement for SU(2) with proof deferred (p.259 l.29, l.38), and ONE_LOOP_PROOFS Cor. 8.2 for simple G;
  - Corollary 3's E_± depend on g_k (p.264 l.29–30); Theorem 2's E₁ is independent of j, k, T (p.263 l.11–12);
  - (2) and l.13: D(K′) on every labelled term, given D2.6's and D2.7's inputs;
  - map l.1213: item (8)'s premise rests on D2.7's inputs for K′ > N;
  - LFR II (1.51) at l.5 was already in place.
- Hashes at 01:49: continuum note 156 lines, c81e708e5682; map 1614 lines, f6e68d7eea96.

## it1-o4-20261029-r3 (review written 00:49, triaged before 02:01)

- Verdict: O4 is CLOSED in the frozen-centre form, with the centre read per step. No fatal finding and no serious finding. The round-52 S1′ is closed in substance.
- Minors m1–m10 and the wording items were repaired in WILSON_IT1_O4_CLOSURE_2026_10_26.md:
  - "cannot be asserted" at l.5, l.13, and the §3 title;
  - rank ≥ 2 for the operator norm;
  - C_h is g₀·polylog, absorbed by g₀-smallness;
  - the V4 locators l.2970, l.2972, and l.2974 were verified, with IT-1 l.137 for the "indicators" quote;
  - the 𝐔-independence of the Dirac pushforward is labelled a reading;
  - §4(b)'s domain is around the real U_{n′};
  - the double induction is stated;
  - λ is a constant;
  - the clause is on 𝒫(𝐔(U_{n+1}));
  - U^c_j(X, α₀, α₁, γ₀);
  - "radius set by α₂".
- Closure hash at 02:01: 9e4c9600a467.

## it1-o6-20261029-r2 (review written 00:51, triaged before 02:01)

- Verdict: O6 is NOT CLOSED as written. There is no fatal finding: the joint analytic extension in (A_k, A) on R-m's domain is correct, given R-m and (R-m′).
- S1: the bracket terms 𝐄_k, 𝐑_k″, 𝐁_k, and A(·) with Y ⊄ Λ_{k+1}. The "real-support bound with the factor doubled" is unsupported for them. Repaired in WILSON_IT1_O6_CLOSURE_2026_10_26.md §5:
  - F_X(B′) vanishes at 0 and is bounded by M_X on R-m's polydisc, so the Schwarz lemma gives |F_X| ≤ M_X·C₁^{RG2}g sup|B|/r_{α,k}.
  - The t_□-localisation runs at the margin-limited radius ρ_k := r_{α,k}/(C₁^{RG2}ε_k^♯), with a factor ρ_k^{−1} per added cube.
  - The coefficient is therefore of order ε_k/α_{1,k}, not p.277's O(ε_k).
  - The q₁ = p₀ condition (C3) becomes 64, and (C6) log ρ_k ≥ c_loc is added. (C2) reads g^{3/2} + 7.5h_k ≤ c₃ε_k.
  - OPEN: the consumers' replay with this coefficient (D2.6 §2.2–2.3, §4.3, §5.0; R2, R3, R15) and the constant c_loc.
- S2: §7's inclusion of the support in (3.43)'s domain. The inclusion claim is deleted (it fails for LFR I's p₁; TRANSCRIPTION_FINDINGS), and R-fr (c) bounds on the support.
- Minors m1–m11 applied: r_{α,k} at T_Y = 1; RG1's B′ = CB; the Ψ sign; the p.269 l.49–50 support reading; R-m for the brackets labelled a reading; the ratio 2 restricted to 𝐏 terms; the constants list.
- Propagated to the D2.6 closure l.161 (O6 status) and map l.956, l.959.
- Closure hash at 02:01: c5952e82534f.

## it1-d2-r45-20261029-r2 (review written 01:41, triaged before 02:01)

- Verdict: no fatal finding and no serious finding. The round-45 items are correct: A_h := 17 is absolute, ν can be fixed absolutely, the stopping scale is checked at K′ ≤ N with (TC), and the response chain gives the base points on Ω₁∖Ω₂ for every k ≥ 2, given the stated readings.
- Minors 1–7 applied in the map:
  - l.499: the "(R-cpl₀)" label;
  - l.174: the Θ form, with r ≥ 2 and CRE p.245 (no condition on δ₀M₁);
  - l.219: R-dec per layer, θ_i = e^{−δ₀R_iM₁/32} (PRT2 p.231's d(y, y′), which is layer-additive);
  - l.177 and l.1305: the ϖ range, R_e's entries (A_E, A_F, A′_E, the pin's C, and the g₀-threshold), and V3 L4785 and V4 L5229, all verified;
  - l.183, l.921–922, and l.1094: the review labels and N_k = O((log K)^ν) as an upper bound only.
- Minor 8 is an observation and needs no change.

## it1-o2prime-20261029-r2 (review written 01:43, triaged before 02:01)

- Verdict: O2′ is correctly reduced to O2 within D2.6, given O2 and IT-1's unreviewed per-component factor. No fatal finding.
- S1′: the dependence of §1, §3, and §5 on O2 was undeclared, and the record misstated the prior serious finding. Repaired in WILSON_IT1_O2PRIME_CLOSURE_2026_10_26.md:
  - "given O2 (closed for 2 ≤ k ≤ N)" at l.5, l.71, l.77, l.91, l.141, l.143, and l.145;
  - the review record at l.147 corrected.
- Minors m1′–m7′ applied:
  - the closure uses Z₁ = Λᶜ;
  - D(Λ) at IT-1 l.1422, with V3 L2451 marked as a paraphrase;
  - the 𝒳 notation and ϑ_V²;
  - the D2.7 link budget.
- D2.6 closure §6.4–6.5 now carries 𝒩₁′, the factor 2, lw(X) ≤ 2·lw_1(X), and the D2.7 budget. a_lab·n_t(i) ≤ log 2 is kept as a D2.7 condition, and the share is not used.
- m7′'s pointer (closure l.126, "O2′ note §4") was changed to "§2, *The step-1 anchors of closure 7.1*" at 02:10.

## it1-o2-20261029-r2 (review written 01:44, triaged 01:57–02:10)

- Verdict: O2 for 2 ≤ k ≤ N is correct and sufficient. No fatal finding and no serious finding. One input is unreviewed at its source: IT-1 l.1469's bad-cube factor.
- Minors 1–11 were applied in WILSON_IT1_O2_CLOSURE_2026_10_26.md:
  1. §3.2 item 1: the case Ω₁ = T, S₁ = ∅ gives Λ = T, so p.255 l.3–4 holds verbatim.
  2. §4.1 (i′): δ on Ω₁ᶜ, with CRE p.252 l.21–22 quoted.
  3. §4.1: the determining set is not a localisation, and the V_k-integration over Ω_{k+1}ᶜ is the composition (3.24).
  4. p₀ notation. IT-1 uses p₀(g) := (log g⁻²)^{p₀} by its own declared convention (l.1153, l.1176), inferred from LFR II pp.381–383, whereas LFR I p.175 l.14 puts A₀ in front. The note now uses IT-1's convention, and a_lab is quoted as IT-1 l.1760 prints it. IT-1 needs no correction: the review's "contrary to LFR I" is a convention difference that IT-1 records.
  5. "Ret(Λ)" became "Λ₁ ∖ Λ" in the l.11 heading, §3.3's heading, and §5 item 2. In D2.6 closure l.161, the localisation reads Λ₁ ∖ Λ ⊂ Z₁, and (i′) was added to "step 2 needs only".
  6. §5 item 1 names the X-factor's dependence on the outer Λ₁ outside X (𝐇_{1,Ax}, U₁(Ω₁ ∩ Λ₁ᶜ, V)).
  7. §2(b): the range Λ ⊂ Λ₁^{(0)} is stated for the filling locality, and the notation was corrected.
  8. §3.3: the p.264 l.50–51 citation is replaced by the unchanged CRE objects; the index match is not used.
  9. §4.2 cites p.383 l.32–33's positivity bound and l.45's supremum over admissible domains.
  10. Status: the unreviewed IT-1 l.1469 input is recorded, the acyclic dependency path is written out, and the review history is replaced by a status label. The D2.6 closure l.161 records the unreviewed input as well.
  11. At l.10 and l.33–35, the two readings are equal as sums, and the exact (2.19) holds in the (Ω₁, Λ₁, Λ)-outer reading only.

## it1-d2-rep-20261029-r6 (review written 01:50, triaged 02:03–02:12)

- Verdict: item (B) is correct on the output side but not sufficient. No fatal finding.
- S1 (serious; OPEN): (11)(c)(β)'s polydisc points e^{iη(𝐇(s,tB′) + a″)}U_{k+1} with a″ ≠ 0 are not gauge transforms of frame points. The argument is a dimension count, and I checked it. So the "frame point" reading at l.1498 fails there. D(k)(iii)'s covariant clause then involves the (s, t, B′)-dependent D(k)-level c₀^{(k)}, of size O(dα_{1,k}), which is unbudgeted. Charging it to (4)(c) brings back round 43's cost.
  - Recorded as OPEN at:
    - the top of the map's gaps block;
    - l.1498, with what closes it;
    - Step 8's header and its l.1498 sentence;
    - l.314: the frame family is Step 8's family (I), and the exception is stated;
    - l.869 *Scope*: c₀ is of (b7)'s kind for the output only;
    - l.975's inclusion label;
    - l.982.
  - What closes it: Step 8's convention at the evaluation points, (e^{iη𝐇̂_k(s,tB′)}Ū)^{c₀}. This requires:
    - l.975's inclusion, (4)(f)'s chain condition, and l.1498's a′-transport costs, all redone for the Ū-based points;
    - the plain clause derived at the non-output members of family (I).
    - The alternative is the literal base with round 44's F2 factor.
  - Not repaired in this triage.
- Minors applied in the map:
  - m1: |B′₀| ≤ 2ι + 2dι(1 + o(1)) from (97) and (131) at j = k;
  - m2: B₀e^{16κ_s} is written in ι₀ and |log g|, and the curvature citation is marked as not covering the radius;
  - m3: the Result is split into δ_n at a field-small base and v₁ in the mean frame, and l.194 now says v̂₁ for the general configurations;
  - m4: g₀(x) = e^{−ιη(x−y)₁H}; P_n(Ū) = g(x_n)P_n(Y)g(x)^{−1}; Ad_{ĝg}; the pointer to D2.1(2) l.448;
  - m5: l.314 is aligned with family (I);
  - m6: folded into S1's closing list;
  - m7: l.941's label is updated, l.982 mentions c₀, and l.961–962 use C_w′ = C_w + 3d.
- Hashes at 02:12: map 1615 lines, a5aabff8bb12; O2 note e9aa71c84c9d; D2.6 closure 74065c4809ac.

## it1-d22-6c-20261029-r1 (review written 02:41, triaged 02:50–03:00)

- Verdict: 2 serious, 8 minor; no fatal finding. All are repaired in the map: l.5, l.884, l.886–898 (the sizes, the sup bound, no per-cluster deviation factor via D2.4(4), and the gauge (LPG′) rather than CRE (2.38), D2.4(4) l.1336), l.1284, and l.1300. Line count kept.

## it1-rh-20261029-r6 (review written 02:42, triaged 02:50–03:05)

- Verdict: R-𝐇 and R-𝐇₀ at complex backgrounds are correct and sufficient. Every prior finding is closed. No fatal finding.
- S1 (serious): the slot-value result at l.971, l.982, and l.985 overstated its status for Step 8's c₀-form evaluation points. These are now stated as conditional on the OPEN item at l.1498 (l.164).
- Minors:
  - m1: the frame constants 3S_H, 10S_H/g_j, and 40C_H are propagated to the map (l.222, l.977–981) and to D2.6 closure l.55, which now reads 10C_H and 40C_H.
  - m2: READINGS_RECHECK row 35 now says the axial transfer is Bałaban's at real U and derived at complex U (R-𝐇₀). Row 2 now records rounds 37–38 (no fatal or serious finding) and round 53.
  - m3, m4, m5, m7, m8: applied.
  - m9: the p.251 part was applied earlier. The REG p.79 quotation at l.972 now includes "given by the subgroup (1.14)".
  - m6: the line pointers are the reviewer's numbering, one above the true lines.
- Not applied: the cosmetic c₃ in C_H's list.

## it1-rc-p6f-20261029-r7 (review written 02:44, triaged 02:50–03:05)

- Verdict: Pass 6 (f) is correct up to minor repairs. Rounds 38–39's F-1 to F-3 are closed. No fatal finding.
- m-1: the iterated-difference expansion for the non-quadratic potentials (the Möbius decomposition, the Cauchy bound, the hypergraph expansion, O(ϵ_mr) ≪ β per bond), at RC l.260.
- m-2: map l.185 now gives |W(Δ)| ≤ 4n_Δ/r, since |A″_b| ≤ 2r on the W-host bonds. The inner "(derived, not reviewed)" is dropped, and the status reads "(f) re-reviewed".
- m-3: RC Pass 6's V4 citations now go by label. The current V4 (563736a8dfb9) lines are listed, and the old numbers are noted as V4 d463c554b76f's. The map's l.185 locator now reads Section c5-0 / c5-2-3, at current L2458 and L2540.
- m-4: status labels at RC l.252 and l.262.
- t-1: ‖R_i‖ ≤ O(ϵ_H) replaces the underived pointwise rate, and ‖μ‖² is absorbed in P's penalty.
- t-2: the W-host condition now carries (2.28)'s prefactor.
- t-3: s_b := 2R_U + 3.
- t-4: the potentials' Σ_{b′∼b} is now a weighted sum over Y.

## it1-d24-13-20261029-r1 (review written 02:49, triaged 02:52–03:05)

- Verdict: (13)(a) and (b) and the group- and cluster-level difference counts are correct given (S-w). The C_rel recursion's carry factor was wrong. No fatal finding in the lines under review.
- S1 (serious, repaired), (c5): the sup-form clause ε^{diff}_k carries with the factor L per step-(k+1) traversal, not L^{−1}(ρ̃_k/ρ̃_{k+1}).
  - The recursion is rewritten as C_rel^{(k+1)} := (L(1+β₀)⁷ + 1/8)e^{−c(L−1)ι_{T,k+1}}C_rel^{(k)} + C⁎, and the contraction is e^{−c(L−1)ι_{T,k+1}}.
  - (TC), at l.1131, gives ι_{T,k+1} ≥ ι_{T,K} ≥ 96L⁴M(L+1).
  - The factor is therefore ≤ 1/2 once 96cML⁴(L²−1) ≥ log(35L). This always holds for c = 1/(32M). For c = c₁ = 2μL it is the condition (C-rel), 192μML⁵(L²−1) ≥ log(35L).
  - The uniform bound max(C_rel^{(1)}, 2C⁎) survives.
- D1 (serious; confirmed independently by d24-12 item 21): see the OPEN item below.
- Minors applied:
  - (a): t is now taken from (4)'s B_∞ definition;
  - C_box wording;
  - (b): the tilted activities, the ℓ₀ scope, and "derived given (S-w)";
  - (c2): the vacuum Lipschitz constant C_ve^{C_v′c#(M)}, absorbed under κ ≥ κ_pc;
  - (c6) wording;
  - (c8): the Cauchy step for ΔY_W;
  - the misattributed contraction;
  - (13)(d)'s SW inputs: the scope, LPG′, the readings R-17 and R-17b, and C_box ≥ max(4A_E, 6);
  - the gaps-block (S) statement with pl;
  - D2.6 closure l.118's pointer, now l.1595.
- The SW constant mismatches are repaired in the SW closure (see sw below).

## it1-d24-12-20261029-r1 (review written 02:50, triaged 02:55–03:05)

- Verdict: the single-step rooted-sum machinery of (12)(c)–(f) is sound up to minor constant omissions. The claim "(S-w) uniformly in k ≤ K" is not established.
- Item 21 (serious; OPEN, map l.168): (12)(f) applies the real-point carry factor L^{−1}(ρ̃_k/ρ̃_{k+1}) of (6) to ε^{(k)}, a size sum at complex data.
  - For the a* and j* terms, a*^{(k)}_n ≤ L^{−1}a*^{(k+1)}_{n′}, so the L step-k traversals give ρ̃_k/ρ̃_{k+1}.
  - Each generation j therefore adds ≈ ρ̃_jα_{1,k+1} per traversal. The sum is of order (g₀g_k)^{−1}ρ_{k+1}, not uniform as g₀ → 0.
  - I checked the count and it holds. Recorded as OPEN at:
    - map l.168, in the gaps block, using the blank line;
    - (12)'s heading, (12)(b) *It carries*, and (12)(f);
    - (13)'s heading and (13)(d);
    - the gaps-block (S) bullet;
    - SW closure §0, §6(6c), and §7.
  - What closes it: a gauge-covariant complex-data clause. CRE (2.39), p.261, (L^nξ)²|∇_U^ξA′| < α_{1,n}, gives the relative gain d·L^{−(k+1−j)} per generation. The crux is the invariance of a carried Y_W under complexified gauge transformations on its dependence set.
- Items 22 and 24 (serious, status): (12)'s heading and (g) now name the premises: (ii-w) at step k with C^{(k)} bounded, (R-m′), (T0)/(T2), κ_D′, and the (11)(g)/(g) inputs.
- Minors applied:
  - item 13 and item 9: the vacuum sum carries C_pc′, with κ ≥ κ_pc := ¼log((9/64)max(100, 2C_v′)C_pc′) added to κ_D′, for review;
  - item 15: s(W′) includes log C_pc′;
  - item 18: the gap-cube factor 4M + 4;
  - item 20: the ≤ 2 end insertions of the enlargements as a separate stage;
  - item 19: b(W) = (ν_r/4)σ(W) for fixed members, aligned with D2.6 closure §5.5;
  - Q3: κ_s is RG2's κ₁, and the nesting is cited to CRE p.265;
  - pl_k ≤ (1+β₀)pl_{k+1} is cited to CRE (2.7).
- Not applied: item 4(3)'s hit-reduction sentence is plausible by recursion, and was left as stated.

## it1-sw-20261029-r1 (review written 02:49, triaged 03:00–03:05)

- Verdict: NOT CLOSED as claimed. (b) and (c) are sound amendments for review. (LPG′) is essentially right, and R-17 holds in substance. No fatal finding.
- S1 (serious; OPEN): §6(6c) had the inclusion backwards. 𝒬^{(j)} is not a union of π_{k+1}-cubes.
  - The candidate is the π_{k+1}-hull of 𝒬^{(j)}, which adds ≤ 2L/(L−1) cube sides in all, with (T-dev)'s carry redone.
  - Merged into the OPEN item at map l.168. §0, §6(6c), and §7 are restated.
- S2 (serious; repaired): step (4)'s decay factor did not apply to 𝒬's π_{k+1}-layers.
  - The bound is now C_H·22d²E, with C_H from VAR (190)'s kernel at distance 2M − 2LM₁. C_H is k-independent.
  - Condition (C-H) on M: 22d²C_H ≤ 1.
- S3 (serious; repaired): step (5)'s local ε₁ is logged as reading R-17b, with its check (the lift of CRE (1.3) is 1 inside blocks). p.267 is read as ε₁ = 2ε_{k+1}, and the lifting is VAR's (11).
- S4 (serious; repaired as a status): input (a) is a restriction of scope. Its remainder is D2.6's open bound (§1(a4)), stated in §0, §7, and map (13)(d).
- (6d) (unsupported; repaired under q₀ > p₀):
  - the global ε₁ is O(L²)ε_{k+1};
  - the cubes near ∂Ω_{k+1} use the scale-k class at a factor L;
  - the q₀ = p₀ alternative is withdrawn;
  - map l.922's status is updated.
- Minors applied:
  - S_j ⊂ Ω_j ∩ Λ_j^c and Z_k = Λ_kᶜ, with the CRE (2.9) mis-citation removed;
  - (a3)'s "only place";
  - the stale l.704 pointer;
  - §4's additive constant 3C_box + 1 and ν_e = ν/(2C_box);
  - R_t ≤ (2C_box + 2)Mℓ_X, M_𝒬 ≤ (2C_box + 6)Mℓ_X, and C_g = 3B₃(2C_box + 6)M;
  - step (1)'s cube sizes and the definition of U_{k+1,□′} (CRE (2.16), (1.2));
  - R-17 restated on unions of π_{k+1}-cubes, with its check;
  - REG [14] in place of "RG1 Lemma 1";
  - step (6)'s notation;
  - (6a): η_w = (5/16)η_V, C_χ with e^{η_w}, and C_new;
  - (6b): the BCH path, the factor 1 + 2C₀/C₁, and the sup form;
  - (6e): C_S = e^{2ν_e}C_S′ and C_box ≥ max(4A_E, 6).
- Hashes at 03:05: map 1614 lines, aac3844383fa; SW closure 38baf2f6a52d; D2.6 closure 3c8a1fea937a; RC pass 5975eb98df58; READINGS_RECHECK 32f7faa03962.

## Map l.168: the Complex Gauge Covariance (03:50)

- The uniformity part of l.168 is derived in WILSON_IT1_COMPLEX_COVARIANCE_2026_10_29.md (not reviewed).
  - Lemma 1: Cov at real points plus analyticity gives the law for G^c-valued u joined to 1 in the domain. This uses the identity theorem on the totally real G^{sites}. The new groups' step therefore owes no extra covariant clause.
  - Lemma 2: X_W's complex part is reduced to K₁δ_Wa. This uses a complex gauge transformation, linear in a (2.38)-smooth gauge.
  - Lemma 3: per insertion, the excess is the non-covariant one times 4K₁δ_W + 12L^{−2m}.
  - §4: the carried complex-data part is bounded from production with a constant Ĉ(L, M, ν_r, β₀, β), so the young generations, about log_L M of them, need no smallness of M/L. δ_W is paid by a 1/16 slice of the reserve's free eighth.
  - The recursion becomes C^{(k+1)} ≤ (1+Ĉ)max_{j≤k+1}N^{(j)} + L^{−1}(1+β₀)^{15}C^{(k)}, with C_S′ := max(C^{(1)}, 8(1+Ĉ)C_winC_M).
- The note lists four open checks:
  - (K1): the reading of CRE (2.38)'s cube family;
  - (K2): CRE (3.2)–(3.5) in step-(k+1) units;
  - (K3): CRE (2.35)/(2.37) at the disc points;
  - (K4): l.961 with 8c_G.
- New conditions on constants: M ≥ 2C₁/C₀ (R-m's C_i), L > (1+β₀)⁹, and L ≥ L₀ for the disc margins.
- Still OPEN in l.168: the π_{k+1}-hull for SW §6(6c).
- Map edits, within lines (1614 lines kept): l.168 rewritten; l.170, l.1534, and l.1580 point to the note. Map hash after the edits: see the handover bullet.

## Map l.168: the Region and the Checks (07:12–07:16)

- SW §6(6c)'s region issue is bypassed (note §5). No (LPG′) at step k+1 on 𝒬^{(j)} is used:
  - the real-point part is (T-dev), whose (LPG′) runs at step j for U_j(V_j^*) = U_{k+1}, on step-j cubes (map l.1353 (1)–(2));
  - the excess uses (2.38)'s real smooth gauge on a CM- or CM/L-cube, or Cauchy's estimate alone.

  The π_{k+1}-hull is not needed.
- (K1) is closed by CRE p.261 (ii) ("for each cube … of the size CML^nξ, or □ ⊂ Ω_j and of the size CM"). Ω_{k+2} is read as ∅ at index k+1.
- (K2) is derived from CRE p.254 (Ω_k ⊃ Λ_k), p.256 (unions of MR_j-cubes), (2.5) (R_j ≥ (log g_j^{−2})^r), and (3.5) with p.265 (Ω_{k+1} ⊂ (Z_k′^{∼8})ᶜ). This gives a collar ≥ 8MR_{k+1}.
- (K3) is treated as map l.928 and l.1328 treat (2.35)/(2.37), with the averaging constant C_av. M ≥ 2C₁/C₀ becomes M ≥ 2C_avC₁/C₀.
- (K4) is closed by l.963's bound, which is small uniformly in k.
- Repair in §3(c): the slot cocycle |κ − 1| ~ α_{1,k+1}δ_W does not fit l.961's margin 2^{−(m+1)} uniformly in m when δ_W is near δ̄.
  - The covariant regime is narrowed to δ_W ≤ δ̄_m := min(δ̄, 4^{−m}), and L ≥ 8 is added.
  - Beyond the regime, the non-covariant bound is used with weight e^{−ν_r(L/4)^m/(64M)}. Ĉ stays finite for L > 4.
- Edits:
  - the note (183 lines, §5 added);
  - SW closure l.6, l.19, (6c), (6e), §7;
  - map l.168, l.1419, l.1523, l.1591, and l.1614, within lines (1614 lines kept).
- The note needs a referee packet in a later wave.

## Map l.164: the Touched Old Insertions at a″ ≠ 0 (07:17–07:32)

- Not closed. l.164 now records two shortcuts that do not work and route (a)'s constant condition.
  - Production frame: the slots reach W through w_tot = c₀ŵ (Step 8), so c₀^{(k)} is not avoided.
  - Fixed fraction of r_{ω,j}: the cost α_{1,k}|σ_{j,0}|/r_{ω,j} is bounded only by Cg_k^{1/2}polylog(1 + β′(k−j))^{1/4} (l.963), not uniformly in k − j.
  - Route (a) puts 𝐇_k(B′₀) in place of a″. With l.942's bound O(B₀e^{16κ_s}|B′₀|), the chain margin would need L ≳ B₀e^{16κ_s}d, which κ_s ≥ (10+3L)κ excludes.
  - At s ≡ 1, RG2 (1.11)–(1.18) with κ₁ = 0 give 4B₀|B′₀| (a reading, not logged). The margin then needs 4B₀(d, L)·O(d)(1+β₀) ≤ c(1−β)L, and PBG Thm 3.1 (p.397) gives B₀ as depending on d and L with no rate.
- Not attempted: the polylog item (its consumer is V3's step-1 family-sum factor e^{n_Cε̄_ph}, which needs the main theorem's loop sizes) and the step-1 check of (T-dev) (V3's step-1 indicators).
- Map: 1614 lines, 0145a4e7f27a.

## Map l.164 and (T-dev)'s Step-1 Check (07:51–07:56)

- l.164: a third route does not work and is recorded in one line. Enlarging r_{ω,j} to order α_{1,j}/g_j fails, since the slots' ω-analyticity comes from the shifted-potential gas. Its KP condition C_KB₀e^{32a}r_kr_{ω,k} ≤ c_KP (D2.6 closure §2.2(b)) already fails at r_{ω,k} = c_ωε_k/g_k. l.164 stays open.
- (T-dev)'s step-1 check (map l.1353 (1), l.1425): derived, not reviewed.
  - V3's V₁-dependent factors are χ_1(Ω₁) and χ_Ax(P₁¹). χ_1(Ω₁) is CRE (2.16)–(2.17) at k = 1 (V3 L307); CRE p.253 writes ρ₁ in the general form, and p.246's test (1.4) is (2.17) at k = 1.
  - V3's other factors are functions of the fluctuation and exterior variables, and the far-row indicators are omitted (IT-1 note §3c(2)(e)).
  - The global induction at i = 1 then puts V₁^* in that support, with U₁(V₁^*) = U_{k+1}.
  - The group bound's U₁-inputs (V3 L5033 with (B3)(iii), and Lemma c4-7-3) are V3's at that V₁.
- Map: 1614 lines, bcc94bf2f32c.

## Map l.1422: the Tail Form of D2.0(5)(d) (09:40–09:51)

- Derived, not reviewed (map l.1360, l.1422). D2.2(6)'s construction is exact, and in it the fluctuation parts and pair contractions are not separate insertions.
  - A touched old insertion is a W ∈ 𝔅(M) inside Ĥ(M) (D2.2(6)(b4)), so it lies in a step-(k+1) group 𝒢 (D2.2(6)(d)). The flat scalar parts are in c_𝒢 and the rest is in Y^d_𝒢 (D2.3(2)).
  - An untouched old insertion is taken at s = 0, that is at U_{k+1}, and (T-dev) carries it.
  - So the tail form is (ii-t) for the new groups, given (S), and the leading word's first-order term is in D2.4(11)(f)'s parity step.
- Map: 1614 lines, 6ad3037bb01a.

## Map l.1424: the D2.1 Radius (09:51–09:53)

- Derived, not reviewed. D2.4(11)(c) fixes the radius per slot kind.
  - Pure loop slots (α) carry no ω-dependent factor and keep T_Y = ε_H/|B′|_Y.
  - Slots with touched old insertions (β) run at 1/T_Y ≥ 16B₀e^{16κ_s}|B′|_Y/(min(β,1)α_{1,k}). That is l.969's cut to the α_{1,k} scale.
  - The ω′-dependent groups use the same per-slot factors pointwise in ω′ (D2.6 closure §2.2, row R2).
- Map: 1614 lines, 71c0624f1ad1.

## SW §1(a4): D2.6's att Bound (09:53–09:55)

- Already paid in the D2.6 closure, §2.1–§2.2. The SW file's "D2.6's open bound" was stale, and SW l.6, (a4), and l.60 and map l.1614 now point to the closure.
  - The failures of (i) and (iii) are att(k+1, coll) (rule change (1)). Their O(b_k) is paid in the collar term, since b_k ≤ C₁^{RG2}(1+β₀)²u_*ρ_{t,k+1}/(2C′_χ).
  - The failures of (iv) alone keep (11)(f)'s gain, O(ρ_{k+1}).
  - Status as in the closure: derived at real σ_k, and through O6 at complex σ_k.
- SW: 111 lines, 2c5df6e92b27. Map: 1614 lines, 4d02bee9f8e0.
- l.193 is not attempted: its open part is the K → ∞ statement (the continuum limit).

## Map l.1423: the Complex-Background Polylog (09:55–09:58)

- Derived, not reviewed: the polylog is tolerated.
  - V3's e^{2n_Cε̄_t} has no counterpart in D(k): D(k)(ii) is per traversal, and the scalar parts go to D2.3's exact absorption at real data.
  - ρ^c_{ph,j} enters only through ρ̂^c_j, the production amplitude of att(j, ·).
  - The carry lemma moves that mass multiplicatively (∏(1 + δ_n) ≤ 2; D2.6 closure §5, (T0) and (T2)).
  - The payment needs g_j² times a power of log g_j^{−2} to be small, and D2.6 closure §7's τ̂² already carries the exponent max(6p₀, 4p₀+(q₁−p₀)₊).
  - The wrap sum is small for the same reason.
- IT-1 note l.98 and SW l.110–111 now point to it. SW now has 112 lines (e2b03384777d). The IT-1 note is 68e36cbc3387, and the map is 1614 lines, 2e743ebdc677.

## Map l.164: the Points With a″ ≠ 0, Closed on 𝒟^{sub} (10:00–10:23)

- Derived, not reviewed; S1 of the round-53 review of item (B).
- Every bound used at (11)(c)(β)'s polydisc points is on 𝒟^{sub}_{k+1}:
  - the dev clause by SW closure §6;
  - the att, lw, and wrap bounds by D2.6 closure §5.0.
- 𝒟^{sub} carries the top-layer radius α_{1,k+1}L^{−(k+1)} per fine bond on every layer (D2.6 closure §5.4).
- There Step 8's size bound, with only the levels below j on the layer j, gives |log c₀^{(k)}| ≤ C_{c₀}α_{1,k}L^{j−k}, C_{c₀} := 2d + 24d(d+1)B₀e^{16κ_s}.
  - Its rotation of the slot values fits in half of the per-step margin under 32c_GC_{c₀}(2/L)^{k−j}α_{1,k}(|σ_{j,0}|/r_{ω,j} + 1) ≤ 1, a smallness of g_K by l.963.
  - The other half goes to ŵ: l.962 with 32 for 16.
- Round 43's O(dα_{1,j}) was the cost on the full domain, where the imaginary part on the layer j is α_{1,j}L^{k−j} in η_k-units.
- Dev groups contain only dev members (D2.6 closure 2.1), and those are ω-free (4.2(iii); IT-1 note §3d(4) at step 1), so there c₀ rotates no slot value.
- Amendments for review:
  - for att, lw, and wrap, the full domain carries no clause (D2.6 closure §5.0);
  - ρ_ω takes C_w + 3d + 2C_{c₀} (D2.6 closure §5.0);
  - §5.1's "Derived given" names l.1498.
- Not separately reviewed: Step 8's size bound restricted to the levels below j on the layer j.
- Step 8's convention at the evaluation points, route (a), and the literal-base second factor are no longer used. The map lines that called the item OPEN now point to l.1498: l.196 (two places), l.314, l.869, l.970, l.975, l.982, and l.984.
- Covariance note l.111 now cites Step 8's size bound instead of l.164.
- Hashes: the D2.6 closure is 401e8979853b, and the covariance note is 6e7d16e286fe. The map at 37b104b27c22 had 1613 lines: the edit that removed l.164's old route text also removed its line break, and l.165 had merged into l.164. The break was restored at 10:27, and the map is back to 1614 lines (ce78b3957dfe).

## Map l.193: the K → ∞ Statement (10:27–10:30)

- Not closed. The open part is the continuum limit along the full sequence, the Cauchy estimate (9) of WILSON_IT1_CONTINUUM_CUTOFF_COMPARISON_2026_10_27.md §7.
- Read for this item: the continuum note's header, (1)–(2) and (7), and the cutoff note's §6.13, §7 and Focused Review.
- l.193's OPEN sentence was out of date and now states what the continuum note derives:
  - subsequences given D(K′);
  - κ^{(K′)} divided out (item (6));
  - errors K-uniformly bounded (item (5));
  - large-field terms through Σ_ℓw_ℓ = 1 (item (8)).
- (Q) and (Q″) are needed only for the mass bound, not for the limit.
- What is left is the full sequence.
- Corrected at 10:40: the first version of l.193 (10:30) said that no derivation supplies the depth decay. That was wrong: WILSON_IT1_CAUCHY_ESTIMATE_2026_10_27.md derives the Cauchy estimate, largely unreviewed, with four open inputs:
  - (LF) through ingredient (γ);
  - (R-Δ^c-T);
  - the lift condition at complex configurations;
  - the 𝐑 version of (5.1c) at complex configurations.
  Its §11 replaces (Q) and (Q″), so the (Q) remark below is superseded. l.193 now states this.
- (Q) as posed is pointwise in the exterior data. A lower bound on D_ℓ there needs the free minimiser U₀ to pass the χ_{K′}-tests with a margin. VAR Theorem 1 (8) gives that only for data B₃ times below the threshold, so exterior data near the threshold are not covered. A margin split would need a large-deviation bound for the small-field measure at the stopping scale. Not attempted further.
- Map 1614 lines, 2f10a769e01e.
- Correction (12:30, after the dependency audit): the 10:40 bullet above is wrong on one point. §11 replaces (Q) only. The Cauchy note never mentions (Q″), so (Q″) stays OPEN for the mass bound. l.193 now says so.

## Dependency Audit of the Drafts (Launched 10:50, Triaged 12:25–12:32)

Six `claude -p` runs (claude-opus-5-5) were launched at 10:50 on the user's request "Run a general audit of the drafts and their interdependence". The runs were audit-dep-{mapgaps, intomap, d26, continuum, it1note, global}-20261029-r1. Each had cli_brief.md (a shared part and a slice) and inventory.md, a regular-expression index of 20 drafts and 88 cross-file references. All landed between 10:59 and 11:05. No run found a fatal finding or a circular proof. The common verdict: the structure is acyclic, but the map's gaps block was not a complete ledger.

Inventory error: the script counted one line too many (a trailing newline). The reviewers' "the map has 1615 lines" comes from that; the map has 1614 lines.

**Confirmed OPEN items that were missing from the gaps block, now entered:**
- D2.7 15.8 has three OPEN items:
  - the per-cube link comparison with LFR II (1.94);
  - the bound Pol ≥ (K/2)(d′+1) of the adopted route's step (2): D2.6 closure l.150 assigns it to D2.7, and D2.7 has no Pol;
  - O2 at k > N, asserted in one clause of 15.8(e).
  - They are entered at map l.193, l.156, and l.342, D2.7 l.3 and the 15.8 heading, D2.6 closure l.150, and continuum note l.3 and l.5.
- The O6 consumers' replay is now at map l.199, as an input of (S-w) and (Z) (l.170, l.171). It is also at D2.6 closure R2 and R15, and at SW §7.
- (iv-a) and (iv-c) of the background iteration carry no status and are derived in no draft. They are OPEN at map l.165, together with (iv-b)'s creation-position count. The ONE MORE STEP heading (l.57) now names this.
- O4 is now in the gaps block (l.226 entry): reviewed NOT CLOSED twice, the repair of S1′ unreviewed. The O4 note's "closed" (l.5, l.128, l.135) is restated with its review state.
- The base case (map l.211, new OPEN entry inside the D2.0 line): D(1) rests on IT-1's repairs K and K′, the §3h(7) thresholds, and 𝒬⁺. These are not checked against V4. V4 has no "repair K" text; whether its constant chain matches is not read.
- The D2.7 inputs (R-eval), (R-round), and (R-att-ext) are derived, not reviewed. C₀ ≥ C_KC₁ is for the user's review. L ≥ 6·10⁵ comes from (6C). (R-member)'s single-loop relevance is not stated in D2.7. All are now in l.193.
- (Q″): see the correction above.
- (γ): l.193 now lists point (11) of (LF-A) and the deep-V(Y) part of ν_j, and says that (LF) conditions every term of a_K except §4. The Cauchy note's Result line (l.40) now names all four open inputs.
- Covariance note:
  - (K3)'s C_av is an input with no source; it is named at l.168.
  - Whether a carried dev insertion depends on σ is now OPEN as a definition at l.168. If it does, the second half of l.961's margin is spent twice (covariance §3(c) and map l.1498).

**Stale text, checked and corrected:**
- l.170: (7)(R) is in the cluster form (l.1396).
- l.1136: D2.6's collar species is derived (closure §2.1–§2.2, §4.3), and (T-dev)'s other inputs are derived given readings.
- l.1094's "D2.5–D2.7 at K′ not written" is corrected; the error-bound inputs at K′ stay OPEN and are named in l.193.
- l.16, l.1097, and l.1213 now point to the Cauchy note. l.1097's "κ^{(K′)} OPEN" is removed.
- l.226's "D2.5–D2.7 not started" is corrected.
- l.173's "CLOSED" now reads "derived given an amendment".
- l.222: round 45.
- l.1310, l.1322, l.1415: (LPG′) reviewed, with R-17b.
- l.1589 and l.170: SW §2–§3 reviewed.
- l.1582: the superseded C_S′.
- l.105: χ^c parity, checked.
- l.629: the X_W pointer.
- l.165: the background-closure pointer is now §3.4 (l.73) with (C3).
- l.164: the KP condition's section is now §2.2 *Size* (2).
- D2.6 closure l.161: ρ_ω with + 2C_{c₀}.
- O4 l.74 and l.96: ρ_ω and C_ω with + 2C_{c₀}, and the c_G pointers.
- SW l.107 and l.111.
- Two-loop note l.57: the current is derived.
- IT-1 note:
  - l.1819: D1.0(P)(ii) derived;
  - l.95: review state;
  - l.96: O2′;
  - l.904 and l.1757: O4;
  - l.1805: δ*^{30} at 61/16;
  - l.1798: D2 exists;
  - l.1796: thin form.

**Not changed. Each needs a decision or more reading:**
- (12)(a)–(b): l.170 says "accepted by the user", and l.1416 says "for the user's review". Corrected 12:53 (date): the acceptance is on record (handover, round-33 entry of 25 Oct: "Then the user accepted (12)(a)–(b) and C_box ≥ 4A_E"; WILSON_IT1_D26_TRIAGE_R33_2026_10_25.md *(12)(a)–(b)*). The 12:32 search covered only the WILSON_IT1_TRIAGE_* files and missed the D26_TRIAGE files.
- l.1094's remaining OPEN: whether the inputs of the error bounds of (iii) use Bałaban's steps beyond K′.
- F15 (global): whether D2.7 item 1 (𝐑 = identity for k ≤ N_k) discharges class (ii)'s 𝐑 check (map l.166). Not read.
- F21 (global): D2.7 items 10–11 still say "not derived" while the map cites them through item 15.
- Minor and left as is:
  - stale version pins (D2.6 register at 2c2c54e67530, walk note pins);
  - the D2.6 register misses (F12 of d26);
  - SW (6b)'s radius wording;
  - the IT-1 lines 626, 661–664, 764, 1305, 1334, superseded by l.1819 and pointed to from there;
  - the δ_j index in the LF note (an LF γ file, not edited);
  - point (11) in the Cauchy note's l.12 (the LF γ stream's text, not edited);
  - the D2.6 closure title's triage pointer;
  - the open-items closure's superseded sections.
- Hashes after the repairs:
  - map 9e1aa7afa9dc (1614 lines);
  - IT-1 d17834774e0c;
  - O4 8baf8e8c1ff4;
  - D2.6 1834b692b4f5;
  - D2.7 8d34ac992bbc;
  - continuum 4dbd4f0d5f0f;
  - Cauchy 7eaf6bf9864a;
  - SW 6d12ce943e07;
  - two loops c536bea3a629.

**Acceptance labels checked (12:49–12:53, date; user: "check whether this is also true for the other ones").** Every "accepted by the user" label has a record: R-L3 and R-loc's conventions (23 Oct, "I agree"), R-s (22 Oct, "(a)"), β₀ ≤ 1/2 and L₀ = 5000 (D26_TRIAGE_R32), κ ≥ κ_D′, the linked-hull arc rule, (R-m′) with q₀ = q₁ provisionally, (T2), (T0), (12)(a)–(b) and C_box ≥ 4A_E (handover round-33 entry), A-col (26 Oct). Stale "for the user's review" labels on accepted or implied items, relabelled within lines:
- map l.270 (w_t's rate, part of (12)(b));
- l.1294 (the σ_{k+1} convention, (12)(a)) and l.1416 ((12)(a)–(b));
- l.1372 (q₀ ≤ q₁, met by q₀ = q₁) and l.1379 ((1+β₀)⁸ < L, from β₀ ≤ 1/2 and L₀);
- l.1436–1443 (the D2.4 review list: κ_D, σ_{k+1}, (1+β₀)⁸ < L, and q₀ ≤ q₁ marked settled; R-vac(i′) is Bałaban's and needs no decision) and l.200 (R-vac(i′));
- l.1589 (SW §2 accepted, §1 and §3 pending);
- SW closure l.109 (q₀ = q₁ and C_box ≥ 6 moved to the accepted sentence).
Still pending, with no record of a decision: the ℓ_C restriction to multiples of L^{q*} (l.192, l.1090, l.1217); the amendment ρ̃_k = ρ_k/ᾱ_k with the per-insertion form and (ii-t) (l.200, l.1339, l.1441); R-I7 (l.1439); C₀ ≥ C_KC₁ (l.193); the sub-domain form of D(k)(iii)-dev (l.173, l.1614, SW §3); SW's collar rule §1(a3), §5(e), (C-M), and M ∈ R₁M₁ℕ; the D2.6 closure's conventions in its l.159 list, among them the carried weights of §5.0 (map l.302), the ω-polydisc (l.320), r_{ω,j} (l.954), the collar species conventions (l.1136), and the shift convention as amended by O4 §4(e) (l.226, l.336, IT-1 l.904, l.1707, D26 l.161); R-dec⁺ (D26 l.79, a reading). Hashes: map c219b23fb79f (1614 lines), SW closure 199cf2d7fc3d (112 lines).

**R-I7 accepted by the user (29 Oct, "I accept 3").** No earlier user acceptance is in the transcripts. R-I7 had been checked against the sources on 25 Oct 23:15, after "check the readings!" (CRE's (I.7.1), (7.2)–(7.11), (I.7.12), (I.7.13) are RG2 (2.1)–(2.13) as printed, and RG1 has only Sects. 0–5; D26_TRIAGE_R33 *"Lemmas 5, 6 [I]", R-I7*), but its entry in the D2.4 review list was not removed then. Labels at map l.223, l.741, and l.1436/l.1439.

**R-dec⁺ checked against the sources (13:3x–13:45, date; user: "Check R-dec⁺ against the sources").** Not a reading. The closure had posed R-dec on (4)(e)–(f)'s polydisc (|t_YB′| of order α_{1,k}) and called its use at radius ε_H an extension. The sources are stated on absolute B′-ranges: RG2 p.6, (1.18), prints analyticity in (s, B′) and |𝐇_k| ≤ 4B₀e^{16κ₁}|B′| in all admissible norms for |s| ≤ e^{κ₁}, |B′| < ε₃; VAR p.307 prints analyticity of 𝓗 on 𝔤^c-valued B satisfying (172), |B′| < 2C₁ε₁, and Proposition 9 (p.309) the derivative bound (190) there, uniformly in B; CRE p.267 carries these operators to the multi-domain step ("essentially the same as before"). With 𝓗(0) = 0 and the range convex, integrating (190) along τB′ gives the per-layer bound linear in sup|B′|; the complex-s factor and the per-layer rate are R-dec's. So R-dec⁺ is R-dec on its sources' ranges, under ε_H < ε₃^{RG2} and ε_H ≤ C₁^{VAR}ε̄₁/(2c_V), both already in D2.1(4) *Constants*. The complex V′ of (172) is printed (VAR p.307, Proposition 9), not part of a reading. Relabelled in the D2.6 closure §4.2 (l.79) and moved in its §8 list (l.158) from the readings to "Derived from their sources". D2.6 closure 4d41410ae11a (177 lines, LF).

**D2.6 conventions checked against the sources (13:45–13:57, date; user: "Check the D2.6 conventions against the sources").** The items of the closure's §8 review list, one by one.
- Printed: R-Z (CRE p.264, "Z_k = Λ_k^c"; LFR I p.177, the components of Λ_k^c; LFR II p.384, factorisation in components of Z_j), so it is not a reading; M ∈ R₁M₁ℕ (VAR Thm 1, p.279, "M is a multiple of R₁M₁").
- Derived: R-17 and R-17b, from VAR Thm 1's uniqueness of the critical orbit (p.279, no condition on cube size), CRE (1.3), p.246, and R-Mk (printed, READINGS_RECHECK row 6).
- Within printed conditions: the re-run of LFR II's induction with the doubled O(1), 4(1 + C_X)(64)^d at j = 1, and τ̂² := max(τ², Cρ̂). LFR II requires only "p₀ large, and g₁ sufficiently small" (p.385) and "p₀ large and γ small enough" (p.387), and a larger constant leaves these unchanged.
- Checked against V3: (Z-h)'s structural input. The step-1 pairings are V3's selected integrals (c-selected-integral, L812–819) against μ₀ and μ_{C_{E₀}}, whose covariances come from the torus form H (L778, L4915); V4 L1782 and L2251 agree.
- Accepted earlier: PBG p.411's tie rule (R-tr), (12)(a)–(b), κ_D′, and L₀.
- Our definitions, fixed by no source: the collar rule with d₀ = 6 (CRE p.265 prints the thickenings ∼4 to ∼6; the choice of d₀ is ours), the collar species, r_{ω,j}, Z₁ = Λᶜ at step 1, the global rescaling replacing the bondwise clip, ℓ_s, and LM ≥ 4ℓ_s + 4ρ_L. They are derived where used; whether they are right is a matter for the referee, not a user decision.
- Still pending for the user: the ρ̃_k amendment with (ii-t) (closure l.161).
- Labels changed:
  - D2.6 closure l.43 (R-Z printed), l.158 (R-Z moved from the readings), l.159 (header, the LFR II re-run, and the D2.4 carry-overs settled);
  - map l.169, l.1136, l.1310, l.1322, l.1415, l.1614 (R-17 derived; collar conventions);
  - SW closure l.6, l.19, l.63, l.75, l.83, l.108–109.
- Hashes: map 677493b122d1 (1614 lines), D2.6 closure 26477268335f (177), SW closure 896dbaba6d34 (112), all LF.
- Correction to the report of 13:57: the closure's l.161 "for the user's review" was the O4 frozen-centre amendment (the sub-polydisc 𝒟^{sub}_{ω,0} and §6.4 for the t > 0 species), not ρ̃_k; ρ̃_k sat on the map's list (l.200, l.1339, l.1436, l.1441).

**Four amendments relabelled as referee items (14:4x–14:50, date; user: "Yes, relabel all four as referee items").** No source states the inductive hypotheses; each amendment is forced or derived where used, and what remains is whether the consumers lie inside the stated domains, a referee check.
- The items:
  - ρ̃_k = ρ_k/ᾱ_k with the per-insertion form and (ii-t), forced by D2.4(4)'s Cauchy step (map l.1341): map l.200, l.1339, l.1436, l.1441;
  - the O4 sub-polydisc and the §5.0/§6.1/§6.4 amendments: D2.6 closure l.161; map l.226, l.320, l.336;
  - the sub-domain form of D(k)(iii)-dev (SW §3): map l.173, l.1589, l.1614; SW l.109;
  - the per-traversal comparison region (SW §5(e)): SW l.109.
- Left over from the D2.6 conventions check and fixed with them: r_{ω,j} (map l.954) and the collar rule (map l.1589) are now marked as our definitions.
- SW l.3's status word *for review* is redefined as derived where used and checked by the referee, with the user's acceptances marked.
- Still for the user: the ℓ_C restriction (map l.192, l.1090, l.1217) and C₀ ≥ C_KC₁ (map l.193).
- Hashes: map e2fff0eebcfe (1614 lines), D2.6 closure 3381a04df6a8 (177), SW closure 09a080100784 (112), all LF.

**ℓ_C restriction accepted by the user (14:5x–14:58, date; user: "I accept but have condition 2 be a cleared spelled out as a future possibly necessary improvement but not a gap").** The restriction is accepted in the per-loop form: the stopping scale uL^{−j(C)} is chosen per loop, so no L-adic square is excluded. "Condition 2" is the loop-dependent coupling threshold. ONE MORE STEP (7)(d)'s error O(ℓ_Cε_{K′}/L) makes the smallness conditions per loop, and that dependence on p is present without the restriction too. The per-loop stopping adds a q-dependence through j(C). This is spelled out at the map's D2.3(4) *Result* (l.1097) as a possible future improvement, not a gap: what a uniform threshold would need, and when it matters (statements uniform in the loop size). Labels at map l.192, l.1090, and l.1217. Map 98100bc1a15a (1614 lines, LF). The only item still for the user is C₀ ≥ C_KC₁ (map l.193). The dated status reports of 26 and 27 Oct are left as they stand.

**C₀ ≥ C_KC₁ checked against D2.3–D2.6 (15:0x–15:05, date; user: "Run the D2.3–D2.6 check first").** This closes the two-loop triage's open point (TWO_LOOPS_TRIAGE_R1 l.706): the choice had been checked against SW (c2)–(c3), map l.1372, and j*, but not line by line against D2.3–D2.6. Every occurrence of C₀, C₁, α₀, α₁, and ᾱ was read in map D2.2(6)(e) (l.922–976), D2.3–D2.4 (l.993–1614), the D2.6 closure, and the SW closure.
- No condition needs C₀/C₁ bounded independently of L and M, and none bounds C₀/C₁ from above.
- One condition points the other way and is helped by the choice: M ≥ 2C_avC₁/C₀ (map l.168, SW l.103).
- The equality-case lower bounds C_i/A₀ > … are unused under (R-m′). RG2 p.20 bounds (LM)⁴α₀ and (LM)⁴α₁ separately (map l.1252), which g small gives.
- With C₀ ≥ C₁, ᾱ = α₁, so the following do not depend on C₀: the Cauchy factors, C_T, b_n/ᾱ_n, c̄, S_H's factor 1 + C₁/C₀, and the carried complex-data size 3S₃₀ρ_k.
- Two constants grow with C₀/C₁:
  - the att constant of the reclassified dev insertions (map l.1370; D2.6 closure l.73, (C₀/C₁ + 1));
  - the new groups' complex-data clause (1 + 2C₀/C₁) (SW l.93).

  Both are source terms fixed after L and M, are not compounded across steps, and multiply O(g²·polylog) amplitudes, so g_K small absorbs them.
- (6b)'s factor comes from a single Schwarz radius. A direction-scaled radius in map l.318's ϱ/r_J normalisation would reduce it to 3. This is optional and was not applied.
- Recorded within the two-loop note's l.12; the note is still 887 lines, hash 21843e4e2a3a. A first version added seven bullet lines, which would have shifted the note's own line references (e.g. l.131's "l.49"); it was merged back into l.12.
- The decision on C₀ ≥ C_KC₁ is still the user's.

**C₀ ≥ C_KC₁ accepted by the user (15:08, date; user: "I accept it").** Labels at the two-loop note's l.5, l.12, and l.811, the D2.7 closure's l.5, and the map's l.193. With this, no item in the map, the D2.6 closure, the SW closure, the D2.7 closure, or the two-loop note awaits a decision by the user; what remains are referee items and the OPEN items. Hashes: two-loop note 80ad4491ceef (887 lines), D2.7 closure 48fb5d607d06 (236), map 19f93050e03e (1614), all LF.

**Wave D launched (15:41, date; user: "Rebuild and run wave D").** The six packets were rebuilt against map 19f93050e03e and D2.6 closure 3381a04df6a8. The d26-s8 spec now names R-Z as printed and R-dec⁺ as derived, and asks about the l.159 conventions. Runs: it1-d26-s8, it1-onestep, it1-onemore-a, it1-onemore-b, it1-d23-a, and it1-d23-b, all -20261029-r1. The covariance note is deferred to the next wave. Reviews to be triaged below as they land.

**it1-onestep-20261029-r1 (landed 15:50; triaged and repaired 15:50–15:52, date).** No fatal finding. The derivation proves the upper bound once two hypotheses are added. Findings and repairs (map ONE STEP, l.21–56):
- Serious 1: the Result and (5) bullets 1–2 presented upper bounds as the size of the difference ("of order gℓ_C/ε", "L/ρ further", "small only for"). *Repaired:* the Result says "This is an upper bound … No lower bound on the difference is derived"; (5) bullet 1 says it compares two upper bounds, not two distances, with C_χ's dependence on L and χ (V4 L157); bullet 2 says "small for n_C ≪ L/ε₁. Nothing here shows when the difference itself is small".
- Serious 2: the numbers were stale against V4's current Lemma c2-plaquette-deviation, 2c_hε₁L^{−2} (V4 L4141–4145), and against map l.167. *Repaired:* (I4), (2), (3), (4), and the Result use 2c_hε₁L^{−2}: s := 2c_hA_Lε₁L^{−2} ≤ 6c_hε₁, ξ ≤ 6.4c_hε₁ per coarse bond, and the loop bound e^{6.4c_πc_hn_Cε₁/L} − 1, matching prop:coarse-loop-form's e^{6c_hn_Cε₁/L} up to the constant. (5) bullet 3 now says the L^{−2} is V4's lemma for the minimiser, while a general regular field has only 2c_hε₁. l.167's "improve to" sentence now says ONE STEP states them with this lemma.
- Minor 3: the missing hypotheses s ≤ 1/10 and t ≤ r_G. *Repaired:* both are in the Result. (2) states t ≤ r_G for X_c ∈ 𝔤, with the SU(3) counterexample, and the 1.06 check (ratio 1.0522 at s = 1/10, failing at s = 0.5). (4) names both conditions.
- Minor 4: the stale V4 line numbers. *Repaired:* V4 lines in ONE STEP are pinned to 563736a8dfb9 (Setting): L461 (U₁ among the critical points of CRE (1.12)'s constrained functional), L283 and L2357 (Λ_b ⊆ I), L2458 (I), L4141–4145 (the lemma), L4149 (its proof), and L254, L252, L157.
- Minor 5: the orientation of reversed coarse bonds. *Repaired:* Setting says c_j = ±c and states the inverse-consistency of RG1 (0.4).
- Minor 6: the dropped polylog and L. *Repaired:* the bound is written e^{O(L^{−1}g₁p₀(g₁)ℓ_C/ε)} − 1.
- Minor 7: R-str was not flagged. *Repaired:* Setting cites RG1 p.252 and names R-str (l.142).
- Header: "(derived; reviewed: no fatal finding; repairs not re-reviewed)".
- Map c2936307598f (1614 lines, LF). The other five wave-D packets carry map 19f93050e03e. Their ranges (l.57–162, l.993–1218, and the D2.6 §8 lines with map l.336 and l.1136) were not touched, so the line numbers hold; their hash mismatch is expected.

**it1-d26-s8-20261029-r1 (landed 15:52; triaged and repaired 15:53–15:55, date). NOT ACCEPTED AS STATED, no fatal finding; all findings concern status and labels.** The review was context-exposed on R-Z and M ∈ R₁M₁ℕ through one Grep hit in this triage file (it disclosed this). It reverses two labels of today's D2.6 conventions check (13:45–13:57), and those labels were wrong:
- Serious 2, R-dec⁺ is a reading, not derived. RG2 (1.18) has complex s in [I]'s single sequence, with a global bound and no layer rate. VAR (172), (190) have the multi-domain layers at s ≡ 1. The joint statement on |B′| ≤ ε_H rests on R-dec plus reading CRE p.267 as carrying RG2's range. *Repaired:* §4.2 (l.79) now reads "Reading R-dec⁺ … logged, for review", says what is derived (the s ≡ 1 layer bound from VAR (190)) and what is read; l.158 moves it back to the readings.
- Minor 3, M ∈ R₁M₁ℕ is VAR Theorem 1's printed hypothesis (p.279), not a printed fact about CRE's M = L^m (p.245). It is met by choosing R₁M₁ a power of L, within VAR p.277's freedom. *Repaired:* D2.6 closure l.159 and SW l.109.
- Serious 1: l.156's derived list omitted the OPEN O6 bracket-term replay for its complex-σ_k consumers, and called O4 "closed"; the bold status lines at l.62 and l.79 had the same omission. *Repaired:* l.156's header and the §2.1–2.2, §4.1–4.5, and §7.1–7.3 entries carry "for O6's bracket terms OPEN until the replay"; O4 reads "derived in the frozen-centre form; at its last review NOT CLOSED, its finding S1′ repaired and awaiting re-review"; l.62 and l.79's bold lines carry the same qualification; §2.3 is added (minor 6).
- Serious 3: map l.336 said "except R6" and "O1 closed". *Repaired:* it reads "O1 derived, for re-review", and adds the exception "at complex σ_k, R1 and R15 for O6's bracket terms, OPEN until the consumers' replay".
- Minor 1: l.158 stated R-𝐁 with Λ_kᶜ. *Repaired:* Λ_{k+1}ᶜ. The derived core (every term of (2.40)–(2.41) at step k meets Λ_{k+1}ᶜ, from p.261, Theorem 1, and (G1)) is separated from the reading (that p.276 l.42–44's re-localisation keeps a domain containing the old one).
- Minor 2: the l.159 heading was contradicted by its own items. *Repaired:* "none is fixed by a printed statement except where marked; the items accepted by the user are choices, and (R-m′) is a provisional hypothesis; the rest are derived where used".
- Minor 4: the attachment target set is fixed by print (LFR II p.384 with R-Z). *Repaired:* only the assignment rule is ours.
- Minor 5: route (a)'s qualification. *Repaired:* l.158 names the accepted premise (p.256's sets VAR-admissible, from Bałaban's use on pp.257 and 269), p.266's layer reasoning, and the p.269 misprint reading.
- Minor 7: *Repaired:* map l.1136 names R-𝐁, R-vac(ii-bd), R-fr, and R-dec⁺ behind the collar species; map l.777 names R-vac(ii-bd).
- Minor 8 (unused conditions in l.160, marked there as unused) and minor 9 (R-17 not checked, a cross-reference): left as they stand.
- Confirmed: R-Z printed (CRE p.264 l.52, LFR I p.177, LFR II p.384 l.4); R-𝐁 and R-vac(ii-bd) correctly readings; the LFR II re-run within its printed conditions (p.385 l.37, p.387 l.28, under p₀ > r(d+2)); PBG p.411 leaves ties free; q₀ = q₁ and q₁ > p₀ within CRE p.259's freedom; no misquotation.
- Hashes: D2.6 closure 7eb3c42d40b7 (177), map 9fffdb018d4b (1614), SW closure c9650d84b108 (112), all LF.
- Housekeeping (15:59): the afternoon entries had been inserted inside the dependency audit's "Not changed" list; its last 22 lines (l.1094's OPEN through the hash list) are moved back under that list.

**it1-onemore-a-20261029-r1 (landed 15:5x; triaged and repaired 15:55–15:59, date).** No fatal finding; one serious, nine minor. Items (0)–(4) and the parity argument of (5) are correct at their stated scope, with correct citations. Repairs (map ONE MORE STEP, l.61–111, within lines):
- Serious 1: l.108 said the 𝐄₁ links are analytic only inside the α_{1,1}-margin, contradicting l.64 and l.111. *Repaired:* the 𝐄₁ difference is an RG2 Lemma 1 term with class (i)'s radius (CRE p.254 after (1.30), RG2 p.7; closure b1, b4), the 𝐑₁ difference is absent for k ≤ N (R-h), and only the 𝐁₁ and A(·) differences and V^{(1)}(S₂) (analyticity space CRE (3.43)) have the radius λ_α.
- Minor 2, l.63: the factor (1+β₀)B₃L^{−2} multiplies the exponent, not the bound. *Repaired:* Lip_χ(e^{ax₁} − 1) with x₁ = 6c_hn_Cε₁/L, a = B₃(ε₂/ε₁)L^{−2}.
- Minor 3, l.64 and l.111: the integrand-scaling claim. *Repaired:* closure a1's identity 𝐕₁^{[λ]}(Y,B) = ½⟨Q(Y,B̃)B,B⟩ + 𝐕₁″(Y,B̃) for the potentials; l.111 says W(λ,B) = W(g₁,B̃) fails for the λ^{−2}F terms.
- Minor 4 and 8, l.106–107: ε′ now has closure a2's definition; "|λCA|" with ‖C‖ absorbed; the stale "re-check row 22" label replaced by closure a2's argument (RG2 (1.19)–(1.20) give D̃'s radius ≥ ε₁^{RG2}).
- Minor 5, l.99: the localised potentials vanish at λ = 0 by the linearity of the localisation (closure a1).
- Minor 6: (3)'s header cites D2.1(2)'s reading R-g (l.445); (4)'s header says "derived, given the reading of 'plaquettes of Ω₂'".
- Minor 7, l.65: the "≈" is marked schematic, with the error terms named.
- Minor 9: V4 L396 → L407, L3970 → L4141, pinned to 563736a8dfb9.
- Minor 10: "Result in one line" and "Consequence for the RG construction" are marked as summaries of (5)–(7) with the heading's OPEN items.
- Map e6fc445bac68 (1614 lines, LF).

**it1-onemore-b-20261029-r1 (landed 15:54; triaged and repaired 16:00–16:04, date).** No fatal finding; two serious, ten minor. (5)'s Schwarz step, (6)'s expansion, flat series, Gaussian formula and comparison algebra, and (7)(a)–(d) for K ≤ N were rechecked line by line and hold; (7)(e) stays conditional on (iv-a)–(iv-c). Repairs (within lines):
- Serious 1: class (ii)'s second-order size was called both "not derived" (l.113, l.139) and derived. *Repaired:* l.113 says the α-disc alone gives no second-order size and the size is derived from Lemma 1's disc given the Premise in its unreviewed form; l.113's "Derived" and l.125 carry the same qualifier; l.139 moves it out of "Not derived here" and states its status.
- Serious 2: the K ≤ N scope of (7)(d) was dropped in l.63, l.66, and the continuum note's (5.5). *Repaired:* all three say K ≤ N, with D2.7's input and its OPEN items beyond N.
- Minors: l.111's scaling identity (already repaired after onemore-a); RG2 (1.20) no longer cited for the lower bound (B′ = g₁B off the designated bonds, RG1 pp.267–268); RG2 (1.7) quoted with M₁^{−1/2|ω|}; "(common dressing)" → e^{𝓔₂^f}; l.120 "(derived, given R-cov, the H_{1,1} reading, and the 𝐀_{1,1} clause)"; ε′ is closure a2's throughout (l.117's 1.06 and 2.12 conditions follow from it; l.120's parenthesis updated); the nesting Ω_K ⊆ Ω_j is printed (CRE (2.1), p.256); the k = K chart condition without L² added at l.158 and l.165; (S-w) and (LPG′) now carry the SW closure's real review state (NOT CLOSED, S1 OPEN at l.168) at l.62, l.126, l.165, l.361; V4 pointers L693 → L722, L1171–1173 → L1217–1218; l.1097 cites the stopping-scale error O(ℓ_Cε_{K′}) of the k = K bound, with (7)(d)'s O(ℓ_Cε_{K′}/L) as the sum over k < K.
- Map 7d25aaa6df6e (1614 lines, LF); continuum note 5b500210417d (156 lines, LF).

**it1-d23-a-20261029-r1 (landed 15:57; triaged and repaired 16:04–16:10, date).** No fatal finding; three serious, nine minor. D2.3(2)–(3) are correct as stated; (4)'s period, placement, admissible-side, and stopping-scale arguments are correct. Repairs (within lines):
- Serious 1, (Z-h) l.1132: the step-1 covariances depend on U₁ through the regional Hessian H = H_{ξ,II} (V3 L711), and V4's periodisation bounds only the flat kernel. *Repaired by a derivation:* V3 lem:c5-1-1's Neumann series H^{−1} = h₊^{−1}ΣK^n, K = 1 − h₊^{−1}H of range ρ_L. On the complex domain ‖K‖ ≤ q = 1 − γ/(2h₊) under C_H′w ≤ γ/2 (entries analytic on a fixed stencil, a condition on g₁). Paths that stay in the agreement neighbourhood N give equal terms on T and T′, so ‖C_T(U₁)(b,c) − C_{T′}(U₁′)(b̃,c̃)‖ ≤ 4γ^{−1}e^{−μ′(d(b,c)/2 + r)}, μ′ = −log q/ρ_L, r ≥ Lι_{T,1}/4 − R. The same holds for C_{E₀} (exact agreement within N by the component blocks) and for G^{1/2} (V3's binomial walk series). With V4's edge majorant at μ₀ ≤ μ′/2, h_A ≤ (4γ^{−1}e^{μ′R}/A₀)e^{−μ′Lι_{T,1}/4}, so c₁ := μ′L/4 (was 2μL), and l.1609's (C-rel) becomes 24μ′ML⁵(L²−1) ≥ log(35L), a lower bound on M. Header: "not re-reviewed".
- Serious 2, (Z-c) l.1110, *Base* l.1117, (Z-d) l.1118: the exactness claims now except the non-embedding vacuum clusters in e^{−Ψ°(M)}, δΨ(M), and the link sums, whose difference is the tail C⁎ already in C̄_Z.
- Serious 3: (3)'s heading names D2.4's convergence and Kotecký–Preiss condition; (4)'s heading says contour locality and (Z) are derived given (S-w) and its inputs, some OPEN.
- Minors repaired: R₁M₁ a power of L by V4 eq:c-standing-conditions (l.1080, l.1103); the transport law T ↦ π(u(x))Tπ(u(x′))^{−1} (l.1042); (1.14) covered by RG2 p.15 (l.1032); CRE (2.12)/p.256 for the large-field minimisers (l.1033); the transport norms in the interchange condition (l.1061); "compact connected simple G" (l.1093); PBG p.416 for Thm 3.10, p.413 for R(X) (l.1129); C_Σ's ℓ_C-independence needs T_ph ≫ log ℓ_C (l.1185).
- Minors left: PBG p.408's context; RG2 p.13's omission ", but not for (C^{(k)})^{1/2}" (covered by (2.7)); V4 pins at d463c554b76f and b35c60e537b8 in (1) and (Z); R₀'s double use at l.1131.
- Map 16e6b980c5cf (1614 lines, LF).

**it1-d23-b-20261029-r1 (landed 15:55; triaged and repaired 16:10–16:12, date).** No fatal finding; one serious, eleven minor. D2.3(5)–(8) derive the exact absorption, the corner and torus bound on E°_{k+1}, its K- and ℓ_C-uniform sum, and the assembly, all given (S-w). Repairs (within lines):
- Serious S1, l.1186: "(b) was the only user of the upper bound … D2 does not use R-cpl" was false; the D2.6 carry lemma (§5.0) uses it (l.348, l.202, D2.6 closure l.86). *Repaired:* D2 uses the upper bound through BETA_FUNCTION_WILSON_LOOPS.md Corollary 8.2, which covers V4's compact connected simple G, not through R-cpl.
- M1: the torus term is 12C̄_Z (3C_Z per traversal from (Z-f) *Limits*, four sides); map l.171, l.1128, l.1161, l.1168, l.1180 and continuum (5.2).
- M-E: the E_const clause carries 𝔞_j = max(τ_{j−1}², ρ_j·pl) and the rate c^Z (l.1188, l.312, l.1214).
- M3: the straddling straight-line clusters named at l.1152. M5: (7) and (8) headings "given (S-w) and the Kotecký–Preiss condition on every ℓ". M6: C_Σ depends on c^Z (μ′); T_ph ≫ log ℓ_C was added at d23-a.
- Left (minor, recorded): M2, the transfer of (T′) to the ℤ⁴ line and bent-path gases "by Fatou through (Z)" is not written out; M4, μ^R's sign at R-steps in D2.7 15.4 (D2.7 file not edited); M7, (9)'s readings list omits CRE (2.6)–(2.7) and R-cpl₀; M8, V4's R_0/R_* offset and step-1 rate; M9, off-by-one constants, absorbed; M10, stale V4 pins.
- Map 64ee30690fd5 (1614 lines, LF); continuum note 9e48b0b2bc1e (156 lines, LF).

**Left minors closed (16:30–16:31, date).** d23-b M2: (T′) on ℤ⁴ is now derived (map l.1142, l.1144): the line and bent-path gases are defined as clusters of a square gas meeting one side or one corner's rays, each ℤ⁴ cluster is a cluster of large squares on large tori by contour locality, the torus- and contour-uniform (12)(f) bounds the truncated root sums, (Z) passes them to the limit, and monotone convergence removes the truncation. M7: (9)'s readings list adds CRE (2.6)–(2.7) and R-cpl₀ (l.1216). M8: V4's network-length offsets (+R_0, −2R_*) and step-1 rate go into C_S′ and c_d (l.1144). d23-a: V4's margin renamed R₀^{V4} at l.1131. Still left: PBG p.408's context and the RG2 p.13 omission (quotation details, harmless); stale V4 pins in (1) and (Z). Map f3148252c88f (1614 lines, LF).

**Wave D2 launched (16:48, date; user: "Run the next wave").** Packets built against map f3148252c88f: it1-cov-a-20261029-r1, it1-cov-b-20261029-r1 (the covariance note, l.1–83 and l.84–183), it1-d23-a-20261029-r2 (with Q6 on (Z-h)'s new derivation), it1-d23-b-20261029-r2, it1-onemore-20261029-r2, and it1-d20-20261029-r1 (rebuilt; the 02:13 folder was never launched). Reviews to be triaged below the wave D entries as they land. Paused at 16:54 (user: "Pause them"): all six stopped before writing a review; session IDs kept in each folder's cli.session.txt for -Resume.

**Wave D complete (16:12).** Six reviews, none fatal; all serious findings repaired, two by new derivations ((Z-h)'s covariance comparison; ONE MORE STEP l.108's radius split). Not re-reviewed: those repairs. Next wave (next window): the covariance note's packet first; candidates for re-review are (Z-h) and the d26-s8 labels.

**Wave D2 resumed (18:09, date; user: "Resume wave D2").** All six with -Resume on their saved sessions, map f3148252c88f unchanged.

**it1-d23-b-20261029-r2 (landed 18:14; triaged and repaired 18:15–18:17, date).** No fatal or serious finding. D2.3(5)–(8) as repaired correctly derive (T′) on T and on ℤ⁴, the coefficient bounds, the E° bound with 12C̄_Z, the uniform sum, the E_const clause with 𝔞_j, and the assembly, given (S-w), the Kotecký–Preiss condition on every ℓ, and Cor. 8.2. Minors repaired:
- M4, the R-step sign: μ^R is the flat-series coefficient (D2.7 l.171, l.191: κ^R = e^{Pμ^R+4ζ^R}), so D2.7 l.173's definition now reads μ_k^R := +(4LΠ^R_k)^{−1}Σκ^R_v, consistent with "δm − μ^R" (map l.1146, D2.7 l.173); l.1146 states (6)(a) and (8) at R-steps.
- M1 residue: 3C_Z^{(k+1)} per root at l.1165 and l.1168.
- M8: the step-1 rate is c_d := min(ν/(64ML), c^{(1)}) with C_S′ enlarged by e^{c_d(R_0+2R_*)} (l.1144; c_E at l.1168).
- (T′) on ℤ⁴: quantifiers with D′, and one sentence on why (12)(f) applies to the auxiliary contour (l.1144).
- Stale wording: l.202 (𝔞 and 12C̄_Z; both users of the upper bound), l.1184 "The second", l.1128 "D2.3(6)(a)".
- Left: τ in place of 𝔞 at l.125, l.134, l.354, l.1098 (step-2 and summary lines; 𝔞 = τ² up to the ρ·pl term); M9, M10.
- Map 0694dcf3e80a (1614, LF); D2.7 closure e1cdeafaac4d (236, LF).

**it1-onemore-20261029-r2 (landed 18:14; triaged and repaired 18:17–18:19, date).** No fatal finding; the prior fatal and serious contradictions are closed; one serious, eight minor.
- Serious 1: class (ii)'s second-order size was also conditional on "D2.7's open check that no part of 𝐑 other than its basic step acts for k ≤ N", which l.139, the result lines, and the claim omitted. *Repaired by closing the check:* D2.7 item 1(a)–(b) (derived) gives 𝐑′^{(k)} = 0 and Rρ_k = ρ_k term by term for k ≤ N_k (LFR II p.390 l.10–11: the admissible domains of 𝐑′^{(k)} contain a large-field region connected with a 𝐓′_k-operation). Map l.113, l.166 (header and body), l.976, l.64, l.108 now cite it. This also answers the dependency audit's F15.
- Minors: the radius variable back to |λA| (RG2 and closure a2 use g|B|; l.106–107); l.108 quotes RG2 (1.34) as |B| < ε₁^{RG2}g₁^{−1}; l.64 and l.108 describe the Premise as derived from CRE (1.26) and RG2 p.10, not as an identity of functions; l.166 uses closure a1's identity and renames its x₁ to x_E; l.114 names closure a1's form; l.113: links are Mayer factors; l.166 states the (3.43) radius as the smaller of its two constraints; the SW closure's review state at l.117, l.118, l.125, l.133.
- Map after the repairs: see the next entry.

**it1-d23-a-20261029-r2 (landed 18:17; triaged 18:19–18:21, date).** No fatal finding; two serious. Confirmed: the (Z-c)/*Base*/(Z-d) exactness repairs, the (3)/(4) headings, c₁'s algebra, the path count, the component blocks, (C-rel) as a lower bound on M.
- Serious 1: (Z-h)'s passage from the covariance-entry bound to the insertions misdescribes V3's representation (pairings against local polymer measures from μ₀ and block-local μ_{C_{E₀}}, with C_{E₀} and Γ_{E₀}(σ) in the integrand), and at complex U₁ V4's majorant needs ‖ΔC‖ ≤ λ/8. *Not repaired as a derivation; status repaired:* (Z-h) is OPEN in that passage (l.1132's header, l.1135, l.1136, l.171), so (I)₁ and (O)₁, and with them (Z), are not derived. What closes it, recorded at l.1132: exact locality of V3's polymer measures (σ_Δ = 0 outside Z confines the walks, eq:fixed-kernel-walk-weakening; C_{E₀} by component blocks; s_H = 2h₊, V3 L717; H local within R), so ΔY_W comes only from the non-embedding vacuum clusters of q_ξ(𝒜) (eq:c-cluster-expansion), paid by (c4-6-5)'s e^{4η𝔰} with diam ≤ 2LM𝔰(W) (V3 L4581, L4615(b)). Its rate (about 5η/(256M) from the e^{(5/16)η𝔰} left after (I)₁) replaces c₁ and then enters (C-rel) and (TC); I did not write it in, because it changes (C-rel) into a condition on the torus constant of (TC), which needs its own check.
- Serious 2 (stale l.1135; status l.1136): repaired as above.
- Minors left for the derivation pass: ‖𝖠_H‖ ≤ (1+q)/2 at complex U₁; the Cauchy/polydisc premise; A₀ ≥ 2γ^{−1}; non-embedding step-1 groups; the ¼ recursion at l.1122–1123 against l.1609; "C_Z^{(1)}, C_rel^{(1)} are V4's"; earlier quotation minors.

**it1-d20-20261029-r1 (landed 18:17; triaged and repaired 18:20–18:21, date).** No fatal finding; one serious. D2.0(3) and (5), as repaired, are correct at their stated scope.
- Serious S1, l.364: "O1 closed" → "O1 derived, for re-review, given the readings R-ζ(a), R-ζ(b), and R-h".
- Minors repaired: RG1 Theorem 3's hypothesis quoted as printed (l.275); the l.281 failure case cannot occur for Z_{k+1} = Λ_{k+1}ᶜ by CRE (3.20). Left: (5)(b)'s τ² wording and the admissible-sides restriction in the Result's bullet 2; (5)(c)'s B_n with ρ̃_k (needs q₀ ≤ q₁, l.1372); (5)(d)'s π irreducible; (5)(f)'s n = j+1 scaling; stale V4 pointers; (3)(b)'s k = 1 normalisation.
- Map a39e97897f32 (1614, LF).

**it1-cov-a-20261029-r1 (landed by 18:21; triaged 18:21–18:23, date).** The covariance note's (K3) and (K4) were labelled closed. *Status repaired:* note l.3 and l.5 now list two OPEN premises, (K3)'s C_av (no derivation or source; what closes it at l.14: a Lipschitz bound for the averages on the complex domain, e.g. ONE MORE STEP (7)(a) extended to complex 𝐔 and 𝐉) and (K4)'s use of the slot dependence (l.15; void if dev insertions carry no slot).

**it1-cov-b-20261029-r1 (landed by 18:21; triaged and repaired 18:23–18:27, date).** No fatal finding; three serious, six minor. Confirmed: the mechanism, §3(a)–(c)'s and §4's arithmetic, the CRE citations, Ĉ's k-uniformity, the recursion and C_S′.
- S1 (slot dependence of dev insertions unresolved): *status repaired.* Note §0 states both cases (slot-free: §3(c), δ̄_m and (K4)'s doubling void, §5 is (T-dev) verbatim); §3(c) marks the half-margin allocation OPEN in the slot-dependent case (three charges on one margin; a three-way split is a smallness condition in g_K by l.963 but needs l.164's half cut to a third); §5 marks (T-dev) uniform over the slot polydisc OPEN (re-run l.1353 (1) with the slot). Map l.168 says the same.
- S2 (C_av unlisted in callers): repaired at map l.1419, l.1614 (status and constants list), SW l.5, l.19, l.95, l.99, l.103, and note l.181.
- S3 (Lemma 3's disc omits the inverse transport): *repaired.* §3(b): sup_disc‖f‖ ≤ S_W·e^{(c_π/2)α_{1,j}Mσ_j(W)} ≤ S_We^{νσ_j(W)/8192} by c_πα·4096M ≤ ν (map l.1614); the display and l.94 carry the factor; §4's complex-data weight is (15/16 − 1/8192)ν_r, inside the free eighth; Ĉ unchanged.
- Minors repaired: m1 (non-covariant disc shrunk to R′ with c_nc := max(1, cC_avC₁/(C₀L)) in Ĉ); m2 (hat slot κ^{−1}σ̂ fixed along the disc; linear extension of ω beyond X_W); m3 ((1+β₀)² at l.120); m4 (l.1353 (2) for the base); m5 (c_G; (2.36) bounds |𝐉|, so |𝐉 − J| < 2r_J); m6 (map l.168's large-W weight e^{−ν_rδ̄_mL^m/(64M)} and constant list).
- Map 077799dd0c88 (1614, LF); note 37011ed8d2db (183, LF); SW 77fa1a69e966 (112, LF).

Wave D2 complete.

**Repairs of the three open gaps (18:30–18:50, date; user: "Yes, repair them in that order!!!").** All not reviewed.
- *Slot dependence of carried dev insertions: derived (none).* Step ≥ 2: a dev group meets no ω′-bond and has only dev members (D2.6 closure 2.1(i), *Merged groups*, 4.2(iii) class (3)). Step 1: Υ⁰_W of a good group has traces c⁰_W − a^Λ_Wχ; c⁰_W consults no outer variable (IT-1 §3d(4): every row input in D(Λ), kernel at exterior parameter zero), and Burnside. So §3(c) spends no margin, l.164's half stands, (K4) is not needed, and §5 is (T-dev) verbatim. Written in: covariance note §0, (K4), §3(c), §5, l.3, l.181; map l.168, l.1419, l.1614; SW l.5, l.19, l.95, l.99, l.103; D2.6 closure 4.2(iii).
- *C_av: derived given the reading R-av.* C_av := 2B₃ from RG1 p.263 (1.17): at complex 𝐔 satisfying (i)–(iii) with α′₀, |∂U_n(M^·(𝐔)) − 1| < 2B₃α′₀ξ² and |J_n| < 2B₃α′₀(L^nξ)², "From Proposition 9 [15]". R-av carries this to CRE's multi-domain (2.35), (2.37) by CRE p.267's "essentially the same", the sentence R-dec⁺ also reads. J_{p,X}(M^·(𝐔)) depends on 𝐔 alone (RG1 (1.15)), so there is no 𝐉-average. The disc check needs M ≥ 4B₃C₁/C₀ and ε/α₀ → 0 (q₀ > p₀; CRE (2.28), p.255). Written in: note (K3), l.3, l.5, §3(b), l.181, constants; map l.168, l.928, l.1328 (c₀ now depends on d and L), l.1419, l.1614; SW l.5, l.19, l.95, l.99, l.103.
- *(Z-h): derived, with zero difference.* In V3 a group's insertion is w_ξ(W)𝔔_ξ(𝒜(W); f), and the vacuum clusters of q_ξ(𝒜) are members of the group. Every factor is a finite expression in local data: selected integrals with σ_Δ = 0 off the final domain confine the walks (lem:component-blocks), C_{E₀} is a block inverse, the X-integral factors, the probe measures live on 𝖫_D, H is local within R (V3 L715), and c_W is supported in Q_W. So embedding objects agree exactly on T and T′, at real and complex U₁. (I)₁ and (O)₁ have zero left side and C_rel^{(1)} = 0. c₁ drops out: c = 1/(32M), c^Z = ν/(512M), and (C-rel) is no longer needed. The covariance comparison, V4's density derivative and the image bound are removed. Written in: map l.1122, l.1123, l.1126, l.1127, l.1132–l.1136, l.171, l.1403, l.1591, l.1609, l.1612, l.1614; coarse-chain closure l.102.
- Hashes: map 1986ce6e97a6 (1614, LF); covariance note 5b82723c68c7 (184); SW e75281d56549 (112); D2.6 closure ecdfbfba5b23 (177); coarse-chain closure 7ee8026e0d94 (186).

## Re-reviews of the three gap repairs (launched 18:54, landed 19:07–19:10; triaged and repaired 19:08–19:16)

Builder: verification\isolated_reviewer\build_gap_repairs_rereview_packets_20261029.py; claude-opus-5-5, effort high. No fatal finding in any of the three.

**it1-gap-zh-20261029-r1 ((Z-h); prior d23-a-r2).** Verdict: exact locality of V3's step-1 objects correct; (I)₁ = (O)₁ = 0, C_rel^{(1)} = 0, c = 1/(32M), c^Z = ν/(512M) and the coarse-chain constants checked; r2's two serious findings closed.
- S1 (two accounts of the step-1 base: V4's periodisation with τ² at l.1101, l.1117, l.1128, and l.325) — REPAIRED: D(1) is IT-1's D1 on V3 (l.211, l.884); l.1101 now states the base is (Z-h) and V4's flat regional representation is not part of D(1); l.1117's V4 K_T and vacuum-cluster sentences replaced; l.1128 states the amplitude is ρ·pl also at k = 1 (τ² kept only as an upper bound in 𝔞_k); l.325 cites (Z-h).
- Minors repaired: the pairing's f is the group word on 𝓗(W) (V3 L4604), not f_ξ; "finite expression" replaced by walk series and parameter integrals, with V3 L4917 cited; complex U₁ via V3 L5021 or the identity theorem; ℬ_ξ vanishes on ℓ₀ (J = ∅, V3 L269, L939); hull rule V3 L960, V4 L1150; (I)₁ "groups", "for every h"; c₁ := c (l.1609 convention); the ¼ recursion replaced by l.1609's (L(1+β₀)⁷ + 1/8) ≤ ½ at l.1122, l.1123; l.1136's (Z-c) exception and D(1)'s status (l.211); l.1403, l.1612 no longer "from V4"; R₀ → R₀^{V4}; the "V4 L357" quote is V3 L213 (V4 L368's wording given); RG2 p.13 quoted in full — the cut omitted "but not for (C^{(k)})^{1/2}", so l.1112 now says that expansion is RG2's own.
- Not changed: V4 line numbers at l.1100 stay pinned to hash b35c60e537b8 as that line states; PBG p.408 (l.1018) unchanged (reviewer: harmless).

**it1-gap-cav-20261029-r1 (C_av, R-av, cov-b's S3/m1–m6; prior cov-b-r1).** Verdict: C_av := 2B₃ with M ≥ 4B₃C₁/C₀ is a correct reading of RG1 (1.17) in the top-layer uniform form; S3's inverse-transport repair correct; m2–m5 closed.
- S1 (R-av per-layer and attributed to CRE p.267, which concerns the operators, not the spaces) — REPAIRED: note l.13 restates R-av in the top-layer uniform form (X ⊂ Ω_j, 2B₃α′ ≤ α_{0,j}L^{−2j}, (2.38)–(2.39)), with its identifications (U_{p,X} vs U_n, X̃^{−2}, the J-normalisation for (2.37)) stated; support VAR Theorem 1 (uniform ε₁) and Prop. 9 (ε₂ = B₅ε₁, B₅ = 6B₁B₃C₁); p.267 attribution removed in the note and map l.168.
- S2 (map l.928 uses R-av for the change of the averaged curvature) — NOT closed: l.928 now labels (2.35) for the averaged configurations at the deformation's evaluation points OPEN and names the route read: the change is exp(iηℋ(B)) in the block-variable change B (VAR Prop. 9, p.309), with δℋ/δB, ∇δℋ/δB bounded by VAR (190) (p.308); the block-variable change under the deformation and the conversion to (2.35)'s units remain to be computed.
  - Update 23:47 — repaired (derived, unreviewed). The sup|B| route loses L^{n−p} on X's layers n > p, where U_{p,X} carries only p-block data (CRE leaves p undefined; RG1 condition (iv), p.262, is the source). l.928 now derives (2.35) at the evaluation points through the deformation's curvature: Euler–Lagrange correction A_c = −G̃D*DH (VAR (141), p.300), G̃ = G − GQ*(QGQ*)^{−1}QG with VAR's G = PBG's G (VAR p.297); the bound on DG̃D* has no scale factor, by PBG (3.44), Theorem 3.3 (p.422), Theorem 3.4, Corollary 3.6, and (3.132)–(3.133); Hölder input from RG2 p.5 and PBG (3.43), with units from PRT2 pp.223, 248; data mismatch |δ| ≤ O(1)α_{0,n}L^{3(p−n)}h_n (axial gauge, REG (1.19)–(1.22)); constant C → C″, absorbed in the T_Y condition. Map bd2a5da2cf0d.
- S3 (c_nc and R′; cov-b m1) — REPAIRED: note §3 uses the L^{2m} cap (C₀/(C_avC₁))L^{2m}/(8K₂(1+β₀)²m^{1/2}), the bound 8(1+β₀)²m^{1/2}(1−β)^{−1}L^{−m}max(1, 4K₂C_avC₁/(C₀L)) for m ≥ m₀ and the trivial 2S_W for m < m₀; c_nc defined accordingly; §4's dependence list and map l.168 updated.
- Minors repaired: m-b (CRE p.268 l.38–39); m-c (transport condition for every j ≥ 1); m-d (map l.168's stale (K4)/slot-margin sentences); m-e (SW (6e) l.103, map l.1614, l.1419 constants and (6d)); m-f (reserve in σ_j dominates the consumers' σ_k weight); m-h (Prop. 9's B₅ stated); q₀ > p₀ cited at the disc points. m-a is covered by the restated R-av.

**it1-gap-slot-20261029-r1 (slot independence; prior cov-a-r1).** Verdict: correct in substance at step 1 (IT-1 §3d(4), Burnside for irreducible π, any compact G) and by induction later.
- F1 (2.1(i)'s "meets an ω′-bond" misses C's range and the touched-member channel) — REPAIRED: D2.6 closure 2.1(i) now tests against the one-cube neighbourhood of Λ_{k+1}ᶜ, which by 2.2 contains every ω′-channel's domain and lies in Coll_{k+1}; listed as rule change (5) (shrinks the dev class; no group leaves the collar form). This also settles F10.
- Minors repaired: F2 (§0 now an explicit induction citing 2.1(d), 2.2, *Merged groups*); F3 (π irreducible, V3 (H1), V4 lem:c5-5-7); F4 (slots enter step-1 insertions only through ω₀; real → polydisc); F5 (a^Λ_W·id and transport named); F7 (outer variable (A_e, a_old), V₀ ∈ 𝐔); F8 (closure 4.2(iii) class (2) and 4.5 no longer list step-1 dev insertions as ω₀-dependent); wording "changes no value of Y_W"; map l.168 updated.
- Not changed: F6 is now listed under rule changes; F9 (reading of CRE p.276) and the unaddressed older minors (r_J formula, S_W's l.308, K₂ omissions, Lemma 1's path hypotheses, p.256 qualifier, "joined in X_W", SW (6d)'s straddling cubes) are outside these repairs.
- Hashes after repair: map d55996e35431 (1614, LF); covariance note b6d50c08d7ae (184); SW 513dcc8d23f6 (112); D2.6 closure 232d5fe7e3a1 (177).

## The l.928 review and the second gap re-reviews (launched 23:54, landed 00:04–00:09; triaged and repaired 00:04–00:13)

Builder: verification\isolated_reviewer\build_l928_and_r2_rereview_packets_20261029.py.

### it1-l928-20261029-r1 (map l.928, *Route without the loss*)
- S1 (linearisation beyond first order; Δ′- and gauge-direction terms dropped; existence of the representation not stated) — repaired: (c0) exact integration along the path 𝐔_t with U_t := U_{p,X}(M^·(𝐔_t)) (existence, analyticity and regularity by VAR Theorem 1 and Proposition 9; continuity argument for (2.35) along the path); (c0′) the linearised minimiser ℋ_t = (I + G̃V″)^{−1}(H_0 + G̃(Δ^{(2)} − V″)H_0) (VAR (129), (182)–(189)) with the exact identity H_0(QH) = H − G̃Δ_aH, giving the four terms DH, DG̃D*DH, DG̃D(RD*H), DG̃Δ′H, each bounded with no factor L^{n−p}; the V″/Δ^{(2)} correction bounded through |H_0(QH)| ≤ O(1)h_n(L^nη)^{−1}.
- S2 (status rests on R-p) — repaired: labels "derived, given reading R-p; not reviewed".
- Minors repaired: η → η²; Corollary 3.6 replaced by Theorems 3.1–3.4 with p.399 and PBG (2.1)–(2.2); U_t's regularity from VAR Theorem 1 and Proposition 9; REG p.79 and the loop/holonomy argument in place of the "sheet" sentence; the common axial gauge Ax_k stated; the cross-layer decay is spatial (layer widths ≥ RM in p-units) for n, n′ ≥ p; the p.422 quotation completed; LFR1 (1.34)–(1.37) on p.184; (c2) cites RG2 (1.18) with R-adm and (3.133)'s Hölder entry; PBG p.397's definition of ‖·‖^ξ cited and the amplitude convention labelled an inference by homogeneity; notation β_H, B₀^{PBG}(β_H), C_{(2.35)}; δ₂RM > 2log L + 1 and β_H added to l.1614.
- Prior m-c and m-e (l.1614's (6d)) — m-e repaired (l.1614 now lists SW §6(6d)); m-c not re-examined.

### it1-gap-slot-20261029-r2 (no fatal, no serious)
- Repaired: N7 (neighbourhood defined as the π_{k+1}-cubes within one layer of Λ_{k+1}ᶜ; ranges of C (PBG p.428) and D̃ (RG1 p.267, block-by-block decoupling) inside it; the touched-member channel through B′ named; §0's "contains" corrected to "meets"); rule change (5) propagated to closure l.62 and l.79; map l.168 aligned (polymer components and members' domains, "built from Υ⁰_W, a^Λ_W·id and the interval transport", Burnside for the irreducible π); §0's status notes its dependence on rule change (5); 4.5's label covers step-1 dev insertions; N10's measure phrase made precise.
- Not repaired: F9 (outside the part); map l.630's "every compact simple G" (phrase not found in the current text).

### it1-gap-cav-20261029-r2
- N1 (serious: the trivial-bound branch assumes 𝐔 ∈ 𝒟_W) — repaired: the value at step-(k+1) data is the production function at the composite point, in 𝒟_W = Ũ^c_j by (4)(f)'s chain condition applied at each step i = k, …, j+1 (map l.974–975); no use of (K3) or R-av.
- Repaired: n-a (third entry of R′ now (r_J^{(j)} − r_J^{(k+1)})₊/(4r_J^{(k+1)}), small values falling in the trivial branch; growth from l.37); n-c (CRE (2.6)–(2.7) with (2.28)); n-e (K₁, K₂ and the r_J ratio added to Ĉ's dependencies); n-f (l.1614).
- Not repaired: n-b (k-independent bounds for K₂ and the r_J ratio), n-d (R-av's (2.38) at α_{0,n}; (2.37) for every p ≤ j), n-g (note l.3 wording).

### it1-gap-zh-20261029-r2
- S1 (serious: "e^{c_ξ}I_{ξ;1} … cancels in the ratio" contradicts V3 L4917) — repaired: clause deleted; 𝗐_ξ is non-local and not a factor of Y_W, c_W or φ₁, and its T–T′ comparison is (vac)₁ (l.1117), resting on V3 L213's identification.
- Repaired: m2 (m = 0 on ℓ₀, V3 eq:c5-5-1); m3 (V3 §c4-10 for the complex extension; product of per-bond balls, l.313); m7 (l.211).
- Not repaired: m1 (pairing wording), m4 (R₀^{V4} against V3's dependence halo), m5 (mixed V4 line-number conventions).
- Hashes after repair: map 84c92548a2a1 (1614, LF); covariance note 38130b3e05ce (184); D2.6 closure c4136c4bdf41 (177).

## Minor repairs after the l.928 and second gap re-reviews (30 Oct, 00:15–00:23; re-reviews launched 00:24)

- l928 prior m-c: l.1614 states c_πα_{1,k+1}·4096M ≤ ν at every step k ≥ 0, i.e. c_πα_{1,j}·4096M ≤ ν for every j ≥ 1.
- slot F9: closure l.55's A_k-dependence sentence labelled "Reading R-A_k (a reading of CRE pp.270–278, argued in the next sentences, not printed)".
- cav n-b: m₀ defined through k-independent lower bounds of R′'s entries (l.37, K₂ ≤ 2); c_nc uses 8C_avC₁/(C₀L); §4 l.145 and map l.168 dependency lists reduced to L, M, ν_r, β₀, β, C_avC₁/C₀.
- cav n-d: (2.37) identification stated for every p ≤ j; RG1's (i) mapped clause by clause; (1.12) at α′ derived at the base (VAR Theorem 1 (9)) and, at the path and disc points, replaced by (2.38) as part of R-av (stated).
- cav n-g: note l.3 wording aligned with l.13 (top layer, one constant, no per-layer form).
- zh m1: f runs over the matrix entries of π(T_WP_W^{−1}), equivalently its normalised characters, words of Lemma c4-4-2 closed with the inverse background interval; f_ξ also a word of that lemma, excluded by non-locality.
- zh m4: *Embeds* uses (Z-g)'s step-1 margin R_D^{(1)} with V3's dependence halo ρ_dep = R + ρ_w + h_box (V3 L715, L3968, L5024), ρ_dep ≤ 6L²MR₁.
- zh m5: l.1100 marks V4 L368 and L1150 as current-hash (563736a8dfb9) numbers.
- Hashes: map 84a5b85b1791 (1614, LF) before the l.168 dependency edits; covariance note 6632112e0534 (184); D2.6 closure eaa02ae2f270 (177).
- Builder: verification\isolated_reviewer\build_minor_repairs_rereview_packets_20261030.py; runs it1-l928-20261030-r2, it1-gap-slot-20261030-r3, it1-gap-cav-20261030-r3, it1-gap-zh-20261030-r3.

## The 30 Oct re-review wave (launched 00:24; all four landed by 00:39; paused by the user at 00:39)

### it1-gap-slot-20261030-r3 (no fatal, no serious) — triaged and repaired 00:35–00:38
- Repaired: S1 (the neighbourhood includes Λ_{k+1}ᶜ's own cubes); S2 (C's range n_C blocks, condition M ≥ n_C + 2, listed at map l.1614); S3 (D̃(B)(c) depends on B(c₋) ∪ B(c₊) and the corridor, RG1 (0.4), (2.4); decoupling per coarse bond; CRE p.267 transfer); S4 (B′ = g_kC(σ_k, A) − hD̃(·)); S5/S13(c) (confinement cited to the O6 closure §2 in 2.2 and §0); S6 (R-A_k's first clause cross-referenced to O6 §2; "for the class Y ⊄ Λ_{k+1} … stated for the A_k = 0 action"); S8 (Lemmas 5, 6 [I] = RG2 Lemmas 1–2 stated); S9 (l.55's two status phrases now give O6's status, l.161); S11 (Burnside for the irreducible π at l.79); S13(a) (§0 index j−1); S13(b) (localised potential terms added to §0's list); covariance note l.3 and l.16 carry "given rule change (5), for review".
- Not repaired: map l.630's "every compact simple G" (phrase not found in the current map, as at r2).

### it1-gap-zh-20261030-r3 — triaged; repairs 00:38–00:39
- S1′ (serious: the map attributed to V3 L213 an identification of 𝗐_ξ with RG1's e^{𝐄^{(1)}}; V3 does not make it, cf. V3 L2328) — repaired by status: new item R-w1 (OPEN) at l.1117, the T–T′ comparison of V3's step-1 branch weight on ℓ₀; l.1132, l.1135 and l.1136 aligned ((vac)_j derived for Bałaban's 𝐄^{(j)}; R-w1 listed among (Z)'s open inputs; (I)₁, (O)₁ unaffected). What closes it: the identification of 𝗐_ξ with RG1's first-step weight on ℓ₀ (Θ_ξ, near primitives, Jacobian, Gaussian normalisation), or a direct T–T′ comparison of log 𝗐_ξ from V3's representation.
- Repaired: m1 (the step-1 margin is ρ_dep at l.1131 and l.1133; V4's R₀^{V4} no longer the step-1 margin); m2 (h_box ≤ C_box·LM; ρ_dep < M(1/2 + C_boxL) < LMR₁/4 for g₀ small, R, ρ_w < M/4 by V3 L727); m3 (ρ_w named as D_b's radius, L725; R_* is the walk range; L5024's fixed radius labelled as read from the list of consulted objects); m4 (m = 0 via Λ₁^{fin} = T, J(Λ) = ∅, ℓ_Λ = 0); m5 (𝔫_ξ at V3 L832); m6 (attached vacuum clusters vs the unmarked gas Ξ^f_ξ in 𝗐_ξ, under R-w1).

- Hashes at the pause (00:39): map b244f7a082dd (1614, LF); covariance note 9b4b211fa56c (184); D2.6 closure 2850e3bd296f (177).

### it1-gap-cav-20261030-r3 (no fatal, no serious) — triaged and repaired 07:57–08:00
- Repaired: N1-a (trivial branch: steps i = k, …, j); N1-b (𝒟_W is D(j)(iii)'s domain, Ũ^c_j for j ≥ 2, V3's at j = 1); N1-c (R-m and R-p dependence of the trivial branch recorded in note l.3, l.182, §3 and map l.168; cited to (4)(f), map l.690–709, with l.928); N1-d (composite point = (𝐔, 𝐉) for untouched insertions, (4)(e) at s = 0); n-a′ (Cauchy disc |z| ≤ 2R′, 2S_W/(2R′−1) ≤ (4/R′)S_W; third entry's 4/R′ term 16/(ρ−1) ≤ 8(1+β₀)²m^{1/2}(1−β)^{−1}L^{−m}; the (2.39) per-step check); n-d ((1.12) is posed on the real factor U_{k+1}, the same at every path and disc point, so it holds there as at the base; the substitution of (2.38) removed; base citation SW §6(6d), cf. CRE p.267 (3.12); the 𝐉-bound of (1.14) not used by (1.17)); m₀ ≥ 1; Ĉ's dependence on (2.38)'s C through δ̄; map l.168 "m < m₀".

### it1-l928-20261030-r2 — triaged and repaired 08:00–08:03
- Serious 1 (the Lagrange-multiplier term G̃Δ^{(2)}H₀ mis-described as curvature-linear; with PBG (3.137) it carries L^{n−p}) — repaired: the path now scales the field argument, 𝐔_t = e^{iη𝐇(s,(t·t_Y)B′)}e^{iηa′}U_{k+1}, so every path point is an evaluation point ((4)(f)); 𝐇(s,0) = 0 and ∂_t𝐇 by Cauchy from RG2 (1.18) (analytic for |B′| < ε₃); R-m (CRE p.277, printed range (2.36)–(2.39)) gives CRE (2.37) for U_t's current 𝐉_{p,X} along the path (RG1 (1.15)); Δ^{(2)} described by PBG (3.134)–(3.137) (linear in H*J); |Δ^{(2)}A| ≤ O(1)C_3L^pη·sup|J_t|·|A| with (2.37) gives η²|DG̃Δ^{(2)}H₀| ≤ (2.35)'s scale × O(1)B₀C_3h_nL^{p−n}; Neumann series |G̃Δ^{(2)}| ≤ O(1)B₀C_3α_{0,n}L^{2(p−n)} ≤ 1/2. Status: "derived, given reading R-p and R-m's (2.37) along the path; not reviewed" (l.928 opening, *Route without the loss*, l.1614, SW closure (b3) l.49).
- Minors repaired: VAR (182)/(188) formula as printed, with the two G's (VAR p.306 l.37–38 vs p.297); V″(0) = 0, 𝔇(0) = 0; data L^{j(·)}ηQH; Landau vs axial gauge (ω_t) and η|𝒜||∂U − 1| terms absorbed; (c3) frame sentence (axialise 𝐔_t with u = 1 at block points); layer width R₁M₁ from REG (1.4), condition δ₂R₁M₁ > 3log L + 1 (true for g₀ small); h_n defined; REG (1.3)–(1.6) ⇒ [4]'s (2.1)–(2.2) labelled part of R-p; q₀ = q₁ for the complex domain; openness of the continuity set; (1 + L^pη|H_t|) dropped; Stokes conjugation factors stated; C_{(2.35)} includes B₀C_3.
- Hashes after repair (08:03): map 89edd3f4236a (1614, LF); covariance note 69b3a3406468 (184); D2.6 closure 2850e3bd296f (177); SW closure 8708fc178478 (112).

## Wave 2 (launched 08:04; builder verification\isolated_reviewer\build_wave2_rereview_packets_20261030.py)
- it1-l928-20261030-r3, it1-gap-slot-20261030-r4, it1-gap-cav-20261030-r4, it1-gap-zh-20261030-r4. Stop rule (user): until 10:57 or until two consecutive waves come back clean (no fatal, no serious).
- Outcome: all four landed by 08:20. Not clean: zh r4 has two serious findings and l928 r3 has one. slot r4 and cav r4 are clean (minors only). Wave 2 does not count towards the two clean waves.
- Process note: map l.1614 (cav N1-c clause) was edited at 08:16 while l928 r3, whose scope includes l.1614, was still running. The review hashed the map at its start (89edd3f4236a) and quotes l.1614 in the pre-edit form. The edit is a within-line addition, so line numbers did not move. Map edits were then held until l928 r3 landed.

### it1-gap-slot-20261030-r4 (no fatal, no serious) — triaged and repaired by 08:21
- S9: D2.6 closure l.55, the "(status: …)" parenthesis and the closing bold sentence now say "derived … for 𝐏^{(k)}'s terms and V^{(k)}; for the bracket terms OPEN until the consumers' replay (l.161)".
- S5(a): "O6 §2, 'What that forces'" corrected to "O6 l.17" in D2.6 l.54 and l.55, in covariance §0 ("l.17 … and §2") and in O6 l.113.
- S5(b): the l.54 parenthesis moved after the set (Ω_{k+1}∩Λ_{k+1}ᶜ)^{(k)*} ⊆ Λ_{k+1}ᶜ; RG2 p.9 quoted as printed ("𝐔, 𝐉, B restricted to the interior of Y", B = (A_k, A)).
- S2: n_C defined as the reach; "depends on d and L only" marked as inferred from PBG p.428's construction.
- S3: corridor disjointness stated; C̃ defined implicitly on p.267, with the same locality.
- Carried items: map l.630 now reads "every compact G (Burnside, for the irreducible π)"; CRE p.276 range l.37–46. §0's "the sup of l.308" (r2 carry) was not re-examined.

### it1-gap-cav-20261030-r4 (no fatal, no serious) — triaged and repaired by 08:21
- 1.5(d): the (2.34) check at the non-covariant disc now counts the plaquette factor 2: the 2B₃-weighted total is ≤ (3/4)α_{0,j}L^{−2j}, within R-av and the top-layer conditions (covariance l.127).
- 1.6: (1.12) uses RG1's coefficient α′₀ = α′L^{2j} = α_{0,j}/(2B₃); VAR (9) is converted to RG1's step-j normalisation (gain L^{−m}); ε_{k+1}/α_{0,j} → 0 by CRE (2.4), (2.8), (2.28) under q₀ > p₀ (covariance l.13).
- 1.3: (2.37) attributed to R-m and (2.35) to l.928's derivation given R-p (covariance l.3, l.127, l.182). The conditional clauses of map l.168, l.1419, l.1614 and SW l.99 now name (4)(f)'s chain condition with R-m and R-p.
- Trivial: C₁^{VAR} named at covariance l.12; *Carrying 𝐉* cited at map l.710–714.

### it1-gap-zh-20261030-r4 — triaged and repaired 08:12–08:17
- S-a (serious; D2.3(5) l.1144 used V4's step-1 gas): repaired. The step-1 tail is now derived for V3's φ₁ at carrier I (V3 L2798) from l.1134's KP weight and V3 Lemma c5-5-8(a) (L2791–2796), at the rate c_d = ν/(64ML) with amplitude ε̄_t = 2K_χC_pinρ_t. New OPEN item T′-1: (T′) at k+1 = 1 with the amplitude 𝔞₁ = max(τ₀², ρ₁·pl). The obstruction is that ε̄_t ≍ g₀(1+2r) exceeds ρ₁ and τ₀². Two things would close it: a τ²-tail for φ₁ (V3's eq:marginal-cluster-tail L1430 and eq:corner-bent-tail L1538 give Cτ² for the Φ_C of V3's perimeter sections; their identification with φ₁ is not checked), or a check that the consumers of (T′) at step 1 take ε̄_t. Listed in l.171 and l.1136.
- S-b (serious; l.171 status summary not updated): repaired. l.171 now names R-w1 and the closure note, and separates the attached vacuum clusters (in the step-1 base) from the unmarked gas Ξ^f_ξ (in 𝗐_ξ).
- m-a: l.1117 now reads "Bałaban's step-1 vacuum is RG1's 𝐄^{(1)}, described at V3 L213".
- m-b: R-w1 is closed at real data in the localised (vac)_1 form, in WILSON_IT1_RW1_CLOSURE_2026_10_30.md:
  - on ℓ₀, R₁ = S₁ = ∅ (CRE (1.20)), Ψ_ξ = id and c_ξ = v(0);
  - −½log det H is a sum of closed-walk terms (V3 L715–717);
  - log Ξ^f_ξ = Σ_𝔠Φ^v_ξ;
  - embedding terms are equal on T and T′, and the non-embedding tails are ≤ C_we^{−cι} per position, with rates ≥ 1/(32M) from V3 L719, L727 and θ ≥ (log 128)/8.
  - The complex-data tail R-w1(c) is OPEN.
  - The propagation to (vac)_j, j ≥ 2, is stated.
  - Map l.1117, l.1132, l.1135 and l.1136 are updated.
- m-c: *Embeds* (l.1113) uses R_D^{(j−1)} for X ∈ 𝐃_j.
- m-d: D2.0(3)(g) l.388 now defines ι_{T,k} := max(0, N_min^{(k)}/4 − ρ_dep L^{−k}), so ι_{T,k} = Lι_{T,k+1} exactly; any other fixed subtraction R = O(LM) costs a constant e^{c(R+ρ_dep)}. l.1131 cites it.
- m-e: l.1133 now reads "R_D^{(0)} = ρ_dep fine bonds, i.e. R_D = ρ_dep/L step-1 bonds".
- m-f: m = −H^{−1}ℓ_Λ is cited at V3 L2484.

### it1-l928-20261030-r3 — triaged and repaired by 08:21
- S1 (serious; the current premise was mis-recorded as a T_Y/q₀ ≥ p₀ entailment): repaired by recording it as its own reading, R-mJ (the (2.37) part of R-m). Its content is |J_t| ≤ O(1)α_{0,n}L^{n−p}(L^nη)^{−3} per layer at every path point, a loss-free averaged-current bound that is wider than p.277's print (T_Y-polydisc deformations of size α_{0,k}/C′; non-𝐃_k domains). It is not entailed by the size condition. A per-layer RG1 (1.17) would give it, but that is not printed. The false entailment sentence is removed. l.928, l.929 ((2.37) is not treated in *Carrying 𝐉*), l.1614 and SW (b3) l.49 now say "given the readings R-p and R-mJ". R-mJ is a reading the user has not yet accepted, so it goes to the user as a pending approval.
- Minors repaired:
  - h_n stated per layer, with the Ω_k bound (1 + o(1))min(β,1)α_{0,k}/C′ and the older layers through l.929's h_k^{(0)};
  - C₁^{VAR} vs CRE's C₁;
  - "T contains 0" from D(k+1)(iii)'s domain (l.919), with the doubled margin written out;
  - PBG's "(149) in [5]" = CMP 98 p.40, not VAR (149);
  - RG1 (1.15) quoted with "L^{−n} instead of ξ";
  - the layer sum's α-ratio and its O(L³) size.
- Hashes after repair (08:21): map 19486e8cd29c (1614, LF); SW closure 8628642dabf3 (112); covariance note ef1684e65f8d (184); D2.6 closure 2ef5e40af9b4 (177); O6 closure cb09fb849e68 (115); R-w1 closure note 720510f477cd (71, new).

## Wave 3 (launched 08:22; builder verification\isolated_reviewer\build_wave3_rereview_packets_20261030.py)
- it1-l928-20261030-r4, it1-gap-zh-20261030-r5, it1-rw1-20261030-r1 (first review of the R-w1 closure note), it1-gap-slot-20261030-r5, it1-gap-cav-20261030-r5.

### it1-gap-slot-20261030-r5 (landed by 08:29): CLEAN (no fatal, no serious)
- Every r4 finding closed (S9, S5(a), S5(b), S2, S3(a), map l.630, CRE p.276); S3(b) correct in substance.
- m2 (O6 l.17, B′ in place of the printed B): repaired; l.17 now reads "every localised term depends on the fluctuation field B = (A_k, A) restricted to the interior of Y (RG2 …)", the B′ clause dropped (it serves §2's passage only, which l.17's later sentence keeps).
- m1 (D2.6 l.55, (1′) heading): repaired with the bracket-term OPEN clause and l.161.
- m4 (D2.6 l.95, O6 status without the bracket qualifier): repaired the same way.
- m3 (D2.6 l.45, C̃ wording): repaired to "the nonlinear part of LQ̃(B′), Q̃(B′) the exponent in (2.4)", with p.267 l.26.
- Carried (covariance §0 l.24, "the sup of l.308"): held, since the covariance note is in the running cav r5 packet; to be checked after it lands.
- Hashes after repair: D2.6 closure 546b7d26c8bb (177); O6 closure fb984850c393 (115).

### it1-l928-20261030-r4 (landed by 08:31): NOT CLEAN (2 serious)
- S1 (accepted): l.928's last sentence and l.929 give (2.37) membership at the step-k margin to R-mJ, which states only an O(1) factor; every path point is an evaluation point, so the margin form implies the O(1) form and the weakening removed nothing. Repair: R-mJ restated as the margin form at every evaluation point of (4)(f) (CRE (2.37) with the step-k constant on each layer n of X; in particular |J_t| ≤ α_{0,n}L^{n−min{p,n}}(L^nη)^{−3} at every path point, all that (c0′) uses), labelled an OPEN premise (not a reading), listed in the gaps block.
- S2 (accepted): gaps block l.214 still presents (2.34)–(2.35) as following from q₀ > p₀ and (2.37) as covered by R-m's p.277 statement; chain-condition status lines (map l.168 twice, l.1419, l.1614 tail; SW l.99) omit R-mJ. Repair: l.214 rewritten ((2.34) and (2.36) from the size inequality; (2.35) l.928's derivation given R-p and R-mJ; (2.37) is R-mJ, OPEN); R-mJ added to every chain-condition status line.
- Minors (accepted): L^{n−min{p,n}}; R-mJ is an absolute bound (a loss-free change bound or a per-layer RG1 (1.17) would give it, neither printed); h_n defined by the formula on Ω_k and by the R-dec majorant on older layers; the |t| ≤ 2 sentence credits sup|B′| to q₀ > p₀; second lines of CRE (2.6)–(2.7); C′ depends on L, absorbed by κ_s (chosen after L, l.1614) in D2.4's per-component count.
- Held until zh r5, rw1 r1 and cav r5 land (the map and SW closure are in their packets).
- Applied after all of wave 3 landed: map l.928 (R-mJ margin form, OPEN premise; absolute-bound wording; h_n; |t| ≤ 2 sentence; second lines of (2.6)–(2.7); C′ and l.704), l.929, gaps block l.214; SW l.49 and l.99. NOT YET DONE: R-mJ in map l.168 (twice, and its body "for (2.35)/(2.37), R-p"), l.1419 and the l.1614 tail.

### it1-gap-cav-20261030-r5: NOT CLEAN (1 serious), repaired
- S1 (ε₁ ≪ α′₀ not uniform in m): covariance l.13 now uses the L^{−m} gain, uniform in m, with the L^{1−m} and L^{−2m} cases and (2.38) at n = j. Minors: R-mJ named at l.3, l.127, l.182; 2B₃ ≥ 3/4 and (2.37) at l.127; VAR p.296 l.11 for B₁; l.24's "sup of l.308" replaced by (T-dev)'s β_W sums (map l.1353–1358). Map l.168's body and its "(ε/α₀ → 0)" are not yet done.

### it1-rw1-20261030-r1: NOT CLEAN (2 serious), repaired in the note
- S1 (consumer of the non-embedding terms): the note now names the *Step* at k = 1 and (Z-d)'s non-embedding bound, with the amplitude supplied by (TC). S2 (scope of R-w1(c)): §5 now covers the analytic extension, KP, the branch and the tails, and names the consumers l.1115 and l.1116; §4(a) is conditional. All minors repaired, κ_ξ included. The map l.1117 and l.171 text is NOT YET updated to match.

### it1-gap-zh-20261030-r5: NOT CLEAN (3 serious), NOT YET REPAIRED
- S1: T′-1 closes (checked): V3 (c4-6-5) with L4608 (M(W) ≥ |a_W| at the reference data), L2798 and l.299 give the step-1 group sum ≤ C(1+β₀)⁶ρ₁ ≤ C′𝔞₁. The rate needs V3's envelope constant A_E: set c_d := ν/(32A_dML), A_d := max(2, A_E+1), uniformly in k (l.172, l.1143, l.1144, l.1168), with c_E = c_d/2. Then remove T′-1 OPEN at l.171, l.1135, l.1136 and l.1144. S2: R-w1's status now reads "reviewed, repairs not re-reviewed". S3: closes with S1. Minors m-1 (L2798), m-2 (delete l.1168 residue), m-5 (*Embeds* units: radius R_D^{(j−1)}/L in step-j units), m-6 (V3's standing torus conditions for C′ on ℤ⁴).
- Map hash after the partial edits: see SESSION_HANDOVER.md.

### Repairs completed after the usage-limit break (12:41–12:43)
- Map l.168 (both clauses; body attribution; uniform L^{−m} form), l.1419, l.1614 (tail and middle) now carry R-mJ as an OPEN premise.
- Map l.1117, l.1132, l.1136 and l.171 synced with the repaired R-w1 note (consumer, analytic clause, R-w1(c) scope, κ_ξ, "repairs not re-reviewed"); l.171's bold headline now names R-w1(c) and R-mJ.
- zh r5: T′-1 closed in l.1144 (V3 (c4-6-5), L4608, L2798, l.299; ε̄_t not needed on ℓ₀); c_d := ν/(32A_dML), A_d := max(2, A_E+1), in l.1143, l.1144 and l.172; c_E = ν/(64A_dML) at l.1168 (residue removed); T′-1 removed from l.171 and l.1136; *Embeds* units (l.1113); V3's standing torus conditions for C′ at k+1 = 1.
- Hashes: map 2e8612264bbb (1614, LF); R-w1 note 4d7da1bc1dfd (75); covariance bc1d561f81c0 (184); SW c842fda56565 (112); D2.6 546b7d26c8bb (177); O6 fb984850c393 (115).

## Wave 4 (launched 12:43; builder verification\isolated_reviewer\build_wave4_rereview_packets_20261030.py)
- it1-l928-20261030-r5, it1-gap-zh-20261030-r6, it1-rw1-20261030-r2, it1-gap-slot-20261030-r6, it1-gap-cav-20261030-r6.
- Wave 3 outcome: NOT CLEAN (slot r5 clean; l928 r4, cav r5, rw1 r1 and zh r5 serious). The 3h window (deadline 10:57) passed during the usage-limit break; wave 4 was launched on the user's "continue" after the reset.

### Wave 4 outcome (all five landed 12:50–13:00; read in full or in their summaries and named sections): NOT CLEAN
- slot r6: CLEAN (no fatal, no serious; minor n1, the covariance l.24 pointer). Second consecutive clean pass (r5, r6): slot is closed.
- cav r6: CLEAN (trivials T1–T3 only). First clean pass after r5's serious finding.
- zh r6: serious S-A ((Z-f)'s step-1 rate c^Z = ν/(512M) rested on the general-k diameter count that l.1144 no longer uses at step 1); minors m-A to m-E. T′-1 closure, c_d and c_E confirmed.
- l928 r5: serious (1) the recorded closure route for R-mJ ("a per-layer form of RG1 (1.17) would give/close it", l.928, l.214) is false for the margin form, since (1.17) carries the factor 2B₃; (2) (4)(f)'s own labels (l.690, l.930) omitted R-mJ. Minors m1–m4, SW (b3) heading. Both r4 serious findings confirmed repaired.
- rw1 r2: serious (1) R-w1(c) (k^f not extended, OPEN) was inconsistent with (Z-h)'s complex clause and IT-1 §3e(3.7); (2) the (TC) amplitude step was not uniform in K. Minors 3–8.

### Repairs after wave 4 (12:51–13:08)
- slot n1: covariance l.24 pointer reworded (S_W ≤ S_𝒢 → b_W → β_W at map l.1329–1330, l.1347; (ii-t) l.1347–1348; *It carries* l.1358; §4's (ii-w) sum l.1529–1530, l.1534).
- zh S-A: c^Z := ν/(256A_dM) at every k (l.1127 with the step-1 envelope justification; l.1128, l.1118 now e^{−c^Zι}; l.1135; l.1612). m-A: rooting via J_Γ (l.267), L2789; m-B: C_S′ ≥ C(1+β₀)⁶; m-C: (81A_F + M)σ₁ positions at step 1 (V3 L4611(d)); m-D: K_μ ≥ 3(n+2) at V3 L124, L1375, L2602; m-E: superseded by the R-w1(c) status change below.
- l928 serious (1): l.928 and l.214 now state that a per-layer (1.17) gives only the path form with constant 2B₃, and the margin form needs the (2.34)-curvature below (1 − β)α_{0,n}·(scale)/(2B₃) per layer. Serious (2): l.690 and l.930 labels carry R-p and R-mJ. m1 (η-units, any O(1) constant), m2 (quantifiers over X, Z included, and p), m3 (l.704's third 1/T_Y entry), m4 ((2.35)'s status lists q₀ = q₁, q₀ > p₀, R-dec, R-cpl₀, R-adm); SW (b3) heading.
- rw1 serious (1): R-w1(c) derived (not reviewed) in the R-w1 note §5 (a)–(h): stencil frame with ‖Z − Z_re‖ ≤ 2α_{1,1}/L ≤ τ_w; complex symmetric Hessian, γ/2 ≤ Re H; Gaussian payment e^{(1+δ)N₁}; activity bounds at complex background with IT-1 §3e(3.7)'s list of positivity uses; KP at weight 1 + 5θ; branch; determinant series with ‖𝖠_H‖ ≤ q_H^{1/2}; tails; Cauchy second derivatives; outer prefactor via V3 Lemma two-block (L349, det α_c > 0 at real data). Map l.1117, l.1132, l.1135, l.1136, l.171 synced (R-w1(c) removed from l.171's OPEN list). Serious (2): ι_{T,1} = L^{K−1}ι_{T,K}, g_min small (note §4 and map l.1117). Minors: bookkeeping as an added summand of (Z-d) with C_Z^{(1)} := 3C_S′ (note §4, map l.1117, l.1135); §4(a) analytic clause; S(U₁) of the fine background; pointers L475–480, L512, L713; ν ≤ 1/1000 (map l.1614); "∪𝒜 = T" removed.
- Gap closure (user, "Close the open gaps!"): the O6 bracket-term replay is closed by O6 §5a (new, derived, not reviewed): a two-constants estimate (Joukowski map plus Hadamard's three-circles theorem) between p.277's real-support bound on the real box K and the crude bound on R-m's domain at localisation radius 3/2 gives p.277's coefficient O(ε_k) times 2 at every consumers' point, with the decay rate reduced by δ_k = 8τ_k^{1/3}c_* → 0, under (C3) and the new (C7) (smallness on g_K for every q₁ ≥ p₀); (C6) and c_loc are no longer used by consumers. O6 l.3, §9, constant-conditions note, "Derived here" synced; D2.6 l.12, 25, 55, 62, 79, 95, 156, 161 synced; map l.171, l.199, l.226, l.336, l.956, l.1136 synced; SW l.107 synced.
- Still OPEN: R-mJ (margin form of CRE (2.37) for 𝐉_{p,X}(M^·(𝐔)) at every evaluation point of (4)(f); map l.214, l.928).
- Hashes after repairs: map effd53d4e5d2 (1614, LF); R-w1 note 816c333109b5 (94); O6 7e90917e0adb (141); D2.6 b0c828b7c14d (177); covariance 44f6e06a03d0 (184); SW 0d65cf66a0c2 (112).
- Wave 5 (to launch after the next usage-window reset, ≤ 6 runs): l928 r6, zh r7, rw1 r3, o6-5a r1 (new: O6 §5a with D2.6 l.161 and map l.199, l.956), cav r7 (for the second clean pass). slot is closed (clean twice).

## Wave 5 (launched 13:16 on the user's "Continue for the 3 hours or until everythings and at least two reviews have come back clean"; deadline 16:16; builder verification\isolated_reviewer\build_wave5_rereview_packets_20261030.py)
- it1-l928-20261030-r6, it1-gap-zh-20261030-r7, it1-rw1-20261030-r3, it1-o6-5a-20261030-r1, it1-gap-cav-20261030-r7.

## Wave 5 outcome (all landed 13:21–13:3x)
- l928 r6: CLEAN (no fatal, no serious; first clean pass). Minors m-a (sufficient vs necessary threshold of the RG1 (1.17) sentence), m-b, m-c, m-d (input lists). Resolved by the R-mJ sync below: the (1.17) sentence is replaced, the repeated sentence removed, the lists carry q₀ = q₁ > p₀, R-dec, R-cpl₀, R-adm.
- zh r7: CLEAN (first clean pass). Minors n-1 to n-6. Repaired: n-1 (k+1 = 1 excepted at l.1124, l.1614), n-2 (C_Z^{(1)} := 4C_S′; C̄_Z ≤ 4C_S′ + 4C⁎ at l.1128, l.1168; 1/(64M) ≥ c^Z at l.1117), n-3 (l.1185; l.102 and l.168 of the coarse-chain closure not edited). Not repaired: n-4 to n-6 (constant bookkeeping, no rate or status affected).
- cav r7: CLEAN (second clean pass after r6): cav CLOSED. Minors m1 (input lists, done in the R-mJ sync), m2 (covariance l.3 "closes" → "derives", done).
- o6-5a r1: NOT CLEAN. S1 (real bound on the whole ball K is not R-fr) → reading R-fr⁺ stated and carried (O6 §5a(i), l.3, attribution section; D2.6 l.12, l.161; map l.199, l.956), with the anisotropic K′ keeping Λ_{k+1} at g_k|A| ≤ δ_k (Steps 1–2 adjusted). S12 (§6 and §9 use §5's whole-domain bound) → §6's bracket part at Cauchy radius g_k^{3/2} inside §5a's set at 2τ_k, new (C4′); §9's (3.28) derivatives keep §5's bound, needing (C6) only under q₁ = p₀; consumer sentence corrected. Minors: A(·) crude bound (M_X ≤ c^{|X|}g_k^{−2}); R-m reading for 𝐄/𝐑 carried; c_ρ mechanism (one t_□-Cauchy, σ-circles); decay loss absorbed in the bracket terms' own rates; δ_k renamed ϑ_k; C_B absorbs B₀/E₀; RG2 (1.28) via p.276; (C7) at 2τ_k; l.702 → l.959; history sentence removed from O6 l.3. Not repaired: §5's own per-cube ρ_k^{−1} wording.
- rw1 r3: NOT CLEAN. S1 ((TC) not K-uniform; "g_min ≤ g₁" false) → CRE (2.7): log g₁^{−2} ≤ (1+β₀)(K−1)^{β₀}log g_min^{−2}, L^{K−1} ≥ (K−1)^{β₀} kept (§4, §5(g), map l.1117). S2 (walk series and payment at complex background beyond V3's scope) → new §5(b′): q′ = q_H + c_Hτ_w/s_H, τ_w after M with (q′/q_H)^{n_*N_M} ≤ 2, δ_M → 3δ_M with M bounded below; ‖Γ₂‖ ≤ 3h_+δ_M + C_Γc_Hτ_w; reserve identity at complex C_{E₀} with T′, ‖T′‖ ≤ 1/3. Minors 3–9 repaired (V3 L441; ‖Z‖; Morera; branch; C_Z^{(1)} := 4C_S′; §5(g); §5(h); map l.1132; pointers).

## R-mJ closed (13:2x–13:3x; derived, not reviewed)
- New note WILSON_IT1_RMJ_CLOSURE_2026_10_30.md (0528c64469cf, 143 lines): joint continuity argument for (2.35) and (2.37); the linearised minimiser is PBG's H₁ = G₁Q*(QG₁Q*)^{−1}; RD*G₁Q* = 0 (PBG (3.124) for G₁, p.426) gives D*D𝒜 = Q*(λ₁ − b) + Δ^{(2)}𝒜 − Δ′𝒜; kernels (3.42), (3.132), (3.133) for G₁ (Theorem 3.12); main term (2.37)'s scale × O(1)B₀h_n/α_{0,n}; T_Y condition with C′ enlarged (d, L only); older layers by 4θ ≤ 1/2.
- Synced: map l.168, l.171, l.214, l.690, l.928, l.929, l.930, l.1419, l.1614; SW l.49, l.99; covariance l.3, l.127, l.182.
- Hashes after the repairs: map adfbda346431 (1614, LF); R-mJ 0528c64469cf (143); R-w1 8b5ac8f55366 (101); O6 3ee675d3192f (143); D2.6 ccc15934ccda (177); covariance 5bb197a6f8ff (184); SW 688d162607b1 (112).

## Wave 6 (launched 13:4x; builder verification\isolated_reviewer\build_wave6_rereview_packets_20261030.py)
- it1-rmj-20261030-r1 (new), it1-l928-20261030-r7 (second pass, R-mJ sync), it1-gap-zh-20261030-r8 (second pass), it1-rw1-20261030-r4, it1-o6-5a-20261030-r2.
- zh r8 (13:49): CLEAN (second clean pass): zh CLOSED. Minors: m-1 (C_Z^{(k+1)} definition at l.1127, l.1612 without the k+1 = 1 exception), m-2 (local c := c^Z at l.1165, l.1168), m-3 (coarse-chain closure l.102, l.168: repaired 13:5x), m-4 (l.1117's CRE (2.7) at K = 1: use max(1, (K−1)^{β₀}); r ≥ 2; l.1122's CRE (2.9) at k = K), m-5 (l.325, l.1099 vs 3C_Z^{(k+1)}). m-1, m-2, m-4 and m-5 wait until the reviews reading the map have landed.
- l928 r7 (13:50): CLEAN (second clean pass): l928 CLOSED (its result conditional on the R-mJ note, reviewed in rmj r1). Minors: m1 (l.928 R-mJ entry "implies the path form that (c0′) uses" → (c0′) uses T's bound), m2 (T's doubled bounds with ≤), m3 (l.171 "listed at l.1136" → through SW §3, §6), m4 (l.704's third entry: C′ ≥ C_{(2.37)} with both enlargements), m5 (l.214's q₁ = p₀ sentence → R-m's entailment); cosmetic: "every p in R-p's range", PBG (3.124) p.420 / pp.425–426, G₁'s printed form ((3.128) gives G₁^{−1} = Δ_a − Δ^{(2)} with ⟨A, Δ^{(2)}A⟩ = 2⟨HC^{(2)}(A), J⟩, consistent with the note). All wait for the map to be free.
- o6-5a r2 (13:53): NOT CLOSED. F1: §9's (3.28) Cauchy disc reaches C₁^{RG2}ε_k^♯ + r_{α,k}/2, outside §4's domain, and §5's per-cube ρ_k^{−1} mechanism contradicts RG2 (1.23). F2: the A(·) crude bound M_X ≤ c^{|X|}g_k^{−2} is wrong (the coefficient Σ_{j≤k}β_j(1 − φ_j), CRE (2.24), grows like βk). F3: D2.6 l.161 still says no consumer uses (C6) and lacks (C4′). Minors m1–m5 (R-fr⁺ wording; p.276 l.18–24; the larger set; O6 l.54; (C3) cites l.959).
- rw1 r4 (13:55): CLEAN (first clean pass). Minors 1–9: §5(b′) order M then τ_w, 3δ_M arithmetic, C_w′ at complex Z, ‖T_{α_G}‖_{V3} double count, §5(d) citation beyond the IT-1 scan, §5 setting, Cauchy reason, c_H in complex directions, C_L undefined, map sync (l.1127, l.1117 (b′), l.1132 scope). Repaired in the note 14:0x (map sync pending).
- rmj r1 (13:58): Serious 1: §4(c)–(d) identified (Δ_a − Δ^{(2)})^{−1} with PBG's π-extended G₁ and used PBG p.426's QG₁DR = 0 for it. Repaired 14:0x from VAR: G₁ is VAR p.294's operator (Δ in place of Δ_π, p.297); RD*G₁Q* = 0 derived from VAR's Landau-gauge problem ((76) p.289, (127)–(128) p.297, (172)–(177) pp.305–306). Minors 2–7 repaired (kernels via VAR p.297 and the Neumann series, (3.132) as PBG's text bound p.422, VAR p.309 ll.2–4 at complex data, layer 0 via VAR Theorem 1 (9)–(10), β₀ and Ad constants, T non-strict, J against (3.36) p.396). Minor 5 (units) and 8 (map l.214, l.928 attribution) go with the map sync.
- Map sync 14:0x–14:1x (map 6612519923de → after the O6 sync below; 1614 lines, LF): zh r8 m-1 (l.1127, l.1612: C_Z^{(1)} := 4C_S′), m-2 (l.1165, l.1168: c^Z), m-4 (l.1117 max(1, (K−1)^{β₀}), r ≥ 2; l.1122 CRE (2.9) at k = K), m-5 (l.325, l.1099: 3C_Z, l.1128); l928 r7 m1 (l.928: (c0′) uses T's bound), m3 (l.171), m4 (l.703: C′ ≥ max(C_{(2.35)}, C_{(2.37)})), m5 (l.214's duplicate q₁ = p₀ sentence removed; l.213 carries it); rmj r1 m5 (l.928 h_n in η-units), m8 (l.214, l.928: VAR's G₁ and Landau-gauge derivation); rw1 r4 m9 (l.1117 (b′), l.1127, l.1132 scope, statuses "one clean review"). An Edit deleting l.214's last sentence merged l.214 with l.215; the line break was restored at once.
- o6-5a r2 repaired 14:0x–14:1x: F1 (§5's localisation now one t_□-derivative with RG2's σ(Δ)-circle decay on 𝒫_k^{3/4}; no per-cube ρ_k^{−1}; (C6) removed; §9's (3.28) disc at radius r_{α,k}/4 inside 𝒫_k^{3/4} under (C3)); F2 (A(·) crude bound via CRE (2.24) and p.277's "suppressed by the exponential decay of 𝐇_k", recorded as the reading R-A, since the layer separations needed are not printed in (2.1); log M̄ = O(1)); F3 (D2.6 l.161: (C1)–(C5), (C4′), (C7); (3.28) under (C3)); m1 (R-fr⁺ wording, §5a heading), m2 (p.276 l.18–24), m3 (larger set's conditions), m4 (O6 l.54), m5 ((C3) cites l.959). Synced: O6 l.3, l.41, §9; D2.6 l.12, l.161; map l.956, l.959.

## Wave 7 (launched 14:1x; builder verification\isolated_reviewer\build_wave7_rereview_packets_20261030.py)
- it1-rmj-20261030-r2, it1-rw1-20261030-r5 (second pass after r4 clean), it1-o6-5a-20261030-r3. Files at launch: map 1614 lines LF; RMJ 146 lines; RW1 101; O6 142; D26 177.
- rw1 r5 (14:23): CLEAN (second clean pass): R-w1 and R-w1(c) CLOSED. Minors 1–9 repaired in the note at 14:2x (status labels, RG1 (1.1) with VAR Theorem 1 and p.309, b₀ and the per-position localisation in §5(g), the δ_M factor 4^{−N_M}/(1 − x) per V3 L3807 with the monotonicity, C_w′ = C_w(1 − x)/(1 − x′), V3's C_d suffices, 3c_H, (b)'s margin 2/3, μ̂ < τ_b and τ_w ≤ τ_b, Lemma gaussian-payment(iii)). Map status labels (l.1117, l.1132, l.1135, l.1136, l.171) wait for rmj r2 and o6 r3.
- o6-5a r3 (14:24): NOT CLOSED on status only (r2's F1–F3 repaired in substance). S1: §9's and §5's statements omit R-m read for the 𝐄/𝐑-brackets and R-A; repaired 14:3x in O6 l.3, §5 heading, §5a end, §9, "Derived here", D2.6 l.161. Minors: m1 (R-A's reason now names (3.5), (3.20) and the missing scale comparison of Λ_j^{∼−1} with R-dec's layers; R-A stays a reading), m2 (R-A formula bracketed, covers the deformed shifts), m3 (b̄ for sup|β_j|), m5 (readings moved out of "Bałaban's, used as he presents them"), m7 (Schwarz on the B′-polydisc; margin (1 + 4/3)·B₀e^{16κ_s}·(3/4)r_{α,k} = (7/64)min(β,1)α_{1,k}), m8 (D2.6 l.161 factor ≤ 1 on 𝒫_k^{3/4}), m4 part (D2.6 R3, R15) repaired; m4's map l.199 and m6 (map l.956 condition list) and S1's map qualifier wait for rmj r2.

## Not triaged

- lf-gamma-creation-20261029-r1 (01:56) belongs to the LF γ work of the other agent and is ignored, as instructed.
