# Triage of lf-p13b2-20261108-r17

## Verdict

- r17 was a narrow round of 13b2 on r16's repairs and their consumer, at LF 14a59772400b, table 6d09b1b5054d, and labels 971e7d7d5325.
- **Fatal:** none. **Serious:** none.
- **Minor:** one, m1. #4.517's count "the exponents … sum to s ≤ 2dε₂" is not derived. u is built by CMP98 (104)–(106) from averaged contours and normalisations, not from raw η-lattice transports. Bałaban's own bound of this u, REG (1.70)–(1.72), is |u − 1| < 16dε₂.
- **Trivial:** c_G and r_G play no role in the bound; #4.561-1.2 cited the use, not the origin, of 4c_Gdε₂ ≤ 1. Both disappear with m1's repair.
- r16's m-a, o-b and o-c were confirmed repaired. #4.561.1, #4.561-1-2 and #4.563-3-1 were found correct.
- The round is not clean, so 13b2's count stays 0.

## Repairs

| Finding | Line | Issue | Repair |
|---|---|---|---|
| m1 | #4.517 (now #4.517–#4.517-5) | The raw count s ≤ 2dε₂ does not match CMP98 (106) | #4.517-0: u is given in terms of U_1 = e^{iη𝐇_c} by CMP98 (106) (REG p.88 l.37–38), a product over the levels n < j of brackets, each conjugated by R of a transport of the real U₀, each an averaged contour times the inverse of its normalisation (105). #4.517-1: both exponents of the n-th bracket are ≤ t_n; REG (1.71) with VAR (19)'s ε₂ for B₁(α₀ + α₁) gives t_n < 4dε₂L^{n+1−j}, its inputs CMP98 (130)–(131) holding for 𝔤^c-valued fields (CMP98 p.34 l.9); so s ≤ 2Σ_nt_n ≤ 8dε₂/(1 − L^{−1}) ≤ 16dε₂. #4.517-2: with 256dε₂ ≤ 1, abs(log u) ≤ −log(2 − e^s) ≤ 2s ≤ 32dε₂. c_G and r_G are gone from the bound |
| m1, consumers in 13b2 | #4.561.1-1.3-1.1, #4.561.1-1.3-2, #4.561.1-2, #4.561-1-2, #4.561-1.2 | 4c_Gd and its conditions | abs(log u₀) ≤ 32dε₂^{AL}; with 128dε₂^{AL} ≤ 1, abs(D^{AL}(z) − 1) ≤ e^{64dε₂^{AL}}C_{AL}ε′_k + e^{64dε₂^{AL}} − 1 ≤ 2(1 + 384dB₁B₃)C_{AL}ε′_k, and abs(V′ − 1) ≤ 4(1 + 384dB₁B₃)C_{AL}ε′_k; C_{V′}'s second entry is 4(1 + 384dB₁B₃)C_{AL}; at the base 1, 256dε₂ ≤ 1 gives 256dε₂^{AL} ≤ 1 and 128dε₂^{AL} ≤ 1; (T-c) holds #4.517-1–#4.517-2's 256dε₂ ≤ 1 and the smallness of ε₂ in REG (1.71) |
| m1, consumers outside 13b2 | #4.198-0, #4.198-0.1, #4.244, #4.518, #4.519, #4.521, #4.536-2; Cauchy #C5.47-5, #C5.47-9, #C8.2.2-30 | The same raw count or its constant | #4.198-0: 32dε₂. #4.198-0.1: (1 + 64d)ε₂ for the averages and 2(1 + 64d)ε₂ for the current; c_ϰ := O(1)(1 + d). #4.518: abs(log ū) ≤ 32dε₂; the product of two has abs(log) ≤ −log(2 − e^{64dε₂}) ≤ 128dε₂. #4.244, #4.519, #4.521: 1 + O(dε₂). #4.536-2: u_{k,Λ}, u_1 given by CMP98 (106), abs(log u) ≤ 32dB_Vδ^c, abs(log u″_k) ≤ 32dC_fac(N₀ + 1)^{1/2}max_mε_m. Cauchy: the three lines cite CMP98 (106) and #4.517-0–#4.517-2 instead of the raw count |
| (pre-check of r18, from my reading of all of 13b2) | #4.563-3 (now #4.563-3–#4.563-3-0) | "≤ abs(X − 1)² for abs(X − 1) ≤ ½" used without showing abs(X − 1) ≤ ½ | #4.563-3-0: "abs(X^{−1}) ≤ 2, since at each plaquette, in its own run's layers, X = YU^r(∂p) has abs(X − 1) ≤ abs(Y) abs(U^r(∂p) − 1) + abs(Y − 1) ≤ 4C₀^{ms}ε₁′ + 3ε₂ ≤ ½ (#4.563-2–#4.563-2.1-1) by (T-c)'s 16C₀^{ms}ε₁′ + 16ε₂ ≤ 1" |
| (same) | #4.563-2.2 | The plaquette bound (2C₀^{ms}·2ε₁′ + 4α₁)/a_j² holds in each run's own layers, not in run A's indexing | "in its own run's layers, with abs(Y) ≤ 2 and the move 3ε₂ < 4α₁ (#4.563-2.1–#4.563-2.1-1)" |

- **Splits.** #4.517 (1,858 characters) is now #4.517 and #4.517-0–#4.517-5. The parenthetical on the gradient of u moved into #4.517-4, next to the A′ remark it explains. #4.518 → #4.518 and #4.518-1. #4.536-2 → #4.536-2 and #4.536-2-1. #4.563-3 → #4.563-3 and #4.563-3-0.
- **Re-points (bookkeeping).**
  - #4.519's and #4.563-2.2-1's "as at/in #4.517" and #4.521.3-1's "#4.517" now cite #4.517-5.
  - #4.536-1's and #4.536-2-1's covariance citations now cite #4.517-3.
  - #4.536-1's gradient remark and #4.540.4's A′ remark now cite #4.517-4.
  - Cauchy #C5.47-11 now cites #4.517-3.
- **Symbols.** The names C_n and N_n were dropped: they clash with the table (#T12.2-7, #T11.5, #T12.10; N_n of the W-δ note). t_n is unused elsewhere.

## Checks

- **m1, re-derived from the sources.**
  - VAR p.281 l.1–19: Proposition 2's u maps the axial U′U₀ to U_1 = U′^{u^{−1}} = e^{iηA} with (19) at ε₂ ≥ B₁(ε₀ + C₁ε₁). This is REG Theorem 4 (VAR's [6]) with (19) in the form of REG (1.69), ε₂ for B₁(α₀ + α₁).
  - REG p.88 l.37–38: u is determined by U_1 and given by CMP98 (106).
  - CMP98 (106) (p.033): u(x) is a product over the levels of R(U₀(Γ))^{−1} applied to the bracket [(normalisation)^{−1}(averaged contour)]. R is conjugation, as (103) shows. The normalisation is (105), the exponential of the average of the logarithms of the contours over B(x_{n+1}).
  - So the exponent of the normalisation is ≤ t_n, the exponent of the contour is ≤ t_n, and U₀ is real, so the conjugations keep the operator norm.
  - The product of exponentials gives abs(u − 1) ≤ e^s − 1 with s the sum of the exponent norms, valid at complex fields. This replaces REG's step abs(ab − 1) ≤ abs(a − 1) + abs(b − 1), which needs unitarity.
  - REG (1.71): t_n ≤ abs(Q_n(U₀, ηA))(Γ) + O((·)²) < 4dB₁(α₀ + α₁)L^{n+1−j}, by CMP98 (130). CMP98 §D takes A_b ∈ 𝔤^c (p.034 l.9), and Proposition 4 (p.038) states Q_k analytic with (135). So (1.71) holds at complex 𝐇_c with (19).
  - Σ_{n<j}L^{n+1−j} ≤ 1/(1 − L^{−1}) ≤ 2. So s ≤ 8dε₂/(1 − L^{−1}) ≤ 16dε₂, the same count as REG (1.72).
  - −log(2 − e^s)/s increases in s (the function is convex and vanishes at 0) and equals 1.336 at s = ¼. So abs(log u) ≤ 2s ≤ 32dε₂ for s ≤ ¼, which 256dε₂ ≤ 1 ensures, with s ≤ 1/16.
  - BCH: the logarithm series of the product, expanded in the exponents, groups into Lie polynomials, so log u ∈ i𝔤^c. No SU(N) fact is used.
- **#4.518.** u and ū each have abs(log) ≤ 32dε₂. Their pointwise product has exponents summing to 64dε₂ ≤ ¼, so abs(log) ≤ −log(2 − e^{64dε₂}) ≤ 128dε₂.
- **#4.561.1-1.3-2.**
  - x := 64dε₂^{AL} ≤ ½ by 128dε₂^{AL} ≤ 1, so e^x ≤ 2 and e^x − 1 ≤ 2x.
  - Hence abs(D^{AL}(z) − 1) ≤ 2C_{AL}ε′_k + 128d·6B₁B₃C_{AL}ε′_k = 2(1 + 384dB₁B₃)C_{AL}ε′_k.
  - At the base 1, ε₂^{AL} ≤ ε₂/4 (C_{V′} ≥ 4C_{AL} still holds), so 256dε₂ ≤ 1 gives 128dε₂^{AL} ≤ 1/8.
- **#4.198-0.1.** The old 8c_Gd was 2 × 4c_Gd, the two ends of a bond transported by u, so it becomes 2 × 32d = 64d.
- **Line lengths.** #4.517 218, #4.517-0 489, #4.517-1 495, #4.517-2 372, #4.517-3 256, #4.517-4 295, #4.517-5 506, #4.518 328, #4.518-1 489, #4.536-2 456, #4.536-2-1 537, #4.563-2.2 522, #4.563-3 147, #4.563-3-0 544; Cauchy #C5.47-5 295, #C5.47-9 455, #C8.2.2-30 253. No CRLF in either note.
- **Table.** Rows 326 (abs(log u″_k)), 464 (c_ϰ) and 466 (abs(log ū₀), C_{V′}, D^{AL}) restate the old c_G constants. They are sent to the table's owner. The request to record c_G ≥ 1 in #T4.10 is withdrawn: #4.517 no longer uses c_G.

## Open (packet 42, not yet launched)

- **#4.536-2: CMP98 (106) at the complex base 𝐔.** u_{k,Λ} and u_1 are taken at the complex base 𝐔, where (106)'s conjugations R(𝐔(Γ))^{−1} are not unitary. Their norms must be bounded through the class bounds of 𝐔's imaginary part (#4.534) before the count of #4.517-1 applies. This is to be derived before packet 42's launch. The line's conclusion, that Ad(u^{±1}) is within 1 + 2^{−9} of isometric for γ small, needs only a bound that tends to 0 with γ.
  - **Partial analysis.** At complex points LFR II (1.58) has the base 𝐔 for U_k and (1.57) the base U_{k,Λ} (p.371 l.35–46, #4.533). A contour of (106) from x to x_{j+1} has at most about 2dL^{j+1} fine bonds. With a_m abs(A′) ≤ r_{1,m} ((2.39), #4.534), each transport and its inverse has norm ≤ e^{O(dL)r_{1,m}}, so each conjugation is within e^{O(dL)r_{1,m}} of isometric, which tends to 1 with γ.
  - **What remains.** CMP98 §D's bound (130) for the averaged contours at a complex base. CMP98 takes U₀ real; #4.534 accepts Bałaban's bounds at (𝐔, 𝐉) for the operators, not for these averages.
  - **Repaired (2026-11-08 17:08).** balaban_proofs/BP_COMPLEX_BASE_GAUGE.md (#4.536.1–#4.536.10) reduces (106) at e^{iηA′}U to two gauges at the G-valued U, where CMP98's real-base count applies, and bounds the factor joining them (#4.536.5–#4.536.9). Result abs(log u) ≤ 72d(ε_A + ε_X) (#4.536.10), used in LF #4.536-2–#4.536-2-0.1 for u_{k,Λ}, u_1 (through the covariance #4.536.4) and u″_k. WILSON_IT1_CONSOLIDATION_2026_11_08.md, packet 42.

## Pre-check of lf-p13b2-20261108-r18 (narrow)

- **Spec.** specs\spec_p13b2_r18.json, prior r17, narrow.
- **Named steps** (changed since r17): #4.517–#4.517-2 (the counting argument, extracted), #4.561.1-1.3-1.1, #4.561.1-1.3-2, #4.561.1-2, #4.561-1-2, #4.561-1.2, #4.563-2.2 and #4.563-3–#4.563-3-0. Consumers in the packet: #4.561-1 (B₅^c and ε₂ through C_{V′}), #4.563-2.2-1, and #4.567-1 (C_{V′}).
- **Changed by split or re-point only** (context in r18, re-read, no mathematics changed): #4.517-3, #4.517-4 (with the moved parenthetical on a_j abs(∇log u)), #4.517-5, and #4.563-2.2-1 (now citing #4.517-5).
- **Re-read.** Every changed line was re-read in place. The arithmetic above was redone. All uses of 4c_Gd, r_G, "axial contours" and #4.517 in the LF, the Cauchy note, the W-δ note and the table were grepped. The LF has no remaining c_Gd or r_G. The W-δ note's two "axial contours" lines (#W12.143-1, #W12.174-3) are holonomy statements, not this count.
- **Cited displays.** REG (1.70)–(1.72) (p.088), CMP98 (101)–(106) (p.033), (130)–(135) (p.038–039) and p.034 l.9, and VAR p.281 l.1–19 were all read in the transcriptions this session.
- No known weak point and no OPEN is in r18's named steps. #4.536-2's open item lies outside 13b2 and is not cited by it.
- **Rounds.** 13b2: count 0. r18 (narrow), then r19 (full).

## SHAs

LF 14a59772400b (r17's snapshot) → 179b7dab2854. Cauchy 2acf54aae054 → f7bf7d6045cd. Table 6d09b1b5054d and labels 971e7d7d5325 (unchanged; rows 326, 464, 466 and the relabel pending with the table fork).
