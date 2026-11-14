# LF Triage, Part 13b2, Round 29 (lf-p13b2-20261108-r29, Narrow), 8 Nov 2026

## Verdict

Clean. The referee reported no fatal or serious finding, one minor finding (m1), and four trivial points (t1–t4). Every named step and every consumer was CORRECT. m1 is incorrect (below), so the round has no fatal, serious, or minor finding. At the user's instruction (given after r29 returned), a round whose only minor finding is incorrect counts as clean. This is the first clean round after r28; the full round r30 is due.

## m1 Is Incorrect

**The finding.** The objects fixed along §8.6's path (Λ, ζ₀, G₀, U₀) are built with R_k = R(g_k) of CRE (2.5), a function of the run's coupling. So a path point at an intermediate coupling g would be a hybrid: the coupling g with the R of another coupling.

**Why it fails.** The notes do not use CRE's R(g_k).
- Both runs use R_j := R̄(K − j) (Cauchy #CP.13), a function of the scale only. Run B's scale j + 1 has the same R̄(K − j) as run A's scale j (#CP.13-1), although the two couplings differ.
- So R never follows the coupling, and a path point stands exactly as the endpoints do.
- The facts used of R are (log g^{−2})^r ≤ R_j ≤ 2^{r+1}L(log g^{−2})^r and e^{−cMR_j} ≤ g^N (#T2.23, #CP.14). They hold at both endpoint couplings, and (log g^{−2})^r is monotone along the path. So they hold at every coupling of the path.
- The referee also concedes that the bounds hold at the path points.

## Repairs of the Trivial Points

| Point | Repair | Lines |
|---|---|---|
| t1: "a bound derived on a class holds on its norm class" presupposes that the class contains the norm class | Stated where the class contains it: run A's class does (Cauchy #C5.5-8), and CRE's classes do through #4.523, whose (2.35), (2.37), and (2.38) at the radii r are open. The sentence on real backgrounds is split off as #4.472-0-1 (line length). | #4.472-0, #4.472-0-1 (new) |
| t2: iterating CMP98 (15) needs each average to be regular | "each average being regular again by (53), p.026 l.27–36, for α₀ ≤ c₂ of Proposition 2" | #4.561.1 |
| t3: the soft cutoff falls under the sharp-cutoff bounds only through LF #3.92–#3.95; "supported" should name χ̄′ | "soft through LF #3.92–#3.95" in #C8.6.5-1; "χ̄′ being supported on [1, 1 + κ_s]" in #C8.6.7 | Cauchy #C8.6.5-1, #C8.6.7 |
| t4: the derivative bounds ∂_x(E_j(Λ) − I), not ∂_x I; Λ, ζ₀, G₀ are defined at LFR I (1.100)–(1.101) | "The coupling inside −I + E_j(Λ), which counts #C8.6.3 again (an overcount)"; the pins LFR I (1.100)–(1.101), p.201 l.28–31, added. The objects are said to be built with the run-uniform R_j of #CP.13, fixed along the path. | Cauchy #C8.6.5 |

The name check's remark (y local, not listed) is passed to the table fork for #T12.7-18.

## Inputs Pass on the Repairs (Finished 14:28)

**Pins.**
- LFR I p.201 l.28–31: G_i fixes the axial gauge, ζ_i ∈ C₀^∞(X_i), and (1.101) is the cutoff on Λ_i.
- CMP98 (53), p.026 l.27–36: |Ū^j(∂p) − 1| < α₀L^{2j}η² + C₀(α₀L^{2j}η²)²[…] for j ≤ k. Its right side is < 2α₀ under C₀α₀ ≤ ⅓ and 2α₀ ≤ c₂′, that is, α₀ ≤ c₂ of Proposition 2 (l.46–52). So each iterate is regular in its own units.
- LF #3.92–#3.95: d̄ = E_s[d(s)] and abs(log d̄ − log d(1)) ≤ ½.
- Cauchy #CP.13–#CP.13-1 and table #T2.23: R_j := R̄(K − j), run-uniform.

**A claim of the R28 triage, now verified.** The claim is that 13b2 reads through #4.523 only CRE (2.34), (2.36), and (2.39), and that these follow at norm-class points from 𝒫's single-scale bounds. 13b2 reads them at #4.561.1-0.0 and #4.561.1-0.0-1.
- **Units.** CRE's ξ = L^{−j} (p.256 l.58). So on the top layer n = j the layer factor is 1, and (2.34), (2.36), and (2.39) are RG I's (1.11), (1.14), and (1.13) (p.262).
- **Lower layers.** On a layer n < j the factor 1 − β(1 − 2^{−(j−n)}) is ≥ ¾ (β = ¼). By CRE (2.6), g_j ≤ (1 + β₀)(j − n)^{1/2}g_n and g_n ≤ (1 + β₀)g_j. So α_{i,j}/α_{i,n} ≤ 2(1 + β₀)(j − n)^{1/2} for γ small, the logarithms differing by ≤ 2log(1 + β₀).
  - **(2.34).** The single-scale bound at r_{0,j}ξ² gives (2.34) at r_{0,n}ξ²L^{2(j−n)} once (¾)L^{2(j−n)} ≥ 2(1 + β₀)(j − n)^{1/2}.
  - **(2.39).** L^nξ abs(A′) ≤ L^{n−j}r_{1,j} gives (2.39) once (¾)L^{j−n} ≥ 2(1 + β₀)(j − n)^{1/2}; the gradient carries L^{2(n−j)}.
  - **(2.36).** The current carries L^{3(j−n)}.
  - All three hold for L large, a permitted restriction (side lengths), and for the orbit representative of #C5.5-1.
- **Open.** (2.35), (2.37), and (2.38) at norm-class points remain open (packet 47; plan row 47). #4.472-0 now says so.

**Full-round preparation.** The inputs pass on #4.517–#4.517-5 and #4.566 is done, and the whole part #4.561–#4.566 was read.
- VAR p.280 l.51–52, p.281 l.1–3 and (19), p.294 l.44 (113), and p.307 l.1–5.
- REG p.083 l.17–20, p.088 l.9 and l.37–38, (1.69)–(1.73) with the transcriber's note on L^{n+l−j}, and (1.19) at p.079 l.3–10.
- CMP98 (105)–(106) at p.033, and p.034 l.9 (𝔤^c-valued A_b in the setting of (130)–(131)).
- CRE p.261 l.42–43 and l.58–61.
- #4.517's inversion: from CMP98 (78), R̄₀(u^{−1}) = (R̄₀u)^{−1} at each step, so R̄₀u^j = 1 is kept.
- Arithmetic re-derived: #4.517-1-1 (2Σ4dε₂L^{n+1−j} ≤ 16dε₂), #4.517-2 (−log(2 − e^s)/s ≈ 1.34 at s = ¼), #4.561.1-0 (54c_avα̂₁ ≤ c_avε′_k by C_c = 60), #4.561.1-1, #4.561.1-2 (each entry of C_{V′}), #4.563-1.1, and #4.565-1.
- No new finding.

## Pre-Check for r30 (lf-p13b2-20261108-r30, Full)

**Changed lines re-read.**
- The trivial repairs: #4.472-0, #4.472-0-1, #4.561.1, and Cauchy #C8.6.5, #C8.6.5-1, and #C8.6.7.
- #C8.6.6-2, reworded in this pre-check ("since p₀(g) = A₀(log x)^{p₀} (#T3.27-0) and log x ≤ log g_j^{−2} + log(3/2)"). The arithmetic: g²p₀(g)² ≤ 2g_j²·2p₀(g_j)², with (log x/log g_j^{−2})^{2p₀} ≤ (1 + log(3/2)/log g_j^{−2})^{2p₀} ≤ 2 for γ small.
- #C8.6.7: ∂_x log y ≥ 0 exactly when log x ≥ 2p₀, and ∂_x log y ≤ 1/(2x) since log x > 0.
- The 13b2 consolidation (WILSON_IT1_CONSOLIDATION_2026_11_08.md, 13b2 section): #4.561-1.1, #4.563-2, #4.563-2.1-1, #4.563-2.2, #4.563-3-0, #4.564 (a heading now), #4.565-1, and #4.567-1, with #4.566 outside the part. Its re-derivations:
  - c_pl = (4C₀^{ms} + 3L²B₅^c)/C₀^{ms}, from 2·2C₀^{ms}ε₁′ + 3L²ε₂;
  - abs(X^{−1}) ≤ 2, from abs(X − 1) ≤ ½;
  - Lemma (Two Constants) at z = i, with exponent (1/3)(15/16) = 5/16.

**Pointers looked up.** All resolve:
- LF: #4.567-3, #3.92, #3.95, #4.559-2, and #4.523;
- Cauchy: #C5.5-8, #CP.13, and #C5.7-3 (½(g^A_j)^{−2} ≤ (g^B_{j+1})^{−2} ≤ (3/2)(g^A_j)^{−2});
- table: #T3.27-0, #T1.4, #T3.32-1, #T3.32-2, #T4.23, #T11.19-1, #T11.20-1, and #T11.37-1;
- LFR II p.356: file line 32 prints "Writing $V'=\exp ig_kB'$", and the cutoff is at file line 38. These are the notes' l.31 and l.37 under the pin convention of earlier rounds.

**Consumers.**
- #4.567-2 to #4.567-3-3 agree with #C8.6.5-1: "its own cutoff", with thresholds ≥ 0.8α_{i,k} at every path coupling.
- #T12.27-1-2-1 cites #4.563-2 and #4.563-3-0. The G^c use there is unchanged.
- The deleted #4.561.1-3 and #4.563-2-1 are cited only in history files.

**Table.**
- #T12.7-18 lists g, t, y, and B′ as §8.6's locals (table c8c0a2f0fb4a, then 2fa4ca5e9d58).
- #T12.9-1 states the current c_pl, C_{V′}, and B₅^c, so r25's remark that these rows were stale is dropped from the spec.

**Definition check.** 0 conflicts, 5 allowed:
- ε₂ as in r25;
- B′, g, t, and y as locals of §8.6, each other definition site read: the LF's #D.g.5, #D.t–#D.t.5, #D.B′, and #D.B′.2, the BP files' local g and t, and two false matches (𝐔_t, ξ_y).

**Sizes.**
- Part 13b2: 24,544 characters before the consolidation and 23,814 after.
- Argument: 31,198 characters, of which 3,090 are context (#4.559–#4.560-0). It is not split, at the user's instruction ("Don't split!", 8 Nov 2026).
- CR 0; all touched lines ≤ 600.

**Known weak points.** None in the extracts. #4.523's (2.35), (2.37), and (2.38) at norm-class points are open, belong to packet 47, are stated open in #4.472-0, and are permitted background here.

**Snapshot.** LF d57736f994e7, table 2fa4ca5e9d58, LABELS 29d13d604009, Cauchy b718fb53496e. Build at 14:45 (18 snapshot files, packet.json 46,332 bytes).

## Messages

- 14:03, from the table fork: relabelled at LF d89bf93c0fa0 (table dddfdf3806d9, LABELS b223ce5e35c7), recorded in the R28 triage.
- From the table fork, before 14:20: table 482b429b85e6, LABELS 1aeda691e869 (BETA's §§4–10 rows; #T10.18 keeps the normalised trace that LF #4.563-3-0 cites). I verified both SHAs.

## SHAs

LF d89bf93c0fa0 → 16ba68a9c7f3; Cauchy 6825da2f364d → f38bf66bebd9.
