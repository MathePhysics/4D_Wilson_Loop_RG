# Triage: LF packet 13b, round 4 (lf-p13b-20261108-r4), 8 Nov 2026

## Verdict

Not clean: one minor finding (m1) and nine observations (o1–o9). There is no fatal or serious finding. 13b's clean count stays 0.

LF reviewed at 0f55157a095f (table 31436db32f84, LABELS c4013f2c7f07, Cauchy c297b0730322). The referee confirmed:
- every round-3 repair (m1–m4, o3);
- the Lemma, the lines, the real points, (T-c), the non-circular disc data bound C_{V′}, the disc through (1.43) and Proposition 9, the results with exponent 5/16, the couplings, and the absorption into C_hθ̃^n.

## Origin of m1

- C₀^{ms} := 2L⁴C₀ (#4.7-2) has been in the LF since 6 Nov, before 13b's first round.
- The C₀ bounds of U^r (#4.563-2) came from the 13b r1 repairs. c_pl, C_act and the threshold 8C₀ε₁′ + 16ε₂ ≤ 1 came from the r2 repairs. All took Ũ's bound with C₀.
- C_y(M) and c_4 used C₀ before 13b.
- The pre-checks of r2–r4 grepped the touched symbols but did not check which regularity constant each bound needs. The r5 pre-check below lists every C₀ in the reviewed lines and its source.

## Repairs

| Finding | Where | Repair |
|---|---|---|
| m1: U^r's and Ũ's plaquettes quoted at 2C₀ε₁′/a_j²; (b)'s multiscale bound is 2C₀^{ms}ε_r (#4.48.0-0) | #4.561-1.2, #4.563-2, #4.563-2.1, #4.563-2.2, #4.563-3, #4.565, and #4.201's c_4 | C₀ → C₀^{ms} in U^r's bound (now "(b)'s bound at ε_r = ε₁′ (#4.48.0-0, #4.560-2)"), the threshold 8C₀^{ms}ε₁′ + 16ε₂ ≤ 1, c_pl := 2 + 3B₅^c/C₀^{ms}, the representative's plaquettes c_plC₀^{ms}ε₁′/a_j² and (2C₀^{ms}ε₁′ + 4α₁)/a_j², C_act := d²(c_plC₀^{ms})², the first-order bound 4d²C₀^{ms}ε₁′d̄′, and C_y(M) := 4d²(C₀^{ms} + C_U(M))C_U(M) + C_b. c_4 is taken at C₀^{ms} in #4.201 (the referee's second option), so #4.563-2.2 needs no new condition |
| m1, outside the packet (same fact) | §4(d): #4.71, #4.72, #4.82, #4.83, #4.92, #4.94, #4.95, #4.104, #4.116-1, #4.121, #4.122, #4.123, #4.139-1, #4.140, #4.150, #4.174-1, #4.198-1, #4.205, #4.207, #4.309, #4.311, #4.334, #4.344, #4.345, #4.350, #4.353, #4.433-1; §5: #5.21, #5.22, #5.68 | Every regularity bound of Ũ, (b)'s minimisers, c^A, U_{1,2}, and run B's background, and the conditions and constants built on them, at C₀^{ms} (#4.7-2, #4.48.0-0): B̄_ν, B̄′_ν, x₂, c_w, c_bf, c_4, C_d, C_ℓ(M), C_π, C_ψ, τ̂_n, ν_F, C_Y. §4(d) (open) and §5 (packet 53, open) are reviewed in their own packets. CRE's C₀ of (2.28) (α_{0,m}) and W-δ's C₀ are other constants and are unchanged |
| m1, done packets (bookkeeping) | #4.41-3-1 (11b), #4.50-2 (13a1) | #4.41-3-1's "a²abs(F_U) ≤ C₀ε₁ ≤ 1 of (9.2)" now reads C₀^{ms} (#4.7-2, #4.7-3); #4.7-2-1 already takes §9's constants at C₀^{ms}, so no bound changes. #4.50-2's list of §4(d)'s conditions now reads 4C₀^{ms}ε₁ ≤ α₁, the condition as §4(d) now states it |
| m1, Cauchy note | #C7.5-2 | The restatement of the LF's C_Y and its condition is replaced by the citation of LF #5.21–#5.22 |
| o3: VAR (172) needs V₀ regular in (7); the segment problems of (c) have base 2ε₁′ | #4.561-1 (split; new #4.561-1-1) | #4.561-1 now says that (173)'s inequality needs C₁ ≥ 1; at base ε₁′, C₁ = C_{V′}; at base 2ε₁′ (#4.51-1.1), C₁ = C_{V′}/2 ≥ 2, with the same C₁·2ε₁′ = C_{V′}ε₁′ |
| o5: #4.567 gives no Cauchy radius and does not name "the real ones" | #4.567 (split; new #4.567-1) | #4.567-1: the class's data have abs(V′ − 1) ≤ C_{V′}ε′_k ≤ ½C_{V′}ε₁′, since C(M) ≥ 2 (#4.43-1.2) and R_k ≥ L (#T2.23), so the radius is ≥ ½C_{V′}ε₁′; "the real ones" are those of §4(d), *The couplings.* |
| o6: "the couplings are fixed and equal in both runs" | #4.559-1.1 | Now "each run's coupling is fixed, as in (b)–(d); the coupling differences are bounded in *The results.* below" |
| o7: "the O(1) ≥ 1 of #4.523" | #4.561.1 (split; new #4.561.1-0) | Now "the O(1) ≥ 1 of #4.523's bound abs(log D′) ≤ O(1)r_{1,q}". The line was then 633 characters, so it is split at "So abs(D(z)D(0)^{−1} − 1)" |
| o8: #4.562-1.1 omits (T-Λ)'s direct γ-condition | #4.562-1.1 | Its exception list now includes #4.50-1.1.0-1's (1 + β₀)²γ < e^{−p₀}, a bound on γ |
| o9: line pins | #4.562-1, #4.563-2-1 | CRE p.259 l.48 → l.47 ((2.28) is printed on l.47 of the corrected file); PBG (3.39) p.397 l.4–7 → l.4–8 (l.4–5 introduce the covariant derivatives, l.7 is the display, l.8 its tag) |
| #4.563-2 at 634 characters | #4.563-2 (split; new #4.563-2-1) | Split at "REG states these bounds" |
| o1, o2 | none | No change, as in round 3: valid stronger conditions |
| o4: a₄ "absolute" as printed | none | No change: the note quotes the print and needs only independence of M, k and K |

## Re-derivation

- **#4.563-2.1.** The four factors e^{iη𝐇} change a plaquette variable by at most:
  - first order: η²abs(D𝐇) ≤ 2η²abs(∇𝐇) < 2ε₂L^{−2j};
  - transport: 4abs(U^r(∂p) − 1)η·abs(𝐇) ≤ 4·2C₀^{ms}ε₁′·ε₂L^{−j} ≤ 8C₀^{ms}ε₁′ε₂L^{−2j}, using abs(U^r(∂p) − 1) ≤ η²abs(F) ≤ 2C₀^{ms}ε₁′L^{−2j};
  - second order: (4η·abs(𝐇))² < 16ε₂²L^{−2j}.
  - So the sum is (2 + 8C₀^{ms}ε₁′ + 16ε₂)ε₂L^{−2j} ≤ 3ε₂L^{−2j} under 8C₀^{ms}ε₁′ + 16ε₂ ≤ 1. Dividing by η² gives 3ε₂/a_j².
  - The representative then has |F| ≤ (2C₀^{ms}ε₁′ + 3B₅^cε₁′)/a_j² = c_plC₀^{ms}ε₁′/a_j².
- **#4.563-2.2.** 3ε₂ ≤ 4α₁ gives (2C₀^{ms}ε₁′ + 4α₁)/a_j². c_4's curvature term 2(1 + d²)·a_j²abs(F)/2 is then ≤ 2(1 + d²)(C₀^{ms} + 2α₁) for ε₁′ ≤ 1. This is #4.201's c_4 at C₀^{ms}, so no extra condition enters.
- **#4.563-3.** There are at most d² plaquettes per point, and each term is ≤ abs(X − 1)² ≤ (c_plC₀^{ms}ε₁′)² in g^{−2}-units. So C_act = d²(c_plC₀^{ms})².
- **#4.565.** A block density's first derivative is ≤ d²·2·a_j²abs(F) ≤ 4d²C₀^{ms}ε₁′ per unit alignment, times d̄′. With the second-order term 4d²d̄′² and C_b, this gives C_y(M) = 4d²(C₀^{ms} + C_U(M))C_U(M) + C_b.
- **The thresholds.** All of them stay smallness conditions on ε₁′ or ε₁ with constants of L, d, G, M and Bałaban's constants, so they hold for γ small (#4.562-1). Nothing else in the packet changes.
- **o3.** VAR (173) (p.305 l.41) reads ε₂ = B₁(B₃(1 + 4C₁)ε₁ + C₁ε₁) ≤ 6B₁B₃C₁ε₁. The inequality is B₃ + C₁ ≤ 2B₃C₁, true for C₁, B₃ ≥ 1. At base 2ε₁′ and C₁ = C_{V′}/2, this gives ε₂ ≤ 6B₁B₃C_{V′}ε₁′ = B₅^cε₁′. C_{V′} ≥ 4c_av ≥ 4 (#4.561.1-2).
- **o5.** The domain is abs(V′ − 1) < C_{V′}ε₁′, and the class's points have abs(V′ − 1) ≤ C_{V′}ε′_k. Since ε₁′ = C(M)R_kε′_k ≥ 2ε′_k, the distance to the boundary is ≥ ½C_{V′}ε₁′.

## Pre-check, lf-p13b-20261108-r5 (full round)

**Changed lines in the extracts.** Each is re-read and re-derived above.
- #4.559-1.1 (o6);
- #4.561.1 and the new #4.561.1-0 (o7, split);
- #4.561-1 and the new #4.561-1-1 (o3, split);
- #4.561-1.2, #4.563-2, the new #4.563-2-1, #4.563-2.1, #4.563-2.2, #4.563-3, and #4.565 (m1);
- #4.562-1 and #4.563-2-1 (o9 pins, re-read in CRE p259_corrected.tex l.45–50 and PBG p397_corrected.tex l.1–10);
- #4.562-1.1 (o8);
- #4.567 and the new #4.567-1 (o5).

**Every C₀ in the reviewed lines** (grep of #4.556–#4.568) is now C₀^{ms}:
- #4.561-1.2: the threshold;
- #4.563-2: U^r, by #4.48.0-0;
- #4.563-2.1: the move, the representative and c_pl;
- #4.563-2.2: by #4.48.0-0 and 3ε₂ ≤ 4α₁;
- #4.563-3: C_act;
- #4.565: Ũ by #4.48.0-0, and C_y(M).
- The C_b of #4.565 is §9's constant at C₀^{ms} (#4.7-2-1).
- U_0's own bound 3ε₁ (#4.48.0-0) is not used in the packet.

**Consumers outside the extracts.** They are changed in the same pass (the repairs table) and are permitted background:
- §4(d) and §5 are open packets.
- The done-packet lines #4.41-3-1 and #4.50-2 change no bound.

**Symbols.** No new symbol. The rows that restate the changed constants (#T12.9, #T12.9-1, #T12.12, #T4.36) were sent to the table fork at 00:57.

**Other checks.**
- No known weak point is left.
- All new and changed lines in the extracts are ≤ 600 characters. #4.567 was 735 and #4.561.1 633 before their splits.
- The spec is specs\spec_p13b_r5.json: lf_sha 9862073671bf, prior r4. It adds #T2.23 to the background and a question on the regularity constants. The definition check gives 0 conflicts (6 allowed).

## Repaired SHAs

- LF 6e38d5fd2a97 → 9862073671bf.
- Cauchy c297b0730322 → 2acf54aae054.
- The table fork entered the rows (#T12.9-1: c_pl, C_act, C_y(M); #T12.9: B̄_ν, τ̂_n, C_π, c_bf, c_4, C_ℓ(M), x₂, B̄′_ν, and C_d now cited, not restated; #T12.12: c_w; #T4.36: C_Y) and relabelled at LF 9862073671bf and Cauchy 2acf54aae054: table 738ed458c86b, LABELS 49097cb3bd46. All four SHAs were verified here and in the r5 snapshot. c_pl, c_4 and C_Y were checked in the table's text. The fork's definition check gives 0 on the LF and on the Cauchy note.
- After the build the fork moved the table to 712c154a27ae (LABELS 59542fddffc0) for two-loops' BC r7 rows #T12.27-1 and #T12.27-1-1 only. 13b does not use them, so the r5 snapshot (table 738ed458c86b) stands.
- Gate answers for r5, all yes; the gate's 16 changed tags are those listed above.
- The r5 packet is 19,049 characters of reviewed blocks (r4: about 18.6k). The growth is the o3, o5 and o7 wording; there is no new mathematics beyond the repairs.
- New tags: #4.561.1-0, #4.561-1-1, #4.563-2-1, #4.567-1.
