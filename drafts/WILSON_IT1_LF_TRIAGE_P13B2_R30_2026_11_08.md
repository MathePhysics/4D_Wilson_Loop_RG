# LF Triage, Part 13b2, Round 30 (lf-p13b2-20261108-r30, Full), 8 Nov 2026

## Verdict

Clean. The referee found no fatal, serious, or minor finding. Every named step of #4.472–#4.472-0-1, #4.517–#4.517-2, #4.561–#4.565-1, #4.567–#4.568, and the Cauchy note's #C8.6.5–#C8.6.7 is CORRECT, and Q1–Q6 are answered yes. There are six trivial points (t1–t6), all repaired below. Round 29 (narrow) was clean and this round is full, so 13b2 has two consecutive clean rounds, the second of them full. **13b2 is done.**

The referee also rechecked r29's m1 against the current text and found that it does not apply: R_j = R̄(K − j) is run-uniform (#CP.13). The residue is t2.

## Repairs of the Trivial Points

| Point | Repair | Lines |
|---|---|---|
| t1: "CRE's classes do through #4.523, whose (2.35), (2.37), and (2.38) … are open" asserts the inclusion while marking its support open | "For CRE's classes the inclusion is #4.523, whose (2.35), (2.37), and (2.38) at the radii r are open (packet 47), so it is open there too." Nothing in 13b2 uses that inclusion (the referee checked); #4.561.1-0.0 uses only #4.523's (2.39) bound | #4.472-0 |
| t2: R̄(K − j)'s bounds at an intermediate coupling of §8.6's path are unstated | new #C8.6.5-2: R̄(K − j) is the R of both endpoints (#CP.13-1), #CP.14 gives (log g^{−2})^r ≤ R̄(K − j) ≤ C(log g^{−2})^r at x^A = (g^A_j)^{−2} and at x^B = (g^B_{j+1})^{−2}, and log x lies between log x^A and log x^B | Cauchy #C8.6.5-2 (new) |
| t3: the constant of #C8.6.6-2 contains (1 + κ_s)²M₀²; #C5.7-3's interval carries the proviso abs(δ_j) ≤ ½(g^A_j)^{−2} | C(M), "C(M) containing (1 + κ_s)²M₀²"; "#C5.7-3, whose proviso abs(δ_j) ≤ ½(g^A_j)^{−2} holds a priori by #C5.7-4–#C5.7-8" (#C5.7-8: abs(δ_j) ≤ ε_γ(g^A_j)^{−2}, ε_γ ≤ ½ for γ small) | Cauchy #C8.6.6-2 |
| t4: the reality of the line at real z is #4.559, not #4.561.1 | "the line being real for real z (#4.559)"; #4.559 ends "and the line is real for real z" | #4.561.1-1-0 |
| t5: the radius of #4.567-1 is stated at the class's data only | new #4.567-1-1 and #4.567-1-1.1, re-derived below | #4.567-1-1, #4.567-1-1.1 (new) |
| t6: "and so does abs(log ū₀)" needs REG (1.73) | "by the same argument for the averages (REG (1.73), p.88: "The same argument can be applied to the averages")"; checked at REG p088.tex l.63–67, (1.73) abs((R̄₀u)_1^n(x_n) − 1) < 16dB₁(α₀ + α₁) | #4.561.1-1.3-1.1 |

**t5 re-derived.**
- On the coupling segment the data exp(ig′B) differ from the class's exp(ig_kB) by e^{iX}, with X = (g′ − g_k)B.
- By #C5.7-3–#C5.7-8, (g′)^{−2} ∈ [½, 3/2]g_k^{−2}, so g′/g_k ∈ [(2/3)^{1/2}, 2^{1/2}] and abs(g′ − g_k) ≤ (2^{1/2} − 1)g_k ≤ g_k.
- abs(g_kB) ≤ g_kb_k and ε′_k ≥ 25g_kb_k (#D.ε′_k), so abs(X) ≤ g_kb_k ≤ ε′_k/25 ≤ ε₁′/100, using ε′_k ≤ ¼ε₁′ (#4.560.1-1).
- abs(e^{iX} − 1) ≤ 2abs(X) ≤ ε₁′/50, and abs(V′) ≤ 9/8, so abs(V′_t − 1) ≤ (9/8)(ε₁′/50) + ¼C_{V′}ε₁′ < 0.3C_{V′}ε₁′, using C_{V′} ≥ 4C_{AL} ≥ 4 (#4.561.1-2, #4.561.1-1.3-1).
- Then abs(V′_t) < 1.15, since C_{V′}ε₁′ ≤ ½, and ρ_V abs(V′_t) + abs(V′_t − 1) < (0.575 + 0.3)C_{V′}ε₁′ < C_{V′}ε₁′.
- So the full radius ρ_V holds at every coupling of the segment. The referee's estimate needed only ½e^{−1/4}ρ_V.

## Inputs Pass on the Repairs

- #4.559: "Then (𝐔(i), 𝐉(i)) = (𝐔, 𝐉), and the line is real for real z."
- #C5.7-4–#C5.7-8: the bound abs(δ_j) ≤ ½(g^A_j)^{−2} is a priori, run by run, from BETA Proposition 2.9 and Lemma 2.1(i).
- #CP.13-1 and #CP.14: R̄(K − j) ≥ (log g_j^{−2})^r for either run, and R̄(K − j) ≤ C(log g_j^{−2})^r.
- #D.ε′_k: ε′_k := ε_k + C_c(α̂₀ + α̂₁) + 25g_kb_k, with abs(g_kB) ≤ g_kb_k.
- #4.561.1-2: C_{V′} := max(…, 4(1 + 384dB₁B₃)C_{AL}); and #4.561.1-1.3-1: C_{AL} ≥ 1.
- REG p.88, (1.73).

## SHAs

- At launch: LF d57736f994e7, Cauchy b718fb53496e, table 2fa4ca5e9d58.
- After these repairs and the §4 consolidation in progress (WILSON_IT1_CONSOLIDATION_2026_11_08.md): LF 69a55acccf73, Cauchy 80a32b343293.
- Table 1fe1ab080941, LABELS b94efd47ec2f (the fork, at LF 18cf0cee58d4).
