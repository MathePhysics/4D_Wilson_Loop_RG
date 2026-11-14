# LF Triage, Part 13b2, Round 28 (lf-p13b2-20261108-r28, Narrow), 8 Nov 2026

## Verdict

Not clean. No fatal or serious finding. Two minor findings (m1, m2) and four trivial points (t1–t4). Every named step and every consumer was CORRECT; m1 and m2 concern the scope and the premise of #4.567-3–#4.567-3-3.

## Repairs

| Finding | Repair | Lines |
|---|---|---|
| m1: "in his own setting" (#4.567-3-3) overstates the scope at §8.6's hybrid points: an intermediate coupling with one run's threshold, and a sharp enlarged cutoff | The path of x = g^{−2} from x^A to x^B is read with each coupling's own cutoff: per bond χ̄(abs(B′(b))/t), with g := x^{−1/2}, B′ := g^{−1}(1/i)log V′ (p.356 l.31) and t := M₀p₀(g). Every path point is then Bałaban's denominator (1.1)–(1.2) at the coupling g, at the point's configuration (the lift's, for run B). The threshold bullet becomes the cutoff part of ∂_x. ∂_x log y = 1/(2x) − p₀/(x log x) ∈ [0, 1/(2x)] once log x ≥ 2p₀. The enlarged sharp cutoff (1 + κ_s)t only bounds the modulus, at the constant (1 + κ_s)M₀; M₀ is not fixed on pp.356–358 (p.378 l.13–14). | Cauchy #C8.6.5 rewritten, #C8.6.5-1 new, #C8.6.6–#C8.6.7-4 rewritten, #C8.6.7-5 and #C8.6.7-6 deleted; #4.567-3-3's last sentence cites #C8.6.5-1 |
| m2: the 𝒫 premise of #4.567-3 cites only #T11.14, while #4.559-2 says (LF-2)'s class is CRE's Ũ^c and #4.472 says the norms are taken "on the classes themselves" | #4.472 split. #4.472-0 now states that the b_i are taken on the classes themselves and the bounds of (LF-2) on the norm classes (*The complex class.*, #4.559-2). #4.559-2 now says the class is the norm class at the radii r (#0.3, #4.472), on which (LF-2) enters through the 𝐑-differences (#4.472-1), its pairs written as in CRE's class with the radii r (#4.523). #4.567-3 cites #0.3, #4.472 and #4.559-2. | #4.472, #4.472-0 (new), #4.559-2, #4.567-3 |
| t1: "composed as on p.31 l.31" in #4.561.1 | "iterated by (43), p.024 l.2–4" (CMP98) | #4.561.1 |
| t2: "a G-valued field near 1" | "a regular G-valued field", the logarithms being those of loops near 1 | #4.561.1 |
| t3: pins off by one | p.377 l.6–7, p.388 l.13–14 and RG I p.262 l.13, the corrected-file lines | #4.567-3, #4.567-3-3 |
| t4: the appeal to #4.5-2 is unnecessary | M^{k+1}(ι_X𝐔) = M^k(Mι_X𝐔) = M^k(𝐔) on X^∼, by (43) and Mι_X𝐔 = 𝐔 (#C3.2) | #4.567-3-3 |

## Inputs Pass on the Repair (Finished 14:06)

**m1 (Cauchy §8.6).** Re-read against LFR II p356–p358 and p378 (corrected transcripts).
- d's integrand in the variables V′ (Haar measure, x-free) depends on x only through exp[−xA(ζ₀, U_{j,Z}(V′V_Λ))] and the tests χ̄(y_b). U₀, V_Λ, Λ, ζ₀ and G₀ are coupling-free ((1.2)–(1.3)). So the exponent part and the test part make up the whole x-derivative. #C8.6.3 counts E_j(Λ) separately, a harmless overcount.
- **Exponent.** ∂_x(log d + xA(ζ₀, U₀)) through exp[−xA] = −⟨A(V′) − A(U₀)⟩. x times the difference is (1.2)'s exponent at g:
  - the form is ≤ C abs(B′)² ≤ C(1 + κ_s)²M₀²p₀(g)² per bond;
  - the linear term is ≤ (1 + κ_s) times (1.6), < 1 + κ_s in total, (1.6) being linear in the cutoff;
  - V is O(g^{1−β})abs(Λ).

  The factor g² = x^{−1} gives ≤ Cg²p₀(g)² per bond.
- **Path.** ½g_j^{−2} ≤ x ≤ (3/2)g_j^{−2} (#C5.7-3). So g² ≤ 2g_j², and p₀(g)² ≤ (1 + log(3/2)/log g_j^{−2})^{2p₀}p₀(g_j)² ≤ 2p₀(g_j)². **The pre-check found that #C8.6.6-2 used the upper bound on x without stating it; repaired in place before r29 (Cauchy 8f826cda6840 → 6825da2f364d).**
- **Average.** abs(⟨f⟩) ≤ sup abs(f) · ∫abs(integrand)/abs(d).
  - abs(d) = abs(e^{−xA(U₀)})e^{E}e^{−Re I}, with abs(I) < O(1)log M abs(Λ) by (1.11), at g.
  - ∫abs(integrand) ≤ abs(e^{−xA(U₀)})e^{E}e^{O(1)}∫exp(−γ₀‖B′‖²/(4d(100M)⁵)), by (1.9) with the complex perturbation; this is ≤ the same prefactor times exp(O(1)log M abs(Λ)).

  So the ratio is ≥ exp(−O(1)log M abs(Λ)), and abs(Λ) ≤ O(M⁴) (p.358 l.26). The soft cutoff is LF #3.94–#3.94-1.
- **Test.** y = x^{1/2}abs((1/i)log V′)/(A₀M₀(log x)^{p₀}), with p₀(g) = A₀(log g^{−2})^{p₀} (#T3.27-0). ∂_x log y = 1/(2x) − p₀/(x log x), so abs(∂_xχ̄(y)) ≤ (1/κ_s)(1 + κ_s)/(2x) ≤ (1 + κ_s)g_j²/κ_s.
  - The product rule, with every other factor ≤ 1 and supported where abs(B′) ≤ (1 + κ_s)t, gives abs(∂_x d) ≤ abs(Λ^{(j)})(1 + κ_s)g_j²/κ_s ∫abs(integrand) at that cutoff.
  - Dividing by abs(d) and integrating over a path of length abs(δ_j) gives ≤ C(M)g_j²abs(δ_j)/κ_s per bond.
- **Setting.** At each path point the configuration lies in the run's U^c(Z, ·) at the thresholds of g (#4.567-3-3), and Bałaban's bounds there are those of p.358 l.27–30, with ε replaced by O(α).

**m2.**
- #0.3 states the class norms on the norm classes at r = α/(8B₃).
- #4.472-1 reads the class norms only at run A's configurations and at the members on the margin ball.
- #4.567-3 uses of the norm class only 𝒫_k(X; r)'s (i)–(iii) and the lift half (#C5.5-1, #C5.5-2, #C5.6-3).

**t1–t4.**
- CMP98 p.024 l.2–4 is (43), the iterated average.
- LFR II p.377 l.6–7 ("Y ∩ Z^∼ is a union of components") and p.388 l.13–14 (the polymer of (1.91) is the connected domain), corrected files.
- RG I p.262 l.13 ("union of orbits").

**Consumers of #4.472 outside 13b2.** #0.1.8, #4.454.13, #4.523, #4.540.1, Cauchy #C5.15-5 and #C8.2.2-61 cite #4.472 for its bullet, which includes #4.472-0 and the sub-bullets (a citation of a tag names the line with its continuation lines). None changes meaning.

**Open item for #4.523's packet (47), not used in 13b2.**
- #4.523 says that norm-class points satisfy all of CRE (2.34)–(2.39) at the radii r.
- (2.34), (2.36) and (2.39) follow from 𝒫's single-scale bounds via CRE (2.6) and the layer factors; this is all that 13b2 reads through #4.523 (#4.561.1-0.0's c_av is (2.39)'s path bound).
- Whether (2.35), (2.37) and (2.38) hold at norm-class points must be derived, or #4.523 narrowed to what its consumers use, before packet 47.

## Pre-Check for r29 (lf-p13b2-20261108-r29, Narrow)

**Changed lines, each re-read (14:01–14:06):**
- LF: #4.472, #4.472-0, #4.559-2, #4.561.1, #4.567-3, #4.567-3-3.
- Cauchy: #C8.6.5, #C8.6.5-1, #C8.6.6, #C8.6.6-1, #C8.6.6-2, #C8.6.6-3, #C8.6.7, #C8.6.7-1, #C8.6.7-2, #C8.6.7-3, #C8.6.7-4.

**Consumers checked:**
- #4.567-2 cites #C8.6.3–#C8.6.7 and #4.567-3; Cauchy #C8.6.2-16 cites #4.567-3.
- #4.561.1-1-0 points to #4.561.1.
- #4.568 is unchanged.
- No line cites #C8.6.7-5 or #C8.6.7-6; the table cited neither (fork, 14:03).

**Sizes and format:**
- LF lines: #4.559-2 is 421 characters, #4.561.1 437 and #4.567-3-3 583.
- Cauchy lines are ≤ 440 characters; #C8.6.6-2 is 264.
- CR count 0 in both files.

**Symbols:**
- The local symbols g := x^{−1/2} and t := M₀p₀(g) on the path are recorded in table row #T12.7-18 (fork, 14:03).
- No other new symbol.

**Citations, each quoted and checked:**
- LFR II p.356 l.31 and l.37, p.357 l.9–10, (1.6) at p.357 l.37–40, (1.9), p.358 l.25–30, (1.10)–(1.11), and p.378 l.13–14.
- CMP98 p.024 l.2–4.
- LFR II p.377 l.6–7 and p.388 l.13–14.
- RG I p.262 l.13.
- #C5.7-3 and #T3.27-0.

**Snapshot (the build at 14:07):** LF d89bf93c0fa0, Cauchy 6825da2f364d (a note of the spec, with LABELS_CAUCHY.md), table dddfdf3806d9, LABELS b223ce5e35c7.
- 29 files; argument 11,245 characters; packet.json 22,127 bytes; CR count 0.
- The definition check has 0 conflicts.
- Extracts: #4.472–#4.472-0, #4.559-2, #4.561.1, #4.567–#4.568, and Cauchy #C8.6.2-14–#C8.6.7-4.

## Messages

- 14:00, to the table fork: the LF and Cauchy SHAs, the new tags #4.472-0 and #C8.6.5-1, the deleted #C8.6.7-5 and #C8.6.7-6, the #T12.7-18 change, and a relabel request.
- 14:03, from the fork: relabelled at LF d89bf93c0fa0, table dddfdf3806d9, LABELS b223ce5e35c7, with a definition check of 0. #T12.7-18 now reads "x := g_j^{−2} (#C8.6.2-17), and g := x^{−1/2} and t := M₀p₀(g) on the path of x from x^A to x^B (#C8.6.5), are local". The fork re-derived t and ∂_x log y. I verified both SHAs and the row; #4.472-0 is in LABELS.

## SHAs

LF 16a7cb388027 → d89bf93c0fa0; Cauchy 4c3f931eee83 → 8f826cda6840 → 6825da2f364d.
