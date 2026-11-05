# LF Packet 4, Review 2: Triage

Review: verification\isolated_reviewer\reviews\lf-p4-20261104-r2\review.md (LF 726fefcc18c2). Verdict: (K1)–(K6), #A.10, and #0.1.27 hold for the N_b problem, with no fatal item and seven minors. There is one serious item, at #0.1.28. All items are accepted. LF after the repairs: 6fc1181a26a9 (labels 853df392f38b).

## Closed after the review

- **#0.1.28 / #0.1.42, the readings at blocks finer than c's (the former OPEN case).** Closed in #0.1.28.
  - Such readings occur only inside T_□: off T_□ run B's constraints are run A's composed with M (#4.445.1).
  - Inside T_□, c is run B's composite c^B or a configuration over it. Its W lives on run B's finest lattice, of spacing ε/L (#4.445.2), while run A's blocks have sides a_{j′} = εL^{j′} ≥ ε. So every reading is a composite average, of line integrals with weights of order L^{−d} (#A.8), over a union of blocks of side L of that lattice.
  - The first one-step average carries its weights, by the contours of RG I (0.4) (p.253) and p.252, on the blocks of side L and on the coordinate planes through their block points. W averages to ≤ C(d)(1 + log L)^p on both (#0.1.19), and the later averages keep the bound. With the gain (9/8)(1+β₀)²L^{−1} at i = i_prev − 1, the factor per level is C(d)(1 + log L)^{p′}/L, for every i < i_prev. No reading lies below the lattice of c's W.
  - Also, c^B's data region is the strip S_□ = □₀ ∖ Ω^B_1, with Ω^B_1 a box, so t₃ = L on □₀.
  - #0.1.42 no longer names an exception.
- **Dead routes.**
  - The gauge route fails at its step G2. At a d = 4 vertex where two local components touch in two separate contact regions, a flux line through the vertex makes v ~ δ/τ, so v genuinely carries the L/t₃ weight there.
  - The absolute class bounds of T_□ fail because the Cauchy note's recursion (8.3) does not accept absolute bounds (#0.1.8).

## Serious

1. **#0.1.28, case (ii), "the datum carries (1+β₀)²(i_prev − q)^{1/2}L^{−(i_prev−q)}".** Accepted.
   - The old term's domain is defined by the radii of its own scale i (CRE p.259: U_i^c(X, α_{0,i}, α_{1,i})), and #0.1.42 states the gain relative to the scale i. No statement admits a scale-q datum up to the layer-q threshold.
   - The paid case is now i_prev − i ≥ 2, with the gain (1+β₀)²(i_prev − i)^{1/2}L^{−(i_prev−i)} ≤ 2(1+β₀)²L^{−2}.
   - The OPEN case now covers i = i_prev − 1 at every reading scale q, and the reading scales finer than the lattice of c's W.

## Minor

1. **(K6), exponent bookkeeping.** (K6) now counts the exponents. The bulk inputs of (K1) carry p₁, the increments of (K2) carry p₁ + 1, (K3)–(K6) carry p₁ + 2, and the last two cases carry one more factor ρ₀. So W's exponent, written p in #0.1.18, is taken ≥ p₁ + 3. The text states that the shift is not circular.
2. **(K6), the opening.**
   - The paragraph now opens with the Λ^c bonds, bounded by (K2) directly.
   - It then defines t and t₃, with z for t < L. The case t ≥ 4ρ₀ is stated first, then "Let now t < 4ρ₀, so that z exists, and b a bond at x".
   - The one-component sentence cites the join argument of (K3), with R in place of r.
3. **(K5), the box.** (K5) now uses #0.1.24's box of sides ≥ 3r/4 in Q_{2r}(z), beyond Q_r(z) in one coordinate at distance ≥ (K₀ + 2)n. The cell of K′ containing z contains it, since its side intervals have length ≥ L ≥ 8r.
4. **#0.1.27, the Hölder improvement.** Now (r/r₀)^μ, with r₀ = min(L, t₃)/C(d) and μ = min(ν, α/2), at the scales r ≤ r₀.
5. **#A.10, LL's generator.** The citation is now Lawler–Limic p.17, where the generator is defined: 𝓛f(y) = −f(y) + Σ_xp(x)f(x + y).
6. **#0.1.28, case (i).** Now marked "given #0.1.41 (derived, not reviewed)".
7. **Lattice slack.** Acknowledged in the text; no change.

## Next

p4 r3 on LF 6fc1181a26a9 (labels 853df392f38b).