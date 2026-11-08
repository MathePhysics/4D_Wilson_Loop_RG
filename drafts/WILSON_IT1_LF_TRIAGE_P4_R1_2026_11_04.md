# LF Packet 4, Review 1: Triage

Review: verification\isolated_reviewer\reviews\lf-p4-20261104-r1\review.md (LF b2897e74677e). Verdict: (K1)–(K6) and #0.1.27 hold for the N_b problem, with no fatal item and eight minors. There is one serious item, at #0.1.28. All items are accepted.

## Open

- **#0.1.28 / #0.1.42, case (ii), the reading at q = i_prev − 1.**
  - What is missing: an old term may read c in c's weighted region at blocks finer than c's. #4.445.2 allows this inside T_□, where run B fixes only a coarser average than run A. There c carries W up to (1 + log L)^pL/ρ₀ near the contacts. The scale gain of #0.1.42 at q = i_prev − 1 is L^{−1} only, so the factor per level is (1 + log L)^p/ρ₀, which does not contract. At reading scales finer than the lattice on which c's W is measured, a bound on c below that lattice is also needed.
  - What closes it: showing that these readings lie off c's weighted region, or a further gain at them. A candidate route is the old term's gauge invariance, continued to G^c. It removes the ∂λ part of c, which is the source of L/t₃. What then remains is the contact weight of v from the Morrey bound of #0.1.20. A second candidate: inside T_□, run B's configurations satisfy the pointwise class bounds VAR (2) and (8) per layer (#4.444, #4.445.2), which carry no weight W. These bounds are absolute, of size O(B₃ε₁), so using them requires that the chain accept an absolute bound at the readings inside T_□.

## Serious

1. **#0.1.28, "the weight does not accumulate along the chain".** Accepted. The case (ii) premise, that the old term's unit bonds lie in c's unit-block region, is not in #0.1.42, and #4.445.2 contradicts it inside T_□. The sentence is replaced:
   - In case (i), no reading in c's weighted region occurs.
   - In case (ii), at scales q with i_prev − q ≥ 2 and q at least the scale of the lattice of c's W, the gain 2(1+β₀)²L^{−2} pays W ≤ (1 + log L)^pL/ρ₀. The factor per level stays C(d)(1 + log L)^{p′}/L.
   - The remaining readings are stated as OPEN, with what closes them: q = i_prev − 1, and scales finer than the lattice of c's W. #0.1.42 points to it, and its contraction claim names the exception.

## Minor

1. **(K3), #0.1.27.** The bound for r ≤ L/16 is now per cell, which is the form (K4) uses. For r ≤ t₃(z)/C(d), (K3) now proves the joins: two cells of K′ meeting Q_r(z) without a shared face meet at a point p within C(d)r < t₃(z)/2 of z. So p is not a contact between distinct local components, and the chain cells at p have deep sites in Q_{2r}(z). The inconsistent description of the uncovered joins is removed.
2. **(K6), the capped t.** Added: if no boundary site lies within t + 1 of x, which happens only at t = L, the chained (K4) about x gives abs(∂λ(x)) ≤ C(d)(1 + log L)^{p+1}θ ≤ C(d)Wθ.
3. **(K2), the mass bonds.** The unlocated "cutoff bound" is removed:
   - for t(b) ≥ 4√dρ₀, *The massive case.* of #0.1.26 gives the bound;
   - for t(b) < 4√dρ₀, abs(u(b)) ≤ (E(Q_s(b))/a)^{1/2} with s = 4√dρ₀, together with the Morrey bound, gives ρ₀ times the weight;
   - the v and w terms on mass bonds are now stated.
4. **Sign.** With Δ = 2d𝓛 = −∂*∂ (now stated in #A.10), Δλ = −σ in #0.1.27, (K2), #0.1.29, and #A.9. ψ′ := Σ_yG_Bσ/(2d), so that Δψ′ = −σ.
5. **Q_{6L}.** The cubes used lie in Q_{6L}(x̄), in #0.1.27 and (K2).
6. **The exponent p.** (K6) now states that the inputs' (1 + log L)^p becomes (1 + log L)^{p+1} in (K3)–(K6), and W's exponent is taken at least the inputs' exponent plus 2.
7. **(K4), the empty boundary.** M := m if Q has no boundary sites, the walk then stopping only at its exit from 𝒞_ρ.
8. **Lattice slack.** The (K3) join argument absorbs the O(1) slack at cube faces into C(d).

## Also applied

#A.11.19 (packet 5, from the pre-read): the δ-term carries the factor (1 + log L)² through the gap (d).

## Next

p4 r2 on LF 726fefcc18c2 (labels 855f7d519d36).
