# LF Packet 1, Review 4: Triage

Review: verification\isolated_reviewer\reviews\lf-p1-20261104-r4\review.md (LF 2fa9f7052cd3). Verdict: ESTABLISHED; no fatal or serious item. This is the first clean pass of packet 1. LF after the repairs: deb32bee75a2, labels ef5cc42d07c7.

## Minor

1. **Constants of Δ_j's decay (#0.1.17).** Accepted. The decay is now derived with constants of d only:
   - on {Q_jA = B}, PRT1's form (1.69) is ‖∂A‖² + ‖R∂*A‖² + a‖B‖², with minimum ⟨B, Δ_jB⟩ + a‖B‖² at H_jB (PRT1 (1.64)–(1.65), p.29 l.4);
   - so Δ_j = (Q_jG_jQ_j*)^{−1} − a with G_j = Δ_a^{−1};
   - Q_jG_jQ_j* is bounded above and below by constants of d only for a = 1 (PRT1 (1.100)–(1.101), p.34 l.27, checked);
   - its kernel decays with δ₀ and O(1) of d only (PRT1 Proposition 1.2, (1.110), p.35, checked);
   - Combes–Thomas for this unit-lattice operator gives abs(Δ_j(x, y)) ≤ C(d)e^{−c(d)abs(x − y)}.

   PRT2 p.243 l.43 identifies (2.120)'s Δ_j with PRT1 (1.66), checked. This matters because C_H = o(L) (#0.1.10): an L-dependent rate would enter C_H^{reg} through the block sums of (K1).
2. **Truncation of ρ on an infinite Λ.** Not needed: PRT2 works on the torus.

## Repairs in the same LF revision (packets 2 and 3, from the self-check)

- **#0.1.19, last sentence.** The old sentence was false for an L-shaped configuration: two cells meeting only in codimension ≥ 2 can be joined through a third cell near the contact. The sentence now excepts joins through chains of face-sharing cells, and t₃ counts only contacts between distinct local components.
- **#0.1.26, scales below t(y).** The dyadic sum used the Morrey bound alone, which gives (L/ρ₀)^{1−α/2} at the smallest scales. *The interior bound.* now covers the scales below t(y)/8:
  - with R = t(y)/4 and u ∈ 𝒮, ∂₁*u = Π_m∂₁*u on Q_{2R}(y), so Δ_ju = h₀ there;
  - subtracting ∂₁φ makes u co-closed;
  - the base-averaged axial primitive and a harmonic gauge give u″ with ‖u″‖ ≤ C(d)R‖F‖;
  - the Gaffney identity bounds ∇u″;
  - Caccioppoli for the differences of the T-harmonic part, iterated, and lattice Sobolev give sup_{Q_{R/2}}abs(F) ≤ C(d)(R^{−d/2}‖F‖_{Q_{2R}} + R sup abs(h₀)).
- **Specs.** The p2, p3, and p4 specs used "Bałaban's problem (the N_b problem)". In the LF, Bałaban's problem is VAR's problem (#0.1.29, #A.10), so the specs now say "the N_b problem (PRT2's form)".

## Next

p1 r5 (second pass), with prior = the r4 review. Then p2 r1.
