# Triage of lf-k0-20261103-r42 (LF 7233fdd32c4d → c460bb3394e3), 3 Nov 2026

Review: verification\isolated_reviewer\reviews\lf-k0-20261103-r42\review.md. Verdict: established as written up to minor corrections; no fatal, no serious; S1 and n1–n5 of r41 closed; seven minor. This is the first (K0) pass without a serious item. Each finding was checked against the text and the cited sources before repair. All repairs are derived, not reviewed. No line was added or removed, and no definition was added.

## Minor (repaired)

- **m1, PRT2's bond convention.** Checked against PRT2 p.224 l.17–19 ("we denote by Ω also the set of bonds ∪_{x∈Ω}st(x)") and (2.3): a scale-1 bond with an endpoint in Ω₂ is a bond of Ω₂^{(1)}, not of Λ₁. (c) now reads "(bonds of Ω₂^{(1)} under PRT2 (2.3) and p.224 l.17–19, constrained by no layer at the scale 1, which VAR leaves free)".
- **m2, the far V_L in (g)(6)(v).** The far blocks are bounded through ‖e^{−δρ_{y′}}V_L‖ ≤ C(d)‖e^{−δρ_{y′}}V_N‖ of (iv) centred at y′, with ρ(x, y′) + ρ(y′, y″) ≥ max(r₂/(2L), ρ(x, y″)), and ‖V_N‖_{y″} ≤ C(d)‖A_N‖_{y″⁺} through ℳ; the polynomial factors are powers of 1 + log L, absorbed by C(d)(1 + log(1 + log L)) in r₂. The conditions on r₂ and RM are unchanged.
- **m3, the claim's parenthesis.** Packet text only: the L-dependence is through C(L)e^{−δ₀RM/·} or C(L)/RM (the term R_♮), both absorbed by RM chosen after L. Corrected in the r43 packet.
- **m4, the imaginary part of ω_♮.** Im ηω_♮ is ω_♮ at Q_j Im ηA_N = Q_j Im ηu_R − D̄Q′_j Im ηω (u_R = A_N + ∂ω, table l.232), ≤ C(L, M)ε₁ by l.6's bounds on Im ηu_R and Im ηω; then (ii) and (iv) sup-to-sup.
- **m5, gaps across Λ_j in (g)(2).** Checked against PRT2 (2.2) ("Ω_j^{(j)} … is a sum of big blocks"): the gaps are ≥ min(RM, ML), and L²e^{−δ₀min(RM, ML)/4} ≤ c(d)δ² for RM after L and M ≥ M₀(L).
- **m6.** "Λ_{j−1} ∖ Λ_j" (twice) is now Ω_j^c, which Λ_{j−1} separates from Ω_j.
- **m7, the margins of the partition.** χ_j = 0 within RM/8 of the boundary of R_j in the units of the layer (≥ RM/4 left for the change in the overlaps, which are ≥ RM/2 wide); RM ≥ C(d)L, so the cubes Q_{48L} of (KW) about supp χ_j lie in R_j, and H^Λ_j reads V_L outside R_j only with e^{−c(d)RM/8}. (g)(5) now states the (KW) bound on these points. The use of (f) at r₂/2 that the review suggests is not needed: on Λ_{j+1}, RM/8 in its units is RML/8 ≥ r₂/2 ≥ 48L in the units of L^j.

## Next

r43 on (K0), prior review r42. If r43 is clean, (K0) has its second clean pass; then the C_H and δ_w renames queued in the r41 triage file, then (K1)–(K6).
