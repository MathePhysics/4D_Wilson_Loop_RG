# Triage of lf-p1-20261104-r1 (LF packet 1, LF ce518165fbd7)

Review landed 4 Nov 2026 01:04; triaged 01:10–01:28 (times from `date`). Verdict: NOT ESTABLISHED AS STATED.

## F1 (fatal). The constraint bonds of the scales j ≥ 1

Finding: under PRT2 (2.3) and p.224 l.17–23, the scale-j constraints for j ≥ 1 are on the scale-j bonds with an endpoint in Ω_j^{(j)} and none in Ω_{j+1}^{(j)}; the LF's #0.1.33 adds the bonds into the y′ ⊂ Ω_{j+1}^{(j)}, so #0.1.31's "PBG's N(Q′) … fine crossing terms are not invariant", #0.1.35's N_b(Q′), and #0.1.37's y′ data are wrong for PBG's k-scale form.

Check: confirmed on the print (p.224 l.17–23, (2.3)). For j = 0, Λ_0 = Ω_1^c as a set of bonds contains the unit bonds into Ω_1, so the unit crossing bonds are constrained.

Scope: every caller of #0.1 steps (1)–(5) is a two-layer problem, a fine layer whose blocks are single sites in its own units and one coarse scale: #0.1.16 (Λ^c and Λ′ of PRT2 Lemma 2.4, form (2.122), p.244), #A.11.17 ((K0)(d) on 𝒫₁, Λ₀/Ω₁), and through (d) the rescaled Λ_j/Ω_{j+1} of (g)(2). There the coarse layer is the top one, so it has no coarser sub-blocks, and the k-scale reading never enters. For #0.1.16: PRT2 (2.97) p.240 sums a|Q_jA(b)|² over b ∈ Λ^c with the p.224 convention, so the crossing bonds carry it; (2.104) admits ω with ω ≠ 0 at the sites of Λ joined to Λ^c, which change those terms; N_b is exactly the invariance group, and 𝒮 has no zero modes. Packet 3 is not affected.

Disposition: #0.1.31–#0.1.37 are rewritten as the two-layer gap actually used, ‖ℓ^{−1}(D − ∂λ)‖ ≤ C(d)(1 + log L)‖dD‖ with λ in the gauge group (constrained crossing bonds: N_b; free ones: N(Q′)). The k-scale framing (PBG's form of G, (3.20)–(3.21)) is dropped, since nothing uses it. #A.11.9's "PBG's, whose constraints include them (#0.1 step (3))" and #A.11.12's "#0.1 step (3)" are corrected.

## S4 (serious). #0.1.37.6 is a sketch

Finding: value jump J, L² Taylor remainder, orthant blending, codimension-3/4 corner patterns not treated.

Check: a scaling count supports it. With a fine pair meeting at a codimension-3 contact and coarse blocks around, the two fine pieces are not joined by joined sites, the mismatch is controlled only through the coarse constraints at the scale L, and a blend at the second-order level (ΔI) costs about J² per unit length near the contact, i.e. a factor L against ‖dD‖² for data spread at the scale L. The second-order route does not close there.

Disposition: none of the callers needs the second-order bound ‖∂*D_L‖. #0.1.16 needs the first-order gap on 𝒮; #0.1.17's control of Π_m∂₁*B follows from the first-order gap by the test function t of #0.1.16; (K0)(d) needs the first-order gap. At the first order the local units ℓ = L give the factor L^{−2} that absorbs the contact counts (the N(p) count of #A.11.16). The interpolation I (#0.1.37.1–#0.1.37.7), steps (2)–(5), and the Hodge reduction (#0.1.32) are removed. The new proof: the anchored potential Ψ of #A.11.13–#A.11.16 near F, block potentials normalised by their block means in the interior (no logarithm; the coarse constraints fix the relative constants block by block, with no accumulation), the transition at the distance L/32 to L/16, the bumps for the block means, and, for constrained crossing bonds, λ set to 0 at the joined sites.

## S2 (serious). #A.9: first-order ω

Disposition: ω is defined from the exact G^c-valued transformation g, u_R = A_N^g, g = e^{iηω}; Im ηω is the integral of the derivative along B_t = Re B + it Im B, and the derivative (up to the factor (1 − e^{−ad iηω})/ad iηω) is the first-order gauge parameter of the problem linearised at B_t, which the first-order bounds control at every B_t with the transports of B_t. This is how #A.9 already treats 𝓗 through VAR (190).

## S3 (serious). #A.9 uses (K0)(f)

Check: (K0)(f)'s "(#A.9)" points to the place of use and is not a dependency. Disposition: the scalar Combes–Thomas argument is written in #A.9 from the per-block Poincaré bound of #0.1.30 and the bumps b_y.

## Minors

- #0.1.30: dependence on a and the flat base. PBG (3.24) p.394: a₁ = a₀ = a, a_{j+1} = aa_j/(aL^{−2} + a_j), so a/2 ≤ a_j ≤ a for L ≥ 2 by induction; the gap is c(d)min(1, a)S^{−2}. The covariant case is stated (axial gauge on each block, holonomy defects by VAR (2)).
- #0.1.31 CMP98 (124) paraphrase, "each bond on one segment", #0.1.32 "PRT1 (1.99)–(1.101) gives that bound", #0.1.37 D_L, R₁M₁: removed with the rewrite.
- #0.1.33.1 and #0.1.34 "blocks are single bonds": single sites.
- #A.8: D̄*μ = 0 holds at the block points of the layers ≥ 1 and, at Λ₀, summed over each component; ⟨μ, D̄Kt⟩ = 0 since Kt = 0 at the points of Λ₀ for t vanishing on the data bonds. The cutoff η is named; Q's normalisation is stated.
- #A.9: exponent 2dL^j; C(d, L) to C(d, L, M); holonomy bound kept (valid, weaker).
- Queued: #0.1.16 χ_y at distance ≥ L/8; (K4)'s Poincaré input named as (K1).

## Context exposure

The reviewer reports AGENTS.md auto-loaded. Noted for the brief; it is outside the packet's mathematics.