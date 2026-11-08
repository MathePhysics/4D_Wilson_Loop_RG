# LF Packet 3, Review 1: Triage

Review: verification\isolated_reviewer\reviews\lf-p3-20261104-r1\review.md (LF 8742125f94e6). Verdict: the claim holds except at one point. There is no fatal item, one serious item, and six minors. All are accepted and repaired. #0.1.19, the definitions of t, t₃, and W, the Q₁ normalisation, and the kernel bounds of T were found correct.

## Serious

1. **#0.1.14, "(2.147) is a change of units".** Accepted. With the printed B₁ the claim is false L-uniformly. The trees of (2.121) contain every internal e₁-bond of a block (p.244). So for B = δ_c the tent Q₁*δ_c of (2.125) keeps only its crossing bonds in B₁, and ‖B₁‖²/‖Q″*B‖² ≈ 3/(2L). The derived claim is removed.
   - The text now states (2.147) as printed, with γ₀ depending on d and L (p.248).
   - It also states the bound ⟨B, QGQ*B⟩ ≥ C(d)^{−1}‖B₁‖² and this example.
   - It states that the note does not use (2.147), since C_H is bounded without (QGQ*)^{−1} (#0.1.13).

   The Landau-slice route the review suggests is not needed for any caller and is not pursued.

## Minor

2. **#0.1.18, the local sup bound.** Accepted. The bound is now stated on the blocks at distance ≥ 4L from Λ^c:
   - sup_{block}abs(u) ≤ C(d)(L^{−d/2}‖u‖_{4·block} + L²sup abs(g′) + (1 + log L)^{1/2}L^{2−d/2}‖∂₁ω_{g′}‖_{4·block} + L max abs(c_{y′}) + e^{−c(d)L}‖e^{−c(d)dist(·, block)}u‖);
   - [T, χ]u is written in divergence form plus (∇χ)F and (∇²χ)u terms, and F is bounded by the Caccioppoli bound for T;
   - the Q₁-terms on the blocks of the coarse bonds meeting the 2·block give the first term;
   - the divergence-form term gives the fourth, and Δ_j's tails give the last.
3. **#0.1.18, the normalisation.** Accepted. With the e^{δρ}-weighted bounds of #0.1.17, data with abs(g′) ≤ S give sup_{block}abs(u) ≤ C(d)(1 + log L)^{C(d)}L²S = C(d)(1 + log L)^{C(d)}θ_B, in the units of the field (#0.1.27).
4. **#0.1.18, t₃ pointwise.** Accepted. t₃ is now the distance to the points z of the contacts at which the cells are distinct local components at z, that is, not joined by a chain of face-sharing cells of Λ^c whose closures contain z (#A.1).
5. **#0.1.14, δ_{Ax(y)}.** Accepted. The sentence now lists (2.95)–(2.97) (p.240), (2.112) and (2.119) (p.243), and (2.121) (p.244), and says that the note's slice (#0.1.15) replaces δ_{Ax(y)}.
6. **#0.1.14, B₀.** Accepted. The radii and smallness conditions on pp.285–289, 293, 295–296, 298, and 304 are added. The grep of the VAR transcription confirms B₀ on these pages.
7. **Notation.** Accepted. #0.1.18 now gives a = 1 (PRT2 p.244 l.2) and says that ∂₁ is the lattice d on forms of each degree. #0.1.19 takes the nearest lattice plane for even L.

## Next

p3 r2 on LF 1f397a562fda (labels 6c1d54db2adc).
