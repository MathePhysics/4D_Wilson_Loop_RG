# LF Packet 5, Review 1: Triage

Review: verification\isolated_reviewer\reviews\lf-p5-20261104-r1\review.md (LF 5bf7a26abb89). Verdict: (K0)(a)–(e) hold as claimed, uniformly in the volume, conditional on the two-layer gap #0.1.31–#0.1.37.1 (packet 1, closed). There is no fatal or serious item, and there are five minors. This is the first clean pass. The minors are applied. LF after the repairs: 29c0666c554d (labels 061fd88d33ff).

## Minor

1. **#A.11.6, the source bound.** S_y² now sums θ_B²/min(max(r, 1), L)². The cap at L covers the ∇χ_d terms, of size ≤ C(d)(1 + log L)θ_B/L, in the shell L/32 ≤ dist(·, Λ₀) ≤ L/16. The per-block bound and the Morrey bound at the strata are unchanged.
2. **#A.11.4, the edge bonds.** On the data bonds χ_f := 1/n_b on the bonds of f's closure, n_b the number of faces whose closures contain b, so Σ_fχ_f = 1 on the edge bonds.
3. **#A.11.6, wording.** Now "d*F_f = 0 on the free bonds of supp χ_f".
4. **Unstated facts.**
   - #A.11.8 now states that QE = 0 on the bonds with an endpoint in Ω₂, since E is supported within L/16 of Λ₀ and Λ₁ is ≥ RM wide.
   - #A.11.5 now cites #0.1.27 for θ_B bounding the coarse data.
   - #A.11.10 now states L ≥ 128 (#0.1.37).
   - #A.11.4 now constructs the sector partition: χ_f := ψ_f/Σψ_{f′}, ψ_f := ζ(dist(·, f)/dist(·, Λ₀))ζ₁(s_f/dist(·, Λ₀)).
     - Σψ ≥ 1, by the nearest-point decomposition.
     - The support conditions: the third uses dist(x, S) ≤ √2(dist(x, f) + dist(x, f′)), from the product structure of the box facets in Q_{L/8}(x) (*Setting.*).
     - The gradient bound: χ_f is constant on the bonds at sites with r ≥ 3D/2 + 4, the ball there containing one plane section of ∂Λ₀. Elsewhere abs(∇χ_f) ≤ C(d)/max(D, 1) ≤ C(d)/max(r, 1).
   - #A.11.4 and #A.11.5 now take the faces per local component at the cubes Q_{L/8} of #A.10.
5. **Citations.** #A.11.9 now reads "REG p.81, whose scale-j crossing bonds go from Λ_{j−1} into Λ_j, with PRT2 (2.3); #0.1.3".

## Next

lf-p5-20261104-r2 on LF 29c0666c554d (labels 061fd88d33ff).
