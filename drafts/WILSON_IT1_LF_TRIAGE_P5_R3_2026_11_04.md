# LF Packet 5, Review 3: Triage

Review: verification\isolated_reviewer\reviews\lf-p5-20261104-r3\review.md (LF ae21b40cff99). Verdict: (K0)(a)–(e) hold as claimed, uniformly in the volume and in the support of the data, conditional on the two-layer gap #0.1.31–#0.1.37.1 (packet 1, closed). There is no fatal or serious item. All of r2's findings are addressed, including the block-facet faces and the distance property of supp χ_f. This is the confirmation pass after r1 and r2, and r2 and r3 are consecutive clean passes on the repaired (b), so **packet 5 is CLOSED**. The minors are applied. LF after the repairs: 3a128b6a24e7 (labels 4fc452947259).

## Minor

1. **Seam bonds (#A.11.5, #A.11.6, #A.11.41).** These are the data bonds of f's closure that leave Y_f.
   - #A.11.4 now gives the lattice meaning of f's closure: the data bonds in the plane of Y_f's outer sites next to f with an endpoint among these sites.
   - #A.11.5 sets Ĝ_f := 0 also at the seam sites, so T̂_f = 0 on the bonds of Y_f and on the data bonds of f's closure. On a bond from a seam site y′, T̂_f differs from T − ∂G^{Y_f}_T by G^{Y_f}_T(y′), which is ≤ C(d) times the local sum of abs(dT), so the strip bound holds with m_f = 1.
   - #A.11.6 and #A.11.41 now read "T̂_f = 0 on the data bonds of f's closure".
   - No bound changes.
2. **Wording.**
   - "meets no stratum" in both ball arguments.
   - #A.11.18: "the lines of c carry D ≠ 0 only on the unit crossing bond and in B(c₊)".
   - The lattice closure of f: item 1.
3. **Outside the claim.**
   - The covariant extension (#A.11.1) is not claimed in packet 5.
   - The forward references to ℳ, (f), and (g) are reviewed in packets 6–8.
   - PRT2 pp.224 and 245 and PBG Corollary 3.6 were checked in r1 and r2.

## Next

Packet 6, (K0)(g) the split, (s1)–(s3), (1)–(4), and (6)(i)–(iv): lf-p6-20261104-r1 on LF 3a128b6a24e7, after the table edit of row 232 (requested by the two-loops session).
