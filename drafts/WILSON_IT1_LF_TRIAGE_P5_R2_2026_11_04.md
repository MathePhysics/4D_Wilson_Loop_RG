# LF Packet 5, Review 2: Triage

Review: verification\isolated_reviewer\reviews\lf-p5-20261104-r2\review.md (LF 29c0666c554d). Verdict: (K0)(a)–(e) hold as claimed, uniformly in the volume and in the support of the data, conditional on the two-layer gap #0.1.31–#0.1.37.1 (packet 1, closed). There is no fatal or serious item, and there are four minors. This is the second consecutive clean pass (r1, r2), so packet 5 meets the closing rule. Minor 1 changes the definition of the faces in (b), so a confirmation pass, r3, runs on the repaired text. LF after the repairs: ae21b40cff99 (labels 6b65ab62b124).

## Minor

1. **#A.11.4, the faces.** The reviewer's repair, maximal faces with a per-local-component reading at the joining paths of #A.11.5, leaves one case open. At a codimension-2 contact inside one plane, two pieces of one maximal face can belong to distinct local components, and a site above the contact sees blocks of both within C(d)m_f. No short path of data bonds joins them. The repair applied instead:
   - The faces are the facets, of side L, of the blocks of side L of Λ₀ that lie in ∂Λ₀, and Y_f is the block of f. The strata are the (d − 2)-faces of these facets, so they include the strata of ∂Λ₀ and the contacts of distinct local components.
   - B_f is B on the whole plane of f in Λ₀, so F_f and E_f depend on f only through its plane, and cutting a plane into facets changes no E-term.
   - #A.11.5: Ĝ_f := G^{Y_f}_T, the cone potential of (d) from the one block Y_f. The joining paths and the second product-rule sum are removed.
   - The support property (3) now holds with S the intersection of the two closures, products of intervals, and the "diam f" sentence is deleted.
   - The gradient argument uses the ball B(x, 3D/2 + 4), of diameter < L, which meets at most one block hyperplane per direction.
   - S_y is summed over the free sites within L/16 of Λ₀, near which lie C(d) strata of size L^{d−2}. The bounds are unchanged.
   - New property, used by #A.11.41: on supp χ_f, the points of H₋(f) off Λ₀ and of Λ₀ off H₋(f) are at distance ≥ min(r, L/8)/(6√d).
2. **Citations.** In #A.11.8 and #A.11.9, PRT2 (2.3) and p.224 are replaced by VAR p.278 l.39–42 (a bond of a plaquette of Λ_j not in Λ_j has both endpoints in Λ_{j−1}) and REG p.81. Checked against the transcription.
3. **Wording.**
   - f₀ is a face with χ_{f₀} ≠ 0 at the bond, where E_{f₀} is defined.
   - #A.11.18: D = 0 on the data bonds of B(c₋), and c is adjacent to the block of Λ₁.
   - On a free bond, χ_f is its value at the endpoint farther from Λ₀.
4. **Outside the claim.**
   - The covariant extension in #A.11.1: not claimed in packet 5.
   - #A.11.41 now uses the new property of (b), reads "off f's closure", and gives the bound C(d)θ_B/min(max(r, 1), L)². Packet 6 reviews it.

## Also applied (packet 6 and 7 pre-checks)

- #A.11.40: e^{−δ₀s(p)/16} and the weights e^{−δ₀t/16}.
- #A.11.48: at j = 1 the blocks of Λ₁ within RM/2 of Λ₀ are bounded through (f).

## Next

lf-p5-20261104-r3 on LF ae21b40cff99 (labels 6b65ab62b124), a confirmation pass on the repaired (b).
