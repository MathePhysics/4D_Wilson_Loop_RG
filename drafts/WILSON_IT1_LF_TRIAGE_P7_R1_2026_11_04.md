# LF Packet 7, Review 1: Triage

Review: verification\isolated_reviewer\reviews\lf-p7-20261104-r1\review.md (LF d298d5285ba5, table 3d5b823a0a37, labels 94b650007ab7). Verdict: "not established as stated". There is no fatal item, one serious item, and six minors. All items are repaired. LF after the repairs: 7b0b39af8da9 (labels e1fcc79f91e9).

## Serious

1. **S1, #A.11.23: the ℓ¹ curvature bound Σ_{Q_L(x₀)}abs(dA_N) ≤ C(d)(1 + log L)^pL^{d−1}θ is false where Q_L(x₀) meets Λ₀ in positive density.** There dA_N = dB, with abs(dB) ≍ θ_B per data plaquette. The caller #0.1.25 (F₁) is affected.
   - #A.11.23 now states the ℓ¹ bound for da only (F₁^a). It states that on the data plaquettes dA_N = dB, and that the sum over the free plaquettes is ≤ C(d)(1 + log L)²L^{d−1}θ_B.
   - #0.1.25 now moves the data curvature onto E. With χ̃ on bonds (the mean of χ over the plaquettes containing the bond), χdE = ∂₁(χ̃E) − r_χ, where r_χ is supported on the shell of χ and abs(r_χ) ≤ C(d)(1 + log L)L^{−1}θ_B, by abs(E) ≤ C(d)(1 + log L)θ_B ((K0)(b)).
   - H = H_a + H_E, with H_E := −∂₁*Δ^{−1}∂₁r_χ. Then abs(H_E) ≤ C(d)(1 + log L)θ_B/L on Q_{11L}(x̄). H_E is harmonic there, which gives its gradient bound (Lawler–Limic Theorem 6.3.8).
   - F₁ := F₁^a + C(d)(1 + log L)θ_B.
   - #0.1.26 now takes v_{x̄} := χ̃E − ∂₁*Δ^{−1}r_χ + ∂₁*Δ^{−1}(χda). It differs from ∂₁*Δ^{−1}(χdA) by a gradient, since ∂₁*Δ^{−1}∂₁ = 1 − ∂₁Δ^{−1}∂₁*. Its first part is ≤ C(d)(1 + log L)θ_B.
   - The old hyperplane bound in #0.1.26 is removed. It was false inside Λ₀.

   #0.1.25–#0.1.26 are under review in packet 8.

## Minor

2. **(f), #A.11.22.** The L^{d−1} of the Λ₁ blocks at the faces of Λ₂ is now paid by the r₂ condition. The L^{d−1} of the layers j ≥ 2 is paid by δRM ≥ 4(d − 1)log L. "ρ ≥ r₂/L − 2" now reads "ρ ≥ r₂/L − O(1)".
3. **(e), #A.11.20.** The count now reads C(d)(1 + r)^d. All finer blocks within depth L of a coarser face are grouped into the cubes of side L, with the weight at its maximum on each cube.
4. **(v), #A.11.48.**
   - The near part is counted by cube averages.
   - For x ∈ Λ_j, Q_{2L}(x) ∩ Ω_{j+1} is covered by the cubes Q_{L/(2√d)}(x′), with the weights centred at x and at each x′.
   - On Λ_j, V_L = V_N = B.
5. **(v), #A.11.48.** For the Λ_j blocks near Λ_{j−1}, the L^{d/2−1} is paid by the r₂ budget, with V_N = B on Λ_j.
6. **(f), #A.11.22.** The factor L^{d+3} is now stated as an upper bound for its items.
7. **(v).** The far-part shell sum now reads δ^{−d−1}.

## Before review 2

A self-check before launch found two items in (v), #A.11.48, and both are repaired (LF 95da671dfe23, labels 598e9b4ccf8d):
- a sentence fragment ("The bound … enters only within RM/8 of Ω_j^c");
- the payment by e^{−δr₂/(2L)}, which now states that L^{2d+2} bounds L^{d+3}·L^{d−1} and L^{d+3}·L^{d/2−1} = L^{3d/2+2}. These two factors do not enter together, since the blocks of Λ_j within RM/2 of Λ_{j−1} lie at distance ≥ RM/2 from Ω_{j+1}.

## Review 2

lf-p7-20261104-r2 on LF 95da671dfe23 is clean: "the claim holds as stated", with no fatal or serious item. This is packet 7's first clean pass. Its four minors are applied (LF 313ee0d115ea, labels d4fd40abb30b):
- m1, (e), #A.11.20: all the blocks of the finer layer are grouped into the cubes of the next coarser grid, those deeper than L included. Ungrouped, the blocks reached through the coarser layer at depth in (L, r) would number about L^{d−1}r^d.
- m2, (v), #A.11.48: each deeper face, of Ω_{j+2} and beyond, adds L^{d−1} beyond the crossing of a layer, paid by δRM ≥ 4(d − 1)log L ((f)).
- m3, (f), #A.11.22: the Λ₁ blocks at the faces of Λ₂ include the deeper ones reached laterally through Λ₂, all at ρ ≥ r₂/L − O(1), paid by the condition on r₂.
- m4, #A.11.23: the ‖dA_N‖ half of the bootstrap names the local energy of V_L on R_j, bounded by (a)–(f) for V_L ((1)), with ∂₁V_L = ∂₁B on the scale-j bonds of Λ_j.

The caller note for packet 8 says that F₁^a in #0.1.25 is a supremum over all x₀, while (f) supplies it only on its own range. It is repaired with the packet 8 pre-check:
- F₁ and F₁^a are now suprema over x₀ ∈ Q_{24L}(x̄).
- F₁^a is supplied by (f) at the x̄ at which (KW) is run: those with Q_{48L}(x̄) in (f)'s range, and at Λ_j/Λ_{j+1} those with Q_{48L}(x̄) ⊂ R_j, by (f) for V_L.

Also applied with these, from the packet 8 pre-check:
- #0.1.26: the first part of v_{x̄} vanishes unless t(y) ≤ 31L, so it lies within the weight.
- #A.15 (K4): moved to the decomposition v = χ̃E − ∂₁*Δ^{−1}r_χ + ∂₁*Δ^{−1}(χda).
- #0.1.25: the citation is now Lawler–Limic Theorem 6.3.8(a), (6.17), since H_E has no sign.

## Review 3

lf-p7-20261104-r3 on LF 313ee0d115ea is clean: "the claim holds as stated", with no fatal or serious item. Packet 7 now has two consecutive clean passes (r2 and r3). Its minors are applied (LF 1ce1241e341b, labels 8a9b2c7efa17):
- n1, (e): the grouping into cubes is limited to the finer layers whose sources are those of (b) (Λ₀) or are bounded through ℳ (the layers of U). The blocks of Λ₁, with the sources of (c), are counted block by block, as in (f).
- n2, (v): L^{d−1} and L^{d/2−1} enter together only at the blocks of Λ_j within RM/2 of Λ_{j−1} reached laterally through Ω_{j+1}. These lie at ρ_j > RM/2, so m − r₂/(2L) ≥ 3RM/8. Half of e^{−δ(m − r₂/(2L))}, ≤ e^{−3δRM/16} ≤ L^{1−d/2} for δRM ≥ 4(d − 1)log L, pays the remaining factor, and the other half absorbs the polynomial factors in m.
- n3: #A.11.23 now cites #A.11.33 for (a)–(f) for V_L.

## Next

Packet 8: lf-p8-20261104-r1 on LF 1ce1241e341b (labels 8a9b2c7efa17).
