# Triage of Packet 11, Seventh Review (lf-p11-20261105-r7)

The review is verification/isolated_reviewer/reviews/lf-p11-20261105-r7/review.md, on the sixth review's repairs, at the LF bfbb02caa300, the table ede3cd24c7da, and the labels index dedcdd461ffb.

It found no fatal, serious, or minor finding, and three trivial points, o1–o3. Every r6 finding within the extract is resolved. The round is clean, the first clean round after r6. The trivial points are accepted and repaired. A full round, r8, follows; if it is clean, packet 11 is closed.

| Finding | Kind | Verdict | Repair |
|---|---|---|---|
| o1. #4.22-1-1 does not name REG's ratio L^{−1}RM > 2dR₁M₁ or #4.22.1's RM ≥ L² under the alternative reading, nor that #4.22.3's C(L) is taken anew | trivial | correct | New #4.22-1-1-1: K_{M′} > 2dL and K_{M′}M′ ≥ L², both implied; #4.22.3's C(L) at most L/2 times larger; #T2.15 records the adopted reading only |
| o2. #4.14, case 4: the metric of S's strip and of CRE (2.14)'s 2M₁ is not fixed | trivial | correct | New #4.14-1-1: both read as two layers of M₁-cubes (CRE p.256 l.63–64). New #4.14-2 and #4.14-2-1: in PRT2's ℓ¹ distance, a point of S is within 2dM₁ of Ω^c, and w_{h−1}/L − 2dM₁ ≥ M/L − 2dM₁ > (L − 2d)M₁ ≥ M₁, every layer of 𝐁″_k below h being ≥ M wide. #4.14 cites #4.14-2 |
| o3. #4.41-3-3: a²|F_Ũ| ≤ 2C₀ε₁, not C₀ε₁ | trivial | correct | #4.41-3-3: "2C₀^{ms}ε₁ + O(ρ̄(x))", citing the Cauchy note's #C9.7.1-3; the factor enters C_hes^w only |

The long line #4.14 is split: the four cases now start a new line {#4.14-0}.

## Pre-Check Before r8

- Sources. CRE p.256 l.63–64 (corrected file): "dist(Ω_j, Ω^c) ≤ 2M₁, or Ω^{∼−2} ⊂ Ω_j, where the operation ∼ is taken for M₁-cubes". CRE (2.14), p.257: the localisation on Ω ∖ Ω^{∼−2}, with ∂Ω at distance ≥ 2M₁ from the boundary of Ω_j inside Ω. PRT2 p.223: the distance is the l¹-norm. The Cauchy note's #C9.7.1-3: "the plaquettes of Ũ are within 2C₀ε₁ε²/a² by §9.3". Table #T1.3: L ≥ 12d + 6.
- Directions and units. A point in Ω ∖ Ω^{∼−2} lies in an M₁-cube whose second cube neighbourhood meets Ω^c, so its ℓ∞-distance to Ω^c is ≤ 2M₁ and its ℓ¹-distance ≤ 2dM₁. For j ≤ h − 1, (Ω″_j)^c ⊂ (Ω″_{h−1})^c and Ω^c ⊂ Ω″_h, so the triangle inequality gives dist(x, (Ω″_j)^c) ≥ dist(Ω″_h, (Ω″_{h−1})^c) − 2dM₁, in units of the scale h, where that distance is w_{h−1}/L. The layers ≥ M: CRE's 2MR_{h−1}; an earlier operation's top N₀ layers M, middle ≥ LMR_{j+1}, bottom ≥ 3LMR_{h′+1} (#4.18-2-1-1); at ∂Z the cross pair ≥ 2ML^{k−j}a_j and the other pair by the induction, whose base (CRE's layers) is ≥ 2MR; cube-layer lower bounds in ℓ∞ are lower bounds in ℓ¹. Then M/L > LM₁ and LM₁ − 2dM₁ ≥ M₁ for L ≥ 2d + 1. o1: at R = K_{M′}, M = M′, R₁M₁ = M′, REG's ratio reads K_{M′} > 2dL ≤ 12dL; K_{M′}M′ ≥ 12dL·L ≥ L². #4.22.3's thresholds scale by the width ratio (½LK_{M′}M′)/(K_{M′}M′) = L/2.
- Greps. #4.14-1 is cited only in #4.14; #4.14-2 is new and cited in #4.14; the other uses of 2C₀ε₁ (#4.7-3, (9.0)) are unchanged; no duplicate tags; every {#D.} is followed by ":="; CR count 0; the new lines are under 600 characters. The table is unchanged, so no fork message on the table; the LF SHA goes to the fork.

## Repaired Files

- WILSON_IT1_LARGE_FIELD_DEPTH_2026_10_27.md (the LF): a0d78c8b6034.
- CONSTANTS_AND_CONVENTIONS_WDELTA.md (the table): ede3cd24c7da, unchanged.
- LABELS_LF_AND_TABLE.md (the labels index): 4e6123a6df65, 101 multiply defined.
