# Packet 11 r8 Triage (LF §4(a)–(b) and #0.17)

Review: verification/isolated_reviewer/reviews/lf-p11-20261105-r8/review.md, on LF a0d78c8b6034 and table ede3cd24c7da.

## Verdict

r8 is a full round with no fatal or serious finding, one minor (m-a), and six trivials (t1–t6). It is not clean, since m-a is minor. Two consecutive clean rounds are needed again, the second full.

## Repairs

| Finding | Lines | Repair |
|---|---|---|
| m-a | #4.17, new #4.17-1 | The top N₀ layers are one layer of M-cubes of the next scale j + 1 wide, so LM wide in their own units; #4.17-1 quotes LFR I p.179 l.21–24 and gives Ma_{j+1} = LMa_j. |
| m-a | #4.9-1, #4.13-2, #4.18-2, #4.18-2-1-1, #4.27, #0.17-1, #4.318 | "M wide" becomes "LM wide" (citing #4.17); #4.318's (F-W) holds for every W ≥ LM₁, the left side increasing in W. |
| t1 | #4.12, #4.14-1-1, #4.444 (□₀^{∼−2} ⊂ Ω_j) | CRE p.256 l.62–63, the corrected file's lines of the sentence. |
| t2 | #4.14-2-1 | "CRE's layer j is ≥ 2MR_j". |
| t3 | #4.21-0 | PRT2 p.228 l.20–21 prints "For example" with the set named Ω; PBG p.394 l.32 prints "e.g." with Ω₀. |
| t4 | #4.18 | "These Ω_j are domains of renormalisation steps, Ω_{j+1} that of the step j", the convention of #4.12-1-1, #4.18-0-1-1, and #4.41-1-3-3. |
| t5 | new #4.13-1 | The ℓ¹ remark for 𝐁₁'s layer h: ≥ LMR_{h+1} − 2dM₁ > (L³ − 2d)M₁ ≥ LM₁. |
| t6 | #4.41-3-3 | 2C₀^{ms}ε₁ε²/a_{j(x)}², #C9.7.1-3 with C₀^{ms} and a_{j(x)} (#4.7-2). |
| long lines | #0.17-1 split into #0.17-1 and #0.17-1-0; #4.13 into #4.13, #4.13-1, #4.13-2; #4.17 into #4.17, #4.17-1; #4.21 into #4.21, #4.21-0, #4.21-0-1; #4.27 into #4.27, #4.27-1 | Text unchanged beyond the repairs above. |

## Pre-check

- Sources quoted: LFR I p.179 l.21–24 (corrected file): "Z_k''^c, Z_{k−1}'' are separated by one layer of M-cubes. Similarly, … Z_{k−1}''^c, Z_{k−2}'' are separated by one layer of L^{−1}M-cubes, and so on", the M-cubes being of the lattice T_η of the scale k. CRE p.256 l.62–63: "dist(Ω_j, Ω^c) ≤ 2M₁, or Ω^{∼−2} ⊂ Ω_j, where the operation ∼ is taken for M₁-cubes". PRT2 p.228 l.20–21: "For example we may take Ω = {a sum of big blocks of the lattice T_1 with distances to Ω_1 ≤ RM}". Cauchy #C9.7.1-3: "the plaquettes of Ũ are within 2C₀ε₁ε²/a² by §9.3".
- Directions and units: LM ≥ M, so every lower bound that used M for the top layers holds a fortiori; no upper bound on the top width is used anywhere (grep below). #4.13-1: ℓ¹ ≤ dℓ∞ gives the subtracted 2dM₁ as an upper bound, and ℓ¹ ≥ ℓ∞ gives LMR_{h+1} as a lower bound; L³ − 2d ≥ L since L ≥ 2d + 1. #4.41-3-3: a_{j(x)}²|F| ≤ a_{j(x)}²·(2C₀^{ms}ε₁ε²/a_{j(x)}²)/ε² = 2C₀^{ms}ε₁.
- Greps: "M wide", "own scale wide", "M-cube(s) of their", "widths M", "l.63–64", "renormalisation steps j" over the LF. The remaining "at least one M-cube of its own scale wide" (#4.454.18, #4.530-1, #4.537) are lower bounds, correct since LM ≥ M, and are left. Uses of the split tags #0.17-1, #4.13, #4.17, #4.27 checked: #4.22.3, #4.18-2-2, #A.11.1.1, #A.11.1.2, and #A.11.1.6-1 cite #4.27 for the M′ device and widths ≥ R′M′, both still in #4.27.
- Quantifiers: #4.17-1 states the width for every top index j, the L^{−(k−j−1)}M-cubes of T_η being the M-cubes of the scale j + 1.

## Repaired files

LF f2a00c781939, labels 29d20c18f8f1 (rows 208, multiply defined 101, CR 0), table ede3cd24c7da unchanged.
