# Packet 11 r9 Triage (LF §4(a)–(b) and #0.17)

Review: verification/isolated_reviewer/reviews/lf-p11-20261105-r9/review.md, on LF f2a00c781939 and table ede3cd24c7da.

## Verdict

r9 is a changed-lines round. Every named step is CORRECT, and r8's m-a and t1–t6 are resolved. It has one minor finding (m-r, the old top-layer wording outside the changed lines, with no mathematical consequence) and six trivials (t-a to t-f). It is not clean, since m-r is minor.

## Repairs

| Finding | Lines | Repair |
|---|---|---|
| m-r | #4.317, #4.338, #4.454.18, #4.530-1, new #4.530-1-1, #4.537 | Each top-layer width now reads LM in its own units (LMε in #4.317, W = LM in #4.338), citing LFR I p.179 l.21–24 and #4.17. No "own scale wide" or "of its scale wide" remains. |
| t-a | new #4.13-2-1 | Off Z and at ∂Z the layers of 𝐁″_k are at least LM₁ wide by #4.18-2-2. |
| t-b | new #4.17-2 | The width holds for k − N₀ + 1 ≤ j ≤ k − 1; the top layer k is Ω″_k, with no inner boundary, and is not crossed. |
| t-c | new #4.18-0-3 | The note's step j is CRE's (j + 1)-st transformation (CRE p.256 l.21–22, quoted). |
| t-d | #4.21-0 | "at the joins Ω₀ and Λ₀ of the class are taken at R′M′". |
| t-e | #4.21-0-1 | The quotation is the print: "The cube □̃³ is either contained in B^j(Λ_j), or intersects also the domain B^{j+1}(Λ_{j+1})" (PBG p.408 l.29–30). |
| t-f | #4.27 | The block size M would need R ≤ L − 1, which need not be PRT2 (2.2)'s "big positive integer which will be fixed later" (p.224 l.11–12). |
| long lines | #4.317 split into #4.317 and #4.317-1; #4.530-1 into #4.530-1 and #4.530-1-1 | Text unchanged beyond the repairs. In #4.454.18 and #4.537 the new wording is no longer than the old. |

## Pre-check

- Sources quoted: LFR I p.179 l.21–24 (as in r8's triage); CRE p.256 l.21–22: "The domains Ω_j, Λ_j, which are determined by the j-th renormalization transformation, but not by the R-operation"; PBG p.408 l.29–30 (corrected file): "The cube □̃³ is either contained in B^j(Λ_j), or intersects also the domain"; PRT2 p.224 l.11–12: "R is a big positive integer which will be fixed later".
- Directions and units: every repaired width is a lower bound, and LM ≥ M, so each line's conclusion holds a fortiori. In #4.530-1 "at least one unit in the units of d" stays true, since LM in M-block units is L ≥ 1. #4.317's W enters through (F-W), which #4.318 states for every W ≥ LM₁.
- Greps: "own scale wide", "of its scale wide", "Mε wide", "W = M", and "l.22–24" over the LF; the remaining "l.22–24" is an unrelated citation (p.195). There are no uses of the split tags #4.317 and #4.530-1 outside the LF. No other note cites the moved sentences.

## Repaired files

LF f7822366eb84, labels cfeddd74b59e (rows 208, multiply defined 101, CR 0), table ede3cd24c7da unchanged.
