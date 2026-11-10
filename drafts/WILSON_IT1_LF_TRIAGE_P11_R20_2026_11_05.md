# Packet 11 r20 Triage (LF §4(a)–(b) and #0.17)

Review: verification/isolated_reviewer/reviews/lf-p11-20261105-r20/review.md (full round), on LF 5fe659239484, labels caf325444449, and table 39fe437e0921.

## Verdict

r20 has no fatal or serious finding. It has one minor finding, m-1, which my repair of r19's t-A introduced, and four trivial findings, t-1 to t-4. So it is **not clean**. r21 reviews the changed lines; a full round follows if r21 is clean.

## Repairs

| Finding | Lines | Repair |
|---|---|---|
| m-1 | #4.41-2-2, new #4.41-2-3, #4.41-3, #4.42; table #T4.35 | §9.3 pairs a coarse plaquette with the L⁴ fine plaquettes of its 4-cell (Cauchy #C9.3.3-6), not with the L² tiling it. Their centres lie within ½ε in p's directions and ε in the other two, so within (√10/2)ε < 2ε. The difference of w in b_w is ≤ 2ε times the gradient bound, and the term becomes 6(C₀^{ms})² in #4.41-3, #4.42, C_w, and #T4.35. #4.41-2's ½ε is unchanged. |
| t-1 | new #4.7-1-4-1-2 | The joins enter only through U_1 and U_2 at the data of LFR II (1.53), and U_{1,2} is U_1 on Ω″^∼_{h+1} and U_2 on its complement. |
| t-2 | #4.317-1, #4.318 | "With W the least crossed width"; #4.318's redundant "W = RM" is removed. |
| t-3 | #4.26 | VAR p.304 l.21–24 (a₅ chosen at l.21–22, the condition at l.22, (166) at l.24). |
| t-4 | #4.530-1, #4.537, #4.454.18 | The monotonicity of R_j is no longer used. #4.530-1 reads "R_j can decrease in j (CRE (2.5)), so no width R_{m+1} is claimed". #4.537 uses R_k ≤ LR_{k₀+2} (CRE (2.9), n = k > m = k₀ + 2 or equality), so the crossing is ≥ 8MR_k/M₁ M₁-cubes. ½·8MR_k/M₁ = 4MR_k/M₁ ≥ 2MR_k/M₁ + 2M/M₁ at R_k ≥ 1 keeps the next inequality. #4.454.18's citation of the max is updated to 8MR_k/M₁. |

## Pre-check

- **Sources read.**
  - Cauchy #C9.3.3-6 ("cell(p) the L⁴ fine plaquettes parallel to p in the 4-cell of p").
  - LFR II (1.52)–(1.53), p.370 l.18–33.
  - VAR p.304 l.21–24.
  - CRE (2.9), p.256 l.13–17 (R_n ≤ LR_m).
  - CRE (2.5), p.255 l.36–39.
- **Arithmetic.**
  - √(2·(½)² + 2·1²) = √(5/2) = √10/2 ≈ 1.58 < 2.
  - 2 × 3 = 6.
  - 4MR_k/M₁ ≥ 2MR_k/M₁ + 2M/M₁, since R_k ≥ 1.
- **Every use.**
  - 3(C₀^{ms})² appeared only in #4.41-3, #4.42 (twice), and #T4.35; all now read 6.
  - The max with 8LMR_k/M₁ appeared in #4.537 and #4.454.18; both now read 8MR_k/M₁.
  - The decay e^{−δMR_k/M₁}e^{−δM/M₁} that follows is unchanged.
  - #4.41-3 cites #4.41-2-3.
- **Lines.**
  - The new and changed lines are under 600 characters. #4.41-2-2 was split into #4.41-2-3.
  - The edits in the long lines #4.26, #4.454.18, #4.530-1, and #4.537 are same-length or shorter.
  - CR 0 in both files; no duplicate tags.

## Repaired files

LF f7d2cf3872b9, table b562b85c8322, labels 7b8c355c75b3 (multiply defined 101).
